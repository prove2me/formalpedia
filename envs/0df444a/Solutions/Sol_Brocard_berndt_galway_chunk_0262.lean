-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0262
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:49:10.484857+00:00
-- url     : https://prove2.me/submissions/391b0b31-6a74-4b2e-b8cf-86f6090b3365

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 46942450 ≤ n < 47122306 has `n! + 1` a square.
For every such `n` a prime `p > n + 1` (from a per-sub-range list, each prime certified by a
gcd against a product of all primes below its square root) with `j = p - 1 - n`,
`Q = (-1)^j j! mod p` and `N = Q (Q - 1) mod p` has `N ^ ((p - 1) / 2) ≡ -1 (mod p)`; by Wilson
`Q^2 (n! + 1) ≡ N`, so `n! + 1` is not a square mod `p`. Checked by the kernel
(`decide +kernel`) through the frame `BRFrame`. -/

set_option autoImplicit false
set_option linter.all false
set_option Elab.async false

namespace BRFrame

/-! ## 1. The criterion (Wilson + Euler)

For a prime `p = n + j + 1`, Wilson's theorem gives `n! * Q = -1` in `ZMod p` with
`Q = (-1) ^ j * j!`. If `n! + 1 = m ^ 2` then `Q * (Q - 1) = (Q * m) ^ 2` is a square, so its
`(p - 1) / 2`-th power is `0` or `1`, never `-1`. -/

theorem fact_split (p : ℕ) : ∀ j n : ℕ, n + j + 1 = p →
    (((p - 1).factorial : ℕ) : ZMod p) =
      ((n.factorial : ℕ) : ZMod p) * ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) := by
  intro j
  induction j with
  | zero =>
    intro n h
    have e : p - 1 = n := by omega
    rw [e]
    simp
  | succ j ih =>
    intro n h
    rw [ih (n + 1) (by omega), Nat.factorial_succ n, Nat.factorial_succ j]
    have h0 : ((n + 1 + (j + 1) : ℕ) : ZMod p) = 0 := by
      rw [show n + 1 + (j + 1) = p by omega]
      exact ZMod.natCast_self p
    push_cast at h0 ⊢
    linear_combination ((-1) ^ j * ((j.factorial : ℕ) : ZMod p) * ((n.factorial : ℕ) : ZMod p)) * h0

theorem crit (p n j m : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hj : n + j + 1 = p) (Q N : ℕ)
    (hQ : (Q : ZMod p) = (-1) ^ j * ((j.factorial : ℕ) : ZMod p))
    (hN : (N : ZMod p) = (Q : ZMod p) * ((Q : ZMod p) - 1))
    (he : (N : ZMod p) ^ ((p - 1) / 2) = -1) : Nat.factorial n + 1 ≠ m ^ 2 := by
  intro hm
  haveI := Fact.mk hp
  have hw : ((n.factorial : ℕ) : ZMod p) * (Q : ZMod p) = -1 := by
    rw [hQ, ← fact_split p j n hj]
    exact @ZMod.wilsons_lemma p _
  have hm' : ((n.factorial : ℕ) : ZMod p) + 1 = (m : ZMod p) ^ 2 := by
    have := congrArg (fun x : ℕ => (x : ZMod p)) hm
    push_cast at this
    exact this
  have hsq : (N : ZMod p) = ((Q : ZMod p) * (m : ZMod p)) ^ 2 := by
    rw [hN, mul_pow, ← hm']
    linear_combination (-(Q : ZMod p)) * hw
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have h2e : 2 * ((p - 1) / 2) = p - 1 := by omega
  rw [hsq, ← pow_mul, h2e] at he
  by_cases hx : (Q : ZMod p) * (m : ZMod p) = 0
  · rw [hx, zero_pow (by omega)] at he
    have h1 : (1 : ZMod p) = 0 := by linear_combination he
    exact one_ne_zero h1
  · rw [ZMod.pow_card_sub_one_eq_one hx] at he
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination he
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff _ _).1 h2
    have := Nat.le_of_dvd (by norm_num) hd
    omega

/-! ## 2. Modular powering: four windows (8, 7, 7, 7 bits; fast for `e < 2 ^ 29`; exact for all `e`) -/

def w7 (p a e : ℕ) : ℕ :=
  Nat.mod (Nat.mul (Nat.pow (Nat.mod (Nat.mul (Nat.pow (Nat.mod (Nat.mul (Nat.pow
    (Nat.mod (Nat.pow a (Nat.shiftRight e 21)) p) 128)
    (Nat.pow a (Nat.land (Nat.shiftRight e 14) 127))) p) 128)
    (Nat.pow a (Nat.land (Nat.shiftRight e 7) 127))) p) 128)
    (Nat.pow a (Nat.land e 127))) p

theorem win (p a x u d : ℕ) (hx : x ≡ a ^ u [MOD p]) :
    Nat.mod (Nat.mul (Nat.pow x 128) (Nat.pow a d)) p ≡ a ^ (u * 128 + d) [MOD p] := by
  refine (Nat.mod_modEq (x ^ 128 * a ^ d) p).trans ?_
  rw [pow_add, pow_mul]
  exact (hx.pow 128).mul_right _

theorem sh_div (e k : ℕ) : Nat.shiftRight e k = e / 2 ^ k := by
  show e >>> k = e / 2 ^ k
  rw [Nat.shiftRight_eq_div_pow]

theorem w7_spec (p a e : ℕ) : w7 p a e ≡ a ^ e [MOD p] := by
  have d14 : Nat.land (Nat.shiftRight e 14) 127 = e / 2 ^ 14 % 2 ^ 7 := by
    rw [sh_div]; exact Nat.and_two_pow_sub_one_eq_mod _ 7
  have d7 : Nat.land (Nat.shiftRight e 7) 127 = e / 2 ^ 7 % 2 ^ 7 := by
    rw [sh_div]; exact Nat.and_two_pow_sub_one_eq_mod _ 7
  have d0 : Nat.land e 127 = e % 2 ^ 7 := Nat.and_two_pow_sub_one_eq_mod _ 7
  unfold w7
  rw [d14, d7, d0, sh_div e 21]
  have h0 : Nat.mod (Nat.pow a (e / 2 ^ 21)) p ≡ a ^ (e / 2 ^ 21) [MOD p] := Nat.mod_modEq _ _
  have h1 := win p a _ _ (e / 2 ^ 14 % 2 ^ 7) h0
  have h2 := win p a _ _ (e / 2 ^ 7 % 2 ^ 7) h1
  have h3 := win p a _ _ (e % 2 ^ 7) h2
  refine h3.trans ?_
  have ee : ((e / 2 ^ 21 * 128 + e / 2 ^ 14 % 2 ^ 7) * 128 + e / 2 ^ 7 % 2 ^ 7) * 128 + e % 2 ^ 7 = e := by
    norm_num
    omega
  rw [ee]

/-! ## 3. The factorial table

`mkT W k j f acc` appends `f = j!`, `(j+1)!`, ... (`k` entries, `W` bits each) below `acc`, so in
`TB W J = mkT W (J + 1) 0 1 0` the entry `j` sits at bit `W * (J - j)`. Nothing is assumed about it:
`tabOK` checks every entry against a running factorial in the kernel. -/

def mkT (W : ℕ) (k : ℕ) : ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ) (fun _ _ acc => acc)
    (fun _ ih j f acc => ih (Nat.add j 1) (Nat.mul f (Nat.add j 1)) (Nat.lor (Nat.shiftLeft acc W) f)) k

def ext (T W M J j : ℕ) : ℕ := Nat.land (Nat.shiftRight T (Nat.mul W (Nat.sub J j))) M

/-- `tabOK T W M J k j f`: entries `j, j+1, ..., j+k-1` equal `f, f*(j+1), ...` -/
def tabOK (T W M J : ℕ) (k : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => true)
    (fun _ ih j f => Nat.beq (ext T W M J j) f && ih (Nat.add j 1) (Nat.mul f (Nat.add j 1))) k

theorem tabOK_sound (T W M J : ℕ) : ∀ k j, tabOK T W M J k j (Nat.factorial j) = true →
    ∀ i, j ≤ i → i < j + k → ext T W M J i = Nat.factorial i := by
  intro k
  induction k with
  | zero => intro j _ i h1 h2; omega
  | succ k ih =>
    intro j h i h1 h2
    have h' : (Nat.beq (ext T W M J j) (Nat.factorial j) &&
        tabOK T W M J k (Nat.add j 1) (Nat.mul (Nat.factorial j) (Nat.add j 1))) = true := h
    rw [Bool.and_eq_true] at h'
    by_cases hij : i = j
    · subst hij
      exact Nat.eq_of_beq_eq_true h'.1
    · have hf : Nat.mul (Nat.factorial j) (Nat.add j 1) = Nat.factorial (j + 1) := by
        show Nat.factorial j * (j + 1) = Nat.factorial (j + 1)
        rw [Nat.factorial_succ, Nat.mul_comm]
      have h2' := h'.2
      rw [hf] at h2'
      exact ih (j + 1) h2' i (by omega) (by omega)

/-! ## 4. Prime pools

`chk6 P T`: `6 ∣ P` and `6t+5`, `6t+7` share a factor with `P` for every `t < T`; then every prime
`q ≤ 6T+1` divides `P`. A number `q < Bd` with `gcd q P = 1` and every prime `r` with `r * r < Bd`
dividing `P` is prime. -/

def chk6 (P : ℕ) (T : ℕ) : Bool :=
  Nat.beq (Nat.mod P 6) 0 &&
  Nat.rec (motive := fun _ => Bool) true
    (fun t ih => !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1) &&
      !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1) && ih) T

theorem chk6_rec (P : ℕ) : ∀ T, Nat.rec (motive := fun _ => Bool) true
    (fun t ih => !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1) &&
      !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1) && ih) T = true →
    ∀ t, t < T → Nat.gcd (6 * t + 5) P ≠ 1 ∧ Nat.gcd (6 * t + 7) P ≠ 1 := by
  intro T
  induction T with
  | zero => intro _ t ht; omega
  | succ T ih =>
    intro h t ht
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨h5, h7⟩, hr⟩ := h
    by_cases htT : t = T
    · subst htT
      constructor
      · intro hc
        have : Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1 = true := by
          show Nat.beq (Nat.gcd (6 * t + 5) P) 1 = true
          rw [hc]; rfl
        rw [this] at h5; exact absurd h5 (by decide)
      · intro hc
        have : Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1 = true := by
          show Nat.beq (Nat.gcd (6 * t + 7) P) 1 = true
          rw [hc]; rfl
        rw [this] at h7; exact absurd h7 (by decide)
    · exact ih hr t (by omega)

theorem chk6_sound (P T : ℕ) (h : chk6 P T = true) :
    ∀ q : ℕ, q.Prime → (q ≤ 3 ∨ q ≤ 6 * T + 1) → q ∣ P := by
  unfold chk6 at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h6, hr⟩ := h
  have h6' : P % 6 = 0 := Nat.eq_of_beq_eq_true h6
  have hall := chk6_rec P T hr
  intro q hq hb
  have hq2 := hq.two_le
  have hdvd : ∀ t, (q = 6 * t + 5 ∨ q = 6 * t + 7) → t < T → q ∣ P := by
    intro t ht htT
    rcases Nat.coprime_or_dvd_of_prime hq P with hc | hc
    · rcases ht with ht | ht
      · rw [ht] at hc; exact absurd hc (hall t htT).1
      · rw [ht] at hc; exact absurd hc (hall t htT).2
    · exact hc
  by_cases h23 : q ≤ 3
  · have : q = 2 ∨ q = 3 := by omega
    rcases this with e | e
    · subst e; omega
    · subst e; omega
  · have hb' : q ≤ 6 * T + 1 := by omega
    have hm : q % 6 = 1 ∨ q % 6 = 5 := by
      have h2 : ¬ 2 ∣ q := by
        intro hd
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).1 hd
        omega
      have h3 : ¬ 3 ∣ q := by
        intro hd
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).1 hd
        omega
      omega
    rcases hm with hm | hm
    · exact hdvd (q / 6 - 1) (Or.inr (by omega)) (by omega)
    · exact hdvd (q / 6) (Or.inl (by omega)) (by omega)

theorem prime_of_pool (P Bd q : ℕ) (hP : ∀ r : ℕ, r.Prime → r * r < Bd → r ∣ P) (h2 : 2 ≤ q)
    (hq : q < Bd) (hc : Nat.gcd q P = 1) : q.Prime := by
  by_contra hnp
  have hq1 : q ≠ 1 := by omega
  have hmp := Nat.minFac_prime hq1
  have hsq := Nat.minFac_sq_le_self (by omega) hnp
  have hsq' : q.minFac * q.minFac ≤ q := by rw [← pow_two]; exact hsq
  have hdP := hP q.minFac hmp (by omega)
  have hd : q.minFac ∣ Nat.gcd q P := Nat.dvd_gcd (Nat.minFac_dvd q) hdP
  rw [hc] at hd
  have := Nat.le_of_dvd one_pos hd
  have := hmp.two_le
  omega

/-- pools: `6` below `16`, `30030` below `196`, `P3` below `32761`, `P4` below `1024000000` -/
def pOK (P3 P4 p : ℕ) : Bool :=
  Nat.ble 5 p && cond (Nat.blt p 16) (Nat.beq (Nat.gcd p 6) 1)
    (cond (Nat.blt p 196) (Nat.beq (Nat.gcd p 30030) 1)
      (cond (Nat.blt p 32761) (Nat.beq (Nat.gcd p P3) 1)
        (Nat.blt p 1024000000 && Nat.beq (Nat.gcd p P4) 1)))

theorem blt_t {a b : ℕ} (h : a < b) : Nat.blt a b = true := by simpa using h

theorem blt_f {a b : ℕ} (h : ¬ a < b) : Nat.blt a b = false := by
  cases hb : Nat.blt a b
  · rfl
  · exact absurd (by simpa using hb) h

theorem P6_ok : chk6 6 0 = true := by decide +kernel
theorem P30030_ok : chk6 30030 2 = true := by decide +kernel

theorem pOK_sound (P3 P4 : ℕ) (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true) (p : ℕ)
    (h : pOK P3 P4 p = true) : p.Prime ∧ 5 ≤ p := by
  unfold pOK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h5, h⟩ := h
  have h5' := Nat.le_of_ble_eq_true h5
  refine ⟨?_, h5'⟩
  by_cases c1 : p < 16
  · rw [blt_t c1, cond_true] at h
    exact prime_of_pool 6 16 p (fun r hr hrr => chk6_sound 6 0 P6_ok r hr (by
      left; by_contra hc; have : 4 * 4 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c1 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c1, cond_false] at h
  by_cases c2 : p < 196
  · rw [blt_t c2, cond_true] at h
    exact prime_of_pool 30030 196 p (fun r hr hrr => chk6_sound 30030 2 P30030_ok r hr (by
      right; by_contra hc; have : 14 * 14 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c2 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c2, cond_false] at h
  by_cases c3 : p < 32761
  · rw [blt_t c3, cond_true] at h
    exact prime_of_pool P3 32761 p (fun r hr hrr => chk6_sound P3 30 h3 r hr (by
      right; by_contra hc; have : 182 * 182 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c3 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c3, cond_false, Bool.and_eq_true] at h
  have c4 := Nat.le_of_ble_eq_true h.1
  exact prime_of_pool P4 1024000000 p (fun r hr hrr => chk6_sound P4 5333 h4 r hr (by
      right; by_contra hc; have : 32000 * 32000 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c4 (Nat.eq_of_beq_eq_true h.2)

/-! ## 5. One `n`: the test

`fm`: `j!` from the table for `j ≤ J`, else from entry `J` by the loop `lp` (rare).
`nN = f * (f + s) mod p` with `f ≡ j! (mod p)`, `s = p - 1` (`j` even) or `1` (`j` odd); this is
`Q * (Q - 1)` for `Q = (-1)^j j!`. -/

def lp (p : ℕ) (k : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ acc => acc)
    (fun _ ih i acc => ih (Nat.add i 1) (Nat.mod (Nat.mul acc (Nat.add i 1)) p)) k

theorem lp_spec (p : ℕ) : ∀ k i acc, acc ≡ Nat.factorial i [MOD p] →
    lp p k i acc ≡ Nat.factorial (i + k) [MOD p] := by
  intro k
  induction k with
  | zero => intro i acc h; exact h
  | succ k ih =>
    intro i acc h
    have e : lp p (k + 1) i acc = lp p k (Nat.add i 1) (Nat.mod (Nat.mul acc (Nat.add i 1)) p) := rfl
    rw [e]
    have h2 : Nat.mod (Nat.mul acc (Nat.add i 1)) p ≡ Nat.factorial (i + 1) [MOD p] := by
      refine (Nat.mod_modEq (acc * (i + 1)) p).trans ?_
      rw [Nat.factorial_succ, Nat.mul_comm (i + 1)]
      exact h.mul_right _
    have := ih (i + 1) _ h2
    rw [show i + 1 + k = i + (k + 1) by omega] at this
    exact this

def fm (T W M J p j : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (lp p (Nat.sub j J) J (Nat.mod (ext T W M J J) p))
    (ext T W M J j) (Nat.ble j J)

theorem fm_spec (T W M J p j : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) :
    fm T W M J p j ≡ Nat.factorial j [MOD p] := by
  unfold fm
  by_cases hj : j ≤ J
  · have hb : Nat.ble j J = true := by rw [Nat.ble_eq]; exact hj
    rw [hb]; dsimp only; rw [hT j hj]
  · have hb : Nat.ble j J = false := by
      cases h : Nat.ble j J
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true h) hj
    rw [hb]; dsimp only
    have h0 : Nat.mod (ext T W M J J) p ≡ Nat.factorial J [MOD p] := by
      rw [hT J le_rfl]; exact Nat.mod_modEq _ _
    have := lp_spec p (Nat.sub j J) J _ h0
    rw [show J + Nat.sub j J = j by show J + (j - J) = j; omega] at this
    exact this

def nN (T W M J p j : ℕ) : ℕ :=
  Nat.mod (Nat.mul (fm T W M J p j) (Nat.add (fm T W M J p j)
    (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1) (Nat.sub p 2)))))) p

theorem cast_nN (T W M J p j : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) (hp : 2 ≤ p) :
    ((nN T W M J p j : ℕ) : ZMod p) =
      ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) * (((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) - 1) := by
  have hm : ((fm T W M J p j : ℕ) : ZMod p) = ((j.factorial : ℕ) : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 (fm_spec T W M J p j hT)
  have hl : Nat.land j 1 = j % 2 := Nat.and_one_is_mod j
  unfold nN
  rw [show Nat.mod (Nat.mul (fm T W M J p j) (Nat.add (fm T W M J p j)
    (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1) (Nat.sub p 2)))))) p =
    (fm T W M J p j * (fm T W M J p j + (p - (1 + j % 2 * (p - 2))))) % p by rw [hl]; rfl]
  rw [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_add, hm]
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · rw [h, zero_mul, add_zero, Nat.cast_sub (by omega), ZMod.natCast_self]
    have : Even j := Nat.even_iff.2 h
    rw [this.neg_one_pow]
    push_cast
    ring
  · rw [h, one_mul, show p - (1 + (p - 2)) = 1 by omega]
    have : Odd j := Nat.odd_iff.2 h
    rw [this.neg_one_pow]
    push_cast
    ring

theorem good_of (T W M J n p : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i)
    (hp : p.Prime) (hp5 : 5 ≤ p) (h1 : Nat.blt (Nat.add n 1) p = true)
    (h3 : Nat.beq (w7 p (nN T W M J p (Nat.sub p (Nat.add n 1))) (Nat.shiftRight p 1)) (Nat.sub p 1) = true)
    (m : ℕ) : Nat.factorial n + 1 ≠ m ^ 2 := by
  have h1' : n + 1 < p := Nat.le_of_ble_eq_true h1
  set j := Nat.sub p (Nat.add n 1) with hj
  have hjv : j = p - (n + 1) := rfl
  have hN := cast_nN T W M J p j hT (by omega)
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with e | e
    · omega
    · exact e
  have hsh : Nat.shiftRight p 1 = (p - 1) / 2 := by
    rw [sh_div]
    omega
  have : NeZero p := ⟨by omega⟩
  have hw := w7_spec p (nN T W M J p j) (Nat.shiftRight p 1)
  rw [Nat.eq_of_beq_eq_true h3, hsh] at hw
  have he : ((nN T W M J p j : ℕ) : ZMod p) ^ ((p - 1) / 2) = -1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).2 hw
    push_cast at this
    rw [← this]
    show ((p - 1 : ℕ) : ZMod p) = -1
    rw [Nat.cast_sub (by omega), ZMod.natCast_self]
    simp
  exact crit p n j m hp (by omega) (by omega) ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)).val
    (nN T W M J p j) (by rw [ZMod.natCast_zmod_val]) (by rw [ZMod.natCast_zmod_val]; exact hN) he

/-! ## 6. The prime stream

A stream is a head prime `ph` and the packed gaps `Gp` (8 bits each, gap / 2, low first).
`sp i ph Gp` is its `i`-th element. Once `Gp = 0` the stream is constant. `sOK` checks every
element against the pools. -/

def sp (i : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun ph _ => ph)
    (fun _ ih ph Gp => ih (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8)) i

theorem sp_zero (ph Gp : ℕ) : sp 0 ph Gp = ph := rfl

theorem sp_succ (i ph Gp : ℕ) :
    sp (i + 1) ph Gp = sp i (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8) := rfl

theorem sp_const : ∀ i ph, sp i ph 0 = ph := by
  intro i
  induction i with
  | zero => intro ph; rfl
  | succ i ih =>
    intro ph
    rw [sp_succ]
    have e1 : Nat.add ph (Nat.mul 2 (Nat.land 0 255)) = ph := by
      show ph + 2 * (0 &&& 255) = ph
      simp
    have e2 : Nat.shiftRight 0 8 = 0 := by show 0 >>> 8 = 0; simp
    rw [e1, e2, ih]

def sOK (P3 P4 : ℕ) (f : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => false)
    (fun _ ih ph Gp => pOK P3 P4 ph && (Nat.beq Gp 0 ||
      ih (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8))) f

def SP (ph Gp : ℕ) : Prop := ∀ i, (sp i ph Gp).Prime ∧ 5 ≤ sp i ph Gp

theorem sOK_sound (P3 P4 : ℕ) (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true) :
    ∀ f ph Gp, sOK P3 P4 f ph Gp = true → SP ph Gp := by
  intro f
  induction f with
  | zero => intro ph Gp h; exact absurd h (by simp [sOK])
  | succ f ih =>
    intro ph Gp h
    have h' : (pOK P3 P4 ph && (Nat.beq Gp 0 ||
      sOK P3 P4 f (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8))) = true := h
    rw [Bool.and_eq_true, Bool.or_eq_true] at h'
    obtain ⟨hp, hr⟩ := h'
    have hph := pOK_sound P3 P4 h3 h4 ph hp
    intro i
    cases i with
    | zero => exact hph
    | succ i =>
      rw [sp_succ]
      rcases hr with h0 | h1
      · have hG : Gp = 0 := Nat.eq_of_beq_eq_true h0
        subst hG
        have e1 : Nat.add ph (Nat.mul 2 (Nat.land 0 255)) = ph := by
          show ph + 2 * (0 &&& 255) = ph
          simp
        have e2 : Nat.shiftRight 0 8 = 0 := by show 0 >>> 8 = 0; simp
        rw [e1, e2, sp_const]
        exact hph
      · exact ih _ _ h1 i

theorem SP_next (ph Gp : ℕ) (h : SP ph Gp) :
    SP (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8) := by
  intro i
  have := h (i + 1)
  rw [sp_succ] at this
  exact this

/-! ## 7. The walk

State: `n`, the prime stream `(ph, Gp)` (`ph` = the first prime `≥ n + 2`) and the record codes `R`
(low bits first). The code `t` (see `tsel`) selects the prime `sp t ph Gp` for `n`. The fuel is the
number of `n` still to check; at fuel `0` the walk requires `n = nE`. The body is written flat (lets,
`Bool.rec`) for kernel speed; `walk_succ` gives its meaning. -/

def wr (b : Bool) : Bool := b

/-- the record code: 2 bits `c`; `c < 3` gives `t = c`, else `t = 3 + ` the next 6 bits -/
def tsel (R : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Nat.add 3 (Nat.land (Nat.shiftRight R 2) 63)) (Nat.land R 3)
    (Nat.blt (Nat.land R 3) 3)

def rnx (R : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight R 8) (Nat.shiftRight R 2) (Nat.blt (Nat.land R 3) 3)

def adP (n ph Gp : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) ph (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.blt ph (Nat.add n 3))

def adG (n ph Gp : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) Gp (Nat.shiftRight Gp 8) (Nat.blt ph (Nat.add n 3))

theorem SP_adv (n ph Gp : ℕ) (h : SP ph Gp) : SP (adP n ph Gp) (adG n ph Gp) := by
  unfold adP adG
  cases hb : Nat.blt ph (Nat.add n 3)
  · dsimp only; exact h
  · dsimp only; exact SP_next ph Gp h

noncomputable def walk (T W M J nE : ℕ) (f : ℕ) : ℕ → ℕ → ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → Bool) (fun n _ _ _ => Nat.beq n nE)
    (fun _ ih n ph Gp R =>
      let c0 := Nat.land R 3
      let b0 := Nat.blt c0 3
      let t := Bool.rec (motive := fun _ => ℕ) (Nat.add 3 (Nat.land (Nat.shiftRight R 2) 63)) c0 b0
      let p := sp t ph Gp
      let j := Nat.sub p (Nat.add n 1)
      let fj := Bool.rec (motive := fun _ => ℕ) (lp p (Nat.sub j J) J (Nat.mod (ext T W M J J) p))
        (Nat.land (Nat.shiftRight T (Nat.mul W (Nat.sub J j))) M) (Nat.ble j J)
      Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (wr (ih (Nat.add n 1)
            (Bool.rec (motive := fun _ => ℕ) ph (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.blt ph (Nat.add n 3)))
            (Bool.rec (motive := fun _ => ℕ) Gp (Nat.shiftRight Gp 8) (Nat.blt ph (Nat.add n 3)))
            (Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight R 8) (Nat.shiftRight R 2) b0)))
          (Nat.beq (w7 p (Nat.mod (Nat.mul fj (Nat.add fj (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1)
            (Nat.sub p 2)))))) p) (Nat.shiftRight p 1)) (Nat.sub p 1)))
        (Nat.blt (Nat.add n 1) p)) f

theorem walk_zero (T W M J nE n ph Gp R : ℕ) : walk T W M J nE 0 n ph Gp R = Nat.beq n nE := rfl

theorem walk_succ (T W M J nE f n ph Gp R : ℕ) :
    walk T W M J nE (f + 1) n ph Gp R =
      Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (wr (walk T W M J nE f (Nat.add n 1) (adP n ph Gp) (adG n ph Gp) (rnx R)))
          (Nat.beq (w7 (sp (tsel R) ph Gp) (nN T W M J (sp (tsel R) ph Gp)
            (Nat.sub (sp (tsel R) ph Gp) (Nat.add n 1))) (Nat.shiftRight (sp (tsel R) ph Gp) 1))
            (Nat.sub (sp (tsel R) ph Gp) 1)))
        (Nat.blt (Nat.add n 1) (sp (tsel R) ph Gp)) := rfl

/-- `Cov A n`: no `x ∈ [A, n)` has `x! + 1` a square -/
def Cov (A n : ℕ) : Prop := ∀ x, A ≤ x → x < n → ∀ m, Nat.factorial x + 1 ≠ m ^ 2

theorem walk_sound (T W M J nE A : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) :
    ∀ (f n ph Gp R : ℕ), walk T W M J nE f n ph Gp R = true → SP ph Gp → Cov A n → Cov A nE := by
  intro f
  induction f with
  | zero =>
    intro n ph Gp R h _ hC
    rw [walk_zero] at h
    rw [← Nat.eq_of_beq_eq_true h]
    exact hC
  | succ f ih =>
    intro n ph Gp R h hS hC
    rw [walk_succ] at h
    cases h1 : Nat.blt (Nat.add n 1) (sp (tsel R) ph Gp)
    · rw [h1] at h; dsimp only at h; exact absurd h (by decide)
    rw [h1] at h; dsimp only at h
    cases h3 : Nat.beq (w7 (sp (tsel R) ph Gp) (nN T W M J (sp (tsel R) ph Gp)
          (Nat.sub (sp (tsel R) ph Gp) (Nat.add n 1))) (Nat.shiftRight (sp (tsel R) ph Gp) 1))
          (Nat.sub (sp (tsel R) ph Gp) 1)
    · rw [h3] at h; dsimp only at h; exact absurd h (by decide)
    rw [h3] at h; dsimp only at h
    have hw : walk T W M J nE f (Nat.add n 1) (adP n ph Gp) (adG n ph Gp) (rnx R) = true := h
    refine ih _ _ _ _ hw (SP_adv n ph Gp hS) ?_
    intro x hx1 hx2 m
    by_cases hxn : x < n
    · exact hC x hx1 hxn m
    · have hxe : x = n := by
        have : x < n + 1 := hx2
        omega
      subst hxe
      exact good_of T W M J x _ hT (hS _).1 (hS _).2 h1 h3 m

/-- one sub-range: the prime stream passes the pools and the walk reaches `nE` -/
noncomputable def sub (P3 P4 T W M J nE f n ph Gp fs R : ℕ) : Bool :=
  sOK P3 P4 fs ph Gp && walk T W M J nE f n ph Gp R

theorem sub_sound (P3 P4 T W M J nE A f n ph Gp fs R : ℕ)
    (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true)
    (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i)
    (h : sub P3 P4 T W M J nE f n ph Gp fs R = true) (hC : Cov A n) : Cov A nE := by
  unfold sub at h
  rw [Bool.and_eq_true] at h
  exact walk_sound T W M J nE A hT f n ph Gp R h.2 (sOK_sound P3 P4 h3 h4 fs ph Gp h.1) hC

theorem cov_init (A : ℕ) : Cov A A := fun x h1 h2 => absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)

theorem tab_all (T W M J : ℕ) (h : tabOK T W M J (J + 1) 0 1 = true) :
    ∀ i, i ≤ J → ext T W M J i = Nat.factorial i := by
  intro i hi
  exact tabOK_sound T W M J (J + 1) 0 (by simpa using h) i (by omega) (by omega)

/-- assemble a big number from 8192-bit groups, low group first -/
def asm (L : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun a _ ih => Nat.lor a (Nat.shiftLeft ih 8192)) L

end BRFrame

namespace BRData

def TB : ℕ := BRFrame.mkT 1680 256 0 1 0

def MM : ℕ := Nat.sub (Nat.shiftLeft 1 1680) 1

theorem TOK : BRFrame.tabOK TB 1680 MM 255 256 0 1 = true := by decide +kernel

theorem TAB : ∀ i, i ≤ 255 → BRFrame.ext TB 1680 MM 255 i = Nat.factorial i :=
  BRFrame.tab_all TB 1680 MM 255 TOK

/-- the product of the primes up to 181 -/
def P3 : ℕ := 0x30e06b35ee39cf75358315a5c3b9b2bdd2e46e25fd10a14382537a2e71312

/-- the product of the primes up to 32000, in 8192-bit groups -/
def P4 : ℕ := BRFrame.asm [
  0xdf0c850baeddb2128ac9d0fd36dd0ec2f329ef90aca3308ae6b7bcedec1424921497fc345111e60cc412113537268a736f809fc9cefc2bcbe959a57ecf6fcdc7dc216df46f82fa5bf3720c4270cf6fb13e1dcf489d98985e4f734ee9fac8505c106eb7b2acdb6bb26b79b9cd02729d2a2b215b45d1ad39b752020674f4f03993d6c7a96c9df2c43cdd5fcdd4a2a82b5082c3e0eab548cededa2cc10cfb2c34e6f98c290160b64fdf83e7d3438e6077c84a97d92b85d47ac7b128a35167b6e0531f91938128b16ed40b0ea8ed276a4a879f7c745e779c2215fa0572e7a15cae72ee309c077cfb5b3d707818405d883f07d24cd50cd5cefb61fd23ae30b49766951623101af6e194dae9d45749c5926504c31b2e31d16b3a1d8d8f628e30e1137c5dd8637ac50c416fb56e780354d53f83146505e0b75b3fd791dfb6d1cccdf46dd3bacd8c80998bafeec517c181f3bb39e1a7ff75b63960e7e4fbfa4ab3cd18f8673b3d211d62f5e0b3e98f4fcf16bc36e8d7000957b714c4798645de1678e06a21c7cc25ca8fd857afcda85428c1cff131cba807766664cd1ef92b24719ad71a1cacc089d80d1baf2446d3f91edab2290690b4fb849083f3506e79ef43443cfe351c5874753757cdb387af230e22804870783e587646125c93d5e22899c55a15ce29a46aa788de770abed396e6fa35fc451018422e12cda42c1968eb0b94f01da5b9943508ea2fe4ba6651d5d47287366890f2cd535e3789780c5933d6df7e974200cef40380b365f780703c6c344beeb37d043d1ef50ebe5b4b1dc45ace9088eb5474968a0e3305d300ae7a40322ab01357e0cffcf44216a95c444ff2a19bac8a80242e5b642615b266fa3b82e4ebec98b03bd5f61703e03d249324888f88edca090f5ed1243e0a4675f6ae3953d13092b10e09246ac59dc44eba77e164dbfe0f4949818965554093616dc9e4d28ec2f4206870ee44b9ad38fba67c42730b4845e2204f42dcb968564cf342d81da1dbbcb2ad1f705abde27272ca6eb434e635441102a00bb1b3837369200971d33813d146a5507c16e5102a5474ae182d25b8f97aee76e787fb717b4826f264800d01b229407e10b46c31d717cace03707e9813842dde7b9c675f84a599ec1ee76abcbcd5643683142b3af9a5e3ba165a9c8a2d3a8d31de317adde8d146dae44c42d3d79b56996c6c55111ea3f81174d232c5ae8bcf0f11585f68cb32a6395e58907339157f0717bc3ea165222c9ec5363162cf78432b92d4ae5025439cbe242ad10e1460f96a3b9257bb1a9075a34866508f80116c20e59d9ef0bcc790262003e760d1d5a97248b955f6cc61eab2893f5cb8e57f2f293c308165efec92b10c382c1a7f4d7b6b32691a1b62141c02811f4b3027674bebab643b34a70f166e082f1a3489b265b5b1fee25e582b1b076210fe9a,
  0xea98014cae2ac4237f4b4213a735cb3415a1380744196e3371ef349273475b1a9a19eea2b2d83e892b4404ffc9ec8f00c804866f9a9ce72904a292c8101dcfff2039576180f44def879add63b1eccb590677693cae9f49dbf554c6ceba32faf6e84616a64ecc2681a2c895e1090378b6222b56e1bd9cb731fa2064f7b7f066b45169170ba0d08741bd1b0820d77238b47918f994c8aced205746fc0ff5ddd8cf95dd8ef62dd050286266519e45e40e5b2950b8b223c07f101ce162963018ecebd501267eaddb02f56ee6b654257d20d3bf13f73db708520ed0117af6564bb8b0a469856a8cc3e2cae84a242db11e2b060f957bfdc5baa0d4c74a319342609401e3be3e2cf7e1993561e8784857ff0965514a4a9f7a10dcbb1fea1c8cf72786bf6e32594aa1d4908db83d4dfb1c3f8cd9d7a4aa673346618dca07b597d1815974f7e7e86e6d40001b0442574f4404912ee91e38bd7d52aa3eb4ba0fbd5446f731b1baa64f5d05d16a29f33c5cf42cf1f8c2f1d0f96b9a325944e8f02b0169806f2efa153ceefd95679ff923ecc80ceafb98996c16305b5e644d2071399cb7883f6b8a85be82455a9824ef5c3288e149fd62ecee29447798e1f5ea7d3919c51b567ea37288bbefe5b6d943b1edeccad5d4a1284aeddf22256e16e5017fe48dda91d4a4172047b9b6ebdbb35f04afab8a3534b41b758159b035c092cc36876c6db744cdc4558288c5ada4a7c4ca4ef963e05eb3b79ee9f2ba92cca910e4fe4419e33cd12dbd87527274732251e53c0c447842cca8504abf89fb2a0fe66269142a99315d9cfd1cb18ff00a8c0cc9b7d21e6b2d9bba36823cae88b84340801e5c81472d1211357bf791b4b9a83cb8f885a19b4d93e68561301fa92d04eac64892047c44106b572731bc2bc586f7d428463bf12880ddf84b9bcb8b75d18f68f07b2d3a4529f33c265efaa9046e94f310aa9a47d70bf8cca38f0a707a6ce8c2756003dc094a30edb3a17ef3aa4894be8e5d72e22421f097677b90ef6274cb0fe493550d58529e9b9331d11bb641d336d163489ce32364bdf6ed4b327e5a56409b1e276f1ed03f5afc4b1f1eb46f50ea2bd818b6ce560fcf4033323b7f46aab313f4bc2688a9e8ccc1545c5c811b34d48d14308a334a169c2016d94e11129100571fa1dd1c841f5a7bfccbabbc545dba69de8cd04f05f4ad32d476559836d35aca9a7381fa618e0c7e7855e9cd829a0cabdbe9e3c01746e3ae03c2e18f4aa76ef419e3de8bfe4b21500785d9b6964477b8a840ec2cdc45f3227e280e2c5f8f6c6a26c3881003f03b9c89575763154d252dc974ecf290538b9105fcea649307d65a15a817627084c27089384b6073f28023d245a2d78437adc9909abf78ae77d00006f6386c40a33acffa01cdf3667bf58b5a38e6502cd21718fca0d04aeabb5d7635e4b4,
  0x1728b345ae1d105890be726995db87cb8d8643422401f2b9d4fd947140af5fdd89523ad14c14787386bde21dc9610b22e07e931ba28009eb69a71e1cfbc0df11d42c4526b66824c91f442c5636d120007e4d24e3bad931045a7365deef650235aae6a3996d4288b7a45118f689202f6eb7631f39ccfe3ed30df63f6dfa1eaea9abcfc0fbb1889d08158387786d5babb4711aeca73bc3b3e7f510660123273125559e32ae86789b3eea846b65e518bd1b82f86a68b6622dee93c66f28b57bb32c66c334eb0e4e18da04a01e1458f10bfb1b91ada31354048151dc2f7b5e1d35cd094790b3a592983b79c98f2002554d6ac0753e09d4c95de4b0a2dc4af58bc18ba1c404b3cf1f6f5e6353388ba00542736dafb6b3890ed4eb1aa021baa0a1027503756833e069161f3b5df47575a40f2ed8ae5cf84444b7fb646bd1ccb521788b5d39ee4e9492f45b5052f2f8d973d0e798ef2bea1edb9884c1f5ad82ff9f2da775d8c1abba03a5c92ff2c3ccc31a8afb22947e1d06745a05cf02d819e21c1b9eeb81560ef0e999cbf56d4bdb20ee9ae7563555bafaaa67efb0cb235529236a4abc3bbed82dcdf54e45470f179f2174157be3c2cad7e76c7b9fa12a3cedcea2a33cdb5facb5327aead5e2ee441ebfe4a944440623d53d4bdb3e5fa4e7f03a0f3ce18b1b2507fe33b65c49534c5ef0e31577cb2e11c80dd4827e40e09ce1cef2aa8a0b6d04973a6431ea0e721a266ed55b1d51682cf24816a6ef7c28d315fd2c4efd94b46caeb7fa54aa9b6e0b0061cbdd73b551b7a80783e8e600f9a9162f2199788c98a444e28ebb46b57043028fe6c474260640a987cbb7babaf34191506f6a669df1064bb5d3a4522f3706dd1a5615ca291b33cdcc418266d52fda48d187a9bd0c40513361bd5652581c1b2ab80879f9b9c802787745e17a9791fe2d94f2bbbf9e8bd08fed5d2fc21b095a1d18135390d99ffac0dba4a55c77a4ccdef9c1b63ab95770f5296498093b9806389530270a161a78b2759215b5156f0b69960117f858d201d20305aac1d8936d3d8c70293ead432613a327abd5d6b7ec767a694bccfceffb2f505bb0e8cf019e8ba6c25ba9c8a66d8ab729be0c889e5c33b9b003a2777b2ee1a7f1ac50a0b600f9df13abc417f92e56a627fec3318cfec09c3ce8ed11cd38beecc9fe62800f28b554bbb032d54ec3265b9510da2763ffbffa465ebba8541e162029eb43803ead99cc036eac2906e2508acfd0b87815960f33f1250c4c93c84772fcf343e319166a963b9438080e93537495f38e222f30b9388f432d57e061f06db832fc76cd7c2246cdbc725791eedbb0f020e4518bb711c9947fd13da39b34eeaa20b783fda7c7fd6bb5a6bfc5ae0aac9be0260efd746edb56cbad7adf1f59b4ef5590ebf5dc901afac752539f95fa616c0121643f4021b923b,
  0x3c458fee709566842171df4fdf91d1866173d1b733c3309816fb19e69ff4d6644f481709bd1680e21b432a184cfcde4bd4f9b43742cb46b2f3ffd58b5ca10366aa342a9454eedf37ffe61d5b7b01c242438d0aa617697b258e4b6e05f86953963e9b1fb21af5ca4ee94189cb1a9899de56581900c1cb81777ee13638ac508ece1dd9c8bf76060130ee98831d9c1fb6548e12387a276ccb9a1faf40a2ee45223252152bd2949b6b5a7ee3ed5c2879d3abcd1a50c7fafe7d7464053500e063887b01e11ff8f5c27000443e192c9ec6511816a4ef4f6c73c364b4b4e11e4b0f6f2bbe6941fc1002d33c2ea0d80d7c2e37e70d298651f344f10070630a47cd0f686b749590c52fe4333d58a21b210eb744d4e7df8a6d79ce7137a4ba9425114e86d112ff16e899cd2041bb3781489ce56232fa4de91c7ae07bd635bf1f0e554e20163b0a43ed81ab1095811abc702564c76b49adcbc3f5264e74823a695e1847b559021d6babbe9d6989a4eb4d5ff4dff6de9169bddcac984a8bf3d9f653c91cd620b187bdf4e086e2cff33827ccf543d72f80d31c0cfa9b0ec3344ac92fd84b3a3671009f4929fca57466981b49b59806ec5b95115c1d11b21099d94bf85ef0b7bdfdcf30ef86cc521e5a4d267c48da55d3b81706d40dd2e26357d7c865da72c94fd723e3cd37aab7bc2e17c9ae1368ca36ae70f1bb5432a861bc0a79709b81f23807835b1bd97dd958f89f546ca0e74a4d91f2231841b97abae7f63d1dfa52d8d2ecbeb25f730e389347efe4030f78f44b1349e216256ce33d6dcbfd14f9b722f85a32cfcc28fb734de661fad78e2c6065b1a970274a9d4c4b238078e5ef2675620ebe8efc5874a7560f17ae9186eba32895c80e9ab5a9367ceaab065805a41b340cf88a6316b15964530bdee05e98635f268eb9aefe7c81d872c1f52d89472c117d4ead5cabd5874110e0a849337c38acfc60a476b55091afdb9c59ea0200bc2c98cb8fafcdb89a5593e6169294a2d7ad79b4d4bd02449d332f5f101f8a95a668b28a9aa5d4ee6f63265932a22b93e6b08c3cb4ce49b2114839ae8d669db30e78886393dfa8e92535a3232ce2d3b388df674137547d46af3ac76aa08a3962b010a924cecef13be7fc1ee1f857c0c1b148c8350206d93cc1c26bdf2f2083e0632187a7170294c132c8c96452ed414567d17115f3d810463dc5845b0e4b2150676860213d04f9e6b1ee1530faab6ee6281c815dc26cd93cc02c8ed58742168b4bcfe102c25dcf152f8c36ededf5c24b756d43201d572e5ec91e785f50244eac7936a17ebe3e80d537492d9ddbfbc53ed3828000ae06dd1478f12304cfaeaf8b594901c5010f524a109d67422dcf2e00b03dddfcb9ee1060b28f0156ff8707686b109c780e98ff3732bd116d2f70c96ca688419b65cdc52070b6929bfff088a3be5f,
  0x33fb30670ccc9d9161ee291159b243d56af86e6c0d29675ffa2c459c998f0c513dd30d097fc73d45684ecd2c87d420a96eddb72894cfb6b134d8599ab23ca2ce27ef0706a741bda8807b24ea39ef3e5da8774e5f2219c3cbb5573bccfa96c4c5f9b3a11dd2cc735f288dc3a82281b63255a99bc8a5e1c55002df7fda7afac36a1d276383158d287c2a4db62276a331b0b14239ceb7b72b9229337e828e76bd3b13316c1bc98279fb890663222d6f91722909d219a67282cad6eed54326f5e3ea9b7aa50d70e0e9caeec704373d0bf36057bfed71c9e794676fcf07be1e1c0ad66e7790c09f157620dfca3e522db1ac9e18ff6aa4f5ee9f682e9b4a56211d5d51aa3fb19b25926b06393d3c4c47ae87ed8c52d4f19f54ba73ad3fa32cc3da4857c98d0fa5363a46671d532322b398f90422bd732d02d272ed70fbfd0cf7be141b677000847b96d192296c900eda94ea4023fdf00bf2e7a6a9381d832e4e1189a35136b481179ba243c5661a527b140c93d9997eb066a8554bb1b07ac04974f076092dfc159a231f26ff9e7fec54a1a4afc94c723cbc812012373c707e0c81c5783247e3416ec84e3a4aa240527a9339adade0e966d9acc3a1867b2e62b4ab1f43d342508113196ac649cf973d1f98067ebe3662022398d0617ba378bc09596a6403112db6adcca330e099daa38cf9f921c1459c9f97d4be291cb38007fc34a018edb5af08589e98b71ab0e99acfda859889c4a0360109261ff6e40c85327af396767fdac713adfe8caaec684bbcab3fea995f660af05b974c5ba6ebf52d1f8e2b31117cb8faf93a0e939836d3b6af25604d7d5b4f6e144a0485d0c5b5400d4713de63a2736fdbbd20ebb835cc9591b48e10764f4744729730117cf94bd42e70f0f2e86b609f59053a2f94f83d2c855f49bc0563edc62683301a6f1af059fbedbfcf1769c0e1fe4ce07b65de8b71ade682636d0abde0bd94cdde2e1cef86e715d495cddfcdf0e420d7fc6c7b523f6cc2a181df5c50d713f7142e22812e9b36d83d5c41a754fe1e2243d67bcc372a7bc1f7b3cd66155a6d68f2d78535f6ead61180b20a9b7345e87ee56618dcbe69453bfb5db4ed7337f698e5b98735b83d30c6b59ca226c04df477bae76bb50da3ba91f4f324c51588c99d2b8258edfe273d77883d519f5059f50178c73612660f88af6f622035e53bb5cb8421128833d0e2963696885b2672976bc22bdef66a3f79a1eeb5745b266abaae035f56d7da1f92773d588519cfb671cf7f840b8c0eece8eaafaa8cdc7bd8e95db47b86de2f99a5c118b3d336c0cf108f8b13199d11f183c61a0e7fe7d42a609536ad880d22ef9acd6e7a26f94aa1aaf1cddea57ca24edf80e18bb54dc9142b3f9de36aa66add5c83fa9a1b3827de04c3ac9a362fe20443937a0dc21250e8d6183c51a530b2ff77d24,
  0x556d7e991792de0f391465729fa66f7cb4cd30e9aeda0d488686bbeaccac9ce166df07cb523e600a3b36496464fd6e277847eea66bbfbbda8d20d01bd4dac96841254b0ff6c61a90385a3239eaab5887ebdd5a6bcf72691ab6644a094162fe467ce8c72e372883ce54ca28eb67362b5b180ca57cfc027037004145ac514e280b4249af145522f74ad3b0f6eb124e1ba8e994e4ddc0dbdd8cf3f80b42f338206e5313438d9856c4af110573fa215009a4a69f506da8f1fc03695d08ba2ea83ba5b5a7e289910d1ded13d31f5810300e41bc97799d709db61c06dd64bac664891f71d68e45800f73cda9d18f19015497d2048b5193e343f89677fa0fc96fac78929ca8a69f8eb195e7705bb820a2c1d044b922b3b6cd5504ff78a3cbededfb7f1ddaa0ed0869a39884c6f13673cd0cf984a8bfdb025a3bb1af56f4031d5d5b37016db05548dedce76724a7fd52bfdec469e49a2080da2082e93fb0e7b8984d7515b69b3237649436f27c00b00035ef33f41f982ea205940153bfc318e858a5987c952474bca14aac913b1b4ab909216ee44902547a558dee848dd30c0c77b4d2794e7b6b4757e9816025934a0ca36430fe238884e8e64fadbb0d3bcaba4a39af73014f4c5e97e70e5de24c3fd9d2783b3a430158d1a672220b22612a92cf52e32121f8a5aa83d3d87fcfed7751c93bad78d5787354ebe4574d159fff7971b47dc3e0bb5c71f97a51f75996eb949d7565f8e6a18beb27aab1db5b87394d2b1525140e3493920f7b50ea878a9be48bb9e59ffc3746855d8bdf084cf0ce93a39f6f14d5b3a7d76372b40e5870bd37b3449fe5689e]

theorem P3OK : BRFrame.chk6 P3 30 = true := by decide +kernel

theorem P4OK : BRFrame.chk6 P4 5333 = true := by decide +kernel

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 46943700 1250 46942450 46942459
    0x40b0a09050d030c090602010e03030112140d0c02040c08100905070908010608010e07120b04020904081204030c0b0105030304230105070f080d050f15010807052101050f060c0d0e 78
    0x20503010480400000d80e000d0402d440024002016400180c488801c99014004580c10940100340040300401564116500300a16071202030035840c0a800389824bc1004181030312900b901c0c0c5072860341c000c556541c454025541008034010a107400c681510044075400030640a0900800100c00c20703a0003554010312a00c0c02103c1c03191140100b070300392400c0d58003501c0305a440e50f4800c812500b0500c48400100604041c03030324000c0c041ea03200c100c110801400030384a84a603000180500902c8000c40d032000c0b080d403032030a201e403030701f40f40150044242c9481504e40d003203268004582401c000040700c085c0c0720210803600103482c0f42c1541da04c0d8907100e01380850400c03100f40150000105108802a40c46215000d030a0300e9420420b01d4408407034009056107088a2f1010500000425034a1200c600a1003031070039110316541c51209403524415424a103580711821044101883e8403aa500c506a4500b100c0810611654404003c03240c014046811569000300709250b410601452001d01ca0160143c0b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 46944950 1250 46943700 46943711
    0x206071109181b061608040312030b09010923130606090c0c1b0e0f0103110609060409020903280302010e120405120c03011a01080714030c130f080f0609010e06040b0a 73
    0x40d02d5900000344800485041074040f1f814030130010002d110030070480032803a0030001130858030700254000380306200c1e0f040c0c1c0a540b030280e131503c6507046103800034420208011aa40d401c01212465207801c0c451802d5034214035120001c0341080e030a018213076003a05240d9036101c400c4600d48580d589034141001c4440c1e4182c800100017030400803251408d00c55000420108150762440c01c00310440c00c0300c2403009101b042c00300040c26250703a40c402910255080b1602c01a210b810720000300c0d103006547c1c00013000002c911342155030703606031309000d00f201c3d07920a030b0091010801e604441c03551090a0360242c903c100342404103100c942002000c1c00781d451159402c58980568400100f805c461080d5074404800010b15111100d550300503408580110706482c00e1180350f010350b0307030115143c0400303040310003030030350014403800c44501003d2800c000e08440c0794508000ca80c1e03404419610382d5050900c402c1ca00070040040d003001c50601c1001200c000d40809003407140d45075600c001c3c454000502104100e0340d44c4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 46946200 1250 46944950 46944967
    0x170604020c0a0212010516030506010c03050715110406090504090f06050601050f030f0601201c050403050102040905010f060504031a071101020d050601110d17130206071109181b06 79
    0x401509040310840c400000309420147d00880c0040803c10b003510606007048144510399a00c04128007a482d01481c2580e12107030f0b40c4c500081d0501403c0406500c03031f81003040c02600181c0c01c030b00401c00c4071501d4490481d46541c510908c8180d45a502000e0300c01c650308031707450b00800c0180c0c104c1503102d41c0500d0070f94039203c9001740748c00f4640c20588a041c8000584030400ca03081d604000110040e510901d400d1600b101c041500a68031501008510102032001003144605070043e0156030186900400075900c40f0340340c440c1c2000800c0309100d8480c50310440c11002400a0044007110240d03908880d00c0940020303201102d86405c8000fa210f401040412580b44000003001c0c0302600411045200110745410700c0000106600304000cbc80c1d0b9900e400441440c42000c0d00080306182c40965518041c5541e680c01141c2086c44264070006500500002502c01c20040b00c210b0366000e074039080322804903030b0b01c0701805c4804c920600002c0324000d92100302840c00841d4000341c1010f88281c010103591415040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 46947450 1250 46946200 46946209
    0x12080a0e0303041d06010e030a0f050f0f010504050705040506010f0c0302070315050405010509060c07031d06040303050c060907060e06090d051009170a091a04082b170604020c0a02 79
    0x107a00201003801884c00070200c0d00d20001c0b001e40c00c1042440d11700c000047d40c40c0065100c420b04d0000826040e40742c08864104001400200c00413400c03001502c00f440b480000c1a07000e880102d40480e0309028154020460303203414807802d8054001a901c82e8018441c00405a48085070751030207a0035880f031544000005044624520107140c040c00c8041864201807605c1400d486d0090a00e50481c2c01500801c56212600c8054070321050b09440c2c68007200303020100401e03200c0e983c0515650041030014010003410b4000004080c0b0642c200300700c0d600c665074152107503210000b901600300002d851220075589490000c0140c50740c00c000402408000080350b5031140303001481d10001c4040f0352948805420301019000300380d01c0040391030072031380380860300c42d070003401051f1700c1c041c40340182581d018107c14804800d0a907405003a012044138008010101c1003a1185405201d08617600e100741413402d0500d100311401660b4510810300c01c1181c1d21881c0801000c0d402400d130300c070300324800e0141c02d0015030b48 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 46948700 1250 46947450 46947457
    0x20618040f021c0b01080604090201090506071110020d0816031b020f010f020304080706180501051f0503011a151c020d0b0d0b04020409031b0302060601030507030612080a0e0303 78
    0x2220314005980e00010b40c1e820000380d04203603516243c245420820344da00c0e40c00c80d200d240d00044c1101c00003080005071006943e003982c10380050707410041c0410720500708484003030b1004c2c400c0c504503015452904140002c0342e44040c60180747c2d00040030600815007003400c2d02d6014003012080c5c1404104a004041160b5003500b00390080d80c0141d10001c603003c500c010a1090340080d01c10660150314626003034503441d920f445001d200905060350f5071a00c0d0070044900207c4a100d9621a00038405824080700c00511034290b003581e07015103410b4860004082c6814441d4110302c005d900799401103e1140401c01c8200c0303044c0b2804080543c0c0030441e20020301c01c070490a06d0f440035407810050312184040142400c031449084200d014041d80103090010503201e850007540140e0446012901100c180740c100c40c9000341d010b9040240000c4114039003015008100343c1e10918080c2d80402295680032003c5050710807901c47d000203004412181d01c041948040104500010f80c102015080161800f181c1303107030f1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 46949950 1250 46948700 46948721
    0xf0d0f1d0709061203090b0703021e0307050c06030702060f0606130602030c0105100e01031e0b010605030403080609060a0303050f120106020a0c15210b04020a211802061804 76
    0x20886a8103100e40301807442407601404c80125030140c807030040d50707000e0b00401181c0512200c114000c5058070030503108104152500c20101c290170404860701310342d943d60760480002180c45000704940324889082c0007094a101c0c2005178010121078550f909036483d001c2d0058103090308400b04226107060704049051b190000c140550042d552600c01f8007090b0b08452000d4548216102030210800c001d05207681154156500400d862a130880040c0b100845c010394a4001040700301090000624250440c02a41c8202d00940301d00c51155124400c1118030f040848080b0b80c014581881800480e110f4800781c03242604d000c1d180c0f454500a2080e0200c40e403803d0f441a40180d00c600051400c11074400c000310f005114100c07180f2003500b101d141c0640306075000c010325074200500213090b00c42c0b4185a08203005542c4040d000319550601c04030300a1480c0031064952841c00202c1842007800c014611540544144580b0006c2903104160308024065000c60f2031300f4860310f480540015503036502d206000c0e030f51 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 46951200 1250 46949950 46949953
    0x3020306090a0204050907050303031801060909060207050d03050f1b250c080d020c040506042315060309030a0c02060c010c09030b010e07080c0c0f01020706020405150f0d0f1d 77
    0x10a02c0344108070985e40b000744008901d80141c1810801601c000060b41e030000c5800d800031603000592160240184a10340c081121203013054400000d1000c10380c02403505601400c162841c01915050980940c4c40542d240020303011840002819513024060006200080c46042868020f90030140f010301c400c0e41090061010410f0141020400b070b405c074030320085c180c46000c2c1c400180600c40203034544030800030160281361500700042c07456990b50300011546000c0101c20b541010a80c18117003082074100c03002d00910006454075621491b080060768882c0540000841c6811499041243c44a03202003049801c8501800040003c04081c00f60061030002941d40d0984d851441c20260000b91041c2d106a04010a401c203200b03000b5030120b401035000c4aa4480030382d40701c200c0b2800f01e2621071a8601d0340019480450030900300000c540040c0119074040f03a420b0050394a04100315000d1040310407140818404010b00766080c1c1140d0440007810301e01140004001546200090f0780b00c1661355400d549 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 46952450 1250 46951200 46951213
    0x2030903090406150f081005031005090c01020a02060301030807020f09010905041209060206060118080f0a020310050702060708040204090b0103080a1106072313060c030206060102060613050403090302030609 91
    0x103401d0901c01d4000425610304060006400c5010280c111844104200100b200b0f20f0000b41f524004040510020a405402c49102100840c0240d0040606440b0303082d42d400391030760303812043d03100103892580e01d6001070074545903034615900c110040d841000d08980107041100022510b640305591715000303102e91180444e032468a031610414824a0284ac3c0040c010059801c0c00170550008041c0e41c4030700d0a0802c00300a0080c00385040c055515039015260740e1080702c25860790154041500000640300b0f8045455605e407800c115815130390100d42540c01603005200043c181841400c80503046400a040050a4505030329440c0841900341c00503a44c50000150b201182c6c0ea01419012540300e0300400b5002d5030814940081c00c1400c5544900810030070300020342d44250420044070510140d0f025010f50a076525100a40340c80c070f41203415000750182c01c00142c03807075001007041407044400030305450040711594481c000415000d84240d0030050751401c04070040c2ca0403c0660300030224640207040 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 46953700 1250 46952450 46952467
    0x6090e010f0e182b02070b03090c0d0f0b07080601110c0a0b09060412140615030705130e0105070e1011120a110303010605071502030601121a0402030903 67
    0x450a0607840103294000c15034080000703151600382c55400c5204000c1c0410201c80e1030041d43e1501e50095000e21001c4210040079081c00520904100604004d80a59203003c1da200390007180303400120b586e06116001400e211b101480c0000740300042902c070350a500c045061640300c0c00b00d441c07421034488012a150100740f180c41e40c2c004094102038026040240f042c2c943da0341c0440e641c03182074420700d8090708020480e440540c1d500000d4130041c00c00382c81c15042e0b00e1654204002c03400c03c03e228049181c0240320100303684c540141d903440300c8140b02800410101d0b150005001c81e0345001d1904e0f940c0d2541d0b0394100c0d14a42001c2c05014009c0e001c60703840c02c2c140d80c20081003100d205c03032428062080c48a08070000050a0001c200041000450a0001d032101d440683c2550303004940f0301c0f1000030780800000402c0b00c0790803030003901c0300502510058410b40e4440c0c50f40c5c02244800d031000c1c0d01107414294034460308407c030b4004500e94440c0c205805040390102c000304050f03803c155440704040e08082043c54 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 46954950 1250 46953700 46953719
    0x1103040b1215040903020a020108060a030807050606040c18031509060e07090e0d17090c0a030b1509040206070b040503090613090c02010c090905060301060b0a030e070b040501020d20070609 83
    0x424100b007150104500d140f19034019546200355172000303043c4410440050b5845d582c45aa03c001103401085d201d5507442903107001038507100125242c5100302c0c035041981545a11898515403540652085400d0301400c544903071850000c0c01410f43c10305078452490301e0001d0018021500c8540f6000d0090100300d00b800d240105844503400a40320340d51090707020000c10b0364810140d410401f500400c010705d039100d0055580c1800c110300d84480c2c0040844800004000d4a8410588105645040c001c40500c0c50300c1007104990042c1e42c0079600c4802808900302140c03000d40d485421510490849103885009008074843da00301c801404e0103c0c140030410450a151801030410b4000d891008005403407500f44040e05030401805000702036070b5100001480d13038900350700940c0649140020705807604171441004000c1c1546014115143c080c207500010520405001d65060341d405801820350510007020031291524103440700000d65248819040603004180700d01c1c40501070b107941e8219007a0920310142c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 46956200 1250 46954950 46954981
    0x41e0b090d050315010e04020f0406051c02070c0e090c280b09010507120e04020706020403060f0b130c0201140103080408070f03210e0a0b04050406080a050307031103040b12 76
    0x1007080c00410420072401c4210902c58a2003040700b402d01c80c01c10118600420000d008030307010580e016400160204142d900240075040c5064000c001eaa0015102a0788030300303a0052109c002c15089008900f800218070311134a0030b51110142040710013100d049030001b21070f604d8901c4600c0c0750034840c449410070981200401006802c48206403407400c0701c0d04000170302602c10350501070450502016413404131449034040d4110610000e0095440d400142420740096210b4402110321500e0540648072203101400703603003100c240040a91000070000040c15014043c440318250841d50f8030214440051000d803142400b03540181c403459215030a24084500e0484d081e000b410b040b00710f0243c100009268200b200a07004007400300f81085411006050741c22f0301c403000410707074010390640c008543c0c640030001030022500101d0782807101c1540c07002d50310b4890342c3e0440b014280307810412001300032078011041e51800c0304001080700e2806945100380e03403072034000d80718141544100400f0b20100308002c10a9 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 46957450 1250 46956200 46956223
    0x150a030c020705090606030601170f01052b1407030501110c060105180705070305250213091109150607050f120c150711010609020301080607030b1305041e0b09 70
    0x50101c2c9060000003101c400000701400c1c40b4250010014946074454841100318842c2e07644541c1c0305047c0490b603148405002d015017030058601c100d04080c0da814030451101079051100070041001c08076280c4d09001c640c4411043d2691140040c000300080c03091080c07154076102c040c1c51644480055141508010041c1c0c002d40c810b0140c41c0003101c802a604080135041600e600f0019540c02c02c1c1d1405403482c1c064182c1c071810000805102d0816460410280c0c60364510855052100c84010042803040b203265460240c1500c9968644410700c0c1400305029030030000c0001c0211080c1100400900c00e03a001120884036030b003101031010000e290420100d204507201c1c405031030510490345040c56403280e10b40308602c45480c49801084201d40a82c06070006190703000d000b801013a40710318404010703500a00c11b1079007a1085100040340207201784545600e94400801c41281042450040c2001d04005030040c0c0d038910501c1d00003a0b034520207018200381d4900c2041e6030724035450440358090070324204188 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 46958700 1250 46957450 46957453
    0x15010504050c040b0d0b0a0608091011090d140118060c02062202010c05120a02070b0306010906180506030420010c050c0d0302071203050c0607020d0207051509150a030c02 75
    0x1400350302c000b6034043d5002c1e030f196002007640328140c072a404400b90022030300b07903908400c0c4280c000c540b40b41d004101c5889504424103c48081580880300030440303601c05841e039000c030410300c451002842c141040502241c020b440701e201350300c0d0310790740c26003168105213661007005e100d0b15005040000c24011800c0207601c0d400030b060b1a16010b54201010282d42a003075001c0781d0301100c681c0c00c5a000d01004944250070004880c00c2c0300f4100c0900d8251340c40701881c81c02501c030300040011500041c1040b02c4c8100c00694980381090724008065031001da910021100d103000c10840841c8640b22000036510503401083c4840c13441410408007071815840c182c410f810480c5998042000c03410020352000c0e00b000680b450121044a81001c0742082000e401404d00090050030b180103040c1d0007406020009800819140151220301c0240c1c0d4030708241d9040700142c0c01c540c4080285d0701e01648226500d20707107140400c1c6040c01c00000696102d41d103a81103207040304085804400c41e58184a00300883e00c6600 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 46959950 1250 46958700 46958711
    0x60e011b03060b0703030b13110d0605090402060910051207050909090102090f120703050613020405010e090709020a09030203030d0507120605060f0c1c0c0b070305012d0b040815010504 81
    0x3c030060344900c10b600303001d0145138442c0940e000710745585545112201603040c08228014104e0350b004010b03070280583c80d1480c1e0900402041074035200381c070f042c007465004217040c7c030300380c20501801030300700b4259418010302c04144540c07800c078844025010312a42403941c50b90b554889070000c101d04410050007442e80c507031050106e2702881d12402d010703611201c4120b407100038440c000041c10b49407198a400c01001c5000f54810b105416111121400d2024402c1ba011b00c840ea03210b01584608020845550b11039500c10101046448400c1d0f004107850540d81c41c184c11140d80700c3c1c0100c0d186a10044e03016028030b559008000c100c076480340702c070083c511061a05002c1e061a03c000640d1500a4002c001c0440c0c00005a02401e03190804c00c5804904015854800615072114094401600c0190a542d0b0103034010010308854400d100d2a4148e5a00e0740654400d201d51545c114844900c095154440c400c41a5002c1003240440000c0d1006140380b500074040e50041c181741150640040c6d00c441d01035824030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 46961200 1250 46959950 46959959
    0x5010605070f0804120308012112030c14070f060e010c0c02010302090402131214060709031b030212031806070b01050d080d0c03020703020c01020705010f1b060e011b0306 75
    0xc01150300c0c858020041050040039824020a0342c8515484600078409083d4640d00709604110703080e040300c1c8004a8035902c1c1d0340e010000b02c40c0b0071140d00e00400c04072441d0041c07006580242d01c10f104a2035903181c0032412901401050030258860729007650984075000c0d4640400405004d01a021000c0310300070b004800b200c42015100d884143d2009040c541c011805500584079035040e695032200d00b00c030a101040e85d0740071500041803489001c1e5003d0001c04040020b488000564a021302260740c8d580340711900d107440b9440d82006030f064106241c80c0034000000580c0e2282c40b0301101102c1d800145998003c0400300110b90312080c00c40c0c0303015420900042001c1030703000703a000e0304555007659260440c0d5440d180c04900c1d4810210340103410342c03405013010986030345070f8007500d0100d200b9022142451444001603030348201d0781c40340d84e0010315140305c6000030740d104c1c04405d0000c010048441c40407410319500c403000e070b44460b141300c501a90341e144000810400c00380c0e1520a082d01c2e050401145041 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 46962450 1250 46961200 46961207
    0xc02031b01020303061e03011112010e04080906161b15110703031b05100501051e0904020f03010906020304051b12030f13120b010501140a0c0609030c0507060905040f050106 76
    0x203210f2440b4400304107080d042107146c980020b0310100c004008002e190284001d10f40b80e81c1007800c0d0f4588450301c4a00106d2900360300c0c8030700c901a0780c00c40b070311508003c208001c1000c0c0703a001000751501031551042c00400540c165483d1800d895000d4419070200303080400c0420300400b0212080100645280452400100803400c0700c1600d030149880c030014a002c91961018080f45403004229100f41c140d00e5888540b60303800181030f104201e890301c000c40c052020800754207034a500d107103901000c44408a401072034044500920900050004a420885a00d505080380c0003250181c039950441803e00c108048180c9072008011002c842281c0c901600144240d52030150014001401d000010010503250300b03000020000c2c14402da9410207104685003071902401e0070711070f09002c43d49009005190038103c0056404030450759841a120001c60740322400074140041c016014400c8110900c00421028003103003001c1d22140e100c10441310310303040c10700044036500d1400d419000e10701801070042503031 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 46963700 1250 46962450 46962457
    0x16140a030c0b0a09050f16060801143006040510050408030106140904020307020d020d14090105130f08030c1203010f05060d0e030c070503160803040e13060603030c02031b010203 78
    0x10451501c40c450f50340c80401d00010140d14201034424451004010ba205100040581c14020700b4055a51f146907a14030654079200700780100c0303150b482c0d06811902a030900410188410840f80031040d651007007003400c50080c40c0807181d031540541043d0308000074090300300203946400f900340724100701ca07117029100d0f04420b0006010303c60401920f094604480c15260040e5205004020400c5540f0304003900e0203541d030f4145c100280054040d0801c840c041ca07008008400315000a004d00b1850031454000441d072a51050440780881e8403032050200b40600d420030058041c003500401103545201c0d08001702d2030301d88501401644050200010b1040c0f10401e0031082c1216020354034144c507102c8640303c0b0400342c90001080c00c5180b00c08074000c148008001520012150250151236070040c20300203d10f5201440c4c010504d05610402003004060b280a10595005e61446800200c031101d5a1310501941c0b02c1d580241c0003d007030b807004081503180c28000b0038400d4070404461640c400314440045c0d180d00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 46964950 1250 46963700 46963703
    0x20607020d080c03030c07020f12070603020f0c0106080a0201081003050c01050f1209070f0504090c05060703110106060807080f040f03030b011b080403120504060903080904060b16140a030c 83
    0x10407030a400c00410400d54190794070301c03a0311010360b52689440b0a01e190580c0000800ba071244120ba030019040381401da0340b09401c148140003801340c40d4184042500654414030ba0001401001c01001074403076001c2c4600300c007030004400584200691400010a848009060004914014081007002039400224803004c01c1c000c0c05c2c5140c603030007800068216800750740006103003040c141c0c0801c4494040400d00d00c054a0940040d0482c1ca0749501c2031108950381240000d00d00c100094080c00503203001005010031900c00d160054103012554101c2342519070700e5000c00e000c9119401804246a0400c44103603000d4016007000b00f01d0720b0a91902681e07240c2c8680302a043c56a40d42c0b054045074800c100001603100c220204103071040071031403d189194020300c03065600c9050229400000c0d8850740c05c4900b110800d40e107000340d03e411170f280c1514540c400000700c2d510a5552400081080d403000141000d80720841c11008071401c2e6041003540d0b0369481408145540090b525000020b80008158034600d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 46966200 1250 46964950 46964959
    0x3090d08070c0609050d020d0e09040605090703051209040506120a032001110408010506010302040e0117010914010203090d03020412060b0310020f0c10060b1b070b0301090c0e090402060702 83
    0x291207803502a102480e01c604058001818039007a10107001d000518590480890b03801c8030307500e0105440880303d46044003d60344c0e000b0710032000f140200700240c001ca900140700e501a142095900d907a1245802c032010009801c400003c0b4685080749400d02c1400da00210948504a03108090040c070340d01d60b400240c0007800d11141d4a80120200084042c5c2e240255188000b0003404e94200c00005a9030082e1251442030f609010002d121544070f802544d0882e45400d410f070090f1303428030340348000000ca01c08812100b9969401c00d4004244c86e00391171401d000045c0e00050743c9041c08011135003000d415419903400d150040108012081e030030a9001c01040d002070002840880d104002414841c420009501050012801c04400b407002c1c0d006102c1c544500742140c18101c0c2c1a0300030f40c03e4495510070b4402d20f2a0500c400c1401510008402d070740701041400b030703400244c0c86a2240c00250800e130807200040d03550f015040c00307040e080b42a0358a4904110b62143c02454a5400216113124402d4008d014 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 46967450 1250 46966200 46966217
    0xe06030a0c062304180536030c0d081801050702060c09011b0b061c0b010605030406021303050609100509120c12030406230f0a05130b010f0609080303090d 68
    0x140d00b10844503c910314480114a6130711661022070700d91140200500381030b03c41c945804602c07140350024034155240040544500075002e41c007080161302e9072460305076459020400001e80707016018445464000e011381c5443c0d14500f4501804080e061001108071590384c98801032082180e00090081d0f40700c00443c40c001d035511520720048070150454030a41c03400c0640c0c503002d4030070004401000c510904099032450600380c546011284c1c0001c1c040005000761000c9001881060710807801581d2041c082c480c09441e1130340140f42c81c0600306580c0e00941d02604254240640741d00c4c2402200c152070141d031300910a030305000000c04d0f03c4d103026140d07013105c0c80742c0010a010307040800d0000080404e152001181c83c0c0c80c040c00c00c4406001000c072000c0004403203542514801918002103801001c0070031907140e981d0355000c44040107110141c400b20250044900c543c0011b0f1042c08180c0c0030306000c0090001407880c041018100d0b441d03e42010110350420f1007000321000002440c41c1000149182180c5d1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 46968700 1250 46967450 46967477
    0x311010507020a0f060329010305070306030206070605041709281802030402041b1205090c030f010e070504090807170d0204080109020108071b390e06030a0c06 70
    0x1414031a1081c02034004964a00c0040c2c5854050f500904a85140e00c2c107201c0b81141980302017544128036042086c0d4041d1070f07071b812215407003a88419408599801c00060301500d03030300000e4542c3c001c0d04003101d10580b50350421040000c40d00c46108007101021405003032103103113400240300380e8030303001411140c00f4101c0d4005400c070070314928080101151841c550100792410101e1019500856059000340e05000c03485600d00340100e420518104d02e0390b1200d060728002c040c2140681005051040240f0480300c242e00360b99418030114500b508034100000d84204018529810b000700c6520640c419454403c0c0000400c0321030003250102d9511500d80c1281250300b01d4841d4060084010b03d200041c40440c0c040b640450542c09076042900036201c0d46078950b05c00c00200c862500c03845040b080480081c4880713001030300c0b0a07e448030101b0000a411107116511224071808034000740b1018146070b91303080c02c02c50702940c041c2c083e81004043d000780408000c640c68200803104944a54010081150741211 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 46969950 1250 46968700 46968707
    0x3070b030603072705040506040c0f14040c021005070905090603030306061b010207060912110c130e1203070306230105180f150309070e0103020307090905100e0a1a10031101 76
    0xb542208409800c05c424101424651358500040ba800c541941c135100000c02c41e02d42103a10a0110707407002c183c540c900c0c01d010090201428282c0407910035440380a582428007589402410720400a5a5406284610f03180c01c024181001404090082e0800c000340309284d211070003219105080840d032880060300402d1418028803136100060042c600c2c20700c043e02007141045862a0070f800703698030040000d543d00907103034a0742400c6117003c0d4080e00c0e4889401c0c1c201810b821040500b80c2d0b180541d48001c5090400c140d09500858a840029584000a10012522903140c076107070b07040d107050401c841c3c02000002c0d0591144a448030364480307032400c0c101107507607410110401095001d4070919001b1007100c01c45125030001da8075400e85000d07041001c51701c0e4040c000524100ca40003401044024a40711441c001041140300239a100e0144103440e03040d041c030f68059071050210340c00050014803014103002030301c080c400c400079200244400c02e010100074690030310b00560f40c000b00801c448904000050307 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 46971200 1250 46969950 46970009
    0x4090309090e0706080a14180a08040b040302120d050301050105031312080f0108010c0909020d060816050f04021c110d0e0708011112010b0306030a06090f0203070b03060307 76
    0x454506007410010751000b08040f60701001c43d6281d07218820240c68482140341503d0421001c11001000400000e28801e8035014540070f010010003500c07600801c603154880d80e90302075040b0942800d800101002103040040441000381a0100504516540204001c0c5148018810795040202c0800490010043c003041d1044103035001000308080321a86801624884084810714254000c40000080d080418020342c150312a607076690b0803e440c10505080c0094000032503006485540d40804541d2410030442c0c840b0aa0a442c000010180303080e00300444a05680d00d528000d0f401445080840b031003205c402080520008000705140f80c40388000c0b0f40a004c0c0d03600c5a032196061402001c0414004500502a5034001d8024840d0000c0c040000c9200d00c1008450000c212404004200300c5000c10041c58000034000c1c141c800d02c4010742c88100980e00c00c820255042c070b0042000e02c0461070100843c2c4014240403596034150328000000903105d01c094403c1c0410b07035410590800c80c00d10b419414 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 46972450 1250 46971200 46971209
    0x31905091309030806100210110c070602100606140304030302070609050303070c020906030d0c03080411060d0204080d090303091811031501090e060d02040e03070f06020a030b04150504090309 84
    0x203001c503045110440401030301554005801203030110b00403078002d0402013110702440ca41d90700102125020411800018842d89503103198240741402940c503800000d004c80401030406500410038000c100052030101e82c01c5520a205110b031001080075506060020703243c0c016014200140c0b01c40f60342c03c0400c0a0841c040700108140000020050000e07000060100000d000342c036545220343d2100b050642d40e849000174100420030501211001922488030396a00078498003135018034090902c04116a9017101040344603454000c5000d1008901c1000043c0008040c0d2412680452464402500380c1245000b9030901d5070f21a40c1800030001d00b504000702111420502c1581d030304c2e0030030359000c0c542c00680310503000403444100003400c4441d1180c154040c0400601903100c044481c0d00304801004038190318145804140204000b0540c0a420340400c0c0b801400301680c2c0d55001e2000500312803580c6015845540383c100703e580a56070044204d01a90000d8800185100260405469400d0309a21 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 46973700 1250 46972450 46972459
    0xf03020a0b070518030105040b010302040207080417010c12090c0e091203041b0501080f0a1509020d050a180c09020c010209031f1802030604020906040b21100e03190509 74
    0x24044650b40c000000e01c3c41384052200e810203a1030490825003078030360549001e003e0014000041c005840d150b0700511203944641c1840e4038040e9501c6d4803002c1a9080746050116035501d12030805a10340001c0303c009050403040c010000103503d640d6145803214035009001885811000044150300204180e02107040c6c800750391620380c078082ca4403280c840302c40c011660308107065a00020301c0b54002c0d2513042c0504200c862640d0281c1c2c031069a039004254003128403a1100d00c0e08400070306613030144000d01132103415007404116803501d168020705a0344d03412020302d00050170790050800b140c10740d101c02064071500381000d03a403080f142c140396002e030044042c0c081e414041e503403c12150600c002c00b05d030210085000c041c005d03c0b41003003078400a4a414580650181c11107400200107241414009500440081c80040c4003c107840109800410390091a461b050136080000e00c111010404036415026120051100c00f842c20300f090340b0b0340500d4040f00780c1201020381118100d0b000d00c1c15500760400181 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 46974950 1250 46973700 46973723
    0xe01020c0d0803090f0d08041106040312080610020601050d0305030a090c0e04050c190501031509020409022115090408070203010c0806040b0a050303030c0a030e0604060204050102060709050307030f03020a 90
    0x406401c10391041d10904c21071310603003410141c0b0510100740148083e200352680003044d61a602c494040c0c1b84103410207540590104404400a2600f0544003208045652002202d150007000d0004071130080b503d001c1550b120f10b0040010381d40da544c002c1c0340103a1515009469859543c0e1400c050880e04100412402c1903c4001c1449100950490320480c011400ca8052400d41030511032000220241500142d08085061081d940290000c2201000c0c2d1003d8140255445280c04103c0c1c10a4020300801c0d500010044140032200c1880c60400d42840c0c05144542090213040301c0c0401e18085c00b0340101e80200000d4140810f80b400c1c3d50f4005d03000f500a12401e640310300002c01d09507080382c41502c50f51400e03000c8001c40c200b000101c000d5070b00c0600118615156611691140c1e0401c0c4408000c040e200c400a8441d0311003401050300441c032030000540c45609100019050a0006010b4410481000420051a600001c21804980d0440d00756103141501d420100c0c00e02d00c01000c09805920707100b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 46976200 1250 46974950 46974953
    0x1030b03010603050105160207060c080304030c051f0218010206010b07060e031902010f0e0a02031b040b0a03080301050103050f041e08160c0512030414120a0506010b04051c02100e01020c0d 83
    0xc1c40c7c034243c0310801e41e00b551a160388521041d02c0d035000d00780014000f9a010710015001034090b0805011090040f41180ca1440b4180310461207625503400401803240c0105d2440786140802d41d540b00001c009001900540d81008010f80e00c1e0300030f0350307006071103143c45074081c140716801441181c441d82c0f0b034560180e0800708800000b9020300859010103e0151800d22a000342da000460714030768881d8014040c10303030420a04035070881383c0001060694440d0f035450f4100074641c1c4030507000006611800c1425200e42c90100007604880e401404405a141e0f12020000080e640d60592816466040860901c1c418103040c00000382c050303c030b5044018054600c40d0014042004e0b409801c64400f1562950000350701400c054881c016481800e1403c4058a0004114640141a11b001c01c01c00c03811130701d080c0100d49440340f502100781d00006081c1c20000e8244020b040c541009556605650503200002400364040b0713034030703d0405206108001c51102030195030b0b842440500b800f40740c02420483d984181d07 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 46977450 1250 46976200 46976221
    0x70303060f0603060503100204051f02120703080414010b0d060c05071401050a0f020f0a0c140604030504090c0507110f04090213020d18020307051003022206030c030902090601030b03010603050105 86
    0x14003e17a4840c4c402e21003030480c4400c0ba4001c90301600d002a10f00c2c481c07811404200c00082800d05000c40179402842400040d8041101c0a45009402580c0f14419810203091800c0150b42d4075030118803c3c0d0600e400d003074036600d4180500c400c3ca980140001685003074005d00f02c86074040d11100070300f448034043c0092008041508190f00034040440100168040d62164100700e00c5800d181c80420401440b0400d0414091006002da4500400b0200d950922110025080c454119001c40c041200494144003c404078807035641d0026041c24410f190110301d440340904810f9980e1824410301207070400404a803030781d800182e5450741c007808801c28130f04601400006034118030051918685000e907202c03125488055406440d03500540901885403d0a050011b580010a9102c040c5602000301c40c0031030740e40c110210400100c107001d408407a03050036001800d4814200710002054101903000000d40d030780c0035100381c20100900300050b00440c00004280500707560303480503040c1e500e003a0070001d16050 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 46978700 1250 46977450 46977461
    0x60209041112130c180608030c15100e22020a0303050309210f030405030f0301030302060610020f1005060a0902070605100e0702060c0702010c0501090c05130605060906070303060f0603 81
    0x52282000b00565203403078004030400040340e0042c011500040042003150040407908149080c068000f06000d51a214920f140d5070188050700103a0703000c6c0900d10030710344440c01095040120444032416643c50302c0c0c0c08224010010301018204106010b03c00c125000700d03014940f209034040c010703005403a41d030f0030b014103940c2003140c03410380d10b028503011602d500c80354803511021402c608070243c2c10315801408914060300001c01c11120342c0b10411590060601c010301640c000e41c4a98000c0c44ca80c0361240c1030010710000704890a040d54803a40768280302c180085110443c07071340000e0f000125a0f03103d00029800c140c847e405038142d03500c005802000c3c008290449071182c0d40307000305100340c20380c1d076452414001c0301240d40c8401a000100400c81902040c0c0041000c3c5005240004182c08651039490844240d40c2080b15100a4207204100783c0c10502c0040240040c92282048114905804141c0a10031204410320840001910f4401c25011b580407001034005800710340c00c11034a072103000d0020503 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 46979950 1250 46978700 46978717
    0x6070b07032325021207060e0102070b090102040f0e09060601030c0e04020d0617030405030a0807030507080a0e090705090d0f05030403061d1603020609221a0a050306070206130602090411 82
    0x4a40d40328403200ca400003e80c8031348030342002105c9107452030b00c2d00c441d00240101d1109880c5950208194000f1816880342d080c000c805003000140c5e100c0c0344c444071000c1d02c8516805801842c58200810080c080c000c21041d601040a0178003040700000048120394100021242607031051020900c1c2411402c154003501c161100d008000f190441c161126070303502d004900c85d459155000483d184000b9180d00701806510b48241005400e1150581c3c42185982048141600244124500142da8907111411a400c0951b03400d24925040c03140300401c00d0320f031080001801851b2160400800c000c0100115002990000030401c10100780c040c41c10005683c885110185104624180000c4040364104804881c0e0090040f0f2402c048103040c804544c0b080c0d03400b110701500744001c444881c852401140c0401c8d4500403101141034200c0204243d1342c02d1b9070400b134080c1d44a50208414103800052850b004841c071280042501d80a14240010384213011515030040d04054030503440030003a038054040c08 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 46981200 1250 46979950 46980001
    0xa050901240905010b03060d120915030c080f010806070509010e04060602010914010e03030105040b130c0f090f050901060c0c08120405100f140f070203060f040c0506070b070323 78
    0x50345d03030b4030128001b400281c0f01160f000844403c4400040c0381c890341303500941e0881c180115059a05e20207030180d020f0115401c404a03883c1ca42e00a001c40d800065541c1c0202c2071158460f8950400c0174150340d50384024580d01c14480e001603090f803107a0103200314a00c0000c0040c0240106a03d40380c00a0183c10302c0c26040b0f8100354040784204140c50706006500d40c07072409100450550b840c0600300400ba284140b19a900034410000740c01c41c419043c01080c0084c8800d8079402900703900918020607054040d48a601008042c9100340403641c1c0d2076031054111410740c41d00704d40110103800c0412407140c666110400c0c902c41d2001000504c0781d100043c0c001c95100301c820380030310203900b40c095560b50500c0321890700140c0720301c01c0d900c540008000a0192008007960040c00c041496021170300d006002e8510101c0c2040100400c41044000c404503c081c00080c0c1d2110b007000c405546481940d800a0441010f041d02ea0140c01a02c00c503451a00106148290043e8841d0604520800c1e00060616640c03510 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 46982450 1250 46981200 46981211
    0x3050109020f060c0c21010504030207080601120305090f0118170c01030e0c10022a0f010c150203090a0b18061008030702040e12040f15080f0a0509012409 68
    0x383d191a01c00c0e94035140d210130180c103c059112080044000318601c50000b007017400200c2201581003442038900c40c0d44a0340003003501d9410005164540001640038454a1049410b0310780003d5100040d00e4071400252030300f00710000384000503180c0481011011044e06480c20000402c8520380144241c000d6002c0305540e59880b01c1700044083d10102c400300a00d80d0b1219211194908052581401056582c4180c2d05908001d8204010540032a01c0c44020341040300f4080046140c01000f91001300000d0811100000003a540d0f00c1c0a80a4a020040040c3c0d0120001d03c0c44a01409000380040c2e000382c464400d8944104c1e440031925016004441610501001603149112460b1500a403140070b402142052519820800035150040d040700c80350240c1d04039020050f0941019001401c10344071040741c024200400c030300c0c40c2d0842064060070042801c044c000e04a050a8200e0380050381a080410300366110f040c0c0e64090701c9000300400b6039510508655080c0e0404483c41030550b42d240509112 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 46983700 1250 46982450 46982479
    0xb090a06020f13050604050604030f030e090a06030314070302070e0c04120b071b0c12050c090106090608070305010b071103010219031a0102060c0909040201110a030c0b09010509070504020f130305010902 89
    0x106d000b01d0140e50b0b0040341c20002400494480f6803290407061013480c00c080b611810b20007052019600317a85070011140c85060600400d42c10040c0102d09914004030035041c0b5040740c4000b90344800300c0c800c026924004001182c803e2520302d00302d901603d011004240c1204891402c00c8484c8012034030040061645075821a00981c603a407000311403504400c160141a050503d580d00085070b0a600300c0e441d21524106400310748a071a201030003011580c47c2d1511240c0b4058000d804044000c00352003c161030080103000d100e100c079040d518840c0d0000000b081d64041000031a009215501c08030000c55140246600fa6542c180c2002072103411548112a6550221005a9031902c00b51804190850140f04011203800c0c8901c81503809401450102c1c80348001da11454101403e01031f05400140c08038801d82c003032002d44442d03260800c030810001c011503d4044101c60703c07165507000d07607442a40c00040c1c0c001072000c110180d03404049501c07a070720b071881c1d6207107002802000380a10481c090021400e030200c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 46984950 1250 46983700 46983709
    0xb0f01080a030e15090a0e01090b0108040b040f0807051606020115050306060906030a0206030c07020420090415091805070e0106080a02032d060a08190b090a06020f1305 74
    0x100e125a15840f42584000e80380104040344061803000b50003003c06200e483d009944070484600203203a1424540100c2d414501594140d4200780d0f03140703062240403070a01c00000e640414055200341c2103080d00c504c143d02ca1800c0b4038544904e0750054034510070f18039510401d2074806400811a10b06130020041001d6000c0e048015a1030741c881c440d41500035100140180c01c1036000c1039409a00102903403004a4542d0005000703800540342c5203280100847c001d030841c1050321502400c1d1107117141c8074143c1203001e610f0b2182849040211406640c90764003e01118003141d124601278850011305000d089554509484150508901a82c0e1031007128400580318a2203500a4181c13680d43e500c011f281c4d51100a00300207580050004005d420202c1303040d049030b03600349070a00d5054002a0b44d40304036060440c10030401044030f030840e0702035800c00b01c100612000021803c0036010741c042c5060b00f280d6103001407542401284d92010b40840c2c0006004420b4142120082410840d61070710010010b48400c00d01 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 46986200 1250 46984950 46984963
    0x207060207060203040506030c0d050c04030c050307050a060e180c070209100e06010507080408190203011b05180a03020307030303020c100507020d051c0f0c020d11030a0f0908010501030b0f0108 85
    0x500584c10410060019040200c011a80700e0f10705003195103428070741030b40030044400889031242002400304060003006103443c9614002c0c001140140501c9080c0400a07860742054811a408d001c04410303054446d440b0f210b40300d4200450500081241e1820214803140d030b6105080482c0309062420024125a00806003071080d5018800d1442550742d5403001590b00c4c0d8040f007015103501d101800300140c0007c0800503000c88804440201001d8101841418291106401c000b9600f50150540444140d8007800390360300950082085500d400052010503a004401c0c0c1002c0d4144c010345002105040d01038000301143c0c031304a822500e508000044443c1161000c0c2d480d403005800c0f16804072411841440501081d04041c0c40e00940c0514059040f0100c0c0d00d03041d00c510f8041c2d00e41502000050b014007000f41240c0c07141c10f1104800700f1a60b00305459116041415040c02841004000103a2040100d60068822000200420b58403410800140c1004440e02015600c504002042200010856 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 46987450 1250 46986200 46986209
    0x50103051f06031121070b07030f0e0f01050f1c050916030b070c0602040b0c0c030606010302040b09060a0309051f051602100e0c180402031908040902070201020111190207060207 78
    0x301320000c0702c204035001c940217200070844d142d82c0210007110702c2c0a002c50002080003041e0300790b032a082ea01e40900035662803080744040c00520168040203440ba21a110641d440074a086a0b450442200701105406851149403400d0f0324044c402c0c40c04001907008500036810b042c00c48040d204841044800c200e01070000415861080010441c028001d003401940144914409402d0684504548585d60450f580da01181e0780000307504440d50030280602504258203103400d40c605070030613010720001c2c414004000c1c000c41d0005a044d44052185d44640d400035448801c0c1c07903d200002400c46c400e4144084a98245d038604404112614601c0e546a080b081140c3c01070b061410740060080002d00010401d40041d000b0100c3d00002c6548280b0221010900b030091041c1504150040c18a000d0703100c00a1013141070803d4421010a52040070f039403c88507001000b40e51956140f0040703024026103501407410070400b0031100320750144c3d011000c0c00c540c4144d08640740555a008102c0c0d881405104 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 46988700 1250 46987450 46987463
    0x803090a03060b0a090507050702100905030c12030705030301030b0405070501050414010528121503020a15030f0f0902010f0201092a03050601061806020f0601090c03090204050103051f0603 83
    0x401c0012080e40000c04107203c003d10306100036540d005050103031041203078444005800041d440c030440ca4040340c00c444840d0545070a010260510010a5640c0080560701d03200b0348030345100a2120408004640000340e000d41a00c1c0c80356501d1403c090013842c103440c121242d000c0c5e05008030350380d4800c500750b40c1114404450048105154001074810380e012428802c551003039446003441d0400c030058110710341c1915651340e0b8540891050740d10100c81d074404103810018898402040541c0e500c0700460b05a481e80c80070b20220b0410600160002d204032124041c01508104141010004035807202c82c900b4000c0e203800703041c3c1448820413422224441c0c3d00034002e40305001882c182d00160000060716044071616459125240c2d10313028a005001d030320400010398101e84180a81190044040080405000800101490048207a02e40005014000413580d580c100c18031014401e0f040717208007a80203001040315503183d003406616045140400c49410701007400307000c0380c407406115040860f0340169 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 46989950 1250 46988700 46988719
    0x21806030309091e0711011401120201081806010303022109220e120d0b03060106091802090d0f020a061112071b060e01020c06040305030d0e10020d02030f01080309 72
    0x1c04000e070a1401130114840104040b109108410000b02c20328040c00842d1140c0c10801c1c0040c45660135602216001580c084101c00100014012480c11820b81c5909081600c1e44c1d0303a03159642e0540703081c2d45040710244d1042170f00001c01c1c503401107040705189080326007607401210300c440d142c9580d2103803010054115400602e0414807003248401550205180800032400043e09080c251418140c0701c0010710405001403207204140c12031051103649071055028240b290b2501c41e02034002c0b511485011141800e0305c031802440d5065504a540154000b000f081c03800505041c00000490b4410040b401944403050104045014054104800b01101d000b040014400304060340c00350040042105c10101c44000c40c4142541b4210301000f03403110740c0d14030b09101c0070780d00020314120038081c100303015010030070040c40810808800caa0502010b01c03004103507040120190b03071908418442e4201014400f14041e0303220080e9070015409640482e100040c1c590b240d060b07032038480c440d0124480c1d001103110f = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 46991200 1250 46989950 46989967
    0x3010c080105030c0d060b181905041205030411090c030403030f0213170109020406080a110904080909070e0405090d020c0307050f0d1707080c06100501021e1f05040218060303 77
    0x1c0c01700f40c124410000803804070000300101d00c3d41c50030354803003c3c18090b0103403c11840d0117041d42034040a4100a0f001c1c0414106a294602c5840c081c4d1007800811200000090a00190450070f01e03064002505241d4fd1340b5098546104035002920120000381c24410071f030400c88402e000342c600410030383d0341c00110907281150420007c0144404c0d010f603035485040c000056681c51003410b006003101009010f00807103030b00c0c008070013a290250044c40350714000280008649801c060b07030305a11068504030317241c2d11031200035600c030607282c3c07005030b4011305010810003003a4002c180e41075582c61a40032202090380150405071100a41e0080300d800c2250b21141c000e5a203400000d02c40041d001d4441c9505c1c498940e6000c84241e80411825181d1400000750300464400070018590b05c00c46030040c10601908240000b5200c40d0100071030300000d808200d41c0c010000c1c090002c0003942d1a03100145900c105c2d4480c4d480b026001c200c90a038841c3c0305000c0b0841d0711750900381380640f0480004028500d0311210 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 46992450 1250 46991200 46991209
    0x1e080d350601030f0b09011203020f070b0409050a140403030e0f0a0b07050306010507060c020c2803030e060d0e010b01080c040e010e040f08070303150f0b0301030f03110d08010503010c080105030c 86
    0xa1240c00200f0700d84030760030045c641d1649480e490103081ca01410001c40002ca0a01a141045546462549a0001000f040000e6100043d40c0550342d4503a00407600344c075040c01e00e070040c106c400d8110140341c005030244401c05401d5030041a0088003001038030421356442ca0003d0715980400c40260030900d41000140c9070310b1240b001180e001105040540c03d0285a884a504540d2460380c41300c056030003240080c003903141035441032a44d04010315070340102c0c80d580c804043c40000390f441b0083c14030400041030b14066540e041944c24400031442d00f04840c0c0d0556140702c2c0a40701c480b0305580440ca181d1b02294090380040d0866098690964842e0741e240d1805c40d048020000c01403003900c031820444405d43c0026081d02c018132506e4001da40108445040c0d12003040c003003c26503c20001d0b1741081d2410032101e41c082081d2030460350005181c0340c45100307074207040d15885d08903104001d1600980e107072152034036082032955040c0c0b4000d900070072180d803900d102510144020700403240c0c5030740b026401a086152 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 46993700 1250 46992450 46992461
    0x50315010c08070308150d020f1201020d0207110a0b0a17071707050a02010b03030901020d0e0d02060406021b040b010801030206070c0b0c0706170c041e080d35060103 73
    0x8041c504081c0810305a140c0403003542103032808a00103400c501c24030800517150780c004078040604542114940400350300182150150040040c00317410344400e801c0b90380301b00390305656044000c0b0740c0543d50303802c0c0c614090b9050104441c015120b00f8000030040340b20001c4ca4251002480c02e600c402281c1d8044501c1140c03910001070043c0f0400a208070180d81d0000a614054050f0000b40c49640c1c44010703061000c0d007960340c0401c84034003a90041c80815842e0f0783c0050908900c5415040c003c559071900c0303001c1480603100c080c0103500030b1800500022460340c001030810028151510b041c011405900802c0251034403d02c10500066078140107201500d010f000a00d031403486820340c0000309a8817a03020f800d40e004083d10200c0c03600400f4080100075000303c02800200703800c0561700c01a140900000c90180194022328044441160040038007616681e50b035800b0b802c50704122005042202401414100340504050010b4404000400541a8427188184880c542c00c0b45030035594404004500904 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 46994950 1250 46993700 46993741
    0x6010b09400b1305010510020607021f0902040213030b07050301030210030b030307140715081b07080f0c0604060b06070b1603060509090c01030606110604020402090a18060509060a060503 82
    0xb980c0b10a020515950140c0710400c0c000225400700351503141500700b1903400aa05038240964000600f000561030f40894503805001e0703003d00450088240f010407000500940c0f60007500144000f031a400c0007100d9030b07201e00480344552121082c03582c550030111840e000a11000350041c8031707200341048440c040c2c0c01c02019010083d0860b403c05500303031110280c00b02d80c0d0b1044111038025501c244125000c0201805103034419042420b2142400d820082d6000000c440030082c04c000440d40b001007003850f03000c40c0c9080011802e03413620358502144450300c40d00705480459078540380000840203030400c1003d9800d880e42005582c0c4003a5034030b0312a805c41103400401d407001c044c0d40d00741c08122540d5800d000c9014100710302c000d000103919003002500710f50741e54100d1010b200300905851a007440000b03506900540c15a0007580341c464400c00b0404144882d00b1024010464030300380100e901003035101c10120761040b034803d015503c403003062000e07107501ca010307190000e00c0400000d44c0403512200c4640405 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 46996200 1250 46994950 46995079
    0x3011401020a260909040605040b1b04030b1003080301030503030f150303030f100f0b070506091c0c060f0c08040210090f0302011103070503031e01060e0a230306010b09 74
    0x4c0844006042e0500885003241c2d810b56030810700c01880300c2c003851a03078072007110805500c1482088814040300d000740d101c010081400c1030005a04400301c003030342000850703010450304d8403961240740080d100d82040325a081e940c035004000945120f4001c0d054210b802014015524580b2600050980d03840006d040d20011003c6100000f180101c1210250040034a426a1911548149055070414402820300c0c8101d6110080c4002034000f1010403019610030f9003010b0094003120f2400c030000d06100000350000501e060641c8880302d030401107032031141c1e00c200e408501084038031000f580ca4100e980154050407440b05000d10055008080c2881d000e07004c501143e0400d20290f48003881c0d64000c5500030300c00100071602e03010440100480502409440c1404161900030034042011b844482c49040480c00075030000e00c4603991021711600c0d0000010f001ea54044d81c4810b0303d0543d070f03886956054001d00140040e20031441d00b227010840002c4079040041c1d00c41c1540e0008c00c092602d00c000070310300c1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 46997450 1250 46996200 46996207
    0xc030307150c030605030d0201020c01060b130b21040303050f0f042001020a0b07030c080a0203040203030906071a040809030d020609070302210105040605040c090207020f01080901060503030f03011401020a26 91
    0xb1030760704100f4001c025081e23600140e0340395407842c40300e403d4401c07561140f6070041061264541a00c10302e04d03070100f5180903944254851189001003441c80c0307601580443e00d121018140018503626800143c49058044400502038880f2055041c0045088501030502d04140306001ca02c44a54035560300800d40510464030b400e03070170b5110352003000b5050302e8100200396520740d19000307541c0200d01d10343d200b03250070b204600b0344c50a600401e4582c421004400d106020000d611000c0000603c0d9440307049514074200245840c10b80343c10304c402e90003180811711038400d91910303180d41440060f04901c070382d00d5030000c0c240b101d16650130320001440d12451421100c0038082c80c42e10b1038509110b0144130740c1c0a6040440ca50815050050f8207a480303030000d03100180100034160150311402802000404c0070700c1d01c60001da5036400d4a0380100a01c0d0409a0f15000c0083c0c0c0341c0c180703a135400c051030507107000e0200d00804c40882c41c010780ea10700704c2070402041180380750a8040f4828109001c0780c010340d00080d40519 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 46998700 1250 46997450 46997459
    0xc1e03060f0b10050705030403060b0607060509010507020c0a0332030f0403060b060304050303041b09060306021b0606090403030c090504050a020d0f0b060706050a09170a020c030307150c0306 84
    0x1c0d602140030070024207544810703280c02450200e2041c903010b42c95040c5079180c2101c5031500f0b41c80707210741d02014020700d0711802041c00c0e5441d200111004a600610100b1203400c1050486e8086c020580d0310000503c140c003804042d514150170404200c030303030120b20805045000c0c54241e01e00c0081980090740801000c2d1740d082811403d00041c04004490f07000c1c0742d5074a0a600d03120048400c02c40312240100c00078020400041e00c004112904581c2140700007640d03680c011241e0741100e1040e00010222401d10500004000058003d406c108210180544080d20700c554240d80c0d130002164001c1c1e12000d070b07102144c04240264480c000b04400c81c645043c00380d440700c000c036094580c01e454038540c503680060700442c001c4c02c622a000b00d03585280d0040c0200030940000502d50700404601034801d42d43d80c000700f00700408660110802c55404101703004090095000090141c00445030fa40150140d409214654900072044404055102d06800ca590848545110081032090a41424140d45140104 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 46999950 1250 46998700 46998713
    0x9180c0c03160b010603020307080a0902030705030f03040501081609030b0c1216080901150501180e010b0301030b0703060b0a080702010905100222050f0603040203070306020403080a110a0c1e03 85
    0x79a480568614160703602c040e01d0944100700050f130207002098030500901036031035030001c020750f040b1003000800719100e2840c4c0002401d00074258410740d810312680301c51004801c004000f0700126002600c400c034080e0703140101071200302072060520300010040c803400d00000f4901d0b8180e541140510511170304003491071000c0d0581120030b941703c080682c0100701420425500604482e445034014009009509500000003603070321050055030b05108449544000050810560700c008141d800c80c0c148031960b5a00d5902083c2e4428042078a0252200000428940c003900442d4111003400d5401454181c2240041320303483d001800e07000465480d035140801045042041d0500a1800c400040c2c1d524400f00400d8244081211104034880136102c0422043e0b44082c4019013110003a0b80b407a0b0380f5519440000e007400c3c00c981005005910105020045c05141005000003441030b45600745820307480c41416584100e01c0300f004002c010f01840c213010b10b400c2104800e05a2500301580500551280e13a00b1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 47001200 1250 46999950 46999957
    0x90504150f05040204050a0b090c0f25020102070e10030f0206040b03040302060601030501060f09030b070e030618010f0504020f1207050301020705010f0c0e0306070305070c060603050d120209180c0c03 88
    0x4481c441e150b509110542c5050700c01c154000e00f500000b007007490395500c00b050541200400768003d551012410314824019802200d13001d08100980d801280c200445409641889000c1680144142000031402e4860080143d000700113440302940250b280d40d84004034681481c2d03040f6040001400006040203400014500581c4690040c0c941441c2c1100010112a4140d02c0541000402c2d031400408a400030501000d8980003031012119a0321094141c401550041d0b070250188034000070428180500610300060b02d101c040240f09130720000030b00f502a213a05440203540920305007013100c0517182810f20032030032001c4507042d0384002e50b540c03001a00720303081410240e4085c0d445403119010600580703c2c2040880e0035062140301584820042641c90b000180210185a590360204000b0b074010b40c40d00300900ea01170f00a1001e561203240854071a004007612001080030b4102d03017201c0803c00c0c02a41c00441c009490741203281c940402060350500040e113401503140c001c000350341c5181001d0005 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 47002450 1250 47001200 47001221
    0x405060c0c04050f060109030305070f0f1a09060708060616050105070903050f06070206070c0f080307050c011404170f070b0108060402120a030801090c0e0a08010617010209030709050415 82
    0xe8480d40c08281c1c28007080d034000030990081000082c080280f0742c0e811002c1d0074180d98040c504240c0ba8001c516140c41440940080900b09002e00400f80c810003000310307141d40a681145404242946614500b00e56070503040c1c90400102e5119000648541002e03c090f04e50074048900b0810548190307200c15085613000e03140c0c04001513070042d0a00511000700a10305131718901d0001098035281109001f5100e41020b0294410000440512414007020044d00418079400a140300d41c1d904041201074a04e80c498112160710b9400c014401c010200c2c00c0744044c0c401c54000360408015501c04ca030032000c2d03520410440c0f4440d45e003440030201149200c1440e9028184403001004036040500402261035001e9200302ca01d60300c800e83c03c0002035030000c01c0e10f0440343c0d03d050108601071864002d079002285d21000c603401c112200c40c002043c24054001608481c00030714843d03500701307800e07103ea8241e00c81d008410790181d0010b281086221841c1e070210303600500803c0c11080303100321001e55100785d410100d007 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 47003700 1250 47002450 47002453
    0x120109060915140103090203030d1107021002010c08040b10170c09060604031e080d020a090509011d0c0f16030216050901080613050309030f01090510111206060405060c 74
    0x41404049010b200700241c0c5041c210030210207a02d0042c844144100c159002c41c10541c540c1404021914200181c071070809a052081c40101780e04a801021070300050300a071700c6070f100c01d40b28400e414010b20a10f100b074511555140165039039a129001c0ea40380c040d104c0070301019a18800a200940724000000f0b00958034094030701c04040303004002191001130101882000304100400006219810035086d0060f1103204200c00300e020304015996000d0300070a4078401c0e00000b400c4002c40e07401001d0600f40c90085540d0030f207590b290100ca4003202c3c5512580707c40841601b010490319121040500003c9a180401601d020a441520161101e41d0102180503a01411003c111210030350702e01d802902050302c02d03d966624012106a641c1406440d000d00d02030580010001e2190600032185c0098015040700e440080c04c094040c000c082c178032800e613440c3c060b400040803001e009005840301342c2c500080e05d90420a04c0c4480e581c9017100900803942c40301741088001003c1c0c40d07100c05069034810740700 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 47004950 1250 47003700 47003711
    0x1501020705121501080309060301151707050309010c0203030c0a05030a091b08070b09060409090f0b1e0901090c0e070507061109010f210b0414040c051203031b0d02120109 75
    0x25a140f480010680180d2203030b40041c0034035510b40c0c4440c1e09880c1180c1c0513001d00403540d0f40415041e10704500f510f000c4d4124284110411142070f80010040d0b0080d900fa07002049402c07081142240c9030300040d9079940704034108102001e8440d100b840030310f03008440160000364400361940d9424499102040191140344014030402a4540500c101402007000341724091034100d480b400142a44590302170f11031000d41c0c411000d002c0c0a80c0030300d14941c2d1540100c1201c41c5041c01401d021b008640e0302c0d280c5800c030151a000a40d0120103000d03800d42c00341e00181a40550382008002c50714400010403101c108a0180b2415021408600134070346071040800109648441c50707400104101300490502061001c000c1208401c54881d25103240c1110b0500c10000b0903d90f00741c0090064981c8012002c100d0380c0000510003401604a1101c0840d1001c640b201114401d22030015203034041101c1030701e141032001030400c429130301f1100205480f50000c0d80040c907181841c0f081c00b0340c0c000285c0200e00d0031565034 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 47006200 1250 47004950 47004973
    0x6030e1501060c060504050c030604050c03071d011202011b030e1503040c0e06011101060305240108030904050403050c03070309050a080f0c060702010e1e13060509150102070512 78
    0x2480340a200c4024003094000541c1001c01c0503008540c400f03401810140c0d10780008042c08010b00c0b0340303040707004002c4c2980d02c05d00780f030b003482c60381c40e04402a520b210f4042d85000280b4503117100e080c44043c4d09403508081080e032900c5883e00c44190341c2035099051080405c0b0381210140f40c0d40c9100c0c8a0b600c01e4031031903140b0016a00b400b2a060a0b03140040003083d0070424800400c4851311100121610405201d4580d51448012a0965442402c3d84091340c241a804410400086010905400c45520001e4006031841150709004000c1c41b0b000301c0784c0c00410604400f41030581082e503100d8003c0c00c00c1032900780f140030003610b194422001980040c031541d10034061440d01c08072600052000790300401883c4001c800c06902d40c0719180b81c40b446507100140307200442e4003030317020f41c1c0c0c0040c801408480c007034022619030920264140d01031031146000c0d428044034100310344a02d90660f80084c3c106001c41c3e0b00c44903078450410480a41c80d040d4494a200040d080c1e0342c07600d84151401040d4060603910054 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 47007450 1250 47006200 47006203
    0x7060302210108060a0f0e0d0306090f020304020a060309020d150903020c150933040e10060e0f240405150702010c03080c0403080d0e1009080301180b060406030e 71
    0x5210700342092141ca0004006040c0002207498000076008000500c002c2d419620354010001d10400c0072550040902002003590140d01c000111204900140b260080060b0200e04034401160000d520500103038050003030030b00c05d901c244c4c0050320142c040b0b400c03e036041d00c90f462403032010328020300c100d03448008540415034140302c0c150b41020290b4081030001c043c281c4464050045a48490080c0c072112480c8a0200c10b11141d079003a041c0d00f4003a4002410241c0c064034003a401401040d82e541e03501008a04c11608503200b000459405564a07076001880380104480b0009446c41540e128060b5803486400007060400380d490760260f800001e903114a0030052050307650144131f145007910024054800981d822001d140e41c0c540d0315187c1a000c07a51503c40c0751005004540001d808080042114446003807143e10509410240c41e04440b828040c1002c05402d445c21b19000600d110000d00041055000301203820640d805503120102c0d00d035401030003158a07a0407541c8082c0000343c407061101c0c0300800 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 47008700 1250 47007450 47007487
    0xc0e0102010c0e1e0603090d08010605030f0f0c0c011d16030203060105040b010c050f0d121b030f020403021e150703020304180b0904030c02040f06050a03110f0307060302 75
    0xa0000340300002c12540c02500940007455034a020780b0703403240980991014904c1416500200503c4503489003010031007140d59150720000703100440d0850b000829400d00601c252807140c0100724141c22070380d8454000c10100d01c40034041d981004401d2143d440544001c1c0245111f6020344030032803942490002c00d40e80380c040d0724480d00d2030040c2e0700041030000d03890105400c2d044d078000744ea000c508501c4040040307410384d404030000392440c0115901940d00090110380c907001c4089550328200e070070900342c207007004607000000600486081d2100c40c031030b1503000e42c20480800000c50700c01820240d6035004075942415042c010510603018480b40381d05440c00704c80c200c041c2c00c44032501c01d040100e260b801039a00d1103a4002e0070103218000d80c0e040005001740c0c1190f0303082c450151074045c0f141094a8040d00d09081c4c20301c100e204d28248080c00c01f03601030070f11034001103940041903810328038a1900c0d12058504034a1005400580d10f41100c4120740382004050018400d5a60060b621424034104001112 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 47009950 1250 47008700 47008727
    0x20d0603140d0e100207090903090515030a06060e010c030c05190503040f120305030f040c050604060e09070305070e0f04020d0204150e060405060a0503130501380102190c0f090c 78
    0x3804180c4c402902e5800111801030300c5080200145034036480c1415500139110380e101da607000350102050b03481000d40302c3c0507501800711120706004098540c3d4003074440350a140303d0980001c0e00c1c0c15401c0042845aa441e03840c15010350240c0c0d650401504e100c04001f8400c142c1a07a13558400a0100000c0e0b6200c1c00e08d20080c030b041d0200b4880c01c1c5241c0e07401001840058054400c0030390a002240c14003a80007203400040c01e000706055030341d40c3e65200140c503d01c83e840c1035620a47d0002d0008070ba5034000e014152040889650b9600c0152001c002c00020003420901c86400076400e21405102c80800d20050001d401584604004c0354081080141418010b100b00b9001740b0042c8020041c41e00e039841070360140821030818603207070b41d01c803031784070240000c2100080d00b15820240340740a84000d00440f600d02e001c4800c07511081a0f10740d80d650b121000c000b421a401a40008184681d502078401240b0342188100d0682c00403c1d41e400c4214041c44158100710348240d5192a03848020360404940d58120 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 47011200 1250 47009950 47009959
    0x7030b130207020a1a1b01060506040f0305010b01170a090302030706020310030506092803021c05030a1103040f03030203060607120909051e041104020409050a06090b0607110103020d0603140d0e 85
    0x2072144400d41078500031881305008500603502040318074002908010042d00002d00282c2e220b40ccc1e150700d41318880903144400e64240d480c0c48040700c040d5129180041440381014644003068490382c0c1c40d40001c00800c001942140802d000042c00030740140000c40c081c1e06102c60300d10419007582861410590040c04000c003550201c5d44600201c41071210b2200080e5800d442160ac090031800c0a90510610380c0c1c15502130798501c0302c1d5040041e0410042c50160286800800603115040700c0e2200510050750041d107000ca2000c03400c000284030350000c55110300003810b0142007829541d120040c410018a502d404241e1400090000c00070a1241560004c2c00500360b80c24801c0f4413016480411010b00701802900600441d5155601e49804a40040000150801c4a840d100b0501c0004206500940ca0114203080c02d2142900d00a81601d01054010b4011800a0301080043d0002c0d4440f6052a009030788403003000000c90302d80d40c0c880b000002850044d0626501a24008240424405600b480b4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 47012450 1250 47011200 47011229
    0x10c02030711040c050c0105101a04080303060d0204060e18010b0108160c02030f1213080c1e030109062406080c041a0f0301060f08011a09040507030b130207020a 71
    0x31070020b900076030107071a082d02c00042a448150044905100796120000b00c0e6003400144890041e82c400c0c0d1074200c444944400a11110010034264103200c1d40c0f00c0c001d00340c0d0003880413031014900782c803200713600c1480200005241660f40500107071141080340c00303136007440c41400754802d0380c28207000300c1c42851400d1829501d50f240c03d040d58120141428044006c022000718040c1c119102042500f445440300c0f07044a004411600d04002c9940c4080354a0310380038110300f80040e01a500107150049008001c1200b1004030000c03c400b1600e0340200081540b640d00d40c50758034003080e4103119500303001c0825050034400c030080c1e20a48581851650000040062030400c2080001308203068400fa1070b01a03042040408110142030414001d4151480081400100009038541c2140d00041c00d0b20b41c58844540d96a42c850b0186445070040c40300d4020140c0402408a00b40b50540c00142d100121f8100003800030501c0d008203480d0003083c600120f403150b00040100661401d03840035801020844800081c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 47013700 1250 47012450 47012453
    0x30f032a120a0b0a090b010c330903090b0c03090406060801050415150e01170c0306030706020c030d051b060a0506040f061a07030915080420031c0507061401030302010c020307 77
    0x942c40314400c045c0069901d494400050384102c03905120705400c00710214001c00c02e00e00309001c03c0d824501088081510724014140107006000305401d40d509030b02c039200240c0c2b80844072042e44d0711440400c1c0710f6000030404c0c407034a569a44900400741015a03203800c401d60512040c030044540d40329070501c0e0040301002c108801a15200c001903010114070708004020101e00050701c119a501e407103107203050760003010002d03000382140155206030002c804071361a0315600d0509a072108000c92410383c26400c03131000c1041c1c96000b0380c02443c0030032800e0010030070b440354424664100710068030380304002626a018003090389082c0c010030500c00c0200c401003107503526241d1400350b840e07140c0c1c0c0c0900e59804c0101d0307040c7c1418043c030800d0004040b5501e40320716001c0c2d160f0000700065402c41d401c0380c14503801244101308e0b10001501c18441c3c18007400138000d00284400c41501c142c0d10405400c10010b080000400003241170194031003140c42a51844100d50541c903019007540d01c96003555013150301c00d214050 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 47014950 1250 47013700 47013709
    0xb03060606130306060e16051305010c03050d1401030606140117060312070b040302060a0c120e031b07030c05012c010221030610020c03030f032a120a0b 67
    0x1500668100c406035580c0c0031600110854015a0f8006800d541c504800003c144448100c900d1055203078081c0001038044803802a0f84602508034030781802016500c05001c01c0d405400d1011a07a8040d0810030700304480d44401c3c60075100f03071010400b6a482c200300104201b210394000d0337102a10fa520070009042428000007080c800100d00442d104503003140114155440c180085000c07020740010840da05c03465803c0a0f0384207002030790200c0041c03281500007400d001030340c803488a1070a00c80e03a418414041184a440141115001741001404201f0403c0d26602c407a0220101403040b1802400c81e903851400d0502080c44c0c90b80c0054140034550412920000800703041030300c1a90358001e9810b0751590080100d242c041b0203152040410f4030007000f008160444805180f1400b01200d6810194840b481e00300d03211508200c0c1560142d10a02004071741c0030792540910740c0503030000b4101e1844240e00015041d1210540040625101c00040103c2418440d401e45540400d080d5410301c000c0c5910400709 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 47016200 1250 47014950 47014963
    0xe01030c020c0105071415040c050f0d0f0201021006080706080901140402060d020405030607090312030e03031302010c020303030703050403121a2808030a0908120301090c020715080a0c030b03 84
    0x7a41040b0001134141d04200b4541c04410910080c2d40c07c0b1408504074683c0071040b41e000303440603075a0000740140091180f41119038a003441da0003820310003400c0c031145d07107203643c20301c03501c00890550044200c082d0104006204650046c44120020300100d4549640a40316101c040c0010f002641070603140c0e00750001003190309070031690541d01c3c42d0b03450f400005120020b001d240c0110784d040c06460240030038240e100c0e03070307902c1036902a5850000e030a4801c00182e00b15404882c0e0803025030000d2000809039540010b01050060060501c10b020304507680c0000d0940e4022104080442d545005000601d5444940a18680892071080207002007010402900b28100042d9510450384820b03050040034480e130308150601404600f014075039440345156a1260024424600020010f010001c0d04040000e9070480c000420900b00703185908103401d2034041d1607060320820039031041640005e0800020325811264040c0c036520441c5a040c01c12041c400d40300c061a00c07070205420802c1c1c0c140700d40c2d00425407 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 47017450 1250 47016200 47016223
    0x50103022107090c020601091a030a060203060409060501030803100e0403020307080a0e04050405010e1006060804020f030c060c01020a020601140306190f020c0102090306010b07051203072d0e01030c02 88
    0x1c0c05101c2045610901d0420240c10100c0c2450400120b042595000654541070342c1020900b0700c0b18018980e00482c009420039985075146c1e00c030710a40310200346640d0086070401d00152010034a0398164036060709540081c0d00c2260000d00000401c60340fa50464084d9002d405030581d101514105910025902d000380d03200a85013920004032080f40320f004940701800201c000d4000e01c040d2500e400c0241c000d0203907408030034040c02001010620744125104041c1a60340ca5103c88030700d52280e40910030f07090982c40c152034141c070039180c001400c1d0b0360701006800c17691403c200169888074260002810500e040e417090b0900407180700d411760107543c049411640300b0181228624940741031420302c00035041400801d00914800074001003883c10640043c0b212407400e4007202e075280d036111014155440f402d1800f8045821126081744104103240042d03820030502e28150104c1089050301c0e02103018000440d030230310481c0342041da039a1600401e04200b402002d0808020080b4941b00c081e403110f07031090701e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 47018700 1250 47017450 47017489
    0x3070206010612060e07020a05010f0e0d200a140c01050304020609010e0f10030911030a0c0303110c090f060112141602120d05060a0b04060f030c1b03120c0305010302 73
    0xb8806240043e070340141c00401400c00d000601e8100000080d444040108003076911b542000c500700310707074405401000e5101c4a060000e0a800c0e1410b030081b10940c0107101c85215860281c29040c5810108010458089000d0b11100380881d40080700c0707502e00300240103100c0c10700c0418804c01003da600c60040c1c4500b00f10a00788111080103000010b01441d6108454540c0503c3e01c2800f40d62090380741d4811084e072032003480b0900d04115510201540d4080001008041c0c500030070301480002d02ca1402002480d15104c202c84a00100c0d40008504c88411102401c1e00d107d03035005c000e00d030742e480b80c0300420038085414200411746060084c0c820703c038030041407052200c5006800c2ca44803031080015401e003412000d02661603aa100078181c015150a940c498803c1964410101d099540201100d003100c11948a0a00403405602c0030b50180015120034400d0111042010507480c0840d020502094440c0e91004210790f40d050042040b19031030740c46201094640401800180c803910912015100d1000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 47019950 1250 47018700 47018717
    0x2010911041805010c080919170c030f03071d010e0108180c0603041b060906081909020612040b01061d041d10090203060105010309051b03070b0403030e0411030702060106 75
    0x442d2038415081c0d02da0010415840c0607061015507500c440000c0c000c0c2c40c640d043e42c007c006d01d031241440c13100c00108003402c0310840240307200310f401041d0018a0101c1e010000e41703040ca03070141c0100005c0e410803203054020a101713005800300000c50b40601000c0c01800d00303011030301201c03080c0020050030004107010801a2190755070441701100300f0070541500d50051040c1d60742c1c5068a050b0356035a041010100710a0860700c00031440c40d0003190510103685899840b04602e82c0c65003e1360700c1030109892070000c129941e50003000942c840f580141142940c6644210036400c0c9890300348014841640035004015011684060414489001d403200010807940800c248008400c8a070100b041c10342c54800c94480e080c040c42c090a5a90400c40c0020300840a0318003584c2d0f13030310054084c0c038100f500c01069034209a141c034080c514401c5052050701e01c084c00b2a091107484d09504283e580c401e80094006c540c0110005050780b41501488480101c0104007605504002d400a035a070b02060103000184076610 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 47021200 1250 47019950 47019971
    0x50c0d0c140706090e060102010908070b1e01060807020f010e030702040b060d0510030507050d030c060c0905060a030608070f0302030a0f080c010207060203010608090129040603121e0201091104 85
    0xc00041c29101c032220140d40300e85990b14409000e011007807251000c400404000118a0340c010300c280d00b43c00d44c100700000c1c988070f65603441c441240b100070708802c4010320181c206030070590b000b4140350207403219840e9070848c0e041022010385000080007520789268105105100901c070084117540509a06640110300002c404000400b14011a08000a8a17240c1003c00c809007582943e40b40480b40a1400c4e00c80c8951148144104a6020040540451020807102001900aa0003100d9145103840d10003003058131440028002da01c10802000000c0e07e64005000c90340041c17080100500e4500c6a030040103180d540800d031101d00d000c40203090600340e008401c0c103112580c0b04852107048200c00840d511480c40c54280020340081c06600e0024100038001400000144500c1e00301701c600e4214692601005624550003180311101e032500203484100c0000052240a90b6801614880d11007034080340603c2c0c540f0011500030034841c401c684c1820105004140840301c1c13a58200015600480e400859 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 47022450 1250 47021200 47021213
    0x705060910110a06090b0702010203010f0e0c0903060f070306051c0803060604080706030204181e051b03090109020f060703080604050a020c1606080a09110f040612080306030d050c0d0c 81
    0x42030035400d91800780e101c82c0d008101c161740c8030401d51407080100c56a1350301d40c040101d080340424080c50144200300c10090064040030901103030300142a00c0c19a01d4420210046801c0800580d200e5000454001c1840314894050107000d000d0901941c2c0c0100d9404681042200800d0201000d051000008040303038080c0c54070000c4a000e071207082e0480c0c01c03080d034800c7d0007002035000e84210900c002558140e002c0440c02806031a40c031135108690401261041c0c91200002c00c8040e003405102090a0201c071054802c06026502c5601c15000005140d126801444110a4480b80030740c441d43c0c0401031180020341103410039800ca03e0581e0b0005095880e070056a00034400c4010f40e00d05846000e030310030100e66400e036408041c1c42c115900e80c0c0c07030350f12007022840a82d03080381c4009240202d41d042e0100c8608004000040e551401080801c0c610340e5140d0710f6184000c003007003d03242501c3c00420002c19007400c0103102130005041c908185459001c182c15500c039013881c840c1c2001c008089030003400b440407 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 47023700 1250 47022450 47022467
    0x20609040605060f07110d030e0f061c0203060a090228090b0f0a0306170a020603130b010b031501020601030f02130f02040b0a0212040f1703070807230705060910 71
    0xd400e150307071a001c410501d54135130084803045504240110303000c5000c0c2030054007525042e5054903400c1d0840c0403407040103641a01c514415401680502010001c2a42c503081c140350303d45000700060796810f112042c0012150950402407c603070040144002c0000b0701c021021002c0c0c07102002e400104038600341100c80d460143d00000c0ca0f80f00c0410f180e00f80000c03000040440c2c0c4a9a10100f01c0e55039554a60043c002ca45c01d4110b065401c012040c00240c00c0c07a40c011a407184c5503441d030184031100c580d10130409210a070014881007a011040152100c000301900c4406d0f0800d000404080d89035503906a50500110300c020301070740c1d09510411114000b90440c021110108001759200c60325905441c80d2134000d40c815a0061260440f1340103030512500846d070564011a003800300081c00c0c0681c0444901840c0c9615a0a200c2000042c0203c3c5c05000906003540c07041103007001220f4825941d034803901c044a598411600480400c00c1035941c0c4c001150700746201a101003c1c2014411015504d800 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 47024950 1250 47023700 47023709
    0x2090408130317120f01180b060904140103050d0503040f03030b061b010b1309080901050c0f03040e0106091401021c02010b03070e040b0f070c0f0c030501151712070206090406 77
    0xc1108140c0c4403092100005001c006100240021595503503581081d2480c00030b200380c98a140410300340b4100787c3d01d02e400280d584803020380340519000100c00410105c0300c01101c22001541400d005208120050005d9a036854040c54840d06504040d26034445c0380340504002402c0c559503030190413840c1c81c3c1d271081d030b0f0010385100c0c80045403100008000380a01580e6289520a4800c140068448020b0340324601307a0f260051801d600300050a001918240d00012681240d0304c01d082103107414500400040020700a0034010901030352405402410000b080e8100007000c420640c0c000900f40d0340000e900c07107507003900c8120302200102080c05900519a1550803501402411808100c110744032a0042c051403141c1c0607a800742e50388000c8001442025a100340000790034007400c05c04a40c1c5031012071070395405100d0745840701c3e58030b66900d17003100e01d1404030908085001d841000f0003400741e80740d44414016a40a4203001c07206440c4400180714009000b0b110b034202144800480e1140c0d800107000e030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 47026200 1250 47024950 47024963
    0x190309032006010e06030a0f06050403020708030706060501090f0602030304030309020a080f0a0b070e01090308070c0f0e0402010906050a0e0d0c120b09010606020a150905010f0f020c0606040603020904081303 91
    0x40480c00355050300c41200b402400a21500035001c05c01600340001c80482c615007040c49a400821580e070391401525005d07100754114840c090010134000020300003041098840c010000e5103c2c54140007421100080c0c1c40381d070040b04c140d0301c20411182c0200889a00c60343c1403a000611302d0f450303c0010171481098100185600c28442d0b41c14a80350001401c5510300e005100080d0380d582c0d6080c0880340b00b241c1c0c100035800540014400c00000704104013614849114a040003c150340340e81c5404242011a4405005484410300744401d40d60080075480142280d45055450825000f034041c1444540082003406440000c0c1b80000b4442d620f00003a0240492100e2408214443e00b000c00b602c0f0b400751b0b1012419407800c803002405600025003e694554400b02c0c0d100d8a64000700410001c0c0504a01034410395211a1403103180b10941c03003840b642c201d0911005031079186541d01c20b4905480204a280502e10340082400940c1c1c0b4055241d034003a6011003003071f41c0d0342c4001c120144000300715400241b01 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 47027450 1250 47026200 47026247
    0xb07090906050607030f112109130b0f011b02031b0108060102010501030c0b1c0606030203061903033603080307030609061a0c0a0807060603020909010504030c020f010207210b06030319030903 84
    0xc403039231000620010b1030850b1001144102000e0304c40807200c540c041d50754030142000d070034500755018880324a05e682804e80100c0d020707000b0fa00400d0412407060007901285800c0c00700c2d044a0740e04142090340100b030030b00c002c021355811681e8220910101c3d0080c05018400410340304a4907070340f107280011300311000f101806125502c0c8000f0780a0740060ba41d0340d2141043c0440ca40222503c0218a4120307605580e80c2e0700003454a030800385013281c0300c0e07030b6a005030400d0b03031400360865800300e204100a510421016a40b0718003030300007c2c00caa04a80020891038103001c3e041020702c50388840d9800440b000111950344070380000a080c0b90441c10b600061100b04046030881c140078581e4883c0f000c81f4000c2c1c07001d200d555a4804482d00300c0303604460003004034280e40301c00300150a002411021030030046c0129001513844441004490714590042c00780354410283d46010410300d4a141134004200760025410072200d80d001d2952624001c0e076a00800d540d030030340c0209041c4034000510b600802031144029 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 47028700 1250 47027450 47027503
    0x1d07090c02070b0a0f050a11011802120f06010302060f04031e021c0b0f0415140901061d01090c090b03040809030c0102070f051302070b07090906050607030f11 70
    0x5080c201441102500a081d00003441100b004116468551207aa41030b168224050060b151600899910b170104081420201c0106100344602d2101210703030042998040c00c2c61041264031b14642c4a005a50740001060200c43c1000045003030542c1e90407188241c950059185010b258003481e8405007613240802c50b016031203180c2c600c80102050081e5110542a003401001d451440c11920004003408605030018003040b1801041c00e400038424800701c000c5005d41ea1907042541c4000d040003001c00c12600c20f21020080c244101d000400b41010368800402208090f0041180c0c1440ba0360703109626484818502c0348542007990140482c3c050280d01c9061070300300040c131500080b100d83e0003031051128a8040d50300005040e07045603861040894124200010701c00c10046e040c504203092602031242100080c0400101c601c540415174a0103607003850500b03000143c80d00783c0d010500aa41c10030802000c03030b0380b02852404208030390030700d94000005135007454038140ad00003003030100301c80fa4241c144 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 47029950 1250 47028700 47028719
    0x203011502070f0b1605070b0a120b04060e04150f06060c020111010b09010902131d060307060503070f1b0b040b181207030c03120501080304090e0a0302101d07 70
    0x4039080440d42241d54458030741c54440400b40e0b40e070085002c01ca80038000292102c0c411401c042c119403044055407011030b030710703504c0b4452501302a40d07002c0401c850300351080b6000d403148a40101c4000403981030140c1d070310781040b12414590180001c0c02000d8406111038445074540c01100070303806000c40c200600355450b50002c08400c900d000480c00540700b0601003049040500a5094112000781000c0443c1d00c0e01c41150029844024003012480940100140005405004c0201e820382011260440d00d442c104050502c5002e800110034000140b05010103144c0c0903010003030120103401d2450340106415001c411000b034200c001045000010108005c01011003803441c0282400c00d6444011100c02d9100e80e1225014400e1070301c002e4041c03108101284c030a65654184030b010703003000c0030208038010030001038a200346c00c003100070741c00081e040180d92080e1103907c0381c8624120140080e000b050350025201e4400c046c03541d01d40c50300c0d59003441d01455603010a80140c0483c034115850181d4441110 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 47031200 1250 47029950 47029979
    0x412080414010c05120918010b09100f0507020f0a03020402030a0905010b0d170a031104030602040810020a0e090702070801020703090e0f0601051c090804090213050a12060b03030d020301 82
    0x10340703600518040d030801079401104448445a40301028150000350030040300390310b40201180d035500c002080303418018060031081080c06030030107801c20f0380c0d03800c0c0b0501444201d0701c08044a0b820001200035a00c401a031003425a080b00381d0446810328040441070000d0b503043c0031900081e6100e40b00000340315001045602081060384500d000707202c0d0304003c20411403011544a8040e06034041d0188202c080803a40b07000b040381442c541000640c54001c0905d10690ba009604201c809a50014090101c02c60812079007a40310144041580b600400c1d80d0010000c0c404520510b01032800742d0701082119000b4800d0700050525180219248c00c114207008201c1226481200e070ba03c40741002003103501ca8449111441040180c4403546059410300094416030320004000300791681c0c60154000255104009200400d0001009a2038158013015025041d215921003403244100c508100050400481c60440d055080b0500041d901c0740c03c400f0904503c10080000345061000002003251300098901 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 47032450 1250 47031200 47031209
    0x703061d0f0c04080703020913050f0304090f0b01200a061a1c080f030709050306040c060e0f10030e0309060301080106080607140315010c05060f07110a080a030c0504120804 76
    0x14860191100c0c2941040d500c681d000304c0300107801c41c0400b800582405114150404064038210141c401240c4403e03081410041a03001a60000502000215854085c1500800c19500101320301c250100000c1e000344444006041551b840c1460103d02100c20302004c946079810aa0902800f014810796100c0c1c140c1c8031002a12890848003049000c09024110b804582d601c080c101d441d01078440d03011a40c582006140e1030412251117804520382c0c40901605005034411002c0c20b43c05418a84041c0011019140d201d001e000042540e804070350b610100718201e62000e090010b406912004042d04601c40d6a80c41d40d00070200000010300000158403840450f50f0303000590345541c5820300111610003407418806100300050020a000d80410200c40750700f6001410700400396a8180c2e1490308200c4205d0b800e803c040ba040e002c0001454000080c001d05411a0300900091140355032003400c90301401c19028100366840400c94855405141202c1c05003201f03216442980304645090141c0d540903001c1c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 47033700 1250 47032450 47032471
    0x15090601090c0809030702060f19020a030809060f04060c020705030313060806091003060f0b0405040f0302010507090f0311010c020a03060b03010b0915121006030614010509040305040b030703061d 86
    0x50b0440711500c903403910343c00780b0103400140d071820400380c0170891240c0200d0362426880070f003002080403100c5a00d00b0f801c0c2a025a0b00504011066801c0140c0201030092203134105411040400006090b0503012540c0700e03034003520000b4080001002289000310940210380c152100103250b54085c0d030001d080004a80e010b40e2551350954409040c042c1500c0300b6100c08190702d0720744c0014800114039810140c6655080140055141031000008090b140305840581d214001003002c076080c1030b4207010b41e95001d021400c02c402e5442c40c0029466507400c030703480f001d0074000104402c031140740e100328859080c13150010141c0c000c198072414813000801c50411b000703210398a450700d840204d0600e0303180c1c548034507041d200c20440110000107000c1990f949080c00a02c0340140c162002000d01c0510030301d0051405a480020000c422012040c018601070304401d125100c0b0108001c0002d07030107001c072819a200040c07019269224514254040c02054001900d0064510702d44244400c036010b0311840303081000d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 47034950 1250 47033700 47033711
    0x60712020c161e0b03070c0501090b04081e0f072003060403020601090f0605010c0809040f021803060c030f1f03020a06050c19031e1e0207080f011b080601021509060109 74
    0x11a09000343c2c00d80d1041c1d4113035007003d01c005a01e40340074940803007459003d60004242d2844650301d0540c2c2c0d007800ca0382124042800f04078006001034804940c2d46110404c03420ba07203054001d0000390402d000c1c1d030f08001c015503007030a00c4501640000d440920110000b80482d14103081600c2c0103500c41500b40580c1c406145000001c45000c030305402100204c0e04180c40c0e2900303070740f800c0c0c98041d2603501c8801d22503041a15a002c44401441920042081c6041d003405031102012030020035007001c402402c1001e9403a4184180608600c88040c0990007159424486455400e02c442d080821051684040d601c07800c5480c0000300d8542100003400d0590414041c0c030513410348030304810742162410b0005000a02e4910700000d4104072500101503c0d4154103008460300210503009c000b0510354014070006070854036040003034a0341009542c01801d4464000e00905c207482c40c0880b851a4241c032040100443c40b000700303105900a104441c400c40b000c10402c1203030710700880c41c19074600c828805c0030041450603 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 47036200 1250 47034950 47034989
    0x30f0a0b0a0501080403051b0c1203091f1b0b07170412030f0e01020c01060501020114010305030307030506210616020706020709050a02120a0603060501090e060712020c16 75
    0x52080303030462034004080c1000c880c100801103034110300c000d100700e0500c00c041206400004802c20f020b071000d02075000501e0855a6074050040ca24080f02c5c0b80c2180c0c1c0e006001040040d9520505152060003e04108104c45400d0004450702c182d401c1c0030707041c01130949111000b80036030340000a2040415460381c40511001e03140c4032008200440d800707080c1d810441e090440a511a80150640c0031404101040410401c040142240c2c030514207940c0c00e0f9540c60003080310f0358082c09010441c40f15040321000da0342c50f5854540e180e21004105404142c0ea600c00a0b0341907640c400f1030243d800803103038401c081c01075187d40180c1c0e0b440d064591000301d1900c01b8204081e1440094260241d4049074042e040702407804002c0380207002c014190001e121b400348001c20344d10107040c450301e110300c407258400318030309140d401c0080c121513068009190721424542d0038056079000284180d004002c524040c40310b1305024190600034014404c85041030700038201c2d640f2070006030315941015504d09400c0ba03480d04002 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 47037450 1250 47036200 47036221
    0x11d0c09010c060c27090f0203011214030d060e10050906010f080606040504090812060307030f020f041508030403050f03191209050304060801060f020f03040504090206070c0308030f 80
    0x21280803900003008250392200090b4075800400e41c81806040580403160503005d004c00e032003510003015481884d020b104120b0103029000f40d00c04481214821882c550404010101400150501400c01c1a00804001c05c4000403c1111078008030041c04002c06900e4209001218100303840b1001031070f020242c00300d9903140444616014500503120211011034101c4103a561000c003d01455200c2024440010036480e58001c0c400d0182c440c80100e9030718441d50240011506c0040c0469000b50321040301800041c2c582821a00003980440310600c00540c1000040d003d400c01c06101c12100c085241c0001d4818800070181050702d1040040e200400b04001c022075580c0a0000c0404d40036841c402240321071801250103544960800ca0041500403050700c9407031956006a00410009071080010802d1a07071042e03914001c03809c4c4d44050302808650700035080e680c0c001e6014540c8202da88003402002c5640b240100c071031141e0310801c000020307940c03800c2451480d003040341c40c605812407405c0011180000f = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 47038700 1250 47037450 47037457
    0x100306060e12030412080903210f0d09060603030201050901111905030402032407090e1b0307020c03060a0504170a020304030b10080f0d02120c030d0c020102040e011d0c 74
    0xd040d625030310007040000070090307000a8011000c102c3d0208204c00700d50358051003001d402d00c50081c40c100d96903d036502d040c145031640380c1c0c491100504074483c2c8542020f006108071000c071002e4501c55501da80000c516940180b00700040102490310340280042090f40641101e442100e000008101d03e07084009001d03403521594404020442c800d42c6104541800307100696082400034088890a01e50580702c1841440c4242c9850a0f02403845c0c03c0118040d40300311b10301c01400e41b00342900140e00b42050910320700c600040800700401da01000041469108000343d40c02018001c04450310350405d202550028541900c0507508406c9a00c0203407111541c0c2c4049601c100300960041d0f2609107181ca80410080e0060504c066034500c0c007400081d005010030103a40405650f402928480314030300c1020380740c8000f2400f0f00c0041c2d603050003c00800d18000c004e0365150700f80240041403010a66804074024072494000c2c072001000d443c0003203010f80d01c0d00e9626000949a40d14038101e41c540b5000600c4501 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 47039950 1250 47038700 47038709
    0x5090106080d0905040f02040e011e0b09030d0e15070309090506030316030c0f0c0e060405060f010e0105030a0207080f0319090f020d1505010803090f0901030807080f040b030103030302040302100306 87
    0x81c00c100e000c000908240c6d00c0301418600d8030100505040d140c0400303030260b80c3c0030f81c0480304200d040e002d8850002040954440242034620003245400c60f4000800d0311800d4202c111400d0080820f4084119224100620401e4121500c2c2e150785845034038000e07107040c03e9400f032540710030b18090001d0700720b00340002103c00c84001d8445041b0f1074101550b089504135551310040711103c4540402d24005030004040c080038150803030704002140380800c244401c0b6040102020300c00c5540c0c802c0150785907008818040302d0f130401e1802a560b5030740c0030603040c00703841040001014144c0018141080d4444034000d18020071070340d100100884061214441942d94034a0040c01c400c41102480c1c0052030041e121242c5136204445019a1011491140007125800d0380049020741000a4180319460603004d00141c2040849003480a075046450740c064a000d0500c1c0240710540000f4004402980d120507a4018800d5400072136036980c40e4600100a908984400c901070484244c0401360300e80a4001c80c401c2c0c8 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 47041200 1250 47039950 47039957
    0xd0204140d05060c0d020408032809050907050703140d060302190e06040207020f03060708150301020304050a020108070c0b04050c010809010b10120f1505030c030708030d0506041b0305090106080d 86
    0x15112408101840c0d8414015000600c6c0c0c20000090720b4101440a0700007020103410414502074469000c00f0fa00900b020108104001c4e8801804181c0e6548030560700200e844c03602030780340c84940c50140d901d08804001550000004622700d6510b94454003c2c1099920980e03481c040c401085ca0090200d000502800c506120210009003642c10564040c0062500042c40c2d500114000d0010905190003924034600198403d801c008031841a985144c0d500380302035008515510741921015251800d810000341040048804641c0080c4102c0e007004906400001d50781003810b06240081e42c4020444400d40401d07840d000143c41110180f09454290902504169900085030812925005a10301c0e04d428160b85400082e2003000c0c07031007413000484d00c554a04503030300d00340000c1525003650f0900280c4294401d05090110742c40100503035980721101400843c07280c07140c0300042c000c4d103021305590202d0034614070b1080d01d040d4503030403150060307402200070098540c17902407081e114040c030f5070b604021 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 47042450 1250 47041200 47041213
    0xb010305010207051219230705010c0e010507020121140c0703021e0a110a09060602030309010b1207090218060705030d14060a050105030414070612050606181e03030d0204140d05 78
    0x780340c0510301134403800784007001d96003030300e0f2222003641c0488c1c00424040d03a10b0780d901c1c034080d084d00741c00910030100600b090070702c5400d120103680006c144400d00d0300c072156100e00104442c440d9051680140240b10251060b620040c0341c03484c0c1c0c1d0240d64001c040e050300144149030503a1550084004a410300100803405003d1710312503070b00c4544031481400c001c690070901c001d2000503109040e00c1050090040d5a0180d961381c107244c403142c0e0a445424034001e100351454484a41c4030400003900030308640024030056212000407145003a05811283c1c091780080b000030f80d100420401000511062407507070801c015102c0e40344426080e102c030880d0159040070741d081c000c0c0000e600036005994407a100e094102c0d824061990310303074142480c1c0e600000100c1d0340d0000d035420b24456070150b95070145041c0d03400c1b070415203144418840d4105400440d4000c43c0c44090030145003800c4410307070020302c0000c1c04490780c400740b080c2001c00a60152054103100c05071602100014504140c00c0340d21503030420018240c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 47043700 1250 47042450 47042497
    0x2060408030c0d2604211706060f030126030a05040501080a05060f0415050d0b1b0c100c020a0210080108010b0a0b09040209010c0c0e01030c05040504030c12020a0b0103050102070512 80
    0x6624801420680d01c4d801401d020954843c5524281a128003960f0b880ba41c0c0d02012040b41e1101f1316001e00940d01c02c48042c4040104881c0020590b811130b8030460301141c050841141c211407141c00d2510003074407800700041d0b00c14600e4100c070060044803802c0c2c0e980000d641d1412900c00442d00c00323036501903000103210018007903840c083d00302d4840c407955980034224080c8c2d1040014400084c00348200ca80000da202004841c80d02c05011005014203040d529180010b403480e1242c0310040c1e40e100204507641c400311801074602c01c20000e100127038064064000040c0711040a0030700d4100f403080190743d6080c8040a11641040c12110080381e4032036580301c1c00c1c50300ca28204030103500a400352504000030210010041003000900034010100d10646011550450801080c150056000135018a0a110501001a07405040d00ca5941c0d04001041c6010b01c11220803404c1c0110894044d0180c601d1000100078000103500038448a4822400c0b140c3c00381040c0c0c22141c0c0b03802448080440f0b02c80301e441d00c0c40c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 47044950 1250 47043700 47043767
    0x2001080901090312020906090d0c1a0304050c060d020c01053c041520091009060219080418150f0308040e090102091c02090108030906040b130302060408030c0d 70
    0x1400404060810708c110000c9031921102400079100d415621000f04040d08002075041c1ea140c01c1415036a10f540382c03d490700d90340e40213925422381c003815001900e95810211a4141c560440e00315000f80441d04000e0108180820b40d440060a10001c1000c400107071103c0a0131000245000342002e40665a2500d4980320040c080a1802150303440c1d10003040c0c107650710144044524040000c0946850800040c0310300c0c1800080300006000c17244401b4000c0031703000114070b240c5401092550b0402c03180ea103801d1005003da43c1c00341c0c0000040017400d9200402c19004582e0210704103110340300c0f16a0310100300c5580209880007401003041040103100085a030311340c095108130410005483c102960021588100f0501365003029000303006141421481d100001c03a004004040007181010306400003c0c140303100318824100b501200049a03c10200744214000055400500c00c0741c4072541e4062594aa900400100303007a40070703031480c85801600440303259018040c00500a079842086003c42d4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 47046200 1250 47044950 47044957
    0x1e1006030e0a02090708011d040c091802190618060c08280e0f01030608030f0a020f07031407090203010303090b090613030503090109061d09040f200108090109031202 73
    0x141d0380c600039840c28401580368101641d000b6991a62050100c1d071501d0100300702a07585501d0891201c003040b0a10000c41c48a21010302521480380000908580e004510440b10005400c0250082c01807540e4907404260004081e007114010384a61030115402c4081e0303120051140903000c04604030800d89030120345180040c10000312840030862a1003450b440d0010001007004020340080e641140d03030b400c9401c0c900808012000300b03080610040f410141c0190b01d07402039820000091001068500049100b004602580005407003658179046c0c80303007040017041c0c082c640751959034403070f184001030091a14400c490480c0d8060381e509640c0c03070071300394074180960011060651240041c0050ac0704450743c82040d4006510805c019a510340c10140054207006c0140c1c07100c0e00340a6541d94403100f20180c00c03880701c011442115640060b64552078500307800d00140c02c001c0d11000c0c4c0d130049400d034460714000d540e4150400340c032a0707c03261307482004050985110050007000168100c420010020454015 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 47047450 1250 47046200 47046221
    0xf020f030c0604141e0a060f02030f0406050c0405120a02010215040b010501140c1f0c0e060d09081e070501060b0c150a0e010e01061802030103020a03080f13030b1e100603 75
    0x65550030980001903540c105d0080e02c1c11000d68202040c110100702152144d0b28104280b000150305600d0030350500000071348002c0010f04001c0c0c841000980d03100d40c06084902500c40240b041e0481c00761070104d01c0e662100b4400c228054800c0103d20704410101000081c4280ea0115496010b83e09280046801c50310254070702e80030703036018418068840010322684410050b0003c070304501c2d46180360940c0584035010410b40a004081144080c0c41c1c07541c008540101c80d403001c01140074075051400300c8030761080700342c0480204148848482080d01030402450100c0c0994000d00c400c644370040c04055100340f038020380d1503500c83e0303501c0b4089514003080258401c0a9070390024080d00c41910a50a4589454203480241d545041c2441005082050030001c0041d90724210f0540d07065601085011000e030201902c1314034049201540001d20b0401c44003c8240e210044072010b0380ca01e041410307110706440ca41d51040d40300c5801c8203421444402d10f4460700000000c2e040c02441c2910503001848102103 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 47048700 1250 47047450 47047453
    0xf070c0302011d06090601170712020a05090103080309070603021813090b18060c0c2e1406100c0206090d020112060611060a0c02030301030209060414070f020f030c060414 75
    0x4108101c184481d111442c8001583d024010314030b0881c2c066402c0080c1600b200c078454644608601981c2c03000141001a074206848030a092011400013a50b540c880b0f610950380b200590300007204102c3c01c40091070007000f504040700d10103512030100760b00340d01440d24140444651050300c1042481c040c0200b14100d00168800241c0d0700080d00d8024046074100c441c2d680340e074552070150800c0c81003000002d92101c4ca8000701030070100642a03123034984010031040820402d41041044480ac000036a540342d22443d181d0401c1b0b0001c0c3c603440d042620108a48491046450301c81c82c00e400e41c002c002007185e084d0300411007031078810984108014005481d80580c10014010b00d01d40c0c46e41898404c1002510880d01c0b4020b0304903103942100c0c54038000030101e006807070605080d64101a000000d0341d064950417114104255111400b090080108089140b40c0620503420700807207607040445202e205140340d09a5034800c03044980e042c6c2d00d00c2100c0d4207104a51001c40090041440000c061203800b65000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 47049950 1250 47048700 47048711
    0x9060607051203090d020105010807090509071212170f0c0d02040b03090601150906080c09041107030807080619050906060f071a13030807230409050a060803030f070c030201 76
    0x8032068a488000700768002e0440000040c0a408001004000602011031009000c9903050426143e10b5201c80e00c00d00c580303103071210040350b01d806052200070301a210184070015100641e0a2449050b0075402c255800310750b6125a803c0c07901c0802a282c1c2c81100c0119060340c06031240140f5014541c00b540800e0202642808042889610344009502456815008200a505045808019a404102c660240620315a0030000c1c140c00007040b540c03000700000c0043e110782811010030090006089498208600080c449c0e04040d0817841c03c0e80900900d0b520f80203241e0b01c003810b100c040760310103043c074480b14014a020803551a00e0030441e50300c400007a000740d09110014407820460340004c0c908480d1049081d00011146981e9040399501250303141c0f035082808050380707020700700703540191002c1d040143c5400e441480140d8a031180b03d81c00c4030102c0c500c1d6569540c4044000030300094a6140780d542c01c0c4100060300c450b000081d40d01070b03404090341d140e298581400a41c0c80c05907840040702036540b2030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 47051200 1250 47049950 47049953
    0x30d052a03031602120a031b0203071502030907050907030c02011d0307081303240f0507170702070b030a0b0f03030406020309010f0e03160305010b0109031e140f0d260609060607 78
    0x1c040d194801040e01e021239081d000c40002c80603454440d04000840d4000d0260030302003029038680c140b84c15000b550043e03981d01e95034801420b000c0650052604600340c1c0060041160b0b1582c0711101640503030b4005c0245102d28000b040240000321441c110690041c400c190101d840e540003060417806100b400248540d507540d4503004401400d070f40002d007a00703000d9203800c07504a901482d0107804100c001005246800d0f0030103804540254800c188505003200002c203840c0c02040100c3c05011031414158403850000ca02c40050243c0449060107454080c00d4991a42400800d0b201980c900d900518182603419004468101486100c24104014009594116142480454821041c050300c0b107140f6411420039600351340a0050312410400170000410106201c5882c140f2a10003025000c881014641030406a58140110083c058095444400000d5074001001e85034501301d074860402c008070000c00031070546083c0701204102910203000410a00e880038200e944484028006400c3c26240d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 47052450 1250 47051200 47051233
    0x3020c0f030a0f020105040201050f030405010b0414060316030b0a02031017010b151305100302071e02270703050c12090703060501050604060e040c02010209030d052a03031602 77
    0x99880a0001d4000107002c4400e035034042030349049500140000d00c01030810b86d00007002c0e8803950020b84003240c070100114007004000c3d00000001c10f80100b0a100a5283d15441c2d022800c0581d030740ea1007846041c008140c1e6001d20301010040744d8102c9030b14201d5955130103c440c00f035400201001000712041401141c10142d018801c0407098000000003441d0002a041c0003101e0101f40801c50300320010320002c20b884034a840c0e4031003503490580e081001c004491200307501078082d009004200148000c0071401103c80f400d100911240204d46102c0c1c0700c200ca582c4011880148461200d010741d950000581040c000e4101d10340080e440e41509180581d02e140c01040100c003a6561a443d410040d002c01c24400d03207000306805400c040790507502c1e281c9840e501915998050704410702403511082c14607001c40c006e6055580c000303000380641e9660607154000500c1a8803050207200c0c108003501c0340301e010600c090b60ba01c6060151a0003140303903440d841042c0065156507003013207007144298980b100d088bd00303 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 47053700 1250 47052450 47052463
    0x304030203070c051e12010f0908030a050a020703120902061902010b0306070e01120f090c12050d020106030218060d051207020a050d050705061c021209060604051009020a03020c 78
    0x299000c0e64882005203020791002c501540010b100b43c100720340f141c040600241030500c04010403245042c2c090200f640507400b501c0c1d401c041c4501c50f8a40741c11402440481d00041d0300c1003d0440c0701700000e656040c045412405031440250010f210b001800703010b10100c1d40032105a5000130540d6040c071581c80f015806c0c101c00d041460006075121074203584582400c00506030046028144100c2640604000916a501e45003009a07016150619005e011403d5440ba1811a42000221344102d0321000040403000040c030046407540b2801f10041003241c41849082c1c2542d42c0200b0f0032740c03010500340705d10310904400f40c04c00e07501624160f561030000e03104000c400307a10602e00b40b41d5519003800c0d00410502110b282d0005d0b0045100c0460b400018030003050100130389004a4680f9140c00340781d0507180e1024414400905003030710014028208124000303140b4450040c5008030780c062b5a5031000d001c16160155060306240d00d44241c140701d05055500940550100c0d0306d0014100145288003034503051 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 47054950 1250 47053700 47053703
    0x1204140106051512090703200d081908010603050421030e0601090b190b0d0509030c070f030605090102090108011401110a0c0e0106020f0304140a0803070b100501020f0a02040207030c0203030304 85
    0x420008844074401e440041315540503207080081d00719503107140c840880c903034030400e12003445015901154030141d6a0800c1084040c0e007200819480d1075020066815941d0858502c0c404203045c0b400011b49240300e801550b10440e488948040c0400c0c03020f0500140107001039220003815150030110060000400141d402044100800700320a96641c0c1407010b505078560030120380f0043e2503000c0c803006400300e00303d44a041080e400000c0340c1e5101c1180c076080d030156000388076142c020000001562040c1d4500b044c10f8a00414007042079481d49480c4a0813071044407034480c0421601c0700100943d2078240c0e2055100341041c10b24072080310b186c4001030b00300300030f0071012241c15030480340500c10006148000c6014042c40d00051404081c5032a40650780d00032481090301c03440c00113583c0c442949440c55904000d15110040300c5d1240c105281c10320111008031100130341d020900c07000150f250720026140c030f05101c2c1070005c0c042e041560780074040a540111001c4d018000455007100058404100862249 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 47056200 1250 47054950 47054989
    0x20d14010506040b010e010206131a07021c032a03110c0102070b09060402010804080f070606140f041505090a110a05071a04080a1d091f0803120414010605 68
    0x1880c042c000c100450301e11000070b43c104402e02085070490b0b41c0008846400203410128180000158544641c040d40c05080311101400300c1d50070700815640004280700d1006003c3d04142401c40c050504a044625807104014441040752001d0800309240c803460981d00050f24000c2a40001c002c4565120b62000156402c107a60000d0382301c040c0300c210000e540d04451484040c1940b810550002044400040c2c400340c0489c9000810400c251240d101b15090345611840a00c40039607511401d401e540000c0c0d800c7c600491a004103000b40d850988070343b6007001a0040b19600e0035040c07100780700354038030000c02070b4006940c0d503d0740c030b40040a09005810a20a01e1303071910390f40c22a5141c4400d2002100c0d0504030710a00c02c0342400002850041690144501031402c034104000c02035111038103066074082560081d03200303420b1098144203451455600000c00c00c84142c29540c2d042d51603607900c0f030645078a6900b503905002c103000a500d11000c50094a0b4040041405615200011001039482c602c1000300f = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 47057450 1250 47056200 47056211
    0x5070201060911090102011104030c030803091f0b031005070f0c02010228031202040303020a082a03030601030e03032403030d02040e01031e02100f0c1707140a030c020d020d1401 78
    0x40d1b90900600c20001002c500c031030705143c80e61b6280e120a10075804002c1440c2408000100b07000802c00c00e91045185032055000c4c1c490007000403100910419007c94003900400b8010034028030b02d401200d01441c815502d0790100c0490407402c98104081200890450044d1340720081303040f140034158101413814621a140341501c40c600540b400140281400d81d01c1c4c018001000403d0b008145218910b0f00000d0039952510f60400600d050013040c080c01403d40f81c030407081214450008061440741c036007a00d040000c00441c06146903a0300044030007c200e140700601417039003002c2c050040002000081c0c2200d0512420f440d003103069800c650888484010658010011b204010310b51b42060489142c2c20003000c245030b004507240b15038905000040c003184180040c0058030401c2c0f002c2c1032507086000a9070311030b07441603500c90300d500508040ea02440c0350703040c0b000d107500041001000d440d8151600c14200711a68207025080890840507a40090002d143c030780442d4120080300c0f0559201da000148 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 47058700 1250 47057450 47057467
    0xb040611040b041d090703050303010b0d060504020c100507020a050c0f0102030421060b0a050d0b06060408010f0e010c11072d08011b05090604120f1208040b01050d0c0905070201060911 81
    0x44190005d0020040f41d00c20350041010a401104490544149156407641c278501080f98038058841c1c1d9011b1034000384002805820004003050003051781c031000e5001c0c4620346136070f04201d03a03c1544035009044d5812415840445241c00d0002c03449115041c010707681025650b07060000c1d041c02245039000d0343c0540c503102c0020441d00780302c0d000e080c0c2002c07180d9800d0303181420f01003a4040280c5c40001d10758407035507000c0348040e95103000f034500405502000b4020014001e5a11002d402110420b240c0380d03007044600c08000d8040c0c40c41003d50f420440c003c2200c140b80002520b0304400950f14809103210000b103112016030300c0c128510190841c4d800106401078100a1a80a0850540c0d10800c021083c0a00d0031036680c1d00044500b11664181c2001c0000d03100d040ca01e181c0c0860030b0008200700717a6940b00200080d0080c45241c0b2a40c016004507156aa0303607801d00c0b1041098030703401492080300a03001d00c04449154091034200085100014600c0d840c0c0c0c240c0703012034020303171541101048042004103 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 47059950 1250 47058700 47058749
    0x303080411031605040c0c060609140c0304020303030c0d0204030f03090e07031103060d020f0603070c0c080601060e0d060e0709061a070203030a050a0210150612090b040611040b04 79
    0xc504140d0003043c8403960103424552031220f038051648100e89a8000002251180407102031039078202a00304103c585d9034203c0b80052181d0982604d014007030740006200744d10844252845103402a015525540c0c0e600c903518010392150040080d8941d00b0b002c040003207103040d070b80501c030280b080d1070383e51149041944400035114000c2c206402c05007010100c030491b038805025290842419521803910300210320014042040040c62950020004410444003d40c412541d1008501440c0e03443c0a50351100040c1d611500300340a8038002c11071302085990503007080e1940c445280d020340c0740003900c00940c43e04075080c04000c0d03000c1040c00d502c1d072109200002148a0b00e14000c900d9492091400c2c00f2540401c1c1c0324011410240184040418080080c90082c440e4555014a2510402c2946000805d02001c0880390180b0000101a842d014050800511407411104c0e008080c1214070754450741c038000034240498102e20f1000042c0400070b40780071440b0181c000780141441c4201c80070622000701 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 47061200 1250 47059950 47059973
    0x207141c080c0c0c01080c040b0d050103020a0f2102060d020304150b0d0c03020d030207050a0906030b060103020319050402120f0309091506070803060411070f0606060504140f12010603030804 84
    0x3002d5080d0108158201528001090241d004080c24064529900c2d066101202e00950b840380803184800540c2810001e902d5102c1c0d81624422140030440070b46580b80749807500b1990048030701d008140081c0a4101c030120784002040c0307200401c0c1d54a4081900303c58001c4e6001920100c842402c5456009604c5105000300741c070340901510614050162615240030044407440081e0061220740070103001e161090000c0e902070318001c0d0464200780d23511141600140b160b0320054807e8103055000c140158824021039016112003600b0518480a20790a1380c01001c0290040b64044c508141c840100c02041c49103200c0c01d20141c016540303d0a032407083c4072901c10010b1048200e0a01c5980039551030703856505685090350420310603a126a9984089030083c0104d01d4141c07805440401d0080c00c0000d00c08020b12250322422041c001d5680d500015140c038012070043c1c031500c01c0310414007003660030100b0240080c0b1b04018542c203955100c822089007110a03e400c10b6000810f048100800d201000d40381 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 47062450 1250 47061200 47061211
    0xa0503060c121305150103060e0102030f0c0c0c04050109270302030a0f02010b0607080301031505090304060e18090304030218160e0619080702010609140103060207141c08 75
    0xe41518a48900041c410b840707601d1a502003000a60701141850f1262003c1d2a803c6034054119800d60051040907644001c092104494242c2082c1c0702d0304500c07006002303a80c090740d202500c801c103940792400300030400d8000355200c940a01c2800710040f5603075100c2c02441e008100d40d04002034401c0401e0700c0302d2800c3d6000c4002c0d0200c0102190b00c8400240d002049a864112525050000c90000c0c0350883c00752440c9904039900c400c011660500f8401d6000c021812030303103d4103500c03e4940d1102ca00c102511011030306036426400601c001c2002600880b100080c8040c014a50402400c01402450742c1c88030668403a409648080b50510031420002105142d12a110202040615001406482440c1d405d0000010400e5810080f083c54540005031000900e80765100d901c81181240000c0144c142201d0480c0107600b0104d0020340076400784110000909a03118103900c583c00c60f110340c03000c0c0d80210411107103c14240d541c15015841840042034403501d20489114503070b60a403000f81001c201410 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 47063700 1250 47062450 47062453
    0xb130518071103070c06030c0806010f0801180b0303040801020915030f011514031509070c0803043003090b0117030d0b1903030c140a03051c020702040e0c0a0503 71
    0x310303500c031808203110a500c1080c500e0019040d101040c999415805081c90050076905105004a08036030141c10052889200c0d94849901d551000d0046403882920225000800d080310014884648c0000c0c1c81081002003110109582d000c24011a1450f41319501503400f0344d5000c103800c600b0b0315100845041d91992044c07500d0840c00c0890403204504018070078005843d480c13112640c0b00c0c6015807140f4102c03500d00c3c00f9003622860100e41d01100745203170300d800e184a00214000100160b000b44a0400300327a801500705419503079107a440300c0f0200300001c522403a002c00305840d01c802c1107e255090040244c0d03a5804942d011580c5040d802046040e00b00440c2481285a0540381000000640c1c081d0010607001080350302d00d00700400d2070000300740c5d040300091290366404814103401517015840d461265400c003812154001c0c5c2a61613804c0008003e0001c3c00c01c104541864941c15500c1c0352506400c000181b9003001c0d0b5000400311207401820000c90742000900c000300e4500381003d40001d00040c0e0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 47064950 1250 47063700 47063719
    0x9030a020303010630050604050c041a0d0608030a050a030507050702010c020d02010327020117040210110f10052d0105010525060b2707050c03070b010b1305 69
    0x500194403404140a584d04100b03200403031402c0c140d00c0c00c0d00a11104641481c0d00b44080703440349050007400e0100c2d04240500d040101045050415034100c4040350005048911a00c51224a500440e48011194280c054580d8000720b8a5a000d00007810303040000c2d101c0c150399607268003014055550040c0010148103041c440d217000740c0d800c8009028032030760440c3c910503ca0940d10040e002002c5099181180320b60500c5c211001420380c0d804c04140900076211100c0510580c042c002d090142114002e4101140e880381c0307036401d0700406c142c0136200c501409a885c0e185d1081c0c602840d01d03414410603000280c41d038041c00555882c001e00754078002d884252007010304100280c0082d91a40601c589810800006402413606159020948520b00035803c06918030110b4203081010304040c3c484180300e107603c1352a13190300080003000c000e0701c04001d00d1900c26a55404500f91210f800080c0c80600e00c0c001080854005050460418060700c0455140e503100d100708908001d0310402500201e02901520 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 47066200 1250 47064950 47064967
    0x10f0c0210050f0106050307021615030e030405150c07031b03021e031b0f2805060c150402040207060c02060103030809150a0203060f060c03040e1530160503060903 72
    0x703030b20703ca05407022810031565035222860100d1508050180307003081c142c50000c0101e50301c80100004588480307555028000003040c15801c1f5282e205601c100382d804030003070300d80da401803503903102400c108201d010941c4e074620b603651580e0b030990303201c50111048284000300901c2149055460614003200303201050b03108480030310100c1d5482240300044a18031084031042c94859955588005107a000904801d109520300f180b50b489029910b81091a50210150301140500b400002c1d200c08103400300090113610b01c1c032a150050000c000d80180d80158003042200c010921900960041e01155070041496624608005040c0343c0041c2200c120350700105465080b902d2403040d4150840601d5000503625250240081e20408200e501c454101c0d0000c00d00b03100b071801c04800b070400c07602c24a21000c6503581d42400300b5a0300d1000c40c0402d41c4000040c5988000451031203841d01d003d041000d4400c106146404000d284c030002c40c04074040c2d180084c0c018800d6003001d01039180c2004504000794100800e6 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 47067450 1250 47066200 47066221
    0x302040308030402040b0415030303060e0601050708040b03091603051c14181206010b030a0605010c08070f0c0b0316020f370b0109020c0f0a0c14040b03010f0c021005 73
    0x10304040d1003651156443c501b20303621540203c44c003042c0d1400036500d141c1e0300d1401901510803072280c640c0d140c4058000510950058003141c0c10181e008150600e06820240c0601950b00068400e0000744100031088030000ba00a0300c2e9006180114001e158000102640b11003140c1900710386020020704241c2000030800b454107840d5851101e0f81250744030405403010500035550a00c8043c1c82d485494000201000e029005600407802d001c02400280d445400540b1041120030000345040001c000c1180400d051245104a083c807521603840f030345076201c02c080140d4100385d400c0c0b124440301880e45140b90750104045002808c001010b4400d0000344030300809072001c01e40d000b56140840701c41e0902d41e010440000b40b079559100045245039611031201340b0003034110640005152043c020350043e03105000650007070741ca42c080c0200d481d150918071048061000c0c41c038465080ba4581b80c8200c6250703028064600d2809216800140741c4440f0100245003107905620100074601d00014415020385 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 47068700 1250 47067450 47067457
    0x61a0a09020f120f010f060c0203070303030506011806090609090b03070b1c020313020a06180501121806090201080f070c08090a0312090806070906090311030a0b0c0c0105070302040308 81
    0x2040880140c0b128220b110034200c5102e8090681e0300341030220104111884a245010b0688042c1c0b45962542911818150f0301403a0352900030358107910005041000030300c81d800542c0d00c100e06140000449102105c281040350060304020701042d109401030204607401004007005001a6005010144120005ca07480d1a80e034054414900400a6100c1104000c5180e0384810070800d44210741d0b82c03810ac8110182c1101d02d640c124071480041c000014010710410024840030102e252070718020346000b005440d0b4001c2c0c404803a8209440d0482c1e1070403030807107026072206030f4000d60010400824a200043c0350800007880c2000141d102d0091062450303000d01041c1041d0b030300c00400c59868420400194400c09107178401404451421258810790368050b03c0c1c08221861103040b1221601c4c1d1500a0740c40149500520700018441c00040022034451041c188640b007018043d10034054141d1107084071140201c0d000d11610100080e2b00c041180244034403940a45030380b80c00c600381400d5503101e00b594030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 47069950 1250 47068700 47068709
    0xf07020d0602070812040302071703160302120a0512011a0a030c0504120f06050a0c141c14070e0402160b0402030f0d0e0306090c0d080307090e13061a0a 67
    0x581038080340003041031580c101d41625801002058440b4030b00b0180702240c1c40201d50417001030064005c0000c458a0303140020b0241c056880103507060601c0f4540c014614007240906404520483d04a50f4400660000906055501e660f4003923694405507001100f180d81a88241c1e8512045144c030803030500110151411170605143c00b054a44620408840c0c80c02160048a00d004030b050b1480200a030007002480d80301e03c212001c0c41203503101d0544030111812445101d01160198401c1c1d605804107e0061500c41020511000c2088540030100100c40500d00c41e1b041a99685081c40305450300030012b0700e048601150154074140700c01c1c00c48140041d03c0c010003030101400300b001c10110740e400e0050009950f4201c0840b07030710340c0d0700a0303000381100c656044142c064014240400d50742000410100300c48503000c0c2481c0035810240d03580a01070360009043c2c4080001180c00800c41040d1b00076070b40e016154079010020581014105a0122003686c04811807030180000e10411075143c0040380c80468 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 47071200 1250 47069950 47069959
    0xc08090a031403070203090a150320030105010e041103010806060a0f0602030a03050901021c0617060c0301030f031b110406060807090308090103060e1e0705030106020c0915060706200f0702 83
    0x1352980701c8141d00c1c6015103410950302c0590920003040030b0050b82450f140310440d554040c801c4158106d4001c4c05c41460505070002036208000600c000e501404030031a01d80809040013880c5811110f0911640c1c1003a0410031480c1c000c9410720003107240c1344011002a080540325011614603000000c0e580c0e01c9490515003e05845030006580440294160360800b400305040850511500c01d8020081040b40160003400c03019030200e07410711000041c014400e14031001c90a2850b420f645644000c000c101c0002c40401c8620910300306600824880d07101041d2088003128240e058a200b0030060700d1841e00144208240507041113000d95000e004071044075000081c07a680c411140004a018007065004001c04004c0d110900104040f152030410490407055006440f40d103840342d00b200c02d80300a2146c40010391014501e61643d01d009001c954101503510f44040b0508090804244c0c181c2141d14199500e03903640303001742e2154000b00c0c11800d04100781c12605151541c030b00f0608456004001019008 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 47072450 1250 47071200 47071207
    0x224060904080d0f06051203090a03061814010605090604020703271d04020f0109030c030b1909050105060a060807121d010608030a090503070b07021309150c08090a0314 74
    0x1030150320740c100c0f150002c0c1c0240c140400c00e40100d400c000b130600351050724000d0040020f5480090000300c140d482214006101d41d03162403643c1c03143c2c4098161501c0c5101c4049a1410500000b0f0305400da8040720348a010011807090700d85010014050401486280203900400400d000694040d0541030044c102c0400031000c80c103080500301c810089500301c04110106068007807071500b4080b0301c0b2485244221209a68001c91200442d0322640c0c61200a113205040c14050000a41301c1d580ba42d8080030241840c0c450042c05d4000105a800d56682a220340e552078040c4011400c225403060040d11040c1824101c43c01d0a450060000403c4585504040d0746e0760080910503000d601ca11059041100003444055251500c8030384942c01008003002003452103100003200d0801003000c4040381d011180e160304000e060f1b000e000c90000b0400007808050742d22074440e0700080c40d01c0d11007084111845400210b400301010040c0103503201400070f855070303808541c100c00001c0d030040c03006030100f60f000a101d85 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 47073700 1250 47072450 47072453
    0x111207050a0309120e0f060406080627010303090311120c04020f04081b010f09060804120c0204050408030a0b121c020f0706170a0b010903060c0509090406020306010224060904 77
    0xa00324414000c18140500320711102c869401117160000090840d03600030400004030801206110310710405000c2403881000403018900303540c8840403d4503401c400f24892624040089011009030000c8000c1124140140148021341400f082d40f05010b60f240700f45070b5001020141c0c0d410800e11040e02c02d80e0005602d5080e0b40c80042a1b50051200c00100ca0341c0760701d90342604645542d00c1c08500d0018000000300d50903107106030700d00d504803251900c1e203403110385850312400c0400002d082510280403201000c8001a102c40c480c6e01c0c13255019005998490070110048819112858070a5200f03503224031312070b0342c00400410000b08582d41010300600301a0078505c26400d115500c0380588650040c080c00213441e541080240180554007010a80c043d614a108207044a101611060004490303a5060000800903800001040102e052007030410985500284d5004000c440442d07270b8640100500c1060b5804000b020012a41c0002c0c426104144203286440c05100801c002d1107841600003150 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 47074950 1250 47073700 47073707
    0x31e090103060504060b03040201020c33040e07030606020c10020615180108031c090f0209090f0d110d14031513020c150105061c150b0406090801111207050a 69
    0x30061402503c14884140e82d10390046c3c0c3e5400481e416030240c09600458105480e0070383d030061000e0f114078000c0e2610581d502c110070f400c070300030354074054184403c20000c503108625840d050304c00d003d03980d408100c040c1000700c002d0516003050b600502580d107a145c0c0c401d1701500402c88540c07040210280d600e40303641311800502507808601040010011900c004507044001000500c074074410300c141c60b040e01c402990513a040300c91405001c0d1030991000d000d48014584050250340200f181030442e02400547e09142d810a00c0e82c40403a004500001200b01440609011746203040c101414403140c408445d004c802c3c81444005c0080d80d03004081e104800c0301d6603030030985500384040090110b44414010102c995242d6a03000c0e01012001d10400006003403610408413646070b1052051a11480b16000f03098018000e8070005411011101c1c902040c440220b2002c1c0c0010041a5100011586492500341c02c40703403040010541c99400300181046486031100540e0441d0043c54425552401240101d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 47076200 1250 47074950 47074961
    0x60609140a03140303010e0c070803061c02090c07021201050f0415060e0f04020f1002030d0207050a08030403090f0b09014505010908150103141c03020318031e090103 73
    0x28540034800b202c0881c04140000610b069070700003031f01e0900070345074800301001a0241200051200408100003805814144004819886210504c02803010250b00181181004039560002c65a000c10070310258a020240c0005644103d0000c10080c14a10503103800c7c444000c01c05400800c036075410441381d110383d902941c02410a0103c1080700d040440c804080c1032010350b070a0f403181000145d105042e1030103111000721086684c004520388440010494080d4201c0c00c82038a89000b8100c0680205a0700001544203510a40e1010001c5042005250f4004901d8000c10000307074050010817210b90308030315002d071035800942c18283c02c003146507a1401100c86059005c000304104004011558000111071030650f03609032101000d00c2d407100d00f110743c3ca4080039010410524008010230100340c04600480410900400b039032180c86c810900000d05166140c41200000d07400402c1050400300c09228240c4160900051480c044442c00071005a80b48100702152424000a901c0717090780c0294080c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 47077450 1250 47076200 47076203
    0x60307051201080c010906020114010e090106090615020f2113090903030606030b030a0201050d020a051603020705040b090402060a0e01020309030a0501020306040606080f15041d0a0c09060609140a03 87
    0x100001583c490703010356110311005500a0120b8905500810f2090043c064040c102070056001c0300c003603103082c0075042035020287c0281169541c55502080680480c000d50007d000a8901c448150342000002850040d9881c6410704075003107030071803040034070240b24001002c06801c011180c507807013400d00c0d080c070060700c0d5801110b42510301411f074410160990042011075150343c03020400c21a4803418181c50346980c40b00240002d20411000c084008554003611316a0303010b103002400c02000084084002003054003c1c0c000d80d1004038104810f140c903015030360a8103800c0d00c02041d10b091581c04140e49019100200c001c3c400d018402e080700b0b920030400d80b240307004000d089480200d45824903500070360050361458099410076401040f0240509207450161400706030f00340040c3d03a00031500c090300c03120184481d070168440714203019000072044d1841050b0200f001030031150b002882c0044c141020740e404600e549060000810240c5c3d00b2503650012140d280383c00c20011501900020b02c40d07440c0307420 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 47078700 1250 47077450 47077477
    0x403030b180a060b16020111030910120c02030f090906030f0d030f140606120406091506091a060d0c110601030302010501080f07140d030c020907020c030d17040206030705 75
    0x14900c41101c4440e04450080c1800e050402c030781622000710160911600001e02040c072424850b010055100e510080c034180001002d030ba080140040002d070500528081c68400181040340e1010026800c1c42803814102480c0011842e11902009070b010310301400d804244900081070015014ee1403d204603014040c1000039039981404003640600249441840d444060b8036210340d051001041d100514090900204100c3c03c0500d10029440c29010041080b0b4025031200001e900041c1240441c540b04000f01a000c55050300b80b0403020b0850702c00c2c450f286003420441d001d02a5a03140c4108580c1d00304a407080c04600e100c11140d0689000540100703003081d034031903000004241a03042d404035059440741c900350b54510100000f155610925030290302c0d000d060003481c5a22600d02184907002c654400d040a441c0c11100c3d800060528a007181d01d0400340c4c004000703006032890280041018103500d4100304482e014a15001d030107119005000070b02030301001011031004e41c061b00035500ca0b1001c004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 47079950 1250 47078700 47078719
    0x20607030f021b160f03020a0e0c0f0a02070303080c03040b0a051302030f031306050f04300506040b0c0f070204020c0a0209040c0806240409020f0301060e010f05030a021302030403030b 81
    0x2220f2a90314400b41031040c04182e500c2c1c00105443c5211210001140d4005101ca8441c0d401d00074100100c180290200b40209400c02490114000000243c11b9200194002d00211481d504020706883d40c001c00020f0103042c10010400002c08000c02550030800c2c1c2c0b103000602c0d0380c0c0c01c0007841664608450280d0b1522601d05042c241920010080107540074610a007079400365205415101402004c4100d041c1105c00e00c8240020941d01540b8000c00707520b81e06503c4041c0030000c1d440c2198040020a46254001748200028407100d02c80700c94100c4440380c6042c3c40e1051540c5180c0071802401130080c030464000440401403102003046109441d001048400181083e00d4290035008042c410301500b8001c3c007001408030050b00300d4240c8205180040707200700c29420800c0000030203c43c0703c22030b4002e0301140c0c14080d944092043c2406820040d14100d415414003c0d0446002100c0d440644030f82e000d0840b00c401030701c41c0d1202c3c02d10401028809030312a101c501d42a4060302c50b80b070401c0c0d00580d521 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 47081200 1250 47079950 47079997
    0x60221010911160b0a0b061c0e0609070b0304110406080303040510090b2d070e0a0503030906040501180b03070507060c020105071407030c060e030703110c01020607030f02 75
    0x120105412691041d904014600c1c03519542c2c0494000c00310703c0d403015401c000e85840403410280320341d03a00001c003c000180e00c0901100090700342e04038141c6c020ba0900c550300c0e000c9003401d151182e2201c60101c0801482c0301e180a00645e5540d900c0ca001d80d203841080440803c040103d070311003004c0d0b4001c2c0180144641030300c1d0a011a07032900304450950b120710645038200c565000354400c1000c5207400c07102c0d0a60303a0390745030000e00f040d14078580701007124048200c2120a8a030040ba9660180442d5500c1108444c0a0420040c05050b2070300802d119410801404000340d444a003168121002820301802c91200820840211205c0390b00c070341541540001041101030b03000c80103103203141c400c0c0401c00040784009012804c03514100e03021400314610b282d400807e8120070f4003403c1a03070701c41c2c90b082c140401c0c56a07448041c1d03046150300d50f040354130200d140030805420540d101745a000a90042c0703900d07030801000070351366103028000e20b05240e81c48600c0030080c031240d011208240b0030814100300d02c40c201e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 47082450 1250 47081200 47081257
    0xa050c0304140a120c03020609030a06050709090b060316030c050d09050604120503100509090a020a171c02030d1505040515090109060602030f0307020708070e010602061e130602 78
    0xc02e4001c42c0b05604885001c0392040010404481a41d000700c0c0040b9040d06550a2000c01e901000d041941481810003160000b0700c90b014042c417940e66030740c2d001406480c10074072406840b02c1d081468486d40d0240200464092204003180014800749808165088405000e40d8603214000b450010a818070203541d007442400100c0c14001c91283c00e03940c146c4603c0341400c441501064801c512070f40100b8038104068a04003a01c20742140c440020358800c50541c1e400580402980e90140e03505441944c455003480c4c100340705050750001c80c0032201c49401c1801100a45901ca207848082c929603a038182e4503101a56046458050b010181c002c01490a061501c04c0114001d23182d0184a10031400010400c1d045e01e0140c04203c410a40017582003840c03e40b00980c82c2d0308020260341c211310a041000918400c00c108807001804036031411000381d410030398020b0801e41c005100380d540404030003c1618900024061940c0000700083c0036004240c1c500d0054083e10030001d0790555558500001c01000c903c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 47083700 1250 47082450 47082479
    0x31403010807060909020c19060f020d0f05010806060102060a05071e030b09060102070b0403030309080c07060c0302010f05130f02031501140a090b030613171207020c0a0308040501050a050c0304 85
    0x10181c580c4807503113503501048421b9101e0080302c0301e400d800a50481e0320b0610400c000e46a031502c030351004039001c1201c1c882c0d00c003243c00a4464420064443c80d0319800d20030244116030240c4440d8028000500e010400030355911409004074002c1966034000601c4284181c8174800310100341c0b6000f20003103858800050150510b0010305104855060204003507600006a91003103d08500341142230520f1a10700786c0c018080510103590542d01017242015024060240b00d000c0d1085454079003510f03449060007421a084c03502413041c80c42c501030500c000c032820781150b441e41c03580c01100622481c4440c4046800d103034003460320031095042c01c40007041c0d04280400c6841c0600065440290456484509805480b61415400d405811070004500e50021847c0d1100050b402850203451010042c543c40d4615130090039501d001055103014801c2290781403000030710b501011503d8180c0107080d51560213151007584180d40c10b0141c000b890b09000c601036000c0d15503c0d8540307410340351543d540c0c03000c1106044 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 47084950 1250 47083700 47083709
    0x50f07060204051e0a1502070f0308040e0c0306090a091103010501080601054603080a0513120b160e0904080a03060b0406020303061c050105130203010506100e0d031403010807 77
    0x442040403030384c50754000302064240c554010801d000c014907140c0358584030102104032104501032014040307080743c028040c260045100348502c0da0796600d0410b40308007884021b400805421400c105000c1c4540d00e0804003608040c080e0b5000881803824a4031a481c005c412401a802d5401e100c00001c4070500070650030b04895041c2c5003101925041d030801c0c4c0440d410b0112075940120800c2e4a144040d00b000300d400601413105c051200302540b60f4440030a1a0042450b0200080340000d080001250301a0410700800c0d03c2c0c2440d103c1c81a269803595910743c00240052031080341405016500d0344106030724600c0ca0000741414403182000d0501d56000d90081414201180c145040000c414040000300c904981d00c4c1d901440c15907c0d00810040700f155100ca440c903003150031007000c0700031032000c6c03042ea801092203440118000706a4814142554402420141f160180007070042a03160000d4801e00a00411160309016036141e00e0180e0b06405500680d07100010044000b0644610018401c0e050300d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 47086200 1250 47084950 47084959
    0x9040b04020405071110090302160f06021e0a020405070e060a0801051806210a060e030310060302030705040302060c0a0b010b21010315050406110a1d030109020f10050f0706020405 79
    0x1a900c929090340d090864034010342241d8021841041d0103103c0c0d0b4840080c0314801d00c1a6a2b62160002980b03c00401982008183c400079101c100801e54040040707030304010342c064110104680f4408010b445041051010740501c0d12500040c070343c540300e02d40c0510041d00003480b481d101c01c4089001010841c1c24001c030b0b030069002c1102d5604c0e030b04004000034482c84004018100141c4d5081d0900668242c04041d04924420005440002560383c0507003c1d001b0103000046d03443c0c0c94a6091122610840d5210074280b5104000303012081e0f610104882c00c2d01d0301507400644d640c400d2040d4074603040080d038010740030b20f01c2c06001142c1d400c00140109000c149513802070309202c8002c83c0d149552030080c0f0004103d62100d44400f2000302c800d41082d580940110f1000a40300901020080c01398001000d038400601c07007100000401442441603045904280c0c001c00100d98294040f48414070040e9507e4490380c034040e080701d801441f81080790b00185150395041c0d00d0364113a203840c00c003a400034090144103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 47087450 1250 47086200 47086211
    0xf0e06040504240e03040e19050708010506160b010602030406081005031e010b1002102a05132d090c140903070305061008010c0f02030a03050c040509040b040204 71
    0x5240500901d402640c109204910f150311104040f0200d0b50045403001009480d014468410388052000d0002008089005803880ca098101e0965844c1c14242820140345000c0500c840f80360701260041c151141034a5142e50f4044080d0600f02400b60700400800c4036580c04004038a03941d010018000301ca1158541203510b440d2270500b2550406140907035509944070080c550100d4074005071070780d100c50700c03200009840703048040410319020710102008050391080084c4c0c0014250b5200e00c403400030841440c007008401e85881c1c1002c03885800340002c10000c001c507902007403165844520005140c003460001c0030490b04c4080f00c9489100440000300f03c8040300000940201c14080e01024030140e40d541850030829151048464100c5031015416210301d5901000298040005901514010240c1039407585005000381c00d58000d241007500b004440c51869061503000400d6581208040c10007282564403001c000c691405103038091030b481910101032105102000450a01950099400f13000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 47088700 1250 47087450 47087461
    0x40524030d0f050f04120609020906040c0207030803100e0708011d090a0b0901180b0906090706050a0503190504060b01090807060c1506081204080f06040305040915050a0f0e 76
    0x701c4140200044010502c440a0850b40c944544000e04507801050034503030a160719124050201d15494608403a05c5a031103000000303500c0d010f15500c0c0d00180c1180c1c24070820902c5d00f0001d440d5120b03844002c00e001070100100c0d070081c044030340c15400b80c890803411ba081458290b42c000c10181c001c1c440c0100c0810b001c00d02c3c0302c2180003908102c0c41008500c0007040f0200c041c1d82e400d809504000c0084d0717059503031204140038084a950400c81024015902d10026040940300c0900b1708001408000030f641c4160030801980e50400251404038000b070904a40b65a02c807805416001114006400c0d1140340c001084104000c0303502009500c102031380c400c402c1507203460030703e9a00d480500800021502e04009880042c0303039000c0e140708106010601050041c0d030340c144180303418034014050341c0703002004c0f8042c001641d003080390003461148180101002d09090300c02600500c0b45d40102c1c0c40c0c0ca034469902140e50002c8104250080030054442d920455845401c283c901d80e0718011080c000c807802c804641c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 47089950 1250 47088700 47088703
    0xb0718081b01050912120703090801020412030f020c0411071a0105010e0f010c060510030512030103080f0313050a080c1006030c090203060a030605010f060e040903080a1104030204052403 82
    0x3035410390001070002840084005403042c1c2c1040c2c14555000041e01c0348256500300c10b0261001240114844d540c80326101c0c034000d803070b128503030704845440d0f8070511042140b81c0700062014404c94241c1032080c0e415980c03900c100e0074181403115203900700303007400507a0501e0020500100292030203850b443c030f0004a2118004220b01c02846010700081d080782c003000351860014142059201d05051040d03480354650740780d0040e5001203030524401c040c07490003001030001c20302080c0021340040d411a451581950340342c6130b0070300420f0a544800400030000540e0341d5804600300000301e0b00401216440d0265152040c0c40c0d520a105514007030040c14401c070307003004250140c0010f581d4000714040782b141c100100d21009400081c100c5a100c5000310002000c51000d00c90b04d806400210401d804141c10000041c1110079042c24a44c041c038a0907003c030f40070950080d52070b60030401100010882180c1103142218602a6401c0030f5031045c07a000a0240d0040c00c0c03072030540d24686004040108012000405 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 47091200 1250 47089950 47089963
    0x3010207030206010510030e0708030702030c030307120c06090510090c0807050904120513060203040608010f030308060904081c06050909160603020307020106030804031a0f06031203040f0b071808 86
    0x40c050f07406003005010380e1824440c10280c903101c510300011515200b51040d40f41098607402100d19800019595055090a0100c881075400c141e00440c601080c560340d045007000021000070401040000400c2002080d401c01400607030003000700c0c0ca00c203084a003400000e0020000444071032940c483e00050106000c40c003001204d00061031642c0c00d61b1107031102460045054844010000100b00201c88004620601c101401071a070065407907904124002c0d08400e01a000032141508407101040040d80c001c5000e6486001030360005543d1301c45150801d10344c01041038884150803464400501440c0c43c1d03011900301d0300304a42c000d800341c4031080c03105d031250440c4201025803844060103214682c02600250740010541c0700008072945c0d00e03100c6240a4209401c1220400c103411207001400b880e401c0a15001045c0054000c0300f0308007140000d0342d407106540000803814001c40041c040c40301c400030715101c55400c20710014851810401c01422084074891602203100f035048082440d4000103940c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 47092450 1250 47091200 47091203
    0x30f051506090402071b08070f091b0e0109080105010902070c14090c0703020a0512070605061009050d06020d050f010608010e0c03061e0301092103020c0a1106070602040803030a0b03010207 83
    0x119240c026940b0901002e980407103401da4101001004600010480450a4005021010150003542d0a1188420140c0e00907405024410b040c0314030b80008240c40200c4e4a000c11403414440f1000e103101c1d0068031a04450760141c4115441d05000041c411041d4000345400ba1084401c820303080c0d01c0308e100c10f407002400d42c1c00701e800400e510000741c50b00803440e00411300c0d0350081c012075800d05c81c9543c0d060310300085041c40f62081140840d4140422032540905500301d80202d411205801d4000f400a0a800240c0b03d01441506405400010302001d58100c0d040c400c5141c501340803900c1c00311049903036501c0c288504000504410000143d800c10842520b0081d9002c0d107800d460b6465500030000040b0341d21018203511500655081059907013403003401d180034403d40024181038500c103201d403400340031880c046007898010421035844d044c1c085100c001c5141c1c00045090700c9070324000031410500859038014502880001c0100d0360b0b000001c00f131403042140c0c80052011a03110000d150907401407800 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 47093700 1250 47092450 47092459
    0x31614040b18041103070e0406140612121b03040f080c01020316080a030204150e0102010507110a1502130306090506060a0b03041205160b0f010801050906010909020a15030f0515 78
    0x814001013070a076140c1c480c140000d040341c0b40309072141c150102011054900f2640d465848415024001e2010031450f1700100445d60b00d42c01280c180c802c40d854806042407010904c00010340042000c500c1480259143c40103001c80303840340e8542c4500d2150454500584000d80324981ca0901250710000c200e411094048032403880942d51680c5006080c0c01240d0504217042d02400f000c90b84c100840c480100c4c0303031440d540d08482404a4000a400c45001910203030821406280300001c0c0c0700006440c0416079448222a40241206544d040c002c0c0600020380f0020096001d00200340002034101841d0390b80980c05848a681b94941007181e4610984601c214901e410300025000ca102c1450824041845007411072030b00c80c141d442031a02400916045030141c030f0303101c103004040320b40150540c00350400e84020043e50900840181d540c0f00c0504c1007400540c1c490900b0011501c85400c0c0400400202408566080940b4409009041030a00721540039280074001015002e032440d041144010140 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 47094950 1250 47093700 47093749
    0xd0e0303060a030f030e04050708040c0f06021905070b0a0908060c210604090204020c03070b1b1e04090f05070e0a0303050301180209062107090806060d02031614040b 73
    0x50700c80945400b003d4080c1c0031b1080441d0312003503545403801124459240c0d940d801c0c3d460300d0685081c070b41c1150141c106503840381000b58240000c50300007030b0784010b4441590804c11400d0fa540307401032500c6400c1d04035011250303000c40c4035070b900c40d0810500000d0310503500a44000b640c40c016100b403540510305401d001198201003881c9070700d0660b41c04581003032015001150086154020401b40d9018181a02d2103600000c1d1140521050348021500a0104030164084c04031446030407455000e060559034140d084054000110240101110001c0c00402c0c020f200354804820280c004240480d15100816014a040c2180c0e20b020300c0620b0a07242d15480e0103045074200030b4520000c0c4140016900040e5080200b801d6030f5071000301425052954454031b00c01003410700d1090041000251510040c81040a4188940d880c0411410b50111050304d60170207150543c0002071070202c1d1a940450840b40c5107a004c6011021003004400c51107003507a040c842116102d043c0000e0000440340592180103d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 47096200 1250 47094950 47094953
    0x1080d020a0807050c030105010305030d11070809042a03050a050105010e22090807050102180a121e020d0c050910030309090c0302070b0c1c0204121209080a03050d0e0303060a03 78
    0x201402800d800303130049840070103020300440e007150000e81050355554001700d020354040b8a10f000341030320302c916181031a040205550b030b1403045024122060b4403c5458400e00381c1000340080c40b0082030740c100d112141030300708048400f070010036081d1440790290342020000305841d401860907045414010b000d03900d042645401c0b030b259503507010040a0b0415299500100030a06107000b8184090182000503903400e40740705010110303034030300b4410740c015900c42c04200042a86070b40c070307040f007650402c07246d1800303600b42c000d004802c58811a0003540420880e00210a00142d07e001e00290755090310080c4082c2c0342c409101540c010284001000600c4480b01801180d1264010034002c3d0b10504001d4140009683e8182c10140d0032118030440c02c0c00481c48003243d090020030410900c522020440c5080e040c002800410001000e000d007006c0c82528103000414441c8440300d0060840302c050703501901040c17030000d00d680d2150038103d02e01801c00f503880c1010703800401240c3c024800240405c1200f03103513 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 47097450 1250 47096200 47096213
    0x30303040b0603210414010207051e0301020f1801020f03090d0f0c030501060b0d060603091a04170a050c240628060305011712040501051606060305010507020601080d020a 75
    0x20012901400341521000d000350a9030b1404000d81080340c1210340711750400d80c3c0300000a01d5407490705d0441d88031401c100101d0311a03078900c02d00180240b0306120485542e07000f00340a403050120444440000080c442c000300c0b01c0d03c1808980c40d80990a0fa5089500c080c88140d40f4095896216400f0728560308000c00502d0350710540300c107148511029080c16541c0e8485a0854a9680c8900701e0745070000b805106082080c4216406802c0c2400c040009409580b21447c003081d00040c4031085031210001708080c0900340004e000c5001c2407a00742992a04a0b0034003d0180d004421448140e20442d440306500c1e12204601184014020000c2c04042e0b40309010000c1c044201441c82454400e085c00510030f446682444001429454a0218880d490074034a010f03d600c5001700b0070140e4004804420030001d55008407400c81c0c4003440c1c03071511481e0154040c0512100380c48000c06461410b0000001c202c41900810320448040d02940e415aaa411103161034003206450130700103070004180480090750 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 47098700 1250 47097450 47097473
    0x6030b060f0a031218060f020303010b0a030f0c0504050406140303092106040c0e06010507120305061336050d030908070b071110020c0304030224030406050f01060c0203030304 77
    0x203008040010700b981d80d4803130341e4101c090f40b400400041c24425070510306582c1c01c0c141000030192860030031806000d05400030340368081070180146d1180005403e4603041d200e82c0000019a046090411412100540280c00ca1340b01c1d1007524080d81c10124006058213030010b0100070110701802961600004100708108004c8803502c51071001010b050399541d00b0410400980b113503200c0c80c050030049042905842030310700b00900c07030747c100001084444000340c288035038103e900c017190802140315100c40d0002181e40d803034490054481454030000b4428001c1c0f55804198601800c02da07100f030104410500b0300c14900707001000d41154403030038141c600d2600c00e0340101405030048540c2400c001d62540c4000403e5016140e41d400507007000305580c4c840c1400e020aa1404407881c0003185410302c2d0840081d2240140e10010b40300c0e4000320500703081040100003003061b000c0c94000301562454940380160042005484036040083d0302c60010490601810062207807640080c011802d5940d90b6030784c03111107103 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 47099950 1250 47098700 47098729
    0x6010906140603090316060212010902030403050a03091103010f021803010b010c111302160203010e07060207050112090b070c030f0903020a05091017030c1501150f1806050d0f06030b06 81
    0x300402034840740c42086c2c8250749a0741d01c80d8402607560f4103407040d11400c003201a00a01000b41c03041092000003134200b000c94410603a9801c001ca0035030750905000a02d1703016500650303015424610892600d4140b6802043c0501e0186003015000c0006001c0c94201ca140045c858081a14045500041039280c9a0600000d000400085680300307109030880a90700701c100b004d500c81c0843d2881c172003107280a02421600d070035038200030b144962415200039070300d1015200d03241c180120b24100644100154101c4e07460113801c4514010300b42041e42e40103048480580040c0c0014031080c00320008540f040700000211307500180400159418481000803050014011809290600000140e83c1000105c03042c1c2c1555000d0141d52195040241c0034207214044400ea61030b03186a000600c002448400d00c51a01c407561702d401070141c81c050806544da100080c0009c0000121600c00040c1c280d4000001d1856401c20703407091240303d002c0d441d8041030703845600006240148000c009101ca003407000b413445504 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 47101200 1250 47099950 47099953
    0x503070b100b0a0807120b0306010902070201030b09070f0207090608070b0c030c160504060509040b0c090315131a09071a0d0906050906011517060103090b180601090614060309 77
    0x1c1d03580d020852440d601980c400b101080b03002040245090304442081d03840b100e030660a02002e03541500298031038105011314524241c2c045407000c25644641d1000b842035001800419050800c11005080c4e001e07441040b00041c49085804074039031609008010442c1d03540002428064100b0705080083c0d0004051003485100070301c1440c1782c0c40810000b00280740f495403200300c1e41074284014401030701c2154101c2ca00841580f0b00340000190100c440581c040c181c45021034841001c0000242484842000d983d041701d14507052082411251500012017441054280c0c291080868215103042e41282c01d0300b0140c0021004024011901120000b03550160303240600c0c00f801a6410022104069415103545a4480403c84008800c100603400b4140d0721040301c214080c0201c0c02080e142581c0b0442164540c4c160100e030725640650020180745505c04d050f240c10b0f250902d040302140c994a800b0520a1045c14000107403503849100f92030581d11190b10f800040d03c0c040050007142e1f4001390405404d0b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 47102450 1250 47101200 47101231
    0x13051504050d031214090607020304031703070311040602011413030815120f03070501061202090c0d1506020c0103060e01080309062a100506010e0105071211030a0c030315030503070b 80
    0x50090384039640030b10b0124203420f943e904100c070344649081d000070004401c9d0b5101700070920208807004081400840d06c0117441b076490f607c8520407405002d046241407180345002c24041841d0f80c043d00112801a18142500302950710480401840c80e011140603000c24618030100d244203201c1328520325000c3e400383c02d00b021a50724101d054503014440040035665080400c80340c040207004e0044400614a2840c00700034400c151300014100400980207003041c010014034107070600380300c0d08200b82d4640b00004c02c4142d59552034001e500c3c0d00c103c1c801240081c0c134200000c140b11034500c5c040c505842206000b14100b50101c41408495800620801c2c0c580055811342c1d1a4040845404501081030002a0038240043c00030002a02c4c07001c0c02c02d9050040410760702e10315907801820348500e66004000103a0b460940d12003918201c8030888610880e000002d09000c11540010351014154841d83d010001c5036640c0e001840c80d008607000090407a0010403100000c64000069640c0112042840700c1340d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 47103700 1250 47102450 47102477
    0x17010b0c0a0507060e031204030b181903050406030b0405010602030d1109030105091e0106050d02040908090a030c0807060905030303070509030f10061805071e02030906070813051504050d03 83
    0x2d001c0303c1da849030000072160342c4c04103180d0505201501d04101080b40090415042d641c82403070f01d407001001a422960052001010000c1c10008580201c0e018034a803030018605040c0182558441e020b000302090a1160303488444c10705d441380c0d604030744042e4013841c1011140e103592001b40a800c1d40311400640c050042c910f00fa5002c0c0304250181d101100101081020701c0ca10090105c42d0007115a4a6450082c0800c0117440b45032480140d07a0f4101c0d070000b44030b112031901d804140603801c850340d048007500c2c1000c010170000400c443d0581c2c20803400c480c0b1701941c440c2c04a4003a402400340c503400d07030418008140024003800290070449801000e440c0a803041b40d1541d13103030401000f240b0305005d44982c0200301151403406401c03251031108405011a2401c1c4001a001c00c0c8030b20000e00c4c03541c4080840d900001c2c030a00c00c2d911440320080455944540c94101010660045403204841c95540d030740003e0305250032050385404500c071900f0181824030340f80c1044140c1d00c40402c19410301c9000c03084440c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 47104950 1250 47103700 47103703
    0x904060b0f030a0507180e040213020c0106030303060f031e0602040b070f02010807030e0604030c080f04031b06050703080c03090102070206030c030a0c0e03150604060f030f0b0717010b0c0a05 84
    0x4440703609800050b1a0328041942c0410b4030000b405a00c240141281091801e028014402c0c00380e03000080c07410b00e00c0e2241e1001c00c081064400d00300e0a124400703d18080007050641082d0200c9020b95800c1c007006031185c043e0401c0102d40c2c40300801800200d103803602280e80c4203103004085402180c00500b8669542c00d103040552121714125800f6140304201d00c21583c11000c017503001170032460200071000d0f0200c51595580700160000d010320480c98440420064840110351101002d042e42503191aa01e01c0d1601600351000b14014200755001c0010880318840c5040d2201141c05540708035068940e02d503404910380c4083c1980541c2d540804c00c040244c3c0303d0000440c0a403072400c09082d0b5a00d80308030050110340c00c0d081c02c4c01c2040050400c1081c5590300290380150980000e081c0003a5880f0100010020011503015590001c080c1000005100c410000740007000d0250030f20703160940d00c00a048406001c0c000e141c00e890154000103001c0e102d60030000d4002c60780c2e0181100c0140c040c50f212039 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 47106200 1250 47104950 47104957
    0x60a0302090f0f1005130513060e03130e060306010626040f02040b01020c1e01110609031c0209031c020312010305030309010f0e030d0b060d090b180c01020c060904060b 74
    0x8441d2800b1020511103803444200030242d0120301c01c040c1240007810b0030006001074140030510103025880e030001c29110744c08020649501c0f030b07014104000401224210a80701e0304904032000c0301307100146001902150402019201d0b40006019260b03503800d0980030348034070f00b2206068a1520320910320030084505880c03000d00035405140c070b85580b5400c0340f04110544206448441c115000383c0815141612081d00f50310f008038042a006010540c4600100c0f0104210080c1e04d546114000500c00720380400300050814455255102c2c03482c00036210300105038454030081d036416621600400c2030011068288004000381d80c41a02c0c40d01c2c52604003100e6000c1c0a800c1503450340c10000c00d00c1103421007446602501c40390b0640500000001c000311503181c0c0650f03102500840e4603591202e40c6580c0e40e4040b14481c03048068200000109420520b17201103084480d10300c2100342c4901040f41c0c2c140092540743c000c20580c000d004000b020010b000740c940003030680300c2c1c00a8580304003007900203514024 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 47107450 1250 47106200 47106211
    0x170309031806070c03140c031b0108010e0f0601080a060b07051b0a0b0304020405060a030b0a05060306060f100e040204090903020102030402090106030603050706050a02100c020c030c0907020d0305060a030209 91
    0x1035480d800c06040721420a5070000c00d07940304510820240c00010740026110003100d03085810941600e418035206401e01d10f856210a525000d0400b00c2400112110880c545207602a40c0e00c0440c0da8030b8070021f501d02542070301c00d424000c09040029103658811030140c3d40c400b54000c0c01142c1c581c0c2e548040c101a4011040841d0b2030380004552005400c90541144038811044503000484c1c1d03d08250005507100141001e8016502d8070002882c0c0e898010550b4000c69120326a100c8501d800c5103800300914044da140c501c40d00500b4045000340c81c040e41054070411000302641040708a05401703881c240d00d009405600640c0a000c0050361071018450148280e00039000580d892402d0310400c030f0b5000c030503007040c0185440c004050010420004401b41501c100d424600c0c0d071503412060903490500100c0a25080301d04101c048050141d0101311050090016012a201915007408000b0011030441c1c10704010780c000e0180743c1c18070340320760170a641040d009422203d100d41c603900440c00c905030441d103 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 47108700 1250 47107450 47107453
    0x30405041103071403130201052206090305060603120a030b0d0b0a090c1a0f070c03020405010b0702040509010b060d0b1206010305010c0908030a0504030b0c0909040b071205060a0b0304170309 84
    0x8114a0f55080701310f0b5241503082680070780c55403a002d028076a00c10401d541c040d0400c01c010400460681d000252400c4100136061440301c034583d6914002c08031109800100c07000d001385004034030703182400104503480a514040e00e50800200c0a0300724020000d5050700d5920400b21152440883c1951074100d0051140106c08100c0d1440e601f00512030040300d5000303500d010180081418a54002e0042d1182c520361600034644d9081a41400040d000c0c894001a52042c0f41c03000000d80041c1c11402840328620030344050000b5914200b1203404c85414003e0305420090400502c034148499902140c00b440d8018000383d40d002d07043d4845440e0001c01d800c11515a0342d0ba05aa0403640d41182400d0020511003005500c0c00310000c200400701e0180d480001e2035800b031400800c0b40c50080c882940c422078005080b451080c03400e410308940c0110103031110004114108195540060b082c0180f5106560141030150f034146003005445070341c0c2c40144140da088910f480c440c0034400c07524004500480c86d200 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 47109950 1250 47108700 47108707
    0x60e010c09050906030c010809030d05070903061a0d080913150801050c03100311040f140402090c04050a030f06020906040806100f0e0f070302040b0a0503041109010605030c0a020304050411 83
    0x2034001d4541002500101d03c00d4501900704101680d00040c04000c4034020f1a01460383d89503050201d2070f6010361341272402a5030030282040419988a0600e10460b030244c0d6052110004949924900081d00c1582c40d800140c1c50a0580204070314100078940c0c514043c03e913541303408040d0006412265110b0700c0c01100322000c0c0041290344d000b40150b03038021510f00c14039440c41c100030000d030301c1d6200548002041c1e0010041101c0d0b2aa0707503580b0084503066000020701032110744d00350482c0f4494044600f28443c044100108090110070426101941c1002c0c1150084a040d5140c3c071012484002c8102e5219408014120107515010090402000c08c14010030140c00e2a03000c80e40c1c0901a900f250600605210003084856480f00140390041c04101c2444c6580d1551142203010b40320341e4000003580c901c00254200d000785e02400462041c2c2c024800403440b400701c1c800708200c841d028030030380000490031700c04200d0411101000b84412220b40c01142d00d084d0703594000c502913961072050a0400240031 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 47111200 1250 47109950 47109971
    0x7030309140a03080619081e01110705010207031404080a020103022a030a0206090606091f051504050102010506060c03190e090a020c1e0d05090a03060203090705031e0604140109060e01 81
    0x5a541b400c1c10b2030340b400c00100c17400c219500b41d84840091481001080762032a11005580c01c0d4029890348201e289071036540d07129400d220b4040d5129840450010754056425095441550181c0e4243e270a0380025290503103c5030011006901f000c2001d5003901c0101c40784501c1602c48510310000b01e40401d01a6464a0359480080d09084000304911000d40144c03007000841c0da507550955074410302600f1002c081921101f42200d0f103035466085190000064a1140e50484000e1301400032140d003640280035a40d594002d020403801f1355a04c5d292540c2c0240f00d4101d9240b0060141c0d100d40015240c07030030324442c043c0b00150401205031111040030b6400110101c1c80701d024404480684c80d8484202d0070101c5c0480183e42d25101260700300100180841d5510310742c3d58500b480001941c21500940d100d040602c0910744991440c17080b02c1c800c0c0b044910b4070400b0f000b0183e19800e0040090013034101540e40e925564201540214070500555840d0480702c0099201d00c11510181e02100000030f190440 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 47112450 1250 47111200 47111209
    0xa0207030b0a02070201120c0e0409080306100e030a11060c01150f0603020c0706030c17150a0503150a02030a0e0d030b09010b0f0403110307240f08070507030309140a030806 76
    0x40d21882d0100e004002e880c016076007020f4204109100e2000025203111144001c4540e840040034072548282088640d03818480010301860094500310707411000005400b5043d00e43c00515680e0700e40507000b22521001188003103d070258030400c0a40301518007103108a40c9030844448100700991555005000d1101c22410f901400190410f41011880c140000032070381c1e40d404440c41104105611051284986841100c0500c21710301c1d4140000c0d05800d2601a021685449080e40e600598403d00c5c0014a031400040e01e4235504013010280d0229260083c5000213540000c0c242d082c100d0b00e8002801c00b4501c00c01c045040081c0da80d40020b8003040000411140b41010703070040c840729805001e5910048003510403101140d40c42403440c0301c07801030b0001103820406c20754841205405611111441c04520842451401c0450396078400c1d1810b082c5403d90b034146091b04d8100000390144640380009002c1d80c042e18602c1d0050700f69640c5018404625854070000260441c0018044024004079040 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 47113700 1250 47112450 47112473
    0x5010219050405010c020415120803090c090f011205160b0d05060a05030712020d02030a0c09150e0423060a09020301060e0702060f1b030c07140705030c1201060b0a020703 75
    0x140e454000d1400380b9060009000a5200102034880c036a10308840f000f04e0100300880b0003c101e6403851f107541103031030f060100c12034000f1500802e06000d04400b90100780b07850400310744107030440c0380c402c595a4200a0000200c0340703947c02c215124072031604c10300700c0716041005c1c1c00000d250790002159104051140082590000b6000c0d83c081c00308007801340219500171401030300342e43c000d40003200c002d1841d00000310070490000300030b5094020074241b8010320541001003030907034480c030b0000d01c104107500c070307461068807000d108081021608801260003d0900000620340300520781650000c943c0710300e881414688150b4001e0201c4e6540d01c141007c500302805030900418084241036020315003050080d4a44070020501070341d01244400003036404036800c0100108445903250583c9a00d0091072004140e802803500355500ca0000c8110b5207030140004d41941078a2002c0c02900a0300460814040a028590416942c075500e403000415611540d85c080c00710300c14035500424007986181801000c44c075 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 47114950 1250 47113700 47113747
    0xf03030f16020616120605040c0801080d090302100305070e04050a0e0d02030c07050f0d050304080312060402030412030e03041e03020108091513030e041d0c010512060607020a03020904050102 84
    0x1000300042000342c005220713940d540c03501d007424102a15030189104030700804164111545c0300f0301e03025030190319692201149041e207107850110f80b0050b04980050300d264401c0c3c80000e5004103050704412401e0703c05d8200c65005a80ca041a180342d0441c800003c06551049a072000344940c3c41c0c0e0703002e89948082101048544140c0051450050784d0389803e030325400740e8084c040c000d12040140080e03e80300e95010313180483c0c0001c02c2e00c2d00c076038440380b141d40c882c0d0140441304d44003401c80002c60344a1500d8404ca81c0900c0e0300c01c0980c40380491505c4140c0c00740c8100c00081500740014080080d121241da00c81c0350182c100080900c3c41903083d4800940003000242c500325450740082c500004032440403410710342000b07c2c1504014804298502102d080742841340300ca070442d0429000043c44841050b85010107840ca00584012506080044905001c2d90401940103a28480810040e0409070010034505001400c18003040d41c490300418002002078504031407a070b40c0020042645142155258446e5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 47116200 1250 47114950 47114953
    0x405041b0912050705100203071a010806100506270301140f07050403021509041b03020c10110a0e03010b0603090a03080604050f0403030c02010e070815010902030f0f090f03030f1602 80
    0x100065150560b13500e905004060146a0b800244050035000f002a41c08079a400403d0072090b0000d00240310241c4401c1c415554548a10004115020000381000d020f803003010307104a017056a20416128101c10401c04916401d0404103800c0c005e840a004890301c4801c0d4074198481d50070701c03100705511450024051003c1110030f00050005030340c0c4113260000e88268000c580c5d102c1c13880354002001480d909600c1c3c1200000d80c040c80c562982c154016005068a00050b50300c003001620071302c42500c006511994410608104043c0424000c0407120b201000c09000016001a001c000c6846e551042c0c80345c4516900c505101401c050348807817060b5004100b901c09020a050202400041000142c0700400b41a191012040c55074800d60200984115050454600c2e50f0b90740308050300c8404001d11483c00210280020070f41c0c080b54000c80b80a486100101c40c4903550f0b03d42800d00f6414054000300d6240240720365104001c404201440c062030750f0030f0041449080003603a00111018421450055 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 47117450 1250 47116200 47116229
    0xa0203060f060c12130501110114010b0c030c030f2502030c01030e0102130e0a110c100b0102030403060203010f0f120b0c0c15010305060708010e04260405041b09 71
    0x858031028001c0d040280c003600c2d03281c0c60b80c004660050800014075908050b04101140798071019008030b405100301d0300d01382c070b8028402c680c1c040401c3c00d0b5032403240034464030641c2400400c02983c04000034000c001c01c40d803c1d00d05000c207a040031400e50f4020b41c024034842c134020880303201401c40d200c0340c4802e61082e006001d41030b070b03a40c2d03011030f8503005640500c505040c0da8103240400000b00390101c680c1508508415201c3c1d548070040500d240c501540c49145807460300c1000c440360340000080321240e01c5090000c1411060b03100d0090090013482c07209038110301007800000300181d000d002542c081c156589020000504041c941c8019900f10b9001d202e02c050002c10030004246200b54003900400c100310055601c2d840324601511340001c9400e03800400ea07000700000f040c801c011460500440081e03590703140e01e076603980c1d6022840405560140c074910070b00c980b01510109040c510a110511b4021150525a403071000408481d101a61141c50340740d804c40070310815034482e240001420840b507040c0c80 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 47118700 1250 47117450 47117461
    0x6090a201f030c170a1a061207030b01051e0304031e11010b0409030e01030e011509290102070b03150a03080a080c040605041a0c031308070e0c0f1b010c030b01080a0203 74
    0x1400b94001d041c50034925901d85403601c06101b603003c00e0010510103000c041d9202c9101940c962444c0c0e0898010001900c0c01c4800c0c0407542c071480484a250b001020400b14400d030540c44248503610142013182800705c0205480d154000031120320442101540b01c100c1150300000209080d02c000c644103502c81c61808000100203904230301050341505e8203180008a40400e907000320b0041940017040c3c000c95143d5680082d800c0c3c5140c2000d103100708a04d5000030984c400045400546900520190240e00040740506c4600d01800185500c40c003061001a508000680890460704603500300796000f00313000480300b092a40001d01c05400040c44401c0c6840c0c185403200c000c003640075030700520089111050312981c02c140c050046d00c0115010405030b0395a2100241b06041140d01d520866215000c0c0a40c0002c81260410340c035407003000030607161480c1812240d1540388661025426490344031031350b11400031111091003804c0292486840000c0c2c40c440810000d011450300820118010b40100f04114 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 47119950 1250 47118700 47118737
    0x10e1908330112060603060f0f14010b0405090c04050406140102060f16050904060801020f041503050606030a0c0c1703100b03040221070b12010f05010206090a201f030c 74
    0x28111142024105518509131030a00b010780300ea50320140480341040ca4051690b086036001d09050780c00e60300204102c607201d20301001c10f080c2c00d02c500340c00404280420050f44c18220406940302d4292041c00340341548400002e422119513801a15111103542003004d2196010000540c10030481b80e0f460000307103041c0404200501038001c110081000110302c4203582d80b40c43c4c01c004090003a02d4025903d9114218804005800c02e01c10030410f0602d0b40f0140010600030701c54140207140150842d0301c0c50b0b83d030782c000d080a01580c0c0700400c200000401c800c00441c124801005212185a4150760340e0308081c3d1030b070303c0d40550790340029039440c1080052100503a9800c441110740d540c461841d4107040013000f103181c140506a88810a80c40f000a901407060803540003250580f0059034901e85003e440300c00483c2c3d280c0d0129804800e96010603601004102908200403141c2c040d03481d0000d0079113801c000705006030b403514540311880c41d81d00300030900550940128100f9440c6898a520418228813a06 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 47121200 1250 47119950 47120053
    0x201140426010551040b0109120b04020604050d060c020606030d080a05100e0106030608070e0c18030f0a05030405040c08040305180f060a02030915040f05010e1908 72
    0x3501c04c82404c420704840c0501840d44840c43c0da0003290f20004904000071180784103041d00342e1291246150410145031903005058007800d0b00d0103c3c1c011b610041071380e6107140752514042c0050f40e02c480280000202c0b545c07501e66250000d07200704004102c4884074a0041d09d0140c029251510075084a2402c00b00305602075100b139442680340c00c011481f9240c200d03c0551001c2c0c030750040c414084c03c440001c1009a010340004044540501c00c80d40c5083d03a5110030f8408140584200c10440c50400c0404c0c140f803c243d01c07454007080c2c01000c0e24103515140e03800e80e01d051110700c1c044035903810114003000640780c05e02c109640503205003840c2d04149000c0c0d40041c0688501c1310000d005100d02d102d2801942c5624852a01300000600240c2c5d0392742003031001958a40010700350034844c0b082c1c0b01c41200c04410000036030341100c1c11006452160350074a030040d80e403801c40c03000035500503425184007000e600381135200e07600800c000f501a00142089100b00200100030000107032140d03801c1c09a980000c0c40400d0031 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 47122306 1106 47121200 47121241
    0x11070506010e071202130b040909050105090606030a0206030a0908030703050f07020703080a0e010e0a030609020a1401090e090f010507030203060f1c03050702011404260105 76
    0x100c403003a482166030100081c103801303160788041440e4010b0030102c0340d00703e40082c4c8162181480311043e04a50300143e070160310341480e4030901500303104941d00200c10300e0150801f481d141d00401c1d030341d0600d03400003401210f00000080d032a20300b640c0401449540030403c16541d0403c0b03407009000d0041035548030700552100d40814608c0d0300014a25088942c00b111050a0600350030055841d44040b540c010f051250b0003000341c116a1f41c03810301c0009903100e2100050710300032a00600154285681008441107044100d00d00710b6078021541d10116480040c5074501c50f59034002c11410f10380600034480701d40d8201810b000440c0e40540103544522415a010214112204200b0490100308240c200a0403100140100400c0c801d400404c401030040c10441c0e801568031103901c41c258000c0e40b0569100f02c40c0304210340902d0329140038008044584009001ea4206079151801610300804e0 = true := by decide +kernel

theorem cover : BRFrame.Cov 46942450 47122306 := by
  have h0 := BRFrame.cov_init 46942450
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46942450 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 46942450 ≤ n) (h2 : n < 47122306) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
