-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0449
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:52:16.610809+00:00
-- url     : https://prove2.me/submissions/07e7999a-089e-410a-aa5f-1288915dce84

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 80575541 ≤ n < 80755397 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 80576791 1250 80575541 80575549
    0x3150307051804171b01050603060603030f04030602090604050312030402040f0501031e06020c010603050109210206130501090f05031c02040b0409050415060303050a02160b0304080702030a1709 85
    0x340080105076401144520401c904070b40700880104007800c0c9010640303503c000700c2c400f44d04880080030480344685201c070020136200d001c0c0c0b905a40ba14840e2040101040d41441c01108482081e0340709030b812441d05296a075283c000e500004901544424103100001d0705440500c07210b8001022441e0312645da180502c100700c200d5400c4203c1c0b6031028030703010060000401958500c1903030303581e8400500d00740265140000292040280c07200319035007008400810000150444413200748074400a80c510070a031003c5051a91a038840000181c1c44240802d540e2a080340c0389412403030281c0c0001c43d88003000e07190700d04007503a4502d045845500c00115049807961002061450780d5040300e0a40c949031030000300d80c1c8607000714084c00c8450f596440c0424108100a025043d005284007814461103070b5a04000c2e03c00d4028020450140c0a0742c2032a480d08804070000c9010380303a10004090468642d07482ea400907400059080b0380500c0b030180e20202180d034901e80e0054a25001e4900c6a903004484140 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 80578041 1250 80576791 80576803
    0x702060907140117040c051504180b030c10090803070b01081b1509040906051005100503100308070204090611041502030405030a020d0c0e070e0f0108060d0803070203040803031503 79
    0x1582c451020a00c4400c00360f0f4040c0c03202c40c80703060f0001400c03002d49550a007a20003035410341c040d50f4418805482441c82030001c4025104891019404000381401d5042c5801541c109103000c40e072603001007031212030600e00385146284240383d503c1c02c0401c498803000e0309032842d88507040940e0701968000040200f12000c10845003010110f903000c030307a00c2c1d081d4404908400070b0b16003040410b000100b160300b915140d035030101005980041d400d02c140d0420810b0518904c00c40d004960040f4030b040c101c600ca550240e4100c0c0d00501c1003d008440d91340c69070311241c44030f800c03040080b40c2c0180c51307221a00200320b00c0c0c0680109502c0a4101d00e41d21403501403540207542c941410704003950810704c010815941d020403040403054041e640c3c0c00c805540c2c2e1070308440c903a80310340144280b04040d0080c40782059100e40080707440242540c805003402052001514030810864546501c080420344000019800d10040c54126030b482c01201c0c20103443d44500e900715003040310301844a800700c03007003452035140803c41 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 80579291 1250 80578041 80578049
    0x20403120f0c0b070e0a0906030b0c030f010e06040b100306151115060303040b040915091814030c0708100c03020a0c0809010e090a0f150501020c0906180702060907 72
    0x2909040310070110142110103240c0000d00707088058400100f01500038032521040c00c1004044904903520f90300c00c1c40041416001c10756101140c02c0000c2d8411040c42c0c01c0301d010b2104d05c0310122150386881044101048000c01c0b40303410546a5038615810b0301c600d64800f81803030803a107000c501e80d0f050113040040d80302d900c105c40c810081048484c00c426140800c25006c00080900600b80940d00d21000c00d107507104a50000c403620900080029202041c0d5102d20030518054044640705070b0390b090400141e50400c2030010030742405852800c001400b040004101c2d00302c00e000d8900b00030020041a04145055000b141140c000d1824000300b05203070300c40c008160380030f07060850a096603d20300802c2000104002000c0b6030000a111100f070b13000d500b800d440010020400141480c01c04080c2c07014069048030b00034541d0074005200003e240c0d002d806410b6400680c01892590030000401c0714550014000980000d0a41d40c0035105145502c0c8032407041c0d10303e030003c083e9070410818040c49d05c991580 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 80580541 1250 80579291 80579297
    0x30412020d1b02040b120618060901020901170402120319030e033907060f0e01020604110d06020f0c1510050109091d061623030f09030c0a030302040312 67
    0xa8081c5480034001d064090190f010f44000950740c00c1780000c1481814050700c0a002407191a0410150540400e1103100c0a488a0291146900c882e00d42600b40e0298800d000d000c2281e0b40004402807035851041a1703c24001000c1811030a8880030048c103540c4048084062000c04150880407260180212030300103100c4001585040020170740322003c1002a0a0701079800260400700c12410a2500b00300720816018040c1c801495039400003800606889081c071010034016008813509600228445100c4d0f508000003c1c914200041000b101c3c0780c0c008030465011b5801d210131112180d2103400f0b08222000c0340d00030000070040b00d50b1119981002411001e8a0840701c80a001c01c4c2d030300500650032605900404034103c08000703d4928003207081c4011010901c43c034010000c001e08860b4038112101c40c1512203042c000c00304015840c2d045400e4500c0f0001920070030101e8424a01429495030003407204041e00c0c2003942c001000c13414014243e00580002e40c011909001744000103804042c0c2e149582 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 80581791 1250 80580541 80580557
    0x60908040927020f0111150402090601030c0207090b040f020418110a0203090402031312020d08071d1203070b040b0402210a0f050c061308010605041514040b06030412020d 75
    0x38500c2140c216031004024051030700303442611545d034082e20410190350620340c141d54030403c041c0c0c60101c0028003103400303070700c20310030349001c40c00b15400f91040403820040c50f80500350417030500e0000c5000e041140481500b0a40d00c0500c0000007401e48060310240c1840081210b10810782d40c101015116601001c181c0900104044014150000122401c1c1c402c181e8002d40c036a03491401c000355800c14000081c1000e8521450f401075558040780303240309808152900c54560300c6000c401c54074400c01402271300c401c00400300e0b603940c3e40c644050480034607880740d02241e1900903259102c00000700240d4003100c1c41d81001c0207000c214548080d10f40c11001050744040013550091440e2070352280c0c00030014091444d0040c10402f800018055841400c401070050342d943c8000b0700600010b4050b40c0b051007181c0d407901c1000f18142c602405080c480291142c03001e12180d007043d4040303c400d000410f80540c0076540d960010f03015182c00d0301851082d8002d802c519280000c124005e810b00440c0b80d0080f00b0080c0740 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 80583041 1250 80581791 80581841
    0x50307050603070c0f020a06030e0d0f020d18150206010602150c07030507020f0603010b070605090d0215071701060f0e03070b18060f0c01022104030203040e070c0609080409 76
    0x10081da0f5101405140005410701242820030b0094400480650040e558020101388035803d41c120321b06808010003212640c0da403440d01201c100c840a4603840040e00031100b0007103614071074074a690f503e0407660480c10b040d43d550500c0ca0303803a62a131311202c00036801c200c00405c0000c1d0180b00ea910010b4604111340e0700307407828050403030251143c041c3c0141800004036020080d5220440c1d5441609400307484c150b600d5840e031005580c180c10101046071620f007002c000800880c80480c9500561046400400008250600f070500c03c001c024050010044076100d1034615a05040c4214001d00e2652120b00c05d54440b440010401007074101c4590185c2e110b0b0303004004d281c8122040b569408140101e40d440c0d22070308030019042d840381a01c12580074101241ca100e0342c11043d4014420f071030045008210045078001c0003156404100d50280c00b50304107110802000f601d44146070b50281036480c104018001c3c2d6642c030741c1224285041034840f108003041c180400ca00c02e10507450b04009801451742c1c020b01c1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 80584291 1250 80583041 80583049
    0x60a05041e03082206050c040906050a0806010b0307020f010c1206060f0c0305090102191b080f03030a020310120f030815360910050708091507050906040b040f05030705 74
    0x6049041c42e614144d0800410700003994141c024142e01610920090801c1d1801c00e100c2d0f0442d0140c1c07030559203407020001e605c1c43c283e4403200072903d03040040d02181c0c1c41c0c1424820300e40c01c0240700034250301030440b468107006020700c1504001d00b01078640311800c0c005200b0090456019800c120103019400d03140039401034011504500b81649441e01d0340d6507003001c1c0300403810241c058610038100300480090004209030b004244048041000b41c500006903602080c0b6a154040e101da58800d8004001140c0041081c2d0000c55209402031351988041d03540341072440c20320500d40010f0341c2c480004c243c10000c141d0f00000003500010040d44640490700c143e400120000e2069658128400c104141a078510240c40c1010a038403011106000030307490500701190312020814032014140b85404001480240605903607402030160000401c40c80403c04c448043c0c0380e41c0a0000e1040c4601440840f035030340d41c0c0d400180060090760546544031464132820b4112801260000d81c800d411100c000c0c0000c2c1c40e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 80585541 1250 80584291 80584307
    0x40f020d0201030e0115051311071b03120807020601050909071211040204030f05070e04150510051009030212030412031416060902010818071412060a05041e03 70
    0x24045411160024061006030001e06400c10300007425400c0c4900e4038000e2540144440403140261005160050103145100c1281c1e001071032001d10400520442d030203c2e08030446000b240203161b03818100300d9207a4807408a40720344412854000343c801070401c0515541070005a004203000e072513104641c14070007030681e11102140100007400c21811611000e2181c01e541e860003040c1c001c0d000b15038403510780c1043d4031a450180c9003500c0901c2080d000180003001e42c41f109100702d030050303030f074800e00c034400e00440001e4040034100c402c80d00807040d00424182d41e500040c1040f006142c4400359464a9071060116031541c80914800c6904240002c1140d0b100142c0e4410500ba418584050f1058181c681c10900c1e002d4003000c007040c92410389500e0100102c5500007101503000340ca0b40d00880e80c802c09220a40d5076413100341c0f092601f1100c020820001320030b880c5900f000000f00001e211300d4540302c0b511314016040b52079000f02900c0340140814032010244c2d16134000d120589092540310103490140c0710f03031 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 80586791 1250 80585541 80585543
    0xe10031e020102120901030b0405040b0403081f14131a13050103050d050a0c0f0f1505130605060d06021207080c0f03060f0a0305030c2508070510030b06072603040f 72
    0x7000058170002c80c5e0b100713a20502c4913181c0200108600e060905080c070451000302c4003203011030151008030300f80b524060341441610f00c149400b045d140e810500d00301000c0c5100c401030742e00801d4203200d00050103003600a142c941401084004922000b0201300020f8104003020b5400e00ca103000018004244041030318000d600590501d40c0d5500405c140440e00c05100035000340c01d07021030301016010003403138003074070980740e40a115010710503200c070f860031030448006950061040146200000c0000c1440c1c001c940d00100c002e040c24498500c41e10345030142ea0100d808894490564400c120b113058000b4000c64110020203030f1030b4102542e2040c1006144009041140300d0100c00040e5943c60343c80d002e00741e01a60b80142503c0d00d03480f140071a15079a00c0c0c0711000089030b44c0c91030704002c40000c04481610848541400800c0c50b949490240074102604a5441c4105921102d211074241c50751002400d009108820282c40c2601d2244055901102c40303402080401003002880040760405040c20055 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 80588041 1250 80586791 80586823
    0xf030605010e060f09030d270e06040906110703170a0524040603021203070203010606020607120e01020f040f0603050604050606030106050c0c030d0c0b06031c0c05070e10031e020102 80
    0x544c020541415040c00384c6451143d00d8850104078060041c0d11580204102c09602c1c0414002c1800b2504080211114015022203600d03c0000a900f407415030048600346005540000d018100c80f9a038821540c040070050300801c5041041e6aa0f04017920411035205ca85104100418140380c0d400705800c4000791140d02040d11f4a8042c03515590b030300c0d0312807001968001e265025200e062050140c07a42c11800081c4e1003946030110000f4910300100d1710300d125400303c1d5201d8400300319164200d4010500301c240724003250f50070f0011301542ca002000600150444a2400184034074107034008007580d5008004a00560a100600900d62250300c03d89054440e141000c43e142d03041402114079050303514481d44e03890302c02c680e0382c221003d4119055080c6d0318040d030303400001a40c501d07081c559500c202c05281e502140900301110312444c8034100e80314200340f01d241620111541c6004012000f40240d809410301e4801403c1042040381851102c09205014075010a071030070a40c0020307448644c0d04a40d80781d0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 80589291 1250 80588041 80588047
    0x3040b0a0203040801060e0108011803020607030c020f061e090c0604231f021203060d060902060f0706051602010b0927060103080304020301140f070c030c06050906070f030605010e06 80
    0x803900a00c2038901070121040208074285d602d65852445080a100b620555440d050035030003180076003508251400e400d40c0003003100e51907001e030403001011506134070002c5015800704035140400500030640603051803d5240b0240f603100031000e4400c0340190110300315034071031301000e81d858460400b500d044071031a00da00107090007000e40240c8207102050381d50f50300069010b00304004806001c0321869501a41d82100d07884400c072141d00b401071200f5601154005840c1c62100005051070b000b40c03805610182500c3d042000000704540d2603040b82c0802c45440780c031a4104854000040541081c40c115071000340206a11100450003011000e40301c1401120303162040002c503c24407031803c50810001e0202d40032980e40303051040890f001682d0880c449d50034400b103981c10301c0032806864011001507080f030304c4903107445105640800f064036040723013408a401f031010049441841118402c0035030760007400d0507207802c401c0205403050140d03e100c1890b10300320f01400342e641e010b2401c400380007003915400d039 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 80590541 1250 80589291 80589307
    0xf1503020c011d010506060a0c1101031407030f050c03010e04110406080a0303150f1503020304020f10020604120302130b070515070c0c150c082206020a03090f0803040b 74
    0x80d21911061203502e42c24140700074a100c0c0540101c3c1c2400f42503100801803600c071681000101c2c802c01460600140c5092003240c0854808203005c0f546280c141030014030901c461500000d4090111060303004260b89103080e80480c1207074019240c0c04483c418200b85958182410140c0e0410081d2004d0800075542015940580b540d0780440042c102040448000e0101464000c02620b0100900c0344043c5c900100000d000f00c140a82e00259640c2525000542c0900b42040340207400080c0266807015041c03845400640b10801504030800303c950281c10b49182c81d0a01001450081e0000b50400d44100b080c0c103840c03140000c0c2c8900b540c031510f601558a4200d414258680302140c2c02690001916a0038883c04540048003900d49a01c10100040c00d10b0351202200c2851030400450b00c080742c0d41c901e550000a00c14402440040702c0340b5001d0001001191200b42581e00b00d421800140e07100754002010305070062000e07002444a901c0040907281040710b41501c90055214203000b080300803910381c1c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 80591791 1250 80590541 80590547
    0x703020a0207051207170106050307030318030819030b01020c010219020f09152e0c081e0414060c0d0c02030f0d090f080c030d051c02030109140f010f15 67
    0x100103090040984c1c0d0018001901d05446403010f2265150b4101c0040f0740028000c01801000100d0710001d016080b0b42e851600c05072002c0003034020025400ca1a440301200242078100540b844008200720400380703801c000c2c000303001c4868201d0250f0641d0f1124080340d8040e070b8001184001519441001201c40c55603101140b140b00044c101d0680c041c0b849070400001040108c3d400071161000c459000002294440b00d14072080040180c0910003200101c1c1084680103404e100c2000c2d00c42c1c80b0480c90800300c0c0c403800814000a5112450800c80003074100444006003440d1a602c240445600d0328050709101d0765603840c150400d04109002e0451070032015581d0902607040078403849001d83d504000300d14001800d8017101d002c2c68111041500300451400e0700080c1d6595581c0c03015000300f20000c040102a46c180e00a0440348101d8901ca00302e841183c102400554024800e40070089070601d0b010b0b1305100710000003002c28900e9411100100b00e0480340398442c00850702c080b50b104071040710f000e40403 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 80593041 1250 80591791 80591803
    0x212041401090f0f0507060c08040e0606090301020a0908121303060b060909010602010b0112020c0c0d060b06041805010e0f0a090602070b0f090706050a05090112020405030a08030f070206040b0703020a02 89
    0x7038420410000c0710014400130314040c43c0303c103110390151600075840710360a0300c50034042000a0803c02e000e010030f0050b000740000302508640f000304243d0a0290701c000080c01c0e07a0003071070000e0004140d41d00810140d80c04020510341031207031900301e0303007080e8107602d41c01800300e003910020300a04d4075152550b207140c442c0380444008034805030108400d9030b142c1c50040c1c080d01c44142c01900044800d000c011408541d40b00344c81075000100c01900004103210100a00810034060581d0244c0c0e554078a188030303580c0c00b00108020060b600349070305070500b00f6410001701e540c140c0c40101c0d50140c54007048068007005c1c094582c000d00301c20380012040c8842c2042402401480c01c0100f0100403607040c0682180802e41003482503181200f10b40070340c0c4c0c442004680b0350203440044004038000340000a20396016000e01440e070011901c00506180c0c2d284002840c00c44012000d0710340d0b0070000b0500090348400303500c0b1948108640010711550529554007070480200034402420145d0100e11030640720720902c05 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 80594291 1250 80593041 80593043
    0x90307080d090b0112150b06120402031203090f01060f06020a02011224090b040b1507061b0c020315040b011202060705070803180103090c030f1b060e0a0504021204140109 75
    0x1220301503031580003000c8448038440c404d80381b1030350403034100f1040a10307802101c0c540b4402400c241e0408401d0b0000190074600604100d030700d4060702d0640c940c00034040e000313144140d10a500802c4004001c15555003141c0b6590804041c2100120b4240304a0fa00018490041582880e059050780040e03039003400241a00c500c209440503840341e401c4400345418800344141d07029100c00700500c2c03004074208412201c0002c00142c102c0110051004c2c12001c5102401d101c2d8042e0318040b501d41c0d0185030350400403004c03482c40b0780030508020717034030083d81410442c0071104407440107020b81500301621000035103801403103001083c0a600d0100030454660350140c82400350302804449000f604c5410300c0303440703410034001c0072440c0f00aa590600c00350f1080c051590f140390400788405a031030442d1588a040c0f101c4580a0b528040c000051a1000c006104528000c20481e925090044600d004016003414a40c0c003032403103a80103226031001080f5003800e183d00558060400c4400040c4543c00c1c90161088580c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 80595541 1250 80594291 80594303
    0x403170319060b0a0e01080f04020907030b1216080a0c120303021c1d0a02090a0902010201061703030115030b03030306010e1f09030b010501020d021207052e05070503090307080d09 79
    0x100000f5010244406000f454526407282c01c031045d40c8000458100c1d100300c0e9048640c04000001c039025007080264190401018640800e21500010202d0307020364181c0c500848540c07154403050303111107144207504003400050000e801c01ca0703210f03105e1382c01d0280c0c0f034000e4a020740c0142d1014001c25000c1c4e4121000482d240d407860308042e2043c00c01c04014055a001030080702517030340010f04036440200304001d21a500500740d4445031101c0084000401040b841207065660f104004198203011140c0341c82c400c4401c1000319640e6042a40c150407400b051042c1900b0f06d400e20840c034041e0b540100550350700800a1a2100c00403074110002410b030212164000c140c0100c806080480703540c002c98010650f806104603415070307640c6000490303450095190700c0d00180c1141c04100810003c0d440107220890040d0300300d404e01c1c3c07000c480c030b0404505c41d6038022040890702c2400308040390362405059808100340c2406419494804d403d142c89100d8200010460f01000405403410f0001c1c1d40898aa82d811030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 80596791 1250 80595541 80595551
    0xe0328020909010b0102060108160303320a020c03060709030b06180c040518060102030403032105150108070e0616141c0915050706020313050609160503030403170319 73
    0x2582c00c0c0201491040140140112030010400c82c6001804081046060f81c0000840d0b00e181c1f402c94502c004404004541111404910017408a50301000701c0c4007001020346988a0510320084c3c0707000007810082d4000d40200041141c07079900703d840c4504480c2c00001481c0c2503914440090340c06050b40c64030780d6100c0540c805010711402c64402802c191402690050151007003543c0442804108503803050060348208170500000c2d1003403480c5052420320300c0c85801c02c002002c403140141c600440340da03642d80f00090006100d640e8811201500111203003801034907200100c02080c010f104e0949c0c29003040d2030400c42101005020003100c44501c00343d0050b901490a80102c0c0e80b01881044140030005292100c0498208000c049c5201800095242d41e40b40c50803030741d69000a5080105001c007040c080d482c07080d010840c00d1042c1d6105d40c0c110b00c00b401003070345010300e84009000950411402a070041c4400e10010345501020101085c0000342251a0f6a03841100340540b4a0b000007004903a00740 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 80598041 1250 80596791 80596801
    0xb040506070f0212030703020c070807030b0a0b040c17060a05120d021c08060d020d050109140106080a0b0a0504020a0b0a03020c010513050d0809210306100e03280209 73
    0x119100d4021000c664a0808404815100300c2e40c1da0764040f600080703184c00b000819019402680100542503414060300e001c69035640d01c0b5400d0007500d50065680c8003c100402c41800c186120b5980560000c8034100244d80400b4001480c00310340c002000303128a22a0081201c076900e20000100400b001030100118005401c40d03d503c900180111070007501c9078040d40902d48400c0b426030080d02c0780c590780d01000c0b0f43d1290308001646a0311141030341c005080020341740210314207000315140d0900604041e049142d0340c1006908440c203580c024138903900b140d501000000d64680349560816050034002c035640e180c500004d00502516886411803640024806d0600768154000e03044074003001d0020005a07030f40c0c40707440f5420b2000d5040200a40c210b08000b6032010702400741181c21000110845540140366552a01d20000840c1140444880801041042c4c51301c42406205100345190114080b40c950000c0780e5182034107001d5407894031400740e40d00c140c400c14015600009800400900c410300b80 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 80599291 1250 80598041 80598043
    0x203190e10051c02040303021f1506020307030f090503030d05190e060f0901050402061912060807030b09070e04020d03021009060e010e0705130c020708070f290d0207050a0b0405 78
    0x1120000c51550049440f0306a00b451131090b10110394164000d0a09020341d80d40301002480000c06001d21103a5448101c000c024040c0001c0c00600480d8004565582050502a01c03070500e500440342003100150341845207440c0413040c0c0328084050880440e0a403a038000e0101da240c060000303501010702e0f2040526504034002a000e0254110f8200c501c49500e41d0480301c0c0c03c2c0c500442d40070b504044104000000c0e080140c0c01c0e100000c6140c030744046c600d000401c80c101600c2c0f041d84100d80340e83c081d140c24400e02111103000ea800810107070007010454900450810302040c001c0c006449040c3c0700146405240c024420b61480070b401001c1001041010310b0305c0c030002c01441040c1c241a40c07078032001200b80a4002070a0342a54802072a43d1001c4801c0b4480da00500584020a411030255500010315000204002d402600d0100705590000742020b580380031807100328030303640c02c400428414801e0580d05103003254a00810110090b80d81c1d206070400758a07110720000b0007000e206580c4100028004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 80600541 1250 80599291 80599297
    0x506040b0c0901020c1e09040507090e011817070b240d03080a050a060e09100b0604060c1106070b2a090a051c020a0b1c020a0203190e1005 61
    0x1100e421090099100d1001861442c00740b42c00c1c0c140075a016501640345803604401d10b210418a8001903460300c000302d00890160b440540c0c00b111503501070201031001101500131001c4072850361000b00144000e040b11101e125094080c094810744100c0c409042c01e0f50312004a40c2c01c50741041100000f0306100c1103040154080260300e5813000e900c0b03440d4107013a180c01110000b4540e0941e540b20003588403150800010308024140d40741051740c0b901d0000e0711201700e480551140003001d0150801e2000d072542081a038100501280c4600e8081105008642d08541c4405070f150b082120000d1546100010800510842e000034241ca0499001c01c1100792030054000d1500c0f94031955080e041d5030030982c10105019081c1007941c402c018184c14425400d084445941140c80301c0c01c84c031111038a5801054690b052a0840c1c4005c80d40041e000c10426040107a046011018610452800845100003510780c0101d88021022416540011031528451100310a01510051200d0003078107415070701501c564 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 80601791 1250 80600541 80600543
    0x906040305061303170f1807051804051504020a0603050405150c09010e040501060903142b080c04030201090905090c03070b090301050109060b0a050f0d0204030c0e180717030c0109050604 82
    0xd04a00001c8641c00280703040785000350070f42030b11a00c86d901c606190b80181c8003030300e1905140d40b1900300700094035541c00203c02241d4a110843c8030841c01e0901340795090041c00782c12140307480080d00030311005031610280d01c0c0071180c0526002803141c84030b103000d50502c10065080081500d44600344900044941c00420704d9140036200c91071303000020750500081c0e07a024810000407443e50700d02040440c440b0000c5070081000d140c207454051850803401c1d4144031142c030514103d0491042c00005081d0030000703803a00f0600600c01c10381003614540c0020304034902d0303005030948142c44801045a8010400010003507035401010360f4202603d1711a032141036044078039207d00c03075800c003000020780a205125403010b0743d80d440c00283c40c1030141e1100360b07080c0d1311107815134070040c001f0885144002c0140c40680051071080c0040782c903440c034040c84007855030303806061200612401700004860301400a21601241e154503040e007206030020f0b440c02c3c10b502502541c0c03103155091030448003c001c40429254412 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 80603041 1250 80601791 80601797
    0xa06080603061024050d020d0209130504021f03090212060a0605010311070f0206070606031112060709060311070204050f07110a030e010c02060c1006081b0906060906040305061303 79
    0x143e5240300c111492400c1510984403061002c2403002c06014071030107040018201418100c4c0350585100800c17007280d0141440c0d0225550114181c141d034500034401001e1801c45a8040c08941420340010741002454400548100b241c1d0112013001c1e402500b003aa2102d400070444011030f841c6140d815120758080350f100b55020310340840400d481d802072003401031855517001914200a4199142d0308525108e22059910038070910000001a482c0c0c01840090351194008000001c0000c0511294980c101c00320f1020740c001504120038558030090f0802120403e10300401c40741c002c00703c7e1242e40d00c25000040c1d0011b04001c100500342c1025505903000755910b07901c3d00c030440c0c1881030031901d41c020300e0002000240a0704a0300c2d0b80750f00c924841e4544500040196162074100da82d20f916154200000046058a0301c1c0c04002180050143c95010080c501e45442110790360400181504401440d85100329000300b503005154461030180c0d40656481000c4034204d042600d00741c404a000c0003004c03400 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 80604291 1250 80603041 80603053
    0x40809090402150a03051023040203040c0806130b070302093d020105090c010215010e09030409060603090302060709080703020103021b030a0c17070b16031e020909010803030108030909040f020a06080603 89
    0x89249441d07620b140223003600e41d80000c2d6a00d82c0041202a50005d1b0013640c01150680011600c03c1c0203104040c05000750080700d04900015107001c10704002c004048405151041c0044011503d44900c2e01c041e11500c1400d8105840640b21450b00540a400240408101c0e00500642031340d01503016600814280049403000e82f15040120794504000700e1900c890f00041c00100144031500d92255000204007007aa03080913250010001100c00d241e00c1140020b480700d98031014550180204c6400c491640381104580f07040282956681c0850710000307041507030005012180b030412581d1400c080d205601541d903070712021840140450140c01c415101e90384401e280303400e00072104049074030481e070000e103622607a640d241401229012038100030f009d0540f91005000c02040c2000c00a280c076107402d000503201c400c5001030242010b416003001101c0d9000308014080d440e0004166840c4103800c4940819560701ca02d042d00c4085141700009400080484010681c9508855030a02c160b03016021144 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 80605541 1250 80604291 80604299
    0x30b100f0b030408160c03080a120f060501090b0c010209060427020a0c1106070501060e0a0c141206150403050c150a0c080a021e0304060201060e040809090402150a030510 75
    0xc1d44010b6500901034407080201e5410300402c80300c0403055500411004442d180d480e1140300c3c643c2d000c440d2100000750140010719030300c02e00e40320303031302030041110001c11144e420b020019107141540c4c020711400703071700210785180b50820075011074441d40400350403151640c1e5510000403050b0200d02e281e03150a107030704000d0600c01c03c140c07091341d40122950360b40800d40040d64840010798140c1c000441c2c0c10880401401010500900801e0014524604c01d00c00c1071034650080e030100d408094622041150f0390000e0a07042c030f211829609240b80400c1141c3c802d0719544002141a0001406840c0103271001c0b4000043c40404901c4469025064905000c100d0768054103414903c07600c410b41d4046180d00c1030300740100e9182400f61403a0411130045512280343c1840c09040c41d074030b070380c1644200e500016040c050310b5428020040148040c070311075182da003040d540350581402851215801051400001010b666910041d0407401400c80c3d1001d13600d503840340f00200500700403100d1008041c0c03031100001e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 80606791 1250 80605541 80605559
    0x140108070807080c090414040b040620040e0703060f0906092a0f031d0615030607081b0f0403062f040501030e0307020907020a05010608010b0901061107030b100f 71
    0x1600c10007080e5183c190650b680070341c845154000f05105030f001950703010f10600351190403a00e0740c003e0b8020050069540740c05d1034840c080c0c0d035100701d00441e01d21003e13070701c510315190074415102038800855042c1c03103580e69100103c0051003e0742c070903036902010410016007030103c0e920a10a5880a0505000901400a4a100032084c100042045c410f2415079010b061748038401c80c003000340240c0b07808a0303100082035004640240042410403a50007070428000b81d0740711100f98003c1c0f0a03065010300000c3c5041900a0116840240002143c550382c40a816041003018126102d64502d05c01007611107813031303080c01c030000c0036140008994031104092401404806c69140d00004460070220361401d07007400011006810b074582500920312043c0460700069845e9240c040c0315100d141d00520b4014601d05015094400c40c1d880004141d00d41014024107448aa40b60347c15203050342080107100f500c0c41846840c28407594000b400441411040c0000728020014003001c44075203080600105450f030401c0303 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 80608041 1250 80606791 80606807
    0x3071103040b040b030702010605120f010513030e1c060507090611010b03100906020d1d061006081803070605070216060e09010e040f05060a0203160c1101081005040614010807 77
    0xd48000b501c140010006800300c900151740c006a948000b0074455a106c003c42c5070410f1b0a08100f030b054001002005150000348070b1154047c0b220500849005d43e1910003a12014924000b20b000d4241000b4103110031051400e0b0504140d807082c4100302a00e0300003c001c0c4045014002c0400069543e540c1100a150500841c1c480300341c010080d1a00442441c0030f00010300304e00f5412034505409200108100c400c6100f0786c039030000c00382c41c00b812102000d03030a0350070700c00010010b030508a00540144003440d0720100c2d450307100d201c903801030a05032030841a0502d5030181040c010030325810302042000c030903404142c8580482214200241040d12541d00b42d5050303506228294100c1000d074010030211412090440e0094000c1401400d441e002d40c40d00c50038050101c40d00c0003000d40020034007842e00d8078403001c00200410303890041101d2030190f4a80c0700700c0f541390b11620304001c0d452010880b18910000c4940003024014800c000c4560f0303406110301c00013901100103012540c07050002c2d0115000f0000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 80609291 1250 80608041 80608049
    0x312020303100905090c0411030114010903120806010507120f080711030d0c0c0c0602010603110d020f190f0f08071e0303050a180905061e0d080711090c0307110304 72
    0x24489040c1c02c040c800d5000740b8004104d0318191250300c140480c1607d5901c80c2c8124819559040c80d92581002407440c6e865600110b00e03810810440300410100301d901c400c450807040d143c80c0248164407401d0040303030305006583c0003426005004d5206151550050700d42010038080d51070b40c0e0840d5461803000c3c1c1d001c04000c090b00409400c00c01c0341181800669022601840d02ca0404070001c4181e81c40c0d0307900c01c143d5608030f01d000d81c1d5500c00078002e102580d080070f0b5207250201d413440c015560f542e001c120090400b6070514000c50a1480c08e07801c070800408044098414550b4881c07031582e44500901d1035569500c60384042d4040e0030008a0345585108090200c2c040d07583d018061949127640031522940300b04299020005c80c2003008078480c0d1041e030104020f058100d0042820b0a2000410103919450501c1e0754a40e9138017902e03280c13151100c1a881c0101030300902d60584074652410184402c0c82a9180e0302d0b8000c0c1c4c020200b21041c400d5401950044c0e00300c0c0d0300c1809080d43c404a0690724415409 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 80610541 1250 80609291 80609311
    0x1110c03070308091504030503010e0901060302150307112d0307020a051003020f0d0509011a0a05060c0f122205150a0e03100f14010b07020d0c0b0c070312020303 71
    0x4040c0d80401c0c064050541c00c001420202c2d100e905c03070140e03002d822110680c5c00b1000a40004010084040d0b00c90071325810034010300080000e140b9641c002480c05c130400e00c40c010341e40000b00000307000c14080c480c2070704440307180300942e820074031111071140078100c03000301c08410310041d40343d180203d6000000791008241e01a00c03070013201c0c2c14041000480303010384030800101902000501c0c0754243e200040e1241d0385d0000004101d03804c3c812001400d40c9c280d0703103100c264141c0b2007600d190346030384405030182107410544086603500e2100083c80d0800c17a00480d14907a51041101603000d0b00200002444040301070682d002040a05034041030040200303110b80c650001c034607505150018179410041c03414150505081c08424841d0011078108461a0a8014040d03950f654008500da0b581c0100004405040c503c01925030500000d84040c0c0240700c8003038001c102200e8030104009217454100003501b101d4407055103410070301c00d007503940707200c2804104da0150b6601007803681e031400001903c1c01100110 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 80611791 1250 80610541 80610547
    0xa06170c030c07080c01050f060301050403080711030c031306080c160605070e0405090705041a0d060207060b060301091a01030204120303050601090f17060907120f060f05090f01110c03 81
    0x14520209070000b410b0300c04070480070807850001400c003c0c003c0c0b40c400c2e0120004501440d08a40a41e0741c405d0040c0041e010780d040100300f00009502c20202039010009040c1421080800d6840900d1030243d50600c0d0301e50b12001641c401030203246298181190000e0f13a51528680d0b9000d0b4002c0d0500072112031300b404000540c40340c400507040d034110982c01006443c0842e80c07240b1800024064410542e41080c0395000b0100038403141c20680141800c0150620004050140403070124101d400d0190b8007425071980030030709400300545600112508003001741031684030350b15031403003074010054980c2b04820b4811030001750300d41c3d5000380207440485001d90540851007030303207803401d4000c0c0c41c0081c500c504000c1c25282c007090b0f617503004040d18090503080703800380c0c9240414940d0740c2c500b02003e00b41408136400ad140401c60400811a4100c0c043c0d840140b0700721104007850090040d0120040c4503a606040c4030070044500f10004440d01d003211140000c0c460083c6810112403184650404541a60010 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 80613041 1250 80611791 80611801
    0xa020901090b27091006063c020d0207050415091508010e15060f0a031709030d0c0201080a090201050405040b01050f1828180b1302090a0617 62
    0x3940c024012881c0c0a044a4001c4402043d0800d0902c4446a007030200d403007940500442c1c501c00c100c03180555106540c20001c3e641050406031005180000c0c500c011103401804d951141000403000100202502c40d1401c0c450170351038080c0d141c0c503000300a480103100301180002d0515080c05403c901d922805443c9031000d0501c80110060306604d02c445400707034580100050b591800b441014155070b1104080d1540704001051005204c001500790380c440d41c01d000e0517041d9555106030500071241e00c090004503402c10b401e80504540a460309140d81030140aa8405003036400690311040d0340c0c800da071880c1082c0d0f2501d02000444450080c0607002403c10711050025040680c410807603103005042541c2082403451002e0011750000030011580141e0800d4188c60b03091604841440d221216640e803007003000402c050550345450700c5081166526841201405811365014042480b0042c00b081112200c0e0450f07000650f104000550283d008402d000030390750300c07503e05284031242603040440c29850b1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 80614291 1250 80613041 80613059
    0x606050f0903010207021023032502100905060117031305190905040f121103070b0406090807030305100f0b09151b0a0204050a020a021504030e030109050105060a080a020901 76
    0x100c05001d9400d990308000c100702680e00d900072410400f6240d42d5031002c0210440002c65541d290f1419200c0030941071040c80702c0b00c03810b010f402a009046c0c5200f8032001007884c90480c13130105458612181c540c5030810040a010000c248141a036034200c03c1c0d91100200010000d56904c42c5483c0000450182c5c0c0d014000f6240194100541c50b10074210600c01c81d49a451034404c40d4420b4030308a4070f00c0b40240040b4100b05501800c45001111418882104080c580130307180c403485032000041c48424500c0000d4100700051f884220303c5508210070a403103030486c0c9005801404192640f00e141211445c2c00104008008804029100258406800c094400d41881850007942d00144004c40091001d000f07428000d403015a507600d00c0c0c00c01018401341c00d005100841c4c4000d010009010f004101e108001500003410003400c85020a4502450b500c2e403c040300e00c11720040a00741e2650038200b8138000d0006c150000fa0080b038085544021840d900c0940d1660390901c9840290807050240040001d100 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 80615541 1250 80614291 80614297
    0x70503040f02010c150c05070204060e04050a030e03100516030b031b010c06020c030a020d03060803130b0705150901020a020606030c03150a06030204020d020c1603051e10060303090e0a0606050f 85
    0x403045c040d0176030449442809805860b44130b1503200000d0400300d003a40c25494980240c6e4005c0121030b20195480c01c01b034030f5540e1500040c0e8006402d00c0300302610721070b02d51000c1105017038078454040208042d04216841e041c400d6030b00c0190034000390406542d50104c0c03901080030405200c004803129603040740d500042d0352001000b141540d10315401e2006010086c03051004080342071640e400b402c01c080390301c44060304031101034204142c0c03a0b205000b020681d601030036440054900311140142c441c00d0381d20b040ca1408510695a08585621505100c6075601c150050300285040e030702582e529540d12810b0554801c10103981c00d0f8035034042644000321400342115690841800080810307240c3c2c41e900460184d074002c3c8040c003901640010b4010880c3e07400e100c0e0a04d0510b4802007010080d1440c0c40316590360410241104861856072141c441542c0300304005807105410036010302c411903681c1809030810708c0c1841092246c6c542800001d00141c0c40b40b01c1c15040d1000c03602d80034104954803180c0032241d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 80616791 1250 80615541 80615543
    0x5090616180e04050a1a0c0304030e03012c0c0f0d030e0a0e160906031a0907030f24051801060f0908100c030612080f030703090c0603020a08070503040f02010c 70
    0x88611000455030b61081000c0500c5240181d00400072101e00b46404c43d0210b28541e258007416160605104003030500b00f04894225815240090a444981000a00602d1510708105408a00200d2100b5101890910a00d0381d00c0c45400d03100401c00d0ba1052100d0580c049816590040106802d103002070300030010301c02c55060180c0f06200a603241c0c0841201c1141c103440500094400c0407070703504106e6001d494080500b480b841d0034418110f9880c00d00b0b05c4010300e001260700c00c0d0707040b200084a10344207512410042412540c01d005090308420500b220100300f20010300c141940c0075021034141801003410040f00050f10200407240c0c03070030500b12a10b11842d0182002c202a01c4070001c6c91044c03c0280c0d9160343c40000c4000361902c03c41e50054112112507014045004000c506a0085105481603445241701400c2d000c2e41c0e0350b1551411402054030500040c540e4120b0307400420322aa041e0301814005405481d2000c1546402000ba101400100d500601c080300041d5558010351080013821021 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 80618041 1250 80616791 80616827
    0x4150204030807080324030c01031d0106170106090b0105040b0d0609051f140d110a0803070f030206060105070b0103080d0e032b020c0d050c03040918030305090616 72
    0x26140c0d580c03120241d00c580c0003a44c030840c001c814054030741c088080c4c0c0942c2c1080941483d4090b0009000300380c54180d0101d142d4141955845510b050450505a403444141450000c1001d2503c861030001c0c009011124029a50701e401c502013004501c0340b103001c1100074141c4800d803d00c0d00e40030084007160302220544000a8980c1400038100c0030900449000381c200c168040b125840c0000341c0c01c40200c030740d4407008200345540c07280c8905450388000c3c0803070103070040c02000700201e02e1808549401c0702540b140d24603101c00151101801100111074060700d1196003500e09644035200119442c2c05032300000b030060340ba1a0300400001d40980b00400d044900700b0808500142c07070000746415500401c0d2441d550540504403400d035074501445900b40340d503215804600b42840403181d9980c4800c0e49125400740039002440d04103144081068900400180b8003d1100d401c840c4200d02c1e062840f4203046010906141c0032454403040070030441d04c142c00c0e506440700b030000302190854046c205481e401c025 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 80619291 1250 80618041 80618047
    0x10225030e03070f150c020f0d03090e180d09080c04020702040f110a02010e060f060907020a0c030302100c02010c0c0803060117010801020909060a06020a0b0604230103060e0304030803041502 84
    0x507901c043c00410028401c480e40e02d61050300c1d0030b04e080b1400f00007010703510821603602c41120042e0388000c001c126032603007544c0480c2890030a150503143d0780303002e80180d0b0709184071200300021805080700c60214520380405640060007000e805880040c8a03001e24010354104000c0c1561a0401e60702401000740020004a40b0050303000c111011181104d07514220110001040440300d502401100aa20701410090545160076049030000e403102070191481081040080340c0014400c0080d440500c0d0094000c2140319502d10b000b0350f54a085404821203503090140e030030b4040b0b006100e030f101d10003020b8031240358a080c1c542d0341201c0c0b40c0c00140716a05101000ca40700503010241d008444c003038400d03440010303503c001200030403440481c020151407046001032030601a0b594045a6460303010351104107024503881d00d00c0001e02030483d07480001100a5820f182244403100d00100904883c0184000c010b8051032540040d101d00c91400041d06400c0208045000a00f002c41d516800031036000740181 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 80620541 1250 80619291 80619317
    0xf0303011e0b0310090c02370212010209180702061501050c01020c0105040b060427021f0309141209120a08070309061403130b041a07020f070801022503 67
    0x55400c140c80461407004c0408040c030260300140f0412009103a07070700042c500c20100c01d8540d8820003401c1e485910070081c3c1506511080081c00b82d40c68842d90003031500850000303c0300b0140c000d4100d4015940310b000c4012055500000c00c000160142c01d569024029550703031581618052038076016414100501001112400c031800c3c80903207e629406000410582801d0510612650700a801c0910407072500b0f00d00c40340091035800f43c203c01c07940307034100350201d43c0360380001450400c4814122014842550301104400c2d4154000d10190b403041c85d001306100c2611400ca552200d15501d005001c0404000e421418600300300200c40b12401d04040b02d880078520b54441401d034000001c11400306580840900c86607400c07441d0071a0000101d09081e0551a154041400364040c206001c1d080e0860a00030038144a1821071804200c9400b000003071390307800c0c070141c001d554000404800425004008003c80ca115060007114541c10340844d843d10b1090300090452409801074104a042c00380d80c1d1a905 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 80621791 1250 80620541 80620559
    0x30512100b03060d020a03120203070507050312070b10180504150507020c0103180602040605092107050409020f120c18061503060307090f0c0f0206061302090a03020d05010e010e0f0303011e 83
    0x11140307840c62740a55128034240c0303021842d000e40fa41106200307400132025958000000d0b8166801c450300560310340301c20307102d42c0e6003c0c0d12f151300c03034010030344501440c10b078825042da030327030704454000c6104074101d4540c880300028110460750251001c0005800819a018a640c4030b60007603000d0000c003c680a400d003000d541c0340c40407a44240d00c01c4000c03540c080723084085c603c0d08810425440e032052404d113600101f000324003a19001c070b030b010b9988115501c0444209644804482c21498440508211256a00500302d00d6030350564000b981d00c5960340c40c0202110030351724007a031030051601600907005440c14501d100c3d00d941008007015014401c030240054175109502512107000d080b010700003151071004c80020700018024010b030055500141c107014090710360056610b9901480c90005031914100c0000407103648040d0b2001e0340c00b12040c1d80f0802403000650040f611131001000802c01010803e01e425107505880180100356041400100800085180900c84204140d0310307800055842e07030504 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 80623041 1250 80621791 80621813
    0x1030602181c020102070b030c07030f0c1203060302030706030603080910141216050406081306020903100203010e0f0106050d050703180b07080a050c0a05090307090603030512100b03060d020a03 85
    0x3008200d00749a01c031100f956010b0207510080d0007447d165902d54500a00c0070b021902c22000700030304000c14152404421032040d200018001da0110f4110380c0c20016603002005044c19010a91090040c41c1000035028064070030f0700126688100004d0403c218141040701d19111080e040c424000c510210414082d00c0500401402d07030407003058505824081903504030710741101c80c01c10510034100018040c4641250034103500c0b01140301803640e82045498110003901031310190b96014415003e00d031040e183e0f580c000e141a81c01000301880580d03100e1807a88042a020300c5243c010840c2003101d0b54661035650000396100e02c1c0c6042c082020500701c00c1d80d504440740004241c0e01c264000040c0440b8542c0701caa4141c001074203030400d219500784001d00800c01d1088021000501c1350000701400991024030844c401040c1c00030040100079904d05000d4a50341c010019004040b01120008031940500d841c540d040c2c42c2400c02480c119a03500f402d0145140f06484280e902c81840400040022684601 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 80624291 1250 80623041 80623069
    0x3050c060f06031f090f210203070b01090e0a02060c07050405060604060f0f090e010b07140114070509040f050906010f09022109010b1f02010b0a0b0d050c1b0d11010b090103060218 79
    0x200042c0c02107041084140b80c9400c8200f40c045409c20071484001c280c443d030300c040c1941c5a4160014020654a0783c4514000c82044029007104c40440c6e0032600705008100c02040b104140c40602c196501c0e00200600b501c103901a0b080415102c00342c0d03480342c510900324009034210504190f01119190102a02c041e1000d0703001d405040d0b80090f072801000601052004030b10341c100002d1160b08a01c40d00c0703a54502c80204000d0400002160404d01540c407900810401300010070100120f0600c0305242e078030703001d0900610a21516450001a003402c680c800c0b584501d031200102d52000034154440d6202e100c01038400c1e255507481d010768004540e43d4030310102c00a01c0c44040341c071914000740000303402c0d01c0407540401c1c421108844208517203c802000c6030300c8804554800501c035035590300c8110440c012030780d1011150505010024003083c00080107564213607240c0b1100c2c0400c0c18003c00d0750907a0301040d003850b003144c81c1c000100700048030340d000740030a80b2303044031404801005030300426100c600f5004 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 80625541 1250 80624291 80624303
    0x9060902040b0103180312021b0a05190503040b09010c1b0f0807060c08070201090305060c0702130605010518030f01090b180703030c030e04060f0303050c060f06031f090f 75
    0x1940404515062050005009080c202840311020340760482160405440010b8140401a480308a600945504403110040000d1b0030040f0181c124188640d2001d220700111601d208101c5c0b8844140c06550942c840142d01000651a0608021460103180c110b11841410703c00e140903d040021910300306005c0304038a10400c40c014520b041304c494040c14865202041c02d402900d0280304984c0d011114030440d80d00200e840d6a12810752004032540e0b86c10b41d0001e496805810280031203a80c8000050031340c076000300e0725022004607020550b070495045100346030200f07908201a14074000b2040b5580712205000b01600d240071007820b540c9007910f10315101103031205c070348408000e050a5243d1400c64461192001030142e1811698080e01421100c81e010b0b040c07020942000132150744030b0300040058505440340726800c0c1da5034074010b003564000200a080301e004c1e1000048400102064851190320018010b050343ca08031030b2000b84098140944420841d11604150003181ca05201d02c0c0700148548 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 80626791 1250 80625541 80625551
    0x90c0b03070e1e030a1106281115040f0302100c0e03070b03100501050d11040603050a0506030c0306070c080d150e01080a0209010521010c0f090501081006030c120906 73
    0x160400200085400b48040b802054810751101078900044170b0441d01d0744201c4c0f42c001d03500520700290144c0074445141c20b4099110910684410000340c04152190080d1141030840c0c0b440d039801602d464175410403000c2c00c084d400000b0003141302c034184003a10314028015034280885059502d0103a486211076000410700d41c440080450600f00007440083c14031020140c00c1d410088810f407044076503841128104100828181240b9542d50311501c544211603c05607600c82d600c55000d0b02901049846560044c9000002041c5040126601c000f088008000d0100707983c604000b90364243e010001540c000000340720721000b89000b4461000e1015802d4641c045c5145000304102c20418141c100018a4100322a03a80044e1507034410380d030540710304866074685c2075046260541d809610002030403842d82004441c4440981206440c04d01142c29920048200e482d80c00548d8402005e980f0360b01000c1418400b045420310a5107c0c20b010a0b0601c2d004d90201002c020f40c209071810400d00307954065440b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 80628041 1250 80626791 80626817
    0x305010c090816090b01120e101103060901060305090a0f0f020a0f06020c06091315030605010906060206040f060b0306280e0a021302040515030a060b071203090c0b0307 74
    0x140038100205108002000020400303100803c00200c28490200002e4841402200700c0e8000c0b0010b002411505104100301c0c2108121955284274111107015450b2802d00c41241c01d0489034100d0b4071801d40a0305c00b510070791a040d0f0807802024001d024a03410300a80000342c3c0003a0100b007590350381d02c1c094003030f00b0080c040c1401005280806076001030701d41406402c0170030815801049400001d0b400321a450307240c41c030300f8020a0329010300d120001c07406840c09102d20003007030301c0051410989005943c2000700381c1e2100b946808441c0d42d40501c0015030f214000080000743c4028442030b21911640011500c030303c2c484042850030600741c94505003022048400301c120021400300d00c3c08568480700c00d011004842064980390805032501a0181c58600c00810b1158040d0301164001c0c280985284d0900362030640c822041d400030380d03404c8034190070030310000344850120701178492982d0003145400c0701000fa100103070003c00c41d28000b1100c1101e41b450000e100d02190021b14883c04540c0c0f40d28140001d0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 80629291 1250 80628041 80628047
    0x10519021c08010e150303041502030a020c03010203011202060702030106090606050711041e0c140f040302010905030a0b0c130902030a0b090f070801090209040e030403050d020d0c05340305010c 85
    0x22800c0160100560b0b1401044420002d280042c0c02c2007000b290f00c401c64140c180440d0071072041d50014039800d2030030038621038050b5000004040b164401d03420380352142110010182070384003e102e070081d5040c0155030003016203044801401030510007400002c83d2a07030f409101e0156200d42c0d0149010490204000051117403d800091004108542c2005296801041e001304514030070340c151a40c60303644659424079809408158a169458a00d55444403113801c03c02180e03501601040b40060051400090507081c006084280303198000d480e0304055464048207000d0760805840c4c10040000c9440000d002403240c0b008602030500640080f80103107480081c061381c1500a850550301001a100f04082c0c07176404201d95055840782070026a48600d0780700020007900c42000c0c00d90b014000040d001042200008000750900c0d065000d8514010b03403820161001603030075501130410740080c840328000c41c2c1031052050180c64000c0384075640c410b901028024400181c0c02c00c84481e903403200700c40c0061390 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 80630541 1250 80629291 80629333
    0x30103020112110301030807020103090b0921090310022110030b090c01080601050307030b09010f140603190225050d09080c0d230a03080a05060a0308071101051902 72
    0x4400c0b0020700005083e0308900859110502c8007170400400816050110780c070070781200c0e000503045405c0340501e0403c0e200542d11064507103e0408940c58480c2e2108a07070404e08184d5036406002400380801e50300114418000e03611018034030b60b000c1d11301b40e0041000740c600358400340144403103c3c21246990851501d091b000304050300100e80c4e58000300c050300882c3e0344010442e038403400130301e041c40e141d1b2605079056001d8241e4a010075404641c00f000403c8141c000b0601d48121058441c818525940010a001c0035100a4410f581042140750011000c962150000c0c62503400041c3c260900b40b03c1d1100000c4107040e0181c0071900e80e00a07003c0c402140d581b041801c2c014002d2140030f442c82a21410001c2c00030b20040400816211a1503a501c043d884c030000407145400802042e0742c20704a162800505100007241c00b0080c00307192601281490400300c41000a9aa1041303040b0f1412085886480b44103002c000054100042041040d10f50b0130302c48203488010246400401c0820744480c0e0b0011340c58 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 80631791 1250 80630541 80630567
    0x2102010609050408220f0801090507090e070308070c1a07020a2304051803070b010617040305030a0f09050f01021c02030609061210020310180515010f03200301030201 73
    0x181840107120200d013906080780c4104810000001000100340b14000d051215540111030304030f4940400908070034103410140303900303100c4e03400d55030140c1e2180c01c81e00450302e241840c030b400b40e0320881003400050603c41c000c03c6218082c0d110720b80050f071f4508449684642c1c0080642803490b0110310b04045042c24444c920242000c642403810310100c101036000340c0e1544104480c032a81e02d03000840c0090b00c004003500f90380482c40c0180e03640c403000c40c200345007049002e201c0c0c0300002d645810381c0c02c00b5410700204a1300881c1d1590b22245540c466010b000040c01029000d0b40015070743d4014a00010b01c108a46414200d800001603200e0301019a2046149142000c1565035401082080344c1d6030b684840e040c0d40b0500c121b48540d500124248031914000581c04c5001030f592001040c031100d0104980f520040301d008c1011408000c441031000015554161003010b1150010540d10200b50700030403030041c0c107014510740066005000d6140070b003031014500321400841c0001005005659001c0007141d004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 80633041 1250 80631791 80631809
    0x9010b03010617010e150c07020604050a090603170c060a05090c09042312090607230604021f0903030f0507050a0b060901150203040302010e040f021305101107051c21020106 76
    0x341da00850709946c03070030008242d08482030001a4000465803a04281c0340500000341c84068015110b052000c02072165002c00d403903404090890300ca001d1a039008a03207900c7e00c2800a00a10f0301c2e4411074502908003e4000c0035180105841d42c0169100c244545115074060800c1c02a0303c1788201c00883c00c94510705060788190040540054421913020468800800503100346541d2441d90404109201d07032885124281c0030040300c038881c1c020000404a0045000320b944000302002c05c581442c0000c0300f8040000480d200101c10000f00b80900c19101a0b54401d080c250316005540c1d40710b509007803103c2000c41d4180c2c1d500c82448010700305218114090850f46101824190084101a52f2030245105c004c1c100f0541c44100807040c1c803242c1043c00e0348410408103548a000354034040342c1c40001401540d003d0007255041036123444c0304a0750901803041e008090003980d418242440034140c200d2907102c0f181c48104284000281c001100081000b0303410090700ca5181d004000242511000d40c400243c0c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 80634291 1250 80633041 80633053
    0x80109020a030b0c090d0f11010804020d12110307080c0c1804080a03020403150b03010b090c04060c060b0316060206010b0f0a030506190b070606051206010e09010b03010617010e 78
    0x141c680d1081d42056035001491025565520304480c010f9119104442e6000070a5840c030342c0c10009040071100505203e181c0e032040741c0241da0b00440707046408030740c0a0751000804920001040700710a141140440a24141c10300c4010442400c3c6540c1c81440220b40e16032000420240080c018000310f602084201c52400f04280789040210385a28068805070510f0400111040014001c1d41110002d652209804039100110981c0000074402d041155000f5420590307590103c1c81c1408c130140c421401c2400c41403d15060040c102e4020488400480b0038550310360035400d42d5a01001102c49c00300090000c01807660a000c0c000b41440010b03444400800800e01030007a071001d81c1e006035540c502d03640c0707000100741c2e44d00070000d100c1c4005290140200c25003800003181c12400c4078020a9901d0003684240056682c49051010404c181103a800c004e40100005000303502090407055000907030500003180ca10070302e500103421076100b0ba2004c0c1d01c1040d0112000795244080c081c00001e2010403010b80340c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 80635541 1250 80634291 80634293
    0xa06030f0b1305060c0d05070f02280f0501050403170408031321020601140f09010e07140307090311030606011e03020d020415090b0c0a03180503010c0201090c080109 73
    0x40c4102115400500701c500500028030381c528418000030300940c211085514505144c000503086030b21030048a0801410030002a407294043c0e00382080c6e03401d060303000340b4038002840c0402c1070108900020900d01d04034804e880300415001f41140600a00071000010070b42420324010388007400e22824085800e51403410803000c00c50b68425a0752102c07043c0510502d000103490300d410840201903400191036130980305010020b82c002045411780d40d100b020591150312020400003a1444081d2440d4046020030041c23118061800406421842c24180100315600203924226a900202d0f442800039013090010024011541e00c5c0c04140032099003c1c02142c01d0641c0001c2c4480160aa12039868019071180d10303800c6d201f0344c1218060990182c0440d00d480c0c4400d07260640c20000ca11090000f080d0387c03008a00c403218103084500910b2840d00800d43c0c030b02e10395001e440c0d00e428040c1e88010306803141000200e54800380038100f030707002050740001003803a110303d841100305401d60003100c0b0503171404035000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 80636791 1250 80635541 80635553
    0x4060305060306040c121103030d050a05090c060d020d06050a060507030306090509060a0b06160605011716090905010207060501120201110d05090f04091205070b01090506010c0f030e0a0b070b0a0603 87
    0x103c25103901140c006032003541407e14a01049848043c25018400001d000d011040b0b079900ca14054041848207100741c2d2a072540c5203554690101003964007880400c0342d00e40c2410964001c0c8030150548001080c4c162b035603000180c6004072075000c3e0700401c10028403c0c041542c14401c0c00301401e60428100070701d04001054a54800008203080d03003160380c800d080d9a0360b58980b41650b05204a16015102025513464048003508003841108201c03001c8070040c1c142c404000c00c0740b0f842c038206002c45810091400800300040c02c040e100594840d5400c10440000c1500d03030041e1400b80407120000d034091a11440014001001c010300307801c164200015801c2e01c11340c03000c102c5840d2541243c1040c21000b808002400400042d81c00814005451482a050580101c090729500740200c00c1086030341c1c2d841004105559040b01c03182e0000d003070044a50000341c420f1000070b044900910b094104410f03014007051110065400c1050710500101e01c040030020111903940d0300c565210014030003645195103203 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 80638041 1250 80636791 80636813
    0x6011a0414060706090c090204031e1a10050d060507020d0311030105010e120d030e2b05030c070b010608010f140306061c050102180414070f03050703020c0709020406030506030604 79
    0x850b2081c00005458014016590008104030380c000c400c55440ca6550b4000308020362280c40103c40c2c076851042c49145c205031680c140c2c00140d4000c9052003042440100c0c0000040b0018800001c059a80e4400704940d10b40c0f542e040c901a1240d400002e290500160292920700d0600b094000c0505090081f141640c09000307582c1101c8007070070701d11080407030f00c400108230386045130b01d002c40c0e84541890f4010503a410340121070205582130541d4400364403440d148203080070b8401003c1508442e110207000151085009544c0184500307070b21800c094195403000e070f01d880282e0140c80000c40203c018071a003000c44162100a00c2d044140703509200c42c00300400e071145c20042001b0310500c560760409003004589104000060760180085540c0d00d800b001c13080740c0e0061428014040c616000c0c8034842c500482d481c042c040c1c1070603118030010703004c1000c0032809404020b102c40200364003441184204c1e40d0800c05640038011107180036031200e04045005084400052607a032007035101d00288030100b4442c0f101c0e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 80639291 1250 80638041 80638079
    0xd0c060506010e13050114060309060112030302070f0323040e0c030411030d02060703050105090c07020d020604120f02150f0412290610050a020c090a0605060301030506011a04 77
    0x10800da036031100183d07490a0480d14281c0c1018503600410300148241d8001c40c16220003409143c0041d014a0a014a03400111045181584600c0040c00040131a048540d08944203240151034100540d070b43ca02c5021080d10200d000ca07104201e0360003540305540c03040d01440d041752482c2e42001d2501c104018220400f41c40c5500d8014000045020301c0368862180010342c03c01307000c1310300010309200000e41d2214102c51510000b0314110000c00e50f0319001601e03602880400301c186003040e00907020815030b15030601049900c41810400044d9134115400301001ea41d02803406007a20a5541c01400801034034424402c0004a0804c08502c0c02c00c040000d0741c0c207440708910030500418403403038111a120b091010f540b06040d16032500b01c0c04110320099007449942c00f07417841e00184985003026500c5000b02d4001d0000b5030448002d0a480b405d01c1c14000c0e134002d00082c8040b40c047d5881c0c0c00300d101d0b5403003038100307580682101c801407100c50301030403141d04441284a0552f00d40340c90403561b45030441850007 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 80640541 1250 80639291 80639303
    0x13020703091403072306040609090c02030715021c0f0603050111030f011205010e070e01030615080303010506070507031a0421080711010f150612060308090f030312040305070c05030d0c 81
    0x98001c00010705811805810300c40a803256940d90b840704030181100c27400d881020840750506101545903480801994507141d0700100036101d10b05d5580448000e07400c81e030000b80303010faa06040b45018624a026131031800f215140f000807101c0c2103091060039150101c072420b43d442010014001c00b01c00541420381100e617081c50700c240c0c40e60940740503405044681040d0500b446001004680c000c400c0804904813407281804008120a6040e60320000a651040b620580c106000410642c00d100004242c554811b5040d10304d856100c0d038940312440900c80705e4020040c110300401041103000a1184400600c035681c00c0102c031a4400c000f441020024014030802c0501c0c910001544400d41003220b4006105006001301c82c162100c03088500d140c0c0c8101e400103082200c44d000d0420441c032030032040e41d811441c52490004140c1c10f10071003092604160b50544000c000c01c00c18100280b00c054040d0b4840d61b945996100c4d68181310346500c180e41c1080d8400e401514a1040e1690041c04800c0034681c0b080d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 80641791 1250 80640541 80640569
    0x6171501021006080d26010501030c0903021c110909030304061107120e040c1106040204020708040803070c0e18060703050601030e03040306150801020306130207020d021302070309140307 82
    0x40040b800c0c10602151100c1140c1024004100d11a000c030f20407584c1e007155903403d007494010305082a10a5140c244130000c2015a800522581d4072a401031134040081d414141e4480703a4a40c04621440700f0b41c4540c00c900700c0703811019000c01902a03610340801c82d04444c00c0b5518288900d0303080d01da21003e80000d00d1560360b844000e01c49003001c1d003075990068000f212a00780781e846100c003404034101c03801014131642c03a04c40c83c450242d001c1c0345406c127250207403402800d69a880ba400c2c0002036010318002d5800c250300703010000ba00c040c100300800100d4401d00d00c402850b4078240d110714540b0320180605990818070b00188400840003e403aa900160601d40890141c990000582c01412840031400c00740c000064040240000b54000801c082640d9801c415411340d01c2281e2802c1740010b80e00f0692000301d4a500000a5846402600c1c0c0140028041d5810014a03800121604400c02154203450740108000702410340100300701c00107004000180d40071241c410300007511181ea50154005181c148 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 80643041 1250 80641791 80641831
    0x12050c0a050a0305071b080a2d0516050f1605040603020f040b0d120e010908060c1b0705040c110f01060303050910030609020309010902030d0509090a0e03090312130617 74
    0x6460700c841c06c07481044044580019070300f080051750f03205410349404550302d82600c000c40616040d00207080c00a00d810645400c10340001261940d00c0390032800260101d080355040031540c140f2880b04802041d800401e046c1d003040c2c038940c40c803400c968009403290b89006410000750b100d0310a166031040080301e0000c0c40240f40000100e00c91440d00020b0101e03082d100d10700380881d4001d0720302460000241c8a4001d82955500f0030703a59443c080381d06480894060268604201c0340307618002404140030180e42c1d41c60b0701c03040420115a82942842c7c0015051001d98400813030520280045801d118000c0c42514207540703001c2c19601c0f41400c0b40740114029000c6544443c8654082c00207429a01d40130765603420890600ea020b06120b01c0300340e20a000d0600c0e50110b0070300a03400c07503440744009050b00c006907403051560002085c02c90000ca0301382c0020015039003503030f03170600c440644042d4508031fa646030468103c65880003d8507802180c01d100a00d00901d009246e01c0b07005991003030a0041c0e03001c1d9100c032 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 80644291 1250 80643041 80643047
    0x809150604020d060905010513060b040504090507090e0723031c030e0106030b0f130b0c03070306080a0b0114030d05070803091f0608011118090912040612050c0a050a030507 76
    0x2600c0300f8803902c9403415401085154035904028105c03441262a507000c903a51840a40441d4254426503000c1c2804003c200b08506054100301c2d601401001074424841c0e444a0344002d54244862090041e00000401d0100404070204980d154000d03100c0002c0703044107400400e40d1080d601c1800444036140d00c0f20141ea46219412415895030080000c2c072800d42d8910300001c0841c0b080e1517180c007175030710b0701c000400d00340204444d140c500b42c0201503648903465940d441c40c080d510142a0608050300c455001c6400d0300704002541c00144946807a05a40d0300d451003035000600d42c13248a82c840d401c6078800d51682ca60107030035a1412500844d085e90f030b903140c0d804030f50302d0070f4141d9242003008402c07111581c864050b2548036a040301d0000001f400303040846015211148900e040510036484000140c44442c2401e000709130b403101c5842c040b5110104000541080ca40007030740f20030b001880f045005a040c210314041c0d1a0002c00034407a071404e012104a02030042e000d003886042c1015900e00000c0c9490384 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 80645541 1250 80644291 80644297
    0x8060f1b18040b01030504030f0e04150e0f01050406050d150b1203130e04020d0f0510050a0e0f0c03150c07020d030504031b0503030d0e032215080915060402 69
    0x114440d0344035030318469200d00c55640703011404480d00c03440c0f401080690f294041c0c0034151060794541c3c0d503103001030310002041c0c4000c40b41d00c000d5600940c8d52111f80d5a500c07403510400d03000d882000b2051442d440d14012401c42c420050704814011030510104105586a0b940026000c03036002240b0141d48011112480007042c0e0041c00c40c1c1d12040341551201d41d40700c044002d00d4000820000c05044580707c060344202d4000513500290003504c00e010000120307013070800c0c00c08014443c4081c3c032440c024803000d00341615015100c94907542d0382c1e54000e26a41004000000d00c41c031500c4c0c090b0410b2003001c1d0020380c40c0c22040c1d11810108402c0400580c042d9001c504944506a00074543c3d0340000c042d080003840f94101b40011204081310454505d4041040d284510441d03a000f1300562800c416280c151000e4080d40031441003501c0244015100d440d01100041e41801c0f10311002b8482e1894005000406403105a0510500c01c1c0c82c000d10007480400316425821b06000c003218403140c1c80d0705001c100248 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 80646791 1250 80645541 80645581
    0x6050a0b0906070b0c04030209070e10050f160c0f06110d050c0f0316060507050c0a120309061d1504030903031805040903030f050106020313030b040804030b161808060f 74
    0x1300380c10401404203408000b4009807402618000c3c4180c0e141c12042e03902d2802404000d602c0030042d0345000300c16218000400c44000d000843c9420440c900c0e100b50008a680481101c1200c00e6400611070244640c0d00178000300a18500805813850316068a616000c084c4002000c00400040c444e22544040140d810301600380401c40341e581500328030301c0088000c181c408840d55403c1c00b000c00d480700c0c07080e010349981025a2029080c0a4801d41e160741003c4106280301d81410745a81a00b004103519215500c10380850000c983c0c03401d81030840307940c245034020704480d4880300c070b490510010a50002201d010b41e80d2609002e40100c54884400a1600003540807a62290400007454205130341904011103600ca04401845a80d807a020281d8580c050b54034010901010210b0400116140b015800d0300b09000c0c00340315203040d8894a41a00c00303074003150344030100c80c0e640768540030840d071042c1c1080d00124000e08130368041d1306100c0080e44030500039140014a043c2e400c049080d0f00c000040c020504 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 80648041 1250 80646791 80646803
    0x804030203030d0903120c1707020106050a170c01030603080d050c1c020a020607020304120602030c070501020c0d020c040203010311120c0402270405090606100e090f040209060406050a0b090607 85
    0x3c01c900c3c0b0000004e0101e03032008400080100381030316a4040300c1c2c01410221480343c2c4440d1802d0004541d4245240b000071b041608640d03c4180c00980c80e11410001009020b1014070300ca05008a00741452800211100507030406140440c00c10200300d1a1064440c1c0c0d10f10100003152030303100e800b0079035032134054140c800b4030314100c6421075005420f840d401000307500e186400340d0b501a52508402c3c1d0b00c2e40114843c18031041541c10040e80050340c41e5006503401110640441d003842c0c600e494079400c98000b420b8800c1c3ca54044140c02140640400c10500382c40011a015483c542c10b40d07480741d030461a05032009010380c0101e000900c03083c01c107000c0600b4043c0054011521203002e0a03500308606010a25003200090014498510b400c150180b00e2144907100c1c02440e02d901c030700040c81017100d2512140801c1050010191405695103210180511345004c5100750380d0034603004001300a0300c060030183c0300c0e40c50f06030104142d07100c1c51051001ca440003030b01940c49001c4000810382501c10550000d00c2 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 80649291 1250 80648041 80648047
    0x30314010f080c03060f06060d150303050c060c04080c01050c03070f06020406270326030718120b06011206050411030403030b030307170306150c0d0210140112080403020303 76
    0x910101d1807141c9080710000c608450300c880ba0310b4180342c1c44131010f5038034262802e22040042d80500f480c1d002499a02141000002d20b402860a80c1c035103018583c000b100040d10002f985460038600700801034205107002c3e040c620301858150803560361084101f0960501c4004036044000f19800d0054815031904581c124051a20504c0c0502c0258080e0049401040300e2414050324070b0744200362500e4083c400c43d00d50b03442c0c0781140c90324000360080d4103002d60714081c8035a040c4031002d221000385006d039546407500c1d0480c40040790700502200c841c0d0000200007008420f420003050b03403201c04503040482800c00706501c200144403c13001d44038541095801909140e200341140294500440c031450280d039080219080c1ca0b41016103034803610001504800c222070b100304074440d10f0401140c11074401001d242d8450721500101003d03800c40c20741260140c001600201409405101c020407500c40c1d98000c006100108850714450401030140907400c038691191802000000011200515001404c50351 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 80650541 1250 80649291 80649299
    0x1b0a080718090804051915020102040617060f130b030d110a060509030409180210080103020310022203030206090d0906090b03040212010207150e010b090402063901140702060c0703031401 82
    0x1060480b42c0c03040d0047c0c01d000120303003c0743e18410701c03d5a00391106036480c0010a4519075240c0d00e00580509002e0340810741e85402081a900d00c00b4100c0149000b41000c500c501045c000c040c10020345105410030300c40b8100c00e00003401c83c040b69103400305500510006017a12101c2003070346503000329000001d0f9a441c2007540500f03100490f20b462502d9200700c4601d41819130890044030040c000b840007d400d54040d40d14030300c0030401c7d42c02070201c8681900410002c89410482102030242d10391040d40942c2204080c802c1e009024812a01d6515144c00d02c2600a8540031004040c4032480c40342d01524070340030002c6011940c800d0392114000da400002503440d4852401d15078458651241c541d04143d00c3c040f0070302e0044406020342c00e45410010800341e203c0d0340d503400748401e81d884000ca28100759613009124014451030921500c02e01504d400180e00356205403ca039084460080329112804460002c01021300d600065680c2d10042c0c0240d955102c690524055000c2d01c954601d0036000054500041 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 80651791 1250 80650541 80650579
    0x9040507181701150b0712171303020c0d02030c040b130501090e07080705010203091017010f051207030b160c05030408010b010e0402090a0902030c04081b0a08071809080405 76
    0x80702c1c1048201c001c00042c81c0b210741c0900c604580c4c3c8030316959160b05110110200740f013408403041e00c400b41e041140240804014950502600711540b0014505852920003410341c10014005d4200b41510402609a66500003a56510014000d188699110281190300d41c940c0b42490003000d42c6000d0034072075541c40310141d501519500031a43c200c0e00c65101c00090b00c0c0d00c000740b400c0803941d06802642c5422503100c188084c058064210906001c03179001e05000c44100080d215000340100d0304001c0d09030b4100002c01c0300c1200c0c0140646a140d00c486001c1c00402c64181c462a000003040111000f0380799200d009542030898214064024040401c0005950748107410417500c20300240c0e40e110f610100d510402040340a41b40c0c1d0706401c1002d0100a1042001c55401540c00c1131403070003041c0c1031a561303840051400d1700d164025003450a02e10101c444509000701404040c24903c03016064160610707118044003484804800d580544503004002446501000c03180a040c1c080e00b590810082d0280c24 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 80653041 1250 80651791 80651819
    0x50f0f03100c11070303080c031803120417090303040b07050c06120103020f090f13020103020f04080a02041103060102060c070c030209070503040b0c1c091e0b04050c060f0904050718 80
    0x102040803403a01080f010340100754181a29850740310b004040c2c8454804000641000b402c010004552038100d17880c904041003d0001c1c210450140c140c145403608e40500c040728a03010f1841a021300384120165584c1c0402910141d44082d4203294480400781051860078004204098101500140c0040151a2101028166030003611640c0240c03500364107008105030229041d40c0c420f02440301090904401200d04070300d150051501500741440001c00c2003060340903030721299295129018803000c50816018154801d41c411746c10354210b00e05000003075241c0c3e03001407582c9003d150004507039007001b15001e440750245802900021051034000b501410380d50050b1001d03070344401303404001884020381c0012140304031000b854846d021031000e400780d4040c0c02c4001046501c00085102e140c0c4040610002a01d07950085808943e0b5083c2410510f090541c4051494041c4d40208030350343c0b06500510448840307110582d400a030343e9403154030803180c0031108213969640218002c00014200111190 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 80654291 1250 80653041 80653061
    0xf090609061b0106080d0507110109090608151006170408070605010605030703051023031213061106010602070b03090f0604050105090d0c0b060103200a120c08060901050f0f0310 78
    0x2c220303107a03c82e08182d648140f006d200500054080082c440040e40020900f0a65601814090301e5030791124103040a44000e50020180342c7d024074a01c2001d0041d2418807030700702080b0306072004842c0c1000c400404501c203040c0c2c0c03150000d01e40c3d0049420001c80008603a01c0360f412242c10400e55842c0c0b00020807560040c2d880b40002801d20700850580400d03116a41c0c115040e10206000282c854085500701c40f031820000740d810301071110064401030b01d4500500196144c4c08140c009a070410700f01501c3c0107a80784c80424903520580041c4a410b80000713191098448002505441c0e944d505200e9240c11400a00704486024107400d020402c0015085213015900e114150342c3d0906840764200d0f40003041c0d4070040c0031041942e000c20300c0c0d54080e600840c100c41500c40b11090b01c2c0b8100c901d00b8a65400313042000d00141455101422403901e500c50300203c1c420b0b80c074146105041102c005101803106001c0c5c18032414840030307030000c9a138030320403010010074001d8241e51041d00c01f4083c4c6001000f194403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 80655541 1250 80654291 80654293
    0x3030f020f0114040c050111100b180108010b091b0406031d0a06141b090904050102130e01030201080a18030e0102031c060302090115120b0d080301090203041104110f090609061b 78
    0x3156640c01100521084a150802405440034003001027000e001d1581c0c410350400114036052420000951450b406840000000709414151005010310b032540280400301a01c0c03c80c80c8401c01602d40d01c100c03030456080e8640071490401e409070001c40010782155a40d0b992107140b000c1005c120003500304154041500114100c0da41d03400000303144640294209004005003000001c90924041d0b0b01650414000c100060422600b0a485005072596800088001c0e04000c0104115a408104581d009440a400348083c2440c00c1c0c8548281244242c000c090000241810700c4591081043e1001451017800350301c04170582014050003040c403400309900030036404001091945080c00d017403c03c207000e580c80c00d0100d206050404020211004055445040c980341100800c070345a014501900c0340000c0180e581c01d042c0703410800c48107900805800380741012449800c49040e4401c0e600123261030f8030190750b200e211340d000403014881d02074107540c4210085aa51404208155400200b000242c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 80656791 1250 80655541 80655563
    0x3082805070e190501020d0c0c050913050f19111801140109050414060d060b0607080d0f060b1b0c0a031209061404050d0201020c0405092103010e0103030f020f011404 73
    0x611150a00d00f804e00640340540c0c04041c203807204503c03406080b5106400364a210070070584a000044c1d840806030303515514058904151411302400303000b2180350956410050194a1048919842854060030043d108400781c0400d01c4a507282e0450300c00030329011040ca0560366840701000d1100071501e1444ca40005d28407940800c05013040e1241a1800c50020480c0c011a55600100400c2103001c41044590a846460150541e220940680701440c40380b40343e00d40b51654805800c040315038031380c440405141010001c00c213451441044402c149a016151410380d04100c1085103410041a00140c100d8060030000050160343c0a088426008680da003160fa1903403050100c546a0600d80510080d05080104114a20700403521229161060050b203094014001c00502244c2040301c90070744981000c0e2041306001d18404501c040c0002e03030341e40b050565042c2803048010006c140002030078489160106070925008018010043d00e041d4000d00060981c210901003c840a68049864400c08 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 80658041 1250 80656791 80656819
    0x11b15051e040c0b0307020a051518062a0c07080f0f06070509130b040c1205010603060303020c040b0103090b0103030207060207090b010203070605072015070c03082805070e 76
    0x640481d9000d076801100d840440ea0900d100f6025a52001d4148400d6125070178907480081c00c140003c0c00003404407901c0010702d02d405c412091441e010f6000d8000c69030091400c10100b407403180c8480030070745014031100d5004051103050006c42c4c410401503038442e00c180f6600003802c00c030001c1d02e20340d140d03940000e5a01c010080b000c0305070343c4c0c0720503100b941c0418000d102c4200c3c07a00b405001c003900040c0000010454080c0d060200b003c0b5441c00c541c0c0c1c1d0000d04015000c8921403414050640180001e00c0d00304806803070354a00a40b16041d00c554144034030b88440000b0103981c4203410941c2c683d500103051140d0b03943c0d2854060350b5500240b14040160107264400105004288510034071500117802462400e401d079600c410080a00900401c00c1c0460703420140340c4c45200b44c0e050b0b14001c4103135005200016900f84051040c420080240d03080212131098000041e5014481c1500080c03000001c0d03010140303181301030417408214000d48400c40c2c540001c200c44183d0002c41c0420454060710201645010 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 80659291 1250 80658041 80658091
    0xc010e010b04050f0f061f0f110c0f06030c04030503030c070302060108010513080304030215010602010605010908010c0e06030a020f0f0301090c02070305030f0d06050d03050c0d050304020f011b1505 87
    0x1c4481e280d01081c4c403400170700c07400903401c0703001c1d405a03000700250101c001410031030041d030410481c00c0c00040d1400d20021140c58000d0002034150307000344001c0c641482c1150010300c40803a4001d10303034001d407000301c0461a152200300564000c5c40d8070205507600c0b403a000010b811540c202c1070040c1c0c01440760200010b02c255041c803c007402080c5201c3d208506c074100c0e4a403603042c8c0c0d0002e0800c500b11b11555180344448900c2c510400d000c0d086580c00820074034501000100031a0094001c44030b1a40340c50300144500350014018410204161a4180c1b6651120007070030007400349060040c90b001c400100c0324104825500112705a41d122903081044000b40201241e5410b01c03400f0040955004101e200e445d41060b034041d0000303402e02c5a0109100781c40c0d0001c50081c0c05018000c0300803071804a00201010000e03c080034681d0201e1824509618158001a45409008461605014401440003420350141459608590708030380700c2074040c00a01040c0c2c7c000d2004903551201901c1d40340e424211444 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 80660541 1250 80659291 80659301
    0xa0209010e010605030627040c0911030f01050d020a0f0308090a090b09040204050a0b06070507030303061a09060f040321020c370e040b010608070903030804030c060b04020c010e010b04 81
    0x407860303031818110340e071b204180040345800c0784019195021101c0300329404201c04151328400c40c4140c052080841c50003402c0f0003900c5000d6203201d5008000d000304182c98402d440942e0442e2000c071000515a911030002c21b10444903a00f100c0c1d00804c0040020051143c3c80c8010003c183d030a17030b5a0005681d540c9051011258248a945c0d40711040c800400c001d850f10390480c5070400881d500000d1180b00180002c1e030380c1e6101030000c86007900a4102013062681605c0340c1070080c048440c2c5c18242c4121103407188820310030003070458402e40c004600308203104a00c0d02034401070355001174000400070a0090103e44800d02c14003e40051103901d26101484c10044841510502d88018011050031082c001400601526800b100301d503001c14030004a038071201003000d0065000c1c0c454a0880c1d4140203000300800d03001082007040c8407818000704000f82d40056069030054152600b600303060000e19011014206c000325180d80070740040b1b17003001c039804194004d0a485e94088002c02101c4008000c0c40142d907 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 80661791 1250 80660541 80660549
    0x312050304020102060a0911040606030504050c0307060c1202011e02090f190911070f0803010e0c030c22150f180305070b0309030c030a0804021306080d0e0607060c020a0209010e01 79
    0x42c00001c0030406141c0d02e9040607d00500c5a008200500c01c01e4000c1402c86e40c250340640c00003502e880500c02845010300002c01c0880c002d4019040041c103081014100402c622801070041150702c0014464034400c0d44900d58101c0c01d01c0144000000c50310040c0003942006003003034454004a02a6507041c40c0140e81031010180b031100d40f110261620700c0c0c4000030305c0c000c050407109800800a10300040c00945c054180c1501c605413450316541060489070100340010042c1c01019410002d00c1070044070303074055880d072108203802155400400400d0b80301c074680c1d0341e12410f89003540c580007441450701300480814681a0381d4400b844036002c0d42c9120003001e441d02c809000b6411901d400d008000005e0003c0d9845034080007142e01c3c00c8112070865107558000600d000c0005c2e4988148011441c1401c0302801003808040e05109003414001c1040e10707000c800480109102c507200b280340c07030f5484000564044903042802003080c070341c000038041c0d100d202000040340701e13401010010503180322804031181a5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 80663041 1250 80661791 80661793
    0xc0726010b0901061202071205030115110a02040903210c110a021507080f0c0c180f240924030a081e0d050406090b060307080a110a080709060312050304020102 70
    0x56403030800182c59105d415a0403201140d0200002d8000c105000f150308102d20304e41d80c40340d03500d626113410048002084d14218003003024920580c9650940054000d441c6901128000340c48441071074160741099503400d9001140f08600c015400341c0c4150b6003c100120717066100c0c07040543c1c4c005811600d540308003400035800101c490395085c017801802c3c042c140c01c41c4684002c600d08003249041e0030558000800b04075455000941d41c500b9420320500c1180c0e0514680a840400e0810b0844e0a47d1038100514107086005002070306050704549101400210a01404141650a064102c4254007290724851f08210501460ad01c0a50a000130350803800e80d0403041c454240100c0c01c000803801505000140c00e02c00091101448218903131090700d0065100350000612a072035841c02c0d104100c40100241d200b508007040030410400d01003040340f405c0e80d2000b80040004100800143c441010342c21034032681c0300d044801b15907400603600c442c003960b004100c22041000601e004035010f00c0120303002401 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 80664291 1250 80663041 80663059
    0x6011d0102060a020307050f040314070b070b040b0c0f1201090c090305030a050c010b0a12060f05062209050d020d14030103033509071806050108070c0501020c0726010b 74
    0x40803090344d0140d5041949450070b2032410480c01780390000d540042d001940c000a244040041d619010002d0500402114072150300745520f58455200030500100054000c0d00503000083e20034110f042266500c0c078001d0000b645500f40c003214244154000d02455052a141412407124207016546020860303a03c100114a0a8540d810032201c90b008403010481035900d41110f000e50380e6510007801c1c041e00440e2810b2065134031a04150041d02c09450070310019030315090510038280c40d0001c0b082542102c0401400101080e402c0040c020400044081c080d4040d10300d0b0610380b03d50100d0102c0490115642d8450303000450b000700340c1d0510081c0300c014042840d0030400940d600c0c40150742c0340800d01a400e90300410b58895181d50541d034003240c20920640010708180154032075041640f004205400041041d5810040041c0100c20050b01c10380a004c0344542c18010408250100c4980d003c50100f900d1400c6c0d0303a45000541c508094030341c2020450449605506407505200709005c0320360003415140 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 80665541 1250 80664291 80664301
    0x10b06091f110d031b0804021e011206080610090c080f0c130b0d0e0316020402030c0c15010303030b0303030f04030e0328031803050a03050d0e0a030806011d010206 72
    0x140251200c481400e02c085122101e5102c1e1080c041d030710380c10120751008140b174845504880d82041842c03d140003803109400c03d02c030240e140c810042c00c0403820350380304940032142100140d80f00015040e100e01d1107400e12001207044d40011904030701030039801d900c0e80b44440d241c3c000310b030030344402c14040000107801da40040c0300010b51aa0980d00000c2100101c0d00d09000c2e03101580c00242250058114400001812071028440b0700c40c0e900001e80c000091800c1040c1c00d030300c880803070408100c0a403080c1e8020020503907407a82d2404a94100780900100c07401102c0b81e020005010070240f0058020a18114802e8402d003004001c480c4501100e2a0480f40d82c1d0b0380d50303000e45214282c0c04029425104201c544c40320390000307805100f1030500c040c3c9450011429403800514990740e0382e120440203060b03540c040000400006642c0400742d8127090141d16038040c0001e03140201680b1f46c0f070b400c1390b105d107c3c000b02c00e051300001d0380360054400383d03105e0306c011000800f91200c0700062a0071030f00685c00140020 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 80666791 1250 80665541 80665579
    0xb03150409020a090213030308090a03080a020a0e060a080103120c051e0c040903030506090c041a030603010f02030420040c050d09020406030b01060f0801062f0a1b0503010b0609 78
    0xa120305100410310b410f49a15601d10300c01302d03041103600142042c26610305005142d0003440305031b0300c03000b1340b00202280440d9035001059201c0c0645600c0000b900030030800c1126000301200b6145207809003040d511000c204800410510080c441507400243c010703611a207880c0f003003404190080e0401c009003100b8141d00d820300e001c8442c980107440a03005030124041e033382e9900e002c0d0004c128001e44d00415103040000c00c008200c003020b018401c1088d410001046a0628036650064090803901301c152240e40c0c11010a0141c10009521040c4a20010401040101041035083c000c0401c4400403414902581840111942520a000400c10501142d120203c6035000440c0c4144082c20206e0250791300d81e65040c07614000e820410104030b00404101c0d8265100c1e4a150040c007003450008a2169110340c5800c0024455141c80501820502d0500d83e14400f0052a040141e10003080796641400d042c0100f0200542c0c00b0b194400c0d420102819203616000040d81c1c61400010200301c1060681d58403c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 80668041 1250 80666791 80666801
    0x50a050f0a17010903020c0f01021903020f06040b0f060a0308030a020f0408030f09030f06130209041b0602011b020102030c121308030103081305030d0801150302130803130b031504 79
    0x2141e20520642002c81e0001507501c5110030301d0140303000850030030014030307000e070038106004c014a004640c0500d1100603a030b030000c0e01c1007122580d154188002446824201d0070004001e0306c0e24051304c40d02d010311082186001c281446200c03036012910490b1240420000104040d21024103040024070100d4480c03201035000f0500f0070002a541403a0940d2511003170308503002a8500a584403000c6441006401c081c402200b0004540018119620308026011700c500300c0064068001c6505100042c00c000c81c821011403d100c2c0900b8101000342c0c1c4100c0203002e0800e0900303603803e0000c0310744c0b600307071644c014029a4001c042c180b03496800d010000000c020115070040421020940c60750540c40400e00c07445c0218040d500038107007103543c0d00340d150342c0f10340c007440b00d500460082d030ac1507540c840745c15480b02150341034809030f00c2c101c03400100703040d4110042c3c000c44a040702c03e0407014800140741e0000100400301d034030b4515070049156545600003403d600048611080c45080c00300d0201c0f5510346a400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 80669291 1250 80668041 80668069
    0x120703020c190b01140a031e0602220f05030a0b0105060a17040f030311070209070807022805010e060903070f0c09060e040203060609091018020d030206070f020304050a05 75
    0x101e41900703012050500b10740016990548003100e0400c0140040c0c03400a555542140003036a142418030306e560307074141d1410780c260a503100d200701c92054201001071580468181e480390040c1040c641e801842c1c052603502240c400d403012148083c3e0000740c64140454090f070001e03000002c100c1d140c0e1a00050001c5a4400d0000700c040201713a40031000185028403909000d1400381c0d00b654031800c010701d0003400301c0e05e40d014100c1c490360050000e14010b03510703007140c0c65000201d45402d0f8100d4843d030034140d18186448003031168070502d11100c6c80c220011201c0d1101c9080c0550028001c40c41400d404a0b10b442040d1481843c87d0420807041d0041004012100040c038812203040440c2c5686036021000c503800740d00085800040d641c1400309511b01000760a4202504a48080c0b090912489055903410001e682e048450b441d8005401102986044600c41d5600a080302e09582e02030b290094940d20121840c0c40881d0701c0c0c6249542e203a10020a44058078000b130070748015607050604201110741400310b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 80670541 1250 80669291 80669293
    0x1d0a140c090913060501030b0a0630030e0402030a0906050604020403030c081303051504050d110607110c030307140601060801030203030901030e010f09080901030e193017010b120703020c 82
    0x24400e40013403c42e10030b242c001d6005054800050404e419448107440300b0794030144554264410020601c41d915040d40030348190a10b22140c0a41146400d07101710040c6a80ea5078000d1011080100f0304210350025002d0724072582c01040b207603803150104412130107a400b0160000f62038403030050011301654001c00b00c52101105076180a91381e03594051400c42070030003140c4000c611600707100820408100c484503c68031805c0503048007140034592941c59100910f0b20042080b00c0f10440301d0680e00388980030600e60050292580e9061038140104002c0d500c01c0c18002d50711400d4000039689108002c02d83c16281c0c014007451510040400442c081d14551850341c00c25540d401c00c0603070b00d890520500303010741c3c80f0b88447e0303842c0c65480001404603000369808070002e801c00e1030101d1900208884c03151040b640211406a00102042d0100032a2041071b05681d0b1500780389500300310390f0f80101300180d030780710700c24102c400356070702e8246401060041c0780010740103012850106100d04d01a40243c40d40000d110 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 80671791 1250 80670541 80670571
    0x515070b010602010c0801150e01030506130207080315120705040b040e1605100315120807150605040f02040b0a0809010b10030e0601050d020607080d061d0a140c0909 73
    0x929405200c220070381c001d00c0540e541e004028003c030b411401c07640c010601c016210741d045006040103072070030310505c2d0300e281050380c2e542c00580203a440b0389100000000310705045466140134904004a540b0940340d451550364200312911203032030000701d003190000034a8050040345103400144005045514184d542c415118a07100b0070309502004550b41c40c0c0c1d90502e104c00441d10303040500061000d00740c565010107082c400c01c0c40008007000f082d20201c0d103141e0a64000c80c5c3d268202940709004070080104070340c1000e0705460010352541c11407401d50324105c40801200300c1480c0450224071480c82403d000355414083c2144260088000c1e0b07510075030031800130440000d4040081c042519072140d100100f41e4601000407103010400c1094003602e0140d940010070340007900002c11500551000030700902c40010b0781002c01e01143c000130b0081000e0410038050f1080b2800c80440c000040383c04040349890016036280c101103980415010703030090300750f0f07900d4103101d441481000300f001040e8080e418099 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 80673041 1250 80671791 80671793
    0xc0c03120708070309032411030907030305072603041202070f0b090f2107120506040f0516030c03050613110f04061214060117030f1b010603050706030b060c07051507 73
    0x40d11011007410300d554010140c561451b0041d8200c8010480408d0901020310400c08011000140602503a0700b50802c96203e140c50701e090401c112034406a0851041e0000201b03041c2c140400196000e06c0c400e40d0884000c1020500490380d0b0000d501c545207414560040170046241e040d4028081c00c0d13005080941d5034420780d008146112020114140700c07030700e500c0c4218401c1c4814000d540142c0540140124060350541b0f84694841d0f000d80090280e04401190008000701003001510f80825480340160340342d560300780300e20194170910044e140c3c6d000e910000f484500803140c401248a50048809070080307030480500031014460301d1851b400c40e680d24000725140300e0003240c49401520640860421064008005060031010307405101c110b0006c4094030000000841a1072075030050407e070640700c0d030f00b4040026954880750510000d0b94038044000c820f100021405106a4071641c0302448050014000d0006a1165402082660708002001d0140345440b80c2851180e42240c4805030500c03400b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 80674291 1250 80673041 80673053
    0x905060403021b0303040506041a1204030e0103050a0513060c0207030501110414010504080a02040f140a0f0c05040f09050403021509150a09050c0411041502030c0c0312070807030903 80
    0x42610103078003503849240080141c07000740001a404240030f42c051402d040c6007074045021400b40780142074100101808011060008105492503581d0b003e01190490603d0b00f00038000300d2044818034002420200080c10083d480d008090191b02e40e400418202034072910382c0001014103400c54001c60048040c00070102e002405100304002414000320ba80e185408003015501c130100f82024140308061100b0080800040b501005903034054030045a44200c0f484800c1c010510750611201d04140c2d0b109008855a0340c0d0702c15540c2c1c860b0410100588180c2c07202c02c1d20103000b1845400e0106d0744030201444110115040580c00610a004070781d000e820120000007051012034658489500404941c0d4110740340c0d441498128240c07030710030802c9840742c0e1a09034540ba0f100d40c0903402175860303001ca020a0110041210000d001542d040b450b0f99003041002901c951100c2c0c0542c2c590300c520002c56006180c00300b00d02160b1306951400030b140840e680e42e10b055907002540e0517014040503040000102d40 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 80675541 1250 80674291 80674303
    0xc02010e2101022206080a0207080f04091a0f0604091e02032e0b0909090703120c0501150b0703181802090907080c0a050c0c1201151505040b030402040905 68
    0x8800c4009030300c491418603442d484000c01c107990181000c030345404010003900710901b1500205041d00c056990403403400d1500c19440f40c90210f003a02007000800152020869001207000c069110210140b1110141000300d040e9131103640703d80c4038204000c1002100034551058078220f4030404007e0794500c1c00304400d81283c00480303a030b2403500004139042038400c0201c41c03519201040d40da16100018100403e500c103601070681d419000700450307030100d0121902000500e00a581c0040c008498007a8810001c100700400b1104407120760800c01145140d0280d00c10344400e44140c0d01d411802c0805984045603642000507842d0070544403040081100c409040600c01010004680542c1d1400001c00340000f0040080c08103082000718818404a03012200c2210008285441c0250310f0780a502c3e6110309203010303a5030655000c80340d00c61244584406400a2059040c9070b074116070041d5403030008446242c0400c000c03078009101000180158414000515003250002d000001d99020303d13565146000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 80676791 1250 80675541 80675599
    0x4120e03071e0303140c12220f090e0604020d08090a1a0417030703020a0204020a05042301030501080d230c0f07050406050a0608010e150a061106060409030c02010e 72
    0x2002d002014414035030070040c0700071345031150b00d421071034944404449600ca072003a003e154280c110000340109580821604543c26214100f0301494140d42d994800d8031607003081c840c22480320304043c542a1072007008103045100307540180c05041ca402c4180d070303902103540c000c24040e6400001540c0100f8402000419112551507100c00203070f41d02d007000c01901c00c0000d0b0764150a4039a108000400c006907002c0b030740312030403035054902503225009004141c2d02070041d40c01040c6140c403901c41c4080c1c8400c40300c80001445000f03882c108102c1e6202c001081d20b0b0301d4540500c070046402c03440070040e240706c051007030140914903c4905040240d806040b03414218040b1042c0c4066011000074401442c15110f14070040c14102c41105205d407420b900541f01b46014840c00d2031440c5911300043d014507000743ca0f440041802001c0c90045c9440b0380d0090046950350740080071500c607040c00203259042c0f610480304020740640354070140310f8450780110340d6403510703002039508a56100700300043c81c1444403114000e9 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 80678041 1250 80676791 80676839
    0x60103030c050105060d02220621060b01020a1e0501020904020a020a060b0306070c11040b030f0d12060e06100309290a060303090519051005030117010504120e0307 72
    0x40d01c60340c10402d094400140c01e151050f4040c5035488010303a20003120700c045e8146040c01e40c10501110308420020003065000c00c08640300c0840144020405000d13202c001881041b0400184600d000126900da4441c80020b00481d900213404107440503000204812521850000d07113400803440128081c2d0f00040002c0780580c1c06840e6031802c000d1240039101c415802600200381525105a0003007807032002c0c400c060000d0076072a18200c80e0b03440356003128005940150407103002d64070b1340c200c440e541d201c140210301c005901744800c440c5d81c440a0003040c0845009040c2c0d051141c07070300b00400036003403103405029080c140ea0702c21260000b0848065060170340c00030302d000007001b03589207003c48240c00b0041084803a0340c54002c040c80000d400c5084003044e00e4041e9a0140c030548000d1312a2412140c503080240d0020303482c52083d92316a4800000d6040e42c014041c51091400c0c840012402d03030b0b4050b1070060a1041500c04d500c1e5103072168042658010300102210f03121540c690400201ca90711103002d1000c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 80679291 1250 80678041 80678057
    0x70f080c100b030c0301050403120b01110a080703080702060403050403080c010b0904060e100b1f0908120a0e31021204060e0105061206070e01090801020a020709061e03150e06010303 80
    0x782d46028800609411801d600034086031400b0780d002021500d1402041340401d640c1d4121680503445030384002030001e001d004594010380c1c98144045613400402c400ca0004400f02d000a01080c40820709038017850b03054407003d0800e0308580d181002a04004010700c1c042d074ac1e49908403550358032006424011030080800040c0c1903113441c0801e090120312109195041e0420310352641544540801079000c4414410000c0c0000044c030301100c8842503a40007000e24440c8400020000c3d00b220020030a802c0c141d00d50400813000b40d41802000510120460050f04070254101c0d80d200c10314001d4035440100500c0145400417484004d08c06120582d4103483c0e03c0c0e130328190480c0b400024411250080d01c221802e030900c21145692030380d5041c00030400f20400c1003021065110b82d02400340000a0200180295107540c1d08890095441e0031911880c4015410b1800000d082580f000300c803100b03003c003004a0402d4174156107680c90003c260b00c1045208a90382c40e503401c0e1821040c030000340a54401c0d0307a5011 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 80680541 1250 80679291 80679311
    0x1403030a0e0c0a1206020c01020c060411010f0f120b150a09080d14030a0b010e0604090b01093812040f11060310060309060b03010501080304030323070f080c10 70
    0x49000b1603402850b00036211450280314160192202c002800d41c03110000d0307501d006c200d41041c0640200710b0a151640b103a2030034802001562008001e560000b80da908641c1e003000380c41219200c2501c090040441d2110550407058070340c40d00144501c1c40d0261aa00c00302c402503812408076400038540754002000041c040c031850000340418403602e8210700e8810782406195600201c07030320026000303001c400ea40e440350012a0b4003070030760104414401007404c0c0d211b9a4440030040030303000d0183e80074001403056030003190791600409040b142c04450441a059000c1c82d440c5596001c401038041c1118401c00e200300146104601e12451040b40704105034440040f80e450500d1600c1034207440544a40401d0040108101031411814200c0749075240215422455052804c010006444019055401c060010802800c0000140b00301ca10035900c2c0c411001c1c4222100216558010400b00c01031010400080894203031100d901000e402613100342c0c81d006545034211300c3c00e00010240c400e106d4854800745 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 80681791 1250 80680541 80680543
    0xc17040f1205190606030f060207031e02070909020d0b0702030a12060e070309030c050a050c150c0c060a05040815060a06020c0907050c0703170706060602071d041403030a0e 76
    0x200050124001105003212960b036010345515803021040d0b00c1514000e030682c140512a0001c200942c2c012800405249560402001075849228141c0200b00d0318024090ba440007200b0300a28080b0542c040d050303070390410b058100544140e5400361703809800d03280b2150101d60100c100502400040c0c00965580100303000c003178089070840030744d600d80b2840d00d80c04000c0f26044002507a440380e031620300000e9013046460196103801d04803402925903c5014030403400c1010018480c001907100711462055807030390940d245d855110300c0382c0e0b640094000007160724442c100000540485c11003400c1c12400c15403945042032030621110241011034039000180006810300c464000064400e0784064420390400340e0114a81c0c41025204208100c0001041020007805101c03201c00340da40410300310b2402c100c40300d007c81117401c1941c4c191009484c0100c0010385500006d9040f04039000341c80c01d000c03080c05040b10b00f03910000080c020340301d00c03082c58900e03800801c6c2880114070031a2914400500f041c41c0625035 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 80683041 1250 80681791 80681819
    0xf03010b1302030612031c3801020106090207080d09240501030308070f02061906050d060b040f0612030809030712020303090d030606121a0d030c0506072d0c1704 71
    0x4640550010004000c001e03c010b502e07107c1c44c3d02084030104d604500d51901404c018501007a280003100031102c501108055000014123400c0240d0081c40090340b0340380417030228070401400130006807040020610329581d13078001c800d01358001c40b010251039245460298041155038050f2244607035a030014000c243c1c00c0b03407490307810030181e18140c00e64036500b110180d034917500585800c0340c000601c4140911500e564001101901c07018041c0141d11209191400142504411451099041450b84440d0120714840c400889598101e5640c602d8201e032800c2d595a440a01240e2003400100f1030b40000c161901c80400000184e03500941d524035100e0a201d00f01042c03406c6480806042180c10804103500a40031620800035601c00921212016030000405901a079034541100724408500c040c180c20150084005d8002c00c191945075503848421500c100c02e01440740ca044240740c08001200030920041a160b01c2c1c9810000c600d00e007581c46009100502c078032204a1903c000500380064051b603800 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 80684291 1250 80683041 80683069
    0x9070602060a020a0e04050613111c0902061c020705011505040c0f0815010c0506090f100506131a1509010e0f060406030905030f04030c03020405010605030609060f03010b13020306 79
    0x70460400a02d0000207046181008800e48200d440702d020926030340e903004d0300b27150700c1c000d0030810010506072540103400381c0c1103082c00d0b07070701000d00c0d400418a4815a02516144a030700808140c58400d100f899024500294004519510350138011800050310910034908043d040f5646d2140e40341c80d141c10802520622490b0070100004180c800151542000310903421801c1c4e040283d408c010340717000484182c06911400340840c4030300e0052140f00540400d50075001c00e800402e840c414400f145010058403400c2e81c01c184c10074001c64002000c400558000f10f65000c000101200e080000b20028038481141c0700000070b98440041d00304880e42c1c21603e801020601a03d216202d01c26620000d0024002c41c8a10300505031110185004c02c0380034821940202c1c04000903a07100c640300d0414098414042c00100d01582ca0400080741c45400b40d41503d10512000300018030b9581c445083c032405945441060f90990348070f805406140e52141c05484000c6c40b0750000507100c1ca03120007007082004010345 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 80685541 1250 80684291 80684311
    0x60903020f062a1002030a0c260105010c0609050303041203050a0b03030f03040f0f030f09061d01030f0e0d17010501030209010507060207020114030405011401050a050d170906030907060206 83
    0x220342e085880f50f4440c03c54003007403007030000085000082a50604407030721400440c0c0303840041000421003681c0e005e41940700a0380e40d407054281c18078001804034000c1100450305002c0e2080100f01c950700c00c4d40c042440c20300c603034000b1446080c00d584403407540c0c1080c0d504a486049401200c41217941c14410740303902c15401241801a0382e040030100e52684501100480010000030005050003000f44045404940c8407461026070030260600074140604040c03c040059035000c800130711544640b15003031269100140c2952661a800015402040100d940303030a650745580e4000c0046c1d2003403151034002c14558840c0c408420b584103c0c59040c6505030000c90515205000403007550b6031010959122552200c001a950030650005030b030f00d078090f400d4a07909144000108010440e041d0000e2104611141c803401250b40c80303000308a818049801016041081110100b002c50204c1003030030401c40045005038540507242000c0744070740d4021201015168031004007041101e40c10403900c1d0780050503071 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 80686791 1250 80685541 80685547
    0x1804030905060f0d1a0f011202130803180a051503070c080a0c0203070503010204030b0105010c0c0504060617070c080d021804020406091a040609052101240e0906010902030718060903020f06 83
    0x440040c000340c0c06e0030311140c10000c0e50400d54000c03011641c11541d03034004200c00c00060a58407443c25580f03a1144000c1407240015508601081c10405003ca05440c4014032101ca80000240d9980507608010103050401c0785003550900403600c504010f04c4800100d5031111009051801494a4030304650701a5001e6881000108086500b0fa4146070642e4400d2905c0341d8000c0090034011600c41182c2c01041d44189044e9001030103030380020028040030f14400859006c0d0b6034517070040d903011441880c060314070803041011000c0d482c556030080c26029200388400c0fa0070503903200818100e030090303041a0701055082d00103001c00491001250098501c0032001c0380f41c035080080007400d621280c40340901514540c011580c03004009000c645054400c0c1c070080108000740310304070724110701008030003d002200751004134070702d05030f4455a8410507101006000300d92911136154001c2d400140325400300000018803100ea044032018601c01801c49a40303002c286802d50042080740031007442840d204400c10 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 80688041 1250 80686791 80686841
    0x240503090c04020c07080715031107020a141309080c07081207060b040906051e0109060e1f051c0302010b0103020a0f0c02150d061403010504021804030905060f0d 71
    0x10041104036007a1405a20b130081d0500c50791804180360802d00c12806548404110804610150b042a0380c03039613003e000c2040a010305000d5807248240181d04140c190714140b01d4400403104220124a000c1c0c6452020500310701c20004460030b590f000c0b50060340000b40314104000c208240800781103103c004d04440b0f0340c50052155280314030f050041095480d21500070040e615903210300310298020605100600d0f2105a01c40c207485405007002c81802210700200710003000c1d10581c3e080d04c52010566010380c4454403000b240d107014110f80e140302c3c40c0788017000c50148c4543c00c881c1c00481410903000b034100014500642950320741e020050405105006003010158000c0407120440058245003807050418008503402c40c640c1d007800c901d84200080c412888a046521400444004030031080c0821000d40415007030307a5003510069401244002c000074100564a0041d03006407003801d00708031060f500c0f00441c0064101d0b1a03440088000410840381c8040c1600911120456903000d9500e002a1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 80689291 1250 80688041 80688043
    0x170705100f0903030c08040b0c10060e0c070f020a05060705030307090e070f080709080613050c0f0d1217040b150d150e0102040801060f180207020904030c020105070c24050309 77
    0xb4500c00a4100b1030384c15071900510040c401102c018100c219201c0d6a9095000402a0b4403a054105110990b1911400090b07082e0303100b500c2800b9128651881d031500702c290f02c1d05103486054a00a0b680480e5424002491f55038410040c1041d030b00c998040e54982c90701c0d5802a10440c210b0f441244142070510801118650000c10082503e240d401c2407025903d0700b2100702d074040040d801c0781c061072140c2c1043c881070010b01d0400d042c050b44544115866051044144207038811114507007908030200c41070703150001d0030044400c142c0c840c4e03900d0041c081036141650340b06c03040c800b40c9007640d88c42104002d0140808052038400c001e0241520915100c2e1160703035400038260042d86940407890b9a41045100b060001e404450040c401d03d4000d12040e9180c5441045c014502d02c180d1400740d040a402a40321400e9000340d41c545900240100b00c941c4c1c66071030640c1c0081c1007078022030400c60308000c117900068282030b800000d81049404100c0080706200011740019000b00e0513000d100050042050b0200 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 80690541 1250 80689291 80689307
    0x80403081303020d0c030509040903080108160e040210050705030f040e0109020307140901093201020601030f060b130f090506060f060915040308070503180612070810170705100f 78
    0x9841d141c428003c07107840c2400c90310340c016003c13809d03441400c04121000b810381c0702d6090b506807100e9030165040341742c0d001003122203c0000d01c1401c60810301c0c1e90003d00545410104040c00144034200b161610200d561042e040d507016a2209000300400300d014095008a180420701414000d0310442c607608040c1c0c409400350050303008005200c2d00010307103200f00380d120341107000040c0b81110002400036282c403015801130381901484450340c04010402140f942c4000ad9140c12030740c12020317800110740e44d91074140103410600d003090340100c5504c510700e1038020980b00341c1080741184003000814216901e045030078950054a200c1c490044004090031540d502d40403560a11400c491a1007c28103911245101d070160390300190100c400401ca4400784100417000b0204160700b0080c1c00801046901000118000d40001c1c41d500c030f5641000032421030040c00d2450f0004090b08010004956504084514158400d8006076a4101704c2d405c0095080040c180032003503080e4100300404080034007004002003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 80691791 1250 80690541 80690563
    0x4020a020312060609030f010219020109150c030213060c1a190f06030219060315030803070e03010e070609031106040b03131106040608041101020a0506060409080408030a08040308130302 82
    0xc2c101c0000c00ca01e076840b002156444640074090711400d0b40c101103010700039000300c10901d07040d40315981c0c0481d8551043c480d20320762683c08136401066000030603405004166101150061550801c00002d842d086022200c2c01480360341d075045000030762072400a8a02d85910f04c03800d4000d90400c14030403030ac00350b40c1681c4c555843e089070000c0c800d0722408129003d40a03a40c4065003040503c04411080c2c118072850b203090f50803e0301d0074404070354652201482c0e04c0c060310001d040581d05001003015a84580d034200d170314032001800800c0c80703040c0c0520395060500703a40c007460100b08a104200104000b03641c0b104c901000444050303041510b071415030f0169220040c07100c05406030ba1701c0280204651071140d203501803030141003903840f581c5407103000e40008400d6800707480b007016906440d1403030344c030001c2e0750f544299100f4040c0100d030b04c403401400090008184100c0760200c040c000072500d5002080500409407899480c4c516a0902d82809050031001800708080441c600c008040480d400090040440d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 80693041 1250 80691791 80691817
    0x6150b091207031703010f0f0312030507170f15060418050402011202040b03180102090d1202070504020c010b0a08030f090f1f0305010503161d04050102071a070e04020a0203 76
    0x120703850005003890340c1c075000101400084420010080c1c0c851000c4e41c140d07010000c00c018400d86031848108500890701c002030982e089059110101407194008a40096450800d84101d4150048003603102900321680c40c5403103110030411200700381d6210f0920848100b51800c1d440c2c2030800307480c140b60590710f1082c07400c01500c1d2000f04085912680e44100c02908092086448a4031004c0c0d070f0207150f006a07282c4841d0500c4a103100601c0d1018421a807103c00014000415098170740d8070f64207095107020044040d401101c500041a840e40d00050a1095115000207001d0b904102044003526082d001081160300c01e024a07001c00e0b12001c111059800300315041e0307000b240b0207000981c0d0300c1c0780c070003002c05501141c07404002c1d07290305034100c03d042c3e540403001d689040388581102e1b040304e0002e212701c9122662040045c080c4400036104244c00900690025151000340d40300d4851034142820038003020801c5100b000903196009550440c505402c031400d40c640640b00360001d507070340140b00c2401c0304 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 80694291 1250 80693041 80693059
    0x10806240c12040915091814030405040c020f0d0801030c0e0c0f0a0203211b09030c0d030207080c01091406030603070512010b040f020403050307031412100306150b09 73
    0x2039182000400b42e82028859016a280d407180c003950040c0508490030070b0985450000030550400074050f031743d20200394071031100d01d032545512404080e46040300045140d01041001107116211070040710008800c60b001080c600354050000e45c540800b0301c42d00c1c8100529080144000380340d01c071451040300d940700340d1201c058880110b07052480c80758200c0340c410b1400001e007003e1400d40210140004542280401600802c20800042c04480480b10002280b980ea04003103c0900369801a02e500007001e012101a0082400465038012000a00340c01592055a0402081d041005044100f407001c0c605040b00910f01036041d103902c21066501ca22400010001805a4408009010040c940209880180c140b440e501c1402000c0540ca00b600860030146034101d0310700e07240205c0b02100c1c0c1c494011842c000301900c003100e01011000001044802c10403004503107000300e0708402e009507022038800d03845910354a402c008580883c8030b009500e030b928100c20003c3c401c8403003c0c4d0f28501419905128 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 80695541 1250 80694291 80694307
    0x1091a031203131403073e0402071704030c0f0602010b060306040b01050d110d1107080406030903090b030421020a0b0105010e040f02030c070203010b0312070305090423040201080624 80
    0x65210b604c9460580148800b04004050001c01c0c05144148042255001040980341040810550341605d5500c071601c11901241c8050506034010031000d401341d6040008001c8204181c40941e01682c030a07110400030100500071644002460401000304e80020080e101c81e903008204035010042680340b045035104500c03190783e40101c04442035003240070010005091619046042034004c030820001003803034650803102c49104402220469a08122080d0405140100440140680100c1201044000c03000012420705090203940124816807565440d5240c1a6410003080001d0010404540c401003180300403600744e40c121415100c080c43c02400010515011401400807801846095840042000b0050301950090007441c1c0c0700310b000303010100c0b4010402d0b80c2c0700d00032001d45042070001c0040c80d000074000c40040200642c068030100d034480100409038001d1b1001d0400303440c17803c403c40806c021581e026805c40e074003103c00c44112502c0024540410314110402901c00c20040d00011350744 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 80696791 1250 80695541 80695553
    0x303040c140406090c08010e13020102070306020a110307050d080f0103020f12030c03130806010501110601270c02010b0103110315060c010906060b190201060509130c05030601091a03120313 83
    0x200144c00220001d000090400d400241204000d205243c00a040c00700403510001540396411079541d0141d0003070022605607141d4900a5104040c0c000601448a48503840180e00f880905689401400a4114102a5003016296080040040030900c0d011001480103035544417015020120036913540d20f03141e59269081c0c2ca94882c0c40c1103002a1b10000c2000d841e0410410715410980e04d07104241c2d11140da0758070055604105420030308246411090052003c040005542887c0c4642c1004c950350b4501c20040e12422113407020f05804c0140d443c0e05680c2e000d960540030380d081c40994030600c075166140c040115030380c03440e0204d82e4520404000402d140b4008003504a200043d0304410104583d940d203101c411201c2d40040c04005070050124420041140184124000c80d00c010342190b1417540d68200030b0308814480c2e0000c95500c480d2020118481d2000c11401c0d02a1400000010350601c8161041c0c0600ea00548402d2003540b04503000d82040011100f500d0b0054003285021142c2c0865103005 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 80698041 1250 80696791 80696801
    0x150309070e01090603140105070206040b0c0d0f060806070e0604120311010203010605040302100905030d0e18070207050a05040504020d03111212060103050702240c090301060b09040e0303040c1404 86
    0x1031140c10064800100e00f8510562003501281d20840101003403030107190f0072030300b80d41d030803501e4401607042100050007003507012500d43d5004034000000e038503008185195208a82c6104046803840380e4414040c407158008006440d00b004031800e2030803508080c100083c509200b28056040507040c004c81c44400c150083e44503c4508600d00025500d0f503031216401400354115102c240d12030300d802007084c030320240a010400161400076020380062846d1850a80300780d20348120300b42e00320b030417002100722080404800b1400345e40d00c2d501500c1110326050802c05260456040603109601d0f100600c001030381d8003040c1c00300d480ea140c140031035807181d0400d07440c1c104410600c07505100c0000180090b801c03400c0c102d54601c21102600c0c20001a00d407550101d81d11400700300c0c80241710b6160444030386103001d42c510542d840074601d40da85140c4189140440d084da6015885803c10b4a0041181e07021441c1a0144041080c0c8441c0107608510705038850820089292050100c00d20f01039080f0161a11541c201c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 80699291 1250 80698041 80698049
    0x9140d150b04290108090304050d030c0b0708010303080106050c030d0c02070509130b0a0908070212010e010608030304062304150603020603040812071b110f090c0418060515030907 79
    0x400c0100102880d126102e0b20321182c00d96520f001119150300007507005510341070150b2141e5005600381030810042c415500b80c562016805e10600f1290000085c01e0811110700c1207000b6a600e200551541c5009403e140f811f800510500c5402d00401d040c01e03130300200391825420b00b4400441ea40c2d406940a80c149001d0303412040d04444820200001c40a1110b46c000119114042514095490303010751030032901c1c0544014280d02d01001900d0240c94030509010345180410000110007107084840d90844150703a0001e400340e080481000107000162050108241c032201c0041414200d1309070074980400c0040000380081d01c401a0060340d4500d03648000061a409001c0359520308144c10015242d8002c148850349007160540083c8005204039108001244070783c4021003088103c0d40c1d0b6013581050959240c0d0403080099002d00310303641d4a8001401002ea40780416901d03410425100724031b0980641101281341481d0040100b601c030310501d0304040080c0c3c2041901d81c0ca034905042d05081041d40 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 80700541 1250 80699291 80699299
    0x20d0f0c140f0601080f0118030c0614010f090f0209090106050a050d06060302071b0605090d060207021503061e031e100c0f03060906050603060d050f0303070201020304020109140d150b 81
    0x401018031100040c0f65060380c00b4101101d1340d2078000441c460030b9410000d050070014411054150000c3c2c00b65420b074a03550300c103000128400e2100381d00b28404072400d900c81000f03005044001c100705400751081581d20134074544158030742100394001c20419a810b10620f410440001108500b42d4460004e503038050300c1c402824007560740ea80c0c0004001c0e400484099135100c64441400c00307510900000b100c00c44004c0d03240c950501c50102d04114405c0d40040302540d030170b602000381c00010ba031004c071108980c9030480e212a07100d00b810000e10075880304d0700d0b04a02d0300038103541001d4066600007810300501003420020710020f40307524012900304800d07411404181030130b00320100545038110084121510307180d6001c00441e42c1d1800c1c41c0099517824800d00760802c03c01c2002c20440c0c20b1034140d00c1080c60080f01101d0b0742c1d207143c008407031850b23004664980041c0d5002c01440115a4440560001003040c9421582e80c3c0324850001085080c0050009100d801d9814807140f4503036240c4c00803004410010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 80701791 1250 80700541 80700553
    0x11202130c020d0809030a1409060c06010e04060e030a020714040b190305010c090b0712050c0703080c0c0612060d050f0a030302040e090307031e020309060f0903060601020d0f0c14 79
    0x2030000b955814a41c5004404540e00030001104400004240d031014101940c918040d41c0b0000d4441d61035078005d00d407143e00a41c0810403413104d40b4082140900070b00800729410716505d0076080240488030b01c1000007049800030081405155400200302003070710500d02403080d05010f28400074008250a488080e0046042001c03509000361400400040b0390180d0003d0103c40d1f110f40085070030032070b54050a08050002d01082c804030b0748200009004c009075060251070410103c11032841c03c2416441200d0010f40043c40010380740b028005034400510a5441d80c1c200340b500d145100512100800050181000f0740094050000030420740a522230390409845490000d424010003950003401800e01400d1090007049a400002044070f20858050356400003015605444c0500340f84142e06400840c0b20038403425405580d0140240040741c120303862182e03682c814600b03260404d0b0006107400d042d5000200301380422134110084210100075450b1004603051185820144d24032400d50b0a1154840e030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 80703041 1250 80701791 80701811
    0x60603050a03030b122d0303010f14090105090a09052e14040206090904081e0d14070509330c0610061205070201091202250e01120213 59
    0x324902407510300981e001e0080c2c1c040007081c000780070340000da0a030340c80d03015512440c0140c100182c0d8003032000d08060001d4038450121056451038000386c005000f4103020071020410b40c61044035010141c1c2042d100f00d0700542c5001c0025a03803c00007010100e0712529000c84108212003442000ea08565125402e48014030700e20315541c40101112201040320319165444c26241d07100c0b0030f164451079000700641c0c603052030340741400080800580700b115910001e000781310a0882450004007000310302d418880e1214860320120007910710106885000d00c6c0c0c1281440500c1e6800320460715401801d0b580d60620420200000d10480511514190842c41c2d082a084161030f83d03100500c4500205400c4070324945541101481c40801f92044202142d04c0b07060800000445402c007561202060000264218240c3c84000282240340c0c155401a00b1009404400ba00050105102401244140f0110a00f002011200000103001e409961881000711408640d10000042101481500c0903c0741c0541 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 80704291 1250 80703041 80703043
    0xd1a030a0809150304080706020a1205040503070209160c170f030408030402040b011e08060a032306010807050a0e040807150501050f0d08070201110f070b0c010c0201020a022806060305 81
    0xb10801c4244210040d0200000000e9910260303405280c00040d040e241c102c00f43d179880700030b40c40398003014140881e00380c1e41d2414101c58490944114020b20144d90360744198030400c01d51400003800c109030307668541a849441e0358008400c402c0305a100241701118003d50160f82c0203401a90b00700715120301d0000411013004101d10186004920035a002d02000e001840150340c1c80058002d00c0684008030321500e41c00f01d00c9100c0041d00003d0292040c0c181c90303100c2e210f0f0001c0804100d0352000d5040360805030749141e00d04000d0503004001c80800f4000f0241080c00041800a603441900720300c050b40004501840014411100d0340d66004010800a60418440c0d01c041e10003449050b108030019100751070301741044901080c00d07651004559181c000340364015030356a00007a41d884124400c44204004c81d800410000024254100c1115120700c101e054150a5510721140c440459005001420001d1b40004005003942461061030455400b80d400882101f4000040036141b5030801c0000424084 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 80705541 1250 80704291 80704297
    0x1112518090c05030304051005090d02040509010c020601090b01020a08030c13080706020607170a05040609061d011d3414030105061228080c1e0a03050d1a030a08 71
    0x4414049682c40540d60300070140c40780a0352003040c0d0040440d2503c0742403039216400a12185100515841902613540c002c5001c513501141d10264680d035401c02c0c4080c094040042d40c2c01800d5810052109620000000b501d4080d030b840020000d020100100359590303006e01c15290f071500000f65034006156900e130702503500c00c424030541c1c025000d001d0110b9407085c400c400628004104031100745580d03c0d500e0b4402c006100c02042512000c5d45c4003114000990389011311014441c01c034015035000d0400c1d155140c00c507007542e0041d181511407060040700c000c0d404142d040552a240c00749040920030840001d00a940d0101d1002c2400303152032003c901d83c00c4c41110001800c0041d8000c00c015941c103000d00c0361090541d05108401e81c4002c11071740e8080306240c03c0104e400300c8100f0780700000884c0e5130f807401550000c0603001d900750480b480d00e414441000080740d1041d28038000401e00d0806c00c0d18050103d200e1296070742c04040e228a80805403007601c000759288101c0c01b5045501c46401800d0000082d0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 80706791 1250 80705541 80705543
    0x20415020616081005060c0a051b040b030106030209040210140301030309150503040320031303050a0209071b020118080f0d0305060d02090109020a0e09010602060708060111251809 79
    0x40200c04400340a8403034942c03d44900e040b0751034005414188070030803085400c244c00c190102e1050641a5002840a00c00700c8221003888840001072000c0c8000c20054441660849000c0c2c2e141c404200003603541d9030603654100342c0640b0511030b48070b4100003c0b030b01c2c8120101910303590722000000004140d0301240e440304481c1d06c40001e00298035025000c99072440250740140000380c0420303803480b1110074456151541a0450100c1e4901444100c8000c03003002e00768004d5500380c01a19145007941803018880350b020710302c0c0c03138542c0d02c1d5030301184415030703009010030041e0401461034412181240030800c0400a0074600003110b590315106d80c419541e4240139034407600024103000c0032610505100c444152020b5000744084610ba081c6510751000f50030405400080254841d041841502e540c410503000c1e01e07451740500401c1c54200000f40844801a14080c1006110b40803c0032410001c81c56004103000b1494001980d0b8a944c0056415030325504030300f030f900c1080880081500c42690101c6001 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 80708041 1250 80706791 80706811
    0x120714030703021005010906180f0b0307080f06010f0b03010902030403020a0b04060f140606120603010f060b071b0302090103110d0519021801030b070f030e0303100302090f07050a0f030204150206 86
    0x90380c071000c0ca0010740701300e0b210f0300c00541c05055a110400c18030f42c10000d00ac1101c80c20005510792808002482c180f115402410b560304041038103080d05a052141ea4050100c3e20000300d801460102402c000e48014410301800e00e90200200b010180300f4000442441d8205040c12041d0030704c1e080000042c012420354078802403800e10010040c0321441c010901c00c517001000b0504054501420444503200205901d030306550b1002e486000c45903034031808001e04070780300e012500c1d0045441e0415075072100680320345413464803801c20001a0394000700c0c01d0540340c0c40032007000a003a0000201b00c800c440114014298015001e12905256840d2100a034850085540c051070210003540500c2d058802c0c00003401101a5070300003030540c0d015642003c0c00041502c2d000a091002070200c5055030000d0311504501c2400000410640c9401f10340b494201c01e0070103407120740e0304100e04090071301c1c4106491078090100c4003c1495900307000741c1c10b84008181c0031ba4900c0720301810400081d1242c00c112000c1c0c43c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 80709291 1250 80708041 80708051
    0xc030614040b01020c04091e0b01030b0903031315090c090b01090608060a090c052101051018092003040602040305120c07180e03130302030c01050c1207140307030210 73
    0x2450280900c2c074608006801405035005410240000f4028101080e80c0e10002e490710148a843c03484070820410303000340806809941149810515040302070201781440d40240180700c81781d00c00c03c4c0b03000d08207540b00b4992040b1301c06085c030810123800c0e500000f4100706210000040c80085c69048002400d40c01d80c0c40201031a00da00003628000300c2900c0d42c580046c0783e1a4113002c40740c1d0b940d102140c201c4150500900b400075484010800c0c15005142c810142c506000403ca541000700c210b0150b2112800e01700449200c111a014400c0d1a078490340145c1611552207a0303c0d400914040c80074511201d000c00d0380d0303182c2824400060350103440300b21348134810102004070a104100696018136844000b51261130329280c2441c2841c209001e4801100344e07070300c83c58444010104001c020360301c04000d40007442481c50040608110050044a0510204000140b49524007140b4001c55070607544d10a5101e0016003001c0c03c00c0386244280d503016100004402003410f80024220648640307640e81840b03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 80710541 1250 80709291 80709329
    0x319050601090b0d09020604240f0906020616030e07030f02030d03022107050f0406030b030c100512100815040606121502031317301314010c0306 64
    0x40e40382c4161140740180b60f424840726107000043c1d00104841d0f80004e11a6040c0703501c2d80004501d405010985040c01482c1e108000c01e11a0002004101c0e04590f007420b0180f2031402e10082e48540004041030b480c400b0204c540031659000b5403040074220b441b41c1c101d968858503841e00f040c02186091090384203100e0320304a64100d40c07090080b105640c0220505203030030b4000c4402c5584da010041c00f11000c0c00700500c018a6031440d8080904010002aa00030515900000615082c0980d00c1501c0e4006c038128840c28252075000401c070303024400c08007849404ca90360b443d004c1a500045800000301c50083d4818503000b401170b200c2c1d050140d40919403c0105640d00c580701c1858044840c0010010004072100310700382c00d9158003565001c2c17030100c82e14002c0706581c0c2d21140d8200c4c4800e11a0b80411340800e041c0c00005407403a610440044444213851102507012054600c0d401c0100410104c10741000b0305000c0003444d841252290407500c00174041000030102c0500600031500543c040009241c140e41 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 80711791 1250 80710541 80710547
    0xe07080304060e13020d14070e091501140d06060807090906121106090907030c02010b0117040b04150204060e1e010f1407050601091505030a05060a020307030608030319050601 77
    0x7000c50b01561201c03241c0c02840014003d01440c80c803045904590709100c00700d0f80580d2400b407803a07603804003400f900c0c1c5841d100c4800b40070b004a01003158060300e00c0d0820400c0c0c0c0020040120200785090800d05030102c012004012680300c2c0b0b0020051399408c144001522035000b0320180d01902141d102c0d0b0b08650b44078850002181c299224032900c0c0c1c04060980e0011549028030b014405030b02416142c80c004007000231442c5204142c64600001e607071800b08900d02075082c81111034000c024a0300300840666024881c1c0c0c160405800600200641d5001c2001c101c000c0c4109102c005598400707640726a03440c00c025081814008046000750740c050960b88030b080800c400e8000340007050311284415545c40e10f0441d100f40f0500d40e0039654150030841e0402003403082020500030b051180d0081070031080c9101c1e00450788001d0380114040e611030401200020300204110b43d1000900c41d00589954603d03034210054204c41d40100e2039800004140003d4941c40e6462544042d666003082c0805d8813490011 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 80713041 1250 80711791 80711797
    0xe2a090112050318060910020f070914040b0a0e10090209010f08030d1a040e030418020c0a08090616050a02030d0e030304050d06060e0f0a0e0106060507080a0201060e0a0e070803 78
    0x42c00c030f800400c015030890069031071040b03070a1300c0074204a0800840c000482c0c4128041c1c440b0b080980e0146000c0c2120403030811014002d000d404501784103d40c4008040c5034980000342009222005250004000d0030382a84841c03810414402141c41d0303034240a45520052400d80d0303090340611452000451812010124641250a2503000314640741100c0039400052040c4c1044060145009902d03400f00d656a001d2542404204006035645501c0c080044481e081c0c00040c2207821401480000e03000c030302c00f24801191640103003075565141309501c00207801b88120300658010101000340e000a10a000031b001250394426021116005100d07002982e955180c0c19011780e041c1d104000078130403810b0040203c3c1540d07200f40e00118109443d1032108541800486511a0080800040020200b0030b4080c41d02040da00f00000c01445042c0380009125100d00e880c0540784903c0024444812407003584860020078034200e44041c2403c09003ca4405020035241e00c00c024410403a0101e4088004022 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 80714291 1250 80713041 80713043
    0xb010b250809100903052a0a0305031c06032909010501141908010203010905070f0f0801030209061201050f090c030114130519050304060807080601120e2a090112 71
    0xc510708142509082140020f0021511400c014200740d0000c00170300100006038281103250b000d408041c0c060350390034402140b28905584124a4031b001080403a40c044100d60b4912900805c101151003021851409003445a1009010000b10003103188010445a40000d4070040d88080d4840380d100d9a41142c2a20401e004256401265080803101c40c9040800410800c03010b01e100000fa5a50748031103822a00700342c1c040d08030b450f218010000e007968824018000c4d0141030400712000806e00c90010481001404024001d522502c00705405556003c00c58002c1019900207208616090200e941150015211044140710300c0b46101e4441c40c040c010700b2103141501c0c803010859501c5855512a03951008002d65440c000d4080040c3c0d41c03048042210600e83c040c0009541d01e601d84803004106c00001404201080101010302100e41c2c0d20003000c0c0f48107400d00401080603016404403c1c01d0041a8440b842c000c01c81240595071180c0c40b54076240c019004640e00c2c0d10301d03a81c5040301040c0b420f143c80 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 80715541 1250 80714291 80714303
    0x80403171506090f04020309060105090601020304030c0e0a020f0d090201080108032805090a1202010906031a010c03021606080615090d0b280e0c04060b09010e0301090b010b25 77
    0x44241c9080c10002c014081049009214035186401c2c00040340032a4015614052a50403600040c8814100340d40700507001074080c801146070038950740b20088100b10501802950301900030202e8091440d03501552484040c081d42d0980e2100c4016140d0010704c00854101e01003058000006000300c4003006031451903403a0845042c1c91400004500901c81c4c0340030040302070001c1404121b00a488090303907070001d0860f41d00046d10003100b600001d0400d80c8103500c003e04160502040f00703c030000c02407099001002c217003082c541c02000c40c42c080c0c0c00c0c44001c100500d00341904180025600707601c1300400303001d18021345441c0f9920b4154005c02c15244a41c0e02800c0d0000b4140d21180002a541d00d1003990291000c42078944802000e0a9011441c241441c880c02d83c68448400c400f40c0c0f0024000580308202c00c540130041d4903d06203a845140c061001e21a06000c28210146103503102034016015442d4001552100b6686985518030b854010748100044841c2c00d503484804106440780342446d0741c0d0022 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 80716791 1250 80715541 80715571
    0x4021b060c1903050a060305030708071b060c0f0f06020a05070606080f060103230a0b0f07030e06012d03030203120a20090f03150603010b180a0203060102031908040317 74
    0xb003081c0c025000c00f904e0610306903620400000031410600241001c2845985002c1e03a44115080040f11081c0d070075000d9540c11103812080008903000500840d64650180a648800c412400c0200c1c20088048020b841d003400022294052a4004002d1055600c00c1c602048655102c1c000c10f0f03617900703042000c280d070342d800580103002103000d0b000c07241c60031910340c2010f4a0340f00c0c5841c2201e0825500480803612005120103002c848260982c1ca03ea00c0741c110324041080240314805c0683e2a0410b1044141c42100c2c0c02c0d0201c84149138004040e6154040807440070450790b00e282c002d589034450f0712208003444201000c41d0000d496402006e2800b5040207003004050840102e0130204e501c980003c507800700703141c42c04a20070b88007440600841e801280008003246408002d050940d40c3c05a01e0b5841404040c02141c000038641041e6030704a05450380050302c0395500d00043c1c1c5148035061038810003428103250241d81607804900e66200e1442955011295035082101100402c3c1c2510002e511000f02 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 80718041 1250 80716791 80716837
    0xe1e0709110d0204080c0f100207031118090f0115060801180e06070905041109010815240c10022104030909020c06010302100206060102060a1a04021b060c 68
    0x35401c08960720403490203281c0b502d800090510b049030320590003510690001e81080200b4940030071241d001d090103071141c1005801032507000b512240b0a000060200c149071a03011810380b01c1e080c1c009002c0c0035540074185181449041d1540d58189007800f03020b030350309200300803117200b01c8121400111462611485034903400e0240c03107500700440003110042e090f5904d040148919003008103500441c055151407183c0b50401d8248801e442e0526485407245004102c11a01664445e40440d0b011000b400941c500014180005508030700c80c658401e6113000c11a40c052803003580d44028a1031300a40e00c00c489041a44e980c14000740d0060341e103800c030480d070381c0c10300000c1024805098079072240c828504003040544441c103d00803600003201007038041d80040700600441c00c03c40003c628035403550000301401d20304480000d68551000706001901c0b601c41400c0b000c1035180300e16201080000800541d02e4400c5c0f40c3e000146036006e0082c0b103060b88035440c041840c80f080c0d003089425558410b01e56503548864 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 80719291 1250 80718041 80718059
    0xa0308060301091e06060e1003060e0102090301020a050d15061e0314010f030c0803030f01261009020108060d0b0c0f041203020708060f0f010e04060b040603060e1e07 73
    0xc00340d98065498085200024204000001d58020001840503070700b02c50b0305080742192800d4200c0020240d29406001f00d055030b00c128001101d82c020300c04510384030340d0b2900740e01a005525481d42c056001050740009a5045405800f0042c1c8110041050440002242410524500c1a640800e62032005e030001e0140402c2070703104035521400d0210742040340b64005c0c80000c100b6884050450207804040c01049000d103c00001488903000070b5007503003031524011240380418411600301652025000c2d1000c440c0403003618801400030103440c1c0204413003034500007400d03005104a0001d40c031407001030f0b01c41c500000025441c5800400041003551010000030f090741c4a60303642c0f00100c10034040007030104441d1042e0049540300e640586000c0f4904a000d6241040140068900011803c20020408803031644c5604542d140c9945043c01e84a07814903500910340e891500f074106003040300100a1140c00c0d00003001d84080802110302104d606181c1c1440984400e65280300c0ea004030408014400c8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 80720541 1250 80719291 80719307
    0x1107030c0614120702030c010e07210203071a1801020604030c110f0603010f0806071b030c1106071a07020309060d09020a050a090b0301050106030615030f061805061003020702030a03 80
    0x701c0120b42c01d151503942c00c000400144121070f2000164000144184141020701603111418501c1000f403444a0174880c2070006030a0a10200004841000e42e002c1550b80810041d80240110705090741c00146040c0c010741540e200e84c240d8200d07590403101041c8554800281148a00d030545d58061058480303540380c0c0712410031100ca40390f212180700701005440c0d94110045000b41110b0044038929890f00070341c0342c180b0b40002e05c580140120240504040c2505c1c2004d80f603401d506240c050400304691a00c00300c0c46000d80485600060046a03102c20031400010078450540d62044c4803140c1e5590311000c0740e5901c50800701981164090194101c000801d40081089510050440240d9500c0c0d00115800c03210300d90008900944610b4080b0203801c0078410913000d00302518050209a04041c6002900f2050101e030f01e08066446a030140007185d03540c426000f4201c42a400c2074000700d5624460090b2406550191090034800441014a40039200f00c814640d4084e021b030441494944054480c0d003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 80721791 1250 80720541 80720567
    0x10c02090a02091c0c06020a0203071712040b070c0905061509030109050a1b12030915020f120a03050109021312060b0414070e010804050705060a0c020402030708071107030c06 77
    0x3580038002810303d41e80b11003040c07602c100b5001c450541c611440c101809500c615030300100c150342045011401584001c07a0340c40a840c841024070040e0021190714600d052070358203181242c200c0204000c100e5203a41c80003460028014000c08450640b500642012074034243c40c103e5000300707031048810000650318054044540c00600025500ba0141c55490900c96a08812170740104049010f07035105c07940c81c16107130152200a0390010a070340503079005401180c46020b0a81c02e400605560f520451080041e40b82c1209464203480035101c2104010303000703400043d54800840c1c00c001c00411500c11520070350380d214400c0d01500050f00c4c41c3c00c5c0800754800c4141d00075118280c072203001941c0c58032a030007004c50100b1f05004515041c0780c0300c0341c001d040c2c011036441d003410080503e041c00003080300041e004cc00d40f01d084400e99a50182c00f582034032550640e01740290018004420440c4031380c0c0041c050352285006880c0c0b01c1c5805900500107882c2c0c0c8150000901e8542c60010501c1000e00c181d003001400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 80723041 1250 80721791 80721811
    0x80f0105031b040b0307090b0909030a0c0204020c0a17040611190b0603030d18020f0306070c0b09030706050406060e09030a05030705090409052a01050406020a020f0105120f070201140402010c0209 86
    0x142130200842e0034500580c11015400d502da640c41c1d031a50078070b008480d901c04800800746090985401c0c0003401080c40b94400307442940c011070355400c0c0b0001801000c0310f547d400100b0625140c00703840140b0058200c0d01c202400300303822403007081002102040001400c0f40c00552000c03000c2c11a5126039000001410058140c4401d000c043e82d02802481001001003420305000c844140c41c0c0f04000a03244580b0255009421a00c140a08103800412112009038400414415540e0340308501d841d50140080180c2071904000501017400140d90190f0151034100f40354007466503410f142c00d5900d10034112104001041080001d081901c542c0141013196401400030482d01282d4494501d000700c00c200b82d448102001880c04007204584420170045a020f0070100d050030710b0090040d40342d9694480290261402c100c40703e1403603115004445140c02c40c03031408240b50400c45150180c02c40c003125040301540ca040c032403060018000406030f00c920380c144d655180d00401603080c4081c440d8041c00f44248 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 80724291 1250 80723041 80723051
    0xb0a0302040e07030f0b04022b020c120904060e090d050c0c0409060203160e060f07061b180602011109100c06020307020c09010b040308041208120408040501080f0105031b04 76
    0x21038501c0700b40b070742c0035a0311583d011483c8601480c0320021035401d00901d510561040110b00440c040e0980314503999040c0d1041c0c4a529175041460740080d20030350010382c003d409001700040280c2d142030058080c601c07080d10200030181d10345074640e0b030103203040d245078074664407010510094910440090100910550607164100b190303402040035038425900441701c80d9004410846003100301102584040250314020703158003580b0340807031500e00c2050202c80c0c054100007100c4050101d1a00b0550741c070840b0303020000c81c0f80080c0c24000e04400040d00c000011030480f0200107203881c41401003250020500d40814544850002000a02d040c42d0440340244400c0076a0311000c01d00b1072010b140329025a401901005040c8810801800b00c140c01c11000740c0e10601c81070010800741c00a0700c0503103e06d200035103948003140c10328001601a00c802c0d41407800d00ca004100c1001244005041100c074281c0341c00300030f0386500b1510030503030409010f900c0d0185c0c400309204402c0350990007141d1000c10b0207000060 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 80725541 1250 80724291 80724299
    0x51605070b151507060b100504060c05070509040606060f140d0522030206190e030904021303080d0f050604020307020607050a12022d0c030304080310170604031b03090b0a030204 78
    0x1071241115200580d00380c4001c51300a092060b64000d072004400102c680c401e0b2012100b1018295000354082c040c10040e4032160402002420040d150103481e00418100b0306252610303040000c1d000364050748002504d40504019814003480108103c8040300741c501d800c0000302c1205000500000340304a4071b0f509000f540355090b509403a800000755000781e014044600d80740c0c001c40c5006c83e400101000302c910b007005c103012040307001c003e40da2414070442d8091782d242c450040b9103910403219080030300400c100144945d101c5c1480d50112942046035802840144d41e0a0200000c9001c1256404050f070010310009408512810042c81910180e0801860980c031034005070040740c00c8028840120110480300c40c0481034480705010b09201f904407002d10781003a8400300c9480c1d000240c001018120003101003a40308000c402c861000d840503400b01484254001c200d2a6180029078050b800300342e05241107050254415441c0f50029050307111842d0399840c101a03141294007444e00d01c02015800d01c0081 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 80726791 1250 80725541 80725549
    0x40c030309211b0b0c010c02010b15030c03090a1a07030501090b0d0b0406270507050d0c06080c040b0f03040c1e05090c07020a080708010f0606140c0106210501051605070b15 76
    0x80030342019400001f68581622030040d08440b0541c10f91849100407600141d00c1d208000b0490341e014036410f1103542c0b40d07203e9020451802c092000003c2000d0031a914040388030301c41f040e4041c4210416501401540d0761213004004440c040e25030103401401da01c103072101080301c07180802d070424400c420005086a1049144c1441c8000b10040c29001450243c41018030004002c2d03d005000101e860b6601401c0130703501c80c0d40c100c1c0303244220f01c00d0103954400540d0444940041d100182841007403195101c90900c0c4201e80c6a00403241116030884140000c2144140482d070f42040b0000c0ca41c055545c2d5041c2000c002280d030005040c0c840c0d003601000b0040c0140c90b205c2c1c03418000d060740ea0040a0807030038002c2507425144803462440010b07251480411005502c0740300711200c1c184071641160b4a188030040d035401760006801107011619100c403090041b00b0700e28034011109018100801854990307282d6100030400002203000010030500450012545641d00c850f00a040054500c4400312100045 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 80728041 1250 80726791 80726797
    0x22080703080709180b1f0221070c15030e010c120f02091503160201020a0e120a05011118030303040b04020118030c0605070b01060f020d140c0105040c030309211b0b 72
    0xd549010b032107144c1641d42e810940542450514050b01e006c2650b8031081c002996078400300306400582e4200d00c800140749403641c04a1360040d4101c40c021451541712102d1418105030007548000003440d00c0e0381030460030418030464030303000b43c96a6500d001701c0f4459000c10281203080c02800d0b0302d40d400c00c2014040d56600e4110420000031100c030549a18040d2413007845a1f80e0042c1e99420340e401080a607403540d500c030184610340c44d01102d1701c140b401a6640540d1038040505002812986440290070500c422200500642d2207101410300350350560b0300034551a40000c0d100240a040c212002c180158040c03441480d10607280b883d170400c05039581d1100320380c2691070790000c008604005070310390501011401a43c09002541881c030781d2111b058000954031650180140308022040d981e01050b4481d0908a8080381c8400c40280124101401c01e5100c00c2c03490b12040b004954000000500d69400f5000c225081040c0b0b021400400125203499031028064900c04008601040000c1901034484001e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 80729291 1250 80728041 80728079
    0x6060302150310060809250608130803040b07120903020604140f030f03040f0f0c0905060d1a0903220e160c0807080d0507030f0501050604080d0507110307030b22080703080709 77
    0x642c00488e00d02030025140d1030340600000b00c9140944511404600f0a804490700240d006600342c005658844003150200c15403039100341a181409101000c1c560b00143c030300e014600651100030b031880003948081d607507c42600d0a01071500213000c00345040190360040d560084c001c18103103580014a13a01c01e0820064014111000f2211040501c20022607100c1c1952000e0266074465010610b0341b1480c075001d101171840f0a411400b1000648450000e200b605d0704641d40107140c0303032002c00c6540c501c1c103600d441d4051b0405014440300083d8900100110f6000ea10301030381c42d81202c402180d141c80703400d40e1245105842d140000c2285c10440f003c10b100701b52290185540c00a1720b14017508800c4180c50043c0d001e0703442010705010520103028045030f000345003001420102e68034070842c94040c181038a408400d43d410b0013951000010301c4400ca10303c505c0303603819400c01c200e400c0342e10043c020f40741003031342004e45405018012840041d010350050b0f13400c542d0500f442444950b65008800413640f401038 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 80730541 1250 80729291 80729353
    0x10140d020405070216090b0f040b010c020402030108070501080901060e040f030c0804181b050a031a0904030c1a0103030509010c050c030609070602071418060d060906060302150310060809 82
    0x19100000310b070a24210000713082c0d0f00400740007145141c40014000c991a548c0c8620681d43c03806204c40c0790380103260b020503196001d40295225a518101662200007501c40d160103c0c2d0b0240004442c400180701d920152825008007001644076a1a82054040040021020320541c4030702000840d088101400041640c052200443e404c0c5030410350aa802081c2c11001007890489409401c035040780130fa5107904900e1400140c4c08034005004104040d00b4010f030390300300042030140010f0690028020180c2c5014080181c3e9501408000d011000401d12024000072800d12018049600c03d83c1342c220114010070844041c921000002030808006442c0f480003544115002c00400f0740520814008003415200700022400f21030102e169200c0c50207105021491000014100f41d6640c0845e2650580000c0100014170b01c502e401e03001070025010580c0314004842c8100c04400c10881120710403c0080a050300c5103250203c19200440081c1c91902035015180b0f041750302a611300e04100f80425000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 80731791 1250 80730541 80730553
    0x90506010501110a050c06031504060e150303030403050403060b010923030f070e0604020d0204150e191202010806031f020d050a0501030519030509060d0f050a0510140d0204050702 79
    0x41c0094021200e0500c0e00e00c59411055151020071004141d02e24008001d881488c0c0d0b81da10b02d02c81c20500216031101d207500a01d4140b000c9290303403803205442d00c66000c41104807151400f81003055601d00003110004c000640c00c00c018800140d40f0f8200d4a10002d0606003045416111f00d43e02c103c8010510011000d520b4426030b80c0c5052404110701c001c0f00c82c26202a0035038508001066824a80040c0014002c0e0f800040c21203d1100c10b41c1150003c10340d47c03410081c05149150f004062070100c1da856441454070074260482103000403000c8003180d6042003aa41e4410080e401903403c1c40f801001c01d681800350ba00c10413a003a6001c406c984142e04030150041c0e0380c482c090011400c43d4000752001148500e40801480000e00018000d01c10360880811060b0124080c9011215031003102c0c1100d4100c0c00110b2900360b81e131010f4100d00c522400d668814449a42c90300f0161080741c03011184203082c1c007540d540030000514941000544044050220080741c1120740104007904c800f0743e01d45005a0241d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 80733041 1250 80731791 80731799
    0xc020102011a15030c071a0117060f04020103180501060603020a080f0103051908040f060504030203010b0409020f1017040f02100e01080403120207050f100f020306030a06021c09050601 81
    0x2885620060a00b82d100c1d45038000c1600045480c0724a0220100f02e040f2001003c50101071915003900c0200d40c0c0492007980071a10210481584403080c1b01d00320b074842c280c0e00c2e400c180210100709244540502d07103505a840e56550011000b40186210302540e500108040c00c012500c01e005000160401ea100035139982d2010b030000304103030340040145c074209008800510004002140445200f00000140315986046040045452245a00c4000404200305000540340c0e000f401030001c4034002c90007007080752405d000780019607404110080d0f0100e04008203050918242c03900d49000310517482d05285051134640b46440040702960141c8407000003c6120b0210b00e46403041e06044441480c01c01c0d8600015400a04201b801900050600800c1451814105800d0341500e601c16044011240316240c030307558894640d000c051070002e220b400c01c42c4840d000d8140307008032030140342d02070f005141c0001c080e16128000d40008540c800003c080c0c0d4032161272821070b40a0440814002c0001d08015494 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 80734291 1250 80733041 80733043
    0x9020f150a0e0301091e020a090c020a0b15030c040c05120103061b05211510030c020106060c0201050d0c0207050904080301080d1d010e010918020306030607110a080a0302070c060c020102 82
    0xe0700203542c3c0319a0420030742c000068641e40112074840421140c542c101000c3e07100156400800790404480d1a14000c110b2860a600282c65000b0500600c90084180c0754030800d1011194807060301c640541c40107132210080d050a40c0300020240d2180341203418541442006540300c0f9080e842996210307211b160005609203d40d01602c03607000d490038030368038103507050000c0c81e0ae0000840c0c0560714840e0940000d100b080f01e24012004d003d0303004000241031008201e0140003091150300c950019031810a0100704580034440c00c1000540503100c040c1000e90003407000020f820312841c035600714081c0355000100d0f904c4403407000740120b01c5800100c1e220340c141200c0d54580501e01303444000b0041049008000345000d0310b000128084286498802144608010b94221502d6801008040d4440d08000d2424400364051030140a0032401d403000e80d1902801143c808103000800b0206820002480002400c80001020340c030b2000d040250806040e0f4950301d4400300240e101001003030041d81d0140c02c40d03034 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 80735541 1250 80734291 80734307
    0xb030402040b061c0915020a020d020d02060108031605070b04061d010203070b040f021f02030405010315050105040e090f07140102060a11030a0207021203031e07020d1209020f150a 79
    0x1000355500350078030920b4012400000c280712000d41480b960303440405d00344a9198076204000034001015542c58200100c004c0d0380c0c2017951074407401802081d130407c90b100d1000c160300e4101c585910096040403062209011b02e030ba1460802c07180c1c0d00c17840b44001400201200508002c0c0f01c90703112021900d100300d9000c80c405503c2c110103411500f0410211000071001d212050300700703070044144501c10b03a1510220700d00c40b01e402c900c00b1003410007541203604550300100400540d6000c1e6824040104000644503411246004160101c0e0b020300c001d024031085107100a51040b1102d04030303054040080c61090030960035400c03031007070b800c0c40e214000e03c00d5070104401034118000070030030001c0346c8003035140c5026404040c0504140c3c90700065141c065607a0000703280c40e140300d41020341e540d905140c021410b5240c65a0315007113404034032000151000f80049149900110540c8400e54088a807085080007002d082900701c2e4450060030744205140c0750f440080c5809111020800d07034803801d150002e4040300e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 80736791 1250 80735541 80735561
    0x110a0206070807020d03230a0204050f030303010b0d0203070c0c0f14031603060e03090414010501020c030f2e150612020a0e210609070e07030608060f0702160b03040204 74
    0x104200b000c3c044040d900199100240c8203510700050201c044014144500074011001022031207498144121060780794000e01c101c6038102e60304101000310f54207040d104d0109100d02000c5d03003000c0c03040e0b603120629034004503801092031601400083c1150356041c2e801c503040d008203030912413040c81489544009030b0591071000c03003200140001711a100c41e4522503103071400020481521070203000c00a2a040003500e241d82d500030020720001011a04d8440e865a091148a00500c80e0301d0450a0605001c6a00d41070160040c002d030118600d1141401000c01d940c00180b02d6244c205e1015a0101240384542c04095048001c0d8003d180d240020041c100e0490741d0103a2402c80c8100300c0d8045403900221a8240c10b44140c03590542500b00321a401c10107070320b1a8091600f0f0046104108070b0113000f140e404241c03448001c0303842d03268881c42c90031400c07100c1d640140c8926511401c04152003031103404e403003a4411401d2044a200c0000845180c00742c1040303a0140f02480e0f00841030008510f01409403500350 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 80738041 1250 80736791 80736797
    0x1061d0f01140609150903010e0f010507030603031d1f021c02030418050a090501180302070b040e010b03090109080a0905031e151306020f1c09020a05040b010e04110a020607 76
    0x8510030a0003c0c83d24881c1c000800d120b40a002d80440e18600010152521248024000c00062240d4401c041d100e0010301c141000c0c5500c2c0030002039446020380305060650782c040c0e80760140010050900c214548a0328101a44509041000021155940c052200141240d400340065001136241e00009010240f10300096400c18042030180828025048000303018800303011465881d400070800003481a114041d0081d42401c0c80c40700045555803c9503003852195003200d440a40c3c4048000560141d405403021060035503004000203104040a1500880c91000000d10031016a84a0070036070321207070344800402c0003e04200000d00d8184145824050041003001070818400c41560b143d0660304081c03c80c00032040040340c03d28086c01c0e613a40d2501e0f40070000315585d2030070b0303003503100c02e600403001c0103500050440e0380e81c00000150260482455010303040401e00ca00344400c02014051000c200c50400c40003102c0211103a0383c41c019000c58800000c14a59101003154000382004001400d003414 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 80739291 1250 80738041 80738069
    0xb0711030a120e1503010f0f0906030503090108040501140a1b020a2a0b0a020c0906030c031c030b040609050105030115030515040c090c080106090603060308030402090901061d0f01 79
    0x442d0784002c440400c41c6035031800310441c2000d000082c00ea8884121111802c0c04003200208900301050740510650f032030078a8403220203503140704000a0b510603000c01810f607002407100080e194001c448041d00180b040c4001702c4c8403030a00c40c0889070320720300701d072802e000a4a61400c2403062950964101000c56944007406030b4143e036031101800d4041030072400300c8941c18118400c0c1c0d1082191104400b5200744803d65a5402041a00a6440000f040c40341c2c403c2c01c190001c20340fa45000a02c41e12800380c040e01508194131a003440707003486007084c0c98070000c3c9900c072a000c000c5651a8407510010b0101e080380000e083d4184001c1c54211000c0113001c0c00b80c500f2120040c8080784d00029806841000707010f984401d80e68900d81424000103540c001c80c0041d0821029281080d040500302d07059601c255034a1408594540084003600d02d07a100181c00c2800c10400304d809801e00c00421a40003030280c00102d042540c40f1417160074800c00b00700168865030440c00340407401c0c014030340c0303240148003024840742 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 80740541 1250 80739291 80739293
    0x40606090b040b07110303070503030403031a130b060c070b12010e061311090a060c020108090d090501030203040c0806040803040b0901020703090b0d0f110d050901140c0a09080303010b0711030a 85
    0x1248294000c040c444800410060104026885c5c507881610000d01520340304c041d9854015920b400503907046012a09120500d502540304244950071080e0040584000b4140c0c002d141005014440c46290060001c211503040300740100800c000508041c0b21140e40c0760071010312000c81190681204402c0038040c801d2050566840240b4911440448400540c24419103041c030900d11401c100c0a4014441c1d41000811039000014102ca075030013a281d07100350350744880b03070180c403113207456a2000401c61461043c425035120f80d01440d4801d104a240c0d81a503621654414039102c001c50341101d07800400401c001c10400c1054266812454a400a608040581e5030150196040e80119900c1440100e03001c1421001c580000003080c609031002c004008844000d08a40e43c0519181140c5da803e100c04608200c6d0140314114461070919030b03260302c1d0b48801c1002107190f44040200d00400c480058049101f070420300042d8001d00d004403006540e072082c3e103003010400303400c0c0070081d100ba008451820 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 80741791 1250 80740541 80740559
    0x50c070206121906090c030c08040b01150210020c030a1404080303060d11040f0509120910050f07050f0d030609050f040b0c070c030b070e1909021308061504060609 72
    0x1568041007a82c02c140180c0d12616a0f00150100c6030301407101c00c0c1040000103d080c100d070b0000d081d88000b661705000e0701d0035040003036030344000a99005141c4a8408010003603c2c0c0c06080310000b00e0910320540d0360010260003110281d801003d0001003607040050a11203042e0002c200801c840c50340500c85091074940b0304415228040105854001e2a0b81c144410030800b031901402003400000f4010031843d44074008031802400c003126090780500c40c4500704080d01082105032030b818800103285441d010b60030300e4120744541007540707400540781f014070510740052014030480c0340502844000740b044400e0520000d080c0c900035848031505510300000d010800c0340545005506c240c0100342810782da100d95156800c244505180903020340003902d4040100480c000c00130b1300a00c1c003a070b0782d200e000044204024100980d8810000381121811040091125503009071001c890342480c0945540c0c0e5a05116090070b0084815640c501600c101d28040c170702d40741c80340030b01508072850601c265604180003a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 80743041 1250 80741791 80741797
    0x10c03050d0513080a022a030c0d06090506040b060a05040e0c0904030e04110306090906010506070b0a09061e060806010b04050d080702150d060506091503090109050d0f0201050c070206 81
    0x41004944400000c2c44030312000000b01c0041d44c2c407541c26030352005405802910f40003070150100da0b110000703549681d103e507840113149074020014068000c60020b04108003076000c80030412a80182c4680d80c50300499010320440b0300c240d01039242a1041e01d010300030070801c07055541005226925180c01c24411540000b0345401c2c2c140b06540a20480d05d841c2001c2d070b180b080c2c0242d55913106007020550599045401d019600400e0291b031b080d041503c45e00311482d125202400b401c1d0f000349042c02030401080b041e080c00c9821810b810070001c0d6940c0e064440e1000e03103c040c0607030200780e18000e1421130307507200030320a920052000d4409400325504080441e8030b1880741d446402d124011403551070301800318001c01c80d33102c0c6a008100c00162801415000403680103c105144d0542c90b001001925041c2042280d0b50368070024420400c20500c00389021041d00080c01c218031075980d801c010707400202c080202040f94419a00c400c0600c005e2800001c1c00c1d100000d080718070541090203002c0c0140c03101c0007a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 80744291 1250 80743041 80743057
    0x14030a05071101170a0e010609020f090123040902070308070806010207060c080c0f010608100209090708090a0c140a05030a0b0105091812042c0408031306020d0e0606010c0305 77
    0x3148240d2002c280040b603441400780403041e21032607540c0a11010a1181d40b101d211203090344024460640e0391107a6100b00c2c0100c1058082d0510100081d03a1198030914904030602c00c50110986c40550400903501d558009412201c0e50340d600013060b005054002d4861948035919203071001d664908800002d454000d01e214400501000f4900002044544800e8078066541001110510b05c460321201e800384c03107184107208480c0a00d042c6403402c00601c0c021a2101c03800688041d001d901e5400301160009802403a0310028000d8080482c00908841c03042802044030b01c401c5030816205100f0048504c1055104902c0f0b0b0b4407800406d0001200b0000d40d03811580100e032000003568646000025102810b28a010706000b0070030401e0200a0321000b070300c251007034060f8069078004461007260301954a00d4000d8642002c0e00005000030f075840000310340c041d0030844068852040340d41c0d580d003603801a08400d071419858201400386400300300002d40d0300450034608480c1c03107078180c0c50141003485030f089 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 80745541 1250 80744291 80744303
    0x290103020a030b0301020c0c1203030f0606030601030f0e0c040b040209030a06020f0c060910060b030114040b1302070c14030601051509041812030b0102010e030d090f0807050a14030a0507 82
    0x3461490340c1c2c0070b5030100304503403000f400030341d0380b0141c1100c00c5071600a40c0444a200e9480480c0c00c00c2c2840c0b0000a4a2042c18401401d041c00c1d1100c80420034603820090030301b410940c03a60844801c2d44144d009400b49510400010b0045103005010802079032214001240102c0c810710550b0460380d80068022013031a084080181d5507442460081141c0c403e0101c0d1581c5c0d03100c1d46003031007281f580011700e80503400341d100c030200141500c8510300c00e4248003c1c03007080003d03040c0b0f054402e400d203000e5000c400d410740300405030184105981440c1090343c22010741500c40d01c0015030100543d1240782c600a5104908801030845d540c10314000030354010141c2320000440f80c0c0403a06441507140c40e40158031032500354030201d00c16045460a2442c40c4041544000041d0038039a406040b035005004250304140d901000d54144003640b0040e0b001014406d505a683c600814031100c00319844070020002203001e800941502e807610300b4421640991654184055401008540070381a80305064440e0300354000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 80746791 1250 80745541 80745547
    0xf0a0e100906200301030b0c0414060a17240d02010507080f04050a030b041a0405030a0f1701080705150702150306120607031b090e010e06010507080a05030a29010302 73
    0x1c2000e074000c156007001d050180e81881c00070100c8154070342c00340d03040f01d00c01d030038031501e503660150070408d01d0007107205200c0103250b020507201d4585090400303041400102d1801c00244101c51404807802d0380259103280c2d11004c03c4a14101200e140c0000420020307050740e4941e03006030540d000801c0b41c803c17400050325011010404400c1109600d04481c0205401044040300c1600da090910400c50161000c0710142c82d003d50340b8038180c1940c85c000344141c0c2c03c900551b0610500f98002e0700d402c010b0803404001c000f68120404428107070740c440140a44071020040800c1800c10040c001c41c035464600c2c2504100c2c0900440c0c0059440904521031421001e00d0540c0300e0300e0304000304610500c4414032181d903000b41010003100691541c400e229030781d01c8241e03441c1402c0350840103483c0004240103030b40400641c00c0041c40140600c603c01600508180341c01445c001498a514401c3d8200c24103000014200200703000500841d07004250080904107074110854100000c120301d00c2d18000289410b1503004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 80748041 1250 80746791 80746793
    0x1030509060a0c18060e0a0905040201080402060a180e040b100b040504020a05042117090f0d0f050712110618011805040914060f0405030301062106030b0f0a0e1009 72
    0x150b41414a40c9080d0f0b004048143d107900c0050400c0c5161015940222844000023500c1c42090050714055034060b1600c8005455603001d0108079804610b061092141c1188001010035890b603c000042003520b503140c0f80d500b0240b40c210742035980a40010301a40701b0032824404580201e00301c0741103500480b401a0b840101060951303c6010b00d40c003c0464400d035100406400c440d402203c83c0e5075110300840c200c801410003071024030f80949408039803c070100715201c21903401c003044c5a5010310301602d4890701543e0950f45007890544680c02c4112503a409010000030030044c1034000426000c121081803c00b440126860070a10000700c150f03041015000e283c501d14403049110074041d220162051086c0446800c00791513505074074045010601c07440002509100700c0d0700002d17000e80e50107000f03589180d02c1e00c2000c40d1320040d81c1d240303403680380748041c0d002c0c00120741c51041030001e6106c0e043d200c1d4039181180c0003500c1c1440003060f0311149070402c0c544641e0117102041e00c406c42d4820351030000d909030345 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 80749291 1250 80748041 80748047
    0x6020303090d030204061d041e0203070905041a060d0f0c050a030506010c0305070209190f0209130504020f0d0303060506030a06030303051506041e0909060b09010b190f27050f01030509060a0c 84
    0x74441e05410271904414a4180c0282e4035001140704100c1c60300c4018110369074400380070841d188015030390040003400040b000c4501d005030080a401c0c541007000b14038100b19126071000c4880704000c150100c1c000150394100705070980122584004242049800c981c6c198601602d58880c0c800300920905101e40098020074212170144940d11303500c202000341d10f00704014000254089000c3c54032590003002c4c0014203230650b0149ca403080e58040c1103060004180d80902807811240c407421018035807904400300c0c450711160065403085091400100d0442d14605026003154006480940806404c0310b0b580c940d6182e2000729401c85203051004911407030070440030381c0642a19080f00382501d080c0303014003080c400c2540089441e00400c42e1609016641e403240c40ba010b2003030003e04d450b1200040c84c22008240070310101d801d205514100061b0381072046410b0760034541c50320241a462a0521001d00c000d06051324060304014003801d0800803030601c100e505135103410003800d510480c1d850340410300080784 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 80750541 1250 80749291 80749301
    0xf030a05010e0606032803050f0421060c0201020c0c0105030711030309010204030507120302071a1c06030506180304030b04210201240b03070c020a08030406020303090d030204061d04 80
    0x1820000800081c0c2c2c08100742500e0b04030a0300c505201c1c0c07044280324091a03048a1141024100709001e1444c0140e06a0f019582d0341c000c0c11558a074010705010004946040c04602d6614412205e01c0030384074010761500d24202c2c2c07410310b042021a171041c45200c80743c220003d41c2c0440302d80c007400c140c1e1f1282c1e101c0c3d01c1100d003129800c8103400540030100138002661015000740041d644110140d40885444008001c1403502035500074006a009500030840160013440243c495a4000c002620701020302c0c0d5841c400205050116041c2956880704100b070040c24400d0a800520705560341142c43c8040d14080c0e5680250f020181c0340741d020802280c100080d000310b400d4505100c06e0851442044c203007001c1d0088c17420218020ba00c04502c10880306002000220205554414000508507212100700300c4540220000c1240c03c5080716001180b4000c0420180004240d1540110740d20f29118580c941000d1081c0c0140d01414014001804429044000c041d0820800900c1030551464800051b01403d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 80751791 1250 80750541 80750543
    0x10c110301020c03070606080d09091116030c0308090102031005040509030d1401080c010e062208010204080307030e0901030236040b0403180303050306010f05090a0806040b011e050f030a 82
    0x1d0320008480000f000c020000e0043d00d801041c04001c403e070341c1c40c411912600720300886000500c40320814040001c1c01c5d4807400050b000c5184040c2000c506100c0c0c0b610b4480b9001e0158080740d4903030840b81c00c05510054166101c20560029030841c20031004400200020340210740c07082c1c0e22040040e81002040003a162802d00191090190601100e60104180300a00800f00e05002e9920010f070030794098000ba144401000c0d0400e850080c98201c02054114a107200301d441d00170342c80340000c0c45a0300340003034406072202001466441c806403174040e00c008011082c1c18012403200c401000960344006040005089803480c0c125503c00c5214828030351080f24000c90b44542c04581804240b0080f15141803040340702c1d84070050100304070300300c1102c4103c0d540710050000b981000042d189510801c0c0c00d0209115a0030f049040c80742140000d01084415041400030350301c500200014018041c0c0702a0042c01010500204000c003016043c840d584140111070045500c603245101c1c40d10100b2906d1409 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 80753041 1250 80751791 80751793
    0x311010603031e0207030f060c0c0c08010507030c1e0315031b0608090604051e03070503190305060d03090902070c1806150e0a0e040204020f03070206060a0b03010b09010c1103 77
    0x51030301c0e0716000d0090443c1402da02d01c01110500e001c5160350000131410282ca8000c800b030000b00c54070b6a200070182c85120800d00402090b810f186000800002d0310744003901030440007107101c1c0b5060700002c040340d19081c511001c00c481c1d10b40c022000c04100008003410a29031601041c0445440030340c020000944c1e01c014040724914000d8000c000319000d2840603900c0707a54603d550380d00c0f0754020030764400d001e0714054000c8e004081038403120162035000b11450450320041c0c03400c110b1030f500c6142c00c5400c02c007440301e105034440c5580030200390b1500c06d0340da01c040111307107009449071292801020300c3e840b030003003403032250340019240c0a104013001d1400c005d0480e840401c03004140c80c0c2040c80a01030f24454800541420002a4102c0780074503403480301d580001c0c041403403140c0351080740b642100c409441a03810650030404001c28550102c000c2d4410b041a400030042c9007041350034000d8410080d48402ea105000744014085d0044010494101039801d1815134019000380c100f1030a24a203d544803945 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 80754291 1250 80753041 80753051
    0x7170f070602070201030f020301030b060d030e0d06060905101208090301020910030e0c040b0d0303020d020c01090309060f02060f070c0303060512100b060c03070803090f01090822060806010c031101 87
    0x401c02141c000b494014400c4c1e03000d01c0444c90501080f001d070300081c040140000201f10018080741402405201894086d03d841580703802c0071000f02c0d880c1c81c1150070595100f5200c1100303005500080c000c05411059044040154a2038041681d403201c48010300100111400a4034444030782e800d40640740c0c104c80081c452a02020904005001080303000308551440c05801c05503045440c2a1141075100f0401810f00d05070b03083c641d0390482c004d612a00a21807916406d004e40c0c41d0030b450912032010040e200781c03107541e111420104058108002c8030000c0c070447d40080b00300014a44124895600105581001e81c40c8805034a030903005030078290002600002d40c2c0d030362001103180004201407003810a4404004002010041c018540b192840012507644208611000624150021540f083c180d409542021448806071403e683c8281c000b65100b00340450304605441c00e204800d005103803004101103105140500150101a00030030450500004094070010b15010341140c00e0100703001030007004 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 80755397 1106 80754291 80754293
    0x30c09020d0204180204050909010209031018050a05010f060605192006040308070e090402030703260c0304090e0f070306020f0c0318010206060a0b07170f07 69
    0x1904550070400010002030b0aa03c40401c020068000b40c6d80b98075041c100321741c3c01d2000e018001d559204200ca440c0030390340040c0b89080e0b008003490104281c0309111032100351004c42180036000d4010880718070f04000065000307900c1003114040070030031107455203000c40309409074103042980300c8407004c1e900c513aa82c080d41c1e5010211602940034104420070503a214200750095808802050952701442016600900e03480709402098900000d6440c16400007035a5084501c805028042c082d00003003465020008080c11040080009035594051100050340d240c0c454814542c50710b1808420554a003004100034400724085401002e01f41d0542d11010000e6112004442c441311042180031050542030002d010103041c0005000d6205200400190510100400c040e10a00100710103011940443c000c1e101c9440d0400c0000c11840106043d0100302e126491490a0a400200d031140c = true := by decide +kernel

theorem cover : BRFrame.Cov 80575541 80755397 := by
  have h0 := BRFrame.cov_init 80575541
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80575541 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 80575541 ≤ n) (h2 : n < 80755397) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
