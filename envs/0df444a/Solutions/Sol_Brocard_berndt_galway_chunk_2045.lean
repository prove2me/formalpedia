-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2045
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:31:40.434679+00:00
-- url     : https://prove2.me/submissions/b6fb3927-90c0-4cb8-b368-0e254e23f7cb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 367625899 ≤ n < 367805755 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 367627149 1250 367625899 367625903
    0x90b0703050313060f2d0513170409050411040513030f0302090a0305030301120b0f010b220509040c060906030b03060a0c020703150b0a06050f1204030521090d05030f0c0304 76
    0x144504002c203404059104020181c0030003c10071200c280a440c0c0180e0303a54194030507640c1145001c0230045180707032010080000d075610460300038250300e0681504140d40101d0304681b007810f1400b403e000400040c00d42c1015100401e403803c0c806a5155403004e0415400340038040c001c82e03600c1090f00b801d02c0c03007a0300078031101030014100030207151213490741031558200740c000b400090307180c1107008140003a420b00207074800c0720385180760314940c100400013455001e980d07211818000031394007200141050030002000703003d028125841c24542801d00c0b4264410521521021030b1360440041005c034424059100400c1000c0c0085c005511010303854801408150310400840c0110040480014100d400110010071048004207504030b41604200090082c2d0b401001400f8042101c0724005408070f0680c0c0c9c4840c1d054004160350780d03560034151200e02c15050204402c49015964400c2241c0164490b40a001c1840483d00104400e8000740c03031b1840140d84101503003030782400143e258042c01c40110341c418 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 367628399 1250 367627149 367627151
    0x603040b09070f060806031606051e0d09050a02120601050105120903090d05070905250f021f0c120b060403141516020d090303080604020a090b0304050d090b070305031306 75
    0x95443e0b2621030200000d41060000131020820700907280340801c0142981d101c0b4403940b9011500c1e0003009042c83c4107501c1c202e103904905507100b104e0314402030156920310f141d0000a110709600c2e490166150309000c2c038204e106460802e124060701c80c0002e40316060300c0068468610708204440e0740950580d0040001ea00c0d44030030828401c06840394034001d00d42174441c00042c403030181000d011a00350750008200f02902000d000110008110402142010a0b02420110584000220100e080001200f01c0c15000050801101012040d80d80300f24810b03445030761007071412484e8400d500280c817a1003480030b074004014007051005c14103410500410307622901c200c2c0c2804007074005406050304120341e603640c0d1052003035010f20240c1d010b000d40c4c18103214614100081d0742c15990080c1020f84042c11140c09183e010818040c010b00440302c1c40c01400d5240c00c02900c07854149460f5545080600c00f0301c0001720594800600700b00d404042d5170703595505d074842c64255134400200c101700a40240c0103403910717 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 367629649 1250 367628399 367628413
    0x10e0a09050a1208010f0b090d0803130209070801230607030f09180221100911070203010614030f0307030903030305060f19090506010c0c1511390603040b09 69
    0x14203c0c40d003849401c880364644002a600d000001c400c03055440c2c1c44849200c000300000390550365013510704072a21380d21502e07158a944403815051412490200000d41000c03407175050010240c0c0003481c59040781e9100442175905491500d2000c102c000030b0112a4015100703214600000303001d0800e451a0706c11307600c1c0900c401c035501c0e582c10489205410000305090350000308038071810980407030001d442a45031400e07001420f0440c1c143c03203103c4a500c52006003030744c1c2d00c402840410190041760036068000b0001c7c81421307103515003402602c0e0f0403481c907442417140028042401e14017005440c40a501074035080300306403640e03c09401901c801806c09504c00d5180d0480e103501d50b81c840048012034002ca10012880c0d0400b00c1407000c496016007000d041c05858500c0c440060310b11101041913400720400b5030300c49803d1090564400145400d034540500403c02421030407890b1007001e02d240400c070725500c1811715a505501069040000249400c9507080001901260401a906802c00c2a0504407400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 367630899 1250 367629649 367629653
    0x3121107180f140a0f020d091a090c03060403051309090f031d0d11210a03081e220602030c1305030309061207020102071b061205010e0a09050a 63
    0x621185400c801114200700740c00c00414016403154440300900c0200403c041c00140d0004a07040c1d100905900000343c80c0d000034070700d204060b010342c0d84440c00403105100e2142186400030050300903440c000480c1c0810000a6030841c800034000c14619400341c0500b14a4440f51030884041c0c1c800324519020041160700040e0054562140c191442d00402c01c3c07100141f40c528008180600c1e261009140703180105001c0050794440e600380c82d096500c03010038420700a5000120704000d00006003180480104034410754100d00c0402c5a84407a03120350786404551783e072054420804090000f00c4004c40c025040018041c20001e1240c2d440404c25001c148420301441d0b80e01403d1342e004540030b440006011038841101850b2990810281c20103e024505000300c03031000c0b03211805030000e44c8034054540d03070105d00090b00030742c11100c0301500300351914100e2a15222800e40035403203106031000256206032880c14501d940c8601030580d01448100100da44555070400040c0042c03030b0b000e0f01c40340528a42440 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 367632149 1250 367630899 367630903
    0x31b0b040c030b07030524150301140a08010e0a06110c07171e101d01020d0615030e250f0f051002060108030306130605060a020609060601020115031211 67
    0x482148a042400c9100d410b40c545450060406862241030600300400e0000d40c1c564003201c6003034000f846500d250100300710310004000d2603400c4401c90455100000105100f0b002841c403a2242d5402c3e00c60001c1c442d03032001d54608031080011640400c3d0080f20221000510642201c51280044501e1900f0310320918900c50803c00305504c0140400c10101062190500522101352480e40031020119004a00c0d202c9076103800001c08291001c564560491142c01c0f0481580007072450240000c540711070880030510700401b01c0d801200940702896051152580c424040c00c50301002c1300018210b4030a21202002204090300b503240701c101030700840420600c0c0605000001010a02360003030906241000384030044101d040120110b400200044c001c41d48004101c075001501500c000d83d04100c1000024010003150b005241d10140001b02860019030020f1020301540d03d420540d011030301c4000041e4203c4112103140c4403047ea114104202085112144c04a200203500b803039101800320351a554 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 367633399 1250 367632149 367632151
    0x10909230106080105010503030c0a080906040f09090201030f05061806060903010903080f07141209010f051303200709180b040308090601080705090a0b240c1203010b07031b0b 77
    0x1103203070754800c000c122080090040900510055010314502001c2004054890703c008070701401782800016080d015072544012500284501543c4a03020b5445109070000380903003030410b078002400d09103110344000c0c0904c501c074098031004000798915143c541246035199001812958885401e01c180402a2402e010383d2003d1440b030750703070340e07451b031400d210360507440e40b00a4a40010030111021041c5945601c0d02260004885445d4030080d50788d844a000c1e001d020040f010085550424081c00003501102000134441803080e1120008101c044860f0407150042000742030303040d8054007080021018583c0b2150145030001c030107001925064030f50f40c0c4c42c900700343c8003280080c0541c030420030348803c140f01307030b03400b4200860203412403034980b000003040c2103c00341004203440d80d00c0b84050103607514484094940c04652148820000c07580745101d0f60398001016201d940c0c064900e0307503644480414101c1c0c0c1a610000d14042c200101c40d10221800f01060100a07804581d013aa03403008214a00941 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 367634649 1250 367633399 367633463
    0x806030a021309060e030f03130c09020414040b0102010c0f0c030309060e0303061c030e0108090a0c14010912021e030a170a031415120c0d0f0605010617010909 70
    0x20805601c03138030304081212000522815507800610166000c00b601e4800c60350003051340580300101502d5414204502d0340554081c802680c030024000a40340e032008e0440d0151242100d040040e440064016400c1c4d589481490000903041d142e0034810a018208030420a406803400007003120b21a519001182c2074002c81d1a0b00c0d0f0f0006c0b0420440b0300d0306c403003a50749800c030b0407080e00c402081c1c07994007a011400c0d00180c0b070f050203038020028030f040d441041080c00007a044201108069030390240e103070080181940c42070003d89100800304588003181c0159862075030261688034900c3c0e0309943d00d04074ad00144406985070155024510100b11a5851401e01c498400030b44c540d01c0313094881c081c0440e243c00402076610b8054501b0802d40c41805110055094026910030300c94003804914181060024045680d000300026518801d2100700b00b81c45020307070320a200800040c1d803a04002c0c0c1f1000c541c1d010340342c03218a50b40b005114002d52a0006090981b1034200b00020032940381c44845035082032221 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 367635899 1250 367634649 367634651
    0xb070212071b1e0902030408160303050723031506071401050f130f02011206090c0e0901080f06040305070809150c010501060e100305060d0804150314160806030a0213 73
    0xd070300324603140d50301040e000780141103103d040c41e0384160110345003080d0343c49201e10007a0b001c4005410b00000c402250840e000300100c0b190652210725010b40103003405d490250004002c00c600d880c8500c10941070030006e070100819117080d580d41e40c01c01e600400685041c0d5401041c1444040001a500d11034110303018802c1001048500c0c04006443d0741d140c1c010038a0034601e08000500001c0380e4600c14484240d0780a103440c0e1004c08000c9a200e000e01256400041c204d4a844203c0c1084c540c46001c08c1c641c000304951050703150b42d8805200ea680c507025a440c0425030003440101c0c002030b000d00c0080400d1849049481c0c180703140c490000c0d03801c8402000340004140c000914888010083c03041d1400341c40d076800d108441c0b42c8104003007962020001d202809060b612404542282d5070b004219241039488884907a9458454400d9070700f400100383c440d0046030402d500040c4805060070054804c005102d01e4a00d44c45504004540304136001e404213406000388040d0034056240d0341d064003d92120400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 367637149 1250 367635899 367635923
    0x3120309060a0c02011e020a030b3001051b3126071802040f1401081005010c0204110c0a030302091203130b0306060d0e070603060503190b07021207 65
    0x240d0b0410340b948070301007800f1039261141058009002902d5018103014002005864000310748080d8004d00640304129803240903020007001b15640546a400040ca501d419141c00e080700110f4075003696000d659000421540494004014040001810359095080c590340800410310160a01a020140f0b80031040b0701c801009014054054800500e50b041d24480c22002840420110752200b555008500410018412603081200715030140c5d0060003180c1c4100c09000c0d0703541d0012080d80c80c50030415011490020000780118502411007040701d6042c1c49003407461816600f040004c0c0541c3d04125180c0c0e50a100111007014100242d0001e640700b41c40c0181e03140804410869900c0307580d1501e0040c6d510421280088216107000c000441c1c840801c4261a0307100c1c900016980e0151040d441407181c40c00c03120a8a000300014008200d8031162410070805454200341901c1d01e0f40006991070420310004450005481031601d030364000340d1803041e2400090986c4032101c095010340e0040c0c4090b44040 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 367638399 1250 367637149 367637161
    0x15070609110a06111b040f02030a240f05060318011b11030a021207050f1f0609050f0f0a11070b010f0b0406140715111806180f0312030906 61
    0x1502c4a00580f8240c100901e9070008030034500c1d501d200400450b10100c510845a003500e1701c031a000b034050000c02840a546a2802c00000c0340100f40185a408488152507800318005c07008aa500c02564a120010081310b4240428041c840c1d0015100c0c5031814488072401100141c20b00c1001c1c01c40701c5c5d80c0c06000030341000c4000200003244044840855800804c4464411600091005881100324502c0340c1c6811203410f12a00300485c2142e07403541402004240715800128840452115444a0041101c80e4440b021102203c4049a100021303505950201c0e5040741c0c2c0003200ba90202900c00301040e03007258440b1004054228100c1110005690310051281303410041401e4003803c02c00f94294285403401d4801041c110480030f0080a144c4002114000d1080d120080c20030b25280c14800d002100f041c0c1d40701115a40929004120b400e028100300c1010f191400455a140340b03040300114030002d682e82000050503e010b4011761520500240a0050441c24082c506ca00086405003030145002 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 367639649 1250 367638399 367638409
    0x1609030f0b15130c0e0f2101020415020a030f02060c090d020a03021e03100504030804020105071b0311040c0e0a0b0a120f24030b041e0203070b030a0b0a030f021507060911 75
    0x15405c1e40c1c03213a40d04032280105500e0307846070080541c1d4641a40314098146800843c020700c2180c0000c0003115900e132500400640000d60f0307102e44c130301c01c1c0c0e2280506405100201d80383c2205892410302c03000c04000d110841d1605903102400309000404032100c3e04d0740c1e03a0004000124588105034000d201c1506100c5616040c803141300c0c0c80d40211001c2c425840e0a6800038418000100003e040c4540419180c0c10311016200800d008540d4011009040b80c990a0103030149100140281c41241401d06105c2c0e130a120390300c82e000120024090341c40080c2030600380c043e15001000b11000f04000300c0b4140940082e40e0140011403603500c0d50008040b51301005400c44c042c030f011100d00c81100798080400004001c1c140c12540140c00c10020000c0c10400d003000c48004040f07180295147c42a2040803c40c5101c100083d401910313054003c000c1280001c060183c40f940b10300c070140401f102c81610502605100508030f0710030740014450391074244141d07203040454000410136280c0c54050142400a4141 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 367640899 1250 367639649 367639667
    0x10c0e010c1a0108060126031b0a050a0b0105280b0c1603060902090606030c070807060b0d0309080d020111040506070203151008070e090309010c11030a0501051609030f0b15130c 78
    0x180c84140e050107c1c040c0d40d940d03524410440c0742402004888801c810340c10040c000c0036030881c0e0003400da90a2003e1404e140d2a0f208003805094442d12070300380203c0985030050303048021107002e5002d00e08543d00d000319002c4c0b0b90308164030301c010034020707a4502404120701100540180d07100c0c3d000012911140d005005600c54000e0840d809403908109104e05403141c1c9056401541d4032035102651074281d45448000340103040640c50700014481224402c1640025030001500d20000c1113489001c680c23681282a2401c2080301500c5000801c41400305081030f00003840118000307804c40710800344804103c020a007084480d030210301a606428042c4c9081401450028105d00c0031580079070900c001d42540760711864070781e941440005203e01040240d5201841c500002c02004d580b0410640c0c01c0c400e0280a089404110601c4100c45001c03c90740a03031421800c0d41c0d0400007034611709015584d20b200c1e041e0094000c8484440816044c1540d54800d4070031460100e07840000320b151014010f020b400c1030302d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 367642149 1250 367640899 367640939
    0x10519050606120606190e040c03060f030206030405011119080903131211060a05040302040e0a0b16050d060b0703030f09080a05090414040501091202010c0e010c1a01080601 76
    0x10804040c880c107075440c403041d0341e000301c0141210f004580f80c03200007848512441811005003100c0451446a0b1038008030011902d070360030340e42400081a003090807012241e00707004102407410440c07002c1c000741c00e108014683c01032040c0e00000e040240510304034247c1d000500720011800060907a00d00207980510b46540144501c0011402e200c410341450b480040c1c14003400c680044031001040c14041e8400a8030b0312100c01400595540c00d2810f0014003552003404103a003d54140b160f03042c040c2c080002c6285141c1e4021070116580e4a403610380d0030701c2c800c0040c00c01040140c01e0100c0c10700d0300180c1c0304120041010f2111b207a035504040c81c000e0181d07000e9081800c01503113010035400106200d40111282c40e2907501d001903075454113500003802040704040020107203050804000810105510144280e0f000d24086405403803030f800100d00703079081c0380510000035907200c2580c040c55025410001c1d090b8420070400e108070003803880186d0f4a5600b64070414244d40405c1c0108100204580409442c007 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 367643399 1250 367642149 367642151
    0x609050f04021f200102070f140c0a0e06120703120207090e0a03090303032c070303031415090606210f060d050a110111030a03020403111008070c02040e010e010519 72
    0x4584a01070039414044465001300b00b59400d410440078429070403205200e80c0a80c1d400203020b40c0742410b000100310717151011034500c11054030019514210221404a40208020142c0386e075450f003c0c010002010440c025070f5216001b0080300040350001c03003510f9028a64010240b16140074000340070346034003502100c0250071041490010a45c0003071100190380c0c0606020440c03404a40401c4003120003204440040b903400b0207403401850001c98208222400f0780d505100c2c00c40f0000c0520403800058410f510b0000c030810036004681415203000741c0c000340003008141860103400b8060340008003080f0811f0080d16403410000060143c150594200a0036900d02d8004603659680e10350b50440b00c138000d0303c100040c008101e083e030b1155540c0e058800c1d0702419a80c40d0b15540e45c028001c0e40160200f1691021903903d100d1a5082c40c035606880e030b4115681e0b110380341e11001415590200850340598020b070312102c0d01c03940440b007401801007855070800005a5458101c1071040d100b582810b22003000d03 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 367644649 1250 367643399 367643449
    0x20d0c1103091002030d1e0e0304050d06051003080304030201140f06060a08060a03140d0206011d01090c1812150218120c030a030806040b151c0609050f0402 69
    0x24410000556202c07002c10b0710010200812a00103918600542060b05135140c107205503842d0000003801000042c080030041400002000d600c003545038051409103980100c250b008050200b1140c1d0402c0390481c040d008003907003064981d2291203584c0d00865042c0d0140c0e4584038802c80d20000101203c0d8401400024100b003070034040700160181c81480b0b8114100507200c804201155a1488028000d40c1e211000d800c4012160710f055403202e0f894a81003016001c0c04000194030341006080800c0403a0034014009680e0800d2060002408101c088204120141c0400c40407064503c0680019000c3c01c0c071180403516461034071010b1400d05c440c007005042d00600c0024448500c0c001000c00e2076404942558440100941c210700e05048062840e90500c0f81480040501d070f04a503407680154002d59082c00200000400e000407640c0b500790070800d60504002c0c501c2c07180800b00e102900900d0020010170456501d001001c06d54105540b031682c07400d03080050204510301082100c50b07074101c2480b02300007 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 367645899 1250 367644649 367644677
    0x905100801080c04092102010e100e0c04090302150c13060c02300a0308061203090108060f0114041401020c1e011211030907061206180f0209060d020d0c 67
    0x1101c08110119000c0c64480a00b1030800000d0a444c42c0b40040300da46c00c86e411000584c1c000e000c1c003082c00d11041c2d14040d200300c3c40c202d211a8001e110f40c08a000005004035411402440000c10084406404601400904485242c100d540d15402044c550740455150801900784002401403640300e031080c0464840300d94011f84988010140e9042561151524612031601d0000c550f0642c01c01c42d0803900894004104054202100501440f4241c414220461a070000517541788140900d050129600b00700060b210720b09402c0101d4a0030041c0360007551101c107021080b0082c0c20640291030546180f0413800b149507410005495815001c94040319201c140c020080420220035500c54108040c101c0150304444040c2c1104846050b9016190b6603450400b4000340c94050600403030740090310396800e0701c000615601498003540c0040b42ea042c00a1110000385e00180700c0c40400c461055003e00030703825603a8444000d070460300c1415001507514a8865180307801c540d00c000c3c2d14014402d5405010740 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 367647149 1250 367645899 367645903
    0xb04050a060f030b06030102091002061012050a1103240103020913020d0602070302012c0601050102030310050d021c03020601090f0507050405090613111c2f070c06090510080108 78
    0x10481c4d07000440d040d001c2d21403d001c41c2c0680304808000d50009010341000311004c0c0d0016a40f031080604c221258440350321000850078100403440090000c2d84000c19000110750405004690710400900300e501c0740308810880811103e148d500d16904c103810b4030040081d4100a040075a0009a06411000f080e0895000890031409900060308255021a80c034007098000d600c10010b101485c0c0c0c014100f20070308144520254009000e0400364010b00d000002c1c03c1d4000400e0760b0080000d8442500042d0804007804505403841000b0390b4000d1842c0c4203016515200500900082d0080e0f02501c95076041c1a100300c1030b5002c07404405c040071300e00000c010701685d00000369001e9410403101c0c810fa6880300d034002031152000c08030a00d001443d04e50400000210078008113a10036000a14070700140205030140200d400c50524100c2d04000d52415514a040c0d01501c43e110200460019081c0b0595848106040b030460700500c0120359039920900507442e00e50954060f101c0146400c5c1c0240d810700b1001c40d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 367648399 1250 367647149 367647179
    0xc0d050c19050d02070c0b0a0e0d02010504060c0f020909030c12040b030703110c10050604140f0601050a09030c080703020a0b2a0106180f0b090f04150219030b04050a06 74
    0x600b00312020503c4480200b0940468800a80262010203040c0d2a60740340412584030140e03060228103075820042523424502c842d0340c1d071640c0503154281824900281901c020401001c00c0360709c401c180712608010b0f40c546050b98001c2864900030750700d0b9031425517203518004120800d100c1411003404100032000e51041126804505882d002c200705201054000070b034050601d10400754044c44c1d114001c40c81d6241d000c5c1c0e2040104490070303c5a00d001c520072101c240c000740c0704120010355410000700d055019038010140420f007860401100c651342c0d200c1c1c0c08103030400e8124020076007048804105520f05043e03200301501001408520785840109151001041c03045404402e01c965044c40c882075500307501075030083c83d082c20340464070744401c0d651400074001d0b212200340f141d16118400845040c003104840c46070403200210030f82501c1c1c984071562140d102000c000c40c04d136000c001099105c1400340110010390800d0724003180018100c07042105a1b00700820b00e40746640f62078001c11004000035058 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 367649649 1250 367648399 367648447
    0x90c020a0b041211030a030905071208030103121704030305091005071d010203041a130e040506070509041b0c060606050a0e0423010b07060f02070b0a020310030203060c0d050c 77
    0x7425980811860130b5034905541214020580000b288080728107405801c400d056a103c0c40a82d04090340b04c5103484048445240c000c2c086840a20061001501013a44002c0b0448941412140700588181e040300d0904111000c60000b0b03160014444010001c114051090400400034003448c0740c4400001d103071011340744200c0340c0d004d500e52440340313164002e000710b0300500081c1c0c2109060300d0140c58444c4441d88001c194207030a403502d502c0001c01c00c504038026030207503038041c0290629407180201261542c010348016980316a40d1201c0e8550009595080c1d2045143e946414010f0f11326400c11800300c81c050b43c00141400810080340108540c0300031001c0501d14212400101c0705220003401c1140e030700102d018440f480b00c7e01c0010800098000140400b5881100144602c0110002203400d030702800c2d81c010300c00c0c0424404150b06034129005581d10424000e004011103a9a40001c1e2600c0c406880201e00b02000180040740041103000c0c0951210300c0050f0303580f0780340020240c004040341000701 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 367650899 1250 367649649 367649663
    0x1e0105060d021c0c0f050108060301020412030c290a0e0703240e07060302030414030415030506040b0409140706030e0601120320150a0902010c0b0a0b0d05030301090c020a0b04 77
    0x19001901e00d010a007000140d0484c2c4000754a60b242e001801030584180600c0e070224804a000a510b441d050080303a0030f0720328480c440e106258955609031000d00100348100c491095614458292805152401590300d860007c0c0e001e050801003841c23070449a590300c0d424055044204d007071001c00e403c0380718211540e952030345104409000c800b0710350090202d07440c0c00d80c82d030240701d03800164203074150080e50081c0e003c0e005116400c2c103002c0c155a524412485094004160000100f90142c00380c0d2000e40e00800183c008030f03420010318006002c8859590f000c550300c00c006880d070b0345181000c1001e180a00141d050810080101d6a0155a2000d05114030b03a4903215100c48081050f116076000406a00d417081c400305800d410080c210b0b00c3c0c44c001c4043c464415900c000080c403c2d40140541c2d4080c41d010784a4580109181c1c803600e240a000078040d481c80f80c0c8418500c0b105440341e500f50507205000e08081c41d125410074041400b92070252000d0f80466009207402c4010030b0b00c0302e19060300590701c0302e0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 367652149 1250 367650899 367650919
    0x6060114070b090d0e122e05040b040c09020403030503060d0305120708340f1e090503073002010c0206030c0a021e03070b06150c1e0105060d02 63
    0x20030010103214240380100720440e03400900035201c60001e203c4030f164403240c48100310301e1440f07420f01c03c8210784c0c1089007003d079211068080c81418064244109085240e1300c003060304140b03e400a0035140103803000c90303080c0c0c020001c01c802d200c1000060390180c640a2070075883c1c5440c44e2001401c078007002e00800d214040036000c1c40c08142c000e00c1107512103060511800311a1078458000b5200b039400322001514444a0ba60176000e152400c0c4c039444591030044403803442e07040507844c12034211201c5c05106040c00a405106032400040203010b42043e032050b69031580d21418841454280809903000c489030829800c1801001d8864150060b5001502d040c181c0042e0b10070300040768000c00150004c0d4206400009011005071040020040041c1d03640880d00d800c1010001811107947c00109115144c10901170100000d0010132040d0304039034020007401d0f80265140103407410b0380c010208120307150b10107540545007042081402c2c1c44581d801c0001c02c502c1ca45940801c4002c3c1c5e000e00028440c00d4845 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 367653399 1250 367652149 367652177
    0x90902090a050a080f0c0f0132030916050306070f0503040c09181a01080601120503040b180a0b04140603090a05060414152a0c0a0f021011060601 64
    0x35114001450000c3c0204101c0380d03118816612500211000401d901039125600d0036800d01c98103a40c10158103175030f001030305180011048103598002801e074400d0001210009c440c1c3e40c3c48400745025070340103000f404003059003d00000502e18694030860003034000108110015801500071800c7d071a003414a10354030755691030500c80c4001c0b40e80018040721314100b00300ca4214007069480e20417a118541c041440d910350408640d10540c00d21806100c1d5110f00010701a51114007200341d07085126100312424076132100e0184010381c112110140e02061443c80c04049441c01d5041880104a128a000d103841e04080c2c2d40d01e14009080340d428024000007020410350b420400c500302c41d00e03410405690450a0921708150300f9415207801080e248101040d2500c0d0a2205d250140070312580109111008031509482c070840e00c2010002c1d030040420f2007402c0c0341800038008020041d01c544264000c0c890903204000701602c06103044810030202c506180302040340040e2064018400b420100c41a039400 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 367654649 1250 367653399 367653409
    0x115060c080f04031a13170a02030c06250f0912020f03010c090f06090617070309050a05060f0a02040501170606040f090203181504030807050d0c05030609060a0609090209 75
    0x5042c502c0811040060b0004c00e001e811480400c00c0204d1071500d8416840e0400104151109942c021704282407a01d01b440a03034401c2c000401c4d0810560068070300704401c80700c540307060442c00c4441b090614010000c080203003118800b4107202c80e0030f505000d981d001d04880014507050441c003e840901505010007000d5643c2c0011004020000400038000310780c6e1220300a01a03d003a104102d00303868180d00100c1c0844c019080c88050310300300e81d1081c00365480310a032590700035806413100b000e0640c0d49240c000880d81c20321524403114000c40090140d400e05d5140310651a10090941341c446d80305100500c2183c0e444520020500d08043e10080540c0311800001c0451240c0e5000e40a480300d446000a00500b868019511a581d4185013000200340c142d10103499505c50b050482082450310002000a03001c1c24100340c1082d45032a000f801d000081003c10219203100ca60703400450408410401145012200390307900c0718082e2041e0002070320b801e6000d0b2607900c96018070008a40c021440406540350 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 367655899 1250 367654649 367654657
    0x513031e03020720010f090602031210030b04051c08011412070f0f0306050906011212120f02040e132012030d021c0204050303040b0a03020903011a010e030115060c08 73
    0x4d008034494409541103110551001d503c041d0103c1c09060f416800c1500a1026504450b4030341c024501d81070f02030048052404006116a0081c44006008804907100306034445c401d510500c001c224200043c6060348142c0c0000c0204010842041c00500116001c01007a40d50801c0613074489081d100101c1d001400c3c4030068001c441310b0f6629640c001115400c01003850300301da018030002c10198803164075003500c0301c2d824000e000140b10803035540d80c00143c20310740c440361001c054542a03030050141100324040d0b0b0648003425903040e801090038020440503e00842d0040700c0308038205c03c81c1c5503d076a04c61b1031818517045d03481c500302921102002c50f00d4010b00410300401e28825280d03940109132803c4003d42080140c940d0000d04406c1c0c3c0108000306200711804d40f1001030086007854601410345106601c1355004508141d000d01904025031002d010782000c413030246e0101d00071503094034001048845002582c0344207a044c00b03035403071854001c8100f0805444076480c0040f220b242a042c00b40441c89 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 367657149 1250 367655899 367655903
    0xe01030b060904050f1b0903030a0e060d0f0912020a050604030807031401080319020a030e04110d052a0702130b03190b0702070603060303020606011808010e0309040513031e030207 79
    0x3013003404020740103d43c5200188150380202d04611046a003008404050013494915a0503034002c01441044a00480c0032988000008082074640300c403484d0080c0c1a903070440b1022885980386e80110301046074100888442d88100d01c01000c046000d52a00c81e91514041d102405020481010604035031094008600c140c0c1c01016080341ca503540e2070036a591ba40075160800520052071a108080b5201081340d242640e0140d4400c07003d07071021420440282117100002c10380b12401c1100b08110041400390510030101e0f0a00359442c0d0b5041521403a0021000104880800081100400681e00c4803035106600084100c0020410503100110b4903001010742000c0380c850051030341c40704011807418030300d100e0b04e11a03080d40c18240e9203000607410707601c0320302005025070010000180c0d254420007071550b003030000c03100059250795600340b03190850318030120f400059040064406c0803070074107004054110f4105c0000da4403032016520700905183c4201c1c0203c1e0301c1c18041001d0701000d07105e6015204025 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 367658399 1250 367657149 367657151
    0xc0c080a08060a26010b0109240912030f030b01051303230102070f05010c0804080f03190608070602072301050a03020d050a0603020310090b0c0a0203130e250e01030b060904 76
    0x480d2404c1d960a0710100c91131498031640c00c0640240e00e5501c1600c280c1d04540400c08241c1106105c08982080081e07201901c004102162100161580c1c0300300200122030b00988400c40540b1102d400141958001d40182d4103004041150340814040894014116138100090702c0300c20041b080c2c41c1c004865805801c0c10151300108520041c40a05c54036001c1d8280700c3c000803c4408034075035094072001001c44014001100500c0702400f080c0103400110341c4510314201307a080b24046441554110380f020f030040c1503164030041017440010340411803140074009040f4400078800d941031040745070100c0c030781d15541041008100800058002d8040e5480285912000c1c1300615001d6422401802c040c40180c0c0f080c403039180c2c0442d90304000c0c820080309135001440c0d500d0503602c03030424114641c000c202d4281180300820280942501e480c015a0180c201c500030000503042240145901c003042c10b17401e44180c150307106580500b5811400716801d8103400c0c00c02085800c21600011101d00800f0f00b407640003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 367659649 1250 367658399 367658429
    0xf0e03250f06051009090b04120e09010e0a06381213060f09050c010e0f030a1505090d02100b01030207060c0306030b0c0a020601030b040c08030a02070303030c0c080a08060a 76
    0xb920b038009522404071590100c1403150795051001c00e840c2c082da0003900308280c1c0d070041400300f410017010946148250078070100d04015080898800305003603002c6c2c544400c5280c10700c8a0780301d150140000a1250000e841081d128458220340d11407030485902c4000c0510b01e01e81c0d181c00c2d859100b81c40100460300141d03884c500e171108441d43d02c514904400c4600307626010225040c0d407554840c074070410381c20200800c035422802005403070b184100c801103980428002e4691925a4007000031080c018800c01e61800300400010000e4103552000e44600800e804c003051041e080341e40001ca003140000544000b2801e032014400507802442091006130629080840345007195030107400903002c607880f48170f51800315038605103401c1c09801000080c40c0142c1040c001000820b03001c1e034410b50414000d0303000ca5070035a030f80d0014900c0e5600a141450150300035190402c03e0603054802d06e4200781c054107000f40003400f590b44002051090300c84040c03e100c40b000206415440e00444400601180c1c41941c041d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 367660899 1250 367659649 367659653
    0x30c07111306030614010b090405040c080a0c0311030c010807120b0a080616090515030912220503070e06040207050109060c091806060503012106140601030f0e03250f 73
    0x14010070b0001361110f07401e100710f503100820800340c0c59040b01e0014211038206030900c010000a0503000e00140d4658003803044c04900c40e9030a00032080d5445c4184489490b5910314a0300e038410030101140c2c43d109800042034a013007a42c11929295202c4143e14040800d1042e8620103001410044c18003600103d85040c0441d4030000000c90500a030f40c813103409040b6640080080742d4420b01801565000300c1d80a0031031107201ca00c5009540c00040d5007080c1d501a60300030010032601e4000c4038482244501c51032107907080b02040d21800c0050700c0241c0241c0402420300d4044419800b010300391a01481e80086e4000901c0000c2d80960390303841e4040340600004407800c600804030011400b40c00c1c07900030441190510301401d8031401045807001e40781c0da425030b0320304480861009a00400802c09102c0b00445000007803080c410980c0d103401000d48207400f0700700840010100d8026035503003442c051a29201c2c1e80b02080000030343e54991110f2a0b444607142c0c100d02c42214a2585113802080f001401c600c10302 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 367662149 1250 367660899 367660901
    0x80a0602040305010518120c011808040f080d1d1c03020105010602071d04060203041a0f0f0604020a0207260f1e070609090209041404060b0102061605030c071113 71
    0x2c680c001d81c02482075480313040c1c40356400d004501c1d00a6540d4840c0d1021140601910080c0800c1d000002c00000d42456000309c2e504142105a4100c030300001c005414407203040d003200810040c0c040c0800501800c1c4d42548094041d4070a510904072001901d0a02c804590319454812940b51801e1b0203078403140d03100d02e00a8080d0000307010311005400383c0741001c502e1a11344501001e1000c81e0224a0380280c441d41c039114001c2d400034106560001d6001040f0040400c2c802d000390050000700e020710014030f01482410442100a01403d00c55401003260007091a40007881409a400243c540c001c10005c4000e06007181d070315040125030a01401c42450015500456204502160810b00306941c940c6400c1d07107619200c1c0b600881000c1400c101d414442c094055000e000501d201410005032160b405480030b180c65001c44040342c20340d445401030111540d051003083c3d041050398200541c0030000d00c0d00903006000003016441441000300302a028082c4180b800c4596280140000501540300c4a07208 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 367663399 1250 367662149 367662157
    0x9080c01020a02100516080c0313020a032603040b0609150a090501030c15050d0f060506120402010e0301021c0f061a0a180605030402010e0a0302031006080f0c030303060d0309080a0602 81
    0x13002c9454a400212054140400020710592a41c0da440e0b5581e525002a40b0302c1d0009082541c000040000180060b1154000407001c4d5000e901458091081c00030f4810260b2202d1410056405041c0188000204e030000955045801241c0100d244d0360b8042c000310b031203692014000c0e8000101d5000140c0090598015410b0b64000c00b48482555280d841c40d0350711490180f061400582d08212061912103a6842840000d407440d0021a03005e940350001035194002c580c4208a03121031805010031580c0004003540500020740082d410a100e4010034200c3e200d4066170004901d031100b102d400c2141c5280c0c00300000c0e04604c94000c2000c02c0700c00050886400031100103011070006d05c522140010750f41c0e4070904498590b99207501d1540c480d401143c000c00c4500c403454018101084c0800169400c1c820030f01c0541c01c0c501d0008040d840d14205a00d01000c0c40080c816a4021003900d20441e200482203d07804481950005001c2c5410314040b181c0440f07551120140d402100d100d10104810f6070000c0c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 367664649 1250 367663399 367663423
    0x3010b04050310110a1b061e0506030703030e01050708090d08071406010f0b2101090b0a060306230d0605010b030f01050405190f060509130b010f1809080c01020a02 72
    0x280c080b49207030500303241110400400001e800c01c1c00e01101c0c159520030034061540a4038503110340f440307108540c0e0740804e507048203402e182903007405220000c000b10688a0270f64080c1c800c40040401c40e2a540700074107541d11104810f8100007000581c18240710001084600d07480028109001c000d038075042030803c5802441c001c0700c00d5003020248031416900010600e040e00c26058061514514060901c90315602c40c8900030301c0502000d01b1102081ba410382c485000b481c3c13070030001c109003002d0010081600465005401450714054044c001d81d00c0d410541c500761800780c00075081d0786181800050301303030400c132000800050902c0004200704480c02c000d10300406118080c40d855917200d00c10442501c0d01210003550325a9824a981068581c9800c21804860542c800185440e159804168090012103091007849507c440f480100855441c509005145a00e40303041560709049a041900301010103d9003d103441d00845400c1c084000b04640090110400071942e666034220040e4807049400c0031 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 367665899 1250 367664649 367664653
    0x2103030406140f01230d0605010509070306080718110301140f060903030a08040813081e011107030309020f10030902030f0c2206080604230c0a09180803010b040503 72
    0x252010700b2054150041c0900d840090002042e800c20101034828002480200a0906000121403103600c50104000055000d00d00100b20787d8104000e110820074003800000401d80f905a041110f001d000c00c4a406031106e002d440380031721603441e0308100581402d401c03034200004000b00004c1d40780010f0f507400fa0170780015100b0819602c41030b8200000760203101e82039605604100030407074039240b2500e00194041d105122060505140c00300641c1c000e50140c001c580198030036140c0c030004100303900412805284400c0240704004400e00d101031079000340c0d40d0080501d5100c10080c821542c8045c1d420842c61000f400141a045400c1d100801070300034040140d000e03000c2c040314810090317804100d00804050192a4103121801c1501d0440c06020032940034243d103a035080080b0308114144000c0e03005030b009903000b6519542004100060300c4800400540a5002e18020410f940300c07002c1c9102103c015850000b14190308075100c41c58041c4101c4010907458000001080103058100034100b92841270342 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 367667149 1250 367665899 367665911
    0xc0304090b01090b0f07060e010f02120901021305130603082a0706050f07080d05180712031715090c04080c011d1207080303100302010e091003112103030406 69
    0x10041d0380c1a03c0d0740c007804000d41c20400030302420080902c01010043e00c2040005450b01f403801e80c2c03070300b114100c2100890742c5c1d070009043d44620070400702c1c032500200e00e000214a8020010b40200c010401d80c400c80b80030b090b0014a20035681525030001009613004070909503a104907551190030450301d812040c004c450340c0341540c401c1843c0043c1c283c01351282500c0301450043c4140704d1000c2508919070491310300004110761828a501401418000d42c0c002e0788000280442c40035840c100081a000003903180b10451102e408254055145404085100802080c0e51500d00d0b240a00da620b200015811618a505000418100100078811075800009440d9100c2c032000045814121100420f00040c4945090f003103e03161142049108000722400c56080e00c0c0c0d904145c0d0700755003044500b080d8084207210104155604120108010201101e000c40b00349081c09180d102c0f60100d0101504024400108403daa02c0c2c2488141c5440300ca1000d81e094103640f401056540da2003120100c0d4464246a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 367668399 1250 367667149 367667171
    0xa030b061216080c072003010e0f06040b0606030f0406090c0909030c050f0f030910020f060a0605150a0c0311120f07060e190b090a06020409090210020d1704050c060c030409 76
    0x204c10b56001aa1040c645220300241c6142c3e15030205c81c0c801269490355942561040901d400c100c50800e0130a4072014205515103414014000c10b03000380b9580c050402001000798000f10644600d900583c08400090340c0d019604001d580d40c1110b0708000c5806103824810380c18540c0203d1031050351840f54041794003503d51903070010344403900a1076004041d0b0042c07101c6500c6182080700025034607858811680c0500f00180d10318134208056404a008550340d00c0c00b0701c41070070503842c5c428040303400700031143c5444009580106082100c45010f0200410992618040401448100d0000015103030094a5008070343c80103400340d018180032500a840e140341382c540c0480209000703101c26281521081c0f803014548804100c071000414107942400b90346015000100c2601c00751010701410080014004031078410302503821203104011003950301183d052031005074441114950140807000051880d10345280c42450200088481640040c3c04100d442803100f000020b070080301c3c0140001e0102e00602 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 367669649 1250 367668399 367668421
    0x50618010c020c0d0f05120304150b18060a05060c010e060a05060306041401060801090f0203060a0b13020d0b03060702060601080f09030316050913060602210a030b06121608 76
    0x2008840141c0c10002c601016458000344c040c0300b0b0b5020f801001e10742000ba541d483c3c00c01d071607940d9a841516010080c0230610141c0e81c02548000c5500c10304200459150001a0946c003040541012810200d40007401070380b900700080000300f8028058586541d0141e003868007808061a20b000d05124100010300034003020b000f07181c002c00c40507000d8412501d594172907201c58601117020f4015507407142c200050b038110911601c00f6003401000701141035002da10406090074809801061000e0070a24058080e81d540178025042040e0a400160780308112901c61001c0d080ba40801a4140100020005241d401260640c42410243d8904016544441c14901d01040944451171036600034000545511102e160034a25210a802e1507400e2164400015a4907042000f601a8041c0c0f2a01d04000041d01042415294440300f19036544280031401030284c00e000300355081003003546a501440c180d84401c401c0f507869080e11100e040551800c1e03411007100001010040001800880015a1103050 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 367670899 1250 367669649 367669661
    0xc230307050a0504021b0703050c1806130b0316092304081207110316060f02090609060d0923070b091008090316150c0c0201120c14040305061801 64
    0x2c00405a0a04000a00000b07410150005c94000650000d004c00f2140030403070540114403c90080c0204810358082c001e2440411a80701002d503a50030030701000341e440e1000186c0c03c1c1c4403050000303400e06880340000e1412a5294145003044080c84d000304c3c00b0030343c5030010880708410880c00b07215030454000a1500d08000c9401a1501400380201e00d100400c070340c421a004502071030400038111000c1241802c41c0e00c6080203160420020103100e04020b40c6018004541c401c100085080c850000041070380c80c4240402d07640b003194002030050030440319601441950b80c1010350f5502e803811030707140301400c02d43c0b001c81d007091441039000015410030100c048514824011304441440a80c620003a07401040107006924580400e01000041e40d00640c9440c0750702d030040000d400943e03404030002c001c413101c1e00100b10411009044420140c1d802109106c41c07140c0325040082c82c41d030444d4080b1208501d0b0342c42403046882c0010000140407000032414005c0381c0c14401c00c3c2201000302840c42c04c0307c034 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 367672149 1250 367670899 367670909
    0xe1917150106052d040801020a020c0901080d030f110708040603060909031e030605130207020913051507020a120c05060709300605040f0311010204080304050f01020a0c230307 77
    0x11003000300b0701d0610440402000740340881c4c03240000d082c0400143d240e80350000c0d0001c04481e036000c031350507820340d9040049030030b0300d042035401100d90750500303c10300d480302c04000c0000103041c0c07035000031004100c881d400075407019144104661a80628680b60640354003034890310000a05140012440b500144130f45a0a41c0d8184c031000e0201c0c1c81501d038084801e6410030f10206043d40c9610008070b54503401114002c10501050060746c8612500c1004240c031005801d8610461420b40f0900006000044a207800582035060340d07400c0d51401c004a00c2d04a1000300144043c002e006c0e80002103400030084c00b020b9100704181d410310394501d64102d41301d4200381703c1e444070045800d8100c41c00d406050908090b10070880800c581802c1c00303440340310a4400507a4111844400d0800000c24194882140100310380c3c8500213520780740c50441d01035500e000d075014048c802d00580c184188a0381c0200481049035500616404443c0e0380c414803034001c030304004443d80030100c0603c028110303840c0104840007521 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 367673399 1250 367672149 367672157
    0xb010519020f01150f0801020c0a060b0307150c0c051207050103050714030411030601080604050604030f0c02041a010207140315100e0a09020102121602010e1917150106 74
    0x24211030641480c0d200d8600025055004070a5210700d03181d0203028109a940700710020250091401c0c0948001c00c0e000d90000708203034414802d49012500109488044607003107003010034600050300000303017400e99503032000d04488030402850070036a411111189000d40212140d446d1155101c0a114900302c0707000311a1b1954004030424410303507000380e000a400140c50310701188074030204d4151540b01d42c010713202550041034200c1104230905d020028517026000603406400103003019036506a03240c401420041c144100c51142e5000c0b00d102e42800d00400e80c00038000e114901c0104017049000c00184089801805000b0000c1a03a031208042c05105070720103801440e0b0b100c1d00d6075050007407034409050403160317100030100040c10011810f4031710f000703200c800000a10000c440c0300181c0741003100c41c104e020001d801d000003c004c403040362440f5109602802c059102010940016941400c042c002e000b00051194010403000e001d9010744400da88034000311800803a104001450009092188030001 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 367674649 1250 367673399 367673407
    0xa050613080910021f02130617040b15060334050a11120f0301083c120c1b090903040b13030203070e190c021903020304050a0b19030b0105 61
    0x5400e02883e00800710b405481500c1940c0d03038440341003002c900e094000e00c0070300c0d0300851002e03a00007060045c0401018070341019420420704082e0380c03400d400c001b003000e0407644603100000e04c030340c0f805900da20f00f81c1c43c01426280d9900d409084258140003001c1c500c603a60705420700e8603108900b00900b0741d401c80096182c844c2001e1021604441c1000c203105440036902032a15050030070a82840a084640303e0895103607140d6051038101c07840c06200c4d0740004800c001280a80e0f5046810645074914042d0700071450fa200104a1040351604400e04c00c4607024070400145504240c8021400c04e02d0441c030003598800324031001e0100b0204503400d80b02c2a100f500200401c0214001d640010712410041c2ca07813404641e5a20b40000b82800c40b190b2102a03801c0610b000c011601e1801d074104100050314107010001c140350035100a5503000304a8010b052503070859412801c1c10f008006a400a0000818020784561141040030440d0000c2001d880107480d10141d149083d8003e00a40d812800181d50701410 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 367675899 1250 367674649 367674667
    0xf0e090a020915030c0a0603051801060f03060c02011805030415050c0c09060111060702010f0e150604020a0c0c0801020a08071112032e080c0109050a03110301020909090a05061308 79
    0x26940c941400d03590620900504210301d8541c881041b0050019840c002040d03d44280d503500042446044020141d1414906103c1c00401502200a80360402c00000e21040c43d2802680103200300300c184400b07400e08100c044100900040100b080c0c1318035081005003000e0742e02042c1d6060040b00c1e074005081c2c00c81d14030302e01c882c104103035841d500000500d00000c0314410b030500b607820000e045d41e0400050351240c0d000075907004c02c1d000d6203a0180244005041d2031a408141141c0f811020300018820741c0c0008520344443d00c956518021030380c004040b84c1c0c1c5180d8809103d8003e500070704c2c013500840c13a98800a4001130081000e10340c0010107501821f4490071802e07694000d5400102010480c024030780001da0031501d900c8211107030400d14134804811a0814510324034081e0850400d03410030146000500260b10344d100c929040780d40c000e603104080c0020800182c0a4000c22000e607400110010801252400014041b507000b4040e10646405031103084043c1d9401c6210749001d0305200d010001248 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 367677149 1250 367675899 367675921
    0xf0307050a090c03021225052106010905040e01020702091b251a040b330a1203261003030e040f06060e01090b0c0601060c050102070503040f0e090a0209 67
    0x28014813458018500361400d01010034480c4156007199100041d0120070045c030082000c0c0c90740c0d0741c556040550800540111407031507114241c040e184921341c02000326903580d00802c400783c06810000d00510180144034040e9000b5001214107a12600940c00418500c0c1c680301c0c04c0c80307114008a0001803800501e060340303001d1003410201c090120380c00e600400b40403e00a180c4001041500a00100c090800341490011a50060b151000e018a03001c0320300074601c40d0402c2040401d107202401e03140030104100003603107803189910445881140f14103940c20507038092541c5060050b00c03440e40307444116030400d01340551340c02c840c010400601b00400707001180c041c1c0340600500f46d0043c4003140c42d100784441c1005681566100030302045000001c0d90a640c0c0000c01d080c05041107505050501e4084094155240f0040c4140c00c14031075410030301e0061000a404658896070000216035603a84d482c882500441c0d09886203215a000c100c003ca8142d060110781400d0150f001420301d401901c40c441001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 367678399 1250 367677149 367677161
    0x5030703140a0807110102010e0c06030105010e0a0e090705101103040501120e1501150c050601030b27030306120102070c060e0f03010501090506101419050c011a0f0307050a09 77
    0x1502c5005030300c100182c0d0700c200800d212072203a61609a1003100c5c2002a080d1400c82c049000d02d0703000501c2c110942e807640e50640f41155400d01e0600440f004440202d8424805504002d420231010402c000b007410b400038101d002ca8409542407510f4400200c0200c41ca205003200348400d82d0420401002950b20401041e00ca62191a030001070344512410402e180c9400000c01103043c5402c07400411510b0740010910082c1081c0c1c0c00d120b500c022080d034450740c449005001c01000c4c8004c66000c121501000340c0604502403c01d5400c0c0f0f410702e0ba46000320390302c0d041119014450a810030a075054180107000752188650b0001e036662079141004002e5030000d800840da2a0044100c0500030b0031035800340900f900030000c40070000b91b01e0a0200030b0020036940d0306451001d0202403000600a00c0400d4201c510f1001400e0100c0e18414140c04126030900c03c007036a51a03598202141d10440b22842113061401040449044440340d602009141d1a600c075481010307402054200208003078903e540001d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 367679649 1250 367678399 367678433
    0x2a0f0608070302041701050412030e120705012c06010909031b05010f0c08010e010503160e04021311030901150f090e01090f030801090b0a0e060607030e100c11060405030703 76
    0x907007007a44030b0310a012003117004600145280c0d1564140010b12540185000300101d02e071505010b054229044941c2d124642c3c20041c00e007190000b8003905100f401c2d4048004041200d03001d05c4504020f41c0360074100d224041000c561402038030000500c41c0780a00c640c08081e40e150301c40c0c44107c05150174403001060000816601d81d525850043c00000c2c00d0711654000c801141c94030149541802c000c0b5100480503040790703020368001d5070b9481f809104026190308540602c07000303600a40d59840404d0504060308922020350341040c841d0840040b035035014510403040d00c2c000f046001c4a034a4040c7c1c01c00094401c5184401c048001400101b10b1604280303201e07401c600000c10407801c20794500310710442c2c003401500003952440040c401d10f8102d0180300b001d00f0781100d20f1820a402c201d0340b5810084040c0450340300312000a810004c260080003808506040200652202100303104081c2084008100441d01c009005440c111180383c07400039a000d8a1020340106407072415070350751210340407142c444 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 367680899 1250 367679649 367679651
    0x10c031406040b0f0442180605061201050907020a0b070507240504140c131d0f010e070806191e020706232406090303072a0f06080703 59
    0xf501440d520780e4001c07541c50038180815094950000c40021000002c0b20003a81c50f450fa141c03030360180102c9102d10000a41d0101c10301104110054007c1400402e05507001039040a401314a0990007141441d8850498109540da00b045a4a4203000c907181c5075140d500038058061302001c102c446d4403801c0034021992052801c41081319080d11902e0160700400d20141c115600d540070001000000104c0c51005010b8100401e100814440000ea00302003022901800c25a1120039158000e01102c0c0d010144041105540100c0500180036003c1c0401c1e410060140c03042200005907500b00154143c840d42d1405219280c09103401c0490307028042d000c40412081d421460306012501e2244014003120703105141c0042c0d081340c50121040300c0c424180c01d54940c1e080b0369080040c44000501400701046011080507001091040091081d0140c04101074243c40042080e2041101d51034901c184030b50b110700d84c0040c4400e410100365114041d40200e0f503030614080c0341040182d002e5407000d6040145424 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 367682149 1250 367680899 367680919
    0x606032318100621150b061b0a03091205210714060f1005030c01200a030503040b06090403050a03020a1e0512010f051011100501030b0405010c031406040b 68
    0x48031898100a0322079400301d199112000c100c246402e00c1c1100c080c4442c1c101c0800c912805454031791901441c1084115143d4407a842a03419650300d2080b90800d0410400041010b0320400c40141d2311101d510f812230200e001c6120110380800440c1110101c03560100040a061f0f1103640480c0c0b801d0881081d441e81c41006002100004841c594502d000700f20030f00082040385031000120002402c080c0008a06003c50001400301d518041a50f1500c0741c820700303018403030f0320a081c00c101000d0b01580c030105480c01840303500c00400d64007034001e5010b80d0140c5200010780d100c04040040d08030013a500200894410428030b2003250280c2c02a00c03000310582001e0324469518007159808290507203c08001030400240380c8148803881e1081400351204140003d11107007444042181115801708c41c1050140d883c0202e050f03840100080703002541010410700180d40d5030320348500703032040641d030465180d400c003e62031040f82d21038418920a08601c200411440c0c0300c0c1c02c00c2c4401041441e000315000f031300d448 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 367683399 1250 367682149 367682191
    0x307031e02041e051501080f091203010f14100c031803020d060912020705031e0304090606020c01110a0b0c0a1b0c06090503070f03030e0613060207060306060323 71
    0x2105288528003a080200c943c0d050f014120300444100801500a0310f264104444880e607100c1e0203907a0080c221030140b481500c1d140c80765441c00003142880801104008000b0440b020100414000c5900c3c00308051008401c0d00b00f002098407204062000140031580d072a008a480b4404d003400a82108803140c101e6601c80e008561030302d00114040c0d038069101c140301d50400c408400c6000b0006a144090a612414880000d0325940040e0001020040403600040c11003010310440b002004040390800c134544d0fa80368040d48a103119102c2a0102d81c030f00e890600d42c050007040c510100c0d988103071a016603648840d49507c454001840c55800c000c950150f100c004d46404800f50103190140c000c2a19551914000802c508010b0300461700940103203900f040000c182c64410004c3c0c4e94503081c085807180c44003000c41d078280910100ca42c000102d4040000d00301d42c0100c1e101d4240c450b142c0d4207110701521500250191441c4454400180c080005503c2065000f003400da500b2046801301180c02014903 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 367684649 1250 367683399 367683401
    0xf05010f0504150207021503060103020c01050f0a060f0b0301051c080a08060f01030b06030f04050a15020d0617030702011d04060b13150c140a0807030f030e010b0307031e0204 77
    0x3015418040c03a550340305110a00110b40c0c4000b010381c02d003a2043d0301e060305640c0412001032055203004400316011000c504180e00a405441ca0071040c0c01c0200182c0c58025a681e012820603a00841d620b450034001041d0810301c0d4256030152a88400c1b464a180d180c03005114102c100d0044411402c0c45510311000055030810003401e10160035036a188a50070b1084c20481381a05c0910120b050500c3e0010030740c0c4544030719080d07035409143d12825001c85c0c0d89030304095060031003d5a00801c800c0403000b1004020364254060030414141420800c070300c5458000322149000d41c007081d984641c1c4107101c0c0708010761092010000310300d5100c8138800c0c03050b0200042030558110b600308903040c0c0008100c180010130b280000c0801820010740e01c5640d82802d8401034080145441d0142c4584041584409801e00c10040804030340c3d03002540e80e95904117030034014906001c0804483c002428200d050316040f0050044540c4404000c0141950601c0c640d910005404400300481910f00c03100c40e01e0000d80d0729 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 367685899 1250 367684649 367684661
    0x20a15120c02060405010b030d411c0b0a12170a09080c0d1a09210306010e090603120901120c050705061b0f0304030527150f09010c0f0501 61
    0xd0390010803c5003000c0c5041030a444940c03552500980c059104000844d50040309031000e0541ea4020504403980d12050300200c08405071070fa02c988030f0700c80a42d25000c00d200010144031248480e40c2d86800e9030004100b00307907500041c196a101228480c1481020226404051424403449495914046400c1c40c0081c5400204400d40445c032880000c000154040c0001d544800c8221080d0307a0790040355503000b561313604a1002d0004228040300281c1c80e03000400c200502c40140e012820412003220070104120f40c0b00b11403c600194041900403001d050080641d07020700c500802910207214260403400c0c6075080000301d00c1c100079017852022840e4200703100380390409600b90780e1140c0c2c440c04c909040e454003d020705a14030504960344450000541ca10a403404d07850700c020003568a440b2414208c4460040701002d100c1e10825441e041d003021265510074000c0c5c00c00391f8800003503240070181400786c0e0050250170308000008100804d4550311a03410203c4041c1325007203450340d60b0308a845483c21201 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 367687149 1250 367685899 367685921
    0x504050303070f0305160e010c050604061e1b0e0406030c0801050106020f031606020a030618060608011401020c0d031107060207061416030c0201030b060703050403020f0904020a1512 80
    0x2001040c00b52036540110007249001480c00d05104a0500c3c040501018181001120030414180c0c031007036440c0c0c483c07041d8481c040e4026049504900307040c10720700010000f10070700200740798254981034184903080c015600c0d5442c265401c1030f06080701d92003c3c4e801c1201903150aa1095440c1d6010001686d6416000d000d0000c10000240d150304240001c1d10b4030b428514030350361580c41404188595101002510600d40d0b00160241e11448104c0003038014044e03a42201600041003d0b403160f071101503034002421107a4956407a102660f03103500c040b1030060b0b00c107080c1c1d0050b009041ea0368400e081800315207445500c01c0c0382100310000340c20b0f2142c0c104402a04004010780041e50308001d42071740300084071070000e0214603142c54071350101010030130039000700340040034003115080650940e0300941c011074452038040c00c41a039400c91841c00070403a40c442d0200301d11801242010305000d007404000c0030f1040ba800350040c40c8540c02c1c50356100c4050014984c070380c20072410307202c40ca0105901d401000c40f081 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 367688399 1250 367687149 367687153
    0x91509030d030e0118020a1707260c0f0a03060207080408010507090306060e010e27010e031e07020328020307030b0f0702010e030307030b04090c080a03180503030a0f03020d050405 79
    0x307524900f018291040d20001c00810401c43c403606015a44010704801118100120182c140549901d1681003c00fa98800c0c0e050446e00070111004111174040d00d10b0f40081501541e0040c406c01081020450941229070340221076000148001200d0360b000700102c0d4051f2001d6420700d41d9804040742559021100c0c100010a2000c003001005002d018490142c542400a2a07503076040050105030b000c0c00900c0050460b41498001d5080000306008032007040d22280240482081403140f03a98035480124100508070350088018240d1008000b80c809055005010b800321440c1d41203100340740816a44900e99044007800940c0c0141e40801c6040000c0d40b0600072080c40307182884800c100510010306030b4040da414207400c071024040100480358800410305001504000d22404107005003040e681c002d00e0317000d080031302003001d00d4001070f10548141300c0c0e604c2040e48110b6042d01c0c02e400c04184542d5406500a00c0080030080c020b02c5030150050142c84d00600703010440007400d041d201c042c1ca041c0c07120b03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 367689649 1250 367688399 367688411
    0x130302030c0321090309010e0607140d0f020c0102011e02070305280e1e0121020301030b090d020f0a0308071b0b07020610030b010311010504081510050a0605091509030d03 75
    0x480e0039401c62030784c86070710a4040c50405140300006852082035010103803080b980090b41e2010410708800126003420030380b084a00c000a00c1c0c002402c01d0310040d41b400094454180e041e0100d610500501c84c81441d1200301c84203a0507010240c0b006900040c80c11010300c0010301071104483d00b0140300c8c82d80c40f044007446c02640480c415020301084401c518540c003410a581842c40c0d51200d440500103e90020f10784801d080c031204c3c0c160800181165030307006596000000000c03e001040c215036000c2d4102900380d5590007603181c01603903100c20144c0409110f4101c2e5131408042800b41d001e40398401030a04000384e040700031703100803e98010006070444074400404184010180c1c10412180d00503e651415860342e4195111602500c0051000600603180315030032080d030b644181705940040c02e00604403038004c0f050708000101050129005160900540740010b05403801ca1070a40403900343d03888075464040c46000340403040b0030365111080a020f08002c20320003a2001c0010360402000c566002500d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 367690899 1250 367689649 367689697
    0xa020714010e1e01091d09010c02030c0a030e0a0f091b4407021f110a030e12160c090c170406230402090915130302030c03 54
    0xc100340d600341241000300304840074805850f140c0300e010880c051410750f0122071101400407101003046410440949900441e03582241a83c04100d5028004c4031000707014291070701c402240d8a010f54030704e5210795401000a2170100f07000760480c00b0b8000c0040c012400305034560700e528555444552041141954a00125404080262020025103500d207880c00c013441c8000c10a00d074842081c28501802c0c410382034131144506809119100084060750407044034075003900040d4a5000e840c2c6203400350707a1001c0941aa00e5102d2140800c4500c210284a09010840f50114000d10b04c2c11810b100b41e20071a01c80c20103282803117001c0d100d81140e0364001400d0322ba081c0b03071003e0b1941d404e80c0009619030914006107506500100401005203401481210390f54940c1014006401c82010440500540c151000201701e0303400d03c128801d0b0300a0781e1480e2152180e45030031303030b585010320010300007101c01c0d01c08141c05182c40301c01180341e54060b104032411302c03815805d16400c1d540300036110001e01e5103502c11062 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 367692149 1250 367690899 367690919
    0x114041a0f01060f05091804061d0102211503010509060a0f02070b06060a0c0f23030903060609090304080f07060f23030c040b0c0105040204060f0303020307260a0207 73
    0x140c0301d8240c2200180342d500d4090050714030301800c030076407040c440c000c40c40e0742460f10f4105405420b03c01802c40485d603400d00341401c0b030042520714000d44040540c824030464002c0c0c14001c8910b4110f10b00c039049100317990f450b0000c000e40f00c046c0c0b80e418003c082031140403095509015850003546843c01410880c109414070204580d6a0b003403224020f801441600c02040700d8055070ba40c010710598415580c0c80c3c400c0d204039215424408002e2000ca0080804020300458102c40002081049541984000441030042e9207015080b6110f90540c02040050074500f0034046058008402000301c0f82050b80b81d60105003407038a00e01c503420380341c0d00c64501008900d0740020002c0c003041840c10310b004003486041500040c00d5140c0856002810004040351140000038120340003009840e59450b21401000d2030203000e030200b81c500342d202d1801c102001c540d02281c880c1ca00102c9038103400540c9000b816070303101c001d21000000031000d80a14100c2c0904803811075401405901ca0715409440c0c414185a680c2d8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 367693399 1250 367692149 367692151
    0x1201080613030210240608040201180521010b060a020606270112020109030b04260a2c181b1201090e01090611090901050f090601110114041a 62
    0x510040401c180407008030340c001c101800008a605008120150000f96800010313602900b200061074030035900142040c0d10260503070056100b40d030740c809101c1c203000a0820441c6030b401082e601c1040800100720b00c5104000b85214080c0060001c582c00d202e242c00611640c0046400c400542c005a003040000d15250a500c50010387c0c584e543d83c043d01c407080180c5c41e40c0c00c1c140a02d034031050300700c110381056a0040c03d500c0003e55100c030100e08940352518200c4c2d00c4021010f14515080e101113104c200c031041c0281550f011b82c03620303610f030002100b200d01c090b00203030200d002f1841010140440c000303058603990520310f00f80018907444409070500c0b58004812407030190100000080c00d1180c410302001040d1080d04403040c024021800e0b207880c01100f40144004640100058500705d102d55149040390003801000e1000c8420b19a16aa501d080c41444694040905d601c2688100040c82643c041c0902c1e00310700101200015448a0a9009108010301a501602c003900049403400b54296075058407 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 367694649 1250 367693399 367693411
    0x6130216021f08060d0b01030f050a08030a2a02030d1104091401081203060d030e182404020301080706050f0f03090a110d0b010b03191506020c060301060c062012010806 74
    0x82905e450b142c1c80000c5106000c0248000f1043c3c0100c400d00004100c41c040b83c5401c48200340c0c1d42d09080401038010300a140d81d002ca841180700c1800c144a1440f00710126688064000c0e6103001c0910b40361200801080540005111080c0404a80b4540610a400280c007209110300d03501d50408410924041c0b0b14482605820400c00402240745c0311361110310301ca25418100320841250300000201c414220190030000c0c4022102080f01034000c4060070207980c42c240601160400388c0c4c506200c1039100900402d04240c2c4075440030400648980001c1c01010385031820941424400c5c0ca03516503ea205407a01852640100800d000748100d80c00d501c0310b554001c903001560f010650307540c00e41140701403262003000303031001c00020350618102102c807000c040d5040b42009040700141c00060100700900601c00107101d4000344400e80d052000440341605c0c0d0540b90500e40c0d02c2541e4406014100f02c039020b440300038000c1c40001100c107010002e00b21864146003000b00369810411580d00c1d0403402050 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 367695899 1250 367694649 367694659
    0x4090b0f12030904050403140d1b05130e090703020303030f010905010902030402211608030309010606020718020f070204090807060c020318091008070305030d0b0906130216021f0806 80
    0x81c222001600104a80c1c8280040d103003c50b0658541c14107440034415880c1e01d080e00c400000e02140d8640d031560011804403880600003400b071381030800031203c47c01104c10090a2805960003031060031140c2c9a80e50340302000004464a0a48a5021904580080d80c071024601000c2c0018081140d071801002c0c0900043d2504600b5881c05070001102c121000820f01c01c11804d04140c44200360f801e04c48540d6604820090fa0744060780d078070060b81d50344e000304c035030410f00c0d46041c00c04207c0c80d00c045149403c54002030303410100c0c00303500c01c5c544000f035210180d9008645c90401c843c00048e2a00d0007000000350250790100e8440020b030610100380c4039174040c03032002c54004210401c05125240765544540c803003520790803016640c00011781c2030000382d5040f03070354240300d400d1000040050002c001d01704002c1d0140180803091031001030107c140030503640d45910105068450958407079960140010005001d1208800607003a000f090403690840901060b86003070103000420302e40c100070780c9030300b01000f42c0b0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 367697149 1250 367695899 367695919
    0x305010b1c150e0108031b0c012f0d0504030203012a14282006062709100b060f2512020706080601050a090e06060f04090b0f 55
    0x400020381c070074402900380c91503550b0303000c0000c0c481e0720400c800e014007124034411000b561a42c040c0703580c0707801c9000b102c17182030304981e4001c041d1080454044000c5c581030711744c202010704c1c200c0c0154079100400b2404010341803405507803100c1d807410410100060001c2c2c0714641c3d11420346c0140760030764604441640401d01c1d90f07165040c2e0000c103040d9103100148203150030903c00100212000252181c0451003c041c08800c01d0f060600a040c5044c5c0700c0c03c2c80c00d845190b00800c128400031035242d0080300106042d0070041c0050b40a0411444414038142c440f101c20507541d00034000380c44855000d0390000210340c040031034020f01c5025803245403114041258818105081e04c0c003140100d108501c1005075000d0410b45918528000d103036014101076001c0340700680c900308150000d69400c0148a240c00150002d0b0101d03030307154012021145100f0465488184c950300b8440c1d5204c0d000005800c00340c20075002c00500002180e030801030800b03400c2034040400c1d0621803c017000810301c00f03002c071139202d540c24003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 367698399 1250 367697149 367697167
    0x30f0b01080a03080601030b12030d06091b080402010c0204091e120315050f0303040b0f07020907030504080706050417040305011a191502010618050f0c0313030305061906050a0305010b 81
    0xd001a8405007d00c0c0100321405114040fa000c22403010444126100c0402d500c220b41906030800015100344c12010400001103102d0107070303606500e00c1c01101103141c00c0c010402551084e0b140d440c1d0380c2e0025102082c2c01d80b142d91a680c01324000343c0141d110303203c40d03407014080000d603035108452150305160922010600e8502c0e05c04c40c1400340310703107403080396540780301103c2d03450034800d2b500240041c5280d00d0b118003501c0d104402030761048100700d2098040d0000184024080e101e03c6000315081050300d030030300c6c403d81d40307a20080c100a041500c800117440540b944103000c0030004e001035481440041515680082d2244207a5041c4002ea4400c4000503401c90f6800b5442c0d10400c1110140d0703005240c400e0f0b070302e04241d00609083c1c010400070b01c54164101d00b42949a042680151800c44030080b45903107110b108245070005864904a41035140f440788003007417207904515007110000b40300c141c08000e40c0c1440940c050445c1c6c0043e0104002240000f4030b40c1e01882281e0042a083c14030515000c4c5003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 367699649 1250 367698399 367698407
    0x19030e070518130b09030403141506010309050a0b0a02070209010909020105070b0c0910110d0306060503060613120b0610020601050604032d0506011404231807030f0b01080a03 77
    0xa034031204007106080c0001d2207070390794030045800712500301144d40c90908100c880e1544a502500094480204603098090603110024050340c071120340c042c10103501d0321003000440141c0400c140594072449440320314808540b00700c0c20a80a183c4422006a0700c01152041c00310b600c005a000000320307407820701ca03140544d81240444808a50011a03041181e0b0765000c040b000c1c0c0107048500340c1242900c520901c050760070030010920074094100322a8050284c00d02203058400500440d000183c0600c0810302c03500740000600b0010080c0c0c00151445d54681d83c00003004e0490020982d46813486105200d02404c0003100004c2d000706500c0600015810304006c502e95200f01c2c840106141116440e0400c03004021460300040c0c1265003110000300301e5800c09680d10b110a01030b4040f01030301d94039010b400b4906841004803442e00414581441d01b00300400940203d4010f01524208030f036050168205102400344030081c501c542443c0c40e500380d05040110381d40304140c2191710250b01c400002c002003900 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 367700899 1250 367699649 367699669
    0x50c10150518160c0f0b070305011401090b0c01060914160c05150703140703051915120602160f030e0418020909100c0509100314130602090619030e0705 67
    0x100001ea6035034140704608507213111a02d0806400610600301d6042000001c2900500442c62a54203001590302d400340c81001c1c001042085000c01c2038080c080004c5810940030300070344c40d544e2000140b242e45d1000aa015201c1803001c900c5184082810041a4440b01040c041280140e141c4410003505071380e600e44d03803015001e641e01051286d060000311441d210790098481c98030322650b1407145081c0340d100903000d804299140d00b8030701103825210301840341511908940c224080d4040041d80e14100024001c020116030a5521507002c1042e11182903d00c0a81c0c80e1040c818054609034207941c4c280102202500080f0510031400c1c500510b440341495040d801d0301940403245140a503e603441154a4440480510500d080c05c04141000150b0407102420112500b076402d003030301121100040f0111101c1c49400d003d034044c02c41c0810f240080c00030704020b1107481824018540559407000464079045204e0301d42252580003481141103034180034808404041d00001c01c0c90500f0640012071002d2 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 367702149 1250 367700899 367700911
    0x30a0302040f080d050d0905121803100c020d0c060e1903080a05040b150a05130e070503030403020d1203020d090b06040c090e0a0b03030906030103052425050c10150518 74
    0x51149420310600030248204107824009d441c19607696000c003a104034888250542e030314400e0040e038a250743c90000900409258184a6026000502e802c0e5000d4501c46001e81003940c1d03541da500300b041d45e00082082032010300100840f60001c540039502d001050b4990080c009920103040c80148000104500349268000000401d80d10f0100048404281c8021456200d02d81c805007004070401100c5680d84030900c20410b40c0180e0f518161107005259485c8030703d2000941015028081d14040f039118114604440d09900d0054a031101400c0e02c54160342d40b003c2c06650b002d41c0e240c14884030340307014410540e0101c680c0c2030289000d840d0a0016060f02c20050a58841c66100c603202c44450368280112a580301d40186015260350b100c0c1811940da100c144a06810041d8906000c858903c0f00c40e82c8521452401c1101c26020381c2c0b2100402c04400c08613004014000140010344041800307024030705e02040800c800196071210601c202800141c2580014001ca9420341c0000080151440096100c5 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 367703399 1250 367702149 367702151
    0x110d02010e0a150209150d06051f0e010c0b093415020307020909061005060c0703020f010509030a240902030a08070201090b0a0c030305060117040b18030a0302040f080d050d 76
    0x203810000c3c04040c0c4079590850354000d003001d00f0780d1000120203000e402200d150440400c007954031802030003541c0c043c040302d20080603400091070300202d00c106a1080c2520061515414803240c9540c0c0138041c80c0c0648010701a40c0010b412150510080110842800c2c40394034484000324200700100707984440e074000c080f0003840705040328540b54001c000f00c40c405031b40508079206501d004a0030980310b843c181d812800ca00400c002c001400d10300f210598240d9003120300038210991441d42042810b11030070080f64103005081c010660f00d03a03400d00580701e0240c0655200e1402d0001055501c0300010b142058840701031401801c40056280024900e14290340110100e5444a040c00141c0d1611042e505c0f8281c181000035041001c00c1e80704217498050742c40782d1020710603030300c07040d0056680c0d03180b100c6001c1c1c0b491030000015007c1041030f44510303080941441341da10005480d40300f031030850380000c40b61000301e40c0029007084003000f0030300c400e0010301e41000034110315225507800a20a00c40d44480446003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 367704649 1250 367703399 367703423
    0x60c0801060c0318170a02040b04110f070302070320040501060f12020d02090409050a0c0b0313030507021302030916240c08190903060b100206011208120106110d02010e0a 75
    0x81c0311107801300180c401090300114200c40c558a251b66940c0f5540220f00840c200014040d030b90a050141030007010004481c4c41c1480c0e02600d00b8001c50308070840503400c620541c0d00c00070200d0207480180a81d50040c00d582421070704c04c0024001500d44c103034000810861031555500c1455400780d001c1c00500c1e0304c282c000d40e542d4411008400030740100981c15a1083c170f040c2e0380408200001076444810f41c4180f484184c45a80d41d200c800b040d010490b55080c249080c440c0580000f0f01c610000e209661005004048440c0341c070319980104e80007228038050f29800522008031001001e5641d900402e03000d0000304001c0c2c0721036002c120141908022200380b01070303900c8280c10441d4100948400414a20842004001d078480007071081344076100a81d400745c500128440c8901340700c8441904404c0d070b0340050890340d1a00380da0b5000e100b4144c000791030105003030260200b00d46085e800107008100d6507170f03201c428032294001035003070840b204004400d581c90120003274040303880031400800310341e00846403c080c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 367705899 1250 367704649 367704677
    0x16050f0402070204090c08070807091e0203130f0c051503041208040f061103011a090307140d020306090f060f071b030302120910061a07060b120706020109060c0801060c03 75
    0x140c0005c1400820103410281d000c1010070000400200700c40558003204c0c4003a82e0340c03120b1401c031000144a01603090b44d0a078036920501c0250011078201d11050fa2800307080f101c42d15034004204401c24125032040020500b0007142c034158020340312568128240c03d155046c41d503150710392200200320301410301011704003380610814055580903150002014819042e110180c0025540240a05500085103050564848071030005580140001400801d040780c100031070004120700d80030185610540c181046030050300d0500c00d1038000c6101c6401407040a0f400c0d00124104a4000c1601c0c0007080e04000300036400703a108185808520340c455880c10400d0103418124080d2050780003c81c2450318000070b220205000003a5503603500d014441c104a080d8840110495104c2981360074809040140074a40104003150301c60380b141c9074010585211000c00550541c1022007680c4141d0250359075026801c01d100d003d02990012510a1a00c60403a60404801400d2402d03550001b5040080008070880 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 367707149 1250 367705899 367705901
    0xf0d030507140d0c05120c0d200a0e030c060c030405040f0b060d0e01090f030c021008010b2506060e0f060d2a030b0108030c1216020d0c03081b16050f0402070204 71
    0x5161341d040d401d104040c07a1070012162654408c02030700400c1c0e840c00500410843c03200800801e0441c0324400d81e441c00c5115401103641003405a50305906019049000c0354590b56000241903040c040e6020b140c440f482e00003040103c0c1c00c000c004c645100c7c14404041000e54500c000c6a2615030b03101400151940e181c50341c940188126040100102558400d00e0305054110b0a64203005100b180d41b1030b449100754070122200d110038481c00d0b014803800c3c414408082044072403030000640400101070090016118502603030503030790100429110920504c460014540c0c0d0040e0302031421b84204e035000c0000d55a08001d0103585044a140c83d40750120002071301c0f040d20804d0020342c0c000d8041c032042c0d6100e078401d44d101d500840800d441403251451400428402c401a00d518005000702c0e07103080c1341c403034090140045041c24101c40e014100c08000c800582e080d005022a20421000360310400e0102c91309500d041801c086000b0a0360000c44100002d60701d03403603042c800d61019a405a2251020310101d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 367708399 1250 367707149 367707157
    0xc03160602120c0c0f012f0712030b03060a02070206180609040c0908010f0515010f050d0203070315061817010905031209071a04060804140f0d030507140d0c05 70
    0x1d001000030622043c408810090611140c0d074000f03a60414003502000c500700c80b5011b01004c070300005a4024105504a00042c0e54401100d24980340b074240d45a90364043c08451070103000c0881d82e5100034071070b030741401c001603a804429020b00311300d484030a800054072402540051007001025400d002030945a01e01941c81c000c5025005001d02158084060305a200e2401103a95542c81c01254414040b4240502401006001c60044050b6581001100c81c0c40c1b54103e0f2000380100ac0082032407000051000318806e14807079034000342940c80b4031102000e06025601400030070180c4815161001000c04d0360b202265192160111000c0300700021034050701c10110042c0441c000482d41103004002008030f03030b00c1007080e10161039201e501c2e0059061580c0b040c4d140e84040e01c105110600c0074500528010340c000340124541c440b05482c0018040c9000c105960020050300b01c05000f81c4659014002e854000300c0c541840b14070b0b240b80351040b240302d0140080d102e688588540846a280f80035030212 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 367709649 1250 367708399 367708417
    0xb0a06050d060509240103020d0609020d0b0411040c120c0e04140609060405010305060703020a02010f09080a140a0e270f010e0702010504031b050724020609030c03160602 75
    0x946101c1d060400c00000c100440d03c025143c05590414203841c54000c0c8100c3c5840c03007007000f444560f4219000d101c0c04d150031b07140481340d1b103903290b41c4080540d8964208a9489128500c0040145820301c2c1c00205a0a03041c0d03421302071402c4c400d901c9101a08505040084490100e0008100741c0408c001c80d030403030740c80f550f03680c0041c503010b50300418407140c003440c43c8640b100717580004840d182e1074280710880314240b00152042d00018081030005201b90018107041c42544001701e1441c40502080303048541c6104100c2d10344400040070303014680c200b241c1111000c110300e850360078500c8111015055000f800d4465108243c0350b0304c18054100042d48240d006000b44040c03030054030f84041003002981c028010a00b950120b170001411461050240c1403143c0d034150360310f10009081070071400030010b8605080302da030f0040a03400701b80d41e011942c812030b900781050b44240b000d143c0084044c0c00c01d10060002c0c8410382041129021030040082207c011280d003040b020414601400e1502c003c0c0604000703 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 367710899 1250 367709649 367709659
    0x30c02031002210105060711210d0306050102060901050919212a12030203132f010908060f100b030a0218040203040c0302040e2b020706020303040b040b0a0605 70
    0x107003510b0010503007076440c2d40306410b0a00103030303076600c039006c0114902818000810340b6116004030281420076420010816100301c002046001100855038104400300c02d032440002d40e84c450800c500c0d0b034100304440d0040b11001c000c01040c108045203030344528045c2c2c03000d4582120f0307003912000c00c601503400740d08c07100d01d6000d603c007400c51034030b030040c200600e03070b081007510041142c4c240003507140a0360071000c8113900c070102c003418003203e400c260040c1d040100391503c035601d4190000081002d042c4080340301d4110b008004001ea45084158450300350049049041090317481080c04000d20004071150020302c81f51880c0b03040c4d030310780441e42c170b0141c2d894221444a89011013400055101074001e41078101c0c13655190980c00c5901f40c2403000f00d00089401402c241040380c001c0015080591080c2502d0300d4203030980300380d8071100e56140d14504038400c82d040301c0409018a2466150b0601c10341024008900c0654503604194886562041024102a000410b13000104021503408e84c0404010540501 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 367712149 1250 367710899 367710907
    0x21f12020c1b0621060f090703060f14220b03190308010608070f03110405031203060a06140a0e18070216050f0d0f02151201060201060e04030507030c02031002 70
    0xa940c0d40394100301d55101c200001c003031000c04081c58050161618643c004864280e80741102c03c0da1030308100060141174005241d40403002d11b0b610781da10007600c00c40c400d4030b01040051501030340119601a40d4083c80c1040c26003800040c00d035076442c0c1a50807001c0c0c00410b0100844144440100800442c50419810300c01c804c5070304484201500078858482c0652035055140e039a070f0400791030031042150350f100003401040b00302110178081c0c0d010400ca0072000b09003e05140d16400803d10300001420100400c0c0c0020042001524000c403544001c0d10062a101c0f00f14500c0202c1d48a450088001880c2484801148808151a40d150410304201c6241004a80341089400a501c1d280324000c808101c00101001041500300b1060078560194040c0c00c01c4040f204a491f041e88071072081d03000301e03480085d070407100f02c114071941c000d08208a40100c0908182d450320a01170300b1600c0b030703501290304440f5040030007000c40c1d082070540ea0b126070582441c00320700306103100080c01c10300041401f011440c4045 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 367713399 1250 367712149 367712167
    0x10b03072c100e071e090501141605030a0c1b0509040221120306130e0d03110904240e1b180d05010203060a0611030a030209030f250b07021f1202 64
    0x500c0c074401c01d02084030304540345d200000003261213003140d004d21030105050f00d0030a030452109170010035000e40000448070000740c40303948590866000310040e800040e0807101302c1090020f41c0d604144555071030442c495a8600d460701003849a4030041019115415501c0c80d05403450b0031440300100d450400c0250703050700498542000c407582040e030b0018000e0b01540601c0009003424801d000e100e103a800014030380241654030480140c8100d181c401e11209040c040b101c04c1d91339500882003142040b0311040c2908102124041185505512940e10224820107203c0014184080400c940a8041c807071585c07400003600711489000641c00b900d8002a400d00d40006021040d8090340c0a200112250504160380d040200ca1003184210304003c40d410030400b50764118040e038014106540043c00b42d5001c001c1e17001402c0e04040d049800500e0f440c0e209514203481d0b914050842c0064a000740781c40741030494903000305500c0fa8000810310000580700303200844032070040201c50340103948601d040d59035180c98 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 367714649 1250 367713399 367713407
    0xe030a08072f090a110904091a090d050a050a050903060a0f0c090b091912060504060b06040b091002031e0403140a03080a05060120010b03072c100e07 66
    0x10000c0034550842d0312035016007150300c092508020b00010603035000b980711481501c0050403007450341025a801080006200c0e162400395030702c13050041140c46541844294842c801110007000340c201e5403c800c0300b2540558000043c0c41d04c44e409460650380328410044150380c24410f02c15072071703890711401081040040c1a6002180202c0c8105400d100a4014074002d59010307426005124001e001400b030610759003420141603100c0751812000070315035075030350b030000200c11000801070b40c032142c40340300b00410710905000d200c0a540c000d40e08513190038034100d04108140110485c00d441050007184031545240300b0425203d030304070a007501414400084000c513036580d00c00e100c103c0d54084c564512055800d40401e14000554068485c509c1c681d8803019001b004150080429060180c1d03169144025100604000c580c551005c0c000a20990790300100361401c42d8643c071407040b102c1c000122070510110400807102c100c059000e402a88e031100e400354150809981c11010350064070b00c04021005602c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 367715899 1250 367714649 367714673
    0x1214120412060e010c1205040501180308071704080301050103020a0e1c0302010f1104030b09070e0f0105120c060d020c0120130e04050c010e060c0d020606120f0c010e030a0807 77
    0x8034600803c41000303400c054038265140a020b5a010600412103c041040640c200700d52052180000250007a0010806099070681c180117400240341c0d18200041140c0000d04412072442101c040403051400780c1d01d007081c0307100502846041580215164907010701421812001240c000c208e050400c3c00c608980c400382c0e0b4044030135401503007002c1a00501e002140720b03d80d00030446c02c60803441d02e82180c6480d88a02000b0740425400d10403500001101c1480003612405445403520300d01040d45400200003d801e0495a0020542c1041041103525694141220326011000b400941c68908030b2484034018021501e60b1108400031038050b43d00148480010b001110074414214602d58458060104401d02141c000b807190380840c000742a10340c0515009582c03002d0040040346008000000141006041c80500025034095000e0009034542682547c07030345607100e00284188038100c1201c9a036140751002c0c4506000d1905100320701600c0a1043c5410781303400c0740c581a5070f03030350500c2c040c051145 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 367717149 1250 367715899 367715903
    0xc032e030503031024030209030304080303040b0f01081506010f140c0a0308010b0304032c040e010510050607030e04180507061d010521070e031203011805011214120412 74
    0x603600001103100084076200d03200050248001700104a00d408058000354052032000b6450b1200b80300000c1c01c80d00400080d44103a10071180c0b003102c0e0402440d81c103511070041e0050541d0340c0040b941d000b150010308220561100003403810400a80c1d4542003500c030241102d01c005040c0200082014907013000140b010000c42c82951100500c0c1e82c0d0700b000f19030f14041034a0040000340000103900000c49010b0324817590307004510000490030742c1e403c0060221079049080f01c2048e51a00c0070080c0c2c1c80d45400208e0002d02081c1c9000c2d10300b00665600601600b981680548070320380e1125180c52100d82c01500c0a5842c1d840011100c185441c0d0001510070710f5140703650403422111610b000303084d5100c0c90a5400e0b20b004080842013461107607210310740340440140040108401d0f0b441007425564200300c2c3d20030b2552203030b06a41d500c3d41849802c040c4514a91721001c17144e410000108011403d0402180d000d9420041c0c440d218003008028508003100781c0b81c100a503c001103000328a0906144400e40018 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 367718399 1250 367717149 367717171
    0x4021c02040e0a1a06010e09011503020d020304030e04110a09030f11060c2506090e0603251a03010e0f0a0f06090b13141501050c030409150e0c032e03050303 69
    0x50f4400c5c0045803007030400e011f0a50095003240040207640120000b000c0d1818850a015003070038200034070319080784c0048a0035000a808002ca41724141844c0c441d400300c50700c000701d00314500f8010a0003d0f00302d007181d12009004248504110b03007030203420303064003405c1200107102e250341d14a88503055a407150101c1c460340075510594002c83c903020b035150b030060403581c0da0740318086401e00c5c00c00c003c40b40040040c0300b143c0500500c00c00b41700110200c0c100103403807009030707420b410924100300744010010031842c3d0000100c4001c20041c028100c040710b240c0d03070014043ca203010700781e42c9009001015185c1503a150501908042020641c00340ca500300c240c0c03c95003074602e40d6041d052042c140c425a0301029982d80d9824613140441d007039120150072190070520604045142401d0800d0a0385141c1c040d50154a0f115951380010f02c5000d11403821000502a0b02d04190150030212488180c030320025004074a80d42c600e10540c0718a48090710458031960f03050003001c90140d40e0f03080080d00e0307074812a0403201c00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 367719649 1250 367718399 367718401
    0x316050c0a060b1203120406181b060318020a291204140a0b0a05060d170406090501020304080d0c060603120908011803090e0a060b0406030605030c060304021c02040e0a1a 75
    0x2070004140c60143c0a03c0c01c141c06d05449031b40f60480100454005000a01d900d00e54540c0440c1e19884d42c66840140d400e045000c280c078000006040311000701d440c800303406086100c030001da580c48511005a500c2041040d1465241803200001100e00103000c922108000c62031291140c11f0752002c510079805400848001c0510880789038580504040041041c032103500030500c224400d50000e54841c01c0500641d8452a40343c4440e007105004404401c2c00040004003442200d901a8500700240402e000441c242400d1085090b11903c0c04e9200e1400c101b011401c1d0400e1000380d402c004025504242201f4110340411002452142d850080040e258241649010740700e20b01c500c2e02020301d4141d55113140e4107090030240760f00d01c40c02800f680c1106072180c2001c00e048810200400091109480c00110345160205050906801683c003901c608400d0041002580710701401013040800c03a504480ca40c10144000b8000340042d0301400000d216114039101002150074800e10440c203142441c00c21 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 367720899 1250 367719649 367719679
    0x1203030b09151c020424091401180c020102160b0703240b1b0105070c0b101a090a030b070302180306010f12050a0516060809010506060316050c0a060b 66
    0x1000c1840d5252a044030190380c0e481c03d045040740403408214401030020030702c03803006035485107450780304540d20110f2541d8401c100110301040c4145100b107600441c20048541c9070298100390080341d8000d0400180c0c40e0104101c02910079411100807406040303003880e1076142420000c02c46070045400c0e038046498054110380c1780c9100d031840c0d0200e80d6141600c0307808501701600401e5507000a000d20300c0b030b203420b240c0b0408100e42c20700030b5603c1140710f9030f100c01d0030328590305112060900141c030b0000c120020a50900010840c42e0003a9401d111445200d5501c3c100480441c00e0519036610241c03465401006006e099581900145168821101c00c8205103145404154a8400070b12500402c3d140b928000c001f101c499111400200e8051802d5803441300e2151581e070304240c4000f20134072035581c184005104035a08020031940040401c0000c022a05e09040070030414800500230103007080344002d180b55080e2003281220003a00342c00701514024100340c034040c000350403400e1074284640e00600305028 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 367722149 1250 367720899 367720921
    0x307091b0e060a0c0314190f0807090302101b1104060902040e1315020414180f040b0c130906151b0f021804050d09120c090e03041203030b09 62
    0xc8146008004510b4845850f00c00d031042e80000c03204400340000c001c4ca04962900c248007500404001840445035a07035070070700003807064a03d00e00c810103001b1402c0c240040315038400018400d83e541680c6006010744121410344181c480300c0b400c51868000300d00700c6000c0100c05600c0428643c0d058030240030254035504510140d0141d4002c12444200c0e0000044018095004890505015a4183d80107848001c0c400040c0d910540008100c1142050401650304110300942d0134264001502019400c0034500b040c0308800140c00582001c50304000300e000c021070704044400881394664a42c1903a5581c0d1100400340815114255100000349500384000340940c03044126040c80f0040812428855520303802c29000003030060340c11000d140c03102d0203201c3c1036161035401107025100034003155800c014003c14842a0750800c00090590180d0000003804440c1c3c1340c0152408160042003200c54860028550701942d8000c01d0ba1543d0b020400303050641652240c604d10405588001c2c46a8900c64005 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 367723399 1250 367722149 367722167
    0x3050f0a1704050d0b0601090f0b0a080a0e031603140d0e0609070b12040302031608030a0f020405060406081306050403090603050714160303060f06030f180302030906030a06050307091b 81
    0x4d4001c00d429a0420014480790321155002d041414003180c2c81d81c803407041e004918401d40100410000000d02c40c40b10f00c1d005010590301907240b510a0208503580e0340c9030703900c070301900e034075040e20006e0030b0460410035001d9000303460741c076066000390350b124400ea036622406841d423b034422840340103a00c0811226072000c22544143c440031460540b070021044000c0885940c010005e0b01140400d00101c3d1103440500c5001c05024003404890352a1f04141444500722900c440c0e061581d1481000200050344030380c400d0310102c9095003050001507464456503140c05040f020010045842c00702040704054224511100f550841e582c1007005d07554421040c0c2e5201000c1c000300f03d42c810288485139001640011940c030142c0f0914001c12142d039a0ba440d00c28408240d00500003007502c03651011444030441c81000c1000c83d8003040b60f0340c0d8440319100039403603210310759a080c028107000000950b4184540c015900601015080716289076070307242031800404801c0c00b41c0740b9044052500641d40d6208142070 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 367724649 1250 367723399 367723409
    0x402060a0c0215180103200924030c0c0f1605011d03010903080f070c1109060102010917190201020304121107080a060209010906020109020f0907030f020408030d0b0328060603050f0a1704 82
    0x410304d806032443c1004142003001c903400e03244440c2703811500401080d14002d98051070070484425240c8a540d025141415075a88400f1019841a00134920b80d0125913152822500c080c240704111401c1c6104e000b06c3c48584040080e0190b0a0206070801c06901c503407018412406034981c0d660301d44903d6803c0711000324840c0094070740390302c0c2c0101901510f0100d801ca604484140000100402035541da00207281040c42e02010400000c50210110890341c4c8040b08100942d03c0211720354074180d40c400008a80541c401d03410052115950000340100300406000f500c842001c0b661b20003020310f0b015010b584680c0b4801d001505002001070881c0c0140190111a540185143c2c5000130103010710111000082c0280700301a00c400c2d440036001454801007019080c208061a55403664101400075144905016806944507a003002c1110440a0428a0301106104481e03e00041c42c1000342c0030340655040580a40100300c084400d81c900054050b080034487c1c80c0440c60001400010f9035070f0300a038490 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 367725899 1250 367724649 367724711
    0x70b0406200405060a120c0806100302041a0702031623311803050403060509071503020f040f1e09020c0307060213080706020d0206060303030402060a0c0215180103 72
    0x300344944d140c890003070900040a442d1030008003440242c114190348004a01002040071841400720500f014030f000564160b00307040540c90b02d072612104ad10b20601e0454502e180660100b582c40c02c559091003900c5000d2040c1020b840c01681b950808030b1103250380725148040800300c42e45407019060072503411a0002111101c00189170300d1030342c0d103c0c041025101020405503980340250004884035400300c005802030382c1d0306842d0b500f9407500740101d030350251071806a1382c0100030421602d458448441880c404500d405603c84440d020881081c0c010f51300241c9410548000c0455150380208151009500054503c00b149a9449002c0101d21070182400300c55001000b0700c0c8042001500240019900004031000699079441d0050401c12207400800041c0c00121021444a40c10040f01740c000700224091461403e00d64002007040c810302d2122030038000e140b907000742507603602d269404001c10541d185680c1eaa00700b01220681e22115183c0c580460310f011800c0800801684d0002c012803040d10b4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 367727149 1250 367725899 367725907
    0x80106080703080f0304170301060e090c160f0f061806241a07060e2506080103020409060f0518010c020309061605031c06030c060503060a06180308070b040620 70
    0xb90000707645d000400035501100c444c001141c1e20301010000b14002c005aa031031540150280080280c0300f04041d09041c0c0c403c80c288200785966103444100794440740d210221810340051446e114160b400b44950107000f842c503015005c0d180078201801a91050b224034020080d00103042e10602d244032856420241400d00c040062002100300005140001042c070789490406180b590f40720181c400c1850702d51443e0b00021080c80f0074805400c0b80e82c806030380b0080400d03001810041c0080c22408144030181c0b11360388455454081c403041d42e0000c200c1c160f54210600003440e0484d01300c8144030b508010100658a04000010151f01c08000d07511980c400401c5240340c8001c10034021100500b6610607100380c04200600d4180200d12030102c1808005a074001c84d00f9072440c00d00341e040503200d510600c28050200104009542d070010010195441400c0640d80c403a03c011181c0709140203600002c00e907200006001c1c0502030001401031045106403814800a420083c2c127000d8a101c019840c2c1c017002041c8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 367728399 1250 367727149 367727167
    0x50601090b0a030204110a080105060712050a0527030f0c060304200d11090105040b0d02040903110a0503120c040303020316111e1014090f0a0b030c030108010608070308 74
    0x10300044004840144510b02582e240d1300042c00300d8a010300304010a1000040c030200c201e40080c0c080340100000c5910904100717441d141c0821420b0440458410030034001a18242503014005840051366004210850b000104200d15100428441c14610900c60180080300c0100d00141c400c0c10030a0281c40981992641e55035407582443c01c140b09182c0c9034041c10713928215150000e0369000e840c0151405803030604c0c800180810840d06812042c00f490603c00401001c3d11621a1507002c15030550b00040c400c00c01d401c0484210700c050a2040590048556140034400004042c00500c0000b52200c407250311346061b4580c981c821840001c015030424451741101e0700020041000e100d010b179040060b200340c0100025040450003100c90542c0440c9642c08500c0d0038070381c0b0320204030212818041d45140508094210b54047c3c00d211a108600040d402d90142d151040c042c1c000f0001d103203245da140c2c20000c9151400ea0801d001d402c50540c60800006800e041c0040c40b1806c80c2d030007414039440c05a45d2 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 367729649 1250 367728399 367728401
    0x105010503150c07050313060f0305060a0b0912010218130504030c031103090603130b1003021c05010209040c020723060703030f09120e030d0c08090d020102160e040b0c0705060109 79
    0x200043d80040d018070000011a070140700810f44240c0d000440b901d401c4c01c00c0300160004070380500c0d0360101440e1004100c40c944401e0024800e030303911030800c40c2e221100080000e102c2c4a03502540005035001189400010040c2d001044d400c0300d0444210760044140303540c1d80700b12507044038050009001c0251150109004005907001d074150741d0140d91902d500203000c6200b650047d2207107030141c58119288003d1080107900280c000894082080626146800052051042c132075041000b0a420515908009007503044410425010f00140180200f04d080039444180030701c00c181e440c0e403031044c0e0b43c03c45c160310b03414400105100611403030404003e51422001450700d4000040115500c0c20300401141f210210749140e00c04a035210a001103c100600d401c01488154a0090204040303d080028600c40140c0b14500c4040e542c0c401036055600040703140500f02c038400d08500b620158046134140200c00c1a500c6580190803120031b0391600803e0050340c0c8035200000e0840c4d044140103001148903 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 367730899 1250 367729649 367729651
    0x609030f0304020d050607020c0a0b090a060f0c06090b0108010b062b060b131406090105090609061b030a031407080a0509070b0a021015030209070e0a090515040e010501050315 77
    0x10300786105681c4d45684080c900041990f502d40075a1041000c241c0700d00d80103e07a00c02805441aa0606064004010800f064000e002d4081400300d84440d02e0304e02c501c6200301a40e4103403c01d000303205001d030900301a501c0b240207011f004000d5092443d50301c0c0a08050040782c0c0d00c0390088984940c521840304c2c4107249520f90300003e0480e103032118400a402910b01e0098040015100241402c481c0380201094624500744c40040c0104c80030720030411180c0c2c101c1c00303454dc01038060b11201d41d074069110004401d40f0800e103c005201c14141d000008400c1c001010b40f04030789060301d0402c10040b46041e10701c584542101c1e031100050400c800038220b440d02e5004030b50044040400c40341c241e520b4089010143d009010910b005038810b4500f106460300318010092014146943c6190f03d41c1140c02045480380300030100c50602400010792000c0d07442d2049004014001c0301010005420041620000002041c04441c80341b03040c403840d60341c3d0300d10604c220760407680000c00601c15040c6e40d201043d07441d84 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 367732149 1250 367730899 367730903
    0x60b0714070e07031a0301050601021f180c06080a0b0604092003070531060513050a23010e030c0d020d4103030c07060b0d08090a080609030f0304 64
    0x7a5800014007032580364506401111a0346000c2444800f50785101120310010480078401c1c0c3c105018008184d0300420404662a01d02d40740d0b9488020440312369014110175401829014102e401150a0207205600b0b00b040e00c040d07a03100710880c4c03074014060317003900d000720b100c0d48d80f0040420003040080c1045e40010081c000800c0c2d1140302410514965601d60011500c0b00042180041c610242100c8030221304035640450350000d10500e4008000d080810140c0902424440c0010b540241c1d40c1248110400074013005101c41d0340c90341c4414000c0410a8180300100900d00f0380c1d10342c181e1540c09504403d0b1800300190003081124960390400004540880040c0e03046488641c416004c01d01202200140003100c04501c224861101c03a13030141040110544038040625008120000c0720100440340c00043c60354116440e0929800c00758018080d884549a004004021110811600c00301601d41d01404a446101c0d00303540c0c0b450349458080440b5070f2500d5030010404152080b030014045c1d41c00034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 367733399 1250 367732149 367732153
    0x9070c050118030315050306010810050601140703170105040c21020d0203150108060111030406030c0908100e2401090c21090204290d0224030a0f060b0714 68
    0x80403980e142c941c2d425200c8001e400280c0c0350b80291001d6202c20844034010f00050700100741c80c3d072411040c2511801102c0c280c00e40180c845e03010515603842100c07003031551206000c2e40ca958030302ea0304c0e0140009110042c00140000d07a50000246460070b40320f51081c000494482511020210480100d5080c070b1f1034034110380d2542032202c0c003000c55040c03020303600c20a8040d200c106443c080d1300014110000c02818a070400c007842d11486292400441640c0c21912030341804102e05000c854240c070710f00c1468011481070310070300c0c00c42c1004003426000701000b83c0000b0165040c44200c3c5244c1c0c0d400c525108041c00c40000103c004104c0040709038000175845030356140242069811120122600384407c2e80035880d591582a804194a02445146413185105007400711a5401104072400980000c101e540702c3d0190622034000e64407002800012010054040d19082290b4003600c040c0d90070035a44420042e19026503944000307038510034034060f1038064000b1402c00c5410f5891b1090a0b0100501300034038 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 367734649 1250 367733399 367733411
    0x5030d0519260a0e010e0a05120f0d020706020f032a0405032d0a0c1a04051318060e160b0304031e030f05010b030f0a0b06221203110d050909070c0501 66
    0x41c2c1342c28451405e5581c0b414000d001c3d105a6810040d00c3c021228020f81c44044c002c0003008944512071088410250407501c0260300e5070140c0c10309900a01030940840d442c81d000004102c11f022520300154002440c0b40c4a001d40038860800030301c0540698010b542d0103600100405407a082401035518281c00116011001380703140c409840e04006c0d03801c40441303138580741c01004c4c09101c040080e85c54041080c81e0403a1b0826150000140c89485000404a00d965890b1000c844500000b0141020580c10820038440c0042c0802001e80e100f504100c141c8607024000c90214802100390100c03801150507640e00043d8102d07030020340c40041c409510050a00d5a2446a0400304031035000309402030821440f0780c0c2d01d0740340445101d03000c0c01000b41511222464840140c8103643d42034140c2d10850041e42003007440c070306001001d20452200303800040d4039105240c800d07010035074413808440c0a4010107056607055416100305403601e002c1d8034401a401151500003440a610840514038054001d100120342 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 367735899 1250 367734649 367734671
    0x519030e2407050f0d0c150b0102031209060610020a020a0504050c04030c0803090a06050c0604080307050d0510140d0f0305030408040314060103110a030804030206070c05030d0519260a 81
    0xc182d1000404a40c903401400c58a02800800e0000c80e001003010308010700c98003401d544811040b030340700c8541c0c003000703545a40091050b4400c00603070741c0b0240d11078076400329820841c0c0c065076128030407191107100c2c001024070158101d2000c60b1038403042c3d501900c01c0c922030342841e080001415004050402c9044148400408500c0103c04100100440c0c006142d54090795024401031600c03541001051010800140a12900005286507c01e40200425843e40c480c405c0031a0309200f00781e84415030304d040c90207220504100940d40c10855043c8503411034a50940800d1042018818030041c00510303904d40380d8004a03005e600155440703841000c1c11842c00c2e40b01e0391030300f28a0b400d6a1500d03071264060401401040b8065510150440c41203510240141c034682e50b07045039219902000380984d901103903840130090511100c0d800350070001d00381d5040820300000240750741c102500c1c00c41c03004042c800c1c0d802c6682c0904000806042c000d008102602d0b074410548501410240c240c5d41c500390343c0c05052031 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 367737149 1250 367735899 367735969
    0x21110315070809010b150a030c030b03010c0e0901050111030a0f050712030b010206090105091f060306180c0b040b270307080a05060133050702040c09030519030e 71
    0x21107070701c00b5200d803000380c2070040a030741c02c44200c0d031055805403140c000000c07140e0600c1010368440c104249404143c65040c08012006401400b203025055801c001c807492849070031944d01c0076041029103010000c0da903218011a0000040201c4c0c100f01c0c4c10402890380b00601c07030039640c0e8504a0f2030a00600c0e101c0d8030f50781e49190b20031030030f695400641c2d14455090203603418040c03c0d400501c0003001307004c0b030b0506540f4180c4030404014200d080092031100c2403041d1800c1e0f00b02038021600503600704a041102c4441c088540c0e5400012613013511400c1c804a100c11220f0706590030f03150f4516206082410f0810700620b5510008494205014001c01050709550200000ca02402081001d0200f00701d040c601580b60841c103800c6000504d003030030f030054a0940f183c4d09080ca008035003010302c0c03415010050159001e200d0200301a410030308040351416095000742403042164481e2044411031440144ca01c401c3c100c5034100240081d4490003055024580b8004007402c02c81f401e03950003010184181414 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 367738399 1250 367737149 367737151
    0x16030e060706050a0513020a140a0504020a0503102c0a090b07030209010e040501080c060f0f030c030414030c1002030a0f02071a0105010f0929030712050121110315 72
    0x215500c1d1030f18100144200d81e4043c02d42c01204020150030140903950014140240c60b009103144804091b0b50085556510007110006080191046580d4040d4410040c901e23841103c01e0860020302410020351141c5403451003181c10400c1d01c00c001210000c0c80e800b0480d01c809010341c110b10342c13195440b4000c070f44a0601180074400540380113035074024000026211040c0c0b040450300c2070380b42c000108004400842c1603540c0400c103c1c1c0541ea200c5644030510786030300a10510035051036001c000c000041000700001c500075030160240b84014109129241c3c2d603885401c086034402e80241081d5491141e80e82c004d15001040301c440030803040070401d480c200700d801c80d041c00d84540112043d400d4048002a0415024040c02e28107003c0745250460701420526907489040c4030780000c07401507030100c402004800501c40740d0352081e0340d0700e08100b00010400d0704803500340b0388040d20302130000171084850030a0140d030303040d0740c03818054000a036160117442100c080415a0503000d410319510703003011509509 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 367739649 1250 367738399 367738403
    0x270c03010506090f24040c020607030f0216170f0a080118021c111908041b1208030402030a0606060e0910080a080c030f03040807051605010e1207030804122616030e0607 74
    0xb40501c1c0f03412b81d001015907048051440000c8d204124941c00c1451070603688941e1a0401d40008200c3d80102c08541a0311401d640b000c03062201003245001a03a0001105040310b1012520442d4400000ca40400f00c6c0b10f040e0448102200d050301d07002108803140c11000032400b880040300c1c01c014230049415000d01d8040b120100003040d01041108001a11480d0446000350002d1071143c1c5007400103041004079130700000b42403103002000103170455404204070600b03194400000e01605d03a0310000a800001d1040603c0d10072611000000c8401c154062140c00301c41d20b180c02003c1c03e0805440d007142aa00c40b44003003107280810170181c2004542080218002c0384a0801550344400c54101281410030601342d0030300ea00007a0707504000d580c0e0301050914050000700c40c0d1b81300c44094020b241d40b80c51116400204100c0011130300091010004800704005400303118506040d21074042203101d07a4a498519043c4107805001743c01c0c041c403d2810600d000e40c42030030603403400d0201c4400140130307130880307001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 367740899 1250 367739649 367739653
    0xc0f08030a031a0108010519050301020d090203060703090c0506071403040b041502030901050406030b220f0e0622030504080106030602250c0e270c03010506090f24040c02 75
    0x1c503611041e4944510740307821000030750f40c0303800c40e1818000808601c0117214240c4a028441a11140c0901c00365002c0b0092500800866482011520400c0981000b4030268480d008217000102268000d01503090951360010200e070b041e85c101020070845130081d0b01c05076104203600484c51548036041008202030300b454446c9586491400e071500c0c13854a1030860041c215003040c0109403040e60000160b400740c4500e41004260a03102801152030304030300b030300208203116519800070a458071070b5210844130618584284294a00d20300c8031581c500c01950980360324210240740b0189410000d035003004441c464500ba134a001c3c0d4a80125082d40c1d015001039440e01c1c3d0009000e40c2c00100b6800080e0304541410401c021b4040c075840703201c10b01006105810309021102c000810004412a0464004c1d05002c1000300784360b40342099540d14051459031038065071802d400720749149001604a8482d000e04401c5c062103594203807045140044039400301201d00100c40c001c2010b541d03076000f8406001c0407680 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 367742149 1250 367740899 367740907
    0x123809010902030f073204181a01180c08180703050706080702100c050327030f0d0c0305011503020c1204030b2403192a03030909050c0a0c0c0f0803 65
    0x5900346d441000c0320b034242c041c2c48440d5089510504000300c1e651104803030000e4043c6524003004404d0210b010002c00c07007400710406410040c0c1c03202c140c505a80f02501d2840c000c0c18080031100858100c18012400300d916000000c4411521690044a041440059801003950f035580c1c82d10740107640e00600301190311503003005400c547c100002e008e50100c20100b889020045200503089200c00303001a940b084011181000b510b01e180c420102032402d50085980d96230310480c03403520f51b4100305000e1034030608040c54244076038481c0c015a41610103980c40c12854501f8000c2c1a4020351006003642c09502410001d00e8002086401905c0210300a08843c0362038501450780164070031085124040122040f00061056200060125680918038100722403004503820204c80c1300c602c07110000384444042c40407140381e844011051046a1007520340520850b21071030280300751030303013102d0900751a00103001d0480b485100c1d078404120702c0d0003200b01c1071100c0d0312540b6080c40f0071200e40101c02c0d6070380006 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 367743399 1250 367742149 367742159
    0x9090304150206100e060415080f0f0a030e120a060603030302090f0108040b070513050a0807230f0405060d0f2609030a03030e030c0106123809010902030f07 69
    0x742080304070101e01e202030300c6070307152500b9650391140707241c021504100444400903120b515954001c044030040c0540c0126041d90340c00300c584c0d8403c045001d0007890700403040ca10000b020000b0f81d090045070b040d01c5029045110303c2c1070080d04511400424035a2041c4809400400d0315881800043d500994026070358210000130300c8222030019040a041082600410000c2000c4005017074000b031071850402c0d0384074202c0d004006204615000b180d4400303d1040001203924001035004100c5079620000c078000d0551324015401d102c0301601594004280010102d42c901e02948941d510000c000d08041c103030b0102e516080b4000c00f840408881a084500915801c0c0700304440044001d5000c002503403034140014017007511100400ca0003420305480d1407811a54007070134401d464201b401a0001c01079a41c4c0c1c4c1c4d000c0c622040c880201510580307003050106554041d0600ca034400c115041e6500390010840d1890080d8080c0000c00c81c410035540c401c0814010383d41408000a001862070081c010f0324207103 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 367744649 1250 367743399 367743419
    0x10507090b190e0d020301050108030c0d170a0c050c010507080402030106050d0218091f2a05070308060402090d0f02030c010c030207060e010c020a030308070e040e03091302040509090304 82
    0x1a400885080390244203040b148800c240010350900c0705072034181c04220058002c02d50020f036042d00250b06508180001c07a00700380000181c1004030442c411680b8404070141c080d40c4d030740c00b5207040524125003c000121041200e40152000f120245089458140100425401c44009076000000520400103020548c03030309000e480e001c0c0c00100d50b2541200281da0000d5245d55201102c0390741c01d02c40d500040c82c0844180484c50314115008031940d0400960b140c0b0b2001480e184065160301105070070450405111604045200c03a5142c86080c5003912644003912001030007055603505c1034080258164589485176002c2c8a40d1052105811245041c41014240122601618108500e10b8030007030110f036001074200101c890f5418030701014200d010040780c00d0301551074003a42050028000004240c2c1c8400320a20817442d45e941d0300c2e0202403840c200000e0f140c1c1d0026881041c2e10500400c9174910300701e04401c68520f100b0500520b00b076510408188100c0044956100e65000420200112001 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 367745899 1250 367744649 367744667
    0x807051e03360a0b09013309090c030b090c03010213090e060402012010020315030d08040224070c06050c070b03010b030130120905040504080a03020a12020c010507 72
    0x45014a100400c2c840e4025034402ca1001d001c0d142c3e000722000f0a015101c29848684003220403843d107000c01c2c1ca0741e914203000894035010008903c09250001504030a10b120300303030300341c0e0380000e07600c80462840e141d001c80c980b800350006001d8085e03024520801d6800344010144984031510750490240741a4210302240c012602900040c0c001d00c08000041c0ea0090091181189003100070305203600c041c000da407500046031840400f2520000900003282101c620944180c2000c4040302c8851000000c00c03101d1600669009411503812080798030783c004451883d00782c480c1c40107101400c01700c1d0303900e4032407544410368021404034000190036688041c051052001511030062914070755454841c20b24014401485907240d5006e1304d040c0944443c030711119401c411110192004442c07441750400030003103d1070f0340306980400c034030800c009020308040c01000e10441e04400810b04010302c44030290f003c0c1d170161041c0800c110b80000d0168001203a807002d0700d040843d0000005140c07a20070000760203090 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 367747149 1250 367745899 367745971
    0x702060930011116031202070602030103120c111e1804060b03030304120e0103020706020d0507030c2111121614040513111603020307150b010807051e03 67
    0x41483d90040140c5903075400c07104002004102c90008a4480c2070813a081c489000521800d0b030700005404050202d160081d60590303004410207400c2d414010004e880f400301c52000100051130042c1c04003014036000c1042c841400c840140400013000c242c00142d0610401c82509120b510440d081c0401d00010b4130500190010079401140303182015258494000d8205402608102282e408115aa44281c0540e900154172640c15521914900c014002900d03003124120006842d2003648540e4074801d901100710710008128400350f01c0c09001c2040e0282c0000d403210400c02c0c000b04410302048015004c000c0c4101a0343c2c3e0902451048100003c0850381130300c2000d00820b20900c81840250769400c0700e04001c2c001c0800000395594281903802e40c500640000034126060140c0c01000d050300400185100d62103415550300d0304000001c110b0031540c050b08814001500b82d000201c038140943c1c028025a4020030712b1403040414103100c89410b0f88110342c0d03a1003080e410b071844280080071400ea403c00e49 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 367748399 1250 367747149 367747151
    0xb0d0c02010b01140c160312080601030605012a120f111204060e0d050f0106060e0427030c02030a06060510030c0f03020711090109140c0702090a02070206093001 71
    0x41c40d20000070a10345103200304030411301000030138810301003080007000e20443c06040c1800c4600c0d40c0b4100f01030821a61181900401e004900041d1650721a20034482580e60586460506962540380c00d100f10f41c6200030380c2e8064158200010109003080d4801214090507561103100c08182e0070004e004c03145078490b0840035807008440600d034003244020783d0280d130124a081809500c4240c0068800386000d14040d109008801e041200600b064118801740d40300c544503010004600b40501c0211507020024001c0803884a4804a8240d5075410001000d8085c0c42c00d03400e013110540020303083c2001302e00d0440703801c0d46d544030803c11400c0120035416280c006090402c600c014001000d4200303030541c102c1c003040650002e0100100f115040302070070030000140100c7e0b599a1075404c1e22000380070548031007010303400980024021189076800c0b1803540b58050700c010b1003900d505802d10081d402454007244d101a05003c540801e444070100c215944864846103168051034040034050060030908001140e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 367749649 1250 367748399 367748411
    0x103050f0f030f0901021f02180321031e01120c0e09060114010207030c09020301050307120305040501260405060703050c0703080402060901050708040b030405011404150504080904060b0d0c0201 85
    0x19007001c01594610200c0694096540105500407070502000c1104100141c000c1c000e2191044007650190208800c100903c10b0090450703020907036105007900303c844840c210704000c00501d4800030041c5400c07881c0b0f0941ca482c44410034108401e2000241c1181c0c0d41200042e05e80d009001d10841c64034028450072200c024141060101c554441c02c050241c40040c10305c1c0c21241200d44d1003000024010354101c522921401d80701e9103440040e40c028490340b0300c64072841001186088000a140f10040c0e816250680740603d000015207207a903001000355515000c03098001d022021a01190388140e1150000e0a101d14000c4009412140b015103003014111060102d440040d4011407402d4109804441054803080c1c0000102d07200e110b03002c0000c104510215000072988071000145015900c51070080c0076061000403c0c03d46041c0403100038015401601c6041042031103036010a40143c0910841c502e010f0503003000c01c0507200f00c2c0d0301c406c03803d0200040218400119204500ca041d0b418802480a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 367750899 1250 367749649 367749673
    0x10320040c0509100207180207120e01050d0507050f04030506040501051f0501050f090a06170f07081302040906020a020a11041103070815030105040c0303020607080601140c15010e0103050f 83
    0x365000f40900039000b0003038004210356044c0200402c00c0209080c03d050301241c0e1400c1501c00c082e40005070200c6043d0707018000a80c0320380c010000d244142006964050038060018100b001400000c1c0168050140070000e540c110502a00204040c0d4050402040103041c80d103017140c21624001c01d241c1190a8103440c00307025280c0144d5080c1211001d103001c3da11801e581510314140d120b0184070a600c80b00e00d1000003050f5400ca85048003145810b0031017001a59413400741c4a20036004c542d42000610340800107402e4403100d00702c1a44060001c1c1000409810b55a0382600702c1e48081c044401580c410f00c001c1082220303d440c0d00d501c00d40c0c2a14144260300c1940d18200080c007001c0c004005100c07482c0002008001048044000090014024452403d0504103400142414001035005000340000142c3c440e0240083c1d6001781c006a60740869942d00400c440200d4110f03480602060107a80d40f201108905825000d0180c41d9096115046501d903103403651401480c0342181444c3e8000b4610191 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 367752149 1250 367750899 367750907
    0x204050616140727051603090c0902070c030218061804410f0a0303200a081e060904030f050418150806220f080c0a0506010501020c06031914010320040c 67
    0x2c00d925040206607045103280085842706107805c811446840451501d00740203204081c0e000b03c9009403444614004040000710b4084400c882042c1c20200100b400c190050200300000c0d84540214100000a514455007801400e007401c600016841c1000b0705d80f00c0302256180d25000c00c10b40c44002c0403003800010005460b00344e00c1d500a002d05a680c0000000c44410307184080400c8000c1010306d642d05100c01024040c60402c0c4c801c2000d8000d00c0060121500c3c48540890240e40010050581966655401c98a510342c0d07402c0c010805c9014040003885d10000000c1e80400440200c0100f00c0c000c01340070000d94105290b22040c0366a1042c002c1c000560141849196501803082d5584041e010700d0418814000b0380140c010901c01002444e8904005d0101d100c0b090584280f05403402a40d0700e0004a0782d411400c200103504c00380c10000b10300b11a208080003048961b6041000c15030103480c0c4c50201d0904000d07442034840103225808031415140040e070140928100b25810010303d181c60b08014 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 367753399 1250 367752149 367752181
    0x1c050c030c190e060402070804090203040303110408100b1504061d0306070807050d021603030f0b150a1809110309060f01060c02060a120f0e060901020405061614072705 74
    0x10183d070150404115a0b0b101ca4044a000680000f9403070354a40e51603110f20b000f54421102900081d2501040062003450341d01210100d4840030b000f0a0300c0341c0c0d00112200182098041207600c80c00c0a05528a901585406000103007116101d6002d00706142a540090180142035203203e5009642081085500314106540006480c40c16507204c003401d40e9910028451002c00c20343d03004080d809030b0101581500810300b80b110070401030103140010018440307400c86148441012280c04c1c8908980c0e00d2007564064000120061402809951420580122544e0440f9103c0e041d0000040040720750301009165005190304410b40e1482d0b141c554001e10141c1c09100082c400c10000401400007441910700070113200e1484030400c084140344500e00001d04140e05120f02e58040e0f107000814160041c401d40b01103d4007d0400391801c04046e01190440c0d400b40c030300300d035041500701081c800000c042001201402d850030402c4009040080b4207072100c0000d040c29108141403004000a0340b445013030380c0d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 367754649 1250 367753399 367753409
    0xf01020304150c051501210206040b090f091618050f1215090708010c020f0a260a080403080f04020d14010e0109080d050108030403030c0f021c050c030c19 68
    0xc41c84510041038200d9402c92002c40203080791081424504511017040c800c1c90403181d0002034000040c25400b181c1c1c0455190b004061742c4103e0500040007060501c200409010700d00501501c08404180c0004070040c00a0b03072062481039803120648149500109038610140c044107255071420305d4003002540403004240c07098040c0456010040d06140c00704042700942c600e035100283c040c9011840c2c030b651298580700c0c802c940c2d0b0911554405640c004140c1e0348010300044044c1020b4440c0c0e440d902200c400140782d106084a0906c01d0b2499280c80b41c2c003070301030b04009569680c1c0a040c641001803003284042c014911401d200c200b4040160782e203e1120100c96407000d01c41581c55420309030701d8010107192040c101c00e03500b081108010003082400910101c1d90000d0200081c1e40c9a0921507a2030059020043c04151200b030004040f0342100c2e2003510a900c01841c100c066002c20540c009040d0502904035096400081080b21524003400104426071084d190003943c80425a42d00410200500c51 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 367755899 1250 367754649 367754669
    0x60105180409110306070c0201090504060e1b09030a0b0103030305061c1502090307030c0e01060201050f010b28110d0e0310090f02091f05062a010b1c020f0f01020304 73
    0xb1020410716850300d144880000742611001e00e402c00018040c590510412070024128503000b142501e49845100b041e618000c41d01802a0340d500c40c103005900e011511030f14045020b0025403481c0e0384c200028040076114101c01400c035455890054180c41e00906442e07c1030b440c1320000a070501d8402520304e0b103e90071880d000313000d0000307200490082c030074645c5503501030107480004010705c6800d9001100b200c41c50070540c10f080c0e03a102012400c8900685e498608a8081d10042180c0b0360b40d8000b0b442c03520b40103d184103074038a403140e1040d40e080081c030950000c56078003445280f044a00303100a440c802d0341810940041403041001a0300c400910740100511961580c401050260000810b0f0083c2d5000d0590601414181c40f900000c58a80d85a450501c0c038200e0f010a01d802d00c81c0c2511124580500340d0750600c1e070611502410003018a0581e003196681e410040c040380d8900c3d0030403201005614001061800d07078014012010f042803140d47c0510020005d803c1941d9000040344c0c102d0b081000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 367757149 1250 367755899 367755911
    0x80c0102011103241f0806040c021905010f020301150f0f0e060d1103010305011401061d04021809010b0d0b2409120f0c090f060904120201180b0402090601051804 71
    0x4141440c441220704a805c41d15813840d00c4542880e10b207185040820a8844031456682e40c010081980d07510029240141c1240c503412442403a00c800c0f0305400d42c86940080b0b110a44518201c0c12a00242e0010768040705011040c15200c2d0014541d00010300b151801d0300c5886038890001d000306e011118050f0040340c0000340040710940c84d500c08040e800b2018141e9949596038240b40b80684040b00902c420385021400014038940101106c81c00d8220032200c00700700c4c503070761800c00000350018520f81c0e03c1905e00c0500c1d5010b40d40c0ba290014003900c401d11200703449041c0e01502101320303103850200038010745000c081c00c403114840c00c4c10010302c0b04540300b4076542c0c0c1007101c022803100c070b8041d03420342000e200d408500700000c580855101710b21070081d5201401c0395512103c107000400c0a4640d039411030700c420003280114040c180244806500f40c000450ba12800e441c16212034040d40b401078a0b1000b11034180001c5160003a19150000402d01c0d10383e040020b8109240e40070000100c02520842d81c1e04 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 367758399 1250 367757149 367757191
    0x30e0c010503070e0406090f0605100f080a02040305150702070803090d06020705010603080a050c0c040204030f020d051c0c05070f0305120a0e270a052403030f070c080c0102011103 79
    0x400203070341004c003400031301c400b907984c451400c080c00171190003094079400c198000c0760904115010102c02081a592a00d444124a00641d0700c0345003d042006459000c110100114a04110500340b008403026100890701e40098001e080144681007203640b5081000240040d65513072020b280320341e40002c00143c0d281381c607250060042003c0e42c0014900600803a0072f192041d00007001c0e0001001040039503c000420078200000c0741701d6400014110021640c500c40542007004050304060f1003142210b007240002000083c2c01101005107000042e00705103a07401f000421300501000340a02c84908803001d00b190b403607645402000d2106d541005010408040c818815488248078a42c00382280e00380342c500c0b061003c0d0310030885034245020001d010102e882c0f070510b4424240b0070791384c3e0440c001300a202c8040f14280c40e10614504c0d0307030612051040003a420755141c0202502441428151040c03072403c1002030030030b1510126941564942405144c140140a04580d07008500300400c4260034021 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 367759649 1250 367758399 367758407
    0x70203090f01081e0c0d14010e010b181507140705060405010804030e0418110102120306040b0604031b030b0c0a081503010e0f010501140d120f0507050d030912030e0c01050307 77
    0x841e0781c8050000c002c040c46842d2242074010a4501d050340011f0003689600e000a2160003400c0c4205990742c04c0e070500421130320900c040030f04083c18201c801c1d6190b41215600051509a040c0383d084c1110744000f441608120581c0704820000350090041c003202c5182000142950041d40305031814040454000b40405208040891001000500c1000000030300c4001300211028104100d40702c03e04080051303920760000404000f41200780948610356a141000d020280c071250210680000d010b000100018146501031503070102083c0c0569401e514509108030005005420320080301e200f040300341d4045902c41c0e4040c0d4003440c81c0a48a0700034904c03a010a004000d0015280a00e010362074030a42081c5040d00039904960001075518411100c0c5410042c8242550350020324811855000c59007150007032101c84033011a50400c0c40c2000c0843d240c080c282010a01244c0001c0c0d51950081c04102003685c01d60b8852905180400c044060203055695400e600c4c149241406004000101541d100b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 367760899 1250 367759649 367759681
    0x30f120c02070501030c1110150509190c0f0c03030b0d0b04120206100612050903070b010806040309090c0522051302030603061303050f0306040605091e070203090f0108 74
    0x1654040000428030903009445140c00d0050900103401c061030485414460340203c200d510f60781c400740041881c100310901c000e11a440d2880c040428003807000030b2981e504c1a100e4810030113144081e14004074030002c04100e800d41159007082c0194a9404e0f95882c5c0d0040d660301c4902e0341400d001540108010014560749032000e4002c245101860400040103400040b80c080b1100d15000c45940707841e103c44543e51548076008042c0040c0072150b1410400140d40c0007207421100d5041640c0c60704240707444260260009810000c5154024400c2c04109540607216200500311160101710501c0e00007c020294031416a8980c0072492a070001210800f100030502e00402008015400342500381700c0d0880070f0b4008039861803180c01502c0004500c3c02c01041e1100c031003503059890034600040509200282d800190403c3d801595502c800b1455031544c500041c001c40b4084045400d02003504000110300c00000c052000b150024044110f40e6140d984420122943c2401c0c00b140ca42e440ca030900007403490b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 367762149 1250 367760899 367760927
    0x3030f0a2903010b030106051003050414010510080706210506030f0f07030209090303040803010b0f0403171224011d100f0906050307081b071202010501170a0b0103030f 74
    0xc10341d50320801c81685040c005a03072010780090141418440c200340c200c4d0784504c6215001906075803401211803180d40020b80c0503114403e000394955103014214210b074011641070000c52075025040c4280c05041140310000c09084c5011103401c40c0c0040a00c054407103004071030010640700e0010803140da80502c4100c0c1e10400c400c0458598002e040d0000d030f40c600030313444168041d005c0d840c04550310708800f2086030710898004070b80c03501c1c591824041400703035486040e000550100a01003c0300107220500000d001400065689458200c0c40b181a841c1500160181440001f0b00c1805030740004a4401c01e84c004c1403d080c05541c0c2551080d07a00e5681c21030305c83c407582c050910700d00041d107550490a2180580c140750345400c00543c4402040d18107110079190703400458044030003e07401501401210604607180300c00642055501e60700c544001c4402d80403200541d448000501215415913140c801510a80004007500000c94903500e0500340103010260800401400342c0d16030034066070920700001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 367763399 1250 367762149 367762181
    0x11120702061e0903040513022b18020312210c130e04030e13060504092d0308130311010504030e030c03010917161e02040b090114130e070f1a0c03030f0a 67
    0x102c50144091108890f07200f118270150f01d8014a040001840d10074010025800317401402040c520b00f800c00d021703800c90802c0b40c1c120900c0041348803003d18441102c500540c2000512a1180718003810040d0f114419000301801700031440c2000f000c694482403244100200351044450203070703440154000b6145541103560813500b000005130030040403901c007110303128a10848030071680c1845940c040b100b001000c0070f4006a078a801181241f03580e04500f500b05407182c20b0002d40710707000c804010b00b91031045506901080c1020f100c00450b081c01e002c3c005020508038001c00101100f50f5400040d0f0446100c08004002c01003000b162004081c1e064900f0940c202c82c9500200d54004640e40e07000303000d224224011801c000309028a03040840303509060320200084590702c40031060901c049082a004030304c404684904001080715814403018003e800f6042032060003c3c00c00a441215069201c1a00741d000e0341008281c00d40a0044192504141c0641c10440b40341c40f4500d050001c5c0490001c506187c0d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 367764649 1250 367763399 367763437
    0x20306270304120209010f05012703140303040b06030706022104050a27060e07050304060f0c0e03060606040e060111030f0a0504050f0907020601050411120702061e090304051302 78
    0x250200d41d0002c0142c0300700c1780782a0607a202c04220340f00351903610aa078040784925841042410310600c44559501c103100400c1143d55480d203500710100010f6408698a030800401d01050142d510a0385500c0306013135000b000584d10740305000b541c031303070242211028000701403240445000d60780040b02c0090100501020080d44c40d44071849840c00d00d410f82d100e103170140da4103e07200c032425401040111001c2c0400e2040e19501d2381c00a950700e80c002041211020750320840704c0d5203406284100c400130f0719140e9030355240c40c81100c285440c003c00038141a125140902c81001400f0f408000c03154007a8082c40e01d00c0301110191032b054a140140204036145042c04070304207589541c05000303402114021101d02d4101210320042c06200710041d0b410394016007003000180002d0619400c223141c900e0b900905c0615100040321402e0902e0307400c0d10060016000203090140151420035140c07243c42c41010900100e0a22900d850341e60702c02c03441900d0040c2c0010604d04000025035066484545c41d810020710710b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 367765899 1250 367764649 367764659
    0x3020f061602061b0712120e030901021509030304060b13020409021305010e13051e100302030c010512010e0709080102030a05090f0d2c1503040519020306270304 71
    0x81c0410256000c070051007080001107421000044c0c0d4415040c035401c2851901c842c50b100c000701c440389001e0000a00c0441c03a6031062021540c81100304040c100c0b0007550f25092034000090070712100c24810500c0160300e1090100148010080340c0e0000c0d1712030000120b002602020078886901100c22080c010302c003003030014407076000c0d800920111140300b14038a15180c0b41d000540d46c3d14040c000a9812074100008030121132065400560411071141c100e07a60585003181d00640c204040360072040750911090708004501b010484130f00b00500900301030381802c01c22800001051014070500204109000200c1c5000780600800f00180203408020b540d81d1400b040c50030060302c0309a03441354180c4210a50007081d11004a1005802580b981e141b05600d0343c1501355003502c01005800c650100c40700d00e10030125503281c0781c0b10380090403250300458480c80c2500344282801103c1c4d407441792002c00112402c0059902103541a070184082d0f00c0781c841c3c40c030304145801d540c01e201400008103201c00540814 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 367767149 1250 367765899 367765921
    0x5060c07080316050114071706040605060417010c0c050d050703140d140603030a21060b0a0804031b02090c0711150d0e03120402010c03030216110f030706120903020f06 74
    0x302e980070303000070310110003048001c8107140340803103215000440c0003041045045160108c2d541000004101080441c1c540002440316802507000030703030031004a00003450210080c003400352100d545040503c000510b54550645403000f001c103010400c0800900041058080c11a064981c510400c8c015100c601070540b43d40200701c1370380341201c0a14400c000410514000013124003a03551580e590310034051182c084280c41e05481048494141c4541c4041841d80c045c0c8050480c441c2540c0c0ea0203000e042505020300321655640480130039036054080400503131142008190482c035141f00c61a9900550300309136401c922211451070703010f0500c1b40005a0b1001410151404108804003041031560b5502c01d030741d40380705905000c0350880d40600014050340c050504040305500a007030151510002003805d82516585000c102d403604001c0e041c45000e8203180f0a01d00c48110700741c0040c100c0307504081015080301d4011031218060b50300c034030f041d030704251003485502240f031526400c403202e90408440c041 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 367768399 1250 367767149 367767187
    0x92a0207291b0c10020d110f0f0c01080a0603020a0e0601030b0a1511060928050d02010606030b01031e270b0f09070b0301051009170f190206030105060c070803 70
    0x1c46079200d04003c080680c540404052100da0081c5c009104c9411130340d00c10390304a42490303030814141c090700d05021a003035402d01a4081c9031390400050540300d50040e001500008028080f2219145040b1092006895180c01d43c81515203a0080151550b038860040300a400412049a0840e544280020f01c60000003001c00c00c40b40c15445100e400e0481c40141640d0b96012164203940f584001c8000721091301c42030050a039250030701e1240e1007400840d1242ca242c140703460746110051b95116810404150b0520a0860700a000d28061060450b41c01c40000426002c449100210380d84012080c21340785421382280308a04e60300401c501c000804d00701801003050841d1a4050364a2800000329401e5000c40e4001c181d50500703000c2c0e402c5900b400c09019400419000c00b80500401d01e10228404200f00481400101500e004201050034403c120741418056a50803000d8034000001b60700603035444c01940d0540300c0076500280c036140f640343c120707241006992004049001c0094040c3c12582010088 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 367769649 1250 367768399 367768447
    0x801031a0a0908160309090212010b070503090a080706202e0906020414042a12051302030f03040501050d11121e16050d09020a030804092a020729 64
    0x17204510790307d44201d003d0b445081d1641c6c80318990f40006004002c00e420140240e03502407004c9074100803924011507044401c0e0742010105034403843c4200501d1390700070203415141c0c00f0154030f180100d0681d600140c2e24500d0b1282c01c21244807103000c115480014010007440160440b000f4081e22840341048002036110b03000d280001512a08918860300b094024090720000e890f8411210300c100d0300e00c111000580c140b0500c00c0100c5c003901480c232118280a990f024007011010050504564030400d0304d090b1403c1c04581481d0410b010420141c0e0300001514070b59034048002264500c1c1800c1510601d1007040301e0340750700030080710900c42c10114003090440008100306c074580c855100c13402d4404c022880380e4900c0000400401001401140c25000544080c0c800351945801c552030b9a901e00043c0c00c5a0440d40065a54520703065034100d2072984d00b000384071500355842d121080ea001c02511111107001d00e00484000010b80c10030300c801061140314901e000c24005483e20b2480b00c66020007500b000780 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 367770899 1250 367769649 367769657
    0xd05191b0801090905031207140301030303020405100806030c06162111030c0703150b09040602031e0f0f0408040807090b01090e310501020c030301090c0801031a0a09081603 76
    0x820f24209a22400100c913400c80021030408001c0c03450100201c4009048501f0000c0c40c1c01c005500310f9801000d14003842c82031300c003d6103072130400080c803080c02c10034103005080101040038462591000b00301d2000d42e18094445036a1442000c188000000c66060020b25110700443d480000340200342d510726a07585196035000030754185110081e981c2c003640003c07084541100e002000041c41c0100f603a5810284010081514034170800040e070130404c02c40e801c6c1c40ba141c00004105076904c130b00c0d012070840f501c042040219030800b0410780e015000004c007682c222000c888049024070540100341d034020b04244040715201c540b14002c0e0005070013500003c6021600b2007201064440110180358070592499a410151ba1400d26060440038455048044140c0120081101281c4207000600c9164402c000550f941d500d450482d1040381c810b41c280c401006014401400003518280004104100108804406880703001c3c0000090003000b0300144070280025050a200881400101c00c1d80d020348c40d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 367772149 1250 367770899 367770901
    0x5100b04140f040e010e0a02010809070303081512070f080105010e060618010e0607240c05030a050423010507030b060306220f060b03010e010602120d05191b08 70
    0x40101400e00030350041c00361001c40c850035070055003045001e00407032000081c8042241180d0500b0b0508403142d50880300060f40108103401e040d9600141c5042c0c11946000c01030080b00e00e140c83c000d200030350140085030080c8528250191603a9805011050720003550240c48242e65510300710a0311444901c04e815a55003000d00009050500704000f5100c0c1c03e003c0c00140c5400000c41c44980d00c0b4200c0404a0b050005042c0401c851741c44403009400300c103100701d8034040526502c0d0009011800800c070194080313410441d43c07104880d482405d41c0d4105500c407601054036140c5141c0100d000300a01d010000707512102c00c1c1d5081508054004034082c4e10301e0b0310304201d40722070f490070b1208a1004852481e00002c0c588600003259200e04428000300c0303030701700300010203901d0089100e090300c12640c4080381100c008401800700d50030280c401360062003180001e00103840c2c000c0640e0700d0341c0200c44100c8043c561b15070010f04140c0e0b2071000c0c80122020240c0410040001448203030a00301d80382840700005031110 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 367773399 1250 367772149 367772159
    0xa120c0c1709040e060c1c06030c171002030c030f1b031602010b191701020304020f060313060f02040614030618130f0b060103050601051323130510 65
    0x604440d400c1500040ca001c1818241e001c454215440700300341c50b401c10384e03866401407042014001030f40212050301c40955034540545903018030011070001480f01d80e01d000c030f0400c005456629640c04131102200d0f200c00300d007100e096550504100303001d5891a1070001080000d841c00c904015441003030344400e4030002e6260b40703110050a43c20400101000c140400105403e0008025090645990b40c80080f074120485c001060045c0c031512a00100120700320001c0c011440341c0c180c02d60601500304021401c3d0300d8241c0000300d0400c0640b00c3da0707000b000000081000d1010000520300c602d50062002d11440310070403c1c03d402903029229500016001c00b407030507001c0542400b26401713100d00424203003c01c5860281c1c44d8078076001600c00410019117028150004c3e00d007040d4401058021207034400e0038505400090151078000740139504110082041a902c464180141015592008441a540344400800f8940c05a00ea80c41035404850554105c28120032500158401e11b1440f0300d800c100c80d611 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 367774649 1250 367773399 367773407
    0x402040509010c140f160b06091b0403030e04060819051c0c0813030f03031b030b0105220b0d0203061810030605040f06060b0a09060e030309240a120c 66
    0x1070b40c044005200320f46804007445138040940400c0440501461500c00aa856110041510341d021103d45007440d0410101d4034099002951068110441c03542490340d892201d600c82c851400010305007c019200000e550300c1e26030000d0050041e07641210080210b014642d004a048100b007242c0303920075220b020040144d9070030181104849515411140c00d81c580e41d0200c0794110451504034001403c0b800404214140c00302e8034094001d4a0004898050b8080c20031518102d2880d40241401c001d003a0381c2c80d90340401110100d880000640007800b444100d40300c0c6030350a540c0840d90b00c08001c9400d14081c803ea0f0700a40c0101f6044a0301010b0303172040f441c500b07614423007141c0358080319005d00e0042002c14540d4014980c854450300006059445c541d031041c080762103a41281200c100081881011190001149405840641048915182c0038000070395a03101d901051801000707030014200030542c0710030442800200a1940303940382c0c001c0e200000e008200403c070060391581000448401d207801 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 367775899 1250 367774649 367774661
    0x90a02100f09030f0204020d090f0303060503010c170403021006060306090e070e190e030a0507030e0d2409020a0e04150603050d030209010509090702060126062a030a05040204050901 80
    0x28075241e0911280c80c6413104841c4004007241a600582c003086448070195039480344c40300381445101001d80180e00b0307040040440344a134203c2402689000d6200c00381c00e0b00103e02c1441484080318441640d600ca00d0101d0901c40f0600940b010142040380116405030503411040982c1c1014808020494801c28a40c0d0745020131703c50780070305902e00d1012070402c958401510900001c00900440d6450310408405c1c80d5030b000194010000e800410700c04101540641b2440a01a00b160303145541101a1100c45606040b0a117001131540346032541103003000c07035070040000c145d001000d001c030140d9500301b06000c0c110200c800b2104d07a449001405910016441440701b035036008001882c0c2e100482e9001d03030003988002d03041414080140310182c129521414218403500142d40500215450302d0042d480d400444400f4201c200401c20101480d04800114035501c070a2540c0320714080d004092030090240721681400d20242800020031060240c113401841c092442514100f21a13a208d071501400c0700d075 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 367777149 1250 367775899 367775927
    0xd050301150302220609030c08030304021e030c150a09060203030903040320090a0e0f0a030e1e060d0204180b090f0c040801090302100f021204031412090a0210 70
    0x1004110858958401c0e8050031342204905940710400320f00518641030204140d01c8040003422020050040021101c0182c1c000d03c0c1c08401542981001d900142d604070b050801c00004119080301d10800d81d5040084903041e00028081c82f14429803044d4200c125440790003080301144030305500081040c400400c492180e02e44101450806046541e003a070b51403003c2115244c0300540540500740c5596200030140220741003640040ca0700034452035203003440d0f000c000c2c00c1030030b4000401c29004250444a81e1848600817100c03260480b001e00f60101c10300c040c60440c1c0307401a00c00325445180b148513600134400c1e103000540d0300e003854185003c1c44083e03402608469030401e0380c1c0340c0400c0960300300c1420310b50040c49805c8441c2c00c2a480300442c1c0d0031640c0c0d500098005070b06c0003241414004583c8181e0140280c0e054055290a020803641d1425000c041c00040410a411550081180d8240c0550f00420071b804251125414400d812580d03642a600e0140c0c4600080041124482e00801c40005411 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 367778399 1250 367777149 367777169
    0x110c180906060d02030d03051905070f020606100522090212070216050105070b07090915050406050904050607050a030207051e0f070807120f05030703031409030301050306010905060d230d050301 85
    0x10b0040e6007c0b409014098240c07003161850b100341003e401c03103e0080520031416540c1b0352090440130f40c2e00a00e82040541038900404006450240c0550700c00100c410100e208a5504803001924001c00208803d0381c4c000b101d00352012800003041c00c400070049000383c11a608444c078145444a0948800801e4850f00e4007060081200c1400102d0b003480f8507501403014108900c0b200c0c0d0715807191003903612140014100c070b45044420700451a0a1080c0c502800d0b040c1d80c2100a46840d554190f51190050000342c1441401f081602c0000c0c0700b50115011194003406407003000b08241d030844500c0720420803404440c0030345880c0340c103c90000103084086585c800014120986811002c403220b085501c0d003511950001c01d08980468410001420306510990340000c45c10008040d00705401c01c0038040c510503401c100f00401c05680c3c00143d00d41921242080014203445440014154203c45880149101ca880f85034030703049882040c81d0080d096203802540d03d003041c144000c58251009005120030f403 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 367779649 1250 367778399 367778413
    0x106030615030b030c0a03231b0d05030f041203030b010e030c010815030114061c15020a050d0f06031707030c12090b04091a090412110c180906060d0203 67
    0x50b00c80d0b0040c900008024042d940e0301d92240010070101d000940041d22030b0040101e2502c0400c42107128100040101c0703000e0422294426038982410700d50840d1a4848d0038940f11030010b0003018030072200a074080c41401030345c07290740b8101418100f01c410802e802091401c40d8070307000c0394068020203500c58001800b40c00103019000054a8413540541681c40e1420024480041e0380c80910804095402c0b80c8400303071151a02e0001c00c046c0d440314481c8030503003d005069810014081c03142d600d003040300003800580c980b0403145048849008286440074018103000d05c1d40103000c1740d580114140e90080c0820032030610000e015044c0380c407403040c009001903881c1c41064040303007074144071203040211880c26804050b80c2d01c240202542094200140b2140d4420380c2841c1c1d1001703040103500f50101619550664a03241c0c50780f2503500c2c00000321006001c3c00c961400540c02c0d040c02a5000048002c1c0f40b0540c0c6016203189000000302140da5070f01a21500300070805900e008000003d00c6940107008002d4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 367780899 1250 367779649 367779689
    0x207030806040c110a03030621080409050703020d0207120815031b04090605281b030213030605160305010f03120c0602070f03050702010807090f0b0c07030506130b01060306 76
    0xc100003e110401c1103c10030007495010814492400020b01a40d0302107a0541070408501f000c800240c4036400c0d00c3c580c8000c4000080d000029542200c040503c00552591181e8041c0c010340704a44042c0b480034800104107007000b614045c5015000413550311000d00340e880000b602e03070048110841d10b41c1903214500420121002c2d52840300d07032a42c00b03000820180f103255030344030a440065555240032180c0082c00300241c3c0e03105400d400c1c4000503120034418040d400c0820801084400f4414080540002e0b41d08000d68020358440e0080d82c0c020400c108900d040001440c80e0090701d0b01c640e001030f00b01000000c0301e000112009051340d4000565580b038103144401030f600c200d12844110744190f001d001c8034002c103801030402001a40261582e0340d46400e50f01c00103068a030000c250b50300b444040d40003440600c0180751a402501c08840513903036505032a050b800e01d0036155074002840b51281b2130401c04c041c541c1420000b88580300325041c012590b01c412003581031f40c03543d00596071029803850300c1c60700c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 367782149 1250 367780899 367780901
    0x10c14040b0708120a051e0f04200d03020d020106050f0307060e01090b0703200f0c060a02030d0f0f06171513050d030b091008060414070803070f15020703080604 71
    0x10701e0f4410251107151404c4410800421401141c0c1c684045507603038100100c011000784021100014440c100202d03103019120460300b1180a0005840c0002400400e1442146443c81b4050742c4002010101071448520340255180714121901e0010b50030140c00042d6070038414000080d1001c0180901545400c200089410038559200d26041090250b00010041c2c088001806d03468002e581e0304031222540c008281901c4611024143c45601012040c410300b100403038440c40c1c03e102180d4203aa11215088201c0c9035019040343c03100702901d006d030000140c0009601234505001500c42c03d101c42036031500510035000381c0d1306c59403540c1d0300481550a034050703041403544d500241c202c828a144031081d0319141d1038014591101d1020a5503100010300d9442d181400c903030301065111240b81790a0600c08001e03252603001e031005002c100c41d842e5030143c1140911040380500603060440e52942428204030400d0104601c043e030307480c51181100300030302c1e14a00031200b4013501034403802030b1a1101c4003480 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 367783399 1250 367782149 367782157
    0xb07060c03060515120606041212031b0e03151603050a0f11090a051c0308090f010c02100608030a09030245060409120c0f0c0605030108010c14040b 65
    0x4410156686030200301c6a5684e0ba001d00740700c0030000c206071500e182804211546502401c80c07407148009002c10000c079410f40758052001030744111160a8807085e18415000741920340d0280058150b00000c0c4000d0300d43c0821240004203089046440c2890305040701c140d1924140e0b0303c52503d0492016503100e00d4026048250061b45002000030982c154034500c10899078212542d04107a280054142614540408110090f0000325a8000d1200c085812850303034882c09540103040c84841c20002e40c8800c0d060041e80c51801141d0020301c4158848c4400030340720506d4101010003103240c8440402c0304d000c000b003582c00901039501e507954181c0c295001c200e086428400d0305151001c80201351f4401003004281150803241c4890341d90b6501800c4500090141c42c01068540554600241d00d408100100f81d421001e00850401001e2041c1504041d120139840c904042d000000c11500091003a1307110707004504075085400200810701140804403168541106801402c0340181b20070300050700140024 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 367784649 1250 367783399 367783421
    0x41b0509091801050f0921030a180203030403050106030311030a080609090109140c030106080606130e07090e06040b01080606010e1210060b0403210804111507050d090f0b0706 77
    0xc1d8078042c0c2c5800c0c1c61403e4401c101c6500c407444425038140f2500844c10070501c0500b007420b801154080801d940c01c1d042c41d02000303102c0b1054607160010801d054400e007400380801070b0050300396a0b072541c890429502138080ca100071400100120941c0100b201d011043e9603048041d070360750039501c0e1180c804014440c180504070f0202c0c1c0d540d5050301e1002425252452103900e0440c0c1c041c1c0a140c6d0b102c0101400c4a80560009080360041800c00150317a0307032011581c11242e00c070b11000031070f1450030940c1c1c0c0c40c00c4025004600312302d01d04aa001d104c4400007640300c0c8540d2003803015000c503130b03200c0012030340b00c11055404501103030000031441da8526103400400000d00d0140b080b100303002e03180d84400303055450a0380400246480058180180321024022980c0c0440280f14901d114580035002003d00d4070041024101070f40c42e002c1c096280d41c0c0c1910300b0000c440c000e0041070702c907082c2d4100207440300505061035001c1903040302c0000d512100380303c0b48412282a82c5c925420702400d600c0d003502901a14000d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 367785899 1250 367784649 367784671
    0x102003010b0d20070501050702060705180402131a0d050c07020105090d081e03160905150f070b07170a050c0d090c2606060409021f02070504050c09041b050909 70
    0x410507800703c0604a0107000c0c000202c1c0d2400c00307200190400d80058901001c11104204200c201d480b000241074034850280c0780181e4510301019605100a0b05802c40190f0004410305e400380d9420b104050480c1e01c9032a40b041001744c46038803801c00b05105803a0001c0c0410300c04e0000d02c17004e02d040709407090740c0f500480c0d01510b4002e0040b07084000041c1500700064055000c401d2100b405003c02c0200032214040c1410f0b0720b210705000c0060001c459a846c00100148009500ca00481d000002d4507a280d61114640400c0e00300074101404131850b144180c01e8800e402000621109994051640603410104200b0f180c01208811b14015083d00c0100381c40c1091840000500481c801d0f03140500c42802c080100707440c41814800030304018002c0c041d103102c0c40c10424400050398032017980320300201e0100e00c0700300000c2c12a40242c0c100500b40d80b00315402441d1030100910720500e0b0006040420301200c00b00080021845803400b1034241840c0000003a1007489100200d0070211074054100040c418 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 367787149 1250 367785899 367785941
    0x509130510060311040e0a0212030d0f06150314010b0f040305030c0109020a15050a031a1905010e0d110402091804050d030501050d02030604060b0103090203102003010b0d 75
    0x44152a001c050310003042a25941c15040040c01140d40380b218464404550500841130b403d18020f540d03821300711000c4d218025154260045500c104100c6404604200c410303c00c0b1649503040900811940c0708203c07108000f90000f4803c11f110340301d611701d000c2e006040c400940e400c00000f03051540052008000300c0e141000040302240301040034215001c003041c0007040b002105e01c10f00031444003540c8000c81440d40f0352001020540c001c1c2c02e45044c003125150000b0014408a01203441c0f80c010324a2a401c141300704860903201650090b1042911000e07260804042100300c02e00c04240341c0c09a020b000d11a00016201007854540c00602100c8802001d030b501f41c14180522040416064408850303035030102c1d42ca611a41e801d40245401400c00315401405c14a80c1c0d0003298a482000b08010a0301d95542c48041140e80203900a002c00343c1c0240858107448541104140280340c82c000e0f514a44c10000b00180251021800b201c2c180c4101c2000903081c1600702d0030b1180940003503e640510840e003c0c0c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 367788399 1250 367787149 367787153
    0x3060114030906060a0f0b030112030306030614040c0b0a0903080a0302220513090201020606190f0816090e03070b040602070f0602070605060910050d1a0711060603031201050913 78
    0xc405140518041c1c40030385024149031040003c20782c0140d01c6440d040311000340410540d00c04e40143c0b4111050442240c04515091408400810107608024907084c80e180a01034510000b00500c1d05c60352082c248848000d4860000100c0c078042c900401c00042d291820501c0002c8800e00902907100d0340f8200941040c0c025000703003d5018500355100a4050801800c0090380303891240001580c00e0038804010542e481c0e00004e4407101c000749494080c030204408010089c3c140039043c0002c000b8160f02910598480e402661aa1071244501f40001400140440c000d071152080220401c2600700540c944412542e5544d84018000d0007038030a03036424042100800e20504034200140e104110060341e170079142c035080044030f10260101d0301411041c6c007000300c0002c8204015013516012140f4146d00b48252618419000f441001c016445440006108402d500001c044400843c1481680d60503945c0740d00345070341c034020f80d08000700c201700481c010002402e226400350741002c407407a01c903c0c03046029 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 367789649 1250 367788399 367788437
    0xc0d021f05130b030408030109020304020a0f23100e01080c091c02090702061b1606150501080c0c030403030e12010608240f0c21010303090e010e0f0a02030601 70
    0x10440100c00300c0e00000300c10b00e05040303203034020000d01581d00386641581400e031601c50140c0014011074a40d00e84c004080380a40da02c00745d07090000e155456190340d030561a80440c20385014030b410000d01c4002e620f0340d00003180c94000001e00350f650444c0d540d080a0300b801001150f440c071004d842d00d48185000c0041078904d80b540b4610382143e0200010580c07c00104e4418000c104000600b070000715001207041c0110303401d0781e001c0280d86046581909459013103140d217204070041d440388028815031900c004800c14045400605048900980362a009503451000c5422188140e000580854000300800d1000a004011050101d00701800b448500f6451144940c00c584e0940c1007258950321880316014046000c0e02c08c0440044000030b4001d43c0d040502d83c03a0303200c0c8400b40081c0c48180c4040382d032002108820311518030040f080b050074002544d4a0602130042900c0d4000e1810380b52440c400442d0b950032075003640d8083e103507000f1116140e41e10882e1500c000c1d040641100d042059554000f20b84040da = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 367790899 1250 367789649 367789699
    0x80606061801180f030309091811060c0102030a0902090601050c0307262106032a180a051b030402010e040e0f03120603010b0a08031c0612030f0f0801080c0d02 70
    0x4035080b01c4139914110308000c0e19070791582c1d00c508165403c21036441d42c400040440c2005150f404030400740205040800100307240900c030110690340d031000c801c1101d0708085401204501d402940d143c00152141170044805200709075040d0000d500c00c2120380e0005c1e0f5a80e40d031160b0071181c201284d0841d003c0da10108056401136000e804810000c20244200c0c1c0b0342c000c5600d8000718201d00801111010b603621400e00c5042c0e0510403c4c041c1048002d18980d16120000008250002071400f65494110b11105c0144011f0300d9410308c0b01c1d501e43c0090280081407080360700568058491890a40803403080002408461904991034040c5100400c02104c00f040900060faa903506c9280030303442c0940602d03084512450100f44100d010b05d50800c42e2a0f03010040760b0031141c1d800f1060582024141f140b034083c14040c0d0114800303401e144c40050074036500c1000d503c0080b006c3d50f0303007190300d09522804071500c00d0207015000d1213410000080078180b500c8440c00d0300b121f10282404610800c90300100b111806 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 367792149 1250 367790899 367790909
    0x4050106150e0415060903020111010e010504140d020610140409050d0302091203090a2102030d080a0f152306071202060106050304080f030711070801021308060606180118 75
    0x1c40c07040140580ca0a03010781d50845034035030806044c4510b80078004214840521002c1c1c14003005104506441c1d1081d0049440d07030700342500034070039400d040c41e03c5807840c151800b1441080c022075041c4030b130852021450718015103486040c3c1d074000d4201560100000c14401c111139115544014a4001610a00020625010540f4010703203c10341c81d818000c0b010500f0102e01255041000200c035580d80350400b41c0140d074070103d0f40064880174142140745c071044048000c4d51510030145030525099000002500c1840d00e800d09003c1458400c406400381d8420524416001c841800d0901172041c044000118a560b0004a0307090740140001195140c1d028900030745018503c01d0b0704031020754040141c2401403000c1d14011340b0718a030944980b2182c1c01900b100202c0181c6c00004508110311400010036103850240035030b206c00d90b5440180d8003e40c803402010300302061018000800ba040428004e2050001902440c5044030641c49480c0b8200803140705410b009001c0350b800c060803c043c0049020340 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 367793399 1250 367792149 367792157
    0xa0e03011406032b030905190f0c05090637090518062e170705090702010c020322154d010e12040f0504140f0405010615 53
    0x10074180e0a15080c0a2400c404c1d003060021409840100034010328407070403000d85450000741d0220303c0d250281c182920420003415040c0214241000d100e41503072065002c2d40308a40031217003c2c1c6d91b03d051001d13600302211481d91001808205a0403039408410000810784031200384240c0440c02e90428440c00015044003540f55610010842042040e10041c1c00c000030810061040b880c040801d07850140503240c0d003200102c0340b11178038682c0d40100c0b0704000c0600314034029a4100d004144440c0c2e520311070b038400c451203201c4a6000ca200c0c1c50062040e40b204500c1a8040d42c45c00140d03c44101400421030750720f1080340c2c020100004e13540380b2404100ba18078a41d54034110a080094100741c40828400400150741440003c00071580d0f04122105901e0b8081d843e8010181d0000c00a0328010900441d2461250003003030311007020004d2440040060b40e4000e00d9980300c17152074200340002ca61001c84c055010590764400b0074424030b040f031030095020b0720400c00032400355190944000c5000b40c0d81d05a00c04a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 367794649 1250 367793399 367793401
    0x30509031009020a0b070819030f14090d0806030d1404080a03180b090d06050a0b0306270607050a11070b1908060411090402071e0c0305250b0a0e030114 67
    0x41c81c054070440d0003170220380c001c241040c6003034458280c4c40c071601182140c410071031198240d403103000f078208500e1000c2e512010004880f8545000300d134018101e5440d00280180301a16000f0350007200c815000701c6015008080e02e00000b141a10028400c614460030a4814400003c00c208108000c4610a01c2951003002c10a0303c6c0003035610745041600049480502403003070075074a407a031014080c1019000792011410f82c4828602d503000704070040c101a054042d01c820000000411031000d002a440004548012500b660f20f098442c0c0341030b030340300001031001c010481d00e85200ba060400e0107902c0b00f080d80c1d4016621040c00b0926404500d0100c080781d03001c03960f5100150001c0100d5030024040d503051200034503840d00c803501c0e8420140805e100300e070301145c40c8045c015640200008070118424480700504503060140d002c00c07181c8022101c2d445444807010035403a5001c0b607800410403141c003903000300d82014045e2034540c121508910400005805c120140d9800b4000d681c100c078001094012a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 367795899 1250 367794649 367794653
    0x1b0703050102071e020d02130b0a0305010b030c150301050904170705070e1305060610090302121c170103110402250c0f0503150a06030b010308030601030c030c020d0c030509031009 79
    0x900444c80503083c0b007002c0c4030b0303100405626800d0300c0850303c0b0741c11030b5607900b22044a0b0103c4014805c04c0f960a4105c0c60f28003012080140545c031000c0d480c1400c408443e004000601080760341b503454644100801c500b400104168285075888a4000c0d00ca041c6800701c40d0302c505042c680c1c5070014803003642e0035845848104400030501c42265081540d104030400030345581d45685540d1400a070049000702821401401103610070005c0d8006154020110898826258411943d40c101101c11000c8440d1003c4444480c50145012420200b0103610180c4aa8038503100c3c403001c900c0c0003070780303940080c0c0030050103a110704d0904191390031a200c0300d1030010710b40d068140f880c4544c0e6503400111054080d0701003445103981c0014114072480420000d100700c0d40d65058444050005030740007c003050202000802040600d82c09035114601c2a0303000c104110307140400b1400e640c0ca2401c203402507086403503034800e031600c20444040d4050090910903d40301074000803034902014018460b05456039240741d101 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 367797149 1250 367795899 367795913
    0x603050c0a051905040914040605060609090c0a03270c05030313051315081e0d080703090203150c0403060509070503030306060d0b040f020d0507020109171b070305010207 75
    0x5000341052400a0074600c0d5208054a03501c52034a1407002c001c001c10411401e284038400312009858078250510440b035484225144560040c0d40483d015414280041c8040c00c00e0002c2d03400070140145518016110060f42029991001030359900301a205c090001c6182400700804041003a00d10402103015160b052404c02103140e900134034841d41003046140079891180a640050b5001101c042c50489001e821103c028125500b60848541e003c4100154516001c180520810468036a5000e001050020a601c1d100141c01e010301155022001c00d00582c131070f40c01a00c0c16403026045492140c00c0354610148007100f12403080c4895000a81801003044c140030700754001d60454024100d040c01c180c00039841e40001404503018000225800c05c80940d42e070030450725510064010804110031071408800307540880b903034512450400d03021400c81881486072a08064210119801412a04d1050222640080182c20940418810724148110140004001144500001a030303a40607850184 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 367798399 1250 367797149 367797151
    0x1091e0506070305061018050306090313080c090a0207080702042d0209091f0b34170c12180a050108010609033905030c040911060d061d01060305 64
    0x10b0704060401c1d09019594603440700c000c01c441142d050551800c48110502a82900a648140c4e81881048180203142e80080024068054249414038a00351611101580c034a0110043d540180708000040d40102c0310f540544030082c0310f040034620b86070b440d0700040c1c2138908a02524201e5903065060300c048000782c02c10400320b070030b40c2d09040d1304050144000603c00740005003d081c021901c2c800c82d8014003401880718003c4e0130340310031a0340c541d4141615003814445201585881040d20040c0415840742881021a125400321041c84606007540d80b1188a0300071122800e11481144c2501c550494480080c02c6001380c0d0002401c0702403404010010030501a0740b2036410711003507030010301049130300540c52020307642c1250170700215940b007000c1c040b030503680c075200c60010310b02044008030180f0110301440c041310300440c00c4852000c2000100001c55103490b0b0000d009440406000282d400d10001500d02e01020060014040f680d80c000a148141c0c06201040c2c2c0380d90540040c400583c05110b45 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 367799649 1250 367798399 367798411
    0xc06170103050703060f060506180f0103090803310506161d0d0311100203060a0f050901060806010c170c1e1906060b07081e0f180a050303040b040305010b1207150201091e0506 77
    0x240084500f41c2c8a8a14900c00a4a40100304606c0c021a0920b425581474810a5200301007240f503810002e400c00c5030b1101019202030610074100c034140148944036101c0500b4080f0641000e0601006007810000a0300460f682101031000c035070400d801c801e1091080003e44000341ca805aa203207408400c00101c1c9041d40c01411410302c900d00b00b4040b42e00c0717215003d03040d54240d092420850312001c0040c0c41c921841c510007001d2440d0b281646001c84980303000703040c03603001318000c0f43c904046081d088529000c0c1c0c0158000a40d001500ea440e010030000158040395000d1500060b10700d0310f90099030040d92060700282d070700c040c002402005821118030311108041315007401508200c901048145544503100f1940450703000c4a0161005990303d50041e8000c100003001ca03990f45945114442142c3c006100580e115403070444802c020382801914909480034280c003078a412810141003041d916494009541103642e4ac2010300d000400200308070020080a030601c3d032401d0498a0007c0c50700c2401000303 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 367800899 1250 367799649 367799651
    0x6041b1d1011121602060d0b0a060e12010c021c11060a020910020601050108010504090501021b1e070b030f0903040801060303020c0f01050a0c12020a0f0c06170103050703060f060506180f0103 84
    0x410515921000380104c103860341114516074480b2080903580141c480c100502e50701c851000400180190811050600640240e80300241e00c1d1a845100d800c90f00302e40780390000350f0400054a00c13042d40c4400a10a1411b441c2040e0f49443c65803e405403a200007100c00b41c0e079499001490351079a241002e4800e200761300130301c014807280d81002d00003801c2000610030b841c0503070b44529018003004429016200724510700888414007100020020781d4a507100884404220190715140555400c08510720013510303494014617141d40ca4143d44007482a0307000b0100851408103020220b030b841ca0a02075040258007039030081c840580c0b01c000f000300624031401024140718007041455001904204007a54250f0062140240100c446505906200c8140d00c002e0030000000002c508100000b0910002c3e103446544080103070841c0d0380c0c0b030320348401c080c04040c01d941c2c0030200410000d800c0781c10500c41d26203018008240c6070b69450110b00241c00141954480c501d108948070340703d00f0994403011a181091030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 367802149 1250 367800899 367800907
    0x712170106090e0403050702190302040f020c0a0807030c0f1104140f062202040609170102030c0d1503081b0d0e0a060c050115150806041b1d101112 65
    0x70041d180c04607500c6442c0c401c0310800f00040603d07004400b5a10326680180c0303403c0142c184c1da0001400340030760380406c074840c1d46820329011100341c2c5403090340e014501c108020300e20482035403200001500840c004504110301d60a02c00c0c001180d42e04040081445a190500407603074003400c003c1074071101074504044523010710070408404600c14495800800589080d01004061042c214503d00710b0f02c05031035950700000300025500d41c0800a4802c66281480b505081d030b100c6c4845900342c0c44151501d081d9518144008441030405074008542c24011880c0700500715a0b907605da4149070050100309070420070b6507074080f16001c0140801603100342e561424454003a007950025030507140e0f502905040040f000022402c115003540045400c116201c44510110355410319901c1400d07494403040b0004441c40041241030505000b00070040300b102030043c0311004000400c84038200404c09011007030189509808064446056188401d1810ba07101e4824202c1c80755076034500750310781c9008800013000304 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 367803399 1250 367802149 367802159
    0x6011a070209010302010c0f0b07020318150406080a060815040b060f031c030b120c0a06090b07110616050105011d0103171c020d09060c0302030402030601180f0207121701 75
    0x10200760560758242800000c2169a092842504e51580070090027070034103030140718001341c000015080e003582000034441040041028408882100011000508010700c414042d40307000d900100d41c03204103036800280d02942c40c1023252620908400700b0304036024180a1000b03110700038030065403020054568a20003812503000c03a035190303013480040d1070702d448002c9400e299501c6130f000083d0780040140384254848822200a4440140810140c418003000b000000c88602030202c0c01e049a0b10202a14101801600c0e4503001d14000c54210780e00c00300400011511000381000740d6445405a400095a0360624020710756050044400c0000480400c00420000307100d94542000075100180791354544c80041e60a002040c04400b41c450128000310342250840c803680e2091180318040e000030301882200c9082501240300507100690903030007081c018400c0e480c5040c9610780240888034006100b80340d1705644002c903045480221024020f4108011040390310641203ca10458003070b141780603500d05 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 367804649 1250 367803399 367803409
    0x40b10090b0f12090c01021e0a0f0303020705030d050a0c020a021c0c120807120801230f180105030c060a1d0a05130c020124030222060806011a0702 65
    0x2601c00e10840050020316003039051003020030b842d000900703480f0b0079920303040c025456615a00d20110007401071040b5010108500c1d00c140d080f806540b0107601401c0103110584034020409255a025401d054080044100050301000181061102007000040d0350506040d004151008540c41d00304551150310b10101580d40c0742c01182802203805401c8281240919001007264000c0c0d00246500100020020600c40c0540c000d000142c40b51030356074003a020b194000c0c2e40b040030a00a02e06a40d502940d4900b58030f01c54210800a580001c1000e0b44035007500000503081440c0c9608607070030741903440040000c1e0404005d13a410350201110341c00c7c28414440c5005180c00c45002c1c44100c1021021031a060f02c0c0c8030945500d02510001d02080d01502410750128050065030080b0401980303403403030300706100c3d40001e850080700341c000070041d00841c6103401704040d1000300002c0300fa46281e040c5102c0d0b601111032062400410601002e044258542101d00c10082d11360003411301d4400302007141400581c1c4e1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 367805755 1106 367804649 367804667
    0x1d03030c0a030b010903031b03032705120708030f070504120c060e180c090f0418030914062514160f0b09040207051515040b10 56
    0x1190045501c00d0f251311007e070009110407020044600c08201f40000a03009140100b8003a080c01040aa160040d0401c8208008503807145010420301313000c6204044a101c1c4294106125a1540d60040c0310081c000d1140e00c0c12000014507007802403050390054050990110284490307440c00b111401e45a0281a0218406020362852894002d4049031080070411400555860303802c2440c1e420b8101c5544550b011812090b111131580b900d02c0b60b2041d1040d044150303161000d50b828050f00004840e00803000ba440801d1101d541030700c4201c01c44a4055401040110407601d29189803440315203404000c1801c00c0041b17106080040005030700000074134a6900c400f016590b10b0703440a140f003c030300c00c074546d80d901401600813910701a405451040e000d00240c60f2810600114060040030803220140050741d00300b0100c03400c0c18548100248140103480020030301c10007003000707402514 = true := by decide +kernel

theorem cover : BRFrame.Cov 367625899 367805755 := by
  have h0 := BRFrame.cov_init 367625899
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367625899 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 367625899 ≤ n) (h2 : n < 367805755) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
