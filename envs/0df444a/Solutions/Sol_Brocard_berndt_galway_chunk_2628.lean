-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2628
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:16:24.870889+00:00
-- url     : https://prove2.me/submissions/7f3bd9a4-b749-4b65-be8d-7c4dcca0770d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 472482014 ≤ n < 472661870 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 472483264 1250 472482014 472482029
    0x702150c0a05070f210c05130b040509161415030c0c0601080a022b1401020301050f03060115110f0d02101d070501030b0f1f0f0f0c0219 60
    0x454100400c120001e0408a01441034003164203c503264401d4406540310351007090320441c1704c2c0e9030f070306099410f0a80d400e9640740320350360102440d0707180e100107000b106107820407100490340c90300c8001c528a0107010309138000c848030024220f6100803c81482c0b60180d580142103005040f1700a4000b59100e03c2c44c00031540030500000343d2641050302950000c0d40c803418941109110b49030011a1b000301c04504d14054079401012104004103080b041801640000d62280082144c0050032012038001e190b8265024980c40005940390704090030030410408032019a0f020782c2c080001400b43e00d03071302610281c90809038241403920860003503040780b074075200960149180c001e240f62842003540020318007003061100d600900800081802018480002210480c202c0c0d0220700104003d5020740c1c4131104441001d0009400d031325007100072481048a8800070344112004042544030310f43c0c07150000b48040d50500d0413481440c004800145204401d01002c0c2c8242040020000b424006c09103000007400748 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 472484514 1250 472483264 472483267
    0x218090c0910030611030f012102040903030905010f0608070306020f13060201091a040818010909020f030420010504090f0633020601060c0303020912120408070e070c08070215 77
    0x4650710b0002c41446200454030703281800300d846074441c05142030320303c220035150000c54160f10f00f0140201c42200f03042c1e445081c248205240c000350311280181300e03c3e58041d031004202191146003280c211800c6c0e480c0c00b030045260410500c8401804607000c011070741c0041016840e0008240c80d02c2041c45418001c02038090704d41d60010340740c0e80640000d10164080c401085d80600391001c212001081220024180402006501030790b014020300c0c0040c100061402d681ca00e40c07200451812a07220f0700d110030701418080100001c200220a80343c00a021003600c0d0441018901e001070113500450041e9111a511940e4000b125000d0f9032050b00188800d1010300a5103404900c039400e1540b40741940d910541303200014140c15400047c80904079400384da43e0308020101381d01c3c210029000340c406140d002030500400282c600d010040c16001501c1180c0c00caa41d10f1401d240d0620303141d513552181d10358010f51b8040140442e00685080c1d8401c0e0000c510a60702d248510004410410320848015034640 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 472485764 1250 472484514 472484521
    0x6040b0d14060a090c0e090c100513050a05061e07020901060309060b01030c020601170307050d0207181a061803060103050c0109050108060a03081b0106150306060c0218090c09 77
    0x20501e4461403446007580c25540702c950401054034800c0790302512030400c0f020b08000e0541c0d80d03641c40303912003004003d441d4000d24020001d40614003214001001401c08140300040002c0400d407400280300844084c00b102d40b40c8804210705000c0c8503000741c004000740c00561401c01c0f52030115846203600804c2082d5035a115034015000b0f01d4803040580d81c06260111104495010f440350f1114a82c86400030040b0343e1908950781900036201540e01d125002c1404180001074081081c040103441a8000c0c041540c100840002840030078542d03a40200c0c00d00340ca41e60450710301c0e52074401c003a60036107080380c3d1082584600040b4580224a1b10740602c520380000003070100c041a190040002662010407081e500c10045610342010b0322450f6200302c0c2124104001081c81c0d0081401c0103500c680c001052094010060031035400307511031055007800406045080c0c0d410b11a002c003501c91f60074a11203030b075115004642070980a070100c860003441c02010070700d1600304001c40c18058170f004003c50403618 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 472487014 1250 472485764 472485773
    0x3120c060608010501180203060a1701020c101b170705030c070b2e0503191b03080705060117060a0b01230c06011205030f03060114030f100b09130506040b0d 69
    0x10900c6428099507040850210391b001500840e401103c00070a6110080e003130107d5101d10182180c0070003d10742d0b00b04212100c10f1000d0001c980400d035004c0b8000f03600021182442041c11401d4a401e00704a02144540381c907244c04034006070007495902c0d00e5602daa607202c0c03912102c0e100304034010b41000c41e2501001100702661030443c40e04408140307071000e42c4a4040d48c0400440703242c000c6c84e605401950a020039180914803401c9070b540038681c848010b840c503e104280c400015003056030172100c00261309045c418104005401010036414111070101c402e915551998000740c02101c000c3c2e1180588540340e881051590420100303d015030010001518900c003155001401081e45402640d0001403440303001344100c900f064009000c0d500d0324001800510745039000401c40c1c1e05201d1041030000740d24100030b01841c41140c0c4c82c2c0041d155401d005c4114629400c003036100c03e16507039042000014985a901070866a0710060b100840c3d503480c0c110001d0040d0445604550704504400072030070601 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 472488264 1250 472487014 472487021
    0x70804060e0f13020c011505010e011d0904230303360607050a030b10090b07050703240b040509030a030c020c060d022203030e1215040302060702010e030301030b0103120c06060801 79
    0x103501d0346000700840001200d01607c0030342c0601c20180454480d40d000c01c0b0a500480c600c0440410400040070401c0c0800000b40d240003003032318251098640000f0b5038201c0d1410040f0754648098000085045140c03500c0c0a02d25000041407081c03ca0320750000058070f0192600006c0c810040400640c0c0e007900d00104002c03c0d03508003170b00800c00a810804c0480082c00c0c5a044400c034004103944004c022803c000c02c4a8980c0d0048104a52a1140c00000004902c0d903608901e180b0301044045c50096001410b020140c0d41c40030742c035901c03881c50542448803d0000004454000b8090b0502203124000318500307a040c690a0021180c00070000103400045180303e60040400000070404107003c0611800c54180712441800018040381a0591036513907490705009103440907502d40e040352094454030700e803800200402e40d42100036034081002d1240b43e40e0203005500c1a130304903100460956241d6125056082810720000d803540b00e40205540282d8400c000c0715640c80e401400600580c0e42c0d401007607008 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 472489514 1250 472488264 472488277
    0x833010c0f1412030c0405040e030f04030503270a151206260304080303010b13081b04180b160c02180108010617031206032503120203070804060e0f1302 67
    0x1c2d80034000c0419994000002524000c9903802d1465080c141008140401440541e8041840d0310060152503120495000108042c5120324041c64a401d841c517042500f20280101241da650b0942450a240d91144180d241c111014005803a4442c050803005031046600b0281000080e42452000301d640e984040008a51583c200000c0006110412005d0f45034022401050011382042004014020030000941403440104004840d03107a41e0700f62882c94a070301c00c0c2861303841046a094095131468503104226006071802181f0340d80e082a0ba85806041d80d0040440a0010728001c603507500e640310f0003070071102ca6405404c09003400103080c14114201c13001d00c200405c1c0c0d820090007007403402800e40302d404100030000003036060104e08c0b404120007510041c0403d030144074901340d0700c0b00c030300e4005903200f95405044100a4030328150300b0240c00307024504144009641c0f04204400010301c2400854045505034030301540101d094000203405403080003070070f961003c0f0380e02d0072081c4002c0d2070307000340705 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 472490764 1250 472489514 472489553
    0xf05060906090412050c030f031503210a180906060503040b0123335406030a06060201230a11070c0b0a0833010c0f 51
    0x10307a9030345030030440c510204490050442c40395200d04070106005001420448206106403810540c0041e15080150000c03190b000710564001d0741070310541000e20280844101c10000b0704441301e146c140c00900c51050100d42410400c40b503038000f05c4045241e0017580039104000d4240051965644024515041034606648c03a4242c0c100000b034410604904088611182941c0d8480a05190400296412442640d941c2c481d1080603607440380b503110301c0141441d00100e107143e290a0740304480105403090400a841d00302401a4504511a8000d0315400300042d40201c50810840184c417030b06100d2040c08040c1e0011004014021801881d4120f24213851240e03008210740751020361484c0034141c0d00340380354000c07243c88408110401040d40144440d240c041022034a0035044d030380d58003c7c0048560100d20742030808103111049983c449038041e0422410100811305041c10a900302d510155031a80c080c4017041214281d0340b41e40904288150070342c00405840e0510402c0c14600b0413514130422984 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 472492014 1250 472490764 472490779
    0x9032301110706050f1f05040c030209040c02030309150108030711130f0b0f01021f05100503100609060501092724090c0302071e0c050d030e0103050c191808010f0506 73
    0x914920700d42c0c5000309480b40110012000c1b03450441400000d10310960103108050f001c110009154070f69028800f20003109500039592440c01a0724542007049000781c00d00514090001000b00e0040001580d00d4503410402d4010003844100001da002030411860742d14803401d210071b00c40e1100841c0d111142c8a60251400000006100012a180c24102c180300d1058001250072070410740d40d03a8000c6a00c4200070b240d907100280c54000080c50301c0c6265044003000346d1120710602c100c01c3c03980200001003100f0f0a14414076418040d04070113030010300c1100d26080000c500c2540703c520264000104198804003910f142c07241080204034980914000c0c1820203007400100c0c3c501621a01c21074500d2a01320603c0014124400d026040032007070b07030307000340c400f801c8900c0701003020f40d21301480828180c426102e401c00c02020100160030703180d0041150305070300310074011244800c000045c44104555036140c00e00a0b1001c1c60100b0032410b0b101d40141d501c1e036180094a0341c50034000d07400303503014000488410 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 472493264 1250 472492014 472492021
    0xf0e0a030b190b04020c0a060f0b06070609030201060e01080c190b040e1e0702030304030f0c021305061504090204031b080705090403020f0109030c021009032301110706050f 76
    0x580000603110051850280300c0001c2e0040660710000c80303803854034080114042c0705000008091344c010414a10283d08403018050420185101d03003d0b242d0301e1000b00780700188058000850394014000d01801194552030352108041c800e43c4800090070f1a02901035440d41c40b00800c7e580c44400104483c09003a20b0303200c5843c8040400f081c0c1080755200a40c40d032402d400d00c0d014610311803010742800301074001241407410010012040e07912030700f880ea00858803403429003801402206c2c0010f519040c484c40c480c00c00c000d41c94491501354606006940800c440c0c0790100840d032807640c0042d698524450208010416070f106030003c02c00c5a0207255202d24118038003180611096141c843c2e04a640c1c001401001035081c0801c8141c1d0042c020700649104440d4000c40500b95500450100c0005103903500c261b0442c0780505150000c8900c3e8500301551604694803039030351001428010b40c2c194412480c5440d584801d400030450f4501e80348206880e030b039103841c025000d0001504c1e444055450b10001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 472494514 1250 472493264 472493269
    0x51c0501080316080d020f2505060c0313050a0302010e07090b13200c010501050405090109121d0d1a061807140706090506040311070812030a02190f0e 66
    0x4003410790300ca41c0c01841c5401000c10b00312416003240e0348100c40500c42404000e15030003441c070240c4056204101d01c0e0b82e0303c0701c40040309040803200b66818400905940030507004148002103a50344545001ca105a0343d481c0d8001c420b5210344000e8000f00680b180071b420808040e41034100c01c03021405142207401080d02e40c4800c2c0d0550f071103c0c22091304410001210320b202c2d0003c0c0c1241081c45520314425041000651746416186e1008034180301d1a034451004100506141c89190b0303001100100030408010705680310078904840c2d00d00d9408020548400c01f00d1214446842005520002d15003907100000d0f01d042a040c0901c1110100b54011000004195081800340785140440d03c58141685555001017640c10001c8107940e03904001c0244074100c001009480f4031011030740210020605440d00d031800500f0100314103480e0700340d42c101040800090400046038007030803809410031500d9070703256481b600c0280121341c0122007241c24039000e655800d03003240c02000140c01664403016108007250a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 472495764 1250 472494514 472494521
    0x31d01020c0108060618060304060204060906080c070210110d0c0606050f0a061b2924040e010e010204150e0919050a0b060301090b04060509090a0308090a060c051c 72
    0x1410b808902d10381c002400a152042c000d1240340d01032802c99030f0352a00c840c0412803d030402ca44c111481030340010b040c004140c1100305003004202d0b07890400458030b8070ba2103c41d4540181d40b802405642d1690103140d04074054030b880521280c650080f100100d0303942e20010300000c20090141c13401c0786003500101c0c10b070070400c0007002d03070b0100030705010314403450000111445d890000403100303002c01e84400b0a0000d445000d00029041d1200c0304034044a070514a01d40c001103003d0000356200f00710000c5d0707203407a801c0755417180340c06c007001c0354001030b800e040b503040d240904214120802907510004021620000c0031000141c5804940d80e000190b0a00e201840103100094801c410041025000700d028829103401a50340721400c450007081c0742d94400081f070419002a040701c40c803207403920301da000309060500c21100200021203010301207080000071191250204072000d000c01a103900040d0000b042002807101465008400b0056100e084070000c00300c2e04110210403405000e000c202106051500 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 472497014 1250 472495764 472495783
    0xf110c040f1a04020f0901180305100509060f06030c0105071a0903031603050f04060905160603020c010c03021222050f03070b06010309200a09050a05070e06040303020d08041707031d0102 82
    0x98000d250580046c015218159421619516855116400f10004800344900900c4045c0764002041505146a4007804d100008001200341d00c1e914040200700d81d000298201d0700203003801c007070ba034450f03003400c165071b03100400c0700c02600d00118101408000da100100452181d110240c001c010080361040444c161a41902c483d80c0c0844081c02060100d0800d0f448246e00c1d5200388200c0311100303518000300c1070f00c64840d4012001300e0f90208960312000000e01030100c64212500d0700310b1030103600e2504003001000140114058890980822452a0a180c0e01e1078201d07400c04115004c040d208405580c0c3c0f640410000c580da00703494004038449501034011040e03130903071002c0401103403084191039200400001f0174840e80240c8089000681d40c5080c420b82e40540c003200d0010074a1f2814070070140c948800e40b04064001c0300100b20400100340c3c080b401c018401ca5900c0c00c0341c0b03592158201150a03001084004000b401e0000b0107a0415400103420900c442c64418009041c500030401a600c500c20340 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 472498264 1250 472497014 472497037
    0x3030c021519020706050a050103020a141302130506040e06041802031c0302130603090c050306160c02010201060302102001021309021b0a03050c011104060f110c040f1a0402 76
    0x20036110350302000000b8000c1c2c652000181440640d86410b42502e000350f90699402d56107000500c02e50030a010785a02800040001c40c060030545c401141c00d940c40b01d100f44480640c0403d8181034401e18030340341d40003448000d040649441d250300c0811006071058443e41e11a614010000e084054081614550780d81c00034094413034041d0b000507840a01c800030342c0c2c46d8105503080103d0900210359814083c062b214990300040c1040382c61401c48503202068001e144030b07600c441c00b001810058a80482003242243c9008800070a4a1005034054907858100a5200c0625481410143e9100d08031107421540304c882d0a04400d4000310043c02c0b885040401501e5900c0401c017800745081940003400c3c80480e884a42c1440c466004004c2e00700b50121204500240c03000492064010b802d0003005000d45550103071b80d00d0a890141c020703282d098030240c0c44042c40048106174101000c24441300c3d140c40030182c000c1c0a000355009041c001030009103001c424162403000c403082941450710a484506d02039 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 472499514 1250 472498264 472498303
    0x1090b041809061a010306050904050c0d080f040b0d050a0e07050d17040e0106081806161112130f030c1202030307140a140105060102060103060c052503030c02 70
    0x519414569120701c0a2240301c1460301d40b9820710000c0c1c01c80c0305446401a80c420312289200c5468001000d80e85194406071082501c2400d0201185000c2254000c0c00b0040310700d0b602da0392403460500300d03c2c01521103202040c13001203400582c0421810051903011500f03e02000540e441c080044101e076403008020100d44c1c0101030902c2241088120740040c0c9009009a842207031031030441e0102944241c100140b01810700f0010460190840f00140c1c00140d284080090306681c0e200980d0f680c0001444460810214529204801d004960f41e2010700101070603112070498403981303002d0941c0800d04840d03e00700003d1001941d041c2984e600e03015242c2c0014030109581c42d00f4019984440c4e041ca060b44e15020030843d040000725103443d001031400c0524060304168861342401c0c0310b1038190b040b104507980d040c50104501070b030740840c69a06403603001000082d82d41d207414040b20140185d41c5c100d50801004213442540f5034014840c602542d01c2030b0f03418454501620b03001c903281e91440d02c4094a6210 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 472500764 1250 472499514 472499519
    0x3011d070c051219210b0d02120c0307060908030a12020f07060902030c01030e1c1704030201150b030103020102101109030f07170118030e04110318010b0102190b0a0e0303040302100b01090b04 84
    0x7035076001407101d001b00a00321381500c41e8980002d0138101441815206a40c0302545c1840c03e07040c14007030a0014541c500b000450980742c080c689480303100d0340b1804420004112810414841681e058500401b00c0030880e07600d0340024649440105031a4000364400e2007400d24501280d8441d004038910000b09401600018601c413040c80400a00310108606001078508000c0301d2601130310130148241d000343e0010660000000300d42c0007030301068100d0f80300c81800f0001440581d80010b42401c0c00d0382d980300c0c0020500c021400f903001c00c6c042c2010141e89030140b009140390502c000a4401c00f52801c28503485070719901144064201c484c103252101032241107686a4020a00494500c0b0301e10a002c0e1000c1101c000a07141015541d004849030b07182e0704401c0c010146a02c0b000d201e440403061080c00102000c00030980d21110141e45031303100600088184c40011a080100c0e04881100485501200d4981c01d003843c000e0341366480c003a4021403652420081490541c0b00b00102d20440b90400700d01c502d40350 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 472502014 1250 472500764 472500827
    0x10504030b040f052a030d0f0c0c09060b0901021507090e07050f030a0e1c02071403011503060b0118060e3106170303011d070c051219 59
    0x78024000d072a03a02e000800040402c034217000c0c24403040c000441c900c8003564035201d0401898003101100f40203620903001a000250012030f611404051401c05181c0070205280c08909231045400188440d420079a0004001d14428003902102d2002d800761418550150b0385440c0304001129600c000a0b440c0034104003004186060903006101441d059240c5980d82d003c0b008071303500c06d81c1d080b000282e41c0c01d040409140207216404d5001c2d83c11450100c00100032a000b540da40e00b80c0200b62000a10951008895030309600a0709110404582104003d43e28100200200342c0408160301042480c0070520062400c2d4907140140c4503191604142001c03c1024851000121120031440192600f038166104c218a05c00300c015814040d0003007100e604003e035004030303050000b03000c100c0c2d07500600c018000340b0708400f98010442e002c0e0140000c0b550351a50219000d001c040700203481070103080d03843c501340f22084000b4000e10000604032007070300e02604003c42d107030031098003504100c8095001700c01030342c0b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 472503264 1250 472502014 472502033
    0x6270a020f1603020c1c03021e01021e0306040b0303030103050a0605040f06090c03020a0f06081302010212120f010f0e0a0b030c060c0304080c03030f07030804060f0504050a170901050403 82
    0x2600d215180341c00d040415401044a030b00401c020341c00350340415007020b014940403e80c4160754080034001c000701e191954000c0d50b0f0300c440d07424040401c002440b8658140c0c1095040d039000780d00a1131880004410b940c0004102e80c800d481c140e0040e03042c04c0035091f8904000086030b04070303503200340244009010307510761400500c3d0103841103440d0581c0c140c904012620502500d0022801a01085401d070301d103204016a5030603543c440541c00e44698000c1054a8100451540c006000b1140d600300900a100403030802c100001c10b000c0551001c240610011a082a400e118540340403850700340742d03250710403690f55007164840e040300c3d0342d0010005011003150b0341181d041200080c0803120101200c03c000b400320781010310302d14041d40c40030608100040040020a20710203090b00079510780300101500d18014404c0c4440501032160309000300c0c0400450703510a0000c012494000c11071424a860100e07110041c43c0c2042c1d50050101508007144c49880f402c64954040584850785810b1540da81c600e201c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 472504514 1250 472503264 472503277
    0x52a10180816060c0e031c09030b0c13121205160201030b03121b1015060c0311030f22050f040b04021e212809020d03030506270a02 58
    0x100024040d41c0300001d00d4500800261072200e0300d4416001c04100240f6152034443c01c1810306e61f09224041c0d03216150003165020589800817400d50403036075010500342c094850040c4c112000b50304420005100c102c1a064030016505c200490200030b04e080d40d04490501030080d8030300204540283d200c00640c000d5000307110740302c0040e0640c2c005014034a61050705410948100e402c1d9903202e01d603001024024800700141381d2400b0070030800030020441d8202c41c02c441c3d001d46018080b28052a205140c0240502518280008201c070390301c0d003107400024020f40011310401224a0301d0220400c40c880701501140c1a54409010302100340000d00400010f0810080c01c0da800c0ba5007001034510604c80340308000c84090f00e11084035516409445464654000080c10340d42c060382c02c1061100c1c0400c0361050b110011041541c0e07404034003280e2101c000800550000a50000191030303664100b64141d000a8440c0c442207800e82072105400e442c203400070000c4036003814542286c02c00107c0120003603015280b07 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 472505764 1250 472504514 472504537
    0xb010e040201020a06240b130603270c06080705030702120904020d05040809030d050315093c0907050a05100201090b0a05040c051f0e01052a101808 65
    0x340780b07485e160101100c10304141084000b0040c0ca05141041d0186942d000401d0204c1030946080d4002d089580c0350f02503405040c00301912042202e81035440240a071010814044a0000c030003042d1400e44c070400d25921881022900d80d9000030102d601540540e0301c41c190a402400c01d0b00c6403580985c001360300620764298815820702c10304050004500c13a07e0310951041c580c03650749071090000c00d4600912040ea42e41001402c004000c1e00c0d81c825088800e031040251031020582c4c03504480c2560330120164080d981c005201aa094404c5040340c8101d000c00300d007480c080590302c817041450780741c55141c050300d900081642020005030410010a05522070a4170000074042c806a58500e0321080c150768050300961280300b840244480580313400020001254088001d1100c2d200180b10100103024010510802c8061031045034051403c4401540d400c2c90b0710b40061503501100c0203a211508180462407050041c41056410144a0189180031001d108400c0e0400713603464070f1865005403c0d104 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 472507014 1250 472505764 472505773
    0x804140f07181107200604090c0e010f030b0a0b0723031809060f040903030e060a021b0c010207031502071203090b0a09081b01090f0605091002070b010e04020102 71
    0x1080d15505001c080098565050715018862031041d4501c190b440c440b480040f00700c010020b0100003100380107050a00c803401c0109001c410596000200e5a000701d0740030401035820f1940da006681c0e40003000e07190041c1d00340c940100c01d800d90030b802c9088034841400d86070400711019080c4111040800a480c2d00e17841940320500c49507001e20381c0d241c60307400b0b000d60b0b840311b500208040c031642201c4c09041d03008940c196020000c41c50000c0018045c1e40384800034500440d40c500049041c180700b07410010001ca00704003142d845060030f4003444029485030604201000f100f4040500c13400f00803910800303216059009020040c21620744c036816000c0200c104441c1a400c002c0040003c0c00c60b4031605503074146031030000340101d10b400e00302a07a8000500030000c0d5490a000e00000070501e405030358900a2010b84132501c0514580c90170300508545c003001d4025461001d40c40208192500194401e0300c4000650f400c440064000703e09038020100014004556400140f240d44a0703c1d120fa58041d00510444 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 472508264 1250 472507014 472507033
    0x30509011419050309060106030c0e010e030a020406230a1427010e040b090d092706080307050d080c09190b1c0507050a02070b3a1103040201080414 65
    0x1c2c2c084090404a901c0451400301c100280341348207001c1e107801400107040c207020f203441d204001007110002020450500c2206100000c050b1800c00c041141c550340600100141030722200c0c00007044d880160514000055000d0450450400420710301c125a4440d540c500804400c104200c1055458441900c1d001003104c06458008000d000cbc581c000c1400c01d8410709141050704107502038200003005e02c0311f0b80e8000d03400358100c41e42c0142030780c0c1100c0c0c20030030204206400700d0864200c511501c042d41d802030b04012020500c86000301c000c0225902ca502120404541d00106a44a09084800007100031041c030295805041950701e000c03107107180d054002011500c58806a9040d00000090410000b01d40b00d107407003050b11f0348141c3d81c1002c0c007814018105040c801009503203013007e0040800071100412522807052002d0b11441d4410456448140010416210445282040e8015995490622001141410280007280d000b20b070181c0d034400d00341d50b840e11036002520385000801c000d4807401811 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 472509514 1250 472508264 472508287
    0x8070f0816030302030702070609081f0204050409030908010f11070f0201030b0603040506040627061107050a0f12051804020c15010816050306090616171003021206040305090114 78
    0x11641480b9403001610ba08240da0000c0c034206071074226006104401d141484406000605d545a4220f000308002011b0351a09400700640190323071100d0b421034100b080d9442019001f501410517605003800130402d940b18145998191205020100c840010800c81980801c94191841d14003600604011841e1402c2c5000701754607a20071a42030302d890b0004008d2008200042c041e41075000462070503030184020000209034941c44056000302501da85004181901d0700407001c2c1d82e009034102d010360715800c80340d0800301c09900460f00c0440d007400b0043c0100c1d898a0044003541e08620440d08640d00c1155078034180300096000717054050083c403030f440c01c1d1401080035144482c06041e410006e0405106202c8100e034044095401440c0302c0d030424001c020480302c00185045d48403040c0c2c400e1881c2c0e0b441c48207044d80c06201032481e11000d840103600b0091500705421145049a2080c0d424103504807152011585420055500500180c020803000d125907108083c2da00c0e20f1144e81049601d401c105054 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 472510764 1250 472509514 472509547
    0x2060c0a08041418040203120c0a05030d14010902030106050702220905030901020c1203160c03061a090a0e0a060203060406170c01030c0f09050d030908191401020708070f08 76
    0x44480109020039407100d0fa4100080760f840c4d61161404052032500b8031398001381d01c0c0c90141c000c01114040101c0e442a03155001c0024071205901b00c1c05407607840718250b0070400a058000c2501402000d0707040002484180780c0308490490b05640d507950b080021316403c206410416000081c1c40355403607028601580a140716035500d161180c0d000310356569070400064107180340c0720510340c825042c2070720504540f41c01008603068070400740010050643c035131a2610f0700c02c00d2504041c0803945030440407020b04030400050b400025080b100e00e00e256450000f00020380e41140460000c6030080381d10000080c01135005142c0202004001043c041e4862404810712040d58968a40030352014101c4c00542d41c1500c280140d401c5203203820400c0382a0311402514034070891040601683d0074400c03403c249031045003440040c044180030b0b00c541510050404020114918007a00c01d184400c0c08260050030510880349a140d010080c079042c00b9150711001c0d100041900d050b1411907003007181d503403080d140c2003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 472512014 1250 472510764 472510769
    0x90415020318100c020f0a0c05090604020c0f060a1107031e09152102031017011407020a020a05040e072108041d011208030f060d140309041b090302060c0a0804 70
    0x2d1000440341c44c454002490050344101003880c58003e0040400810341c07040140003695010398015040381c5607840880c0007032040d44442c50f1980039040d030b0781050b518041940350050542d01c0043c0075840480601003403900c00e9501c0100800d600e580c00c46948808401c04200c480c405003005080541da42e10b0304940c803040980c0403800500051480c2803201c00c40480e0f41c20524003080c0c21400c40c5001161600d21000070b01812003001d594984003111504250044808004081d52251590401c0440a035640d10350032000c074801c943c142e01c0850607041034807034030442429000082004600d4000440380c02e880c059401c0184428032502d80c004584440c009200808810341410180c0480c0054550a5103060308400c416035801400c540108441509680c0c00c0406c8071246011620754400058920150030380c001d01072044a610740c0998400403001c0c3c5a5014291414010f030140c1c0d0b4460802c108165803000049a0130031030030f001500b4410050311020100c0303402c590010130103413070f40c0e1070301d8000383d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 472513264 1250 472512014 472512043
    0x3020603010b0a110f0703030c080904020d1b03050f01150e09070915021507030b040212070306061d1c15060e0105120a030e06030a3206090415020318 66
    0x80c0c801043c9a20103400a5220480b6000e040381600c0701082039101c00032844044c1c01c0050940102c403d210b101001c80b00c139514000e01c05c43d5181d0390150100d014104107064600e403e20864401d0061230b0284c01780f144600020200110346da820b024916001e4040c2c003034003a08110039520b006440d600c036094168016180c80d2101c1182070301d4480b031403211950043c40c490454000c00804410002d01040752a00100a81004140c5074010300201d0b0080c0203200d007040702855854148400d40b40c155000c0410f940256a854609543c0b0108821041e5104484140c100030071000c03032540c4011a413029a01c0c50b100d240008044002038500c80709844103a0400031441e84501c0041100e85400d420456a551b051b0002d000c7da60810340b0080e04600b001c440d594003e020000010b4101210390f80302098050108054800b0085030b40e0300da000304602580d030b40c2d1024103110045a55440c0c2030084510a0f903000070703810041e1400c0c402c620b000e904090442c3c078070b517600d03203030900f000705001d002c0240014042c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 472514514 1250 472513264 472513267
    0x30103020a0b0412030f110a060507020106120f0209150901030303140109142a0409020706060807030510090515090f01050a06150309080403060204030b01230607031803020603010b 79
    0x154010800c003040d8035480071451003000c120030031000790041c004151343d03605414546a81440520190303170004d5603485291140c00384030031800030409030380d01050003400d055008000c616141c81c09080303044001c20014004440a0b401000189803c9030030903400b40320b0f030741010101c000907004181341840c2a002100420703111080c070011000841d520302c5c0144070f1008140701003407885410145c203040150401d1160302e140c8082e500c509600c0c580c000e402e0b400003a0002d54895480c0301581c000d400801081f6421070402200060000c8001a82020740b5000f9000c1d1428040341070840009203000b010483c0d40e40515951200710a41c07031085c80f889600c549002e00400101d101645085039401001b000800d46400303030030b0000c60070001c0ea210040c44281400245003405003400d0885001d107a1005005500005000c003c000f4904230140c100c41549054914260013005020f04140d108007007140c00040510001c00400c3c030a1032800f4161240d99a1800e140d522600811503d520903040360650380c20 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 472515764 1250 472514514 472514519
    0x309060411060703090302090402030c0a1e0f05010801120f060c0521160c020303040906080706020d0302070201080a05040206073017010312090e1e06030610090c05120405030301 78
    0x3002000055803200b00c6903145061441c0d540984140c601d80000390140c0d080000040443d1002c01614100300c0e0b00030041840d00da030741d8008850318144c14030040008003540100044a03901031803d10140c410585840720542e0030074040041400010b20250b40100e6480248004101e0a202d4441c0703040480d52041e40d00d07500741540112480602255686005421042112788003191484c01041d00443c03900c1c086035102c90001a240d40180e40240101c2841d1110000e0702120000d40102120440e400345d4002900401042e01240240030300603001c10701c001f0020340c43c83c0d00303a80300c40d03400341c402410282003049039101c909150b9840d40081c0c440301036039200880f02207886900703480e2034222490211604402800c08488a40040c4002000da854201ca051892801800c1c040c01414040d882480726207004548185040d0102920f5031180480c00c000c0350f40e5042c08142180b1500690804120310741c03415a0f814010004140c01d80c003001018030000341000800d40340e240c003a034013540003180c8950 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 472517014 1250 472515764 472515773
    0x1b0d080d0c031d0715020a05030c06010305060f010b0307030908040308120f01170c0f0a33050a200106080a06050402040c020d0f051315031b08091b04060b03090604 72
    0x92071828514083c10941008071a240c40c001020000d40f2070480f0603010300c020340341d800d9141c00c002650080c00380c080820002d503402d800080b600e04881c0244116103090300c43e00740651a0200c2170252104ca05d00420010300054003d401180744a07108400b10340c075242ea26142c803c140d0700242a040c0490601c0000e010403564003403507590140010801c2c1030000f121a114507640c60b40232404403801001c1c660100603540d0f423034080110050403040080f00041211814450000302d205000c900140303019200740070098070440668103000c44a8642907840d444041ca000310072001001001101e648500000c00c00031800e01011038003a111b45004105030510744104030a644c4208481c82c110b611510b110090f551b41310704030300030840785d03800c0c0682c0d50480c002120f8983c41c040c5c0c006c6920355944450030030445074154014088004507800a200c0082c003120100c0e6882005e9508440603801420708030000c003400901094820710050000a01076a1003089100a400440700c0100641182c4100011310 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 472518264 1250 472517014 472517021
    0x310b07021c0504031b03050102030403230306090708040c081606140906040e0a060918020306060103110306220c03020903070e10090f141602010b060301081b0d080d0c03 74
    0x704410303840e0407000c090049008103540118440079054550145e5a0000c041d02d45007800007550700903000395524035081c01c1c0502a1454414030514511400d20002502010001940d008140c000c25800c1162aa5031048030f2050000e0401d462050b060320000410b8007040168107076883c00c08940c1c4a805240c81d40c0070704034158082121240500410064500750f4420b0200e4040c2d5219030b4001c1e143d80c8955071440010320540e000304203054903103514440742c00030600000c0b521346c0c800c404031180d80ea182e00c0110306540c1d190300701c1c040340031060000c9095440e04000c00d03028611141121984c3e040364180300c00c00c2d940300b02c0000001c00c0d0300141244c20360400380164400742940588481003810405101001444184102000e00f40c0d10030610b00010540c1d04151b414886000d41c90b515402c2c60b061102e420380c000162540590b1a0070650b0740c3d14200407056030f04a40503100988600e1000150f9054140100d4005651024030001c5072000660702c0c8014200341116050f000a15418a80015048 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 472519514 1250 472518264 472518283
    0x405011514120304080c04020a1b050106030209130b2815030b011a0304021c1a0f130b2410031a010e0d201302071106090108310b0702 59
    0x36038000300402e00c002d850000d124641d46d2020b550059403214182d50803240f400701600f4001d402019080c000c5d0601005400101c20f0701d00807140c1d00819200c40c100e5100740004118024030142c01c0b0303c00601d40114072509184a400e001194412102004082e10226071044106001450801e80240180030f052882a80908805544040b410300f86401050090000800091040014280b082c559901c210000038071103502611025112154100c4105030030300403114542001040c40000e54101840207050b600307075400000181080c2c4541e404402c01c0030004010b0101100513900c00e69443d01c42c0c0d1021008501965000640c0421070710921030151021070b0314034104408a030383c40840d50380b0703080e02c1082c4681c031850302c00b0804070300c4031207982c1d0507800c0a00c60b0b8030100c0244822030007840741d002800d0f01440303030040b4044a0321400401403103015802c420b83c000b408817800920605807560407611080055020041174182107041030403c800640400c40d240052002030090540d0100b000022 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 472520764 1250 472519514 472519549
    0x19120b0301090b19090602030108010504031d0607060905011b081006090321270f050306010f0e0c0708070f060c0e03030307030f020f0a0801080d0e0d0602030405011514 74
    0x190540c2c50b240c8a661110140c0401e40204400b000b00001c08210303400b415440f079100409640301c0d03a4807074003076000300001c0f94294003181012480a07220041455032030382c0204020a01d40c10040d807626245c0003041304000807141903590b81d00100e07002002107904482c3d6070740c5030759960b450300c0d15080e180c50111007a4445020700842000034000201c05041751030b00740618507920a0440c0000c80b04844c4107100ba0920b40081c0002283c0400840c80d1003548410348107080405103103d95208181561050244200a0264480c48060101e65407031a4259005071010144605117002615903240c2648150030403101101102580c6080010a020b40f046040703050030b107041c2512546000c00e4a03440300030400800c2607174403241d0400c007030f62550588a410146400442d112641a00b02600b02102802100030b83d2280034152212148910a1564080000350a12a1460301540ca0002035040507004072015521034049102c0100100301d810003c0403181805c0307030040800028002c03040300c0301c00e4029 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 472522014 1250 472520764 472520771
    0x30f2406050303070b07020102220f1703031b0705010612060c0c12080703150305070f0e07020a02010513031e030f020c0307030b0403110a080904060605070201210219120b0301 77
    0x1030b9603021040d82c80e12034124080f80c041c0c0d5200001280207102d5204407801c01c204059200c403940160040c05000e4881c0340c0d000841300c5403141c00701c1140940c0550b1743c044680c002c10000c0c00000e0005203500c0e080006681246c20105255601800d5800306e400069110915580c43c0d000e0102ca030044c03464084003030900100707160302e07610384c0007492104951130014404860041002c0324401d070310154040c000107400b040b100c0e07180c1c507259468042030711400c038101c0a2804040f400070440124070b40121595001002c0284082c0c4c0151000d80100e17001d0fa07502d0304035110020205811403854600c0380310080850076040790514000d0800845074800380d0455000c030a140350035840c0003c0704001d072600100c1801d5244e03107610301198800f590001005507030090803858402c004d0740101030540701000f15000d00c401a1507480c11282802044006800a0311f400710042815181703020407038100307a10307070405403604401a00540074410351000c41d82c0080c044608001d107031201c1e03100ea10b0080b0030440092 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 472523264 1250 472522014 472522019
    0xf0203060f04050c25110312040e040312060816080712110f0409080403050c10090e0907081b0108011d0721050106080106080a090302030a05090406030f2406 69
    0x54030101660700400e01881d0b07140089a4072411500503580043c40d43d4a0400b542e00703040078202e0f80000c080c01c0c1182c0c00d4503c3c140d41074081c41c02041c11110b0390310500c076250034103241c0603448910709006081a801d110501f0095090007081d4014107000c0c00302e4600800301d42c621010405c440421a80c4185000c0e0800603003800500c1c0301c00142c1409a070020300644040e46058001280d00c012618810341c0540340c003403500104400c01e40a4070889000d10290b075402040742e010302ca400c3c0d1401c1d9035400000c0040c9010b20000000e1160a50003052800c1201e2040d510791014511300000701090f121aa202da010b010b90315030b0300c4100503002d8900b01c18041d1000107015648200d00202624032806c4c01000c00c41900460344082050011b17500141051140c7d51396030002608030302c4203014140c0051a1180001c81c2e140c002c1c001c103010103030b06600646c60928611000c94160300318944546d40181c40728070000108034511480c0b0500342c040c40e01c0b04058042030216001d00c20391038801ca01c1290510008 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 472524514 1250 472523264 472523269
    0x29070c0f15111b01030f0b09010f1d1303050703020f07080106151b02041e14160c110f0a03050114180f0d081905040f1518080c1f050405010f020306 65
    0x200803c0705003030801040740035000304100003429038100c03115002001c0c0c0000107514408054408110344448200740903c000151440e40c2d1600200c1d0004c900f03034030708001c0d0070020380300d4001404402d0181c0305a604006000100728100350542c5c0c003401550307450b02014400d013102a0192a0400c040f030602021080066200007088110900064411607442c4030b035240217549038060840305005400f04002c1510413035030302404d400051340e240022114081c910071907103000e1112041490340015803800c0084039401040301040c00001007603000f030f030120340000c0044c00074040c07003000c0503213526460354038500301c048551041110008124281d01c41c0c5032a100340700000c1103441c0004800c0c0740403500f543d2540e0503249620000252a0f01d00c5103803000700024450744640b1955124417483e08407401000e01070741002503804040c21484007000001c9403000090b40d0400809400d2186400c1d00c44515400307920702e400d54107a80b151195141c9900402040017000c0c0702d18400c40919107811811420002c02 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 472525764 1250 472524514 472524553
    0xa0c020d0e030c04020d02041a180409030e2b030e0f030a0b0114030705060a0c0b010e090d0e040b03011b09060c0b0123031c0929070c0f1511 62
    0x3e00714002c907400210b240d4806030540480d00501845100c130400040304540d0f244490f8011a144a100c900b1400500c505180a009804005030103580d5806040070101c01c101c074461004c25800c144007090451340304490000403003000828004e45480c008200c1c0001408600864020842d02c21b4000100302c800107805102d055054501001710259800400350100e03181024075007081d030f484603000c07500162031075200e442d80c11081e07c60010340110b66030b0349000514110f02554100801d810030007141518521481c0e0100400d80000e002049501c41c81703000c00c2c02c40c2c51034618020b00c035500314002c0750102d402c001004010580b52804c4030f207100191712400382d00d11041c020700010460356458450529011104840010402004c1d100700480c1444618000031002ca012740100c0c013201d00c005001040b4403002d5100110303c0542859000650060600715801404119010504640c001c01e0b84622218681c010304003d14000b11590700c08003014280b45130f500c60f40000c9600c01001c50b84c4000d2481e6 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 472527014 1250 472525764 472525783
    0x6081b0a0b1e0a030e100f140907050f0d1a06010f020309010507030f0e031c020c1806041e020d06141e0603131406042105030705031503060a0c020d0e03 67
    0xe050b02d03200d0b030140808a001e8044036201d2a050702c6a00c07041c181e05002e56200c05e407411082e550400441688856850700c9080450320201c26030440c0700d0820440c103220480501040000b8000200303072175155150303071752421924040641304001c84108812560010034000308400c1c61300082d07003443c2414000a240740310300741000f030800c04403c070076044a901501c800d010100b002403d840f0448003454a42c032942940d50514801032060f03208592590409019240c00a4009488030455590780f4050102500300c4e00001011040b802c0528610201144041c100701d14130144003081080c5030007441035980c4010400c2d648544503540c294465400141e401105201054400750f4803903544860384a250031403808042d00c044404242e04040c4000850b003244514030903001d2229112142c40a8042d42d008034262001280041010900160160001c2c0d03501c0a800c820b54650540010086402d181c4141c4000c004c05032542c80c15680990144005a2400254902802c2c500e0407040040d6840d010030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 472528264 1250 472527014 472527067
    0x2190f1106040510020105150f01021216080c100c050909040b0411060408071d0c0315061b060a060503030f07030e120a03020a0501060618031506081b0a0b 68
    0x40c18032209a4880034260b60081a004000144003804d20301e02078082d180403280c0b01d1041800d030b80c0a1a4915000707400018194044e4000e04101d10581d0b03440e45641e1003240200070380c600300e01540d000a803043d030040c145502128003800e49042c00c01880016507030aa4210b509100090000c481c00c3e0302c0d00030034603a1040d0040f811110755201c906103030800307071020b04406400200004010884800014240c4101c034500980c41e8801019400e0304081c2020541e80340e50b249c04104041101044140d80284040000800d0315141120028003062180c14245040c0c10b1a0800c10030000900b01d18450301c0c000301803e501540c50414041c0d4400900d11401e40c00070f060102c9001c1481d80354981c0c0c2c200d600b00401d25021284a03004509006e950b861a85c882110650309100c008144544191b96018901505d040d12031b0038a42941d0b102811401c08903000000d155031107000042100c001c120304c030500107081603440d050040460600c0740e00500c1e90031088403400b0030040042d0000c2d80362104055000c14 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 472529514 1250 472528264 472528283
    0x12020405041505090c03060c2a10091505060307030b01090f020f1821070501111501090506240711060c0304060e010801060305090d080907051c0302190f 67
    0x842c5800400c50600e01000301d0403524100820601e0240040c00d141c14000c110304a9015a65440d0000c507107200f142d50240110b1000c030510b070000b201140820310502e04040540302403409400600341100d140c0202610844002c03690101c254201d840707815008601a0050a60141552114004640103100f1305d5441d0769030308410b01e002c409960548030800c101110144d41d0714110342c80c80c40b440303025005035803090800f664042403410310318098080c5100c140d000f13401c400346000d00540304075101010360203046c06582e2901e07484461000c26135000e020f02240000b03450401c54140040c18a01c0d100c880039001020001b079500c1e840801c1540e00f0241d100813080c65803c5044c020503c5800b59101c1d012030b501c07021401158840d0080f4001c01201c10070707070300d04209a0381c8072400c034103461081d100c803d411307042054600315161280412983c452901c02c22a442c980e560b5000c82c0340c142000c042100c101440d42d0320002015818800c8000d0490005c0a150075200c150311000403100c1c044070010300c00700c0b2 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 472530764 1250 472529514 472529521
    0x90316080d0e070b04092d0203061c0b040c1502061503030c0610060e0405040f03030c030605221407020d1d1c0606300507033912020405 60
    0x810381001c0d050507000c4043d21007003035481411011507002800781001c0c02d414180c0030004c4102c5000d0a540489050046040640c410742d2100300a6001510f5207420824000440c04046c104000941c185445918405094a042c0c00c15840c00141078122010070030b908404140740590001d807254210311b482c0c0540507000705081c0081d00d10b210740b50144d016801007504111440d01891102c0c800c40b05251280708451030f110040004440d01120010801105004400c0210f0b01c80d50218a80500c18200000c06688450000e824100c24000d9552a044030303803201c0c0d0f101c91040c0101e03000c401c46601e0108107414143e030069100d10b680300c0b084007004005503030070010f1542c103035620004401c0585030400b80b4041e00701320980840044002e584c1181000b400103081c1c88070a2403682c81c9d07070004111122400b86100349075030720f40c2070a400307031400d1040c0e0b00d000c0702180d03e540088034503061402180c584000d8186061059115038041510116018582000007500004800c00f20b0795045030b0000d01543c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 472532014 1250 472530764 472530787
    0xb090c03240612090c040504140d030605011209030306030212030a020115030b060d150c0909200d0b03010e011410060f080c0c1c020d0e03011512050f1605010809031608 74
    0x203540c05e1000340d0041c00d10b014807080c024800c00d29111900791100703440a2007030552003075091320b900380310380b500103070040b00381e1204047c060740718144c9a0f20a02e40402c076560b0301d400240104a2805910f070302504000344054000d0b80901c10603810211804904007a00d01d15242c1100b0450000d00550060800f010824100a551504440324104a2500300201410580014a44001409011543d51424511034850030200b81180b003000c180d800b420303150a2070fa01c0c0b03c40113008410b014503051340d01c0310102c0e10800000c0c020407207124140c0000c3c15081c5094200d1006102c1160b100740180041240c54510a82d03020203213a81c020700c0c124030b050b591803103804858a046200a00c40381504c0c0d2030350024040c02c0c1d0116800000720180d5441d0290300518108040c22540c4101c0241d441b01e0603682c04004103c6604a100c03800c0703010f42c0a403951030540051460900b44540d21010108070036001c1030000e50f80104d689600309034224020b60601c644907040b025500e110f00740141501c4800700d02c0c1040705 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 472533264 1250 472532014 472532023
    0x7030b1c03020c090c03040b1b0c01061203030b0901080303010618240f02030c1e03040803210f01050f0f0a12060203010815160c05010b090c0324061209 67
    0x240640c4480c10048a80e50400a4460350f41403542d6104d8007590020404084401d41030300e000d02d4000b1014102c039103c820700712070881422460390b06814400e10060400d210700f807144d94002c05140c0d228098185c1289001411120303581c00307841c40380c4094030040c0301c1c400c0c0c000150b90644545040c400b440b444000914144401c6a0340110f01c070440711184034800130003032140f000c4100324944650300201107a1005070385074005c40c0b03042d0ba00c65224000b400a0303d180c038282100d4038070048065071718094032035007084d0469002c1c40d00d240c080000321142080ba66855105241e00c11418006281154105000900032135043c11190b8414a51404194020307525440560300a00e0f20390300300a40d100043c80c01d40041c0d0405d2013a8190381c0158900400030419800710b2501c9000040f44022415179511404d540c071a9014905480a6513aa400e41503e52200e48400f07000e008648036664681c5001404440d1407030b60849d14908070f2031300740800d514035290310060300c04101c28814510a680c3e5610f2506180 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 472534514 1250 472533264 472533289
    0x12060b0a0b030c070b060a081906060b03101401020115060c02180108100e010504080403020111101805060601091802090102010f0906050609150d060b0103090632060907030b 76
    0x40520000c18091103ea1400c000d244803440b480c45402c25982d10010020a0f404a2048c07001503000320442c50300102c1030104003d0064130503070002076295265511403c1a0301700f151001a00c01141c83c5c1071102540713118540440960900c020300c040a1003141c060fa602102d84101710600490f500703400110741e00c507092116640202c6628181942c1c2d1745100301c1e912044440400010b0740740c030058000042040c0100c07482170b900140c00303a2902d80782da0700450b9000c030203aa021541d4001c4054081e006c1c14a4041d1520002c07616041000142c400d04050741082d502400d8107040c0401180d08110501000440008020020a0068469000c000141d000d050800d85524080e46081d0341c0b0020001264420740c000c3d2010744000c1c15a54442091000c1c104c0c0c010b000690003618155404000b49441d0030001c2101e8043c034011035042555943e58003034a005a0710303107441c5230f80c6e0320310b00480d1410054511900c050959034a2123500382800032601100018003c1c0c002c1680710b1b04940c0540d2504030780901e8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 472535764 1250 472534514 472534529
    0x2701050d110a03110403050a02010810080106151707141e1b070b070b0c030a06031a04052a0d0c031506051c02130b03070915180612060b0a 61
    0x3801c0a0044880e2107030300240d00c10020030714041d08103d807019020152401d60380c1c003900400030908150015209800004c1a4040761514a440030451620a004413001442c24003403500e0114a20380740070700b9002445040745100f461040400031856401481817900305a032500146c0d4a600744400c03400035440c00316010010794400107500c020803001104d10040901484244e804080e140c89444066105603032000e0070001003c0045a280c542d000011500102c0e01c0f88005059a034954600c2c61140302091425080000d0004210a02030148450503151107202034240d02c18240e11010b50b880e41d503100d842c500884540c28034500708803551014501070364100701040801d2501d010454050300c0c00380501d41c041c0d6060704583c0098131503504103504d640d90003450307041302d04d0b846180c000041c410855601d605100e013030303030006440c4030302e119100c3c80e001d800d069a101f01d0700f4000817011703030940b8003a440102468420104030902d5100e01d0f210034194060004205e4030b00350b1000440140503a0005c10 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 472537014 1250 472535764 472535771
    0x609060904080d0c09031b06050708130f0308130e010b0d1d06010f170d1b050c040f060f0503030c06010e092404110d2102010e010c020f122701050d 65
    0x744001e80000003170044900c0b88200f0b00202d60140b25544c296055845003001242c0c081c0011400251203602901440d0040100c0002603966442801c0f480c8242d54800d07101c2400019112900c1003011881c0d001800301002c80500651603c0405646440360220004016903942c00b100348816813181d05903200702c0c84100725541543c40b1181a4064265449200c4074400c0c84204040200b102007000000c2080f80c1e00c500300c51100107000c8090603820075800707c0d0140642a40d400070b941c1c991091100e0100c2b000c00005102c2d00b032403a070b00543c0010790400c500c41d5000b88450103140b680020301d90705641c16009484a1341c4c0316418042d207049658048550001142c40341050f90010602074140309a00400994100800d42400d2162803d40180060004d640c600c1040200803000203030380c84100781510000982100392054542110070001005c00160003460b201840607070100134200350221140482031801c6013500d0703044181c3d4140401c445400c0090150006582e000d003003650300303000781e584060 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 472538264 1250 472537014 472537031
    0x4140a0f0212011509140a1503020c160512060903030a181416171c09030c03050c0306160f0f050702040518160b1204021504140f090609060904080d 65
    0x3030340b0504136140007100051070620300085003e814450003468110203404041e0050a000524480c840303091010402e140c3c0810403401c5110081002c0d9401c80404075801000a08080821001c1d4141d402c40d40141d40c0303c0000d000d410036011084a80080c2030090000d884586850450f4039001c3c0e2036005400780d5840e50044114603004181c4a0140c1c980c1d1702c0c10028107440306203250007501e004941e446158000c0350b10b14072000c166001c1c03030900071507410001c08680d80e0b0707035403100204e05542042340c00350020402650607040c00c05c002c50300000307003030900d0314503050900c00288107040042c902010000a12904800c1d80e000300225004650054000d02143c500068104070102c840560300310640b2030040e00280f4200681c030340c4001d07119180140d43c03034035211030310680090700301501c10f0b41d01881c804524254203800384002d100070300d07102450f030300e912040304200701085150030f1905000f4101c0380100880c46d0766104105500110480e215a4661264180100c05004079204210540e20384201c4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 472539514 1250 472538264 472538279
    0x91807170303041a1314120c070504050a060b071e0f050f0c060c070b1305181b0301030209060111010b0303130e010503010603030203161502070b04020f04140a0f021201 74
    0xa500c11030144495445404d20410a81c1c407400040724001d0080d2512060140001c0f0402d9903c2d501e21103050445034020f81075418103600754400150b4540d40d030b00080c01003020742000e00550384c0c001d02c04001040880c1c50103000070034034403a1a40007409105000303106c0c1000250002c00201907604940c02c0c0c454103404e46002941d844440300c8010061048403281540c07450300000302c035000102c0e0b2015210300c070310f40994000280c0260001c90803845074064045841d49031501c802c4016190360090310740b142410601440305469000358545031080400041c005a2140e0f079010f60807034030a280011908a07203a042a0042c04445025a414040083c0d406254429050000c081d1251001c0b07c402c6a640e0740d0416081350003c2c40b004000d41c000b440569a0400c0c03003440506068011480019000a44040390301241c1c82144100c80c210300c0c4400b800154140000e02c0c03034180d082503408004020b4403082e0010308840060041c039000d9154250080007080700d40540b039941c4108a01a0280c0d43c54108 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 472540764 1250 472539514 472539517
    0x5031f020f070c091a030c1014030702031213030c0b1f08060601022b0f0903050a0501020d050903090a031e06021c0b010924090e070f0219020918071703 67
    0x740c0901c45d0820302d4910b01e001070f5014400c1070ba20000d00030411a4000d105120031544940d4859040c80308a45c1a0381c80c0d04101d400643c070500b03441e4040c56458201c80146409440d0181000c04132019540403a00008d800c605400142e40d080060006141d0b2803020040c20542e40d0000c020640585800c0020044400141140103860980a80e52000803040031201d0f4052984000caa004110300c515a4907940180b54510344d0031044e1030321143c81a201e480b0a8a40850000101c907503a50000d240d017568110b40c0700c1c0c036030800c030060040c40c60414580002005c1c80902c0c0000740940382e11042ea45030200e086241a205d459100a06640790500c07060145c2d0140aa0b0159803065403c00c101c00c1d01a62181e0245016100e100c4107035094840c04418a4400c400038149140512042a00109001504800d8640300b17112643c0d440002c80b5510000908140000d0320083e4941100000c00b8016910f211901d54841c50402c00c1103082100c4050052074039401f42d1280452014900d5241c030311020110 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 472542014 1250 472540764 472540769
    0x6110a0b0a1d1509030f041707031407080106060c050d1202041502010b03010b0901030206030403032004090e0d0302130b0f04051c0309080a02011205060d0605151201020405031f020f070c 82
    0x10a00541130742c59004030f603140d00c10322403004c03480700c3c0800c014040b0568020002c3c0485044c0001c542c40c02c1d440c0e030390f528180f001801c44041682d0100000700305081c1d090003410080d01480c68008410b056a60720326a84402078118a01848400b014a4048800e2039055030020301034043c144c80b5494014101178028141041081d000c0c0d401c240f4041c0b0b0b80d051640d601d5040326405881c03c1c0c03855072951002c8000f440c201703002203684030040b0110002d003000c010141000c0e1880a800240c12030059404510303296041d142003043c140180f00d440c22041030000200121035901109640d0350b82145900c490b1445550009075002c00e1070b003102c80b11580c84038400f0306928441d898215a064640a0031941c92401140003800607441c0c0400000108271600305035000480980620404440e61b940c030026600c00f1942405000020000030100c0d2030039400a0200c0c11200c0001c41c0340500344030220340c448080c040c0c0d07242d6203542c5040d0308204080c0383e4125044801701410352611440b4038501020401e8151 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 472543264 1250 472542014 472542043
    0x90516080c04060321050d0203010b0c1c082e090204081e0703030f0c0f031112041a0a140307020615030f06061219080304060606110a0b0a1d 62
    0x1c511455180c02c1c584103036004d0701c1d00310181c8400000c042203072030b5444e0648103444042100034450081d511b030740c41c0040c502034210303160f0f09038454540701000c3d0320709a42e154500c80d2050009804a0406420014564010103d005240942200544403801039010191281625018000b0000b00c80034141c2c0a04180c5401c4804e6031108442840b00000003004040001c40b15000382608200080c050313000c141c01c1110a05007c81e025401c1d454100c403c2c600e540056000c100c40a020794207522051100fa0314808841c0e9000e41403070308100080004444009000416207000a842c003841802448903c2c802c0300f03182c0320071b5607074038003000025110f0805035480c2c172030800007c035410854038001c41c0741950001c190005105d51750300c400030821155090503451030240a58254104501c2c8541c2c0e4050010340541d13207290340d90400303217061011180d0301c2c3d10010030000707001d031800480d07030020600e0604c450308102108511b403a00c03204007004100b4007403c0c100403190f10301088015007011a0089902810 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 472544514 1250 472543264 472543273
    0x40e0c03060a150f0b0a030b0a05130e070605180603150a03051b060f09010305060103151d0604060f0306020901020717150c091c15050103080d0b240c0109051608 71
    0x1e0f05000940032015020780c000c514024440f21b580301d80721350700100782408003c1100b03c0c1da40d51840458000c1d100800b404111980701c01e1040c01c0d010b4100101c42c01401c061801e24500303a10300f01c100b0304c2c80444070800e40c400c441c000007052003101c1000c4103030083c52000340b9102c1159600d2514035030b9000048043c6c12155007100a00c14240b4041003a22040740550344800e02d00b092510044004000c0142201d05165a4a000760310103115026090b000c3c0248203c44480a10520030701d1981010080140e4480e0b8141314040c0030a0782d860f03500e07601703c0354410005038464000c04010317801c164007034210207008440641c030a840c100c1c00090202400020310450b2186849031142c10301e1910500284075000504070603550742c10b06200c8503000360280144140075503101c42008102c151003003030f84141d42041000c10914044025849684002e0808072040b00f43f10910071030b40c02c0d035502020006c201d00080840e929088900a400c00c0682035807010642d400c3c0d805040c001002c48105000305c45081c0714 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 472545764 1250 472544514 472544519
    0xd0e011508030a11010c1223090d11011802011b1a1603050f15060d05071e0504050d020103050901090506040813050111060f0403090e091b01030203040f02040e0c03060a15 75
    0x81071003403d2845285589056001040341030030307c007030a20030304d0100c610001da9180508c169450100c1c98020300c09036000d444030703106100005203111807141030ac4074541d1501548010340c802002001d4480d50b820b00f001c0c00c0640d42c0300516445070b0109507001d801402081e0510a212000310031711032140b02807900180850b000002c04800315141154031021100610001c601c08001c03906288050700001044039142c03040f0000b10784284c54043c0c1d10800403e00c0d002411a1001c80c03103598580d603280500d08581010716010014140003072611001c0d040c155100d020a281210a4000104254109003103071800c1c00d062178214910ba1098544a0750442c20391030114441d8412095142d8250b102d000410040d11803c1911b81300c100041d2044090025001c0000341c8410010070031842003805002601c3c100106002c000c1441140f95030361410580b0410030000001c4001c800e00026a40580d030010340340c0da650741d840d0300e444101000e8550512035201044038040380b40d00075190140c40b1a11010ba0641e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 472547014 1250 472545764 472545797
    0x90501030c0c1106031902040806070801150e010f0c0203160e1315051305060115030f0605030a1407080a0b0610020606060d09020411071514010b0d0e011508030a 71
    0x2502c1000101014400103d040310340c80c3c94070145412942c220241c0511a9040f40008200d80c402d0744091042c0d080a070411040507080f0240500426070340805003214081681c004007052095418a414800c3c0400c0400c40c40e48903024051941d03902400f21200d00890008032600091640b040802c030382103480004031a00341d20781c0c4905c0401da2002c1100080b1207014001000340100501554804d000d140740100070503020030a540c000c4c080c48000710f084900e6000014160341124107020b9486080c01030800158a001500d1102140c00c64102d41061000c44401c600b031450b954049142803046800e8001400303614450180186821100e001130425400c0342640c0f03d00085030072a522130301c20b02c111141138080f82c110701c0d19580f0041001510000c1210300e548035070806d0340141d81141039134a64980490f083d01c504444132100d050307804040c1d031411000311500c1c412900303040c1c2113949405040c03065003001d401a10590400c400e101c0803032600d480405a4a0700060b10307080001d518040c04a1004 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 472548264 1250 472547014 472547027
    0x304051027020d0f050102040e0a050903180f030129011b0203060c070f02090c0a1701030b0c07030212040801090c0f0b070807030e1203030714030105132a090501030c 73
    0x1489501c1c210071075110340d020071451480c031120a4850080c5440524002402880100080e103011041001d050400d2610314007160782c0140081074980c0104075022880300080300b00b00d1039238800c07508a0ac40c0310803080468003405150841000c1e426401c0503001040000900c0b41032548000c0c0d070b54005204000a00021021040002070f4241d00102c002c18940f60002e001854100e0080703007020041d58503980031654041c0700706c401da038000340003166072805070394818040c0d002040031440c180501e5065499480d56141c0c003074940c01c081200010b0607400c04d4001d01c01412008030501a25486036a01c008030740c0600002074007201c900265100c04038144105903041800e84100342440c9080400c60f580b42041ca0348190340c03e40612142c00c00c0a901a075607150040c10340000c0e5406140c490800d01c6018290031200d01801c65012028170043c492516690040c40c0c100b0031800021580c001e1504001c84c0b480d00c250950880c1074030031500205002d42201003001154000ea800708089074681404403102d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 472549514 1250 472548264 472548311
    0x103052a0c0f0307110906090601050c0a060e0c12070f050d020d0b1315330506130602060c0c030a0c05031b010614270907030803040510 60
    0x100c11103080c1000016003124003000c0a904003003030240c9007103400480d440c030b85480704528988540c8005206410840754420071102d03250151003c40e034600740303a8001512080000c2c800c80c1080310105041440391000c000e1391100741c0d008070040041a180c10314041d210203407442c1890042010000850202c20001400c00c1143c40b0350350988507850504040086480250b6016a80b01c1c241e000c840000c10011403030300340903d9902032a0541d5000d90314040c00500202454494620f241042259003c0300c1c40c1c0100000601040c031403050040c2071010540540180d0b00a00e41204001c10040d120200500c0000260f50030360f001c481940d44c5da424070341c042e48505100211181c106000f60300c0c41d00c0c06018800c40b0783d4031400980782060f50880d1800c03440005040411060380d100c4004000107440c10306280140d103030076035035003002030100c4440a20307048900c10a80074607000580010502c1c0e80500080d00a1584100ba2603a241000e0811550705e90740c60403094009494455580a280c1002401440 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 472550764 1250 472549514 472549531
    0xd0c1e020d17040c0b1215030d052203082a0d14071502030702010605090c03040b04020d08090d0c0501020d0f080c18030307050313060c0809040b060c01050906090c010305 75
    0x1c500b044003030580d04281029000300c1c2c2503140c0c0781011800140c0340c0007408500c2130030004101d080c60100c0300780c40c20341c00c02c041041c020f8203d4201888910340c03080c105c0f07608009007050f2200400c1d440741155030b01c9449620161402d180801c80f00c0c7d41c241d4211135000502c2e542200b99207844500d00c00c0682b00e50341c5111100100b104003541c0700041b51000041c0c255036000300405408a1120480f440c240e034030444264006035980c80050005192000d0017541110740101c0e81400c510b0241d5a03041c200901030006032080d00584214400c1110036002c40c0e65405000d4002400001c2610304240c85404600401e0b015000741000505080e01c24040102c0900c402d81d5004015164500030010951180b0210000b40c0342050b5a09484e84041008100c0c00d44540000c55840c013401c030071010190071503008001000003400100d004030ba941400d0758401d5608031000a050224400082e880d440350100801030b81d400c0c0000c025985401150480c071984550058070815018940110116282240c0428 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 472552014 1250 472550764 472550777
    0xb1c09060902130b060a0e0d0f11030d0809070306020f0d09030309170703020a0b1e010b0301091407120b0f0d1505011e0e0601141c0c0c0503090907050d0c1e020d 71
    0xb03034064441c1d42d14461780703040504010480e80c065140c4030607440781d05a08ae10b241700ca01840c4520307414104030704210040d0620b4050543c0c00c104c42c07450b49520301c910002e020a40c01117000d0b00b03103000344c108a400041d204001007201d00040d290280c094000c1e01019a13001d1400049042070041d008111842c0d2503140d40034208a42055582503c0140050400f07204d0b854252030302c01d005560704144c0c9021381401d2502d184ca075850b0111850940b4038204040c405a08503c06101e81e16402403003143c0c01844e01680401c1c040c0d041320100d50412003104281b03074411044002681072198584d1404c1040c5038009003400a41c0e26090036a841c51420300c011040d207011404d003004086004824150002014900040d000340b00401c14109a048050140c007140034042c4000394000e405d11505000c40c6040c2011300e45148280c030340a44a00034100c0560040c0e044200013681c81d07110303108849110a5034041000115001d090040041c0c1c3c41082d07009407991010446100c00b400003c240c42e4542c02c5a4820 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 472553264 1250 472552014 472552027
    0x2030601080a110408070303180f050a090e01110a0e0a0920032d1501080c07080a0207090c091e05030d0f030b0d110108070c0b010b1c09060902130b06 66
    0x800500160070701001102044c030000c102c1d0401804100011400780c1d170ba00c094280401e0302c03800c030100e03a81d02052442d403120034100a1601e0704c01c046000c480b515100015002c150480030f6000d064882c52607603660b0000100c244040d50401c4404941a1082c1c0e46050703207503260441c107412a080004480070302450820398190028401c8000c0d5800010001d1f04050340e4017690450340d0108801400024501c450303401c008120f55030170540c07800303c242442c004145040019684419101d40203016061481c00504005018003c0003907200a00382d0741820800c060042c0001024409540100c8145030000404109032400400364072056030740090141070410a41c50042e240c21802a4030340050546654202c8901e545280403006200d01424803070302c2000c03201000400340040201100306000403800800c2c04100740401309030640b00e200441e917556801c58000d0300040407008218403c15410514500c0402149410a40907948203540d4130820100c040409000e0f50030307210156400103000c4c41007 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 472554514 1250 472553264 472553281
    0x15030a0e1614030a0213390c0614010806090106090b0618011404080106170f06040611040b030103080904050c040303050d090f02180601021b0d0f021801080610090203060108 76
    0x3441c0100070080440e1040425a80410f007400c06c0501010055a51160314220047c0310348a565128040114140c150700000c0e914940c0d01104078812a040008643d58403041001c030b68007550b1821060209061103694504200d640c5010440d9015401c0d42408030016030035aa50244218401c0e00601650a103014005030802031804840c18504102c00e254000741841c22803c002c01c040c00e44400049025070400038250700ca690040342040d56507202d840749a00d40d0102141d40ca81040c3d10443c00b00324010300740e010700e500d4002c58000240b004400000002040140030050840420581d820700c519500e40840550034019488040d001c0341080100784c9007030006500940c1840d01c40c0800e51001c08940e00840c02402141080d1a40540c0031028010f0035a01080207070780119041c094550b403c5c03c91008206584210f1400a1140b03c5455210045688010311410420552000c1c0201d560b542c0c403540d6034461081da44030f0b0120781d9070303c40844e8840590088038400c00301030711255440e13105c04a5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 472555764 1250 472554514 472554539
    0x1270f0e0d2c120102090d05010204031214190905030f1c0809101806020712030b1e09040821040309060807080613110a03060e06041407050c0102070215030a0e16 71
    0x303e024665600304016061a6981269001e845004400042c0c88a043d450520303242c82c80402e581c4107100c0c1141d20009001d0401c0100c60784010407881082004039501d0083d200400a034001e9a0b050040f0412030450150029000161100c0c41d07418500e0070481030300559045c503090307031900700a401c10305c3d4240351015141c00c03407403128010310315022118074107032141c0080340c220798402c44924034403101d50072829034075000d0b9040c0300f0001c80300340d9004410695010b0b1b59040310324003a80510504000034052240460964106041c0e80032011182d600140903084c01c00403c46044000c244600800314071940711340013580c4181a15140d030065038540d5000c101c400c800c109401c2401c903407280c01d811a060711000c09010061102d807008201181440d41060f01e24800a118901a5152038055041d800800d82c3e16604003c8905040380d99007415483d00e23001e4071030014042e412900020003400328451143c01144a00b031b031701000b002110800a035040c0c54401c041100410f03003018400c1032081905480 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 472557014 1250 472555764 472555789
    0x6120b090a02032e0c0915030b0619090806040803130f1709040e0c0f041e060807032d1e050f031902030301270f0e0d2c 53
    0x28101c0329040c840d940024074041a0b03540407495083e0a44011145800c80908094440c404107018442d42c2c0c1d010300002d02d0020700c0e10415806800b100c40404181d8002d070b2000e6a001009000c581e9910340f600000410f01e0b03400300e41c1000260044100050100307000c140c0034025540721003c42d185413034040b41c100d500b00f00030b2000d945640ea207410200000350704844103800e02c0303074600549803541a00402c006c00c0360079281604100340c05c02c445a1038541d842c01d03003e51004400302c6001500240e410002e001304095010941021442c000d00810203000008a1500b1a07214914409140c0d09d00801c130000b1100e40104c42460300106402c2d100002c1c0c007102e149011001056010202d040385840e07151074213800e940d2039605034100150041400700308001c0f603042c10006000035491540340c005036403010000405800342c0303601c0b58040c1b8689070556030400b074000031941d0300503c942810061220f498490120b40000804c0c100038180c0e00025035041c000340d0100007511700000c1c01800c24140424034000c02c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 472558264 1250 472557014 472557031
    0x1201090c05061e0f1b06060102010b0118090c1809060905070e1c0203010209130501030507080708061501020a0b0c0a0e100c0303090f0f0b040c1d0601180305010507050c1006120b 78
    0x45c050003812505181e061103080803510300030041424000c0029007182e0100c0c014074100300c00800011125110359081c83c0465109080008108480c20412941410b414610704440200d180000501b0495078000405442c0c42d40810480c41d10781800c2524480c000d180b1140e0400d22201c44c40d0750054210178100c4120380064009840e2800550000d03608a40315240000800e54403001030060000800111000e407079a500106135183c02c14442031354412000f402210041541c10129030281d03c24010039100551110981106d800c00401c020815045040801c0014205200f4508a0329000244940d0420316031104e104450701a18101c01130102c0480580f43c00f010340408600051001203440043d90064558013014245480e000c100070311503512414042d0003134492140070760590140c0701c2d0000c500b400c200c126000fa000c4508000086d591018205519060030401c0a542190040c41500303030031030603100008103c901d075008030350180c0074440b80c1080182c80400082c040309001504903190 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 472559514 1250 472558264 472558267
    0x7110d0303060e0a02070309050301020c03030117070302091008060a0b01080a0f06080a050601060206090606011d030a0c06080603010c09080c04090515010b070c21060203151201090c05061e0f 84
    0x200c0c3d0103000c0804043d00c85901680d40080c0c21024154080401000ba0000f180207500d459140b0b031407a80d481c00103028840b00385c00b808084950380542044020300440e8040c0041d107080c40d103000c202c1c42001d214810103070b15004890006406070200c1c0700303142d0616816154561903032034a641001c020400b011058100b183d40302c0c80480d030701d4420025060703d5489800100020340c14004001d0500e0405404502c060b0f1140d0180859030f07800c24901a0f86112403518050711030b8003580003030324000e003a980c05030030384544400210f00c25a01c40d0800b40b1420081d402402960710703100c0126000e00c110b200d1082c0d160044c4084051929250300031088080c010401c85610380310000228136446c1003a070000b07803540800541d0400b0044000c0580c0d0081044c80e10301301105941d0140510118a001e1006164543c000006400008000c100c00c04002016007400c0300d40796649030b0207000706a1302d0800e85c1c5280001000061074a03250044580500303207610b604000c40f908840da20303015002030700d5101440e0300 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 472560764 1250 472559514 472559519
    0xc0e03030c01020309160b090f130c030e0d0903030203030c030a0204031b05010e1e190f08030301030501270312020702060723010c0203090f0a05090c0712020307110d030306 76
    0x40400251810321001d00c0010394a003440c3e206946005990000c021103010410410821451048190b810a0703105031002200c1150344c00c00141c843c1288903051050348c4c54002c1190426501d90f00405407204208101e4200a1050805848050741d5200040040e482000081d15001b1100069a00006100c2026003000d850341e50381600070000c84103440743c00d0740d421003c200c01d41c0e120300721101002055174901c4090070402e00c40444c400714288214029400703504201d0340842e120102c1401085524585d842c22034885020030341726842031000384c2d201c1d030901669013040c80204800c2c5003202c10b07014103641820b0141d6400d07a0000010101c40c004147d003400554056110600142015407107440000d03d01820f282202c0c1131290120044041603140200c1112242d40020480304261011102407483c424035400003040318001da008260800409814440300ca00054060840c891042d0400e100400d03400c07204030707aa0301421034054804011590388026034105403070004482c0d4001d24011940d41e4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 472562014 1250 472560764 472560769
    0x9060118091a04060605250c03020f010c05011802040f0c08070c0305040f0b0910090e1504020d0612030801090b01090e09030d0903020705242a0a050c041406030a060c0e 74
    0x4c219902c0440070480c005030012201c2140e03200520020704113540040441c3d00c9483d001c1c500001ca02001340100d9404941b09500da01600c5412400c66011000f40009030b2040c40191b0300400b010f408a00442c05c0c48001815507041d0b00444060b0101c03640c2c1c415441d034907058112080d07003560b00283d003400401c101c08aa0581042c03401d1000e03050708004d055849190341c040c00720210400792075100308203d20030103014a00e490b17040c440d08242013903440501c0c5000c581c00580244102c2108801d61880d03c0400603400307501c0e101c003002d964040c3d21600c146a030b072a16010207966a00b02ca00e40050ba40e2201800090390a480702500710032201b00f12410a0030141076081103960400c070640240e804408100118504101041d010302c16203503064200b02012440ac00d9180100d54060300e000c0c01207421014800565844400b42e00c02000c2140d030081524100359880c2ca0840201c1030081d42801071482c40b00090895003800b03a00080e0080013600d034603486402c010003011214408129000c0c03030013100c59 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 472563264 1250 472562014 472562021
    0x40303020913050f15010302030411090912030f040201030e0a0f020409060912021f0204180c0e0901120c061103180f10050c0105090a210e0402070b0609060118091a04 73
    0x8442d10400c002090602d45d460b004680c580161450405004204000c005801400701c3d2413619000d4401c0c900c2501c03114031560800c21504200b000c582c4012003040703940280202c0180c000d5000380c070b040120204401882ea00c5283c0e090b0090100740450102c0801403c00b80c0c0074034200ba0040b1400907210000f9556014903200d034a56000050380400c0104a10082c03030101e0503401760b41c9850452400746001410242e41410502051030a5541c481802825000b9000940c4e40940281048042d40c3c40e02c0900c00500352071034007600c141402e2840814494012004c400300e5440580055040c00740c9680806518220320344107640140d00140143c1e2162580c024100c6d0b0b80da0251902901c65000402c028210f03440103018818551100801801003100340c80165400c0302d602401640314180f0341000da031201c0c030306e26545800500c009041e4050081c0d084041c1e0080d10101c0302030a40341c5414004580c0c0c0c010750b240140d01c03400d6103d000c101c80302890303200e40224903210ba41800005078043c0000c044 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 472564514 1250 472563264 472563271
    0x60708090f0a080c0f04050121060204030602030c220b0f1c0c120e0606061909050307091d16090e0106170d0807050a021c050706241d04030302091305 66
    0x2d81c00394010413082d10301403030003071030341141540e0400003580b40c41140c02042c1c45094906624106000c010400c2c040142c0448014517003084056581b401c2140c1320340306661106000304c24002c5400481801003030480c62070345c112600d041190b820101d80c60705558071035000c580140342c0d07500300e50310316032060845000c2c02d80d561043d80c0b030340400666440b507000300740c2d0241d00347c00d01c40350800001c0103540d0f507a00042d50444000380807810070b013058070035094031b222849402080c0c0c10301c106038001038640c000760455100c0012010590310140103e000141c0e5807100c8640c80ca0594444880a000702d0010707502000c007030301050b00080b44840c3c0e00c208002c5800225003550035030740c11602071200c641d9004203480f0303000320b210714100d4501f9404020007034403501000c450719844003c8100c0f180d0264840c80035150b2040d000201003092801c05079566508034264402d88a503449890741c005552001c81c400c008180117491444c03c5c00350380302e5600320000d40c000680b05071302c142d1024201c4840b81262151620 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 472565764 1250 472564514 472564529
    0x1151505090301050103110103182102031e030711060f16021009060b100c0b1f1e1707120204050915010e04150b1018080d02150105030c060708090f0a 66
    0x1187c91407400040c103841d100456024450300ca0480400059840311401d000c0311080d003400000c410702140120304511a940b120003595103041440c840303c50070040114040c5c0c460b034032140035103007030000c010307803581c0003103403148032440303544c000a00010b5016031140050089031050303d14140c01041c03580b00f100c0031814282c0b00c83d5614404030105040c25603c03c0503015030f504000058008a648080390824028130600c01c0c0031314110192261085480890082c11150041c1c1d50303203400080441c480405144a07803900300203c0100079200502c08202141076460a40e003091400c0007540a1002401021b0910401ba1240c40c82c0f88680420070003259020380000c03541d40d1001c3c20310b801c00d036000a41c0700e2000c0f10031600d8034201c11010364402c6000860f06100d82498100c80c041c07501084d074a4400e9501c0302c0f600d402035003801c0b046542d022661102c0200590300d500400d90700c920615540384561809541c0183c0c04004082c040303800b80c405440d160000406001040414202180d40031107150300060 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 472567014 1250 472565764 472565783
    0x2180601260604240b07080d06060f020c0a050307030b0c0c0607090911041805060f030607030c091403030301172406090717011208070f0c1701151505090301050103 72
    0x11540c940341c0203413160103080d980048061920800010041030062083c0d0041540c0050740c1010094101d05680c0701107140321003000b18070b581d00320150030040a001810b0050084801b0754040c0d240035020241524005401800601c0c21a940d075000d040025000e080e030078505001e00850010104405031250f011907a504a030540362058203401e40e041030542e100c3c0300d0000e000501c804080c80b00c45420103c1411408a0192140d1000c6400301d0110460b15415000e100100140383e03405d904100c403001d0b00b60382c50a84d0340f60345a00d9840541c04400c0780300e600d43c104100400280d207586140f4550840c400054900300c10100040c4030140c100da03080b82040c4041c50041014a1904420982e03003c007590030303e4042941502088a107800050060882140780c89002005010246c81901c05850784480d008115601a0401d14008002440351480190541c0d07401580108180a00103d03030000c0b0b03c0751242c050404655545150342080380c401002001d012100465909000e5a0b00a40c011511340 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 472568264 1250 472567014 472567021
    0x50906222a0f02070911030c09040e0601090203060a1211060c190614340207050406180501050d0302030d050c0f13090f02120c030a0902150408060a0501030218060126 73
    0x40c1c240090717640400003e51400d0845074095504d00300b00c4e507100031704c0b0a0041c0e5618031800041c0082030b00c4441082c00b4440c61001150021203980110300880040359000010740d40c03280b11100c4080101c800410250b214000c2c240d59051460107060441e40c0030040d1600602d45208003003600c01800c1d8150340da10b856003440314080c0c0c2e80105094016034902d0451726541c84140ba02000d1050f050f5001807400b6442c0300d400000c0c3d100340241c4014240091050080a5980d0b156004c0300c103668810101441c80c041c00010240b8080c40490403065068019604020765044907000030440107054128a460400c295882000314a00804540c0054403800d8030890400707142070100c071111034074600c03801e10400c485071705909104442c5901ca0221040301e59640d5485041401406d0100c0c1c009401c11030b0640300a910020300400b5106441c0c0c041c0440718141d40d01e040c00320a0383d200b1f11000e508044001030196801401c03c24042e4030180605045038112042c40d0015001b1040c0d1202c0104045600c051 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 472569514 1250 472568264 472568267
    0x30a030305150d1a18030d09020a052d0402091002030a0905150417030910020d08060603011203030203070e120a231e010b040510050906222a0f 63
    0x21004480e095511840440746544c078800d02103000f40010030740e0458500054044d0f644d1068012070700131500d080d66202e81000003020040e21101c0822403003503258130070104643c1049a031555020310301c0110b51401001208480004840554426400603020441400642c4581410100611259004599400e0040030060400c4826040648210703a03096004000c40c18003400d44090300c03900d140303541c1e19460601e81d1138035500c600880303950004520a0095404c0da004190380900300100d407a0407519035030748410428248800d004a1041010340190b1101003440303503018660160140c18510703813610b150400181d4101000c41c0052342c0b40d00012040c0c00700101c03a1841052001c0300901034400c50726000c841da8580c07070741d991000d000443c06600001c1e503210035040b406238101c01410401075400c01503402180c2c2d801c1d40c02424020320507000441c2441c14442c190140620740c029170143c0303070161865884050403601d140071405155040d044071490700001d1a804001d03140c0c0c0c48141d080e400c801e40 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 472570764 1250 472569514 472569541
    0xc0c19080d09180b01091802032202030a030c0203152d0606090423040302100c020a0f1704030503030a0b0102010c0513060804022b150207020a0b130302030a030305 72
    0x4003000302280c41001500021000356180e440325a102090f1544c0030340c01250b08000c15401150b42015202e42c41c400003a140d8001e40c0101c040416103e0614040040d100702c01d0306e1200c0c0207426601070f048001c0403074891805024020310090036566070b500d00188102c450300040d541c800701e00d0000701514100d060801070200c0185607005a03d54a46000000214140507061042d8000c64031030b000307400c421410403034131020754202c039005c84140c7c140743c2002590340580b03402e021802c038502079003050b405000240141000341d02c4032420b000e0100075a518580c1c0b079020207032198614028400840003482c01c2c030156118103010040000d000c03407108002801c1d681c2200700305050240400c2032921030745090350503e00341e6846041c50201601d503403004c02c0091080440068005400d100031b500ca500040303d40e01c500d907000d003e49521600380441800d00700e100d4180300943c4810280000c20a00300140090002400c1101c091401aa600c2c1c01080c00d05512280071000241c0d07407010400f4041d06000c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 472572014 1250 472570764 472570783
    0xd020d0e07051912060b030106080a201f030e03160b09070e1e0402010c080301240513050d06090816061a0105030112060603060606090501030e120f0c0c1908 69
    0x96543c1092509601180005101c080580080d132218a410083e0701c09410603002890f034581100c030030783c0d03440c00c1c02c44400d05115040e1290041c2d81c50184c030146084084500082a081030246c2001e0788804c00742c009043c1000162038602080c0682400d005071140c880450b1402200c0c131481500d406071840e81415005d802600344070800405229240c6165244500841c40f1210414541d4450303000503205030610134170050420000000206803400c0c08104134501d80c04080e81000c0f0420315840a1b5036074094043e6003c14550640c00400c80c0e450402c0110b0b180302c0c01140000386645103516102010b03848011482021144a81c0560401000d481840704210030608004000c02500000a12034407042c416141440d03213900000b010b0180780c0d031004000b1607020300100021550b450300a042240207200c1e036400300303180010684190801040014421000c074481c0c91800b100d80b01030081c0d03900b0040074140644180e052a1000e900c5412009000410020140512600e000c218a2a115461 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 472573264 1250 472572014 472572049
    0x190c0503010c050a1d0d060207060e0d0f0e011101090b010e090a0b060103020a0e120c040e06150607030c080a090f09200f0d0f05061002060c0304080d020d0e0705 71
    0x2e07444503400f40d00009990342c05060f442c004031500c000c1d241c0013026807108003400d5802205004840d0400820303600501c0e01c1481118144810800392102c40c0d2200642c400e8000403580d1805ca40f03000a11404400c0da07140414103141e2000064420340a0840d8401c0408940d40c01030301c001402045950320071250700c1440b100040442c00b6443d03580200ca0b04000d0b16a905054020828110b414001c0065810200e0003410034501c603850540307003507a100150344030343d8041d81c640070051300c5440d80460580c2c442c1921001000c400c039000d03010b000855000010503020403182d05007000c000703404034004020070181c65462856481c109000700c00c075640c0c164000e1038514a040c80c601c60b29061800420702000c0ca280740c03181c43c0c800111041c1c0d003508c100d0150342e14261400034525200c0550ba40424000d6200307481100ba100820700d400d0b80d80d0b041c10f544e442c2d6102000c4c40003500180340000102003441141070098103000c1c1c86241c400a070380100f401d8850b20342000100317000504000140d056907443e038 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 472574514 1250 472573264 472573271
    0xf0d0524030d091a0c01090b040201182616031101080601050703230c030a03060306050c1303110d060e100510050f04020904020c06040f0605010504050c032403190c050301 75
    0x41103026010b0740082c4152a4944004450b1644e0003090005450846000304001e10498207075192020481500f114100d010807040380441d4609a1140d601c00700740c035844143d0403084081c120150303290328540e02480e4018481d85081030035424521b80000000c40c841c6d145007450203201c80c0050400c9100421740c03410480300f401101d0100380e000c0e032056920308061065400d10015141c0303115052043e25105c2c40d1503c03001886601540d40342d80040300701c0b0700a50701080326449040b4903825510401085c400c03031290031079080c004540c01d003095200c071a00051072a800049581e9881d0180c81000a030b0a40c95041640e802c43c0b8036285019141d071150710200c16030246410840001c0a0494242d0914000d41d4003060f506a640c83d950304481c4101ca940c0d085a5003890f085c5068066840c95010448016003400700000d49414103000b031320b028140c2d100c030305410b41d5503a40b88504a8440300200c40e04a240305605d0180e1034406100215050117000c030b03503d07040381d070b0303070610780c0d404a420361250780a03a14 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 472575764 1250 472574514 472574533
    0xa0f0b09011a0904030305130b1f08070e060603070c050a110111010b0102060711070b030c09030d030b090601030b04200a0f180302120708030c031312030e04020f0d052403 75
    0xf1000303003040d4000e5041c100002e031619003500312000c000c0109801001c6081304801c1c04980e020f00e00161400708858aa280100c98945500c01e45800040c0301d103011100205020585038a0060007070355110b44035203482000c04250b500c440d40382c1100d4080a0b14070782400c49000364156444112540748928000c024401e003240500000c3d9621002404501003001600d40010910428885c0c500207209404805441c0c0c1025500e00400d075020303c07541c40c400d1144c0555415485e0003070090000c0d00c0401089807240380d81d100c005401030b00c070072151660b10030b81d286100386044401001c02920290304a000c40d40319010402e02600c40300907214a44244202c00c05200105000c10f015041601d030305648203e200c0c00b0700c600e140d00d407041d940c0041501340804540300c1420030001000e00054408800100d1199907a110414602c07442e811000d000a15003104642d03040c1815002448452103002241d4a082c03015105141159030035502110000316075a280081e500400744090417981e0210b018105580 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 472577014 1250 472575764 472575769
    0xe0307050313060842030f16050d0302060609041106030412140c0307060b0a15180f06080a110d0c110c2d0a0b0706091b08100209030a0f0b09011a 64
    0x90050480e1070281d0f040c454140304c0004145c54010880d103001d81116031084074a00c2c41e944484d108150103907845403440c0001030750303c0c10401001800d40c16070064035031707a140c14043c808007400040064580040c400760304909038031214029841980207011502d0000d50100d4000d124090704c1d1201030741b1700b100780b0190141d10b6009c41114030641c1d01440004a40305a0350106407407801640c403a074000c1035020b10700070442c2e03000110000503031052802c4041c01500c502110902c032845000300360000e20120001038032944035501005d101121105018200741c03030040250240c0e000e0610b030b84002541d00303425a4290100b004001403a9038102d40c0e009000300c81c41c1349500420200681c2a10118492280711540d80380c195085028003a141102981c0b0580c41c01e2990181121080440d2855411801c0751001d4160001d1034041c0c940c000080c160102c3ca11a100e0301070340000c03084507810b0140781010320002d80b0100d52003c1143c400d00a13001946801c5103c1c908403403c09100c00802c407100c0c5400d14856 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 472578264 1250 472577014 472577071
    0x150c1101021e1305040203040f060f2d060b04060203070203070f1208031504050c0304140a170a110712050f01150509040302150a05090705030708060a0e03070503130608 74
    0x2115002c05203072250b080f40f031802c0094050f540f15039002440041444203000c0b0b03462300102840c0c0510401d1004c507409403100303812504001da6020762106a40f0441d070902c07804ca240d54401c458040390108200d03840f8206900d0a03800f551007000540e000140310411412f0a101041c0140341e00c059681d5038528002540310058290308008140c00000800291183c045440e042500c10020b40204058a80300c0707562803042c0e00c00c1e5000c0c1c624003107110113100c420300c0c0011404c071040e9000d000f400d0320102580d480c0f141504120480c50501c03c1d50000c84105d00e50401c03c41c1c0007001c80c031038084012074039414403a00703000c81701801500d903034140741c200620542c8141c001d404803902034481e82003d640344c2c20100c1c1420303425021041810f08410034481c0501c580d400c00313030003070400c203007a140c44542d15420141d40700e4041c82086401d03000480052942d094aa0000c44800350240070f6a16041d083d555840c00d542c00140600742c82e52100d2018402264400503580e84110340740c066450b044403016031903400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 472579514 1250 472578264 472578307
    0xc090121052404030e040203090c010305310303061e0b0a090305151006020703030210020a0201060503030a03061a0406021902010e040911100f050301031b03150c110102 74
    0x500d20386009100c1004020414040c02400c000e180e400007001c5a02d03a90140e03078042d10103500294a06603d00f40c946010310889000f584130f00d0042c04000c20900055000d804000c00000001c0c113840200250400c0b05103043c1355540060b548000f40c81302520700a002c95030035401940350001c00c51800502d4500c1c0e510306500703550b00089041d40301d1215038002c549101ca40c1d003000b0924000c0840800d0320140c0d2410648c0030384031316184081c0241d2181c4040f03aa0350068031028006030700c50100c4c0c20784101d50358001c141c408014030020804030340360310200e46198010440200040e40c0d4110400681143e00d44903155280c281034024070309490000d000359603402c441c010440d81c0c0d541351081c0341107a00400040080400140c000c2c4403c50040c108580508101c1610902030423008801e4000346200e24240001529640c032000d04590031a03c805845015504507100b0785405000003101240e02007800c1c20b10701003040004100081e034220018040030b004400e404042c0c0c0140075450700394162003400c907007 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 472580764 1250 472579514 472579559
    0x30609070c051615030c110a030537020613020108070f02150a060f050321130b0d1a011e030c03230603061e0601030c02011d010e0c0901 60
    0x74455000c1c10118140014901d4160000004420001d1003807903039885200c03a10155201080b05489a5000340c80302c0c0000407015070b180d0040701c6a4000203014001a00344040d114000740342d0f08112100f041071034940015404411601c42406021322541041140e0f4032900c41c550450024155074006040b4400103800d12040c04005600c98040d54405c210001c00b81c20030044001031410120003a000070000b90103908900540420f000c515400e000a03076080100e14881e408000c0036154520080366007008000c040c03204429040001c14040100180c000000714a400003402e092600901c02e500804c0d981c0c0506103c4400706801000d00510081d452085050402280390840d01001328002c096810b5082c0030141104d0fa070701030a902410f111440780e80c055007101d1040d02e40b0224030700b0700c80340c048003403401d90031319400944507510a41054003828201e00012036643c03180001090215402a2007000c140c1d075444840d00801002c01080d41d02240541d4079031140d5051425450f10075034041d09066 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 472582014 1250 472580764 472580777
    0x706050a030f090b2703030103062403061a01020d0f0302030a18080c010e28020f090a140604021602041104180c022118150d0504120503060907 63
    0x200154000d801070540e407110002c0400c00300c40b07289030422250f80141d030f100180c440074003840e2050034000d0304000d1490f0045e00040d4103603881e40e621b0001611007044541e4520b100c0c8152031400d0080c001c9204095403040f40080380340907011040d200c8048152410074119031140040c0250290030981c1c1e65034503401032078003503a07a0307071003202080260031341010f10a0174940c0c4229400a2103060f13005460083d01d0f40000b440a80717942c06c0080d503180c8212445c0800740f603c0d8036185038444801c03d88018001c4c03026280c86500104e4000203200d82c9011581c0d0080c1c1ca448903581d02610344001c400a5001d8411a070450511050380022245064803180090159660303041c1c0700c0410104c1001c0c1c80007080d44e03010700f8055900c5c0c0c00140f809005c14244100241c8203002c181511801610b0740d603001400341842007410034003142d0149080c2040c80c9200c80e0081c0003112800010403c0d003004080e0300d0000782010404c1d090510b048500c540701000845d08011060080c45102e50399200003582240d880c1c41c104 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 472583264 1250 472582014 472582027
    0xe010309140d1d090c0f030702160b0a020105071b08131a0a0806030c0904030e2b0b0a0b0a2607090b240a0c05032106150c070605 57
    0x1002084400c0420701c8640c410720480512207a48641d00b0a04903061010781c9030510507000a0001520b002c0c0c034850000d20702440302815405a13003002c4c60380101244115045001041c080c844641500e401204e0681c1c80040c036441810380900900f40c100c0c00314070788140040310048054459900c1c4103001420320320001214101950344541020241c911180078144409086000e00307070b282c0c4100700000c00302e418100040d54610b8085100d85a928003d42211046d9a0341e07513040b48c071031211662959101443c02a044200c80942058101c41d05e00c40c4a040004211410043c401c40b2005243c0d0000138100f000d80d0015458101c803841c100c035007184080c080e98401884200c036410328000111407074440c606000686041c0c41e00205070440d4244d4481d40741c02c1d20028089005c403d03100e41e040614400708894403141e07114039008803c90340500280c80c10002d0100307002c0b10800400f500c150150481074144241c5150204480302600d0f41007418600e407030100d03a080f82d1120300300d1182505208011400 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 472584514 1250 472583264 472583273
    0x1107050f0a03121709010b03060a020a1701080d030609060f0303051e0c1f0c020c1c05160905071b0206032512110c1902010c0b09010605040b100e010309 67
    0x180405954480c3c4000c805582c807040007032030710004d07201104071103a5850204608100601c9500000c04020f0003908503176032a10b003100c0180d0b200d6001101040324442c00d1042144410807054003034036030480a0074003800c000c0d0340101940e50580091554520300311007000030011000074401241c1e03050604980781c100003400960010003401148a0069000520041c068800f00b02404400445142c0f03590410512201d00c00b1181c0080b04400980d1251600c04403500c0c00e8a1540d00c030340c2050b201048042d200790b07a260308020001120726440740502200f403011056070b001e45a840b03001b81c17a22520901102c92080d0400e4661500a0700030301c40000840c1c40504141c2010901c030401103010340384200c0780c5c0e4005200ba611078031800e40320b0349450710308561041c1fa10704840c46945050b00821050811078140724240b800e03154124180f20380070317014074005155284200c0c812040071000056903032401061200750349020714800e1190b041c44c501c049a0540200028808110030700e00066414607031302d01b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 472585764 1250 472584514 472584529
    0xb030607030c0c0b18070b04050406060311121018020304060608030304030c0b06010c0606060807020c0906030d030216020415080d08042001200d090801050405030403021314010e161107050f 83
    0x280c4502e601031b040c3c0200303080c4ca40000030411114166801c0000c00d5892800702c00b2510190520030300490f007080120340010140d10455080014241c108070001c0da201410440b12510554000c6507a0b0080700300014080c26100f450000c2020401640c91843c1655004203134509003803000b4039840300d102c0802c2d02644103109003c82140e001c442040400d440720320140844408031101001071044d50079080703007818000501401404080c0040030700100f00e65055019410406094400c5c1c1c3c4c81c0e1051201607507a0f401813040803a65091580103682c07c0203401d80c240350052200e0700500c07000b5005d010004e4000d881a00506503408440b00c0310b404441c004a5284400030400300c507800c0c096900140f000d001040480b031100854940e000056543c40215090307800c1200d0141844e00140420409410090095284840c0e8850300044e203c0020460b4851010b003a001151980c0030715003004400d081d001880d040504039410300303003950100450103581c0d03881c0601850b070269030b245054081c503840e03103417 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 472587014 1250 472585764 472585801
    0xa0e100c050712050f12040b09060904060b0306010f08150d020112151503110a0c0c0e270312150301060b03131a0912090d05060a0b030607030c0c0b 65
    0x1025600440c1e0380300041c20401c0e162540580d01805504c5c4158050180020785284460050050707504003442d0018070b02c50307034115024164010308104201001c9640d1889168081c2c01030300700c207070303242d08000000502448500400c10140005041881100091105913144e040000c480c44a0202c007a44012903000242c008018042c905003090300748000c20741d080b801c007517500d038090040c40354004070402c40c250f075400c80b50b100d88058100018100d076031003070788854403150088464a0802d5a5016030005410044400040705280c0d5460045001c0402c43d055040d40e4201e07004609240c03003d4800151024040c0c02c2c2910040c0118120314503481c02c3d00312500403e82348141944900d800e807201e00b404452003004442c18000740740344403a40307180e01c820f0030702481021004011a8000440e54005a400000340560201086003104000f980c10018180300c0d050030344021030140100400d03d40f03446005401c0c2400c5c9401c10a80d01c0b89568008142484190490310302d2101d9110156014003000c00341 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 472588264 1250 472587014 472587023
    0x6060e04030804020402070809040f090b0702030721020109021518040b03031801030b04022a030406050a0807090e0403021e0303090309010509060c0d0f0215060a1403010605030303130203060c0a0e100c 88
    0x300c443d03000507504c2c0e888180c49070300440c0b000800e63b0b20044126100d00c0750450003401d03001161240c1c04d082409440707940714100f10b40000900611503400061109511001c122054403002400f001c81e40f8408038201c140603025101070184011701000244c60707010f040c4020702e810f0442444500c003030b0310a412082c280d1001a00440da500c810807131103103820060001080d0b00148814514904a20010845044448a41e10a424030502d1181120070000292004080045017900444c2d0003545001c1c01d8022031182d0018007006c144090340001d50f00f5078030020269908103100700200c24001004032908003009203400e0765102c008400184850085d038802a555103d00c030307510098a034208078081c21207000b40e022186440744500c0d40502d40c08040310100d4208828034000c019444031000c0fa14040100200003152507074a42e80424076680048500140343c80301500720b0002d5017014480190841d144030303042e40c60700040c803001900522622450f980600781c10201001c1051007078282c40e00d0305621 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 472589514 1250 472588264 472588271
    0xf061d03100509010917030f162c01020d0306143a021c1a04062d060f21050a080315040b040b0916030b130906060e0403080402040207080904 62
    0x1190303c040c002c0c01c10b004c1c11034038201ca4a003081d045114030b205491091001084045440d0780d41550701481c0e9801045c0c172005e000b5040c5001c4403852101000500d105980c014980a541091000a180007401d002c40b20a161a140050040300c8582401e011340c200700f0381e1004071240d0080b0200030a8440c0490304010703d0310703000344400060284002484094000c80c0c00c0c14090700c00112501030340c222894000c2114400714451282054a00d14540e4000d001e5400040d41c10070001070110743c3e610440741e60320744459510541c284a42c0354410500682002c00c410b501351070034410044164a4003000340785a070b940c0608104d0410408020021080b030b8051921a01c9003041081c6901a91486401900c12402d10180c0d803000e0405110f07124140c00010045017440d2074811140040c02c0c14040c20100309a200c0b07001148584480340d0001189a010400103a010301c64101b4030220364150700181d888007000018000881e9110032465003042d011070300143c1c6d0320302c0c034541b0019510420070220b801034207 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 472590764 1250 472589514 472589521
    0x601021207060b010e190e1e04030f02070f0f0b1303020303040306020a0e040912030b01020304080109030e030d020c06180a090f0b040f0606021b03070806010e07090f061d031005 78
    0x1ca940241031444001e885c0c04405920f000c0800c0355100c880700c0c0e039070319100c5200400c00031032800740e1081d03410507002c0c4103269980c1200c1c803c00000c510101c80a40c0440c501036481c2029130350420644d00140704065240d041242441c8620304207074070621514102c10b001040c414003103e40d0a141d0310055a009007282d6a49640c0d04d080000b0f50400d600c2c100204000003000b420900b4980030f4070403495840a0684030b000580c1170194003d002c2e10105d18114030007404082100e1000348101582d8500030344500c560800d5010402d480e003d130454049045400000c0f00050310340380e20065503942442c5540c07025880200c080811010005ca50040d0182c60900d0b007070408132201030b800701520030001d4800f0b01c00000ca400c800d1041d207003103201e00c0300141d0100c1d1000c403000d401040d440c1c4003490014140c40d030050703440d60341a242c0030081c1c00040c40198000e040c48107a030f0304043c8a0700200420698410501d141c2040035101545030261103d048030509801c003041d40c0d0510045800c031a04410410590070b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 472592014 1250 472590764 472590773
    0xc080708060a0b010201110d1a10021e0d02070302010c0609051501060f0c02060405040f0207020d05030a090806010501020a0b070e0306150301110310150c0818010f05031e0601021207 80
    0x1807007074a00820403490500101450351043c00380080e00e09220401c2ca181800c01241d21009080c80026122802e030134080301c100030796a03090000641000f59006000c032003e82d4040380030118150300403075104c0d4001c5c03100c07a04264001c01d00c901120f0b0242080c010507100c1d8200a00903000b141c50003084c43c0510500d010a030b88001640b40d050f1000c0c0d580d074000c50100c1000c196030000350842d000c3c3d03000c1c106000400051406400244102c2d540c11009070400c083d42d400f0039648110320000300c82d69040842d0000031a42d202d803007400103100d020028243e80d4503000c0087d456020440c40605010050000110810300035031021651940180484901d46083c8030060020036801040c0d601c81c1d420185482801804201a03e0064240c4100320101a02d001c0c1c20b405500c1c500c2c00441d040c03000358a1210081050302018001c4140084800c65624003640300040c40162042400001d00a0510600404904181c0e01d030404040c0c88507564115159100142e2074a0240c0c0c1ea440c56405000030711b0820403 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 472593264 1250 472592014 472592023
    0x603051501030c08010902092107052409010305060402090907080a06060525060605030703030819060b0909070e0a0f080d0e0310051905010305030c07060503220c080708 74
    0x40c0200c002860003a8403210046050f52920200c0c100019a1900144800c4507030754003c00701c0308001000c00180f4007041a02020009070701080004035004964100804d0800352040d01d8403040040340c0408441d0b40010305c5215009410980f0b0405a864000800d03c0c1c58950480d000e0500c0246001001e1500310b100030003403181110403c40140c18502c0000310f85002d002541c4502052219048108098000103280448864010349010b91140740010709a1000d202440103140a039031180310b6403502484080d44940c40d04c5c900d240440c0740800400450302d0110a075140c440084540300040e4031450012254224500302c03071580032885060001d0551070580c1c4481c1290303010301c01c0d0b480d445407403003007070303e80d09010708036150160083c560162040500c1d0b400075610101e10062008041c020306141c7c0d04540090f003045030107500000b032141510b08100407620081540d4a0b00ca0720318503010a000035114003041c40c08601200c00e61803101001281d458080181910000311101d590351608220b546 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 472594514 1250 472593264 472593271
    0x31302030c0609010c0311150c0301030c1212050d0f02190201061a09061b120715050c18030712080703110a02030d0e0301090c08010b040b19030b1f060305 68
    0x64441c8101121003802d0032801d49002000503169029203e4240c0c6042d00c54000d454a01e0001c1c0c02508003416401001e0201c040c094802948000e44960440c60a015200541d400c080344003920141c80c030000441a130030240010426151841d00c1d04084001d940151441c00c104051090021501c1003004042540c0315240d805140e00a210b500c0c1d8a824510b074212102c3c06001a0010801c4141490300f06100141750080d64038030030b590314405000c581810080b1038401c61660b1540003800906008070490b03407042c0b801445408109030f0500003ca06854801c0102000032400c0300f1000307081a580a00c0340790000c0000034111078030508640b500c1c0d0035030b07400b1700b00441c081052441c10803002000010f411040550142c0288104802c5074416240400c8040505034550749170401140000c001c0c000000050402500204810520b40204010f448007403074624000c820804510342216011440c1300210fa420a14143d520b441d04080a1440c0401110192881c11034117000150030f81d03d41d204070b20 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 472595764 1250 472594514 472594519
    0x30406030e151524030a020702120a0503030123010f0f030f020313060e0d0e0f0a030f121d03030d090203070e130303050604050903072a080f24151302031302 69
    0xc8400e0150b80d01c050600c899041000130080600010344000c032103500500d0002e000800c0b464010441c042c05038640807402c007080350140c002200400c0700c10440350001d0b400081c010340f40031036195914002005441080d4010b400c001c032414011420500942c41382680741d492110565603458181c105803240100c4a2007110542c0c980b100408081e440424411168010740d030719020320882c05c0c010041c0030045050902d40c85404800e00200041140c04a082000c0c0724084128032600c0459010345103d040b54481075681090a0241d491681c01208076200a1417030400003070805520300100e40303400f80c05d0b008000070140e000103001c10040e0020114201503c259418030495907090709003c1503500c00d58140f546a40f00b403100b2000500310001d11000e5095a810f1103a0100a030740000c10215015401902d8940004000c903040b02414050107030402c00b03c5807603521203100c8140007150044000c0c49000a20008295441c80c5c4e5100d0080644040d20000c1c00d54983c140b060003500f207010701c0b032001c03032 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 472597014 1250 472595764 472595779
    0x504080c0102010b0a0611010212040f0308010806060303070206070602090a031b0501050403081204060b100504080609060402150a0905040f1e060e061e0307060905030f030c030406030e1515 83
    0x20141d40c4140100002610007520211102c0e18008003528054006940081c595400b40700b10071803561108007070340c4514095a90014207014504014040c2041a0003d2965070040d00c100049514000221012941c0c1500c860369108081e0911000034094085a0350b40f00d441d1010000500c10720303c2507680030721016500055401d41d14001501e243c40fa51100030324441041c0b00c84120324880303080440e803241c01580003261910b041c1c40000e031022003506480c004241c0104091100300420080694000c2d0300000400040c20107400141c40045245041c44c0e40c0480000c9901e02d661040c801c140007003c014001740400b00342001244054003044401000f10182240c1f03078040e116460003201c0c12922040409407050f1110700c10b0000c404900c1c61260f8450b010020080159141000814003c1055940d105442c41c101001c05080840b0b0130200c01c101e9100380101c2ca0301520100844040b154241070020301041a110068107261410f100360035a5200b0030b04000709420134030712201d10b6160858524 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 472598264 1250 472597014 472597033
    0x30c0e0a020a020604020f031c2604020303090d021903050721030f0807030212130302060615030703090f021003050708090a030c17040302090a060501020d03060303021b0619050408 79
    0x803003280520000d52005900000125000d403c01c008005103001c03000c0d003620761141c40500420040740145020100244124000c62a1a009002c84411088942030303141d41605050700081e50340d00600380302602c10700054506d4821940c0314004200784080000c160b80c082960703810003030b0322002c10b0300c070b4410054241d0074508501d004160b04981560752540300da40305928840310869a00e00c0c001e01c00e006250b0f0801658070250715a0312024858083d2000d4144042250b2130028280740c40a0a1603000703001c4050140c500030143e80031703658404010b1400003802d46003402d09240030a01c441c0302039000700380380e030015003d0703076144c0c0206200744074940310b085c65a01c840020b03648e11520307110050001803441070000700043e210700105040280c10030545091685035000111780102c04c2e154003050941c2c440c070410103560188180ca0312130a540c14100046459520065140d40c1e8420300750302d01c9a000031800c50b45555040565507207030b4410404001440a03001c02810790b9000340540d40c0390f4803c10850 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 472599514 1250 472598264 472598281
    0xe0706080108030a0c060f06030f050c0f092202040509010207020928020d2a0311070206031503010e0d030b01020f06040512160602030a0614030c03070b070f0c030c0e 73
    0xe29040b40c5007a00114509400c00c0d00468a82802c000100d51032138880d4401c00018101d4010f25000d107000343c40301111141249012464070b00c940b48424003030300c91242c41d0002942c6405445a06c0b80b034082c0c00c4101e0344003010710485180510303c00254041d03e00018442103080550140025910076a80c1e000300b40c8401880848038032203216074403403025680a50a455a065402a0001841c42f2601064180d142c007441900220b40841280235050403400128205502d4015003201c184016070341c51034040030790040380d21844010464007071500641c0400b01951000d44c0a0725020804605a500f04601140c1c001c000e050703035903005170040c410f044035007034100780103e140c0b40070710303130101c01001041d2699103d40c031550032108546c000c00700e8a13440c00e00803e200340011072144c4803803c07001401c5802d0040482064440e42c0846000354811182e041e91038500051350003c0da0108400b00d506c495042c6001d00b16101e414400a1100706c03171000010400c0120703200c810030b844500f1404a41690303548803 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 472600764 1250 472599514 472599527
    0x70c0b060d080f180a03061b03020f0a03020f120f01180e151009140f13121803020402040b1b210307030e010e0f010e0106120611070c06030e0706 64
    0x107019011000412002c0d4400e01104000e040c0c0900446070fa001d00101000007881c9034000d0341c026168036482c0c03a2040d1203036074000c0300010b4441441c142142040c01320403689c00607002d40c0100a06059000400c0205154030b1001d48102e10b40c2d102103039881c0c2c9052190714142c50004c4c400c05901c0c5840342ca440003001d2244c0104041603085c0381c010a21190902094000f03400d001d46000321401a400c1d000c100d02c849805480c0d505a16010b6404160078960a0682c0450000b80134502c10114811020300261004480320b03510441c91400880d56288042e40080249441e84020340c00780c400240010540d22710b5018000030884c004251407400c601800203030f121007806800144d80c200001e800079400700d4000156070000181c3c0360000361050180080c0f800c4035610350400c407603540042c485c200310f0902401619600100c0000a00240c0d00d003003185002240d20b580300400d0107403101c1045040702c2000040d0380c3d2054014031060145607440c017010b0700500c1c0903503007000f40340540700010859502504 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 472602014 1250 472600764 472600789
    0x120c23040621110607050a030305060120060414030c071205011d10050403031d010e1614040509120304031d0a05130e0f070b0904050108060f06010c050c0306070c0b06 73
    0x600e882d040ca0320795503800c071440c000f000e0f41603220000703010070404940100800c100d2184280c40008450600704009050f4070714081403802e5084030704110101c0d02ea00441c1c17440d04182d003c80c01d14410692895840d0541c0508510880f15205030a0006400c0b075866452013821070113403008010340007001c0e420114200d07482010f031402d98030400040510f90103550009910030701070300c2e002400b09030b0f0840100034041c41e0030b008280e580d15107200d40340f018010b200c541d0101c00111100c0b0a514544008400c0c0c11071104001886641d544001480100f0240401c003a03d0080d8040c0694a203000e1070050811023007100b03c02040044158021518104850610301381e440091a4284690302c0305042c2024200b101800d540c0c85c003c0b075010f58070203002080310310040c14580107404c1d00c404c84032080c0800c4600581c0503440c40d9105c0340c18442040021484107412200a2810700200461420020302d0a03020200a6800d44101010072000c0c2d40e000c5019021603100c0c81e01d402258842c1000c20030042842d4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 472603264 1250 472602014 472602059
    0x203010b04051912060209100c210207030c0305060708010815040206091309060b01030e0601140d080f03130309081507110a02060705010203070e1504120c230406 71
    0x108014012860043c10801214074912181c610711521100b0100c4089401001180c0d4a600400e200b80c451070041c00d0800c681185240602c0000b00a448000044098500000007002034503139007000c680c03091022501454000700400c81c1c4954074680701750b6801085070603900045092001040d004004560f01d503d85a00551003103c646681c1c0030010160b012050303469000b194407848100c50003490050908881c0541e00010f9040d0090300058103a03107400c5160482600880d006004504803101128565507081c0c440c0d0076112018034080c2c8030303031244a0b00352501401c044100002c2a20b0601b038140c01c02e1182d580c02804a175a01480350b952050307106c807411441504000130300c001d845050b40da40c3c3e52002c07808071048880150007241d03803a0b000010603074890750004100300d17500b50090103035048032313030f003603030700080401003102c8003401800369028071402c91050000b06002d1129442c52140984150117615104a4181c50300b4042003092500c150301403400d00f50005480b29903084420041b4110 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 472604514 1250 472603264 472603267
    0x31202030412080a260609060d0f0b0a020f1308120c1b04240509060907090b0f040e010612050a020c0a0f020d0501240b0304120e03070e07030c09090203010b 69
    0x8650f10aa0603030042c525241c2000385820491400114801010145a031821902142411b10b10f0600400400092040d800740089440300000242d0440361074408a800041410140e151112400c02911039080241451000030a041d10314015010003042101d00b4281150f19001c044512841c4d64051007800703200b950814122001c03400b202c0c0701000c13040d4000800010b0b0344590b10001508601900d8200d80030704412460030307c141e0601c0150b664200c8400c850301151482c1420008ac81c4440c03038080c0c088070712000b05240c07585041703a2081d02c001e80303440746e03480310190385131300c0003c2c401c000f5003003072001050400e004640a8401c41c4200d400c0191281301500f40c00c00961503050b1000d069000498000602031000c8001c0f437800c1c4640e94480501030644424800401056200521a500b0100c4860801c0041c04000354910b0542a401d00c41410403100d0030340280006800c1888c43ea000d110003c1003142003001c900c0c3c1c164006200a05291250302a03552140c3d00c88080b40024000c4030b018010 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 472605764 1250 472604514 472604549
    0x23130809040c11010e07050a05120d0c03030e0d0804050c0d030e0111031201090b120c0a1404150803090a061115091204060f08010e070903140106120c0312020304 71
    0x2003541080c820b0614604080d5140481c0c8030059084828005d608a115082141c003408180382002245004001c01c8441c3c149100c60400f00c280c581c91009102001c0c030850381c0380d42e02014002e42210610006c0a07041d640030300310704032020381400004c880072212070161021380c032060b00d02481c1c0003078801d80554442103000300d6030005494071403054100d50701d0751106004070391034903800500d141d0184c5000100820001c41c440140b0010808038550940c10350850744120341c454407030b449007030104d48000c40000402c1c080d03c40418001c00403807071b214071b0160f10301601107254040000100310032042900c40c4003040e6074a000c00c80d918030350345d201d038145c40d000030031520b01c6a041860495040f82034a000c1c0c40c03228030000d1610303691b40e000d503110b4008a105600c81c81c98003034001e801d0f280100701003480090315141c9810000e040c980d0601001b0006015105000d1945200b540082e0291103848003501010032182011104d111142c401141c1c1d0002c1d115910061501c00710503102112102c202e00d1307003d001f = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 472607014 1250 472605764 472605769
    0x30c060106080106112e1d1204030506270a05071a090306130317101a0a020a060908090a0f09050c040e0a020a03140c03041104050c1c02070623130809 66
    0xd4008441c01c2c01c84100404071502485a00c107840081c20091f100035680d0075012503007403d08402c4440c19411401c180001c001041e800302c0c01580c00b52002e05a0000f460342841c1071002c00f00100d07588003052003410885800c0260005080003903480501502c1d01c00e01c5106840c000c45d02c16541115016000030001c980b01058001465079118820306181140043c030403c00c840550b01190580d201940000c01004207124050400718070301048010039141104d1280042d5441c194480c00424165813464000c0038816000260f43c001140223228585240ea65410086624114005c0381c800d1860f14010800c0401038800f19412501c500c0c05120403a031703540040c10000d41040030003a0034036486030100440c841c50400020300c03a00c40c007a41940c4905190409103149a81c851810380124545818020100c41140944a0811115140381c2c040030101c0340d000007074043c01d200100500c1c03c1240d401c0c5045200640883c4141c000040c0440c90340e00c08150000d151007039000900303030040800040c540e90 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 472608264 1250 472607014 472607053
    0xa11010612080d0204030204020a080103031101021204021908191a0103020f06030a0204030b0f07200c041508010903020a03170103020112091a0a0501140111030307110708030c06010608010611 84
    0x705190000182801e46d00e1700450181e0b4130040c20350b000100004014410142c12030019070522030b011000b1400e105544000d000c00d40c0700507101070b100b4405144552040711440c05000c4c05040e480050702e009004040b04034090340c41c41c54044545103a517100c032240140d00c41400604076078000780812446c05410b002c0c81400e5001034116105103408200100215a188030042d000d000803072481038082c42d00d00001002e803030317510100c00711522841503200d4404000090500c0803503021140020f0000d1807103002c030100c3c0042e078804003030342d42080e07106403d058000c181c9050840c000e440b00301412a20101c840308042e8240002070101300b5006100c1c010001c1984240e8000340700751008403000091208400300d1200480d80304000c161514018826498400e40b140e100304020300384210b4180c50040801e4880c0001026081040b0300448506861a000c0140387c009044010583c0d40e95100c40c0401521900c0901617600850001000015410710449011240414901c0600002c8020502d4400e80 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 472609514 1250 472608264 472608277
    0x3510051203160816080904141302060901020703060911120f0304031b03150603120509012c0603040f031d13050405030906040b180d0f060b060d0f020a1101061208 71
    0x1800f07000c4c02a060121002c0c54400d10007806503294640340e0001c00100015259050040305030074840304240a4000324182d805c0c4e520960407290203031070b1025400101e141002a5001034221400d0810400c1807000c00000146082415141d2164903412a10026600e004002c0c0c0c80115900c2008100081452540a40d0765130100940c00c003039096590304d41c004030b031491942c54940701d079a8640400410540550700c143c00412030400e50300f00b140001c0080d040e8121141c100c2240301c204c039044203500e01045000c1c0e07521800204125103a0030715082c0580c604102d000101d000c101656045001c01c1141a100d00a00c1c800a002a0302d80c1102c40070b403400b0709070152044510b0721081c41980d0241e601c40e00a0400341044061481d1545801d51682c041208a829203500807104104410082a44000c4403d45160080e1010034032904e800040f4042d84902d025000040d450220385400a24298004101c0c00c02290303a0826031102d203030052400c81d40780e4400d222882c400c0d9116030001500d020054501c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 472610764 1250 472609514 472609523
    0xf1305010603060f0209120606030a030815030d0c0b060d0f0f030e0604060f0311120117030c01020a0504050f0906010f120f0608011b080603060403351005120316 71
    0x507007541d203503211000e032200e0081c41c0c038201d80c02080c022500c1c2049140c0e40070400e640b0005140b1400e2940200307486403a518006010400ea8100140d003070240700d020003211940103800c9950141c1c01300e10040030300840b104201e894a681c5c42c0842c103e80b601c00c8807041e4058010705080d01d583c00d107586501d00382c00007000071014490b080035002e146580c1c00000e08028184c98443c0d10a0441c0c6140040c12103503505100c140e40c2d501401001c968980e8900c071075043d100f88500c405049690038500354514020350149100541c000500111800d5002d8042c01c100c0f80c040c0c3e40040c00c02c01c550100040c4140032101580022960450035125034403072001500c510301030034000a800c000a030304110a90340190001980c0da91030b030000030640c2080c0e50840d500300c66a0714060805081100009407940e201074005001c00c14640c4203006000c0c007001c070142a0742c01c90442113240402c00503640c0c80361a002c0f149101d410304032440c0041c60f07082c00c9100701e40c0300101a02540c80c20031141c6d05020903d03075110040d00c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 472612014 1250 472610764 472610771
    0x14040312200d02030408010608011e020a02070b0d0b09090102030702060a1a1206070e03030711131d06010501030e010e07090e1f020301050f1203030402040506011202040b19080f130501 81
    0x70303160181403244803048110303903001d1903503941000c00082c02d4910550001c07a680c0c2c03608140d0400040740b601d411403c0200c0309000350b40c40590840c02ca03c2e1000b103130031040f900440054103d40004542e40225a10181954410040c0e030f00e42022038200e02044882001580114000424400160340421401d44003da0000d40592500340454101c819400d0801c00c3c0740e02440c14890b00a8110001442111044006518210380ca030383d2240740c4050428600d000e40c0d6040800412140b19800020703078814111901c414828440b112942e42d03c8081c80b0b8903006c46d141c580580d10140060040d20303030310040d040007400042e103880c2680e0007d254280021807a802402d000c0c144e40100d51008541c0c2031100c82001d42c40754102004c1007210b403849440c142c0306015148044030381c170501205076039000d85c04440025280d581c500c0142c1d030300c50a000003040c0c0d4a2002401081e181d0100000e411000d5450301c42c11b620315000501510100c0007903804c080e006141d40005070040c5400505040c50501c19030020 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 472613264 1250 472612014 472612067
    0x6120f08040b0a03091a01080a0623150a060329120a0302030a08060108071e020a140a061103061518100903051504150902011b0606030314040312 64
    0x302c0d140d401030800c010001c0c2c0c841c0b1000c0e051201d40d100302c201800d481c4452003150b503d406181503940c090030740d0080516445008110207805507401c4090401e28000c1340d40818170308040030103852462651064841c1c441c0080200714584203103e003401c904031450038548140c407840380c20030940184c00000c69001c44080c1403d94040360a08c4640c00b824801c0c0c00440c3c8808035190040c09070113006003001c4c104103001040060702c0d58840c40781085200c0d0040781d85c0c1140d0303145100b00d05100c6404005050400031400840440724000358261000e8080c007010000460804603202142c441540c8603070744945409403c0d044c0d6501e2030020903040f0650049e1100030b40107031000c140000071038a2640013040070020100140002407151720180c243c2d600140140389040c0d40d5202c0c0401c0c1101050150540d076020450842e4055030b4848408042c110b07602500c104c0c203140c000d018041d18001140003e40c45801381c000d80c8002000e03601600e07031104501c1d0582450400844900c1c0a1250300e85088000b083c28 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 472614514 1250 472613264 472613279
    0x60f0718080d03020c19032a0b180f01020702031222030807020f220c1704080406020111040b040612020405040203040c0303080702030a0e0607020301151e0906120f0804 74
    0x1c000852010b460242e110344110400e06c0c10b0100349200c0305a5180000e8144001075400515040c000e03e80041400c0000041c9103c0d002c40003d030500200312008807024000d14980902c52060300010510440303095084608030385090f030041e580025015445200c080740c00c0364013080542030052440e071904030700110f85c1c1d0220000151039403050315102800140c1a0540c1407c8a100001550a540d11480740c83c600242d88104000e95511224403035540c0b543d40800e522a90702c0454054801488030314904090414410680c0103120705030140d0b04c1c000e10342225055003810f5404480740e086103d810245401401d44081742100c50104c945c40e800c1001180380d0b5517a10255000c0c50140721889416400c0d894042e0400c90080c004006551092000f500b015500022080c1c014100742d40030398a85442c1c0c800702380501400c0f40380c4108407043c80404103540d0641c0d03121504500240c4c000c504842e42d912010401c0310241d010b40891100e40418140108420301c9424014a1080391103614266581c200c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 472615764 1250 472614514 472614523
    0x20a050705131407030c08062706151b06090c01050324040903020c1810060509031e1513080f0c1002030712061703120a02130303080105090702060f071808 68
    0x4da08000c00e94650301c8840407030b4443e0340c1c4c0340d02c03100544c0d03400e030340040d9180c0c4146000f12407080c4407014014200003480c65180d204e24028032085001901d03488241c40c0c240c1d05a42d42d8000f130141018443c2d100024010790340021282c405010685850346551203003596002152800001924440d81c01070010f5925121032203009001030096018102009070902003108803000400240c01c0d0307580580510020b04552901e82003202e12600380030b5903c0c035101c4082801c05c851009460040d80d440076040704144030215000030000064030f03054002d0703910110182d04c11090b880740030b03000180602407001404a0800148080e89006048445911180c0a03140590340708460120020710020181701d210101400351300702a0410441e407410000c168004241c2d07074042d80507100001d41202000c40e480502980c110f030348015220011100c8a501da040140c280407003803003168041c2c01000c000410803031000c80c055008580004101207541c9071741c1d170211010582082a501410103519000591030810070 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 472617014 1250 472615764 472615771
    0xe040b09010e071206140403020705040b0112050f0f01120507030311030c0a080c0709061505030414060c180f0d030e03161214060702060118020408061e0106020a0507051314 76
    0x5200220400d135515084058400010b85509418001700c00e001c00660080f880e5025030700306032400144212920700490f601c04403400355244603480c140c1070200000641d16003d2080e8103490745080b070780e6618005881038840b2004054842e0300301e2401400028031540402daa51001030007102d0404041100542c00c140c070021303040300c00000c00900ea90f8801d40900100f80104034415041240da0b1034072101003a91000c40014104000000000038204402c10444c560111945c0702210854500f82c940c241c0e15610901c03017040b0101004246140d2498010002e0040c0e40d0301412440e1062070030307601690075080303003200140d050003400b106110414080d00000000c00c1d00807440350701c440da90300f48003903002500500c203d0142c00c844101303d1100d400080590450303a0b60700c03502c001601140a880020300075900583c42c00c0c01648144005110300000c0360803a241401011a49a640d0b948180d940c0c80710359030020300e150886041005030f0b24100b036840c01c01c0b6103400d0000c42d01040c00000c0c03200100045 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 472618264 1250 472617014 472617029
    0x10080a11120703092105030c0901031806050114060906070609060b0301020706060e0106170112032006041401021806030604060302041e11030609010b0a11031b1005010e040b09010e07 80
    0x30103c81060002c80c0d440b0b07800c81e485050040c00307800c40048005004e1f2000802140c0000000211101e40381d210f6403081b84410394024524440c0c00641c035084010300801e00c1000c48181e074204101e1803c1c904242140c1305900000c107840d2600342c166a60201070301ca00501954120342c0c81c0603541d8a91000c1c001070800c0d44c8184030005046091910040c00900d06030030100400040181c0d40c110a50300800321819150309403600c0019060f9480c1c212024599282e00e81401400d010a15001140014400f0301075032044d001c2c0c4204840e119030007804c0380122800c030f9600c0e010001822400b410701c0001580c00020141001c40c40701e03144e4011034161840d400030405d0b020f1501400316080c0a19220b00b040070058515002d03c2c60130305c0340c00101100818001c80c140d0110004035901c031503005094000f4400366030310035240c80782d1400c00600051000e54180003c940113400d8221810019446018180c070359880032940c59032250349860180c40c4008240742181d6680c0c45200d100714404001a41c01031154 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 472619514 1250 472618264 472618271
    0x12060b0c06011208040e090c221b121d0307110910060e061b07080c10210b0a1a0d14070906120b0d0f020102010b10080a11120703 57
    0x2200101807070808141e000e020311440d440072480c009012081100c1c2100c85e000080c940f40e4031101e00060030240f40513825988910120202030280001403a000f40032010110100f00c540e98640c00c442c100c003c0340146c0f07800240f49191181c0e08940c0c660020350840401c09401200044030344241e8035540c060382d41900d500c90300200a040601d4448040c55101000003521600f040c94481c000e8580d40a900d44548100e40c0490b03031036000724610700b0003840c07103800e6130403510b03401c0c1d844142c5034480b040e10321110b000d4003180380c032001210701505007011a01c8000160007510560b070800c010042c224151440d41c003025404001481c000b40c8100580b50219050078507a40300f1903014590111b40c01c691041242c0d030727070380020051303200d4001002c0d404480c0107003080d40415501207148002401c600c20110b5010307a01d2a08081032104040726409a41d2003a0020041c4119030010051240c54142200e0005209480020205452504209404c4041d20281e03414991003030261110900c0403503200d00007942c0e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 472620764 1250 472619514 472619527
    0x1b020a0308030f0c040e0406050a141e061206130c0314030a0801050405060d021203041d0f011a04120206040e0109021306030506010203250b040302070602010506010f0509040c12060b 80
    0x8115154015a803103104e28075081c941041d40100000042c4060701c055038a100252200c855900010b64424141c01e40001d00d16281825412480d20040700902c96000000020742c141800e00550840703626600040c41c1c01d50fa4080419011030000d0b104442c0c404140c800000060a00c1e42c040710206445405113440b0700c00500e008003900b8050344098411401e00040c41001d4856104240300c107601034508251581d8001500b0386988102d03409181059a1920000c0d5a181d00d4600e02d401501e6981c083d145c984d91350986c41c44103c03514541080b0b01481000b04101030312102624200151018040500b09030780c03003c0d1003143e020300364840ec942d0364000070000001028480558050103907420308100c02d081250000359680510b0504c00b07042204a030b070790031205a03002201c010311039200600d00c0c844c1c44e062600070f46640d0325108140c09503007010080b40307280d0f000b140400700100c2c0d20717550300e0b051a01c0308d810800540700990b142e1007880644201c041103075909001d13050140a50340a540d98805 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 472622014 1250 472620764 472620781
    0x60908010b030c0a1412060702010c021006050a0620010510090b0a061d040608011a1c080a1d03011b09050306061806150313170c06071b020a030803 65
    0x410655065101e6049244040c141380d542040c1398041d500407a020000c40307000c01c070200b02140611046812244644020040207a071f05400400f402c402035400d44903801040000b00c07081c1c0b4210302409a01c0048240c040c043e4610904001510341003003c41082c0c1c03503605400c00c600b1a801920b02a0031030740541c1c0180009040750080b8007101d2010303140c154880e8940400140085803404984124070700d44202583c0342e5030f5070703009a0068449100200304100e840c0b640b0055059000c0b242501542007558201d082d00c0c80340449640203070304070980074644001d1401c1126140092030800c074014404640905c904c4d01d003440b0f80741c005000461000c3c070804040001401043e890380c4035600ca684018100803181e1902c503403030000b0240e5590403a1281c1c07249000a00c1c280c1c040c0c80c09003800c11002c01044010121800c00d621040c0c0209514044d0804100e40e0b01030902c070300b20380512503902210100e04086c0c840c521080041044007204103a0741c4041c0c0c0000c0340145650300503210410084203003c00714 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 472623264 1250 472622014 472622021
    0x21903030f0e06180f04090503181906020d08070908060f0109050c0405150901140a08010f050a030b04020d05071d1519060305090a170a1103251b06090801 68
    0x103411112213080145000031046100c080c2c3d00300c10301401541002c54000d4440b80c01c881c0803298020305580d168100900b035011840b501220151081ca8501001404a96801c030b41c0b40030b8a81c2d40e405040c02a40d014804c2e41c00e0345016100c41c0c2007244a07080000c20316001d206c00e9005102500c901c1c1c485500d040c02280541d440030780700045070003041000700119030380c42d8400c00c6a05041e2074817948541c285801660111540000c54107c94000503c3c141304070351003003050341640c280a402d82c95441d203410a002014141307020040000c4c5a0b24081401b600c6c1030302490901c83e01c038008562003036440d4104d08000d101d40702140c10024140105000944001543c80510184240d980700700080030518031007030040c400c0c4140c2c0d09141d42c407800300e07600100500240601980010702440601400706441504e64041814a00000d031003020088613060080101c80b009024241521034403d46a1400310802c111b403902142e9040304504c1006446002c404010020300994507a495410301c2c04010785d0a4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 472624514 1250 472623264 472623287
    0xb04030f0305090c150c0106060f030e0619020903010b04020c0d030b2e030609060f090e060709091104080618060c0301030c1406071b1505190309021903030f 69
    0x781400c100801401c1c0c1c10000e42e0100e518801c68410400755034008040030030740324040c0508515400c040020640d280c01803801c280b00403107541c0403c070340a40d050f0f03002d80b01c1ca001c0d41d40c00345c2d4180144540e001c0302c2c940d4000d092441c400800001e11a0740c8500003a003260300006101882e500034189010b40c40e60103100e00e0000780c2003a10090300c198016446102c0c01800059100340b1b112000c01400721881c82580403a01074651140d0821146840e0030a1441c82c101512071450355a09090800c61710500100d80c10f80200c0403901e400b800306042c401c9401c007605100501100ca2207080c0400198800104a0140182044100103000e0000c0314030160400c000103044101d4804204010070004266507245422201d800c428910b081e421360001588503c0303041d40c003030090900c00c000f40c010000039050b010100e8290103070040230b207001018155903500840041489070240b98444240e0f250107600010380a030310040c044250210050b03140c04c6069108c1c4c1042c4d001a1015602425003034010785c0070400d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 472625764 1250 472624514 472624517
    0x90106031d160303030e030403060608070905070215010b0d0905070b0306091b0d090c0302100305161119020402161110030b060304260a030b090a0605032a0d0b04030f 73
    0x240403060b11607074403600c907880002c2c101342c1e0b50402c041c05884113005850207594880f005004441d9200e2005a65001500458101030302d001d0200700100d0001030320f00040c1d0007889441d0016860841544190741206444100b81b54032011030070001030b02442030b000546070025095880c8d00703200c0e05000c251480186582a6418440070701c600c64800001605d07052204600c01184901c100c0c0707848026101c81c1d500003504274154210601d01c01780c040c0c03c4540b140e0b9620545e0079117411084070803160b9425405a4510f00e400074200300b0002024249401c2d0000c4c0041d00141c500010041800c182810441c01910301c2221940940f10900c1c080b50490903003201c40c070303042c46400581d07000622540300c0035000420621981455041c4091a01a0082903013103c00c0d540c2c4e00c903e030b10070010b03000d0540c0e8009180300321040c100080360100d60340721b007100755040a4005e12a1400404009846201c5054a800c9107150303501c918455075607003001c01103003920030f0720400f03150709107450701030034000c3d12040240 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 472627014 1250 472625764 472625773
    0x110c0106083706060321030e0c0a0509090c0d08130602010c09051e040c090602060c03070f080c0c030a0302120a141306020f0a0c0218070e0618090106031d 68
    0x4519855150ba28041104001110400c0c20041e1030301e80000d102540c0014051181c03901ca000340304030102000c040d000500d03102403100c1100e0101041e119843c001f962540402c40070b10078451814130b45180c66004400c1d90468400b00c01c01800149400ba81013421141d04200044006084080980d01801000c0b00e000a11920010120190883d84940a402d0188031b0100880481410b401d4036107084200240c4208074a031a010f1008100c550b40c0e0149402510a0401095414840c0c40c1103c1c07284480d5035801040e468849422910240c010300719600c0c01005002041c10603500388000e11a64100d40c50040c2c0d5103050b8422048903501c0209060b100f10b141210110881c98003001c0c040c0d11600c21840e1210041c80792030660f0090040c1516480c032207001140d0003104941000403503855034001c941a00c02d0384041700005c40c5c01d400846042002907420400884142040e0000d801c8424031480c2c5c0c840d543c02005c000c0360080c0e1090f44900d002a89441c000320b0506010794501d40c0e240361902c0a030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 472628264 1250 472627014 472627063
    0x1404090c260d05161505010303030203010503010b09040b0c03450303091203130f0c05150f07170c0303070306061805030a0f0303020f0309010911011b031101110c010608 74
    0x3820500130044290146000380c04501d003081654660905c0d05501584100b03d55616418001c00a41090003143e01039860890401d40510300030040c02d2140b90b024210300041d99070124507460307982026180b24100354241d079a020900200c4a6404003040c40802107419038070100d032210102040480c0700030b901d900100148075010501058004a504403441003e6482e00c070a01140707606241070717501400c04415210382c1010041180d2031241190340456844141100d0004451950301ca9460101030701f0300c0030801000043c46525807840d00000d014400341c14421140105400e41d4030031a20300c0d0000c2d95403241400402c1c2c101c00302034001c01004e21440e80060074800800c1d0780b030301d080102910506441030708804142c406c0d011600481040e506603916402c1c0600142c0c007900030700804031218101e100c1541900e5110b94980200d18400c2e1144021101950300c00b40c4010341081c0c40e1140c59503d90340c3c65403100001000038402e580b02d03c00002030320b600d044022800c203c04c00b40d400c020041100300c0c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 472629514 1250 472628264 472628267
    0x90c0302030a050f01050717071805030a0812150d150207060908120c04050105180406031407032006070f0f06062907080901110a12080a0f0b0a1404090c260d 69
    0x540e40c1c0000c1d0390a01c0348ac4c000c140d039022030f46912590300480d814804d05000208000f00b502c090144a200d500c0c8074810740d200c00d001054445801424140c102400c0c607070b4007001c5407041140c4004520404030040c50080d1546404044c0d1b80f2400c42590340302c0c00040c200c0600e621441e4200e50081e03c1c449428102820b11000916511541e07000340c402d607085035107080e000d6a5660010000311361261001c04104080034030070703032140410b200a9070001052130060280c0850b070340031010314a07c000c040d686070501e0b80d9500e80c18804145019a00c100d0010903d00c0012040e21440019001c0f85840d40b24129840c01907007550110f900480564030b03414004207000070407101c240c0350300400c24284124039501d00360300c071440d0540110010301070411000c01c488200d50007211081c0114101c01c018407801c1b2601c0880c4064480082e41e480d0000c1140c4d200b006003a01c000c0540ca0349003001040810f02d14074603114040c4407005500a025281e1850b0a600529001d90050030810031290380940881510441d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 472630764 1250 472629514 472629557
    0x3160302031002090102120a261e091510180e0721050109060f0b03010e0a020f060417030910021501030f030c060203070305011802090901030204090c0302030a050f010507 75
    0x4008101d25000b2130307034020f076a0003400142c40904a00342000e40703548080c480146044802c460715a04210400303c3e0a0f807082c0c64285c5035103d159407569480f02070040500c2c01d224040d004080002500507010f030f01a030101040031090040c0110041c00007001d0070040b0060411820030880d918240c80d0420740c000c04140482d000f4110355200d0f08900400c04c4105d2525400c2141d10002840ca501c0c4c031401d8010442c00d80e2010140c500c00c0031041080d1010582410b080718240b500c02c0480d540300400c2e0100601d0b10400720005080d0107009075081907956801840805e00d0b400c80341c01e00750004210102c0074180301022410707000e00b0780300610543e040d4010440032000180409001c1d500d1951800044c580601880a07000c1d030300140455403480d1400009000300310a0103980d03100d0070230700d00013003a042c81c80c000e4861010008111010a034a5135007000000d10f01a102101c84049545000015940c140307c00d5035100d0140b03015281c09018010142d0031108010490003d10000e80e2845000b0003e8a8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 472632014 1250 472630764 472630783
    0xb071a0703230406140705190e010c06150803040f0503010b040b1005181002150105090106050d150801140a14150d05010b031204231c030c060203150316030203 70
    0x1a0190680c3c9803424120301410360071540c100181081c00500c00080e42c020024400b03c20002002d0f0040c0d00f01900845e444500e050ba681c0c0021008800c80c0003080c616840307020f1440502d802c0b001c00c1d079a912022411a0030950142c5425000500204010f090a000f00881e00e80c007218100119064003000585002006040204100b0301044192060381e2855581c180c00170020048074004000c03000080d07585c041c801d0000442c4810000000e200e0810300c000c181a58040c0d1222810050f118190400510701f40001d0401c02c0c10006001580710070a1050031000020400842e0051a100c201c07681943c06416484581c80d0b001d0003082101d0040b40040f03d14020212011a60401c50b410082d014044882c4c00907414019000c008010310480c1d001442143e4565440040714141001c0d81062014a00c82003608110400402000c0f0341c40844910841442030520a20502c0140c4507a001c80c0c0080300c00100312140383c603d400700c41c5010401d10701489403650340754110506650101c1c0d01c1d8451007 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 472633264 1250 472632014 472632071
    0x30f0203060d081305060d0c11010504050c040905030d050103111e010507300509190302090c0c031b0109020f04050402030a030e0607051b0910030b041205040b071a0703 74
    0x10889800075044c04564030010a402001181c44078440f41012008003280406400402c5030062418500d000c1030003028420350308480a005203a01801c10320010f000d210400321001d0008008840b400c810b40e10a5a0107540906120a40d100b01c4405000c108000171200600780441c05007070f000160390200888548603807210440f4a031101c0018417140b5008034001140940b004d401944480c1544600a812006411038451500082d02003d654460509000c0a50040341107000030b4840380455000b0242c081d68441101d180400c5400c0e12030316502c902c03401c800240d444450402c20b5181c94800030440c000c00303c40422580c201540020340c1c0f0b041c5140e004043c4030f012102003003d56102d40c00d0b030f0345080c0c100040e90f42c414117202410342e1200c0031045180c8640c06260100b0100e40c040b80c0c100081d02e0348a400c1c02500d44603910707514824a211180801003001c10400424492114005410124810b01410890040803e81e0740701c40c0e40010403950800d40780c60458203e0030f42410742c400130000003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 472634514 1250 472633264 472633267
    0x901081b040902060a0f1404030215280f0e0a0e07030b120f07090f0905060f0a020d0606081608061e030c030303190b0a06080a2307020d030f0203060d08 67
    0x40d4000700d0090903080030041d50006001c1030074140550080804181210560303203200c210030f480305c6090f005010301c0c000a90040c0e501d210614a402d035002c01401c80101040e01864400180300791000f016080f00c0d40d240001d20707611541c0782000c0d00050318a010714821212080000d00342089d15800610082280c002c0648800301075000d921000e1001d07100e4102030043e00ca819550011890b40ca40315485424801d80c5040160521500702c2d226000701030368408090038868032004d44007408060b01031300c0c0010a65080140183c1c801c074070310400c001808982c80745d1030580b809a0009041030000714842084c03017500d20420510756500704100d0719094500c241c49500240b41d5000c43e20b48109441c80903014032002003400307000419900000064000f80c0424031000e0448810302076142c1c01c0d44a03c4010680c1d11001c544903100a0300505942003135141a065040d503120b0341e4070348050003680d072100540c000c00c41e000c4000343e00d40955081c0c1c013504c290940c5142024070105071500019400904510380 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 472635764 1250 472634514 472634563
    0x6100e010e031b0118060806190509070c030806010f14130306020d0921020c121014073507050d050408040f061803060b0a0b0c0f0705090108 62
    0x50a5200c00c80d0006012128204603440740c41a42c08900c00200d804554a0700707602c03000c824143c5161061b0340c0c5035601c000050f16458140885154901f030800c10030700c032009000c5040e450f014644e0b841381e5426900d5007055010ba040207846400094106d9041054481401444540004141c0044240c2c0c000035561182d1803403412650b9102d9800003403149000090070031006186400c07442d01e140c056240480303440380c40c502031410f0b0407140a0700b201580101e0600f00380c502c0c2044030342c04902075080a6a002008881c1e103041150f90300c020440000c180403051085071684000741d00c040503c0302090315003002c088140141014001c0b101450312076440340000342c7d070328850001d6840c409030420080c001070130540303400c2c2c1d036a404c2401800310740704010030002486841500003001200190343d11100450958891502600a0008580c1c1089040d000010401d1141c00100303440406800605019541c5d0916107081141319032106100781800d0380180540e07600810740212203142006000340303424 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 472637014 1250 472635764 472635767
    0x10908030703080442090c140312070b061012090c030c0906030519080702150703080703051512210c190b1504060b0307050304050d020105010b09010c06020702061b100506100e01 78
    0x401c0606c000c0c880c0001407400640c107210b001000000c410b04030b0030b4440b10004c04003e25801d004092001d000000b40e01c000c0b800d2420f03c406034048800e0107140015591504030144001d46600c2a8120703070070000302d0b00800900c80b1022600d4050100120b083c407149103541c4801da80c403850742501132144401c0b0142201008990f204541c3d401d503024088150311800c00c2088070b41c070b41007038000b0390219035100d0001c0e184c544280306851107a1900300e411500c1d41944c8040c00b480a8080340c00308418400c490450b140048140b0b50700781e03e51700c1e00d824299180108000300b82050400155640e40c0413920f01044005455540f025511440c4000d034130201404820009016005940c8556001d41d000402d016099070b202c0c0c02140310713501a43c2100c8a12410940403402c0300d03024811542c0e084010300012440d07600c00d200345802c4034002e013005804c08a6940001d5156485900441a0410400c2882030141010301c242c402030980c0300d00400281c6400e00104908070245072401d82008441c180142c031030ba = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 472638264 1250 472637014 472637021
    0xb100501020c030a062a0503010801050609060d121205091b0d17030c0d090609020907020c010516050c0a14130207020a0e04020d0f110406080304180b010908030703080442 75
    0x208801010421580e06d00100500640d1007030040c2c000310350904000800a05108030814001c3c600500603119031186602c6040499140d42d9409041102940d00c40401002d103010341c1e40900c850b41c0207800349100c800304d00c9961101749a00c80340240800d20341d0b0400300c1c0d1005844030600e40c2186c1707031030b0740da68448001c02d4180c421034103400300407490200040c0c1403014a5000c4048230b4425101c1410a03101c0300d00590360b44c0d01416616000410820607444c20a6514444400300e921540c00c556070351340c01c01c0014410b481141c121603260710f0754004c9a00c0c41d03d0076a4650b48007103001c00085181c443d403500807654541c00360003201120205480410215145c4a030305c2c2402070303000a0014100d0842c0d1030040216600511030b07130300c681c3c1450340c0490341d0780001c000c6030122441341b01801c299282c1018000d02510801405905101140d1400154003a0500013002444e100790346082e12403038540390208001c90200c415000112017074000070b42d080c0100b08c1ca0304401e9104200c02d41c60364072551030b0340043e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 472639514 1250 472638264 472638311
    0xe03030d0c03091106030f15030c041d070b3603061801061a070b1e0f0702100606020c0d06022122021003110d02070b100501020c030a06 60
    0xc003031030600c820700d001ea8150301c010703081d51143c4002c400c035055510800c0100c0c00141c91800b004020700d80800d80d0b1510020094031588005025580c0c80e0010f1000141204c040d000000c58a030103020040040c01404e00c074900c0a0101103200a050121604100200e06801180d0308400c01741c0f03100c0c4c5109051507440090318550000c085424a2a280208000c03400202c40c000031250700703103800481d081080e030300030341d1050000b0203200b0b0502409032250001b89002405085a015001d0b00c00c11741c03461a603903070b2840350308001d00c008080c1c1800c40c0001d160400c3c1121704a4885e00e0403005110103a0b01141010403418201d4580c501c044003420600c00274401d050400c18038440c05004100090b994000c6140710b640500059440c40c441c0032840703120400d415000940c40031141e0b1014004900079401030340f5442190100301d0601050303071202d40480c1e10500d01912002d0808040080403a450140742c800b40c45d0030300c05014000501000700c0d65540f88034400030b01198a5450f07402d41034180c0f0406c40c85 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 472640764 1250 472639514 472639537
    0x103030f0c1b0915051210180c121a0c03040602070c1e060e0d0314130302180103020f030d0807050f09100509090121030f020f010c0201060503100510060e0303 70
    0x503031070f90307081d100d8014442e50100e0b078940c0902c0c4100148914005010810216400015003006041c0c031001800400d00f02508501d40c6180b012400045085000e000000c0e110340c54007010380d0130346400c003401d1102104210120264403007042240010207c01501c1c6c0180c0e110b800540c5944280c5404c108000350fa4102d0b40313842a030304044074021800d0348804d0040300c040e034982e4100604014140720f100c2901900190200794211324000000c48104005c0000200c820300d0b881e5915180d0740000d9070010340403202c4c44800f603000018011362510350040c40d4012001c81c0100b03a80e0044800140400a0040c805402d1040c00b0500001e1491004212441c0c40c40c01044510000019000940290080e141d4a07005200c20400440c1300c000c150301c0303084010034020b010924800d40780d50882e03020a80e401e8003401c5004840004019240c00d0041d00c45060300e0317400104009040c03000341890040c0107035440c60628281410301485c0d50480030000305640d01c0d8a0411915a010804645140304408941f074 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 472642014 1250 472640764 472640813
    0x1021903030b090421031802331b0a03020604020f01091e08010c0c0804090504060204091a040f020a0c0b09070308030106030b1c030819060807060507060b010302030103030f0c 77
    0x10802182400301c001030342c840c03009544c01d20280c0124101c80c02c0b4101d0b59280c01f45040e1040161a050ba404070228840c2500d0340741c410b55111000c495046598030740c080030440450b4140c045520039407030b040402d14603002440403044030784000390f0310140680083c0c000e091000490203582d103e580088081c00d91210030b903079684815400e4403040e10851152009551074961007030b44a80c45045005081508203010a0a00b404e00034114010200a40b044407410f90801000500e01c44034080ca00c2d14040e44a50007100300c080d44280400e4504003000e8910f02d502c1040020003003a040101a600280c02a0035004c1b03981c0d428604914082d11034001420a0001000008120383d040d045410704040c2500c20184210b0041041c08401440800c028007040c3c10720002409400000742d03071310307083c140c0790700205596551354041800c0c0b1981e90454000100300040081c00d0285600070106030002c00e00c5e00714038540c50340d1030051a20008902c0001002a01c80800c02400f449000b4451456440400c00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 472643264 1250 472642014 472642021
    0xd05090102130b070c17030a030c2001090506010b03070c08070206070602070b091605010c12180602010e12072d0c0e07110601240210060608040c080c01021903030b09 73
    0x881c0310742052108484175000180c000c50000c0c4007514501d04074031010010b504254800c10140d006d09100c000d103200f00030342100c0a4581500504c01c801524044000000d610509824118146241600700b00d050705004c1080c4a00103900004ca10f21407a04072510740c2e111940c0d840050190310524101034078443c000305080040c0a50500e0035405010110220703417020203040e207800c1c4401c1c1c440c8a468045a80115201c0105014004d0181060403903e44001d0f4800d1b04008080e92884541210005039521510184141c0c410061380050304034120010b07041c00b215640d03240f1500d000e146400e502d000001510710500e02c40d850070440c0304c2e40c0035004c4080540c948421602d01d18003140c1e00d20000d082900c21444202010030440c1c10f8030180d000d10007910f540d0021082ca41c8031010402d42c00c500c1800b190484400301880b82c14040d248990700e800c040d00b4941840c0641950b6500440c406420030120b280c0d01c0e07a00090b03285c81d4004185562180d0045c1c03410705500421560f01416040260348041 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 472644514 1250 472643264 472643279
    0x20703170414070e011a03070315080304081612020f061c020a121b0806190e01050405061215070c020d03090e0703020702010905060705121c0b1002030d0509010213 72
    0x603030090080181c201c0704025134440303843c2d45400d02031280c0001c0c0000c1340741c8400720082250046034801182c2c06d010030194031246200041c800c02d80c1c4034554981011800b4000c0382070a0261b424085068101c140c03040c4d080461030040c0704c5031040000c0c403503c0101000901600c401d002e03240350032145e204d4460303100d029480740400780d408051461700050500b03007401000007451040c40c00458411003491100004c0781000c0e100d075903000d030800e0360100b1110000c400400300030700e500000e88026010b440039545428180010340d20050489c0784103840e040380410f59194009809140302d5042c845a501603100c00c1000d807000381300c46901940003118107504505050b009400a4100d41c0d501d006500c9039070b81c3c010700310200c0c011000000c1c000342141a00b04020314110010f004420700407800e59240b080c010038200e6603548042d002c5c080110a1000c15220700090b44641c2d0f00d54141a5081c0c0c030300c1c8000345d0000352a8440d801000c560540c0d50004607640200944c10780b103804211070403924041d80c0301c2c0503 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 472645764 1250 472644514 472644533
    0x30915090609270f0e0321090d0503071223040c06050306100309060e030703170108060f0c031302030f0a0b0a02040b04032a0f170105190207031704 65
    0x203128045001500700151050b0b08600340b43e00400510301c181020080e2124140182c500c0440d9501055111001904000f5091000306403415800b403908001041401d90b15003010401003c0c1200d83d0042070101403684e030070600f200d5000c08a4640086180a190301040080005e9201d511500201e410011401600001d0942c0030301d0103499221103041d0f1f42c0d14221090700c011a036442d04503503a4240e1401c4580a41c201c491131a21a04000ca040b5046034040fa1031074010f6030080c2e00003443c21030344000300e04c07000d00c03000d0240041d032002c1c0481c1c0c5056046c80001050150180c0700c0c03a5400400a40c078140c13009580712541358000c054441c030024502a107641d460304c002054503030894a40c0483c0503200d0510031503040321140340d515030400d4990b485032125244060240311460010f410140d0142d1166242c0401401d50f8540c1c4034100d42c02c1440301c1c082c07003803c5100303104568588420300c54502c0301004520005014101e016036600b02c0351404903020700700c94500c28161023071201400300300b1483d404c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 472647014 1250 472645764 472645769
    0x2009130611130e0604060b1903110f070c21121e020f0709020702090103060b010507060903120c020109052e0f0506040b06030c030406150806092d03041203091509 71
    0x701803e01ca510303844104022a070913031107869010b6400304802c0003c4149000d40040c1c240d00c0c0d040004007941c00718281d00346980b14000e100b40400c4000f604904108900c031000014200028034945501260410150105440c03030000c0c0021101c40c40a40c41c0d0782c401e181c940c88951464100c122100e0038414040c0d51a09280b00c1468503001d5460045407000c00d51080e01c80c040c3d0010b00043c0964a980c035030000415480b4034090400108002e402c000c0b440c4e500840130003920960325001507040781030682d0b049030364002203d0116410700c84440085540042c410f0f00700c80c40c0402000600003c400f0100801d0740030000f03400e045040c4603d0690b5054103074091442080c05031820312401c618482001502d2000311824003c1000610120f800f00d400c962040007041c074054842c6805903110003056103030000c2224044110780c0404032030000c600249030120840e15009032410b14003129040c2c5039841e406280504035041d04d0b41d10b070880505201e01c00c1c0304010003002d4540c21a1903000f00300108001e20790f0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 472648264 1250 472647014 472647029
    0x1020f070b0324060d0b210604060c0e0a060906080105090126011d0a12081006080c0f0301080c010e0306060d0b0c090414101a090f0307031e200913061113 68
    0x383d4050302070700c01c4a440307c0605070701c000151155555541d030300c200404881c05440100240b0304440c110a07119440309401034021030300e440a2003403030308200400000d0705821a6008491400c01002b00f480000300f1070200d0070f183c1010080600034540e0b618010507203420170800f00402c111104400b460041024810030780241c21400f01c070881c15001340c94a90041c0c0c0c01d48050307564100c0401000d0701c948100ca82000c0c240c024546403815103421454160001e030000045900002d004883c01d41c1c006018400010094018109519185000500d100c1c114030028103407200400c0049c2c0194010011540c0c0340100910400140200000c00c090301b03001220250342da105050004184600c400792140c1d441c201081002d4505401d032000d0002040402404581501c6600d10102c0024500710240c13404503244000315883e6411400c184550500d001203070f0074003288054031000798bd160b5160b13041d44503001e07000380840c0d1070841c90118010440455482e24482c1c0200b00030070384040c0300c454041151482c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 472649514 1250 472648264 472648279
    0x306042406141305090709090501060503060102060a09030806010c030c06090c03150e070605070812010602160b0c0607030e0a06050a0f0c0215041b0807030c0501020f070b0324060d0b 80
    0x240b580040c8a4032070001040c0024482c0038081006141130f000c12a4001241e00e0300c40040c90741d9108100039a80d00380c03c404086031002c820405117590420055074081c01d140420f019010950310050400e10300030f48a00d04102c401c5644c1002e040c0501c5107140c855600200410100c02c0c1810708004100150000716009007100d601055103403c54000e104c501e11291000e420b09a281240503101030f4400c0740100c4510509215801c0c80382d04100c800b90017007030b81c0c0c0c000c0c208003c0c141c4000609804036404c2100510300074002c000308200c0008016501025508000507a14600f035455841e0254503480140414182802c0064221440d0000c035441017031a003042c41400c10b01d20b021390b110b1003001c04004040c0e642c10000340200b80880c54103075540704c2c940314806882d0384458216080c1080358005840c000c210100411155034100100c421462764403019110030341c2006a00079480c031018040d410030201c0e1406615403001c41429000d001503004000310703035030550046144040c04003044e62600c038612 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 472650764 1250 472649514 472649537
    0x20301150b040506072f010e03010903080a0c0314040f020f0901060c0b0402010e04060303020c030618030d0218040204062118020d06110705060f090106030f02060306042406 76
    0x10215618030540d0410081181858148400d00c80da41c2c00c0880d05489481c21a44d4820b107583d0300d014a02014014130143c9690004001e002400e80406000441e00980c901120341c80070a030320100054200400318400314400400440440182011481c1c07520003680d4401407008004541071110340713013882500c0f65400031604404102640c0320034807a00c00441c00e11549080055a002d082986c0503105041c62490400040e000c50304a40c8550002c5000d42d0015500328100d203804c00149510030914103880c602401c068141d02e40343c2c0246583d4043d4550003041c0c111000d416440350740c0406c1c4000c0c100310b480320354861700105607a41140e41100c5030704c20602513801c141c0b07050080c1c0040002c3d44020401e05d062030717400e00c55401d14204054070032a5944034869500d9034103500030141203002300010881ca0910a540c420210000b61030040b8030383c90440d04100288200c40d84500f51a012601c403a145e5880c08082000740068546414410f9069202228a03900d07034007210090b11060b90b1040b12000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 472652014 1250 472650764 472650791
    0xb04021908070306150201090512130e091507080402120f0d23070506071b0b06010f120501030305040f0e0606040b0903120a0807080717010b0f1b030403020301 70
    0x1061403044000314419100001460340660781040d00641e207483c000900035901c00e81c101188843c407503454010b0b51991294028040d0401004070607c00800750b003440e00000710016095a0400d01c03c030081d2a942e440003600c48a000e0110500070240480300e000d25142500006000e410f0031107049108036107400c0b1520b04000300148909204c890a40107020f080382d42031007070781d1540c507621141840705220038010130742000d4040500b2030079208000034102410003072000303404890803015210780c0c00c02c071a044501054040d0503903904a4002c0c04c0458074100c8206007160312a4246105022440c02c0200000400d0b034482e004000701d0b110304c8032004116444a03020418480240d400a520140031b02040c84026050801410b050300d0040407103947c1350155141b4403240d0840c01d00c900200d91101d04014000d60001003480c0d2000035403910340128292030251404401d018042c2c0c452103000410400c5107070360360001b10360a0300158056100c0005401456a03074913445800124003e50030444407910b0302 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 472653264 1250 472652014 472652017
    0x215040f03260105060904060b0409090c231302040312091a0c1b0612011215050c0d090c080f070317090303041a0d0203090606010e0906030d0c020303040302150a030b0402 75
    0x31018419184110307440c1c6010401c85400080015510503034481d230008520300c501c1c00030300041407240804100708a82d420003026580720707540300d42100185030032112004000f604040c05541c1d800c50312036102c0600c3c13810220090140381c00080c0b4911049008ca20340a8104032600112070700c00c1081c5400005001011109004600c10013140380d01034124031890102c201c0501130140c101500482c100000c01c0d00982e10b601d000c0e07100b1582001001c07507180c14480c914240e40003194855000340402d051901c00000c041c4981500c0c40c0b04166140480401c01c48134003c428014000e5004441c0c95031a141040e80d01c9801500c400c5030465002448802c02010300400e031450b1000c014051403d042c43d190700380c11a014024002080000b00708401900f05440c1d2011310300804c01c0324010b1845240c0b0000260143c0004000740d44100800d00401c512560001407480e200c44562905420710748079032011914501480c0c000039481640103103000c200e500c1c14405411030310300940d014003503480404140002c9 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 472654514 1250 472653264 472653317
    0x180604050919110d05011b030b01050301060c031b0b0108030c10110403151e0603050d020c0f040c03020f07050609120405030a080c0a0f080319140105090402010215040f03 75
    0xc403403036106540040b450f940e59085000308040d1403200380582c1035440c40d0031204810309944559074030a030300500c0c0c1c130747c14460105692000e0030294519410000041e00000c0080c4008080050209541000e052111501500d250780b000c0b140d811542c58445e60b030746a8100a00140062082e091140d1204885e8083e01c0c0080e010520454681400c64442101d0403200c1070303074061215180c0c01840c4440610114407042d006450f00002415419450440d081000d81d0900e00215441080c8440403a9118002144120000c45000070341905500041d006402109409106100d0100d078034000d204010590a101c1c031942402e481d0780a5000c60302c0e03009406076004140e05a41b140b40030710002500d02c1c0040030420521030403960001c80960310210240c041e5102101c44000c044140461955500000c0500e01010807050200100101e84001c1d10681445020312500c100d801040c191b900a101330301c00300a0b4401d15101510306810000704411742028220005500202050194000d10211128 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 472655764 1250 472654514 472654543
    0xc090f03070302130203090a0f1203050f06090a180c0f030606060815060a300606020304050d060209041808040503072c0402030f070338241806040509 66
    0x541c0f035013008044002e40006000310402d102d07001e144408100000f1410588134442c0750b49400007942800d009023a41c0d40503140c0344140500d007051000e03d60b1083c455035800043d20200044124524a00c085051a02000a000d41401c1d40001c6090811100640162030041d4070500c4003039600e28085650b06030460300040484881d50001c111f0b45400030040481911901c1c00704444901c001070007621054581129a01000f1400a20074030000c500030b180081880f40051810540340001241d01c4240c0520b0080000743d0015449419030b48560001c16207260040b0034140340d02c0985841e0b4a2540300b409894400e01c20100c0014001943c203905c00c1ca00103228114400f000015003e02da41c1d07141c040d03c200d038940286440c5003600c42d03041060a00850003290031441164401010703040031110381c105001d09c3c03441c828100c0703e4407000f440c8982d00030360810b80c001640d8030001c0c803000c07100140b070b0303c4a40e010032042204c4070314840d000d181a01526046804101da034507040506a40c1c0e10002c1e00c201c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 472657014 1250 472655764 472655779
    0x61005041203050d0603080d0e0d08060f0d1b29090109050904050703120e040e030906070b0c04050415031b210f020a0f1d0907050906010e090c090f03070302 69
    0x140001c1c403c1c0042c14403030400d03c5001c01d00395220754420a45402c5800d500d6206566a1401c0e0880c0000300045c0d00c004a2030b04005079242001004504610218407085000c2c0080e19502d0082041c9541d0712164089014101e2040740e884540c801e6014080e80c04480400d40984000c240c1501088129501c03210141c4036000e00d00d1411041c007060050041003950303180114400040403901c03c510034800e90103260b40b00c840c1240c0403810841150034010620f0070b0340c1d1090000343c84a0f00e500d4112400c0705e41000b510300f0310740c0d14601c0c0025140b0130303500043d800c103007011000d00b07014040000d5901030360b2052241c489810130480807046044040c0c0b2915481230840c3c0c6a044000349c0c54021034003068091450f40d841069182c02003035000781790341d2015200c070507034210401002800301500300c085401140403801d1402c1c409021596803103c0e01605100d400342c07101040550f8002c0b40610b20280d0003901e1103141d0301d08801e48201700d0304400f006074010b0480ba00304111910300845c4070341c1075950060025 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 472658264 1250 472657014 472657049
    0x91215091507080a090f0c03060204050406080a0b0a02070c35010504020d03081306050112030f050a020705010e0d14010605010807020c0303120705040f0b03040203100204051f050d1406100504 84
    0x41c02400b15400c090b540c42c20b00c5801217020540c498000c7c80554041c900141e5254a0001840b007102e107154010041c54004522040005a000311520f03001a4100c5026031a0100740c101454601d02a91040c442114450340c000300c03c548000f121000052011000311f41060000710890070b80c1c204540080d88043c103004c800d80000d0107a65080e030070541c4800010b6601402c0d640b0a41200da0a07007090250040c03900d041000c060f8085441d1150b036110b85041d5040c8140088003a556003000d0080605200300441400c40907110503070360100e0250041c6a07100003031407208016000305118051640011090800550b9050000502e011804d00c06002103140054502e06031903151800f4000c1d204200003044000340c1007188204039009001001d600a6403404e02c0c2c030415260a8a41011403041801408100400c1d65403100081088441e00d1401102c03840d150310403034a40c8511a9058092440d103202c001070a0b0740c0d1a0751034850b070415212041a000000030a5829008900c11050742c0740f0340c207201 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 472659514 1250 472658264 472658281
    0xa140402010c060e010c020f060106140711040f050c09040e07061706030f0322060320091504150e040e1e01020d39090501030209121509150708 63
    0x412040b10700a20001405442e1103000b5401e484640202c58010ba00c100501302a10009002050052200d4100414160301c0000c558042c3d00403004041c1c44854400540c0c4425109c503085607018a403210800c001c185411082101150040c25031030b40143e107031084409034940001119016204242c6460100c0450741d260036010701d50003811190103004800d0f055445010800c05402280e21a11904a540c000040984110091507100030300301030900f440e008408a00620708110803840e401c100c1c0da1a144800424116030440416983e003c02c0060006401c001028804466400070b64840c411842c25004100031359218200144503500002c0410059212141d00b00303060300c940d88000350501c118100310300b007152503410b600901ca10340c1c003100311841c0c01908919044904003c0f60f0742016074a600005140040b603014031810b0503170000d46211165580010004803041c0c0700c0840320140706207101d159071400156020407440c443e1040000000c0440b03001284142140d507902d080307a80c0c45100717 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 472660764 1250 472659514 472659527
    0x141c08060f030c0909011413080702060a0201090c08010f06060302122206060801051503011a01080703110c0c090906090a080904020f0c160506070507092d0e060a14040201 75
    0x18081e4188078030300c5000f10f103464851140e8402c01307000000154010302c0c005c4690100740e00070102c0048001c20f807495000035101b13000362081260140c584644507030400c241603005210b09407015020380e04031400040c00c00c0c0c05401c00301d20070b004440c0600c500703a82c60b4025010b901400712040b9034a6803010003d4081001c400c0d005000c03520510f020815030078152190302c100c1d82240c011200b1651918200026003024840000c0351080580c000c01c000550380c400c3e26284400c1780002810401d0020128203803600c0303500125449402c0509a0750740701100d4080d560341d0000f9160450040481c2000030301d015402007012446821480003038030781403ea5a40d40c100c2c6a0040d101103501641c00c1c011118544108030141600b021403030001c3c0703212080c0fa10036078808640d5a004901c0f1711010001e1100203074000c103180c070454003102e4001c680f55140181004c04d001400340c4294400c0380b01c0805c03080591454004200d4041c0c8181030b00c3d156102c40149405840c0718008000e41c1c2c9158002041c01548101e2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 472661870 1106 472660764 472660789
    0xd0602091f08010e0c0a300204030c060c12030e100603051f151802090405070c0c0807050f01050a02010608011a0102070e0108060415020405040207141c0806 69
    0x204c000307007144141b1314000b0810441a4000560392007040065268020f41c00b100428014100000802900148011307110044040000034890340500800e0700340c550040c07202045002003e8055018000e4040e145406200c0c00144070440c02440c81100007640c40755000c0c1995016003010042a842d00c15110600f0a16048004070100c80360704405003211416162811740001d6050644028016003140c6070304607080504000c0c4c1c4591241003c200c00d03200c4d11581aa6980310301805a584c1c501c0e00999400c900d0b208000807440d8007031006800b4007100741c40081a11511a8170305420f440822272a01030f0348c0c2120003440115a0180b0981c0f0180c84842c0313100085600d0300d11019540e200250014110490a0740b4201034000341e81c045034090301d0060400c0d552042580303090003040d0314051003001c45008220039681e5210341708280e8003200c81d0554403288148c4501d809c01810080c0380 = true := by decide +kernel

theorem cover : BRFrame.Cov 472482014 472661870 := by
  have h0 := BRFrame.cov_init 472482014
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472482014 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 472482014 ≤ n) (h2 : n < 472661870) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
