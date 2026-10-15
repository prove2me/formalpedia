-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3870
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:55:32.360752+00:00
-- url     : https://prove2.me/submissions/b14e429c-5f2e-40c0-8651-e11d5ea2b57d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 695863309 ≤ n < 696043165 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 695864559 1250 695863309 695863327
    0x210090b03180304080703080c1902030715020c0301090c0501030e1203060603060d06020313060c0e1315031b0f2408180102160209160509040518060c0d050606 70
    0x2409594200e180c00041414008240142d02e02c1c40c07189402140680c421560000100007241006045401d500e03001d0b40c0700448901191400c41c0000c0c1402545030304544801d000c0c0522034800c0c081d681d182ea104a44800801c00d010030700b15014102c0c29911015444002d01c490350705406019004810702c002001c010020300b8100c3c80c2800b010b00194480d00000011400f0359481030901c50f6056040300c000c42d984d042102d41404604001042119480d0a20100c08071060184082c144601006041407840c80c82d20460a401000304401d54400d0400500700400400c0c0080480e40b180c0c018241c1c0700c244a0b08040181803602400d0b800b6040d001080301e000c070b05016401c074101030401c0007818051915150540c01c42c100c8801c00b02c0b0002190310206107d00c20100c1d44080c6400355000303407001140740d101d806540c0c0342560b500071900b0101d401040071851504069100075031046561090f03940900ea189102400d0800c152115240110082058408607943d445001d800800403240c480c82d188020f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 695865809 1250 695864559 695864579
    0xd0b280819060b0303040f12170a0c02210d0c0c05031903030c02030706140703050115020c09090c0307030305031504060e0105040902040906020a020106061e0e120703150603021009 79
    0x380c0209640d4983e084004030f5101001564007900d40310405040c0180c440448141081203070506642141040850100300c030284002c072020744003c0d41e905050b94030160240110070101b000c0f9450036411400728000255001e0168804100407503a80c1e0050680909140c0c9502c50a50041d5100750007410009070700040d454020796070250301d8100030804e01c0e40240c0580c118010110050309003801e100b0b4150351542186941c038031070320306620100560390700e4510701c0d1400c1180f9220b110242e441111069440c1c507101d0401c50b4400098012a0030b0880c1c1d00000c03a00f815040d5004401203000802840010040e4007002092034400b80d13020000c1c28035282070300c6c05c945410311502e070045a403411014155240c0f030f0090707030106422407010340da0380d20940c60003030080c03165100d00c0c000142c07040300000c0c00c1100201f8000c0040956601c207000c14468008110101d0460182000c00b8444c42500000080c43c1d030404801c3c00a1130840001c52500c1d500601103041c08610050041040e1604140680411 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 695867059 1250 695865809 695865853
    0x10080613030e0402070606090c180909050a051002032a071401180b011d1603051e040302071503020a080106030509010b0a080604020a1a0a050d0b2808 66
    0x1000c10340d412840e03541425100420100c04554019000207000001d210b81a00100304466441c081009001da03000ca04540140351030300d8803086000b0300d42042060240903003192600501410030b65102d0764103070b51501e14009d0a8a200300f81d294010042140b0140e0b010803a1500341c00031b02248000c1840c01d02409454426420024107041003e0300500c04d50900350700920303640310b1010048807900d0700703410540301c4000b00348507800a00107191076041d07007003413090be41d6401071910003100880340002c5c1c0400d90281800070290001b0010040461001085070014680a11701980242c8030550809040b00300380f070034117251181031600400079150242e0340712004904581e464500004c2946903240b0940c09803a030f4101e8194805a00607011900102c0810b0560245108441d500760312650380542001e5a115142c80700800f04090080c158520300880082051082400c0c00082d2150500d00048840c0c02c501700d00c00c0041c1c0c240c0000c44460448104d07001c06400c541c802090034400c03a00e079244510300 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 695868309 1250 695867059 695867071
    0xe040c2309130b040303061502010603241104031505070f021e030d1109030d1803110117040305091005041a07020a030803130302070509010605030c070c0803040803090306100806 78
    0x2110500044a881035201200050b9502c140300c0c01041c1050304000300034002a000e0311b491840b449000030314680c014441c40007100d81c0014103c07800f880c619036080c410138988582094907919084100e88105060006001647c400c60007148285806082102125801401070051107640350a918041c1d400203545000c1e2101084400004028000d4035412f60041250f0406a18203100c41c010704501d031070000c0c0c004410700f9012103501480040c0100c860400440003182d2169000d035003407010411290043c440300c0c4041c149500d03000c140c07080c5014517481c02c58080d0006000410200714510707081e0320003084400ba0b8600241030504020180210920020002c0249400090894119290840104010741c5c00c40845912840e0098088000d680418030440041c055014040360314a8401c080d241030352107076514a4215505c6960000e2230f9404210181c481d140e060400044844c0c0810041c0040e00c8a0b801460300d414110302414503008010b450002203001c8201c1c14410340c000060401e80c089 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 695869559 1250 695868309 695868319
    0x40803040f11030d0903020306060901030c0e07051c020a03141b160b01140102060901110a0f11010c0f030609060e0402010e0105160f021008090c060c010b06040e040c23 74
    0x1601e1890b02c400c1c44148508981c0d01405104141d16525030010280707405c0b81c1c029800d0341c042d40d98010410901010034000202110139043d0113120416501662580c0020f0302c1c2801403800c0d8440c003d03c20b1200c44003500d00c600d190000f500c03075240c9926000b480b44030f4510350301c030740e104c0d05080c11283d028000c20352000e000c1c0d49000c9980506060485c1c03c2000603070f08486001030a584842c509070300e00f02c2041c0c000b400b41c0b1a54020503081d403814400e0300308011708480b01034200b0020b44e0301128041207043c05203040000c90485201060001c1c4a2208101c84548030503501089034040a012b0307405607404030100743d01e8400100411900308002541c440e03824a0400c051101010040e5801d010f08030b050211654090850010003101ca0060310179540200c0c3c0246c2004628803044907034401c00c0351040b41603040001106d00700d0030070304042c03ca041420400803580100c080301180103a00613a20140c0c4c0c1d102d00e141808140040011030602401c007111312490f03003c60040010408542c0303044a83c1c098 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 695870809 1250 695869559 695869583
    0x18031e0a0e040e0a0303061502030304240525031e0c03020c030c0102030a0f091208070224010f050a0806010e090a063201180908040e01120507080604080304 69
    0x89403041d6000460740800400070441e00b000c45280d03941c1c40100000450120f843c0810104942e20103099265124810f64002d514540c0c6680e203030807650304409056401001d03000300c030459040b02409414801d80b84851644a00031091054203548400c3c0790018040c9071511111114128400c08113480c1103040110210340d3b0458854220f009115500342288103000100e89184000d006400840c01200140301c2400b884000544000441c7c50141005000c0b000700f403890103100380665909a4800a9030060300c6051f03800ca15203298a01202ca80c0d51602e0340c0000040c03048042604907a00034040a80347c3c2e0207010300749800d4555503141070094840d02c01a1400103401e03a8010001c492100354009010712541085500040021640506068100c40240180c118981003155014100d030050101f8213182c90501c445980102912034058990145c104004554140758150190081140c0d10380780c0300ea50494101241088841d8004610340c0e080101400301040400741500d40081d0049051011 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 695872059 1250 695870809 695870827
    0xe0915011d150a050a0e06090a030b070201111605101a01080a0b0d1a0a1104090e01020706060303180e46020903070b03090a0b1b1218031e 61
    0x54a402c494445124002c00580250103541c45005020300e81000d032240300c4203075054810041103004000f03c041e04410350b11020070100f00c41c0ca20f2640c1181c07039400001500b03042407040c980c242d8000021021400051042d034002c000b0b041101004d008010042080f4125a50b203a608007400101c1c000f078104000a40403501c1c60042c1e0b442000301601c01001003d9a03401c0e494592445240d40244458250ba03d80018103910200d0003100825030304000070301d01c0e20381072440150081c650224010207640d400e00006001880038800d00002d94040d888014580034000041d0b1400402d0390403241d003841c2501c0511211648910603a8a02401e210034008003130300b105150640118070f00b000c6c40c4e1071412000109034214141d402060070913801d40590b10269121900a90584400c0c0e4480081c1d910184079072001c610090441c0d604503011100c03940d0f41c4804480000050780040e07004008240c1408244000e40511010050004455001960800c94852141480c0f0300c4003584403006114000f60b0280 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 695873309 1250 695872059 695872069
    0x10905040201270510020f12030c130906090c02070311060d11030f01050f0a1d0c0708040905070306090c0c030c060e0a050106090507140d0221070e0915011d 69
    0x242c0c106520030340340034540c05103042c0f14a003a42c4103250281c4a0220605a820310105501e43c094442074018000e4000440004119500007416136075050030520a00c4881c81810303c1113401001910008141c40f41400c010714120303142d4100007019503210020400000d0010500b02c44d8900d012207042da143e50303160b038080c03024028490300c0010781100001004030814414032054142e4805a03905408900303182c6c01d000c85480d6500a000c0240d0100780c14410559032090241d500803206c000c0300f4100022036880c146290880d400c140f14403038940b420041007a40c1881007130018011121705214030f10307100b40c0252000840e507101034100148501e101082c046141c1061074207030b03c020308490005580c1d0030254001c0074079014a20940d400c1001188807d0b104034814000e0295240c802403525910342c070248000e50180200840202144008045c100700b0223b003684030717651a07200c261901003482c08008101c40c00403c03a00c1c4800300c0c040501500e9901c4520303180710600c250b065041c0d036440140021 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 695874559 1250 695873309 695873327
    0x40f060c0e0901080615010216180204030204090503040303121a01030f0b1203040e0a0608070b0d09060c120f11180f0303030903070506010e04021509060d05250203030f010905040201 80
    0x260802d444000004803407400095191080c0e0084036001d50341d007111001240c03520410f026404080042c06818820302c560307540d124100610340f00e801880d103540d0f94041019aa50002c00303440340c1c3c201090030810b058202c0c2e01d45010b40080c00d1b007000801152585105103940400880d0304041d51070414544210030356000c8411b0000c010301c88180d060170080b14507038a038001d002c3e01d61a0001040403480300c1c0c41d980650010381da111009001b0807410150205503582061050314803840d100d4921a01141c540c0c41001c210504596a051401c00d2102c42074055688071030315001040c1ca0b042d40035654600c41010780f04000680500c0007002c2a100001902141c2103124140d030500000044c07150306040000108092403140054480503a61814180044d810481e0083d4000202014061281520000400101a00828040c00c0c10882110303801210b01c12100645e00c01c040708000d100c4070341c403614004400e0600344011890351034020300074560500184070751504151500702003000c40e0702a011348 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 695875809 1250 695874559 695874587
    0x1819061d060f090d02030301051c21030f0c0e0f1315080a030e010f02030706111917060a060c061d030f0d06170a1b09020a030e1203040f060c 62
    0x560700350501c040c1c0448501d100b520309401c3c0384594140355446034004000c0d28100d42c002045031800a038103001d070102c061442071045590070b40c0000c41c9130f03141128883c988402c6040b80e900080a4100e060284100c0341c4071003081051001007440401d841d42c0d0043d54213000041540c0d02e48944800003081000751801005056130090344003404100380200107100e19065002c0d650308081302103220010341e01000c18441040c011b070420420a00801c4250b004140310529008031302d440c01755000016104459400c042d01c0c00243c042030800c9140403420003c0c1d41000c0100c40c0140340c5854610050401d624403c4004c6c82e0503260140000d8024420808804070150300e0203030381e43c5000708142c0740040d61013414008420f520309407010030b143e0044110307854030103c0c150042001091544a000c41e11424aa041011411a0602203041d51035400600b07804001601c02146c2c0e8500700c19400d040641d80909031011113400d01c2084040341c481da41220722640c0000f40050080c0030040102c645410381902 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 695877059 1250 695875809 695875813
    0x40908040f031a1b0a05070f0b0916090b2211040620030f090603040c051002100506060901200a321204051509030d081819061d 56
    0x4008180480c9104004500d050402d1401042c0e8605240c0c0d103400000c030742c01303425548090119000c03090160f801006088d0107000c01d50b030b01825595a085040808071140f8600f600002c4041c0d1005192460420190205000030311a295054020400e1120342c0403000103440300721100c0c6596003400f80c0c00909030030407051880d580e96440d82c070301401149948030001e040d19904510781c03100d48804000d41c0c0e24141c200091520701a490010041b20b60000381040d6181c2240480c00966640c0c1e0012000f40d40070950041d008040401080e0021a034008009174000c050801a00e66142c0c0d00840b05000340c10801c0015080401191105140074000d4200500551420412209401500340740c1c4403404a110b0040510281c002505500c50300ba41d6205501e5120a02c41030245140c0400141030912250b51014203103201000041c3c68070500040c1c41e808901540309015034049039403041b54282304040f0041020314074034181c40d000d0700d800a40181c060ba81d1b400000000681c0000c00d0b400c43e03450142 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 695878309 1250 695877059 695877089
    0x601060c020a0e061507060e070306052413050709171c0e0d0605092401060810180b0a03051e010506042f070803071e03020408060604090804 62
    0x10000c0c208645a1500303a10514036070500069890f010500340c2d12640010b00380e40c82504d000342941906800a4070101c1d5450388844080b610715404202e0b907002140200c5001c161410103c4140b590052072405403000d141e524440e15140d81c4580840c7c00e4520310030301001a243d920542c08440c0c5020b00d401c490f401d00000d0010004034040000c1c40600c3d80c1d294600050040400c080956a46121020a03a006102070107018040b9425500007a0701405a4003500c0c404c0c48124044109000b8124254640c1c50041e80140700c0c01d90f01038441350384404030901d1820800d05001ca402c445086a4041c1c15400f03443e84418045621204a00d40056070302c0700882c1c0e2204000c4048280d070b10040c094080e259031a000c00584546020f020380518500c256900400b0340c00c02c40710030010041c003540800d25602c4100101000140c404000314400c0c02c02e039942010080c480c110090aa16440c0c0c0d41c5820540144018170a80c8030101c2c10030b0700803808a80015841ea00d600d4450b03040d000759805407503260305242d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 695879559 1250 695878309 695878319
    0x110d170402011b0809040f0e1b061312051002030702060406090501060b27010203041d092b08060f0901090c020703050d090515120415020c0106091d06040308150109080601 75
    0x400a404901412103080c800000035501c038400b181d840310107001403544858440c2720b0702c01c403a00355060030302800740a042c582085001840c520b03070701070751000c0700c1004494810009d002051200c01071501d050782c801d5246007080f000082d5200c10160002e880c030703523503180303480e04001095200b64014082c00c181d8035103034100e0300340d4840b00c588070244008080c041d0a0700d6410641c4044100d405488400f2051101000810122910b00708000c020400d688620f942c00f1004080f01c0c10400080001f0301c00d0a1207184080c20001c00d04000681850f0044004c440c01e446d10b59940e5110340c3c151050508001464010003504a2030034446070300240050155034018105164018030500a655055550a092018050401700d084c412264100346400e034034070109001862002c0c1c01003451166203c0513040c02c484417541d600b11002c590000038115030310110400070b860500306507a1040c10300d401902491030291000b9100e084020101d4480700300184025130b40e80e00464828000d0940281161159a118 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 695880809 1250 695879559 695879573
    0x1d04051302010e180a1a0409050c0a060203030106051c0b1908070b07050a0b0c070c0906030209061c12110106030f0c080a05100c0c05030a0906110d170402011b 70
    0x2031035003680020f5800600c203200e130034004184000c038980c00d18940300c241e9400c80346a00400020780880b668106420010305540c0e101d0041c1d4032454015005001440c501380c04000064a25a02c110306542080c00104a2a174011040c0c944413101c00202440d1480d203075140be401801000401a84003a0380c0d04c6500c0083d107082c4899007070301c0d5040300300d81041d0b85584806e24940110311004046e0362100740c0010009291820084d0046102026103003804c0d03481c2d8880000ca01a6080445c5c00c0360303550310070020340c03600c079a042ea00840141e542400c4005002440300c0017040e070b030f1005010000042c007400341085c07144035101d106100900007008903580f00c2c03500c489501400941501d410b4000d140105454402169910100380e019006081c2c0e0100304201e10b020b80b40c81c1a81000b40691900210007003802480244043c201c10f580d00c0000d0f074108040a8098040344810306d140758000f500030071a80d50006001c0c0d008401c1e044c1d0704002903441c0c1c40101c455500c030344c50345d8003c804941c2e80b000070400d0b0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 695882059 1250 695880809 695880841
    0x5060a060e0106020a0809100e12010504061404020d02040506210705030c030616031109040c050c060a0b0607031d04060e18010c0f0c03110607090807080106030f031d0405 75
    0x5201c540c090690fa601422607a400d41e990002d0f01d031440c200800b40c20340ca00300030310010110182c2401d0402815500000382c82c0d41240007004803594641e0f00300302c1044910700c078410081309031003d41e001a0420f40c022824001c80e00c10b0080c05a555007010400715940c0034600f81498a50f004009818102d041d40c89482e021035200e9640a4884c9941c400041c0c40c0106041c1d00c10500054150b61001401c0000c0340078021000c20703030445103400c00548c0e100341c80b2401503085404a58807107660b1020142001271920200400d070044a40c6040b0b4403041a5451034111040039805107080070b0b120f5981d580c4c1c0040c907012540a15801494401d001a50402407625288290611925183e00e04504001c240c262260310740540b00140480d01e1a032042401a1402d00ba560301910f0324142c00b0031411402450420152a0300c5c0100b10410000c0090410402c14400541241e6009002c0c2d20326540c4e410000c0204008001c00340800c485900303102c0c1c10801e903400300d2804000d00502050412104003225010 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 695883309 1250 695882059 695882069
    0x41a10080111070206120408190f0206130c090e03160c05010807030501032609041406030c030f070504110c01110901080a140103080d150e0a0c080c030601180305060a06 74
    0x10034007000700d0b0642c040740151180350344c01810580ca485803100418038502c5004204596003e014042650012501c1040428108007515002031248213148080d141c43c000400da203107100100c2c009440041d20341005c4200b2a072640c0340110b032800400d8119421070185698062410003860b4540302440780200303215040329020303200c42080d5180d0190032803d82d1b909020203060700800c00d041c00d00040141658116404284c21a103040144401c00607003582d004001410764802d1503403c1c40003901d4240003201e10f140d012001072281750104a00c042d1a50200d100781d611680da0754007403032405c0c000c0c40200d030190044031000300301e901e1585100c040c03a5000b0111450008094200103044c0b0040c070b2141c85e00700700b0794858981c0541e10316a1400c00e154041070061800c01c2d2600018804036030b40100303080140502d00c0c003c0129141ca40201c104452a4894034401c00203030710180185050f4400440c0d4114200b8644a21421609403034850440480d0740024860303c14101081132040184c1d000500b510 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 695884559 1250 695883309 695883311
    0x10230f0a0f09150c020d061401080c030109020a031211031b010b01030b1e06090d03021b0d0308150411030106030504051615180909030c0c0510080c03041a100801 71
    0x20001e25001c82c0d40308003d0142002d280301e031050968085005840f0003003042c0c401011040c10031010703910702c0143c44081380400342c2d011108005200c030480074041d0321035102c2d054000b00583ca040d50002003810f040c2c0c3c40090440700821818420192040c0480800c00f00f003103007104c0e40c864402000c00c0505645010300c01c50395181044a00296120b8001e50f408410010600d0314011000d01a017a9802c05030380809910050402c10004252650340c4092140c0c0d0003034000c1d08511862410400c2c003c0c984200c0b1500c2007456003513070000650000c0c0c085411100b4a549100801915030204000b4092034080a10f102d2010000043c200e5164018510440c85042503c00c4262118120140b440c640d00800d40c1c0041802d010300c40c1544521084110060811881c0d40b01c5a51011400100d500e600d100342c000401c040f0f5903005110607001c400d0005d090544d004447c40e0102c2d40014041070000d04100c40d4030704000007003014405400c100c04c8952a650081a00c6410803800b203001c000d401c4d11905901e9 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 695885809 1250 695884559 695884577
    0x7080906060a05090a0506010903020301060b09150c03071415010909021f2c04020a090303110d02120c0c09070f03140f040204090302160f0e130210230f0a 68
    0x282c1090580300040b01d902400c403039915120703203010701e014020041c111810498200d000001580c0c0034050380d4002c0c030482030f03525030743d078003c0f02401a0454051b03030341103040300d040101010071b400000494000c241c0116182d114401040001d80c1402424010b03005907000c030300d0020a07041030315800303200f81a1080307405000d80d00c0518414200000350301c28034400305024a0a1007081200c2403c0309000c2482d40850102c04402040082e08a820100e040e0b000910603c60500415401c428650ba024900300c2c0182100c040c2150025a07401669020401541010904410040041040b00144403000341041410328000070000c00d2240c0c4072030f91100090404c820b4101010226581e5805890260049513240d599502840f020340300e0348408074114403c202d1600c02814407e00e194000d0407030581000525880c0c0041070780010300103400e030f01400c2145060900146c1d10001c1c030907031078201e80c1054200d5840c40302c4480d0440c1c1c00310400b902c803644002801c1c4042c22404000301210380b00c1c2e880754144 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 695887059 1250 695885809 695885821
    0x6200d0b041d0d140d0f390c0c08010e0c1c0302060c0c1501060203040302031b091b09040c030e010507020106030210110316110a05150f0702040204090507080906 71
    0x50540384000400e0a0b00800a400d0f10207100c0c41410542c034502c07804052800c240d00c01090100d9102488070241c80f6a106034018403207000c0241440e508116280c02070302d840d00e609030280c90105510604c800d02801d044001d042050400b002c80c0204421402003041000151825448942c03d034101c074801c01d0b110602c0380d4840210f0034421b2002e40c0643c010312540c0e94503016140541c2c041c11486015110f01c40c400e50711440c2140215000e00605e234082c5440e1450344c8149403071300070580022510541c5104000c50b880e100d07045000d41c002c401b01c14007009544045025642407086411040e001800c1a80032040160190016000c40100070000c1007281d545404c02c908030744c1c9500009503c05000300c52a54003920411501c06040015070a0b0b034900441c1d92030b038016002003514211500403c4c40c602c0c0c461807602001c1a8003d181c150703256041005800c42400307140c0304024403088000d0020900310b056407110742c140e0b8094a00f2140c20415428082c5019000d000e0449a912a9205480000b09 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 695888309 1250 695887059 695887091
    0x10f06090207170313060e0114090a0b070503070e0405041a1e01050a0806061302120411100905060f161a04050d031b030f0921090b0c0a06200d0b04 65
    0x80304083c017076046010050150782e000e000d042400c0c1d00210035900c070034100300c03000040031300c041c05950001c1c002c04001ca11442d2880d454040240350b0400c0c000b0610801041036004481d2003500582140c0000e02d03a5541e18050116150b101048007500c0c0d544020401c1460400c0b5801042d542000f00412203683d8a1080020401b5580030b084065000307070700854528149034810308071580c403551001d828402a14403101103050308490a03645512100741d00035807801c015030903146540c1580b900c114110b08000120314980b045444080c0102000103090079884030b0302e40d030f52215560000c12003101d18111090204500360955050301c0601400114400e1540a03100d040310841112444100c12807824000b640100011900c010000740c66140000000c0d0105580903190140e81ca01701c002c2d0500e04034028185400b60f04401150001088681604403002405201c0b26601140c0400e603000542d400710742c03840340d001701a040d0071004642c0014003c05a0000340d81ca600640e404c01070b0315030590000f0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 695889559 1250 695888309 695888311
    0xb070e0a081002090a180902090f04050601060e130501080c01090806070c031d030f1501090605092412070311010e090604090507050d08041e0e1602010f060902071703 73
    0x11a69409a041d4079802d0516401401100c00b0050070301000ea641c5022003826180d90b0080c480e00999151003940846c0b45c074080803a0000107601c40c0300c0062030140d66281c0d035a2018005c0005220301c6440414131035444040390900500344100610a55a40702a001c0d075a00c100c4050501003181c0d054003258002000032a20b110341f281d60780f00d0742c140d44152420307980e1000c6005016085e012007611082e06883c1001441c1201d160750008005010101c041c040010f0010380000d403180e418074004201e0303582d81d00300c0c6035008149808a0401d09600c1d4209a031914608071030f480d00030440c0301e01900829004540f210480e4000c00048a05412100045a202210b40129a48440c003000421020b090591019244a10480403204c8054840d00010441e070000355003200c40d00c50004080c0b080c00c0d910600380d0234140c40c45050182850600c0120130a0303071030040040036048543c0300c894a041e0b1003504075140410013018200491754607042c032440650301c250001d0f0307800241d00c0760154190300601c00726 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 695890809 1250 695889559 695889569
    0xf0a090f290f040506160605010f060f03270c08010501080c010f03180804091d0a051e2104081b01050405130915151208030a0506010216030b070e0a 65
    0x20a04441c081d0700362446800440a0b038404050034440401d0b40e07241c1c0381c001c10510058440e41d0182c02143e103001002d81e00705810081140c4804a0200700e031f250010129030010b90799040200e400000c0e9208103032007804081c0300d6035071740b01d500a09006100b80f03025260180c0d003000c1c000780143d80c2c96814483d65064000365041c00a0124807108e480c1034860360104880d903010089940e4684c51139100d100d0207801c00e402100303007550703541c080b850003112954840c41c152150101170041115a5244c42e07443c0c100141c462140f03145050b0507000380f840e042c019208940d003004c0e4800402400b19882d561150080e001c1c1d85040d200d500010031001c00350040308000741c0c0050f900d091501c1d0500e0706001128075100c00001d5200d4860400d00700203044c2c411103d001d4030900e000028001d421121000a202c042d50042c0c50f04a0078695446c041021b510441e9880300c1204004143e40e1140d0300100d1614090201e000c0c0040c40c0c0f0303400481084507410015000320130907501c8414607003c41c400c100200d1102e10071 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 695892059 1250 695890809 695890859
    0x12200106060e010e0d0c18060501090302090a0b060c060c19110703060e0f03030c21010b04050f0a120c0306270b0606040536090a0b09030f0a090f 64
    0x4040700544c400c904540030600c0240c51072403009150fa4a14140c806503400111029040210703c08510a542c4543c03c010a02407a02c44c0b4194035640103e40360741005840c1e07820158440d0030a5401d61206c40071140800ca81400b101da142c0340044900e009900544002d03585225201105035aa6100310111580e04500001500c9218076540d1500d00908402c46440c0240c020080903484219050001c0c500c05c1c5810414582d982c14600080d00d020020940e032031080002c6e07000103206642c00d0009070f030140c0b0010751f4400858001c42002504c42d500035407002e0480da02c2580b4020800c007420901d07204403072084005204905031031548000480c1c00b481096190f6031482e0511000c20f0813100c0b81500f0000c040c091b076290940f074001042d03405490020215840c0120401402c25442d0f21b45d1301241214501441e840609103006525200e00d12030300054240c01c0a038021820040d01030003100e00e11580f5a520341d544881120002d00b080c11300b0310489101070034090700051540028092000028080e0507 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 695893309 1250 695892059 695892077
    0x8090a0f03031d01032003161b030c061e02090f01050c03070f020a170d090609051c0c09050117070803070503090907050c06040b0a0c030b130c0c1220010606 69
    0x1031040043c8070400b124504050300d405180340200c01c0303009140c03c03012000407190b40c3c030310700f40340c0c0a1080c00504000b50304004a0080010040101f00d951041c0e082c0d140c981510615040c0c10040f0191102949e0600605d900201440d81c4543d2a4028000c101060340c62a5400b2214001540d10740510b449035500d80d00100566400500c10281921445100400e028003454880c00c80d24000d01d204841d49030540c1c0088200700790b20341c11045000040240b46000400e240c02d00d400302e1182e4410f465130450f25500c40840a00308039070446440c014180300107003044590394810542d5664003090140c9044e5000e81d003c0420308440120441d08440d41180046140c25100d1050080440004140c4003c0110500a00c409075200380078040c000d03805206400c007942440b00c07204044607210004d4806161805204141540f04c11480e03618100306103000041204041c50243e402101d1408000d01042691144d02c4040d80c1041c48000e10001121916503d14075a8481c00c1c03c036441806401c1c0412181c030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 695894559 1250 695893309 695893337
    0xf120c020c0420030c090108150109030f110411041d13111809010207060501080a0c09020a0309170c060106140409020f0d050711060a06061704020a030f08090a0f0303 73
    0x34002d0024080c40c00d80c5610214a80f6250000b580c0065413404010702c00012030305015039010800da07421001440e91150847d030907400180203054540300080c10142c030101c58000b40a01420b40c072200700d601400c00e0104400404041c00154418001c204050704420890040c540d00c09862911428110610212515454a5005034642c0341c070812580030708030b1038a00280021038104c880c080c07250440003588030a160700d0302c00c0c25124140c102e00d070f840d400040c6020102d0030b01d00c030840c00c80c0c1c0d0315400169154040303035044014142404c0040c05040c0d00b00901070b9a120b55500134081d4107140c000740d6080380d88404040b9030151214542956006041c8010f000b00742080d8014401d04005120041c50841044403140584008507540c4010407034902040e4401304040c06001d43c4150184020040719080803c0070340607000392040180085d07100b40c0064110348a85d81218003868210400050141441c030b0f0001e095484000c51070701490b0041c1c40060f000b0b11840b0300d00241ca0303164960500101c400 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 695895809 1250 695894559 695894561
    0xe0108010b1803120304111002061521070e010501140703140d11120114210c03120a0201180f060b041e02041d090a0f1704060f120c020c04 61
    0x26202c141000c80381260402d502e903030100800c45101c419505420380302d140070700701b820b0000600701c1064001d050b00454000020350101d600c907808890160300a030900100e101003052441c42d042c60501e04100074031030391241e030301c009031000c1200c0c0001c03400051784e80c0350001101d0440200341003c420040500042c0000382c042d9001010207506000001e05142407001c3d0842075445050803000180000a4200b10316134a00c00d1311805440030890b8011340301040000f160300c6440da903401040501c2c4072444100b41480a01240c50000801412910303024000425104241c0c00340c202903016600c3d18402c0254611251804041c07203030000090b20824400b61103d401800c4251005a0b000c1c0c1e80302c00000a032500c05129514a030081030300161101d0031b0030200c40c544805e03846801a40302c00101040708080380090800f4000b580f0045c180041c46981c6070000074011441046400800702240114112754003826808000110340d8a042c0302c1003401c0c00050858040e001c03a0700042c2c000080da00003034105 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 695897059 1250 695895809 695895817
    0x503040e041109010308071203060302090127021209061006020d03181a060a0905152403010626160807090302180a0b10050405040906020d0e0601150e0108010b 70
    0xa000b030780c408510700c50004a503100c00b60002c035920b03040821600140448a084000c100489050402078103046400041c5420814401e01010308000085200702490481805091040351881036407920a8800c20b0341307211800f11f03421501c41c8a2789000030400c005078070301c1c0811901140c0241416040c0408111301501d07094a07204008035040207100c000031111071825280542040c0e000709241000810002001c9680d403110103106d0a141c02c0c4407070160b0288001512080469804000d40340d42500700014034081401e00791101c02c084000201c154001c6605401080a640c903400090700058141400c140c1c1a1031003020380d48804584800d19004803903950300130403207051070010f030380e0f5070b5001801d1003900241507030b020300c1841c05000440e5000d00412034500d0003140c100b102c5603402203006119000310320485121b01c0d1207010007010320220f07504403a40340f40e50480c107004040160207607940e669800e10481101c0c0c110005500145481500c250400701c105a465100507413070400220f4280d00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 695898309 1250 695897059 695897063
    0x303020a090308030a0507081501050f0c01060b03010f030b01091a01030504052a0a050d2105070c0902030403020c030d0c24020406091401021c08040f0c1d10030503040e04 75
    0x401d80004004200001d001e544500120100440c8620700340700000c2c240d03c2d01801c500d948402e0104154416a000010780e030901c4440f0008a8440034a00000e0740503191660161441840000c000f040360300d622840a41a00c0c02101a0141d03a6640d00700e00040f02e0b0140d1043c4000f00307840b040042690322a40007030350064012000c5403042903d0160f25503805407060308621381008034240e800034500b040e21240d002132600725106940c01000d520341c440c84800c07803802108000009111210844e0041003601c0060b074001d42c004405c1501c80000300c00a600640d0107402610030304801c5480f501e000102d07180d10f40b4007555034040710703031560b540c0500e052401491080d04607144006140940f0645c40030384004c100702c2c5e803100111458503446100300d8403056140c40c119001104100b008007940082d0f201c03800c00c28640703042a55540e0401801d1861f000d200180b018480c0c1d0340028000d02090504c2e0f01c04200e0302c60a01c4c0544500035100004003180c0b200070b0141d001440b040100c0080c5113102c941c414 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 695899559 1250 695898309 695898317
    0x1c0905100306050301021308120703020717030c01020f121305100e03070501090c150306060e0d08130e010f0509091b0616030c030305010801020306030a0204020a02030c0a1a071b0303020a 82
    0x2e6110070002c0c4c00c0e600044621403004032070300300070014240200704070391000100c8030340103142042c1a1030007504d4511501540c010403003540d0503201400010021141c1035549080219240c1080710901c403d16401504201c0e0005412004030f109001c8000f02104079950000040c081301c45a623200700d01078140c0794810329803030209200c40000300d90b00b030064400c3d0341d11842d9201800350400901c0f81d080d00902d040e06080514091003030002c0307030300203118200140085a0511110a040c58400030a200e61251420b01020800d0005140f5010f0881a8180e0340034070643d1401c640c0f20703814000c0c0120101c801000303503404800880d03d807004a81140c240c140380500264500083d14907000c5c50340d48195030880001700016020300c00d165240c454103024100d0325000354518206903002a0341c850868102034811030703000482001c0d640c0200100e4091420742c000b542c26600c1e450820f51746503003000702d146101240d0710740040c0b01e1500c82c1000d03d014140002e4840010600d903242100250002d0b141d18040c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 695900809 1250 695899559 695899571
    0x4050601020a17191407031803060c0f0806120c0f010c0b240109081b120d0207182f0d02030916060e0a0501080a06090501171c09051003 60
    0x1048403d00b01c2d41c0d0780c1c41c00c084000d0359880000301640120b02c81d030b11000e080060480215140c12542d504a4507119018070b4400c075460100c8080c0034030b13140f080e80010140c0341b501c2001280181c0142d00180c003080c0a0b10791051682d2003d040c0321648104040d10841030f00b028140080e1458200010070014506151440f03d4240d90399072600c0c2c280e03080c1c801e41c40b040c50b0107207046404801041c0c2441003040030310345010001c0c90500342c5941e8034081e01009070300301c060320601000d130740b40e03c0e0030000b1075000542182d110345a0650080d4035150503000300140c41c8034150048554034418050b50035044c055000101d80007600c19000e1540d1030711050344419450080200d20034070301d01d03400510300426110380a400b030300400c10070a9880420b607500c404107201441c0e214194a40c1e4800107081242e4081c01d02616941e01c404085008024070f801c20400d0034070b80000400c0141c2d07541c0200c0300b185074901c211940180c20b01103031084040c03d58a03480000c0d182c9203080c040d0341401811005103060074240842c0d4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 695902059 1250 695900809 695900813
    0x60d05100b0c1614131805100e0601091406120307020307260a02030c0d150c0203040824160203160b100b0906070204021b0d0207030c0b1804050601020a 67
    0x22a400304050b0b5240b0b500011440d200b0b00001444000240425141020541d0384031000c039050300306a99449890680e6001c03c1e0b0104900da4051440e102c0d480b00a88001041c914072600042c03079190b041021522409002080c00000352044c404a08d40c1c00758242c0ea283e9036a03040104080201406030806e000c1403205030010b890800070500500400c1d92142070081809414000380c5211a180c40030310382c0141d802002688001c64640301c485410f4038481103445550074152aa10410408003c54601d01398001c6c4409030f0100250050f80c0c0d60a041e190186910540b1083c40303070410350002e80070105403000c145520140c08080407440b900d801624203201481d1425400709031a010700791a0000b010040001440f50242e05001030001540341b14200380c40035012a116016100000b401035500041e0342d01c00408002408080902d2202221401d04071198020f494011610003110025284980030440b4a103440540d011100103c02c4031445200540421000c0d007400341c1203074194040c1120401c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 695903309 1250 695902059 695902079
    0x1404050a111f120c0c0f08030c0408030711120a0b0f0a0e0303070f020708011e05180703060b1828020405130204031101020307031704020402040510230306060d0510 72
    0x30b5182107440760212550081c0031801a100031040950410940820302d0300050702d00301c100b0503941d410545180e180d584d4440c00c03546920840e00141e8448c4404669101005005206c000082c5810340e000300c1200c12100d0900c0d5203a00a1100805480f909000a0b40a4007550f5000e980071703040d500041000c0082c00030301401d55206680072000989005808041c50350100468001000244000c0022101498000300d8400f00c0c0842c0015207500d0308042200300140300080300c001d02507a800da6407030603a24505100100700c0542d1081c0100e01070860702400c4552240c003940b15090340710300d100b01e6510220684e050300441e15540d4412a500f484013080c3c42c1c40e65000d5842c990441303000141d40303074154240460040c02011070981190300c02c0046c1c400080d4403008604200f1500c225183c00c54540c0d100080c040d020300d80200c1d810501030900102e40691040c440003400346c84100418000000c0c00074900c452008a40b1181c101104014204048403203500555100c0075905200d241e1a03100d0300007070 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 695904559 1250 695903309 695903359
    0x4020703031a03030a0203040b0315030105190e070f0504050604090c1214010218010f021014160e0f060a02010e12040810050714030601170412031404050a11 69
    0x5030020780d59804440c000c0007585406500281c00710001c40c200510100029a0380c400c60107144a0a071000c4082040c1141c549441890031400030b0091100c0e00e01000000009401d0000e1030704200d003000c0e81c040e110140451440c040d2015060f001004e0703420002880701819001d00f456400c20350f507110440206032031040c9100a40b070007840c110600f00c240d0034448902003105c41e9419159204100c25406016003002c0e0000c41d40080c20903101c4001c80000a900b03010120f12002003041c240101181d16444210f00340c0e10a030552068140300c2d0038079800071144a000c110045410525000031a03040e481c1107805001340543d60b05c00400c210301d0b00700c0f903142441e0710035244e24400000803a0602c145002072001c8000454881c00801c000c0c80e0000000f803051041c00913070b4a0700135001001c6a03c07070348552080f880c06860700310550154201884d0000b034105c41c07008c8420000f45000030301969011a92050303802241c0220040c08540003030748499502180002403d68010100c050080d041140da217040 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 695905809 1250 695904559 695904563
    0x340b01120f0b0406021e16020d0f14031c0b030703080306060906071a0615091017042103060b0415031e15050627061b01020904060e011d15040207 64
    0x251b19240101c42504035081400c10042a9100911140070700d80c007450421180140c0440e0942d518204a041a9030400c0c0e1744107019044d41810940001607801c0000102001d030b40c4182c803014006200e0b610380007150074001d500750381500013000c05c00110b01d0410240d500701000074051450544c00100141e25503025440880312008108555002007407042d82566000b5001c1d00c9405010b94400302c0c071038440c4186480c680c86048010f8140314084d10840413001140c169507800d042c0c50134641002512006003c481c140f00c0300000c50040c1440e03119010350070480c2d5440c44118101410007040ca41c9540d00301c0e200204056441c29018054140e4003116a01310141640000e01c00401e03400c201899200d41c0c01003402507604200d8030710410109078030320180700010000c81c094082c1310300018140b407052281300c0e010549904003100c0400b50660090294039421101040b20650302c40598440100900c141d08a0342180c1c003414211010202c061a4401311800300ba03a080d84182c00028100d8001c0300301 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 695907059 1250 695905809 695905811
    0x101e020a020718050103051c020709090f12090f121502070309090b150d020c1e1b1c0209040f08030a05070f02010b030c10050c03340b01120f0b0406 65
    0x40200844001400c1180c00000f00d040c8600e6045840b01c2c0d540b504040d0a42d68000952101290300c0c600c00d00c4610007400c0b00c007505005030320385800c209100c501c00d490b0685905d1f1040ca6481d10f0103008018500403902d141084210807840c003017488131000003858064541c244500c10201c102c40051005000451207500c1e41c0b90001d00f0101864220f444d00701100d4020511400c1004042c0c02d60025291462a0381c0e00160751242c41c06d0005007130011450450390b0b600028001440c0c0c4c0d40d0007240f40d9003150f0310304030102c4500b0300c41010000d4100c1d02c000300314030310801014000054140143c2203a40b050113100c0120110010740d96025017075200f2200320750010b40d903c09101c0340c558050070f50807951046200902210309004002603c802006080380d118104088140d00d001d8040c0080c1d0b95881c0e11603064988545007a26104040800720f90010440022200e40b04400c150709072070403d403d900604000c000380e0a0801a0320480e071305490640c3da1642200200b00083e02c00950710b482103218040c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 695908309 1250 695907059 695907073
    0x60c1b0602030c070b03060f062a0d03200406051b070801060611030a1d0f0603040b060102240106180b1305132304030311040f0521101e020a02 63
    0x141503401c00d43c1381c0e00700030000d050401c24402c041d0340e01b01c1c2d508107080c811610503644090500208046142c1d010215420301c400d002e50203030340e860108090900303401a49080c0040948241101c10320031244101ca54914420300c014886a80b00d04040c007042d9582c03616a05120100700305c01440c02070a5481595113039103030141440483d0744817000758400ca034000b00035410418410005081c80351014039141c2d0308444e45800d074043e65203074203116203402005001160749040504103d0603001040750b50031b016100b00103c0c07008203000c111900c1001002540c1040569081800c00c407003401c1911031000d41c007a1040c3c40441c140840303400a00c1c54540c2c031105840c01c280307000d0522404c9450320130251540c0d0302e08100c0c1c10301d41901c900c03203421007036a001d0030f40d40329542da00d002d50050040c01c4015003003070320110300440c41807904840403041c4e03042158850904852011910400f440c0580700165903001026503107203508040e04424135030301c204040c4641c041c0396414030034100c7e044a03405000690000c6 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 695909559 1250 695908309 695908327
    0x1f0608190204050a27020a0516110616050106050306060d0609033516090303080901060f0e0907090207020f0405040507180b041805030913020f0d02030603010c110601060c1b060203 79
    0x3545d03014084800c0d402c08007510300250041c0105003862000d02624000b80c401c2282261003e40101d0004000c00e0f1101005059410340038a100c9080f9208e40ca08400429070749030015040340300d80c200034003146038240300390b03034040c0a098006402c030140302c64003041d1441240000c150706480c1444540e411034040710301822004005005d0591300c00010042003000401c0d51007542c1c032041d42e4050414420335201c0c00000e5004084c0d0f64400748250416000200d41c5080c42400140034140c0c0004540515885030003010480c440d8502c000d41c001040090050b007802e240d0803580d1301c203028000780c501c0c0c907907103441802d041c0c00074042c161000c41c1e8a0600842514080c4521030a01d00104800340d18006280c0d0380e142e80f4412490b000f407181c698840c130001c4882c96501114152144006020b4407140c170307004048040e41050303031f846109500300123100088511807440a01c8895408000700000e918055080d10040350300241580c15038106140444030307011711040b802c000c0c0020307401542e82d00b08203 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 695910809 1250 695909559 695909609
    0x100501030f121403070507030203190224071d030c0301050405030c0706171b1606021e130e180303100609050303120c130801141f0608190204050a 64
    0x81c41c45400e03c12404500340c44480040e044c0c942c418030f98180f0960710b01d101d060507880c50140c1c01201c500c84210840f521402ca0b400720741840d10101784003060640c44030800d182107020a0440e003000c0003a83c00c0605646a00080ea1860200180502a50400b110300c2e4040303425038204540c01c1d1140da100040e0f00f00c12200c04c0054100400c0301b03141020700d40d0f440c8030101d264000050310140440b10602000c115100b44031007200c0141a450519450250700b42c07030b14401a4000c40e4030001403003505070040d16901040030480e40c103101c624520342c0105090902d941300c07402001d44180040f44505c9805044500d0410045000c0d80803444010703844c510f404001807070750322107801440c00f070f4100380003c40541e410042e07810380000d031302080980c8903821a00d40c00c00521156011941c55800d100c6203642d00403090084602030301503107040c041c40d48032100e01202400b4061041c0800601914002414040b10940301032140c2c040301001751506a0f15400201071403002d0300b1403080e0419100c0004280401 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 695912059 1250 695910809 695910833
    0x2030403031406120a1514010e040b010b070f1b09020409050103050106090e0a121b0b0603100c051c060b07050303180c09150301110d060f080118030c05100501030f 72
    0x8480d1110240a58601c0c0c41d229115011700038041c01e00c642400210002541107a030f031201c01d01c1700e404525a51003440d405041d4081c1c0e000e55003024044000f14a202292089801003604204c0034040c204075503480519202076048d02411166080320b002c03409041c2400200300802e140000440d080d41542403090854800745c1c48015100e2a017039807102640c84c0030860f1481c0700c3e0440000c00010160b80c905683daa00802c06007401080c144100c402002840d4140ca8080d0b5000e504031521500d48507101001ca800484410011400511082100030361205140b181440321540105015603216840751403604075a508407423540001c410010204207410b400040981507600500040000c0000308902c1e0b600a0001d2a00b807501c001d1210440d20250007420040380100105643c1d0700346580a20000c1800d8040d5640011102070006880041400344c00594080c20226168403140340e032301600c1110f007501003200e541c000d22107d284045e41c0c500c0744900940c014141031000c00b0891400c0002c8080c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 695913309 1250 695912059 695912071
    0xb041b1701030209130302010b1008042102100e120d0204030203060a02120f07030b0a0611150f130f0b0103030207050a090c09030b06040609180210020f1c03020c01020304030314 78
    0x6800d00400141c4c1d43c050341640c0003000102c01c0407000e031080c1000c81c05814104602030300030809404010216034404c8202d80708034000c080c03005801a240b0242004005040b03030200059000703803100d141943c40e650019400103640b030304071101c0c0128840300c01c03140c1d04036034070300b008099001c50300b00190308081c40b481da40411600e601b1417a10720007025038202c26101529a03c174942c40b40e000560864020707480588080c100408401005580d42c0c4000c02040c0c0c065540e03102c500801d0070001820240702d5005008405441d100c45595a85a40c3d100400c095500e06581801207038072070304041420f50001901860085c1c0c00780c0703980e500741000c3c001c1d071200d01d0340322208961401104250b07250344a94035500741ca80c07001940b40790342ca4440000300a02a2500140d2005140202d80e8090000038680c54850501c2620803103c080412101a40c135164a40c500140507000705580e5900c601d94451258101c0074541401030800b04001034150898208640460104c0d541d85030f140300c035000060566600c60 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 695914559 1250 695913309 695913347
    0x40305150103031209020a0e13050c010e091b04120605010e07050f1c1e02030a0f0c1407020a030c1211030610170c0301050f220201050703120b041b 65
    0x25145a43c000c001e00300c1300b0240500c00d60380302e0000045586403c1c1000c028a0131200c168007134144095000c0d0200d010560445552080600c00907803540101d0300d41c1c9203014000d081400342c2c0c0c0c60724000c1414545105c40103202550400000c100c820850105624950054000181c1d560600003046a00c0d5405409281444001c1c41100707103007800301084400c0003190645a001c00313140c20800e00054a9242c81e47c10000d503955429485011055020398401d04031030400b807102c0303241014480c085508202c22040001c11154149104842c0740340200030843c8054414141d80b0b0741c0b603d5a40c11054540c1103030030004040010b59007401007421086204000803409000c8a0812a042e20011807540c0301d818960b03011049401002c3e041842a00c0010034058020f02ca2850413514085914104546200820012040141000d04041903202066906031212464107049880c1910011840480e01620303948500035090f00d030f03e4601403c00000300040c0302c11741d03400d469000640201610400040f002c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 695915809 1250 695914559 695914561
    0x40515060d06020a09090240120f06051003022e0c0807081207080f0405030318030d11040612021903150e0f04060605012d020a0b0108010204030515 65
    0x16a00c504404480720340c00403006a65620581c010344003030200d5403181c0c214904c045410442a64040007140d5000c40c08141e80104c00316a80120018444203400141c0907540c2e0242809038502d03800601e0703001c900900362030810030000c1e0ba881c4241d40045469a1028144010070011800d058108001c4403c0f044424114207541014403c0350071100c01c0c15508024070307070044d18180300000084030901504407501c0f0355103480642000f0301d0544203540b4607001801802c0002e01030001c41440f0390055500c00e000c0c1d0f10b5501c03100e00480c510f881c205841c0d001c2d40406c100c890a400e04a102d20020452000d84060b00c5501c1c5c844040c040702400030f20400c61600400410080003420807022040c1e041a0500098244000e40c01040c0070750190440415100a04280400b007400c0c1441d20348076030301c10007051051640b220700448500d0440281c1da83c00c038105000c010340613240d100c102e00d880c0030700b4030494202e0030f0240c480c0a1000c01c20380c0140c0c0982d600203014800c0c404103001d03800ca0001143d04007040c3d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 695917059 1250 695915809 695915821
    0x911070b040308100f03050c100207030c050d150516030c111906140c090a0605040e0403080a0b210c030f03041a16030e0906090c1204050709090b040515 67
    0x4034240c010030003002c200307071280001c81242c0c0b1000e0000181c10008409910241c807840c0440d62024403038105446110120039034107507544000766030401da0340d0140400c1485441c1405110082515000843c1c64880600e600d1000d55071a2140754447d850340301c4034484002b904040902107074525003900082003910400700851903000103986180046c22140301e0340348c40041c28448002c0144580d951381e950200f01c00e1000c4648507070050884880c08a074164041e80d541c15003656603119500c02c045a6000c0b0000080c0420f0044030180d43c000300380c5602040d01421400010010911500b0915589000c00340510890008000c640150780094005041c0c03041c25208503a640c0c040c0d44100c0d1542000e0203d181e410111403429940c143c9200c6031242b1050301507240c0584160380b102c9603603000300d01e041d000506904d8403a107400d004a00412003285085c00b040c1100c3e000700c00040041c3d445100b020f0f0300144285280c4905091719000c0c502e04000c5e8100f40c0303062030400414074091004107500c0c80a1202c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 695918309 1250 695917059 695917073
    0xf2114060109140a180e030406020d020709050709060f230d0b060403020625020306070809150601090b0a1107030b0f010806041502090d2a08060c0a1422091107 70
    0x56401c001005200300170b00c178803183d01070070340e0003031345030b4a4000420005081c0340c001600806035046a0207030368103503480781c003042d0440b40115090400295041c1c020002c0f9070240c0d2100d42c44582e207290072078489450000711781071a0138960f1640c0400800040030003908a281c0300d44054200e040365228509450b540026071103009640b181e0a4410101007070310030700c01d00302140a00e2668003505680d2245440c00005d001030504440541c083d00910310130107400303025451010311504c0c05845050291341021007480c0d0640203225202c0900a030034003442003034907081010800440c4102211492847c210546071040b007410380c4101450b07409071081c403001900c42501040e060b148003a00503118052440014481901600050103540da6000f00d071b0460881850442c4000809010044146503928000c43e40c94100b01e542e0105d03180d050044141003403003044041c4009545c100c02606120488800141c03484880700c680e1a000d500d00d4040003403540a0040a052040c03101840d401c01d02141c80d28a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 695919559 1250 695918309 695918329
    0xe0f1c03030510030f12030f150e060102030c0f03030a1104060207051e0d032a0b040605151f1704080d050402010504150801030b0f01060f211406010914 67
    0x2400c0c03545802c000b4840300361044103480150382241000740d44001c075080c0461807500803107500700000d040540101039903040307000e8032030201280a000d5600c1850032810542005d0090300c146d0440c001002a074481140c20007000e0400c82551f40035641d0b0b41000c51116084460300ca04800c0340309000e11040103402e03000302c0c0c0388048a1055840c4515050750008600b414040780d02d40941c8607203120304100c24168010740914248580d040314101c001108104441c210000030001060422400006030000d403090b08134070b030045041c80030822038803014800140c0e41100d82b440c080440088103c944c000b5544100400e4441a10310044906402c00e91102d140b1032044642503083d054072a004901164851811103009218485000e11091748208000300000f1080c4420f0b10b034021280f000c1030003c101c44000e2412245907031078060b003003681c1050035100d8140b002c0d04203020b4004030400070b03c244c4c01c501a80b8100800722a00d800141f41040c0054020100358022805610903104925210303110745c5080c2e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 695920809 1250 695919559 695919563
    0x604080a03020d15060c03030b1c0215071a0a060e1006050a020a080a0306030b010e1e1005090a0501081e0d0302070203120c0a120503160e010516030e0f1c 68
    0x240c0d0f1541c00112020160401e4003d4101c01c0341c5800740058120392100b03103908440d02c299401d202100754041002484000c64a1001c1c45089800e403140c010f10f000a04482c04400301c01d841d900305402501c4010b10640c010340d8400c0f00301310840070840c600c610303481140007406000030910f440e0304141d1680d52f00c1c3d40300750280d2014810002030b900c403001d000700b251108242e032194055580d00190400200500540d100c11604000d0311400481d512071461030561290707400c81c032044008880907007003032000745000e815000503425400d8042126198101043e200d14103081000c0b4081d40b50685281c03802c08544441c0422044845c43c0c182072001c04654004840d006140150300e82c0603030300000781482d210304030340d1540c0c9200199090502c1070104480414502441d0807500106680c0b074140c41c2488219900715080380700c43c0f0883c16560050790300c0318050301c0c180f6015003007582c00019a0f100140302c038000d0380401d20b505984a01c902d010202801120415078140b001d0a201501d0340c0b41101c4043c41c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 695922059 1250 695920809 695920811
    0xd09170703111203071407080106080f030315060c01050a0915050402150f090316032607081315021006080c18092406090a060b19140d1d0604080a03 65
    0xd0003100401002605c201d2034014902000c42e465075110700380d4548241c41602c00c0c0d5400c02100058152010032401601c00044c405946155540380c0c440c50084203444420b5403100d4280f041c449640c109101d8140305007541d42c03002400720b2050906071400c9074400700400e03a040c1458108801600c0e0361413000038903a12070703017040d4440e1416106032807180900c900454040c4501d034070508006841c485683c1c100c9010304411003031000ca0050f981070840703803913003081c400713400400c920000265090010864420801c19409046807105035920404042c003c4000060b480815000c0e103e889601c20040242440c0e0020b103980320070075022400803080b0002c02c04d544040c2c2c400040c8600380503c480b40c41c42400000889000c280c802c003180a05600761800d60041d81400700040c1d40000c244100400d5881c0800010300700400e494216249418104010b001c103c0e00c030f0a501311607040714004d883c1d6080c0314180804c800a440c080070300100b00b603215404d116030040d400d2001184230301c012107140c0100c0b864 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 695923309 1250 695922059 695922079
    0x1e020901121d0f1e03090102071206060308040e060405071b02011808060103230c0a14030a0c0b0c0105090a0804050d080f0a09060305070c0506060d11030d0917070311 73
    0x100541070815490900300343c0036102c0c2d03d542c0310501040c03440344a21000c05054050000e8a07000742d480c098510b0060150380001d8007030210801d0801903501c071134403c403400300d03c0b00d84a030380c0d4540c80e0f00650700200546003038505220440c502400740c6a40141245040a50581c6030034140140c0320800501a05200c1383d144801044160341004801815102088807003070350f56031800300c00c189113042507076607000e03c0540c0d10065103102141c01c40304040c008240c4026141400d20074049440f058100640c10700c15510b1450002e000384036004001c0c00c10029403902d50305511032050a43d140148514486d030080b01501e8000340c11501620305680003920764007500046407404244910a40258499660f00410f4030103902d68030055041c1505d11a9409100546070550700323591200492800400d95000b00000809038140200a00f035098003801001c0c4012014601003030501c0500c204800024610715002d2103072180e141c240316588030880000341451461929400a94190801154400d510740c070 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 695924559 1250 695923309 695923331
    0xa08060f031f0207081306110f0609062e0303050d0e032106010c0f0b150303070203060109020a05131205060f040b040f02060d0c0f0e0102031c02070203070b0a031e02090112 76
    0x1405540740660405146c403a51504c800010303007640030f00410355041d8030031442c02c41c1e05003502141103030265003c140140a143c07100c1c40501ca0780700c64154031001004c2810380380380f011802d200e2140021402510354640c0e9600c001046820703034940c2008000c441d0310800449004503117102041c4401030f00e045141d03556407148001240d90b440c111b6070141c250301c4201149000d07c52030300002800390300c0c2c0303d65103c014052581403540702c2c082d8410196146d000a001081190425002440c0c81c409514205103450f0303002c501a140909103402050850300d00d005d00a0801c4070800c1403130b410a00c003400d004120300d041d40c0c449181d40d600030300040203040c10701441021911128281c2d12603e60004080c0726501c52000010000001118088000b41482d14103c480d540048100d900c055000b4840140401c0d08941ca04040e40c09103030102e805114840300040c0050520000d003450019543d004603051500b40b10030340b10041d0344102030403000e10400c040340aa07031308070101005010210001280001e481 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 695925809 1250 695924559 695924573
    0x11031308040e0f06091302090604090204200705100b10050d020412050c0918211603050d150522090b0c220302030706230a08060f031f0207 61
    0x50340300003440d0340084144441440b108030128070403001035a17410700d560b664102000044510f50f0019400404d0040825403d041a0b002008050b00141000c03800c0154071a03003043d040ca001104201101020800c0b104000307080c4911007034030940e02c0d014807401885030001707040e100c44500c040303051160000e82c01c09001c032160103590090540c2d2105010144050a00545071800300380d40c030784102481400940004d2940481c80d00d00c046440040212070031140659802810940700f500c0d444c04144800740e030310702c00c148000d030529200c2d40d251a02c40c06550010001d4840000d1310502c0b4101903007081c412074840a0000524590008090090480700c1c1c3e0070b01d00506102c500542064101e804011601c50088000e15a03541c881065507855034a10ba04e11a80020a001c000d5241c0c1107141e0401905208a1903051964201c2d850f011100c14103400780c2c5060342c000001307140484d54240401010b45040c1a103000c4d0340d5800d801614410340c2c0216014084c0d104111030004d0f8690108850082c8158 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 695927059 1250 695925809 695925817
    0x80f031902100f140a20070606051306030c060c0312180204060f0f05060405030a0602070302100e16050d032309090903030402040e0d0c020d0f06090b010303030c0311031308 76
    0x2d0450100981d040e98601000580020303141e540038421240081010300312544540c14201d217000184417251034000502d032080b98040d4000750384031504c4100100312540c0b246881d00110107212000152a8036614259804a101e640041d041c06500003207480800d4100d8052141301c528200c0005810140050341c412896120201a402c5490194041005680c440aa800303036840005441e0200795070300d0401c201c62003940189a0960480820100051740c1e60f000380038441d00c00c1c01551000c5840901c014221451494222410380c000b820089118034042d90b0744c80030b0079003650b07c201140b500d038401612000c2d25034042c0030740c0e40d4483c011540350300c861410342e03052a1004004507154200800741e01da41e03800959045e03116601d8152a10f40c020300000750003c0354403140c0c8131030380c80c1c200d40c4e02044a11684604242c0d00c1c82405202180003607000d2190081c0e080c03040711012003950450900808480c00c09112500781460a0034280060f43c01300f054a82c0310002560002d00a080c52404282c0340c05 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 695928309 1250 695927059 695927083
    0xb1216021225060f06090903120506060417010c031d06070807090f0305071703091c030e0607080a030b0405060a050d020301062111040903050304020108060406081207020a080f031902 80
    0x1c4489030b100c042081c943c018540c0c098903d4010700641d9290f00400707040700c10808008011540e4807000e80c40410658009a40c0b258008000c2824140d80e0256224844225520002c4695444800e040600d03014855a06440d4646d0030b801000b20085002035610100501200244403258002a000512600c0c1c1d100c0601001f202d1107840940c0c0e031800d5640c0e41103034000c8044000720340004450b02403000098820303c8900400002803903c0c18880740380d1400c985c8100b5401c005d04026041020f0301c804006000c40f1f40710300e40b0307250380b058a030718004c0840d0b22a0b61a103108905000034081140e581201c05420358000b100d00c0d0100f00114800280140750540c04040341d4460304e8100f09402400b8582c0681250040249140034840e0b40c0402049400400d8010007291007400810050b521440400e50b015101410004213a501c13015040d1402940000c8000c44850004550b011400c0210402c0028101240107000c10031090126584900800400104c4005001017030802580300b0810704103805 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 695929559 1250 695928309 695928367
    0x60a03050f0a0c120302070b16061b030f1407110a0204090308040201080903040f0b030711100c090f030203030d050403021c080609180c010e0315010b12160212 70
    0x910100386864035002c045100f070b20000192034000420041038041d601030503500d0380c040c140b01400c0c00c541c01c0310342d0820000b4003440c00b09840c00d040058034a100d943c2104c2c801c0d0803500110b0120507802001d0b503810340c4400c03801d9810000801c82c559000c40c641c0740c21804604084c14502c0030741507202d00d814402c600180d4890b007840802c0c0107064014021741e000e98002e0780da44403241e80380707080c44e0382e00e2256102d69102441501410070030070300d00310060760300a606442c01441d07484415006501c2c116044040170a90356171905030b1501e00390010744400003018801d10021a052840d00000d441303021302c0035409030803600c84c000141014820b05c85010071001500070150001c0e80c1040081800318100c0e9040d0143c0603c0000c560740e40c000c80032081d24403103140d0081091202c80c20045880c44800f14503140c02d03101d403211200840040360b580d54081d0680062030303503ca902012503d40081c2001d07000740c00011102a20000f1fa51380410b247100c071000c820740b041d030307071a1105850000300080060702d880e009 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 695930809 1250 695929559 695929573
    0x604020d0f1b0503091b060903030309010606030614030a08070204021b0c0f041b0e0406081002070611040f0303052a0d090f061211090a1d0114090c03060a0305 70
    0x510140d9020700410360048030401c544114a1000390f44038031007034414240f44d41c04070b107a5424a074198560104450030180c1080d05180102d4082840d60f0000d541d01c0039036075151801030200c00d6243c41a5001003048100b440b10601c205400b207a1125503502c0080d003014000111a030540d02c0e1a0101c2d43d031500401e800c0310400010900403900e603071402104607c604244131b000320180c41d0502900c02c1c0340020f440002c08200da10042900d855034110303030b010742040d1240400644d00d5002e20100ca40d5401e400800350340d0300d800c1e190420484401c14021840c01800b400140464000d103112a4142d9030f0604049603a074040c0c1c0d100e400c150b03030031040e901304803041c29581c5281d0140204640007415a90b8403180f00c041c0c0c80706040d40d6021210700444001400c502c10800101e00c0d01e40110307103215031144510380341c0704c00c000c08100717034000c1c2d600282d074051a01d102075100c075113203c00d070306004290b211004041010142c00164900303201520303400700b0103070110124403e595002c00c2c0c20004c56011003204c606c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 695932059 1250 695930809 695930831
    0x50f061c2a06023012070c082709250306030b10171f0c230408060f010501080a0b0402162003280f08040905010e2401080604020d 57
    0x140340c0300d402c4e086940c132a40c4802980c0e0312142d80007520350794820949003030520b040c0c0301d80c02c0c00001c0d0007400340c4200b0100300d103004041040c81c0c00030540d030700c82204000a00354100d151100752251a83c1d00a005945040410161f40035110308036000c0302c0300a40b60015252070740e5040303020701815000900f47d000b1403002d001d0070319040003804080740e0749842d0132800d000c03110000a48402d1442d8601109103d1049181d9091169074004448444141400b545083d0407400c0040c8490000509100c18000024184003132101080790710b031b000d112158085401d6041c540000c00204019010b0286941c5a1031081e5481c3c1d1260141c482c4924000c01e841559021403c22904031501f000c07074500b01440e07075105c0441d030b810041030391200b461040202443c000117502c0041d080b14900401071301d844100e50500400200ba4400601c001d21500c0c0010078254103120141c854000080d003e1301042c1e04400100e22409440b00340504222000d081040f010364801001c01c002e445201c000c0c5800504d403411001d8 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 695933309 1250 695932059 695932063
    0x1506010305130b0a15080d1719090b0103140f07150c051b120a05070b09032406131e0e0106121b06080708040b0903120a050f061c2a0602 60
    0x1c0e16180c6444045c106030396501d200c0d8480d01004c5038600003c8024164020740c1d085099030a130011038002003042040c4ca9054114222041024115400d141c480010818805103940820400303810328040d10040816041486d60f6440d107220354002b0119801504448038003c500c1e84d400d0603040400d44a5085a20740d40c000203004c00d1809070b114503040302d00348030b0505001510820f13450b44100106440c900f8940500c5c01031f000406065172500c0342e80041c00c242081e00e0307105640e855a5401070b010b02d08001c4100400b426103079030005002c92500900c0c0250204180d5989103070488194002070800d5400c244c1405044160070000383c0c0303030140800d60204605174074030178403420f04860181038031500c4200c00c9450b00c1d021741e1024001071803500403502080c1c050740040d80046440044910f40080900101c070321010454054041683d95000c002241c40050780803607003c10101c1d0340c15521202012440440c5504c0e441c06000740806400c6980c0d030544a4042c0105075184140c8a071500d603648100035 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 695934559 1250 695933309 695933321
    0x90923062e06111e100b030c04110a14090603060603100f0b0903060a06060c03050a0302070516051014190e0a09020318010c05040303050903010b2d031506010305130b0a 74
    0x441d15110307400003604804556500882c2130001c40c805082c90910003201c020240c161030f07100c9030b4103004140d4820707440e980c0c51248640c10340242c0c02c1151102c5412034003600602c11400f0310b803584902007080c2e030b07240d83e20381040b81d61081c02101c416440c3e07140d8541545168070617030889100309021500c0030540c0c1c5407820150280580c210102c07400c50f83d84144090503195244102e10100e0718142c0034100280c024005400102c01514005040140544840e031a003190b48002a980c000c240005202a0074082001c480c01070f858213040031740e00c4905420110a1044101c14040710888248000d400752088062501c0c01d60f000b005c907829039469224240096200f90384000601010584145c0c001c6010b004407000301c8541d40b03809062519646042d9850f80c88000043d0f895503849107202d02c287c0d1101242c5404003150081680100c180b82d00c0b211444c0c01e078000c1148281c0c0310500d1407101d41d880710003c0394066004c1c40c000c64070707440700d9811a04080903150003d1108010004029250145600c09 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 695935809 1250 695934559 695934587
    0xc0c0219141c0816080a09090e060f010b1606020c1006170c060304150207030c030e240a0c200a06210e1204090923062e06 54
    0x15000000600c1c10031910841c1d01200e020340141040389400450400c901800380007000e10301d841c025441070341d078071080c40c0d03c4148000089400c105050041c140c50340f0440c1402580c84008004500b424020904501414400c400b000000020104500080c0766410314042c0d90105e010754030f941c211010591035030040d49903940c005103007100c001a1800c2e510191519469810080d082c881c0d60f5009006082c1d000600503910144200e0800030451541d100501040740070b40e0f1036040042451a00402c034103100489680b1920b4110711240280c000040c2404200a48071003451f904c0010000580c1ca4203400030020700344061f1044001880c02280c100152080411100000160f456030000c0c0c80003c070b080c40391241d0700014180490709400340e61142c03114814a0040f01d00c101c10028911a180c4d2164015104082e110940d400c01c00031003040a1010741c64210140c02e00382c407007041c0c01d41d482000400c5254160090750030484511100c90150000b104000c011502c6075466000284c00314191040c0c1c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 695937059 1250 695935809 695935829
    0x7030f0906051813110c0309040e0606090a020307020a0c12151505010c050c0301150801050703050714071b06091707080d14040e040f0b130201050a030c1407060608061003020307090c0c0219 83
    0xb2044400710118083303120b01c0c001000f03241180c9445c0740160094200800d030505522034906c40c0404100450002c600400340c0c44024404030750302c0c0c6002e0703003040c3d100d1100340070039824010000e1040c0304601d62002130714420328201c112000c8a08143c0d00d0000070324010754142d4a000004003440402006040950b080c58009011980b602c1e07400300c00f01c8a00300d0309400054540d4450700d003c50b40010083c480540900c10ba0144015005400100f0a010b0b901120110f55002d004001e54417a40a105607840c00301006032010741c1c605101a919480d161581b5420443c80851022440841030b003550b0181c844020100c900303251a2909000300320b0090002d68151100034002407a01c600745064540c01035040c0d446070b080c041c80c400150042c20380e84000000b444440c000e109610580080545440c0340034070804580b1038074003030034a0f050034405000343c0084040400c0600240c0c4002402504540352010001500c4109401c21604417120040c0250300c012008602c449079400052a941035450780c9803 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 695938309 1250 695937059 695937071
    0x60f01120f02092b110414090f21030a09031715010801051e100203121e07181802160f120507020306011809050307030f0906051813110c030904 63
    0x4c00140d651030444003d400401d80c00160000189404101e2031035610050801320707401c02000da5142c109181110030115a038043c2070840312070002085020001d03400010584c013a60f0b400302002c001444001d041a840a0311100c80b00200f52250041d0007298916110003001c60903d516020b440c4117071b80710140e00051810001080528003c120001d90f0104c5601c24220140c03010b0910819034202d2001109500050043c0c1001e0404146c145124250341c03610030f6561164010b180030700030310150102c3c04000915502070300c5000b03120308503420340e840f8411101940030360f440380d02d0181c8a83c0341411800f0114000103010040003124601b529846417100c078003040c103ca20b00b16228059120040e50583c404c00040211245040000300184c01c01000419a811191a035a00d1580400402c42c00508005d940c5009194803000d510045c16451400f2031a0170484160340031054514501d45108040f80d0098038004c10b00d9500003c000001c00c03c0c0c0c19203801c0005e1519440350410000c441c09241003403 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 695939559 1250 695938309 695938339
    0x604020f011e0905130b100c060608120403060c0503041e0c1a0d0e010e030f090f120f06060108040201091e0f140102010609060602031e040b040b0403050c09040b060f01120f0209 78
    0x40910a10414040c102030045c1c0c1c03400008488502034107100351009907941001150260bc00e01109082100744206640ea0f0b6145180c81d82c21a04228000c50411a080c0244000901c030142c08290a4600c0e40c2c0181a0418a0034605030441096210301d81c0701c07d12111562103603800f040500103a54a06508000e00d50100c1400d900340c400c414404c0c40e00f5041001807401501000300030f003541d1103019155054105c9407001090b101507400c0d18482869102e072022613822001080280c0d4422030a107850790060406500185c85041540107500b104000e0480401c1030305013034040c2800500400400c0c5141d155203c070042da407807225804050040d401c0010104440105028010480d18590300461404c803030b800d686241c48804944a03c40e90004000000e920034244c0c1c06007000d401c44a0600741e8651441c540a45071110040503580182c00c00000c02020a200d5060a0340c03045054130f80c2c8514040c0c160040b11704294940e46d10410900e4003e015019403c40d40c00307411a80420750b42651103c04032 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 695940809 1250 695939559 695939561
    0xb07032009150904020307020a1b0302010c080304020d0209040605220b041106070501090b01050405010509190c02100603060501050118080316021807022a030604020f011e090513 78
    0xa20425410000200300101c01d608003103407402d02d550b80c4091198200000354000a0607640103641450060b8020300c009418807d040107a0804082e0355010800810300d150300107015843d42c5c86015100f0301c0040700203001c0d9110b581c00c11515a0380246100d24603d802d00d0141d0040100359150381c1041242400380044207540d0301d11500c0d494200c3d01c0c000240d9203550b200000d18416500d0142c01150520040c0b0004100340695800c0e5807240000e529a581000140011a84142c0c8510301c1501d1250034809040000400040c00400c075420104034081c0b4500164985200c2080c0d510807585006000000e02520780e0000d41625002d0340c8120468280c040c004007540064010b00000f41c1042200c020055508195102d24601c0941420941d1003003103107110b90340e001101c0100158004002074110040702a00200508050354034080407800513001203542c0307640041c0020700441c500c000102045c1e01603600c0c40000e4a101a00320510811003200808022103445410301520a40c000c540641e506 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 695942059 1250 695940809 695940851
    0x80705160f030c0b1302180618041a0601050702100309111503090c091608060a030b09061602010e1203040f08031810060e070c06110a030902120a03020d05250b0703 72
    0x4149000c0750407c2465042850f00190207030798402e404038061842c0103100d5594610403400f07454031850b100341200500f00121001402d41c0d0420108004a0300140e0700c031218060f11080301e1400149e000091b150641c0c114201c45083e940c414601480400e01441070303001503110303904090654138020345000601030b080c9019200201480c203984410b440883c424031002e540184003e0802400c159607841e601200001528110079540216040001e841d0826448c0c90840c0001d2008010000c603800300305172640e0f070b40809610704607800008201404590643c0610054200303100903174034103200d42c09030140d185014050342d16005d0092103800b418082e2140c04100c8009182020b840d541d00c5000f00d800301e00c801412150a96100042c44140b00004003801d08011070b07442c002000354071401003081c07408154000189552001c03011100090b808504240840718504100c0d441d0b0010000241d01180118001100c140384900040180f203020021140508010b840800c42c0002001030800d44102c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 695943309 1250 695942059 695942063
    0x9090204060e060a030f020a2a080f0a0201020415020610060320030c0705011b3c020a0b07030c1e0801051306090515040c020d080705160f030c0b13 65
    0x54800700c0c4846401d00000809104e0b5003031800203043c60803079050307404a800c41603a0030000303051500300c400401a06400c4540c03560316655542415585543c51421901c2217240c240d000030b40110b810702040b4003d405890181c004400014415509144001d540f004119485100300003018400980c0a0003481400040007806a00283c0f8045001452a00e94001307840807182c18400c0141002241c0c082c40740f0702d0044170040d6a031250030202c00004210030800c55482100e07420083c15051621a0710a60fa14441492402e0140720010600240d090081c0b490000c1d00b03290803c001c1000d032584c1036002d00308248254442d003003148150381444660f841d00d005c03424080384c0210018001303480e0400300c3c000d001c1100300c4040755443e00c6021020941b4026908000c044404041c0c40495203000d0142e50490741c00c81c070041c903030f501c81c9802c02046040c003d00080140040021007032807800c030a041347e28240e82c0040080d0624440307854002c14070080c8001c01e56110718114017044038458241d11400200b6 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 695944559 1250 695943309 695943317
    0x10f05070204410109020a0219030905060a020f0d0e032a10030e06090a030804080a0210110307021c0509150904090503071104050c03010b07150e010b010909020406 72
    0x20390355400d1100400a038001005400c0c0300c482c600300e99100c00704141240081410701c200840c15000c40c005611001038020302c01e03c3c0d0040c4001542158002026010548110307011506501d4604043c0d034071501d250016500420001640e100140d00042c003c915400d082045a591110f40340040341c0700202a840305d40d05400000780041c4503194200c84100180480076100c214001d0310300040c5e0203403451028a000300b62501d0b48103032602070602055510031585806442402c1803590010300c1c500300108002d19200001c074503000514820402070f85004211742007000700068201c50388603250422640040103209480b544041400c0340355845070038040d039442d41c604021448003004412059004074000f1800c081c080c50300c4907640c50007140c101e24081d80255555080c2c1d42825005800041c04140c0240c2c03c0005120090343c0060442c0d045800c9036540580b074170722901d030100c0012804001144818100604101d403004190321071884101c00343c98043c800c03a03503903003010140d000c0c9104000c042 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 695945809 1250 695944559 695944567
    0xc030503071d030d020c01080c041a181c0b100f050f06070206030a091e020307141c110427170f041206050109020909070f090803030108100506010f05 66
    0x668001e49440b400050800845015900d0003404649000010310102c00140d000411201403941c10500441d0019800780304c2c1d030300d0301d420650b4401483c43d00285400700c90000081000038030b400d454104000344002007031040c034401600c50142c4400d25401058404102000118036544480ea00e2a030031100303031610200c0c01920f42000c1004116000020f90f0b08000200014401a942d401c0114440e4442c1d40c800101c9007410300300145400720701118200c103955000245030160fa00018803070102e80800c1010707082c50080001060407440750843d910740c40354400004070200201401000368181d0141e1301003001c100f0030464010940031001d110002e459501d44044081064242d00c0202c4100c1c0384c0d540386c500941d0107664010380c0e001c3c1e0f1081035800071100c0e8000412659026041c0180134544042d8241100c46002a00280d00034007448103009103100844046400360095000034881c21041c3c81d1250ba60b070045580303400404204a82d41c5183c6400034105601800c081341140c000360361281e0074 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 695947059 1250 695945809 695945821
    0x9050702010b130b210f0106060c050c0f040e0d030b0306070e01092606011205011a0303090d0507090c0e1014040b070c0e0112050d0203090f19120506070f0c030503 72
    0x100200004c841d00203041354246001c0c9005400107240d10388100d07004040b45c0761445c600c542102c00c1030308042c080200000c425000b1400000e150302083c00100c52407458030000c500094000c1c0700061048a090091340e40700c4195070b41561040310400c0c02602622820755498101700c0d818800d2203c05400302c5c03559001401100b090407580c030900305100c0315848880314040c1400b4600703d400d9101c0d0341d900c02c07a0703e540c6040080a008450341003001c154110400a06d080000b41c481c020645003070300440340040c0d10410300c00e04000400040c10380e81810801c441c21868028030a03048042d10b540a04501d000117108207200300e1803017274842c0b40741110070700f81030034280c0003d0181d21900040d02c41010001e40820484200c8640c1030082000040d0604030008905e0301c1820440c90920705070954201303110064550b141c0030102d00c022032040b10030032110260b10241d00f01030782890300a062600101501a41005070000b180c5009030710a45880c024044038038011111011100760041c0094404c2c0b01081c8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 695948309 1250 695947059 695947061
    0x305012102040b0616110619050903070e0a0b010e0a0f06080711191209061e031407080105190b1603020c10180b03160c0305040306050c0409050702010b13 68
    0x428610091002c22040443d1002804a030002c2c0309020122a0314800081000f9888000341041d4200340c3e565400e0450010200c061003034620101c10030f210700050010826030301800f2a00c050840f0910203c42d0703041290720300004000d004401c0740442c2e500d01803030070189171449a400c21102c401c05207202c07040c103040c01211080d03000343ca004180007541040307456002041c0070988030380040d152020032110311400c0c022040c0b0340e800305100c00c0c42185642401015448800b07910502444e07078070220706000b02541180105814040c02424809040602481d00c0e84030980e039040341d60440e2071562401d005410007510a000303110b00b900781141000340e4a42084104481007415000f401610381ca24040004a581c2540c115130b9080051000c01c0b43c000c01301e1640462502a08904281c45c1c03e6252862246d40c07000d4295002c1d6003032090f0005010704142c0300700c3c1190f01542d8440e0040c0b00c0c07405d04035031450080c0c1150040b0702c42242010001002188140701c0c942517940000c1c2105084c80804407560 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 695949559 1250 695948309 695948369
    0x702010507050109051f150509090a060e030c010c050a02060f060d081c0c170423070b040306060b0f0d0515061c1a090a0228030c020c01030501 63
    0x2418004203000c84030104000b0f10403a50301358060f4006c2c001e040d010100d00783d00e800e8240e00c542c40152501c0c9000341c1c403024140a41d8155001030362202d03841d8540610742403801c10742c4c08004000a08000b401d0f40b00c00008005030084494440003170084100d1340c0805e503014040c80383da65006a000c0b0700041c00540c019520141c00c440b000e0204541142aa1105640d60317211289548681c00746444d803081036001c40c07241c03d001030308500d8584000084078041c10b020364006000580101c030106040e12580d5100300440d0300480450080f074124540d07034000d001160b0400d101c20f42d0b0380b51900700002807501d40002162007600c03405854910f080c01c90f0301081c006050142420003030110483d12682d03541c55540c004d100080740ba4500010300c880589903001680d1107085502c000d001000250b9801d602d8200c0c04a420000b031407401350701c0700354140003681011612049600040b5628850220f02601688114143c51041d401c0e580b21054200064040d42c00a200703085484268400361304c50340c2c1c0d0305030000c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 695950809 1250 695949559 695949563
    0x1e0f230109030605040308180105010513020f13080601090e0d0c081c0203010b04302303070303050f2a21090c09130302031918061d0402040b03040807 66
    0x500001c580725150714040302c904403800c5012138014000d03c0143d9081d00e0540703009441410080c8000e41c18480422108054022030500640c0c000c1080e0054030a80d80c1691441c2c115412008005c0d130f0348440c2250307964020b00c1150401c6281c00000c440c411004030b10b0068840554031307640e425650907520786642d980b1a11259400a8000b03c3c0c103500c003c05d5000450003000d1110707000b0380b81c42c10038085003102d6103c1c081e807482548203841800d003030b00c50003040b450200f42c00030340090342d171100703d01c01001e481451001c555007400700003901c00c00c040d003590016001d89105640345805a44040d400300403021040303082c00c0c2c403030101581d02c2c1ca400c105000814851f40701c104240e40081e02e400101c0b1003618240c0d2100525000000a220700d400c1c003400080d0300c0340ba4444003c4515030f141e00e000e074684c451028600b034210324001e500c031440c60080207507080022000902000d150758400c070051030b408154541d101a040d0341200b00c0d240303140c14026241545c120795800d62558840355141c80710f41c1d03c11442 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 695952059 1250 695950809 695950817
    0xa02060d09050f250807060c0c120b04030806030a0309170c040f020703030b190504020d1b020a05064005070e0a05010b0315040b13061e0f2301 63
    0xa039000040b02800140741d5031803064000c040081d29201500c11000401100d20280d940703010040008020018440c421204941450000c900c09070410016038025900f140d04029a900401c4042050f80c59545201d01d0017a507400c0d1640d2609c0302055168444074801400003960988140300c1c05900c540040c624034410b00481c2d07894840c8802080540e058001e80207503281d400b090b500c05154060003050b043c000c044412101003000800b245c0c001c0405405454040c40c1d0201c0c000c0c1d031302c104960003a000400340c17116000c4919449000295135030f41076081203c090042c1004511000b9111414002c82c0d00103a05200b801c800c1440c614010a4084880180640044a00c2c8010038010701c0703580e0180203186041e41c2240741ca440094155601030384107108404e1308104204415101c6003104605000803140864500d134510000380c204412405d00c3e0924a162202c001200c6a443c164030101c4615094112591981e030b87e0040c0c2906010310a12504a80c4801080810750040422013811001418 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 695953309 1250 695952059 695952071
    0x824040210110712050f010c080907030f030302070b01090207021f020d051305090c0301031202060121020321070201031a0904021903081c0509010c1e170c040510030204080a02060d 79
    0xb100c4e44a04444041514103801c4201800c00585085c0128401c03856281400c40817403d01d048070a40c0e03182c0f5440080c0c040c02d044110f920406100ea0122502990400062503003541c480815100035441801c0482c450228030b003409980040350039200506c0c00840d0080c001084401d9010389895020300c40a1038501010040800c0940d6401011030003070203012403107516076046141258541c5503401c40c200a6500030001008012103600d05c191007d10491481c6610240502c0400d00d403080801d808542d22038200135058440c000c10000c2c08005000341c0c1c050104a0711550380c00d2940068030b0740c02c0d4000c40c0c88800280542400381c810024603001c0d00c03144c003d1650300e8403084001d80001410b4216135410b581d0032200c0740000e004050304812054020840b80f802c0c50009040400c02c00848990130004042e440002401084510f000782c20007102c1401900e0603020f801901d074084e002c0c0074403030700380c0d8490611850b1091096074290380b82c1c0c030000c00416a0940070170800750040000244101d494107 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 695954559 1250 695953309 695953319
    0x40b13030f030f080901090503030a0c0e041d0120040b0306061b01021911070303230d060602160b030f040f02120a02030607031406151308240402101107 67
    0x510340d288994040d40e40c00710280c0d2241001090100098001704140c0e0411038000702040d8080126500f03c0201360b80000d04440c0c1c0341080d20004444c220480c0d100e03140c407a4450803590803004460309060590009c1021144629640302510140c01c0c0042400300144401e0101c4030610f4000c0d900128014071050034842c04c01c1801d0036001403508156810307500407810048051212500340b0b48140241844240089130007450707a80d170411444050100000410094401503546401005c04510024070175900c80e00303498500054800c82c820100188503001c3c2c1c6404200c0c03021003800507160403d02d41440c0d501d540c02e111112440260094696040d038068448c01030740d4005020220282500150181c156203004041c1400f800a1071007040c5820206440c105100002a882e841101110443c0e80050241101c04a50040c520406540440d91401041c0940005401c1d440b0007841415030709200300390000c82c0d40307241050360000d400500d45d1401800072402020300703020840300d050495007901d0341c81d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 695955809 1250 695954559 695954573
    0x51005041214070518042012070f050a06140c1504050a0606140a030311030c0604030503090708011104050609011101022a070f050603070c0b07090617040206040b1303 73
    0x9101192003109039650460700b080d00b07100c0c50000b802c003150f160071189401c120207020440002c10080010b880c0710720990015010020920324410090030030344c07165010403941c5a0b616030038000c182c03034890703004c0b0001814038214a2007419100b06a882c002d62035940c00c85d100b10f81d00258042201d030301680703a09a0070305a020304642c0c41540901700030104c400c540d0612404569258018020b4084100c840c080c3d00e880307041e02c500449915190018150700c8200106003140101283c24080d0300440c0d084c08241940710380603601070501c1c9010b4a240d61b503221840c0e422034400d40240c00c01c8003000e00c0100520701d07003080584192601030401e14207000e0415401d07404c992006c1002c098611205608111092845060600c01d0704688000c0140a05010440750407050358030555108201c00000581007a110b0b20710016030907404668a00710381070034040a030840020303010b0303400020258441c83d5119500001d65a00450300940401d00e800d0828920b10b00c10f074041c800c2c0751350360b09074840b0000000d600 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 695957059 1250 695955809 695955839
    0xe04050408040e130b16030902061902061f18020d0c0302043f15020c0d0e043b1002030411100f05130e2503060f05100504 54
    0xc5103628958690070040b44184103d806000e0102044030302c1c0c5944009903450070105c0d0010710040c030040f000040c14074201c0140860080094200340040b0380001c0401d4070660000071980c0343e40980d41c076139030383c068418561103086804040141e8200410440b2620f000b035101a080d002d03100c00361900031041c0c115401c4d01c40a28032100020790025042046012242d00c0310b007001c00901060134846180340340400321255a2100c0c3c0320303100404007102e0030001140a0180324204040c029501d403919030700c10a840c2c601c0801d1180101d400800420341c949024403518541c1c100b00a444081c804141c40d14071001c146904805080d4502d019039450000350401845440c2600c1e2000981d072860b092900d9002d007030380b88100902510881d10310340842ca030005040e030802d26032881d0113525034100c074864034103481283e4041040c8180d194240650482c0380040d050250700402068610058042000c40483d800c920803050b207941d00c90004d00c040c0c0352102c60340c00c81064a1030a80d08041c1c81c4c80e10760850f069 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 695958309 1250 695957059 695957063
    0x70f0c022707110a0206070b070302130801020a0801120510090309051306091d0d14040f080a05010b010513061407140303070912020603010512100c0e0405060a0f0e070e040504 77
    0xc01d103080003040d581c400030b501161448030002d03000c1180a0740c04140c950080c20f800030410607620700010f86803071080d410395104006012a031091030355140c5405000798060400c02002803d68800861030284500c205051203a1000041540180e2209114001c000b160812020401e6a60b8001030035603600c1c007075030401e01071000c000400034a00141c0e1421501d00842510802c0c2c003590071940315640c00700d1109400d40460802c3e805507000c071014101c00384225040305407100d40c00c1501003401c520002d00e89000900c940020008060080c0054501d8061000015a01c6942d40c100b40000c62090301c6080420540c00000703402d1030110354a0003101d003040b40b4002c01c950310200030084100c0d171040812004141d05035902050703801c03d401280e09071105018403401160302c9aa0030546d460200309018507418400c01c100914100900018081c1100e035919905c41d03410b00012444514000220f84200c0d0310305d43d0400c1c0604e1400a0000380810010030640500007220180003464550b40030385071080f4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 695959559 1250 695958309 695958379
    0x60d030e120d030b0a050d14210a020613080a030b031006081c140d0902030309130606110102180904020a090c0503071101050741030109050f070f0c02 66
    0x12180102c01021211203503984d03880340700c0c0104100415220f800c40211302c180c004059403440c40e980c0030070500c0c14100101c8480580c40454a01c0081c40031800580030358015a03080d59000c1c0c803141c00c11041c81e1044040900b00b072104010100080707010744e10207000300c0405015604032001c00c0501f00300f22841d83d80f1a104036000b42001901103942100e00340581d008909118000c0030455404c8182ea016140d11200ca0b1a61103096500355a81001995074004c0000e1030380c440550682c10403400f038031041c4035003c04a403821005400307610041c0269260661f07900d50400340c150000081110804010f0026a0060304070b02c400300c0d020016024038826941d080d00d0b06950fa05102c0801405c106c1c4440200c00d04c0d9240100340310755560f0107071004090380c0ca1030030490300d55038070740300c07100d802c801109251464818904280031440b249030b0080c6040b51096a8108001c0d958412103030641d840c104c40f00d40000e160440c0c034010060140520690050019000c0c1103041d2102107580e00c4100ca00301c01203016 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 695960809 1250 695959559 695959573
    0x5040515092a160f081b0f0d0e09040f020a210302060f0f2701021206040b0a1d090a020603070e0f01020f1f0b06070f0c0e010e060d030e12 61
    0x2008508000e81030454610310b40b140751148001030076550003802e800c010180710300c01c030200e410320011205a8511841600c007203c1002e1000d200302c0e6a51450000d4582c1501894100b81034103030203040010045180508000d13a50f680301d681f10b0034100d400c0c05003241d1100000d00040b509108802d101104d0300d03002a010a40e600d1681006403812500808159046c140e41e000c118101880c840d143e500421806900003007506000c000e02a280032500884d09a58400b090107110200740c1c0843c0740c003ca4059034200180e860580c144520052a4041c0801c1c1007208500088521001c0e00078a5200d0b1004041da420f40109500180c0c69600680b1640005114207000c19402d10385400b2400e043408003400200035010041116544400e03e01c0d44081080c01d5030003030f1800310380341500310f400d03403500040080369035454501e010411440040e0301641e0380710b0300c241e01190300140032110314180d685650000c90310b40c1e550010410310300d00295040b01040800d00660750b4544500e01229040719409000e44a8 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 695962059 1250 695960809 695960851
    0x121e231309050121030e04140a09020108061e0d03020102040306090b0f0a060f140a03020a060908160b04141815030c03151821030f0702160504051509 66
    0x240c0d001078024a030211049102041c4d600440940d50088075031504110075400300f00e0002400800c0f043d089010941d1040080000340d181c9540902c0900d8802d07242d203e61030b140c8206100c0d6032003803800b050b082c8a1501401103140d25114030f00b00d40081c0300748005460030f0380781d5440f4410382d0003508085904885010500c801c1100d5955030542c00144240d0412160b454450b036544410311911404800315048641200c02d0784491910701f0103160050620121199a5a00242a03a100c0d2240641600642e40407000c54100042c803042115041502c050030542801c120514108510312030035030200c0382e03041c0300c40c01c1409001d500388644540d0841300b070000d02001c14181480c0000348140d10a0b042030102c2c42c2c0030040c0081c00c0e608100f02107030f02240b0741d9060f50002d290461400d240300301428042003003c040c690604c02148a0072032407410440f1519040c2040e680c552441d00f40301000700d1144401c0c402800d01e980615800200c4d059000c44080f103c1c40801c68000717041d45c120b140c075980c0801c2041 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 695963309 1250 695962059 695962061
    0x10501030f02070b010306020a110610060305060904050c0f040e25080102091e0409080f071b0503060a05100b070302070f0e07080a0f0204051804121e231309 69
    0x20400d0070004150310b0021a03669091281005001c01849168042035007a1014840c490050311500448122403031703800c0c00d0a10321146142803061800003400c00002a00301d040072010a03002e96800030090640c941400b0030001403181010425402c1540d440c2100340d450360400000fa90540c0728580303030300e0300300608051031a6440ea640004070f46a0040051966544542d00381d224141004402003c2c20107207a00018003500000b0001b605641d408942c54440c21140c2c030007011464481c25a0000b01c19203d2902810310786984682a415000f91002412a0001350822070f4017102d10080d0041c2691035040c080c269400806041d401a8030044041c002da094410900001d01001443c41d011842c00c808014200e4800401c2400c20302c1d1590507045c80311000c0d4040e2405030400a001074003c1c443c242c3c0c81104150200c80035600007070204c400008070741c010041d8085e81c04007050100d1000d00711102c1a220100010000441849151104540c1c43c040038050141d582c10607000100c09450440280 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 695964559 1250 695963309 695963321
    0xa1a070c23010f0e010c08040e09030409050a1802010c1a0108031b060c0703232808041509020a03050610080d0e0a0e0406141503150c0306040b0307090e0601050103 72
    0x5052100f0361100500840d00480c2c0c41001650074640524104801d141002c500c0c015540b092111000c2c4106000c6500c5012004c0e000780c4545076030400603592109507000641c2d081416480b21800c03001c1e40c04000d5441511801c0101d4024040c40b1240b0f0480b4003500100e2409903c5018950008200102419010b11810350000ca47c58000c00440c05d100b0500f2405d071146400c0142404802000388507a03200c201e144e144840c07010f6062586500b0500e801c0360f8481d40800e040c901544082d4105074600703004ac00607a02540c1c0207011500700840303000c2440010203521000380da2110f000c0c5000400150100a442d110b1003541001d00440c034903144a0614004034501340c82c05101da00d00202c0225100c140c0700c2d80031100244940007181e244d60078900020500004035a64031080756003001000300525180501e0f0070820380c11100b05d45c11821611550034820754612100c040e0410200b0708a184c590004070350a04000e081d5030a19680e440440c048603004c003418449600801c0c01048a0b6815200d40 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 695965809 1250 695964559 695964629
    0xe0a0e01150504141002100c080709081518030c0102030a0903020609070e06010810090207050c0a060306030816050312090105271e0c130608120403020a1a070c 70
    0xc0f4109030034409650a4015602900c5000741c1080520751500d502c01c00c0701e0b00c208080380404000d800404032000381000e100320350820100340f01c1200020b058400140c6050818201c524107810341d101c0844000c00d1500081c0c401c0c485100174088942d450300203100846c02840030a4000442c54418500682444801040c801107604070320409c204041e004050030341d019009290130300280e603071451000c854005c150007015415202084400c00c2050001d075000302250f00b00c0b4070b0840c980d034483e011002c2c0c802030302004013003203800d01140171041185820003407000d1013402601d041039280d800303030010b44008455410440c1c0d1a441445581c0320819100d8014400450f01c0c003c445006940b015504c4204c010110341002c0031180e105041c04c800c0c010140c00c1d00c40200394020f030070b440b0000e11000d00a14002c100f424042c0e0304004e02504020000c80d012242d01822115009141c2105500259245946041c0800007042010000b034482c034605d8014240d550b61003a01c0c9221642c550301842c07030040c84 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 695967059 1250 695965809 695965817
    0x50313081501080a0206120a02070c031a0907060c060911190f0918110a0803030a020403060e28080906030a1e110d0b01110a03030b011407020d080304030e0a0e0115 72
    0x11380405a180c6004540d00c844109103003004070b45804206070000d200e17122025002880c00c01c004000c02a190340e4a0040a500c40b84a81981c4c4607400c076151a034020748951000b0a81d442c401400042050304070354955070040465844105c2080080f50f0b000032121840c10302c05c0c0e6903200034004907106188800140002c0c140070080301d1559110149000c41b800000b40070200207039040d10f010355640030031704080e1034500c0660b40c83c1c1c00e00348903080203504217000c1140d0b09403e16001082041000549404440c1c0d00c000501c11541c01242c0e03100500c5014100f5200800704001c010015110000154020390340c6000c0000e04030044601000e04980303005405040c5418280e0210b0b00c4070303908087d240d40840c0360342e002a601d940daa00594105c2e0409070006c0842c0a404103003001d0640503404411041004e0325241e1812400000381c00040c800d0060096214100300288804100001c0107181d00502c0ba0800f91004d4032800c00103883c20040c0d6001040d80c0648600602c205504104204000026420 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 695968309 1250 695967059 695967073
    0x111219090809010e0402070f050102090a060c02180c0f0a0210180f0204050901240602060906010303050703050a11010e061b09030c090a180506062e0c05031308150108 73
    0x529000c082c070072000b41504004218003407904039501d0b40c5c110354100f903001481c1c0c0c0810901e407500074042e41124086620440d960003000031080d0240c049503c401f9030045c903160404461010f440c0700c600c806400c0361900c04082c0301c503044a0003401e004090a1420760000d08408581c1403c0c1d00c00d88810000d050075072610762822000003510189018080341d4122404a050340d00c2d802c0c0c0600402c0320185d60000303548131b203104115410241b24240155071040d800e40d422503540c001610350f074003428440100041e0003013210030046446400a0207940c0301341d00c2c1010034901d10120503820b40d44412040702c180e810810a008103803042d8000100402c0c1d0b006120303800d0048260010f6212a10700400c1c0b4014000600044e0710a0041d6110b10181601e00b4407840703201707145007022951108101c41c2d42c1c0c014100400c400070034000e1140e550060980e62400d148224148103411525229408004c0300da512083c040098240c0018071000302401c6504c00410030b00e942c50900e40c9104030183d0120803039400c222 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 695969559 1250 695968309 695968313
    0xf0f070f1b020102030903151005060c1506040b100f031401210602120f01091107150e070f08030904050604060305121b07090608060a0c0f110111121909 67
    0x140e000c80d0712150000301d800122480380010703030440c49050f12041d8913008080c05050505548141e1a003e001b4040701e483c05144c60740c09100c0c80d4807070660700c2240c5502108111000030740d03028401350704c18800b40c000b01c5d51040c404c021400d0241c1401240c1c001c1420000080358466051244002c0c44148d5550768405500d04186032035141840c1c200700904800070340d03a001c2032010340c0d012500380101800c0c04284519204000e042542402e0003000d9031541449102800d00088500ba5602c403a00503000d040c254009582c03807001028610b958030400e000741076000594140c02d1115200400798280911380d2803803a030341004121000100070700d10440c6410800e01c046040051801d1050024081c40c0f6910030038403140344494054603e4880d07a03031080010210f01414290005403c40b4484412100c5949442601005032117052600400040180d1448180307640316901c4050012046000091400702c42c00d020140303a4009014452810f02c0c51043c4811194004400f0355000b5611108010300707640c1c0c1d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 695970809 1250 695969559 695969567
    0x7111009060e04020f0c0a081201091e051509090c010e030a150e101b030c1b02040c0309020303031005010917060a0b0a080604050c09011a041e030b0f0f070f 69
    0x550b0b542c09035034042961803c1001800c00c81d10b035080440200e800c40c0ca034a00c3c10005a81c0701e48a03c0c0d810910740000003841c010180078140c04180001d480f4607002d4410144400140720003401c4582e018a000c1c510201d5031106507810f03004104c2003020b00f1a208034100094454001c25601c2d03070090303004c3e54480c0081903070002c500131483d10301c200200c0c7c04448001120701d0100740c0c44100f130f0003d24281443c010f1200c0a01e100d490005907031010700403000000000e885582280404011040c1e5524901c00185041e07803014503258113a09000410200e5900400c0ca550401c07510700024065514080c007440d80c1029511004000d6801c0d00c07100800c41c03010440d12104007800340341115844003103901131651450148005008008100c40c1149000e040081e40c407045054400d009030465000400c0c0d44209243c0380815001c00c00c2400d207464500360002a54800102051039201c0c600a800710000e500e1514841c003a903461820710055040801018102c4600580314006000c07045420002d55500 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 695972059 1250 695970809 695970827
    0x31b20150a0e0f180f07020610030233040b070b180307140703020d05010203150609030304060c0204060305030703020303190606090b032a0d060503011107170405060711100906 77
    0x2501d141901c50241c80200b01c286419030030301501c0070302134002c210317280e02d40c04500340c03080c41aa803c03190340c1d40710040090356041d16408040c0d0405114036943c000c1e41d4a452100c0d802d40705114070f040c5040807a01700084030f80c100d50030140d0000310008041c2c051022103a00145c000c51038144480b002282000c03242d0b0782c4d01c50340a0007008503403124000c098a88080c8903e0008607005801020540c2d07492501c0c50003944103c44150426001c640c0c040810304040c429565000030140065144c9401c02c641501c0351a0b6480c4c04990181d100c100c0440000c10510207040710510036001961241003006800c01342408035203118010030714101e020809141d2101c1741904a40c0c3d1508465a82e8a032a6180c0d14001d1006416545032058082d2a14004600301c005001c0d007140f140d020410700d5280c0e420142070352014440c800030044240000b0300410942003a40103501d018010040c0b070580d4440204034031750007111068501382d00010f01c2a800c0c2c00c14600c0142c01c0c4200c0e103011a07446045c85005458068 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 695973309 1250 695972059 695972087
    0x30b06030d0527090a0f14040309061b020a03080a14070210050c15070f020d081b0a05070501060609060806040b01080a05070c06090b0601110d02060103031b20150a 72
    0x6440c0f241c503449031550311500707071006000c2c06031480e600e05550448094040500c28400c9079142800340d04240c3c4010400c54080e50307040c1e541004491600b401141c0400000700080c40c022550040640180c0e11280c42c1402140b050a500d40c42d00105c0402a108800e10313451900c20361030412204006036101c0075130003154007490400c0b5440c0c141d207401c1c6a1805c014820701d100c00564000904c03058a4000390040761303001441c1d0840704520180d00d011034900300140c68032201c198069800d85500c901d000003404460b1214600740f421320300c19850300e600303442c096400440829420942803001c1540880f1080c5d02c034074181d40c180310011825000030032025009101001080d5544003080810b031040c1c8c2800d101e582c20003414040b45001e070408604440c81650180e01082c90300b94031414803000480c2c141010321054001d4061a0320b140c80944003a8143d405211199900035840e00c005042d5280900080810b06094085607040c80144807118208860f00e1058400034007105034402d0780110f800403490f07 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 695974559 1250 695973309 695973337
    0xc10022806180c0803130504091703180106150e01030b120f01050a0f05010e070e04202d04090902040e0f16060801050a090515030f07030b06030d05 65
    0x4030080124125208540000a101604107840c1071104521602d0b0303a2420b80c01400c040700a240ea98000d180d8900c21411025031501100307400300480e1420386d115942a40c011900c051030719509040d070907090f610031580307200c082c030480420643c6903401b445050040c003c100c4554516054000001c0d220400101c0424109522600c00d0181c0342c07a4003440030041c45104045804058144015a0107071100300c5845680c0392821800b02100401801038074121a0000d04010b626120084101ca4a141420300716030050340300c94014900b80c0107055130501126000d098a034907441e1005544102c2840440c540003d0833a120341e07490a841803404440444d20014000501c0d0003061000c5409040803480c0d00703c103401100c4003400e1141c4003082403405140d0144c41c404c03a080d00c070300d401e644100c000c2c0035103034008586074018400c240720741c0d00817608051030041e00b22030240c81d20006890071f00012195034698102090070003c0080d1000074503080701c0c08030b010382280082010010014010582180e4981c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 695975809 1250 695974559 695974603
    0xb190e100b12191107031b020f0d110a090506121f020d200301030c211103160f080d090e150105041503050124211413050c1002 56
    0x81110190442c400f040200300034800407030450303540310564010103010350102d5280b088603156264504a510321296008004510f00c1a540080c4000d101075100c003140c50500d00780d80b5018a03138138004602c000f0a2125408681e80c0703400c80c18002c80c148642402441c075401640030341c98095403030980078644400d840703006885003903e00040d07003d480300c11406101900f0015600700c4d0081204002c50580c2c2c010002041e003140d49580f8410036270300381c451030041500d8020b0074000103203a0310024050000020120350909020074244084101640d0145402040000741040380c00e50910440001c2c440300c1c2865100c0034070300080c064080000505401404c0a0b10b6205c0c0c0c1181e00a4060b9005040c2e0810820440032100c003002d401000c081c0501e00c0345004080169000e0151a254400183c001e5564000c100c07030f4108031b542e404e0f0680705980090540f10300300d015010201035201d03481041d4070401d051505440d810013608202201d4007140c0076031813110320b20301c000e1b17000600d8484000028001c0201 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 695977059 1250 695975809 695975821
    0x3c0106050a1409042a0b0a030b010207061b0c03120309030e040209030a0212150a0905100b0f040e070b0a02061f12080f0f03090c0406080601050f04020d0b190e100b12 73
    0x14034015170807850304103592100204601c0390240103005c2c215842d031410005200000b0040e6581d03e02c9201d420001180e01400144800040040f4a0503c0c441e1480c4208651030355180003188c030300c1c21744410011f651100050301b49030303228000701000e046c281e4007140b80201e400701007604c0c0d00ca4a00c0281c0505180040b50407020400c10005101c07071288055000c550030680e000c4009010b4002040d190b9100d941c8460300c00f000603100d110580d142c000c040c03c0c2900c500805002c040c0c4103c0c00c03841c2250140560001c1c050011000034022611640d014200518054502940e00721201e07030b03201c1018007000d4090004000c40c030301c80c1342026081000c0e641c95001640a0308002c0c41090058509000b000c8103000300c3c1c0c140094082c4601000304c4060040e1a00da004480e640d010900c1110b900c80341180c110515030525a000341a0102015408190a41c01d00c01191101c0a0014041108405040100310048a50801c260020039011204d00c1340c034a05604015940562010f03c0c0241c05c20710003040c4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 695978309 1250 695977059 695977103
    0x307080702120109120212030c04050f0a0b0406020d090e04030207053d0305091506040c03060824010e060907110f0d031a0109083c0106050a140904 65
    0x5000d010440248080300c2c0600d0171154961054034220054414010200b42080080d010b0301e101d45440300c121810f15240c00304101000c02000c062a070001403070100490201e40d03990041010b081c1c9a0000c0443c90000200106011229444100c5c0b040600c1c080c0310020354080781250403280210313001d0310080c4020028138810300036004400084104111252003c1c041040038164000091714100a0b9a50391030000d5240c80440b00300303e03c04d84141d40043c15510300b80e0300161000002e85400074225480780300c55131810b81c5c0040d040b20740e032100003031841505501c054400c2c09000c5a402440d02804c054001c035040203400742840040c42409080c051a1a20030003400d000850000200d580c107800003500980180130b42550000c100000b501c0d10000365009032052012a401c100040924810010010341a00d0307040c0d4bc1501429280c0d442122842d8984011141d1810b01200004400c1d00d0801040092134040e40030342e01801404808900c99920300b5442c0e039005800078400441c0000e1400024 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 695979559 1250 695978309 695978329
    0x2013218030a0209010603022b0518010e06060111070905090105090d05040612050c070b070e01030f140103022b05030405102105060a0503010c0c020f0f0303040b0901020c060703030c02010f0506030307080702 91
    0x427000002c8540c082e4040c030316004180100034040251051407003c0c0030032401c1e07400340d50782124644e000c04040303000380d4802c1d031200180144100039141015184e040090a9400c1034502a5142c4c1d114401d00c4000307242403000c0c0210511505020785407030303d0000c02500e1014021a250200d0380c3e0307000000c0041030707120308a58490340d00209045462038110030107810042804419800070b440c2680d0154050360500c07620f100043d07090b1040b241d03680707903508100d85e00044440a8003c07148181030a00c84c00440c10107015054411000b031032716a4200028005006940c0202a040013102e45803040540707501040b0102c00704d000800030446079031b0400420010070955104982640c600350400c801550302c4011003400382c0c4202ca00c0c100c9c2d45a01020840e050241d00105a03054101304801c0000091080c02400c480d40107006540891151300c0000700690480720301507004c40d442d540715004e1294280b056907921030240508000c2414a80c1c0460360700c0c00b4400d002852070304000341800c25036403210454 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 695980809 1250 695979559 695979607
    0x1e120b16090b0a0503041713050409060b03010501080f06160c030c0201020106051e132304030212040b180d03021c02010213150f0c030c02013218030a020901060302 72
    0x10b540c3d030300c00064000700558000c660988005c0781002c1d0f804c281c6100300d011a10940314401a0040f1941000c040000800c08160200d1701a542c4108800198600f07000c1d0b20300900e9490080d0210b065810030380380c10071000810115501c150410b42d8500150004040b01c84103400d894400f6020b0110310040c0c2c010555034000c01d5000e170b04880c2040724507482d0100044062070645055080d9280c40d03c54405450001c08582181e0126021a401c2c940e05250150750140c001d00c101c0d09031380c8000640350700317941c09504038880c0c0358070014041511114501030421903400c00c1c3da02421a9030f030303620000e44030010b01c1e0b00020400c1c1e0001c44a003005100b501994007802011202d41401c664404250101990540101010a14060f44841850300424000010036019200c14004c3c201d50b900450f0940180b426003a1000b400320011100643c0001c41c07100c000c103030002c12580d100c0007a06000a001101b610080c0301e9480802c1440040e111101601e0444140381400760326440c0b80c520606118085c129a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 695982059 1250 695980809 695980829
    0x103021003150e062101020a0207060201090503040e3c060d020f04020d27020a06020d080a051e070206010812040302060706050a0207020303160b0a050621161e120b1609 74
    0x14058905c06500400c10050300d6001c1390b109641d101c400380d00b84c6098174130207401508144001c0101030850a401580114582081212400318000b06c0741d0000307502c0c0c14845901d40c00000b80090440c002c5803581c0116049581100030112607000131201000f001030303d801640c010038449030b020213640101d07500403940d55640011040403445144440c1c001d0b00240d01c10240c1e8100000c0990000c0b41300880015a03964083c502d9461010450242030003030b0204a0b4043c0208078a128101c0310344138140100c5980d4042d0030154907205500d85441045440d11182c980308001c00c00050340c44208503104594006400b01d000c0d505d81d040311009000342d10313000c6c1d0180000500c1c401d8001b07209509054540c418110a0559211310074008100c4208aa045410040000840c007041050454100380400d0040c100c0d0fa11818881508103201c415901428040700b001703ca4081e42805a0140c2016200041e09445d150740680c03034400d80741c500a45054109204401d524034214407401110300a0f000300c0c80307 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 695983309 1250 695982059 695982109
    0x20f0f040915050f010b0403030c030c2a060302042d0f060503091c1202070c1e171615020304082a100801060f0306080708060103021003150e06 63
    0x2482011081c04a0030b01414501d0180016036400740c0030515816a881080000c1c207180c2166000c0d00d900f03600c014203400740242d000c2440c0005400c0d42c0309500003420810390100c0c40050b00100c12214050b900035006041c010310040c000b145c800030040c5504640f081d004500c040c220600d5684948494018000041c8144404640140c2180c0118003400955003210082100354441c03c11034070302d84000d0340000354402070b20031091215030083c004960141c14450003c5a40e140040c0102000c505c1c40a6050f000c0d1200f000303400900710800354000400e10140c2800c018980100104546c240140e1a19045656008035080d00c00c0058501810049086400074101d0400001c203c402d001070b07401a020b260705064080341022050401d5250383c2d902c40c1c0c1190703402e04d02e081c1c2d50600c56808030303020540c1e108000580d08108020b040d0080421401a007035550460052100306001d0a602109040c20039980e4012901081915011120080340c41e1080d034686900203242c00c071030b0264128220a80b10 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 695984559 1250 695983309 695983313
    0x702040b06030106081f03020f101709160f0e041b0816230a060f030207080d0605030c1f03020a11012a1d06130803030c07110616020f0f0409 62
    0x407014046d100d03c0400c2c03502c0e9403c00607a00300300000303400000e4100504140c3c0054071b0414123040e10030002c1c40c0c1009500c20800050344040c6810844640c81076a100e20744164028540100080c00340410720400440e80b8188550100c03040380c0500000c040c1c44e4138611b041c01c0d441c24140014050b20002d8286e410654202c2803010b040f00b01401401902c5060340203610809041814075004050040d040503912461702d0010f444141024640f6030505070200409000a50080001c10381e02c00c00b4600040c40c541000c0906140c070100500f103030b00804001589102054000981000301c0b20103241c0507a507444030540440d00307e00560340340016982040c220b0300044d5010b034403898070ad4245c00348541411244004c100c0c5c20401100a0014080c500c03004059241081c60040400d1283c0c4010400c00e50341e255412880c55200715440713004003d01190762020044030400440c2400e000700c03041c905240309200051030384000341a00070310401d40a00e2030003003611105062150054002c100300842d440e18 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 695985809 1250 695984559 695984567
    0x12030402061b060c04090605120c0904031806021513081801090308030915090102030606070f0f0803040c060210090309271a01080a0204060c030804060618060311240702040b06030106 80
    0x90103640d40580c148100408e05050600080019444410081c0030740c01d401c000b440340041c4090015001c00502105e08281030074070380090700061a8540c0200000b40c464030800396403142c0a041c2c00c030003800c1c42504c00d01003400c0c10181c1d441c01c0342c0300c02540540124480141ca5002c105e600040c0300d45408402c0140c145004104500c00584a00024a080c0c2c0c80014003401c0b0311088400755171015080c0020004680030301e2203a64110f12035038285890706203035213550103240c204031070845079407142d031000340314203a0305011a00350a4500d000a00032a14503580c06006480180951140b000281c400b5050800000d07007030742c41d115042c00081004089110304214080e40c58100e40d030104901101007030b0600b010344211800c44030f155807001e4041d510b41d80c044554a40c082d0090300d03c1034031200003055281030407242119014002e100003440303070324514240400605540c4e000c0d100d00200800f03120700449074400c04040003030320481076585509071700c0001c000300050b4046a406c51030110000c15102e0b00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 695987059 1250 695985809 695985817
    0x1e0603070921021002150a0b130e01020a02070f0e01090b0409020a06080627130f0b011d240609060f04090501050405090a0503180d06150302100212030402061b060c 72
    0xb5600401185020071050380d5440c9402186d00c501d50602c000030301c0c1c448499000155110380207040940000d417903007416081c0d4210103081240342c2d500003405003400350100642c0780245200290141c025140c0b03401e10009420521441c0f1809854820481244d0f80e164819100d007640100050310b29500c0d2100100149030817203085000781c000e1507004800400702208661040c90724901c1d01002d41e00d1505012000c1900001101d40c12401040f14000407200b1302e525000e094441d81c0254206078031501e244542d58060000b542e14079442503800002031905140d42d4225000382c41280e03881d054200441c09610400300c4100d44840301040c0880c2c1040700d60061812610115400c2c4441c2d15a400021780321b403405580203080c0da0007042400841000807a0b0700445040061100340c3c41c4209407a09400d40b0520801d0005440300c0725010700451034070f80c1d0702d1824040a44000c02003900745d00800c01d100d1201520191080c000440c056009070224030000340c20000b40303c2500d0380707824000d12010320341d00 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 695988309 1250 695987059 695987063
    0x604080304020d230a03120608031c1104120b0f06010f0305060a080a0302070509090c06160f06020307030f1506020d0e04061511010f0b0a0504050a06030506071206051e0603070921 79
    0x5840000c11f00e091490050307600380d941900107185404041054074001c0c060b0024a48480c035240c211070002c00400c14054001001e10388504004a45e540c500700d01e51030002081403401010901c184846660310560006e0a1800c03410001440d403030740c50004074041159840081203110310a110820540e0108040d4100c030f070255101402c81e280c40c1c1c441d0707803a04403201d805600b004081c01a8490500714192181d100c0b4020446880c0098694030f80c002640d108840c0e803030100380c0303c081c07140c640d900c02d105041928217444045001a410803500948070240800600100442203a00c01c000340d8171580503100420303c1d0070310214420360001c0c0160501180d2020030206510300029000100a0303801802d02e18000200400c401504080800c0004c04001d0300403204241c4c1c800c0f020000940401113135014248580354180c0e600006200c6001741e540c60380055016101c440400541102d074038036400e81840045130780b1070301e9a80303804045500d404240e00c0750b10410b44100b03840c1c00401010081428140c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 695989559 1250 695988309 695988317
    0x414120105070216050319080a0306030503040e19060305061b0903010c20030304050309090439140a05280315141b1309021b0105090604080304020d230a03 68
    0x10782c0c171010151191a410780c40401818211201030014141d28000c0c0703a2070106040001d1260344948a0074a1900150020440034851000b48072071117906003000c40c0b14a4500006114035802c5688481d00c0b4107001c0c00340c42030703070b071380c032060b441c4980c554500740c4041020290080050121400c00244000441541114001c2144480c1c48442c60f001c01180c0c4a16000740040d46009480800d2080c0c45000410a4032031150440d025940c18000c042c0d0854040310601c0c20720a8010429600d00c6220035541c080c0c40c0031501c048100449031903000e051412070300d08490821710400030f040c0c11003500c2ca950500a1074081c1d0070901004210070051418200c100f840300801000c040c91444d103000c00030603540304464140e14035000349502d10000c010030304503103400000a0320b15036804540c0183d03007108180010325410140c640491000c241315245d481500b10005103c1800c01d500d03602078610010740041d001c0e4a0b070804000034083c50008850340d01692510700c80c41001206840f580702c0d081000114001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 695990809 1250 695989559 695989603
    0x8070803181c1d04020a030614010e030a061119020d1b262a0f0a1a0c1303030f02010c260a060b07050a1202030a0504141201050702 58
    0x1a07900041d1603105041d456911031100c07150000c0907902640c0b4004104840c4400684490300740d1103174009440c4481154901140142c207228442c400c40015103901c1e0f040000300d5065000a079400034901e002c25421050000e103008040c08040200e11581e4403004e211100030701d41c140030726400542d80106140a590392a81c484071540b150003412000350b0050f118081001c1c41d0841c8001550030202008020042d0920780503000b0f049900030301d00762060f050300b524088400c88404034288040d0445540a40292005002940c6c94584a003c210300703404000702c8440004221400880c1102d0703d04107454a0010b4195803450f004140c09010710301e540043d403c0500c00b0100c0341c040c1c402c400c0400e048102d20034222254108460280d540101020501a100c140000700e80110400901031607004031b01510700c420f924188440071100c0d01c0c1020b030455108015600c40c0503805400d0790299402c15004011518044000a51035a400700301c12406500e040c0038001a15000250b1461900c100c80304a202 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 695992059 1250 695990809 695990851
    0xf09030f0307150216030815090a0605090c03071407050a020301050a05151002031c0204031407030201140c0c0d1109070e0f040203161808070807090b0405060102071a040308070803 79
    0x40c5e0203030030b49840084d450582224002800307a0034640e4030400c8071020204810116001a4101d00305449003200e140c0e0b121f80c10301041c1010040d4a80c00304010700f41c41e20b07500785000e0050440c2040e44042c007040c14007203001810400c0a20110240d650024000d0000f42040e9100c00000e0809940056004401041103c02d40c10501c801513941c4441e0340146081c01c91850085581c00818440608207690070007011000600c540200d110010303000d00103002003400c3d0703c0058004544111310011007242400203191102002658403069042601e200706401c02c04d1400c00340c5840400003140c0d02c44040c40c1041103580d031042c01402080012180040d0842515041c0022444166441490603607050b00d02d000da41d000c1c00c0051a0b01890a441200256a0b5010f0f0b80c02d1828580000b92150880081040801d006006400f81400221020861810600c0020755160800c3c82050003940001844800e42c45481d0700741d50003150051070641c3d94850301d1400304401d0b03004452003180140a051a00c803 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 695993309 1250 695992059 695992061
    0x10507080a140601081305010608010902100801030f030c032001051b090d020405090309062b110a230c01020c010c020a080d1e0e010e07050111070b0f09030f030715 72
    0x40b24515070342403038441d01c0e10401141c004400502c18100300c03074403422020014409225030001001d40f41c0000a0540b264410052480000300603102044250001807000c1610514803555081c1d060400d07440c0d0300030303034a410385008455151790b42e841030b10000c0c03003c032409042d0403162088240b1a5907042c941c2e490300c00344010b8040e8140d196004a12184240010300741079100301e03000381400007144d003000714040c00980c090b40403441125011500030091000c480310141190b1072448020028441c148c0c54a240441c1030162082a03020001255640c10b001031510500c40e0035180810007450366548211400d6020b036128503e034640d0b0f9807a203219001c800744042120381a4940c04920303a442c0c02101035003040030705582410342d40c1050358008104002c04051190484005454001084060070040f0b02801c00d100307030744181d050000600420076040404581103050311016050503407241c4007a400c5070128014554041d03003521486500910402000000e0004903100d03d03071034030030b042001c2c140c20 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 695994559 1250 695993309 695993321
    0x40308092d03040f0308040603111912061a0703020715080106051c020703120e01053105191b1508040809040504080c0c1507021c0f05010507080a 64
    0x5a0350050001000740c1e005080e82440740c0004515044904068982400d03600ba00c0130750340100c45407280050108082c44c1c00d400b4003000500c1002c105418080721004542000b1034003040d841c200000030146400c191519440640079108440000a080c454100c180690b54000e4000360003510402c000040c2c00c641004908051030050741c0d9204069180080586441e045942c01602240000c2d400c2882c1185600c05070940c5400383c0d981c40380181c21603424100700d070408034104110742d061404000680620710500130400703e0314a07411345c6035000d049450462484000d0001d026001d110b04249400104a08110306c8900848020703e1042c8850000c51030a405442611003250280402c00180307406039a80070352103400381181526101491002504079101280c0031203a0b00c001142500c42c210003040070000c1d003c000d0380c58540c2001c89042803403243c000e2400003880f640ba0300c031180011142060340640c641d80c0c04060141e071003200340350041c0030740f000301c9000001031400d400140000c0c103140100 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 695995809 1250 695994559 695994583
    0x3280509161a0310080d0c030e01020a03020a02011404080102031f0f15050a1e090305060c09090a09170c03030a050c040e041403090a0f090b0f03190302120a0804030809 74
    0xc2003a009080b4200ca1154000a090385030700100a400002c082c0d101740b00b0060204c5c0e20366079901031f81c255441c010380040b40342e811260455211003241e00000741c001911051003602424030f80c82c0e2640007583c0203034901c500d802c550169400481803141e07681441c41d000c0318001000e2506201c9a03190483c0101e007206038801c21198014064802e04085e0148004011000e214509440003a20411060180c03090000041c00015540750041007800001e1240c0c41d048646d685605c0d140c81c080760002030b0400000b80440d0710720f079980ea88207020011092a0590342c0044414050740340c0e40701881c11910781e0012140d40c000315003001c0c0080c900c0000340c400c0310142e6442412054041e200c94a5483c902c0001807610102c6100410001c1e000d0760750800303000c0081121080c4d040d805401c2c00c01030b01c103039242d083d1514018010000c40300324641d0081411110880200c604042400260038101d1900342d0070840406000800261848a944d06c10407851165000380c540d41c445495011809a8038483d003548 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 695997059 1250 695995809 695995829
    0x1406030303040f0f0209010e0a05090c0a09021b0601061106070305061503270a110901060c0209040309030209010e0f24010e010e090106030222080a06020328050916 72
    0x10b000110120b0f03e00030080c1c000c0111201c101304980c0441d02c1d50400f82c01201280c5001c00822400138814000c1692140f04080945000e43e425000320308214001c1c09200001074000c02e400c501204c4040403907504942c01c004903086540c0d90140079140303e101c00c802280b58059400011082400380c003859000c1d404c0030740019a070000300b0350901e00c43d4102618202c55081015800c020a01c0080390696890b140c48000c0d0a48440a01d844007203010107041c8280694081c000400040c7d070000d29009620381c0585000102d40c1d83d5280c01c03220040d00d41c000030350003a02b480c008248000300794010351203005445406984c2c0e4544419100700b00b50388045501c00d11482c6555020554414118800d54180606290129101d194009001c14100360080300000754007249a1a40c115003a6030480701203041c003003100c82c0b18105480780e03131920030203107003e0402078001020502c1308801c41c0824001f0201e030040d40a42003107940070b103006005c0c00e032007140852141a160741c1544824412500480e03055403e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 695998309 1250 695997059 695997061
    0x91c050903030f1b150603070611011d2413022707050d060e10140402040803030405010504021011060f270109030e150702120c0a09090b07030522050c04110403061406030303 76
    0x2003c07a88184ac03840ca40c0c1c4c0d00e54940709280502c01c035181740404894003a60140288445640149000c0e000580180d10782d0035030030003803103c0d1203502c4039805c00181e0107a50400e0454660030030442c00c0e04001581c0f5699200010800140030340c0480501040c03419071200b03104040d658090004449401e680781641c12401c410100400d0030005442405500003800240c00c03c1d0351092480d0031500100c906840700e0751220104021480c1102c0c2c031100e0b88195040c403114140c9032171081607407107900605845460b004280420b01d1178940740c40f0000783c104e1084000c0904039a0050040c06840842003c13000f1881c1402c03c0d180d1440e10410816042002d4000701c4e06100d11a020003640c0344c1d4060060449005102038030301c2c243c490130380d46d4020f00100c40d00414403034220701d003100200000800d10300802d85030005000c01c4244014044c0c007031203c410a40d0380c1043c0306080103802c1050300140a940689171558203981140800f018000304d0780103c41c1004921485c254001486c035088809a9168000700 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 695999559 1250 695998309 695998319
    0xe040512250312090b100902120703180209090312060111030a03020708040e01030b15010e090a1a030d11060105040b0d0b070309050a060203010e091c050903030f1b15060307 76
    0x2110700d01c0d010300a00d4048140354042c0c407940215024201c09036a42c0c0d0303403481006101c00d102c0180e2030003088034010840c42d02040d81d80d40d203440341d0050854000c0649078040840003910948110b03e04a400501240203418130041c2981e40b80d10070318141d4058511000007034415070044000c3c00c1a00c04241c091407520048810440c000d50044104a490800c14000440c4225002c616540614464510f0b0342047c100312142414604c0d4911040f81005081403408030b40b030f190700003c43d80000480402103415485602040c980e641c0c8039901541600c55402c06c80c10300c503400007611240c0c3c02210141e554607602d8005020950701c00d402c80300d8015a08442c0d400c00a564221031503030004040ca000640c0c10707035a039074a1b0705107810b003402a14401e8011006002000280390015005080d5000a0400101e41800354011165401c026401d00c8400b00e001021902e0a100f2244410205034040d5520f001c1302d00a401d104250070f40c080218490700b80d81c610240e800c80100e41c040e0074010000c0004600d04 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 696000809 1250 695999559 695999617
    0x9060a060e060c0708070902070b1515030402180c0a0f0215040b090a06020414090f040b0601080903070606030605010305071707090b01030615021005090114041415010e040512 77
    0xc2e40001c466121390303480001c1d842428803181d005032040701c2c00965251424140b402c1e058030050252008480364422111003981d43c3c3c000591000240c0d0003003a201d50310380c0002442c1240b44414503c0c000d401000b005910406840140040c03540e5071141440c002c00d8a130101c0e95071414442e07240007008204040780105881c0b40c0c80990103000350040316075520043d91103034240e0b001544843c018080c08000e0f00050700e041500558000000c2d850b1709800d143c25116000019005010385050011500100300c0e00001402100c407500c1c2c01c50350034003035035a481c0349c104001d140911003560345010310080410000628000b402c010700d5418010007840d41000101c200610340e03103030060b05040c0e032032100041d00c0b880b003540d0b4012900f49801502031400f20f055070406460000784a58850791602040b601c0c101042d03642c6981150300940f005d408006050f0740145007071030000c1c0643e91020345d4000091902ca0450300103104621410542e005209800c10744007140c01295415680c0c0c2036032540c200d0180d003203 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 696002059 1250 696000809 696000817
    0x340801031209360e1515030d0903031409010f03051f030f0203010f020c15100f06030f0509030f0a032003010e01031b050a050d06090803090a030207140a061b1502030609060a060e06 79
    0x40900b0202d001b044072000a252884806c43c02002c1003602c0d108100349a00b00691040001c0ea5410b03403841e106e110710000b0b0100100a0078042459940d2011408e4981e4800194110f018201c040b00a650b48030f003440c1d5030644007004102e20075800e01070700f2036000c02c4600a0b107041e844501c006000c07410b40c000800c0e10b0070400500f4500e40c008000740016242000b032004900603c501e03180001c610031124160030a8501c000c2c0510035a41c003c2044440b501401c00407111100010b141c00150000f010042c0402c3c03d00442800302d0102000c8004156000d42c500d49504980c400c41000d0440c203030240011f20a0080f034400c0d20350003c0104d80402260802c007000e103448a10803000029038803207584d182c0e0081d400645070810319038004508581050f4040101d040035221b80e400f0350308051000400500088040c0c01800708100c00100c1030400303000380c1c5030005403413640840340c4082144070442c00c00c000d400072038000d03214004800100d030260500000500c02e6555a640e070300f01a001c85801d022403680 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 696003309 1250 696002059 696002071
    0x8032505010e01050a02031e040c0b090d0516061b051504030516110a050103060312030b1201050f0402180402090a0b010207080105340801031209360e15 67
    0x500c0b007240390520607081c0301d01131064001030001038032401c11068840c3e82e0383c02c8801c010140750a6038103000201d41100040c0b400c03030300d0700840655104130000224100032802c00000b856803094800110150548100307000c00d998107640c940d0889590100c0040c0c00b040003c1000c0c0440c1c011318540070440409010140d401030203401c02c50710701040c9500d4030712001c0b101e410035a61035006002c207400c1442e144190300c00902092a05106c00c0d400e6442c0d007807079405007880309414142c0d5107901030300c1c0340c40341da6041206c07040307072002000075142407007015820302c10850b4101d202c0c41031035801c5580301a105081501540d0090003070042c5a0b80c2c003200c48010700412003101d0552240f0500055000f0f002d010b018891a03803440704052103054064103460380b41d208078070f0a51810840310701108055202c1c40680c110b0b40c0001401502d00c0055500780c651b0120f5800c04040540c0c20041c07510b0f152034402c2d400080340389900400002c001100714010441e5086905a2200c0d0440914003038003048520030180c000b1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 696004559 1250 696003309 696003311
    0x2010302070c23040506121b011b0c08010516080402090402150a0302190f23070b0a1a150d091104020406120c0807120507020f01020318070803250501 66
    0x40c2c8420440c154404080a160f102c000010190342c0d0b541000c0c01941e4006006451011a107003450081907142e04400244842c00382c86640c1c4841d45c3c4e849500002c1800d1007900304100505c41600300b000140001d03008180056080a001c01d50002104801c105241520341d0781014540f0b981e8204130141d003010340244d03488401e100001c0c0304841c1c00301c0100324181c0603450059651040f940c407810350005c20005901440740d2180185544cc0d00176900c6a0300d9110702400601941c5c00301d81f598014001c021010300607159600c10809134040755440032108403c11303020700281b851101c0403c201035140445c070188441e010b2203040c2c0c181295801c40604213104045050009a0b140041022604642d02c100000780d14441d00b84101c00071880b880a0f9143c6502e04880d051400b0540a440d80d03991803e0800070301d80c1da10000e500c0b58803d010410341100001c1c02595a802d10485110340e180303240c500c41c40c083c020071000065600c0c002003141d9105152035205601c0200e949011b80d1a400480f50070785040d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 696005809 1250 696004559 696004583
    0xe01090306020f0703030501121a04050a0f12110120090103020c03070b04030914030c01110a060504120329012109200915090714030412030e0304120201030207 70
    0x651540043d0071000c40043d41c0c2912501d25003402016648180d01003070003681000c2040010601c804a07100c20b0716140008450241c469140c400c1c40e0003581071002c4c00c05102d0004441c20000640b28281d07c9043d41d40c8e4590004035541680d5080303c07040849030800c4003e400c1c009104d6481b0201904400005040c01800e00c8007400a440c19580082000c48407118072108010030140c000100702c0103411040b40035074140340e0071008259904041000203040c010458007515100c07800f04402c0050a600c62414400e500701403030000800e008412000e00406e04049a01a55a100407000c2004281701d8040c640510b02200042d00c01d0381d20200702580d101c881c1c11441000b40114000d0704010f03445034441c0054114403c1d8002c2412000511480c842c0514109020018145082e220300a02e021100341c07615803545003064075501c003900c400340c490440200811042c4603460700f4080840d08962402d00150000582254880c400c1d401a141d007400e03090612f002551103980030709500e80c0325001d05055 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 696007059 1250 696005809 696005813
    0x31d03030405030406020d090f05190902070605070305161e090e07050405010306050907051b1603050604302f0d120b0109031b05040c050a1b030f0e010903 68
    0x11548100d5080c2c032181c0c0001810890301c2c2c1d040108140e01c4280340f03800c6030428249205812102c003188a414403441440c0360300a1100e880d90407400003450003400441d5201c03050300cbc114010b03080031a88030740440e01e010009010f08901030020454a0426a0748000e20202200c07560301034040b04802d04104248000042022400c00b504680176039102d40782c0a0b243d40c13501000400340c039000e07003103240500541010b000c7c6481e041425140900c1881000110417140711412070b1501c0c0e400e010311321410403014800001e2042c0802d03d10701072400344180c20805440c0d0641c000780020a041c0407030600c01c1c2c0c0550500454802d86417400075407400103000000b01015094500c081c1841d0502c4d0820b50072005c03803061055044082407103107550008061254104ca00000b800035540c030322000d45070015286841088011480410001c1c001c0144100030701070291100901a422261414000c20020040c104035800c0c9114555031503a85980c49001000039250226084004805804d040c4032040d0000b01c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 696008309 1250 696007059 696007063
    0x6020c193204090302071a13061b05011a0f040204150810081b03061602102003040c03050f0a020d060c180b03150a050303160521120a0203070906031d 66
    0x30f4900070380c0180b40307550400c1c0c4411140070303d00320421280309080110300503451131190080e08032112420f084620b1204403034011441104401c00a01651030600a031940c2a500d0200010300300d410384030041041d2034001884102c2c40b03540642c000f02c19140d8004403100b4407441c800c1307601c00a420030b9641c1407581d841e41c1e985081d2064201910b00100354003603216506041203055804801401d60340c0300b8034103c0d60080d44545c101200c188429444140e0401d00e030350342d0b543c00071003040c40d9200d180e56440c2906181382c00300e00d2030008403000c3c0511840742e4500380e0f0001e40b03003a081d41c0040041911146960720403004080c0000f4203001c0c000c2c01c030850b200105540d40e42034000e03c003502e101c41e9603140524a42034412802d0380268410101c42c0c006015540340001075a11403001d650b01604100e400b81000d034a0140f071400d80d941020102144212480045405031800108000001c0e205803100345081c4c05034001102d92100042e00c00ca01004600d00c681c00450610361f0781041c00320075240c0302e20598 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 696009559 1250 696008309 696008321
    0x2502030601140d0c23030a0f02190314010219080103240f0f090320100c020c0a03060c140304020916030b130b1002030903120f1306020c193204 63
    0x20345d20200d0301100b80c04030900c100b10322032140440203441054499030700c90500340510300c4042c0c000e03001c02c00d000e4560060240036001440e004948501d20201401110303000c0d5001d500b11840c140407000c0e080000034080e130030b107905030390f440301515911402050102246510780d00410040a894181d48020281c95114083c10b02c00300c08404074200c0420b0801030142c078211880e10403240443c0345043d1b0010800300d00031203c043d0707681c07000c90a03042e40c00040f8904910041c01e1035029155180020810070181e2061504500d030307840b1104003002140103031003c3e000440e0043d4000340344200003240d8000b074403554100d0300b2080c00c000450f02c5030780000c1462101855562083d403135441d44a08041d10b0502114501d0a0305c1d032004500e0003007282d001c2030b2205c1c40c0e44002c42c0c40c1c0c003000c500c0340040c1c200300081c0c40301201900000a8a10ba658070025907410b40041284c2c007494091440d401c000100703c1558064820360071500a001a01c100c040710400810202c01c40c10031070403101e603100d40c1d45900401d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 696010809 1250 696009559 696009569
    0x4050106390506061f02070501051308010c080a060905010e010b0912030f090f030c011e0306080a03051b060405030a120603060501120209010803030405060601031e0609022502030601140d0c 83
    0x42c001403a0003404d026030a15034079084800c0d000317000c0802480c02e40c005010402e640082c60034a84821089500700408801c0d078021000b607500341044d203800b0300c1c0d0000f000c0c2d1241300c20b807109005880e0343c0c4c2c403c031089940a000e00807050780030314010303c0700041d118020300d03a1300f6001c0c140c0505401c400c07a2040c00d503040000701d00d01c041c0001804030304510304444044264801100a404004200c90000c2c1c0710480b107000041031405982070600c5000d0086e40081c000b02001003e60380c8940749444d0003006a4031420990059603c01198880d0000c800a006849654840000c610341080064281c403000301da03407aa00c4689444800110001d452400303a94000d1030041c403221424442481000400030051704441e009520920800010a0001071401d401c90000e0900140600f5640c195406568507814894109410603c1c0062020019030042201c129079409540b94402c0c0010070b000d40034650000607600d41d100000600400700d054540c03442c1c03031000801c03124100d5502c2d0790341403c011195000c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 696012059 1250 696010809 696010813
    0x2030d0f02270f150f0304030c02090f10052206080f010e03130e070516030818070522061805040c0603021204032115080c040501063905 60
    0x309040b10410142040c200c00201c4101c401c80b98400c0841c5600040703030b076480e10880d0b9200011104002c107200300c032109400500300558074a40b0b400c0c0940103030050340f8100d0182d00b103940016070380785103185800d0007075600100709021b40c1d1a06041042d000507403042e040403480800c040d80803050403442044000c1c16864050038001c081080c60600b140c0b480e441c0320481d44c0013042840441ea59403000078098a5a40c00215001d0302d8110044959006510410038000c0b80c1e01048018140c021510603c241d42001004503003108803043c99884032900e110311a0420703800c4900104060071010060030703030440a8000902075646004241d00820009440b034911170b0354506000501c00700f0400840500100d09066192035201c91122580801c01000a010030040350804100411701411190703840e83c40c60400d1109600085110b45822560322580010f4450080003c419007020f000b51b034101c51864841e03c80c514103154081031104025400c400c0c0d402800e501c1c80c0114644c882102c0070490003080 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 696013309 1250 696012059 696012067
    0x7080a0c0e01080304050306040813050a0b07060e0d020c0f030a020325080a0f0b040512030a061811030121080318010c030b06030c130f0b07021305100302060a02030d0f02 75
    0x900101c24000c1070b004503032507400412081c800741d20000b03582908280d121040c070765207880c4941400b0b4043c040da000b281e4030002c0c40c00c000549a003054040d00400307010304802c010203013102d071805507192a100703182070150300000514089450055030a501d401c40c0034054903a43c00190740040d0800060303541003c51f0f41c2000880c80a94400b08903080041d1000700020007000740345031500484001d01c1d2030f0007040b42c1d00c800001030410038244110000224402c3c403941d101c0c201f40c2c812401030266401003d850740848045200c40c0031483c01030721510642c04c001c5910316400d1402500300030a840f40710b40d51418001806c500011810b000651080c2d50079042c046088108e00950350a40308010854420141411502d4503107541e8102203a40103040c0819041e51401c1c1c2000e49600079003658040c0d013a04100b0400000e881c20428020603c2501c21a140ba80b861b00080204044420507543d2000080d02e441040c030043c2031040c000c20030440c69004407410001200500d00a444820b211408000c2d0041 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 696014559 1250 696013309 696013319
    0x3090c290406031b030603051c3011030f01090905030f0a020303060114030402090f13020a120204180c03021c050f0703110a06050d0c050909240922020307080a0c 71
    0xc1c1e0250030b90600d450180562803650311020b69400740300c0d40b0700740340c4420227005aa4150086583c14078643d00410301600d0040c21000300c00c1c020078400d8105805a0402c1c03c600b124070205001c892103180401c078103100c00c0e424000110010460000c0840d5a07210401905c0e0440c01c05001401d582030683c0c1c000d56891401000050007407003a0740f41d212205e6400e005100c0180d4501ca641c543c040700d02e25042c007043e83c550640003441030b0b003800060341001110b04089405180000600e5205000b0f503402c0c00410103a003c5030f07580300031030344018160904452041c001458198054401f2402c0f00c0a2a2400e5401e030310ba0608108a2160681031680406000c000b000001c2c02800e0540604503407212000c0e160000141807442520608a0780c03030f94896940485034094001e031020418050210407262420281c120440201c4d03100c0e41003c0801003265400c0c42c500f8518841c41200f441100c1119074008201c0c0d050304d891800c40807603050213200ca0114500400704540c084450082c030003400c143e4506 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 696015809 1250 696014559 696014591
    0x90f06040c030c0509040b04110409020c010b030604150e01020d0f02070620090904021c0302030a030513080f0a120c02150606070b040f08041a0c0d03090c29040603 72
    0x2540781000341400c03e00e120f030a181d040300548241c10400d45000c2550400c400004004100e4817001000c0700308041400b003141e01c403a502528103000aa0f000300700c9032000d001099a1105c04035801031260f0825056060b040b12550048019080b00350009810072040c0c0d0039010a41d200705040d001c100e80c1c0428014107011550080101e03d031048510f840c0d010b502c203022440d0511490b10141e00499250001c4ee0440d10f5003002d10b1005010744000740c649a9203880c000751203502000321000000d00300300205451082c0c1c44a01000c25520101c99481c0900350350310020140c10014008061181c1c00e1240f4001c114507004035511014558003410303008400e03460b80b03070058401030300d01e9024085c1400300000103200680d031035402903004059100510958075020209201e1034203c20003042517515004ea00c2100c03040035004801508003521303607501c1562021012a03041d141d010748805002e500401c84036264460500101144c01340000700f20051204800c8950301c15448880081e03030b152041003c0c0340712 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 696017059 1250 696015809 696015821
    0xa120f0306030b060d15020304080310060806030601172e0c030b03100e0f150105010e011e1206030b010824070221041e0e0117100b030c090f0604 64
    0x4541030800486065849103000240010401c601507010400e40780140300c0c0c4a1840c254075108042c05640d0307444c25203400e00301900140e8102c0d00001c81d82202088145c094482c1c00d100e03480180003046140e10380140302405000d52010320400e4003496802da030200c889041c9a10518404080c1e408403007041c0842e0000b1244404800810103281902d054101c2d680030a50007000c0080a8010908178240c0d0b00c51810180b6500c50000c0764441c01e10305c002c282420301d03000d9040710026250200c03100a0140113590502c0405003520708400c4941040e2000b0740500c8031200c80711240e81000804c0364480d030b201c401c0350201380c1100d030296000003124100514002034542c0f4800000e240b0f4416400c0000019548426000d0301001940501036410600c04013503007031302c000b48103101000e1107594648610003080322082c0200081540d1103c00852030440e00140500310000d0400140021300e00e8080c60401401d503001c0542d418026a04260b456035034000540740215401e0090140604002c010003040702c035 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 696018309 1250 696017059 696017087
    0x30c0b150109050402090303130e01030c05100206040201081f08030c1014010b0d0f0504060c02010e0d202122060806091b0f0714011a0111010e0a12 65
    0x24403a9005509981c070400315070440f6020b031405615074098030002801d500030705e444105020100c200c001005e5540c000310074101c0b13000d02600c4200e16158004d21150302803d10b07041d40580e01200100e80154481c44281e45e01415010031201148860303c81030402c406154000d0086500c0491001150384092108050321001048100141032180b0180d0040c1e40d01442880300d810000b1507480754500003900500b031243c4104104201c503181c54a00880284607081c4800019860a00300e503031107040002e00841c0b00308080c0c507602d100c40003a0541c0621948050700010060046040041c1881510205c81c108400144581c54907008020503000041015100700da8141c14240810009150000c04164118406544040701c44d5038000c1c00704458444000c80c2009000000750075841e418100d00507000f4035200721240c84000420250b034034203030340302c003101c02e190a00d4411044080d036001d074694580b007100200010510006800d6460300340000c00c1800d8840c3c18a07001400c08481d070195861078102 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 696019559 1250 696018309 696018331
    0x30c05030a03080f18010615020c0405190c0210020a0215100f0b0c0a050a0506060a08060f011401090807060203030a06170c12030d090f02040b010507030203030a09170304030c0b 78
    0x10310700b610700500c500805001380c40b2099852020600c81340c180c2c01c0e1024191030710b1000b0b100040e03403141d4408400c4c4264546c000140900303000c220003482c19000c1c0074010000050700000504045000b00020160b940c544410b43c0b01d070324016030034148180080c080860603600604078103081141403000145006280c1c01507044010003d206541181c0e0445c41555500070f1041c1d1a00c010043c070901d00b2810010181040c807a0504440400c01c1c009820351240b07d013540d4481d02a5030b90f601c0c25a0b1440c0c00e41e01d540744400e910006000300c5040c40c0341c5884010303051501e00000e0350344004250401c90f85170440c80042e0400020000d0004840c000c1400400b88030f00209402c091801b45641c07900d80c1b90721094454000380141740d01d5400c041050350600611824200080451031a18510118038504101d00850030305690300d4056001e1400e0b2409250150061491540c03190646c60051902c2041202c2e04149420030340c0e040e20402d00650720880c4a516100010145030034842209807008000d09200 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 696020809 1250 696019559 696019573
    0x309060c15090804080303090c0109061d10030603080c060103031d09060d05160905040507060201090503041403030f07031718070b0d0204090c09140105090604030f0507030219030c0503 81
    0x1504003214552030a050030400600c1040500d442601481a40d001c41700341c4c40084140004802e012500c90070307034a001d0b255484903039562181580c64140084070b40941905a6407a19450f0400c0c146030031240001d0b06d00010407a46980d1409487d030071140821035682d00240040c02016081100006550b80d9240400108080080064680703500140228091074001d0b40b900c0801c481000041c5501d600f25100c0c0304103135140d4007210000c003403c07242a140340c41031240000d6424018031540e48a9a0050095440e00c0c4c2044142101104040082038061004002c5400b600725024003400055209039190328806c000001520310380100542001c40d51800460f41d0300c0305990008907a004c5070b69a013607050710384240c041d41c007009024641c442c041d55410002c3d44140b05910410b03075815685109554a0a501c03000011526401000f40180e0050010081440230810050860b24454400e0045440303464503540419050303d0b400710f0b1900180304003003007441041130f256140d00140a06070018204 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 696022059 1250 696020809 696020813
    0x80a11030c250210170c040b031614070807140d0e0409020f0d050a02090c030601050403020622030b011805060603040b10030b0103031d060901020c04050703090209090a0309060c 78
    0x61040402c041400d1030344035069601c1e81c05004809989a400402d03120042800b03c0b070144c1541c00720142481a10f1845c40041c1c0c2491100f030030b80d415540e501302440e00b140e94500000c0100000d40c5481d50611940d4650040300000f060014004036100f48461501d07200c0707600d080358010308401c2e002959a0481801114116440030502e070005000b114085a80503103400814041203070b141c0d265801001070b17840740c010f011000506904082c42500c0d207907690b503034244041c26240001d5401500280040000701b000d4504140608151018807128000144080309500308080469008441000d0307a44010403c00030714201c16000f100d41940140601e29210000608500c0006c100500486c4504003044c81600e110054070040d56024620038407558690a000e0450f80f11001d80c515046404903c0c00f0040c18140b0903107050b4041030f0010400944c87c00c0400028100042240c0b081603901c100240142c0e0758034131000e00612203880a03211046040c100149007901d076402100600c2003031200350700 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 696023309 1250 696022059 696022081
    0x8030c0604030810050d2001050a2124050102010c0c0302150a021905030f1e04030c2604050405090c010c0b070c080712020601150909021810080a1103 66
    0xa0700c20b0303051030300e12102d554501240c1164591900f00a42001c1d502c9115070030007140030807000c0072491b218070b0100680e510f030004484600c60810381000050540360002c42035801142444140c0d0070b030400202e00300e007200d0b0f011a080c2410091848003c0000c030420040f9503021f100310f601e4a83e5924024404500c2518080d503202c580c00c07040071841c540300c000107810149641c1070ba070518185800c0d4202045540da4000c00903081074406004011845000ca1403405c5080340c1d0358040666110b81d0b18155071151806d8130142c9540d44191607288000120000091041000d1110f42401c054440c0d100c1e0f0400342484101d034002000203800e0b034000b103c10601a03801c2402100039a500507140c3c01103985c1e09104480e402000c98004003600400329040d0300300442c21624404003659907080310042d82c1d071056900e001e200250110000306c0c444641c207014030f1815400801c10824030500c03108541c0c20040100b800d82d11746a071160001641c0c80c09206a886003030241c1d0104c100c08100c0c2a0442c00c100f10146 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 696024559 1250 696023309 696023311
    0xd060903080f010b220e1f05040b0f0121110a03061502280204050f01030204050609070f030209010905060309071502010606050414040b2d1507110303040315020405040608030c06 78
    0x1981c0380c1721348101820111020701c02c3c1c074007030070040b441c0403c40e003408081080300c0010131070008041c140c9543c000c2070a0074148190350400e80300403c003e0038507600000540342c0310740d4811021483c404c1d41406a018a41e10700511a684042400e500da844884520080072604281c110700c003410b00d0012034405169000a249210302c00f22217a96101d41e9805e6002c0c40d00844d0018000e402031b040a040100034580c0c0e0b18142d048a00a603070900560741c840b000c014500d903003107801001003515806442403051007540500328501c03041c10600c69558032107000844031b8104954800d200e521501c024004c01800080241c5002c0d600d000074046035060150282c9180038a0240d450140c201c0da084c401565241e400c500d418503006030405000520a04203440b200b000c0ac0545042c184180780954080d050041c07104161401000405041c100b05030744541700b110001d0f884c29410301c41404048040368170b017035003001c2c0014006001a9514600024030003a40e90a51111110360400d0100303040c040070203e202c0b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 696025809 1250 696024559 696024577
    0x114090a02010e0604030c0e0402010e0103150902090301140405030c0106080d140a122901020a03050f07111903023c04021308010b190506071509020d060903080f010b 73
    0x40040d004083c8041413a034091940060506c00442000103000d810b9010038074000c40c002e90340c020302d0140d640015000d5440b5903200098114400700104810441c1c6d0b409440391500081c00461903614003040380c3c950b0003040c0c5007a100c58200140d040c2049034244240c0c03004200300070103005803040340307038001c3c1000f0340120a0303107015040000d5030412944034480450314186680d00c100031460046804128030800000300c00d0303103601d9101c2160703210f60002501c0385000c0c2e03142e0380c3c070382c40c004828011035200c0d00424001c444a815040c0c654213950744000041c00342d02d18010391050420302c0c5004000c01c4500700c112145007100039560f401d803040103c03052600d1402c68180102d840741c5252010500030702c0781141c003040030070084102280702001904829150b8500f111505040c0b00401c1d14070031310b005940300c4c00d80c1c0403004210800004a102c1100d404800417080300180083ca140c000ca084100c41d01d208481003a6900d004a080503000104c8a8201003004800c1806c1c1d03040155a092920032900c030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 696027059 1250 696025809 696025817
    0x52203080403022a01140412060902030109022211070209060d0302070b130e0f010503030a0f05040506031819031b081603030c0219030c0201030b04021603110114090a0201 75
    0xe01414020804040050402988644c9219140c40060301a584da20112030000d01030f5400c402901140100f510141d4040600c43c84030203256070b0f06c01004000004c27003280c25549454203480581c0d00e140000d403166840c51009118000844440d008841005a030f0000c1030000f0700c00100541c0382c0c0b00754258401c1080d10310760b00310350729401c051b4540300321503000d50b01071040060700044450001284004550340c980100c240340d2a00505814804000d015080c1c0507882408168451441854034015549050030518501900e4038045040c0341d00c2121003940410342200c0c0a071400d4000c0201500d003d850064030040c198071607030001c143d481c0303081184043c440030300e2800d018049501e0840c0d01d0201003010a161080461802902500000c9000009401103941d078849010039850854800b6600d070740e07000e00e500e907994019030040855000d401c6c0c01641c07d00030340d034038100035150255006000e40c48400310b012085440600f56003c1d0070451900002d40814006030300d8002803500f10990382420 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 696028309 1250 696027059 696027061
    0x5030f0405010b0907020102090f040908191206080c100203031504050703111908090703051011210a06120203030409090311061305240a0c031806060905220308 70
    0x1c00d14054160101030a52000c40c410501c8441d5030158018480f1030026500103103420b80030b504020031180c1c0c45501030100072007001444034078245402d47c1801c1ca006400c0180031001d11000e400c04680254006042c664000d010503d0107181c47d0b02514040500c51009520314074100001c078081d614910b9825020300e0325180400c030601c2c000c0e0800c1c4510b0004224094461580b28440d840395880c000a92010030608404110301c3c040100b400b0084d039401c4401449500200010b110081460002242c000700e0140074070f10100300400064a8140003034180e03400c490034403482c80c4d400c65800303501c190024617180c00e41000585010059904440d50440001250f902030708013590640358000d05194140a5a030800000c2a640743c000340078507004504130f82d10381e1034500745021450801c005161800c61030400281900c3e07229040984040350030724001c10500e0000c104d1700303003190b0b0f2010112003140e10b429040c07000d8241d600c100ca43c8000070140c031510854503031321845100c1e801f900000e010041504 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 696029559 1250 696028309 696028313
    0x6010803071719350f0c160f0201090f030506042109030f0606030b16231218070f0618140105071119140405010509010b090310020a0f090602070605030f04 68
    0x100b25500300c1034a400940100d20966a4a824030074401c072500802100103034041007914881e034007610341407100c40c14014421f11741070b11210b500d81848041241080384440c40440c01c09040306030080150300c030784010841400c20b4606048402896498051340c02c00040105c80b4080c1d0002c403d1046a82010a00c2c00041c8241010b03000391025400241c401141001032003245000b10050034001e202c80ea554440c0289090310b414200021004610351581c818000100314203a0740032641c0c0c100303003161840101140e888000a09104280e070240740c0009000800304542d07900152030600c845d5500524440403801c20703251013802004080d03440d04209001ca981000c004000c900303d08500c400400f960b80c11051420706112024043c010b8501940c2c1c0305003080300a0400c0e01549040e110000c1c000d5656a0811400d014103030005900c26515110b45108400041102d200510001e5841e64800000e010100e20182007002c46600410456000b04401c1045d070354080280e0744c0000122403620150788070345c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 696030809 1250 696029559 696029597
    0x210503042a090e0f0d0f180348051005030c070305090a0b12010504060e0f041712040c0515030702030a080711010c0201050f1008060a0509030c06010803071719 70
    0xd12109144240d0060101d11034003c40703010401b80c5281d403840030f5114880300c1564107a070248001451808049403160070b00c2c11407401c00000101c40a40700e0001c07000325000c107010031108502400b41c060084811300190074015403d1601c240c0340c0c1000c40c81c509002107071107582d2081e0315001e030420902107003078601c0d603903038002c5c040c01044442c41c1c0645038506800301014902080c45641d125500d13240740014000c2070210302521030842c21003a442a5a03c5d070321110401040c001980d110500108240d0919007160842c45010b14041c07501756000b03c2c1068140f0101c61807851615000e03810600402c6400c43e8000102c1e00410101d152443d0240c0750f8403000e031209580c2e010181ca0300d509004c11503a6843d8158000391207001000e03805d0792a61100300502011007454041c0d40200d810040020b1b0031030049810041d0020740300310859243c5814003003c0c6042140a8020501c00e400006000c030600110106410340000f100c2103031407a0480180e101c3d1400303282c2c4500c0341e082c05101c2c001c6001035111 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 696032059 1250 696030809 696030823
    0xa06030506040506090d0c030f08070e131a04050402061e04030c08060a110a0e090c04080307080a02010e010c0e0904050a170a030f0e060c07210503042a090e 69
    0x840303011900c0600b840e1420a44070082250403030000c0c801c119142051b144511450300f440d40d0182c0b295610f441c0d03111012500d0030790040c54901400201d0801c68440c0c0c07103621280720352000c581d00018010511451400c00d10a040000c03034030603410201844090790700c880803500020021460807040e42d07454000051607000310361000e13000211042c0c00003003a0703c011414a2140049034801c0140c85204600e440c450301515101d0f10015a207440109003604000e104241c11216042c8598102981c9000b85491684010401c070f581030408604603041580902031100310a00d88002440018a502402030141c00f401a07181e01c121080c101180a02005000c8005c0e15a08045070b03842101200c0303012009a03010481d02d1000918015000d4503d1449100d020f070305103440805400e080d1190902131050750845070090b42c1b4001c3d8900caa401d9106044000401008540c440039201c2c0380c9420b01020403101d850220040303c41100c20070112075050030301c1c0b5064038a90640010700d071224820103440c25503 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 696033309 1250 696032059 696032063
    0x608030901080c0d140c180a060f031806090804030c06050313032d09060f1103300a0902011209020d120221121b0d020711090a0b0a050103060b030f0a0603 68
    0x119000c240110310240e00300801100030650510b0804510507c107025100c141440b9140004002e00c8664000314401d40029100100016460045110603200c1d41c080384d05e890012501c44c01d0003d0104100040c510090004207400d00703103981545450341a40d41d015480f07510080822040903408040c0410103104440c076415203031582000c407035139401301800c0e1103158080ca1004c180311719405003003240300d5080906851141c6016500308074610300c1000780701c6401c100420070000482940c02031154a554018441d0380b505070b01140b050900d00016204540d1585a1170360b66081c1540900540c80c0c4524220450340d203d0403003c242c0070300e004102c4c00c20803200781e40b89400c0110980380c12582c1225000d0726400d090019203200b41d469101015080e142c1c2c8000078000d00c0380502c411400080c6543c06801070300e014001600c1c07051114000540c1341201141c046a810f6920b8054040030306110f080e5030040c2501b820700304000c07424480c444099000003005d82151141520005803030340743c59001040116 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 696034559 1250 696033309 696033341
    0x15020a090b031023030726030d0f05100b160c1e081203131e1e03030608030f0d05060406050d080c10060501090e040c0e090d030608030901080c0d 64
    0x400c1c01c00c1c3e21030403114140301c0c10b01d0048500c2074442a40020044556010704c0050042031503502d051100803240c010707422250724035400400da240240070305000a0003400d803000000901986a084508200c640241c4101c5405440c040103120760300340901112440b103419400007015010501d0541e42111a03600119900000d00c4117900c0d188290084080c00c0d00c8501c02604c40e1400e12a0700f201e07941c042259001200c85e80c4022a80c0030030303086a40011601c50808204141310400e4907584d9010044500301d0603079845e502904020706a25200380409400740501840c940210480c60b640300340070b40401c1300416a42d44010504903502e59108500070030b0040c0a078908466141824591504400d00f0040c1c18080c2d000310900c0c03603060b4815001907850503101d510140e41490440742e01c5c01001001241c074400c4803000440d081142900143c45040554000c2c100c1d00400ea0740141604d606030302800c06640144205007141e80c00000480c0c1c032140b101c41a03525080340d04006400f810496001e96006 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 696035809 1250 696034559 696034561
    0xd080c0f0316051b06070308070c02042a020708072c010e1812121806041b09050c0409020f0d061e08030c0a08030901061a0a0305090a15020a090b03 65
    0x802d0b09000000019001e0416111903141e10541d15000340221120140e122401701320400019024071007294000f880761400001d00c0d65203501180c120394103045400c0c00c11907a65011070040e02c00220550a5180e44d00c05861030700e1428180725640c00c5203005041514018002109001034a0080c040c0401c0c00418a4262035a407003681c86144101690700102c280c0c501c5550040201002402072448801c0f841c0b841d00e41013540303452100e600d8024104c1514500c00446a2413050001c00c000d82c0618001d01c0703003001141d02143c004803818211f0303105244040c01d24040100f02181c2000755801c9031010751025903140c41604c0d02018520640f03040700106c0740ba01802084050841011000e124022801c0f800c05a48070b11500d41d07a80035000b800c40850b0701441040d8001182240030b1508059045c001080c0140c41f1200b8a0060b4000004501e0903a0089945121690f040c0501031f001150080541100c44403600c078121030b00e0594241c070100d0350700003600b007000707912030000e0313070018603100d64040e8403 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 696037059 1250 696035809 696035827
    0x309030a080a0305010807061209080f0c010501090506032d0a0c091506050f0a0c05031309021c050f07050705100e1005241306090203181b0d080c0f03 66
    0x1103411041c0b01c540043d24040006c25180c400003890000c1e41c07200e450b550070981194154070003600050004842440050003940701e115000e00c00b030b1507141c01080000c245581090455000c030741c3e0081c4814031a42c8500b000200506102c0c012505402180141100d6005007154451901480801c000d282070106140014140314951000200c600c2c030040d0b04040f10340d1410110ba450181c84415990320808000300d503000da000d501503010070740c81841520304007815941c42e010091100e901c441e80b117a800003160950052171603021481000944401c01a504002150208848004201e034003488000642842404020040c0301016a40c50700c060110707a600030011900d5802e003140c86410360341064041802c02210490b040070404014441c00a0789070060108400d1404101c41070805c15942c0f10081012400e030b00040d446011911007100c014070031040c07103510303265880704a5505c00c0074000c0c00f02c0c440d5a40f4040c960305c46030006002c42d16412001411418408580300e104683c3c4070004803100 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 696038309 1250 696037059 696037073
    0xc02030a0f05160914010501050a0207090608031c020c0a0308070504210213050108100c0909020f27090703230403031d0102160318231f020c040e0309030a 68
    0x12489504000084150f13191180000d43d11002240c011003c2054014007565115402800d00340c58140704a900300c0340e513150404200d5845070403941182c0c1001030308450a42c848140c02000240c0c1e204214030f0302003108141a01ea150079400101004210008210000d03c100c081e42c001d801100c100040780400f51101e07490351b4903140400c07030251101c94499288210584201c038100c428440c05418000d5000076940010304101444c0414403428500125a0349000d1011306019281e902d40940c1d42c221206082c044801c400e00e032015070000c841c1c003c0ca041e49078081b00139000001c604010840d0f8100503120241e902e2554180c49070310254900700024141d0540000c003801c200c1b000103142c03403400c8100e410301384c0c41860f840813014451603003041c001903c40d0745000003111202e50000022500c0e121001d04881034016000742c0c241c21807001c0c03c140d140045040401c48100c160b0f1400c104d60311140a034a03650440f54151040b59103100c16031101c442030085442c1c00400400f518160201468410 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 696039559 1250 696038309 696038323
    0x10020313060e0d0c2c060904080901050706022d04080a020d0606080d02010c030f11030408131212090909020d150209060d020c0708161707211101030605060a0c02030a0f05 75
    0x240d400c06401d1041d01410307000d1401e09018520180000f040b03a88d0b03c2d02d8485243e030004000c0c1d41009010001c1e80e001c1415403004c5c1000c0d42c440d14656003c0020741c00d400070354201c504908103032080200410811010300103502c0031016810b13034660314070a0440c2010801400d840e80510351a014800c03c5e2040e1590640c0101c2104203103480c104001c0030358840b10400c688130340c10b01158282042000ca030100d121180504411074000010500d480c1d2518107a8014001c400000c0300e8401140040064083d003021000d800740c0340c00c6c8800c0207840c4482c1c000456042d00040098a08014002c10f482001301e1074044075100c071070241c00a0359401749602c01c10000e600982d03003c2c095001351240455140c00108044180c0014880310010182c24590756442c40c0907241109002c074400c0940c0041d04441480c9109000c0c0d9900301016106045428002e0f0b03491040c0308028101850003c041c0129958481a90200505480c02a04e5002c440c070102c0e00d84910081e0141841c2c240300404002c00000042032 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 696040809 1250 696039559 696039599
    0x807020d111207120204021b0703080307090b0913020703020f011a03070f14060a18091a01030e0717210405031b03070614070f05060610020313060e0d0c 67
    0x1c00b09075440d400303040d403a03d00a000e030120743c0119071900c1000d460250064051040070f104185411245945002e01e40542503004494040001c82048445a04000c400006007002c28034079203000d410b8800148660f06042c843c0c2442540440c1c1c0e9014180b00300f01100c039608031b00000f003003518910f02d103000b8080321501c52588244a41c00d00400c0840e00401d40d102100c10039400c1e0000c2e15980020062136400001c094010010702c01e00032020003550205680c02800610700c000380c4000391040e10308000c0044036915041c50304102e03111a2032400002c40008884600c80440c400812080180b41850049600e01c25980322580f400c80028001c28010012500304404950351420030348041481030300e1450071164150400f4508200303090144421440310381c2030b006041c4c9040240d13a20034807564640a82030314581d0001c004c000050030f05c1503000c3c0b1840c5541c001181802950620305064000c14011241048168117100107144c030344045e41496070b83c0c03110302c2d40700441d200c1030210110303811070781030b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 696042059 1250 696040809 696040819
    0x60803040906060c3203040e04020109060309030c06110d0e011a0316180603020904032a0209041b030c0801020702090106170a1d0f070e06061c090807020d11 69
    0x700003801e5004071444807015034411107502c0068003c04011411604180717600d041e0740b4040b410804030032000d200500c00b0340a42d480d00070043c1070500006013041c0b00b50b000a0181445d1034410b00100c0e801c4050449003950003040070510a182004241c814004c840640030702c0f6003080011110301d01c06400c500079040c02041d070488079009140400d42d070364040b0135052980c013050312410303c507010004000004405510380d000c07807030703954130750225246810403078064000880000d5026101c000780c0041341c1c0c107174600e50f4a01d41c4180490b000143e10b1072026100400b0b5840500d8644d02394401500e61500440c0c11449410800340d41d903000c94040d5120b100100c1c40f4156a00011a009000e42d090b40613240000712407504680d126180baa00505d108644280d41c40d083c2c5103056000d0300104020745a20401c1005800b00c0d52400c120740951001c0a0701452096400380030550701200941c18a40e500c0601031008111f861260070042941c1c0f064100194210301025a03050a118840744082070080c02911 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 696043165 1106 696042059 696042071
    0x12020d120f060e0a0213060305070e010c05070f061211030403140a02100e0c031203040203190f0c0905150a08060c0f12090f100b310608030409 63
    0x200d901c80c540d000070311100c1d46d225901c2e0300f1000b031004d070070180520b0600316001303444500c002e0109410408134407802d8007441404c1203400c00800300d1101502455459510080c442540102e242d11441e040019046584032090222841550140d90311580e206001c1c0c600390b071780d5211883c810110312400c104094121510320030440140d941c9801001c0500c043d1042c0b5050003a0324201e0000c1000600802c00542c4020941d90030200344991080a035510500c0c11004407048804040c2401801d1030020071021160341c4403500410881d00c211404041000400020840a00600c0b032907400020110301c1d181859800344c1808110805110300344001d240c254a41d0580c1110400020b80c001c408000c0203440510883c480100320300f80900140907110f011502c1e10b07204403028031b281c90091143c25090040c440345941c40e00540785090200325581d0b20300075903c0e005070040c038152030325150b = true := by decide +kernel

theorem cover : BRFrame.Cov 695863309 696043165 := by
  have h0 := BRFrame.cov_init 695863309
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695863309 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 695863309 ≤ n) (h2 : n < 696043165) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
