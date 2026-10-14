-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1517
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:21:57.342178+00:00
-- url     : https://prove2.me/submissions/9791fa7b-f3b8-4bd5-b51e-1ddfef01723b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 272661870 ≤ n < 272841726 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 272663120 1250 272661870 272661901
    0x309190612090302120f07020a090204050102010f021e0906070c0e06131e0e0f010f05060907080c03191d0a1209060e09060409020d1202011d0d110c0d030e09 69
    0x3e8090b80105088500011025004004111150005614004050780030880360390303103503118901007503020809114941e420301600c60044800c0c40154208202039814038041102600b24000e0304200044001c407940761328042d108091303007100e00414000d54494000c0c21542c0220b6006200c1d82c110700c0c032111032030000c0c4240e4280f090b14400107501e04065107640350091a401711644074070f2055000d0031803004400d0040c040c075803480d0100810745080032024000d50120290240050140b0ba4040242180142c0300344e90340a4140c120788401600400d6501c0010503012410941850400d5000040c1e09000100e10480502c2007032140a00740c2c03444800c441d07038560390007000000303845985544500c0c0f0709040c0070354010744010000141a4115030005801c0304400390b0071a600c20803002860206038081c49400741c0a560f48485041202015041d0350700d9180001c02070041c01807035a007550030044200b149140000740500310403031034500c5060207402e0340044100148611183c40000354010a43e8a00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 272664370 1250 272663120 272663123
    0xf0103091a19023115020a06060f0503030d05060613080c120609030403061a03010221010e13060e1f02280207150c0602031e15010f11030919061209 65
    0xc0030015407401240140c010040601680f10b11081324001c585a5000c0034030b031004803601d03001020291014605207041d60066804024101c10064040186440c040200d032016044c0d400d00090b40d0790355000040d520f003c0d000c001e05044083c0000030440603400590140d200c8400c03140c3c041c108a40120b46d599a0310200d58074149030b08203100030800aa10f6070801c1307120008500f040104400280d000c81d08a030090307607642e4024041c901c800707a07001d4004065207000d40000302c0c00ca0381c1442c00c91602c07825003024820080a0a0b074514201050325810321042034040d80c15040400c0ea154840e414a029421010000c48590307880250352040514a4000011004040d001b4100c1c2c00d01e0082960119040410200c05001a4807080000124284000c6103d20860011480705020748860f0410740d0000804807414100d0300d5081110a0381c005981e048200c901d840c1003200500307241c56050541c011060420303000740c0c840341541c00e15501c0c011040203031502650b48241041d0030500450550b18503a40 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 272665620 1250 272664370 272664397
    0x30609130c060c021f0c032a080d1b08090c0a080d050c10051f060302070f020609010207051e01030c0503071e05071506030506100506090f0103091a1902 67
    0x1c04101c01e602031850b2a40d0140001e201c0650b1800b85104202c804010990100004483c84440f004064200c450f0001d91038011802002442c00c0107090b0620310088580901483c0001c5280044007a540e00440e110161102005400001c4c41a0141c0340c003100359543c840902400c108180035041c84500001200c0c4400010507038881e1007442916264000c2400d034446010700d00c900404222a8007840d4051900310600080980d10314841160400c455003140080600400845020644040e84e1f02103542d0101d6840c0da64009000050307282810650046400c81001000301004000911490301025800e881c00d201030749818804840707510045540e100483c0c58030540d4080c22010104100ba540f1290078654a80201600c40c0d40d21841e11803a4140510b8640c1c1c410720422509011841d00503440d110506805c50a000004149008038442103000d011200c039110342c0e6038400c3d005501e0094200c0344805422000200f645110303e401c550102c07401311400000614103a0328030890300b00804542 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 272666870 1250 272665620 272665643
    0x524070609020102010603021905010f0306181d010c03020309010f0b01050f090a0b0408010c0905030d020c150f0309031801080606161109070e0f0f0325030f0803060913 74
    0x15a180c0040c000014168110741d07031030b01c0120058444140382c0c07070b14545c9a0059401503142400061100d00802614001c15041c01810800032428140b000011404080d01051029011100c110f0008120326030340000c0d03007441142e21145405600840c000c0d9000c0c0e0007407048551a4101c28180c07640c0e01000741c0004c0003000026041030f00d06010389680c550040034070343c40c01e540b142402c0a5800a402405440c0d54a4a014400d2908004d81100404e020380142507140d940c414080d484103141400d20780108003000743e802884100c2c0d0700b12591445401080c60712410403031241070b038039000071124415545054058400035130044501e2442143d009103074500d0184e03102d0300c05244401c03c0104840a00d29001c9240f04c41d80c4800c009031003104147da170307101080c1c17048080124a035100b10009001c0c4000f1580c0d2443e5031004928600c00c06000011801840c21080e0410340500b815407020303103402085800388003007001f800019401888100c0b0380c4d907155107406214060342079400100030511014503 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 272668120 1250 272666870 272666873
    0x50906061909050403050a03050702060f06060f0c0703030509031b0901030609050c1f0f05090303031512030a09030b010905191e02160c1203140717070606052407 71
    0x402010030500c6294404000690b03655000020741c0e0040c1c134100c000c44c4000c1410765a0a60510482c3d83c000c44502c01404076042411209008044c0580214015507000600d064468000d104035002444843c003110500c0f680c908004045402504045110b400340032104006800c44610b03840140c5001000c8250507440c541e01c0d0402000383c100211440e01034440385010035680e945003950880d10058200030039540035070009007621074041c101000d004050040850301d403000400d032940200320039581400d01c100900000c0300200c600220a089101c0041d0b0030340c450f42d001118204907403241503014000d07600c0b50400015558203c80015a03110246c0c1e4080c5114119088084003a20468070021049140001c4c682030340d00064840070800c4520514174200140c0d01c40c0c1030000d01c40c91010607244d40b000ea4005202a45c0e00084512480b400310f01d01c81480302d074414500e04c001a81e003465683d024203251000c0905524800d030391250390041c03117044501d04240d1600c0054a155a00d95241c034046 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 272669370 1250 272668120 272668129
    0x2306070507032c040501060203040e040206160c03080d05100302060d050705090d0f1401050709090504051204031a062b06020f07050a110102070f1502010908191205090606 75
    0x80036030800107090b0fa5410022078903541c841440a00b0510b03030402d0348104040c042560300603448002103600c2007008124190300d280440750000c0c0e04032200c950355504e005d800d0044000f40c50019000380d91b455000410002d9100080c440b6941c0c0b56401d120f1070b903400d008118400402d21000e50041c4040144001c0c04405510580d0b1110316400c0c8181415107510110f900304500750002c40340d00000c07043d030300d040c02201c00360307180d052040c1d000030f1025207400e08d030081c0b40503014441c0702d031091384a401182c20003d080c0b02c020050240540100d07141c44c0d0b41c1c02c0c05d4000300071281440a4100034880414400c1c00c002e12200d1604a42c038107140c6040b00b401760003c0300480d1011050719100d50078000e000484c1107030402880301a008000510111030b42e400c016040c0d4412140082c10f41d4010a800c01c0213010001016085840c2107030718a0183e030300600140e0140442410040a5181c002051210101d000032980f000d103102e950b600a40400180341d40080b980c1c15211507020713512000001d14680350 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 272670620 1250 272669370 272669377
    0x106020c100f020f010501080f060a0501030c180b03010f02030f07020708060106210c0507050613050705040902040902091f050a0b0f0a090e01030f0b0906040b0a02030907081923060705 81
    0xa42d0f204403100c84004949103401c4038020b800c60110b0b50002c0c40d03010b0040c4003c00c0f46580102e16076104000c1c5514503544c041e0030744403a218040b02caa0001365250502182a0f010307034040c1401a0013030152130140240c0b003009500880703140710940d071104040f8580910000f58401a12405c800821003a401c250050b102c0508141d54034010b01c55000407048022150f0203240303100b00540e00c0e020307140c030458a05141000c0d402000c2900341d4000e001c0140110700f002039110215002900c0000d050199400458040c0c4640c55019400c0440f2105010b021303007030031094911201c61000441c1689032217400b0028081c0c0c0900c01d000101c8400d2000040c1d40c0114001031106d0071050070259071844d550171614046d000d00f40c3c01620002c80d100c5031101800748a19480d64411500c0f40603000502c0c2685d504111810b004e40400c0c0900c0c1d01000003031030940108207400c060840c4000302d8202904481c80a0000068ada0003106c034180586501c130180c04030804003821050300b00020700103c0c1c0c0e03400000c403255003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 272671870 1250 272670620 272670647
    0xb06100206093408060a0c050304030e09100e10030b0601030908031506040510050c0c0f10030b010e060408011e0209010c03050d0f1409010617030d0f0b0a0e09060106020c10 76
    0xc903200301c007000103d640c1c2c8800300800504026107030501d040c0b9128801c50b04800d12450900204000304000a40c0c4105040b2207500111600740c1c40e521005224003030500c0036008419100c000350305000907070f2160705d54403080360b202c3d122060b120764074600110300752121080c00500311513083c400700d1001c4102c0f203550070000c0d402814007810aa9103d0024420542c4055503c01161000814020500090004171050001079071901d52503e02080441c03440411401000105035482e00d0040c942da2052098061084008106d03548958441c0c01d62402000754a5005c040300380f1092a02d50b442c241c500989001340341c142c48050050510ba1020307200e0b5030101240b4464103031380e07220405000400c0e102e4480e00310b1101440001c0d500d420f03480c9900f1511184c108218407480440c1100c0600000000c075085240703c4100410692008034100c4081e22100900300d41c0701881c1c0d500461507641100100d0302c0f40038610207c440342d0360380b080240d889080610a02d41c20240b82d09020440074004d034000300242 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 272673120 1250 272671870 272671933
    0xd03060b070b060d1209030c0b0406050d05060103090507090b0315100303050a02190f0b06120709020a090506040801022701021905150f0106090902030f160203040807030b0610020609 80
    0x11340e25540e520003901407200310034010540c4c17000c0c14424030410300040405044481062032078241421005051406082d22881201d17440d980042c503d0f9109410064080350300c501201c8046071035106d1300c4013030301240740c0b0907019200cbe524008207480404032481e40035a80f05002001a01e003152001c6030b80d54402c00c40181988030718041d00c504a20415560003440f40684450301e40000540390034048420301070160341c4a08060380c40e404c00d031000450450129913103070000603a5a8811001920709a207154030581d80701002084c0003031900c4c0b040d00104440b231655183c1c0100c40e1300b00c1c082c8800038210540914010781c410001610b801032403109009125015a00f16099110071401000c0805000c43e255a042c80c0000300411642d80c0085641000c1c2007030700c005509500d484101c0341d003000402040020080c9551804003000c5009004580250403640c040e11031046d140d04000440c0942503514a004a172854110741010b44085038244c020716152001d032104c20603c002b1503408c1080c5d000c5d002c005 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 272674370 1250 272673120 272673139
    0x6040c0302040903020717072103020714030a0f11010e180a050a0e010c030902330307230c0d090302060a0c0503040518090c1804170d1d0d03060b070b06 67
    0x52516007c00284100d1488020001e0500705010ba0025820312040c0f034103d02c0d1011400350029401049120688080060a1900a0590300000d1800c031203044042c040321102c8102e8003c0c00f80601200b4240c400030303290703071841307000a0f420302007040c10401c07054040c1041000455104147c40d04a01d820000e000c401040b1545142e5202d421180110a03101c04699100c0b401011410407485003d010f0881e24070301d800150f42c00c00c0007004031100003942c01d1603138000400150b0040c01031a00010000e01c04007080302da200c405c1940d40b9664040441c441c481d2082c1e0000031026407150888905403a400382509040110110701554600d84c1d042003144c20780400e00021a40341c850800a510740407a011141501d03050580a09050030f980030422406181c01c500903100001c458400650031583c0400c84410200403900713016040d00032600b60782d4031942070035400207590300941207948500d44042d0076240f800440900c00e0b01100e01d07902c1a00d14a5009002c00d40108100020403a4096009007024a4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 272675620 1250 272674370 272674379
    0x1211030c01052a0c0a0b070611040b0d0b0316060903030e0303131418070e0123040b070606080706090302090f010807120830090109020f040b041416020c010206040c03020409030207 79
    0x2001c0c900790010406d02c2800b0802505210540c024400251020403840380b600b81002e00004261042c0d08900000300e0b12180202030300e440c01c01610854810342d102d800811501c40d000180303032190910090700090010010320342c081c54048200e814051407a80107580b020300c2c2001200b00440d800c11110350001080b401c61900a50301d040b80b0340319030900c0e075805140c1359a00c4009455002c400008204050f445801140d01c00c80c06404c590503140032025060329543c5c5480c088010b041c6940081c0f40c3d5014200740001c125400140c0d410a8901c00c680492855588a0120904403001d2185426503031040358100982c1d000c405c200d01342c0500030b060311850107440c0740d1040c605912a8048644440c410104420141400c0e484141c01000c400000c2c0000304140d000684028615400107104a9a40c40d05020641e2964016082513010442008445c9001400172140aa08410460160080c0382a5010a600c0800e1180c402d03540504000c505c41e0071a000d2100414078094101d065120700340340804d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 272676870 1250 272675620 272675629
    0x9060112060906080f0714091807030c0e07050a08010e0a020c010203010f151b110a031401050403090614120a1d030904110a1e091211030c01052a0c 65
    0x201520000201060f8030346080b030b0031850180d81c68031115060304001c5050010842c031103411031595400310303050542d0b51110061568035100340c540a420030b118265002003004006001d0f0b50445004110040455883c4401683c980c403410500300f00080c3c4000041c0940105540301ca81c002a0b07841c03006041007904800c250883e4002c1c0c2100d00180c1c5000000c0000c2500409401c2c4800003610781201078041440812110118101004290342c1c6405d18801003030704c880c0420700c000c5402c00384c080e01444c8010003240c02800240e42c140d0009864650114080303001e03282c00c4800c0c001001d0150318161100140103040100074140005894131034004400100740c24802c400050f01c84805169500c01c3e100c2000b04032003003050005034006d418007401e040c094100302a0f0b04d2074100000849909880394074200d07400e000304e4000d000203104c2e0104960a01000d11141d00950b0015021103914800c0000190f0307182c0243c4070b103040c1d118801d00c1524140e801124600100c0813030035086400101d00d52001a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 272678120 1250 272676870 272676881
    0x6030f090124051203070c170c0406030f03031a01211d0d0305010f050a120507081e0601171222030b0403020105160f18090501080c100e060909060112 66
    0x9010740b01c07100000b8099440c08101d00040c1003002d00040d89000c22035540c182c032054442c0b20700d9400e400c25840c0c40c00010300c14000c0d904030b100020401c2080648900d0100500004002c040d030009192811018000c19503003031031000c21034161203480104025170400701c2e13601050385d02c00000c9a01c03803e16400390b0544030f0341c446076a0311840103440320740070a2800500b203500590000d0481c100054040002e91a104400b109584403e01005510722840c2031040c90452140d2242809101e07416644104c01c00e11101030607014084000e817109030f6642c00e0300890154440d0742040c07181d04988017480442c0f038280014002c4021400700c0c4684d000c0c10b000110380d0300c0070940c01981d4603c0c40300304002c00c0590a106041c0d00c4054004a02c101c4848000001e1403010101780da201402000c82070f01e03c1c1c40da0f0183c0d42c40c005041024091009607110908203898140c507442460142c5282c0c000120154011400840b000901401c080d00b81607070b076001c0000000e006801d107418000c4d0303074a030201070301400d0042 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 272679370 1250 272678120 272678171
    0x70204060b0301030203060f0420061c06050109060503100902090d060204060507060507081312022506080702210304020f090a090311070f03150204050a030c060906050906030f0901 79
    0x166803290b04d540185402d094006160000550b8101c1c104000104e20400403910500a4050b05001c0052030740402c50502c100e59400255920510a20301040d91030b80000041d1082a6540090595100070694880c002500c0d80c1c015510409000c0c402880a54003400c160f240040c0b100c4c0e0300c0b000c00e0f11200c040341c2c015008500003c4c2e0000d000014441a402041d0b08107074145400364203460300c0d09002924405042d0000c0c00c1480010f01e40f1741d12442080f08816054801d400450100c0407030500001100703c0c1d10500f40030900c40c0300082c1c00c0da0700100e11700d03100c00200c44000031088520b68854481d9400200100e0380941c00b4042d40368140c0714480c40c188a252880c10026421025090150001d5104200c00c1242d5110410502044054a41c03240840c0d80c810340d4101c0c902811080d2a0103809070f80c0000b604000041c00000270310103820f407003c0c100d62480d02d900f90403e403202012140c9116103141203405c50000c00109040c03814510070180e00580e940000540c0401d21000362401e061403594 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 272680620 1250 272679370 272679389
    0x629090405041110032009030c1020070f06020d02030703110703150f06050a050f0904050a050f03030118050402012a1401020d0b030f150c0904020a03060620101107020406 75
    0x1c0044034000606d0108106034006541241054030000001e0303542c1c1e48801d0a580240c1c0b11880484449000799002c0c2c0141c1c211140007078000507852001c0340c0d50b001c24450f94a000000034030001742c003030000c80d0240c1d06911aa024600d48070036030b00c5c1616101002048151144240c540001c00b098100301001c08400040d02d010035501c03a00405101036412a8000c28801d12501e90100890f80d40c02200c10040801560b170036150f96a0b6042143c10b0002c2020094264025140e030b00c0056074010008506844642e010104070b18180704d00501100e4040741e000b400304074007043d01083c092446400c2110030480780c05040c04443e155450200042401150140300d07034020a6001070f901d414000c00034401d030290014640303403240001840d5900a040e924000412079240400c18080344401101c0039030b80042d20070340d503072102c4110080003000382e88540c01c00100050401d0010314007085a40e00034411803001024582d0030003540c00010310a4025502d5882410024100181c03214020200100400355 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 272681870 1250 272680620 272680631
    0xd030f020a0b2503151a0c061302032a1e03070b1917061002150c070b0606070f1506090f0905210708090d0213062909040504111003 58
    0x424843c0e501101241d8005260400d449003a0072484406002c040354035034052503450f82082d51014a55200e21444035440f4000e030303400c1009070000240406003451095085a001288000c41090540450303040000c468080580084d5107103450f006130106400b4020808001c60060000649040216840070310341c02c1c0c01080302081070054040340ba40440c024181601c400303002040c503200c121002854507200b02000480030034036503c01c10034203684010898000300c050030b00914102031a000110b04441c03071901a00000c600341040810f460f251544140342508100c1c1ca95242010b40b16804008800300e90b4070900090070001d6409010a0303090b05000016070b001c02e074201141807603c1c2c0d8008204405000601e03500d1050382c101290491a00180030076241d00c0c1280008020b028001c601940c4880072003804444034415a01c2281100c0307640b1010180c2c1c200c2304c0b10703180d80b54407110001354131840280211941c0d401c2540004c0d80c46440b034240342040e02e40c0000001e807550101146100080da817032 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 272683120 1250 272681870 272681911
    0x2a12090c121f150308030403051207050f09040f11160c0f030312020a200d020606091003021c0f03020706090602120906130306021b01050c090d030f020a0b 68
    0x1d0a80c11036481d254040c155680c00b01c0c52252401074603115000b0300c00ea403119001c000da004031400c1c02c09164010340c000c1d0b0303030305050078000c0c250b0700082e05000003050040081140139009100719603a2100c0d0050681c101240d1004006c001d1108500403280240c540c613141d004820814000d1040f054903144201362000e0508000115132101d800c040310011640c40c003403020980145a40b01680709070f12000da6100045c403011244c0700451441661311f06903860081e2800d1310003084c502c40380001d541c2214895980c0500f08680300d41d054620442d49440390306d0500c09420141504440e81174003507000909900d280d55100307011038003048281c2c010b800610041c09100c0d40102c4510040c070452008142880c2143d03040a5103205176030103184500400103079240700c002c1a48a131402142c001c28115101d5604602e0380c00c985120f22144e02c01e551034040051803403540c083c1a60042d800c06400c41e445000b01780d40c02d58654064230008000e51080303401c21000205071035806880303403000308103600000d941d4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 272684370 1250 272683120 272683129
    0x809030f011d1e070b18060a0504050906010c020618030307050d050c0d0207030b150d021e041409060112030512042102030a020d1b0606120b0c032a12090c 68
    0x200b00142445a00c03000d440703105000000742644c1904c107100d00d40344e51082c0f030048038905014134901d801e4000d0008100d08012039040781c050b0040300c006a07210301e110b40e0340000440d8079441d0311100952008040c030015082494165401c07510b2034002d002c0701c2c6029150b8940c64507220010b00550000794001500c035141d0321041c0041403071402c490009004c650b0859031b541501041c001e00b207010740700c1b0325420034450f0b0351404032440c40c00360054409054680040080300b60541b400c0c0d00940621b08011000e00c943c114a6030a5129141250280c24170ba4240001000d804182010070340030801c0034030030401582e690402c05030146116050710b0080406503601145841c90381c13503a84003550420300c4144181034001c518504010072925081c13101025041c3c242c003120600100281c06203103007007404100b01c9501e4000c060168002c0e8000e10b0283e4035485528068070084034040b080c2c0c0c01582c8100c4940300041514180c20491070f03003c0e418180109c0c100c0d07070300d4402190603001d554862280030304035050 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 272685620 1250 272684370 272684383
    0x1204082d160c0b120f1503031602240309070e0903190504090f0b0f030304060906030218040e01141f0302010c0602040816030303150e040809030f011d 66
    0x41200c0e00d010002104003044090380034650034003030101d4000070340104110b11078461001816034400c0d810f84501a039049090700c0d0400b00c0e105404403142c034010407070030103140314000d1003d14020011403800100c0d21030051015503d0b0412a0444172400d52203640c81c20104542200c0001303070f11081e0700d0b45441c40403246005029403180e284041074a06200004d18040202c80194603022900c0c0c0c0c0403034205504894a214940c8285102403416245a20a41203508950102c03801141c2518002d950041015224031940c4504004504400402c2020301d000741c0151408207443e0b503100c4040035076140403d06441d000000030310304c2c0c0d5403400f4011500c4a100e00143e0400c0e034142d9200264030510a0100301e8031803a02000c0e050041c0790311042c08000254048a011348032541c166400c40300c1e0240402804142c0c2d00044010034107141c05e0b4141f00000542d03820446214000a0a0b10703202e5484001103548018400e0350940100d204840c3d030340109015421195540c40000301100440264060402c070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 272686870 1250 272685620 272685667
    0x1201060302030f0c07030c02030f0106050109050316170f010603030c0204050f1b0904110d091403070827091f090b0306070318061a12150403050f120408 67
    0x107105005014151000750035182e1320101d40410940d40c0c01c0c030741c01d068520500c0c1a400030340c180310300c0050840301702d0103400210444a0a0300c4001c101b0b51101e04140c0c0300c0b000e110b4103044509010a04000c8030f019040d05004650010301542d2040c007200c06d4031403d40c1c1d503942080e40810300424201003103081601c01c080c0e02c421031942c03000442c1001080750000c05a81154030b042c060b0045210f840c565529031161500c01c00c00070321266141c0030812580c2c040e01110b0fa0542d0702c52803e1000301212000801103c890035401003c482ca010048581c0105c1d240c0006291450a506400508429100c500419012380c0d04240008210240016644071065041d0060640c082c1000030130343c805c1e14002803594008003d400d000c030303030b954001603000c51a1740c24040c050309036410041c60f0200e03903403002c105411046055401c26192192003084d00da035441e640411b00e03003040c4840c00003808a0710500191480150035070920b450281e210140b088a0350068a007911504030008200881031480c84030780c101c40 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 272688120 1250 272686870 272686877
    0x4091e050703030e10020a030f02030d060f080c01050f0409050c041806090b030a020904080d09050a0c031b05010206130302030c0708060907090c090303050d11040803030711010e0d270605120106 85
    0x101c013170b202c0082d1a0f0301140801000d01610703007a80e0228900920584d030030420a04c0081103982e68400345011280d40e1449004818021030038007040359403058080320813624202e1425880c1c02c0c0f07405441001404000c000312461035050201107074084072140c02517424420800c001c0340d25400e00745101c0c21175105000280c4241e200b81c400c0b10050f15a0390b030701c0c2c2e80581c00858443c0c4031454401210045e208034803005003540100ca60761800c100402c10402c4c2503d0003030582e03040003c1358a00d020000c440c0e5000780c5000d64084000907010a03031249141c04003a10a2060702d0500d03a49100303840c58100300340c102500c0c9030030150820070403100c00c01040d002004c400c8820f028504400c04003030100c80781404040c04011001030408810481c80c0c002c850b002c113083c114541d88a694020b09512a0825a0844d0014001d46150112750005000718610100840058046540c204801384c5d09076510418010b80750381c07480300d1592058032056411000742405c0e200c0701ea86540c404501d1204030030580040c81030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 272689370 1250 272688120 272688139
    0x20a0e01050d1104060f0807060e0405010f03110f030d020a050c060712050307030b060301030c18090203120a020c0a03080c06010806070206010303030c020a0215090307080105060d0204091e050703030e 88
    0x50390b1510680b101154000760315070710062019000c6800340c02c4a03003140030540b940c04d46c0020b01d124002aa0402c4580c1c55441010280c43c40080000381d407000c2c4104542e075025850b0600103e030314080b0758400142c009100e200010303481c1c40404c0c10440d150390700c13501513005030260f2400e020003030201c4261035408880700d07031800039244d4400710702124010342542048000b10011310154000d6102c0d02c0e810300000c1115403250381d245090300290489019003841114440c4040e1401441da0080c1900958001c024249110030441c000c000c94101071a040214800c88055100030340f25140c460f4091402446090f0352081590066440e041043e405820264019800c004a40b5804514a0f040d01d60501e030201e40e80526513002c0f41b42424401010354001031050304080301d46007020003004026416819225107a50381c80d0940c1c220742d012119146c0080000d0380000061406502001305107100d1b034420320204071440301d1003140e600c0c0a8130858096000c0750040c800c0c5504204115030002c0103d0308a0403 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 272690620 1250 272689370 272689379
    0x3090b010608041407080606041a09010e0c120114010e0d0309061404031e020328020f120a0b070318030e01121e020706180b01031212020d09020a0e01 66
    0x440a8051250204005440001ca41007000803140304030000380c024102da202e03640b00c0200c96165901661440c0c0300b6072401101045110641507a0310591500a101c104281c0c40c248003103014450041a00c0540f9034100301800144940d252030501070024519031030014880040050094024056440d02c9440c2880780800001d0b4000da24a054984900d0005840d10b404002d40c1120300442d04024010f55040c0e90781c0008500050902c2010360080302101c680321051904204040e003200b8810302181440c40c3e4101c090b0411541110003540080c0101c910301a00c4909907061145084044842c1913581d005e0040c4180d0500a8010550743e03008204240600f698000d045100c107140114103001015003403060f64851175200c2c030441d1541c081c3e022014600220110000c0d070040004031001c0389080c1d5011031800c412000c82030807550210604000b41d0840d1250030030900108159820072440680920484800b4009411050b02c0c0c4840443c2c03400482c810003400c40019040160700700c01c0d8200401 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 272691870 1250 272690620 272690633
    0x6120d1d18010b0706090f050123100905040507050d03090603051b220e130c0b0c031e040f090506090f09030901050d0608030f070525030305030a091713060309 70
    0x81c115101a80e15550b03442640ca0170202428141c40003805000d5100486c0040c0715040d04940300d91869500c00d80e40c0342c1300c40d407030031148200e06491400c110004100280400c01c0d02d90b004a40040c0200122081c4c15510400581d00e540912001c40c005a46010300300282c3d6018010305401c5004d003000e0a9890440c0c100300c6580340034420554510030400340c41615138006004410001d45038400e003120746442c03d101e0002d240350001104648254640a001894510b0b05082d26229030904000c0c40c03810880076991040104a282000c0c004202004001007a14506100360001c2c00c1211010800d46070220401c284200024600300035030380b5910420500e4000442280c03c904801d090858a0302c04845441c801040903030043d0309280300004000b0b2503050000c0284c078859100d40115042940820307600301443d00380c3d04441d4001102c0310380900002c2c0c001d401440c2e100c4180c1900165280700d94a81603040e1486454007203400f54005004101410700700c00e6100500f08600b001d0000890b15a90744 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 272693120 1250 272691870 272691919
    0x1e090612030f0509040e0309030d030504050a0308060114030a0902010e040b0904060e030909130c05150901050a050d022a07210c050d030810150f0806120d1d 69
    0x40c20010b0080424509500801c01c1d2003032610040d204028000b00c003000d450382c0c4c1e407150160703030710a100b18043e2a696503c240142841950b0200203403803107880d039a5090341c4146000c0c014074140700e048e1500380400c40e090310146100b40b020b24408075000e03226000241070055070044080c0a04d05141c0b4101c0c030360f00c40a940391340080d4040c60008840e1040d0740c8240c11030007001c102aa10600c43d01c24419441d00869040d5052401a500c80a00725074800402c03103417000500060102c5141032003801d01c15030003900a41120301c22410041e18103a164180b0f00100e0f401906070041071080e40c0481081c00707240200240361181920300500c8078900301103001d0700d4000032403a43c1c4140d12507021345004104c0f5010789807004000240c1204c01c0040b0601c4d0140c800c140803601044401c0b03002c2c40c00101ca425400c2040e02982c401c1c2c4a0f010b22807203001048445180013405242c00461070101050410400c1200e4250b040c00c45e035610700400d441d00e181d44031a4441e080c0311441001715240400580c00d100501 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 272694370 1250 272693120 272693123
    0x302030f06010806030c0a090518060405250e0705070c0803030702031615050c04031101030603030e0405040302010b031c020c120c010c330e15070c030c0b011e090612 73
    0x8008580d20080002d140c506d810000035000100c1e4000080e819041e0340040e0301a202103074408100010058026540e10303000c0703501410560103800901c2c119584d4095800702d0301c2d002901c0350403c5407104104000d104080c0e0301c04001660000c0d4180900816140c0ca801402113a005140b540c140340000039528080c41400000c2628400c030a0001c02000880c5021030544019092000345460342414401d80c00c244029901e241e03c034051400158070a06c1000203880d49901e4039122031041406000c01440020011800e5650703035172190300e040c3e404000d50f10f400c0c095501c000902c81540035000b414075045c107007100e000e41501030b07010800320f1011501150103e400e1030b11240d8000541090100e4507400341c080070740040c14910840c1c0f100c511010305140844a500b0030b11041c50103141540d6101075804110010101543c0030811b400d11540300015910300a1800c10400d00d0280c4503180e480344280e028944540b0f030541050303c450300050b1420700928007803104101e0640381109441118002010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 272695620 1250 272694370 272694377
    0x510030203121b100c11210304020d060e061f290d091214091e0d14030a1b05060106030b0103060b0d14010f050310020901020316030804020a060302030f0601 69
    0xd24041c3d0f5050ba9040e4401e800c0440c1c111100905458401c4e00144402c11401001520b1445620255080012402c00ba8541100b8901042c000000d6220142d080604200e07072024002d9000c601051650017414100c0811001422190500309003a4030041942000303505802400c60041102040851100c82c4240a074101c4103000c3d1410b00381c4422900c40c80c0d02c1301250702d1420003030a00340070205240318202507031a06c48141c160000d010301102030003080c2e42c255104180100003c2c602583c490380702e085500190441c000100702e941d500b04420b48000c40c0100503440880d01403902ca60104408403d42404101007030803543c95226142c90300414011001490f468591010080c1d1090303110760700903c0c80e0070201d501c0346400700701c0b580a400c1079810028425403040020802c4403e100103401201c0c0d004006080e219104281c010107500282c103220b056004c140049500e000d4100d4054142c58820f69408925151510410034451820b030018400c0610602c20425402c000d03010032a0440400d08 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 272696870 1250 272695620 272695627
    0x90a0603080f0f070203150412051207030908250506060a05030d0807180b07030207140307091824050a0c0e0f030708010213090b0418080d060f0e0a051003020312 71
    0x70800f6000f4402c07400000d404d44540110b10080a500003450703800345100ba0400340c1c1c1a803090030122860300400491000c3d030400c000c0411001c900070703880b04c18042d02c00c0c41c265040404034501d01145102c84004041000c1120200d101001418000958014000c55500304400c0c14800400e503144d840107003440510100d280410758940c01070340900d50106010071840c40350780c0c03a41d4003020b03640c210b840d003180584180b14000c04c41d808a50040c031503210700a001000000d141c02d000307101908201c0c12000c6031003182803030710300400c0400d20550410071131140e0941005881e484032030105c64001b408080c0091515070b640240039805000150414800c440345040c07555800006400d00400b0351200d8015840000c41e01c0c11201c2c250184421070b15000410400c0001e0b410920080c5e03150090001d401a14102c051030000f56000047c0c541f0f410440000150a501e400c2e4040851083c1d0700402c1d0749050040400a40905a004441c3d01030751003a01003011514560109507150b41d00c0b01525070454020 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 272698120 1250 272696870 272696887
    0x30804020114090d0303020705060a06030308060d0809030d0f08070306050607080c0c03060a24181d0304080304050f1f0813060510171c0e131505090a0603080f 70
    0x19040e10405800100b0800d41c2c1350403854068002d601c00c10b401c0350a402100000342250741c076441001c0840c2d0b050307166207840c1d40d00c103001c1160000300702a044038400c000340f09481080d00c0070420001010303c507491303103009051420b90260072000018a8401094200342061086440e040250307604650300280702900c800a281455003440c41c1040141d4061144800308905407020b904001c5039400c00c40c7c0c08140300d45038010b0304019a1030780d0003a40c0e8042c101c80318602e0420a03a038841c800100c01c00200e0051641c0c015517241c2154420341c03118a00c0e51000c038061040d07141c00c0d03c0800072080e0840d10207241708680030b407410841c10003901c0c00b0b00340094000040d081c10200f48450f45140e40c014020420b500d0b0240c050700194a0f14000d00030780c1d042017800107a00880009910340b12180011a0345003500315500d04881c01d01c003401c0c415412840044100500c1c070114040e80c640c000002c1030b40c0440f83e080c801030002110004166050060a051081011928010403a8a40e20004800e1617451040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 272699370 1250 272698120 272698157
    0xe0f0f0c0f0703050d0903030f0612051905120307020d03050109022104020a091e180b0103290103060b030f032b09020a08060405010b031606110709021303030e030106030308040201 79
    0x150070f0302c55071a6052401b64400c1581c140d105007562742c040881000141c1d1202c86124110350b05450040c02a0f10000461441074080380480e50018421000c4804001220100081c04d40041d1401c0300035911191030001c031280c141c000c1c1c5024140c80b40e001c50030582c03009000c030381c045c043c840045101000e1402150654079901110b40142c104050140044000350340080031030744642c084408aa031504492000e558080c1001c10099178201c940314041d0307400c40c4c0340c6901c05100e040100c07400e1014040742c0e81d000429201d0707584c02103010f504002803040c4070509040c00c05145111841f0750790001c01404028400300c011100c4030034902440180300c6118942000c005007266400a98800d00c400800038007424001811403040b485240244101c0c0701000505640382064168000c02d800b0461b4140200d603ca540c04200089502c004ca49803d0395500b0340c0d01c102e0707100010003000b041c2c05a50074028541c10031010f00c02814168020410941742da1001071011a02a0009040188a01c036100c421400d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 272700620 1250 272699370 272699377
    0xa09080a03151a0a030e03040302010503340309110f010207170a06140603070605030c09060307030923120f12070c0c09060f080a020901060509010c05070e0f0f0c0f070305 75
    0x1003640400c14090001c02904407580c20211130400040d0500502403203295011013078400b12075068481906548464014482c5445040d05c040c1109600400650603202140c90340c03052243c0c280c40008910819041c944000d243c82903989000300c18401c0c880d046643e001800b50704841e9405048440252009019400e10346c081c0401f904103401c090f8610b480c001c60541c0c6034055201141180c48050383c81506440900046404039921007050084c1103050034030900940c3c2c041264a0001951010b641e03c407a0b020100301c851070203001c9104500c6402c01d604010307198034034152000103414083d01d0300c00c1d05e4540c0304120040c103030f0803560408900203a02503100c84cc0e41c035030300c2410704000e2030b00c0b501070200400b603501c202d0101c08040d000001d081000070030088210f640140c1101c00350f03804c00005a81c0c13a0300c481016410485c210f00f010700490341c01c0c00b00314040d045400611915041030550143c21180151021491000e00001d000091040e401241da01c141e0014045446140c1c03400c00b039a5500 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 272701870 1250 272700620 272700629
    0x6041103090607091203020a150612051c0c0203060402040b060c0f030d0c0306030308160e1206041202070f1a0d140a06090506030c130f02071401050a09080a0315 71
    0x2101005110218402107200c500c40c01c0c00d5a01c40000c1c4d079a80c8901e1021200342900907006d40c1020000f40c012815141d22200d461212942c08105581d80b80c140c807d41d140007110640c1c1580100805882600700d540109804d540e5a190801c0300700d6803500000d032280005480244120fa41c3e90b0145055110242540c5008c2d94035021782d8000c40102441540780d50003048031101c2d161500003180c44450080c810241a2605a03407000b440c3d03a1070910041886010b00048414030441131045c800303507550b140f4a1401c411151300034001500309490402d400c154602d035501d0545d0800b4206000300141000100110384070355010364120004080318000c0c5100382c1880e01e169600300000c0600c94490140d0003030141220f501c08121050355060580110740d02511302c6581500449003148581c94551040710100d05500c4c00083c0048038490b40f00100d83c4014011a040c032400347e01a0021031081c070a1580c00b00c0300510602c6109026a580182846085041c2c4181179965000b8800c07031920365001809003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 272703120 1250 272701870 272701901
    0x1c05151c060b181005031906050a29010810030b071b0203010501140111070608010b0c0c100309020a151e0c0204050108060610020309090127090c03120f170604 70
    0x3000c000c43c09658031004461040c1c135601a0300c800222401d001400c40051040306100300c45032203031642c504001c0c01740500181007054484c1c4114007469029184050045141303605110404885000035020b240f00801808103c46462800c002203440d514507036521040500e014011414101d40811550b1030303490001c3c0d0958a002c00104041d09440c0c810300c00b00000740c0342e2100110803945260794855450180c0c00c00100d03240c004004500c110005401600c0c801e20a035400b030414100850490303000424070400298803543e030f6100b0b6040000c10140a00500240d00c0e06c2c404021070080c00c100c10030703158262940d292030907017521544030b1100381c5480b96000b0310520155035101d070015503465043c1c640a200d1440e0003041804240000112a005100074001340c050b40e20704125206014490100310100b103000c1d8402029400d1903228003401c29104801900103036003507007000705001c00383c40121070506c41406c046800c1e50b50030000303c540582d031703c8580c3c43c3c20f40d1343d28000c01c01518a213081c24598 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 272704370 1250 272703120 272703139
    0x50c12031b0304090b040b0d0210020c150a080c0708041e08030a020a050f030c07120302121902010b0906030c1201020c07180f060b040303051305061c05151c060b 71
    0x4250120041c800c482c10190f050040e0317000c4604000c00c0791010106168081d0440f110100107081c80c00c10804499854010b44800c41000404116841c03415407010307101d1040040c00340d10303550b0002c644541180302c100b0b406040070f0003951503a04621450040b01c0e011801010300d074ac00c0301071001c806d9018161603816651036421b4108060742e50780c040e40084640d0300035030341090401400041596183e0031000c0081c130480d45000f00c0241c0c07003800a0429800c50088120f01c070040003025000380b034084120301d500d96156002c91030081c216854109428824100c0a09200c140e641c00a8580348240003111b96003217481450b840240240301d41007078141140242680012000d1402e06001d089105080342406a448042c4602d070440c0c803540160b030300010b8207000a04c0400e1040740541000001c2d00e080042903038456001a00ca80c00021200494041d00203100540300c0c028040c0c01e17000b5207042d4412152103000e00004a0a00a8081e00c03d10003900309501014072400340c100e50444140030306018007 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 272705620 1250 272704370 272704417
    0xd0f0b120c010e010509132c0601060801050a0e0c0a03090b09010b0a0b030f01031209030f151406060a05130510080f07081e0a0b09010602070f080307050c1203 70
    0x310782019040031404200440c607520340d20350042003110340c0d0100040107481c4100d50034506000038402e02c480b10118804092000c01c0440e0080c1288032400660b41c0104015850400014441c00301600002d004011815042240e01045145950844000c07109952914080300c811001454504405001c102e024020302c0302400042d84503c6854005450000b121500d56103d084030707101c03e5030701c040c080140a0040021804101a0300030074a40d03440c000c49480c0d502d80754045081a500004d6401d04440f00c100850200c0e107101c0c500c0d54040d051058211303032511000242c564010070424600f4044000751410034406100728070070240038000d00c42c1c80b60b0b45140c240181040b2041b1145a060100140401c0d03640340910700049c820304000c074100c40320240303800d07032074034040000380031081c0c010340394440b00300c40c1d0b40c5102015003c0e10032a801052020f1a008040c1c1b000c6405030f1061090b070700108040c1c0041a80403440c409008416074050268800031041c9524511906680300000892545500e2 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 272706870 1250 272705620 272705623
    0x1a0307030c05130b0306220602040902090913021e030f060a0b0312191202090603040303090c0f060c02060310210204050105040618050402120a03031d03070302030d0f0b12 75
    0x203081e25416141c0704244012443c2c3c80b001c64000e0595603034035621600002c0d2481d0540844250102c184d5079000480b00920b90b070302e8061341c0054001d10602c5402040c8500c80703051032024240d109600c4000441c040c40e190b004101d0701d00360300c1c820140c001d0907040d6107000754804004a41e42c1001c1c01c4202c610a26050b00d40348000e20b41580d50741e21a00038050000680c0782d142040e2000141048010101010990310995203c041040d0000406400b844043c2c200d80e0761b4005103214a000c0c1d1404180c0310050301d80541215415040044228540d507000e22540c1d910001643c18260b042d10303040e940b03860700c1074019089080340d8071110344061030040c4060f01541200300700401520030f460901160762100c003048252072a90103020403000c0e40c13040d0300c48929115040b96030440d0025003420362520491503030341e0400103d0320701030300441d8541036410884420340ca4060303007020307411018504025481e03500945070300c1880c540c01402d548582202500c2d0000f68018901c01c00e00500500580300c4c10400306 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 272708120 1250 272706870 272706893
    0x1318050a0c0b0406080705160b040f03080c0418020d0f09083402010302090f04050c12010512031b070b270d0c0506070302070504020304140f0c131a030703 68
    0x12107542141c99030004103034802d042600c082d1151074644c6001036440002c101c5040d00401c4000ca440c89521070705001060161000502403400f40d0f030a80b0503480a810054101b4201508035903c140c8101b01c200a44130b608140c540026800c03690141c0d40d6010340598901a00d542c540c1e80c1030ba076207402c004000b0450220010500c003a040a000b521300c0c0c42c00c0d0070030041580030316060700644925030040401580309600400107483d00401c04d02d840018a404034003111411a1260071502c3c1c0000d03454503445042ca1440c0c01850b0440d03184e1203142c68155510346030b00031a20031b550346040160307401401e0081481100050010342040e10384404150840c1c4600c054400843d03120300d00c4a00c102d081c5d500304500165540c1d83c01000c0410094900001e104064ec00720340158110b01035414003103003944d21400290b001d54010308170480034034200c06015081182d604000709a9a200d008402a40e0700c2e441c001c4101c03441e1429002600d40010a51061451180301506a150066034030200c1000f0080302207 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 272709370 1250 272708120 272708123
    0xb07020607020607080601020d11030720010306080109050312090f0312190c02150a060807090e0c1e04020703090b0c060a0e0a03020303010312030603120e1503151318050a 75
    0xc41d100c944610134181c0380c0c1c00042d00d071140140c00440391103c03028007503407030310310f05127140030813685002c0700703502e40e410b40004044003010b80310900703d103c1400d981e050181d00080c00d0303800b000304201000c03580c0c1c003540d03403150050003d01105408000381c01c00c1405d101600b00424000187c90390b60410340186030742104100c071043d00d10381400940410902542c85560b120400317a0b0010301c0e52000040304501e000360f00405078604180c4600380414000000c3c401d007401000140340224508014660742c078100b1650f003d0b2540907203003421032040a81110464840d81d5078090b10010390302c070010f007011612400340c2d07001060495030015001070a5140003452511410454008200d202c045a5420751101401035001c0d0059005000610218846441d0a03c0710074240c28001403043da65501da00c81054080b0580c070124606a10041c207505069080300c0c100c510103485580746250140341a100c90005170300c194010600d20041820424159004601c0d03060702c5014a1070b9041c2d140780041d0344941207a030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 272710620 1250 272709370 272709373
    0x11223010204032918010e0d18060e010915020a061103150102010204050f01110f0d0c11060301050a03060b131e0b270916090c0806121b0d0b0702060702 67
    0x1140c0000441014168840351210440c500c0c603072642030384a4410451041d00305e801d5581d80d0415551410b00b0089140c10b20706c6515140c1c240d0001d01d400c0d070b961740415803150342800810005210242c1e0b001e4409029a444840c1c03c5007032010820003203240c0703201014000d02440c9042e10b4842c1c9654404042c51080c900d15040117506800107004900f07034082c3d8401c0c0c42d0403040e030380324103849980074400d00c40741451210102c0b41c10f811003c0b50306180070011f075204400319030707001c0f804014400c4a0b1084a11564243c0d141d41c695494540420784603c002c2c40040d01043e0380b01c03a00f4485540e818840d02174858003c41c288000c40c43d00f445507029101001420400c9441c0105d000104d0900f0f0000040042c4420a01503e2040f8035540c008601001001d592040c01061200c01c0030424009942020b000c0041001a5a80a44401400035040504107034070805000c51b080f45500070001e084110000140040032400c2e4082c00460700205216800519082c405400c10058a0340021180e05c00d4200b0350 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 272711870 1250 272710620 272710643
    0x7060e1c050705060f13030b090d031a0907030b031b18360102030903030105040509031603120e0f0d1403041a060607050604060504020a06140301122301020403 70
    0xd010354508000001011500080010462403401302c010b00300c2c1c0e01c894031015140c412401c0c0c1181004036140c10455a40c011a014084030300d404110a03009000d860508112200717403085020240804840d00503c10f0b08202c0014041e40d1080c0c220b450382c0b04021f82110f03000507691521454901044900710b008008680315501382e0788070940d1580c0a07600c018820000e64004c3c0900a01180081d903004804100d244c84101007120248000d500c20242100659260f504000412060b210301600042d99079105101003041d505402030000c0c84141c0c18103140719414248924480500a5a171004460b40580f411504111402150222040311a0f940d48912002010030b442c0c940d01040e18041c008070540c11034500e00c892600a41500450020b20752410601c940da5107078504801110308448058032030301804114103003061107030040e00090400c9500c444c00c001080b501400140300d02d00f140450034a4070010301032001c00c9000380c005041100116a1481c1c0e140710b020b9402488111000304188 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 272713120 1250 272711870 272711899
    0x9120201050c040b0711060c100504110405010617150a06110c04180602030601090b03040501020c06011715060a03081b120406080601181e06120203160f0c0507060e 72
    0xc0040300c0c155400ca84500e81021506e894484109400036980340c1c0103c0308001c4641c0d048e804202108207595400c8001c1824506860014804800c0c01d03200341c062410040103200d02504520311102d02021101c106650369582d00a109403103910701c4100345c0000c07444c2000700c0d609600a144400d100c40b10303000c41e6413402c108010311080350b410004209450040d00d07080c00002e450303a001541c0000341494046480c94640710071107034942c0151000c0750240e50004211710000000d1222030b004103003042c0240c4007012849801e035128001e84603500c00010800d000070721a076490340000400b0f5900015aa03454200d0044000046019049201c01c18402d160718007035004c0c280411141510116903c080e00d07900c400006582c100b040d0b0006e02584481014041003801a0303085164503860a070055001461400b90060030307036008458180c90141c01017040181032062400070300705011107480c000d034002803d80c00031503207080c1c0f40c90700034024040c2d501c1c0003400d00d5201c41c2082d1000303270844140324440f042 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 272714370 1250 272713120 272713141
    0x6150f080f040b0403050a030b091501080a0c050319020f0c07081903050a0807020a020301090305030a1103060d08280c0b061206010e09030c0f0102070308090607050d05040606090912020105 83
    0x880b0300030603044a01c1d0000d4006813003200517000714092801c003c81c1d00c0075120b00058030303840101c0713075242503a0f490491780b0410b690044a1603000405c80c5400c00c011810b9081c0141107110080c03030304511410000039504891000d6040300d00c0401040d031070a1b21040c081810b03544900d010301c5416071604c2034140e00015007005070710114440740d06445003454102d05110540c0e020400a0045042d801400d0806c070158034280203100155100755a91540c1c5d26149280c02d007292244425000150810320401040e51900030f155109240c000c14210b44801511003200301c1400d079900c03d11861200314055581042c2c0020030700501510079400ea04603991200184010003011999441c016842000100308100300c0003030701c2c2d40048142c0c068038034000311244142d141403a04103008501d6940029010203156000c030105070800c1029001d400b250501d00c500400c14000c014084410681d1000031808004a6030f01075801030140b070b6402e100e00035460a00d407a0703c40d04428101d025500b4003001401e909003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 272715620 1250 272714370 272714401
    0x1908031c06171f0605180703050a0b0d0f02060405060c0706020c1203031308090612011a0724140108010c030c09080706050d0207050601080f0705100f0c050106150f08 73
    0x14014020040c200c01c0d400b40c5039103000e480c400500303c0b5586031408207981c0c803180300780e2072969200f2448140724200650000c04481004000d00302180c600700c400f515a903950781c5580251500700308c1340103901030640000343d400c0c4200d5000e40e0b8840b10000c0d51030003c040216481c4101c0d00c1c181c099842e0700201e00181304c00c40003c017085130350540040000a000c00301d2418403549203805500c14604000c2c0c0c2034003140301c0d54050b07803011040181d0040108022040d0542d0301e0015100583c0f0a400c2c0a595038880315244440c600d41e0203148171001d8130801c0d50059034410320b811856130602c61b0446d43e441a07440d00800701806000c000a0408503804103042c0100c2d42c5804442e42c820042c0711040c13808900b00c07015041001d942030b00f5a000c024060200301c3c100301c010f010307103241b40103418020110000c251900d24103600250003102d030308000042191704280404c145802a082c1000300b0005491f180740105040d801042d04021019149040b00e80e0286030100c0c02d80c0d06854032221504d07005240c0880e0030713 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 272716870 1250 272715620 272715659
    0xf0203130606080d090b0a1e0e090615043602031f050a060c0602090405090c03160f14011e020705010905040e030706020703020307050a030503061e030c1908031c06 72
    0x108299400c10040c4a101c0040141d000c040c40c011490418034015000044070f4488c0c030b00000b80350102c10015078a41304100e19003002c070494800c0450701503259005000c0c02944070380705480c0009103243c01d68140050002401081e00300c3d03807404814201a0f410001e410940c4c04421000301113081c4440040c02280400641d50014401c00c003031843d00d002111440e400400031507125809120060198440d4003c3c54003c100b10805400000c207000c041c14a00201481c9134044110301c1e050401c01d1071442040c80301541c0c28000c418019620b810010394012081406602950710a032030980d501c0c50303010581d6801ea0f08266141d01485949004020607038600f03207080000c079001000440300052456000b003030f032144640180d134100241c03070b00e4841c2072020380c007415008580000100203540c07900c0484072280700314140892403007165101c04a5980c112480f42140a8450a540070000303910f000d0101008014040840c1d69912243e21041180341c0500018015581844004141640780d000c0b0744404a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 272718120 1250 272716870 272716877
    0x1030c0e04032a08030a0c0f051303020d0f0f05010b0f01091809060b0909070e0609270102130b0c0106150f050d0216050609070e07020a02090a0f0203130606080d 71
    0xc0303c0b214080020345055a800002890b01094801d0008032150061480f481d40042c0008590003102006099011000c80c0001040b004014a013403444c039450b042819641c06441510318242d01d860011010642d400c07001c3c20285012130038000b0440e05401c841c503180800c2d181e40081008010054401070001e01482a00840110355114041e0070b0790701071000b00340038201c00b003920400003011074042c02040c1c44034005600465410b0003104401c011086d00303d9010b4526800314600460f20340351100340700c21127074030103a00c0b0b2186507002c04003501600c458480f0800c1c44402d1995034182d2540c02da11400d03c003013140d400c0000000c3c3c402c0f25006500604800368a03041080c01101e60200d6080c0e1000d50503006155080c016442c1c00c21903002408242403040300201050305200348401d05c0d14050b540403400b848403840410103180da020450301c0205505541038002030f100ca01d242c40c00fa20480111059882c030100410001c0190030890b450b0403400f60b9401c100d2681c80c0c0b855561904810300c0c3d01c4020 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 272719370 1250 272718120 272718137
    0xf1b0c150f09060d140a1a0904080c0c060a0e010e04050c1603111b040f0504170703020703020414011e080316060e0105010905100b1905072901030c0e0403 68
    0x400c1601030040007507590003000c0c60b00e00b07003401210800705d4614100310141910744100b001400580b600c61680780d1040402c0b182c4510006400140350394000a000400c4140080b03205101d04004001843d6283c0e0b0013001c6680300e80c40e0b001c00034120b00c5192005400250581e202003140d04141c40343d90702540d00b09841601d010002c035403900041e221410220200411801c410b04a404144100010141440004443c2092420400058071240320498030301d80c5c500300a110010b030600750840e0543d1140d00e1007039200c50040c24141d062160f60360003c3d4006041c25100c6000600304501581030781c0314620f81c02001c00900c100d80e580c0c0c0d0414000d031036141e070040000080c106016071161845920954000c074100b00340029003401e580d402e030700c01c064031921181840b10b1110701d642840c0240030304080d003500700410f07a4100391002038060504400c2c480f0010b004403e014841c0307080c250b111007082c003103070034415101036017403001d402407009550030251500c000c43e10401e090034250081307800d559550f64 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 272720620 1250 272719370 272719387
    0x70b0f1201090f11130302120a0b07021e160501080619030803090d0503010f0b0304291605090315060402160f02030c010306050108180304090911030601080718050603030f1b0c15 78
    0x2000c0c0c0c08e401c0306200c3c070300c20060342c030703001031001007085108140d07a5000e89101c800d014182007042200f555008450381080d8110201c001f8080c5011088030002d1800400c0b84d100d48010a0140305810101841e4442c1c8101c04400d100e1008015802180038a00715043c600707926808807a00d00082c007984428a81c04c0c0350400143d0a020084d50304140280d06144402108200d05010004000c10a415402c480c40030030500a040c14500b20300c0b43c0d040d0400030302d0801c400e0006500d54030b400007640144122400031a81e02c0c0c03141e90641e0f00200d0b0f030502145a9807070074180300344480c07082007040748603101d070001c5211903500c2401004229001a111b0b021700e40c58100600c0400390b600d2003003103003500c02130000003a051054091540344030300551100b00444c12074011715062030416004004968401c0c5010440000f821170700700b8242c055100c0000e1551103180c0020b0940c8940c241012103d10080740142004c409a8010305004910404441020482a040c042c04400c3d020b1421035014040c003804030b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 272721870 1250 272720620 272720629
    0x51507020d060b04020d020307020a031202040b040519080a050307060b1c0201050d0b091501020f0f060705070f1b170a0b06010507050f03130e09010e070b0f1201090f11130302 77
    0x80ca0743d10300401c007508001c401400f020898004449120059024180d21018190010503518146811070382c10342c9010306051140c08230788558031406020703404081507450481c00600403000074002000942c0c424640e2070078800e540340c00c2510140c0d2844e280c80801d00322854a40003442100d070b50700b01030042000e05a001962290021030001d00768503150504000c2c2030391480c000324030070484100c450b2840c29400c80020b10b0600320041070265588180020103010340300050703040e4042c0b0b480c40c182d40c2d00c10091921182039411800002e1240e90254000c1550a5070000008155104210110b59034001041c495545a16102018140d201030102092241d4030480051003211b0185089440d5040c0080000d0703d10b5101e040310b040d0070320031444184940c11707168141d9500303c0726110080c04100340810041c1e480307411600c601036680c0d1000900d481500929415513050b8102c403a0b54400c65a52402d17000080c101a00c60031640b14904500442c0e4032891209480700c8544001106815509650a11 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 272723120 1250 272721870 272721881
    0x60901030f320f040b100306050c03011502010b0a21020a080a02040b0a03030210020304031110090302120f1b12030c04061e05030a11040b13051507020d06 68
    0x150415032038a10328544a403060061040450030740c1018480321030040c41c54001c19401a10001800d9204000d100fa842e0700c0490b41c80d00150440040c00e1070f921268039991240d422548002c00040c241000c010220400901645c12541d24030b040c001d160b0213800382242200c01c8080040d6120f0a510020f211129071541203090010316001c410a400965400203081051194009000d80d4001c4200800710b0415002d8054500310541d050b0802c2070459038040d4a900b621544001402d90200016003494440e0303280d003410328111002c0d24606403008080a020709940358094000d4403400c1e94041103c0758000c00c48a240c61183d400a040042c407540141c601100a00c50480398800c00520f00360a0140100841c0122610300500b50303201e2914102500d44989206911212011240f991281035005021298042a00d42c6c00243c18a49500f181e41a4000c540009648400226540d003400c0d01700c640c00020754604907581c92001d11454120701d0b5900c54510000d40002e84840540d0009085030440d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 272724370 1250 272723120 272723137
    0x190f05060319150b180f03060708010e040501200702040651080412050403110904020d1202010609140402030a1b051905011e020303160507050109060506010210090f0206 74
    0xc4440c0da50b03403829103a400075007021140d1520310f012020580740070b5080b48040c0000758048c0000b483d0021006d065020144104001044c0410000342000000c2d030003120191240020899010a4801d01141da50031490f0100d0080b850010081211000b40440583c4810100350910100007143c400c0d40400d4003601024500e440c8445a220080c4401032121502e500c0741c4e61240348524290421103100c0c1456600d0006011080000740081031078840c0081071600c09603034501f1703d40c65134030103e001041e202030040c0032500301840c0740368844d81c103401000807a06088800e000740101e4106540306c1c10000c0d60029415030000401e2400a568808007a0031012103000707405502d66260040307100c3e40c3c0e00d007008045140c8106000e0082d90713000400802d000e402900c1504000d0303900417003e03503240300103003402c03601c8020852000810f921550894500c0c44c0c0c010000d000c502a0b9103407034070240c0800d842c09809801071980c0c060f5424545e01c5540d41103600305184030340310317021a001d01c00700354004d001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 272725620 1250 272724370 272724401
    0x603120c080f040b1c06030f06020c0a060f2f0703030e10150611190b061c0507090e1f150b0a0c030e0d0c0902030702010902190f05060319 61
    0x4500542c54900054030051040030040d0b9030320904505420302843e02158003003030140ca0280144046920b401301c00901582c031043c0182c0c1c4110300d182aa02c0c121012200618140c2000100e10040440384c000245005481ea8900542d4008143d100c80e12481c15140da0451042404580d011a1080c1c00040300600000292450300c00c0f101c002c68161840982840e001d418404010031500c0da22021469690090388003400d6618081c903201002c2031400c407006400b84c5100004034025903601191541c40c14840a0444003024061a19913140c2e01d00703111780610b0518040300c00410076400b01e1030444991035a80c0c1800450341038005140104031107105c0902c541c2d0202c02c0441e80750f8a840042190016035200c1c005400094600207004444a007c0c450040c481248080005440d440701d000a9881c6040c0c056100c2d92080c100320b0040003082801303236228081900c01c8441419440d45c9000361181e4000800c0400c0d19241030025510041d00c5007900301c0d00080032000301400a80c060302140003600e0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 272726870 1250 272725620 272725627
    0x903090f10092402070e060f0f0f1306090506060702030d1115091c05090105090904050a020414240604031b0306020415030f0e0d2012030a0f0603120c08 67
    0x1085296601c0940203c21000d4440000664034140c0410401000305403d448120ba01c0c178001000c520b082c030000e01c1c12130085000032516000d5550300005420b501c0405070469580c1c10240c0802c2002d04000e00c92549840c0c5072502058250030321804036005560058000c044488028404032890413281e5500804e60141454400410200b020103034010b0721070300c00402c080712946030350840310320703000c601e00007401410851410360303036040030503207a1365072080303c0e62100e0765903600300740d800d000c02e01074020350261510300a00081007000c0d4119000300c0d14404610300c0540032900d211100445942010b9000400388400c00024020111078841c0b0004001d030300280300c0e03599580c0000e07600f298212401c4012041e075503c9803158140f00c0c006c40030401c1c24051040704000c51501ba01c0f6001c6080043c200540c00380138100d0b030b00e02241c0300515040350000702d41c2143e014824000791604151500708416090503441000d00000d4010001600d4201800004001038031000b940c100910200403a070104050 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 272728120 1250 272726870 272726879
    0x30f070e040c09020706020a020606010f0e04020703090e0915091f02070302010917041e0f060f0504030c0303030507201005072d1b03020607121812080903090f1009 72
    0x140043d1881c584a00700248c2c880c80c0040c80a414024010200f50400c4803813041c0c4008a0707803141d000040440141e80c0140e030b0385220b0804440d00c000d241c00c86002080d0f16020702c40c0602c000100024184140d48403040c6e07548542104a40f07940c46100c0380d00c0d824100d0110360128185650082c0b4580740301380000a11005141da43c0c031040564020b00320500721011070704000318464020752001400070100405816414071007071382010369240c0580f004026411000050050107441210041d642008055031142c0d40c1c0c1ca8000c002d000100c90b120700164081840200180344500c0b401c51300311654001d403184080002f150402010700130100d40401c25000003800c0d642d40c0000c03007092501414615107003800080300c4094040404100d0b4200740024890500380466400f00e8881c5c0c1000c15450322101845085800001811050070b400c0c50f4222144101c2081141112081c5c0016030329858080350b0799192400503459005903010550401e0300d00b142d00580b461b202000c01400c0140342440d110042e01c4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 272729370 1250 272728120 272728139
    0xf09020f1918050406120b060103110d09031e050702010e03010b1201090605010b070f140a02040507020105060102010c090b2203050105041208090705011e030608061303030b030f070e040c 82
    0x5100700c001044019414104242c0b1403180b15000e00010b40e41440850f15203104050160003040000d440c01c4100c0d000701d00240e10a4001c11224030740c030194281c546044e05c03c400d000701980081140454403258050040300d02e41d0038000c000c44002d440e91801e24142c2d400561300300701d0b50030403070343e1555030f40c459100b00e135440400d241d0b0f5803100d8000004401c00d6a141c03040440c2c40613003003010212414003011002071035000d03400003125404140400340001e1107030850f141020702040250300604140802403001d130305511041c402c41003607000344160b40068209844181c0300d0b00030119080e804002c0420383c10b5420404d10051a5580355400149507a515950b00311001590111040002002c1d411800e0f035101c00f00b15048103041b005000d250f0700c0d00e070000c0c0005804848241084042d060745981c0e8034060350022005002174001e9510724981400d41c04408080d25504030080f80c68490055802d0500113075400325405190000c002007030030b00c4c000248500c0c00420450b2414496400850403820717 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 272730620 1250 272729370 272729407
    0x1005060304150f0f1811120f01110a020c1f0509030c0607030201020705060a06050a0e090a02040e01061505030c16170d09060e0133170303060a060203040f09020f 71
    0x100e0800000344c401d0010452416101580c40c0f0b8a0480c60071006000841c010110320750300114101c0e13004500c2c081e090700007800c01d5498041041c40d54604254044144810b00003000380e03032181da003500e0100d4400300400842d045400c5030902150102c840300c040050040303000b401150402011941070306110000a10f01d5440900c040b0300503500422210b040180070424a6040049200c082c0000790903c404280c2e4880184500d094009080300802c82c00201440048080340e00a007052000317000e020f41160191455100f00722072400f035140044d64552017001582e01070f40005003680e1902c452034192103001ca000441c140c500313100010b4681380752610364008003000070710040049590f40c0a41041006c840d0400f0318910300d40d0609a128900e212441c0c0c9070a1800a6411714150b03032035540c1c0c1c4819250085070850002c19040c00c0c00942415400030145102c1c100c215143c500d640e4842c44e0490f107038081d134032812410342801441440524400d0300502a00904060054240700100c40c2c3c00307a010b00d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 272731870 1250 272730620 272730641
    0xe0a08090316121101020607020c040c03020f18030f2808210108011a011707051608091906080412180905150907121a04052d100506030415 61
    0x1090301c03d10701e007000341c3d115901e0070000e400d0000d00810315003000080d48814515a8152203141da540a01821034000e40c1034072505800c07000e040d41c0b1401b4000008480c01040e4a44074440d201d6128041c4504100041c9004410040302c4071a41c44510812040310b080b60b4440100e440d5081880841e200120320b8140daa0030803c0340840617040d500d030140303180c21280100074040e801c00c007042040d03140703036004000d81142188008246940b596024421541c0d401000000c7c2001d000110f5030700c3c01d03c401c1e0030160004440460b0040c540502c085818120401d035072090070040f460410014011841058101d0607614442c2800440310840c40c1e0b88440540c2d5980105030388503070f6801030000400e6802080301103010b0540740c001440c248090003070b00e0005000c809500003910743c00d080780000b1034540d500c030f500711000e04240100d0030309440324404200400c5000d40960b4960070a503082045580c00d0b203009a00c8082c1c50104035040c801840420b17030000380140c41c440d803107299103400e15813241314410581c1d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 272733120 1250 272731870 272731889
    0x1415070609320703120503090f12040503120702030d0f050903030304231501090e0115120b15011209060e0a0311120f0301090b12010f1b030e0a08090316 67
    0x142052804244558441d01482c02c0e0fa4000b01c424000101c1485895007a1903050070880e03140e41d1a0f030030f820b06e401400300844416000740000c98001a0107280940243e80046050325400c42d80d040400b0150700032500c003e981a409038151030100c5000c0e180003440305015107007003131a03d041d0320003007488d59109030f41c11112005940c6001c10002529185081c9100407900501031541c81494003410a11041c0a060700b0780d90384e49048209180d007580149840511441400249036861601c84e42c500582d200513201034000c540090b42400b810024507030396940507103c1100c003104810b800001050000c0b030884041d0365030030300400c803200300300200041c071031107a0344407410a0607900100d030616500c0c4840b40381d0321100340b2030f803c102c8680006507030541d0f40001d0300081102006001914904140f9654460b1b540307003030310711f07101502c0c01d401901c0c1850703186600941140064004800325103050130286115040035141000048103d0010300c0400001001c548001c400c4600c00c00c440310540d446920390 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 272734370 1250 272733120 272733173
    0xa0b09060601171e1f0e06100903080706050a0914070302031e0703020906060f0d091b08030d0e010b0a06020102031906031205030403021c020d03061415070609 70
    0x3980c1c4504400e400c0c0f00c250010300503d00701250b01c2003c014101040b1405160510005140c0794154468042020b10351040d50440d259101100303c240002503a00c94000c4452416440001c3d0040703ca0340300b00c95101c90014074104041d100c0030000d001c054110620107031140c9a03440862500c64604501c2c40a03a40a031280e1840c601c101841c15900a41c204a01ca0500c0d0403030140010124041c404c482d01904c9050255540c0304c0050b4031441a103c143c0146503020444041e0455654003c0c010307644920304412903070076046820003c0d00880d01c0340b8900765104000007501c2c3c1c2415000700c00e00214100002c02c0800804000804030b032025041807005170b6002c03040281d980003000c220442070100102c10403030300c1e04540b04c28045190f040b00803414000000041402c01d03108200d6101c0810440c5400d581d01e0207202d6000b51249000012180000e00b05031001c100c0c0380c1c02d40404080e00c07900034812342814000d00101c060036080640c2c20703600301d0b64801414012a2280d100350321100c03180d034240b110 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 272735620 1250 272734370 272734381
    0x7060f0b03100b030d050304080702090709060e0301021207050912030d1e0501060c0f050c040908030406140f0105011d06030a05010e01090b090c0c191211160905090a0b0906 76
    0x1d001203602e03041064500788007074401280c40c01718040ca07556409160050380c0b0303515814822564401c0000094100c401701040100580e030110000c000e039141513a854004004200805080c2d0046c204000d80d100d12100104e1072140c0a000105141800030304007c910341c03e0210700605507003211001c0d6860f1507c0e1741c03100719003009401c0c0d104032401407007204012070350428074014840d034074050b402817048483c09601d41c10301000300981c41d086500200284001c049034607160441e43c10a45040b1011400c1c20234400400e6284c41800740300c0c038100d087c5940d00e0b07840c00300116682011909108200c1c51a10100b000300d46030701d80114414a070801000c82c640d490107003c0c001d003000590240390003d19200c5802030300d41d90700d80106d070046091a1317080d0710340e40005034013802c04050600700e0311150410840e803c20412a9065150007070801d0304c1d01c44180004108140e207840030001100f18032100c210060041006613840036401410b40b0045034217001c01a541c1c40e403040b40c00c2e00c40017441c2d40107004000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 272736870 1250 272735620 272735623
    0x1050103080c0c120c06090613080703060c05070b070503070507060e0d230306010c0602090301050916060e0102060117011b110606010306060c02040c11010c080105030c1c060b0607060f0b03 83
    0x304010f0381a101e80c1c84242004400d6512411a090014030405000035400d01c145c1d1840180e5001304500069848040d5690a00c1c1e030b5035503070b28841119140d04104009100703030300401c1a62040380d00401c04807060b84c0e0b03440040310245e00040c11081800001c5c030401001c240544210040002c030940140441098400003074925580d401c84c8090030400002c0d608407407440081540e41000302070034402c02c0304c4d080d49081800390090000694066191104000f8001c5000070740c5485804000340742461a1b03210f030004c0700c0842c0c203821517902590050004100803044001d2614440c4c501e0800010000310103a01302250340c100c000710340b00203912001c4d108050b40701070181076001002424200011880c01d200030705075a10119006e44115940c000160a060003948a07104c0c3c0c12592000300f1810181c414041d200d160280905400792160f142203503505e062801e4400b0070552150740d00070092030a59a10406000e215a003180c028070103000e01e10000e94103001311000c040c40a034010031480c0c3c6140078117 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 272738120 1250 272736870 272736883
    0x1202090604020a14030405031b0d11060903090909011d0703031d01080402061b1608160302060913060b030c040305390103060b0d05070207090c090608150301050103080c 74
    0x841c8a00d10400402400c01d1300400324044062115000030345965850800360b00354050b0407100781c0003400368030614030980310200e549a40b2002603280e14420b1031401c0c0400f0750700d0400301e844441d035510800000150b454144480c55001000a0020404038000c02845840a180c1c0e082040e00340c1c0700d40c0091080603004002e6400b136140e01c0d207000b181101c4117400241003020180000c0d024070000204241100807800d40032006036403510840c0d0f41420340c800d04c103505070701a00c0303a01124001ca202c0303401100e400400403000c41c0d4000b000f4608202c007000802940080754016245666a0303a840010b0303d0b80603801031449150960100d42d12a0b00d50304103641000740c0c034001003d00441d964a01c080c1000302032401d107140c200550f1f60300120750310a40140c00402403074010540c000d401280c0d464002c09107410203442034200b40e09881d10b49543e181184251815061801d012841d0150700b404014032035aa0f03103600c0b01c0c00d08114001c0c20384020110382110f1080e001a981680c001403102401035040086 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 272739370 1250 272738120 272738131
    0x50f28050114090904140307050d050a0201060e0903040915080d020610150f0f030e0604060603031e1202030601050904020315030706170a0203070e10120b060708030a0b0102011104120209 82
    0xd06150140c0500040c101030030090000341400c1c04044100701101c0c0400c203417112305621408640d01d4281c80d11000d0056040740c1000c000540c00e280c00407800d800803440c03ca00866841004500b0542010300c40c4000d81400102c8280165107414002035400303013040301c0601e06a00b40c01801003401d21070300f1101100c110303800501c21b9201c0003c1e001c2d0b4165022048900800c103500e0084c29081821000310003420b858109950244995820701003405400e1f485501200d1007502c40c0d12611055041013030b16140030401d10f0b004114080b5440e64004013540041d83d020030b05140c05850720700800700003000c0380c2085e80c00382c1a112155071340c1c0c3e80c6030408118540150a81707060140500c2e500e45903101040d54028020103c1c80e0700800840c0800703000c0c0d40c81000440e00200743c0618803100800041c00b080c1c001c03000300300990822099081c1810f01d03100300d9601c181c000b10131034519511491490040c01d40749103010b04545da03401a85c8c0074460210b010700080c20016100b10041e1801c2d0040001c2e062000c1c00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 272740620 1250 272739370 272739407
    0x111e0a0e0a0f06030b040b040201030b0d1407151b0804030614060a08070b0d0e0a051c090902030105010f050a1716030506040b06310e010918020901050f280501 70
    0x3c1800401c00e44080141d20a41c131200c0851140c5d02c510040380605000103840f50403090702c142000800c0005c0002c0a07411040208450369a6614401c50400c0700351408400d000c0381110060030441400c013421060110f0040005924050f940d0340c03100100ca44000161141402c1c0c44140001c51601020b400000e2402c1030003880c0c0c89003042a0100144581c01407003105554480386182c41e00d0303091100c980165000030a5a142c50036040380d07500d804011046000024990840109102c0d00c07078800c1e00d05039032043c0c0d50003d42c1c0c8541c40090f11290310816402d82400300ca0f0a44100c2640d07036241080c82100540c80180000d4562a03018044d82c4020700098400ea040030301c65034088c2c0f0b9441c2038a2070380d03540c45542c010786c7d40d09200450290000da080710401c8a0f400d00701284d401c10781017980d8101d9005450801950b0403608200c00501003901d0000d51000c2c00600411284c036050310f00301c26082d8000e00300c00300c4a04948080000d0760115050042200c181c3c4010400f0750781120600c60703031070310081 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 272741870 1250 272740620 272740631
    0x100f0b0a03031d0316060302030f010905040f02040908190509180606121b03070e010e010c170309030f0c0a02010e090c070f060b04090507051003020403111e0a0e0a0f 73
    0x40d00070744144800a6110f0103224030b00da100d04180c0d0200403115540b2420021003840b151100c2000f00a584202c4030030328101c098100000d00c0684900c40c0601c100e422030300c80313058025540d0800002d008580d03010b5035040c1e003d2203411510303c010b00e2240c0321740c00303540c0f201e554030311b080000d11089003810384e0240d110044000804c649500c40c00300b2903090700a868110366046d610941c07602c1c0340840c540000410704101004110a02c1d070444100d054109098803034400c407018078001103681e202115802048100d0780407041541111502c040c0d50080c80d04801e407420310085120b0840309410022003440c00354000860182075580041c1480e0401d5015500410580303090041617080380b040c00802481c42036502c1403d000d008003a070251027140d000070002c0c002c000050404654440d598000d041c0b00f0511391054214960191007241c044a5000218495040500341048118000d1750090f4082e418044603064855940f1a00d00003e058190066001c82c104601c800e01103407031600c07811005c0c0e407918 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 272743120 1250 272741870 272741873
    0x6090615031c1103070c03060b3c060a090911040b04030305070201050f0315030601140f0d020f0409080d06060906051207030b0901090c0e0d0f0b0406020c100f0b0a03 73
    0x105000080c20002c15284003200b440b140212030a075070701212120540070214080e000c100285440034100c2e4020001880158040c0080003002203481c24403281694402d001b0141c07981040c2c08403804100000c0b5040f03081440000440c01d44c2d882860741d5000030384d00d013809002d40d0025218159100354440c868604040c1083c603131031030920980c0030103000e004000c03600500b1a80710f04101d03520360403000b01290f200d0804800c4000d10304110f10040380f01c7d000c0c450022803c0700e54029502d05e95800105080c00010f2040b00703209010003910070a80c0c01c0760900c1000b540c0f5407154021090b0162144039010358070a440303204a0704450450f0810303010082020303001c02a4507441003d0306d0b00c0c502400111800e0344c8421300c059004100b22800e0710380140306c0400019464840e0b80c03010b4a840080e8503880001d09c9071000300719503a5502000100409181c0e09040302140e100b005043d40140308240042c1303002d941040340c61620b10207007003680c0e500303031542040e482c0d2892a000d002d0380882c0664812000a045 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 272744370 1250 272743120 272743123
    0x3010b061b1e031c020d092114160507030609080304020a060801030305030130080307020c090c03010b1b030c060105131a0103270602120610050a0c030e10020609061503 74
    0x14515040b0300b0180301504030044002a904448030940300c640104074035070003442e00308050000001811450b8180038446c6040b18041c0303409140000e2780201ea146070940001d8507188480c0f0b000c0c02501c8078418448084005503091140404443c0141680c3e5160b02d0944104405041190014002c00c80300f0f10040001a4210080c2da0540d40134041004a90403061031f181c010700b045144a00710540c1070b803480c605100f0184000d602400050b400e659042c4031213810b1122181041d1501460b9000030801080f14215220260400541c80c074003409031400564121403564008140c10fa441d500301000411907442c28030064800c540014030f0034480300203021040d0000c001380d1090141415226001c1c0700541c107117055580c1c4004043c0c8410040105141001002074100c0b03145502c17545000b402290b01481c0004031280461210b030755031842d20300800300854280c0b02032a1704400f48101004410341c0c81d91000d01c256040c035910750083c003031450312140081c60144003410561224455110440c0725840 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 272745620 1250 272744370 272744377
    0x1409062703070602060c2107090609050a030c0e13080d0b0a060f0e04050c130602010f050702011518090c060503060f1c0201180905010e0405100b0a050d0203010b061b1e03 75
    0xa504451525052003400703c1d040483e60603a03000c103491f041000c106840d90000c80742401c3d40da03d5500d005806450350180704031068103000c041d0111040381c400f0084e044103003040030303405070f44404210b80350905a540c980c2942c0040d0344121300d194a0b58180400b50602c400a84002c10081c03520106d81d12404002504080c4440019409036448034001045501d0140403120502e0000c402e8000076a500e0740300a0081c64242e00011030a030a00011880440c414044c00500300ca8007811085402c1ca4614180c04020b002040720f280d039606c41e041c000104080c548094010701d001c2d22919524a0b1510802c0801c01c0003481d9a07100303030401030344446080541c000540d102542820071224950307503030b41e0129490200d9405564040d081c00c00103c4c0001c2201c0d119401340f031040081320840900c2600e0801601d4404410640010125408210070b10b0300c403400b00b08980c009000007410b0403038100400d40703d602c11940c1484030075154811a214023010004820040103640145260341c845c0c507100c0c0d80703903c07 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 272746870 1250 272745620 272745631
    0xa0b071805040902041b0f02010501080304030209010e090c0409080706230601030e0a0f03030c090605041809020409350f04031704081c030509010209010e01140906270307060206 78
    0x10f41c0c0d075100400f11344565118001582c48881041d010306902800100a0070903d140ca9005500741000026900f6000055a040c2c90f07000b0800d2010742e00b0028000c40b00300c4000c10889491007110014002c0f80c0300d61203403404841c011800e0342d0340c800b0f0f50f00700301c02581c03803052041140d86804440a0461404d200145802c5142440e001c904007000c1203500780ba000641501a018100e001d00000c00c141d0140d100c1900b04000351030341101d541c0d807440c055881e40160320511070401e21400420391001155449551041c0c030007040000c00390001c2c0c40b04a0716201c444000070420321514644c110074001c004440310120b0b41001c0d040d1512501c40495506405503200080c01c000c0348007581001e6101030030590b0050301d030b032404588100380111039001c0882c1003072560b10042417401000c03611042043c000c0740e03044041a110840301581f40001142d110125200e015100341c1d060056502c0c0e959100014080880030046040c0074559070a5009108544c0320200c502c46e41c4101810031440703401148103640304 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 272748120 1250 272746870 272746879
    0x13020f01030906020d140615340311060a0b01020c0d0f0218070f030501030f0f0201050408030a080613020304030f0c0804090219090503060c072904050a0b071805 71
    0x12001005034090720b00e92000804050001c0381210640740c03a1740c000040d000710b114003181d01d5141c001c103201e0545918030b0800b04110040005504016041c80641e5068100e40d01d0160b0002d80011005040c1200c1001280050403540da040311151042285640011940700108010304281001039503500c91460080c0c0a40039880401041c032036130001c0d000a058000c1c140d40c100e0390740320b880c041c40c122007154000049440000e000d18014030a208050503640c2c0501c000c0c4403c0d10343e0300d034a02c1c159107240d81207042180030000816203d2040c0054a11200d090b00d550390142041402c118004040c030024041c0d0300e105008100c04207a000c4070311800010b860510000360f5100781001092480760b42c1148441c3c40c00000c60b8408440c600c0d0302c00300995415500e101001e6201c00070151642c0080e914400440400e1040d4004108941c6003142501d2450114a400710b520000f50050402c044400742d034a82c00c24001c400c240918409400c1e4402003614005c0e400c0c048038400340c05100094010580107 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 272749370 1250 272748120 272748139
    0x90f0a030e03030904110c0d1d092707030507080a030e0603072a1a010b0d0b06070b070e0102060a0209030d0e04090b01170c120d03051e070203041d1302 67
    0x1c0d0b10180221004404007030700070b206200c022091088207a00200e2108203500c681c2480701007440c8a100c110040010506c4040c00e11207610040110b81e08000c1c1031401c0c440031400c0d0003400c07180038049030003201c021080503261040c0385041890034480b0703c0d40100441d1300091041e90000c0e502106000d8408412201e0545a443d0290111180c21010000701d03213100802c0481e480a00100c204003224500c110750320103580ca51241c1c1205098028031403485609424480410312402640184020743c0024000c5428480d84c1d445074450100d0968441c8040f0750400005512542d05001c015804100711000750b2400208802190743c52203508000300400c14070300741248840d9125080364024941141071001c195854410301c65403074101d408081c0051245854000e0325080030800b40d42e1034030614024000c4d200f81c0c03a00640107482d009140304d0a401020302d41d80030001c1032490700b50140718160b00954640f4200310b0620150b030302e60325070f40d0008a00b9008000c83e008460720440c20490781a02d4440c031 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 272750620 1250 272749370 272749397
    0x1030504050a050f060a05070509090631050a0b010801150c03120e0d020f070e061e0306040f110109121203110d0b040f0212010308070515070f08090f0a03 68
    0x50a140140081184c0100c154881451200240c1503000b110310940c10840d5840d030030415a00383c0308109003160808a07a500064141ca8031070740156020440c05035900c035813400301d040e41e0705441ca0594128031003a6110144038100c030692250421440d82828141815414003400c502c2d1a061420342e48100303c1e001c0264000c02d072103034041c105a40d20b00901030007a54544540603480300d1041d1420401442203100c0101030090000c3c884085602c0b45141028544442c024003190780c42c2e4041d041c0041d90681c09080d4142c5041100a10650140c880c0340c00c1000705284c802500100781d20010304005224005205c2c03281000a1194156880620703800380ca0b1581400381d007c0c1c042080850321401e400708052401d45200c0d003000a12200841e0100700058100c6581000c0740960081e00c0d9007078104038010301c00101204c00038550b070390007801205c1000f081102c445500c0c6908513a04400a1800244001c8a5422082d40c030b40104940c40039002c4c0c201d4120495544402844004d800c12540d07030880e08 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 272751870 1250 272750620 272750623
    0x50304170a060204080607120c090b13150503010f0914070e040912111203010635010b07150506030c06130e040c060215090c0607150603260313020103050405 69
    0x4030481d8401030964844c0c0c3d4658140f82c80b541d040b6113a002054844c501d00c41d62040c5ca201d10708084006444850240e8100f410a581582000c5417980d4072b8001c41c0d40c00305804102d1107500d11040959922a075496051180140502d2103942c0070b004007508205001240b000d840300019444101485e06002d03103100c2c1d43c00030740903111800d400f0300107510703070310150021540c8003201d1140e6140c00c6041b40c3c4070000036a29150984000d2140b0400140c000407112080141450200d1143e04604010003440c40849c007001e04c20340003a0f0000f0305010000600d2000c10046071a500707901010050104518030302800802d46484070031400f940b0030f400000390411408404040030024200c1d20340c00310000e180038501500000c1090003404094459042d02440c007107181c0a034140305040754400340400c0c0e8a03030414041c958002e990300300c3d589142c041c0410140c50307091041d64021341c05502001d81403040108901540240041840030040c0204104a410b5611075108440c0d0356080c40d00261555903420000d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 272753120 1250 272751870 272751883
    0xa030f0509041505040b0613060509030f0d050d0c02032d250201030e06010f2709060903090b070b131a070e10050408060f09010609020a09180905030417 67
    0x56074803c1c030b006803a00e10420800d90103420349200750303403c000c0342c1261010802c103030061060504d0301c06100c0340c041c4a154450b5000d80f46014014084504201180c1c1440782807205112042000500100d2048094280c901601000c5101c6001841c5004400842c400007801c51001c0384010380410320701c880817480540116428414444040c0808000c031040d80300c2c03018000c140990019040542c007411188004c504281200e00c0c41421640d02480d000981c00010031040b8820260140f0102c0c1048503c124014a28000d2046000094003105854090315419298000ca03840c0581030000c0070000c0d480420242e000500c180c40c1402d804440e00e0030001400d5000c07840c1d412403d0030030a0100340368001c12886490401120701403004416098219806c0c0514410011142d0010000c41d921806060803240c0005040001088190711040a04103a034010807104002959000c0d041200f80c1c0c0c98202d0603035440c0d0b003107c10b0240d410f5076140c0d26540d004500820840d1145000714403000388040008 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 272754370 1250 272753120 272753137
    0x70f0b0124171f09060e1008032d0409111b01021303082d0d11090f090411120304030606080102191101022205030d3204170606130b030a030f05 63
    0x6010140d1644003400b0500007c0d11a65000c40141201091a040c0442a1101055009001c403925100101490195241c2120b0040c40000c00c00020490b12a41e000300e60210301701d1490b0a0780e507040340240039040e00f040b86d801444d5903c180001208500103c08840880343c00100035504c694040c030a50030203060101d103440304c940004141030180880c14028003644030081b0300401840314203055003400e600c11100c3c4039078880d0030341071500c4592401c0c3e25003a40050040752403e650a000c00003041c44c0d0602c0c4d4140e040254070118041040040ca401358002030300c10301000b981006000b8007402408a880f0111006200b9001d9442d0311280007541941e10810f840482c03c2c10141c041c0400c480d5007a0280a4140640102d203132210040340901800d841d030f1203408503080300e0b2111603070595908002000c10754011070020840090440276914080a007001900041c040505051003008481d4032101d00400e4010300700029840e4170380c1c0105901600340d80506001444400e41981215a071280c80c02c03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 272755620 1250 272754370 272754389
    0x20c031f11040602060907061805040f180b100f0308030f180102030403050d05010509070c02040c0201020c030f030f01080d0903120c050f01090b0a020906070206070f0b0124171f 78
    0xc000a05641c002174140c02114001c1c1a541e041340c603864110f070749410500d5078490b0003000304d000308900e08041d8011030340d19481050014140c029105c600320002c00c0c820065803001c3c0d070b29090000c100102da2062004140d00c403440e80c2820324580d201b03144ea000003044280380c01400000a01c0c28840c00505501007900c400003103503685094036003c0c01c507801210003080010303d0311002080038100314a003907018880a40714250f240c0e00b1030382000050080031030704808654081c043c07a024400204040c1c94800c04c02c41040791a1b140402055400400592101c10107510181c03282c840190071107140000c2d40c0c0c00c20b04142411004010aa5000d005000005c00c244543d04412303600010642c84145014801d694504060319040d4411040e801507019159100c00c00b00035420051900d0402046c4991255030200120b0b030b0b90303483d1b44880380300c240e1009035880075070300030091803294500350925882c81c1b6042c00004c2740e503080703001405e801e00100701e00125004007820b9184c5141c4660410010000943e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 272756870 1250 272755620 272755627
    0x906070218040501050705030c07120203040b0703120c020715120b091306050601050910050c0a06090c090e0111121302030d02010b0f060a0e0d08040f0b040e07020c031f11 75
    0x46007003401a400c03602501d20b5460140860780491241045a00403841064040d040c0112030f25041d08115510f5040800d51004000000b6100c01100240961321f0180c0c4490b4480b600e0310392000e040d04d00180c0c000c000c640050005008195040207500304a16851602018002c0c0d2144150010700211900caa8000c03080c4c010032132480008256040300710b10a00080c0503d03190300b4019160341c0a40340c1a191b00c01c02c1c1d685080d0246104001400105090301c048407003540654807407078101e421a04058032064004e80f07083c4031038002d50182c6840004000000c2081d09a40075801d0f81c1805401d905240d0b4008541c0401c1600080c5a15681c60a4006040e0340543c0410b02001c0e00030120882c546004802e030300300000984c9483c00035a18288050744511880040b00300030003000c2c003c000d20072141490706000200b508510445100080c080f6101015503890400e071003135400c000c00814810440d0f00202416000d0785010400142c040c481600c0d62298202002c2c1d544040c1c041208010315441010 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 272758120 1250 272756870 272756899
    0x4060b041a0c0316050c01020607090504020d06090207030203041d1911071b1d0108030d151a180f0a0905070210050a061706091c090504021809011508040809060702 72
    0x159407000382c0b01c0c0715000306d0f01441c1040005a0321180119806008219000e408020a00381900184142200729400088070381e1504d0181c000c0742c11945e01a40147d20114050090854035418040030007003c101d9010245007841c49644007400000e42c0e808800e40303c03c010101d02906e907042d00c003080d504c0400c040e516802082130303030b40c040900d00c5120381e03840180040a415011350030025060b25000d501552511401160b8180035001c0d041c07807940c015180500015652100404110340f00001041f055a1207040600c00000c1008003900c50b071103020f10030042d0002e0342d06c0154140449201202c086980c0c1d54420b0240d090000040041d500340381420100114180d040d8030a6040d0343c030303661240255000d3307203c2c402c0d0399810480e0f624066500c520001c550300700040c010685400264a82840c0194454001c54141e0304030042079401c0c4003080d1041506440c00381085801351211741c0c10766100010b41d0200404808001d00043c00c90a8000340c0d4191903201c076001c440106401500c80c0c201120134 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 272759370 1250 272758120 272758147
    0x806072105071e11060a150b0f0c0c06090d020f01030204120813080123040c0b0f031b0903070b1606060b1b03070201171905090a03020c04060b041a0c03 67
    0xb0300d800802a0703255504411015801340815101e0804644014107141d40d5120a110080c8000c0f00d03105c0940d2500c5000080c00d41e940da0080c001c80041c500c07040e4807180348803100c9107041d40a144c6a48680ba0500003170005445104121ba40d850301164880c2c1d1901005006900912a980005d01003956030f50f20a070511960100416101801901c8401c0d126a00c01840d07080b07400c0c0d401d5040e200207a0008003140c00c94400a500d42040c015603a401015035142c3c60f0700f8899028201070540050b0200030420038454008640c085080e80440b036528002d1181e000985820b464020111303500350225a40c40f404250120a10800d50b105400300289925504030a1141d00142c405800e0600c6600f81c141140ca07012081c2c400d0554181c642c1d0b000211b64000202c80c1200040465462110801c000c800c00300c1b1901800e2f000f1403254014025100702030400a0901c0c400c25185801a41000802c00030300b010242101c00703c1c0c8255a05076030090030100e480c00340380b19000f400c4101d44804590341105e05803 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 272760620 1250 272759370 272759387
    0x151a040f0c020c040501060504030813053609120d0e010204030620090319020423060f1e010c0f05030307020601090e0109020d060e0705031e1501080607210507 70
    0x52035000c40f102c000800341040142c60003400b6400002e6010300041001409000c094010a1202c4020a01c3c268980c40810448408101000c00030982200403800703050b0030703030502800b004804d1252029072034200c440c2591084003001480e00c01400080c54060003100d58440c046007000300d4001d55440380e41c0e05044014090807070341004100001c0c0c401c81140000c07181100c014010150140442c02407901415640151034001680c201da15910301d0315001401e051900e105034040810701090b4100b08051108104414140310b0207492a018401c01001d0b8009100110f08401d1900c41240102454000d90408070f0303a034018054807010052040054003c2070700e0707069814210040110704085010300382a90101d07440079412940c004110f03404540300750418054082c945040795040f40d03840c00400e14000c98415081e0f81134264400d044000b05007409401c5144800f02c0d0410a80d505000d0f60949407400030300b6190610841c00100100e4250350042110310b00e440410800075440e2800d0003801404 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 272761870 1250 272760620 272760641
    0x1917010c08040519080904020705070303090b090307050411070c060906080a06050f1e1806091003231c020604060606030c0207210506090a140703151a040f 68
    0x509003411010690300c150162880b81c0d401400419040d012000c0015108400e05425120040c0c20002c22201c0c1d241c1380000d100d158030070f0703004240d01031840c1802401c04025400540110104018203c25950b0018850f425a00200d5000a509a0747c10082c000c0c0d02c160700d0011b10300140d074900040d0b056044000881140c0e00e43e04d4a4100d507552025040440300c440c024142d0201c00110b40740800e0608008460011903c044100e51a01c406c200203154665500c0200399014902c030104036a40c20400b03c1560012501e000a044e010300710b5840751070000c1103c440f90300c610001c812007030f038519040040d02010102010302c4040c40403420b0009403551030464003641e8050400a001480030301c40d10601d92440d10660140c0420b6080140c80c482c410a500040d407480b9101c100c1c1e410108400b0300c1141c0c02448070500400001416140488400f01c203004420b5541c0c01580c4204041015964848025010f440c4005a030400d0009124020441c03210b859070000d181089140d20909035a02100d03402 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 272763120 1250 272761870 272761873
    0x607231203040b060334091505040b06090d170f0d1b0c05030306040e0f070815160f080705310f0f03020d0203030d0207030e100f0c111917 61
    0x4d5542ea424155108040403003403c1d5891540308810720205070701d2404503102004003001609607070300d12486080c2c0b5102e0640301841c7c1c140c01010401c0345040c1c4201c880f001400e44401e030811740080e000842c03000d9190809005126030000c035034803450301803044a0303001c10b0040502c1e031100400044900180265401051585449541502801c0c0103c1032511919071040055141daa2070ba400c2c00041d0005032420030a5200b0411248004031051094501400700c2400074002148000d1031720307281140140c880b0003040352403050302c070000d903101c040f5800d011154201800192110b00c0119024480c0c00c1c9078880c005070a6001d03418440c0a44c41040808410030f042d0401d50751074480001c090310b1148640854038804c25020001410201c006d01c074800c0c001000e0340d0030840141900300036a40010011070005070a0300c903150040c43c010a20b00c5c090211840c00300710403050030001034008103104402900d030f640c001c240c1e14001d5840d501c81d4451462130316418101566a003a13a089020380c074240c854803e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 272764370 1250 272763120 272763143
    0x80301142d0d020301020301080d0f05130e070e122a030a0b0402060f0a080103170406020a0b0405010e0f1507210e0c1f080a0209060723120304 63
    0x101c0c034200807001c84824158a9904488207841d2441200500c000001e0303400194006160016a4081c40511f0091204102822a4801400c2d00411380e620410004003070100038003814114014000440d429204044841c0690b600e07010816100407a02900c0c4a5000020004408110b440410141280360418208140b070b105038a5201d6615039442510a805500ca28503030004510852202ca8209002511040c80d2041900c1031b00590f902809061003c100d0401c010401c0101846c2e80385d007a400007060003802c00e400d00d40000d4440b100901c010f03210346228808a02481310030342c41407002142c154200d0f280729201c07003501903d82d040c0840c80300f00e8442900c001400c5500901d0105456407503038009052820180d854030006203000a1680394030311400010744600d8803000b007681d0b0800d4944e6000700540f20300c804010301c00440103104020650040c00400c0d110b4035410180c542056101d0f206c0c45040081e20001b014480c03080c0d001070302c1407240c1100c0c02101c8000d000118004c501074240c0340c28 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 272765620 1250 272764370 272764409
    0x170f0711100503090a020105031e040b071428090e0106020d030b0d03080c1606051510030c0503160c0c120c08071a09010c02090f0a0c08060634080301 66
    0x480f80001c9903002079580185c0d24240056205100650f4000181c0010f00d1046500b5807500d604518111021512003404001f4031031a1f507000741c900002c00c48075440e003c3c0f400b04009000304a0740040c1d0005140c0266149806038014090102c1a003d000e10140b050710b10f41e5181c400035507460b8100c1d41040420702d807665405c40307400e241500524150b00742e20383c1015915014601c100c01d40c850303400c0310980a0300e0940d040028005000e424040d14550701e40d500c49260700c2c400c2281c548550010041410b1401c8860003003d900102501d5000c20090810f0044022920080e1403140016238014400d90100380f000c561038008000e0741c0311031801404001d0b100c60310f03804000c1c0d4800050040b001500400140501c000c01501c0007400c40c11011700d000d0704840d031694040f4064660554410180340d03c030784200072010080b4031070360310301110910b400209410450701041da54461884400c2e004048070a0700705400000348801d18131340d00070100c2440180c000f0304200b0540e800a000303810010034031038003020 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 272766870 1250 272765620 272765627
    0x90a090b060306010f0c0807050114071106010e09071a040801360206090d0b0603010b0f060f0c01060806010314060601090302011209060b100903060605011407170f071110 75
    0x61150302400052440d1100c0006403401070f00900d116040040ea10407000011b56a90043d1001034456070010842c409401a401c0880b040203080a080040d09008800100320001d00d250445928612404840e260602d102c0c0c00c0000d1a000f0801c20401d00d07491080b9108508020003c0f01c680100030040301d1103100003e801c0c00000c0d00c401d810044440c0c81c480c2405000e03000203041c20f100901c2c0d00d00d4120b0310400705400d46400901a55101840402c0100c141401e0040c030308002001c44d82001c2c5a00f416002600c24000c00b0350201120754041400d1280c58003d5016001400e114003c45141d50703940d24003c0051140810390408600030000420b00710b5015840500680c2d50503140d02c003c80e0182c82100d0000e010414058400d940c41d60341d82c025680310a41310b0307070503204039544190883d815403c0580a8a0890740700c6410012940d04080922442c84180c0e1000c683c49408400e5071010000404031038012144140c20000000400750200700300001c031a05020070a507144c0c180c41c111414190b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 272768120 1250 272766870 272766881
    0x40f02090402161a1006030b031005040501140c09150903070e01120302010c090506031311060d06090515030c13060503071d1612020c070b04080102041a0c0703020132090a09 76
    0x1701400c120710000e01055000e908603001030341018085a140640c0d40c0d00600680f9400d0ba4143c505954030460303480440745800700242d01c4607802c202e03e490006405d001c90308034054640d041c0c50203640032500404959017400440000e104660000050b944c481d9683d48030000310b0101103015618091103100740c240030301258800c8030300041c071960848da0342e0103121000d8001d2003821a981106141502c0141e0b0b101c0024000711401e18900040003810095410100c0b08050040c0341401980c031f25070411035400140503151804260fa1241544810140710302c06420b054110a51600504001240c4004c034060080341c0b0400380b02d10741d020307a128550300d805124800c13004100056848040074007985c80540090015008640484aa8558404400c0306a80090300107403441d9400103001c00c0005099401110139500e8410054038041640581c0c40e41c074800b80c80028140001e010302c1c810342c4014200122003c2001d429a0031180c3e032494803c4105501c12140303184980f00d01c1e81d020a4203015031045 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 272769370 1250 272768120 272768131
    0x16030e060601050901020a06050a050a06090501030b1503070905090c01030f09030e09180703080c120a09090f090f0f12050708030406021b070b0d051e0402040f02090402161a 76
    0x181285031074410045626900180c580e03810352007006201c00015107548112841141c40760400207a03800d080c80c01034103460103076011034026400c2030014070114003605000c2d6080140c2c840394901e0780c07084c00701007400c000c584c0e030000002919090800040c55000b040d20040d0340d909a030200040590207401008862601e1805000180240c6100c2e8890614941c495000402c4051305003410f10b20555039403801c5016001281d8412010818030300090b02009242e07030710140325008034100509590000c0c1065000c1c0328180708103480783d2968039111b4580c3d0104031815082101043d0344070180c02e1441c02c1c00c0d0401001c686040503030303c00c004810b204009540d1160751103105103255444984400029400144c00565038802c00d500704041c01e11704000c044000c2007103106007503c603407110018104440004001c1015192001c0b5002160382c0c9204805a016504613000684545a180680300030702034201c0303088d00544001145500860008030184090340b260148020003107001845003540d51041c0c41 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 272770620 1250 272769370 272769373
    0x221010608040b04150603241e0c050403020a03080909070306062007050a03030906020d0903020a0902070c031e060501170a141002030a02040e0a062106150305010516030e 75
    0x424005011100c0f0140c0250007220104860640c0e500c13140c044894640c011512000b450686100460950140c403590002d038050810601544148903541ca5039030203101106e560f90380070170300000b07409041500e000e95006007989210944030b00d802c0384c2ca0303400130400d54410545500002d06280c424000d010955941e41c0c1c07500c41030410640f8000610542c05810815406100404900e07504c500c01a00001c1d80280d44803852149440006402c003a06046180304100d00c07080e0074000350700e800b034880c8200e0b440400c4c01640d0789201d003441160f945080d0001001d4202d000c8a0190310025103001441c00e074040c8000300066640c60000d155180c9100c02c4000035a049034848901051980400e03c1906500c0c9080c2c512048a4503d00300c00c0782d01c1100c16050b801c1e4080380a008026500ea202540444044403c02c8000d003004200c81c90500c40e611103802c4808041000d60411440e40c20800300c402804000e00c1c400c0d604c0e403174401d010f41000ca8586905404441c01e40400074402d002d4030008126580 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 272771870 1250 272770620 272770637
    0x302010e150c010203070215090601030503040e0405030d1b0e06130306090f08031608060117011e0506070b042f041a0607060c090603020a020316030e09040602210106 73
    0x51160410074100001c03007264050112000d042800e000031441a4036a0740580f122402c4007007004005600507240200c3d0f548104c4c01480060b400204840590b010050402400d98640c47c02c185580708004c80c1404280c14005e810600b000c00101c280809030b07050304e58a4101d681141801598060b45800220b40072541d482003003c074060b9030280d00c4c124010952100428132540b2007944a92082d14860119810070307002c10240c13079209240c0c640003d07092809020310701103114060745082040c003844006d5924000f041d4614002c05242c0d400402c009001c0c01c0d2101d45600b8514041138080f1410364519200c100c0c04503d801ca00e10040c0c443e50f6503041044124030941c4e0a01004002c0c2480e420000d50b0fa05084c8030103075880801406480e44120350125002c021001c1c000c11108042e8007010a050041c480d04003030380c0d008010303514109000c056500204295080464080401d560400d401c48406014031007401400c0c2c00920030000b80381e011002c079003640c5078480c0074000309120380c0c0002100030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 272773120 1250 272771870 272771897
    0x60f1e04020d020612010b04140103090f020f2808010c0212040e06010903060e0d0e030c0a05091009020a02101104030c0605130302030d091d13031110050f150406030201 74
    0x2014960003543c006050b20781420750360034210b96100300a8020300305607036001c902040000004160894500b40030700c0c05004405450b680c014999001c403000920421140c4008102d90b142d4440d1901007412480112020085884c00750300004800d000e10b038840c2d42040030741c0d1501307800058004d01180203d11554581490306c22031820140d030282c1001d042090818000000c1090b0303014443d041d85002d40681104907000d40c014000f0340d0059450382c0240c00110155400e40d071203030044000c40f54150380d04881e595030f1184150400e0520740044003450320204d86a60300300da0004a8050900c1031040800c000e103104080ba01881c02544001131070321080380c0d001c0c0402c2d4840c0d030240401001c4051100320319601e079070010f814000c82c800ea0400107101000200000b140d0343d6684540380f44501e426150b6030034080e0189108016028029041c0441003240707100180c001c0080d1f4140510b500ca0400c901d0420052006810038161000080f200d40c200324141645420b01c0b504085130b03030507107612141c200725 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 272774370 1250 272773120 272773129
    0x7080111040614090a33120903111002130f03320f1b1207030f0201050d0608010903080f090d03050a06030b01080c0405090f0309060d0207060e060f1e0402 68
    0x215a0400e040800900100c3d0403601c07061304c0e20000d011000b4110207048551081b01c1c440d1011000c41c140400c0500034084055034020040ba52a1071154034040b0f030150382c40c201660700789485008003c2a101c1e041d650f080741c60295010b044030320402280034139010f9507240a45461005800060000410101000005001e01c044181e802c11440d441d03000503111340c0c4849040000d5101c121403503030084901400503040c8014294210b0b803085840407030007050001e032030303680b00070070700004201d140c403040f03000156800741c8243c0310407101e02682481507a4607a003600e4080e0484a0b411000701c0e001c100869010b03c04186141d10a500540003003200c91022202100581409010382403041ea4910001c4040345100c40480c4c00380050100914404c9003403014041101c800605029403500700107038181700202c000c400c90b0f503042c00032a001e0761290481c2d00d01e840240300710800140750301d00d0001c60340c0d2400c20100da860721580801c0c01401407603488000e40210058100d80340d60107484c060300000c00506d003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 272775620 1250 272774370 272774387
    0xb0609011a070f020d12080106030e0c06090d1b03030e1f1832060403020a230d050a1101020c0109061b050d0809070909021e030c04050c070203070801110406 69
    0x1200c40b84003540c151340115080a41c0d160050380e15507644c43c440c0500c1508900c2c0c95004114518042000d0416188610340300c1d07400c1c001d540d2013444c0010b0000c0301c541c1c8800300a85255048a2008103846072080001a401c110f48411404290000c0399039601e031600c03525400c1c2c0b02840c40d40700e401c2490b000a04540005094a405d2040d0882c0710010a080364200c10021068824029810745240512681d60202c0010103640c0d03c1088104024001078441e011040b0868142c3c030126403000301d80702c10f061100702104005039001000d49614506104000604000450041c40c601c00d6000c0040012615200d440040c6808100c00c034200f086002e21400e0031101d82c00d41228000c010001556501d0704044264000388000768602d0f080c1f001044041c040d5800800e00014208401c0c2030035400704000c548221203240d00c2e026820001e19450310144040c01d600a40207004000c03d00e00256005060340000609a0091040d405c0115402c207051050320500041c1060140c1410f00e4000102c0e80d100 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 272776870 1250 272775620 272775623
    0x406080c0c070e10050306060306040c0b1605030a09090b04110a120914060f070c03020705121e01050a0f0e0a0209130b0403090510050306010e1504080303010b04030b0609011a07 78
    0x42407050000700b05082e01c40d40d900581301c00328a004a10b103010100b6107402d501038000d600c240c11000a00c000941184070502c11910441200c0f502e6000320007524002c0784055a0140442c0000274070410790baa40030010f5006e440070100108030155192090004032a0414005040f800d820490061542e0086070026201c20340901c0c0400c1d00100c994402e4846140320500e9206a4090300074805541c0600d406a40c0c40080e0f464038800391012511b0095031001c1d148903142c0501e22032001c0c010700c401c0c148002d401d10050030b08010a0a8030350101c96008200880d441c078500c0b40361590390748400d00d45000308810184032000421035010f00790204203582102a00c000c51080811754000c0000c0c80100796148224082d403981e103101460f01c42800403204002c1020020004104100300090317030098850300c42040c0503500f18442e1005030059086505c0340350800c500301c2c8000700000030003444c81c2c0300a10a0740c4c411071000b001c5459640c240020450203020302d1680d51501d01c0b00380491340c1c104000e0b0440a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 272778120 1250 272776870 272776873
    0x140f060a05060c0106031707030f050c0a03080402060910110105060d030903020907170703050105010836031e090406080105040b180304090615020c03070501050703050c100507020703060e030406080c0c 88
    0x110303542d6072603404101151f4914042d2440210f4000203154114500c1c03049421281845440d05000030306040d241e94140c0f000509214111000c03900355100e81c003e43d81c80c0c901c050001c500000080001a04480c2180d0503500c42d503003050000342450800d82540a002d035070584640780454151b40c00c21241100040c2500108481d40507150628100240c0e4107001d01d10315100026554104400188020702c003c1240c1041440384441003030a40e04803115203010140d074202c018070350269205207401c500c1403030203010007080451400b8001101480060907a0340f81100c1c200100c9a5030384046007628000c940c0500f508542c1800580e6180c40c00c125084000c501c2c0096078a03083d1140305c2c110486646401000d00c030214003183c3c0040310340400c104251140c3c220000d08000d440c040c0020039a1140380c9006040101c00b0404010000c0b04001c0204003040038001407149181c0804001e558105510054a0190500d41303041e82010002c81110141c405646d20380140b41e07120044079a4542c0401c1d81c8003485d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 272779370 1250 272778120 272778131
    0x3141b1e0d081b040e0406060603020f07140a020301020d0b0f04061a0a02120f0403150e100902010e030105161805030703060207030e03060109150b1908041e06140f060a05060c01 78
    0x18051074100800245c20a440040824202420188200d43d1113400c000306061042003103240800780d003000d607505280e000482030429170344046254105100d5460094056001241928080541c1c0c0c20400b201001030b2440e1492480c3d030030812003a26400d100c0c9505210b01c442d400d400809012005002641860046072404101002c110348142e003c844145003480b0045010300c01c1240d0f2401c3c1c1c500000c40c422050184110324184152609840706401c10031940c0c07910903c0443e40116020310075241c00a000708110f16140390300c0804da5816044500014840c480a4807008891000840a89030064001d045003400c50780c400b00250311540c000d50031f2180b149030031085a6020821746018000d80f0a01080188045000c2c000b1041c0b180c101c01000780c010701507244542020056200c031445103240401d10350319503050500045000c1415094182c40000c2258244085a000445403c40e03807200b000c0c6c3c9940b0140044828002a9001a40070040342c000b00250715044000d42503281c001e400001e030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 272780620 1250 272779370 272779411
    0xf06050c1201060e01030c0f0e010f170f070e100804151e0b0312120604090c080a0305090306010f0302062a010e1b010c02011b03141b1e0d08 62
    0x2152100f60322240000300c40b03a4803222a540d05000701241c00b507075401c00d0101c0080ba0039015014808032410141007100c0340403800c1e5070354404c00f990045411f082c100385645003003403401d0101280c8100d4008004c0340b48038082c138606080500243d00a910543e031511030300c2d140d40d0f9881007403800321152640c5494450411600c030380c2842c0380e170081642c03000000240f01640713241854104101680c496440905c24840b150140c09a880016480001100c0001e502900e51415000c15056a0810305803072069500c1b810070140c0003001846200750440031602c25a03030300e1416005203c96400000c0d0400340a001e54100d1003010a403100390381003070201040380700700078020301821126000280300640d4094400385030796100000a24101207828a0006580f83c1144c0007c4c0804110308404400c07008059264010b0522400300307440b403550300300d140315500e200d407030f80da0051100d42034030f422082d0059410141c0851010340c1102203614502d8041c011050b1503442c00e5440820080c94110103070703291949a107 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 272781870 1250 272780620 272780647
    0x90b030c060c0a1104050c09010c0501020c01020a090306110316120b0907121d0c010f050702040c2c010e01030902030c1c0b09010603030221090909010203090f0303040f06050c 77
    0x1a0451950b4020049001c4034189008454051820680101e11344403d00a40340b40c45c0b0203c0d804017400382800c9407090344a141c840c1c0244a0001c513100154400710b070703000056500854030070480340100014801c1580484000c0000e200603070300e45c6481d07030302c003070205100c1070107071070290502c040c0c030301d000284484038102290306640304960000000f0048044111144501d10800d0541d96220403a0320104144817946541e400802d1a0b0506202c81c0b14100718940384980c007110f140c02e41c042d0050255248071080501181c000c8420643c820901032180742d8a98049407494050308016564004601c0c2d4810040d8000c0692040583c0c26004010301c000594441031010101004200031460a06d56641002c820460010b0924007159040000800100b64005900302807524451501c641951840600300d2552040d00d000c0c540285041c13007085600c45040d805944200c82070720a0740d4041c240101c0c61034980c88222001451079100900120105000342d00056200c08010302d100d260141032a40345 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 272783120 1250 272781870 272781877
    0x403061812050307020f03030114063a0c0e09190e0601030515011502060105061308011b02061b120711120702012604060c0e270619090b030c06 63
    0x1000702c1d000100380701d402ca03410090b0460010b5050065811035040100301a292203091a404d80704040205a5440d14501c400000c08452101d10340915129800740100721300c040518010110789103400c2032072440b0b85c000e0b070418100320402404081c00f0780c2e0301d031b404590348035081d0504032030780d5510305080030700000070000c4a000e58010b40052110b41c1d00c0100282104030141c06c041d014152040d44140315540004820307041d01c604464241e212800300d0307a0301074203615a5101c14140c1d800c12099038440864034004924240c555030a440041d550b001741a4000b028548140c080072404029030700d0310700c0f1038a40c0c1d644c02030703400e24090003030b00c1f00d10a8032032524400c40c440b0056084001903105c00c561304000c01c22080c000c3c81d50010101d403440e08003a5000c450041014184a0300e4071010014980f082c0065031f4440e400501514015102c1c0c80c414030841650b9031341c90246501c200204950785001300c49502c0b034ac3d5502034154020344c01c140e0701c0400351070143c200300d030503125003c0d801c0c51580e1048044e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 272784370 1250 272783120 272783153
    0x12070207120c09180b04030c0203150705090a06020f0c0621101805221b170c06030108250b042c0411120703020915010807020d020304030618 62
    0x5400b4160910344401e003104d80c4c07407280c1d82c1520b0710380601303070b00007181e080042d54400c0e05401d042c01d04000d1400032a08004e548104031400d202c200080209103500305000e00103510056400303540302078030780304203030b94034035103951030341119030002c00b2085480c64070100500300f14904500100c98942109003005000800703540317004005076120740074055035103c001d10300e00c031ba80e911200380045d04084003640588000200f0262414100300305800911a41034125a45040c40068100d0300550b00c0f00c000c02028840c1030400c495004e0034a080c0c000d490b20f001239038140c49800c07003e445400e02000203c0c02c041c0f00c0803c4018603a0a020303000500813075100c041e20040030245103102c1284c040e84842101c024803200140a400b8000d018407010802c00c0c883d101465100342e60b244004204010a1464905190300c02075100040ea0100135486001a42c0000c80b20820380b6003030442e490300300061761909604005c00005074418030042022403207903000308031500500c01c5c0d01c038040b212644980c0554a1100e40c2e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 272785620 1250 272784370 272784383
    0xb09011404141611060c040603050a02210a0b01140a030207051f0c08010e190b220204060e030706020a080a0c0f0501090b0109020414060f0f0c0c0f090c1207020712 72
    0x5803032000d0f60300040c1203560000b05001900d4245018000048036000e14010303081010307603c06c0041d20030501c0d03904842400c3c610741c660481e070740302c0600400d82288003210040340c60340c24031030f10b00c0495018454070b04112201341d840504180584501718029080140b09071510f04c50800f420160910f1103c02c00c010400820000c1030300700341c4007005440180107901801c0740c842c0e050100001110491158040c1e60b0784101c000c0744000210b030024000861f41c840c503c070098000400020311501e640d00030700480312591650000d0380c0c280400c050b00c03001588904005600410000800540d08070024005146142403520307000e070b916214945481c00c2d14900f00c0d4107030355603058030f800c1c03141e217407480c600400c001d490561a050030019412040c000f0103910501410b408240140340c4440348003030702c105c0e1601040c501e465170b1449107526030320f10304000c03002e00400201c202100300d4140714035203e109000078440b05140402a0b0300c0d20511600042c00301c4114011035030040303105080c0782e41250703950b0300456 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 272786870 1250 272785620 272785651
    0xa0803162604030906050c1b04240302120109051507231c1a0112060302040905031b0a0c1403071806180e071a0d1104090b0102010b0901140414 63
    0x640134082c00a240c2250052040900c05092a00300001e1260907146140d0810358413a03032000b02040150170751000344180c07000c0030b0464007024420300c0300510450b40200c1b40c0450208659800c00d00701c8041e0800580242c004101c09035003007812143d0150003049a160840e5600100c1d8489580305492402142d400c7d4800582e507190350030407800010003110f20b07242c00c01c5480c1240704c22081c2c170aa080206410302a078055201c0118440b64020390041da00640b0034054212245000350302c0746c0c0f00303a4045004503004066480c404400040055138540e009910a1150b0304140c1809001c04081c00c103a9458400c00d100801e0b405048190300c55001060348000c42d4035410840c101c4c0426a075880448120351600c85901c100c514001120421520b00e07181ca02d102c085903c40740d044500c90940c40080d8141040358000c00100004020403c0342c2040c48100176440700100120300303846c2651011a4040401c90050201c8416110b00d21540c02e002400010400068066000000411103034400303c0c84000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 272788120 1250 272786870 272786873
    0x3050712060b01030e030306210d090e0c0708120405100c0206070212130308160c0605030601080a05040c09020c0a0b01030b0405070f030b1302010c050307060c110a0803162604 77
    0x40c0502d001c06070007420140402250740c5d40b50baa50307010040c01248603101a1168800b054401c140803040078800301c00361f40c802144010080c1001249201c1d9100400c00040041c0008015506554286500540081c9892141d101c1124403200c013a200352481c1c010b1a0320340c0d542c0b624905c1001d0740c0a50700d4001e400c042c0b400001c043d0a155042c040000f00a8080060595003180444000140c03940b0804550300c0b00700c803a03200c069908000400621184403000042505034018000d5480794409a0340e04ca001c1d42c803844400c0645030240c400504001032850140604640d903000317030076410341d118100c40200c0c12944a0940081003039206850303a11558050100b44001445a407004c2e003181c100486255103560f0390740440342801000412005040c400e800e0440e0302c6000d111000541000850703445082e00c0c00e00c2002040c80800040201703410242c84a10307103402103034070316080d03820204460171990b82d800c1d100031052901312178100b00034000d440101d59455110030001c6101800881e141c01d81b415 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 272789370 1250 272788120 272788133
    0x806070e030601090b0906130e061008060a1b270306061508070503040f080706020d02090a0501020c010507020906040204120507080c2b060f060611011407050f0304080403050712 78
    0x1a003288031114200170f03107440f003500c0c0c418a007500310109903441d02d00c0da141030940c14010000003800c00350a00a0000340070110710072446500944072000c05031201615280142c4d000c5030604200442c1421000d00d51048450003990900034080741220203089150740390202c601110200d40003141c4d83d55490005001c450203c89644038a900641403515044c140440050401c1c04020320040c008089052a01304010802042d83e000540c04102551205d0074040448081e40048803868060444181c00248541c4001050914014182c40d1245032011580900000040007408a070300242c0070800040c50714000b9003240c0c0c0c02405003010b807001604011440d4248000158828841c0c000881455400d2118619100f03804500800c841c10b10f80940c41d1000c082d01d84020884c250030315040c00010703030541080700f0100030082100200105c0c0500390845411441c25680300001600c140443c00140c1c80e0302c40103680042c020760100c1d007071503a80e503189803038100c844c0c00c0300880ca5086000041001070 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 272790620 1250 272789370 272789383
    0x911121f060609030f0f02060706020a0f02150a0b0d050a0311150c040603020705010902040507020c01020c030601030503162a050f030303060d0213090501060803071415070c0602040806070e03 84
    0x8600040c0855407410b00001d240120b01e0101504580324180c0e201c0c20480340380303081003541d640500840d4441800d401c101d4001d412454420011407490150003041600c041401913400340c66450100a64a4140e1040010041600156005511501c9100101c1c508200ca0840c9608c03903a540c0701041031920086090903c00103185685802c80c0040c083c003000b980b01941d050340c0304d40c64016100c1100f4104140980710b1000040e421a191200380403c080d800b10f81b41e03002140a030202e03260107058200b1705569010034480501960014080e04004d0b4080c80342003040c0724006d12017281205540041c2a144409103240e00c407040105901c100400c0c1070114103500d800740304a014600758030306040412846003c101009104604c0c100ea4000320002d282d10210710960000020024180c4801c15180d803540804815200504459803100d000070001030001d01c1c9030700b507108407425a12001c01c143c41c181a444800c0311501c1e000c0c840401e920008101840c420b601a03078694a0750300d010402c3c5406d020 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 272791870 1250 272790620 272790673
    0x60203040c0f0b0414042703080c0f0d050c0702030f06060f01050406020c04050a0626100603170307140c010213090501080706050c010204080604030530010603091112 73
    0x40c4a402c200725840240054404440c6880303042c1c1e015078000c40004005000000303042c072418480c12850545944101d4020203036511a442c0c54201e502c03501e030300790032a008030f01405086240c01c2144d88001d03c135541020303802c181c040703060509020300c81d80000e0400c000c004403d506540002c04110007407602103100e44100000707080840c606424260025180d4400e410168015521000803815240641c0e101d50001e281e6a800c00140d0344040303c440c462892202d400c682c41d403103000c040010a1110344914411a540440300200d90303144602000e013143c0009043e03000303005e403013042860461207100081440540d03d000050381c035483c0100400e401441c0750040b0202c18a040300500c000305000404900341d07510741c01d105460320300c940340c1e55000e48100c0d00154145c0c02032100344020036810201802400302e200c1c2101e030b003042c0038a074013114540c241000c070070256410400400c401406944101011401011600109107984010644001c840004100182d21224100300045000d443e11000b0b070 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 272793120 1250 272791870 272791889
    0x9021809150708160e15120c03010b07030807140d061d0702030d0f09080d050613050f15030309030109140d1d010f02071a090406141e030c030a060203040c 68
    0xd00300020003c00c0c540004003c1a040144a59007860641c01043e03101d10080c801001054550a50120b80000e5000540451001c4400d403000c0f40b000070102094034107031440910700301d08215058400315180103025220109000b400895042d442001da0028031074507036052804143c1c20302d44400400307400e450b2500000d483c408441031100303043c3d011048440452520f1004603c0c0d42d4142c0c40c440007060420b40081640c100040c00c80e8030f6441a4114034450442142c410510003100542001a2142210a049071200310310008548400b200760060030b1140140850b820441b40101090071604008400c1e642508070360f0068190403000c1018561126461a0041c56402448400c040506808541506000740400d05141a03482044054010401c0d800b9074480304a000d02200c1d00b5512402e507090060f414410702140c0c0c402c01c2085100d90741f1024100c5c81d000c40f80f40a224402d40e80305040d080c1d243c02007004080c0565010046155842d00403c40160340c4d041504e002080e056245d407014041 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 272794370 1250 272793120 272793163
    0x30b0420030d0810080708060714040f03020d1104020711030c0409020102070b0f1905090102100504031b140d021506030a0b04080d0b06270109260109021809 69
    0x154070042020000c11505091611040d02c91500080b0b68080da50012100e610403404000b070b0740702e000038034940540720395168218620500c00c2d4049003480b41d402949080c078034501c41000142454107000300007600034101c8541e00150803000400303030b034811031042c0c4a07404000d00001c41c030301c0c051040c05400303001180c04000c0805c8550010352960101d00c0340d0401c542011581c1700900031034504481c0325040c400c42402c0469401500a00a900301c44407e50042c41107081140c2119501d100d840d0080c0e406403240c83c200e00310b800b8500b003074400c59001283c81c01c0c070050403011081801c200390007100816030003500816014002140c8205401444244a5848004180003140500d052140c1240c0c000e050031795031300e001007000000341c5402e4030060b4024000041c20030006070842224080c074280e00091144005958004540e4900c044c003440d012201c800811103024000c40418030082c8079440004500c6a0310390b00003520000110700007018000c0c43c40c08005030440f0500c0303003d96440904892848 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 272795620 1250 272794370 272794433
    0xc152f070f143307080904090b0f010902041a07111e0103050c04120b0907080a080405040e0c0112021e030a050105030601080318040b012f101803031e06030b04 70
    0xc1c04440000f60010f1a0300000e00a0501c500b00c0201c070408440030b00148494603407464807074030400003100c0c1e01d0200080c24002148144c402e0003202d0840301b0503030070281014090841d112440d0710880d400c0310300b170000c221071203440e8840701c0c801d100a07022074000042d03000c0d00200142c02c1d01c00c001c0006ca0041d01c204800d01080904080c1d5032241c941102007603c1650b034480000b46440700c0c0c1e41128915104003281402049075420040080d1030301944c0038441d0f03002c03080d04540d450724000c0009001c61207285543c04000c90550103020380c0301d00c891602c0c41040090035008140e40c400d903501c03c5150740f590014011820104540b07030040044100440c549805e04240920a820114031544980d881d516451301580c0b1aa8a00916000400303803c1440c28000c40341c0940451810304404040c000c00202c180100068032031b1201c440000c82149100b800c0d196811401460300c500341680c0082d00c4010352420140610a850140d44036030040c44e01401c00f030820700f07078100c1c5881c039640d100c400705041a035 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 272796870 1250 272795620 272795689
    0x60314040f030908010204090207230a11010903061407030b1c0308060a0321020f07050d0b070215070c060f02090f0d020307050d0c152f070f14 63
    0x56006401c06040d911568452804032a180700381d910122040d800414003040500295000300000761241d2002d40741146101c1a0420442107180f07412040d412a941c408041170082403c101d80d03540501d0404a1961240d840034110b0302c8034200010600041000c10020342c0e0035110f42c00d942c8804544d0104081c4003070044c0c01c00c41544801c010308201088022409580300c0525140246600605030f04010180300307034100c41c80440345100750040c03142d00000035070360720042041c8060b04c1002d440010340c2d031907944418005a0010b4036000461050341c1c45d950425540703c80c0c0300c5c003c0d00c89075505076104065040035010ba92003062000c502910402c400c08031995140603480402d20300366a100507100e15800000d08010f80d0342e0020740c0008070307a140750741003110240416050310061700043c2c2c101840b885003100c4c122403103012075003010641402802d0100c0381c80c005d04401685482110b2406031660000d01d100c2409601030f5004044100f01580c86c2d19020340850038020580e00300404511100d000c10 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 272798120 1250 272796870 272796911
    0x6090105012a03031b020c0a140a0504090c0509010b0a020f060f04021309060c030209090c0c061f1d091b24070206040803040501080106030905060f071709010b01090603 74
    0x103420b0502c05414003000c01d4003a130008000c0211854400000310f10a100c01383d1210302c100700301071054905640108030404044030100714401c010f0704104c0c54500740020300c002403850360f10540700c00d15a440001074654032011818007800040d01807179103ca50310f0700702901e82406c2c0e03107555505401179010010220f44401c035039680301c0c0d0100d0f940410480c0c0c00c403130100240ba2030381000c2d25007030400a5064034143c00d0f4006101d0350fa400d80f0388911507540c1081c3e002c5071740240d040c6a2000e03040f0401181c420030311442c02c7d14042246114aa43c51942c8040d400c0030620003594062042c1d00d4101000740213042403081d0a1015500b03540440080c00c40340002d800c044801158004610000001113890032307200c420307103a140f035020b0702c0701340c0e21510f403021150b40380c01502c10580020524400401c800703101c2d0080e40e0100e0380c00702c020f03c896210f52139450b00c111030043c054420804000540140c4050844040740254036902c00080c5010090000401c050002d41007201494103141c10500e8004c40342100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 272799370 1250 272798120 272798177
    0x1222031205031e010f06110712060e0312010303020a030e030109020916091205070305070803212e0819200a030213020301061b1113021309050609010501 67
    0x241d5255180b07144900f4491040140510440b03000d0004181c040c0841d01c180242c6080ea1503244410326176140791a6140039501403150510f20061181000a1072030700940540c02d540c000b941c6c00c1c8070b000004c0c464032090903801900140d10050619051540019260104503800e50086c07002903441e80200c1d040c168080c200030b0301c1d00500481e0041d000c0c803602d00e40c000b82c03400c500140c0b1070242034240681c0d01d0b145030105503085c3c02400f4001444140c004200d81080f0701201840340103210382213132200e00d003900800c2c40808490a00c1800030b4103c0f0002c1d81104509034a540100c1ca82c103001400d494110000040340b841c0111000c0c400101e00e81c83c510301e01d14000101c07030300e101c2050840880d9404a49500003504400003903070548000060b0340145050f91611369560041d06541e0141003e00c0d0030b940b1000e81511340110098029040c80803510081c80051240586004003103000658990740b0365212071100c035035901c107120144c500f01101c00d006240910f41410b00c0b00740f81c9800b61000c49030904 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 272800620 1250 272799370 272799377
    0x9090601020c0301090c031506081209030106051302030a0e0606060d0b0f09040b150604050618041e0e15060108011509080a03120c0c032f12220312 65
    0x24806a100700300c500240b00020b030003071080705524030b401e00c20009180012140700313070610080310003000140b00d00411111910001d00d036600c158a0380c400f07180d1040c24800d40554a8580200c1d0648a000c800942c0725200e50005a0b20700c0e002203030008840400d104001142c000e1400e005e01555800243da280b040078480c00144080601b0000b11079001000c0c101c1e0b04901030404120500429080b4103108500c24440440c04410403000c0165070310540c05829803200c020f201001c000815004860551040507100044001d0440e161841d4a0303401f10703c881d00c060712007030303a11250360061000c0c284201c07580034260390320f040040000c0c001d00c40500610f40c01c0952598204860b9128181d0070f802405094191800b068090500826407038a64000904050034521a5480940f0500010035650f8040c0d072855a040282400411404d80e0540c281054401c1480b5136032888405014480f45044042502c590b1124885c880009a030120ba558401d200c01c0c220081001c00d150b1000c4000c45225840d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 272801870 1250 272800620 272800639
    0x803030c0c0a06090327050108040312020c010533090406020f040e0406020406030c18030803091f0b031e0604080304030314040f0201020f030a0e10020304030b1009050a020306030309 80
    0x5040714980b00c0e41070000f07000e1074104260f060038590043c071514041d441040b2507000005044412200310900c61190a000070110400100030030b100d070396901c40340c040045c0f0144c07600e84a0b01d61142921070503078418a000f0800700d100ca445070f40c134110030050300c81001500104260700c1f0340060300310360004001410154000401d210800b914000f103030082c20b00c1800004040c1032070b0900030020b40180c090f810121345480b010406c440e010317000c007400124100c0e48031034805081d40d4408015800240103d20588030303644030903c0361809619078905180383e0140005401501100305490301d0000d14107089107202080ca00020402d0100d00c0c03990050b04401c1c051343d40c0d11107240403002005c20554040280c1c0c0701e4801d0101700942c10003400841c9000b6400ca1712401408001c0c1030310703807050300c0741c100104641c00320090130b0b414009054074603e10140123503410035660791500d507480c82086504400d501c040b40d100307224103500d81c480d00d0381210b40d10604509625102d40440da0720b01c0760012080c425451340f0b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 272803120 1250 272801870 272801887
    0x8091f0e0a020904060e1902030d23070602210402010207060509150d021b0102030c0412020d02030319091203050301050105070c051f0e06190c0c09110c160803030c 72
    0x1004400c03a01c56000c1d1460250386003a0400c007000f03240188119400c0c7c040e110075212200110440711901c160018080d06c8000748a9805548a40c2c0c10b003500f01aa640e12000040181c100364054132805005070005655883e950381e00d0710b240300c2c1c50a1485402340c401024440540d900080d400c00380e840328103010750703101124400a4010045071241d801c01400028001c403804c510b503005810301c1c0b404a104400c0c195001d0f000b4500741e010440303e541244400b40020450500030201c0c602c1403500144c07a40398556404e40103c1d0440d4000000c0d500c40140302c0c0384030031505034007800c090010301100d41440000305455900030075511042c410503040010108100c018000d210410400034032009124200212681c1c2c0131040400482c0f0540340841d840c42507c6085042ca8011910301008661038180c00349040138080e6050603201805581b04110400d02090780c414030304c540390000c0c0c202013506447c2e81095140c149032100c1404052070500310418100008030000045e29080404006d0b40ca44aaa21 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 272804370 1250 272803120 272803123
    0xf0905070513111c0c0c030e0d0602040b0d02070c0f05090a020927011a040e06040507110a05070f081501090b0402071704090b060307020a0609030c0f1208091f0e 71
    0x5000f5419103010001414900b04d0b90403c05010380100e031550240841c12540c80240c40c00555040060049514055100e8151801071050300c0500d00c80c403070050900751030301172010303039504100d61941003503600040040902c0080411080141140902e200a450514020848100000d04007200d2943c021808407865a5107400da04c454510858448201100401508901820030310500b020044807120860460002c1c00c100d50690700f40a20811040c1c845906200041500810420030005155182d4008440502c0500b07041405400141001d500703181100c1c000035043d86c0801c0301640421581c102828801e0b0100381107908458001903010130010105000c0e201d4604028103c10341d41c0b44100300c1c140170a001d03000b5508048820440042d88105000c0c40c3d1000307036044805a4040f00e0410b00149441d001f0014146c880d01e0300800307042107070742c8885017403d00c100201c030303c124202c5840703070070903030060b20300380e210644034020724008611150040400c07035407844400e016034540c00c40c000720400 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 272805620 1250 272804370 272804381
    0x3020a0204181415010902160b0919060504031b02030a02100e030304080f0601090e100209060405060403060e1612020f03010603050d2c012f0601090f0f0905070513 72
    0x10888500c2d101c1c590402d44454880c0d281181880304c8070024000440e0840301c038825a0028101441041c10b43c49441d00c0307002a04070020300e9002c5034811840109220b043c1c001460100c1c41c4107000104503403e05180103803c17484080600d80c182446840c041002d642c000a0414132680c041d2203d2410490b059011640843e0314507a094040c0b00015000800d0400041c0108906000c0c0d010b5072501e90b2a131040405468600181161a0b0f119403500424aa10360f170041c00d107220000d01d200e1400c2d40d108042201600b003540151415540d8504200d100e200a01072000460101031940580c64108110560144000c0802901401c8a400090710540b403d502507009180c001c0c04940c030301d0040351740040130010040b12102d11a50b01074540d5400040f03550081c1e1204005031079803c0340c510001a41300b80398540c90f20b048007a42c02d864169101c02014407055020300455003001c10314100618000056501098080d0481c0d0320346851800410001316410b02510403c4507052a503000d00c14131100a00b2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 272806870 1250 272805620 272805623
    0xc01090b09040e06090f0f06060a0e0709030c03060b240d0c020c0d0c060f020718020c0c0a0b03070e03060105061b10060b03060a09050f010b0c0708100e010e030703020a020418 77
    0x4c20390082c060101800100b030b0701d4801740502182c0200d4007000070141c90300f105441160704400c3d41c1c035007840781d030f518900324542c49421807810407840c2e0f64984401c04260607a41c400c0c3c07041c507030310f00d801071983c10202c242006203115004041108148406004028800c0115007050f00307a41c1d8012452151007440364400500009115803054200c0c1c7c01c00d100d408900e441030b6000300305050300d00c0468030300106c0d807241100d0f2a1009400d01d00311209501000e540101c40314201c0d4080c407d84020340b5500c8030307141e0001e466600300701034a0f890000009850004481c0599101e81d1025004001a6036002c0c00c4075015000121500405d43c1d201c40312500e040190048800203508250780800d0180201000d9442000c04a407400b034001e80d201003c00844505440192040c54082c006201e01e14420000300070030601e80e0101e03000c15030344003c22401d00200100256034642c40d043d0403003510341d090213522010031b0fa001c045c6113451116500030350b5074800340d20001c4c041c589a4440c03071981d0850641c5550080d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 272808120 1250 272806870 272806873
    0x608030313080a051c0f23010510090e070905030c1e131409060609060402070f020d0c09110c07050102030901080f06130513020406092007210504030c080c01090b09040e 74
    0x61400710104c405013101c0c19006c11018a0640604a201c04000f4001d0b5922410b4100d8030301340c1d00f42020701550316261400311081c40011800050f0649000100740d20850322a55400d01039420282014105071020702103e220f442d000c40c00c85032000003aa00c009070001e0403910003010145510804010740854000900ca5802034000c0002c16880462200c0c8143d030300329100c820716919101000101d004105020303003288142004900141040c101107090701c0e000e0110108501c0c2d49450807816101461b84c0c690b131011020031164403000c01080580d02500c0240055404d05002000090841c10028400881605040301040b84c0d45c40c0c005c90480d07c040c0801c4148403d240100901d8850541d80d4070480c021450721400181500c81031040341105280c151440d050002c041480601c036402045095640102120611b02e0003c191401c80f150010951203c5450350301c0c60a00c82145440d0789e01c04190b035000cc040d075140aa900c00848419980c401c0030f400d44921610001c1f030300a00381c00940301c21a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 272809370 1250 272808120 272808157
    0xf0a0602070608130f210306030b0a02030402030c0a08010e0705040627090f030f1e0203040b1810210507020a140a020907030605031002070f0b060d051f0608030313080a05 75
    0x10b10032407070951b04501c0c4500550381c89031041c1d1340d022001c8403401d20014020306c19060100e10f8440568006580043c00203048075445800d4030000b0304c1c00b02c0d80d81c1c0300c87d01c240e40d03401801e00e0080c011700c01000145011101040780515111240642006020041c2030200881070340c1070441c621940000706054004580c1c002100d01440e020700290381c4000a40082611981c807a000c409030146040101c218030f5004d141002c1c80c0290002803504080b0b201400301680d0782004c189915003103401c0307450320081d9803400c81390300130810000c0c80403684000f200c203214103000c00c2102480d00050038100080c0d10410001001c00c0c258005820000d55001c025130010287c003e0228040c0e03d5005070065800440a444000503401003450807807080b464000c02074000d004002020842c5c00340201d5018030081c16200341c000c4282e9446040449505109a600b1841c02075610003010034030585007e802d20500452560800c401c010111110041c0300070140040051805c1304180b08000340ca82c03007103145010000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 272810620 1250 272809370 272809373
    0xb0f2b02040b0d051f150e0303121803070c060f1e0336060b03010b15030403180302090a0914010f0905060901051e15060f090f0a0602070608130f 64
    0x445070f004000003038525061201160800c0b0588800e02c0e9548101d403000e0710540d1030305568510071001640c5000c01e2001c03d40203250f41c5c0d00e0510003441c404e40d8060350010645080c48500800010078044040154014070440000606086000e0191480f506045018400d101000c44606290892012024075400188039406416410a07001c42f019040f542014880f004100510507c10042140003020300c0c020420100f0b4481e44a01542d82001d400801c0b19a0084e001c5a0031050340700d0010284000001000f040c168048440c001801d41d40400c404c655186400040a500740913014940550351001d0020810066140da1400f01c1c40c12002404001160f00e8910000c001844055609004540015403012418450b2500c2000d0303000070040340006401080030000784c005c000d203040344200c0404140540d124006400714a240b259000c0d0350714110018842044404550b150103818030f0390701030084a0b0049901000c0e502d0a00d0903015135901c0140c1003450048000001d0484105a040d260 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 272811870 1250 272810620 272810639
    0x30c04090b040201022a040917040305030703090e0c030f13060c020709060f150f0314040b041e020102030a030b0d0b010806091b0a03030c080d0f020309070b0f2b0204 73
    0x244110f0003602510081d00340168031319400150585950580c40e0010520b40661400d5800700e080540600c030b0322076405000307108450056100e904103640d16800840d2940405074481072041c050300141c2d943c0c00f11420481e1090400d40070160040715100d140800155906c02d0540f0030500c100c0d0040003d100d1030740201d03c0607484404501070344400030700f48100450094401540c650480d6012844100311521703000c03007220441c0121000c1820151181441c1d4858030111078207078001d501415546a1504051611514400140040001d00c008003000b420140c0e030044140d4520300294100821500c1d238a0000031482d00300702500400b40d8613000004581c03030800090b40b6120340c49240803140c07800040d400361003100e0001d2407810342c00604587c085c000648203c1c402203030a44503d00d198104118402035109407600b40351100746883d808010032808000802c6503400808054403514038110701000380c45454402c803042d1045116510000704040c2c006c0341c403507a00e00c1604041c02c54496841d4980d40 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 272813120 1250 272811870 272811893
    0x60603060513060e04110102030d0f050105040b0904050a2d11040506030708030415092c070e06090d050f060a0203090105061203220b040b0d0f051311030c0409 70
    0xa03405014a031203840481002da00c07a0f00305440d940656003015507100d0340e0f102c4601d9202d0700d42c00c1c11030006000395040048107000c0c2c9010b00d244480302080d1503041805010448101c10800782c45481c00c4800d0001003180400c80003422038110440315034942d507110180d0484030031620300468481804100d00e0034000040300700c09184508031410f010a840c0c140805556011034003c10f40c0c15082040208000080c103446c000c50507051f402c04607a416501c55141000c2c1f1130742c2c5003001903c2d0014544d21000709443c803541c2da00403040d0802d44140401000428400d00a40e050a401000b2000c10034042c0f04081100382c01c1010b40c0d00445009180207501ca0b0043d410a80c0c980d445503080c50080340706880c210b0038102074803a0001c000c50400028070540301110603201060310b08495035400200b95851a100144040c0c0485c02d8000c1d070328500c51546508603441d2810365005e1901e854248481007011107009900d190708460040c0004859100081c01c160207c01025806803034007404074200f05915410 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 272814370 1250 272813120 272813129
    0x10203210103020913020603011401170403230301151407050304032003060f07080a060f0b130909020a050904060b0d0b0601171005100c0203030a03060503120708030a0b1306060306 79
    0x107284d103070749071182c2c1e545014000c400020344c00309040c0014842403080014656010704149400c081c042c18a146429069900b03a40c15000160002d030b9150314200d02c211841c0042189810081ca50343c5003c0a50244210704140f01d420004039100b202c240502010540c0d00310b07a004419240d90759901e107412413043c2c0420b04480000f500e00002000380b80b4000c28207a1260401030b100010302e90751848122008880142440491680c1c1c0e10041007210060b00003038040e100e5084d015a030385030000d40c42c1e41c030201290b002040090a1809070401a25a004120111141a240000c0c90740b254504100900410103809411010700c002060074070805102c014050103083e2207540000446036070b041e02c0204120707040051600104810009802e04002e200704c81c0b42d1074642101c61443d1903002a0856000c1c5e8a47d01c00251210001d0080e49800d111100040185030781151910301c1650320381c4414000149038010055462403010301c5519110209841c42950890800120742c4805020700100f41c130340174 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 272815620 1250 272814370 272814379
    0x5030709050705040506160609031d041a090c12071206060314010b031009050405030304050106050a23130e100b010509030601033201090312050c090f01020321010302 73
    0x2440c405a00c240d9018248640d2030a292605003400d0000da40d020103003843c011142030804074041901da00c1116801880390742e40c80c011015402400301003622002400d84100c0c6409540b02844440300038542000b501079540c083c0a5907850f840b4400d6000e040380c2c1c030418591413410850115400f1042031042404000100102034907820110202d07005160017a914111410051103c191014080c5900442007007000410b07513169100b050941d0000c2d1002c8170694008414001000420302440c4050101560003814041c644407010010000d0101c1e0800c0c42d100f14002610140c07075048a1a400c404c1c01202408008414034030103568417011900603038000e1505d54203080c03a40c45841120755550006008110503400d45d240c5100d6840140c80900007c02c4003040420300c4a4440003808182e14840000035060b041c07414080d003940da501c2c141960303040c941000c0000d01410f2609682c0f0040c1c041e15040042d10645005031710f10711406c002c0c580100800f01c00c2402800c1600ca606040e42e20991307 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 272816870 1250 272815620 272815633
    0x80a02032b0e0f0303042402120a030203250c110312090f131509061d01090b0102070806011502071d010501210213030210080103210201110f040503 65
    0x20818140041c1040351000103600a95401c2000b48034000003200b8030001450004107800354000a0718640c011390050844640c0d0104a0081214580303008042c403034540090103905000d9420656148922040003080c1a404004203885004900f0f000000c400c4400c0e0b20a02c410784504003034069104a401280c1a0f00a490ba0020a04001c40c00003a40c00c02c000c1c42900f040c608008000100e103500c8615900010380700201c403d60440d85c02040c1000e0140740e110b541e9103091507030240640d4650340103010440d00400c500c056000d4086030442c112010740c50300003552401440100c1c100016540041894821407001003481120f440300d2000c00d8016800300d8403850f5898182102d203014051660301403c141200420540d406003002282070542c1800600c0f20300d030100301402c01c03604080780580d100c801c5c5207824411420700d42d130b42e00314004850902e22020361466403007a1105100b4a0315500403e0040881c8458034000d4100c005112040c0d500d81d138681120b03003480480d0350014070995201e8407451 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 272818120 1250 272816870 272816893
    0x5010909061a22020d052805040c0b0705030d05040c06020705090105060304170c0709090b07080f01031203180b0411060304080901050304020a090f0f05061008240a080a0203 76
    0x5031042d440d050060050801c00400d040031810154810080342c4495400300140780c5600b0461003044c1c07052a9603034840b0a840750903c07075000d20901841c0601d00d03083ca8041407002240841142508450801a19961310000c5141041c110b00a20a1038001e0034213000074002000103d03034035041075569980c201c84249950740100581d5280a1040c0c41d08510308001007804220340741c6081e1020610030300111300d0140c010300c1c0310b4506445944408031032651094001c0422611080310768002c0042d2400c101c481c1400c00011006103818400142103038480d050f82500c8074000d401440c0118054000342032400301d5420301070100c100896003100d2001e1040c88203045490301101396401542c04c0705040d403c005803c40196081c0d80044e00c182c1c0c0c0594a141d0010f4500c49601811100c000e8540010801c1910380101d2010345a01414045c45560700901800300c40d80e20508990b07000c001e00d01c070b2400c101d070300844010b5140c0030014495040b0480d14000704124200007203008a05109500321440000107 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 272819370 1250 272818120 272818151
    0x7080c160915060804060b010903050d03050a053303070909081b0d020a0f08040e0405030a030c02120a1b0206041508090c0d030e041409010605010e0402040503030a0c060f0501090906 80
    0x840c003c04000c500c020b8003180c003007245507000310f40d07030401810440002c82d101c1c0c580b5460b05807a07400010000ea110001c011111515001d00780c0c20024801c00302c13403841400222000c1c0c00d0802c0190906000c0303441c1296100d950100406402001c1c4002c040003d10380c0740c00d10110b5035100441075000485085000b1004d1240000c0f00c2003002c0d000d9028007064003c0740c0c0d4141c8039845000c81600d003c03078180004215040610040c81c0642d200e003004641e500b1003180042c3c00d40d40407900c48010354108000669250150300210781e6a06002d1808a1441030407203170b9050300f030107156030103500404c0125010950340725426462034004000d48400903182d9400c0100e541c0c1d0740d0300d65160350308103c610081c0c0c1c0000c1c2c0101c044500c01d00009001040742c0300220b4800b16610300844028100740e4440d01e0400141d60030010075130540206031401c2d481c0c542000003095070380c45294508030802c41003410785000d00160b0f0703100840910303103024248035a507900c400c0e90380a081d481005070303240c502d0214080e0340c0c0c100 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 272820620 1250 272819370 272819411
    0x30a0201090302150f19020f06040305030718090c0c170f040603091406152706061309090303050a110c120d021324090e060607080c1609 60
    0x14160365002400e8110f40c240004000302020303004d03400310f0030b220820412a0100103054400002d085005884641c810002d25008540d0040c80260b042041417001007035024003285da0100301424a02a001038051507140c0742d01a41e0710460000e4506400c842206a0010007402114096142c58402e1921464005490310900200b078500d0b00080000f0006140071b40c00a1841320300a080c11101c0d550101342103400d000e0101d40314003001d041d59440071020b00d0690104401203d03110110b10040795585104001c0140c040c00251140c40041011a0036015480c0d4190291400c04001d02418560341780c00345c0901419202e59101d90b0501c20120b201000d084140c40010440500030240c110400c1c40c08a07499121840158a0903020008540610002c003590f00041445c01c060b00356283d40c103d080685000b01110385010044901da0130001200c113040c545420003c00ca50715036076001c0c035140c07000961140d07101b2001e49001f02d8100e0581200c0400382941152440c4c0b1043c04400c6801158102445 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 272821870 1250 272820620 272820623
    0x21306030c0b0313020d020402121e010812030402091305032101170c0d03110a030207080606040501230a150c110f0d0305070602090d080a0f0c080732030c010b030a 72
    0x4004d0600320300580392a0b801165010b00281005203044114980c0003021041282c01340751143d2080b44050201d5180680340c0c0c0184101000390000340f0000700310305070790303c000380020748507804206c00b00d42c200d00040d40310b4900550250840340d4405521006a0380c00e2248114460840012000054440e6800c6020482c0702c2132803010b000518484000c0000b01d19800a00b41d08201e04c20200901082c010044000310f1402500201900c5107003d5140c0e107070000017041d01d80182c1c103100c0101301c816221a08221160700b43d1500b10b004006142c0860030603e203942c40031a08051400815003020b8000c0016401c1030f0180c0a81450852084203014209170180c0460750040d0001c0324103c0400d200c0d002405081c2e114500251503c110355000036200c10140000781c0b184400011444102d5400c0f121169040c84d1905294008e40345d180c590040500036007001038440300041a0710f07100c4040c4850b904840384aa00c0302c0c40d0b81c07442e001490310f80d281c0003190350488030b41c6045500002842e0008000c407085 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 272823120 1250 272821870 272821891
    0x18050901060804032f01060302130204030b060d08090d0b07120e03030105012003040603051807050102070302060306040b180610090f1707080a0b04020405070503060d0816021306030c0b03 82
    0x2d40b40c640e01211032081141c0146005e00050101441c04004145000551002c0710004140f043c1903004201404181103041020248104000c00004106803042c41e030020048621041d00c0301141041c40d214421245216484001c22000508000704505071a0190080742e442c80000021003480d00202c3c3e0003156009441c0d401030004100710340c8940c0703400e05408040781303a07401c4014482100070328640098110501103500d070307810041004440404000c0c0d00e11800003c00e10b1300e00d00300020351220301b0f44c080a03000d01e100100050250f162604900b44914003d0a0300140d0035480040c0040f44000f61942d43c4120550192440c000788502c00e1101520041150155a2841c090020070202102d1810012502660742d00140d410300074401e5011140c010044805289041e1040204490740200f03030320700303024081c42448010b860b4004400f12072030384080425556469042160781c48202110002d6000e0800800c406003200117070040d0003100c1c4140e80c84008251103620601480c04102c600a012 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 272824370 1250 272823120 272823137
    0x4060b0915040b030c030109060218010f080402010c0816050c01020c0a1a1e0c06090d0302070803132105070b0702150a0218060a1e020318090907080d1805090106 71
    0x601d001e0f40a00c81c1800024216a5000d4200c8003007420b44505176400d41e4200c1c0d010807440c080c0d0301c624003c001505003d2a01e4003800b2800040904420800b910182c10005000245410081006c00310359030302c9164085000c04c55000e241845e580d111309880c50303005010740c443d5020b130b604050780c81c6001d49a1b514500090140340e11003000b82e581000313204a03462004000309507004044040180740c2400c0c0240a404246800401a460582402412000c0503c10801580032031180d40a0342d0304078159005285e400200350070f1101e10a550009220344d110541200b861640303400c14020004280b05105600b96907984081c10f98440b000001007a001003a0080011000005a402009404040f029000c1c4000c660b0020541075040b4100c0792010800311035209070b0340d108042c107007403100429100441c0b8000014012041d5405e2501840c0d000d40c41c018080b4825910500207040034241c070204981c507030703c040d51004000d202c1c1c40c00b40c49001c8285e400049010b003013281c550f90503039a090321210f00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 272825620 1250 272824370 272824411
    0x2107061b0f0e0d02041a0603240904210c0830010b03040b040503040e070e04141b0f0409050c04030b010602120703050304061803091406031608091203010e04060b09 72
    0x11b0642c5001510300c60303101800210644c1c1d40d26000d107002d800c0040795200c1054403142d00704030854414802c94414840041003000241001e440c3c0a040509010442c000ca101a4404e40d40383d4422400100020b80115010b22201c0000401c3c1f103120b10f880002c952000c0101c4045580c0701001c1c0103039a000101000005d0224001450151704607202d14110381c9869903c111200d0030310000e803403040004000b41174180480c078150140d094000348545200517981448403d0200c120510742c4401e0300760401180710806a070061f0250340040124000c103101624040001600d0b070741c85400700f158023050f150b002003822840081c0310a009849107511903d07010301601c00743c840f50001030040700c4140e103898480c40b000f031860040040040c42078440c020682c0c00d090300c44968200f1002564080c2801380100001040f42c003101d00b0341d5041c3c0b8200840e961303c0b042c087d41e04040c40014414690300e0004000100b146040d8060381c825030050604003c56804501000042c1000b5243d00b0415010b410341d030340 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 272826870 1250 272825620 272825629
    0x40509060601200c21010207050703141903080c1b01050109060f0b0a0e040f0e06190902030319020f060103050307170708030f0a0b1305090c0a05032107061b0f0e0d02 73
    0x40300b445c4c0409148181001550082e00303981c80381c101203846800c1100704000b0803a6801c50482643c25507009041402e9007070f251111203608200c1d0207000c1000c041c0119420300200030880c1d0085240001a4683c07055440403940604428442d60b05010300d8220000b0300f6440d001c00c01010f94000ca90300600c2c0c003403002400c0300c08a4034140101c0c0d00035a160382000f251072551148034880200d000150807607281c203001080c8a00500c064070010780d4104040500140c0d008401c0300e1401441e40040044418a400c00301d28201c4050001e0403244a940004014010008003414800348035250110a2600300c68001116000c1d0000042800c801800410402d41d50b60b0f10b041d03480a00d02d240050300309880000521291082050b04400b59560f400f4810305000a000110f000c3e00182c8002003d94504400320340d84184030507030b0380c0008241c152811000c004000403030750003a4100405100704e00c61460100091580200ca05e0b010981030202038100328040c141c0d84044020041400030721801e15028031 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 272828120 1250 272826870 272826889
    0x50603070818151915120206030a0f0c0503040b010f060f050a020a0605010f030c1203050906030702010603020a0609060f080702100b0105160f02120609100b0f040509060601200c 78
    0x440c207502540c00f202c4000040c10007964840e2944031495681c6a24801c10b0f02c013110101200c41c4410a141c680510034184124003034100aa816510f00d42e5035503c012104008103030b00304030380c200f480c01e1604c1c220760650702030301850040e80502e41e0360115980c2c802640c0c00729091440303007a01084103082c841d01541e00480290030001c070140182c1e0180c50043c0d907440200c8a00340c020300f41c1d0761042e44d002c0c41030044200c100f0b80a40520003542040c1d11442d00c1c040d08078000c002c07806100703e8001001802c214801e4010800440d405442008002c1d100c0304040e001851901a01c0b0004d006070103a0f000161082041d103018544580180c016410302000d29005000c20740c4000b41840b4082240d83d0030021044007928449000703000c0c1c00703107012640c41080384030345107280010b45a03413200c001e100440c1008582c1080c40902a800025070030aa6400310f0007185030040804c1c0d0052070a03003001005103000c0f404a220380026038a80c0030300008910a045021110a0a5507040d8044c0644000505180e00ca0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 272829370 1250 272828120 272828161
    0x2030c1c0b0705130b09030a060b030f0f06060f040b010e01030c020102090a0f0f060206011d040303180b061005040f170102040b070c030b06060c1009140a05010e070506030708 77
    0x40c04061616501c5400c441001561070000080340003980d044600c0c154103142003c0c1c6118281a880c203100500025619403c50802500c00c0ea03995000c0c950940c0e08000c06d0700c2080104c802e98400c903001040280d100c0900301c4486014600b00300146900f80340c144511200300314143c540c0e403042070071500110014080507091500307540d800c1003101220b66403111140b00602d012064184c034141001d00c0d6040ba005564003c0c03043d0f512040062010709201f111005418507604620130413943c0360b050440160a42136103000e82004464002001d00100314035440c814034041e140341c16040c020b41e00803a9144201d02c50341f08110040f4000b80010010310829418035001c0c180090306241c3c803007612514a6200700c204a40ba4115180208204198469a903a2001e01201d038070782040c1c03130790030810b40b150a11090001401d60700d10007002084000400480305046180807240203144500c0c00360300900b1024075803440c41c40385120008107031500004481c1b00d0540e03992011000e451301c81c040941c1c909a00e01 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 272830620 1250 272829370 272829409
    0x30f1a090a240b1c0e0d050a14030c09032a04022a0a060b040b0d08070201091a0406090e1003030c050705030303190506030106062f03070524010302030c 67
    0xc02e1084840030b001039000c1c0032043d098650720399040e445040100a48507103203000c0c40c01c021911070544400b19031034095141c0790402603507405030004200e0b2400e0030901c81d003110202c040140503a80c4410006440d40000a0f0211060400b1001c0b0030103581005003011000c040d0402c0758418141810340291900e8000307901211640420401c201031611105094404140c1c851040d07841484110300541100c00002c0c4c1c2c0402c45a100b50340450300300103504a010300f51074000500107086910a07082c01c0c0080c148640c80c1454002c244225a441da8001d00c10b260006071030702008940c03100c0030b0f07490303500415219541500d8185195026540841700001c140ca680c02281da00003803030385040c80114415983c0c0807029012103c030b28143c0c000c58802800c00744c0243c0c5858170901c11a5040701d0080619400514180b03684030208003614070800c51001001042e01010460030304101c3c000598071041060120a076464140090070b40044d2002448040d500d94800340c040005d030b04100300400000d08800d074 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 272831870 1250 272830620 272830661
    0xf0d120b06220e06090402090915180d08060d022e020d08090309010906030b0d021320030c1603050f0c0604050c0d0c090b03031603030f1a090a 63
    0x40c001806600885a003001d8542c200c00c60070790100e5100140300140c4001c09000300581851000b01e0301040d03005000a0103070352294042024018104242d030041c81c2040d540c02c14501d44400341c558001c03007044521500340315481d09036250307074081c40e051485840040c26150b080740040d000c2158140010007102c00000040b0344820040500154001d40e10f4250340040440d0041048010b00e642d0004100e400a03130010b209254040c1c3c0d0182003807040b03591030320f808141e2060a00024001c040c070319600a600c07805c1000712444d910120341048130400d044c09120b100d004100d80c00285640300032034243d100f20400b0022800f184054000382030b4103074040d14045051810000c60110964809014008650311a108000401c50100036500034008140c80000800c40c0c036035610140f460450260307003040c4d5107800c0402e01e81d460801c1a203210105100450500b220740c1d040180081618900613009103003401508004401d00c050460302a02002c0c103c40420355440703108800030a105a1614541c80210 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 272833120 1250 272831870 272831891
    0x1f020a0c05060a0e0d08040201050a1101060518041a0403051228150504020a09140d0c0608090607020114040308040c030203030c10051005090f0c040306020307050901030c020f0d12 79
    0x411a16108041680b400602031164401c4e1501d8000d0a20910040158030410400142d903c8030a90302c00300654100b4003031801400e1282d41c01740c01d141d0000c641102d400a8010080318001403078500450003100c110340100f4414104403883c0f00f0858001d000300710100182001080d0b480703400b9510503901c0c6013035203d440000f646402920600780d480e1041a40f40c0c1d9202080030302d522550001000201c40441c0750503241f010140c01841c02e441800841100410280015152200e14141030341c1d01640b0040c4503a100c0e00b0190000c1804e58038555203215102c000399066005104462003c4186c50051219039110390701114882402801140c0c50311032142c1c0040107860800c040d1264a030058090300c08400c00c400701d00210ba00041c00000d907001010700400c499210342c00701ca078010841d06454415907460981014003449a5400149400d02c00001c1140301c0e40d001002c0d052204090f6000e2140b250400022680d41204c1c0c0071050040e003154100e01a824040c1c00c1c800916a0004c401041c2140c15 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 272834370 1250 272833120 272833123
    0xc03110601090603050606010216140f0405040302031207020a170a03020d060e0603190c0603021e0c070f050402030f0604240f050a0e0412180e190e1f020a0c05 70
    0x80e84003404a42c2c0310072081c130800ca41070241e954446828070060510b812400020030b14465948100810b20451615183d16070310b90f25130010085101034000c1c0014206860001e54036404425003e0543c1d04003404110003030b20129500014541060101210b4800400750801c01d80c0810214000d041d400c102031843c58509018200c02490941c05e2124945030050500d0706103007074490190186c8240309004c1000a0300759005000303590f0301d1300d401600c4004055a04048814082c1c04024801000c15000a040400240303801680c4402d144098515611428841030b404162400f58481e01c4510000d580d904180d404510382cdd0342d81d0f807141242103c0340c00c003103140241e0a03003004d240301010510a0141341031800300c00300109980800c81e0030714075083e1540440c2001c44070b202000c1000340205211444420070446d03014104c01940c6991600700030024641345001403000e1540d4070304010740c90300c2c001c3e03000c5050821100c100401d294441c80e400b0707480c0300a600c441c400c40103210b44482c540011030740 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 272835620 1250 272834370 272834383
    0x70615150c05010509030c0a0602030a0b0d0b060f060a020c040b010e0607061b0e0d08070213020d020702180106021b060f0307180519050108060d080c0a021f020c010c0311 75
    0x11291075881ea00c00361824194203443d00101455500c1e8403c0200d0100c04c000010042e0000d60130580c0140c40351240043c2001a02c1848500390740400072002c200240400700c000c580c000c030021542c240701290304c001803010500640743c9400260b005aa0740d0095414960000b42481005160282284103038400152054100c80802e5030b4055a5400103002e441d0801070042e68202d060070481c88071285a40010038145130300d5402010300c0c402241103411510381c10700c0281c0e2050a18010f41d250100031314600001d40042006900c04d0b06078500c9400300d211010820360503941c40d540070b010074061400402d47e01100d00c40c101074100000b0480b19480705085405140150402c5e59082141c800da144040d04800480d003000d4401d201501104511545200818048510a081c403181c5581d4500015296020711000500003030800115103100d22800300c0e04030900c41c421110480c061541c21010041e0084509000e0056400708800c081c4542c018100740b06960b02c81d2800010350003c42100030f05058 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 272836870 1250 272835620 272835659
    0x314030901020d050c040b1e0702030709050412031509020a050d050906091c050306010e03030903160f080a0209010314070801060b030123030a0210120203040b040506010614070615 79
    0xb54003003000300c20200b450007141e40105041c0605030800c1c1c1007801c1da545c10710031084da01e14010513901040319641c80c000e0540d100c850f0002d05940809a4030050321020300340072601101c0015504044803000d50080c8514800030409080c400c15107824030701c141d07000b5031202c058502803107404e11036401d400c52203025440c4950070400c0030340010b0400021407071808003044882c102d00c1000c0755488017003d60040c00d5a0f4414001d281109401000340082419441031682c03460301805200f44110307580c820581030108541014500d554425920104143c40f03c9180000941c015110001080803070075003c004540480315000340c83c44290b45520460855070503a0140588000100041226600b42c0000382002070b10b8101d00706402151400081c0c407002c50340070080c4510066082c1512441c421164907a03140e00456007190784c3c1c1070504200c040c0c0501141d003203455100c0c841c004240c280c4594003003145206500b45490038008142d44103c040d010740010704050480c0c0c0400001c200604106003d200f1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 272838120 1250 272836870 272836873
    0x603020d1104050702240612010c0e12030901090302151303030f030b06070b18010e0d0207140102010e0a0f051f09110915040e070e1906060c020d020d03140309 70
    0x100100d400e01c0255a4002e1041055401880448007039000180f806000c000041b8981c18881c0c1d2000001001c003503100c50101c100b58640424000243d42140c0340c0403515404640f070403d0440e008203c280d403072284c108180e002034050002040141899002c1b50131500000c54014104080d00d002c00018151541c0150002400d250340c00740481d416125809401000342c404c9894030b909505ea003a10440c000d8241b055020308021242c640b0300c0f003940141d0340c0707141e1103069421540311650000c0d0b03200a28000c80b54882c0e403900c48000e9940c0144641e900003034190014084c568010344030030811610b4840c1c01e40d85401801c0e02101d4601c100822800d290b01d505000003480d101604100100c54031052265000da1054018805004c5451500c009003241c200c03400718149064080f132905101965011001c0200c41c1d034140918070b48035104088200215480410209590311011114028104070294000c0c1d200400d100150a100d40040081402800e040d640c500c2c0d004030302207140c1e0044503c41c545 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 272839370 1250 272838120 272838143
    0x503120a0203010f0b0309010e1605011101020a08070c080405030a0308151212090301150f052812030302091e0307060e0f011b051c12020a091401030603020d 69
    0x804444600190304a10185011419581007000000750045280200b100f405804000900004425007009401d4030f032000948205a14000000d161441c842c010103000c1120040b80d203c600205100703403001c4c500700b42e40311140c3c0e0f20f40b0b00f02a51154504030342a1340e42d92040201241c5034401b0040355414a100b0342e40ca81803490300000030910640e0758000280708111203501c0c1c4070070441c0090300c0f08540404002c10303070341c400c590700001e030045ca40b965000220360580e081c00501e40840803011011281c081d902880f403072003201401d01084040100c0080803116204080c05052096a04441c0040c40b030f003001485c10b06034400140d0f0840610789000e4041c2039001841906080600c03a04c0d0040c081030508000e02103070130000401c110018034142c4e0401005000c0104a015036100f1409400c0e00102074500d059200c060103652841c030f484d1172001181c160742c00500301c80481d200315080c010702035076810200c5041002550400e0070558440d4105903d918012000d40c0d04c500c00c1403030040c45001840d0b50b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 272840620 1250 272839370 272839387
    0x3040b0a1e03020a0c03080601110109060e01050603030301060804080901050739081002030408071a040302010c0e0303030a0903020c031204030c09050606070f0302100c05070516080a26070503 84
    0x10740e5815940d5510400d401400b00710b40c4580c025054010300799141c00c14821598400004880341d03407511a402c03c0c658200410542884903603030040c0340d40c403c0d500c000d1140e940c03404103140d503a2000303100e14800112400002030100c1d11080103001c80803014501240f40112a03202c1d00c41c2210306401070100500700c480b00d81d0541c416100781042c0046c507030740400a0035151461047e103c00010040c05611500000003504002e84a02100d03e0541d00148108001803c00d1800c0d8000800f00c130200c0c0550329102100248600071030360310b144000020001e6246a8030004aa000760819160031819072041c0742e0f40d071005540c103010320a800c0841c0000c9540712451410014182105684407175281c0b407500b002c1c01704c140c5424040303801154100400b100e485002d4502280380c15013440d80305011510f883c8003c0095980100103094090140c0200c0302184039001045410380058800c96240e50300130150740001410380c25541c00d84115010b1540000b0351041603003042a07200c001e003180d89400c0040c0484 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 272841726 1106 272840620 272840657
    0x203090d0e19210204090309060e0604210201121802040510050d140705090c0c0c18180f06010f03031b02011b08090a0e09150f06090903040b0a 63
    0x2c000251428024007092340e0b40200d100045034801068003d2501c6826030f000e4402080320461000c1002480d5038001400074822414400300d54014884032082e40700d5109162111400c01070112031500c104002c650008081d6040742a5407041030203a80c8480350004a000e0381b010800c0600100c0080c0c3c2858990140e101c20b5001c00f500c0c0800c03160543e488046d02030851501c084408000c0e1200c20090715000c204a209208006500010984454620104803c2502400f542c5480c0c44210b070f401c0c1843c2007600b103185c10412981e010820154003100c2d00715030500d52a5507081c0c00c10f90341e000130805003d090300100f105c20917030120024007040008807111044010940d84031155501e0000246541c119561002030060f101050120a084a0583c0c80343c80395422180d002e81c2c90000b0003400c01c2c0c0c0a0000641484148004140e2290190007000e241480d41c44180c1028120b00600 = true := by decide +kernel

theorem cover : BRFrame.Cov 272661870 272841726 := by
  have h0 := BRFrame.cov_init 272661870
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272661870 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 272661870 ≤ n) (h2 : n < 272841726) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
