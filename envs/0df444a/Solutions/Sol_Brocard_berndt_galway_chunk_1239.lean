-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1239
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:55:48.11496+00:00
-- url     : https://prove2.me/submissions/136ccaa6-8e3a-44bf-a036-db3d9faac7c9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 222661870 ≤ n < 222841726 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 222663120 1250 222661870 222661883
    0x152a0106060c02090406022a0115081903021507030605010f1e1803020604091b11120f090301020730050426030d0902100801030510050604150303020601080105010e060d 74
    0x607035031403828001a0258802281488c29282c0b90044540d4110845200c111324182c000c101c001030100d0401d040004510a00580350800c0e03042525100030f10301d101001c10f0180c01164807080141c440200280c4003140d0150001c0d545860070300ca1036a014642c7e20395003407d4030f0003410920002d04907400740b00e0003144000600409074001e26414030f5035443c900c001d50b002400b403a1226070f120892000b8080300450720a08142c0e50206003400c42c003903128140d2001c0000c000b400200740c0001c801c4040e07800502404550b08092107010110b0303609000800203148100c0c103601301d1502e1049003198480064400e170f016000000380c24011507921800343c070100d44940e460145900310030206003100120308480c081c0c05000001d503034030b920f810603040380c000d281c0300b558551030860491a00710399020003804020030a4014140ca4101076009400c56508060004c2c0700140213007a010301d90b1901c40540e4401c03005a00301c03100420041000f0300c2402e00401c1a0340d0300c0c0d0203500c1c0020004180c04030310320700240301 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 222664370 1250 222663120 222663139
    0x5040c0216290708180f12010f0e0a0305030408070201090306110a020f0c031f02040503070b180301050c0a050c070503030a0207080f010504050a02090c090411180409030e0d02152a0106060c02 84
    0x320307a80c5034401ba401c1003000c6c02c0048401c070750860960181a044581902032800c01e0310501c42e840b40044e0b2500c085401d692441c0c215140c96480350159801204140e0400810180100108030355100740324914945814240da00d40880c6000303414003c1c1c0403c420b116030003158050945440210306800210807608101d20b03410007165501d0002d00031500595003601c510f81f0082812441d210003091a0000c40d8480071500703114100b018261002110a552041014081c8582241c00f0394040c05940023a0010ba804c083d4039200400c2c51500102c0480c4016882034500300800b002c1403100010a0344920001d000038074258071017540d16002d02c030000380941c0550002a96a0985105490108030001c3c01032041090f10301007120507403c448590b45101702f026001c1602d520307282c4035203411240d142c0c8980038003c020100b0009080c4603c041660803495100c050580c80300300000802f1506940345e01c0784c487c00081c0d0301050301016a1103807540e5980c5480001e1000d150000000c841095044a24012 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 222665620 1250 222664370 222664417
    0x1605060703200a0218070c0204020306040f11030612010e0c0919150e071701050405100b07060c031d120f07150b0f150405040c0216290708 61
    0x1d00508492924002c401c0718814405009030219446000500844528142020200204125000c01d130383caa804600880c0c00c1400500b0305402850303104200038400036a40843ca4140e90a54003100c0356058154000020080e403860030300740b8005142c810f0002000b4203032010315060b554140106070b042c845d2500d40700007010100340d000741428184440c0c4061000c641406d00d40700d0058894016034000e1400d207800540828400c2c1114503a1062003122101070340d1078181400002c10740900700c1140a901c002c00803c56042c050300070041301d4401d000000380490091001070807291a001401c000c0740d40c40040c18111800080c8060f252011030464a9661320354040d00092441000c000519400030181402c05120003a03002070b801880988419185441060810501c01190088118130b9042400284031905040d8841c02c0c501125004460301d03800c002e50400c524440316440860040b24017041e158481304584100308030b4180e00280c80341001210740e80c1c14801d0092071113440c1e11540c821007503c2c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 222666870 1250 222665620 222665627
    0x90609040e0124090501150c021003020d02160c05010305090d0e0130050f010f09180c080d0e0d0206160c0e0a0608070503070503030a080a0608060a0603030e01021605060703 76
    0x24056142e00d410380c020003c0d030304500903100d8200d102e9211080c3c90900001f40640440402c0003072241d013581e559011919a90800410940c2540760b181095424040f4140c0019144000e102c1c6107080d070b40d500490440c80c5400b01d61000c0315000306040600b08010320980c50030000780504610032030b05118070940e00440041b182c182000b0301410096034a02a4552050120f25540c0c07904445641c05114540e00d110418640d0751082c030036288441030b40e800c100666500c6a100201c65140c80011180349511500c0740003151051780c00908880e001844200101500580040d005c1202503510040001040e000600720307000d44011041d22250341c41e00d0300100f200882d5007034060082180074840604004040000920039802455500d20907420301180d58503000603100b04403100200103500d04240c82104540101029214000c015140d110200300c0803014040b8500ca50700846002805503d1400c005048640d000c0616065401c1071060b5843c511015040e8401d89a06544007a911015031600301c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 222668120 1250 222666870 222666881
    0x216080a12180c0f141c0605010b18010f020601060f030b030d030c0f0801030807020f22020306031605090103060b0a03140c0f3016080a030e060a0f080403030209060c010917090609040e01 82
    0x14a07c5150030004110064400b0207008010007a941f515412618140191940350300542c01d0b4001d40c1c40301d401008110302c00c4100c41203040052030086182c180e8440031a25010604000c5404252100000d0105c5980300302c440540d41450f180c506c0d403d5141d074070b88160070300c40e02401038043e046c25a8003c80c56115800c800e0b0800f8507011030543d60040042e03681009400980303c1c50b109016500c60b81d194140001030082c01c1c0c80c1d000b8807003049039280d0f45d00c41000b02035440e084c0382c200030429800004507254421100c1c1007880702000e0038a000ca4982008032140c0340d0078040b03101b940d40c5c840c84444000d8030001091810800026140080300f40096985000c102100e030700600c070140000810b6524000c00c0d203808061280d03c540b05510100070800241d406040f10100000c0e0425588004861003003201c1a00030340207050051602e1801c1c00403401341c2c0c4c040c40d1440020303134440c01403004000902c80703c0d0990b210f5000716281400e28107000502d031071090402e40c0c0e101c1c5407100000b1b0140c80c405c1d40304 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 222669370 1250 222668120 222668123
    0x7020409083601110c0607051f0606020106051c030f03060b0f090901060203070b04030c0305120703020c0f0708030406030f02040b0a0914040216080a12180c0f141c 72
    0x200c0050b00c42502032820401100e80c0e14801c0c0c54602c0721810a0b5000d480403101e056210f0f0301a10000c10381e0b401b844103e420154054a191180c83d800015400c459101390300c1d1400707456401f040707641c2490710207420f407003c5131711003401a071917800d03d915501801c07040303449501e906203841c5041501c0c1340341c00c4000e840607030003e6400600000b203101d90f2080a6000380104e1009460030f08a503a0384207002e90302e9008505002d031030301540500143c00640b18002c0345600030306c00e040c42420040d606140c05143c010032103928010039400180400d032000c082104201d80d480c1300004140d11810030b40c007141c5074090b521400701410703141c1c2c01c070300304403801030701502c0140c2240001a52110b1002c0b1005048503250301c11807e0000e507940300140d040c00c0c94022a5607900c8981e00180400c8440d0790f9080a940c0025521400c1021061114194010500030602d001408403031000c0540910304051495009503884881101c007442000c0000c6403800703a51034201041100c2d032084054202c840400c650b07950000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 222670620 1250 222669370 222669397
    0xc081b0c1201020403021912240213030b0603070f142b0b34030b0d061a1210050907080a0c090b10021005060321030103170a050702040908 61
    0x101d0321581e01e0158082d0044034000ca40d42c0401c40340700c4e010780d10516924056030300c0401201e520200410440c60b443c2a107198088182c005100500610780100c6c0c01c80311038400c1d041071004041051041d844c0d40b15800c000210b001d0b0282a1170800d00c414080a544140094180050b04540440c0c6da05403003941003150002c02181045210b0603044882a4000f01c1190041d00400110b26821200c500c04074100031200c80c03406da000d00711682841e0069103201c00000b003644400009102c1e48460040d405c44510130400071803400301d0032996200b01000744909034000c103420001204043d00005040b8090350880900180c0c540f20201840d080040c81e400111151048401045c100400090006c00701da1185204000490840c81001801051100342000603402030495210300692070744a41d4002100900325200ca01c0c952949404401118002c000c010101200400c140321b1103401e5580360494540b895850000c0110b00680035020f10311010340a250361310340d040c00701b00840301200c016400003031 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 222671870 1250 222670620 222670639
    0x7030506090303070f021f020f04050d0c030210030e03090f1903030f0912080a0f0e030d0c020405150a0b1615090201021b03070e13060606110105070c081b0c 69
    0x10041507807580152030240c0001d02203e00170000c14030204c2c00e202d081c001c1d00c0581168110031003002d406034114104a86d41d14100700720000d520750b2418020080b42d441190080c616a01c1c3d03004010003447c505ea8100149400c20b40f203052901c0b0080200e41c044001140c0416201d800c07030303010404074001c4040c8034496003142c0c0c0780070003815005400c410310984103a036100d8145450b90100b15911040c2c0388000c10700c060034412050130502803403808140c03481030f24110003901c2c0c112000074540485002c1c0440031030030030103160003036003801e002d00342d804104500170180c0c101e100b03408030301103400e18800c1c0e00e010040401c000388241c1c1021020b159054010003400341030180e40e10307000020014602e00b06c1c050b104040c0c280a01d50800da0046c1220240100a41480ca2406a40785400d50740201070400c62402c8441e00700004600d841000050300b401e5442ca4030f11024a1825400c4440151514083c0000c0411500004043d501211140326070030b0080003107016201760f002e10b00b04418411550010015 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 222673120 1250 222671870 222671881
    0x10909110d0c090e010803070f03030c0e060406030b0405011706010b070f1b0e0a14060f1f030c11120409110d0908190306050f0402160b040b04020f040b03060a050907030506 76
    0x4200c03102134607800d07548141181d980b040300d1982c134400c40d80001c1c07080c400c4c90031400200703029a01080f450740d45410714125a4101c5000500143d02903004076000c03964136005009141842e01c00c840c05415000e1901c21b61141003400e8a54407107051180d686d00e6140001c00808004405211001181e4441c1803a446500c0441a11451101501440265580010014a1180c8240913465645440c40c0c101c1c003860b210b04080c020b24072401e44005400a0920220b107520030000c1010004050b500c0d40c0006156400e614024164410720980e44155802840c03503ca030074401008640448900c4500080e620880844440c19400ba90048003022450480041d007070105040086c018020840203a00e00c46d20600000d42c2299020700582d600a501c81c5659400e03410325600400320001304056003404010a81d40d0300101803002c507801c0320101200014482181420039041076180320171034050040032441008680d80f1880200300301911910fa00214901e8002807005501840e0040241c4e001490711 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 222674370 1250 222673120 222673127
    0xd05070b1201150203030411040c2715050406050f070609021008071806200a05030325080c070f02041107050109120807050a080a0612050c031209010909110d0c 70
    0x348203c4032190b0100000d1050b052020080f41c4c80385520000c1c0f0445c14402809010040070081c960301c1c00e2105100300c000c1a50310000603900564030f001c52485400c4e040004000704501c0c600700c4001840030600c400d0041f940c100c82901c1e0180140c0f0601500c4401320308003000601240d03140690002d01d00b070303208190158007448030381c0709400302d85450ba560316040c0791100042e51207209403030000325400b10203014070004020400710311851604403030403441103460711030840c0e0066038043c0184a96541d101c1c00140d4442d070040c810100ba040100f098549100c441039070f0f01c0751600060030302d908a8025130855a9980c840c0030900c01000340d4507222040c0f451700c140200078041003514822440c220402e41203118070951441443c090350384a0910410007025610143c02805103030315151104404100086904d000800b036901960052107021950010300d0705282021500e50070050081000710710301e036000000402107071185400042e02c0c078918905039419004846090104500b01120318070030030f50 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 222675620 1250 222674370 222674407
    0x9030c040c021b011407020103020c01090605090a110102160509040213020a0302041404020c0d05031e0712051005030613050c031b0a0f030203150403030b090103050f0f030c0c0d05070b 81
    0x300c100344080f21907103d00054860b8034001d41040c10001080082c040154425006000c240c905100082040706482d502c00e825100308807000c226651000c0f00c60700a2140740c0044501c1403500380003405581001c0120348540f0b10150103004d00446402010800315103400814000d404000b00c0e0454455004000090196200303104500b400c542d450041071580c91300e40b0840d1914200d0500030708081e1506503064613645c00041071802d2035001e0b02520b00360040411a210310401141e80e800d81032490308410b0404a410144c4150609520624184020b0301c000075119040354007502824000342c2c052400d1441c01c21101342090b003601800071400041d0090940408918104a030220a1261505100c1d1800c100071302c0003951603030106da81c4401504e0780c8000250464080d00d40070600c0400341002c164000400c1e441100d507580101c002803107400e010303c000ea4a0369401400b55181c0302061004555880c1a113003054417800035010681704221040006000400040e0142a05d1b0340000741984452704 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 222676870 1250 222675620 222675643
    0x40308010f210308130501140403170702120c0f01021606230a05040807050d080403020106090c080c0a051303050f120703050d05060a050d082d03040809030c040c02 72
    0x2110444040382080e0a4840c4080c40010104600e80440030b6807011100303e00c001d8802d04050000c81261408514203004800ca82114040c2070301e0941864500282009210010140c41d010400305010100b98042091108001c2c8840896103e10f1000c007403d0400207000c4403451a9840007074006c41140c049124031601038090482040454019050304114403124004c10070185d581c1400030382e110481d0360280d5000303405030301e519082070741642c2d5131031502c03020380660800b1401c100200410190f0900441000d0b00401e10103014001b82a84040c24115001e0280307000b00b000400c00403c00c900c41d4054600b820100c5032080091543da0030710b0b030340b506001014580c6138016100c074801865000021203603943c3d403541e6145e1030100c2640e0420f0051401a1219500042c441000525540e89401c5c01c00d00c2c50103201c01a9441e040080007145406007a4040303c01008000114804042408156507001d03812a2400b0ba541260500003030404039600c08a9910600d000507a8100560004d029150314 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 222678120 1250 222676870 222676889
    0x30b0406060903140109050d0305090c0907081008030414010e040e0105040b07090b0306090a0f0e100e0105060a050d1b080307080319050408180301090611092b030305060d0b04030801 80
    0x80c4400151a080e1382406d400504181d120f5003200c20075510a40c00540d02c50315560030b4503c810340034400100c0240082d030307030140010703600d0b814015103a06c10260309006001c00c00003986001cac40d02d0007034417050f1901c549403410b10915261011040c0ca1301d411440e00301700124000c12403331034545040750501006032211000101d48540101d1010307518030889000d040000c1c504103d65aa5011301d01c09000101402d02d05540c0702c481c4c09070300c04010001001600054403002c6408102140780d5400c540004052600c0b401040c6000c004c552a290410800c65800030f6050141070160400d5640a02d410340c0070216501c00000e0180c20700c0b0080c1d0140d4021010802c07004091070b02d1503100001d454040e2070103000100200030034041c8101207111458585405000803408000369100c1404481c980945c000109000207415401e0380b801c015a0b0701c4109110301c0f480c8015000d030b521207804c0300000c1d4000b030034140e036030f80400d03030660360641590100d0386d104ea402c1c411440e2500d8018040c0c4020312a41504 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 222679370 1250 222678120 222678143
    0x106020a030807020105010501080105090a0213090c320c03040f091e05060a05010f200309040c0c030507020d061d010f05010b2b0b0d03020307020316081507030b0406060903 76
    0xf900d00c107024250490304141d480014690a0204000490401608800c01250300304812800408070829050042180500001c2e4550aa2001034001884045003ca4400501300180c1007101d0a8505000c580107014442d40ca811040501a1443c8241d42001d583c00c444900e000555020302d80014000e0310392041ca51010b0b01d9952401c0050300d0081c0c4600d6404800c66400b480154441c00b40c1e1154203400c1c0c60140001c45515000d000703000e0702301405010f43c0e007000074054142e0a11f4003175902c1400203454000d0b4107602e170751070040c41c6004014000340f04121880140c1e00b03000d165041642d20340070945030a60320000d0510102c2c02031024003c1d92090b141410300015031300f0071920507200342c80407904003111607000d05030204588007804540c02d6a1196560100c81250b2541e80d40b040e000780c4650001e580d0b422140c0105880d10f046800001c503040d141c07020901c100c034030204049808501013020400c0c1e81d114014198003900088a0340d5410070f14001c0b001448607400a0703401c003201e01400001c40b0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 222680620 1250 222679370 222679381
    0xb03040821061c1b170616091206090c09020702030d03050606120406240303030b030309010e0f041e020d0e0a0b01050d050a0213021902010c080c07080903060106020a0308 75
    0x2a400441d00198001d01c2184402c0e03d500088280740091445500f00070b10841e0b421842c4001c401c840d4100d10440f040c9114140d039140710805c00b4540200c90301e80d0342c460310b00034450010500041070144107103903110561031400300000c0e5004030046580c00090290039948403101d060003908540d009030704c24400e004c11880094040d11900380664800390625203003480e065410310940102034801c840d8159140d0b0b44444440550003440b00e0741103003614031078000e031940c10001c06450180301e22901c29042000341c22a640e820903228480c0840660381d04e81083c0010002a004001000c041c10200d02d40c0f030816028020315a000b01201d01425900308034a25030b0301000e55903200b030808001c00c00301d420303401400035141010240000324407400c1201d1003581c150380480c0000600e0b0307890505c040d4000c80c01001502c01d07028420b000c00c0342403008100c0005c1841d4010b1060402900e581c20003080064500207000844c0c2c21100b201c5009021220f079075a41d40300c001d6503140110070039400104003502140 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 222681870 1250 222680620 222680677
    0xe0109030302071a12070e0109090c020d030e0f0a050709060f12020d02060706020c06010f06050304170a0302090a0f08060f13060b01110a031809110f03100b030408 72
    0x1565003542c010034080b42445900c002c20000f014884400203002d010307544510501d0141144181309565410b80c0c50504c40001500843d0541c0181c0b040030b04109400481e198001054a0032440728640804c5550154492509103c0403000c3d012042c0100042082445400100c5a040b140c0140701001300319a18091498814a50301421180c84518240c420251400b90780c4031a500b4001460280750480540d40c120403640441074102c41608140010400c9400840b0880c2c0142514200355186203000d59039484140f4022880b105000b80129010394030500c02e41c1950101c1d400034bc005441e0648480000200034460f20814099100307000002d44102d6486403014015400b50b000199444401d036202c40c041d01d60890728030304001d88117200101c0c1c0d203001c0000d1712009000740c84491450580a03501801ea49160304402001801c10344d03440c0d1030030300c440202c0300d8020000b20782507101d8441c0d80c0004140701c4e0301e5022055420001c0107000074411154000c008450700042d80071030700a801076180 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 222683120 1250 222681870 222681887
    0x30c0c020d110901170a080c0c0306040c0302032b121b0206190605100509190909030909051302010e0a0f031407140a0302010305060114030702010e010f0e1f0e1c0e01 73
    0x3071040e1b40106410900240000000d00120886442034503002100700000c04e08d008402c0318141d9140e41c074620100b06504044c4402028081c0c1c141140c0801086030007140f202110103695081000500c1005007100b259950001506903611800c0012401a00305e0082d0345040580314255103003401098071801c0c41407449035034129a00604030002e9021b8400381600c0580082c1c003401d81003c601e8003c0c40040e21009200c3d0050076018100060322038640c24000e042803907a410041c803051803d001d0041301908642c60030314499091810800c005481c03c00b08010010a51061a60107031680c804410490301c0144000840e44080031103946580c0d44491120251b914130002d030f0003615101050000d0352094100503803045040c10071440c0b4902000084656502c11200000180d65801d0700150790002030140e80044d5801000512281c448059400c1d2501c00c0b84c4c41600046082101c0000904101d400480c11000307103100b030303540300d9400254000742d004071809040001016481480c40b0b540c0901c000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 222684370 1250 222683120 222683159
    0x10515030604080d020405040203131208010e0a0b010512040b040b091f05090f150912090a06050c100614180417030604020702030115050f0d12030c0c020d110901 71
    0x400e219102c80d240c2003060340c421040314050742d40800020900740c07654002140108910100c460720351450b400c0201003d4400014007041060f0400108120140c13070300165000030805100084124a03203005031801d2094003020761400305520100018003900c4d0740001e20440c0150081c0d10642d0340d8180a507152500481c480001000b8580d110300242c09581c81158440940c2003103881c6440c0e40013455207840d03602201032407803010183c1041a81101440b1800d884101190801e0500c1c501100049690b02d03940100820042c0c0454045510720f000c1289146001c0c20f04070402613a40c42e20303d001d0184c9102ca00890142c04400444d00001c00d03508c51003446542c010310601d0b100103450b681d428080c1e10152446038030540a01403000565428810124035040c04001107681901d0b090921417010200480203216640e88401c02000c03c0f0000005900c4006500d0700040001c8050410b40d0f94410b0118069000300c001d610000070403801d155500c02c06241150340c046240e995850700c41082003030100707 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 222685620 1250 222684370 222684373
    0x3090307150902061216050408070e0406060e04050703060b09070516031404060e040507050a0c03030b010c06090822080a1103070b220b07080a120b13020a0201051503 73
    0x29001203907685401c00240e01554402040c4080c481c0c001030402c2d0000320800041c20503000603c48120040c11b10000b4040e400d00b0142d040c035180101d21526240d0905c40c0206240641c4006010098a0b0703000c00080c105000c24400981480d0030311589e00d219030300040310b8140c500880500b00d46000c2148a00ca6003c45e40e6542c81c0c80c100340c03c10580341c50804800c40c01d00a800b50b2501c0c1d8108108080c20150030540d4491101040400402042d110701818080c144401005207240ca603a0250f201b500131505402c5c00304100d40403c0049807186241240078000b10302c0d04502d1805c101a41c001802914400390b0121034880b04442a215202d4851195000f44e42c0284400300001d0041c03000f181e000340d00201901c003150b0b640c900c03080ca5980215032042e6604440c007800c045034003a0541060190524032212424a8400d5071821890f100b000f00810034014200c10001082011307401c00940c500e03010344411000d44071150004042d4010544000240d400c01d0700003010200030110045c1001d80040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 222686870 1250 222685620 222685627
    0xc0901050d020102101a01030501210b0c070c1502060f151201020d06060207080d0f050421060606021b030606030705090601050408010c090914070905040c030b0a0b1e030903 76
    0x3040081e030755804801203040d8010320791008040d282902c11919181d551409100c8020100000141101c0058228918504041c10244a41d403104004400d180c2d621480314402610354203015901d03400fa40c1d030018408030312510003050300008107081147c4c00310700d9000c232009038840e0902911503080c125040f00502407980442d590618084e054907a00c500d804000600c1c0440d03c45101d4140e403001d820035070242e4007912080204104c00c0111081c40001c42c40e00e6501081078001c000c04920640c0b013546050385208900c2c0c1e4400400040d80207036141c2c410070400406559140c007a499007400007201c01c803401c14400300d5105040220b0440d00c41c002c001d0103082c445040c4010420031500140c09281041403d21020646038001d108101141e043e07525456001858248032505451082c0c085840c0941e20300140100160011580b10598904131004111b81104031022802800c0b500100d99100401400000e080b0132510000e140280c407110b440440c100741074051034660b103c00d480c080195030080 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 222688120 1250 222686870 222686879
    0x316030515040f02120106110d0815031b01030f02041208030703020408070801092f0f041104060908121911010f020706140f0907031502090a0305031201080c0901 71
    0x2035211a50107125030a001e49555403110110342160910143e80007074035400185107030105403006003140140990b2070800030151020755815100c0008441000500070100007003004054141c5c45e5010010003e000c0780c4051080510750a031aa0900d98128003003840c001d28144c0e00c00c03441c0212001e54580c0c22034810310b040f440d81d07000c03801e5000504603410190b007400003155007c011b1011b01c0c0100745000003ca0100001d0425402803102d07a403103510f010b458005849140390301c096000000380c030212074940f44296060007190240010340c60364001074600240100b40a600000c5040c250340d450011604600e4900340540d080c3d22454034600400c001034036180c00107030b116101d40c03190361603408000306828440c4c81041d4281d030890982201c1035500c036422610700d07002101009503c01120404052542040700c84980c64001c60302005c2e1a0108000204002076400d80403140c1110024040300c2d10700e6541d05000d600c9070000c90020441103034031000004e05c030074005440320300781800920004059190 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 222689370 1250 222688120 222688127
    0xc0a0803060a0902040605040e070503010509190e031b061021030302044110050a020c0d03050c1c0503060f0301230a0b030a1205070c0807090606030509030316 70
    0xd050a0703104080c6032001ca009646130014100400454846503120303030500c800e18404580052515041240c144010403a0341c0d503d140c5039401c05141d40c1001c00713598441c502c030070141c42015405c140601c00003808250503081c0f8010720b04010200f800380c510940f45c201c02410b0720034180c815040341e120f03131040031822446441410910f445c880e04006180a2750b5440c240b014407125441910352548001e504420808400d412004008040040c0d88080000500095035003210903035201c104440801c01035055030080121a400d448000e0410115121520340200380368000400000c15000300103070301d00002003030300d43d1041b601d0440d00d52034116550b0500307106442d100518074075815074981010400c150f854100210352b10044070f500d00d01c1494000e1703640064401d05000701340698000c0c030441d00414055030303041415840f0b034941b1550b41c0307010341440181301c0003980003851240214040001c1007411940318108458240c0c409001665903030110a071a400121200d440001d4130b0320f24580352611 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 222690620 1250 222689370 222689377
    0x602010c0206091e031c0f0f0c1d061e0304020f010c030c0b072006060312040302060301030602070c031712011409180708010908040302030f0607050d0e100e010b040b060c0a08 77
    0x10b24104990518166801c541020503403009410303d41c594030b0b0b444841e042c00d580584034055001c03141c00d009c0050804d0008000791545a115008220400c0030006e1a0b034a0008072941380d814035540e02c1e6071890030b0381c4102132640305542c00c92240d40306940840895014104203001c26815861f030700300104580e240e8207a80f0100402d210204824419a410903409091a039a40444030300001c208a141c00e006051030403400d03204581c3d00300320034801040182c0c0e958007180d042d6644003c0168492105250103c0d01c1e603150740008180809403c8008440100b00c0050816854040d402d18001c0e680c89240d00c2e2902d2114040e260032550400c0081c006c03c005424005203a001e6104403460070740c0d206000b070308481221000b20ba0001d40010100107501d410084a03200d00c0d84a006880c240c107180303802820034803070340d0080c581281d01c81c11005101c0509000000601310043c009220700400101c0c064001c01c0000c151324401c40c5090400b860034103108007a50b010b22300c090300400d1b4030703003413030b15403041540 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 222691870 1250 222690620 222690673
    0x305030f0c03250b060427020d020607030203130f0311040914070803040503071502060711120301090f0c0f080a0213030f0c06090b09030a20190602010c020609 70
    0x1004105444060440c03800000005440d841900b83c042e94500c1d049001d41005880f0502c203c0c00c0070325522401110009101c00100f10202d0552007011170301c0481c180101d142c80c042e40c0a580420036200349500030005000c0400382a40450100e80c480301904c1c0c20b820107000191004d040c02420711024107050780104030031801903520550000310710070120f00d4060290045a2142c101080400c0380e81010885080503207070360900310000740c0019000958a90008200300c08100a1124002130413506101604104c900804815560740c2c44020b2a07000e08440008a00860716040f81d00300c2c2d40c0d102d0a1001c240e0040c1d6034507041b96031030f981c02070303000f03034200303e20311801c0c0264200d000001a42c0d442e181d441d410710881801049a01c1c104000c1c040c00000e5004c200d40d80000c200c4510940ea0200343c002a140e8810103011a1548161100c401b200907460701c4c940122060480f401460710320601c0300300b25030051f8004c1c00b440d40b200c042261a030f60140c85c0c4076516801144c1c030348119a0a0440c2080720b5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 222693120 1250 222691870 222691873
    0x30f1806050d020d09021002010e0c18072007140a090e07030b100e0a050f1b03060607061103070915180e15030a0f0302010c0c030f030506150d0209090a060305030f0c 73
    0x1d174103400054100b00d00c580c400000d40e41d40e54000401c198184101c424044084942c11552000d41c401180c0c3c445c0001c281404100114071090301107000403240d00034100100c01200d10035038803802c040503030840309200b181c8505000e28002030100400c0c041c010440d10f005d40074000442c034596440b0041071001d450943c0d4000e0034500440c05079601c410440c882c1c14002030200d107030b06081c1a803d1044034050516500b030340c0035100c0b50030401720220071641c204600307030303402540d034241403d10400038202103590200040700007091040540d8042a050103850040c041160113940760382056034072808400c00c20f0000407008004010842c07036480c006034040000c15000c2d405410f0000028109201c03680102c540f0b280040440b0185942441a00a90f07a42e500784100485001d490141451000039908402c060701c44000940613102e00d024030441c10341c050760882d2034107007400012020390041e60390113001304900c000045030758155001c0c203002c03241c0140c0914608882c20007604c0f210f921911184c40103 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 222694370 1250 222693120 222693131
    0x150d03030b040c0804020f031903050a020a060501080d120203060d030c05010902060a08090f0304030305090405070207170a20010507021314151c050601150903060603030f1806050d020d 81
    0x303911140a054040c445540e1511031318a02881082002145504424000e6000c03000034950348255000c442c00c44d64060408036224180d0810492403c07480c40c000a01982c10709000152128000440c0c5d008545c0d59103c0c4010300c00007000003001c078007084910300d0340180101c081c140820f018040a200307840c098800442d1407161030700856125802400d407800094802d40c02c00105017418045201c1810582004c0c40c9060302e1a10010158001d01c84070502c40c56032900828a15402041128014000ca140120544014003c040c1d00c80b218420151880641002c04940d02103088002c0e452202e0141c60380350078801c554003402a43c000c0300da666a041c0f0b0340c0d505000308044800a01d24810062000c2c007034104080c042c01d0000703850042280d40c4940c004001501c0c0082c0c8081403a5054072800180034405076141e00d0221034001c966800600258600100401450707031100204494844688506001060720104d00145c0e20070382c41903400040003030000c4168000c1640042200035000c4001080 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 222695620 1250 222694370 222694391
    0xc0f0c0804030c270506090c09030a0204330305070306200325030519020c070320010206060a0b0d0f0e1e07060c1505041b0f06080c03150d0303 63
    0xb20380e0154010300f01404c10700352841c4000d03082c60024110b801000c0f100b40300d5400e000000c25150704000d480481c500002083d0318019440c10003c1e6500075400510034006078010029144c0350000825510b40b40c00c05a01c440c0c62441704d0b080482d0200c9a010006120f00e41c81c644940d8000c0400c1012030040d050031560118248110402550081d0005094080c0d42504050106134440c07000c0505002d0509047c1000681580c007803005032080707a00000582d864a06814690400d841030304020091000a0402642406840d003070220100080c0c00701c0300c054a6040c00c00030221064840ca00c0090802c202d03000f0700c1945c607000391060190090303020450130748484495090000c101c5641d5510810004a0359040c0b03410055400181814117210810140300d031150f9110b07203103c5010101c21902d95022904010400b40452100401884900203030384c1c60f0250421401c4c0740b071040c3c030005102940412959001d18080f00d005068102103c015042514240005070f070144906405141d9102d48006 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 222696870 1250 222695620 222695633
    0x90504020a080610180e090d0816030b0f060f04090f060302130f060b04081005010e061e0d0803011212020c06030f040201090302030f0717030a0e0910081506090702010c0f0c080403 79
    0x51b092444000701c035072034402802442d00c48160b10031020007408105100301132884040928200e40310349004604500740da13000c0b500b058800390791650040b80000e0320005200f040c2c1c01801c141c2d0401417041c403008681f0303003101043d2501030001943c4100d41c140000c0790038100d03510075000300ca01c605002c03a049980781e5840d40540c0159020746071a802c010001c0361031040c03a1160034050400c0d10910221824020041a0340c21440076800384100e07280d000c2e03034009640382e0042c1c0422a078045004c1c3d075a5a107035200c21400c0c200c0650100c1e04100301c280701107072107030011074140600000540044e09607074602241c0d940c00f82001c1c0c401d905100c003840002c000758400340440505118444014500c0303d01c0e00c1c550071126120386552001e07a8005001170f2140541c01180c180002908071801c1d942921078416500030b491035a806150301781310700c00071124a840004001807080400300e41e0b0110a6580c1c03a8180e003a6980921070400090001c40b01d020b03043c0c000c0009070480fa020300390700d03403e083d22980c404 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 222698120 1250 222696870 222696917
    0x21005031021020306070206041502070302030906070615290306120105070203031f0b03010b0c120c100c0503040b0c0c0f06010e04110d0515150d12090504020a080610 73
    0x541c0d070302c0c05601c2c9500070344c107081007080e402c244240300403e0325140c44e44411614010803c80c07508910703000140081858400c005580031100300826040d43c81d0340900c0c02d0300042807100007008622010042c0098912440354000300b804040300803c02561205441021450f0300c0144110b900110070070407018280da0900c50244250780540007540d40c1d0505280b5011843e59030300d070304640754280040a011043e00300045c0c0f81182c0e4000b211546a071a4146058200402c0ea2440c0c4661031001c2282400072100107080300351028140401c2080c2e648080c01202c01c1e110480b005010b500e00300c0c1c04100c004a61000414480907001c0076221131400c8002c4150802c28280d1000c01c2141c040d800303210034082180d2b854900010102c03504607600c50281e894035210b0001c410030000c1c041d84140001c0c14181a05e4011250700c000612492548926141804484252041001c00150812004645424240700f142c50094403629001c400780da600b81040b24845100c0346120030400d0b1420741c03542c07c0c1c4028000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 222699370 1250 222698120 222698159
    0xc01020a090314010b030c040f140a0c120b01021f1104080609060106030207021f0207030614070e030c13090f0f050715030507140c07030507090905010b030a0210050310 74
    0x80d04507261031420300e01a0803240311004040381e45091201201c40c2e1340010140c44038081583c0216071142c5140c8030740c0040002200c9211140301c01d00410990741c1d910751100070749442c03580b00d8142c2c111001c211030003110201503d6a01580c4020724080c02c6200c500046c84220304140300104e042c64110385040d0150704036501402c001e511a6051000340b02d01840103a0240c02c05140850800d1b0141d0001002045240011001025540c99071200c2c1482030100401442c0c00c07040600008003c051007121034002142d1000014049903038202c00c901d40401c94229500009141c1a00740303162000150040102250843d102016803c040c40011500000384c4900390003080034107045864094031411711450000c0d00c904052400c0f04100b20190441c0742110701041c0b000f00f40b51200c0140215502d0030b8210780000c4e1441c03056000c00216030240750480a4418410002072107144690300c18565a8201154000e503c4000041010a80f612440c0075551280722114000e40b01c550307880d501c401220301c0941 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 222700620 1250 222699370 222699377
    0xc1e11100c1106090102070209010b0f0c0a030c020906030f060106140c100509060708060a03030f050d090b22050303130f0b010303021e03160222060f06090608011401140c01020a 78
    0x5400009490601001d03130300c92070200c0250714188580d40004c0c00700d681401000c4030710707030702158145034905444207859010054100315400c4511608019145d0302d40740717000b244503404140004200d42400308107901004901c10082890340d003004c0c0292107450268402483d820070501c42d55100d96400c105902c00d00030311b8a00000c85040500c603c504000740144000b0900c03400b18182b180c01c1c0c41d5000c41e00b04403501458004c1056220a00840b4184150241d08a089007040250ba00740a2110091801081030308200c4400510307407111008016000300c1302401c1c80d001030000176201c000a40064004a10440c400c0781c0404250303582d00282d04080c1c005500581c8103200c45400b0041e02040c002d0f00c4500c2600541c104410a0380c1d840c6002c00c8a04002d00841e000c2d003035003408100c2855560072410700c100c0140f0010780ca03040d44040e01c00b1140b01d2100083c040380d90005509000d03a41d0b0034180c0b03c0f1034103c0040280c2480c01950b240d5010b0b03d9400b000041040b00c055007540030310103041c5000f596034 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 222701870 1250 222700620 222700637
    0x212040f060f020303090307030807090321093c081002030601020c0a14040b0103020d020a081b1e07020607081c060e01060f1b0204050c07060c1e11100c 67
    0x704002d18010402aa620966004005001c4040700000c1503c4010380c1c180341403100340da200b8a003103480003401d51004000b04a0529403203510403009e0b0905400489a58403011555559000c409108440c224549181c02c49280134411804ea401d424843c000b80c4138102c0c917083c0b40d0b0b803001180f500811103d03544016601005101e950340c3e05110001141904940d00010241001506000b1000301c0328011311499442550b440a40d0080d019900b15140709041192500d082190142c00c01d5811114004004910380c2080741070b6101e1019100c0c0010900b0444024000600e0044056400210203980c0481c05000300710010b03200000804544071032841600798002c0807120501680c40c0d640220306002044001071040c40d52010000f80f0a6800d0b140c508140c000c030b65a49206082c0844029401c90705100801200e4010000100801c83c407d01c400c0100300586241100d200303860021500710030341c1030b40f00389444c54842c80b04114000e0400c010ba400404022083c141114550f0741c041000c100b100c13 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 222703120 1250 222701870 222701879
    0x6170a0e0d0807030c0905091807080d05070303050f0c12190f090212210906040504050106020703140a0b0612150f100602010506130e030f0d06032001020d0e010212040f 74
    0x180510a45c2c0d014034105101c440f42442c0028000510003454188034181150340d91002040801c0801c000380441001e0340d00c1c01207200802000f030303800400c06401007403d290124030241c86481c0d00b140310300007162075181883e00e03842000f0000700d80035040fa052184526100c1900c60385034440d5403000c00c250303440011800b0742841400200300c09a60b044000c1e4019a0902c2640980d01e000181c00c2c0840c2c0f9107066480d8400c40000d0154002e540085030450301d000000300c1c01d03a070000303000800d9901818100c80f0400310a90007540c0e903122214010800260200443c0050400c00f07041c0000300340d00f800392100c450f904031080d118440110340380e540b00340c4030034180a2401c0044003008042c008a1009100e0b918110001c244200d43c04003003801d5a56030740031300c000301c0c950500c00e4a00314010700c81210764482e84d40c0028400b41803d400265482007035850842c003420303018029031407451410780280045c00c03040502030724581301d1459081c6c198010520090100840c4000800c050062803000e4980c0d82e040 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 222704370 1250 222703120 222703127
    0x1c031e050a02180609280b070809010318030e0f012105040b10050915030703151a06090906150903010c022a0306130c0509010311040b0a06170a0e0d0807 67
    0x801d20030f40c0c0212000c000d0b2254070788441d581144140062080c1c810200c107444c0121031002007540c00001903080100c0e94508004041e001010b8031002641e080c00720584d501c10306411010750400c0200414640c404660703440c00e280100d40210581410302d1500740e01c603e048060010743c8a000c148006503507000700400c02c0003001d003081d0030940013143c1002c1241018007181e00008040c00100401c0e1040e00c02c50040d503402c20200c0701648d402040d191803003000503080d03c0a805004030503001d505401907516114100b05040d5446401c0050a010043d22004244015410303001641079030110104a20f01c0d680e1030034090350f801e50120b40c0c0240981414540d8003000c400303070600820311091068134005081d07034000490340c1d00207840804400b6140d0715032410103080c11840d80001d8004c21228000410300c101c04585c601c0c0c2100070f45040c40b030305001008114009070386004640208448520301c3c00c3c00e41c110014a81d210392000c8000804160200f9458904004e6104550015460340d0804c0581c990 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 222705620 1250 222704370 222704407
    0x213020702150c03040b03180a05061b0a0e04020c0a0503040b1b0c010203070b090f12030708090c130c0c0f111206070804060506031903030204171c031e050a02 70
    0x3614001d64240192100680d4680c4150720038406c6040000c000f00d081c0c420b800c0e003500e880e003e0000c11a0444503c918006803100421159482003240103040c0c50442c21241c411200d400950340c5c0c07916180001101000000c0d002020508107502c1010350300307400520b04000410240c85c020402603140c02d1a10800c032800e0100904036070f443d410054504a5a90300001a40c140300d600400d400b40c181c0c2c4287d40305241c4805a038941c601486a28100407807224884010341c0502816a0ba07030340f0558810071800d5443c3c07140300100d80c0105054a0018542c110383d800310000660301d1600245110300c13a11102c160f007950000585400e08141c9804c41d06140c01060344440e22149000f03800586494480507010410060000e4603e5450303034000b4240760350601c0b10054002400100c6d0070801080e040080094125010381c0501c4120652000000040090455203490f400e60302500100d403a520124054051880900410080d00600b41000c44280c007a4030300c1100c88020043e200d56183c07802426010 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 222706870 1250 222705620 222705649
    0x13060309080708030c071b150e012a0c0f050a080a050d0804020a0b18040501050d0f1401020c100e1203040f0b060a05040c0207081b1806030a0213020702 67
    0x103240050000000d0441d6040d1100c032504003108036100e6464480103e410700c14284024800803102d41c41c0007415460f4144c074800d40ea81c06403081d55140c048601540c1c20b0300c40d040103d000c07a68103040704003484c410000550506011216503106100c0c00d584070900f512150f0002a01c10342046420321090805200d9180105060001001b924203240c6940342c4600404a40d030040000c004002015501d5004143c40140b08002829599406001c0c0720b01e64000c0c0e40f00090f20403030070711000062514000060b1346070142c00050301ca103550303241d503155240006c400c001c0120b00e5400b444000900a0b00f0712040c40055000c810100b5528211a01d9034104161481d4150051234140700f03000214200d2640036405c10390052280403107898610001d00702d09220390100364054240149040f005501264810440d1200d200b01c2d400310740210071011304040d00d01280f80e0848070201030410345800318007925030480b4000c0c059501004807600402c0c40c0744503800d060503c0b25000138a01c811800d04540b24203151 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 222708120 1250 222706870 222706877
    0x18050c1801030b070e0f120a02012d0302070219151e05030a0e0a0501060f081e0d0c1a071713030e010f0e1e0a06030c0f0c050a0203060a021306 63
    0x540c1156201c0140f004082d114001300f00c00c6514541d165107801c0c4400414103001440f8003880b1640c0f03c1216550184101c08900048050b071161030030b00320500c1200c003003002c4070400440c0100c03000b80c03c4009411400c1e0030f9a0020800301c440825201d1740f110f000144c203080c4000c0d0030041445002500035060f002c009007004c0c1c0078860b00100c090340102965080441e06001040c000c1c81d000c0180e117402c942c418041c003154a001d400140510029008004540c00c40f420703a80f0b407007419030303c0d180c40c0c44000b454220250400c01c260141244104408030683c2d100e481e090212003e03042035500e65040440d01440424000601c0c503e1092500e80407a42c80251028900901c648658008040303960000300c4038188000b8062100b0454002d010b41c24020f4000b502c81c1401d8100142500b803c400d00c82c400c18020300d00317442d010031514442d0042035602040e50b150101800f030f0400c2f08503098200030405640500544100e8001070b80c0901a090088104503c090380f162441d182680ca010800d51004060 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 222709370 1250 222708120 222708169
    0x10081603020913050307060608030904061703071103031b101a030c0907110604080d05010501080c0712090b0310050405060303070209160201020f07050321040b0402040b0418050c 78
    0x16a21240714543c0b080064000340f8a901041c03404500c0d5024102d00208018182000030410b801c0000290500982c11902031107002d175a090211740b041000070398001290802c009035008224003120b50f8043da02c01a013200d00e02030801810540e0b0641c00d9886040e40d411000400c0002d501c1406107086456141102d0004a049500082c2d500c0c41030004079401501c42c0743c0010545400742064082c0c41e1303156025505a03203030605d000304161b4051110740400c6850315001080c29417007818204e00ca4810205030500d882015211294040e0150760803d081114225020400c880400040d6000c0c0d510f141c0c2d82d00c080c600b04001c120684e50001d0140740070b58414826500581d8071560000d801000200f1020310700a11581704a001e4402c100380c8141800002a80e42d080190000c018180c01110009a1100d141c3d140c0c28a14954419034000c0c00b4001c0342c0c3d01203405454968003200618000800c000341c22000d1481044800c62140d13001c0e14a07030040d500044072420086800d40700c540983e01c02846 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 222710620 1250 222709370 222709373
    0xb0915160f11010b180a0c08011a090d060c120608210c0f06040b1f0308070201030f0f0e010c0e060f0a0c0f02131a010e01020318040b040510081603 65
    0x8030080d200100304482c1c06581c1c0305111003944511100c107405040e95000001003a040e009400381900c12164603031500c130180d0710240c4102c10080c140c4580301201c03526000820040d1a190304440e0745564820920700c200000100c0300e01c03c050303002c031943d165082c010002d010554101c0760258040704054014000c4481050300d000b01240c5003040002240c4c0e00c64811081c05442c014140010107194441e44c4140010b00280184540c81070b41d12031400b199003a00e00c08101841c410610009002c101d0034041c800040d0f000f50021401c10300400000144d803a0404010411754070200c0c490714003a50344d080c2910302103034000c00805d060f00c42501c00528002c01001c3ea040b180c03180c20045001c00145401ca401040180209440080d800402c041c0d58004c6640880005210440d038021105c41d640c0e900000e130f9401501560b8404405030051814118204148504078880091459101d41c3c2e50000c11840c0d03441c0d10031603014102d6914400c0380e00f800c04003418034000300080e103e980482007003000c00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 222711870 1250 222710620 222710627
    0x10b0d0b0105190f030503090319080702060a020c04050106111204050604030b09070315020d5a05010302010f09080a290a051006030603150203060a030b091516 70
    0x1070440c0c400f5580603d821110000c10800315441d9003007a4070180d40d5020000510074000701a112182c8214240c4240d12000803011020741c85032600100a94400d000d9100503203002005000c030000300340191f41c07182e0a6040081c04840c002d030440004210348d50901d500d600380c1081241251002880c26500e42030a03c0c00107085030066200c01081e5509650010f26244401e1025000555001c0c0c070075003814207001c032910040c1d04420800c14400d490305440342030341100d21aa8a2102e15146040e6500300300303e0440b03803216070042d807100c1070980407420300011003241803035100403020000300001040e504620004000444119035a800c000003104240200d441c04504501c0d1541c0c4030400400380c90b4076180054070016044000455031600008020000700d26400076489156103107210030709170380c55441c00c2e07003100c0d40ca00014142d0f515030300c0019035841c0c507980210303005403004011784507569696a84481c2c008044a881d2420b0300701154405d0241c00b02e040494210507595090080b402c08403000030b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 222713120 1250 222711870 222711893
    0xa15020601080f0c03030d090809060f0d050703050f04121b140f06011a0304030c14010b03100e0703060b030c030610230d060b010e060a03021e041a030406020c01020d0e010b0d 77
    0x11450559507423018020000c210040ba8407102014100d282c5858090300000e400d40c0200d41d1901d5600d043c0b400040d1600e2203031144501c6402103800c1d00002c0c2d16941c4540e5218014552150207224101e843c00c000a90410313002a2114859003402070b10202150080f030404112046032491075100a0040c05030280c044aa9100164100754040c0c5a0342d86090860381c152181601030300450310f819800030f56880c190001a0701c2c038010350489030707512003150200c02100c2c1075900b00700d125046400140b0014005409c0b84000343c00080454400340c04020000741400ca0a07159490f084002902c00c100201d03981140c62600c0c14000c091400a6018030003051680010582c000c10300c0b541c40c003040c00e0300d07030091245079281c08010b0003144d1201801e4501074002d42c00503107942a11803080c1206044490742004a03415240300c038030400095010800c0340700e441c3d0409041103d100f0b07002c1c4020101d0001c00d03c0501005100f02e20042188a4021900c0e0b086a0860327640700c0c05084030310a48404a5440e1104 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 222714370 1250 222713120 222713137
    0x9030c10051005010815040908090405360f150601020610031a06040905070b0307020c0d02030d03020c1c020a0201110d02060708101706060a1203080105010e0a15020601080f0c0303 79
    0x40c045585000040181b0411601860791281c81e0124007400c1c082c1000107000703010000d68040143d40c480b00e030444440c829038940307160300100c0e05102d002c041500d050914070390a0b001e0103ca04050548010504100074210540c0358404d41c00204440e07036904011a41d005428110410415420760301c42c645101505212456800120b50120748292541da00440c9240d0704034003900ca815032a0041d2007420350050b21100f006114502e20055075240000c200008160700800600c0303115a401000d170081d4215603030b05152402000022000140181c1849603000d8041c1c3c094644c50407144005403001220480d60f000907031006035607400480e000a0415048130050400600d56900d4582c1e8803204003c54104542c0c41d0f030300e0703c100790b40c403140040c820740104400c803103008505440319820032050b003c0c11405000940074000400c142d5004103c041c50b00180a07001c58000e54a80c200d03090500e9a400c40718005074050001002035403001c0c05106d0300c420494004d030510985142c0002d58a015603510b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 222715620 1250 222714370 222714377
    0x180f06010f0c120309050705030c0d14030403021905040c031802040911040606030f0b0f0123070206070305070b09071406090a030501060b030403090807060828020309030c1005100501 80
    0xe2200c80740c1e010b00c8610307089662007a00401c2e9283c9a440c010081c010710101154248941080800c06180c00300c2d03052900c4401078441400100a5214002442105210101e45010801c004000750b121000300030080c4030004034072126145013005100c00c645900d00f0000402d071910401001c1218680c0783c07185000d804550101d040300840c1400d40142a0b1010b200340d1080c60500c001a410340c06270055113503500d809074108500d104200a009544203002030180c0000e00d000e040003050000b41406180c42010b041c1d601d4180f50107036010a003190302610701034021640229032001085102e14038164407040702c03005080c44510b4881301313050900030b040540b840f8000c0424141125114884103100654010b002402040d51710303080000706500c159400c1d0001540542c0c049881c00700000c18804076142d41e03035070003203a0385d13010001c8a15403801010142c01740c4803031007004032100080c000745000340442c40203141d9491641428a241c000c4491941390754500704010400b2a031055080d001c1216800c0c203 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 222716870 1250 222715620 222715637
    0xe010e1c05070b1b0105060916080c091c0228151205010909260307030903110d0206061c050d080618010e0f090102090a0501180e010311180f0601 64
    0x64560304003030643e0821168101c020800d407007401d0880c1d240121039401000200125250041488504101120341c0c0c1d40710345420f41102c56040c841d11a1951000c07200d5840341c1049040000907482204103d440415010100701c0e0f40150725020040f014142e1081c83d10f42c101440c4410300c0c2043c0e00a42c801c8155501242c0c41040360103004000d01d25440c44401001c11096844200d40d6009101c0d691056411070b028201d807070042e00114510b100108032010700c0d10f046954012041300540f620240403404c102c03003000d04552411080108040741c0c0181d40140c40c09141483c01d10a2089500a010400400e2078115001081e00442e95074181e408a05d80742e09143c0d590000302d641000c02452500b004240e0100004280340b1031500e55001f1888012009800d44402d044c032400c1c1c0c080d0140702c030b40c00144000304018560042d42071a40c070081040318a4160756665031170190814003640b01341d44003082c80c0d4118800c1c0c50040701c0c1d0704000e040f541888403c0d04141c2189216460010b044a06000c4100b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 222718120 1250 222716870 222716873
    0x1b030c0207060e010c0c0806011409090a020d0809130e060c0708030f0a0b030303010801020702030d05040503192d0203010c0504080706050313060204060f11060603100504110a150e010e1c 82
    0x1011400c5c002c64000010403100d0381e1780c00403155100d400740b00e00151540b0120603000107107003000003103014241c04002810004565000c00090911010003120229420003550002c0e8494000c200c840c00380c070340380008040c2d2881d5000c0e402c010005082e5030f03a25604004450000340440705880d004000c003080d000c07a9640d50f04a0074028481b0550465151201100001d98554150020b01c000e910070b03803d90741c607890080016070396030003540205035254000d40702180450b0001d80111141c039010711a0b442480151818541d1801c501c07100c000c400e2002c0405400660801340202d890700c03610b600d030403480c1c2868801c2d0107032034a86600910080040020103d5052400c10700f410030101d802a00c11135503950746107001b62010010817858004a1400d031404500c4c80404280180700d9100a00034100010782030a10800030000100f040340e841820001610707264441f00011b0018149840c01e64150140003d00900f03111091a01c8034100583d103456245140c40e004c80c0c0200f81c40c0012020702155149 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 222719370 1250 222718120 222718127
    0xf090f0204050303131d060f0405090c060a0e0901080a080910030204150305040312050103080f130806010f0518131707060c031b030e03071b08101b030c0207060e01 72
    0x260b5229550611002c210140c030188500d4a420071120342880503003080c0304a11030164100c40c11140550700190b0418008810b051036040550311840d00c0d0f050710031019444d0001003960700801035441c0041d0764580c01841e58140303502e009004d03003200300c02050a034495a4900f84248626000680109128030700b441001d40250181e0b00a0a8090741c41c0c40129a0000004d000b0802200c083d80050082030078604126070301d104060503260494040b51a0800d414000c200a40c08081032030400f1a0f60f40300010b400e81c0c107001e01e5000c0c0040c800c2c01c1c2c0f1098900801c000c03141c554200c40343c0018246000b40000407012001d800741190740131081442171002e90918a210b40140e20019103120300b800000d1000320342c107034081d00e05202d94401e803503600c4d20034034012001c4400011740190143d008001c1400070404141c0451880094000d10841d500d4842c1c0c03000e82407020009104159548501d04002158010400181002c00c82e00e0100460026400003e682e20700901c41c54042c03102616850b4800d910 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 222720620 1250 222719370 222719377
    0xc0602161101090905090604171342181d0702060717060d020105040801020309010b100c0b0a0902040612050307030e01030e19050115180e0d0503040b1e151002070f090f02 75
    0x8400c0410190940c0c520b859800009120f25405820007040d40b1200703240c41c50b2007041c0030003084810b400d9203076840035004e5034cc00c84000f6004810010b000390000f1000c00750722554a000300f81040e402094240030002070300d4002c001e040c007402d0000c3c0703413070f03200111001c0030f40d043d4485000c85484050b40364a0005030340e113108070f802019081d40004200015080c054001074002c10080c3c4d2031092130b0b0154103003100ea8254040340141502001404580100c0d40c68102e4800107000070000501c4940d81d8042d12000701688004580c503400c00314030042816000007500141c0355081c02c050042036440182c0c0c170307221013515949600c0500d80c401a40180482580807880540440e000011003030344854699401c050003800c50740550b070038680c0d0304c090386c5000f044c2c0703820180840d2182c5056445554801c444454000c0080320f14040c050884100c0b0300d110a40c0900a800c030312180c121150101081c030880954045450096600c1148200002001081400101c5110f020000341c55040361400e54044d10 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 222721870 1250 222720620 222720637
    0x80d0f09060e0105040b06031b15090301050108160b090d0f03020705090c0903100204060504170109170d0c02060105010e100e030d0201020301060914030c010c060216110109090509060417 82
    0x345003902c03a508054055103c9400740340107941e010b02c184c1d00c02c810550358020500540003170158a00d1414410708010f0244c2160000d501392a41c182a014800706e07084480980c007520980c0d100e030694110000340b1a040b080640a003206061800000d00c1c046415071540c5280140313001120310021341803510074070908001e418003d040071041d0506c00e01c51a440c0e005000018802d019013407034124130841d103100b1038080302c490b501c940b41003601e486610003080c481d000d140c25855484100000c00a400884415a10808410210388032043e444200048400440c07403802554042401404540e8000b88600440441200c4e051016510003800319084042841c100c2c2d014440d0380380d0709641c0c84e01900614141d907000e59034a04182e58030508002c0000e0f80d4100290503800c0000701440652040c003a00d0f104502807074002d442c0c10035042001510680b1004141c80d100d400d0030039000c142d03a10231030600040c12250002e0081d03080c5000b400d5100e05010300300070301c89002040c00030b200c0a00c0d0300507200d120 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 222723120 1250 222721870 222721883
    0x80402011707050414010c2121091103030c07050f120f030a020f06010b0f030a0b100306090c2307050a020d050705091003080a0e030709020a0c110607080d0f09 70
    0xb42070070040a400ba800900402003e82c3c9403142c11099948103084503950140c029103065441503402802400759030a00b07401c0020081d403495407500003461036118509000684500081e11081c504005060004000115100b074008100110b5504000182070f800c0e100708503651219240c0503c00290f130079801d50070f0210107000701e266840c03081c20084094844516a60252040751901c440655150381007402002c450701c07001d0103040c42980d001000745601440810300024a03154200c009850071085510440c0000e0f15041c0510041c2c00b10300403241c0038200c6040c2160003201020100c08143d0360030040100c3e50601086030f8061000401030440c03420b402500303a80c01c09100c0c1c01c0c49900ca0305140105400351410402062030540d06080040881e80c020002c81e0030705801c84c404488206032400100d03494491a100858141c8092008020424064680c0c00001440e071803c0f0f41c0c4801c1d009480d40c8203060501440c1c01249144040310500c01c099440000c0302c601a43c2c001000785224030b00034012 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 222724370 1250 222723120 222723167
    0x30106021f1d0318030325030c1a0615180121110c06010b040b091e150703030b0a1a0a03090606033207090e030f070c0609080a08070308040201 63
    0x1002d000310081c10248900c1071310030446a9240d0605030b9a201e0410403400c0700c1d00040c2095041e810020401100c50700c0b0f4541210344c00146c2d10754a072500160156128060603600c140003c034500b254a9840201001c601c1038104503920044c8a80740220b188100c0c1405844c04004120201c659981c583c0108400400c000b806451403030904030782c0001e82d604801d0f10500c000484c00c114040203860071201001c48070f500e0141a08107218110281c0700d0044c1d83c0d8101d2014460300d80d59031100c801801c0f240c00c02d94649900481c10000c2c00c0d03e4180700014040e0071070540500c5450000181b158410300c4048605580d070002001c01c400600030b851020300010f25000300841040003016410b80100e000024400c2c1000040c0312010a0002a9440d0910741d400340b5800c000517601070f041b92550529040989041c540900c0e070f500503903808078070100c50106443c00140417050300090404090009000100302d4821944d540202c0e84c800c0d0391024080c00040780c009000c581c03040620b01a0340010a041030b54 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 222725620 1250 222724370 222724421
    0x110105091f0809160e0109020d0f05070e130e03090d03050c010c020304050f04051e090703020d15060b070c03031d04020a030504031d130504110a0e010f0506030106021f 74
    0x4044401c3d920041c040c0181c9003903401d8000000e2103d415075200c1c400b0032207aa4649491000254044c4100c0c49245840f0801540311580d184203040c4542e040343c5417040d4000140381046901030f4920b907100c481600d04000c20045a600005555008000f5034130207010024508055a10740198025000d0941c24030881218559021000d00103c81064400d130222214510401050300d9044030500e050803401030105100a00c1a00a01d4000c01401c00341e450103516500420300f5000c3c40c9005070b402e040814800a071507149440364070000c000101e035050403c003080e80c9441e0010014031016007040003004a40301c9603080a803114014101c010401c540d0b81e441c2600c007130064407086900f0303000f14807240219900512400e000b0342190f04021f0000d04100d9035415080006e00010700265000310b41c111181c040ca80300c1d48c4110001e8015006840029890403440e40f040c0c290541025014202c148010080d45400003021103e029030519000b20136160405804010007a2800100c80198200d03103151 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 222726870 1250 222725620 222725627
    0x706090b070e03120c060403030b12010609060311040b1c1703090604120219080f0d0905060a0f0209101d100e01200c0108071106010b030901051003110105091f 70
    0x10700c0d03031043c1c059405540d07042508424600425401034000e070011400100060710070350211507007510050482e00c4106013400b1f814216005600040c00f0f0b0350b9500710500c10300406010203d0040310860b81805002c403044085510fa01a009001c0e400211100d40300040001c2d04070315a80182441110544a2500b0310300d5a80e10b080a96003a0380d1003103142d001e0410540701060344c0b10001c81c22456100d07441031940d5801410f92000072881c1c0c001c0c0d018080740d054602d05000b000b10b4940510020200d038100f66090204440c03c5109460340d0380d00c1004845000e48032000300b200c0090540c01d000c9a003051522030b21007007969800c9081c4d44146031140001e002d07038000d02211401c5800313a8503061103e0320100f00c0d0940d44103042c10f10407158041d450516083d88034508007540070426240254000d40d0760740394540f6024081e0070001040f84040100b01c182035092180c02d901c00703207001c00c221005256440c2d80500d0007c900c1264108034000490184941311502200d030051035942c03000d803411341d0910004 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 222728120 1250 222726870 222726887
    0x60612081c0506010203030106050a020304050904050a02120a031b020d0b09100e07030c15120e0312060405160305060411130806010506030411010e0409050105090c04052a0706090b07 80
    0x1071855003a510381d4104003441441031030710401c810380046180d43d007070680541d0700da049003000e00c0c2140301c100b01c04103039507c4505001e03018038440e00007041c3c9a5041e204101001003030f89110700c001c1c0d000c29004404640c3c0240300d620042c0c0801c048a181a1060000c503200c1802584041d028079100000c1c051b242e00000785020480200090800054040a0003030740c4411052001600180c0c0303404003402031002e408041d40109660b42801030444101c840000107694440303010110680001c0340c490802800d0703202c45a4400800c40b400c000c145044240e11907600d50303440c8500101581c590004540752107a60103030041501c204821900d0f1303a00303000418440c1c0c0e1140200c01c580d004401c00002d041c200b10040d00d004941c0202c141b038a60006100464044071b0003070b4000d5010340c80700c10081c007140003880340b24010b0142da03010b4054007407208180029641d019260111a80c031044500e0051040a0700030034401e0708450038150755000c1c9042000c090142c1d480086c0451162109001a982d0440900f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 222729370 1250 222728120 222728137
    0xb010c12120b0609090a02031e070519030b010c110105130902190e090711030706090b0f101514222102090c07060e0d02010c09050301020313020d06061208 68
    0x41c0422081c42d01032200c0e40c050840c12035008803008010450220050700916444504243c100142d4440500755414480003a83d040c00410030001c0d2404064050035100d0100240a050601001c000316000901c2d20344900c0000d0031030f000035044481c2c268031580c211880d14240701d01d0940996191180c5c100294410582210110310250104020724080c0d001d48840b1100240340c43e84944e100784050b6070b90354089021000e54041004030700700081711886a0000640501800340951070885c400c01102d2001030001316a8032301c3d4400411401800300382c801e00780c440c01d280111210300030040c890458010200118451015404a00c3c421000f106101c41140c80717070800355113082034002c0700410f8400b1403c8082d4100c013243c000a80a980c111006009051003281c0c00201681036180d014101030402c00d4120041c0d4441c0401030041c4c1e8015038140207460102c008600e582410303114160540d41f07210000b070040d100e052400c404e10000394001001007000c81e2080d04a1803961518290581c0200e20 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 222730620 1250 222729370 222729407
    0x2101030b07050a18080f160e1603060506190e2e020c06041d0114100f05090a060801060e060c330c25020904140c0d0b0a110c0601090b010c12 62
    0x3004002403c6007c0f040100c9428001c0c0748415210303c5020051180c15000b00c1080c191580d20000f16900c1d154024001c400311194108184201503100500704004803c61511070410b810f180362098440128440e0141d074205c45018481c1c0c200f4000ba4140800701007480e81c840008500001d0025501200c100301d440043d070181442d03178075020b00701c0016044403601c80d006454110b1401c03002d400f0b810000c0107003601d805c000e42040011000500c030401c3e950002d200040102004121158010947e90070ba2441240c5050400360301e0302c9000d43c0d50a12003201c0146c644141c0c0150300c1001c0d03401991030010482020301180b40b4241c0034042c01584815043c2d80704141c0440c1400c4500704c190303000001c29500500c1d000300c07516140c031061606444034160010500550b10025a00d9490388600c5124a01c201d03e43d0035549055540e130800c990440070280e0700f56004000c2107420842c0404d01d50705560798003400003003400d0b000c00122289826071200620303903408900b41105094020420141d24030b1b4806 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 222731870 1250 222730620 222730633
    0x17010e0706050418020403140a060b01020a0b160e030706170c040617060f04020d06030b06060702010c030c0501020d0c1d01050903030d050406090b04082101030b07050a18080f 77
    0x405403551484248a0074002840a200500c0b0b010005a01507415500d00180982070503240e8480b141015050801d004a55202220040c10010780d80501c042c0d0380800d0000e425100d40710345858008102c0280482c2c11140003640c00d0440c980205003502c10060054221100603441320006440003101000386208010f01030000b0b0b51041900003110700380c034084c0da6812040e940726100e4044940001d042c0f55884000c004124103140c0301c91014000702c0d0b40355200071560700e15505050380208009000c0c58041d81041000c0000f50340c0081c650040d00b03506144c400b104001c18100680207008140303480320801c3c20243c007481160b500020401c4d101c645070360702c0309180c0503041c01524988564060141c06810501c41680d03030304003642c001680b007405020301013040c074a113a44000450340203c2e000c070340174034010842000301c0c41d000238190031009015161002a50542e103d5a03003138080201150708000000941d000000d100311650a241d1031030040c3c00a88a80b501d0160b9152000340c81d40002600c0b030300 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 222733120 1250 222731870 222731891
    0x1091b050904081206010c02120c040b0405090a0f050a0b01060306051918110c06011d010e060307030609060e0706020c03010f0213090b2413080303091f06080303011701 74
    0x11100700340510f40c04844946480d500c92030785400c42d00e000304007074140a4065121000741c0c480500c1143c02c408244043c06140400004010444901d400303007a01491812081011541000030304c883c003542c10400385000043c440c6003540c42c20b03802107030007002e01300d000000007007079030b01608110155141210388445141e00c0da550ba00185000d44903190515910900442c0682d03c6c43e40425080091041ca0514007003e880003146042d200303034403442440c541802028920010b80c0e5955024004100c01a04c0324104040001e5580b005400003810041e0b60344000c00400c0016484400c4d01e00c010310a5540641d50b034000652101407401c0e045000754200764030008026410700c01c0725040c421f0441804541030900100c40d00602c1800c01060b0000b1624401c1940c2c030300c2c08981c9a1413a580d07000d07240d6452800005034150b0385e032244d010b8001980280140b1880c04400704a6004d40c05001c1030b10340307039501d0398034030000070b001c0c00d502c0081103010000002c074402141000c40e8040941980c001e10000040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 222734370 1250 222733120 222733129
    0x30c0602060906070e150f0405040b0105130b180306130203250b0d110301090f06060c030e0103050c04051503090c09090a0b071e11070504020901051c02070501091b05 73
    0xb16003410203908000d00103900180514144880300001900c00c07070203c0142c5100c0860b43d4050f40d030b280c9818401103003c000a107801e0141184c001d10a00c0c055040103850a0071600c00d00050041c0c0102d0b043c08036103118070381946d50b0303000c491003401402c5411906180d80031014040602c88240c3c0680108805520511080165008600c0048044140c51382c988590235200d074105075249485191103462003100c0b140082c001e54043c1541400016801120180307140c212034040e400841805445030540001c0383c0c00882d0307882d02d400c3c00e0034042055502c3c44c142100368441c0e50131a55200394090482e411260032880510301c00c0481c841100d1140942c0c80c2008001c0130112180d1030f0542c030194400c000039844c01129904049241811070009080382c541c0005074100c100360070b0014030841150365200d00b0400c6804010308051b1021880c2125100000303155205481c444440f00001d6000a0440242030341107405050700880200650321031464503000c2ca444800c1008840e40d0303960004281c6191 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 222735620 1250 222734370 222734383
    0x1a0d061d0c130b0c01090206031e0601080f060607020d150b011205090c0d0521030403031b021905030403050a0c030b091b120f060703020a090e01080a031103071506030c0602 76
    0x45600c508a2507600d860f00420840d4043c038081582ea540f55146280161200000f560080f180d00c080112230690144810070701c074800400071030401c0b11140070301c441383c8810700603641c00c480240d55040d0385101d5800481d140314a8180700904890700c440c008017165031158801c0700f01c0c070800da843c1e02039002005002e0003980d20071b031080110b51304040a4071204c0d142c4685040d81e0944a841502c4210b2500c0000024080c1a0001d6400349440001004105a854820700072a000070803040b900614106000941e1800d5460211540108c4240d8007024803e0802c2541c00441d8003000f240d42401092801810070700303141c801181c1c081040d4001c91005900072803070140400c200d06401c581d0bc42d804040190a8809014017066800b9061002008010502183d4442c50f0746450245e618141100f0007440c141090b07000e10400002540103204064021403404240381d01f41c6004151034119070708103410351042d84c3c0c0c01400c0c0720300b11a4001030a4466003110003103a00842d0740c1c143c2c00daa01c400c107036160314 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 222736870 1250 222735620 222735637
    0x10b030309130902120703240c0915090e0907080f070312030b040609050f0f060d0f0b0717010f030302061003020603040b09011d0102030f0c131a0d061d0c 68
    0x100a40e030098a040c0c100c1d40501d07941130008008810402d03001201d541080f005070001d403a21480444084010050390220300160003042c94104144402c03101e00401d168038038060390000044400100402034450040d1030064242061a98507500f8000f02050361001039206401c024000d603900c80c00100c0d40420120300300c07034000403184010807104d031007240204844490203a110381d40703103000305001006115403072033108460880340090602e461020032060b002803030f05100700d55100f0300350000b0b031825901032000383d405180001ca54480d40f20a4490f004031840f0301d82203040c220000110001d4600340042100e00a8003a05d20685803000410103510880c080650004000c0002c1400502800662035000000d040006003a43c00001d1a0a00c4041c1c10000b1a40761740200911107070014560440c0e070820f031002101464018198000d40455140d071050302c1c01d8404d190a003040c107580b0b00049401c0d1040c3c000742041840c0e151411051214404c0031100d000315400f1000804184030300301124000c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 222738120 1250 222736870 222736879
    0x1c0c0b0601090b0d0b04060b0d0c140c1902040b033a090b091914030c0f0306040213090803160e090103050319021608060117030304031d0111070801060503010b030309 73
    0x45510f00041c084d00b441c0003103980059841310005401002c06000d080c27410000000441c0107249481c00a100c1303540ca8008075052202049541010800050001480031503008034414400d010b0000800900004840c1e9415004400783e5000c0d00c0300b1169a0b00710140d203040010303048144540007081d030000351103028020031400030b820711400355042c2c0038082504004003040d0090100a4884510340c285a00c0b50700030f1319103141d4008980c42c050202404000054601740104402e13900002d5130b4840150000e03003c0c010242c10b0305000b400941004040540000959542e8280010003103040407003400200001803102c803c010140c03410342030039030489400c03000075402e006801242c00c004030890381c4041c003940b1070034011001d20501a500e500c01031062402400c22985407035603042e01201503409030038558000700104000207401c8030119842251890001c1c14104d8080f0050b5150150a20241d005201310301000818040542010003551400d5000340842c0402200f856968041c010859a00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 222739370 1250 222738120 222738127
    0x1e0301080d050306030f250b03040f2604180b0f0102060a15050d0f1103120f1b19030201060611030304060c030605060403120f080c0313051c0c0b0601090b 68
    0x22031094020b0744d0421002410303115020b1010a02a01d800c40e0303540c1c0210807010303111501d1055203410151800400006040911b140b6066840341001c80356007100800214507400e10348203e20311510210314006c011000180d0b115103441130f0700711f9a05c143e201d1010312420420024502d040002c11103004000c1a001440e45448506584000e030036150440d205201c80c90500240315a140b008020344c04d07000710500c042041c1039081c0a40e004030600c4105019510004840343c5141d50071040ba0072054080c0743c03041d02c808009d124402c20321105080480303984290f0300000354503510340f44100d500a22a80080085c3d90fa80c40c3c050340e00f220369617080c0d400383c0c00c14070014010443c50380001d1065280c2d031400082d0315440d20002440354006030000e07201d409501020130038164100300741d8021036640381840da91351f160000a529461100401443c80d50307c980000078100407003005041141958907480d2440b0500c041c400411040401d202561003891090114219500a01c4400159040030407400d00e0f = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 222740620 1250 222739370 222739393
    0xa2103031a030d23030126010f1113240309020a120309060807030b06270406090905250e09070806040818010f050301050d06060e04081e030108 63
    0x81601140090080350591180e20070342c0d078103000c035820040160b194407510800801d08040190203002103101101010001803103102840a44030088069145095610804034024070340540f0181c4039198103141040d416403024111003000d00814461200f9034442c2660383c10282422002000311440c0c0158090881c85209200741c110788585800a06080320250790340308900100c030090a0300780c001a608038801d00259900110080d04010b5503d41840300c86042c00010342c040c0b0410715100020248501c900303d01c03080c0690780301d0003070800410400c001c0355500c0c041405040015000c031030a004481050210000c0d90494918440926500d04000f50404100c100c0080002d00804201e02c01c8104c0021000f8007004064443c0b4820380b845921562080c442075500c02c80420380368103014001a20001c2e4a6000d0280c9044071000c60340c078400101c0d5410800020b100715000741d03025020441c20031051152110080c42001c16409500091a17018070071400c16020a00500959401c1180c2e20fa0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 222741870 1250 222740620 222740627
    0xa020108010b0c030906030c0a0801080f06010909060e0a12030b04060e0412120908070201090e06030a0b100308130f0e0c04050d03050d0c08010509090102040303021009030201060e10050a2103 84
    0x40c004602e07000c8030310708102000082c8068000301d821810300c8c0800603900302090780c03004006004090002c0104145400100f101d41c4a6a05028a4404903038075079a44050100a40000c94501d4000d003c1c1e50016246c0d061181c0410302d03981488010070304010140709141400d00c0707101e040711f80e40d001c40001911990340c5c10342c540c0003102100f010003d039801d480040c640188510401c2c940b1425080c6c0e40d03000c0620001d0701e00c0722035030302c01d140c002070074820000b40b614049444541036038800c3c00c81e000c56580d9039503442d0150003508090b14400011501c00410020912540261602154640412981c2e0484000303201300407290b50340c01c04810b00041000e07041001c0324500c91032007402d000382000c05c000030b032030111143c0260500c00500c50100400007810301012003504142404002c0d4601070641c0c44c0030359602c50460380103901e41c1e40d03a2404070501d4400e50203407000d002c03016600141410000010b41b900045406003622544c2000c07000500c41c21003800283c3e501d00e51041c0c03844116980e4800340c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 222743120 1250 222741870 222741877
    0x19060503060d0f021909060504060e071215060801081203010b0406050a0207090f090303060501030e0c09040219060f030e1501060804150509030d0e06010302240d02160210020a020108010b 82
    0x1181d443c01c4840301500140c0d540003c260082110000301090725180641e00c0d000c0c1c0c1c00704e5018a01540c6440018010700141c0030303c4691003041405c25491b84800c1c03005c101d00500d03449520020003c401500491411391002600e07040780d451008440c0780c0041450381c0c5c05603120a108a80e1024000c0000f0412140038038042c001d0201d9500680e80c04590310310b01c8105a034402c2920b410306a6899400c00101605031050202409081ca800c000189804094694984111901da88180c0410000601310341c0c41b09000c2122605c034004079560720341c3d51503001d40300c050b4005400300413a080c080d25240726800000c07800d20304250181d65400f0381c1d2800c2c0094600d624060030a55083c2054140b001d5114840d0040d280552451070040d40d13500d4400101c0320450320858134111841e082100100050303a940312001004143c3c8140a0400a02c0c1140d00e102c140700d64204031190500108040048407800c001180c82c1a000340c502c80d500052403401203848000c80c0c80000e020401190040c0102d55000000c2e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 222744370 1250 222743120 222743123
    0x9030f05070b0a0306081519020904091a01050102061302100f02030d060b0d0f060e0708060d050607080f060409150203091204080c0a050303040b0702040203060d0f03020c19060503060d 81
    0x2907408880d280d54480e441c035030021075840042a142c5030100031500003080700c9a40b44420312280c0315981080801c03100840c6d5030f1140c000800760080356055590340c0e00e51100c001158424031822000001c20100102d100007442014050300880700041c0c685440c8011410b101d039070050441003604940c8200380c465545070203d4074114032003800b0f0301030038148034821900039240e030303091240d1160b866034200d60607203000c40b14800400b0f0804c1c404100d40e1814544898100116003028065682d07000301040c81d00d02000c801804c148215800d00c44c0b0750341c02c1482640501e09007102500140d0740c40c41480b064a071703a010020711603640e10001641043c2c09502540d00101c800041d201d0701400024400c0c1070b90401c0d0000038040e00000050070703092605a951000603c02940590f080c2441c107071300c01003207020315440a8021070b00000001c20139070354803500b4220300350301000c084c034250074504001390f44507003003004140190740c1403052800520f04112214111403140e0f039498999611a401e020004141140 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 222745620 1250 222744370 222744373
    0x20301170d1d19170601031205180f040902091006030c0309110906060c0d0810120c0317070c060201020c0d050301121502130e07141303110a050a090b0102160609030f05 74
    0xc03800b02c121008a40410113482d00a04055045003000014103101070040d1003030040401c5003031000220010005441c0008894480680c800345002c05d005c2c00201130000d5000400004011030001a40040750947e00e040e5400c2210a20740c06081c0c044070182400a400c0400c4024101d0462401407082640b004003d007802d410904030340c2185240901c4100c540c0701244120081109840b20b05010a0080503000d821400284558031940e00c0101c2c0d500016007a180691420b011180c0b0560456089603030020600e0f8846a54100080c000d401604000c41d1701e0040516a651042c40790307082e60306076124501a11405400756030354209200c94014040e03907254003882459840313440b842d801e000408806007151428a442d840060440c500d00700e40e408214804c0c401e03a00c1075000d90318640140d81d40b0116140c0080740500010341501d082e5885107034803600c142e601041500c0640c0000400c544203070221855019040105c50741d1040343d002c0c0800140ba06041040410300542c05540070900500 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 222746870 1250 222745620 222745669
    0x507031709120c0106030b060306010b03041509080409050103060c080603190f14010b090a061d19050108011d1902041503050d02070303122f0409020301170d1d 70
    0xb11054160b800c504921102655210381c104103010485201ca03900c102c00714060101981031080107950340c0030141000c0c0241072840f1446c44060702640c450b0000540100185803503075a50921340c0041c000c00d000403942c9504104011030414044d403c2c4078001d0f14010040c20350051202901548078019103419903840c0301941c00c0e240403c0c07030850b5030700690802c07800200320544480c0034410a803801a151001652410390108600007008270f040481310440d0340c440c41c141e1070343c8102c00da52003007032441520070303e24000001509010540c42840042945000303403000f400c030340440fa615903540d0f4a10104299802c18030200618166101c155040120714041c0315203a200e856051400c03106800d1040581c0c04040c090040c903410070381c203a0400700c00f92414000c500b19124550810000610100152406105004000300054050b5006806801000c40d00d039a0350315a1054079030754050b1322644602400c5161418907204080521036040d080ca036408500308640b050141c0403068603214180d104489 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 222748120 1250 222746870 222746893
    0xf02061e0705091306030c060206090d0c080405030f100e070501080f060105191101050c070f020f01051e04150203030c040b07050a0b040302010207050c03010605010905130f0e0a0b070507031709 85
    0x4901c4d0420074910312400050f103a0452400f0481001135411680070b40d403040301000340c26900010a4064070702c0c140b40019510303810b40741940d00ca011f2034008580c140542c92664001e901c0015100e038960280c01c10031306c0418865840d9603140c8880f402503e0000d841030b0001040784034400241c2d50040030625025217010080d10010690081d0305005000040100704160442d900074040c5503080340c140a40203281031126554261540703220320780240100807403103042c14142c0c014015a80c141d01041d004909030710843d1088003090b0300c42d004406414031800701c2c6100312840041903900c02d01d42120103a15041c1480001b041f5074025807400c4070584520201c0f140000d00c0080c11354056403080c1c001584030320044c40d04900704400280340c14000da16020080100342c1e8403e0b844030489505544210010481066450251006c024280340c510300f0700d44684182c41c1c00191311780305140a030401c240030791100380c2c040701c240c4115107001e00090780500e0f0b4007411901154480740c02c100d0341c80481d02d42c003084 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 222749370 1250 222748120 222748129
    0x11070302030111070302010b010824040e0f07030b09030c030318070305070b0307120b010806040c030e0610061107080d0509060c0a0c050307050a0506030403180b040e0103030f02061e070509 83
    0x21801d0340711034083c0070039080b0405030240503c0b1307603c0c0801d0a002801d860460a43d030100254800481d900380721007140030800b0388556101188041ca41001d55100804c555011a61103915200132180c82070f0729400980817900c044203844003e01c0c1d00303024524648401c081a594101200007500e60f0340941a0000000b503000c000260050111a550355104d20f00340c00003402405032100700306000d90809c009034945030392044500754070800031600020303d0403460b80e04800420004140d144103104d00018171503141c0e042d400000884681d555000142c039030000d2400e071140020300c01c0000c0f680c40040c844282d20b02a80c0900003094010300351600f03000c001d0354144e29000c90030000ba540e070745004500b840175080500c43c1c0005407400365184081c013850300780455140e20000b00b000c0c0400909840d042d00e81410040c074200100001f01e00070351101d80321101c260300000203101c11001b24060007800701c44180041340c020300c6034800c41a040c0f44040d00000c40d0340d620780020b01520810400300101c0585566 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 222750620 1250 222749370 222749381
    0x3060a0915140114010f12110714010e1c0903020d020103140f09010c0c050c130e0a0501051f0608061e030304080307110906060409020906120405010c2d110703020301 73
    0x40c00e5810107890b52500380e10b400d81c02040f803504d030304103d0501200603401d0703080f0400513140c910070312000035100c4001c0c80d810410700a051009140301004c01d9008524201500420560f550020a0b00c1e07400d402040c008140d42c21203100300f008244400f804001502c3c1020800169a0044c14046480c5240f6240d2200c40c000448400c40ba2030403c0303085c0030002c2e8091146c14044000f505140030703440143c2d16516500c5152041080c86500b840120000c11741701e58001d030388203903551740803500c4000051034468040d000860f104489513100360307074040d001c1c0003400c400801c40740c0640703840c0610b40f10402840070b1150342030421104030000d60080340c080d4504100030001080140080c50307c480380c9151a101004090f41681d01c05c00d51441031000d0b83c2d9880301181d0888011001c011b0b51000e1580108003240110307000081c000081400b00030a121045d0000200c40030b0276a01d41000d0388000424404c13007140c00f0511080100e02c4454000d580e802200c021850781c107810100e40b800e640d243d00003400d540 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 222751870 1250 222750620 222750641
    0x2060403050a11060a02070b0304050c04060605120a09021f1806090e0c030105010e0d050f1b12060c0a2307050a1502070809010c03200d110c03060a0915 67
    0x5001d20b00c1c42c020300040e000080c0000344101c86140c40c1405610000796100614001da0340501c40c0040403d0070040104030a04c198440a8000c0c4509941e880b80540309030490300c0904001c851070800103201d00654414858004c2d80140309008190140c00052460302c800070380d08041c4058521610702c0003801030b42043c014101c964505a02c01c5c00c1104a400003100030b032074040c3c100c3e014001841180c1e00030070300304841c44056030030442c90780780c5040892500c00f03001c2c4034036524000c40010341d020054980c0400764916060b03030502d4441c02c0343d0400300e81e01e40b0201d8000115070401d20500c0607544c0b1403100600011010340440d081d01050720202e503400e40c000700b01181c0b070741c0c883c0090204010300c820560201f0b9054103011402d102c41c5880e11034040c49104142810002240445402c060140c50451010a207183d0030301680c40c0048181955070f400b44c105840424039107015040701c0400068502d05424000d00503012984422030254080d041c1000c0455201003840300c0342041e21918401e030343d1243c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 222753120 1250 222751870 222751873
    0x1030602030c1b0f0d09050315100b040602031801020a0f110a0b27030f19080c03031602010612241d1c0c0819030b0402130f0603060f060c0f0206040305 67
    0x214404c0c1c4070340b903c020704510500f4080d44980401c85540c2c080351643c61010050f0382e0300440c1d5141c2c03003a09003010146c1c11140c9003031008280890701c01d6001000e03110850b09204a84a07480140c0300581e560f4202190041614031284140c0002038080904403800f0580030700b80220460710b48114030001d400c5266504051600c90301c200320544d000082c444860081a400360950208c3c122406484543c2030203a0102240c2d040b03503031820403089108840301c52140d00c007034039201d0802c0c40b880e000025415007001c1c0150309111001c110241c080c03500300c110b2a4050004505015440b410300a07851200e0600e5101d00c0d40d07040710034410044070a02100104101001d0300c03241081d0f441c8150b0141d4925808810400302c0c0c5001000140c200040314000300c154400f40c0565940b0480031400307400242c0510340c00500101d140b80304a080b001c14082030744d141c6841700d40e919880f11412401c4502c03e1050f458031480040040252070701940c590b0246c0c900904046c48000c1b80c82d008980c4690199000f203a45 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 222754370 1250 222753120 222753133
    0x90a03030302030402040b041b11070f080f0f0f0c150403080a170901090b070c020f030f0a060b09061f0c080f0c011a0604140102100c0503270601030602030c1b 70
    0xc625187c462001002c104a0701001190380201900c018950740c2d051a80c28014a4a101d0750f000d502008414002d0407540000c241164880c1035803910741545450b455420702c070344140b11407581d0000c5085c1d011711400b0f0000340000d1500304100510505501c01c080d2060004100120102d0005001800034000c56100c60032a000c09003c803c040400042171840143d01d0996030400158003a10301076002006454618044083d5000054403000d82e1042142d00d44246503030008c2c02040803424030034075401264200700a40d203150a0040e0100120360035a40102ea081846080880034110744049150514081c1d05c0c40c00a5528500c1942c0030b161061a924004269010447c9003402040440c00002c0d0000640d404035901017101400350b40680c04020b45c1c80e600300039669108100c0489400d61201e02404003015481010741140c0c01664004215000809648805080d0303103410094801c80000134a280d80c40e641700d43d0025000a0403a00b5902810017681c0c540400c0d1156201110400700064040c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 222755620 1250 222754370 222754373
    0x60901030e0615031606050703031109030a121101090510090c0803031306050a090c03060b0301021611120a210c050a030e0a0504090b040f02040219020c0f090c031605090a030303020304 81
    0x7800b1311002201745c0780d04130302c2c50a0045e65848000c1e260756135810300340413641280681c00c0d403103180600414150144614803050050043c64038456600070360603140c0800d541c0c1901032860030703120303d09006401c07640810120361030002c6950102c86114000c5d461010340f03039100e9112b1815644140d804410390070f00210008144001880742e035800980c0502c040200540c42d80e2141c0000c4c04c00d10020380b2881d40c81c40b0305200c1e03850a4040301c0b049003c41c80c001c0a40c1d2650719240100c50485c00106003e0b00403141005041c220001d002c030841034000c594555039100c01e00c0240c50a0301e0201d4000b0401066090314070000702d0410280d0303511407090301c514990301c84502c2405a50942c5600080c81182001181000706600e05600c0741c1042e0000e440700070030200c43c00441c01905c240c580580f4035031a190311900c050742c4c1c041001001f004080303404120410000c1d04001c00e446054070f0b200740c408802c00101d031055480c0390f0740484400d401d040031801d14641c0400a00b1000c0d40b94030a6010a400008010 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 222756870 1250 222755620 222755623
    0x120703020a0b030702120c210c100509010e0303010302011202070302120a0206090c10050f0711120a0b070c0309060f14030108010f111206211603060c110c060901030e061503 76
    0x151b404000b468554140040400300541c1c40c14001d0801040002240d44011540e00000444200105000464001c00ea05040c03c00003840100c0c0c500105501e00744e190152100003104590403070307405070344640d24440e03d115500000c0d40000d6040f0258403400c0c204100d12401c440191200c0040c0b038001c4c10706450958003145c00c28003100210b0340b1403000000c0318104142c0090603940d9411407049419202c942d50300e08000c0b5000c00d09250360740325841e10315903101900001245503000d403040c20000c103981c072505402c0c0c58003586248010041032441c4000c0c804144607004003040c0a4403881c0051180d4004040b0f98803682c42a0050201c5945403440003804040354010316600d1083d1650f40b518284032103510402241001d0305503441554495500405141214140181c07801d006040d07505050746000b12843c0130700310740b01c100da5107400d000c1d030740650a0241e9000c600707680506014000c0e4001c0102000071039132004806a0602d40c1d078680b0101e41c02c030100403243c070500740c00c0ca1102d803035040e900030103 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 222758120 1250 222756870 222756883
    0x81c1b02040f0f050a051b0c07090615020d05070804030212010b150409060609050306180f03190e040e06060f01110a050109051501031e061107030e091b030105120703020a0b030702 79
    0xa01703d5810b040c00d102021113800d01501084a1070008181c503030b0201c017000c0d402c258444c0d20004010b03050520224034a60b003401080c610440c250219003d04074140c50079502800b680401400c000000e1204001501f880c4080302d104940c480000100c0b50850340c0011044503800c0c000030320304100420305000c01079591090b04054072607803d0150020340740c01300003036942800420b4208000340003418402e0100b01048010488a25801074940304c101c008040485e0070087d040d40000a4501e500c2244103062621914000022250107050360750b0715002480910041010a14100981c00b10130210070b580c107100c281400d92013240049910003803410f1441ca0035407014481600c0081034401000040c4548408000c2c5075841c00200100c1c0d1181c0c1090703001800684442c021076240040c5040405a000c503c40001400803034181655865402045c00c1641201e880c80b0940401040188078500e4500491144882a40100c0c0c4245460358003040000d8003980c000d205010010050066158051046 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 222759370 1250 222758120 222758131
    0x1050907140304021e06210f0601020a06111b0601032006070b28020d0c03110a0507060f060602030406030b0d02010e1327020a081c1b02040f0f05 64
    0x784034004450a4408840d20014000a10642519041c0c148000b60580403490302d24004141a854044010150f10840000080441103039801c034000340111994003601030041c0c8040c1e00900c41030006030b40d090014001d03041c3d2840680700601181d600703d0110040c0e107051030b15a00c09014154918503144d0002c81071009460588280030000c5407850310350388103039011140c01c03003076654080c1c8032205c2081a1074800e28200005202c0000c004085816076002010002c6c03c0403410058003911140c01c9084a8801d0300102401004020348405988107402909005000e024006080c0e81d035081c00404455640d807004000d600b02003010068590035208207100f6030000d032180858007184e540001d08030340b4107180d0144180905443d00340c0300780291b4480c0301850410400c83d40445181c6140072003900600c40200d129450500c000b15140d100401c541c20135841403440c60b0800c031150a011b844a42c4007010a0400100181c00c00008da030f00c50091407092600b50710009440d125100c0000c003030741c0c0300814 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 222760620 1250 222759370 222759377
    0x50a08030301030314070323180a0806011e0906030b010503070605131505160302060624031503030f12040308010b0c070b1b060f0a0606080c03060d080708030a0501050907 75
    0x1000445d800c0701c040b02e098a2480201a81c4019a141c2541c100081d8600344806054100000004408504c010b025140342091581c4011521404001013065940900380341a081480100003d03401003c910110708460740d0b015510390b4a804850044800c503034810f50b0b1209204004100e6401c0500c00400905100d2078014501020b8441e40d1404020303070300c1103041841590610040184c401e2050300ca024441418110300f00400d811300a68070b44083d51654807902c0b80b404460b583c110010380078402c4002c0c0d0140d581c1150b80e242440941300e418280500c2d0140001c0004218202058004040c81c001c4051104901c1c1060f0900a010b04416000100042c400300441741104c840000c203841110381400001d82d50b13411140200c1c1111800d100c00e44460710905050052444204042601c28005d4460811105a40740c1080302c10f140d0564040c1141c11042020032800c4c109643d00855440c0070703013065031406d4511790310300c192580122182c80c081d030ba403100180107071701e041c001c0560000010310f07 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 222761870 1250 222760620 222760627
    0x13110a0b04060807050702061605010606170a05041b06030218010e092a0f03150a030f03080a1b050c070f050609040b03070302031e0c01091805180304060306050a0803 73
    0x810040306803007640110707814852080009180c0ba0f00c100c04443c000c642c060449515055028110100e40b6482207040300c19508207100030454620410450041c039210911003441c6440f510038034401050040c01c02d4a0364500100344410990301c0c40301000090401c2e6a00580d140d100030540c1d0024181a1100d0b4104100803c403c2d00030381e0f501c1004c43c0c01c0500c5042c0c2488044030044a64403000b850034107102c1e5440c0210700000c68440c640d02851080e50525281000d5103000c03000c00080b80f10030b000080551180c0c008000209115411103603100e519503c0001d604801d480104900c002c41c211800c002500009034003940d18400d02550f4024a010822881075a0502c40002c1d00360080181c5c076805079035114520703649542c0c1000352200840d005825070340048141c000340c0005801442180c1d0391841000c20225065100710360f00003c55941107064010005000700e803d01400014100c000074805030103c030240b809060004000425054800060051501e01402480882079000d81215003060 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 222763120 1250 222761870 222761879
    0x20f060105010c02211f2f0403030c05010e060a061e150c02010201020910350411040b041a040608070b0a050c150403030b0405090f0d030b120613110a 66
    0x81300c3c048031070518175801000605000198500c1c0c52200480f0340f0303030000007041c3c0a01050031030340007650088101418844650403030a811440180401440c1c6804404000400109100d812050100d80c0f14000110f42c180c1c81e071107128600341c4151504d0f0004c0d82d8441d0308006c030114608030700325000d144080c2c40e880c4500e828450240b1280050403d0248036100200004680c0300390f0440c2c1a44000070b013010b24008034044003c01400350561040c0561840109440746003440c2c1c04004681440c14803061074550300c0e0783d1020709047c8480101ca41007074440b800281140d40d41d004811680d11440d02000260110f60700b0401650b42661161000d50007440c010b000f801c0c1e041d4211142074a40c1e05000307984a4038001003070700e0140e03904503d0103080102401c0c401010b42c5074000d002203600440f01070159884d4280c1241d21140381e4040030f206644401004021103020350000e1800a100400304101125045001410010100c41500b402100410b603603040101100c04e468655000380c0300c80c805903041 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 222764370 1250 222763120 222763129
    0x1a0609011409010314190c0e0705070c030320010c020a05120a1409190b0406181514090307080f06151003050a02040b040b12010801020a0909150510020f060105010c02 73
    0x600000d0842485030038803100000003046201036081c85a034041d41d0300740030303401c24107841f01c040d001c0c6184440d5004003045042d486002540c10907070304144c00c034900c14599501514170604000c04007400e02c00d049007c0c40e00c0d2200388500c0c0003107000754000c0e1030ba51000c0e1030a00e06203000c04030310b1825584184051907025038000d49035034011588141055480540c000041ca1100c08902d0180c3e00c1d604415000c1131b0311061340040e01c125101522800a020003c100c00b8044412a0041e114035582d550408070700e162049020303031440201d24181c20701d0520048003003800c00580d60020000c0d540100804010080100b003103075400520f00c40c401805c03424010024003007070a500311030001c040e20b41001c80d070025003a60446000740340008280c0d5440340d84243c0740e0071582085030b941021084800000581880c18000c03100c58148990b1109402070601c900c280c02018030380c16200e48148480d1000c20b041d2607880700511035003020380040c42620401d030421450100705811460402086c40290001030f01e4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 222765620 1250 222764370 222764389
    0x50f090a15180b1309020c03070606060903030908030301060509091008030c0703150911060a110a0c05120105010f21020d080405090702010b0d0b1f151106060303120606071a06090114 80
    0xc0300c000c05a900c07004c0c07100080c51802780880c00b4081c2854181c001a50917040000700c01100d02c6900c2e8451403d44c0c440400b501ca020906c540c2c00820010000d207030203460f1803611b0551102820a180c068070b9100d00e01c06103180c01454006045a12145060061003559007004812010180c41840705000903a05c004040009689441c01208003243c0d00400c0c4e03001e40d440c01c0c0601c418100720780045038203081c0008074070014443e60340241c0d50301200104001c0107010301c0381659280c401c1e041c1c0e0180f8003818000480c6102101d8050407810090182c0141d1741c60035150411805000321a80300c41c1440b040050310b4201422072015680340c414118580d4607405100300616401140802103941c1e00800386503d00c5e460410640d203c1b00104000c0307105400c8018600002005035141c00300e01e26000c2c5802d950b060265a00c0354564024450090f06031002071a4652101c0c002e006281020231594503201500307440125040320031542010018035043c10000b540c0104041c44103503182c00c160720b0210b030031601c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 222766870 1250 222765620 222765629
    0x50a030204090311060702010c1103120402010f0302040911040302040e0a050c04090c12050a0c05040c0504030b09030c030315130c051b07270516050f090a15180b13 72
    0x15242c0280c07109041c05803811403051507558050721454034103498002c2c02024001c201401181c0401e44094903504000f055440c0700054510f480d440f511a41c0054490003030106501040580030400455400d01c40d00900091044000140351124210320411040c0d440c4403075000803c0c0c2c041900d000200d10009010310440809603000030f4211070078188a0120303031b030a400080000300300400e45410804000350945165006482003402d090315041003105454101440000040050006002040300300d8651600454080d0480345004443c01525045410440310008a1460f04980701d0541c102054040700107019124104050754010101501c50700450312100c0951180c082c08141520b4104007540c0a080d01004d40607205200e180200d07043d0401c08071000e11b940c10440480c09410300040c0c80d804000050b07c4003814401080c0304003030150845c00031103901903a8144001000a03113941c229550340940e9403180d22220050001e04042d1440d503011511740f800421450800c00310b1000c0150564 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 222768120 1250 222766870 222766879
    0xe0709090c051b1609110901200a050717070e0c16230106050402040608040219030206161a07020d260c0406020717100c0c0b0a1d07050a0302 62
    0x1140098112114091900b107040d02d402d655070440054a000603414424980c0760f41c60132180380c1c030b5100e04000e075a801184c102c1e2003003040c132500c131aa41c0224840d0340602400030000f02a0a80100700c00e1500304491400e03107083c0c010302030034003541d4a00c1c0070b05080c000210004000c024902282c1040c40701c00241415100b0002045482c500300801408044150b0007040010581114444407140540a02c5040040d580707080c40c0050141030038000c1c3c40403a8165111400d0780e503290703000d005104099040800845e11010030120060361068058111910388540c171418001492901200411000d0003000c080101c5000304204542e000500e54903032145841c0c044030020220040341c003d45504048c20048205800401481c00301c0380000e802112544d600712029581d0b2010703108400c480c03c1281180782c2e001102007a0103400c182c0c10400c1480300c01d1802504000c50354985101d200c9099646841c0d140d242c0c0c001445542c60b02941c0b0350102007a401520380310345008009001c418003480002d004 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 222769370 1250 222768120 222768131
    0xd021e09100809011b030203150904021023040e07030e06040f080c030903030708120f0f0a09082a060601020c03030304201305070206010f1404110d02040602160e070909 74
    0x1006000e40108402006440c00045180071508011b000b07900304407841020408403075160b000300c0c604480958007550b00980800024003440d0401c40b200c440300e80e071680036000e12188100f030140156000744001d01c00300c2204880ca00780504024280c854090b5002c17010342c8a1000d0201251001c2c3c8405001607021207a95602c0010141150030f5001308901c0f10b926020100d0f4260a1204c5903000f0302503100c0f4070840c5010359403a410403e44c07030030f001d54284c10b0f150003890005130348800780d90120150900506813142013188951141c45602d0a071210140102e0120103004011081001081e401c182d0034009041c4020f10303400440d41c0c84c040288042d104c142d800300d010a90a418464029905034040c003a040c15549410511001d090203031040c1c80184a03c0000207031312840f04480b501074030801c030b0040100c03018580800000d040c000600095400080002c00f0035400144000c0009151035005400c404050f00d0100da03800703601d42d0259610882c0b200801c580c455100c000101070750b0f03188900061 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 222770620 1250 222769370 222769381
    0xf09020301030218182d0d020a030e040204030c170606040204081510080a1b0e01050a05011110020d0606020f06060603011502030705030a1205070c110d030309080d021e091008 77
    0x714000314201752a1380b4000c00500c00d5525200e00c5400c0c0640d00d503031403214a0b40d1009001c032a560300d00603109400607000310a241c40005e00ca040d001015400051015040c15100d442e10301c01801c00d0f07404450781001405054003240307414007080d5070140088804500b800c0c40d08a03810b41382c04200045824011407040040c1c2e50b00c0c000118400a020703404219030301c541152800300c044c070b43e00c9038072214038030614400040c011000c0c102450503203401034040300301c1c00d141000543e01d05040381c14140c81800b940c50325032613482c95071002e04000c0501c000041000c600d13000000c0d0400c090340f0030348100c039085681085502d27119401160704442c01e602c0d40001e00805140100d00310b02540100034000c0c080001e4410b921079000d445119994010a010403050b160340b40f05482045903690000c0c007401d070340581264540f0340409901c01c4c0d64064180400c5880559680000d0340c1c0c81803c01065595000c280ca504100141c02d058401320a20340c0c204c2d2805502400041061003039017022410046071000040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 222771870 1250 222770620 222770641
    0x30314090612041b080c0310020703120504030203191704020904020303070602030c09180403020a030503180106031209170a060f0209030a05010c0f02070311040218060301060206010f09020301030218 87
    0x59254002c019030b404641050700d0009410300f001903e40d02c0707071310802e000071075a0400418a032482d06d80040080c130b04450103003440d4007c0e4010741400d03010700501d4440310340392030a00d009030b5200d81c1c402d40c080c540d0703070140e41c4011100340e0500c22440304001034864000c58076802c5c408072079049501107511610366562440007a00d54840d10200a003100d0000c0709102c44448610050580400112282d8803c052042c011070a03a07101228046c0041e4801015600440d0084000316004410713010810000c20405000b142074800740e50003104c2d444440030b01e09044c40e602c03c450002815083c1c500d020000c031035900e1a56500000c48000d0300c45540d030303e07510b1001543c4d98112a012400501070f00c001c4501c44c1851030003002c2060184000c2a1480140d4501c80d00c040781000540e07512a4101d05841c07049000d0100940091707440d641d03810858441d0300342503554040514000c011340c1c1d00030701c403d40c10420081640390560b482140454018401440107903203081c900c50314880820382c4d201d4290b840d100c450 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 222773120 1250 222771870 222771877
    0x18110a03080a0809010c030207080d0e120a110607020303010f06080606090a030b0a0f0510030b130807050615041104091a040e010b01020c060702010c03081f0f0302010f0201060303140906 82
    0x14411880020b00b200919000700c05144580d5540000300516030b862802a41a481900d10040c0100000c00440c880341072540c0c080e1642c914100c0c06c4940c001c0329946280f106920880c4403070081180c400c4c0c800403c5400f08107456000c02d83b440078609651600d540701e42c180b20540131300ea050007400d030001070382c81d00c80109880341c01d54010302501d1030a59034146090844010780f041549541024031107100da8066029543c0202503500003104090b10303545801d0382c1e4403805000070400c84002c5940f440031a445101500d003040c0954091328150409100d400074810018603c103000394244449414514503003c152811142c00100c04514900c904244040c501d00a00031a50300034030702000340c141c03000c055024900d130140030b80898a20b01070010410aa500403040024005034246045000080c07003041c065800080c2e03040745540842c0d80020761b00710a0707e036070043c2c03000c1e900010042042d5a44205480513007403090008208460564400800543d04c901c2007000800000801c0040364480d070088 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 222774370 1250 222773120 222773123
    0xf0105031b0708070b0703290406050301020f04051f051c020c1c0f0503010f051012050420090f01050103050615040f03020f0a06050403120905031c0f0318110a03 71
    0x711582e0b50000d2030000016001840d0986854a044d0000348542d8000d114104030010300050f0441d080c2e05080da01d00c3ca04074501100b0380c229071174110020385034400b400030307101c0c507a405241961030314145000d2246480c800007500c3d40701c0c40d20140d99224150030500b211000c141e5920340c2030152280c426080045d1080d4604002c280c45007441c0e0307001c121020020088c1410309992840d4610358501c404858502003802408011101c6440c100702c14038041102c02072020300c5050a1010b103124240400c1115000c4074291011421105000c124800070403034520080d1044880d140c0b5401c16511083d05030380140502410305550380003194030355071820901400711211102c0340d6580c3c3d880c0d03c062a118a40317888200d00a00018840208510380180c2c030348161051595024280ba00c2c64803a20520082600b8070414040345080201d9642c60910510800c1201e007240480d03100c031a814004d20440c04042c045040510f00354440c44407540c4034100c681c2e2150000740c020742c9080b0b007000050580105920 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 222775620 1250 222774370 222774421
    0xa030210031a040204051e0102150f0405071d150a09090c0801050c040b0d05040303020d0207030503070809030310030b0901061d0a0b03030f04031e050102030a0e16050f010503 77
    0x10908402941074000e4400c00800d102c803a140d0022280900041e8000c500a90381d101071850f400c2407002c20b444a44110028051040790342030251104c0070b82010100362020b0300801c0d5843d080105014003080007100514041d800f44403401c6c40c0c45a1380c1e4074860050143d010b4411071a400145559980c04580c001d042d15110401c5045d02c01d240c5000024580e00c500c0005508003000a025404894180d030101c0d40c171000d403a441c01001c04204801004010811418550b00f4002d00c104880244003400d1200c1c403d498081d0ba03070a18030401341002a0050180321305a0041080104a00f018540442102e600c507819485c01d4941c0a14103016100030b03004211903484500781011288400f0346a00d01801044008000052141e010b140c1c032445548050246101c0401040000480c7d0425554000034a4054034402a0f103540c0e8460990380244c0d4050000b60311001d910031003142c00d000354640c21100c08541c40c406417500c0c0c0824a4a51840c1115040c041c011002962440c505198460304100c11b41 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 222776870 1250 222775620 222775639
    0x5060a0b0301091a060c070503300a120f0203070201240b0714012f040f180e0d0f030b04140c16060606170106030e0a08090102030d110702040b0a230a0302 68
    0x16487e6a803000c41c45614070038411084030011146002c803c450040c1c080100404a1820740c64a10019a01241c450010400c1c0c681d00e052070800036202c2c40000e08000c007400b582d82e042c48040242900c00030403116881e40d5024a4260015044401c40400c5070720180c1c5160311101359080c81c0c0000c00c19400800700700d5007800c08d04006059900308502c14083d05404008206500912002c2140514025450461007021042c880c0d03508654007900410540d110114406203580f13450382c00c00e15000482c0c4042448002d154052a4042c00341e401d4031791081d01d041203200d00e02c9903592444800a000f02200200006e0b414a42041c0103401072002074125405000c00c50f81c94000904240d5552148100c1059900020918030b1190003100c0d100515a00203020300d081c0c0d0b848103500703544211444ae0540c4402c02200000d004203006e1044283c048450b05500d606550060105403100305510f0781c410a400c410501890301c1242031b10368902d004140300594200e110020070194410383d00041d522845c0c42 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 222778120 1250 222776870 222776887
    0xf060803030108190c1a0c0312150105160213020c06040c0905160f113c03042d030209090d030f0605030d080a15030c0905060a0b0301091a06 62
    0x114100c0d00780340f04446009100000c003550300001d0f0702c4020039a039020070302000588070f00440c4c4c1e481c40c00845459841c008035103503601d10350351002004280c910641070030030251a001018001c5411400e080842c50200b28000042200201d503100070b11a4402c0c0820790b100085a80c10744030003042000c01c9801754281400c01025614845c411101e04504040c002038000d801020001c0b101002d648a01c205643d900d402030710b2681000d0b8013045548a00c004410703841c45010044284554081030829002e00710054044080a96094501c01c40e441080100400c80400540c00e6603103891100c0c407a41c820600f01c01105014140e80040e5105240e0001d001402102140a15000c2c106440412244138251303500d1060b6290381c818150f2542000c00c0030f40340710740a0301415920107842c24000941c1800e0214a02003e88184c00690381d04410340300600c200c1490303120f404d13000300c4200c4d52036001a01d859414021032105000b021007450305d0791911802c0034030550783c1c000c50312001004941c49e00c412 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 222779370 1250 222778120 222778123
    0x1b0109080408061f030605060312220909050606011101020f040e010509150102070519030f050307170313080703020a020307060e100e03060609040f0b010308030a06050402161101030f0608 82
    0x24001c0d0116030295030b000c1414041c0280009511303010410f001c403a02d031300d140ca80d403004200c02094142c1600840c01c400303c0781c1d44084001c100484d44060a404e402005500005c1030700b0b999000042582d10b0700385040c1c0481c200056496214009107411400b00308450300e050b001e400360050320003c0b100040350204d88202c5e16000141030300c1040e18207442c43e940d1242e1041420141c3c00c04580583c00c0810f0074030050600c44101c2c40b4502444000c543c17150354980d034070146011403420a607001e81011925400f0412405010f50700c001c10340c0c45080c11802d090200d0200d10300040d4004010803000510401014002e200001c103858008090300e0440e581c452018080700d010800d92403160301c2401c4515281c9025030640074800f100035000300016560881804000540076105686052403160104000350f04090502e01852245d404107450f810000c5402043d5140d9400c5584110b006002000243c0e41464400740d0043e0007a001e4840403180b00016402000e040300e8000321242080d1000c41c882c0310 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 222780620 1250 222779370 222779377
    0x10203010f150e0123130801050f090f0c01050a120203070804030e040905030915120412090f03120c2d11060423130e010f051006141b010908 62
    0x30041d035408210b03840e10030212418000188a83d012038a10b120022648002e491100904d001021071a40f4044030030314039081da00c05907800280260745400070803e039540c00c8403c2d541c104200d2401401e00340440480e41d600d41e00d4405505040100100360241b046200da810035188118a0038110b41e03d05000c1c4000f030070100c0840d401da000c83c18061000d070207801c15226003021036400c18040c500300512039082002400300328040340070020080c8000c00310300304c0310301036507028a11601034081e44823034246000c3c00602955003d2404108400000c2001c519152050300442c03400707262090141c21b041c6441a0300d640d00c00e0003900481110510080c0c10f8040032a40029540240a41045007031007608002d160b1103207024a01119030b560103c0002e501070800ca10303d106d10002e0005401910f09c2c00540221620110600150307911498140001000c0c2d10502d80c010100c501c09604060400d40c001d00a0075040902044281d00001c50200500c0340b0341c038044410b1800d00084c0180380c3c25050a072079070740 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 222781870 1250 222780620 222780629
    0x4062703031d09010b0d0504060e0d020a0c0b031905040303060305010c02240705092202030c03011e0602030f1b03040b0a0f0f0c06052d0a0c08102105010203010f 71
    0x2c42000c8850032460f001114504840c082e02caa20b00c1c120700103911001074200a07004990b07954881d07441c0300403c5410701400042000315401440c00321043d041100d2890070a50100c20102001c10a0001034108903030b0f951031000254401050355203552404034000c001c607910103080da500c1c01c106180c03401e0740071072040a100c1140300c807102d102450081c1612007401c1a036040000c02c00c104031707101c040d04021400001d200c8a6502c1c000c01405900c801005990040f0b90524020100100600900000300308083d80010114228a0710034140f0101940d03e104030302d06a1100d10000c03503900c04003040903840003805040c0500b0b0344e803136a076203000403d0030f0f402c09a1214041520300140d4040280314520b6100140459a600c900e00381154071218001c22000e0301c0195003212a00c0301c0600003d06240d41d1011040d1110b851910745000f02841d8205c0b5800141c1c2420802d100050115030074480280e88151b941115103100705000e0342105031001d50035810010110b500100000402c02040d42c0000f0444 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 222783120 1250 222781870 222781907
    0x90106031d0d12140115110f010e030406030f14010e0a090804090203220c0302040c11030a0f02070f060c0215070f030216150f08060a0515030a110403080406270303 72
    0x7404c01e03880702001d0b03440074002d910102c1d04075551202554402d080722280d40e241c040c1614a54140c1e2000d1345c1c2554005001502d441d800042e08000301e03a8940b180444403081c41404100e22400c04000c906201e0040c81a164110040404207a2030311243c0d1000c2c0c04254410200c03596659203141c0c44010750000c40f89200d00040390440300c104e40c90721039800d09245500100006c1c4550443c0d0801004003860690300c400c00500c143c182c050b588041000b403103028000c0d02c1c0d40d121611511002442c01210341c200c0408814458000c001164000180c003101c50b40c102c3c0d00040789080040840544d005030a0050510b02c0084c1180c010305401040640410403c50122400740e5240e0f0050341ca26080c00b15210002100b5070b0170340c10020310880c0641d0300702e10f0003044031100964075000143e0b84004aa06c505007107038000309011890b0a80d2107100b0f00c0300c034500c0f420350400b49980c40d880c1190040380315141c203000e001600c040c5581e041c00b00084000c9141030764002c4460301c908008200c0f00d141c096074000e2 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 222784370 1250 222783120 222783131
    0x605060402040b042c04080702040c020d02030708160503030708040b0106020a200406032415150503070302040e0103060f1a130b06070507030503120a0b090106031d0d12 74
    0x66040c140222002e60380360811182c036103803030201310034203460b242e116008075000a07071640c142190b20981d49030b008a0060341c02680304d00d01401000112030305481801b081d07600a03061000c40d10f401100b0b4a01d815080410161035903050124600900c00b6034034000c0c02030100000304141c150300040c03464003c5009030740d401c0d0141e81394081070b603403105c1045c009002c109590740514001909102840d01c00c08015201046840d981e41e01c010094035091031510240c0c58105035001410f1040c0300382c0003113400e602c5c07489000ca0f10384034500c584906400121002c20500000040969010b501102d0081002c000128030941c4e681c1005401000e01d9610984080c0c10f040318610b00d40c50218071611b03403040003001e1105001c040d03007411005018001c881e0781c204805102110110700f007405083c0081d40603e01031030f0364292100700e0003620f101c0140744414981c90300041c150b171516404251819511a4140011003102448400b201c100c8a00f5080d1894801d099001c100e070356110200e40314000d550701c001d124 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 222785620 1250 222784370 222784381
    0xa03140610140a331d010201140c0a1407060f06060c15020309070806040c0609060503040302030712051b1501060e090c0d02070206191e0518030f010e0a0605 69
    0x407108003041c550140e0f100c44144150100c03600b2219038640001d40c0205204210754220791203031607102c4000082040240316010440000c17a1071200b5040900c020403010400a2400c2e002440191185000590114041c002540246544030540c1d0182820b41e85840c014584840604030002c422b600031410700c1800940d160140300c0621b030459000010320f00300b48404903410001d40000b003041340740d482044400594a0301c1070007040e0040e80592203000e001406c1a00240c41000036901c20407c1140400800004c00e6010043d01c440d99400820400e810100900456450040d050421103590601104c071b9041180020280c1099200040030700c2d250f0790307980303090740e05400e170405141e000b14000001030704908a03000140011840305100504080349070700440c0d0141c0212450f90805c20304040e001076103542120300d0f0b040c140740b01c1d030003054441c05100300103145000c2c6009113010b0402d41065040503a40c180400d01c1d41412032802000000103604585549d0003103100203a884c58600b802245 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 222786870 1250 222785620 222785639
    0x30714150301120615050a1e050a08030a0f0c0b0a09110102010501120f021302031311060703050a2001020a0504050901090903050a1206050907090e0a06080601140a03140610 76
    0x20704941401c0d40f084000840c60300e450000d0514211000704a5aa030b84010800d65500c0d0f8030031014040b0081e0414404598180700c181d4034000c2c4c0c100740c0c0f140030041410003010400001710381c1d54001510f0711810304200c801c3d0980f42841c040304000c01662104080010b010340c680d0000690502461032f050090900d6401a82201c10a0050302030400b00c0c07140c1d42c0003092000407400d40481c8003411006000c4022402d84007207030019144600222102e404a60900804c91035903240c645d0102c400901d05080e031380d0081d0680c419154490240003001c4980060503007103800030000d14100d000207655841d580180140503070300c24019507200301008000403440c06500d210720011340f5030603151149001304440081d0b860700611003d25500d40e032103100115045c1c44652030300340244d040e51644407000e820f011014010325070043c1a004c0701842e1030303820082480b001540a04480041951f50794519821010cc1d400710015000503001c00065280e030035000200040041c881e4240c040b4846000d070300c07601403c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 222788120 1250 222786870 222786877
    0x30411040e0607030c050405040903022a0f1e04110c070807052407050a0302010c1403060a03060519021206090106020d0f0302090a090c180f031e080903071415 70
    0x401c86a401040014078407070281e4004070005800e41021828981d403100018203880c0c103640b0440040e00824002954610710b02030083c1840c940922250003000c540307011030010824002181d00c03c031031006400c817064410051100e80304101510078452400c21269020403584a5070030400d0b14480c17900c0020f14060045030071000da80b0000d101121920b20f02010040401c045940031800300310812038480068000c00c54804407603c642c0012234040031030b01010784030361440d40980188210410801256a4880d030182c42a2035220900282684031801c414440058013140700c1d440d94400244101d030403c400159910a000449000b03009a0702c0d480100c0c2c90300c01d800110740214502011042c0d04174042d0300a0900884040c00c050714040da00d009c0c01040c1c4103207681d080e0201d00d600817104a0003400261a4001e003c03d000d0040381546599288440c5260b14000c03c400c00c20302d1018030040001c080e04540e0007080003011502d078161034040200114594180040c1b0401201800d0a41d020000702034 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 222789370 1250 222788120 222788141
    0x3070f29040221060a0905120a090f0f050102191b08030c0d0309020303030112081608030a0c030c02190f06060b04060f030b18090f0303010b040303091403030a110705100503041104 79
    0x60b161545510007044090701002000326050b020b0f20741015054008e42c0b0160003813030800e42d626800c2524041c0501d201e500d07684c20042000701100c0e02400741c0d03600010444610201d18208610244040c2490050082e20b0300d034400c1d40d040e59010024200d200040078200380e001403800d4502200341c07101c040d800c0390340164000b5010f070018401040310842c95080100214020340690b40340007402c4c044125080c000c1c9000305e400850110610444070308070b119440711650541002c025400d082000a0360342c050f11041d040341c104030140d801e0200030781030300e091550907480113090107019203c2c8014140e68201e401440000703801c081d001da49691090060390802100030b00416402d0011046603444803000a185000500c5a010211100802080114004c10320940c40c15201c0d400d524000b000c102c80c644c01b9065054052050050582d804000c481e00d070602424a0701052200c080030300e00307018141d4001548018850150011550031800442c0308911615a002101c3c0300f0008000440320704004 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 222790620 1250 222789370 222789373
    0x10906180c0509090109080d050403081605030a0b150a030507141206121f0e0d09030c0905190f050103060b1804080a0201020403051c02150903070f29040221 69
    0x5003000b890070040d03401d9810501d103c001003940754454584405c80d6120041c0c01240035500c0d4200418154030440c601d40102e40325120050206118100410501016000b080c217186c1c1c9502450f01e5170303601c03000d4120408010301c01940301e01030a0b40241c0148000c450541c040b410703682c9a0244507640808641c5400c15900b035521140d210030342448200c08425036018024882c0e08413034615034080d811100c0c00c0c00303100780010510341e800110a506003910204080240071050310144001000221000b080e14180c5000052039903c4801a03a100a042403802000d517203400140b03c001e8409800c00f50582e40194000d00c0b0604d41e80c030511260109484d041c51f048030f079880220b000121180018050001184009404c00781c4a4403041c3c10300da6481410400081d8450f802d550958040c00030055040001085c0585032500341e40e12501d900ca00080100107103550403480b4104a10a51090312524800721a2002070540e103c41c0750208606440c260712900310280041000411000212a240b07801da0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 222791870 1250 222790620 222790643
    0xf050a050f130905090d23040e0601020a020d0303050702060105011b0f061d0109050f0106060f2601080d030e030903070302010806040b04090305031801110f0714060901090618 77
    0x48074090398000500010070009180c82c0081c084800b4020b09009074040c802600f0120080c030009409411191009060b00404c10007803600b005030300054908499202c480b01003103550381c02c0100e081c04410403000f54130641e01d0603c0c03000d03d64554803079442118203070201ca200b40d803524019a4a440e042b000010129022903c00000518018600c1d170145c2c400d0b43c0c0820508410302e41c065260344405d0050b0341d0390390348105d20814001300700150b42c0c40c200c8601c0204a60350030103000a000104e0302c61440240701141a110000250200c10b55203810b1142260260701c1d40c40c1c060081d00c9040000070800000c1c00c207582110304210100c01c54200c008001c005010480c9183c1c01503480b0800140116841035035050302c02420340340c1d4065452098400c0c0e60362641e034501030b59495200b002c9200c00300724983c90040c2c00500c08509100f100e0200f1500b100c140e4a942d00d80c07405440c41941d002c80041c45e0301408003402000b0205420000460b80304503828440c0960440c8080200010900060600450344 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 222793120 1250 222791870 222791887
    0x15030c1201330c0c1d06060909010506031503100c1106160c1106030f040b0c0f0d05040809040c090626010501110f01020310090c0509031c0306120501020301060f050a05 74
    0x64080b180038405810510260300702a258035a64500c0d980c02050100200c00f00d220080c10717801d5006501501c01c5802906103181040403445014050003401c1c080c1c0d100001142d482c2204100c00c1ca01050300408440039482014007040190030303028424004103500d8504480b42078004a0001c1c1b04614241101c0a04038501c2821610450030240580b051a400b40b51840c130f5454007030007076100741e01e9526100c41030700301403410a200c008014244061488184081482401440219030704003e040b03102160a8807030b410881071030f20401e40a00c1e0720a203030203148180d032a0030944080071200e0989584500711072440d4082d211242048041e0a1000341d140140940e6004001c41c031f400751140307002c0300e484401d40b440050881c0d00039614074101c40b008410420406000340036064008000c0d1808905004824010982e00c0110b502c90040404180c0301084400b03200341e00150082242034020381d40e0f80c489003041e078000e50081c00348400266140040e40076050085e42104c41d40c40081d03491a10b0b00f140c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 222794370 1250 222793120 222793199
    0x30f0b030c10050f030a200c1b0f03030309010617030a0c022115010503161202010806060d0f0e0d0e0603040303020705100f0f06080c0f06030615030c1201 68
    0x520142e0428403205000c807412121424029500c41c0b017079208002400e10080c07800c561485080102954406010808000305450100c0c8004429100618042070f0106c00400203030341140d0174003099018440441080350802e015080701045031070701d003003e1000406640c440303a228420f100054001c101c0d1280108010f060180060045800160003c1030928500c00a2410b1100e0071003005100903800c40140703d5460305100700d82c000d004090304220854902102c0c0b201c4840c2800c000b0b414090240c00244841c0ca8807400c0f00c0c01a00d09003801c000c4840c4d9000400010f11800200310101e01c80d10f5640714040707000d244901d48602d030003402c0e14119a200d503001c0300650310030f02c41150b6600a100c030801c000c0c8414045c3c41c10711144190003182c42880c0d04005001c69070703564090380b031580c408075030386006032540e4000380c100307000540d01c0c2541d070358410000c80c0000005d4000204860744c000300304504200707150302800321400d20a40c4260240d9079101a030302c941110074203a40c486031101e1071090000c0308 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 222795620 1250 222794370 222794389
    0x204050f06160204050906190c120c0c080301060906120209010e0d06020c0a1a09060105090a0b06071707200603070f0e09010f08010c0810050103051308041401030f0b030c 75
    0x80da500e190002c65880d4013080c1a0350b016501840c580d808201800b481e2003c68101a2000c1160a810418800000001498006400b811010069444040c00a064440c40400d800349800101180c1c1d296560700c80100070050360310503000016101002d5444400e424003c40381d18210596500002d2945d030400c110301e540420600b103480c10382c20008503620400600074107001c2401101c000400c03000c4519210700c8000c00038540360700e0360080d9005010030360343c001d01c860b0442610140040c10125080c0401c030f0134070884901a04000c2444403100d0782c00d04d0140141281842055441880e50314006250116503201540b00d6204a0510014103610b00c900850320b01c8564910703200c08607034000e401080048030281c01490988045610900851500340100c0825100603c1d05041c00c1c034007252003081d0301c042c9024680c10152a0710110f000040c074801c06651403038011590541d110f41d0b445140e10051400c2540c24007080c10103203c02c248092510482141800260140801641d1182080100341c07 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 222796870 1250 222795620 222795637
    0x30c0304090507050d0905010c080601020a0c15020f030d0b0f0a030521041502060604270228150305010b0a0e0d1e0c03020a0f05060f030c0f18010e01030204050f06 72
    0x40705000309151807005d40910f6049034060350000030b1807007141500600c0000c00804003410355107c0425000010390240c8900f04452070001040c0383c0c1c45c40d45008a00b02448101507507218400030a0703030303021480b455000d0315900138100c41e0880b0345500501400180c0304c0d9840090a070340c00003092035030f600c0344020b400d4000000c2441140c0c0781540382c820311800c1042d10091600140d111724200135a03800c2c68403c01c20400290b802d424400941c112540c0c8542005400082c01107616455900c03989200c0101840851842d19000c4812034540c500000074042d064495800a41032000000c1c0d4900d8442c100d44202d50035541d00c801128a603130901800100150085030078034402401c1c08444049440100741d91407084036031120542c618010010006120b0f040641c0e503620b84101041aa5580000c55030190340d126000d5450f0340e520b98400c4201d008200940324064800224820000e0000b15000701445003602d4000e81c0b090340c18011000c03801a4011180c0014040003801d5652800d90003511108 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 222798120 1250 222796870 222796877
    0x120304060b1005090a05031b0613080d020a05060c040f03120e090709090b030c18041110030608010e06160c11270f040b010e0915090c0111030c0304090507 68
    0x116000d030082042c2000d0b80841c1ca002410200b0b007003500d413034110201002803000314001c01e41c1c826000c03036511081c00001001c0781b240790002485c0c02420800768100c1c004007440c0341036500390856560f010f0344071310300740e0b204480c4da01802d40000e00d4001a10152029645210404440303035095036100b00003078410642c51014003103042c1029400b6034032603110314401c500c15075403404858034240c050001e503842010024405d4125040f0300809454240c02030602c1d001818407507000340c850381401e402d00107803040d03402c0d0450b100414140051342c060b0404811580c3d480020000035107030803d81503c610b015220141c01c5031420440b2202e080c49144504021b6014040324141740e440000042c2d501056481000d1030801c1e86c03425140100440c0700d1080e44203a060600808900d07040d80c1e00003242d8814002c00d400d0402c840003003910303981c0802083c02c0c10f0b070602590390047c0c00c00b14a03007540c07001c0ca400c4d414000380310800045030640c0b011094070307042605040118103050800350450f02030900100030b0000c2 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 222799370 1250 222798120 222798131
    0x1c020a08270615030d0201060503060718080f0d110607020a060c0e1f0801050d0809130204271808180303070c090c0207091103133807030c0212030406 66
    0x368042880361500842c010f01003150805001400e00d820500581c480000396454200104640c0d1404144190b1241140c0b80c44c00018a03090880c1008600700e802c50640782c46003050030340d040c01c4001280745030016192680080b000c2c586004540c2c48008442200050304109089c40005419030041c64020085081a0604030003c1000c100100c1790000704002c4503030445403a4854a03084452503004d800c0a580e020404170003038980590310310804c1c0702280110724081d40d913048034040d9816100035241e1401c0600380e82e011407140b64140502e80803121016450301801c51506210104080360599000301c995042a184210814582042c059101e0b007500040100c0400140c41c0f00d0340c0c501600c0c59080000e0418041d6400a103041100d81015080a00c1e00e4116488065202c05a0381d00c949200c005000c0d04219140c02c0262131000218454000302c4503458000d03581d03582201444032120360301000c0340c1c2c0e03075000408c500340d82e01403403144003680058240b006402020301c002c503801805044081034 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 222800620 1250 222799370 222799441
    0x140a0315050603190b040c14090411130f02130f06021f060f0303050d0b010305071d0a030b1602100203060603040f0f0803151c0305040902070609060f021c020a08 71
    0x10b0704c8141c0c420407120f050500040200300400b16202001401e0800c0e01c040d0100510300124801040c0504060540c4070218008100c5035909000f00c0c040605000c8244042c0000d45894406900480c85000c110600417001081160011008200300c0703034284e000300b9503100c018280840820070804800c0180351035072004a61b09500e0f5811800552103640c4603982e0f80a4010000c0490360038401c110704143c280300a002d001d59205007043d4268081c504500c81300a20200001e09141c0a6400100f06c0d10340d000c100202824000c0800411801c10b4003642e074000c50040c151801c91008607009070f4002c50610110f400304072141d1000045071b20408080100d11810b031501c01c015041103644144440d0340c09031441042c14803203024202d400c00d50007811100c0c811554064441e02443c054440c08541c0405c1d80f400b840425089203102c26080b130020410442d0b8011180060352080c501c0d414a4101c0200c0b40001325140d00c2142d41404003030713940320341030b882d00464403040341941d01c01c0070300c00c00c003040c00e40e030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 222801870 1250 222800620 222800653
    0x181e030209010806040b131104050a020c0706110c0a0f09020c150a060906051210050631060b040b0a0f2c010206010506180609030a050d0207140a0315050603 69
    0xb8082c0041000800311442c06141146000100804503000003950440400000f4862103050418800442e0003050640e102032580e0001d014802e00c0c0086445141c2c0d00040403500302e0880d20450303035180c041d100b085030700e5002d101120419102c1c1a01929010703c0800c41d0940c1c5501030401280c468050b6003181420359145503000da003e59581c84101d07903e20f0b042040e0106481400001c01003522001c0410251185480d1078011312444444920786580004c0c00b1940c4083d148031510f44c00e05e400701406100550381000d50501e80d0860f2104c6450700303030080f4120754007000741d6003140d0144580e03520782812144204d0321141400040000d21444880180c035840d141501182c1c002c54080550009400004c00241707082d806a215a003d89410420b002500c8402d21287e04940c1e800c1d510319a840c085c020100c0d20f0180a2078018010f401508800d0041c41e40c089500401c5441642c04a80d11109440400c031440405100c0108400c40c0880064990181c50f008103a01a200a0958124580031103851 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 222803120 1250 222801870 222801889
    0x92a0d08070c140a030203100522200102120d020705011103090309040f1a1e060c0f01050601031107030c020a030210050a120510030f080c010204060509040c181e0302 73
    0x200d550041a400c140410104020000380f400c0084440024107469900840d0302c8985810002c0d451a403036000045000301c4030351403110b84c0203c00250326000344460800c086c0301c809213440d100b05894581d125540300e40c0f0029035943c1010380d010b5400d15002c0f0110040340290700c240c2003207500395240c2c550a00107510030400b8604c51507500010b147e40c0c00c840d10800003150040011003c1705032501d0703041ca841c1c0798051450381580f1815610748441d0f020000341743c8803a143c0c4a2460340d11072400a210b246c08007020501540ba511a607000b07020300d80302d050040d400d4400c0b8402030303c9048800e1000b80c010a100301104030101d0b0010340500e00e115201d03000300d03105005558140022840000b080c0800e0303640450301d411006182c1000700801c1c1006104681c100002d4800076080e40c400600c050300b0b110582d0100c80d001030b2010b000310b540780d135640310160490b007002101e40c0c440c83c074140c16842c000d4007440d9030078050030388441c0fa900c4007401d10783c8050300404541081d041070a60703003002000613150140705 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 222804370 1250 222803120 222803123
    0x9150611160303120509060c0313082206020d050715050c07060608012c0316020102030c011a0a05040e12030a020c0109080d0e0d050f0a1b1a092a0d0807 67
    0x144140c00704404040e13001d80714064460141c917880341c0200700c050300002c000d40e50480452440123030403941901f4482d80d140a82044003c0342c81081122210454101000c6000c031a0580c090b10814807032200c00751014000c6010141c0002000d400d0002005032503840103130300150070810581041401d48506003150101d03040a140d0740c2d969820360f0391001c079248801140c2c503103c1c418200006c2d81451180d4480c0210030b030329902c84210407000e108580c001d1003582c820a240c40e000700300340300c8034032420800400e88a100340c0c0500b080c2080481d541c07c060080240100032000108154022aa9028412f510081620404680c00c0c402071405040a02075983e05034015440c8540f40c4610030002030454a0307040c80c011b02c503400030080e0812039402000b641c1c0125901100c031615040c1c01c640903201547c00000d122440a080120b5404001554206c600c0f12082010381e0401079590f03020099403100560041d440201171070010802c00d561003030500c03001c007001131b20130111940719940c0c01d005900300080 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 222805620 1250 222804370 222804377
    0x312120e03071b080c0102070e04081612030f1a09060a050312130506130303050304031205070c0b220b06130e071701050f0402060d09200a09150611160303 68
    0x4140d551010911a400502010400b1301905c2490340000b030b40d10001e17407041868042c0028009018421f18400355400390b14401805800b81e106803030b1400e071304003d010314400881d140c01e000e045c01e954203125030314000b00c010f0b1016443ca440c40b820403e21281c014030495002c030000301c01140946040c09092071000d10090b100c0d407a082c1116011022112076005607000303000601c50540c000c0780180f0140708032505424082e95070345030360408480b40e420b0304003402c104a00709000d01460540c018440340499008402e10500c503190f618403001c003480300e201003980031204e446011004c01c11007100c946d0010801080c50008020100d80700c015900c625056009035009103c0806c030000c0d030240000b40042642000f081a0300c0c0082c1251500100900b0103070090782e020645880361100c0d54003100e1807903008141451002c1c1950400502d140820302030314019100460f0008803000c480c012410307001a2090f1101005082920490b030b44440c0c40c407105028440e0784c0207580b00c0e0f042d5403824400b45000f5507 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 222806870 1250 222805620 222805643
    0x60e0f240f0d05060d020a0b030a0603021c06150302030d0f0225170106240210290603010e04240606020303010f06050a0905010f02011415090903040312120e0307 71
    0x80d00b02007200c1c0014202d034029580848100016038407841c012058607141c100c1c06480791129082a0001e0540c1e0300025084a01d030507041d9031801c0a2140d510050744180e10074841c507807882041c0d0090740042e2100a405502c03032804100384500640c10024068186d20499013100111a81d003451000030a00284040092001c140700119003004400740c1d00c80410028494145000041a13405441050052459040e49030448880d0310a00038025041d090b04424030041500c11106d2184415522006a020f40010303c600704a0902c1030070740f03049031a264440e036070036600c07610f510850703440c01250030110b510800c003210441d80e2944200300244c29668006c0d40c0305d41c1042e4058002c00f0060300801c00b0302405000b6924045c0d4882c40380c04c1a54801e107003480d000c10b42104203a000d4001142007031949500c0008010b080c1d465002d100c6d10410303040340d448007941c2f5000340007074a80c4914000076004030340c030f00400f00405008000d000c14010702c0c0b03400041e000700741402c02400c68010300c0e41111400d8048 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 222808120 1250 222806870 222806887
    0x12090605010f0602030f090906010e100f1112040302130204050a080c090601031b0f020115081b0a050a0b03040503040308030a15090e1023100e01060e0f240f 69
    0x2041c0c2d50141c0118002146003150310070034030070640600300300c0900c1500402d000030503030307441081c490a05100240a0b100c0c48280c1400280044400114050015450b50b1441c030b06000c0c0000c1035201d40c40c200705400e1410b815074092103503020035940380c0715900ba020440000c8980b0380b0051400180002c0c00608412041d1400b0012901000f0781030504050501caa69069152030f0300e945132400a00f4100441084c400f031000341d01401560b110030066096070500011040400326a42d030140c610200d0300c40441d8140d000f0084810014001c04e50061121142400000019801503800c5801281201c0c00d25075640d9518801e6841216000041900e956030f0f091450654021040588407900c0c0500c001c5d0045042c0c20390383d011503826150f4142d160a400320442c46c140000c074420f411851410038083c130349185000c40070a214400d0b08840c000701000007034001d101e4200111642d100500101d517010740181000941e000b5130301b150301a5049441c16207070380c2e0510001054108607803400c03591142c254 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 222809370 1250 222808120 222808139
    0x41d0709110f090f03101b08181c0c08160605130201080c0d06031a1014030705010c060b0d03030e0f03070218090a0503070b0a0e01020720011209060501 67
    0x24900228000e06001c840c07400704100083d0f0f00c6103001600c0060707054007018002450150f070604030340c1c40307540303442d41140421251541000701c04c4c929494030f002d5622040100c843c456001c030300d001640c0c0c002020010121404402c884c03144036440c0b40c00b1010a54580b10101d0a6120300c040181d88032400030322340204140c60184543c8069405141c00e00541c1c5a0000f07007480c02e005140f80203030440000c141da41c1c0c25140c2c0c014009141c02c6040790030010700c8850701a150180c140c422070340c8201500c2e0000307424540c811101e625650041c1c064848140751000540e00d08260000854105468080c0365010b074442c2c019020000780a039401250100b0001951401c191000f1ba84810582041201034003607143c202402c00c440b14802d142558a5849464081c00e0114015000300113010000320017007400441800e40740142361041003041a8040e5090a600703d100740c650081c443e811100b0340c0b400c025100001c8198102060406800c40343d003e510140455a0790b000071150b503581c650060240c00c0d079 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 222810620 1250 222809370 222809381
    0x30f0406120212152d1c1e02010302121f050604030804051c051f050f01030201120f0605030708150601030506010804080703031d06040615060504060e041d0709 70
    0xd0300c070304510342048459003d0240c02c006205004900d8451900803154680c00c0800c0a14017001100224260900030018504040c5d50806442103843e80c180381c5100d102e00804507180c41d44101c483d00d1800c5441041c4541c521511416414140d00348007150392907481d19a4a44100d18100c4c28201c201007034185080c011407240c1000c0d004038800d000030720002e11603d044600ba103000310344501d41c0201c0624030000c90744070343c02c0c010442c7c09070300c10703607031241e0302403001c5181d441e802e46000e02c80740e0380d4810f851071141170074400680003400840030080c140340355901590159844080202d00c454075140441d01d032801c154800e0555a0041810707480038212000b0180d0886403d00c0c080c809410702400003000100c000d04050280000024000300f09070017076104641095203c0340200001045200407600e540c000c0ba81610454244152205d00440c1d0b01560001e0f10030b652122810903003400070468203400501003594006a9640c0c40111a00d50040d1200c00c6c0c52410005007805800c0842c507006444 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 222811870 1250 222810620 222810647
    0x50c0a08010c090e0a0f1e0f1b050a120606020d12050601090b0d02190c02030c031518070305030d02071a010312080408070605040605100608040515070908030f0406 72
    0x2450482c80d006180c0d401034044003141c4034941001c08984403080307100010940903100404d05032800113401d4981c0c04050014103c0302c40c400302005001d400a80440035910410054138041c43c117400c42d0f400769800f40025081c04100391504e1070480d07107081c05000c100e610b5a00880c0143e03116944655200f81d01c0840b030900c19510340018010b0741030560010303001810074042d059540001060380e10010100340c1c107452041d881c40c0c10281c100c1d42d002c071000d48104034000003070303020b801408003080c05400d0014045114140c140d880020b5070361410700c09250110081a8020780307009042c0c3c008046042000546400c0461040050383d505240c90840c41303181128000003815616a00104003044050304440380c070100c24180344603d85c0e182e207840c050602c2003a0006260f6450101030100b03000442e4000340c4a1b0084a5442c0c50781602c944041d20303901030445008001d075110302500c10b9052142d403031140c1c0000140c01c00b60320041c0ca44015509507004605240c00c0c004010608000c030550040c46a510007 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 222813120 1250 222811870 222811873
    0x1218060c02030301140402161202033105040b03060105040e01090804080c0102010b0909100203041a07030603030206010501170a0c0c120507020307050906030a1202070504020f1908060d121803050c0a08 88
    0x442102c81c00d40210094080c00340c90a91034049d01c0c20543d00038000c580307280c0e54080007040d03081e0014548142c05110080862040441c025000c44d40d070600b803158005941d401030042c0880e07031810042102420031f00b4110b210554030340307a1710400145102c0113880580509800303130031510400800242100c44806899100d0340c43d1328180548081c010a074000054404174002d030717899641c0d082c0200e0600c1e40000c0700364090340040c10001c6842d819401501502e120b9400e45040740d0342d800044600810303024125906202d264007180e8850b085a00c84495140c4c942441f5040317500f692100691181c100c46c0020101b400000c1307000440c82c1c180990409028203d90b08109400d08c0d5002c1b0341da0300c40d51000104900030803200700e43d0303036802001048024000180107654404542d40301c2040303900700c0f60030743d000d008110f02d020340c40c0390080782100c2c8500401b5003488904003403901d801d800c42c8a45c2006605101c46094030840c4402c1c41046040a90b000304000e2912402c204144030f2410a158130004d1035 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 222814370 1250 222813120 222813127
    0xb21130209040b040629010305070f0e0f030f030f2d0913060b0d0c0e090c1c2004170c060a030b06040b0705070512010b011218060c02030301140402 65
    0x5a9610304032039005030f00506031040036580c51610f10018050103c0444400040083c1c18115130b100c5c00d410152070000ba6401d116607217403008107669080c01103180401155400c2c40c04846400c2c2001140c0b11203a00078110344500c003141c81c401b819a44610503046503c407001500b80b0100340c42140102d0003818510505258541ca80705100c254011110307124851550301c0d840007960205900071002500c103d910441d81d940c2c407500304000911050780c036500850012080400c0380c0c23a01000240c8031300070006840d0300d000300640c481280d610003d0041030b0102d0307450040c01a2160906500b002c0c080d043c003465a591400c3c00c584000d4000c0c3c048100c1010741c04000404250384484054410150090a0119860001c0b40c0018814020754202810300c0c240450418180303d4005805003c072101030320312810790411b040f819800d075203410150501007441c0005800c440c030200e40c4103171246004843c410340e601c4888c1d80c502041d1001c1e4164030005a001100501100c00c0300b01139544507074401c4504516 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 222815620 1250 222814370 222814373
    0xc1e071703040501020702030f010c090e040c1502120d0b13090c0902031513060303030b0118031e0212060601030b0103020405030606060a031b03050907050114030609100b2113 77
    0x2040a03108448010032022010800304030f070035010340740c0580e8001c0540316851802100ca42c000d0150140c418001034240d080080e0040040d440c0d1801f6680141c00350010381d08004800c0c01d0704e810010000210b1159101c61520700242074050840380800c0d860200e041c030036003000c1102119000108502451800120900003111130400200b02c0300a041d0258a0380e403500141c68032000404441a013000300b00c04040c1000410f517202e241034034880c0d00c0c100103c4240000454100c0010b543d0744500ea014007000b4030106120404404c1590f04510b07403c01c0d1404030340c0c0411001d40d0400801c011561041d02401499078060241800742d4000b0302c0c08605142c07820340001e94030400640b6490290314005456011b10307210b1b4110140803c100c80000c000e00d100060024000d04040743c031240c05004800021415600c00c03100e000da0500f2107031034035095459890800203041d0020b00083e205014880d0005800307141000642005602e140c0c1c040344003481d203001d11900308001004d01e812440400d03102030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 222816870 1250 222815620 222815633
    0x2704051b09040902150406050c01060b09090f221202060c0c031608130b0403030306050301141f051314061206010e040c0503070306020306010f08010302030d0e01090e0c1e07 76
    0x807254602180e020604040c0e60021a03500d1000c139410b49050035001402048440d080300c0184007481c1a400208661550360302e0b45962401102d418951056540d40411000c440b201d003841d400c000b41d0315080c0c070244045000c1b0303030054102100440e505640c0c07008810a4907014860036920010708009185011813942c1113549910651181610070300800230200c046c4094441520100c07990b43c0c3c807550710f0325200c110460717085d007151000f100005d0030b1800c0803580e0704040c095540040e00080c01000c050700e07040300d01140c4200b00404042c860142c50030000b1075a82d00d208029640000c04000689001d4801d0f0b141d48940000f000d05020341c4004c001581a0900061228111112f031144242c1645561420341007111090713100540c18400c0350f20210502c80964011b6002e03040980f10103902d1044140287c0c1c0d012000d110296150300071100c4002003e010382600c00700100c051608040b540d071140e6000200c504103443d070818496000c100307504a405078543e42c06d4100c038100081401c1140e944d9808 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 222818120 1250 222816870 222816877
    0x1e16150603081e0c061e07030b130b01111b040e030c0307111306030303051618050411130306090c0f0806270d0804020118120f082704051b 61
    0x76820558800705203442d01d6214040e00c0080b0004010f86030241021110154003a1b08146141682c0b0080c4000c5038203036000e03100d8501c120501800203850ba00c4030041040041c081c2c010210b050045400d90b0301c000f1001809503184000c081901c08400d0700300709040c041280d803006200380c15035008206002403460000180c844080c0c4c0007600b080c1c0c008800012613103480411220344203550401901108040d0035800041c400e940044000c0e210505042e005c6440441b040c2c2c201410235003508003400b090170300c2d070403040545206450551400322165011141d85090798401d0320301c15034502c03004041040b42c02c0764070010440141c0904102e814000520f0700c0303000c080c0c080907c0c800718007115103e030082d4055004048003010309a90410741049000b5082d402c017107070100c1c0007402900c9007d1031004c000c40400255031400d03c05000424180da180b400c0c1004200d01500d05200c14041c250800100792019000c002080d15030320301600601c0240419078401909101700600115001c10701c41140f4000d5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 222819370 1250 222818120 222818137
    0x80f0a06061704030e090103050105090613030c0312020906041205150f0f070c020409030203030604240603020f190f030f09020f0105030a060e01080706110a08030c1e1615060308 78
    0x1008402d403200d141c1505c64601c2c01ca807180d0016170000000051103c10360086205001c16400d8031066030758903440d0b8821012002d00140824100d5003581c010034840e40c0b80c40c0000420200c01450142d000c00054590381003544418403583e441c1d50054200602480800d120b425141c0325103140d07040c84065007541d4840140201007500d80100040c003568442c14002801036000303007040010320364600f002912a0f204407610390007141003501c0291108541007255150035502213042071a80d0030321400b00c019500541030440011014044030124180e40c280111448405440e00b0000507103034500501642c01603400181020314240341080561100b09020144100c03d203040d56070b9640390241c403001810250400300342e01c15400300214000701c0025010040d100315484588007045040403843d0b9480034100001e041c1d00090011075071003e8127802030a01d104802141e01203002d50b010305201aa0030040c0c04003024640c030100780c018050399005101c20310005081c20710200d400c6440d607881300d1041c11032 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 222820620 1250 222819370 222819407
    0x30c0603131403040902070803160206010605031503030d1805100e1c030e060f06030f3408010f0209011d010804080f040302030703150c050c1f020903010903080f0a0606 74
    0x400b103100000c1402150064098481d0440d00d07078402d41080b850341c1d0001c40300f11024281c0c1c601c1c410b480c540006840c03030484400c1d0b42c60a2031940c03144661a4122409003150307415110600c05059500414083c1504400c41030a10344102851420010718040390742d510090418070300204c000e042a001b0808002c10120341032102c0070306100c601d080300140301411040c0740798061a0240001841d0301501540290001c4084981e104017000c810703078659207083c0c0c03c240180c1d02c5003800c1910745541d40d8010380c01c49400981c100040d917074406aa0039039601c142008000c03036000801140d25a0001c0150b44841c1140b10400c01c0d2043ea440043d149607409080904626008900e08403060719510032507015540c0a400d84003440d0707491800342d01c2503060a581d280c10301e0900c1c40340f81c8018820401d41d10f10002d0340004045d03070200b40741d006041c020321590312001c80b070f020801d160031501c0034096131341a244250784125562070721403d10314204001500f903144207420f2240801802da4422030301505d01040c800c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 222821870 1250 222820620 222820643
    0x5040b07021009031b080c040e100911060409050907060e0108040b06040b120601080d020c0a120f170703021608030409050c070b0f04260d0515030714030c060313 71
    0x40c03c0d10315402d01e0b40000d0171444401456281d0340c07001490402124005421100010864006c00c4107071460f20682c040341d40d000302011821100603070011180c4030f0040d020048110080e0380841c4003644180c100c102c0c020b481c0c00c00e110001c5000c02c01d00009044610b010070f4011045c40c002404a080074002505070710003400400c00b42d9a03240e12413070074030800815600c01c44503540720191f1200300920a4440c1c078000d07101030010050001c1403071890030380001c00c4d804120f424100d0103805203080103810b446400c40404c0440002e8a2002c0c82040b40041d441520b8030f8031454a0024a072007000b051440d29180000c4081010010000c2960169408200c01060310707668082c002081c2d0240c600d02a00041d211802d00c1444200e0b10407a03030155000e900e19500040c8005688100401d011001003d014010480d0810303454860740425042400300800c0c0303450743d1103580000d00d131100507040030f401d81e010b1b48500c02c4945801c0182c00f071070030029952281145041407400c41b801355014400380180060f403 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 222823120 1250 222821870 222821899
    0x106050903070f0609090f02160b090f030d0501050906100f110a02030d0c020a140a0512010b0a06051b0106080307060903170106170a0e0a140109080d020c070605040b0702 75
    0x3070081c18050180d590901c3c0d1030a5035040024004a01c40c0300b2091841c0c6002c41002400d82c0713600032201000a00404910000f240c0c0d40c4c2c181c04e45100422194140c011a0003e5283c1a02400240743e00d005803c008101c075410300b8101300c0c400e00c010300031750300c61250b0000d68920f16030003002e940444d14140c200b00e400241e086620342e0925804880c000d42c0360003004180c240c596001001042464026594458490b44410059030049880740700c103540002e0311030003001145003540208004841010000c6113040407040810782071802c5070032000c040740c40884e414102c0c41c2d03041e5180743c0040d9494002d0040d545000720491302c0c0d1042c1e9201809650301c0d910508203142c0034204403000000a41010111981c1d5584000c10b4004405032440d00a02d48d8000b20b100001c65000308401015010060301c0c000d101ca50f1000a500382440a0510300d541740c1083d503021072505c2c0068a00140b01ca10050782d83c1401c980128241802030304002d0a20405220502541c1c1010083c0c404455050340d02d0309084040 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 222824370 1250 222823120 222823123
    0x60b0a080a050c0403020301110c1e0616030b041803120b0a1203030212010803030915010303081f080312040b01050a031e0305091509041103060607110d020607050a050d05030606030106050903 84
    0xc1707800c0a5015820110b80f51203100c03e4038000c2181d50204400e452403222650356810300c0300d03003000048016501c02c0000c20144592100c0094038803580b4200050354505500206050396206080388029143c200c80c010141500a0440c8203a081c0244041040501090024940c144180103403001e40190a10a008042c000d030f04880c010203010880706030942e55010b074030703503240d0088030301046032700540c54480c0e200e10f001c46005042c0e96064584000c5581c1d0303402c12003214440c001d05980103400c2c130742c4000f480d210244000d028440100780e079140185030500f045000c2d0201a4000340c0160720001d41000800c01c120303102da10407210b00311052150300f2981000c468901521040c6a4405607034149070400f2032a00f002400440130585040c441002c0030400528107000c110b482c60f420031400c00000000906a0b140800003507001001d1541440503078000c121705030030034202160b071030340180028428003208002881101c04646001886e41c500314003c40c01e50301041c0f1840c0240040841d40d003105640 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 222825620 1250 222824370 222824377
    0x20117060a0b090d0b010f080f03040308030604200d09020a05030607050a26340906030902180f190e03120a091a0709060504080703020f01091a0d060b0a080a050c 71
    0x204040340c4a400d58481754502030030b50140c456400d452007109c00d81c03100c07500040181c03400c803500000401d0031540c1e50400d0001400c0752171032154080045007e4803510440c514041c11480e40301900c0010660301c14418444c400020b5040740744254071080c20061150760200481d0083e0368207107006105c801409948000001f0960358910489141c5010405140f036004822407496403a030909401d400d2030120203a0507a491000c1540c0002c69140e003c1c040e40e4000c1e00903801d45071000d04070b9945644004a001030444003500c5200d45940c2c01d506105412039009942584400325800c2005a2000c4041540c0e4078407541e4a413980d160388070400543e50317100a50018403180c2e00820000d24003c5110680080d0381022103420011644040c03001c105103202c1c4080d40c00781d80070310000748007160550f02046500440003031420f040041885010886103c2c7c2d03d419130035a045011a5619914070b000e905090b21030581207110071000a000103001c66600070b90458100308805400903843d15070405400d182d20 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 222826870 1250 222825620 222825623
    0x90e061527060414091510080717070503030310090504170c0a02030d0f14030a1b0323040818040609110408010606110a17040f06020109020117060a0b090d 68
    0x1444200880701e000c1207140800d1007440100c604004011a000240310703548802e030b8005007903900684000403c01c20f035102c034540045036182c46a207029581e03400e96140070707500d400c0354040003203c80080c3d00180d002c02020340648000c0b0301075070075442c02d00104140301410344a481c0049031a00003060a0004804030f90079441c03007411000b40e413000d806180c19a20540800c00700d00a10402d0b102c100c80c58400e003c40d0200c0500f0755603a18400050405440036900042d000300303500d0f55601a01c80005140c3e92505455007900e480204c0c14a11201c0b466082d00205125a02030441c04000c000005145c00c0c21140c1c10100103004040300b203441303004035006010f6078110031185403070302c03804030000140080644211003110000b03000c643d46400d000c0f200300950181c07541203613103c0051600060300280080d907040c030000300c2c00341c1020b54078601c58144003515400040541d40d200a01c10035964040f00c3d45e2041d80130148401900c1c00c050300803c062040a10495410a601203912001661403d40c0004500d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 222828120 1250 222826870 222826909
    0x10306050904060507120b0303041a040801050f041b05010e010302211e01050607050c0d05160b0d0c0207050f19030f0501060503071e0e061c060c020106090e0615 71
    0xd01e014030f095401007000f5034201c80410300d15088202c00c4051401100400d03d0043d01860500340741ca0805442e000c0c00b0281e00300c01413406d00c004034940790300b442028420717032000ea4610301c141403e040c00d003148005200e042401c0051544107006507600b00410348410708080c42d00581c1d425411000210900e0301911400d1144405014040ba0540d0403464041d81c0710300801150440c0d0340c99081000e00d228200000341a030f040b0b0045480d242c0b92815901000c00c0c00340c0b00f42d0300c4418a01e003002221600a4200218581002c07501c1d140d502564400c1031000e502c5070004000c92400e000004058a40b4111312903c140307004800510881041c1c0d0b6990015640205810091007a601d03055003c0c10103409903601911912500050f0401d54480012080d4101308040c20560f007801031107945144010410340d0001500c0b02c130110710f1078949030f01081c614001c4000080c01250b0200090a40e04150b2103601d0035800c103540c2c02c0704007402049094201405c41b80c4481c4e48401c0300f002c600c45401d12007200990 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 222829370 1250 222828120 222828139
    0x5010605041508011a070c0308120a0c0c050604060e0304090e0d0f1404050904020120280203100c030b0307094104020f210f03120c0901030605 63
    0x12180c101001d08142d8840c044200e8000724040c00450300018244100c2d60f580d244a920041c000850740c0041c19136030b0207070240e030f110355407030b925100c41c4e0368400300055501c42070480030400c1e00e1109111301d1800c00c3c7d961a04c030581200d161995640c540f000b8101401c1c00b950352030b6558208908102f128001c2c201a0001e115504c403000c03403a80c81c0c1c00d684d00f102010920003e03c001c0c003d0702c98800031410004007030b801c60a05040406000089030028400c82c1404190111010000c90070506501200e080318020100f4561600d4205140345100380d05035400364006140c900180e401080c804100c0707204000024003208811412000382c00c2065010380c04d0b0240d500c010a42551540000c4200c0c10b601c1c0d91101c00900e11000c2900402882c0020324205103140c840c2c90092072032420b51500507000912404140003600c002800700d00e5070001307590f59000700026280708500c042c485400f0800c0150080c505101c07020203480d00c6030000030000391a00030006030907015031380a68040806400081d02c107481 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 222830620 1250 222829370 222829379
    0x12090f0a0c050301050117030703030b0607330c0e0f150301031208130804030308070e1203040302030601150c12050c0d080105031c0509011b1406041e030e120f010501 73
    0x1402142c001c650180d424200042201c01d4181c41c1d1a4070044c0180c000c600d0401181c504400410400751090b5015404100d910b0106000c0104c88003036810b40b00850300038210740118190818980000c0c0d010741800c01e4003104071a5040282c030700d407106040d50710240150025000483e0604035401000d0340900100002c070900400c04900c4050100c2e81d11074803003a440386035056030402410f201c000c118010401081c40005d00c16695aa0420218100a600c0118000009031500c071108042611980007040c20000d40c50200982801000c461003889100c1107110310080002561080c042e21242c1d001c680c648155114204580340110024151064000d402d00c0c02802c0c05400c2c401e01d0f20902c141c0c281540c8a01d400580103540407281d8071031510707100b0000f0040d0f50400d01c1849001550320080540c0010508030060460103a1100c4003038001854949040d00103042c465071801204604903c0910003c2c0d0060761850044104990101c80b4005600d60140b40075945000c10082c0d5007020000503 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 222831870 1250 222830620 222830633
    0x2202061912090506010320040f02181504150210090305070b010b032701020706093206040312020705010c1815020c0d0204020f0c160b07020612090f0a 66
    0x1000d226441c0e4400980641014544055607645400581590042070040000560064100c00d405a408140f2918840902c000400b110301c09103240c00100d40019003001c0000c0e005203071403e1403d0440303403642040d40401c05008140164001c0c03140820141207a02075090003045080380242c1110340070b102c07500f12858010859001a48100c2d100b280c5070300082440910881a03a203e0008400b1010300411524bd02c0080d0071074985903403045560800502c00444c0381e90040e401443900992004d0140003224004500c20b100c81c0c4240300c00c03c40749821340c8860344000301d0003e030819018644154a01d860600180081c440c01000800541c40c00c1086904030740c1004482010040c44614115540d80c0c4808000080da5146041001600145841586490180c04c14061180040c00c010b0410105008940303007540300c402510641c1d48040c400501098598508038080c26541810b82c0c10700b48541d001c01c100380a041c0e4018034045540001440340c0c4405c200522000c00d0100455540640c41c0c100070 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 222833120 1250 222831870 222831907
    0x111100b03010606050f07061d0d080103050c0301060302240f040905060411090d17040801050403080906010519030605061f0921050712080f03070e13090b220206 71
    0xd5020754201800040c1c55070041041c0d0703c44651840541d4030307000c0d003a80d8200040c15000e4401007561100702504103081000c002c1000740c405140c07103941d0194150b040840c9029a540e0606120f40c1c100003007800140c4514001c810141c0f014008244202d4110311100e40d01e018010040d45180804100010404147d4100c0c9026030800e07030303080100740004840000c07148115240035820400c004000070004e81e04000304912000d0106500d824540c83d02c542c60b00b0340c1c070190307015000100d80c1001e01c00458028410340e401840125410384440100c0041d1030541052884094005503442d4005199a201d480c80c0a210101228003010001d01040300603040c0388542c019400d040940c2c9400b400c0110604602c2d0ba00603070000b00401c0c085260003922140a6014a02105c07802401d000380b11410307081c903000e94018811504c42c00300304041002130200e00150741d442078100c541003109040105034a4205e054200d501146540e407994803408150100740a50078000b904040001000141041201e401 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 222834370 1250 222833120 222833141
    0x3060a02120f0105090c0703020102070b07170106110703080a020c0d060e0d08100b0c030c0601090b0f060a1d04020f03090109030917060a020307030f15050a0f0b04090b011110 77
    0x91007869107919050030002002400741c1a0000f051002003030b284403000340035008843c424400945017034000e40e00c5226607007090b01c003940800d07003a19007a0a6103d4003006203001d05110f1510101044540e160280d59501e03500c0083c05c4c1c04400074030646207902c2842400c4a14801500340417003d2010b280200062151140162240c0115100118030301d11421403640916401500300104a05162058070309078408145141148002c001e01d52141e0001d2080f80d000341030210001070040d00c3d8800f0700a44004c40c044142c400e51040101c0c080c03043e045007120000d01c01b10750745025140300d240007090080c4210f0101041c0303408080104405500b05420100d5003038825520305411a684408801554889041c0c07a8100c0d00550002520014264080c0d035002d0410301d8040b0740b040014510b4011606c18800c00e110310784204030103018a003800b05002d001051031aa003495800d02d0002013103028001e41c043e4981c401d03101c19214100d6803141c044041165110019540c0100d084200c60008090041a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 222835620 1250 222834370 222834397
    0xd050609010e0c0102150a0612080706051e1b09030a050106080f030f030c0f090603090f0d022802040e060108030a030f0603020901090f27111203040317040503060a02 73
    0xe40740002c54010400c543c0c0c0d4101a00109203600806c1149990381000800c0c4c045141d036250350010304900c0c52900c0c1c0c840d25011310740300f135030b40c10b15400d22030150360000f030400242c00801191f1202c0110035602d6658808445080c803005240754030f40c0b0929901c40c0781d251a5040c45021040d00612406522100c12591310340102c51140005a1307201c5d460380103154084c285c0440c280005600c40310181c00428502040000103032520b5102400998180c00a941c0104280e111040d03a44802e402081089a1745e15603000420034078540e0841095189540280b00341080198040e0004540303407508444103880044040c1c424540e162429556640c0105810000090510112001800c0e00d40314040540c1d4020341004081c0c1c0c2805401c00150412000030284140d652029800c2d240c00080a155441001200442540710300e0810011400031001e01d03d100d14015155002115000402c507000c8070b51091102840700895801034819024a91200740c0500980c02008000f070351650091000e03100011 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 222836870 1250 222835620 222835631
    0xa1205151e09161802070609030908060a06240519030e150702030a14130603150506090607030e012c10020c09040813090609060e011703030a0203040309050d05060901 73
    0x440c100c0ea1a4074030000d40d507200002003c00d0000c0c000c18070148040d04503e01c009403400010780d07140c0c4101d400c0f105041d40010076401d006e005105d8240140d64024031000c0c02030090b1810b00070010301d10b004244919252070b0003a803d54245500a038181ca080000e0002041400d034440c1d00c2c00b41c0908850012115a40640404c4800485c08040074502804e100d500850a00386846007e503000d00b074aa56000d0503c80038060512000440c0e500c460190510341e40100300c20b00a014120000740198101d00e1150390280001d10180c0c4420041e140215058070385025004e18980040c0c5d010300003501c0307000c0d0400301601040f4041d02c2102c2502080031045c1c3ea40b1034a501034400c1248c803000e50742465a4080f00400201e0081210361015001581c58550000d031401c0c1d651842c030040700c0c807035404000803e4440704108495400d80440390300502443e0700c0c00f0541070034442078036180c0c4402041c2e0400789a0101c0403c05051040c0300c81c201410340a0014620350103941019a91040201c980c64095030904 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 222838120 1250 222836870 222836881
    0x3070b160b1608010302010c0309050d2a03170f070b070c03080601030506010f0f032c0c10050f070606030b1311030c0d0b04060b03060c04060e0901050a1205151e 71
    0xb18240c01d100d040d035a1020035074211340c0110380341721401c00d0030340800c00a8200401c550360380d0342d0030856a03842041ca18245090307000403111014070720300030744054045880c020408030f812a40400c0d5460700d09601c544e80d681d4808040b1000c0d02910801900341200b400c00c0100481e005011040700c2d600a448003c0140c3d44c18004400392001250a14000784070400d0f41d00da807038010f50000350595001d017004142e0b070a6040c050102e03aa20310300401c0c5130002c1841d020001600c01d00c0002415941507600300501880010f0140c443e100e0200c1410401c0700010301001032202a5004030b0107190701001103402403d2490f8806044080c0c0c0360b0954840c403008660140328900061480c4401601815003401c0c88030dd61904c1d039842400600175240c0d0340c0c46440c41d6803c4c0c0d03418001c140c842c2e0201c6030000d89990805000402c0c0300700c032200b200d0145203070800501c520313500c017161941201d4100410304001031449c030f821828099107410b4201a00414014070650001c140c50809012620418540700d07076555 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 222839370 1250 222838120 222838141
    0x1205030705070509060a030b0702010b0301020d0c180b0a050d090506040f110f01020c0d0f020301050106210203010f0515070f0308060f010504050d02010503040c080f0d0318110f03070b160b 83
    0x17504d00f554070910350b910030400140e41840e8154003ca50740000603040c0040404203007a030748840c500119044c4c0d181208560150031800301c034412846a030502450f00c1c1010004005171003004105410f0060102e5510880c81e09900310840e041d80c8101039a240b81418542078060403a060300c115903a1031080046c0401e03040c9103841c40e400c01016030003030022002d171780c040c0464400c500d00301f0b50720511121020f83c050781b401d0107068020403803641c0300c0c8003030000400329902c840b10340a00c1b0000d00707004100401070a0120303030200044d28011501c40c80a080b00d43c0011055200d07811005040140c242170304030515810074101032181c3c805540994100420f100110350500c214020b40b54443e003000e10180c055403050700038540c458401c143c41440c03036450b0026280386c104100450503030f5910030000380404540c540240141c100c5200c400907840d0700260388244c0840c55030541a4041c1c4042e90401d0b84a07501004107200030810500c00d242d0314100700c0c051000c008403c00003030303606500c08000b04202000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 222840620 1250 222839370 222839389
    0x2030315010c0b010e0a0f060e01030209060303120c09010903050d02010c020c030102040612020903031209030702100f02060402040f020f0a0e03061308120c0403060e01020a0807320412050307050705 87
    0x10f118280000c1030307013000030b2101101e0f4044c0404843c103640700131745605a10103200319405861942c003082c02640c514410441c1544004001ca0f009410600050b5580b4000303074412038004000c81480c0e07841c0c0b14400012106448070f45e00143c081e10401c0d482030101d9406600107511b4180690a8a06054240003810300340d204038421000081d03054800e04000111b40d030f000c0d0101034401030950340741c50b542100f0806101c1c019615981c043d0000903013541181b80c4074010384500091410703c951003000691020b0744508005002a005944546021482000550494150351a4a40c1080e258040c01400800c000c00d548041030080c82000080f6119006030252030ba903980c0d1003074001e4034011144006140701ca001030207085010909120100014185000303c01000108400050b2500300e003400082c0a1300c80603140f50b007401860340d080d80660381c1245244004000c01030442804a6000150384a0f9208681c00a04149055096807042200c0030008011550181c0300329480d950311035040101609 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 222841726 1106 222840620 222840623
    0x631020a082a0108130f060e0f06010f2601021e220810020702030c0315040c090b0a030f0312060b0903010e0102070203210c010c02030315010c 63
    0x1455000041d41d0402d400c40018101d6a1120020b041c4401c007030140d00300ca00755018210309200304410b510b00c60320340c00f01c1d04214090400c0b12507900e0380354000c00240c0740d004900000030701547c1d420940c000d580320003001c0185a40216003650f5403040e203045e06040d80d5028443c44071043c12020350240028840680d550381c032480440e400b00c46079140b041383c4280010126050003244d0380045c030b90485c403d204800594407541800040d140c207000700d0003d68540b04034415044841d480700b40c003d0003a44260444e01c4440e1701e5170244000d0384c2018041e0398000b5415002000402c0e281110b04c90341a00a0811810644414000748203071802e40c0c10030b045084002810b10700710f090910070740507101c40c1c3e10021810280389c1e5000a49038000c0c050740c2c5451040071000780103601c6c4d00c54104d80c00380c00004000c1000304403864001c0d4480d003040b10012130b01c5d04c10030500701c0554000c10110710005e = true := by decide +kernel

theorem cover : BRFrame.Cov 222661870 222841726 := by
  have h0 := BRFrame.cov_init 222661870
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222661870 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 222661870 ≤ n) (h2 : n < 222841726) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
