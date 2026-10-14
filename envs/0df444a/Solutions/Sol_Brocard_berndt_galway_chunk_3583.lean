-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3583
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:05:03.553721+00:00
-- url     : https://prove2.me/submissions/5f195100-e8e2-438e-a765-d011e6483fa9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 644244604 ≤ n < 644424460 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 644245854 1250 644244604 644244611
    0x5030c25030b0a02040e010f080111030402060a030f14012c010e01050607050c060d0905010507210c030e010e0601030203120910050a0e031501180501030b07051b03041517090c040f 79
    0x100c6d40182034015000b4045411170755070040c64049041e096500750160301c01c01c26028410000540c8034041211f0314000c1d54940012001141d842c480010b09040450504c850407980010410903d0040b140c4040001038014005031545031401302e00d942000d015207400c004401004000c18204013003d0b000c0e152044065030ba03024074410218180c0e400002200c4406611001180309000003881800e40000c550300d02104103103165100d0326000d40000c1d01e51034882d0390700c0f0300030700c0e07154401e92140309c00351308500007404130300c4540403c41d694642c2800242c2c46801018041c0161514483c200d4040020140221070700101c00c0c4e00540e0240c016016a00900407907000e01e09080c2d80501000c50309252044d074000c002d50428043d01d00d0f40c0c81c0225201c048618250060010404142c070141d401307641c034a00715944401010f40403d0b03001085105031804d110208001c0744440c004081c102a03032140f582c03820303403101803c50300742c6070360000350750341e00f22600001189032080c1400c0d005052400400c18011 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 644247104 1250 644245854 644245859
    0x13020f0d0b120109050c0901140a030312020f070f0203070b12040b0a09021306030b010506160b0702150103141b0d02010e0303091201050109050106020c010230040305030c25030b0a0204 81
    0x43c25070b1500141142c00b034001030700740c5c040c900c0c10031505809803031000c1c4070100003121000880d40301102c900000d001c1c00708010309141400703016011541c1c520003400710349484458900d409585244042c0080f0722a0240324008640102110140d416030201c4a0080c0ca5580b520784810b00d12103000750903010100c2d1111071780360141e140c2008840180c99030350b10008229107141810791071032106810107841840c041022501d51020140324405031a00000513048540342c0c98410b03440d10001a10301e04d0464003034400013091056401d005a0a40d80745419154420b0100499140c00d40d58000100e41c003080b84103036040136520035140b003980700e030001d01100c1ca02820480001c400a01e9150002040c0e916500107101003122070140790300400380c0d03000034040803007400d001039242c100c24481c280ca00e49103001c2d40002c4200f407810003090000a050703500c0c0c0c0c651310f030b042c40c0381c076640400100400c51192000d00f040c0c244066050041c3c004a030714074027070f41500350350f01d21500c5ca6000d009428440c2c2c090001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 644248354 1250 644247104 644247139
    0x3060203040b040b090601080304260f0a050c040203010513230a09140a0206040b032a041517150301020702120606010809030c0c0d020d1a0613020f0d0b 67
    0x860066000b000001c590740740070b1408800b002c400038038111040d002400104454540001950709454240c00c1111000c00f079003034001180b066210901020f4071410150081c2d4110208411340c03c00d0050080e14210300028003400168403080c401c00b50040314950090081c1c1c4020b6100301d03003052042c4030300389009000c0d050860030300e1001e40e510081c10390b83d40441c6040041d49644582c07402c1c10240600307001c0910740c00003810790045104641c801c40d000400500c80e50000350950004103024207a80141000015a030140d0707404c075014441c0c16507002045481031038010a660004110780f445980b0b26907480001500260040c00d103d103400d903409010007401641d03079142c0015454658001808076142c80000109002000740044031203800c1001500c8503000042060219000250b400182095862010482c41c0081790300103131806032002c10b241e5240240d502594000e0300120f44401d408009211441c04074070a58101c00540c2c074080007400020415070b00452120240113102414503052903e0b03 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 644249604 1250 644248354 644248357
    0x3041404142e0509070e24070b010e161d0603041b1a1207110d0807180503070306050a020705031206030d0503040201270b040e01050a0608091e07030602 67
    0xb6460020242d00c400955500c62080052140003001200c40d09140d10301400306040140140011080201030041c0c078540ea1114031031210941e01c450304000e0f150003801c0d2400a2504508402c80300c0340c1d0344800008011100028489c081c1340130304c0501c00280b440c480c0039224500c070312811904010030100b000c2010703034070030024510482c050a2800c00c000c901c6030441c292a246500500c1d02c400056800347c1102d0000b6042c5ca20300c02055520541c2512464401e940c03d42029040d920280b040d0107088410700c2d4405203440c041c580c00d84036030380c4a1201e0704042e408a14540502a019400303540e080012403401c3d004240c200181c07610040c640200e039103601d0b00f180d000d01c4140c0480c0c1c00040611585060400c21100c212505103480c03429810280c3c0002c00b03040320b003071541714490214407580e03c2c119920300d80b907801000032500095965603110024411000c003485600d200e01040000007540900400400d8800c0700814060213101c40602031800d1714490420314114180708005c80030000440920 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 644250854 1250 644249604 644249611
    0xc06121005010f21060b1b0c090c040e090114040303021e0301151b02180103030909090812070e04020d0e0f280f0210030209041d0601060e03030d0903090f080f0304140414 75
    0x14120101e400e103510700e03245000f9485230302d10b004854580401a00b0300900055070192210003000542c1500d82401c4030340944100495181341c92071543c244410140c0650041c801680c00c0d449508420548001010241c00b0034881c00110311661650340700f000344501c0f840440c1c4408103481b04a21000380e004600607500c89a128810703040c40e00014001c0c1500003541c00000c040b041c0042c0300070760701ca5076004424020074040810311040d92010904140c007402c0480e0151601030011500d41060900f004050a1a00040082d82c001c10102003a04000403940c4070000300c98680004481d250100020001031400f20180c542c00c04c03043d00500141d803000745000310000c66075800b680718880740003003100712008100c001d641202c107511500c81007140071405c141141c4a07401c05102c40045640801c2c00c501c69429140700044c0741051000030103410020000c10361b500c0380140105285c5500209680c0c2201884842d01c50340140020841c0301c03180000702880340d030040d101060000025031b0040ca103002c00e6 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 644252104 1250 644250854 644250877
    0xb0a0612091a040302031b070605070f050c0409050610060302121b0c01020301060206071103070c090b0a031a0702190b01050906010c050d0201090302240109020702030c06121005010f21060b 83
    0x550514169629042d4000b014a03031014000140c527050014125100d9030130001e00f0f0319030158907042800000c0c0014002079001400c103000ea422285400364507020216100c0c402d00f810005c011030b28a11a1003034440b82003629450000548a9403098104590108002c1c01210020000080e1300c1c1002e0001e5030082041c0d07001800c40381061030f405055610035201d140c100740c0c000d01c00d1901241c0240303250401c4844000340002e0721203862012601c030500907000078080444034416007400c400c110700c48a20a903840d1f82588c5140003406003100d03501d54000c00180c28480500c00621091410f59105a004441410400708102c00c680d50103060528643c1182c000d070750349125100a054052204000b03502c102c0000c1c16010ba800e5001041441d0180030321407502c0d9020503002c0440d241003145003044030008111a4540010310140e40c0e1500d01101c00b0088001d000100080c00d5000310007903240c0c0b503040d480700e80345c11850000181e4161003200d007664410362a1380e00016601c440134010072000342e24 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 644253354 1250 644252104 644252107
    0x14060405040609021201060e070c050318010203040803121e010509010e0a1b0e0a06090612180b04080a1202040b120702100615090e090a080a031b050702040b0a0612091a04030203 78
    0x4e0801230b03001000001e000505110246d0b0148001030030100071100c0610b40c0303040321504a8100f20041346140110340100e419440006079078000f0302c40c40401c640c8203c4c45552400565410003030182c0c0380900070f10078560402c520500511402ca00742c10301c1c651180c400c500018900c41859891005d900c1802218800b00c3d10811a0034940e060071038103500035260b2401c00d94800c0d45460402482d0388a41c104a13001e456035200b007040c40c0c07100b8040c410240c41d0010004000d50510341441c4029900122500000c00c103034191501000e0594002e5504890f44100c8150410000040d041005140140301d00210b028012145800300c00c3d502c07030040500707001a101c0c10300210444003e00502c5007074100342c4d03840c00d0540810020910000303100c01042c1c1d101c148a501d070108907070300342c01404240c45120038040682ca00c03440c01a0b4040050301900b03008541c280145180c0c0418091410118050840001e01d01c0d05c049209082d15040203400702c1c424001c92502c400c09240130510124191806c40040c0c00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 644254604 1250 644253354 644253359
    0x90f210708040e1644040b0603061b040905040303020d050a020405040b0a291b281709030a08040306051608070203070605101e05131406040504060902120106 69
    0x444054100207800c2c0707030410380701801c1244840904401070508031413108440c4441050042c200b85c0c0d4804640022400120b450b0a2520380f0030501e9a04031707200c90291056600107070303580154800c0c58008001a802061409080589100103400f0003041a0207158003001700303103581000c1d44140352107040c40300b0005842d42d0419080000384d4a0a40c5944c2c403031140618103110880c06000d4000c2c50071a980c0b01340701481e06a440f5280140140d505118148442640414040b01c000c195000b08880148c1d81c094510104407424291858004025001e8949070580d040041c0c0980c1c000d02c216071005080b2180d11146070748880f00c1c0c1e401500200e40441e00c44040c80380b903003080f2151010020107030a05a0042c40d00c100d00035947c0c052108060400340d2240e001c80c0b030000025241c4005481000c030181108500f003980300781c510040d4443c4c0c0c0d00801c60b002940185c888148038019580d00005011012604e40d182000042c00001d801602e2850b80d83c80b06100580d20301c00c540428a07000400440e220b0b1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 644255854 1250 644254604 644254621
    0xb0708031e10231002010c390f0c031103060a23070201020d06140a080705030d0521131412070303091502270d020d060f090203030a020312090f210708040e 68
    0x210003580742200740d40608d101c40c2809541f0321500703500400310412801d00182800c01c0c1c0e04640d10001c02500c8070030482408002d1001140900000d880305500b16003a61b198812580111458510035007100c0b240040b00002d80803c0714905038000285100240c20328804030f40120403245a0350000360130355815400c42e002c50030580995401480380e500904800c5140502207921202d001c40e0300010030500007002c4190150300040a43c080b030720340303003460310074940700c59080d0403070781414019074029801d01420005502e000681000c80c0713400f900080e051414507a015000f43c00b90040c2252130b00803260b460401b51030359101429200d4100d0207207444001200360b03001141d4030f01c00d6415025541c0d86c20b1741270158035109074001c003541d44800e0008800b149030809000030040010700a40c14000000c04200f00e03a030000252504541c00c014102164403086e2120799075804a40d2900c00343c0c3c00482e407112010600c4005064203440507802c0e03e01e4203146903034500c0b2662082c6c111090000440d800d002065 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 644257104 1250 644255854 644255867
    0x12050c091005120f150a060905070302090f0a05031c0c05161d0403080c0c0f010903050d0f0b030601060f0522091b1d0a0b0708031e10231002010c 64
    0x160700c8080a41301d103140743d210050716100180d0003440010003400219440e807005521040040c5100501081203080420b80180a9441108800c0c8a02c07405035451000340b80140c1180d0455000170020100c1c0034104021407800ca40d011581790030b00c10f02480704004100c003402280c50200711000b503100c81d241020207030b43d48242d280d0b02001e052100c48080000080d0040d410303541020280000503103440351002d025107007440380303500c0c0300c44c0703500b003c1c100c07070030960001c01401903403003e543c052202d000c44951900445600c1da169541c1036006800401100d4090500e900c0c9800303c03464011710b0b1482404134803c07011320b055800341e540806803000308082c90707481c4280c0c000842c141d014006803034240b10780100701d18a403802c01014100e40b10700c217441c50b5071106001001000c0112041d03413580120b050201090b0000c0f11110030450141c40e00c02d0a442c0c3c1b91507054890948034151080083c01c12040d66a80000305044004585075004501090b030f0f6196560040c510703082d40040b0f1150845000208036 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 644258354 1250 644257104 644257129
    0xb01080d08070908031e070230010b06030c07020109030b010314011413140c030d0323060117070e060c0d18051005030924040b06060a0912050c091005 66
    0x30402c0307070801130003409804021a403000d0804240441c00c240d1612611040d032054800003944491205066111000342c84540c0d0f801740089109202103447c00c0a043c0d080c0d48010310001d0b8000d00400008500350301c00406407842034011301d408641c241d103964072102124420703081a03807030285295100c800c20b00309000e010300000d8170300140300b01802e14006610444a60000003270074291215801800303500100301c0c1c100c00c804010203c0f00340300d12402000d00200f080c04204000000c00c19040041c80388a88d03d020300881c1c0c10396812408040400020a2642d000340035001044141300015000d543c1d0200036200346041040500400c422a400107804c40f1640e0100399510b1206800802c4681e681c11410882c9881505106079a50359090041d07040040c003c6603054001e1010303200c0207c08140f49103d40c0b04910440b90705519403180010094207000d09054a80018210201800b48000003500520b04500c920304a800000896000034500c000841d54000503194040d42000b4034034103401401030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 644259604 1250 644258354 644258357
    0x919030c03050303190212012919230a140909011512050f071d03060c0a08150607020409060905062a03091e1c02010203011406120f130b01080d0807 65
    0x7e0584411004050030b0014841c1c03116090303a0b040c441840c202251102c2d2004685811000d50350710b070311700c42c90382c89260b2107600e00e0004121480340c07100800100001d500c00c1040320499405c1844155046601400840c1e18006005050003031a085480c1d0030381241c06081445d441d62880784c9010001052012a07007200621103052906001c880c02c141021103030845600e24111b40900032084204903101d080813041d9405106500030410508410381c0901043c8400740d565040c19207828402d14800c80320a40d0040e80194100305600042c9055800985910f11401010810b402ca6448a6090030001c8400c80090741140300c078001c045958080200c41200140310f43c2d401c40c20b000c1c00071691540c40991040c40c503080619a604020001c000c8071a04488400c4e442c02240348158000340030350020f01c225000e004502001166a103000015114030302c081c42d05030303509665101030140d02d80c1d102501c0b000c480c00940c048080441c20102290340a0410174008040c3c2041c1c00500802024008280f80c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 644260854 1250 644259604 644259607
    0x1b031f2f210708010e3114120409181b0f06090e0c0901140f120a060501021005100f090e0601090b09011707051e0a0b0a050919030c030503031902 64
    0x96103640042d2801e055030881c41c2080e05030f94500648228800503000b07500f0035016400c00c41c8640800c41b0b030313203418202c0c812843d43d1401904011216902c2040c0004890b8816060005101045003a03110300700e03104201c40041c00c0d070384550301c1d141008880b00c0e600c01d44590001c9014007844c13070305044250040200385011548545080146070604802400c00b401c07003680083d901e0716a83c400c40040c00040000d4100c180d654012624254940c0d111060721224010101d001401030307251442907208903841a00900040880d160035500109401401c130b14414032405000b0401c2081c010111000d018840800a200035aa6000a1034020305a002094a5080000383c0880340c41c0c1e400303500c0c1151201410728900b94074001c0d0305402c06003541c00003604a46900e0600d03602c00c002c0d1005101c000000e0b42c1c080005034170307100030031030b40d10803090032a02060702009150110304100c03840e1515400b10148003e0020748981e14542601015401aa1180c0c07010050081c183d50005034407502e5100c191046 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 644262104 1250 644260854 644260861
    0xd0525110307080c030f160302070602010c09060503250c051002030c190306030b0f060f030601030203071512020a080103030206010b070f02010f031d1b031f2f21 71
    0x110758900c54120010803040c1d001c110303428070880030020b0340c601e003c403210502d03200e40c00c0e5940c814002184d003400b03400610941e04c001031303a00e00600c10102c08030120303541d5080c15410040191040c3e44080d211560682d40501c03801c280c5008103204020300307030541c2c0d103d15445000d401e02c54500078001480c030541c5417040007800001c011420445480200300702554011001070741040e0010442903001406480760181000800c90f01070010034800d62048a11041e558007180c14980d442809000094043d40300d010141700c070340024600000c0c107210710301c1c00303500ba02000304180703050342c004011002c0440c0f04040107200301901070019501501141c1c94280c1883e45580b102c0d00700c50f0345004064103201c02c507049988624400c3e0003040f4090284040842d280744450012035403540440d0035850400004d150b08901480e0206502e10f04026410500000241c262074400007002d080d00340b0850404800e20309800c0e801c00b1007840758003101c0340107503684480030310500c50b0000b8110800035a4810ba0031082 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 644263354 1250 644262104 644262137
    0xe012607120201180e0a0e19081605030f030403020d02160501030f1d0d08070309030509090c070c0e010603050601030605030a150b120618061e0604020d0525 69
    0xd00e01222502400540004440d00050b5408510614542c681e40300440020401c420040190390050b0a9030301d003089449644000030752182320b811148480301c05203001b00008900804007a0101e4105a10303e070516071016540c007032442d03114103c86061036030080104428140c040c48001c1110040e0b0002d00400040c1042e00450407969025203414140d58000700260207015030301407807201140c180181d01c1c501405a3301a91500440c1030b442c00500081c00041c3d80c5403090007103108191341601c420f410305c50a4000c026100100615200f030494080c032072500810700380360141c40148084100301a50354107011000741a15001002d8071705040c2040010015510300141851045401114480d8204840385011000d0302c0141c10040d0b0100c1009034407944980701162090180c0c010203100d00341d04848135006600c2c1d85c0206c40480313440c7e840706070311000701d401054030304c1d8403100003400145030880781b1221608440b4140c07400c40b6500112600528100400340ca04224480300c0d04090f4024481c0412 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 644264604 1250 644263354 644263363
    0x240503010c1407030306090c030b0406080d0c060b18040b0711060106082806090606021009050607050f1210030b07030509101802060703020604170901080103020d0f020a0e0126 77
    0x4020311102c000141c04410706100740c1c001da01801381710005201644440c64003d0281605d0000c09114900d032800008040000017602d8002d811144c030f418030803444985814000740158000d140c0c00c4006c2d4010f01004c030121019480c0f1072445140300003440e0030034201c014080c80030403001240b00da1100e0b0043c81140d4100c200194090382c0860040b1400100c045070481061a14901041a50420501060440b850740044050711a16800c6480a600750307240c1d8410307100d80c8000a01990005004241914460300040003052007100d5114079100350350380140c1e4605411a079201d40210030190501c10030004049032a0896001e15051145052180b24142c441682609002845948035904040391050030036105000e50000d1503a41c8072426400c0180d2070f00022501184c019003c090103040804c80c0100791440d00606030b4580005030300b15802c1c030510300900d0006a540b25450403080004ac1d4035218508041c1c400700c108024554500750800c3d500c0400800c6d030402c07901c11180c41500a480009 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 644265854 1250 644264604 644264627
    0x20a05070f0203010b10030f0b04020304020a05060f04030c080d17160e0d0b1008070b07030e01030203040206040519030312020a0c260c03030405070e090a11040f240503010c 76
    0x1e031a6007440e0802c1c40002e00401c0c5214001380c01c404021354078402d098141d032007011504003100381030060700700703a1301040101d11084400a50000000c4001d0205081c290064501c0490584050342307031079140d4444209168440c0c4c030141d042c0c1d20039425402120b178020202c8082080c3c042c030501081c2848101d400c031000200c1700c030314100a100c40c4595000d503241d485a0003401c0c1c101008100506050758180b840c10611b0085490505c9108000a001d03030750350003114502d541640d28102e061448200450103540080c0c0103036800f14050001044556681451a04600801800c501d400e0300d549005032000310700da07403114562407042c4000c1200c45c0d0412505070708036511444503807131170030300e040740e003140c6190840240000600402c2407c00e1110000045001c0da00407011541e5140c0d98211103040010b040f204525aa040318010000003008030f2000591a030700104003045045000000700222411015959209104200034403000b03000b0220910103810142d000340701142c4d14040c003520b5203440c4c1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 644267104 1250 644265854 644265863
    0x4050603060904110d0b1806010501080f090a021c030e0a141c0c1e1e06030e010b0915190506091e0307140429060d02041d160201020a0507 61
    0x40010100050000a40c004c03c400038542400c8420b2414a625101811281d46040e082d00d00100b1a5211000516504880059644503c15035803640019004900903111122a1045140b4000140c0d90340400c803803604034001414514070207a040050185103a90207103801103141c00401e12010041c0c02214511010030354804801c00004542048001180b00010342051040040854000310106e400d400c075a01000d003016200391600d00050a404040600354000c03115030004000301802908545a45601e50b000000c0080048011690002c0c04a96141440c1c100882c02c00e050b00d018402c203c0040050034801d10450304040105050b03100e0010043c1c82040d00d480c08035010000301750844171070140601a6130b0080d603a15004e4920f42103806c4582c5c4250f0500016800c900028540203560f81038a0a02141c10500c003c14400d07958400c12203000441c0e02048007040c0c1004810010344e404201c1ca09001d130760702d410501c00303482e030766122070480071a4010002c0d010130320f40c400107841800d07400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 644268354 1250 644267104 644267119
    0x150f01090b0c03070606091508060c07030e0d0212101d0309011419020106060f02010e0c090a090b090a030f020a1109100315090b0a0b09130c0512010207060b060405060306 75
    0x40c110198954091421300506081c1055404038840405401c407007007030320420442800081d1620945901d0b500708070740d04800c0c45030600010000c60310586c0100c91102014003484915015600071808000c6011a000701a0340440030300c0048d61030911900803500e0000d941e0074100816021100d443c3c2c402c0449030b42c100030a01001c841c40702c5110040b2101a40e07604001403000f1700042c0c010f80a03000a1054202003108004400c64150060040e006400c9a50002d0030000250804110360b00e08041d220140c025594005000051078444030b541c000c04040c80189120801454003c1141c04180030003421500059693720006400704d000078145a001c036a07010342540c40c1c03008842d450300540e0001e841581310302034003503d5038031a500103500ba070301810143e80b040e55030741c440400390340319600c8143c1c01c00203a40004080c403480c90b1001a046202e0410144016940c500003014010342c00c60381d02a59500280b484104011031240202c0b80c0d03000d07242b0a0070700d03141c400040c406010061810303014a0f00c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 644269604 1250 644268354 644268367
    0x5070b09120d02010c02061008030714100c020a05070602150708090a080301120c0b03091906180309060201061a0d0209010932030309060708070606120b150f01090b 72
    0x10345a03100a15400241e08035003100125100080c041d0a10078410b030050300035400414043d40324404940141c4103164002c510380035030b582d40d03000403a202030501e01c0d8600402203401e4003c40d99020703074403080600358000c02d400e41940c20014140b250b143d00260640d8821112030401601e1500b960b030707000b251411f15840c2c6584240c10682840c0130828010f00442c000000402c26104000c81001c03a18044c460341e0038502d444090070304642c8420780380d450542d401007100030140c042c520311b24809144515004540a0308140c4283e076818903900080700800c00302d80045c0842c6038248140c00041400310750140308544c0012030b1542034071503150080ca000b82c00262a0b0880e9015481e040000c082c400c0e003082c101c950080601206a03654200c01c503140000c030b15545220b103000801d41300c0c90b0360018025442d006042c0c0e140e003902c0d489200100c40c01030b103801c00043d40e29a0301e032103c40190700840042c54245840c5000300703007a03020480c0f4035104000d1b0407100c00650740d10082d044141c68811034056034851 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 644270854 1250 644269604 644269609
    0x72301090e150904060204081603030210092906011403061c03030e0d11070803040e0c07023f0d021c0509090c09030c0109120f0c092309030705070b09 66
    0x401d002d02d41d000810141800b04002256008200b21303040402030f074104071029521031041d51414800500103030b000122201403000558041c400e500d1045800c403200502c3c4112003a0106201d200f5410301e0000e039801c100455800a04032400f20300e9500c9054134510f05080000c6010114403207410414000c54004000c050090740146100d13450a012201c0c0314480b10002081390000c0c0c4c0c4413500d0750280700000101100c0c000283c1c0c043d41e880c610501180d94992407014010b0300001803d80e072044880c6030f00125000d80f00b000071100040484000c41407034852000d460b00c0704c0c165585212a610825040152503400700f070121101501d400c0250070144420000c840c41e008205110354001107503000c1c04040701c00340340184030008068060341e00c0c140802005542e5050b0302d1281142200140c00a0400500e00485a40400b0307c9101c40428258a41c0110b10880e071000b6508605a1219002c203441c00324100a40e5034800d030000000e62a11016a60b000d8a41d000c51061180103800815030074001d6 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 644272104 1250 644270854 644270881
    0x90d1121070902032d01030c080304030507090207020612131e030e0103052d09010606110709020a05040f090207060f06181a09071d010302090d080c0709020309072301090e 75
    0x460b0f4002040300500d05d4404079a100d2028801100c100740807000000390500d0210a40b011a90403d002d800b035185404031181c040d5100301012640528100f20f000c240c0192001524054540742060034520100351806101c000c400340020355040f84100003060001e42d010b0750b03c003840e0400380f0300411552110703581d0b180c40c02a8090903650708114100314250310405440902e20800038040213101c0640d858800742c859590300c00d001c180981290038288001c081d190000c243c400351929060340b4141e5101001101b015072600803021107600016900103020040c00b50324050341080c4010821146008409284001241040d1850b2170b02c81c60346c03460340c2a07950a5503803118000346c0311242d1483d1070130000700320484601110082c0e60301c2c10a01e03007181d4841d10980b0502c10300039000300c40248190721601442d0700a001c1c0d88145104010b400300f00c101c21800914001c0c41c1039001800d001d4140041580f40d0001d41521090030a40102c4e480c0707181e80d20a8140007140c0305050001c90035100d500c109200d1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 644273354 1250 644272104 644272141
    0x103090204021c0b0a0503070b160b01091d0c0109061b150b130e1e03130609090b0f0a0e04031e0f030b01111c05090d112107090203 58
    0x3051012030324214010007188800c070440f100102c104541040032041141000f144d005694159204403014400049000c000b0180504a41050035892445988116840d4426001500302d103441c3c5000508142182c840c1d1414201d40c40c010b810380b0950303640001e00c1c240d49846940100100445075014007904c01c0d054000d810340001d41800030050194045020f4001706402e20301950b02d034868412007003010702c50700280407007203000b8111140c40500726202c04110300090794014002000751072003c5548495000003000161501c0c04810702d050003200403500800180c1d400b03940280e04544a079034034000c0d4801641d03c40c80c4840e080307803220306007142c1c0c11010149880c850001c0d000d64051103500142d034003616940c50790f0705100942404004481303054100c8070034030720307030784070803107450001d94403000c540101455403900a0400d0313000ca00040b41302005400640326004051881080340c10024100038644009000c030303600416410251542da6581da204041e0080c0d8003001013034040d05100b180455 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 644274604 1250 644273354 644273359
    0x170c0a080a1806090b04021801031e06020909150a090614060703031103251b030e0102162c09120706020f030a02090f1e01111504120f0c0206030402010c0201030902 72
    0xd5040b6860210800001506c059102c0c6080c2558610360703c12060845050b01d900041700c07144d410784541d41c10300034a400c0d203040b5402a0240405e00c01a100c0182d000d209281d150760440d00501e03824103020111805401008180b4200716080c0b20f42151045498204070068505940c1c48440d410220014500790301700c0903001800209010060340c600034001d00810502d4064020010340030420394172000d44a11001007404a03548002c04617004a0380c03017a8454042c01070f900903c1100460110001d000d03001081041d0f1200307400200803100160400c01c01750488112001d80c20300d800c0c2240e6440151800d200201030000d09030007048102d406842c03c05000c1c80c051526400d0203200350000e0f400031650f075070040150b201c00c0b082a1a240c035a25a800840079001c040d500c02140c01140c5800d42d03031004014030b11840d01c094048294a481a40c450f0740600100c0c0868210030300010103031555140c01004001c642e4104c500035030303120000c60340c2159090030916107954103440160040d105a241c0a50b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 644275854 1250 644274604 644274611
    0x40c1d041b08100608101806050619180503120318010203010f0503010e0706051b1c170106021c08180709020c0d1106040201111c170c0a080a1806 64
    0x4030007a0b00001c12500420b03a51101d0035070f46032101000c440715141121031201b00c4201e560108001c91203032142804074403900c1008190341c0e84450100e049540f00315000d0014401c0400c0c0c190805034440030410b2501d000b190b542461910703000010b41d071498180c1c050900380500001158014508007030580c42c140d40d8170000c3d9125030392900075007070340c010f24850203001f0350a107070304008070680100340941662074a4442504181342c0c81441000c418030300d5664840c0384221440b0043d1140002c201c48180e843c2d60ba10440d500c8102c1d070322049001810b0b444481954006041c6a8110200c121108900e100c0b0346010f05060b036806c0940f10101000c0070440016000d0220040b6114849070014500ca1215108481080588071022920b1801000c020011900910081030040d8412810b5005140102003182c40c200020360303d9490180c3e44041c00f60220300001a840003500c100e4612643c03000081c00b18a052075100000139154a000405000c9916035440800d206041d80e180d2004441c0d42010080 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 644277104 1250 644275854 644275901
    0x90c12090819051c1508031c060b0c030f070204060308030712110906040504050604020717120a0209090a0509070801020d0e0f0c0a1a16051506040c1d04 67
    0x1c4016030300014001c481d00701c000a02d9091580610110b5003035907008695000680e62802100004140c0c0c2c8460310013500600000051110702000544480e07030b1540101d4054074100d03480d90f4116800e662082070300e841d040c00f003110031070000f000b0346140054651150750340c0c2860380f0009000300300d6070700f009050345804003c0c0b2806c980c2c81044200c02400301034041010300d1a010040c3d0160048030512039001408100a202d2800c041c0c1246da0000c5e0050000742c281034803941c45400c118402021042840b80c041421500c4046000d10140c00c107143c80720852400050802042c0c50020081c0500041c540b01e10103e620398100f00f08000040c01020000c64031070b450745008002070444541d102d2450701c11848618401c0d1008680362060010042180415514015007488101c20b8100c0750074200c1401e120b10b8441d00b5021402c1a9010721407c040d280d10030061801455829024140d140944e1902c409030310301d2a00602ca51801040007241070548040c004001000f804039a01440410400784180 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 644278354 1250 644277104 644277113
    0x1051909050127020f150702151b0d091a090d11130b19060503180a0203010c0519080408040b0c0a15091203050403090b03070507020d0506220c090c1209 67
    0x24000f284201e40c044044041401042036901c00c40691117403400c0100001c80041c5810f080c054454540980381c2800c080740e1380d0719070119110701444c40311207070400310b003c2190700d0b40020001c001c0c21680707a000c6040803105401c801c0341d024000300d01d070142c2c001e01e0b410810300c03283c40711414000340010207000458070341c3c40d0b08002034035408441d680558007515a442c40340c00c000c4020300c16144503645090844d41c41135140c4103a1400b40305072001d240125800403015807028040c3d40c03106146511a43e6503407041e02c00000304980c0c554041820890500b0030300c0002a40b100482d4101c07141c992503d9180c401c48241503051664403a0b004010010390928071483c44144c1e0428030310310b4025500426400c0740b0000a40c281c400485000b00096424801481032804003000346401046501d8000c0c03c00800e40c0c042100e01211040030799141c0d0004040101a000f2800d003001101c1040d0644c01c40318031182c0e00c1c46843d03000d5006e0b803602c041d03d480001018507c140d410304900c140d01c01c400c1c441c003061401d0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 644279604 1250 644278354 644278421
    0x70f050a0603110f0310080a1209060f0f03230a0c030c05030412080c090301090c0f05040902060706050606070c030303140609011d0c0c010e01050a0c02010519090501 73
    0x2298000d15015600065990081c8101940f100391084098038116515a10080d00d0388003c008807a0300c2c5030142c000c02c0d044420411000944d21407001d0a00d00c08007040045d12404d02e540c4080108404049070410b40c55004c0d0744082e03080c1550401207481c00301c1c4036818056000c100242404000c0078010401000c1c05500040200b1043c0c0d24100300400e1a1801100d90344803c64001c1c101500d0302e00c02c428114071846207958000203080c2240d040c030f50400002420b648900c5420b84401064040c1840080300c410144401070808850070403501140c0d0b40400c04a004829000d0040c55441001611f1621101d00305d581480c0d0001c10490410748030f2070040c0041c5407250b8140010748d001e60004400e410411082c1e81030703603080581e2081190302c50350800c841c04401052180b240c0c00920400c050390f00f0034080e0700001c0040800104032840c203041540101c9602040310703011603041905100f1283c060b0038414003038420006000c1456052418060302505860200654440e121004030115482124 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 644280854 1250 644279604 644279609
    0x31805010603060b010305041a0a020f0307200705010c06020f13031511042106091203091406331e040e0f07150e10020c03060703050c16030c05070f 65
    0x14420000c484d0342c1130045007162801c440051180c550801d1000304003199026443d0b1140d1503110140c5000042d000c6c081c200c0d0815102c030404a098944154642c1d45030310405500d003074411004041451404c400202641124840544065030020341c580140c0794032011143c0e51104e0805d440310781e41d5240303000b07890950b01044450150346840d40700361105041004890889500500d05d280c002107620fa08041141c1505085500d80c5d5500191000100d444640001c3d40c0401d440008140003e030800c100ca90300d40900940ca1500078004010203801e92220a00e14000e82221802003ca0440c41042c40640d0100c1d413103502c03562600345044c04140800c0301c2440c901003a502406448411440742e6a40c0748000d900d0005500411401c0c040c0540580010070f0991051900d20340c09919800851000c01d05885100c0060704642116082ca0408018180e001030080c64104614a0882c0c000000360003401c0e450300740014508247c8051521034040315a0080c0c00c0800c1e101c1544d543e4090050041d06807 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 644282104 1250 644280854 644280863
    0x21305091e07030b0d0312020d060b090f0139080403050304050a150c08090607020901170607091d06041b030501150c0b010513110a050904060905011212031805010603 73
    0x40050704061213809060100100a85030b0389603124a983d0075a10b0305003503100c24903495800d002c00000f0000d1400781b88000c0100c480301c40e503190441000d1009500190b0b0326135040c81f404030004101841c400060b40034884034600c0000180700481b401104071162800098400c200c04078000c8244080031005000302c0d18226403003080c1030390f944603484041d003880500b82c01003000080d606020402a5009100b10340380101000e180410700d600188580c6030030b03007240d200c0d0342240c0c4001c02010010003126130841d000d400c3c0080c04038542138080b110010b0001c4113003043c4610034046089500c03503421484a01384802d4940055654011005005100c00d1140001e1400003080c0d99561600454181d48100c0d0072a40c48445c5a0038482800142c40400341c1d120141d0380c0d152100a8100c20810160280d20016621941e442d4911820001075600b1604030780611031612004103d181d040c8480b00900c2a4805442031895080351000e400504254014006801601c3c03401010030106500c40000e49114 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 644283354 1250 644282104 644282161
    0x201150e2a0f0a08010f15120615180504180303020a03090f0308060102121e0705100204120605060a05010c11030f33010501080402190503030f041502010504050d0302130509 76
    0x31048103580251b81403040d10005020b03400412200c41c1305240e92035001031448008244a0354402d191801e01d00701e0b1fa01c12001400a0703801780488c4a4501ca02d10040c14121070900c01c500004a45d0050407070901402414980d0005500c001e082c02504200f0303001d80c1120885003a4001c82c01c0240ca0351804403030444c010b01898085503040b081c550700b6154400140c19060000307080a5885042c90342c0200343c00d07515072145002101294945000420140031104a46103c1c039409140200603250041d04a502c1001c80d80410301c12640e109801c045645d130006580000010154046414184035030030440481c01800103101d241310300e9038819070074540b10716070b00c00c41c003207010380503070785d008000e01038140080d80e0b45012501501c1c0c04402510010744600129040d0755071040064556032103800c185511560100e400c000000710703615220000103460009014504d82030784c1d002c0d10b80d032200200d8424540d01040511101090b122020083c02d4054244090742c104065054001d802c560320702c0e0104000c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 644284604 1250 644283354 644283359
    0x10172a0f250c12030314071d010909060602010c020d0201200d09050d0503071101050105030a08030402060409050f060a05061306050f1201080a06050117060106120f020d0c0201150e2a0f0a0801 84
    0x2d0306ca40c0b0606c2d41d48d4400c0010074819841c0b4008000d96901030781004003d0601041d100311030320403e8000c240c02d4000103230740e400e0014060705005400444a095901d8941c0c80080c011560314510141c446034080b10f50b40d80a203550300c0c4014402000007410a10800c007960b00c82c2600500114003d03801c0e0f8440000550f068001d040c01c3c1d800034007c0d0380c4c0542180203a080044d101401564001d4802024a410140c68400ca482150b0040301c00c200c1d030360b1030201030003028144040c01d0342c09400c0a8915900e415a82104015910b9481c0f142c4000c000300021400703080180c1c0d8007a2007000601d1400c44102d0750b5203041d00355880c16803010a40d025464080009000d106448141d0700003000880900030a0386005030a42e0809000c00d007041c20161a0010102145400d10061035008100340000940c50100d0b00000d0844503201c0001c003144d040c2c1e440600000b03400d20304c050b41c0700110881e03a80c07881c40840c405519004c603602050f490b0060108480345a81e581c5009418882c4041d652405e01360b0703 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 644285854 1250 644284604 644284631
    0xf0c0f120320040b03070c0b07020a02130603050d1d0a030501090204051303091e1a070507170309040209030738031510172a0f250c120303 61
    0x2c00b840d400c50b051000400041000d40c08100256600044504003c215a001516502d103c400e04036501001138101d202040c0031490450400b01c0f44e0030f5641c2d41040200c1c10b568490ba0f44405030041c0d1414000050203038042c280321140c00c040d0107030303002c1c0c1840010f0f9607902c4e2807030181044071400c0348100c1c18440005c0d10428412850030038260142c3e21245541d160004803000011010040491142940350104080745c2e80c0798101d10380c2c0a85150703680c0d1805941809403d02c3c1c2950029140901d422288041ca82e0700002980e080c1c000c200c8005a503064a40700003460728101d070344045034650b1103240040320044001d42000c2c1d03801d444440825888891020902070303102c11079112851560002c00b00c010b034107004482041014103400c001980c4800c1c801d200c083c240b000c640100030302085808400264030043d604c00442e614614036070741895034200201c205070291008000c0d401082500c0c4401421446901da010160080070000d213480e11120300e5042c06180c11800d4020a00b49100c1200a0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 644287104 1250 644285854 644285891
    0x21011a0d030f0c0209010f030302160608010b0906070b0a1514130e01090606090b0a0503010b0d141e0a1106070c05120c130506010215040803070f0c0f1203 68
    0x54004040032480000e81d41c05592046003101d0300c1040040b0b0981000042c1c07241e242040c080c0074554441d41981e8030310f28001f40b03450b801c0340466000e081d0402c8204040d039086294581034580f507450081d2030302c2c20000801d5039405440d90160111209405001030300039260b10089140aa48d5080b1401035118442c1c0a551014107509030340040c50190507024039180e587c0805001800600041425542c6484150035945a9044043c03005d07641d09110354649000e00e0400300910066000380301d421030302c500041060240e01405440c4108a00369412610801d00200e840071aa1804502c2118140e84000d961600d41300d400308e422107404040c20109207480c05c00d443c0101d40c01010b60880d141040d0a000e0003030b49086c440000b92107441c800b10000d03034403e003004400074401c0310006924a001d0b40028500541415950041d1000c1001e110101d007021040b294418070340d00308985244011003003112030340c820000142100c1d0019406d10104200041800c034000d070981d03000d00c49545c403805450030301d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 644288354 1250 644287104 644287151
    0x20304081203070e03030a030c09050f0904080304080c0a080304170c060a1d0106030f05120f191709061b0309030a1107030b0f180a02100305152101 65
    0x20740c1c0510405080005164001c50b4040c0140c681032205442c5030020074030f160460325004c400b103521980d00900241d84003984000410f801c41d0b1440c464140840812140d800140020701881d50010006044c4149403049a500c0b241c0081220041c1003a8200041d958000351001c54034170a201032312802450100c0241c0f02d01c210340c80d026004684032440701c0c1008012100060b5801600a820014500820f10490004500a10005c00410300c02d00e000c508281d203440026010f00700070b01011580f941c0c0368090703800d01110b40c80d00c520109000d41081d190566a800c24041e00c80c007180801038100d00200c0d20501414909090602d04c0510001c0c1d4105d034041121048000e5000380010350080c0d1081c0c104503490421401a01c030881d03100c0e1618840390318111761885143d001041808645503502d010340c081d0074180405094080c80d541d001544091240100408040e107807004a450060341104c000050f03400205142c1582e2580a0340303090501440541036444e5190007070480300c429508115006 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 644289604 1250 644288354 644288369
    0x30303010302210a0606080c0315131e060f0c0f0207060203030622090f1202030a140903010f240f0803040303030e030403060c0e0f2e030f02040f05010807020304 71
    0x11400200c8401c08060003040c000c005051040001c9580401d6003031061b00c0242c501800601580351103002850300d003840e03a103800c044451001c810018181ea1104200544036072080d41c410300620000c46038404040080806840b280c5030980007010b807002036000c08240010b0343c48500126031001416a00c805061290101682003000001c0da14a0807511510a98641112071800f00c10388a51410841da1140d800310307291694041003078203000d500e084400c0304901501c015460844824401894409480700b1080748800100340400c081d038081d08103580300d40d0388850402800c001d05400190a075a00707001c180840d8507159012076020070403544481603c5443c4021031400e80f85503070840c014002c00d981d502c8240001d00010000690078024000800c21035601c007030010803a8001c00106041c1a22507e1184901c2c05141c0094102200304800181079904101d4414980000c01e07005004040c03140820b161000401080c0000442c00060548a0030303642c40c01e40ea43c48100a03646e078407035800f42c002c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 644290854 1250 644289604 644289619
    0xb030f0f0c0c0709050a06031b05012d0e1203070309090c0e061207090e04060501090f0e0a0b0405010f110705010b040c021902031e010e061609031709030d11010b030303010302 77
    0x3101310703a1500070b160884001080054415901e0320b1380242406030006032500301441000c10420743d03a014442e0b0b001e00f0041600703a10b0304101103080c10321150b618940c61042c0605680d21a4003a41e82c0e030600d82c0c000c00000103a80c0e48040301e180007041045240204807100d442c1103c050340181c0702d40101001076130080c00c030703a2429101036840314894000400c0e240800288c1d000114000f000d010640e40140d1244030081600d50524440009072480702176451001880d01c000381d884400001005480359802c845401300701d449500300316004d0112481c4030454a800c11403081080b003420070052a4050081c6e008002e06804102040f090f160031010700c90043e40806035035070b01a81007411020200b80f0050450700720000400c0481c00440e0702070b180142c265501d072034421070501d081c8880d551020300000110060701540c44080c051040a000142c55107550024000005400000b02e13160020020102c3d01fa554204d180108224410741202c07100b5403c14010030307441c1c100041500d0690703900606a0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 644292104 1250 644290854 644290859
    0xf03030e0303040302060703080901050109150605070516060f02070509040224040312050304120c170d0609140610170f060310091b0501020307200303040b030f0f0c0c07 74
    0x89a00c0500c0d50352180c0d26002c00c20000006075100d0004294280c4a81c60708000c501c2c0c450151070844105a001d0741c405424040032582d200032600c5540103a5030541005a11001c4905004c2d25259408041484500c80140046026600681301120300790683c2d080710450b035150410701c0410307034094030000c0d0401d5034030036070b40c0000080c40308800240c464181d00d182482e80da03850342481550070510300340101c0c01c00402d0001344141c40e02d240308032480c182404112641940d031214800f804070504000d0030000031401c03400300b60003034002000520410380d051008580000344291000c00980b5100d21a90380c1c0b612502141c0d004645175550121594085e0101d551007c0c5060602c01004026903810300801103d41c4051385140703ea0260790b4018180c2401d5502c0c0301d001d003404500260007450555100340f1422000034008507c1e12011a0100c0050000720786001c04646940150f4001340c1100c0341c08820051600b4150341c0d228400d440305003903072109842c0e0f101e03528401d10030340700c20800f503400aa005 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 644293354 1250 644292104 644292107
    0x913020c0a0602161103030909161808060114120c0d0c0306090c0504051803040918120807020607142b090819020f0a030c03020111041202190f0303 65
    0x60055852904141c5400e140190740b607404030b03400300c0030030301541040700030a40c107200031117440020300301094004615244580c0c00080c8e44100041002c440d00e203041c103c0034442d903c034010f010310320b09001e8003040c00d081e2501d03000780c0c5807402400381008100c008840c2c0c161514001c0d0701e40d4069190301c03028001c280e006c442070008034018038200340d070000d44501002000440728803410b4270041c00f5502d03450f1700078280300400003510006081600741c08a51400d0310091280401101c0072034034042e9002070042c200e041d03101c03200c910b540b40250202c1c200700c0c2c4250140d600142082e1007900c1940c25030320700360740d003241c00c0e01c06c0000411043da10078800d1081c201800d45200085000b0303000d8558141c00078402071003c1040d230303c114030200c400b04000310711264a1001501403801c841d009001074101450b980300c10581c0c80095140150400514244010526000b03600640e0359082440c503080e5101d44401496003041c15295080303005403020306110220041041c411070644030000d0300014624a561070 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 644294604 1250 644293354 644293357
    0xf041812020127260405040f061707030b01050114030703050a0e0f0f01051e1911031509091b130e07030c030c0801150323070806061203091302 63
    0xc0c035005540d0f943c1e486000366103828200e03410401c42c038100264803098616050780304410704410700c42c100d10280d50030f444c2e00c0060000d590540d0001e0302e00080460126481001806599004000040c0b008066000c5014040b400200b5640650610b641a99030341004444040740c803141550103200c103101092040e84a6001280c010b941e095000c00e11140c3c00c801241418003940048030a680041480e401400081c0592a440900c07464400400300700141c0c54605e1510040c0503102d0b0710340d840da142d04c4480ca41d030702840000c803a060340e0075100e28020301c0070a014011800103502c60b0034043c0000d42003010010b145101d40b1086914014841c901005001c20102c2c0802e045c020103844211610200a00300900c000130b40c011000f01c001c0e07915600380485035200036042200c0300c0e41031005240365034800807505002c907580a6240c00000e850b840520750209200303462400f941c02002c1b00069002000103074070340255000c4543c14500d00d0750040c440d40c1c80c85031001058000030702c0c8521444003201c41d030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 644295854 1250 644294604 644294633
    0x40c3003170a0f060506181c060e0303071b2a0b2a0f07050906060702040c0f02011a0919060f0602160603060602150c090301060803090f0418 62
    0x30076011550000340d50752580c000c122000d01580c0c0e500d0a04081c3d55040d809400010032058440324588041501c0c0140b103c90180d02c01c40c0103184202c00309203550b51250559510b02c2d0089001c1115201942e15a40c07280e05c2526041c0025401605440d18040e00c0d500c4d0030030941c0d00541940c000401b0310548000881a4001d11415a011200025042600030005c0840d0041d462000d00460449520001e0044009800920315440540c2d40961440c0009080c02a20011117000c1e50f00c0d036858001824078400c50304c00940207410070000d4181c8540000d00e807140a01c0e250020312542d600500c082c3c004103100041550300042c1e07800411f584c043d124180c151543d2110030042821502e4816420032000345a20081c01a4000782c03d802d01c0381e00500a80c0b026019514061082500d071034002941d0745018200240891081c002081001c4104012952840d00140003402070360390341c0c2c0303899407a40c101e00d50b00390003240741e101140010b00e80746c42802202c10b032070303811210502d00c2900d0f035062441c030b00d5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 644297104 1250 644295854 644295857
    0x60f0117040804150e150a0804031b0f03020c0906151803100912020f0105011805060f150417030a02070e1e0f190e060106110a0b0708040c3003 63
    0x800c004201801d13110800c00b620265502c4d9001c2c140300f440c080c003004ca078480c645003081e901d040c049801902c2c1c1c8000311a401a402d480d003440c0410345000001141500c0c51300c000c001010444060307003016004a2031091a003401c444130723542a940e2038103000791165018114000200104450a0708210202c01c20445540240403200800f00c02011303074085495000082d0340700700800d5000c1c4c00c15941000319100c1c007210034009200300e515000c01243c01410031400204005c1d260400200240c0310716080e0b0001141c02480c00d03800102c40c401110140d8020b000300c05400d0049600031043c403500004450804082d035001b00081443c1c036032001103003580904404407908242034807c80a6500d100300f1801a144c038600c49006080040b1810a07a020144600140c03500746280e001c82000042003180c119852814006504a01c0d22902400c1c22092900105200d01c8101885052903201100d02d1040e4843e4448881442c0c0b24480003002c0140a1400100c4554520701011400105d80716160a68070a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 644298354 1250 644297104 644297107
    0x302091512181c120e07051005130b121b12182b1b08070609030c12080106030e1902010f0203040806180705030313060315170a05010b010e0f0d1b060f0305060f01170408 74
    0x200c000e820f05982c02005040600c0246508dc890b40c0080070a0300280e8088485991f441c156403a071103545903c80061580e4110748907030300c1e4825460401d00a1413400000b144500c01125010030100b01501610840c603000140c0c0741c0c0c24080070b0030031450404130403070708941454204010396503100c02500c00c0301411070030490300e00114070018458451410003050a038a51071980e42c108030000b8200c80807817180020b580d04c02e1840f0000f00c514404001c400b260286410716114020440591540c40b480e4071100e1948104402c210b001d40c1504010300c8803004402c240c9042596920406035240200020344007003c041d0385080140d035009500002109500700350b42c11010ba6248003105e000341c1000c944800d80d4020000340000c1280a21400000b2750302400d2400640140e0004204c024000000850050700a1030410007482203400c2e20031450b440381e226140840392540d80007400200d5a49542020070f0600010800390f16000c0e001d500c450406175101941800308103484039203c24040c00a80d000b030700 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 644299604 1250 644298354 644298359
    0x3020a1106040315091a06060a080c09120106140d0305120a06090603030201020a03151202211e1002310302100302091512181c120e0705100513 63
    0x15000540c50519213404000b80045480c106a10012014942c2101c5003a080e020131401d070f40c5407020b944501e0740300c2c0307000c00042d925001c14100c644a80e40c40240e03c2921100600c4540c0c0d415040902540c5110182407481c441c41d10a001100041400003408201c042c480400f1060500382620380c0864000c0c0041983e95a0783e0400d001c991058000b900182d4000451400f942c0c0c142c01211000c8d20540d803101482840d00301c25100341c952483c0c0c024420340c508030319a03030070309141c190b003400c0380c03403120305580c00f4144c1c0702c401d24508900c020700b190060046484035100c0785214030964101954280d035403408010080351152040ba103191030b0550a0020105c0400503845030351410443c445562070069403000349a04114504892901526401c042048002c06552510b110316030881904007030460140300b003407501c070300f4000c0070f8108100074040000c00004243d13000780b090346028400c8504000d09103c0000311a2a107015001c3c075a00002c0d80c0c080c8050251150005101010980c02c40c80c95558 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 644300854 1250 644299604 644299613
    0x31509341205070e0a0e1605010906030b060c0105010b03060114030108061603020c0f06060f0d0c03060902060c0a1a010504200a020c090108010b010201050c040e060f15030703062103020a11060403 86
    0x70360941700b0140c03603035441d81401642d0f08100080301211000701d80d50b0074107615100000301030311014080c030703002c00d92039411009113034451205903107018140d90028015036858042d40c40c5690022100c4034000352412318000c90500d442021281a00c04141c007501d556611410003080341d1100c00c0684040646c2080705181c03024060080341800c0d81031601500050078031804100402c4050400035108400301654240043c201512000440b640000c011a140e0704c540001615409a0349100c0c0d01805225081d60801c143ea1446540d00401144ea01a844e6210303418041181c1c5010400010311540004056404580d44064010b8110034412144652030420100385500c000b03078407101d2981e44401c880c0c00650303020700036254842c0402003884d0500b131904241c50311049000d440325008642c00740400c503581e207500c80d9019840c031850a0071a0399081031103004004001d03600c070b0480070440c00325000c284e980a840501921a4251b80103041d04107082c1c0f60b40041c5202c4144982d40100704010000004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 644302104 1250 644300854 644300879
    0x5030a0c141911012a0c1206020706050f070c020f132301060e010225030b041a0a020301081506040e07030f05010b101202070203150934120507 63
    0x141002c0b000d0403002003500e440080d80e0350304980603041c4190441e60f190080c900400c51030856921421500403480d481c01c0c2980003400b280c10640c4070902502c0500180a038540080101901c40c45003049180d503800c1c52080910000d03681000016489800b200151904280e005040c00d0b0042503904034182c81e4054000320340100400b11368000090340c811030b501200f1540342d8014040c40c107021b907154002c180000d40350f02c284582003000c503150098030010080d076000c40ca006035034041c202110034107084c00c115400103103812010141010325000605040130500030f407412111803400601f03a00c156812141d03a0400014402604140e4965101e03030561010032600c00150b0007020300034500c007580d007010f500b0340c0e10149106000e8102250b0702c0108940c41840c42e1140c0300590001a21684c15100090130940c54003500e20380d0204560910030350784404105c042a146842c0d0248071004048000112680e204a44040c5c080107641000c002c0c4080c100050b2220074030850594008030307190350450190 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 644303354 1250 644302104 644302123
    0x403030203100e100305010b0d17130906060c12030c0e01270e0405100501050a0b0d0b150405040e0c0618030a08030705030f010524340606060c05030a0c14 68
    0x9558810300704006004080c401d230b114100e42a100e414903028103444800390f06200c2070b40100113480000c0c0c082903c940806191000e0401c07444113000071655410b00402881c0e691030305807038544d043c044460a503030081c42202c40110381d580b12800144101d074015108241606040e00ba54102c1c010300d401860800a6618040d20401502c580b9504003824220b241100658070401101d10f000018084c035510481044102c40c1d4681500d41d441894040c0c20010706944101680c1150f840e0300941003040c0c001d0054000e44d402650b08000c2c6040b0000d20903502c98a0b03002e8035400c40c80230480300030200202411135440c686c024003180c2000d80280d80ba02040e6004881c081c001441c08010f1103000d190442c54980140710440c1e54102e85008064511560b041d00400c44201900015a2460111003580301c1c1405002c0ca80701031211071101030700783c0c1801044800880d0010316003103000c40da940c015281c200c0003e402030011400d106c0668003e03070789484500402d0310b1510008400d00c801f43e004003e0400b0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 644304604 1250 644303354 644303371
    0x50a2c0a02041e0620060415090f030e01031a0f0f030c09010b03010305060c09031507140c0a0b0c03010b04060507030504170a02030609030f0a0311090a030c0614040605030403030203100e 82
    0x283c82e0500041c0221820b0001c01c043e1085c003d840d81409000040c4580c0040d000481078440c8002100c0241c01808081c0d0000c0c203c88502841405042d006124901d0003142071f03e060040440088010084000c14010aa48000d4501004c4054103060746070141200c00902119110780f448000070f10010800d070312070403a2032000401802001028403107203820000b0709811a0030580d403400042c0d04d50441d540f144903003120200005d82400c0c0b00303000884c0c200100c00425580c805135141803e031901c01e1640241c030140380b100d020440400107082101d0480e240c038141241803078100081290345602030071068040100520000c210030340c402c03007c01d003030710500c2d8020b10f80b0846510506060020090001090790414401806841c9401c81101e41000031440c000032080d40b14200742c2000d005e09190b590f00710312611b2010081106c0e01d0700c544d05849081c1c80b11144a0b000034010301e0079101e50b0088400141d01440030400090094000e582c04c1303c141c0b500c03004810b4480700d00f81910441101d0014 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 644305854 1250 644304604 644304659
    0x10816171f2306031b030901060306021c0b0a0302150a020f03190806010305010501081306140c1308031303031b020315100b0f0315031c020106050a2c0a0204 69
    0xb00800c91400301c4481000182e42c0c09043d45800e510a0003103100c0c281e8402d02120740040000c43c05442940820003031903012000b1500c440c52481202d41904282c80c03200c0034146040d0012525252007211501120b03402005454000d010303920b83d4810b50041c3d51020706500c0350940c807101980080c03019104680404000054181d104c147c01400703624064440d07410305107050014030059038840b0155a02202241c0d00700e1503072515103130a200a01d010207092038084115018844e0810030310009080c0e5680481070f14049640f5600c82648038860842500c00e041c03084101007000034000d94585080c0f02c03488020000e07000f401d4000c030341414019800300038484500020010333038603401d0701c0040260142d815a9820107136010140c052522000d095451144103100380e280d5140e50401000c1308840070b0007044c2c000c1c5c030041c81e40640a40610b0103201e1250018000216035408218030000840744400c104081421413201400c0c03021030042c003105801e64007000085482083c2c040c50035184110b00c281a07 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 644307104 1250 644305854 644305889
    0x30f071b030f0209160c02010e0312070b01050906100e01080615071406070e060d3c0609090b13050c0303040b1209010204050d0b070315080a02010816171f 68
    0x4c500d1004154a003907241000500203016807180f0400c500307a40c2800c100d5001c500c0d5200080ca440c1c0d0103406003c0c007407000100b0008008154111904980b03054401c1c29203038596000300030403440e46d00b0300c00e000601400d040c0500e5621a060380780d040b17030001c1d04414141c070460310001480e500038007058a804038528004000c21301e0400009500c18854540b0000c0082540001121032081c2030006203a00d80310100e0003005a00d0041c00ca006c1c074003004030300313480384040720404088054101084078514607100e00061390105500456504c69803002d104e42180d941d0500d4400341c0e040024059906200d8404810102d03117003000104040c2c03048198164560080851004040710000d15441c6540d0052004000c0740d142c201113010300f641e10150034011941d0b0007004034020704008044180781045600c002560160100d41c1c010124001e903120300b003d90b600d0101012041b04001844002080d40b4071000036110280c1945801c0080c49000790940308100026148520031138210001c0c0c0e1a000203c03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 644308354 1250 644307104 644307109
    0xf06190308120601030501080d0302071403040612050606030417070c03120302091f0f050a0216031109072109020607150c1803031202030601020a060603110a05030f030f071b030f02 79
    0x142e80703c0001d18080c002c1e5810200c985031508138a404946c140354003c41d01500b00001d03a50505404c28080c2c00312510b442d03594030f00518018102c048400c00c1460a408030b0b0050a24104980c8500d40215180b42480d081c0800b80300d844d8003d042c240c23040d8018000200c0003c0b50202a030b0740d1310015640158481c07000ca0200044403240c0001c0681c2000d514501e2030303486400403460060141503003080e545403c3d100005904018000b0785581c564090401f002c0204038080e1a41401c1030000d40d03606003296503e11050316021078004810340c0562819014038580f5a40340c0161081c0b6101030b10003401c1c502980d850f0b040e0090101c684032915a101c86c440c00b0065800b40c11500140b420001140380e0a1460314050301509488021805039500000001c001d03034003c002d054a03031a03000600300503071556810110320b290310095045108545808001455150004110507072880e44006545482901017004045511050b8201d03031009040324034644003401c090300200194000d0029004900e5a07204 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 644309604 1250 644308354 644308387
    0x5010e090114091005060111070644071701031406060315040308150618130b0f1905060f03190e0a0f0203120a09050f01170f06190308 59
    0x40b645030303140c0402085075100300080c1c511400a500200040d0a031206801210070710401061100c0741c0c42a40800215664460510f00c3e9907000b000007011402c2c0d607c011600510404500130ae40d036004400c20100c0754181c0c01c0340c00d4100d240c9080189501880c465516042c050982c01560f0400e250f01500e020001d0904c02c035980300710118041c080c403001484210100d120003400142c03c100c9030400188032100c000f40740c250440c1d001080240c4a401010008441e6070781c0404450180000c10003581061200d0300a00e508070a0091004000b8040d0400f8010004061800c03c22807030400c2000142c107807954030082c08940241c040d0207a807072030704d10460b202141c80c00f038800c3c00703a5180c420501c1c0f120344085110b1500c00d900c102c4000c5000e8550001038075060014906503004ec1700091440001e5030072410000480f5010b54090380f0310006078005403201d00c801f00c040c4001040c80000504109003010074242d00680080911400031110b40d8060081d030640c1d00100d030305038800268180c07120950b01 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 644310854 1250 644309604 644309621
    0x160605130e0408070807020604030b04121e050714010207060608060a0b0d0f0b091f390f0c0803070c1a0c0d090201091d060a090606020d0f1205010e0901 67
    0x1c419042509250395854802d202c0c1c00c0d000340803640085961411941c2c0c5e034089500441e0050b030020180e081c00d040040101c1d00322000f2030082802e03540400005800e003074903804044601d490341800c0445c4c5490300398000c0003015441030255401c00407000001e026101d08009003403800010301d050314080428000302e4009a2803e4444c4030246001c40015034000e501000071030f4404072500b025154043c20900d80104140113564201d1002240880e00070941e101d0b084010343c4010303010450307035a8500050051194114509111454024800040d006800c0c5184d601e1207403800c0702c5044000d4a80700c085402c255194000600000d801d48140f24440b049032a14511284907451241000105441144100c00300ca114250312841d0203400c0d6809004550024007540ba045244400e484101c2da10001088455070311548e1025404039007448640703d8002078482940060140d00c40c0140280d5584c2564581e170010002071611000c9240c00c0c5001c2d86000349881000b00006080c1803d0142c290703400c00b0b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 644312104 1250 644310854 644310869
    0x31807080304210c03150f0e1903110d03060608010b0901020a02010f03090b0406090201031506140708041e050a0803070b0c0d0e1207060b09062116060513 68
    0x14a0a00c44600040102d608660800d007158a01c40300044403030051001c04207014009204480c400028410203451610461141c80001c10000c210760686c44100d0358041704400c0b096014110540030640d00ca9600c2d2001c901074282080344010141000307150000c800500c0b000262504010004030303811080307550241010440050030900040e00003035a448040c1c0002c0d04212032400310140d44e500030750040580c0c80d000340030341b2050315083c1000d40282513210305c01c07400245003450001c0690041e007050400e480d515950a22500761051824a02c2d40024805448a803410000064200c11000c40107140b00c50084440c03440601d048108a00102e0552012000e1380040251800140b0b201c00742503030101e100c1d40368a4540300e00001d054010b000c0c240c0400140d210740d40fa07880e98268071002822001c0d100d44424411001d50005201ca1102c0039258540c001d036228001403041110251000b4a00440f80e0464882d62945940100054420390203030740400c00000e00170b00303684c1b400c24207034010f000d50 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 644313354 1250 644312104 644312113
    0x130e060703230c1801110f0a0506010f0503030427060801090302070807140915090f0f10050907081806150a08010e06130303060302220b03010b132a050318 68
    0x140b0168081c0300301200c0350441c03118000c2c40741880e030055100000b41b140750022520602100061555114040c103c262040e00c2400000601001038901000c10307188050051401c103440c1c40e00b40064948203001d03402c041443c1c1c00f000219032200384994002461041c0012641c80e0f110300f400307420300c0b0640e00040541e810814041c4445c85a00141d410441e00684d01100c0940d45c4484030b031a00e0407040d01c0c96030b1090a010910843c60308529001c0c0c002d051800c10400603842d0543d000c403180070b541c8217050304804d850300000c9800707020740840c1e503004c4004150f509180304030011072403d140741100c1a1035407480848c000c004a040285d1441c0107490500000c00c04285550700040c0d44601c01050402001e11100c035001c10103200e0b82040004582c05411041d0305e1855840d040c20301801c1c1d0408001b4a460400c1040d16031805008018041d40060a8600803070000301409000e450034410440c080102000c0100d000c616242070207010384801d40c0c1c0e080d12402e02c000d244000c00000000c41722142e10 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 644314604 1250 644313354 644313361
    0x60907050405011b02040e030a14040806010b030c120a0218030f07050f0a09050f0613090f030305060a0e04140d0c080f03070311130e010504020703050405130e06070323 74
    0x810604840944809003000c8130450100c4810304007030b03030003128002c0d04103003880000720a4103000000b500c0d091440f82c940021810b4a0032000081d405584103002d8580c1c000b1004004c4080c0d110011608091a03e0901d444e180c0c11003406402104280c1b10141ba480c1d0005e2040425480e260000880d41c0d401c602400a0145440c03900c0d0b5148200d006c2d0794480e0326002951307540790303455100f110024402104140481d02c0e00711002c04024130101e034010301640c8a40c07036460f0740786001d12a0011f510382c07101452806442e1502c00324010000106865040000c458002c1000c40081e0821342c1b00d540304600000a01c40d0074450242002145007240c028480792040e502d00068141050384c400401c0c004050303407240d0f540d1100b100504010035091a10794800210325088050003442c580580c0c44100c5044041d0b40d07160144000c9120320031014000030010700c4180700516011080e0724000c0442d0901280c540b80004c545e5040070f101b40c1309440170a0380c1e0b9115406110407044090b2500100c066050190718 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 644315854 1250 644314604 644314607
    0x607090515032d07090305060f3d0323030c03030408070501091e0611090f120a022106060409020105090103050a110c0313050307060e01050f0702090a090209060907 72
    0x20140c200340b00c400303049001900b6140e12510200440034181c0d4071403a20300313021101130f019941c5401306442d20700804d00022240f00841598a01403038240c520303000112121262220210341e1320322042c0320b51013041000b00507803070840f020402650050808501441148c94807019000d050b00181c0c0c5260000e0221881c90800442034903030007034000d050740b5a02c1400d850500d004150105001784000a83c054002c5041a903000041029205200801405ea1031403004036150240031235055105903940c0e00b400d500d04000d20518070303004000e0101d500d103c01e0350f400501100040d6000b40c2c1c480b000c0c40c4079088122010481d4981200c1f040d2020003010205400007072040c031840500d1814103031201d0105180061a03072011107400c01130105240c43e1992046000d850340c0c860340c5080107881260001184038500840d0000c1100e0782d9407911a08507040f01c1c0191800c0c1c000e8216520550014051100583c80d850300d13a910800050074005007490040c810031180c0301d006885c060081003200c0800c90030b01d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 644317104 1250 644315854 644315857
    0x70201020d2406050a0507120e10031505060d0603080c030316080c070816050132060619021024060e0d02090c07021302040501110d08041719020607090515 68
    0x101c0a034039004d03583d50b1a0301400e495611800000803c0034602005a0206130f0340710a1480003248119400111190700d080704038141c4454540110440b100d08408002d00d14140c0020140b101c01c4100200300c1315540c0d2a408501c0e080400c40340d8180c2c000104101d9000e403c0c0d200c030081c0d18020f083c1441c1e68205809070081d60302408500504030000022460300280c00340340b2118009500400920041c0c02c108149100481145c0c08100103020324810bd0000c030714400800d9214650284c612400d20124100742c0c01a1400c43d1030300410b500900086c840e8440c011700814140c80140340d40701000c0ea118404200c03040c40258000d800b08a12484480c041d9951001e42a040640446584019445d95907029005104109009501080d601c02104e10f20005402800850300d00740c0b21070001e5800d40c2140c03911400c111100100050703100001a00041c0005405075100705d0504449081428040c40c0c180c4800f828102d100140e030040d410040807550000c0104060700f42900c2c2c42c4a110144041032466 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 644318354 1250 644317104 644317109
    0x402180403021c201b0d0b13020a030203070e0f07030c080a0b010e04060e041502030106140c0a080d14060a08030409113f06060a180905070201020d24 66
    0x281640c1d0103a201c41441004014006071800340e00b42c130107000308603126640c0d4203042c04260f107840812907030302058a0b040384c003042c0858000200d201e8641c1c80082c0c001c4108400c000480c2c1c4648801000f1002d83c40420403400900b0084904400b1800c010104401105008040f20209820806028034903a4040840c50b0040307107203400420300684000050751645103401d40a80c1040c0780000004002034006030240c001c1d40100c1c032840180c00001d4026060784824000c640200d40c5c28141000f00007140340007400c2c1d2428160540d5440c0c00b042c1d84844550b408031800d04c4042c1d46800e0701241d4580d0f40e0b1403451300902d04940e0104061710b070842c403584074003482c85491212981e9088021008401a0440341400390110a4100380b85140b0307400320202d114824180c5104203100258200b41d0603a079440303801000300400b21030500300501e1007110400f2200e84e4440308040505400a03014165019040c000c0c50f0076000036072240050004001220580d94109040b04d0742c0030740e0318003414882196070f0103 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 644319604 1250 644318354 644318383
    0x70e0123150a1103031024050304021201020d0504061b210e0c09090d0f170411030c0d0501231b0306031c05190503060f12010f020c0105040218040302 66
    0x712070b40b11010946502020100c0c42d5102d01000041185951031104d110042c3c4103d40110146040110030103810b20070300c517640e0408100200081005850300c050040000019078001603c0c04032600d1641c0107542c0140c1d01142d40f0b5444071132200344081404402021034102d89445100c0940380f0040e40b0f200b40d0105401c0340b84a079104100040c10b01c00340920b07800d034407001c1c2c07040001d42080680f01e03903620050090000000c400c4118131000c1380c400c4508072411042d1029080c10380d180c0b6243c24100e210741084003540740c419030141616946030007010200581c0141c1c000155001349203e0a04034000c00203521000c2c41c800b204005196500c81c01e021904a6180c01460302d0342d4581c170200c0d00d480d402c01e1155081540c00c41040c0310a507448802001c481e008641d00480040e0300c504151405d0000b500d00350b5201c100b8100c4000d4508110550046442000c070001c50614500031803002280e1000b403000305141d4640b42008250305008200d01650346040f1400401c1e4070700b68a0003511425421003601 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 644320854 1250 644319604 644319607
    0x12060f01090513020904260f0403031809050f06030106080f0318010212070506100e06030c0f0a050604030804080d0215010909210e03011b02030d0b12070e012315 71
    0x2003007050b801c0034000c0f4160307001e002aa41428641002c07202140b5070304d43d038900144522044020700341d6000564660307a1040450070b042904596090f80c1140c6408003490b22007200c8000001c5160150044c40e00075070000e08440300e00c4c01c100c1d09250960310660445880d6030301112683c059404000b080707410000d240d101d0350a01080b0500101c2c20401100c0215541130008201501800f101080c100c0c01401c01c0f03014284219076451419111030803c8440503070640141c04188014240800d01070842000108040203030f50300d4030f0010344a07400c5600140ca04e0b0501150902513820308100d0401900b00500003400391b010000c4026140302d01c140600103103240c0340e80c0030508100749803c0e140440c1020300000c21142d0500c650017401c603090341010511a609200f440c28003201580c1c420540c000085c0e02842c5010030002c0b14a014140386c0c0d01041d08034507080c005803900756050200301c000e4001801c451409515081000d001486100222051040c181c0d210381c0c05540c880700ca581d0981074030310a95 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 644322104 1250 644320854 644320861
    0x3020f03010b12031801090315020a030f0615080c040f1a04050d351b0712050105060118121103030721022a0f06071401090212060f010905 61
    0x6070140c4400c41250781c0003c00e503820102c01c1c6101101030070003080c0322010604600a50001195482d55500c40900400114510000300700b41a030028054440303203040204407804948107000445800354030183d80002400d202d0000305034040d0307460303402046800203182414180340e021042400c8070322a0006203849081c100741d21a171084140c0d4014000180141039440150a0a59070081d0400b6910781105503183e1403800740010010407510340c90340312401400c00030b840d0b4021048140740131103140c10344a040c00c0080d80d11080ca00741da02040c03090001240350305080b400034201c880c242ea0245c41c2847e4140060020440110103a0390064016110419108910000c02c0c1107100741d4070702821011021a02a20f1070454042c0b0301c061240e01c1d8200c40102201c0800c000303034102000e00c01e844142121211741440c4c94402008840c4100040c0340501d040c040303585d400000d0100f11840744c00ca13510f070381ca60000c2d482c081d03111000b4191004050074280c5000307180d0400e01d1805020b28540e050303480011 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 644323354 1250 644322104 644322109
    0xb032d060c091c08160b180607050a0306080f0f01060b030c19051b07140d0c0e0402061204031211040e07080703020f04030302340b030c1e03040201022503020f 70
    0x40603441c135080110190ba0b000d54603101240c04150710304c140e44200500002c40c0c050001c0300d40b0081c9000c0c20102a1030301d51180e0f18101c0301c9038402544201051b44800021440c0d0b002840780081142c4000010032041d82350b11400c03820756149510001000c8018002c00c032840300410200c1e213071034050004001704e402d070041050340d95009070b820780740c45109803610b80aa04280022280c0030360b400000b0346107820200070704204601c44c0e1402d009005c004111401c2201d604141b91a58004d84000c04282c18200d01001c034449131441294141d00040b884078050040140324810f08004000d01c400300352038a1300b0014403404500b800b50050040007582800203842c540b12f40c0c11f44080110032041d4640c1c5580c1da050003561101984001e2200c91a01a2401541054041c07891034080c160060170034031902d031014904042d040100422951181001303014020310a1050707441151940200164407414107000080c038142804610481c2c080c02401d01900344d800380240c102c1103d0341180c01080321a602c1c0302 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 644324604 1250 644323354 644323399
    0x1503020102071a0f0a0c110f010905040905122701081e06030a061d01140108060f130c090e15070806130f0f020405011b020108060d03030b032d060c09 66
    0x281001025001702d0303106096507001c0e403480c180e40d009020694001c107008040101440d41c402c152800304c1c0c3c401c4070802041c201600300c101c14501503002d13107600002c4580ba800d01c992200751003840c00707a02c01008078000c010b40d40c1c10040f00c5600f80f922240505e001c040342d6610a243c081950b40b00c0d0020b000240040c0c0e000c008440780e85600c650144005123207100585c0f5403529000d441081035091008401c041480241218100e4024800401807501e946503542010040a04581c1c4007200d8a1b110390041124200004024000c1c60300000d12040c5182059040c094100c480e40c1050b9907900600040c05da10118117078020300e080b54004074142d00c4489000c02086000316404819042070704400c405807a56015000312030081c3c941c49141d44811034507060b105c80710708009000c203900201003600740c10450844000ea501c681070000d5403031604d03000240340c0488a000e500d40c0d501c0713251010801c42c0c0c2c0700b10408003031035100c2c00a010500b000107002031203008403040302d030044010305078007468002c1c54403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 644325854 1250 644324604 644324617
    0xb0606070f120305010f0e15060a200c0405090309010c0b060f1201051f0605040909030c060e06070f0f350f011a0a051c0b10121503020102071a 63
    0x8035801403902c0004409070141009108417501415141c500094804e08607420340d00c200d0038889100042c0800b44100a0725400c440c0303000c8100000c580e121310310b900b0200c0b0040c503000242c41c004c01071350b1000000c04c000d44000810401054005120405041e60844041410301d80c1c840b458428a0740ca050205d47c500d1000071809500000400d40140c1c40b02045d800540182000d0440404440850a024105004603c207107400034404000801c440c0071a0350000c0d0805109103485c2c0c030326106a440312800e076008030000c003400e50403810a10090300d8200300700b0b00304031105091010079040710340405403c02074496442c000c0c2c6440c410041e84180d6810003c10140e820700b211010a9080038100007019140074003410036203254612001902c244644c1c10788200081e00d59840740f030b141c00700780390030794440d040000060b40c1c07510740e60310680980c0d40c0a940c3e00c024a80e542c8540010400d500740c4003d40d0070600b13010100190811042c005130f6804100042030b548440c0c0c501d030103d544042002c10603c01c05 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 644327104 1250 644325854 644325863
    0x3090c240d09260c01050f01030807060b0109030c09020310051f030b0402070b010f06230405100c050d020c040f1835041502010527030f03070c0203190b0606070f 71
    0x3e00c01861900c000d840500f0340c1c80340281c003c020595850b07480384c403180301c20b02000e40104028083c03040001c00e1a041981041418505120550b0343e0355281507481c5400d400c90320805030040f0070080c0f10f0480340c10310307001441d084603081040300c4460807031940188004035010406d5111501010561501d40480e080c5661001543c3e0140d81c3d100120881f40340715006000000d03500c040c440b51512503205e41c1c4169204840502c6140614000821002010401c684000c0c403c0d0116a400451000c1c04207000014080e005411741590083c03c100813030b004601e44070003042c608034028400d00c034174140e18440c1d6540f00920b029000d0200e02d0603c8c000c07014840e040d51011846107044240811100680f00f114200300a141c201850b5041c2642662001c958003402e03c4000c4c07040700e012260703282100d40a01c041e001640c0c0350018082c000352440d0300444059012841c91950340c07045007400c104492824003170510088801d4039030303582d14020305000303800d0030f03c14100030070100c0c14040407504030501550310 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 644328354 1250 644327104 644327153
    0x42603182e180c06021009020a170a050604110a0602010e0303070311040f06170618060f12070b030129030411120a0b06090907060801092003090c240d09 67
    0x1a10300030941c0750f01130140b40014001e80d44016070302441800755485403640105034408240c2405111703a408540f10051001c11b02c550300501c4041203061009034040c80c02004603803022203003c000d111085a05600803411689040c907072800414011003600d4210a4918000c07541e1f0072020a00c80700c3c0c1c0166040070302c02075000c08000484a401c0a42c503201c00c100d03000c0421980d030710310303081004001c2c1552058451001900004440b490320000455000c2401020390b41d0008101e152280f0700388054000c00e50401c00000140943c0b45442c540b096085810b4580c2c0d160f110070761007865200c0c000500010420b0002100b107a0380d0b80d84040014590a00403421913403081800d08180319601415500c0600030700351000801c000c9480410420700f9101075445411199103810f200400410403c0070700343c440300091810303440d01c0e00074000850107015110000c0c030956405404101c3c400340c404140f0440d40107080c610110345411182079400030441079000040d80e244a081018049540c800c48242c030024 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 644329604 1250 644328354 644328401
    0xb07030603050f1b0616060b0118030f14070303050409020a030605060a03021305030f0a030c0f02040905061806070c08070606031e0b060405010b12042603182e 70
    0x1000802001e143d42c0310706001001c43c1903605011440c4994614819501e0105030002d0111f016608820344040d4180350105040e01214464440300c99207400c00c49501001070600800e11550710301e840200c0c0005000f9010140c0303076a401a01c60310603440307205851a0007240c842c0c68240640e0020000b040c01802256881084040c001c009600108080c4500381019402152605001a8800450b0031140052403028040c5c7c0b400d0341e4160841804451004820b40c003007005860380d015481919100e03200505290405d6010818198011940c4801c00c0e40300400b00f101c040d41c090030a0000c0313078000201c984d680b0b5490810750054103d0b40c00c041d00c0c607481540032100192400c4801071600340134031581d04103600c6400401c0309441c800e214a02c6011000e100c000c0100f402410380d103400c0391058040403868003890850820800100d60000c90b00c0402000b005084130803101003002d44143c141c041c0c54020303401e50044c1031515080c44005021144049610300030241c65000703c0d8903070308000c0c10082109 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 644330854 1250 644329604 644329633
    0x91d0112110402040e160908063103110d0c12080624040510021923101b030504050a0b0a0605130b010f090b0f03060d02120106090e190b0703060305 65
    0x103005948101e210403241000d003507118412162035051f41d00c2310000c0c112988490110700c007540c612044410500000d0038001142d8041400f42c0c1c2d14080c800e0311040c15038440495034605042c6800011010300280c4002c40700041c25034800c0380c1e09003a05040011090303c60318081540f0956401142d150800d810f28a004503103080409042114400c44945400350203c031001c0342c465000c034101103803034a5640904000241d0100328030142445149600c44540c40b1905403a24140a1281d0b4203491a698100d401c400c5a8940034031001003810700b001d00c840e040c1030341d50f26a9141d0000300038100d216490302007940700703c040d001400100b0740100649140c003641c0440a000704014114030303003c43c400440d0b5045803409a0500002c903100c10842d5410f00e40240b0280302d0320717840140100d034010b000c42a0400141e5a20b5001c840c03400c01c1200005955083c54a001c084580c2030502d640141e00000c104010400c000c400e0a011503840080c0300650388880d103081c0c014181541000709540500015070071084c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 644332104 1250 644330854 644330879
    0x1e051f0308160b0f1f030b011a070c09061e1203031508010c08061806101b020a0b120106050c0a020111070305390a0605070c0509010b0a091d011211040204 68
    0xc011811645c820042031520f00c016459840c40001c000c8030041004021001d100c070700718880ba54800c80c0300340c5484807941d1200104102a0041f00074595183d6083c001407102260040c11040741c0303214038500c1400c11039030804201100000904046c1c0752a08550050259441070f401410500001e000d000140c06d00540040d10440340f09000340032840f1000041e40d41080124001e030006086165100d1546008031071001c0e40b075403409007000c01e0011000c0180c44880745c0381d000745141050b0b40d44502c2d0052004d40004d1069021000308403061003d801030000c041a0214415424240070755103540c15050181090032590015065001321a0010031040905401c003c10003003818582d10450322140088164586d202a0660800f41c2c15100f80a01c901070f000420384140500a100031040d90380c0005040040300f40c00001804001080039004030b500010140d010f07104643d2055140880455109900941407080c0008400c0d0f042500c0280401155240b0076081e01134000d41d5190b440c0c04d40807441 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 644333354 1250 644332104 644332111
    0xe070503010b0f0121020c0303010e0403021c08150d0b0f16080108070303120f0c1d0109030b060603060d061103042d060f020903011e051f0308160b0f 66
    0x2079420901000c0071403400c401102c004080c140c451510540c1d0540341007000c2d42018030510080c2da42000303405149501040603500a2803c420401c1c00c0c1c1ca030600d402800c06410003407011191035042c016405070b50f04000d54a41c030082d00581400140800000185a02d01da8900541411044818809c03c03002020b04184241c0c00480c004800201540301169248000d2213181d0072604402014000607100310407030340200710f0700000401c0180620442030b01705c5640401401c0450b01d414800c1021780442d0b03028002c490070034200041d450386941c4440d1800312000b030074941b0801c00007001508945c0c0d8140070340d6443d5081075007000340c8581c079000c1c02100d030701c15101540c4190709000c000d99000410188440103500d1100281d203001ea01d47c0c0c604018100010b101e165064090004120b0b54400b442100d5014800341445101c060a4906090803600050080081c0c00202a00c509048410081c0307a0201d0fa0301c18481a40c40c44c0712100b0400504c8100d0700104102d0810050040c15900c150b80c0600 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 644334604 1250 644333354 644333359
    0xc310207060e030301030b040f03030209031c1202040806271203220503182209060501081218030c0402033d03020f060403050f06010f08010b060904021b010e0705 71
    0x508181c2d45640c0d659020034840204504940000100002c4d0314050b4111080c2c031a003009400c0c118840700007410448410484514844a1500c040c0311035071140f082100a070869808516180c2800c1c519a1074400c001c0403900c034288910b41d40c0415200040c40e09400d4070440040d07461100000e80b03013103041c1d80140d940c0540c12000000041c81d82c2c5070042002503150303010300110704d0300d512420181300c0074403c0781c40e0641c01400c0c245c00850b01310540e541410651240c2600082084903443d00004840041c1c1000314154480c60f13041c111781c680fa900f250304040840100850040c040d00c0064500800300006542060000c004c0c0011800104154202c1016485400b5120075500f008442c005024042c0345010b10110781080001d42801440c2000c440b0001c3e04084c03030240c403030b29924500003800d001c00540d5030010300100301143c030a044100190500000900080301328200052450084c1c4801c903208550000b030311030060703010800141c009100725009110419003682915104c2856120390b50 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 644335854 1250 644334604 644334611
    0x7120c030909060b0301030609020f1507031101050903120c0f04090e0615011e091d1012051507030216030e03070b040509010303200307060b210c31020706 68
    0x507551255006600030f584d000116182980c5c41c43e11000003500282c1c100fa42c103d5000005540720740c8803000c2d9100e941340c18110f240c0d507464052500030311400203510b09104992409041c002c1e9024040216458030094007440380c0181c90b04400c6030900c0c440c401c2000340818002900040d0400c0c1904510355900c14902501c80e16070b100c3c0314200b201141021001e0000c1c4100e030b451020755000d84c44021585299107401c15860740ca4043d11104850600440040b00e44841d0400c0038282c2810208005090300c8008684a02442e41e90b00341d0f40e5903901d424001c2071501c03a0015468902c039a054503185400002c41480c2c40c0c0381401d003e00802c01411850b8040c0c06000404100c50000c070045404035000506604016860340d10122091840100030100c404111911111440307000c00203040824042c1170002019803410b0100b203100724070164148444549803070b00203414140440e00c2031030401c0544500d40003421100889036020700c90b540410080781090350305440b010703166010300615441280c040 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 644337104 1250 644335854 644335859
    0x2806050c0306090c0d020906030114040b0604061403070318030915030c0c060b1534020616050c06040807050906030f0a150b04020a080a0f05010609120807120c0309 72
    0x8803481c40111840c607000101c0364003050f01e819040d8024070301d82e2404c0340c0c014148598000000c00c994400c0e804013611082d4090412560703e050300c258a1450022240580b03418036240002d0030b0b0034a400c02941801c54003000040b203c0740607401c4507210006c0388007202401c450a10b405400b130740d6103011f1a00503103070000999181078001e100d407010203000c58a84011401d076656071980942104084141c009056045c00c014992403c805843c02c5440e80003800d031610023048480c1038030025040000c2c0181c07506c060410250705c0340801c481c2025904070b0640c51402d89800e2032890020071201613500004009400203c0c900c0204000040c0e4808407245516030729404209079403503a0b1a8495800c070707007201c1080c0000540750b00050141400746140070800007031800005040382c1201c1d5000c80815078510400120101910800d11000316080c0108029414440010401040c0740110411403400f20003100c1880b48140503101c40b10751040502c008a400e0030001010902d04000403004100e4a0901 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 644338354 1250 644337104 644337121
    0x30212090f190c080303012304060e0f040303060321020106152c060403030e1c0506220204050a090c12030519031401091a041b0c0302280605 62
    0x40c1e4640620314000c000050941204400c0340141500456910386034020003d130904040c0080e500902c0c0b00064031a0282d040302401c0a0904030f41c40f11440346d89002001d1055400003e1803542144e0161004071701640c5a2906a00400864101030314151807260f00c403518540c070709800c41036501198001e2021780e550700c0e28410f100c440c501003080410140040c038440394200454814480034843c08087c0c00c1c206080100d00340d588140c005400062024a41d0751441c20300441004c0c020a12984665241c152604c4081c1c0712030002e42080100841c003080c002660030101380c2d1008094005204020758204850b411004040c170300310848541504020024080303600284401501d60503490f054a03080000c017a00c041c000c1103564040a05a48940f5200c0c141e40413901f5a002c1d115890000460445400d40a4011100c144205202d24200004d011480300c007804001412000360803c00f2540c01c280c0303010703420203500410080800544207103841b580364030447e103110114040c000402942d203d6420 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 644339604 1250 644338354 644338363
    0x709020906030402010e0a12060219050703020d0f020c0411040312020f03040905060612040b06090901090807080f0705030a0f0f03050f071103040810090c0501030b0a0303120b040c03021209 83
    0x6149901c00c0c0c0a10000e40994000d40e20002c041400400500c4103030786401e038003000fa000b0a841a0341c961307070114901248080a5080a8400300359003000b90070b11859940c0256174107800342e0300c60200220070b50041d0f0801e008106000d001c2c1c400400c2840070315481240c50342c5c0d80e0003d210954040d2a8040403d006500100d903182d4010024000342d481c00f03040c013002c01d01402d0b024280903042503080010064110000800d18001c07031080000c0003190a201d401c10801ca00e025081030102e91500d940c00e0700041e219811990320f1a0701c4032185484510300c2070340e96030724014000041d225010010f130844c400307548440d00d106848959214600c400c8c00385d000c03c800312102100c242e0342c08864200859403041c00b909004815504150840f0b25250301d4000840c10602d5595415441c030791100385c110704100d80560b412000c2c000a203010000440d201000500f407655511024050101d121041e400b44005908039280b4014094802e00845a9420780100290300001d0003850484851012448103080441c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 644340854 1250 644339604 644339617
    0x15050103020f03280c03090606060e0303041701060f1503060f050a1211120c01020f030703140703180b0703030e060601020304140303193f0b040e070e0603070902 71
    0x1000e04569813120401030a5500c00c0c85030240b03c101c8040140c4050f1107000e17000d03c820060745c004c202101c1a15141c01929115048070041c0b00c401099590070f6200002680d040b81d600f480d1000441140910b12801410f898200030400b07084c80d0404101c43c6c0800b54000c07400651654100500d50340ca6412005001490060940c85138140a04101d0320442d07902046425010345040388640080e030001072015200c1400b44411600210032500141da0180001500003100c0e2001e0352900c103e41c0d41c014059030303103200240c00d07040011034032a044c07600c26000c00100a8038800c040b004681c0700d00d10b121054004100850000e8200222882c00324004280326000d04010b07002503040c2400c00f580e03100f003151034111a6406110500081051030b07038203030400032140080e840c0c50908824010703407024001e00148080720a58003a80c0c0c0c212507130140fa121072082050540e030006807904c0100004020f09200d000000d5940300300344021489038527280105000b114120308032992280c0d5854080300748e000700d1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 644342104 1250 644340854 644340877
    0x2030606090d06020904320903121e09010209091305070302130f050a06030212031315090306050f0603010b0315060607230105070f080402030d0c030e0406091505010302 74
    0x24070244a49041a002890046100e500094100449540403a080790380851108580a4580780201550b5200c0324400641030248150100d603840c4c4044007940c0c0384100780c2e0042c40b50074204000360b038520b0250750700c00c0c4c1400b040015148509080c400300707000c2d4006ea0318051040d24654041006242c4140c8821811503210300605651451902041116840280e40e050001c0d1155040c101102c40c62003424032800c0d4680380000d5490841c014040c119440d9001412158802c100c0d2041551600407010111a121100c072421200b030802e0844140140b84e00041c0403a0601d4203004130320800600301486004150300804c035030003944042650305c2030780e11101800311800c0070214205042c41c0004007440b0340640c801c1c0c182101a21540c0c0112006240040b242d655180280040d59500110000d0241460320303201600341081c0e0002611390101120706824460111003603400c05000d10512040090000c01c20400b441d628403508024045107084080745010b0b589000c85c1c550300030300c250390500150 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 644343354 1250 644342104 644342107
    0x1050117060904060b0103150f0305060a0b090a050705091206090f010621081b0a0b060603190e070306060b1b030f0306010f021018120903150f090804080106081002030606 75
    0xb951a400300030401818003c0c1050340715520000b81c203565030145e038000e0030004400c02e0302031718500781642810cd0140100341c05c0c50a00b060180280c0e241004036820050107280000e0517164210295941d1250790200740e00401c03801c20990710703100c0100301c50f813150002405071440c001f400d2120034200c07501806184c40041140c8844c2164540440381c04080d1032050b5900c45c90308580e82a820f110421042045102c0c1c0c2c8030070050001c1040d103100e40c54014005450b043c0c21414200c0042203103ca8144d2055416070740d90410100c0300804120000007150420b5080000c5c94423006481040c1d8455030103441c0c258168403002d030015070700001301e9180141e2500c00d181152070b488011150a0400310984d011403160030404940d4104900c505403000d0340f01440d5150f207a906190130082840141040014040f105500f08040f85c06019203908000b0011b40004042c40110426402020104006041d80700f0100d408601c0a805500510955500504486844c480044d070305040e84400c039111034000d01c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 644344604 1250 644343354 644343361
    0xf0105010e0f090703090f050105181207020307231f14031b0a090b0f2802070603200301030605060315070509011d100c140a0c030b04060b09040803010501170609 71
    0x301751b00170460b03941300f011100c401102c01e40300e00342503a006a40f1141c910401804220304450100640c500090703605040a0601c45c0740e80000f525581180b10b48258030081c240d0340450145480180e40000400500b0a0f040c5802a8044807900c2041040c8001203411030341d8581e9515030800644c2d04c0350350b03103081401900b111081d903c2c0d02a00000c01580a00540940220314000400c01074565803031004007a586918280c0c10100130b120b500081100f008050003d9246004d9020603038006403001b40c01d000c104110310b071075a40c100c8030b83c0c4140ca00c0155030100001c800c109464011a004802c210304071150b8007061301c001c1510000a03203100d400b040302044540c0e01d5501990990901da05012030014940c5e10150200b12010142c20046000860b1040502d0402c89030780e1a0950322003044008010609403a5503e045c0102c00740000791100d01d00e070f00040e08100307960304105800980500310280504052038800415002070040902007043c90b60b2404031542c110a0031841040000c100b10113030346 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 644345854 1250 644344604 644344607
    0xa060819050109150e06010501051801080c0d020d05180c0127050901140405090105010f120206070503040f03120c02010f03020c01061a180a0602330f0105010e0f0907 73
    0x50a000d011580ca5480703503068808101020044055201c107140c02040348049058881d00b4003005030052414000103108030341201100c10b0508005a03400e0a248502c0d49440c40344054501030340c01900d00700e500005040e07240e1591034224600640000c01807000325040e003070466444055033035055000802ca00c2d0441c4113106640d6240300141020100720890f1a1544003040c8964006d030814404100c040d1030280c2241028071031942d00c200c404000b000954140703c4907002030411849114441c0e003901c111082596200d80c00c4490072644202269981c55440b2031606030312549100581e20300d030410902d80e010902485015100b20340c140c3d600c21501c0c05600d8141c00035000f80c0c4010040790360f6080003040114440394000303501400a0b51f06901e514690480c04520b40e8980403041c01546ca0180404c103c41d00001d155041075090f0900c9110180604c06a000c2000c00441c6600e02040d24028402100c00d0014114180c4800380e8a04ca08164640c0070300c1481a4041d180700d4020b211a0300140d0080e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 644347104 1250 644345854 644345893
    0x1e0c090a0f0602121c0504030c050c0d0b010b0a051207110708010911010525050c0f01020703050601090c02100507051b01090201080c130b0304080a09120c15141206090a0608 76
    0x5440d10240660f10818041e4000850301b04940403000326100031030b92001d014081000c0c2d10350507002c455207131485026070303200c0366010010300c1240c0700d02c000802c0e03ca100e24000c20035075804030046006112039140034800108000e80b0280070f07507298003a60001050880d8107000c2d1100c8150010b040d103540050f070a00444080d8031281c8421910390000420800c1240400f140500c0240104010311311120395404011511210408082c10342d0b01102e810000583c000c562281181e10210340000c07012070980c03040e410586206101540c0e1498241041a4641c01c58050900001c4402d000c1c0c01100a5480860032503411800180c00b0640e24000220319002090041c2040840032810080e003954550001d0b074560800e440480740c0500c00b14014052590043c003807402002c0030583c244844d10380e91908503061050707000e003e4050508000008250380100000d42c1a00c1e1003000c116660103c0701c000031001141a0f90301c80c410310303405010401d10545030051205403074000b406094142d4954041c400074 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 644348354 1250 644347104 644347117
    0x60105150c0309101101020c06011802090310020a02030702190f1a0304300806130603020d062a031a030102030709060c290f07030507171e0c090a0f060212 68
    0x800c00c605c98003d07000d80081c000342c0002c2614230020810303075041c00d0200900440394800e040102c0c0c8180405012960b0001e10000c40b007900c4240187c1c2d55040c1e22089046201e10100a90020181d00343d8161a20f1400f00250072510040c148014840d15004a07038141141d18000c0c05034143d040c0003080208402d40721812075520301d03884c08072410a07019100b802c400e1403801ca0101040c818010044141032902d100d00c801c4038a0002040f00314203560010381031081c8404050600c69480340303120b03605001144140c1c030340ca41d842c4400c0365075650700c20010082c2002c03e2040b0140d03003a1035a040e84508050003a28021502901c1e01881c1c607040007411242c01c42d202c4010b46440e04020b014004d41402400205c2c15a040880310b50850706e0030f41d403800700669001e81124201841d100030030004a078440304004030382004101d00700e003e4070b481041d072a480355103020544010700d100080c400b2645052004010a0070705440c1c101c6039641c1c40b8807000703d82406204a2015801c00e450b25488003907180003c111 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 644349604 1250 644348354 644348357
    0x406171305010e030714010b0a0e0901230a0c0c03050a0f14040b0406020d0206060a15121d0c03211303080a0804060b09190f110c060105150c030910 65
    0x3002a00c9455003400d46584480e1210340c0c0e00005003e070140025000c0743e000390541c1100038800401190007141810701588030380c4044100388004910f250800790481d0003443c0c03180a0085141c0a00c100030b414544040d14a050002d00c1e00c1810708855000e410003551450701a21807504020200d44180e0392403a000c1c9004040020012200c203c58904002034070282050300526a00c0e503003000b0010380303045841d0510100750f6000c42c0400009651b01c031204003d5900c10b008201b040e119004080c0c0d1007003c011794042d039203820308080c0282c5c0c1d43c0c03010200d41d45441d801c0c1102c1a203120b400c00d25840b01c0d00c4511209a00306a22210300d0075003c40d9005083c40c15050440a001c15500d4031151944d8010401101c0040d00b44018002403000d203001d00085041d0403036141e6510304004140706200610364011424180d240c0c065004a500307603034070a500e80c10070382c000c030f42d603461211546039207031002402030324880c882014002c0603c010f90b905844403103c907840210303c0c1c0705035241086000c0c40c152080341d0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 644350854 1250 644349604 644349631
    0x108130215030f07020f0d0e0f0904030309020a0b0901020624222a03050901180803040c0605121506070210030c030b030d05090402030613140a050c040617 68
    0x240140c80d01880349194958500c4900c0c0c6a0034207008a00e01140702400e80021980030902d506040e61001c10446054281030070300300350b010b6a24000c94001c98611031140e510804a8080100f032607095005428028403c0720f0802c1000e84500e0818114042c40352a103006901c214005030003241d505414401d104402c106603030b40f4840000002d10b81841180b0401035285041c1e9841010075414000ca650b04e01c00341c10446151f0300d905c1d0069912000350b540030410180c41d140800c2d40500207600c03d466500460020091f5140b10741401001d607481503900f00e884110207480090403600c82d6007952441da8070b01a5850079525a0242c0c140200100c1aa0036800703030301000014010b0740c4000600e23400035042e032404548041320280150482d10100c0115003c2d806c501c0080302480d030700c20122550075000703d400580f21707180c100124a02c2e01400c20f215040741d2030404610500f0306840c0e0780c0c0c6c2c8a10150041405180d1322403c6030880307809140b00ea01e0100d400c401d40c42445009a028103075000c0c85140e64007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 644352104 1250 644350854 644350891
    0xe040e070609090e150c0705060108060c0d1d0f0a021e0901051306090507090608090a050319110f030702092a0705161401200d0804050f0f0d08010e10050108 69
    0x82c1e4240d60560304451b0300c500000308981040300070320410b80100040000780001c1c0c5001a00c05c50b4501c074011035020100c0d540d98100303070b1040c520b500040100c00004103c801c540700c1604040d40c0d4100c6403000f03a10a1901c91b0065000d04c20504910032034000182c0944190b0740380800380701820748a117192422660300c541c408503940e40d00e440340f84c0c49007102d65902c0301c600e07103811409444030340d018160000c0c1d0b402c940001d4010070000411140038402250814005622118085410081d8450000614000d244081c90b0000c800806003510ba070088035544039544628813041d030062400741d0316610901400815840c002e091502800303580d070280c4180c500d00d419640d5080d103d18120b8000d08600c0d04003045070042d5590200c4100f40b00703540254581e80d14020803e00301e60b103200760082c0b1010000540001020040c06000b07a4155003e244103d60f41e48442d000d404e0307101c8109906000000741c05100004968181140513030145170364120000480b4100350046400d80401465000c1769215840e03403 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 644353354 1250 644352104 644352133
    0x519120201030b06070b0420030d020a0326040609030207060206011202100c0b090105190b0a050d110312250807030e04060807082d1902040f0c0e040e070609090e 71
    0x12036109611582d280100400d100310900c0407a8032304613201d03000f42e1002004008840c2c000481d6010203030503080c201288201c03110740c580078002c50880c12888500340d405004c100285030704260b0889109400b42c40e01183c86081c220303a514801d101c0da8082440751600c10002d400c09445522050006107031020040309180c845044050060b5101621030b9034802c01c21846802c10740300c0f40d02001400f203007808840e8030400064650920340c0540d0b842260480a40c804003d8400c2c00d01078074400140c29240105440b0300200f0094202115545441402c046500d01a16002901c036024503070150107503050034541d80f42141d0604a103c002c540051750351070080b586450400c000d2004000c0c0c1c3c40240148503110b00c4140610f03640c070402c1c01c0504510f00c0c071034450040c041605400204800f5261020342c51500014018004e035141e9800901e15000b94107498a034804904950b4800c00d0f1414801da00450304129583c00c0c1c90b11030840040c00740d803424410309000b0340005400100c0c2004880c22030365400d21 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 644354604 1250 644353354 644353373
    0x30f100b0714101104052e12050105090c0703112b03061d010b2803090302060906040803070507020d060204060306050123072414010519120201030b0607 67
    0x7070558200300d0491964038000000c011034066203524180070300040511a49000ca0340c051400b4141c469a030050300d4412001c0441402a120b18524012401503185060080d0140c48603004080c01e03181488004103040c100005950301601e10700264510303088803510704036001c00e040a00201d03036002d060100030307650381822000e11541c280c0410701100010f01c80d6010307089030340c0d07a8040c00c0c0d82c4c1e502c0c0f43d103c02c3c50f0b4045a00141121200440c9a0380d5130103c04c8000c0900800c0c06036900500034800480c400a83d240d4418452184240c0854a05803640345086944601c203e0300200a43c0041001602d004e1185000d4201c0e03500c080c0c41c40c5100700c141d6884c20305a0304075400040c00a80d487c0c2c010802c540e8000804400c130415074000400d04900c824501720148600340010b009000069031034a604020b580b54249a020725400400130a10000783e4505048400c1c41254031504e00b8006c81d505141c0040c0b101e504641080c40e401d008910240c0c0190b02521807560f0391548400144064000f0038540503 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 644355854 1250 644354604 644354617
    0x20a0b070201080a0b010c05070e01081005010533070f0210022b210531020d0305040b03190b0109081903022d07090605100c02030c04020f091e0105030f100b 69
    0x4658152b80d03040c03190301c0d4a00070b0b019903004025402c10b00100b290340c0782c05485030a12101c0d0808603001c0c6034018040700e1424245004107500e80c50000e0300750705209170a101424407900c01c85508500081954040303079600c0502081041140681c0c00f00c0070132400180c100304072159681482e4100c07c07104502c14204192002200246036202c03010003003440001100811503450318082c4010f000c0070403160884805100c20001e005051018000d81411300030400e950003400c41c41c94096583c40c00000c0d44001d0440081040c10050400044510541c043c0c80e618003514500f1000303003400c10844c1c4e002c411410300c1000a07030540c0500d03251141c0015050f80c0b801c0030704181985021810603500c10b45803030710b2040c0d40300030000b5140000c20701013680c408500d450a8103181c5000130644245000090a008603002095800307880000da0030a5000b006015111302c4c3c004480e51800c080c1c0d0ba404942690f00345c4c00700d160000390100005015010511112500b200060080b200361315114031004044d81e1000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 644357104 1250 644355854 644355869
    0xc040c030e06060a0b2d0c0a05100209060a030f0905010203040507081015050d1703011419030206071509020307030305030a1d1f0b0301050106030207020a0b070201080a0b010c0507 79
    0x29a103120034070354200401900840d05507400c94200d03103020125100c030300500d903070620f41c0c1142e900c411039170111028604403040002e8004075a92140180c20039900c24125004613414000d503a00802d0104540c82034038200341c409440145002603242e421801002d0035045070300c080d6030b200c440d08013041d03092001d9881648284000c1000c1800d081180e0f01d48203904d6000d000c2141809080d01e041c000520450046a100307440650181000b40340103000c4034031201d600944184044000146e00c02c45005900701c018068640b9407041782c2800d1001c0050700f240c080a0340018082000740d0010b009a4100780e0882a80c2c880010440c801d1b50029017465141c0d40282c000034408010700510307490522072641c0c6500003000503220003c500c152192110050141c0702070314182e008034010302c01403030b4004d20003a0a00400800030b560315403102038001e401400c0b069020f021500b034007150880b041001c03100e545405840700c01d403070395a406010015001e40c0700c6a034104402c1c000c102c400139504010500181454 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 644358354 1250 644357104 644357111
    0x5070302010801080c01020a0b0403110d03050117030c120901050403060c05090f010f0c030e0a0b04080321041106250b2202060f030705270f010c110405090c040c03 72
    0x21800014100d000c103070001d5141703820071445514542c0c3c0003d030703000c1c04d194890021002036580b8102528200424181c0206a02520103405202945548080d0690310104a0340003070003680e01505540b4000c10340b681d01309600060100608032210b1000e410602030501d000d500d0b29403079a449405840c0580c40400129201085404071403a11294910205e2070070300e01300c409842c0c2751100800c44900c08074042c060014425694060740c582103e0440038006152120346d8035a5145822640c0e1380c0030311550152039582c4070300c01c1040e1440410041c040c84d0859480044041110200101a0310643c41c40e042c1d03030352644000441c840d00a0200414078021516100d0520f8000d00b801c00340301d0034041003082c0c0c0d4a0344883c80d0040e41e0318010303261105911303800d441e20b0707503107840050b5218810780014264940d101d910030034070201203507502e03410368005994031030f031880c1c818005546000920358010045016103050cc601400c003a03105552004001045407020300810380418110707504d800e06500003a44 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 644359604 1250 644358354 644358359
    0x108011e080f06090c0f03100c110d020c0a0806090d050f04031a041103120a0804050115030f030f0305060d080705100f150b04030203031b2e052809020105070f0507 72
    0x5060005039080b2030301740e60680d06c0c40120750001c2c0d01c545554200250a590310003401800521a180c06450911950112280b0f484e440601075910701c010070303584c0e20842c11550080380c039110100d440380c0541c1c40c1c4401482c0440f038110007640e06070040d900300314072030704180070000100b5454400a12070062060b00c0c0307991410705080840101c032001c020140a5408141104210f001c0003040b00c030300c40045c3c81e2003045601c442c90900d000d0040ca40d4003149500e45c2c407001005002c4081c10040d00644291540040214081b1003034040e074400b10350340c0d944010048e45000200c5c859500030b100c5240b08500707813030301c52070300700d1a8008484210014510140d03441050241d0750700250002d00240c0109010141441e00e950b0003e0782d40d00c00c454180e5000c540c0c49042500f030210800190a066a10701580071801a48034003029245070030017401a1800e04200c08282d1320025076218016a0640085041c403947c82448007102503c10030800b241007210800081003c99210110b0004a6104038040e0100b01d2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 644360854 1250 644359604 644359621
    0x10c0806011e08060d03090e04050102040510110c010e031006060e13060b03010302150c071508010905090706050319050a0f0b01050f0301030f140a05010606110a020108011e080f06 79
    0x400d051041940030b10080064402c1a0000c407520b500180c1101d81c2c844440c6580350417a0954955409202e11071604d00605c010001d0640182c002e070b41c130986440100c4032000108071011190503809100c0354000741da5108841d4803519070364140c1c0402800300c80000c161108108119001c940c05080001c48207888051342e407030710a5099030720780800082800582d09003003490072540b0041c40000c3c41008544d0040b440c0e0111041aa8007000c003000c01d035088159500300d048228407050070340d88005850309001180411861203414001d8021318014031186090520554042d80b000c0c185030703021083d8900b510b507004198000e580c41007000d4000400c81c1c0102381d18182c19075568010541c144002880019002d140f4902660b0440c2c0e040720075404c0c81401f134103007003254680090307200c1500e01500308a04180401500071000711226aa644c80f0b20810710501c4a84034642d556000340000c01d0b003401000b06002d0705114504100c144440e6001241d6141401ca00e8101c0826034030749542c00207020044001d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 644362104 1250 644360854 644360867
    0x3030f020f07050d1418041527050609240f0a03030e03070605030c030c0d0207080706090b0703180b220c030b0f0411010305041506080708060c0a2a05010c080601 71
    0x150300c1117022414131118203000702410b01164586c0c2c4c040c503510f8500703801c03181c400040c10000300007013007110440310341101c0d088406040c0044980041c034103010204000d401d04003525845520750f0b0b112010000d03100820304102070180034629900c10b1609400c9803581c0cae2004018001548282c5420491520381020b05091144544c451024014244200b040c0c402400046907404100a4404d80d600e01455600e50000c0c000ea0030040d00700c2c034002c01c080d07041104039441100307003d000c1d98142c0860368801400708c050314821612030031104820208080000c000f56003040e000b000c0028000c012004005e5031109091100800b5203100800160420078072440324020345d04407140d5815101d20345130649400c00c080b04e80c44091810140e0f2440010b0500c8040e40d1518001040d81c60180001c1d81e68410550f524145401601100c0c00b41030045140e04c0312600071200c448900303460354841c848174400d410401d2400803010b40c0e05030980e0301c500800201c082c40f489d90b0402003919074070703114105480014290b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 644363354 1250 644362104 644362127
    0x30301060e120609280804170c0a030c05041e0f05061c020a06120f06031b0602010b090a0b060412050a0b130507031511040b12071b03030f020f07050d 66
    0x40707401002c1070081da03130b0001c01c0c1c0030000a00705440d0900078801c6002101c04040c8650090540c01c000304000c14103482440003440d0607113044040310040c4140b04101b0589000030300c801082d21181100c100841d081680002c10f10200350241c1d41c104e82510601d4809490442001e44181981c84041014a01d011603208484c10f000707c180b112244001d030b01043c04c0c01c0b91805030100744481100c280400d507026130450b0a0310841c03e20180318495482c9001200b84000c414030081d4000b00c0301000c03440320b02c14803910116060040055625890b00182c074001848200b02d0607800c07010030000071441c642c41c0205e07114554450740c010000c2c901036050440714082c0c003910740008401090401c00102c2c1001652400392500320016102d0014012814001032840d0b0346028420325001c500001c078485084043c00d0740c3e40d100d40000240e035603204021910100042e101c0d08410196182e50800729200740c0c00a07240440d002e43c01484c294004c500065035030807201040302c840d400800122001640130654428 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 644364604 1250 644363354 644363389
    0x100501060e01261302030109050d2307170d0c020a0308090f1b011e09090b0906090a2d06081002090607030305060102070f0806071e0219080f0304140c1c0204020304020a0503030301060e 81
    0x6202c0e00c0cbc0c103281d2051080340409068a04003800ca007002c003101c0002c03289644e4000c40204404150450040d440f050181800c0e00410b0950300083c017803243c041001203a035025400505107103000250b0b001c0c0001c92000f1300504000244003000320310301103c1d01d845004465a1100b00300d9070300e442c40f800203694000d03510038081e8214400307000450300c80522058100030016404945101000c0800502081e40030403403901003c00c110380c003000c85055120750b06030b42c90103007903132510002c07402118140d02c1030912590f00101c08101c490042403295200740e420210510588e00901d561f008104802c3c6036681041900d0b0700b02e4806d0080ca035420440300d0010301c09102c9454040003000c14041c1d16a241c40c401580085c000c6140182081089400c8030040d10400500940f03c3c20f05040070202100030303580d2900b1070b104105a014603443c0c240e0440480c89071070f52030740c0d00d00313242c95082c00060741010b00100d0701700450700b101180540d001e00c060350107411180c0e103002c440703c2e40d0820402703d08006041101d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 644365854 1250 644364604 644364647
    0x1b0b0c0f1014041e06052d280e030f0405030d0f050d0b01051b06220b0c0f09181614040e18100501060e01261302030109050d 55
    0x256521048a500d0340e01c1031308030282402d8031203107442c10500e140d000b10380180803503c1c1108128030595201c043c100005045401601a159288202d074440c030400d4924408500c6042c201300e0044020b030f1f0a2070f42d0b21480900c049010b10f2290b030f50300c4c5140c000d42440b000c0f0030b030089800e100300d0500f00403401c01c41115140c041c110811504018007540b24408140501c0d98580007a407800d6406003044499101c00c1c0b00c00040448400c000b51030311362030142c402648082c0d145004448a28400b4a02001950007590410103615450b0001781240d0107a1381025042800b40031490321a602c0070f034450202e44146015050514118064102c905d07880e01e240814050140c0060100006400590b019030300015000800c546449150600000c101010f100c0c0b107200b40080001650456003000703049034103641300d00242100d0080107603002c01411030656841c0911055031300e80d00d529620070a4006400b40c00d038241d08056900440e00b9525a01825200c60b400140d480801a0f030041a194442500c0803034403 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 644367104 1250 644365854 644365871
    0x1e1523090106030e010e240c04030b1909120c0b0604020c07050609060714010605040b04051e0705091e0f011407030c06020412050d030b0901121b0b0c0f10 68
    0xd0181541030159a04240d83d4544905060509600203d00d19403200f040300c015040604040b5010244030740a0030305480d400d0003080c0100620029242681d5101c40d91000036901d0000401c0500c940c12008542d05072500800c4010484075014107880096513078482000d40194100380b2201d0fa4040d04681c041c0d4070402003001b480a0100d012820b03164100d411554035107035072000401c0c6010300c041c00f0348601e8101820010510055000790304680007502d050002d1100042084100c550490700740f5403408e40c8a0542012050361840240d2050b030500b4102d007401200c001140b07801c0c8240c0001d40071001c00c030b045e44040349410807000c1d5591500340703480e415803241180c01505078042d5020050501c0103624001c000c1147e103805480c05440b003a00035485458643c103099680d40402c2940c040840d2410911000c0c6003040e040660503100c0e0b43c8548450303030030b00741e483e820901c200b004601648161a00c01060203c40c040003405055800c000400d0805000502141842060200b503106140b508000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 644368354 1250 644367104 644367109
    0xa0f020f0a08030901020c01021b1902090a1d030a0302041a0a050406110703020d08040e06090c090f0303120421020f10021b070305030a170402131e1523 67
    0xc0c0c001c4642c4804001c0c3c807900d50690590180c0a0000030703800c04d5001040c164501030031a0241c5942c00c0d100702c1100d014003400c1d0600c000c55020a034010f904505030000044152802d904072035500000750320300c030341c03401c00c516111405d5801007000340002a030005010404100740020300741600e40c0c94602c2a00e82425114042d1892003240705100500a1072104012003010510840004680240000c40505407601c0d00714250340c85809203141c10f00d00c250120740a03041964100e8440c4041b424207501d801d208608000382c40c500c162000b9031602c020402c5942801041f08141c2c0503500c00c0401d00c3e05031800b101c40d214400c5a8030304071411035000090003410320000040c2125100300441e401071742e540080074102d0b000030a01a600c006c9110710040002001000001802403180d5940c8000c0006102e0190314071080c01514007a42c400380004581038440011f500c802e501c002290b801880503c0400481c10940d009003403000c801d4000c4c00c0c010054602048040e00c0c1101e0840c95080c7c035080030000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 644369604 1250 644368354 644368363
    0x61509050108031b150c0d0c020c01090e0903160f0611070b1b040302030616030c050c030d0f0e0d03050405010b012a0c1a04050a05060a0c080c070909080a0f020f 71
    0x200ea03402d466400003244d0603604107100c07000744418040c00c00a058a44181c9461442e4001c030307004043d0915000218118500c0401c81584071181659003064a0b0f04e4200c005402103005481811140410010495440240c10341180213911450700c41120391a282003180846114440b540f6030325a0800c070791400903030b00c0d208240d400100c401041d00c200c01e03e0380d0401c00302d00503a04029014807403c1d041c01a4903141d01c0244a510398656402d00c40045102d2044078980107045010b04598424805000130182540107a024080b6850b80000c0d100f811800070380c07900c160000000046aa03800a01003402001e0040704640102820045110141c544800c040e480ca0758002c4415a442e030340480307040102c1e4003a101300802110301c0b40381d0810314482c603440d6103a2040c46101d01c00c0c1ca082c0c0000a07241414000e4031103045840d01c441c602d0701403076150560341ba0f0040ba184801ca002c2d0100128074804d035440742c0c01d451b50040d02132641320402d903140079208031038000c0c1d00c3e010366108501001d1618030000b03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 644370854 1250 644369604 644369617
    0x61b0806090f0a020f07050309030d0f2a0c030c180204050d0b1506041d01120c210b01030c0302041d030307030e1005010602030c0607091a0a051606150905010803 71
    0x156114a940e40f000e0809000f0f02500403689442e04d00041d00b001032060000c050412079070110150f515a070014042170b41e0300840c43c0c4100010038600214141003040d040200d800ea15141100c1015010b041c0d90f40126100c00d40e002100d42a6030310409120022101004010601c080c0074110300e02401c100001d01c0c0f8400008006115201160014225107603000c00425003510103007043d40c40315168515402c05000e1180c9080012006000014820381c1c800b98561203203401003500a00306052010008180d10f2102185149528405044c40020010700841d4029409a211400c0d5181140f040001b40d84211544001d1601082041c2c10929408001c494014000e8200010000d18888405052131401e20744c0011045c54070000103402500840284180d002c813400303a54407940d4000040e10720f2619401100c40f02e40c0801c000c2404542d03124001d100410a6050843c00d00501201031003145c1c8103101c0c2120126202c06c000e8001140145a281c080c190070f16083c0034660402c20b02c3c0380d8900607407 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 644372104 1250 644370854 644370871
    0xe070b0319060807030f1a10061b0c03061d0a0c090501120c060e01030b030f01020706110304030207030b040c030b100612020a0e090a060b030108060601020601061d010305090316061b080609 83
    0x80d94030001c00c81500c540103c4225900200007c6185c0f5201d0162038142c11b1041c200465140021010b00071081c06070105040c0c0c1c0b00a01081241c1952100e40007818240400c58441c003142028168121042021000c81885030725010b01c214188100d20b01a24010ba1001c03c400d09403941c80800140d083c140c19050300c40c2e44ca04090504c25440c0101c02400100c9601c940601500c15003010b054010340050040b00c1c0140e0301403140c00c21040c2031000d24842142c003c1e005030001d42060000800d100809604203004000503581143c59840d0b89811600940317400e0041d840040c420400c0381d801403225400c411031a1411030a041004002a048001680d0703901d2142507040d0025050041d10340c401c0018143d665440c0b41c0740d40e10380645555075441aa0803030302500c5200300010320640b144081070152080192031101008200c40150301030a0040c115812901040c0310500c004c100d030f1001d01440c0d60050801046c0d08290b040464030014030b220818040103c200d04115090312a9040c0c4c9030054000d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 644373354 1250 644372104 644372123
    0x7080918090d231c0c0c0503070f0f020a062d0e1912081308011a01050307020703050f0309190806070f05070803130209280f0e070b031906080703 64
    0x1d460007002c0d44464140f021030a0b902042c2075042004020803100756000300281000082504042918a4480204000e101d035004208400000d0780042050015500c54502c1b5428030303c045c2e000544c003180b650440c50008010b10304215a0751600300d6440e10302111032542e95104200c8103070081000300c06100c1c0d0fa0045410000030b1a080c10213a201000428000c080c2103801c00140c40c082c1d18550007842c604105001c4000045107549040c402c2003034440507030348003403189500600150703180e81000b080801980680030700000031401c140010010191524081e540d1000c45000b046861111005800341c20030a50100b80040d840c0014016006110307418402702200f0b00c0f0808031102d100e20352000300610408014040315055030146803181e54405c8422031219a2404502c4c1c0d105102c0301035000e030001e0341d2051091040500d41c0020122002c980010401d00c0e0064002807600700329030310200714a00d001081045250300044141c42015200f00c05100d031514040030710703039500c1e020301016019114 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 644374604 1250 644373354 644373377
    0x912030b03030d150608090d080403030506040f0c23030103021507080f0f0310080a050718060806091b03120319061e05100311040b0a03020f07080918090d 68
    0x60030400d0718042154010140840802845042e121521301e1080c407022030b1515000c1018024082034135003110005548824943d81c480e1001c40c0540005000c0c40e40242d5154144014403145001c2c00000c4006601d0320103410384403910714100c441083d0f0074141003c109000510044e0795140d6a10032001d0240d4041e6101c88150900041c0c5108103e043d504005000072103904000401010b1440358990103203c00d0a140c0d0303003443c640c80300101d2034000d10326000320a0a1241e82080014150541e420000028000c6c0d2035a081900d800400d0300d02031866400000407011303090403080001008072081c1e0252030080c02c002441107460101404601000504c0d071400307841109144c1c070202c0100350305e070011000c0010039080d0302c2c1c01d4011400380d01e01800710101d0140320710b8007d000750507480c0c900350a82450a46400103c3e40c640d0084141e500c10107808000052f5a2070426003c0d0070507600562185a0701c18442e420008000044000044541c40000801c89003003408200010040b06034144242c1603413 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 644375854 1250 644374604 644374609
    0x7050312040c050307150516050309060d09020a080c03070b1c050f070201110f04272301090c0e06070c080f010e060f0115050f070804030b070e040912030b 68
    0x400690202202030318081200380441c0403024411640e054013a10b660980720000c0c0c4070b418201c005008041070080241d03080e010284900090480e010307a056a0410010000007101d581c0400c440101407500e07109564154500b148800b002000407a004141200c003440c0802c3d1219000d11030300008447c0401c0041c40250361428260300c40d0300c0040c0410140c90701d50382c2c6070040c4800703980c0c0000561801441140c00c24101e01251203030b60020002c941068174203228200600c0c00e0300160510684103002e2204081041c1c0501205980c90f10384240940840d1107046958410507070003145040c3c20610340e0b54140e600078484004201d02603605036521805428031622180d01980400c44510030290140d24029043d4086c054078070300300087d1211920b40842c1052210401e025414240b216560021981801f50004000782c801e8414014204890303501c40c881c2c02d4000d42e10641780c004000e01000b00d4580d00491030380321301c45c0880b410041c81c105504e45000600108511009040d40c84c6920303a10340c1d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 644377104 1250 644375854 644375857
    0x703111c0501020316030c0c1e02040603080c0606100e090606070f050d030e07051207090905070e0c070c05032103060a0b0706020a0e0102060f0703020322031106130215070503 77
    0x3070707003201c0299a2070502c50900c484600c895203907080002d10b80f003100301c803403481000004840d50b04075441030000841c403800b1030480a40528101d03402950749200200017210400903100400114020340002d240c60000c1c4050001c0543c1c201c42040403d1520a0140d510388203070b41d40000f01505d48903111416441e01041050f02c1da0005003540c400c0030540400943e0580000007080d4082094603807243e960310030301079080240e424014994016860900043d08241d100c0b04009020b0011212001c0d5620300c0610108002d0b90203005a00c0300040f00014400052141f40040405a00420044100ba0032075481c080b005940c54102c508000080b580300e69074010180098141030b800150b455549241c400029442074204001040c90b407200c4a695600102d10548507503141140003e040e0341c0c1d034034100c000303500c0100fa00318880c03440c10320002d501001808401082d0300c240c5a0741203122524a101d880d24100a10a01c8180f1400170020016120103a820010150189920b03403181d0786884d085045 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 644378354 1250 644377104 644377159
    0xd0e1e070f09091e050a170405010e190f0b12010e01080613060b040c120612030807030209041107030f090f1d060a030206070f0b070201020a05091905040606030606030e070311 77
    0x144d0b0b6800000c0c40700214201c5e07904c1e41b00e041c4610390343c28101c16100c8580100e104840c04039586e1682c02041e803e145e2611140d0003958010305500039100c864031141c03840e90782c110b00500200032a19140c40e000642da02c902500b101e20204031198035000c003413651968001c11600d64010380fa100b550402086800420282c2c4005009000b64041040c0003014900c1d000040109181005400944d403854a00c100d000381c1d41541c3d1700c04682d9181d04003540a136009034030041c0c02c255240410582c68124070043e0a1052080d40e4804440c404010028204401600800f640c50801c800801101d501c03d0031400c0b15011706808444591b4511340000c000e000c4941c0b01940044e00050028200300c0f03040c07102510301c3d10807000c4c0c03c1c03d070310b0340c2d0702c201c0c200e00070810f05d40041403007007000300c0d103d2900807401c00201d0713041c10112080c1d503281d10228094410030750142c00402d449050a014040d054011604440001c8006041c142e00d19141c01c05090b0801c5180e80c01408804248028400c114219401 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 644379604 1250 644378354 644378393
    0x32502071701090215120402150c07061214060109091a04020c0c0114092209060e0303150315010b030c0705120702090a021602040b060d0e1e070f0909 66
    0x40750240c188001e0281c903c80b801280319080f8156642003901c5605c0030350703d0780e80c2c0324084100030759916401e020341c40b00c6104955142000074080c1001401c1c08000301005021580d64005078804404140c10a64030b0602001d80040116404c000386a644840c103e8100c400800300421003407461150200c419048020160300301d0300009200301c1c110340000d800303c512203003039941c21103c402d0404503071040d0040740007040d42b000409a0200b45a280d20b04950f19a036522100003a80c1400d5a5500c0100c804055861074507070070110800203590300450f0015000c0200b94050300001340c000941d21041c02c030500843d480990048045521151144103580d4895070103011030b401461054406101c5801c0030034202d11401d401c10000c0c502d8540c81c002c0e5101640440314104014001c2e13420000030303148500c0181d07001703481482040c140c41c649005508481c00c1840c094101200c50300c10001210a0700140f52104d91702c140d40400c000b540070080c039400c0324017040700003441214500d400f0b0142d9548019446 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 644380854 1250 644379604 644379629
    0x20403020d0c030320120d060e0f01031e08070b1b04030b10050103062102030309060f0c0105090606090403080405030d090b1009181130060c03250207 66
    0x41008800040c0760180c0c1e001c0e40316a06200314046400d0325034094445d04c100d194204080ca5088440e801c405841c0074422500082101341c0c990703640840c3e908003240c2545c00b0004e000d004000f806044580006c203100d078800344500b28940f41c0c98840f200e200300c810040c40da8648500007030360692031141c600061480b0810003991190381f0b0500038003086003983c455600711020200090700d98001c1c4560320031079100020074200e502d603c0803411110381010800760780600041081703141d02c1d41c3c2c50f402004000340215030191141c0b1001d41650840310001c2228115500803c24402d0076603c42091580c0715500d0324002c0c106540d44d10f0014258003905490783c0c00d85040000220800c000c2840c407501c5840b460b032201c600c05654011200580d1011070090803145051802d11001c60b440005c9140c00f004090a808024081d12003e190140c080c0c240c01800c910048a40c00326440c1c0034004641c008160082e404e085080030109484140040b100000405107500d450000c1240244001c0c0006d000480041 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 644382104 1250 644380854 644380879
    0x1b0f0403020a0e0a0b03070510080406110f0d0b0301060518090a0f110f090f1b090a09020712090503030d0e1c02070501140304050c0609030f0703081b06091203070302040302 76
    0x103482400c019100300304c60504000c01e040490a0000700d000440318000c07c4290305001d032080a5414000117801034511640312029140d01c1d4111000510703c0020010751282c0e10850b0a03020012500d40c40c940c07510036410084100300707990350039a0321401c034100900c2d010f40981350009064501191404001c14079a4030644600a010380090b0b01d400c01034040e505040401405820030103001802c4505021680303149012681065a0b85100c0a5152004600720701d0180c000c00054428211544420111500003954008200d94280042d98004007810680c0480d03050034002a100d01980380c0e5035001950314440270007240c0d01080284400009071403500d00c2c0301034a000c002e4549000380a140c1c007151071880140c42501160b800c40b03200e103030801c001c1e10801c1007100400403940d10001d01e80e0303810311500000c80040302c810300a20008511400340580d542040d4550440500102603104100d50072140c10003000b40004140246450441e003000c59aa0751115000c1d00240100e41010f50010002500c1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 644383354 1250 644382104 644382119
    0x323010501052d0d23070f14070f0c05011404061d0418020102010b030c0f100e03030415090f030b0604110c160806090307030935010209010e01081b0f0403020a 70
    0x4d065500000006000d140d8044440310070030b104446245214981000c0040c52440c0314040a0008015500d03100720484040c1c100c1e040315810400b016100c0b106401c844004000b0107204500040c002824005210b0400755500c1415024600c0b070710081c8103650403124550314a80845e0400580b0042040105191b00c2c4258401100e0880301203015611301000c00c00c2c6481c000039049001440148805022103a0747c041c0600ca00d90120303100c0030b000404030508516074041c40a040a0444588031485189610000030154080786e401150f024034529400c0c40402c81100310380ba400f000a84e800f00d000385d6a248554654030455810b404a4001c2c4e100a86c0f9483c080420901120042421074000e0344803440c403d0b880c0d1080450090205902c1f036020442c004025104101c00414501060740c5003a05080c0b10205041c0750071118000e0350b000801d5078081d0b030070000b101c030b0310794083c80c2c424210f2a00361008140707840c1c41030407038140321400f10f0403107422401d180440303010f1980078001c0060f10360f94150 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 644384604 1250 644383354 644383357
    0x180f0604030503071715010909050112020f0a1a071209030314160501150e0c03250c151b020d0906180b22120c051005091206070323010501052d 63
    0x46d6180010035100000034421041c0c081d06051300d003c100903c54092041d820000e1304107074410004d4201911090000740c175000c2c052814003481440041560380c00700c42c60070121040c0150007440034040c84400c10b00200e58080e0031040d0781441c94440716510400c07a0640c18008000210003840e035804c06403480c2806050b8101c40048030442e0004000c0b940b62818401810b0108544154100c0f1080c1010b140604034210081e404004a003445202e82d8040d84404583c480c003100440020f60f1250102503907400135640190306c00f0310b5403000d04405400c1540c010300d50013483c81450100072160400d200007805600311240245030980c00c032603a035208151a80ca075003a1034564008105c0c41400700083e84503c0b42d061607026603007e041c0040143c205010081e039602c4003402001048005c1c07040c1a146c3d100d2421810103800b21740002d01051501640003420340c0c104a041d6010701c0e4040c129078040d041d41210050644200342041c54950344909108036a41c10000c003405000c2071401c1c105502d120300b400 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 644385854 1250 644384604 644384641
    0x20a02130221040f020d1a0a020910110601140a180b0f12070b030703140906091606091518090906060512030d0e0102130e180f06040305030717 63
    0x10b488101404407203103210320b8600d080b00c0c0540301038020100c141c01032070245000d2401d107104101a585110100038034000d48401103801c00c1107254001045845440c01c001da84212103040e180200c408907590404035210541841140c0f100e030040341458855590fa62001c0307015248282414140425005440025103031070310a95001c2d40418000358042d0402142003e0718a50810003041e0040c81d01c0e111400300d6000500850405640c2e980e146034110802d001d190154900c00700a1410341440300c01c49042c003442d203000745c40c20030700c0c003030104825500710074064200d038101071342c10300b00003c07412041e00c10000d24140c035403210380046400300f800c1000d135000302240b50191504101d03046e101d50a21440380a841520030040d881440325011071103050f000703003500820920025041011201c5032070f8500391141c128902e04110302d01040ac000000c480c02c80390b1002950014056000c83c04d10168640901910240400c00c00100103a0f01c18060110b4003600c442e0001000d11502d0417946005040c140c04 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 644387104 1250 644385854 644385877
    0x607380f060604081506010332010603051623070b0912120105060903010e070605040911190c080c070e061e1c0302010b0d0b040506100b07020108040201020a021302 72
    0xc000c2041c40c200b07281601d0a8a03503400003410500402c0b0a2140c600d0001010320341099280c418200c240740c000e01c40b42a021294180081001c110364418241a1405030098010940780204221104100c1c01c50141d20141c01c3c10211548841d10141c409584580c2c440c00c0e1074400b00182400030031405c0180e052044e2560003c0c1d80005210404044240c401c1c1045200841094030050005107040c5d001060582002800054464642c0d4542070a14006030310410100c3e8005c5420024040140100080d41c2000f0030914a071007004a103010250301580701d42803c01070b200400d80100710050b01140e0f0490404e4003201c40680e50741d41001113040d03080750314600800d03402c542400b407055802c014032000756004141003180050060f00d507241d40e400384c1e801c3e02150b40740c4903000196141c41d41d800c2070440c0210180c01c01c2d481c1904040d0305d40000036254005040000d60704001840d54502507c1c5144e509281c103003030300d496600040b4980890540060b500010803450580d0b0810b45a0040c4000004c8 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 644388354 1250 644387104 644387131
    0xb0c0c060108010b01021b031f1a010e2b1a0402040b040c0f0f17011401031401060f1d130b010801050f011b031403090706080f06060738 60
    0x210b0801d81c1c00c1e00d80162206026034030200745000c0e1000c0e034582665080740c0150480346000c21002d041054145884501e1448540d02d0201003030503007061110141d100ca080c00c2c080110100c0740b0220f15a00700585000d01e541240b00c01500010800c542c0303c1104c6030b00b098280082181c0703d90b0301611848140c40c102c1c0700741d20b40286502242018091584400c140c0d4907008031199208200392a880703981c640c05020060141c03218050b003811120058060701049403003012202004001404803035600b11030b11048100b00004021070340d40054540d03141051071811445d252559030044482e0210015000c0c1d105c0181e0b0040309a65105510403003155100341d0310903a0710307640d032400d1000b480c0a40d84c581d40044c10251050404e6401012140003080c440c1c5818103042120345803003c2d282d00300750b40040c41a000428200000f5034000700745a000018003100e080075040039400070301c0c02c1c0701d010380050061113071600d00c140045603990383c103010070a03111001319406140442c1c46400da004464000c000c2c3e84 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 644389604 1250 644388354 644388359
    0x1614030c04060b0702090603010b0622090e07060f0504050901032f0310020c0709090b25051b0a05010c0e240304020607050f03070303050a1404020102100207050102070b0c0c0601 78
    0x40600a16003103c030f402c00c01903d0600150203000c15858024143c03a019074035031107a00b070203844280c020002c541c200381a507a6200c0000c04000701285840e80b142d40c50b40c0c1019414905900042004000c440d11420040400650382d40e05803254026070b800b19074480c0b0400300000c144904402d003603042c545107a06025104a82c0c80c940c0003a9480030078059090340c071000d02c500300c0724460740c001c1c20008210f00840d00750319618039158050703e807955000c580d1000e00300b0521894442040718001c407008070811017001403102802c0107202e40510708034020304412004000c00700c00703010f12400c2c0c1002c1c1c02400a00040a501801030009581e4103501030041030701010803080900820b1000d0f22000b8001030151440e2583d40030400035410080d0199080d002e26560310300728500c200001d0074030310710a031000314003842c11072030a00c12180c134a5214041707a800e070001c100040c0c1c1d0109814101d074442250040cac581c203407030030003500a00840400800060341d0740240f1045003140f40242042c0e0a0413411100541c0c1c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 644390854 1250 644389604 644389609
    0x20f07091b0207060519030207060203040c0501110f06040809131505030f06010506071106121501120b0306040b0901060f03060f0b010903260c0d0305150f090c0901021614030c 77
    0x14110b10940c030000720103014043d0000140d481544114840d847e0240c144000d41d100c0308200c0c0c0c000c0d201242d5483c0301407410010342d6001008c910b425003854000e0b29440c0014000e040c0c843c1001000142200360016000c411603030f8410922a17480f035000d40070480c00c03544400301000c82c5c40d80d014481c403d20400c00f200180c6a070018500781030710805400e02e820098669508613820313000c200369030b6005006026131042044018021842100d40305800c0b0800100c0d10000b4201c080322901003d880d81c2446000c10302510f0008550745c1059001200e40e101c1c1e80e450011030b00520054204000707042d129140002400346540107400140415402005044162401512102c4051000a002001909540303000d0905004542000c5440c05195441c104842a00c0d90030541b034030202401007903441080c454980007515078a01c90900c190342d803501070200300c400200039043c02050144007500c0060690a244d10a000d840c04420300d150005030003075203c401e460b050411b00c0f403800c0c0c0070703100309811441c1c01d1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 644392104 1250 644390854 644390863
    0x504170d0621170c031c06090609050405031204020109150c060f050910110904090f06060b03062224061416080d06170307020a15050910020f07091b02 66
    0x1a407010400d900c2002483e050700140c0c2101d080b00003640000d2014150401c80d01c2c1c00d0104030b4545000c0002d9440c20400810101c44603500a90602c0703107003008100001b00d000040f14a01585400102034980d16880102c0c0c1e4031145801056800402c6c680300c041c8190800d180075200c6100c1c0c0001d10060303403603000301380844e1021074910f10264442801b000e201c003c5a4000c40010500c0401c1d1031034902203a001c50286e941c2c2c01d000703d07150741c0072910b4003042c0201881890060001c200c4854514240000028030144006642011101c04007491b1440d2564a81c05104242c03003d0031102000c000161324000300c92402d106c0c050216140c51a203511030800002150400d0030b20440080a502d195141d20055030070002d5890744566603084040b49403039280103101d00500c2c000d002145d07104000d106001c44030703184e0303885060507040c1114001c861603000307016520b0313810f001d40340706803000c0016030b040b40340c0a6076119101c6103004581c000310b0840c0941c0c00c10b5031004051100c0700300400032a280cc030b945 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 644393354 1250 644392104 644392169
    0x30606030f0d110a061a12063d0e040c0e04080f031f091a01050405060f09180a050103030306050f09071211041205060601080411040504170d06 63
    0x5402c011940031000d030103618104410ba400c202242d140b691190f40d030104544400110307070b8051340c5880400c4254640680650058080d180c040c0609081c01c2123540c5040000b610b43d07209101600c0b0441e441200c60480220390190003070b030803107010b42c0e45010f8608410000c0e50292201d40c18103501090810460140a001c0c56106043d82c6c0740c540392001e14811500043e0110302552482d003807268407030a01d040040040e0215180c0000c0246409020040888803480800d042c80303410311042140d95190001e43e1144c00e145010143d0755010341000602030314144445030100100b580a21420b07101ca03030301140c180da02c00c1d1000c002c000d482c2c904000b5165064124140d00640c002c00080f41e103845003c451060b526601d10104e801140141c5101c40c981080d00b10401030400f035402d00040c4a800c10903960054421300704410982400d0b140c044d04034001c80020b0f8007517071300c40b40807400b001282c03079101080306082403a45441307442c01c44400003c0c00c00b42c445e0b101c02e0001c95442c0f265505c1c003031201e10107 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 644394604 1250 644393354 644393383
    0x602121e01030b2205010e10150b18030307020303070609060b0609060910020708120c0705040e1216020a2c07020c04090809190609080d1407022404030203060603 71
    0x140c542d110948003950344005100d001c40d00b26800f00184c001a002d011307880420051402070942c0c2c041c3c12658500302d0741081c190500120140d05d08000c004a40f4003117506100c05503484c038141d2420000824914421500000d42511000925070140246640611405882400e05000303104114007001aa4003403540b034690302482c100080011407403c81050030800d0881d00543e42030701e648440c3c017401c0640194170000420400103036251200c205015030b001400c821603041105e0100d00102c4d998900d0342c0d018070220800009407540d00801c1500c010817805500900003401c0a03118001d050320035000c1003901c440780c4181c0070f0001c3e03441905951a0b204800030b81c02810410f8100c03041001405d0700314016a040c65080080710300e0742c0ca48881c18240316204200c2c4560b070902d070070b000a1050545a01440417504100c16183e00c03240c1c0400300b24117034090741c8490398a444841c00028803004620b9107d00b43c0c243c80c2d8040010a64001c009002281e008400f91005941c9120178142c17901c255042214 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 644395854 1250 644394604 644394623
    0xd080609070e0f040203090a05101a0607030e0604060509010f14091003140c070507080309150306010509120607030b061c09080705010501080a020a05042003090a0602121e0103 77
    0x800881c40b070021030803030680041503040345510325004141240d10541d1064626000740c3c41c4001442810000201841701c440020130403240441500c0c2c903403200150143c2c0c810140028101c00341403003089891104c074002010a5619039407001c0203041035015610150110b82581d0b607040549004002064a50071280f0110749821980010086020091703010700040c5640d8100440603403c0711001c2612586202201c07550301c40c0d140c100240351480c1d80d0321030411980101f08e006d5a81d100c160034081000e200341c0d07002c0e44940700c101c0141d500c1c0c0a07428143d40c002d40e074441100e403404800036441340124007176103041140b18284803d1007103a1141160381e00b640740c4002c20040074440309602540c5114040d0030124104403180da03455081d01e1080c0c0c8078005a602c0114244213515101c1c0d80c400003040100d81c20007010406d8aa40b11042c15440000040e1840c0840083c02d803080500c801424103038099003c41d136444401400148104042d10150801070300b092058040c0c003800c0042c1740c103a940103070004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 644397104 1250 644395854 644395861
    0x14030c0c12010e160e0903030412030504060e0d09240509090721020d110307120903261f05180a02040504060605030603010c020c010c081e0a050a020d080609 69
    0xc241d0a1458186900c20741d030750040340441420601a440040f40d002a031002c480d4644440502c16550140801715150070030000d00000514400052400766034a041c04102640c0d2400c0c400010890f0104400440c0141c940c04040c1540c0401444207403105070382c0581c1d030b002305401a84c00c007101484404d00852410852072049180940003554008158070b80600400c0058921007030084001c580100081d401142104880c07200e8040c84104081100c2c00a040d45082c0c00010311803072001c12400713885680c801601d01491301c02c04152003080c41e400c5210f6a0b0944d210008a5203d80482e07500100c00219100c1c3c003880b1692100784000c9800051a0050180e035100561890140151900c80300c142d08000004050711a03001d47d4005010039200c0b90349900e4110141403e40c0e030f00c100601d0445d040107801e031280c1d81c0c0141007825072503084200241c561030249200d142d0900450b003502041b00c00401c5450400342c0c03000c002c28540f20180d00f6501e40c608100344c2500c14100648030141e02c85980d0002 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 644398354 1250 644397104 644397109
    0xe010c02010818070f0e07031a04090f021906080f0c04030308190f02030a0506090610050d1d07030c09020a09121b030507050f0909070302043614030c0c 67
    0x3079074211500000005400a181890f14075081d03542d4040d201d030070541542000744810f60855154840c0241c04d0520944485a6204034142042c90700c451180750b5460416042c000c0c0c1074280c107105a40903005402001d519504000f140c1503c2c130600e03000410702400141c80003134082c209805401e03240e500c1400c090a42c0da0a070740044004004240e8401c2d800c0a45649002c64010562443c202503001a40c034107100d8248816110011311580c000ca0108007404002c1d1a0001c154041c07060720b01e0310a4540303880d5140a006030040c80104103d280e00710300212803040021455800301d0384107040604404d5034644211081e030017180d8040001c07481107031040140c05000039202c14194466030138203040e40181071084004082540040d1a5136101600a00a5003880303c400d0a0201c02116403800030302d0034030a01d03a960440760200074012611041c1d08400c1ca07c5880440c2c144416505441036035074030b400040e1100301108001558501410310a5402c2080003000300d403158040e1001405084000409 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 644399604 1250 644398354 644398367
    0x6010521010b0703090918030513090204080f190b0f0403090e040b090d0306081f0902030d0c06050601051216121109030f01110a0819020a0512070e010c0201 69
    0x512819500d940202086603550030340c4818003900710742d0301035610341109050081070b2614a40000110070f141468410802142c08400121954180b411710f03a1a510303c642c8030036820090344402010390000c81c020800303000108400d00c04030303c0c200c211180c0b0a50b5040c81c281c400005038001d4112202e500110740d0300d55034100713450351160083c140b40149903980c081480b6040d20481e029941d1003100801d10a1401040c4403000c0c4280591905009903030900380d0058441303006a02c8814407100d07100c04002d15844c40d82204460b0364008081d20b203a2007040e000508028040541150000d19003400a4025030140044c0c03910349070350b00c0b0401c0170b40d40e80c010f40c40551400320800a00b80641d480d1685000c003000d010380300c00006031031469a1203901d14028145041104400a00180d04010030b681001c0110b4042c0e501c06403561512104a072240c0d00b401410300150225a0401800028502c044a070410020700080040b03003100102559418001c0f200d1901c2600750303600150b003640440000d50310a52 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 644400854 1250 644399604 644399617
    0x6040b0417070209070809010606050418050a0f0c0503070f0815121615020c03010603030e100c0614011806031110090e040f14030a0203030a0908090d0c05030f0a050303060105 77
    0x2070740d00e1802c03440b500000c0a40500300c2e211800110030000f0004468002c0c020240200218141541041c2c2407a8140f901d880440c104a00e40d1070355a0300203001080590880001c0c01401081003200c2400c416005103103900448040011039544540b84102a11074448103110307045944042c070792010502c08003c80200480c1896420740700c2c0601c0301e800348965010b2a00180b40100180044100404010f810040003280141c4640d2402d0340c1000842e4008070409444241101c049005041a10b000d070703016054510050305103440c00415402c3c0d5041603003280e0603140070303103541d4004815a10710241501e0007401300804440010f8464281c5007880040f000b0800038500704900d400392a40b110054000044800f0b4030000c4003080c100301803140d182091400aa01000a1407034142594806542d038803003e0480111940d6940b0007006000d4040152903c60700700408588125941e4100001004a1400341620074018040100380b828400125145110341c0b0401031425903444030b00541d1543c0240 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 644402104 1250 644400854 644400893
    0xc0d180b0106181a09013e070806150f060705101a03010b01020d0e0105040306051e060108130f03050705031804060501110a060b030102040f090f0b0103110d150b0a09090b0306040b04 80
    0x5c203140d0501c00d07d6003520000e0712244108108a501c84210003a28100c9641d1150015400000c00d000010521a030513503021003041d9440390901c03203541c0105205215669003e801402086001c088101030754200c0c00d220a1040021f4580f88031401c205402c84018882e52805a03000e8520380441c94000d448800441c0c1c4141085800c2603a079840320310607150112000e45150300c00f0341401d0110765111046a410807000c0c03a00003554a004481b00038043d112200c0030704030014240f050010984904110340740c103075000d01a640c50388040c00c0c0481420f140c1c848502c0c803c900700180460302e9442050300000245410380141280c0c40389458050040c41070310111a01550200404035100e0000483c010040000110010318042c240c000ca1048440000c000c504040c101014440c01c0502901515070520443c5d10004001000031115240c5000b03540c8403502c0ca01010a110000d10b80041c0c590088030b521400c2803041c8a40e00d01050348400040303034018210744400f000b00c1d01103403561031810601d0300c01 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 644403354 1250 644402104 644402147
    0x6120712020d1104090606050c0706050c1e06070e220b0d020d050a060f060e0f07020f2d0c09010308130302030a2301050c0d180b0106181a0901 63
    0x1482d80000e41d000c280440b01d0f0910f0005042104190621482c07004040504c0c00c5800e0a8240141a440d40d04610a20003000b00115540511041c00e010700004810180130520401038203114454903a4011203d00e0b02288480910100c0c0341407966406003000d01744402c10303841e005012140c00041610039446604014909150001038690301260b0403428011401004001180d14202e02550078007500704d00301070b050100c04c024030780e4500c103910742000c4000e107442900d684000040303141036440a80d142c107920a0300035400c0c0d1040c9940620f0b41e510304100078401c0c1a0743c0c1426940c3d0754020342854682210710304004102092010000d00103031804000c0515106580c0d4000038075101c0c1000040e2a61009130015010310a1864600d2858055000003072206241032003001d40b9900810300164407207070303c50300070404c27054880300f482c541c13107901441005003961140d45c0101011442c2500c000c0e113445c01c40012810b2811046520072050305004480e1812102e000116162a18140755900d034180 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 644404604 1250 644403354 644403367
    0x91f05060705070f090c020d0c140607091d04020d020603060a1802030a180f02090603010212040b0a05010e13031425030201471905040b0612071202 65
    0x2034900c000c260303540c002e20040400c01d0401c4036190900c0001e9100d902c0f240d2400c0d00103090941c003c07816140f0a0f009080c01c900b900340d08d084c485260388400d0708480083c0103441c03c00c018107410482810070744501c0540510184c15800b8441d885410585000e503026400001c078000602d412001540d010101605170256156078013003288400c0e4592164901454000c810462011250b20400100303c03030342c51211134100b825840710a0915010000603006898410005000b0749094045a601170b00f440c0020f011490301e420204901d14090700c0d040c6078141444000218500c10b1402240203c803040c5901d08000740303a03602500d42000c8032050f050420028800107005002000034a0800c00c6041c8084442403020b282c02800c4070340794507030510400151054002580c8000c1c0780704425117406046041000c3c100c40c400c01080c1c0c2404560781d8402e600c0b21800320303181031544d81c00c81101c0e410340342032100d0300000c1c1c10014039020716134448507108041c1e0001b99506101740da1105202415840043c0341c01d5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 644405854 1250 644404604 644404609
    0xc0304060207030218010b031618180e120f070303062711130513090501020406110d08190902040e06090106080601081b1306050415081b091f05 63
    0x42065010101603080480100194101a4000d1640300e6021a8140c01507040c0898201c6500001d0145081c50a01e403800e03201403800b070f50100c054008181d8600074081c0d80c481c40100300303c09849a20340b140d030410f019405102c0b0000303101628070700c02415043c140202100324034103a40042d48103608064803210000743c03031608104404105404a101688850925850300042c0ca091203070401e040c080c20085215101180c941440c1641e004407440389001c2010180721b4040c055188018001d54400600000e8071078001d1403c25000e441ca40680e03507a00300c1400c0c26907456800312804507034201e0000e01d461501400341e001c0012203100400c005114007088582c24075000c401c0782c085895a42d1500188002c0c00e00b00403550045c140745004011b242000703a2040f0035012000e0070301d8041c2980d82c40c0d02081c1c1c1c0c03460308144003034007000d0010070004e001c203514402041d41500c43c940444c09008200229604101e00038954608003174036812080d2110b480d400d42d0300107642d003e0465401a0340c0c0c08252907 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 644407104 1250 644405854 644405857
    0x1b0f122304090b0f0306062806051b07060c02040b03010219030203060109050405060f2103070602070b062e110105040501020a0306060801080601061d0d0b15060408030d050c0c03 78
    0x204444580c6440da07040800100441da12081032034802d03100d501d80401c00b40c1e0005807203944108169030360b91040402c1c101c401c505d001d200082c0d00300c00f403020401088082e0b1101c09403180d0301054140c0c0c3c2e619551416540e0f102c1d00d443c00f604d800984120383c4400541081d400c441078190b0087c00051404411411420b2460404002c0100190300002484800d42e40300c541000645805c58041000d82041c400040c0000441000b56004102c151041c500300c03c0340310020f60020804030140ca5030761140d8a00a00294072580d0f040f1020303d603200c0841d9040c10030340d8100c0011035005070311407903058510280c58026903600742004104009903454046031103081c06900d00980c0b08100240e1200c003500070280c291076803500f1001c2000607000c010400e103000052007904540f20790900305412206425140c00c02c0c003c070300f407240c1c00c409030101c3d580400c80205080c501c1040c0c0650f861041404501c2004800d2003103210b03484c281e5206110801c6801130a44c0720310740018442580501c0c040b405085d99065 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 644408354 1250 644407104 644407157
    0x120e09010f060302070201111b040b0f281203260f1801060914150103110a1805060a02030d060503030405360112050127030e010903050318011b0f12 65
    0x303141271804d4140c024102800b82400d030010880e1030509545c0100003040d07100100aa20780101408a88008200000103510b000a4406101c040060b0744140c10b000d4015582c01882806140c8810b01922000c014009401d00a0580c20250301d00d0b0b403501d508040d2014401a46010341c0d55071400c000980ca0f1541c81040c080751030104d105c0e10140f81c41d080040803240140c51a506140c1041204002641e80404960039100ea504003900c03114940d00c04075016400f5038000c50703040040002c100c0c0680d60004040c051801d41c280040c460140c46100b4940c4a0080c0c2c03041e1600100001144141550f2095440d031000c440044000d4542c0c00060240c00c0500c001c0e4000d503902040c00000d041400030030b00900c00b018880480350221940b142180b8190b5142094000d410040300421081e0707140c4c0309448034002990054100d0b512890320a152221940302c084800303010541d84680701541c459000c250451590f0042090101030b461521008020030800c1c40c43c10800041078940c0c0c0002d031002e240c0400 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 644409604 1250 644408354 644408383
    0x403030f020318010b0a0b091e130f0b0d0c062d0f1409090a02070831080a170a02030d0c0c1101030524130504120e09010f06030207020111 61
    0x100c503014000c41401c48004009442c09261b00c2031040c00480c40f21003c4890121040d0344d1000d9001d440c0141071040e1006510b1035034840ea00710451480389005410031202280541810041100c0304002c1203c00182c4401c014001e40703501108126150168401d00f102c0707604038125155040b03010110b1400701200018500102c0e580d0b0343c03071203607256209200f80d15851000000b285004a21000544c00da84000c1c82c0610b5590001200070401288400b40c5c0c016400511081d0400e42910002100f116071a40c1c443c0300f840d40075100000d401c01c00140d042072403a04489655a80380004904000301d5014041c100705510080010110f000d013140710707403601c10300c00359504986100700386400608070b41000341881c1018140014800340c5164400801030b00d0980c4500c91504803060030200e0001900d984c14401410700d40700411080c40342c07419652449030b002d6500c86101155080401484e42d600303006101e02041c0045081c40054000e42c01010218014103003005000e40f0742c4403c9141808841c2c0201 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 644410854 1250 644409604 644409631
    0x9030307210908060c071704050301140f070309020f091e090106031502090f09090111040311120a08070f1e0302100506040e03070b0c0403060606110610060e090403030f0203 76
    0x7000158000841c0c4043c060100c040c0489081c0780501c600c441c055020041c000209100c1100c00a981d01400c44000341400340c0240710410784141c0000b10340d070303080b0b0f03100e859100b4440010740b94038030900c16400350303980c0141410700c80b449400c14051485001001c006002003c010348001480c00410900d209480b0f40001190460662030f0121a070341c1070700202d0500ea40103200345071203030356451540041d076034040e14820740030ba5072802418058280d501a024007620300080110901009007610a840401640e2501c501ea0180c11255554840c0b66000b801e0080c060121100080c1e070401d452a0040c0248682c0e20304504210900c3e1039904e200004901590111003039001c1074607039002c2c09038086000c5804101d10b45941064549034422581c0040411050b1800140c80d2800041078601035174120004100844c0c40e040c01500d500c61414079105035116490015080c00030b491504000d80344560360310030555000605004005402420403400e0584030070382e0f20091800d510103103100c1c0c01080b0285 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 644412104 1250 644410854 644410913
    0x302060c1b040603020a032a0f030302070e2502070e0a061d09210f1204021507051b01050c06250815010e130203011503050a0911040209030307 63
    0x1c045200d1000a0140240e007011010000760765840714450440c0c0d040521b40b594429442007020036410917101440e5008050300000c28511002c4145e0b0090b80c0c86034003100c61064a5032447c2ca400002210461070070700d85400842e018001e200c000c00036030003403070040346d08091702c81c3c00c1c405441c01c048a091034205c0d5140001c0011480e40800700c00003c055460000e900c0c1090002503440341c040d280030710754549400a00f8205000040c0403102c45044034102c580d00d9400d00f246941040070144c0d401c1e803140c43c155513182e815008490413615200d0740080200780a280800c103050401800483c0b503130602c1401c2c007602034000000d0100707030b12900851001c03280c41030509c8a07400c01e5032802c6503503804205500c000c10000a0450748140034440c003d082c81662416a00009400524060b40054880e400403000160100b02c1a018004241340d0b82c03011b00041e600c071031100c03041355014900649065058020301f0b15505141d03005204603003002d030030399241030741030b4039004000d030300f88250b02d4051105041d61 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 644413354 1250 644412104 644412133
    0x2070b0d0f1a18060f060415080c04120f02010903020603160311070c21050f0d0207060e03060402102006040614040302120c0a0c120c051005160204060302060c 70
    0x140481000d0b520082c801181c8420082685600840c03000d4000b81c41003004169a543c401007610a92100202000d0751503840c0d0480641440101c2e40b080d0208070400003040200700c08a044e00c00ba0785103441c92544c070900549407495507014036202a410700c00f4008012026071030701d40003584102d07509010703001d201004e0305004007120801140705040510611120700014104c100000440e00014a0714115981c1c018900c0007454480b100100244219025900c00000c0410807090302e00c40c540955440740e99645090300c85180505003150f264000c00000f80040ca04030400c25507040c100d250010085452500501280c045c8032500300150b4065804c120800004d40280403d0400c0c01a500c100c2d41800da6010355117042d45401c0000c410340100c1c001c08601410450501c415410100082c20256102a01190184214400d98503480c85171004200c5082c22504146100c000307582e21442d04910f01092060003c6080040364090f469071000005662244090a414170500b0058150044000e18 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 644414604 1250 644413354 644413361
    0x20a050609010c0903080304051e1606050304030503180a053702210307020d141615050a0207030602040f0513060803030a090813060e1008090d0c0302070b0d0f 70
    0x1d070340c1503810000c3c02030405900c841d846086a03807081c0260748070384403460102c0c1020880c04031407030407035805020740c04c0040001829100101b1083c0e1081e41046c0c441c0c10444861004480184c0030540800c081303100c6000342d000c0011010b10540545d0100c0c00b00341c4d20340341408440c1c003009640c0041290110100940540040320b112207102800060288550102c1e001400002503880300c01220488202004014000c443e012980208003d4015542c0d1400d04503005039520704149510524071b01440d0088189528801e42b01e04858460f8040b2140c9000c0741d160340200405e0085024064001000405600140002c0d0a090f21040c0c0c1c81030424050100150403000c030030a05030f050080070004904007004403904900c00e03480119500d403142c1040405071084107801020f074880d43da40002c00c0c2da4000005104900201c504852400881c1003c9980301c0b000d88400342c65030050829400160701407100b5013299032107401075820042d07540c01004426000b01981c0c881c2240c84600d0784001100f10b20 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 644415854 1250 644414604 644414611
    0xd110106060305091b0d08030a02070b011409011406040f080705030c0117070309170c06190207051f090516031e033f0b030705030c15030c0910020a0506 67
    0x90b041240345070040b6074540d1100c001c00c90301a40c903092081881a9140c1d048281c503c182c02c000055640d08007805020020350105609465154030780f000400d250301425101c5a4002001b400310065900307224013191480d06c042c05160b4080c4003048000ba0f1800300d000f804001b016010081d020084c500801e05060917140c00c0c446040047c40ba400104107607081d65044c0c0c01481c246400210301040c1d01d441c50100c400c20b1004a103201e40401d4035800210005070b070500c500c0805042c0e075020715198031103c0c20307806103e80c000e28541100190711156218040201c082c5511002c2c081107424541d01c4046c00c09012840c0c20118500001d41403041c00344540b441d811005500312002c0a05000f514001d0211000000790700822011360511880c1c0c2e64488070f55003030803450322500d86441191028150003801061650340c06030050420010341490301090000703050a02030903401d1700311602ca503400d2655100420a20101d0024050300210303072120000c003004000660001c14104501e400c0861805400a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 644417104 1250 644415854 644415857
    0x50d05040f0905060a030602070602030a14060312090f0604060c0302070501080c0d050406060b0a031a1e09070c050a0b0a0f0b01020c040e0709140f0f07020607050901030b030d11010606 81
    0x42104100d228455640e031070441e1030385a0006410384490b4001a01e00c401c540c0b01508807800441d100c07044c00b02e558000d50080424034070800c0306034550103075060b13558022610350b64160003003018070300c203400108010010b02e00300610100c802c080c00400116540c203e0b4020000080010a1110400d5010420500070b04401d08103402c1c7c80c54440248004c1d44900039506400035103480c0441c04001464021502802180b0b070031507201c1d002184010002c1601481c1c0c2c7e0007400b506c4809046034100341c50f00c0038070610f41c410f500903c540d014080c0020041e02070b21010404c1303d9280001d0104105102c0444010302c0b5080344109400c0c403060290076245030344001c1051a14040f10407030140e0700040c83c1901880700b5540890800350488009003480152342c4440a880c1c18201e60000c82c500e41d91215120700301060412007540c690b804400d50383c810880f01400541d0001011035506801031000d00000300c014500803940751001c07070100307040078011890040440c001200c090080c00c028050100030701101e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 644418354 1250 644417104 644417107
    0x1060f0f03052406040b010e0907030b0406140d0f080f040308040e0f0f07080c131401030c02190f0c03140a020a0503012a0201020c0706110601120807060b0a091404050d05 75
    0x10820720f110450380140c8040d00c1550b44035030560040c1d0051690b80d0304914014181400c034544154050040d01841d50344622540c40c05602050b07403c2c4027410700004450103084485c0e041413a5407002990071100009940317801c4140201300ca40b0700150020b00166106140c019117403460001000780701100600f40c4d030300a9003080c1c10089507100150b06541c0c000c07150b2800f105180c403040003c000d581b00d0410700401d801098207000ca082407000c0440842010280c0c6c040150034a0154103c0c1c0b80c44c20060011000410442e080c4040346c1c0c4164030031030340c81c00740741e01e040090744e680e840e4070740c20382008030490044d0041c070b03201000e510f0806c1c80000200030039002404996032511036070404606800720303014a2540e003001510282c0c402d60617109807282c140122901c441d2503440c00b4058140310840c0c08018850f00c000442c00d0444440e01d031101e42e038040c071000e0801985a4901c0090000c0300603031740d00400070803400501c0746040c0c001c18580300100c8035080d05600701400c00c1d90134028800c40d2041031000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 644419604 1250 644418354 644418403
    0x530010e0103022d0303040915270b1c05010c09080102031506031e040c03060e16170a05071e050603070507140f0601030b18060105030d0c0501060f0f0305 68
    0x4c070b4142e12180c2984a0141074401503484c41601055141401c3c0160503200100300402e1f1500d155000310813000396401440211070b43c40c1c001240111400703038586e044c40b482000000e43d0210f5030700b0070400e59038010403000c031030025440760130344105240801341c1d080d0391182c01440d4190b4001c1c5070700001d01641c00c025451071030440f040b940340b01e1503000aa80200c4002000850000381c6d0011840079240300c550b5860142800d08100b4190586404203807080303031412039270b505800cbd00000d01c004200b10a2820289052509600483c51000c001021982e402031400e400000b8005012110107440d582040e400c101404024080210340c1680009001d040c080043c07010301d507041030644484562001b0682810500040a01d052000d0400305c440f2501c203900000c01040410004580b0808a007200364040c00c1d04858941d40d030328020b10802c1c0d09504400050303048540325408000109001d800041011682c2d0380c040c4600e842d45901a904000e4104420300800106104d5004041510070441c0b02524 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 644420854 1250 644419604 644419609
    0x10c09140a030b010b130803040e19020301050901120f1b180e0a0209040c09020a080403030c0806011202030703021b0c011707140313020409150b0d080f0a0530010e010302 75
    0x21010f016005d44d1a201290103201042c0200c818005060041c1c02d403a10780350b840045800c04a000d0b10264142e80e00110100c40440c1c0a01c00c0e241292001081c10441da4a030940d11401c2440b00c180645403400b201c00900086200310354603981800346410a100000c0ca045c00100c401d0010382200c040180c03d00d07007918030600300050155581e81d01140c080c0c00b2a11280388c058601e01103540205480c0d070011400b940e08079045955944218081d03101400f2906494030101c948800880e1283e002c136111800600007400150b01940d880202407c0042c5004803e07401c0e440d02211181c418045584102400083d81d680106c59200030b032440302131200a8148590007404940c1c0c000900c021194020002640c00c9054880c4801c00c0d81d0050300400074210b003030501d400e41c0313011441c1402e143c6003841e01c00b042500b440301082c1c100507001f00074a42098140c850303010030766000390f5100307080002c140914a46140c144003c500a5000c1c2c90440b01c0180c182b010000d65190142d1080882036000d000420158 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 644422104 1250 644420854 644420873
    0x70b190606120c23030103030810051c060b0a08030d15120627080c0c011b030806030715080411010504150e180a0b0108060d0201020c090c0c010c09140a03 68
    0x2048500c042a40014240f088441e0f6001c11051001e01034007130840c40c00c4460900040d41030702d0095803042555a43e0b8801380c81c4072007281c4107070b541000300318400880107a92009a4500c461003250041920142c6100194034003809401c02d00080d04006140c054814035031240030600c05030061142c4105e480e00f80311031408201101d000d01140c3c0c603008245680c4104654403183c200a11040051514071410507149a42015162140c1071040200c8180c00d50301075205151481c00c602840c2500c20b0303141d03608540c0050054141601442004e0001c00d80c9a45078a4100150703403190f035811098034050178038501c09c00d40c42c10083c0c18008100400e00000f445200c040c2c00305107450034000061030106000c100d4101183e940c000d5415080014401110036541004c1400c0409a0354030200b9110001003211811000300c0003400360340f1086000b162030828081c8140c4c001c0c00b4013542424a00190003050131b44100c2424840003511242050100b10454030110f40d0200e001c0ea840d40c521030440e514031950 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 644423354 1250 644422104 644422127
    0x70821180619082401050f0d1509150308040b0d06091103090d0f0f03050411090403020319020606090f10080111090a061701061404050303070507030203011404050c01030507030e03070b190606 84
    0x4220b00010900d046c56021012508c100c481264100241442c801003c980080d450080c109054280800440c0101d401d003007080c02e80c0d4110003c203250500c0d10405507481c2e4496140f0b04885519288000b40d43c213a103110700c11000d00c000d80b54030791320303d00320a840303007017030f00d820884814455041c4150780b40c264040d20b818170307010483c240060942c4690510301d42002c0b40c600284e40c0492180100010558040003910400484540c4000e030030324020800e0703841d1001107802540040030140014040f180c0001055044400080c542c810540c079014141e09603040d2025405650400156801c6217080840708500189120329060030305640812442440032818400d240820040c444182d195001e207604590003400d00404896903150103140240c1c4484c030751306c001d81c442c3d460a260942200002c501c803c0c132560384140540341409a070750054000341006000801090f03500c1c24040d1100b0b1003003008040040c0900d0203041c0d5427030030b40e0a1807040010b01d040c18018506110b410808540c010b42643c00 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 644424460 1106 644423354 644423357
    0xf180c090b060706020d0908070318060509030a140106080a1a070f0f11010f020d02030901050a110d110f0301030c08070821180619082401 61
    0x22203650120064215000b0042040004d52641c010079403486c0002e00003d10b9030046c1c03035134910390f0006001180401c110070b05101e01c5100c915841c800030825403400070311b040115004242c44200b030580040c00807011420014070320700290841009000060111b4401e003289060281e80011002d030200c458a16510205800c01e106011101c0302c0b0865444490415040250440d0700d8402c1c0c14000803155a0743c0711007104880c040c0004c20b80740c1454100943c030ba0402003511804c4a03006809440142d2400e001d000385500c1d000140c42103e03210350000620004441000c5810b0312501c800080b000740000004400c118070455a901580c0c0018222004e10381c41c0d002582d500c50348200d60003441145007403070a0400d440030000b400403203074a403401c8198001f5000400d8064000700300450126001d1030075000056030110b000303540704094021480c945030014841d070401c00c0e100c0701c40a0 = true := by decide +kernel

theorem cover : BRFrame.Cov 644244604 644424460 := by
  have h0 := BRFrame.cov_init 644244604
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 644244604 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 644244604 ≤ n) (h2 : n < 644424460) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
