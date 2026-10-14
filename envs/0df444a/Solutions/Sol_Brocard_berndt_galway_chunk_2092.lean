-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2092
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:37:58.056865+00:00
-- url     : https://prove2.me/submissions/dcba69b5-564d-40df-b337-01d9d41eca75

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 376079136 ≤ n < 376258992 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 376080386 1250 376079136 376079153
    0x418020c06100f060c1e03050a080c0324040b0303180f031c051e04030c03020915030c10021203010312110a0507050919060b0a09050306160806010513060c 68
    0x405500074030000d002e494812a5404240140701d48800d00240310640700612007240396903850044500329015081446140080c084c1d84030380100400640050081140307541403000b140e024441d58030701c03d220f4440414010316000f085010480e8810b80d103590480703a903101031001c0e080016050310110050044401400320307429410300c1d078500c6904070600c00c11544c0150b8180c0814000b2501e4025100c1d4030070310072140e061051045500882801140c0041002752030744440741524420b0b5252100b40d1101c8801060b24260b1051265040d0807218640d0901c0c104550b178018500c05074130444101035100d01608a0b10b5000380c0056400c010300800c910042600a01c1120990880c000208000340b500e031070382c2c1d0f00c0b8801e0740295441001a42c0200d08071543d8401da26911b0305d02c2c2c1208100480d82c5940c008400d038000941c220114542c3c15000555240c0810f2440c405c50740e0201c00034144004901c103d07103480c0c2c010401e5041c08000d20050f07107403501010072078001c0c01542d2500b074480e2480d401c10300300 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 376081636 1250 376080386 376080391
    0xb0301140603060a150b070c0609081605121002030901090620160c0306021305030c010e0f06130305030a21050402011b0c08030c03180102060601081306020418020c06 73
    0x300010280306018860702c1c00929254003040c05100040d0001d6030381ca0381d4100b4000c56008560301c02021404005010741000d1003c05c81e2290f4581400413581c40d840c1507110f03c090040c40c0b8207000303d12000c0089081103000c880601c00d00c0c005603450469040c940c04100d0300701340c81f05465030b076488680c20b042100340c2c03141e81010804c10401100300d440a000b01c1c1d030309120307618040c060304c0d8001400408000503400300e64080c0d035100d00255100c0203107403502c1e61106444c3c41094400c2c820110701400d15409018000d05000001c0c007581030106422062246030383c00500f00d004c14505840000012803c2072024258518580e913070f881c095400c00392921011440501ca51080707511b04028000140c0c1c210310808040c08080321440c203910714504203034800003072652049d003075800b0000b01c0341c1c04a88003000a08041d6211140581030000caa401203958507002c56541e40856580d4000c5141c0d8801c0804202c0f0141c0b15a030054a020748922050720b84620744c4440e1507a56401061850310b2140a11030b559 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 376082886 1250 376081636 376081661
    0x7060b0a0b1614010f0c031515090b160206070b010e0604060b1b0a060c17180d080c0f04030f020108060d03201e16081902060f120106030b0301 63
    0x18244107401c050800721280b10040284922000e003038076106a80b081d04142ca081086800400c813220070050003501510640148a540c501b590201140480c0d018900d5084642d2981d10809281c0c1440e460076000d5010b03548180348030850f01c94100043c0d13150300040030f08500c02c46914000707501d00340140d00342200c064003042c030850400c0d400340104100d00701a2000e440300b134003020441401c407a101f035082004280c4050210b03410182c80607219a003101818807480000c3d070010410f5620404440908003680c1c501c071030543c101c03d130152032051054810540046102c034070300b49046003030f03440c40c3c4c10307688284d004461480c1c10300091015503030011503080e4882000c1e00c0306050b8488030350f0000c0002300d2603442a201e45882a044204407030307040201440b08c2da0f007105c00c0c2d2000d900e8450015903400c0d000051224a111807c1c004c02c03a0760002c14001030600c1c46c0c02d450084503490f5400c20505400c501a40c0811190620591400440c0401894000c001340d45000801c00030f038800b0300d404d44c0c40c4040050f = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 376084136 1250 376082886 376082909
    0x50a03140304150c030f111c1404020405180303090d0f0e090103030318020d110301230f060612240102032106150304060c120504051e07080307060b0a 66
    0x12000c5280d5580a2484480f82e50380080e201c228008154014501e000c041c84010f4500040c241c0352030492002892260505e5400000107000780b841101030350314070503580f621151442d002c90010300300fa40001d42c1180825001d003146000d4880d81d14a1604121382c00956a0300440c1340d40351058100108142c8080c03e1714104031286030b04808240a080c06110040401d13599211101e030881c04614a0b114503640280b00149003640c1c0c1c100400480202407007544254a0488420050000c0240702d0004884100d40d040340c0703990b0103410701c0c141200100b01641105c0f04104401c032003803016075028401d41d2000c6608900d61a0803c1d0085030901600040d4107661040000ea45d0901c0c0381d00c1013072404800b009404030103542c0c076404161001d00b00011f2a1030200003006003c208021a04040280c000c1e6546a90300c0b035603004641703002c2d02c40c1514082c1954101c8010700313a50710050031601202d102c002c4101e0704003a540314205459544004c00c103035032885d503404900c191850140c465100401d00b21495 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 376085386 1250 376084136 376084141
    0xf080903071202070504020d020c011112012106021207271e03060203042301060f03060209041b020c010908010204061e0207030804030308040b0601031e0b0307030f050a031403 77
    0x82503681c890107101409042429180780060707882041250050800a0030654481d004481c0c1d0501940044442d08031a500301905205404041c8054501500c0c0c0d00e003a003170300342e46443c85042c0300012000000103a54408a4a0004a8507500090a000d0450b0031581070078a030400c0000e145d503101d086840d50210301c1508202ca40030718201c8110a8a4030b000c45c0940b86e003844400046020900d900c0201004d0003c4100020712034250344030f030001c050342e195000394400c0c5140820b08845240c060b0501c3d50070080b00c14408150194060900d006000d00005100d40b59501120f000c01c005071100c8005030310511b01ba10107560300080c000018610500203500313240c208140503200c4290200590304422070040c0249500b40300b08040c00055400c90001a51039842e4123000301410403c48050f40c1850304000407403540c6d40300384141d12801c1e0040030301845c03c60040b4120340c05400c82d1a59954584992440031000c03c0c000c03281e480400d48a5001445000c078a464054040060b40d42c1c0c80c55001d03c14800c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 376086636 1250 376085386 376085401
    0x15150d1505060405040c0515091203030919150b0d0c08030a020c030a1e050709110304110616080310050a0e040b130507050103050c04090e070305060604090f0b0a021603020604030f08 80
    0x81c6d400c2035500c112201600c44c0c100003040743c0b040c0149140c142e407020341c604203a088000048021400b4044200556122904080c07600d880d154050000811001c2001d4180c04180301c1030b030040103404002400009890704c51344a28014940359045081c40350400644200029010800c0403517020094014100040543d2580009042c0081088400790400019001004424041d02c4040d1030b00d5070081051030400d0208050356041150225043c900707804003400c0c00d18154064400e02004009450030641c4590b950042d030341c1000c0d05004004145840c040340c507556030101400078010784c007100c0d5110710382810540c01c08035000e012440c820403441140c002085c004580d107816102c2c20308022940e40c540350241e040d1803140d41d000102d000c0c175010107420768000105003d0120303809103044828035290304080008a0350402c074010044520410b020f00029181076806a00504032000103040c0000090002481c0840d950110f0040e005007003080101034100100401a03038103032411100c0340ca040032 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 376087886 1250 376086636 376086653
    0xf0905060c03040809120a02010f0c0b0a110c012301171b0d121e0503010b070201202b0503070c03030e1618140402010215150d150506040504 62
    0x1c1600c005048000000350a100c0c0003000c407005860060003160041c02e00100180d20740b42c0001040b030000307541c03200380d0343c0b040e200c1d013150100d168114805020b03a442d4039024038018840341c3c4003156014000d00041c0030a0901b0720035580040045060440084142e02c1c550f01d4501050b0041c441004c0070342c91a0810001c0000c40d2510700d003685000c60001840080018141404450003c04140d01c022204c1009548640c042c82241c0500034074000130b24020100390b410740024003526081c44014080d4101561080400c541c10700f032984100c40c41b080a940714181080c00d11070102c1c100107c034414201030040c1c6013a071035080e001d2510700301d81103042102004210803010b260141c105a101c02004068000030b1129141c0c40c0014842ea543e02991245500d4400c0f034001d80f0355110603e001e41c03529460b100c034621a88200da050340074200824403103d034000c1100000e002e1054070015040b0b0441c0070303102c2520050003140180300c9800454040c042803070583c0c8000f0040d034069070801c001c0c400025801c2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 376089136 1250 376087886 376087891
    0x40501120c02070e070c1b06020d0306051c15020f091509060304060f0b0307080c040c0309052509050a0b040c031e0507170408070302010b100210020f090d0b0a0f090506 74
    0x2030746000495200e401046446c080f415202a000c1f09102c0722005001010740900c10480e1010307002d4480311a0815019000c0310700ca441590f401a400c0c2c40ea40340000a08a46510140e11443c5035012400c19107840500f281c106038810440341c0d000140044852420101c0403401e604408121407401c18410085151404040e000400e499200c81890100741c6075900001d8450b880601100c11032503841c05660f54454811320090701032480c0c00c841d421618072070301407a252150000020501d90650700380240001c3d001360818910005201e40c04a4604a5409454010015407201040d00b80c4518200021642c510780c6140c145450030343c0d824803520112200c0340102030078070400246079a4a44054841840a10145122000e90820001046082c0c000340290a00a070b0080000c101884288911070081030a8900580d00042d1920311615154004050b0b003109150080c5c101249000820815003d0403012134051880500308485509035215100d140301c00b000043c0b02d40303815621100c0c5c998001 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 376090386 1250 376089136 376089149
    0x312030411060d060503100524010212090105120f0402100504381b01051b0715090804080d0806010503070903112403010e070203030606180d0611040501120c0207 71
    0x1261001100300d20f03603c404c0c02000058140c1c0c00e0510500ca202004000482d508003208010011062400d044c200b00e03441200d1042c0c0040a0300200003030309088603080302c0103042c100700080103030102e0075500f05445401000706c0500a00503042500c1004101c00b620b60803142044000d00c41003000c2d908054080020400004520011282c8100c90300d44e40c08a801201d00c10f800b0004e1008481d4408003032070240841c01000801480c2c036a00c1c0c0050144048140310907401c101031088501203000d00081400c41e2a030f28600003140b608550b1801e1160300036030b004c3d000e03580041000311171554100c01c0302a800142480c000c0d16501d0000f10107480c00e201d500024142007990b20481c4019160000c099110352440c28561607401c0308000c000d2130a5109000c0c0352440900d85000c0381990b80000141e82c044e4500134846400c044091034030035000000c80d444145d1000070010480e01080c0648111036111a19001c07059031103050000240082041c98407104842d850300d0001b005599002c2038080c191242e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 376091636 1250 376090386 376090399
    0x21201150324050102011104050108060910090501030b160206010501050415020f01060f0f06030227060d0510060306060504050d231b0432070212040e060312030411 72
    0x400d500460061001100c10850b80032240094040d500a200c24101154000d03070081c03084000001c2110148d02a901c24540442d4602c4081a118a05910483d6014608d0800100d03030303a070f55a40f16415203402383e10036100c0465600c24030115000031024420b0180d920f00091a5551400c3c0000b045413003284600000810b501507403119040c4240010568100802c009118403034440c0004c1c0120038107403040c01e01002d845400012441c2c06802580d103416a18980f4032a418920f0b2620440c0b00c81140c511507001804200c0440035400600c901801518509904002c0d58145280901101d00e207030085401e10030240020003595680742010f0801c10740c4207503c10b0701c00b00c2d0042c59041c0c8420320002003a160041c0e4608101c02014021240d104000480d024400710f0403032032280c0800c8032400628029a48104001000c5c0d00c4a10b25290304208103104803250b40340d040e070b00080c10390040e400c0351b00018800c2c01480890320341040303840c1e8400000e48070381d4a54109991602e800c54102031409003d00c1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 376092886 1250 376091636 376091669
    0x108040303180c0b090109080d080105040213031a01080d0c20031237051803031c0b09010e1003030f090f0303120f0c12021309060b040305010e01021201 67
    0x20b14000c42c1100581e00c4802140c22585403074265000c0d4000208050000780702a000080303e907800a100f880c0d039511a22004100d909010600020307502240b04403208040007a80000005c1100c104102000c1e03000103d031000c3d504080d070850070200b90b044054104211861000040340e5007010141c4080f03800300f41c50100300d04090100b4248404010010713540039022803135112410101080000d840e100003070070904000110300f022010f020030608400016400d00106041d00c4100d801c0400c01040203044a00301103c81031a1486c0d0b0380f41640f40d0184507110603100f1002c0c01e0807050719014009000004042e803800c4030541c404000244006001c0042d68801c08140c00c1c040d40041014004c800401da00c03440d00c0e800c1c042d2200c41d040b1b00850404d4a4075648800d04000d0348030b96403540f01c003942c604602207508140d0801039082655440071040d048180000c2c900014400e0034024030145040c03a0f110b602e5270504074212404918508200d900400c4140c00d0302c202068801d055170001c0a1001e0b03240c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 376094136 1250 376092886 376092911
    0x30901170c0a08150a081c031107031206050301020d0b031018230102071109100f2907050f070b03010b040504020309010207020d060501080c0103150608060111100204090b040b0108040303 82
    0x1000e5039036130a811542c81c84000c102900081001030000300303400070030b20600000d48421400c46450b0f00c0620300c003040902c90540042c1c0b1561070344080545100d030108055885000181c02ca81c000800380140b070b90f8540c0701d0701403820700b440380c054a0340c0b9182d402c01164542411041d07036070318038180c01890381c3d803800b802001c2c80f001007411019030040103001f1502d0b0b10746840c0c880d031030f070140003165845078410100040d035071540d04141b0410307503090425010071645854003640c2c00c0c07250f0100000030f4215440c124007151010754041e00c002401a0010300c060412042c1042c00c00f0b00c4c0b034001e0744c1c0301101080140b03c02501e4108580031100141c600507540c6c2e41300c26031203009000c0d0303982c006d6103e84540300e0581440000d4009a05a583d1082943c0b860f203560001903080700c40100044907030034070100341046514050030300a80e000c00c060414004d4989030604580c2070802004401c6201076001c44c0501c1045d03114801c07118401010b90702040a500c2000c00a0502c0138011b1005040544401004800 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 376095386 1250 376094136 376094161
    0x90306130c03060603030810080c180a060806041209050603010b0909060f0d0f03120b1c03050702060d14060a0b19050f130e0a14011e030b0108030901170c0a08 70
    0xb9508980c1c100300c030035102d2500500248056031820740c1e0100101010400b100301040d14080014010010354280c0304030307540020042401885414150765903c0c0c000341c41602446a03a200f144100c501483e20480c2d448094400c51039034003c9030181d18248010710424019204844819000312103940d02580e40d0300008003820151000140c101c1c401c015090704014600000c615824030a0b11201031074409404000d00300c40e501e48035198800010aa80b0301c825144c5140040260301030700d021850000340340c010480527030103030340700030521591041d112104041181a058008600f04da5103d074280c0b134a81c0d070245501443c81e41141c001404000268040d000b5000c4500000d01d0f810b0503501d03a00c65540b84182801c00703209148845070f00600041c1d2000b854031a041c024090090040c0d01a424030040040b800d0f204005608411010000031003ca07110b0b050080c0201103a41c0255a40c42a42c0001001107100d1042c86030070a503c04c091040e080c88003004c1d603508000c0c500e840b800640d55194008e12 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 376096636 1250 376095386 376095389
    0x2803080603281505040510020c100e03091e010c0b041502030c13060f0c110d05011130011a0d060905010503150408091e0a0303020102043002130f0e0c15090306130c 72
    0x4485182040740cbd543d450000c0081c0c609242e00b1941c5188010b45a2020142c0226044c5c0060010b07085a459600040402c40403581080c021070817044030305a500e401004923403083d2000101e004c0c003c11069841d180c1000d02c8000740c40c091070120070146d125140a0208010b02c20014480c0d0709450081d82240c80f06c2c0c403c0710b070303030742e0000d00a0008800c502a100001e034882c0407882ea02034040c50f00b00d9011821103104c2002c00318401d000c00481da103002d01000034480c40d51914000b45004001048124030701c1d00035403003e030485000c001420b505d0002010314007aa110003441d60780304507400308004502d1903001d03602d14150076285075140700c0b024640380420440111000ba80121403603004014581e05501401c2a00e02c07000c001a0a40b211008003404a000c0003201044072400c40c41e00740045c100b001c104408107142507000708020b29181c507000d0036100d40b00b5080b81e01c4d40c4a0310b82d5503814541a651605050600c0c4449031a001101020985648001340780d9508500d4080700c000400131000030a00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 376097886 1250 376096636 376096663
    0x935090906030f1e070806060a030b06060708030f06100c0f020103050601020307050109141204150e0103020d021914040e04080901140c0c01022803080603281505040510020c 76
    0x1c020f00110807103100440b40380a0701c0d808505c111480450384d07850006050307010300300082c594894185143d5680822160050420360040810b00c441e000285011010714062200701030404c4461034000280100415036107007250030400c00d64524008100308800b10010541c0a02c0e0100b900d44d903000040c0e242d40320308100284150702c0c20414009102c288100c44100ba45601c0942c1c480c4050b810200c003260089006000d85100c4011903010a02e018520481c40008103040141c240060780102400b241c01101c0072107403c4038005001c501081d0f020b485442000d07101c41c10b160500381000b000180320440204000c010f50130004555082d030b8002c001031800c1c2c41200c0d4919503614000e048107a2200103808815000d40716003502c444107076900040310481c0700c20140b2854040945a2012120090302030040c40d05030040f104e10040c0b0805042c182611071601c06015041580e89180920038003500c004001e90702850141480002100070a00c480c0c505c004960250700d8000218283d82019107444000d07 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 376099136 1250 376097886 376097893
    0x30912060e070f05031203130c120201030b1207050411070c06020d090b030c03070503180f0318090c04030f05070503011e0f0e10090302070302040935090906030f 71
    0x4004112054008600707400046041d02c80c0d565440b071001180400c18000c1641c1360b044040c025048800100145501c445a50000c0404000d03640354014020b019400540301c2d00d900004007020355805009401107600252954400b441190000d0354a98480d0b004441c0b103070f0344540c10006e2840e1032800351011a900900420341c1c003552202c010b95503203d100e12070804100c2e42d00f00040c0c0c074918001503d1140020f200624515035603a08201c0d0a0f0b80b00501d5032a4100c00200325100c1c0d2001006154194100c6500131940d03007508081d000400ca02500d200c030320a07900c001c00c01200e00403440a035011071760b0085601d038000ca224545181080180e0304401d82562801401d5900200751080c5030441c903012990401c03c954440e5014000e0300c44034041640c103540107084445000044d50b004400072030280c4180c505240c0c480e400141502c0504000b5204184190465504080582c0182419000c0d0991200790f82194044d402c0c22401405030543c40307490310300c00060f02e5403014000c41140a09a4055 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 376100386 1250 376099136 376099169
    0x6091915030611040302090a0507020d030b12070801020913020f040603110f0c03030114010302070c0312090e010b0723070b030408040819151109040203040c0e0106020f0105150f0d0309 81
    0x11044560054170003a0b20504095001c00d84001503446458003c411690107004807000955041d0080d04c0ea240100d84c01242071101c1c0c490070b039010f00c102c0000d00152400566155001400c00c01e0200740e200140304050310401c00108414004801c60b8101c66680c02c020a280c0c017840490b80050003525400307020200b001410540520001c001036041e1651140c01c2002c03003844400450880c0980722004080c802460024030104008240b101c2103011306151071000795460b02154240c00c03000381e100c0f480103080810745804002101002c0d01550100c0c2c000300c92100c902031612603440e03c4521a1442d11440080820700b40854078040f50050302d00308040301d111040d82c98420500c0c82e14510b09807400b6040d2071a005801d4543c0c0101443c40e00408038031400c0c062107804000080d070000d00300f201d0644071b5140020b40942200402e500906042d000b4000e050042e003141d609440c0e0040205201c3d03480c0c1d54148900c7da0340c85070840d6903810103640544414026140c10389601d1070a402041102044407603 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 376101636 1250 376100386 376100411
    0xc0a0306052212030c08090a0b04170a02070e010803190309020301020f04140a0b030907180b1c050d0503011a0c01062d0b03220314071208060919150306 67
    0x12210702e0a0b0f91954100001601850201d0302680c0070b482c030000507000840000c0c0403410300340b19203400030701442190652440040c03000740150b01c07a903a030741c000d82c100700010023452042d0741c5054010250800510f1070218003150b450a55420032000e07400307040c0d441d140082035407804d5041e50340b01d0181503106607030382c2d0b00c0300e01c7c940c450b4404400d00d41c0300f4140740c0c0001c0741d020600c5085d00d00500780362005211290800d0b8000740c00b102d52058210342c0d0350383c4103100038007640e4003001c2c0840310300200c054000104982c100603003003009410501c42405401c1004111049001840200284100342400e48668100e12400e0140100d84e1014400d881150740b030360001000c490801000c481c146d60042501a55076041c80c105000894450a021000407101c4100310426913640168511030319081c0c3c001c0d041b04112101a400c56102a41c1e01d103e000c00b40c0a61507040b810310703a0007500c02c07960b030f904c1e500d401e18041c00000c10703403100c035101151070300d46a1210302c100d03185102c05154403032424817044841d0074 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 376102886 1250 376101636 376101653
    0xd06090b030607023702030106120b0f040201020a0b071110020a090e01050a05060c0a0501020307020c090106020f060613110c030d060f0608040f0807150e0601080c0a03060522 77
    0x21000c0d00c280181004907548a000090061101d5400c25480c0c4621018030b02e91494101c4c00105031381000c1c00c8000702401a6428805d1a01900d69038103484000c681d035080083d02c000300109111300480c10b00040c44050303078001502c45a816030001c404030307040d501d1100440d07110150712171a4541c0e104000301c1c07001004058000c0c200343c0d8095601c41c24136943d06c6071140c240400a01c240c54101c80800003e104c2820507500038200003003843c0c22558044001d81da03840c03c9900844580005030401d012940d440d1400440c04d41c01050144014400d85007081d40e80c0f5182c0e03034050103440c0b24403441000302c6c7c6064480c0d084010b20030400d501140d180c2e46902102c0e500c9505c10050002c00624200003c10b42864550608050381c030301e0340e0790f54600c1d038860ba16020030b81d200b560261000b5000740105000100002c441d041103aa40d4075000c510501c11607011880c2c0030060f000151140c000c8c4d030030443e242c1c41d05640c0d08110b9401003004282500caa0422400640d111407107138008103940c0040d070040c006600c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 376104136 1250 376102886 376102901
    0xf19020615060708090411090d06050406421d040203010f020c03030a09020a0504110714010b031b04090b040506150a050d0602090102010b06181e0108010e04080d0609 73
    0xa920a1110703095503082110511a4100060091000b48200c81079424554400000580001d03600d0f403a145600c0f002496014401c3e0b000c81d00039807180c00308410400c96002e01110528001b400d480300e220420a81d0101d076a1075000e801c2d40161380020b000f00520512050001020500312040700392607100b06005d002d0fa401c07101a4040d41c01c3c0a1960004c000b10310845001681d801c0142d8150303200e0381c000c1c00103400712020582e40208045408520341e600c07440b4080c040c013203051001380d81d40c60b24075005001d04050b000038149a450000c099602c0d131000324022420300d03c03090082101040440020b0b00070991030304082c080400c0c1c2010003003005000544c40d40124003000c2c1d10380030342e00d0f103a04111054299008064000040c92010400110713175070040c08102c00d05000101e2401074807800310b180c540244604001076850740812102a08110058400d481c90a44801041c0c4d08040000b0308501018854501d20481c040c00040c00d20a03000c05070340540c1c4661209201c0707e6514000500649501e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 376105386 1250 376104136 376104151
    0x310030b0603060103021f05070b070507050c030c03070b0c0a080a0201020703090f05011403041a190c05070c0e0c0408010212010603180f12180b0307020601061b080f190206 76
    0x5004140301c0e160001c0d80504803580144a0b0304a45c00c480d0017140d007400082030702e40078404180701800000c0d2404107d40d00c17958541c0c0e16541c0300c4240e401d00782e1402017807080980c002d8006209001c03031030310301088030400c1d00d14092140e541e1304207541d0154500611528054040100032465000060f41034008125041c081c0da04d1002e003548a140f5141400350078071a0501013046580300010107042c0402540d803050160b1003506ca14601a080001c03e074608031011303440d2401711201400003458921401e013102081e85011800c10760b065680c071100002e203019035030074000c0c006c0010701d01b0301c41c1d50225405048044001d5480e13181a00420b02109000e01880e8003280c18202501c0700b00202c540d01c0d20315150040103000142c552506d035284200400240c0b2000c1210320407803d0688240c2d50340c0d010050502c0e1003400d56030300d02500028100001038008104015a101141e182903110710307075511a050300000000d5813000000160302251049415007402000028851191260085403543c441c140 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 376106636 1250 376105386 376105403
    0x151e0408120609010b03072a0506010608010911090d02030a0c170c041e050a0b060708040306060b191404030c0b03060406050907050d0e0f0a0b0711070f0308160602031003 75
    0x50710b1042081a040902aa121005003400003c030414440c28802e00800082c140c81c1404480c2e030003203d4001c00d119242074841c3e40c800340c0100611507004410a005100314002046090405ca4a1100b01c1c85100c828a110b003400303d8004040d50780c04c2c0a450724603544010201d01c15580e816419206d4131401c3c5943c001801001191000d90a05000d500403000008507500a1562140101001070001030a084000f0b5500c0380003183c2d0391507d400603e00f980c0a00c0c94140c840e0701d180f404030143c926035002024014414010f007604422840490b50003c038090900000740d080c5192182020b0003644d0000d84100358840300024200a000d0080d4001e0406460502909131682d0902c005840301b5641c840004108000700701070044180d20035402000058140e52180702442d543e6440c1100905d400e40e0b600060b0818005a0b941000080c46884170a501900780039103441c003c0c0c80703104c100c0e12024003003400006600fa560050069060302a5078049004c42d00c9081142c1081d10001d45400304607007154 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 376107886 1250 376106636 376106641
    0x1b0908010c08070e06160506011d010906060806010f03020d09060c0201151a07020607172508040308030901090204151406120606160f052409151e040812 67
    0xe00c01c0c441a48504816184c4000101300c80c41807101591180c80c0412072000141e01210006006001c503500070409140503c0b240508200051400001070307201c03203026490245e08110691b045021158050000d00b08840c180c80e4103c0180c1c0030b48510403000508529041110741007094a9122140320b00070307a4020044a89440e080c14408605c60007040305000000e10241000c001a10082c003050342b006d4009070501c01142d44070703080900303100e01e050f014401c00300b1020342e25007940c00c0c4070091019a44200c5520700064440d821184074a000141440d100040001c01d2880b00b5040348400680c085d208200c2482610804d0001d0111402140b42c0c08016104400040c5040401c8c2c03250fa003007402e89005151110007c0100550042d40b80c1c01d0320041020070200840c0f62900c0b400070301805075001e050042402d180200d001070028401d0085191144240b00464800255030070004154080c0f5008030380b940480d44404015030741c88042c0019120040204110030b46024103400ea88403400c2502c0f42c2c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 376109136 1250 376107886 376107911
    0x3070309090c0815030f1f0c09141c080a17010b1312050712080c01111c0c02120403200103090302060408130f060818061512011b090801 60
    0xe6600c2070700b40d00010700c034001007a0100c000c091504a02ca0b4014129134100320070190082c03c0250001d0a215070307608006c00800382c8045c7e070140d5039450243d46041c1c001c85040c0421031000c2414182c00d18003944200c100f841800030154410714010b904448955111000190003c0429004080c0082091148000010002c1102c400c3e5011141d07684503800f44141026085034070b020301448241c5440c400c0b2400003810b01e98001601000350700075412542d840220314401800c1d521410440412404108420306d10400b07100300c10007540c401c405000c1031040704510100d251a4200606082003480041c0c00801c0101d400584109202402d0502144409400041d41241e0500e01d010300941c210790300140004544100402404402c2d2021400241e100d500b1081c4180064000c100072940c040103018a80800c0c9031b03d241d20404200003000c4c90700d09545414407101c11a0703c6240240030002503000140c50a400a0840003e0000d28101d00003120a004214010314070030340d8125460300b040d0311401d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 376110386 1250 376109136 376109141
    0x1303120f03051b0d0b04060b0c0105010e15060c0a080a02030a090f030b010b03070201410c0d0b0d12031b0201060303021509010212040302031b0703150b0a03050601080307030909 78
    0x2c2da540c0203116040041c010303e0595998480c1c60220f082e03666518084140c0c2d0380340d05c9104040c0c0503400d5a280c0f100000c0d2a00741c00c403074060300302084a403982c1041085203c2c0032840704501e043c1c01d4032130507120914450154603202c40d440c0d00500f445070200d024184558000080c114031501a40d071002890744d5294401c0b00300e031440c080600303051403000050228403002c038001c64118429100000d0303080000c0441031840310003090301034003034900044400201c81c0b850070701d40c0941e070000d45d4144c2c0f281081c01d000c40151040d08080c104080e1984829281d681d5a0b0301d1500e03041d40c008800e000c040c1e4202e600180103010700210070004041e00f510003801d079031051091b14103803540341c0c0082000492407410040740940042ca501103540d000c03c40700140042c0d0407042d0340150310940043d0b4550540020b8401c00625001140c1c20f107a001400400c0803c03039006c445501d00e090813900056408001006c200d401d502600040d01900c1560300003d1340320000001446002d02a42e02d10240e9034403400007405 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 376111636 1250 376110386 376110391
    0x3180b030606070204150b04080a03030b03030c0d031e0f050f090a0309060806060f0d1d030703170c070f0c090507030c0215061f09090c030207050618031303120f0305 73
    0x401c140d00f80501e10060030a03a0104a040c808510040d48050f650300c001c000613802904604034070741019110400305074050043d40c110300c1c0214040e50905a088800940ea84140b64070b40c010035844450200e02400018807071141d42544500a0120307000d030700c00c020050324094980c42180c0420100054090001103002c051807039240e51001e6600e85800070459410601034207441d480070082180000e00e8007041d004151403082ea00d80842c2d07085016040c030319441142c1c240c0790040d070401c00110700000c0d40581c404c12481c0240382d10a005441f488100ca40314080e800c001444080036003514028000383c00614421174940f4001807105580b9418218141c44013414582d016074064481c1d140351030481c0505d150b0050010300b00b0200e408040c004112403071540c0c002040805c6010300700740a049041e00641d00c0c45c010a0406500d0a145a540c003541e80314014452113510054222071031014009100715803811400c025100016902c0c0d00f0071006e5a88040da8590214464241844102c0d00a020700d91 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 376112886 1250 376111636 376111639
    0x143301030818031203360a060f0603050d1205070329031f09050f030c120711060f0a082a070c0e1e0c090603190906060303180b0306 58
    0x505000080d1107502d400c0300744003112a45030092103581079044150750302440c4140107680300e01c0015480c03080c210114122604214840200015150b119240d000805181c002d500c00d0700002d510080c51081c200900380c40d00010719600640069054041c0e208841007071000f000e400801181d19035250603421503210b0594030b0f840343c034910340c2c0e02c0030f142c4c0284a80e03510a00140544502d0164403286e2001801c0b01e003914411150360b081543d061000c00c106448200c1c40c000011403400c03000d61416a07452140304003000702100c0000d01502000b5048030205046200504125250080383d0041d58240c0c0154a0001c000746841c00003841a0301c90f1000300c01c403403085040320b80c0607031000c0c40926800da000740419a824500b60400081c030742862071101d481400c2c1041000f007090000041c03030380d541b8005411001c6845061006019540e100801c80360404050b05c1ca058a8400a4040501030306422030060406468004004241900840c1181c4501c0c268071081c003240da1203100d18003036400103030303040d5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 376114136 1250 376112886 376112903
    0x61b030207032a0b060103091704080d110a0b1306050a021c0c09030209070309020303030109050a1b080c03070933020f070e0408270a0e0601050306040914330103 71
    0x40400c0c1a840c104d80c121406140c0483d8100c1d043c0c840801d00c5404900441c510036000408201501003803107807014603ca249442948070050b408031541d0b808410342e02402c0e81d41107101007511012011000030f1020350100e400c1c0803a15040c07a03090000d4101c00007001c40d1161004074420204030b144600b60700c6c034080341c0750110840d044d03400303003c105003000b41540b092541e1014050301695080000e54000d0681c10004100352070042d5030031003665103501e41026108007640325022600d800210040e40b058070700c02c0264a0341c1e107441049607005000e038002e07068009410340580c001c190260860881000c1140d02060203002280102d98901b00c0500230803030394100311030520200c0254081d080d0401c1c042c14480781041d070304e181050180748269500d070025464681d01016241001c0300d00d88020a0701002d0031801d480c0030000605103102c01025241f24990b00d01c545002c001120314008640000b1900300c44031416000d1191642c00d1000404107005040031406603240c1c824180382a058a5000a08 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 376115386 1250 376114136 376114217
    0x801050f060d0b03010204120f150216060b1c0b070801151b020d080c160510090e0a1d0a02151306300504020906040603050d0507061b03020703 63
    0x700000b8400f04000c9940355408000018020b460351441c140000e0240c0c601c01c003040814513246030f0901f121050f8018481c01400035442d006150040c203d40c2a801c02004646880c01400098404550079994410041d03148111001d004100c045c2c64498486512a44d55590300c0e41e0000b0750f007401401c9050009461701280300d0910001041c5000740620161103403001c034910366204821340c0c0240c140407800350711180707502403d0740d004800315005101c16201721301030000c5280c000380b200d4014050b114840d985000410b81d82d40c5540d006400084800840903420205640d10944070010201d090b40b00e4080007000d60302c402c031020105c0300c40e00e49444490782c50502d0300d00c0980310401696900d40b10040c403000d1212070f0342030190f40c0080c0340c041504001218a0a88104950400098145405140340c500305100188000802000341d01290504a17119502490b25101402138035085180d40c035030981804420b650140c000d407408921a4a884c1d5185400120130a01ca82c00e0071020034080041000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 376116636 1250 376115386 376115407
    0x32706061309030c080c0606030607030903020d0503070c0b0c03070f03181103030f0c030406090e0f040212030c03160209131121010c0f03050a0b010819020c0f07060801050f06 77
    0x4038442c18400d00780603500071929207034022507402c41c1a0429203a08520200b0080e4a024800c29510801070306040020401c00c1c0c500a5039818104a05020301c00700001181045020301c0030082256071190300a5030034909841941019003054507880042800c0b07a0451421500038060003030300e841035400144440c2d1442e1900f5200c9074101d42100d030540000c00000312141ca100d0014101c22201c0c5005595032403804800810268065015001580724841400595640d0300d40c8075411a80484544110403800c180c2e4608600c40c09080048503c40050400044400001c684410900032aa0f0301401e07600d48040580307421300c01c01c006103990300307511100009140000d40b0450240384002d0f40e11040c2131b420b001e070782150f03444181080403400020002803015414041c4950010b0422001c0c01b5040c0302c080064480c0a02400c040001c450a075202d0b0b41c054826411b491289080b5021104400c41285030b203070300ca580c40e014090010b20007500212303240c140000c0c1c400f4001c2e000340040e0b252942004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 376117886 1250 376116636 376116641
    0x50a020f0306090402180f040c1a1902010e010c2106031e0c0306060b31030809060c0703080d060e0f13320c100e0919020327060613 58
    0x1081242c6c01640e803040300d207010b100c482e030301445014040c82051590620341450308000f9055480075400d40000c510091402c03850100307480c4a081101c0a1001004243c882a409000f080030000c1980d03107000c107602d0200c4c1d404100e08201008034000300501d40b50303550f8145c0035545d03540406041c0000c2030342c28094041040c000301000c80e000380760354030810340c4980c1c03400223490b001d920241e020880880c41c0c11100c0303c000041060404c06186040c00c03070740140004528900c07980710281030b165000c110010380791103800446421003094019500039984a01c0c010000d03800c162115207103180f80c05000702e00c1000c4403803954001c2e031040088045039525031985104100c070340101243d603180d04204c03009441907a105410340090f074840703141c48404290f09650307203092583c00049202c1e00c1882c1c0b03020241c5401c030036400c68020040d110710949a96481205d80c920602c403072103203140c80c80041000200b0300034660440340701e2421040713240c200095884060303a80100703607030301c40e8440701d49506041c0b0b901103030313 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 376119136 1250 376117886 376117891
    0xc1f09060507032109020f03010c0e2e0302210408090d061b0f0f170f1b0f09010e031501050402160212030c0607021207030f0e130b0103050a020f030609 67
    0x80c980b500a40d61406440d240c40420f20b10743e8000c00385c460b00c20508503d032009100ca000c407001e600802001c8502c1c074000340544400d1a1b0b041c041c03000400005541c0e00041400350307001d11490254944c00901840090096000380c2d0100044c507084491003840703820310402c660256400050032130070300344550304026503c00501800c0318455901c0700c1010400c50b0640d8081006100c646400c1e0055034620310280051400c0c4050008006041084201c3c9481c040006908001a00c070100b020380d1b940000b01110034103500251409500c08242116412800700003441110003e83e40c901605402c0400c3c15910800132210340c402e020f40800520190030180d000e091000c030b681301c0c060020700e0541c0106940d00744280c4524a6604001240304069000300b00381c5401c2200c61009002c1012a43d4000b41c5500440c6401020409002c15400391113100300c01d045100c0c40c3c010407118a110440e1440c0d001001d809036200c3c00301e424540040d03a038488030302c01d650b020415001c0491450f5206010045181d000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 376120386 1250 376119136 376119143
    0x1030507090507030b040c0807140a02061303050c0f0705030714010804020409150603080423130b010e0603070201020a08090d020703350301080105012705060a080f0c1f09060507 78
    0xd03603100360101d58950151f0444500c0b182c480b400d1030f08140700000d000741c40c10a05800c04180801100101d50b0f4005200c43e405071303400d540d400b0944d031186401c4945115121021850b4812004905406071300400c1071011250214100c1e209076903070b00551440320010313411060110f044400080c01609007500100c1d05c10380b10707100c1d0700120a0044031820841d0510b4109480042d00031905000300c9502c1100303511840305035001d0318040d0f030800002800103040035107040052a1035410b00801a4020312a1030407002004101c0345c0c40c0c1c03500c0e80d0001d00030340107070307500d030001422040100f450000c2c0402e081c506180b035580540609411611000881044680d2a1441d1400305003c0360010110721400108111804921581c1c1e500d400b8845003510010b070001107401c00030508000e0b400c944506e03c98411100ca210200b81070b07031041d00045020045610205850285d100e41c0102d4000210300e04c5905001201c10780d00c101c04000160b006444660400c9000ca40c4041040c86038600850203041a41d11 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 376121636 1250 376120386 376120391
    0x405031621210207030c1202030f0c0d08070813031406071d04020a18080a1a01060c12020c0d060510121a1b04150306060804050a020f031905061006080103050709050703 74
    0x5c2e42c1c0c5d504192071981d540300c018001a0620b40e4000c5203000d0246001d1300d03e0f200c00900081c401c18000031841c2d200c900b4000d00490000a01c00104030294040e904800a01e038003032102aa6a070428000307000551400c049203000d0f05c800158041e004410a4a051129113a501180d0380300c0070601009610985101c41407145c1c40d44054400464210280b02824403900500f8100440b031801620548a07000c100480c0701380400180324045c0c1c0060501c0f0703099000b51407440a0101c595040e410441990a0503070808504400d90040c4601900041c1c01403104801c40c0c0e88003a511824003c0091007050300414504007040310f45000c80e07000c03001c55001004000e45104014851401741c2003a400360b0b02051280310300a0094540f0390305031103034000501c0c80e420980d113035280c00e9070b42503143c90f00498000d00c03400b068401c184054404010010101c2280b41400307055411a003040d079602c10080f40c01d403008001c03102c0f02280b01449003070b0188c102c0e9440401002c0080c10202c03044060003000700349400b00740c1d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 376122886 1250 376121636 376121639
    0xc010305060a121202210304030e06070227060d03120f18030f0806010504080a030c0c051201050a0b0d03021c0212070b0a0f06140f060405031621210207 67
    0xf001c0310b401d54942c452075a0051641040c280a4108055110203807003060200701c8180441e0030541c12280e12652529040400005100025100340a1400c0c0030f900040342d1008c4956030f904075440400030350317092400103156594000420050780403807400140090741050003030404401d29000111100b44114000ca0381e0b5602d07a0348010071110580080c1c001400381040d07441160741065500c5d40019003881c11903d42400c05d00c49560f55811b04d070b0014104000640d10b00103005c104d00021000e4400240002800c3c80520551070103031005030344400e000381c076001c0ca050203031804540314895140d05402a0015249810b40003c4002d800035003103066020300c0c40e4220300585200020060544039282e00d48032420002c01c4a01126002c9148051440c94200b06102450b0340030310940007151704982000d030042c802004503017140201e83c4042c3c1c00d446400703400e50100ca0b100310504107035a05420f2800b65200040c42c1e20040e4003400c4d0300075026180111700c03208005034041d1216000451030040341c0005 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 376124136 1250 376122886 376122899
    0x406080417071a0a050c041e080708010207060f15050d14010207080712020a05030f0d060503030c03090907030b060406031a03060906070e19090509070b030703020702010e0405090c010305060a 84
    0x103901c01d20342240c50b00c40c412000b22103c01d0300c943c280d8010074502e5040069150040c0e544c0102d104a000e0805620041482015203804004841d4050240d01042d106a07507603a4100a010f5000341208840c1c5a0503c0e021541200d054440c0016003001c0e491408580e03468601400001842c480080c0c035030b00780c6c00a049542c05030900040880910441849503185041d00f407105403040054401800c6412550510000c18000416290b0540840c14019510b903180080a8020700d000d82c401034150101141075110b50038044054403584105a40c0d030040e60341c600004a08442c02d1150312035200724144000e1061921980c8500129043e8405544016101000103031402008540f091003592180042000e04c55100d50511401d10003541c130000d07a1030007450a6078900e0007500410880554500010f00e1143c02041440c0045c8142c40840740d585c145031000038080c0d40005403e03800710b00c4450001019051610406216803070301000707040f8442d200c1b0011009044041c05841d4414907408000c06d41 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 376125386 1250 376124136 376124183
    0x1051e161205030415021803060103120f1b1e0b13051207050c040c051603081f0608041b08030a080f070302041a13150f03060902040b04060804 63
    0x10900d4500c40c1032032003441494104169618001a1070800c04180140300001d46004002d81003d25441c5016882e114940000c541c1c001080b403802d90f05100d090000028044514015690703280a60b40e51480e000744413001755004609541c0c0c10040c42d0400003040c011a602610711160110548588030214041d500c0c2c0301c01c848000e882d2002e55a070100c814008200c41006503203900d10b40c45003000d0070704400703403241602e85540c94592401562100d60914800f0300c120201d855980700c0100c1180e65204030b08000b4001d120440304296415144c81a50341d0040d803840d07822003120303d01d40d940c02c1310703542d603588656400340c60b04088400c84403070240c00f040f40c400c1400a000155029980d050f813070702c0e041325181e031000000340c0913101b89031042001b84150113111054050540034400300d04c0e901c9a4688022402a9070f0b60310408964220710280d0403400d038000c010ba0700400032941c06215094403100307000c040b445a4840d80140e0302c0d00700401c1220b0f502600c00140d005000b000d0820020000c140c52046 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 376126636 1250 376125386 376125397
    0x31902010b0603150a08060c120a0608030f070308090606090703020a14041526061e0d0f0312062108041205010209120a050709020c010b040c0e150f04030201051e 71
    0x5035400c6040410020b41440d84d11170000b8204000181010309106070000741c0340c40b0b2441c400f020b01c203004000606100107a04401c0c02012214100d039604c00041000540503008050304070002118070001c501503040c0016218020706008240c0f207525120300205500a520031000f8906000c85502d44206036440c43d00074200400350f00c408a41140c0c030780c2400602000b402480d00b00b03040c20380756088400c810034840c00d5030f100009803602d45042c0f401400400ca0342002000803544982c903a2540020081c00c0240c41c04a00d11039200d013104410f20b4000070060781c3c0716004030741094881d4502c0154043d0004c0340d0000c00c500440e070f16460242c0740d030099054001078140c203075a640c0d00052085d69900341003c02152240503203001d0107540d6200d5684544880d064850000c0c0e4a4001c24010b1940100790300119900d83c0c000c208000034010181d0251440e40a2940c441c804d140c00d07034003880034640c1039080320b2140151050451030310741142d0040d903241d000384000c48110101c0a441c540c455000038020720 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 376127886 1250 376126636 376126651
    0x10e03011419060b0f04030b071403130c080a0201170627250203040608070e1804020f04020a3e010615050c06181f0218030d02031902010b0603 63
    0x150b01c0c0000110309400c0d00c100d0707070000c4070500c070030040002c40103284000e072020f50780e10201c074405603199840704480310012031084862000d000814403003942c08104410000754070508404044075a12425181c0b5104c8001001c2c2c04204031002c0d020540b0222000141d004000401c1050790780c49141140d0300c2c21401620009041070307450280f0051550400040025403822034041000c80402c880c02912400340744102d0042c050a280800d10603805040c071b6288491015000310603030071100d00402100c0c94250b40590094004100b00b514170f09041c0203d0310030102c0d40c0c460804421082c250034082001c0300d50058281c00505400c40c0c801c103c0c591900c680c060049002140b2182841c06a42040900c1a070010a0040400c104010048042641940f00b940803003100c058960312144142441250341030b682c1d040e8084103050340703018826400341003040407128100001c200c000080c5a66150010300b4107016038400d0208038420f820a402c40380071041e1610002c02c8402844020910355002566201c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 376129136 1250 376127886 376127911
    0x1a130b0f0601120f1d03030402030c19060305091e03090108010504020f07020d0807060c170a022b0906060f0609150e060a050409110a080f1b0a02190303140a0b0609010e030114 77
    0x543c501080700f030bc10210110b0b19181c1c210304245401c00756024030301c288801e0640350b00c0041c90014041c043c00c002c0420b91040311a0355400c950105031681d00441865000c2180c43c0008120b6003403274800d5401c003001c3d110100703140903826000c0000c40c0c2000a400c035203900003000104c002a149024008150b0020f072552004c034541980308100541c001040540441c0c030611400c114190208204520804e260090200071481d81c2c1c0d001001d0501c102015040a05010380000c0800c5062030000032130b8016655a900f01e6101c000041e00c2c05852404000020402c00003180c0d207103882401028030400c1c0e801c203140307800d507501400416070722502c0603401d0706003010034080482e0313070000307211644102149407105042c900341000c8460b41d110000f121202190104075802c100c0d000f00072250280100280040f001c003183e1900401a00030707181084c00254002001c02d644160a02400e441034900900141c00d1484101c01101d641c50305104181c0d2540d20f50965411340cc0b400402c183c01600400c501 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 376130386 1250 376129136 376129141
    0x50d150b0c0703120e0303030a09050a1a01061d0306040b0c04030b0405010606030c080f01060e0105040b120103140a0305090f04020d090f2003070905041a130b0f0601120f1d0303 78
    0x40001e08050030310401784504100c4880869030b02000b120303030000c03041c40f000442003064108585070104403d0004c00412003e0303401e519a4054041c42e504899541c4c0c0e62a000580c50b0204810410204000300d400d40e00400c045000036080c01200c6034026006501c070303414142d80380c503102d40f00c06094500351345a0f55210020310081c0c1e85409060310a140504049181e810501040e5a01c0b075014411002001491b000300c12040c0c0c840c1040351300600448120b552903168240c115181c0e40360a102c04c81e00e046c03240c4664181c2080200f20a4461b640640741c6500b0200c000083c4413482d84441541c80d03105500300545511014079109600c0f92034012001210600d16514000340d4030800100145004892280b9404140d42e0016000c03040d50702c0031f0800710b0381d500c40c2e28040c04020034110750042c04660a9003000606584d4201d20103506001c0c0381d813100507440e00021a10001d03400d44500c2d000600c2c01c4c007550400c1010b9040791810000d0003000148070342501c01005000c585440c01081c40e50000000e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 376131636 1250 376130386 376130393
    0xa0b0402131d0a0501030f0b071b0b09070f2102010e0d120e030705150d0f05010b0c12130b07050a0606060527181b0403060915060501050d150b0c0703 66
    0x707256903c0040d0704420019075066881c0c1c0303d80518540c00c002d146481c2080029001c51241c000c0003c40c1e406000719000c181520701d0300c1c1d02e4907842140c8500ca94810160009010f09800140004980c1c0c60404040c2d0740608020b0245507210060003a41404039011450350207450700060300d0742e10360280c480d00d2010a01c941e40201103030b010030702c0184240e000c03410a10899481c080046003c002d410003d80d81c500c6194880030250030300c884044041031902c00009500d001280013044080c800c0b005854200c1c01d00050f161050080d5040c2d585201031184091160840c4a002041041d0180040340d0810045079217680c26a00b03030390448000101c003c14171200f158584e201141840f807460414507600d03100c0c80c1c040b03545a0b010b6110140149a9600418a401c1007100291034490180054a6a40d038490812402078450b14004442c159640034185c0b4190141d486980241c950581d506450080fa1269600140c80c500384039044840060800040c50340507480100400310382e11014201541c610308 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 376132886 1250 376131636 376131689
    0xd0b010816030c0b070204090b0411030f0604030c2312180108160309080c1c0e03010506030601170c09100812040b07080a120c08040b060d0b0a0b040213 67
    0x801c104100d448404040c00002d1200001c0001c0d2100078403000d441c3c844600010340a004420000b8001d0101e08041c08284400b03540700000550041d012950b103c0b0700503105903590082100c2c082d0005040007072000020f0044d100f90008440c1242800c1c8402d000500e100342018402d081d0110070000000725800a4034a40400018080090030040380d00e240201c968014490720304518020160313a03903030000c01c00042c01d003580da0f5822210110352003102d12180c0441c100344020207032400302d4044400182d151405000d49441045c0103009000d05920f4040c045002840c220b0032814240101c0c0d04e064690384910481c184198060820f0030384640c6400001ca040c100541070190140d1001c0009000756101441107914580e845000760b56500071031603089440c1c0749102c3d08003100c42c0c200101503030020f030f0141409014a0044c0c1e00224030752540380420400f41005000109002c08200000d00d00201c0c6a000c0b01e60710201500161821207040002200c0d0740039608880c010022140c4100003418184 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 376134136 1250 376132886 376132903
    0x30c0501090e06061e490e12030901060608010506190807050c010c090f0905160e01050f0301090902091006021009020f0306130c08030a0905060a0e1c020310020322050c0d0b0108 78
    0x860000401b0041c06560407032242d1641700c03140d42d03031180940c40d00b1210802c0850745035260806011b40300e003000120940070b084076109a400140840001246c10b140c1320303045130b081c50003418003002c1400c2444001d5445080040c90f030000e01006206020203038400780a08840052540e698404441c01c20250300c0004003140c000800030b40c03a007c1000100122038010380c40003150780c00c0040c00e0640240040382d041c031408c6100011000c1c08400055805041d8021000a9100b00d410309115552104100f1240c03050384100c40060b44105005046d05500d0380c08070307041d00d0003d4829182c0c0e0040402007441c4c0780c4251218102052000c40c10818401c618164101400e0741c403014510f019030b10140148405400c1c081c0360b101e40000929140c403a405610f07522004c0d00d015007856402c0402a003190002600360301d080e80640181c0152000080742c03442100c0c419030f00c50000c0c100403043c43c40c0d1003152501240e4100ca40c0d20034104d42b120325076204c001c012406031060002440f15810f0044160810303100d03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 376135386 1250 376134136 376134217
    0x6010f06110d02070b03130c060503160806012307022106070c0201201e01020a021504021305180a050a020a0b03060306010b0d180804030c0501090e06061e 68
    0x1000e02e4426601048940c1280d0045554641342d448a5980402250b440100142883c03075061001840e1900a0040c40c030511002c05000403520300c041080d0b0b40708a0803544c090000700351900e05240314108811189015018009060808082d640400e1410483c0141c0c0c0811668001007214044400c01142d80c0c4114103162100c1c40c0032079507001034441d500c43e1a1031236840c25601c010740c0d0301000402200c80442012042886008003100d071440c000c3d40700c070840000500810103000075903208022494019070380a440300450060591615004000107480100301000b402103000d0300e000200301481c1624050000341212040c03510400601e042654400d424040c002d100f0000c1030340d0301090719411510140402a5030714a150201801080040d184810b0f58403401243c5c82404550000340003a03901c00c2d00702c4500340c0c1c0c44100545481c0c05600c1590030010303600001410303c0c11f101019200f0060100e5820340303850300066060003182c201c0c000e049050590000102030000d403504010120ba0316 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 376136636 1250 376135386 376135393
    0x150403030c02090601121a0325091d10020408060109090206071b15020a0b0901050907060e030c040905010b042406030b060f0a090602010c0306152006010f0611 70
    0x599a00942142070301d0402920070054a00002c503140d00031300701d41c0e08052520f0420000020702d000010030030090030541030f00a125060042140340c42003801e2460010106190440c42e84c40c01c3c0000001d040c0f2007440015020300d008080c1c4248001300545028141d503801e0160301d403400d1030101d42c50024140d1101600608100d90380016031244001c90b0000e5401554240c208011164170010000c4264002c540001c610f00244d212260b01284002c0d00b14840c00000720039807264080d9500b0313520151341c40c2c4180c0d0003c40003041098090154444001e401600741d62090400000140c1100d040da803040c1c50503516855106e05d40d1400788030348152a00d02e14501c03428241000402c41d900c02e02c42c002d010a150313480d8003503003440d542c24007510034045500e007a80d0307620030141300000c100a211344280c80140d0300b024440744049000e03001d01e1054958444000c07401042c0315008880003180c500115100c5206a05058004007041c012103000c0c0c0003540980c08440e19008005082081414100c2c00030740 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 376137886 1250 376136636 376136639
    0x602031303020c091e040c1814010503010606050a26240307060518040605040c090303090b34020d03020309010210050c030a0e1c0c021c0c0e0c040803030f04021504 72
    0x84030031420700b040030380c072501744500d0703035540c503040c2000e00403504000c20f1a070301900c280c6ca41010940040c505401c1401070007480c0d0b40c2c1c8009140c01d8442501400e000301d10180300062086209802642071004440c00b00365152200c070001221a000a8554100f012070b50b14035840000b0b14054120300ca050150000c0c84182d160900050441c017650f2030724161081102240742d02d0703640d66001035000d032a00610400c080ba1203014041c1c8511300320300c001c41c00710744c10000000c0d0158001080c8c4403041d46082c0742000c4100e1a02c02c003043c1c20400090100c0c204609480c510158480c4406102c0c7d5501c00c0e00116980c1440100280c5440c01d0000301e03a0901c0e041500304a90882d8100503250041c1a1190200302010001c55840c144031441408007541c50000c410411116400207805140038000e0f03500c0e030086c41200c1000041000080c001410120581c8000c101c4091040c84496110003210855801c007030301d440b90241554015518980e180d102c41082c0030075840c002241141c00f580c0e40a000381b415 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 376139136 1250 376137886 376137901
    0x609090d0e060a03140f06090601090b070b040f080a21091505330907030902061614030a030b03060105041401090903050405040608030d0e0601081203130602031303020c09 75
    0xc52088407103005000125603805014080d030400340c071048111401da5002d01d4510300078000d840003203030428424145000420085e5004d8040310090700d20701b960241c039058441e1070b80c00c00d841d03028004580e000e400802c2d80c00480c5c150300180c0120b03900765030341d40d4884190000c403d04440312880e010003201e10708102040001c24081910540340320704071010803a035581080000d2103005090030688940d069424a40c1003000308160071507164002c4a0401054680ca24114200d8001c4800290010010414205c81807584100e2111007440b4044810300a0b80c40741a80f81150480014580820784511070f0807450b180900036940034190981d0100b01c07401440d10310101d8030a042c4100b0042c0d950f0707000d00b0000d261240007101d0207000058024030220355609815540c81d0b0129400190191170007101c64095071010034402e0403212890010110030f80401000100c5a0028040c0681000405054000950b840c00036610501f0381c841c1160f86143c042c20040d00342511054040e00c00c80c881010070808 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 376140386 1250 376139136 376139147
    0x509090d030e03120103080a14090d060506030f190303110a02061803190c02091b030105100c020d05070f09061505090105091206010504150305061f120b0609090d 71
    0x2a44101e01d00820380400c542c41440c254812030500c14034080f00c2c10f002005102c4928010306110005031740c0c02c8222a514151310b006802030000340c5034000300200054011405c3c0c0c4c0c000f140c0254000741503a20a4904aa4803483c01c82c10910020551a40400042c1410f8042c85003111800070129058a080800760009494520082c0000689544840c104030301640c20010b0300d0900c6541d00b0141d8640c0e0070f49502522032440c100040307120700d0500002400044070120022005003036441d03500d0459090004100c0d0082600b004582007000d520070300f03000340c0e0300d03400c8007290f182c003030800303015841d0030502320700407101e92a0002c42c0110700b82001004496000640c0410100d25454081c3e100e410070300048400344600c0d91072a03071111400d6644050600003061541c1244c41c112030410a98220b2507044409407260320001d009504100000340102e864038015154110b055804622615224419000a0780c000e20007030341c0e10845030003001410306000c03c00d581c001c464980108060b07490804001d10 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 376141636 1250 376140386 376140403
    0x3101109012007030b041e110f040902090a090606060f080109090c080f0115140108061311070302060103120921020112060602031306050901050d09050715030c030501050909 76
    0x40148181140490720b41480300042e03200a0070003036070300441d40c1c1d08280c01e01580994040e2040c6a100405040100d2003848100c0e645911200803100a8030500403c40803004a00c1c0054016881d038001c0b200590321310582c03d00c1141d00000001e282a4a030800100300c40c60b98000d002840800012121401d400091103030440785151804141000c00c1c0c5481c07034810140d9403141016206a403100741000f10f040d0488a50701c0b12a0b0380050b40d00d503440181020074a02030042d203000c00c8010300821014281102c54105025000f4004142c94045240c0040303d580121000d40041e0054030050081081003c00c81d40c40310440c1c500046290300780015484480f0103111380c2c0c0c3c400042042904110b90082031914017040108500b0000c161351950040d4981e48002d010658900e103080c2c2c00315149010b1070696804076410394520f82080c2d1541000c10040c0700098003554035104d540c1c400102400d0400e04201c120000d60360102d8075610845c0007030f06464042c0c000d03500c11118101081400140041c0890 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 376142886 1250 376141636 376141639
    0x60617070e061204020d020d30172d01060e0a03020603160e10030618050405070b070303020f030a0b0429060d060504050106050702010f02190206180409030e03101109 73
    0x9400c2d01c132440010007281c01d21400030342140100d02034009001c4010105000381204404220902d07501c184041c42c1590040c0104020480c0752500b501031116004200754090503090000c5041c0d030441088412690300d15001103d40c000200050041236400407030742500050a449100005081d40d002555501004101d0b0011500c654407000c0d00c14032410002c0c1400c90050f02c60302c1081f00c80b12005000e01054000e000c4004441c0c4a81280d41080c1c4c42060311568001026042a9003058000080c90707010700419000c050f001d10405108100e03d2000754010740000d400050505a04028407040c0d0301c13045005600e901201c5e03440f01c1c1901d0740400070118203508a0f00c441d902d003003004c2024001c1400c4d420294000e4503050001c11f80540180041140c14000d81b070b0749003002041d0008a95625980d005d0010040d050305050006003064400360105100300160012461243c10100341151070302070054002824502107206581014456081e01c182e801109206002c055220492240710307010025 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 376144136 1250 376142886 376142917
    0x3030309020d0c0915050603040203071208040b13060807030e3016031e0903020d02061c05010501114308030307020d090e0609041104060617070e06 65
    0x240c11540c6100e00c1021071036011801c0c00d041615508003400400b084580003110140c102c1012500345040010380b0b00c034590040040400c0d908208041d0004405403504440c2604103000120300814001c010301074100c0e130186a0350b602031400f24020302c1007401521107020f1501d050b44e41c8103030400c00b00d0334142180b41c1c00701104000380c24010904041010b031010641641c0b010401285108804c0ca00c0790140307001e2395070800c059041009520440140d00714000c042000c1050400c01414040110500345000802c840d0030305c80180c241d040c001014104440f0314596480040c000b960700010242e41d103a050300001d01150403031000d803401d20002d0901810f2007041044051081f04d40840d8040e00c0012441c80b400321650f0744282e02c1381d403508141c61074405401000c0802d1420b510540201c02100c031804400800c1352640703400c0c821500f9016209a851000e084002606901c070b034040c0200030704555031250368081d07024290741c640d640058070348402c10400c50101400b07695500d0948840f0002e40c03095 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 376145386 1250 376144136 376144151
    0x10c0302060a0b060408030a020102211e09120a110d020304080c1210090803010e280e010603210306090b031c020a0210030b04230718080a06061505090109030303 71
    0x4d440b800b4681c0400d1729480300050040040340c2c1034000d0b09204c070003648144454a940b42d410300102400722010309009a038000c0c80c89507880310080d0160401d80d0f003070a840c40d42003c4c1400c1255907215003131800101d050a400c8001c60300c0d00b008200d01c2d070307440c601c0518200341c00c1480d203a4480072444111442500310b0030141c8007c64041c0301080244403c8807080141c0f0080303280660807908248606881d01c2c040500050900c0c81e5100004018541d51542c170341c00503001c542c40030003400c280000e42c0d500c0d0b581b44400310001d80318190315103102510040080302c294a03040020180c81c0c4c07a8110403d80c0d8101141c0f40c12548001403a42208001002d0803101c80713a00007012071074840c9001c40a9441010750b00c01071a6640c05610400710050155000d000c0620100b8140d9015619116982c400052110002d04644c1c0303c3c488584500385c01840344105241e589603107603d040b4880341d00380c4110b0760b15403007004042c040c2019044513107100e00b8158100340c420000a800c2d440184006801d064407200b0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 376146636 1250 376145386 376145389
    0x3150f01150e03070801200a0c0b0a14040c05210a11011e0306050f0f0102060708150d050f0c0a150c0305120a0605040c0203162303030a1a010c0302060a0b 68
    0x9005040000501101c9045a1701d180b0326029084601010782413090f02c1c074407070744005800e82c2281c41c80030103511103618241d02580c41034521403008051030f411030b9643c804940e543d0303440c407074240c012802444101050340c01c0c0010403e0340b80c401342c1d414004031800380d0761913040701000c00e070445840e03006810b080e56100510b005031907920300716034141c00f00400500c169090a4050344002c0a55205079030b1044800e0141c030504c90100da05d0440f0724090303400400011102481800140c2e4880e8821450802c03030000c010202e19160100c0a00700c40c0c40e00020300515903041c08204110f40b0f40e104a44800c0d0b0703e460100c216204411100140702003210190007242418014001c03985940c3c1c0602800400d4070384a104078000300400d000d814410f84c00e000d2201d203032610000580703116202c201c0c00760004030000c1d601c1070500915032070280d100403140e01d018902c54000340043d5201e01c8103444003042e2b642500f0090312030f001d08820000c0c10300210b410403001280d40000d0455000c60141d03c0010203511800 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 376147886 1250 376146636 376146647
    0x1605122b1104170706030e061504021306080a1103070c031b0f0f060c020c0303090402071a010b0c06010b28200a0b090c0d0f061104031103150f0115 65
    0x82400754004400100041c0408440b8460241c804980741a2180d0301c0d00d458040341074491070845000580d00820110b07400e0b0703035810400c6e00c103980c00030720040c03404a01d14103000614625500c8500422104c8040107400605401114114000c0c044258558030f40490007030f0080d19010b1000d000c12090301c100c5460100c00080038136482c0d400030009040000320340350883d14144041c4044031101d04203c4485141400000e81040d0104020044c500f0b1908040038400203400542003600c207080402e18851580ba0707001c20f07071030103400864501641d490315032030903a14041042c2c1c404490700e181046250026084081070b40e591410800c59140d460611010482e180440101c1014600703c0a60103106200c0e40021a608421710503036800e440c40d640d070100242c031044000c884980006610b5a40301c0004c2c1d80c0005647c043d4400c03c0d0002c0c801104500c521044e4002d60402c80d52045604050740784e519040042c0400e148025010445503c1e10500c3c0c0c05440c0380c1845038040e078203454441008a41d0090 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 376149136 1250 376147886 376147901
    0x4060b06070609110306060901140a23100906141614030316080105060306150c0106030c0e01080a150e0a210f1403041709061605122b 59
    0x5000c10384614050030000001c00c0e41e00700849074211318942010700350901040c2e842c4180744c01801c00c00603a10b0040381010f0303c84c0482403980e0007810610049824004401d140c5614404203d165092040050600540501419640d82401602d4100f0007205610440d00c000d4004540510340e11207440341d581c0b00300413a80410040550804180405689170000040c600c140c0d04003006081300046188165000300081c000c2035013103101000021003e080c02d000383c0098603070110b2214500003209600600319140e80d0000c0710201c4100104004106c140c10446001d0180f080203401000d40c55540c840380c1c000540d08202c0307560740f18142c40004100902400203210b0704848040710000311140015100b404807085040450340300c00c001142144a03d8208045510344030302545541c68613203c0151041000601070420b10080028110989540b03014240e40a00c1000d0f00d1003680f032500e403e6003024142c581e40f403007580303061000251540020309040c00c2c204841e0300c400c1118104101040151412 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 376150386 1250 376149136 376149139
    0xf180109092d0b0105060418020f0c0d02060109140c270a0b030108070f0620071a18040509030d0e010207140a0501050a14010e090c0a06050a02010608030c0706050304060b 75
    0x1041c2c89518120794251042840d61040b1918400c903a203035810002c85002e00d014405400c0320340c82500d01c15070203036030040200302c00c2c2c56030b03140c1426800c0310010303d4000705400d1400160010401008002054000d503106c4031012007400a60b8500042e4811030b6008030300503d117154200d41150700e2000502400c844d042240505903690054039049003240680c000c0c4142d04141c412100d0000b1030701c0d600103000c1c06071182d5036541c80030100540540c06182001602d0b800d8103001d000b500180141114000180d0f0900b9103038010348031005000c00d008204023a4100600807410902001480440401120613480881c0000100b01c40354400c0e4600900492000410944600c00d5245030f0321b03000101e2100440c4038100a00c1290394040e40c1340300b91108a0764424039103102d0720041c80340c5107503008200c1d40501910101c410b0002c000002541c46882903020402141e40012145801ca83c203000d00805400c5260040d807624803041e551981d50011440340c2e4081210100204080000b607402000d0310840 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 376151636 1250 376150386 376150433
    0x308090c1f21020a020f01060b070f0606050d0f120e06042d06021c1b06020c0307060908180910030605182401061e0305070e120a020f18010909 63
    0x481d015a00003035020344c00400140c031490103030280d51001406040203481000c0c0c0600c0c145402030f41c890901c0f84c145d0a0403a0303101d84030040440c0359183c1c00031880e50f050003030051403400e500720f0030204c2c400810320b0403400801010442104054541d40201c0e01101c0051580200401c5c8034540c2c0030301d415180e03614501440c200000019415030004481101640603102c141c0100d03294041900c402c2d1a0101c075540e20003040010b240420a642d02600b080b641c40001d0302c0c0f4021199035114201c0f0060b04080381c100d00003040c90180091003842251100c181555900c11900702503843c1c0908003418400140542e07142c0e400501038080c00f0a060180700320348007c0b142c15190460b0071101a100c104900c0d111b141800c1d0000400e40e210b40109648841c56402d0f24040c0340c02001c0841c082e000003010781090040105074010152074040100310000648000350440300d03514410070040840f1690310600c81c500c12280b09078541914a51181103841c4240000351400191504042d91103c00150072034045 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 376152886 1250 376151636 376151687
    0xc0318010e060604060609080a020d02040609021b06070309080f03060a05030d030204230f12070b0f03010510030c050d051902040311011e0f0309081b0a0308090c1f 72
    0x100c1c00a50039004100031102441400d48892044841103c03038881d4240a030300c503189101c00b50601745000385865001500201d003054503034259800380d13481681440344022904981d0460b01200307000a51304110326140622540750350b6260001d46007e601005c405505001003c0b8100e5540c1686500080102038143c0b02c041c40c250030041e009402c58419058140c02c0480010304004469001101840004003240008074a160507c44158203411410003507201390071010824220071030141c15a0380c0c07986032003952581400148031100300c805aa007414982041c0d50a656150084240c40084081e090002041d6030742842c2003148220b220303150341a4074400600407060015a003121020750500307807283c00900d4240024808441109039002e00051100b10744d480b42c42e4400e400c09003c65005402450a050300c20f040d41c04d01030040151007881c0d500001b400c0d4100368100f41000d510082c0340001d0a915540300001c0f4500524200c00000d01c811090019810740340500806101009000301011008 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 376154136 1250 376152886 376152911
    0xe010902040e0a0b0f0606070f05011d0106090e06040323070b0c070231150b0a0c02031614010f021905162403020c070b0a050304020411120c031801 65
    0x10003c0140a0724403141d03c0380000c0a01034046240381c0940d6014118910b002919203c600300c5058043c0304680755500d900c03010801300841626420190700001c00002c2942c0703001c01030002c455035010402e1464100d4010000400c0d008800b10154241d005c1d4002589194101c0304141c07403181910042185118078244054006c80c0340140c8902e0b44240c0d2104990f803e62807034200b030381c0500e041310034600780d0807103104d500360780c1d65000305280c5402903550450b5283c86290340e11864008420400c0010700000554007940340410240d485030303202d040b0380460b007400e094031004101c60f80c115450520000da042075044d00d01c204400c00d040500b60305044950700315031400326102c09924030003481030424400041000034040e9461002e41c0380903018040348440020b400da0181d00034005464840c0600b8038000340f0070322400300610a01a04d50380700f59880c0303010b10411003269100b12580c001010140150303140501a0601c184c2c0241050011036141e03514030101b80d02030706038091060300079400d010290405 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 376155386 1250 376154136 376154143
    0xc0c0e1306061d0a0f140906070215190b01050d050a0914030a020601120f1b0f150f1d04020a03051501020a030c14031308031305031f0e010902040e 65
    0x80c400e40c800e0000e00c0d900c03a01510320441c0c403821410040f11000100701c86040660115404101d40d55021039941c400c924542110001111a2445600880100400c0c1c50341070104410000c1d5200d4814024102a000c144010350810b201c94050342e911401c54110307038000c00544581910402c000c1c40740d46040c0c01808060700000004031407810300711b00c9000c1107120105c10b13140b40a18580c000c00990b8646021a41c0981c45200c0c143d030003500d945061400b15202d08100440720520001c40c400ac40c0c13405a510312459980c0c3c2c0007100d24800b81c1c0c0403080700d59100e100543e5640741c40c588001010304551108400715130901080380d115200107600e80318079401d40c212903c150401041c60010240203c01aa1101417288004000994444ca0030000a00401c40202602d040d0804c4030f00780009102c0c41800ca00c00d507000305030f140c0c1c008503861b1a1500c903000060098007003a40506011070480b0781c036113059581408910324540c2c81c1d42164000c01025840003010f40d0f002842403004481c448240c944 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 376156636 1250 376155386 376155421
    0x2120a0c0203060106050a1407020f03011410120b01061206050604060c0c050a0302060304081b0a0605190c020715170f0709090207050a020f040212101d0c0301060c0c0e 74
    0x40c2c01a9400042e0705c60142c000e49a0048040e113031814041a417030b4440e20b4136402410201e91050f00781588001c00e4a00344103001c110100701c82289160f0a12036404802c00f15264081c0c10090040c424010010300c00d00341d090304490f6036003080d00e48900115007540103418180c000c1038200d0008180001c010b80d008085c1805540a1034200e1001502e40c0140f200402c8a400042d4100c1000c1001ca030000314850300404501000c01c28580b01d01d141c1c40002c2d810721138a004162015510745041c0029a00e0344903130301003080418101002044140308020707449620b64480c50b010155200e0b001070509010b0000c03511039104003d45000d080c6404085c01038082e505641100000b0300c0c1001c0030401d141c061088900e0190410010445242154204400312150186031908241c081c800b8030f294122014406000e101e0258070070302010f041c001c894000100b002e00e0f4540c81c0c0348900c103110304010705008a81c1074450502c1c00800180b418141410b581d0001d90103400000160000c0201070600b03040300c2d80 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 376157886 1250 376156636 376156639
    0x91a09030d15030507050108040302030d0f02070b150a030210020307060213060e01020a1a060d0609060c08060315040212071508041506080d3203041b0b0406030c02120a0c02 76
    0x42004840e1028035244070b054000104250b00c103a0f010b01080d8055115254401d20a1044a00e040320317104081050754005040080015000701c1d03030b80d080100d1181d01da41c0c480700d0420b40646c0c8c90205030008600c881c0601c0064001e054480001c59824801d20440307440c6500000290750743d2803440040c1c5e0350a0f941d07219507000500601d603003034608d61000c80c02820440c1c12170303580c81c043c0c00040e075100140d0b000a00f10300e910110040b0004001501c074060401e03070600500c400500e030868000301070102b14005041c0c0c2d00c00c0d00034441488801d400380e80101c2d0003d806a488e8070620721a03141d0a45800017642010214501c4920047d00d402d031700c0907556100c0c0e882030341c001c1141031981040b04180c0311140103950182e08800340802d5010b214a03a009401c08a8548000c0b610031070000004a20001f082804035186c1300000708014024580e200280a20360300c003105820ba0700d8108407071800d01882c05a001016100d0701900000c9100700000900382d032241101c1d07a9600c20113003000e042c00340401c408030f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 376159136 1250 376157886 376157891
    0x2124040611070308070e01030204050a0e07080a050c07060b033f210703091401020912030309031b0127021e1e03030f0307030207051618091a09030d 65
    0x1404500c4540240d4002d03e0345601c4166458460180c1501d000701900032007410154240000a400d981d02c10034400101461100d1601d03605000000400902e801001050440d00b050240b0900c01c040c0030448544a8021f400043d49015803000281030884820f103687c0341128114400c0d4601d070514003c4803543d010b170400910082140740c0e040d0298024640d8000e41c1903d8103158110800103401403690160b0a0702d80001d03c040346d940d4401c18034080056285181e940440c0400c8107041c80d41001d074032201404000e5003113240880155035248500010310321500c0d62419648941030f425080f50520810148811200c0c0c4c0300c042d0714010400e4803900980c4513843d02460007112102d00c90f810105040041e10703038000c1c480141013900b00281070240c410741500c010001c00852010007006540070b00400e41d80541d0303d14090400510b0b000341d0301d605000780c44001d102041803d04c080b41429540050020100e0720441c60300b03000003404406c400702c000c000340d41c07410490404d0020000304400e007820b0408 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 376160386 1250 376159136 376159151
    0x3031b1507020105060102070603090f050d210e250305060f1e0402100e031e0610060f0e090a0f0903081009090320070503070b0d0b0f21240406 63
    0x40b42a984d040d00c00380d0240e04629410702145100e83c1103499664096141c284000c2c58130790f03c0c0e503c0c141020540000003403141c0c05812680c92135809091380f2111003001030090150342100242c4450080388010011010300680324414041585098020f540141c10b80f112407424070304880c2c0c1100c0031100350b00c0359407101445001003003180740380a00440d00a0b19240c0d4403036011000740c4584103140007441d45441500c51004030812240360881c14290100702401d21410621020b551040d200d4002c0001d02c020405c1c1808a103074007a043c2075184400b15280c258589a08200000400c07854003201d40c07290030620302c001407541245055005900315004408819944c3c902c0100702d4410410044c0007501c490035480c90001e04a040d6012201c590083e42e4901d039417100000e28020056000000069001c04c0064000d5102d20a81754583d0302643ca0303d00442c0e21000051010304d6800000310f840403650380d5198501404c2001041d46400181003010848140c0410600003604aa0031614075082452 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 376161636 1250 376160386 376160401
    0x4020f060414010f020313060e120a1a0406110a020a0b010b03060a05060903030c0d080a0608120301031b09180b060d08032a040e01080d0c02130b03031b15 68
    0x4450031035000c0700c5040b101c0042070004607801c0101d140544118070091008442e2503042c40110002841551612010010000b060020f0a00c5030140503081e90810300c141408110743c070080412055940300c030303480b49640380c0c81c10304000e059201c0c2e80c0f0108413020654414507500014001180c03801103c0c0540c4580c0ea5240c88603407480200c43e41600407480003c20402418071401400400d5002801e890800316400d10035441d000201c9081c00002e80406c0c00d001100c0c1051145401038011074025019400c2c0840203402144010700c00107015980500c4d040c03002202c20742d00080a810b50342d074141300101c541c0c1900310707141e03000d08400d984041072040403c1d0649003403000002e607168099a070901b1556100103025903841100c0907102030318a1a080c0ca000f802d03a040040015140c10403d404095052000c80c078904035108101000b4001d004031650f01503a6540301007540c07440b145401250358500703140403a080d13000300d40051b41080c4d4106404882c001001c20031000400d00d2003c10360b03c1d580d8805 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 376162886 1250 376161636 376161649
    0x11070e15120a0201141c02070c030201120b03060402010c051507081b0c190f0f050d090806090a3201020901080702070e0a0c0c0f05060105120d0212090406180504020f 73
    0xc00207010030a1124484e5405c030624014140415039100a008459101d203d034805030380c4940401c440998850400f40115a0040c0d5008600400114200454030702440030030b0f81c40c6d5010380080d041c001070540075010080c080101c1038004191041100460500c43d00c0a4140a429a408070790003500f0b0840405184601050381c101008000050401d0060020070428010044009403045100000f00710040b505184c03800d02d000788100e00030841c00042540041448030240c129078134035005035080c40740b9600000750005006410484600042d00e40020003044080480d10311107900032509515140e451043d405403640f1003081e00d40d0f101c1c076a10000c04980b559041d002d05640b1165100125480760803507030005001c4241801c10a200c035100d9202c00c1e6640a5040e0b044419602020060180d41011030301010304909030002030540c40d05d010300c0651145441031820120801c0440c12103582d81c6c2c0c0c2d4101400901d6003901150021081060080140104560581c060605211002900c0c104170 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 376164136 1250 376162886 376162903
    0x10060e1c0f0c050d0b010e0912030c0325020d0e1c050703061419090303020405040908031006020c18100b030f090106080a03090b0901090e0a02070507090908090111070e1512 76
    0x401d007040303031f007800e095003040d030703409000d440092080b40410340b184140000290b02a284c511101c58885c03500b00c030000c4882c00002d80c1400c0000348a4483d00038150006560b10340c0c60801c0c03d0054403000000041740c08014120704244030441c0080d40c035428070030045261001d07079000306014000d800f041042441e2500041c0c600d4042e0116054140100303801b0b55100c8a251403092030007501d03143da5100000c00b0b8600c0c014041d554040300005101401d2044101000181842d0002d040c4025004c00014218860308055401031010b03000024010030004040388040e02070200301d540c49051210032000100400c0300c44400662070082c0104024000254895840c3c0c0d0590b1410301150808810081d20340002c00d110381800070201e00880e10350303868802d80303108268081c00182c0721006414028904840d603070052508030302e40312100c00441d00c00c0c001c8460801081c20950750002c1c2c0031005134a09442e0b0707802449690440c03c02e2100000d0324200c141004c901c1261441a4201041d40d5940c503a5481c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 376165386 1250 376164136 376164143
    0x3040f0305012307260109020301080d0c03020c0409170c0c1816030c030b03060406020d110301050a0b030c0409020a08010303030c0f12050c1c02030601140310060e1c0f0c050d 77
    0xd0f02e000907503452050045079803408500d040d0502031152024015551002a0000c0000640100060064501c1003200300340c080418641090351440944000e500c480945980e82d000b00c0d00c031200402401a801412020060507001280e5a0030340c9400031501d4240c14045030f80324840032003045842900c0c81d15911700484410386000ba50b59040c41c000c4d0000e04c0d600c030300c5234189a100c0400f446c0715a002e20440f40714501031070000d42c0e1000030140b008210b55a641440c644030038207000620081c5c58018481d000d42e9400081c50303660351104001d5440354002d0340d000c090744c2400000c07000c020f285c0c804081412603200e51010b00503408000000e035502c01d2003d81c0e031000118051100d02da00e0000d038000035000610120014544030f00c280e076400c03000e203540c900c0800b0207400000380000e55034410705040000c09006940c0d815030502002804041c0341038420b1108000358034180300301c035907914040210b075501c00c2e207a20170080781d25141c00001c1090000064540005c3c400c00099181808004003c13410350 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 376166636 1250 376165386 376165451
    0x5040e0a030512070c060923190213020c0723060f07060f060f090603050d0806010c0b07260a0e01110403020909030d1514030102041a0a1103040f030501 67
    0xf221540c0e070100e8000100072204012414005030040394207881440703a8a401040b0342d54030b003400a41c000900001041c00f85801c0d600c40600003003a0800700340c20162443c3c0c100c0d10520fa8104003000840a401015141c0c2024020540c0000c1c840d05520700c14403250040820450516180e40200a0507001d07203044120b4400701041100002401a480807200c00900b8200143caa80c40d400403400c0803145400c49031240303680d40c42c24070500008228031102180c03185030880c560320f000c8000a190012511006050009203000724040c0760040503004070b082504045600f803805a40043e03241c411055aa80e03180600c0d201020b207026806018242080b00501c22417881c062855090201a280003000001079000034028607045240301d01407101050180d0071900d03000da0404d60714010700c03140c4100080c803aa104010400011420140c036002d102601d811321520750800a40540c1c9a178200c03c441b00c0c10b030000280104020901000c0791043d20701400081200e044e98206404011030212280420350340d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 376167886 1250 376166636 376166647
    0xa1803120b030106090509010c02061506041a040e040305070312090b240409050c0306160f20010905030a030f060e2706040609150c0801051908031305040e0a0305 71
    0xe1641e00101c68030031000e000062102d40d200c00c0c000c112002610207810716511540c1c9501d480343d04100c40c41d0400c550850a030001d52900c80010124419481481d004000424149200000d00e1040c0c90061604c9088402c0034601072800510561054008030042a058103a40341070072035621400c5135a0354030a082c03480c1d6488001a803820f004802103034540007680001c0406c890740341c0780110000c0c0b62140c00109005020031081504040000b02242e0401420315030410525610900c41d4200e00c3d054100303888002018407a000d80120009404800d96003000c0255041010002c0104140046664108030a100c02003410007a40c42610600c4002419140802c404a01020444604440060f001c54200708a90b502030b00300503045400b5034072300d0f0340c43c2d000100f4401081c80c0038640900302003042042c0d03904184068207034030040c0240c0d40030301080c1050004644008907035802420540c4106c0c1d03114401e85035000e00c01c12542c0622030240382400c1640030704580002c0d02021150745900e69500740f4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 376169136 1250 376167886 376167917
    0x70c03051c0f1d060906040e0402030c0105030915071e0f08060a0b07022701030b1e07021005070e060408030d0b030d120c0e1f02150106090608060a1d0a1803 69
    0x30706903030300a91344280d007004000840d680e48001000108001c0310400741600d41401054108464614061305000c800c0040107001d00010428049d000034044e41c8902a4450100445031500309103c010107100707170700710300601140e01f2454a20701f40600b45d407060307202d5507a60280061000e01e840f9800440505001003c014601002801820101c100010300d804426035603500b00054280d10540700c2c00800018007041d07e119645407003509a2000c540d00d142c0c1080e9800175591030030440d003d407890350340f0310100d95120310a01da209030006005041d40d44440d100c06e0055103a6104418031110140f60001d410024200420320b107004010321389400e14141c040429090152525007281003c10605298080c4683c0c1e440c90352070241038105100e1000340c3c1e46000080d2500091042c003c0c000200c40d00100609640aa907220649109240c00c034610f48032900850300c0c55400d6003003071030104246044c03c018051000c1c901445007502c1c00d420302448800154a2201c1c0790044009800142014201c100d038 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 376170386 1250 376169136 376169177
    0x30307020d1a040f030f0518040914013204050a0b100902041d0a060312050901031b031e0203010303090510020f0d030b040b0a05061905070c03051c0f 66
    0x694000d40c4240c0710b400c1008101c1c550600d08580480748141e0854005040c50740c0980c190b0b81d081201c2c10800d10f4808010501c072018000303843e080d4440d5456000303050404c0f07840811040307441409030090208502c00c0004803076482c40820700310700381354010703d499104024001e045030040b078202015048041c540d13200c07c000070700000c040141d03011307422100080c2c1070007e03c002c0c0001e058024054180710100f25107240242c1c00038040d05641403c2920500c00b04280c134440070041c00d10360405a81c1c52086d600103a020300f02c070190030007000c206130070b15500d80d64154000030a210060b02981a03007811024020b01280001c1c00060009180f0a00c14011401d0000c02421b2405890040381c810030b805418031840c000b100b49204e4002030300c41000074001d08150181e070000c1d030001c030790104900742041d000c0741441c0169590480c4105070840500902401390040b24183c0750400700710301f00b49840b030411a9071783c90004106007484060032100c41d4100c0c803070700907410003041a94804181000c0e40d0403a640c0b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 376171636 1250 376170386 376170409
    0x150402120c160507080d1205070906030b030a02061303021512010e0c0c0a050f19030c15020f040b180105070b060f04020409020a09091401030206032805010b03060a060e03030702 78
    0x1000a02d000d02c0b0301c082241080b80b0001000450020006151204401010300c0080140407490714200400e2241081c2c00170000030a651891030000b0380480140002440c100d10500c0194100c480040e41c0100010110b800381e0949009440a00301044800355030b40651107002e01000440600c07800501020340e40c0b81c0080c4e00f160521018600b03081d141d4080c1410a80b145900b205c80b607108166240441505200101c45030740c0345195000c2d90301c00c58401500c01c1c3c6034030000615401c1c1844525400000c1ca034142c460840c20350281c16120390300c03421444a29800b540760881200c0c00440c10301e80307940c0704000b1580303865400b41545055499076014011107040c03055820350b000d5000c3c00027050f00c0080d4070252410200d20341d00c06429529002049040b680001000512088000010310141c0c80e5142100d4110210141116041200c0f40c46506404401d008920609007464000a0300d403904c00d0142d801208112400801a56101002e9689022011a803900f40c1c0081c4450005850084480013 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 376172886 1250 376171636 376171657
    0x31e04020d0b07030902010e010801081209040e0d020601061d0d0605062d010e060403030f0c03030b0418020f030604050d050c240708100b03040809060903070b03150402120c 76
    0x103041c1412599040d1200104030365043c006030342d80b0070031810740d1307804000a403000a00703081049095040000e01601c400001c80c100c10351402c00136918696031601e5001c0c210003800101600c158180c1c41c54029182c0c0c4080c07103040000340518070010000c05045004050020b00102108191000e235580d01001d010001d00180e03202509016580d5601048810140007041d0030f9031601010111070000f412140422044900465080c401400041c0e0400303455560042e0904042311900303490b26044000d05000b40403da040b908010a8418840301045c419076480e1080700d000c034034500f060003490b907292000c41340908243c0c410a50030310840e010380c00806003030b034210003030701c0318890742a50318810b042140000303a0a4030003203820050f0b5191b10607505600071800300c100c040b00c189403584148080c00041d001402080c0c00064001180e51103034111102268003406464078140e80d01080d0000d0b40049401c420445456052f4112614080c030881d1765130358140c0b04070421512280d82c4032116421030078010 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 376174136 1250 376172886 376172899
    0x120f0414010c06050a02030712110d090807080c010b040b0102031206090714070b0103021804050c13061706150f0901030f0606030c0806070201060501090b03041209051005040317031e0402 82
    0xb102284660092510980d01d403000960b80b410074110092103040b50100c10801c051504450645507484c4c0030072a0004042104c010650b070000b030405044a101d20701d00100381180008000c800c03020103400021101c1002c84040011840c054016130f101d102d01c085810901240d240000d61620f02040155003140750303884c1ca103d16030000b80c90220b0b240d01031103003a105200000c004008610b03041c0b000b60a07403803201e0b8178030b042400c095892580d00c619101c9400e1091414030005401e403e070756840342c40245160110409400c07a915561600c4041c19262181c0e00c4a050000c104141440805c124103000041c080c40c55a0b03185407901e0550040a040032515103846100001c085103d0341ca4102c081e00001c0003425080c02d202101a003101e0722980030a06104000504005644040f4203695009403c21f4066100c07810f1118200d40c0540181c000c26888070411441c030611a91103405801030328418a200c540c0640040e641c048940421104032000c0c14000c000102120104034400380c0091014061 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 376175386 1250 376174136 376174157
    0x271e0609160504120f0209130b0f13060606080610020105070e0105070611032707060f050d060306150303110105130f0305131206050f040327051011120f041401 70
    0x101e19003003200f40f1040d5410200030501c0300662510307c0c00590080030266004917042c80d0b0783e442d2400c0590082005c00455000b6000030501106004d00842450748070000f085015100c0201406000d01134540e940540b5079011320541c20307401481201d001d0300b0283c07201c01c0245081e40044503140e12422048403425100d90708440907100340d802540c024644c0d81d0500380c10704400164010b04000d01d50000c8043d138441c940c2044a00d4200b040380ca1552503520708940d45180003010b140140c40150b0000b40ba2a24180041c00606400710b41c00c02a01d120b55540c0c5a107000d400701180c2a5007065580c0c1000c50a580c07402400a40311a208403a11031080c1041c600301007a02e07000c1201c0b01403552141328400d4100c44030718200b054034410942d03c00720310803171902582460f80300181500114808485986244500e504002d03030701c80490300080c0b200400c401c0380c0881c046230043c5010034440c8441d00a1269180c00b07a5909440006d803030042e400d03070300214201441d00a1040380301c803032905078505000b20f801c43c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 376176636 1250 376175386 376175399
    0x60a0c1403040822030b01030209061f03020a0f020312070c02031f050403030c03050f0f090708010603080a020106080d02030a0c060605030d03060302030c010c021e271e0609160504 79
    0x1442c4201d001d80740070341d01c0e00700d030064440340038003610001d840c03800400c002840050101c540560540b501601d49101035600d2401103500c00140e481102d502c440060b0111403040d6158004080d0b40020307540724600512007240c144c1e5a4064508a99000c0e4004c200090310710744540112500c0500041c211000015003c1150f5441e100760703003420f5000303510350003000207050300740c024608640f00f14030301000580340c00400c442d1a14005082c041090400d1400301c1c0c81e03e4800c01000010301035030720080101a9403440c203440b031980031078041009235091490001c4d1040000c130340f0000703410a0741c002c0c610f418000601240c0f11880060101c640b103a4034600400e00d41c50400c081031345d8003141d4400080250030350040508d0000d5450465041002c0181d8040042c0c0318031100540090466400000021f0b2040015101c0042c0440146803402c0c407000091030b40c060961114040e0300003811051000c0d0075120561140d00080310360542050012022031140414070000e041c1c0e9501510745182010344840c3d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 376177886 1250 376176636 376176677
    0x7050a0f0b0708160806090702010f0f02070c05030d02070308130e090607140406140c030c030703230405060a0513051309030306080309014514040b03060a0c 69
    0x103410741d41d448503403080245641e00b103c00240c10080c0080c2540b084220380c0c100404015004107550300540104000c2038100b0b0003500074103007030700c01410103000380080c03441090002d4002c1c50f03090b10910b1030184000b0311410042242440c0e10b010740d004d4044a411902c030095180c2c020b0740050460a0b00a200040c0901ca640c040b80c00303080350101420050602000c020311951010006000c003007030800c010041240c2100101c0d1000010218650b1650010a412410341c06010b10846e0705010014070fa500701544840d400100d0085c42e4080c028402e24182c100c001c5028a004190300283d04000504080307009070080c24035841c40000d142419529503000c0342d56054003490b051010b549a4250381c08140c3c02d40a18005061190004e505006031407000904100003242c90744a051041e17403100081c0000302e50f448518002e401850400e00b180e40c240318035502881c0c8070702c0400c0d0801f0311140c0d43e2440e0078010313080c1040008005140783d03210180d04100030040200128180050040001d0704640100d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 376179136 1250 376177886 376177913
    0xf070203010603080d05151c0203100c1808070602030d0923010c030c0212070b1b0c03090f0f0f040c170a02040509010e010305031e09190906050109030f02040207050a 73
    0x81d0440e0b504d40b0008180c0c0c5007510406003c0a21088140c10001f0851b281c00180000c01c9611a004180f15151800401c0c10900d20301c204030030340742c1071504c480100307500000c6a0803210050039543d003405a494074010f80301e003041c1c0590f40040c4c20030040b02503920161f03005030010601038503a84410606c0202c188103443c0194a0f11540c59443e58000c1600c0c40d0107109014144100f400500980c05245594850074890302c0002000124003102080300c1000c040340c18107007103204081c04c3d56140b5140103a01d640303800202c0424421000ca80f90149203007441001305030008030240c0386010380b1003a80d041102a101c900c0b00c0c001000710710203607044150401522140995a11480160394501f803034240001030005070460020f09050200400000300300104888440d078120b03080340ca8654100c0400181c078883c0e418207075409440c403008032a848165000d5001142c41c88001082a1650760b40195415501440003421402d452040307100175041c590000e1000d0351089054450391001369490901d5403448 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 376180386 1250 376179136 376179143
    0x120305090310150801020a0813060b030a0b04020a0b09240d020715050c0405010f0509010e2814060403020103091a01030b0403080109021c0b03120d0c02161a0f070203010603 76
    0x3ca004003490901d1151582c00500b0305036000b5440c04c9803880000d1b03d0200b0180102d03035503010404070b0030240300c0d050f444070320090340050998188848a081a4a004006480a91042c000c5503c0001c094600104440c50880301130445203000d058070040940b00400041140d05444003000745d0b5104084520045c051140f040390903560721554910031a0803104001d00406210404002c10700c2140c4c0c10a1000c4110285031610b00d6480350300760300481c2c203005098103680d00038080103008004d41800113400708070380d100020340800a541c5d613000d000c060040040c02c0ca070088010030052000d94400d400c0784000c140902c00901304c010b9030f00802420031600b640162521201d02081c007041560000295006149034034043d0709004220455107003564000076035002182da59011641651002d0221100702403c00e10003a0b1524030048041018054a203507800040c080c4403800310025400705070310801d8448814210030034403803e140748445a44000d8241000c141c050042c1001a60700740030b0500650711 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 376181636 1250 376180386 376180391
    0x314030421020f1b0d0b09100903110105070206010608160e09090f070e0705030604050711010906060503150c0409151e0501080106111c110f15090601030507120305090310 75
    0x1510368803a0606596050040072198180e12a42c46580d485c2a00100b02d0b81000c240721158036114107140c40c006455480030410360510780702c00c09040e00031130f032050a0b00c070b82002480340b031f624000200e890f44402d008003004640385401180c2ca041c4d40303440d0360402520f1401e0128050303540e8400219a160f08032140101ca034040880c030081d100003480448000c2c80e40d001e40b1500c509020b04044c009010040100c1e01407941c950000b00c075240304a41040d10440c0490081100c8403c0f800e200c1c0240029015180c080d1180701c1403603e051000401003841001c0503006103003001e0505201d04050000ca11180810b42c00248010034126550410101c0b030710b5414025071211880e190024212201c16070040c401d0201580900a41c1d044c04901081142e00c0c10300ca8440660302c0030b000307551070703007081d201c107151403145070303007500920b03100192071020b0060105e480359445e40da0810050351180d09000c0108190000c0d0700c10000314a0454040c24054403034103210342801d0207100441e207080b00000c00c01d09a070741c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 376182886 1250 376181636 376181653
    0x26010f0501090e220f021e03190f060b01020c060f0a080604090809010f090f09050a18080d0506030c060309100e0c06090114040b12090c030109031403042102 69
    0x68000c0c0c2d11000038007030b07a4030442d0540380002800c00c4103031032512089182e140d030f824103004024281881c40d15070b0746d004202d41004204038403065030503404452418024801c210118880e0f20360100d240b07001590210007003400100c42d5943d10040e01104c2e035182d0540c0700788043e00714035680300d801070844140592031b800c0d141c00100350300428129001e46514082c5103400c101e00c01081c080f40441e08039400a007400c19101000210440380340c61150f01c030b08030340c103502d40c0007040d1028942c0025002d05004001800107198210305030108442960004040080404c0b001c4070070078a681107180d20480017019604141140d50120710680e000310f4107120150081244440040c46511800b1104010131000344424881e60700402e1003440340301c0c0c01606103c51a41c48400d50202141140d0103030003240038564440d082800410803158003a22003913450302800c5c2c10025039040c14400c2103403440e016580d50480c0c0c03000b540032031816480548192100751014010491044040d04650007040e051340c020301b45003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 376184136 1250 376182886 376182889
    0x3031603230318070503030a0507030201200318030903030703050d050f0c04140402040909030908070e060d0303020a0c0c030b0603071a040e13060609020a0801090207030f26010f05 79
    0x40481c110203031814040d50040701920084002900da01c04002d410300314400815901e100d01c0c040a0354481c82d4180300024400c13442036405806024514800c0c0c00912110280c0440f0101800c121a10076090010030301c00070300c11040c018003945017540307402c06032403805000301d01103030543e44a00015408204001076056410020784600c0d680080c0401c030811203030030704a02c880054400c91051049050480065200650381c0c2d904840003040c0e46041040f071240141b4016191009a2003070b440d06004d407120014499010b050100c2c81820001c1c07003041308086a0f5415002904013008110420020714040b10001341c6044101c4050f50040803c0c4003540b62100c02c061801401c0e41180071062002d0f0031078500070b403031842500c0907102c01e03810b6180700b80e5a000000b041e01c0096039020b03102c0da050080c00240181b180d401001004c180380d842840f103a88a41060040c6e2040d00d5004000070001c4103132940756803190503440d20102035100d40e2031004009142030214102d00789c02600111420100030400f5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 376185386 1250 376184136 376184147
    0x80d0c111008060405070e060c0a060506060a09060f0504090f050a0e0d0206060d0512030411030c01030e0c04110f0c100c020708071e170c040b0406050f0409020f03031603 75
    0x420407600c4620000e034a0500809010000c0c01250142d07407550017140000e4018188180744103800740880c0c2c4c8520604030480e544903a007200c01c2c1c8180d0720303143c0410b603039007028000c5030a01d0251f40c0b540212a841c1420444940269281c40c10030448188400709441c4c003640a4080001c11071600480e041c1080580e030412607111118104595005034085c50b015034000c00d005500c18000c4a40d54070100c1c031800e000d4144400040321912102001040100b005174250146030804410740441782c035650b0600041d012141c1e200c240d64165403005451401c54075080d0042c0d211600c44540300c0b42851015806e040311500034181c4030080b40c10810884421100f544507030791201c5001d20017801610328181c80c146e1600418000d40342d49110300c80d045000040d41e03c0d18a40200812142891030040c40c01c0001d8445003d020468461410410a00d14034a03180c000c1106648000748070120300b500c010200002440300300003c0303070404e0341c1c4480381c00385079014005064a2407409040b0380c4e148a452500400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 376186636 1250 376185386 376185413
    0x1050405060112050402040e2d0606090406050a0902030d090305010b090f0105010f11031201030b070f0e060a0e1221070506040201051c05190606022a0a080d0c 70
    0x1a4a44000c0000d075070703405099141c5114007214000f07000c5d10f0358008180542204100500c00d88690b004100307030401000c1c11f283e90308080000d14605041c00c83c0460743c0380c000540b81982c1c004105004a004190198002a008450107000081181d40c580c0401d040840290f045404250b940c4004c1003800400c1c01215481d1b241240c000c495490182080c1160200602443e410020007282e581209806010200440c1c1400000c49448400456590807002001d010880c1d00809503008140510f0142014031100300513500c4404030b050554092081e03170380210710007100b00141d00f2410303005525a200740d5101d0410040c0a04240003440d84450380700c904e00d48600141b480e0801c2100c01103100401c03481d400170740c24680a540e0704504241404051f03030024a1001c402d10780014403180c01c2803042d02e814020442101840501e03030742c0e6800c0c0c1c0c8a072424001e4a001c80c030500526410394070440740d5841e0f00d0034000d0141102c1c03502c0d60031451401e81c500040d80c000c184042003941c14070008001c01030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 376187886 1250 376186636 376186639
    0x8010e030913091502070507051203070b0402010f0e06030a02040e0c040303020d080406020c031305090c09031209040e0706020f0c040c12050907150309021003090b010b03041a0a020705060105 84
    0x186081c06010104802d10680014012400e42c0c4410b00801c20030038055900d025030081c032007551504481e00308907454080714820b01e0720861129071b480b4190701002c81624000c0e90480c3c1e040f0b206940c0c0d50015158403014810721020003400881c10740440e50740c2d8001c0e5004414070080140c5a034200904251a00c07400f074002441c0b01360a1104200080d0b0005441c0b0782e000d0540350958154070356140041c00703405070804001d034601000c1150304a0404110061040b20411102103c40b600d85100407800b61142e0303194541c00d50050125901c1f020160f40041c18140c1b4080c000198429944443c1410542c003604400700580000760029140c400c2003001920502003102c04006100b414800074000c1000603070210a05515507000844242007403050303800500b203500e05811000400780c5c004004105640c8220700c500700303218030103402c1c0d80700c6d05c03818120301e9000048200c00d03420300c02d200305240c00050003203810040d9014806145414428494051060401c0141c1c5614046c0b81281c00d185050300660f = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 376189136 1250 376187886 376187893
    0x3020601140a050d080f1903020a0906030b060d18050a030c05070e0c0306240a050405011101050609010b1309060b0a02010f050f0a0b190f03050d03060b190c020307060908010e 77
    0x14800c3c1d681da020031403605603014048569030035001d901540745000f6064001640805140155203403074150f00105100c0a46603501510681c40300c3c401d808598802c01091340108003400f4000c030090a59000043d071b0200032006100b011840c0d510149007003c0d000c0103c001a800c0e104d40360400a0822070080680800308440145181c40c40ea482c0c4070b40401810207100e40c100300404c3c0c03401c95000d038441c02c0f02101c060507990f0703866220700e014104d03600030300c00c2c1d500042c2c5030103060881000c184680d44c01003d00a107950f04c1a481c1070071642160f040410590750504404000140f0307000d0500c50000201030120340561540c01c5400d02900716801805c000d14074508110420802d01748034021654001100540010f040040f4808201c0b030220100c4118246200c10002003101721000c582c9030200c071320038811a0018150890214150759691040c00f28405c400e0001c41008a803020084a5517600b81c5020b000c802031a07000285024529030068010800481060080020078098036000b14600b4004 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 376190386 1250 376189136 376189139
    0x60403230d171e07030203330f06130f030b06031b13020d050c03010317070f11121b03060907030c051203040e10051305010303080a050a1803020601140a 67
    0x1a2544280340482c82500c900074000030410841000f00c034aa1480b469010320703042ca040719000d4025442910750881c00444105401e20030000c80c98166440d8107000035000e0700700d604800f03100c517100d54440b001d03501c01001c0c04036040303641e0f440000400404884440030000c0b4958102107140450180485000e900030003101442c0311640740816003581426903024140c00c500800720802800b034450709241035402c00e02840752038080d4902550580c0d0040c82c40e0280284101c0310314840344542c1800400b1140811104000300b1007544192010f00005072030310704e0295480711001e040400249440f4410107250607400e5090504202c0b15074000c601000030141241540c840000007511482070317500c03c0c04403c095204440e428006e88004010008202c01c050500e0144801400074a000da41e000d213200c062031100340b03c85800b415040743c0d05920f94117102d4881032a490054000144180481c0762203010712007a80011180c0c1c440120f01a5010300300341e50405003c00c850000c400f070114402c0740c0b003100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 376191636 1250 376190386 376190413
    0x1d3c0705041d1c030b030106060c0b0901140a0b0418050303070306090c02030f160b0c070303110406050301150c0506070e0f0901300b0106050406030c0f02030a030e0c06040323 77
    0x900d429030000c5100c82d00704041d1510411405001d50120086d0954200000016865000300300c000e03405102d801c21130b041d66100b0312040d08848002003869501d1700401c0210300302c201503900c9070302112400790012036440c010305d00004094000030300417945580008208680b5913818407901019000204003482040780700c4200070350f240240b8960b11180800065071b41030507001006100f0b0f001e0751102030441340c0e10300840001c085421040d4103038042414a007444140d51034000403a03080d0b501507100c481c2140d080c00c4030418800401d032000d2040c005c401a4490114108020151048070280d8038231020040420512000107040074a15018007601070050221103807050101d0030304110280d00281c2c182c16071100b0182c080c40c1260207031055100c1c40c000724480f0303440301c024010356015480c24040380d15102d10843d9923407803658203800140c10600004044511a070081204084a68101c0c7c0b2004030080024459030b02980c01141e4100c0c0000c41d541d10b004256401080d4441200084c0c03005810303001 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 376192886 1250 376191636 376191643
    0xe091e030405011d040e0d08150a0e06040207060e060907080f12031b0a020c0f09100b0a02010227031c05070b190905060402041d3c0705041d 62
    0xd0641800401a600c3c000c4c00300a0448003940d100040007030010000091105440300b0300c1d0580d010000315103c0015568021a02c480200e4150245c00300d0019032030410340051000c1c01500240c0c0c0706408100e06008240749005409030141004094852407d241000910701642ca610080d41500221403101d10b400c0081121140c02d003242000590325aa00009603540f10504c03d01c4041070100455a0484958000f03080c40d480c10083d00c14041c031609840800c0480301c000c69240020302417281c0b092000c84450ba020b003007552407500005d82880c0c00c9100c01d81c01d07080c005414442c0e500d045000d0240924080020202000502c001d0401042810b180240944101c0070050210f004800204440d45c00e1054028442440caa004210350005c0c0d1600e140c44100c281d4060b0f10450800e480ca0502e052800012030b80d012507500180810703112014105000d01400c54202e543d2002c01c050600c1d1100d0340c0149490340128040034100142c11302c81007104580c1c01c3c1400d00180e448240700c040340d124001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 376194136 1250 376192886 376192889
    0x1917060a2301020f0f01060302130911011d04060b03090d090807171204031a01060206131103010b030f0708060a1e05060409020604090614090c12091005010e091e0304 73
    0xc1c005044aa20000603458031004282c0c801032032082c2e820b0380040b40419401036090b01e100300c85c01804038a5854910040d01d1204402030030140c420b96082120358095203480018120300d0311019100c444c02c41c001800c8030b145600c4038101074000010005401d0040c03206803c1e0b640c040c01c00e0305519041c03101031940c2d0861030081c80d0f03510703a06801c0045040400c0103110040006000d08680c0d4949901d0242d2548000c51440c00c1c907a0078160000c9040d5002240c424403440200007040d410302000d072211980c01c3ca072012480e03055540c81144099944003032080010706a410401002c0e0315103400e0701d280c80c1c00402040c288042d031501c0509040b94a0302102c00da0203418440011440b522000001030080a0040c40250301510000340000e81a0742d580066045442c182003400e80c5802a90500c19010380444074a140d407402003146403c2490100c0071242c000480400300c0710300c54009010a03040302d0007a00040303c8034165104000c145042004000312241041c000c103100b00d80c1000d41c542e40c074080c9 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 376195386 1250 376194136 376194179
    0x614070806090403120f0e010b0a06270909080304031218060504060e1b0a050402030f01171c0507140c010915030f150603150f05060703051917060a 65
    0x5404102803511454504415614120040011b003540c217800900034440c42d000030885500b0900014050714000441c1c80442d0b038a03484204200494180320301091140c0d001103803c1c84445100401c1b02c841d284200240688503100e1581d48cc181410b02400003096030f00700000c0c0600741b8441010046d0914001c8a40c0c95211501142546a51500d00c010b03181c40743c410f4407144102011000a901410400c41400034181e910b24842900c41c02804240e1100311002c01c89210341d900100301001780b80d0705036407442c10490107986259503c071092102d020b0081980e07400090000c07401c0018080481c81c000301494604005040f2100250000790504695214500407402200e601d1100c09009411a103954101c00c981000203120b4040d00d0403a503201070003100d0010b450f04290031240704c041d0081c0400c2e26004010004140e1401040101551005c8012820400140312100c01038a01c1240c0d94440c1c081070f124901180d000041d651801017009000c54814141504100051519150b80181d180b00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 376196636 1250 376195386 376195399
    0x30602070201050c01090f1b0605070807020d0c0b0909160818011517160302060f090303040b0d050405060610050a110f030a17010602030a0f1d03060c070614070806 72
    0x1d000582e86800f910740494059402d04d0000b9007044610701001380024420800315880c1d00806a00c0d41400d1034901800010980c100100c2020844040191070002c0c402003100b05e1100c916642c1030700c101c500e54007040000b9004aa03107100351800c071070030070f60099195a10b0040c906401000808018019048403040c1158242c900000d110a4100041d1005040c5068500075618801d00b8a01c21104848007080d00411f6170514004009060405c2102d800800c3caa05180b40d0b06000b11169000100b03196051100700000105446580d0140501802c0f280000a2602c2c290429a0510390018121440380d00a880302e8190260050f09540d11905c4034a090542e103040c8110441c80c103c050104200780348004a2300c030000f290b07c02011820004d80e41d00d89401c59a031281c00340d80d02c0c05840b07005004103442c20030007520180710360259100394100c003b00506420620000c2030078070605031010010b00e040010401c0c14400c49000f44510101c1c5600580750902e40340b83c1c01002100702a105230f200d8070 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 376197886 1250 376196636 376196647
    0xf1205190e0a020402221d07080a06050904153801050408100902100918052203091e03050601050d17040e0106090803030f06040e0106090915051b04030602 68
    0x41c01080040030880c1d014204558403011140c88101d01c402858071a014464900c20124800c101022050215945210915000d440c1c0c80f03010760340000b000702422001d60343c40000156030384d900144a4021401108114840511042610155044054020b80c480b110000e9061b042082050414400c1f402c0c40c1d00f0117030100344000483d10341c4102d61020941d4410990b0324a800c003801d0348000151882100d030b04a1200c011601581c0c00c2e0b4282c4240800c01540e41ca04c40c0d030f64282600215804420204101c07440c0c0d00b655908003d00c00650700560000d07410810038007601c1031061200c00700ba102c10743d1044e0391134034507a81c965407a00140155401181c0071140d0b0420082084001500e10501c0725055840e652a40014802c0c048240300c6d450004103103140c00180e840004c812a801820780d42100c0480355941d000707010213031001c4425a805c5640e5440009008040ba00c50324a42c00d00c1214182c10f000c40d1036403890240c030006002016441c40c49111140c2c1030b1102811181103d0b0310000160700d42 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 376199136 1250 376197886 376197911
    0x1050c1e0a022508060406050f06030d0509040b01030b0907080103050f0a0203030f0c070b04030510111213170f0d150810110f03010801050702060f01050a120609080a0f120519 77
    0x1c2c031480d403141340c030341c41408148810804030b07400061080f01d00c080100d015545020805039500c5400840c00003059003000400400e04040c4c1001d145420181008107842e002400820308520003200c1a07800a90003200500070004103010440300104004020300c442e40e00e40d00007a40340d2042d0000c14000303980004802900c240700b401808018408041182d8585035039080043e120340a1210001c85189810111202101400151024204841202204d643e24040d446507002c50070031003600c041c80d40840c00c014030102030000b400c01d0415056290f03140d0301d4010655064445c00c500d00403c1805480d02030182d038800080d00310200101e00c03030119880641c4004203070b0340e104000c252001164004004151280305421140c01100d0302e40c2251080c0c0d6484407441c00004013800b6295010205140401842d13040404025a15000b20f1700020551a140c0d0b0315822a40443d20010205101040c2440959001220240c0e010854881400640b6066411001e908503151624551580d61100c04410 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 376200386 1250 376199136 376199203
    0x606140c191a010906031a06031c03092d20060f0901020c12030a030b030f0304060903020a122d0c06050301210206191101050c1e0a02 59
    0x794080e8011544204040d040040494402d0007054410005072000050000c501d8403d8204036500300c3c0da00d1613900801d0017802072a6801a1009515214101e80d03050401d41178440d5240c105550303100028107296a01e0b001e0311070188600309240d0f0003514180d0010032a6407030360000d801030703110614a11941401d40e0030340d4941d518945a42d0000e002156101c09201c0810003404448000d0702150364070380a25041041e24041034014420b0758009224121600d03000b50040681004028141c805441c50220b55a00d90f400a03800310340007032595501041507051000580b0b01900300c950200e03101003103c1c0c035107408900414021800329030118416491000c0004c4603207140681c811415502c182d62408014001c1c3c0080c02071886900000d0050390001c03100d900403400c41503010b406141000103d207090180000981010824840354070b401c3c05610400307200e0306210b0f244400300261640c140151400c031070143c800040003204000c210402c0c081d0780000d9089a01c001080d42a040c4802e041001800d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 376201636 1250 376200386 376200403
    0x105130311070305120d0f0506030a06050c07060905100e0d05030103301106072d030b0a0f14060901020a1101140d050114180a020903210a02010f0606140c 68
    0x17030103800c041101001480005142840058105200da86550120401143e034181d80103981540640e0003030000403295044030358405000085907080c0140703034807010240e039894181102e60303400002d809081e83e04039204244001d01c1d054010100d010480c40042c0c4107100c10700003e4403001c2c200340484c91000555007170740b124294108507500021445100904034141e030280319602c83c050b400001d0b2a607480380c8ca8103009a10745000440c42039445c0f80c3d928401c0840c59141c10201500d4103103054164132480ca0f80001040340d0120180c0c261314040d004141909a150760ba40701c1c000802941c440360ba070005030380b003080d50442854940c3c442d44000503209580e95180311003003d503003c1002511640c0381e511080c121081c0b14a14404403103d401003108944140100b42e070141d6440011401c29038859000e882c61850180840724030b55040340c1c03129807030900000c02d80c2c1c9030180017424001e1254207004442080807401d0041c4005403d007070014003c000406801d007210240171407110760f60041004420b0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 376202886 1250 376201636 376201643
    0xf05181003060e0d02120c0d0806120106031208010e010b03060f0d050601080c0f04090314070501060b071118040b0a09110a0b040e070809030306040e030d14010807060201051303110703 81
    0x10280341503100c0c0c040384413001c09070196190191100f2101c0301110008034444018290311440d2100a03130384102c3c045c1200c2e400c03042c981c00780d400c006424403850018502800c0c5429041440e110000d0840301c0503001900d20a4001d0010000907050100303803a00a80100c03051620100000003007018170340243c0000d809032040400000d05041c4c04118090228020303124040b0080064044c0025103001140040010701e01000000d0070410407009007240c00e118100109003e030b90741111480e150030107042035607400307a20400a002890b01c0468045c254802c0e0500d0413640c074003502e42c08440c600007022840882d4035807079200100b10200d103c03d44007100092503206015240d001200c0c90b5006801101e10540007600801d900e64020804548280d8840d0700951440e0b44c2c0c0024000035101241405410384001d10450303d2820281c001c0758a01d143d200d071405800c0d032401c90301514064256102d402903924220a1042900744e28903031102c0240c03d82810303200c018507200c400d4688030b280d60018 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 376204136 1250 376202886 376202891
    0x21c060b0a0f171912110a080a09120b010b09060d09060f0b06120105010c0f1401050406060f06050301091805031605070f080316150c0c0b010f0518100306 68
    0x100769001200a004143c440a03010303003100ba070704005440c0d0b840e144040d802c0d00c03014160840e8000501d4008800c48002d02918021100b20a081076580c54142e00d402e003212880b0020070800c42071a80009210010303e0703802c00e00300ea40b02e8261244070580c40103000d2115007100004503032000752110000c8070481c4250490030040c10240d801c03c5001000510506001c5505101c0d007411107240c80000e4814001d018010b0000c140d00e404010741e1105528901100c68010381107819010441e480080c40c0c2485050002150364a46032400400726140e5400c5514109054a028072501d03030f02006590568180b4100090040781903840395102d212600c1005000384000110f01a060748606c0b840c109070b0f44908210780c007007500c230f03252400840850301501d1b48a0f4000d1048a0021409da405091b0b142e014591484c03040310450105800d035980300d02d407040441c00c22501003041044068034a401004441c5116003980c1c10310740002c005440e4140b0140301d01d8004404240c8403e020024500110b5001004 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 376205386 1250 376204136 376204139
    0x191806020f060f04051f1407020d090816050d08090303070c030c050f060711040e0d02070503060c030702030301060c2a031b060e04020c07051201051b07021c060b0a 72
    0x750780d4850414038103031500869010800d107540d0300708400d00855000300544407080400150340c121a0440a0b1600c0703c98075090082c0109040070451070003202140e010300350103086507101501c10f1007a6800000c40340e0261103900080d0708014a004185c9804070341130b46541005080152260003400c02042e414040000c5080400c00b0070302c0504101da215400c12504507a4900c2042008050304c0c1c00c064100a007000200001100c0c1d010851342054018070024021a0200c2c4480c41d1142d48a540c3c0050703400340006215500c0c0400c411944000d40b03908483c42e41c500041c0080d100e000611511080c0b2184e00c9240d81040a00c000341412603046480018000c0d07039141005055102c180310030388150040c3e06031003480e50010304d141e0080d188a521345104021910301801b000794000d00100b015402100c8001c9416aa030300c80580381c20701c020300046010f0814050b07000861400208070000383c0c0d01000040b00680b0340d552107007a6100328a1940d5041c00a40c00c0c40360280c40001c65450307003c91a00310 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 376206636 1250 376205386 376205399
    0x5090a02040f0605070201021c170411120a0f0803180f030702040e06092d07080a020a0806041205030a0f2d060e040209070302040b0c01020d0b060306061918 69
    0x6041281c400740d0b03040421590300d4206039107512130104003074016000807000094075038243d000322400d00b105241c50b0062680c1001c82d51001303042901c0c01c4a5002c44007115291070315004c0b012003d0249001c0280c9803212240d60340f041d00d072444401c01000c03140007000103086201f0006200551900d000d040e10f5000c070204031060740301e40c0120300c124412490170176080040030000804920900380c00c401010300d8100c1c221000016070200b85081e02200480c07551601c120b006108441c0245060002081c800e102c6204210100351182c20041c5298496010040840c1d150400c1000b007030100e04003140e40707846054018000c0c1200d20114160039040000700d244040030740f2100c10720708825000b02540c07403100c0d5405106450442c410924075015240101e400b502d825040c054200540c2e007001440d1503542d0480343c03050b410840340b4900c183d60104000101e4095406040100141102c1040c03a43c601507001916034098001c2608c1c201c20021108030f01d80d8014407018520845403420345520039a0b801 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 376207886 1250 376206636 376206641
    0x3100c02150a14010b0426100c05091e0604120201120e03070303050c190e0307050d0c140102030702060d090c0e0c0a11071202091b1b0607170105010e0a05090a 70
    0x110101d12030b00900d000007405e4030a06050b1004c0c5c9542031000c1c0892042c441c0c88030020b404007040807185004111400240030303500e200310304c0c00004540b10180c4074000c280401400c40e1100c020301d10f14000c000488201a541d24080364290b03607000c40042c4c2160381c54001280c4003041302036000320072803810340c0d03440d04228004060605244a80d8003030045584500c4007103514010b0480400f004c0100358400552207000301081b225540e00941140c00a6680d0000503008200c15007060b240b190024a00f8400100003008510340313120300780002c51801c00c5960105030039103c0d8003080c2d00742503650100e0f0340800c4041000007004000b058404003040c00d000c5810305003a40040380c00c5012802101c0c1110b006140400d14608a41c00580300078901801c0b40c00380142ea00d8010b0a06070551124031003040f6649009003d821884d4949066030388007542656494034242025101d142809006540200350010440085040d40c0c2d003803038080007018014000c685d0a10741904102d45c4880c0020801c42042d00c1e55 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 376209136 1250 376207886 376207901
    0x305120a0203150f030601060f0c0c0b0a20030711030a0203010c050a1d06030601050f270907023c0f010e0106050d03021c1101020703030603050d030b03100c02150a 72
    0xf810f00040c920491040000e65400c6031a01d642540082004211140c0aa1040c02880c403440c24155a002c0059603140c0d0703401c1581d04010030b043d0340800c04030a00d0390302226880c1c40e000c1c100c0c50303090003d507510507207135480c014400d0040c0000d07204511502075071000c0c400145a61742c0a402480012500b88010744107030452541040050303005080c030194101c001400c1c400d084000f0b0b1166140d911030000444880c0d220381c41805c00308104100c1000c002c00c02144101c080251a10f003001c140150604001602101501070343c00c40d40038029540f6210000b000402c003001031404c500861450404034004e044100e802a02214050040d9001c81500c1c190040d004d00d0841400030080103450b074082180b603502912010303006078003040305012040643c42d0762005e24400e0b418440c44010110a1542c00c0e64058032049002075111301d41002086401c0027120900c03692400d0034050034041e5008251394007802d200e043c4010391140c0c0c030403007440d0084c825080701c2d003080142c640301441d11303050400103800780 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 376210386 1250 376209136 376209151
    0x506041d070e0a0603030c0f0804030c0e09060721090c0b130504060611030a0c03090308030403030e0c0307080a1709041515080402060d1a1e01020105090705030303130305120a0203 79
    0x880d00069040c03030fa5204101c180c1e41e00d07032103c4041d191113460f20b41e1468107141040380e090a04000100c0803070034800aa90007080c8030000c100003450509002420010054400b80c1441401c28445000412000303c42c040902c0300d0900041011050910900402da1948040689000019150078190f110800c90341038440c2558140a0699a40700448862601503e0302504d40c1007030000440d02881405c00030351807402898549045612900c0b404440da0003940c0c1140460359618036008600414404052841300843c0a8500c152030700511548440d94080001c214120901c0305800c50134040c000e50b0412a8050000c00c400f107028552103100d01414003500c00c405d00f42c400c80c101d12602c5540d03114442ca602902140c18600c049461202070b21041c1c2e84440030114011200c0c1054440c1928289003440261407440f181d030001001a01710f404c05080c0b080300303030003042d0240701c0c0b46c600004990700b000018031550180103940c00c08403a03a02901c844241e184540d002800508503194000e94004c1c000d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 376211636 1250 376210386 376210409
    0x209040e0a020303123418030308160216031209090603030509040203040305160303050a111204140a050f0102031504181509020d0f14030c07090506041d07 68
    0x80349268035541d80c0e9200c1e00030b41c9503108000600c41e00d1460000706800c4802410310200c400f1024001c125059034414000b0360481c1c0124081c140558051164909031510780100c50409003141c5000748900f0740200a02819428819603400f010301c02c00c40d2448480c88a281d07541a00d0300c902c4d21a41c1d540038141e95a001840a040214403110b181c490b005c05c0f45c1c0d25803541807605041406200c065040107005900b8841d0030700082c6030303120411112000b49446503800103414034010600c80f084a40c19110044038206c1881412004030b034000005030096007001c8020041c4c01c01c890840c0c903040c0d4202c402440c83c090079a0001c119001500030314040d80703101200590b5a181d00041c00100c82c20245030f4000598552450305c0422022210008032000d10752001c2984001c540200d440e41456860850b80075aa1100c01d03002e01580590391440ca0800030042c502e4243c10b050100e688400c0342c0901108035640f400480c815550381e500201000410034081c2450404051410380c590324244517107440c00720b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 376212886 1250 376211636 376211651
    0x5040f0c06080c19112e020406050706090c1508040c05010c1509031b080d050c0304050601060809101109010807020705060409020906070c2c040308040231020904 71
    0x20b002e000010300c102d02004040c0d0a00c90030714801e8401e02003010380340301400005084161411418006001c660012075205000842404681810f198901301a1080544140000d20180b90710008075891a41c02c41c0f400304040030581440740e1a82469030148070440380b012100b1030385a402c0054944203500035108494102e40d900300542d15100382d840c00034002000f00c80c4c10301d10420598014600c2c1d6010307160001e2040314042d00c0050312608032000b911410004607003100c0918580c010b19500004090845007141015907885a0303441060080100340030b29440051404d0000b00212815584404400d110884042c0009095584090442400182207000061301b00d40005a08001c540002d02850326092a20128100035006240c442e40d0000080051001003030303600043c030019252107420100400717001802c031050500007030366822155034a0002c12000c25003102460350701540546519000da02000503022074031481050500100c40507004004111915901030300c60706405690401024 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 376214136 1250 376212886 376212899
    0x304031806021506220534140a03141e0612030a0f1202040902120f0907031e0203150610051206060f19020303150d020f01140d05040f0c 60
    0x11484140f018419401007008134526003040c0500004240c040c009228901c4507a809600594405846414803455601584212030490300e0039609401002c071000d070b0004440f038070080c0094001024090080038042200c0711404d000360892003001c144840c610b0718501d03012514000b070f14200007805540c61462000540070707003041c44040110b454030b0402035007040a030080460b00041107101600c2002084810007004490b2400a400940441c60b00940c0340d0b0b00f030342480e1000c50384c0244602e0043c47d42c60305000b080c0c0804115003003601d8000140c600c01c02c0400305d0024a03100d00d210001e4040c4039114001c1e01c0c0401003203920740211001c56a6002d01941e0729402c0301e00b800740030302d0f82c0b50305540d82d0081205803402100500903903031580c607038a0034811118846440b02c1c03404800c1d4409600700000300414020821490540106c3c210342d50194856180c0101e0402c8404003803c03810320607148104002e01c41e11405486840890315001d010798941880c1064202180340c208031558407003250080b864 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 376215386 1250 376214136 376214143
    0xc131e0c05220f0e04170904180c03030e10050a03110417100c0f0e0904032105010609121a06062710081e130c060302071106090a0b031b030403180602 66
    0x50b40d00100c00e0200240b1003100f65201da1f001d0414030781e01a95603a100d81501240080c424400b5000f0303075041e038807a8514200a0f200407984004244502d411945c43c2c0741c450740040c143d0740c0c080c0c04e602d40044c03160041d038043c203100d01c02e64210050007490346514042100e000030300418101060b0b90b080c00307250003100c010380b08001107001ca08081201c42e1903000a60501481c8160312a0182c82d158013040030107102445801a041000c4901300c0d195401402030503003110310740c802030041c001c10300c14023801c0e030b00c503d400106a848020203124141d004a00300343d598200340c40c45100b0610503040e80c86500c03401031a0094503e009076004090103d074086219005824152155448403800740801070140f00b00480520020000f09280701c412095102107a600c642e0300000c0c0c0040d440042e40c607501428041c9180c41e08402d1544030702d004101c0c044450700e41050f00c2045031072441003581c41c0e44441606100007062a06117211104000c000c00050640c4440240301050b40c030b0b010800c0a07600d0b68001c0781c8 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 376216636 1250 376215386 376215391
    0xc050603042a140607051507080106110303271f0f0f090f03050d090c0e090c0307080304090b060715090b01081504020609031501080c131e0c05220f0e 66
    0x503c20820481c1106814081c00030544c00c2e109100703503416140903103180c2c562250141c400d480014002401404826006406d0310700104100e00110b042d440c15070034008480d403054410708d0400310b0b903514010700d0103400c00c544150300040e8004085502d600c2d85208000b4044644c2241d201c500308000c0e000e04403140e00c038088a10746c11030155040714409031016a003503481010302c1280e03250b0726072001c0301203080c1180c442d02500740c450319010f40f81030265403a4903040d01d0050380e900c242c002840c02c00c082c5400004450880303004039800f1030385492203000a07102d40203070700018241e82c0c09104000c0c0030110541c0000c0c24184289541e029998944c0c00e46030303840c010b900d501d081d58185140414094588030002d4030700a42c00804607180007004103500c1c01c180b40280d2103d1b8079503010000b00e40061425400c030031b011090340d40c410418082c42d0010380320f9101100300031443e06944da40c20350005a20803011a40c020104000280920040020000c00704045226015141140040c04145280c02091190 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 376217886 1250 376216636 376216649
    0x1e0501080a03030506060d0501080c0406082413053403030210330801050703020c0705060d0e070b0408011104030803190605030d0503061e18040c050603042a 69
    0x10660303032642c0c2a0001d020113060ba035409402400402c0180006010f846d0292004802503c0000391040c10321080d1041030304404003580001d4540c0c119105924111109c0800b210031020700c0d40c0b1864116401400200006002801070301d00000300c2201061031201184101400702c00c159035070380221840c40c13125010042c016000003160003c0140a5000121980c5500e980e9040b1030800000c280d01a903e10074a8500003603148408200b010028800c81d0341c00780c001c0c201035280900b110344aa07110406409042e1090001041515a60314164481c1060302051000c80e00c2c095203a140c000c1094219119240c1c066081001601e00100d128040e641101d074040c54450460300c564501002d91007900a481d81d0722a52000000b40540d02000803051509080c0c841c240e0f6400c180c2d040c095545030014051030302e003d038240003c05030384810f49030340c0c07a5070502500680070307440718948a8511f10301c981c00154000c40c00700500007030200c15280e00d003800b0701740e1980c80c0170300d5000c44e400d172000300c40c41c850310 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 376219136 1250 376217886 376217893
    0x130608060702030c0d080a18050a0209060402090f01080406091a10090c09051e04050a06060306050f030d0c080706090b0a0f0b01080106110c0607140712050c042d1e050108 75
    0xe5800c3c01040c03050341014541f9004600341250110140c070101da4240c081e00c0503030103500380505600300003500e550040e000341c030305501d440d4100c3c1c0458105003400350300504000c590380004082c4401a070124841d56880341b0300c0344400f40c1e980c10441c800c0b0b07010350300d10008601d81d040019691090388641c903011045a210b680c440c0d0324101c00c20102003240700360700070201e030111f0b54440595030700c1c450144109800d030300c006502c4d420410000c04850b51500858081e83c0710680d584a10340d0001050f0105a800c0d24141010b00c044d483e000100380900c0303400420715801c0240800800040e10340340d902c10454001c003009640b6020380300c00291100a03800f9070200c4c0764000180580c603c2020000d401100d2441202d07074010a0b030001c100c0f25404500183d400e0401c2072110f00034510305014420040000c0085120b001400b0303140c003500d50300004003281c070940d96084102824186042d40140340402907a0351540c100365038000300080c1c8000075140c04408a003543c00c2600744d8040c4a8a4107807800f40006 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 376220386 1250 376219136 376219153
    0x106030821090604020a05150c01090302010e010e0a0b01090c1107030308041502120c0c070b040b03011e030503090607140102120708010611070521030307110d0c0f060c0e130608060702030c 83
    0x1d005143c45001508c8006000811040803422024000c06d28140d200f42e00000d10381c1e04005102c6e084582101c003144240e040005044041603110710a079054071402030740060241d044800c10358401a020001d0f00355806154030000616070031020440c0b149028032144060840400c04000403441002c84000b2440121800305001c0c07078540c80500307880020300080b80c1800e5202c0005c220141c210340d00c039245600d0f0000c014440e03c03d00d101e04a1072443c400e01e04140440c10351751855100d0003041d0b40039003c1c140120310750040c0001250070250350032042c1d00031596140011b044240308030f8122011008986884c000183c05445513110781642c0040d40b002d0081d031401c02041150120380216405002080e442110b110004280300a60140019440c1c0ca601c4070454241142007007805500001801452401c000201d040f22100c9100c0a42c00240043c40011654003660521005030300103400184c0c0380e402d9041c0b42c0003a4800c0098514590440d200c0d660380c59022a034920038a0201700e03458100b01403 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 376221636 1250 376220386 376220389
    0x70b1015082d1806010303170c0708030f0a200a12020706060e0405060718030201030e1006060504081605030a0f030e0d12081b09060c0106030821090604020a05 70
    0xc1040e00200079034152080014049010a03035102c1800000301d096050000f80541d00d5040582c0004402031500503248641c515140a8442ea50310002c0280614841c0001500f41136020111000541c4c010740c030a4807030418003500e1200380c030201d41c0c00b020180344c002c2c0c00c100381840c000d4065110400303003105898440100c00840e81a088001c100242903000d000c8e0388006a1180211006000b22444610151401381041031904101801c0501404401001c031180d00380b203c210801626020300300403c040e405014010300d0000d50300d5a0051107880d0140110381213074040002c2c0b04480148080b00d040030784446c47c1568445c0b1600ca66540355001201c00c0300000c2d1115a50a585070081c204140c003004614041400c2001c0120100e59400e28003140004103074000040c0c980003c00b0081081d0252888485540184a5810241d1140e40c0118017228240d80942113040a15408040f403074641d2890303456010b0025072400760b450324800020014903809400076400c2e202d40d400408140d02c9602c0c080 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 376222886 1250 376221636 376221647
    0x302070303060b03070c03020d080105031e160f0501030617030301051203070609060504060c0206090a020103020f0f040b09010807020a0b0105040216050102030906060102210d02030a090215070b1015 87
    0x4400320141500d912001518020500c0a540324401903214400e50300c1d4203160090034410311650200500c414040144155240020f0f1035212120030b003040e54400b12601d10302c2e03141240070599030445804412005c1961034070800303004108e070002c0e01c0078454551980d890641c201c0040582e115a0352041c4010449441c00d09076422000c12001c0c183e905c5d10445403141e8090310031109056036810303190300c2400308010b42d9101e080721000701440503003194101400080d0725283e40d520060304164011540110030803000301116001849110300365600c0745e48543c0452680c02c00d42032140030886d0343d17000074004e500204454620700d500c80030822040e030130001000000d4020744240c802c80702c505d484400001d04244011802003c60b0030040c0020700e045800240b41c00c20117500c000c80d038040ea50082d04502c2401042d07505103c0303101c40240c4caa9039003240d000000c081140007e980500e40041c0c4680c07100e5540000e01c4000d00400c5050120b0342c07000070044d01d00142c0c5c460442c140144900010251744603d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 376224136 1250 376222886 376222897
    0x706090806153c040e100b012006100b030106021c0e041e0b040b010507150e060f0a060e070e041505042306040905070e0702070510050a110714010302 66
    0x910150741c3d4041441c1c1c80c4441903450340e62078069603449080050b018401400c1c2407407180201e41c24171030754440c4414a81c440d003c03010012422601d03481a1411a03000f45046d0130f049074202140081e81d100740785219940e0078162a82ca411081c0d40c0030225907090340e1401c8906803040350300180542c041510710083c010b017541c040003080003184001c408a0360380d64001c207a0980003115180007600401c80d8017404513040700141c00d100314a0600e240034a660040240c82d083c64010300c10300c15260484c3d0400740580360f01c06041c20395008900821a600108c4501d682c010004c0c44010400b80752500000d542410b070135105000490940c246101c96450300360411000410244800340ca900d90320303401b190543d82c0100001e0410b50b02014a0b6460102d43c50f80c2c01c0d84040219828801c3d09101d81300c95488084502460b07088603040743c0010b82c228000c1040304010724001d800304401e280442c50083c0507401542c80e200000c1c4003031588901403d00054694140e0b82d2100d807848501010600560003580700 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 376225386 1250 376224136 376224139
    0x5060a060c080313080a0806190e130c1a120f0103020109030818041a12030f220e04050703020915150306040608010227060f0301090218030f0f070609080615 69
    0x444130201d00240d1030700060b010805075030b02c07030504130706104041002202c000080c040d0341c280244810012000c04164440e04008000103607074542c8071909008001403090340010204d200091036240341d408a01c401419141d0109800360308a464a0071201f101c1c40c0b083c44040c0c001801e010043c0082400400200081c0340300b40100603100e1040070118054800488844090000890103042c02c4e0030490b030100d52209005025614204260038800707030501891002107544025409140307483c01008030300c100070341924a400c000c1c520b41031030110303a20245800304a0040e101e190202e003800300c40e8641600245002407650340100003000200d003d580000f000c43c0d034401e840e104009014079080c030040201500081c14074503024080d00088011640311000a40114810001c0009101041c8242ca0545441c4076026a03a90305000c925012005605007032541801442ca4582c5103002c000380748001d18500005030b4440781d596000a0300c11404510494000e50011000640303004031101803200300820 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 376226636 1250 376225386 376225411
    0x5150406080c12090f0105010927020301090b0c07120806010c030c1b03050a0605010503031608090d08030c0903062511030d09030906020705030d09030b060111030c070905060a060c0803 81
    0x1140011001440c0c161039071004ca0700603d01010503d035080c00381c4c50150140c03003018003c49400c00c921140171140880300000014549080c0c0701103540a4000c0d00e41d01742c11807400344081c10103600b1510340b6405460205c41c000e11100d000455140100e260500c221016110a00b1000c1162410746241c110f508044440c0d01141c1200d40c4001c0d00300c504032010318006e00040c440c12a541c509042201d8040e0071951203070380148042100307600b00e4100c100b070003544001402e840300c05020100c6d108440b1080700a002c203101108010400c0c1c1c80340080d00c800c10080b0200c8034243c5552031850140f007031810190468500c1002001e6102d401145007404070780851040b2442c0150f5600c00300e0444e00342c0c1e5401c0300001d181c1c40c010081e95030304000040180c0421005048074450020380946100c4082c80000c101400f81000075134160300500040510b140d044050b2903a030600d10302441c1e110021405090450392a10010611a0504a003803105030345581d01d56103481c01248d19110000d4000a0070200c1042 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 376227886 1250 376226636 376226647
    0x7090b0616110301050108010c021e0a140f0303070c03030c080f0c07020105120703060302180f070f03091b180b03030d020c342310020a0813060905150406080c 70
    0x443c02d00c04c1d20f009149400c000581c04d00140d80003400d01070b005800b42e601c400400c485160010010400d646501c2d481070f00a409d07034000004d80d03800e04055004640300360102002300b2610942002d200c200d00303407091340d0410103445024401e42d05400c043e2006848041c4850000d007261142030000c0c0020f41c0141020340c00c1442c2203560240300075085400038000394a80400f0030840c1000351202d00200312409800381c0078508400e000340c42c240700030031703401c10001c0001c500740c0d001c0e00a9215002003604020740c00240320815900560300d020b0303441020f0041c11a04041c1c40c100320140308072050800002c01461506082d40c020300301940007201d008409008066802c4448650380c0011607424038024030070035103403401035689031811905030b00803040c0c404019500a6550075601110342d800100301c400c00c90200d4031510403403804c8003d610007803982070001415000e02d40501c0400041320380c40d40d55014815110028409942c40210011004203000d120502c142c41c060030582d98071041e200d5900b803c01 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 376229136 1250 376227886 376227889
    0xc280507080418060f0e0f07031d0105040c0504020c12070c050d0b0403030b01050a0e190f17100b0a0e0c070c03030302032e03020d05151807090b061611 67
    0x1548280c3c8180300c2201103828881040c551409080b005003100011095071a16020002110302c030020701c0850010780d94130024010394000d5000e42510b800b00201e1007002070306010124006c00042e00d040e110aa078000000030245014021140d0b1160740b5006801e681459102c0505c00744c100c1002103c2c0340030490301c049aaa12416030b6030041b0782c0145c59264890034a030078054121400c481ba910b04110042102c02c000940020400b540100c043e280400d910603001a040502d20311a000b85803001c02407900000c48031100100211100a041c081c0d405a18003001c09000319590940d01940000c8295010043c02c1802c002c060717407062230040e00303e140074600d81d02d00d00301c030900e80c10840c040703640442403000400c5181803124460124005504002000c6405011000390b1848024030a48111002c24100702051081c03500d281d00340d44803401d017820300c44074244643d0541403004030340c1d00c15074000044440c800d00a004442c0302c0600b120b803034980e0050561070240c1040609843d2444501181c003401e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 376230386 1250 376229136 376229153
    0x1204091a10021c020601030201080118091b0302040b0a0e010b03090f070603020a03050a0e120f09120c010f030c050306010507050c090411120309060d0b0109080706020a06050c280507 80
    0x1911101d502400c3e035403516102030000f0492008211045601c000700610061b40c0040081f410b590504014205110920301d40c04003030b11190340010200d0442900d0418816006400c40341a80d1080303c06103c0070150806003e080f00051191480081404004000c4407a0000003503402034032400645100342c403a40001450882c0544c84440042e0f400106507180580c10b01c00c843d04a6400c080510401d071500074010382d1401d081440225103d0000780404100503210111242d8281c050142c010343d411800409407104003504100d03010034841d016001c4414420700ca07109040b0207a442d554216181c9034011102604603c004a6813403041001440403036a0b4030000d140b007a0310400105007030a03070b12018007000c00c0c203505440300184e0040c00b02ca0581da0f2240e058640f900281d100002c0c04070040030040300c0c111780c03907400136405020310000410225404601d8030304184c01090180b0040d200d13007040e000e40788909070100703043d080001f180540310240301c080709500d04100d242c5103041850644491340b2 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 376231636 1250 376230386 376230409
    0x2071203120f0b032109040f0b03070e0c040311121c0221030a05040204090b0901020304021008160c050115121103010509030304080d1805010903111204091a 69
    0x104040040d0301d4550440c90040340010040040140036420100700404d5581902d102007401004010103180c0042c803100c400d590706003000078010301044881162220040031803c0029019000301a00400c050070508806406500c4c0e45455038901807440e1200c0258400c94a0381c1c550049051041c0005004104141c05c04c83c090100c1c0a89203101d90300c2c01924015152000c0200344400100c1c4509028869041c1e981c042c0a900000c0794030fa8840c4001001441c591000425100545062080002c0d0540c061403003a0b1080e521800c0d041d006d40426104413004071801c00348610030031011000140b081c0c50b61045c45100d00c0001c0f072480308040a0810b0282150000c0c05000c1c000043d031404c3c00030090484003042c1c0140c5c000c00580c1480c1c0003c0f030300c03444010405020302c8400994858100c03040d9002140e116800c050030420041985002806040c0c403013001c1c0c001412103100401100d002158900300501c0f2081c0083c5000e2070300d42e1a50140c4942d00d029092140f148040c0000d80d110103281d0310 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 376232886 1250 376231636 376231643
    0xd050412050129182404090204090c030b061504050d0f060c0e0f060a0203030c070c03020a060909150608060f0a030b040f052803051c0c09170f0607030b01020712 71
    0x40b281043c1074180141c4a46866900010b000b00206111004401c410b41080c0c4155059031042040722800204e009000320100003074006d8a401074401c01e0203450740b00c1c00140c0b403040e036441f000c5480310000c02c0100c2081074055000c01c1001c001c00c2160380341c03802c108001c0600c100c2270280e008402c2d807141c60032500d42d0f0000038080f511508982c0b81034982600c1201c0960421072365a420301f224050700954902000700b095105400c00a4401d007400b84180c90403000315801044409056152030b0001e1060060f0f02c03516034500d08059600c600a812802e120f42070b25460355941c43d60b230b41d84908110041d18034141c040d40100961002002040020440d540b0481c0601000ea00300055880d015241c01d42403c4035916000030071400c00518401a00714016868040c82d0103074503a564451015040d2203d841180112880d01d101d4100307107500034020300101c560341e85540a64500000000d03803542e1160700d201040ea04141c0000725114025405010714280c10b204550032181c0b00d61001c03542a1030b401c0b040c0c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 376234136 1250 376232886 376232951
    0x7120e1c180b180111030307110a141f0b030a06051302042a02060f040b270705040b03030c070b2503080901050604090302030d0905030f07150605030d0504120501 71
    0x807070101641e01c6100e0700450080c6040300c00d90745d2010006449000c050601402c0002c80c0301c0b01c40045c4800c0000c04007182c1c2198242c911484065640380da20901c1411b2803414271450070381e01ca16001a482545900d06010340508002ca00c0c41d03031480c0040070700071701c55031484030160070070380150725540f00302180f0040f81d134460110b140303c008032184c00480344800081150721050401c0010301c0c0b40c2200030342050b8455012250382c0c484480803140d8a04224540907000c0500d041c102c1c58900001e880d178202d400c00e6400b0805034604100b03143d201e100d20032400070f09a12004007040101011002450040d000c50781240a100704205102c4e09120940400d600095014041c450741c0b800030310910350030810071079003040f46014640c1d019449020f08449011542c2c1d6908500050082c140101d40036103518007082642c6141c145450384070030503503184069400b8584840411917090004089228a55903203a42c0e0401d480d0a4051502c000211003c8800c0d540740c00081704220441840000c13074203500c4011 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 376235386 1250 376234136 376234147
    0x21908010e100b1b01020702060324060a0219020a0305060c0d230c090d061d06010b040506040506130e0406060504180b13060b100807120e1c180b 64
    0x7800341480014004100040b41030804100a400b903000301c421101d81c6002c841d103807211424120340240075080d4060b4000320000104840c00c4132050020148140d044000c400e0490110180403ca000b82021000943d2100e07590480b011003071806d0068141c8001c207441e80040d1643e68090074900e06950034030030340380e000c2005103090010740a08407041e248064021548511080181c45c2268081c1590811090006501c20306450740042075420ba07412a0061090102c5586100e02051403422100004d004060020a8107400d250454088941c0145a82c0c28141040700300501030740805040358040140010006004140442ca6841a030140900040c0186444280300564140a5480312441c0700c015040b40080d2001c00480d0b001075a01c044034880700340d00e00c2c002e8000c0c50001007041e44441e2006034050b020780d01c4004d80348900c005079102c0e844842d0000105042c2d400c40e2081e043c654100342441c900e941c14100b15028000441d03c1c103049012b406a10003240960383c0c0e0030045044000044 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 376236636 1250 376235386 376235399
    0x6060d141c021b06070f0212060106200304080604120519030b040f0903090315060503030d02071a0705161a091e19020607020a050915030d0e0d060f02190801 69
    0x8402016000c1150843c600510722000480341c0c842c6801c001c1c002804d008801065442c0c80d11240815585a41150b140e56140c48010300000529980b5074072a525204c0124191000881074800302d40d1360000408480e12550b82c2c4a8441c158680100108001803001c07107103014010304041c0b81d246a40c0c60010751421035034107000c140c0d03541d4001c1604440c00c284510000a034801d8110302101e8000010f0b907482180100014050140d44c0d000c643e01d44408101482440304a0780207019a62084202c0515880c0d04101c4000240e02194001c0201d4800c1c088000582c0521901240d841e1003141c00390045010920301d005810801d0f54480015405036003404c080d60a090700032810300d10500010716140101408555400d074460700001e000c0e10004ca0740800315250281502c0123804020304141d01c03440c2090003c00200c4220710814030134400c40490310074140c02a8440d1062400281c080500c12009460342809020610108948503500300422201c4004190b008071440d14140d40d80a4294940700 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 376237886 1250 376236636 376236643
    0x910030b060a06020309040b15040b031f030f1e021503242407060513051002070f060203131e031d18040503120f0601030e0f06060d141c02 61
    0x10441e9024100852042c84101e80010039281120801c607000b08802e940c41005c1403012201c0c0110303e400c500007003004070385d00d0429001303184070740702c200301c5010030b0440c40c175210348502d4051101a00400404510314042008100c5c4040b0a4a0440c1035050780e403035550100355184002e03d040c25030610701205000c503150004920f0301d2560044844012007005480000d080e1249009000f034040c0960315450800401403016501070a0704980208440d10f003c00c40c00c107100b21809021516401015080074030f070405032003507030031944d00045903100e00710301d40d038400c002580090196241c0c0110107280d400007030307210360640106400550b13240781e10b00381528010b84408960403240c6281904030890038419100e01440c428004514101803a40d5100c50030700c18150305c5000181d01d407040505003000195442800058004c00c030070f90b030800c1660b00c82d400c3c00d40c0715500920184500d800001c0072a000e460040440341c2e030a40a00402248a8000319585242c034030881c40340000844081080d6010b981c051 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 376239136 1250 376237886 376237891
    0x901120b1c031803020906010516050f010b010f1b1104140c09030d0306080606270901061809023318041104030b01180603050f07030213110d0c05090910030b 69
    0x42d02022507800c41d40080c6d070b00ca070b008110314100300001ca48034030114100e80014425a80000940d01806001d5130aa806015841c4048e4082644002003007500c5205882407080c000100410701000c403541da41c1d82d48008465242c01d0b0b44a515461010110b4040f000c00d980a031017190700b141e6581d0800020706040203161081e41090614282d0100416400803070200d50001c0c0c200c5065071107508039402480040d152000498000344600c041216170f410540c80030041d145607046070031044038101c0c050426030701704000007034101c2c20449200c44001e6042d021510303290b0401101e00c81c18001c203054100e0a42210004a050001c100205082c5041c584924500340c50b0341440c41c0e2030b00b0f086031107401c101d00043c45400c40803049020669410005a4880c2010350b50101c1583c0ea078015020700c0c640c2d111158002680705600c0b20444035040c00f0035124001e4480441d000f010304000500007400018106054400140b0a00300444801680c400c072801c2c3c4180048410341e0041410340c00c041240e440c00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 376240386 1250 376239136 376239167
    0x1107051506010909092105190512010902190e010e0429030a0f030c021c032001062105100e0708060f0c0d05060f03010c050a080a110901120b1c03 64
    0x101080340c0d0101c0e02e00015200340c0b09200300707400788440c440c16003247c0500c034005804d5942d03442d50f080c401c64168440010300d040810002d04183c1079803160801004c92259860300d041e03050080c0e030007915450059000d030300400c0c0141000038010358001c0200d0141c91038456203145000405881200061200c94a00f140c2402603009210310501607441c01140c110310030024042c40300c1d4484d210115034441d903100d21518816880702e10201e10310314001d040a8088645860b414101040381001010141300e034800300c401c5055200b500401c03a0010410074048000140c07140d008108807140480c1e664000c60008180400003405040d1821003400d0400c0300280c4084150f403140300a010728280d030a025606810103d01d40000d05484084c00101c1c600032803580b0315015400c11900150040d000f40207130494407110f0301c070781009640b41082e030070860b100410054292030781030201c2030603548585d1000c25541c8490400240c084d00d0200010001400c1102543c14142c507240c07404105a882001040484031 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 376241636 1250 376240386 376240391
    0x1121a040f091106030a020d060b030402130c270902030108210a0e1203120a06150908030712110a06090201090e060d0305090103090f05010b0907050f030a1107051506010909 76
    0xd5031a803d00e001406030300d601c1400080302040c0860840d6044410303800001400b0031500da9101010041d5070070807101a4030030201d080d01c034012104d45019030507a11015a03646581c0542d1045004405c00700c0b80b040302e409800080c4c022816200c1c82c0f00850290102d007000b0f01c941c24071445034480d400ea81800103d40d40c0400d1240382e28180d0007040001d6070070804c850000c01940706085240c40c0d030141801c070358070101c404810300c032030010158031140a941d4017022906091140e03004c2a1200c2074503100304441e45e44200102030105603988004100b5800e6440d0210b86600110441131403e42c2403541503441a83e603584400840d03811a6014000700344406007000035140c07a00000d1031400210802400780840007a008005078860703131003c0c1450f544100710075103410302402c20703a0081107240081070081c080c80f804500d48a010b4000d0700c00306c21810040d54035641c0e480ca4294068840350b03485071080402882450f0000b031080c8030311062203411521340150b5140841c001040c214866102d00d140c3c0d413 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 376242886 1250 376241636 376241651
    0xf0903240903130603020715020d20070203100b03070305100e070e070516020418060203040605061203030a0c0507080f0307020105150a03111801122d1101121a040f 72
    0x6079000d40e0f440c11201c450a0050b210603513400d00300050b40541468245c43e46c4002240b40d0281c00c4c0c0c1d805400800004484030f021044003101913000d601c10b0b1440a98160b0003071303001c12101c1e01141c1014020050142c1561041650b90343c54915158540c038001d4070154070ba504554001204001401c0104040e2510380704074213200102418512400728003400c0010016040d2065403100c1e0800e29000b843c1050f00115100c0380d0134801d009400a48040b1051414500802d0762468059000d040d1b421039000078500d541c5800061a008104101d00003051007014003043c804680c1140c0501000c50000c0341c6981e1b2450308d10b0001f0300f15640284200c400d480c0040c210810f07611001c21755000e03203038452035603240c415115001507900d1102c007134195551142d80c8008180784408a82d141c45651043d215404180c5041c045060b00d0714091000300e50030030281640318003080c4001a461036a28040c1000c01400e0740b500413190586011007070307802d1699046d000c01c2101d42003e20410350b0340200290f0801076030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 376244136 1250 376242886 376242907
    0x11010c0905130f0e0607030c110115230d0614100b0d2705030405090c09030a020f1207140102070e0c03070c050709060e06091305060a020f0903240903 66
    0x400d031004460301c0756842604041c0900366910401001c00c0104c01c44038246000b0a004000c0e00381c03208a80c0000c0c050091041e0004014001e42e00c44040c0000301c1c1c4255030411040c4441200d03009411010300d41e08442c903250945541e0104030500307005145c0480d400c0c01c4042031186450018000312a20700424000308040880c0c0d0007a1404d0fa080c5440c042240c0f211304480b0369000e9021801145044500030525040000020041045400980300c011a40e55001c2002c0c409001c1c484035190142c00903a2660700514140070300658540d002031500c0380c620410a141803602d1074941114400d84003804110240c0d6804111040040a21611840f079a2414011010041c0805030218050003902104902040000c2c071412001e040f401d28100a843d03514245500d05070415070340c09000341c00500c00b181e85a941c03001044080360b000710080c440d82e155943c652000790300c004a8480d01d03407003d000040481d03606008070100090342c4042a0104003100d45031700c50340100549038003855801085982d004 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 376245386 1250 376244136 376244149
    0x9020a05120c0a14090114040e0103050c090106050d02160b1306050606090607020405060a03020d08031501030605011d130c02030301031509020d030c03230310050108061503060303070206070311010c0905 89
    0x1018130102d8903140c82c040801a1200700ca0b650758113504071800704001c034159418803c00c2d41200d01a00c2258034014580040c0624a2028082c032000203000f00110760110102e5001040c031032000c800c0c118098040c07034907103401d0408103460303d92803c0031051400e070500c0110701501c0d4020604542c401e107803031100320000b000e03407046940c0240184c0e2180d002408650310b0902180040d5005001d5080c114140d290a4459601c222604602075000d00b90000031548640728560641304187c6500c14400c40e0025401c0c041d9281a141d6544a00400d450600b8519180550740c10b407096034000311f449504610309641c50800305c400d8001003038980701010b0301598641c2c95900c840745e0182001b40681499040494025540300b01b50301ca880e100d18041584000810001d6220714184480d0f0408282ca501c01140d14072410307075410764806000c0d9229942a020780307004541180004045a10700455036010400c1a0018142500443c07048801407a032004d003801a07030916207061030a03810507803c20000411 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 376246636 1250 376245386 376245407
    0x80903030c070209151009090c08070c140c040e16090e1c03020c031603110105010e010b18090a05040b0a061a0a050d0510050301150b030103020f0a09020a05120c0a 72
    0xc80c444800205d05040c000520702d002040001d000c281c0641401e09000d080d510703003440307070603503042c0360600951180f40700f11300d624002c0c8007569604c2d2048807582c980440f030305624009149a07024180710244140d5440c803c0300301a40c003050280100c001c0c44065002210640d600c4001030608004980c10300000100c2c103500c2c00804e0f1445118103143e850000c4000b400303200340500d030a00c00080d4141d04480c6420200030a1032090740c980250030113525800782615420710610b4165030030303100140b2444035418058401030141001038443d8a8202c1e000403801d0000f40e1700b620000b80e03208e061105104a441d0b0312940641031280500c00b040c41d0400a170700c03d610505400e440c0032804684100340c54481c0c000c607016213200b0307081444242800201034040707626a100380f0b0701c01e40c6800c0e0303d501d1284815812104840240c3c2005045a29580a02803001400706209601659000c40802e014000d807000d0940191a50354041d182e141c1c070744124070345060240c14842c0764007090144031040e9a00100750358 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 376247886 1250 376246636 376246639
    0xe0105060310020a02161e1509090c1107030605010e061002060f060411030a0e0118030c020603060103060b0f0d15080d1202090d030c0203011a0a0303080403050d0903030903080903030c0702 83
    0x5130b84048241d0102e05052a00003807070f003c45d131441c000281170200300b000c100c04045840c10003152580c3c0da00203410444000905a00400c0311480c04000100310369201a003c6440360604200c41030600360b4141c142009500100c9081e40e8440060048440c0302441507803009003a0740d000d510049856000c0d550381c4c3d004141d000b9503410500001d50781e450b55000781c08402c510310f540c95100d09001032100b0142c0110001003040d50311301418a01c62a109034600142903806480c0e07412a0b960701e4091180030760000340314a06054441303000141e00070a81004010700420341d0449922a00f141c140c0300d0a0300c0c840066402d1690101034140100c400119055a00c1c0c042e44c14900c2500400000810203400b1300d0342070b603600c203000745a007005041c0c0241f00ca4110074802c41c000c000c2c2a100c1504003904e03103a21460b45402811a407014000203001e00c045681040c001e00b01745092510f40d0242c0000e880d0070340000c80019484a1a0000b0107420407965500002c0c02d001031411450314242201d428029000c029 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 376249136 1250 376247886 376247891
    0xf07060512090709090b090132180f0a031202030c090603040f0506150405010e04051509010905013e19030b031005090f0304060e04050411031c030e0105060310 70
    0x140e0300ba4030421801d4014001550f0a100e001224103000400010481c1c880846500b403c0300080c1c0c0c22500d035142d4810030781c0c25144416220540d4908260710070700500c00c141e03001c4142c291056643e000c005580c0310300d12000050170000304502e0014443d0f00080d55080c0d03502d00620034015025050f0056400500c0255000c0d80c4a03078a5061000054003400c001810074064981401500001030058036000c120540c0d050119990780c2c0c01c68007484904071806410768002089600d22900d545071019000b810718000418a4000c5803104c60866400040071005c0e507844103444a0a00c4c01c3e0a80d40c0d0a108114002d00100030b6074603000c440500c524001c640c20408003041c0d40b040300303029600441e148400502119003111004002a0080c601582c840c0214424000f51f40080080003084a042e07403516039070200da800c0e400050001502000d40100e5007220152005682c1d514100102c0d007801d91402c042080c0c0039044a80a03088a0704400d1028080c0d05140030440036840010708024070b1100e14000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 376250386 1250 376249136 376249141
    0x209040308041e051621120932010305040512030901090b011e080706051c0603150b090709060207260f010603050d050a1d040204050402070b090f07060512 68
    0x707071480941c90303043d0b80011501003812410300c0400500d0305954004104140202911a549012000d0841c126211100d6030458a240010700c501e108118109290034036146140d02e079180700202c40c10822280c0c0710a008461111b59100d50141c0748074040c5401c2c281004581070540302d484e1200901890b0004071480080030841e49042540b152200366000315800c422561a4503044140300e40d10404440d001607002004102118003003065000ca444a40743c50b0f203810b6100f58032030007020000e00019651543c840d400000b01c1c1c0440c1501d44000f0515000054124a8504000002501404140420000715400d000050700040c40d041a0b40c01195803170144107281490205403262401d840095010703560780455a007805402100603a8401c03801d8500d07403040f440301100c8900078030b0070100002d41f041c03120b880045000c0e000b442d440d16024101529060b11040400e0507a40101811140c140719581080303140c01003406003038000070010740a046501d1601400811350700828107004406c0310900c01 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 376251636 1250 376250386 376250393
    0x20f041a3013170a02010605030c0102030310090b0612011401081506180d050703150615050913090512090301140103080a1d030d030c02060906040c1205160902090a0b07020904030804 80
    0x110543c1d10b1084240e1a5180560040207020b08080d100f4070b8064494246403080d0b5600100c1542c6c07090341d0390204800030928107a0840c0281102054107a00110708003d11160000c0c400c0066000e0880d4100e1070b03020303d070008001015144001e0003000500e41303000601d001c5554481c212624903003066801c05176801704600203200c960003218000c003c1d01c03c0d440c00104001c10520380c50300c50111403808003c40c0d961082896400307003c0705841c10000d2030401501e6014980802200000c240300000011071321860340e1050314000c890300781c1c46511040818880380c1381c41c09016421040b140c00c0750b042d216502d16680d40386940070701c00200d07050004005103e01c121201500d80c0c02440001002c03a2a900e102c240060020541040504014058a40014000800043e03400c0c02140d1003006100c0841c50030740000c2131002c2200c012035041c001c00021802c000b807462071038005803500440040c0d0711280300041003107004e81c540c01401c0480d810b108075000f60743c0d84043e282d881501400d2000315a0382d01d02c4e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 376252886 1250 376251636 376251653
    0x30d050f10033f0206071206050a050d05010f0e0309030c010923061204080d061d1f09060f0e06100804170c0a0c0306050108030f030109020f041a3013 66
    0x561820f010342e074120341403103120b40c0004c0d030f01c0c0510b2950f11908a1080c01c40c0c4078109942e40740c01555002515444200107909080703040c1c1055502a20002a0000c2d14a02c01d2060b00d0080703407903110550021074050928038003440f11900e07494003403c000411030710b09008403c80300040701c1e4289850f0403a500100382511040c08441c2a14511104a04c0310f1070240781006042d08400d19140303116181c071f0741c00b21f1980041c19112000b000c03840c415500c0c580d224003a0b908013003151000205540800100054080a64043c20300a404540c000400f5181403071028006084018010340c864164440e8807242140c021044d80e4015400c00c0c04d1f00c100031301580001006100c0c0c01c11110325441540e4401c1c1c2400b005000080c10b40e840340704148226640c035180d641c1d50340106001b01c02c10040c1000100203280080e4001d00d82c000a140d202400d059481042212800000f000226a65000906140b008450301050580002100d58076210b4106001003004241c2c0014904514058003c1400b4140811807 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 376254136 1250 376252886 376252973
    0x180e0c03070c050303010303020109030801141e04020910050304060f053c01060302030405010f020c0316050a0212250f0b03131b0302010e091521030d050f1003 70
    0x3c00c582d5656074a00d030090007082c41c0181907002504007070000c00d10449c07842007440351a00c0100a00d190116041e00b007150300d880314030610340c09942004a05030341d440382044440d40d04c099894850710381c42c190414000342c4150000482c8402d01e081c0400401c0b401d02c01c4040c100e102c8402e500b400c0f0840c5050004075a000c14400300300440030600000801c80c2c1d0640043d07109a101d900240021101d0b0b941002c140d001e18004052650001c3c0300d05078000c141210841c4500d80a0022603030081c0c601e030046400d98454066070030154000c040d5007a000000d81d0882d99162001460704001e040c90300070b03520100b001500520400d00d50000101760b00d1b5910a910f8411280c010582c0035078980d1301d000c00c072442c00852104030b001c5584210100e031a840c00030302d06072041117108490300ca084001c1003000007031013549162840030403a840002d80180c004001812118140c010700007850300b0a600000e54011000700303d000240d00c1140301340001003030800f01030000b20303104028000e07854000d4881c0d001c01c0c3e84c1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 376255386 1250 376254136 376254143
    0xf1b05030d020403050f060402030c04200d0209010206250c03030e010c020f0c0a12110312030702010c090b1e0c07050301021c050f090304060c0320010507180e0c03070c 74
    0x81020740590800d640100b00f03c9120b03604560301001c1c800105a220141114041d50540044c9448905408d2941200300110303981e203522400e42202005e4004190082d1802d080c1c9240d008c03030425420351b010000c2d2500f0076a114134580d9140d0640c80380c5410061240a100200510010070300101400b80d0484908405000e000348640030030000029611003400b418a045441800000900c1c0d0031b00a02150965001004c0c42c00d00800715169894240107901c04150036124541110748000e0027100954010b030301640c00031611045400c0000c0800745950003541011800f08015100200080c000c14500a042184151107601d40401c2d681044041c1e4010b0740c1550000500741f2014881208000250b0000c100400c510389620402d0360009008550243e11680204014088035004400410059200c0e01d404100081503404411030040d842240c00c0d1a41e441e04280b10003541c12180c1340c48100010000c0601e201c0c6031003445540428003034087e1110720703c00808180f03941c4c803840c49242803d42 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 376256636 1250 376255386 376255393
    0x10c060b030d1205070f023307081905010501051204030201060b0d0e010c0804030903110607081803010b1f1d09010303080109060b04061e03380609010f1b05 69
    0x4200780c0103446a8081180c0c0f0300e44914040004400038001c0d000381c030668050b54000d0015043d182002c140380f45000c42500b4903095800c0910403c480b414a40c44d110b10516503c105203801c1100350180e9000c142807035083c43c01d041000511507a64440300342d032010b600703841c041401034446040990050800c0c1d0440013800d8000901c0ba504114036403c445811038413800200305107884054100c5041e00c080d2001800140c82100c03c1020442540d1800c20400c0028843c81c6005126901c4040d02e9000b942030074443c00010400c40980d2400f07104600c00740300107441400508042050000744a180c02c01c0c4403080c49842c035101e0a007680d01c290500c21130713480505112100d5840c0d0402511f982e40074402e9044550802c44003090041c0d4060994044034425102c448082d0501c051001030388217003220340e008060380e03001100c0c3c0d910300c40348183c04905000d0305180380c9a420590143e001d24400301c4134500a2100b0401500b0396640700ba254420f2103542e10f0000d00000f2000c40c9404154100308001d840b911 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 376257886 1250 376256636 376256653
    0x9150309020f0f180c1b0c010f080403030219030608010b100e21011107050d0f02030d0c05090a030b01060f030b03030301093215100207050103020a020307050303150f120606010c060b03 81
    0x4003802d0041400780c8800518002650b20740400541d5801f100d0302c49400117425020324103c4e1070084184c1900540301e0708000d03040140d60054802c58000780c20100b030010391a800204200c510a11030340c82ca11000340c23840030000219140c05800c01c444803072140d0291b801c00413185100402024414100c40300384000b880440881d81d140a069005581c01340c80501038031010a80380c40c010070380c03a030b4040e40940255040102e1501e0384c030020401003443c40f003032040412120b41c403580c4200714a8003031071140000c10125410100700806c03007030880a88a05044c904402000a07650010a5a0443d00b2007036002c125110b1a03e44448006e0b1040c049078039404400001944055504230350324450101401c0f070816880264040212500e103078502e80e800f5807c0407206201e0341d40300307800030410740140d40110307071a040c0c0c0765803010b2859000700e5100d803074140542414035030b5140c03d120040d007000d0100c415844505010b4a6240c54280150040c0d060113510303e83c090810049401002408000800756022135 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 376258992 1106 376257886 376257901
    0x105010c050d1214180705012f01060b0c010903170f0402040506030c0a14040c0f02070909021903050109140303100b0c071509150309020f0f18 63
    0x880c0c40d80d000e91441002c0c44c40683c010402030303508108010350442014107040d03446e04140d041050070001d8282d2400e5241d90481d542c40e00f10301803580c0c00d5824a00c1e43c0108405c2d448611914000301d91000805e0040d4001c00c0c0c0300c2c0c000c1d11030342403076036541e2060a0001c0302180c09030529907025000c500503003020703407080d03921034800760071100d041c402c260000781c500340b20354041c2001c03a1540581200500b4103002d258003100311401c0202c04e0221240c0081d40700c0b60b090144140e500d50f6041e45005564034126500c03012481c0c042e0601d0103c0d02c03400c000b4040c00628005803004041003201c45100200001124412040340300174003219801e01400e1680b540c010810ba101741c0c81040c1006c196880b8003440701c0c8030b8154607200d0184403071074401b0340c40c08a2002221042031520301051000540c890b030807102101502192600b5039405248009411021000c4819000160160070030410 = true := by decide +kernel

theorem cover : BRFrame.Cov 376079136 376258992 := by
  have h0 := BRFrame.cov_init 376079136
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376079136 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 376079136 ≤ n) (h2 : n < 376258992) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
