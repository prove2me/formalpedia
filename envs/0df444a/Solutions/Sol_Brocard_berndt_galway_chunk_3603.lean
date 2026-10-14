-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3603
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:08:36.365611+00:00
-- url     : https://prove2.me/submissions/bd82c9dd-2481-4a5e-bbab-a3f452a5b3f6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 647841726 ≤ n < 648021582 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 647842976 1250 647841726 647841731
    0x130c1d031902010525050c03011b1407080304030e0a141509030a020d050d02010c05131701060906140414070e010513120b070e033708070f05062404 65
    0x1c0d0542e405001103403c50044041c4026089903015440d0240d0203502c3c60494003405925118915843c0c14001c1c1b040703080007002c42905408008009942c1e01e05240d40d0807008030418840b0401040d91300c40590b00c070b0b41c025241c90900b00510740070040c501803a90000ca0300c0c000402e98440c25612206c5c683c074080e0a821210545d250f00c0ca500107454100c2c0d140c0002c0d48003400070340d1001003103000f080b0740300028961340003800320455241040e2000c4c058121184121021801d041104d402c00806120040c0f0074440001070554881c09444280c3c3ca641c0c20480c0d00c101c4001480c5a14281803050b00382485024507800480d040281c0000c22140b103009840f0f0400a000c240303c1e0200200110800c010074041540d60f1320200940f1b00130040350811034030342020881d00000a2070b20700703010411541d00d0410840038110303180f4a2051644650a0740b8100d251a550884440001141030004140313040c011000101c0703101c814a411480c15074008c100301c80e03180046aa01c0951496058401740c04241120302 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 647844226 1250 647842976 647843023
    0x604020a0309080403032303010812030403031e0209010f050301050a0302060304140a1212052e09111201050109030b0a050411090f07031136130c1d03 66
    0x201c0c06841c80350400b800a49000400008040c0c11146140c07030481d00030b100c40320307000905541c0a0381340000d201d0180d80307400400e01c01c10001038460085d0350081c1319090008007000010589031100c1d242d0b403d0008055070001d8104a80c1da084603c5000c1250140b4007d45950b040002091000820340710080c095040400440c00300078128191180e030007008002c41c0c00c1e070346540c00d154110341c90200850001c9a038218004401002078021540b0a04142c0d04040d4900030401e82c900707454200300b504001c5105404004030b0407844500400603c5041001050b480d5443ca0b405020301807810390156042c01050002000001c1d442c1c03e4255105412013400a16540c45040015081e510f1544091b48181014200510b02c00140260344c007031519698100712200b4440e03060a810300c40c42601480c0302e401c50f40b8407000458004810b8155800c81d54141084031110004a44052002c004400040313403140120180d2943c402c00c11614075801c03003c0c0070104242040465143c4810009454420010740c01 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 647845476 1250 647844226 647844247
    0x1f0905010b09040f020109050406051f0908010c05040e010807060c080c070f0e041406011d061504180c1404050436031101090210350f07110303060402 66
    0x69280814090b0101c050b51403c0d141441124000440807404a10340b20300228240c1064400d0304155640501625640020341e078429000140ba0032608081210301d44003c1080442030052030076001c80d42d1146a1030b5810507682160321001600403c1d8198802ca20411850340e00c2410781e45829001401070741d69454220044d801c00c485c640003200c12082e5100300064265645206a10981c010540c41e1040f142202c201c54540000388980b0303090301200008909010074840b841030300301d1f400a0002400c210054008581900a50300a83c280c505655903144407107078038080c3d0070a008007403034011505814100e1002460141c2c6c01054000e56440c0b140c140c5503c080f881c1c03201c1c450840d0015107031f2240018154003680c80c1a1408400044c2d2001c07000080a5050049110165008043c0c8100c01d00c50300c0129020040d400301e1500c071040309900d448a0070f000100345980306144100200c0c03985401d50060203d1030000e065801044242c2001480b8684044162038100784c08540160340c0f41c1a00e103 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 647846726 1250 647845476 647845481
    0x30b100804031b0828030b0906120708010e030a0906032a051b0f010e030306090f09030708161e05060106110307150f0c0503040c03111c060c111f090501 67
    0x1a80141314180005020300c1039820a0b81c2c00d03d00466001241a202c3c92520302281601c42c0c0740e40c102d40000d0868040f5207189004807000301211100c0702101c246035564000350f401c0d10341003641c4400c00e40001840c180b48580c400034a00113070507141424030584c1110703240312503006180203001500903001c900c1c0c1003605100c3e40441d05c89075246204051941103108403551100c0f6407199140791036182c0624680c4850340403041d82d10480c4d0040107444103a594030480000100002d0140300709001c200b1003180000d000001a004440348560312046000d19032600300c0092070700d600000e1450030400510b030001000003414505482651400b101c400c1c00d150883d61075802403080007850b004d500807000c03089244540c00382040343d40119090281d181403160a4803544001d07140035000c4182c00400380f005c118098890032007244040c0104151101c1000d0211b82c1c2020441c0840c2c01684820408001c540c0c48280180e00d5404407003d031030312818000741103110781c21911b451040b403031300c41c4400c0c028080c0a5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 647847976 1250 647846726 647846777
    0xe0616090f06050d05073c03060806060f0114030c03062b14010615120515150f04090204090902040b0301020a0f0c081b07062a02040f111306030b10080403 68
    0x8442c0c0742113420240c042c0c1c10030042e036000c214000e1482607e106600702d209011346e03011103440c4000380605440d01424000c010f42d5045201d03050103000d1890400400840005501c41c0701010314154681c1001e200300b208000c000d074032000120050717010840c441b01010b2281c02d0000c0e405a209038000b0140e5008a0140c5469400090341290780802d146000b90440c886203401090320390100050782d1078014115800c0403140c00b50b03410441400c00c141c942c003200d00c020f2500aa0318031580e420700e991340000340141c1c0e000381c02c00202103403184401400c506060161806c602021402941424246000140f0000460000e20100030a0240038024031060a00311051082091014050071612171030180c1d640701e285c0715a400048000551494581000906092060350000c0d0311031501400c0d0200405003404046820302140c1c1d03200b9a004111281000b40b0080f043d0300009051140762000180840341100b114600900003000750711801680290b20035840f03071703140c03c00c2480c5a940b40720781c2e200c900c0310 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 647849226 1250 647847976 647848007
    0x15020318060a0b030f06070e09090c06031602010e060c030c0901090b0a080603301c1e0b0406032d0b040f231002030603010e0616090f06050d0507 64
    0x70402404220700003a00b0110011a0580860b104400313a001070b90741e60b075411101c1d03e0019100b220501c90307501e4000c0325aa00540c0000880c0e6144c2c9030300c0001011648280e411a40600790030441601d02d980a0140514601000014114520b02036240041c00e1000400d40b0207005800101e4680070382c002c0c5000000b038548148090348403070b65841d0280401c80140c0d52140f091040e521907924048100d0000002c1c10155800e11401c0c62490450780115040b500040e100d42c02e048810121703504e0a07101d1041820002c01d4604104040107901c00c040382c2d448202540180e0130050305001092002c2031154051f0000c080800302c4040070b02c1c02d90080c2491050003800e20540d0350034003090129040805e00711a02600949409050616001c131880c111103640b0f90700d40d00b01090614a002c2158095581b001000d400400c641c45090140f034100030003100d440700e049a404407001750456100d928035024106000b15802d50718103100c07014140e030180050284010307483e0300c000313144640704460500c01ca040 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 647850476 1250 647849226 647849233
    0x101508070e0316030b040b060d050c1e030d031407020102040605090d06060b0c07030201020c1c1709130609110f030114040b0d050d12021306050714030a12150315020318 74
    0x1101c2c6403000451700d066034180c3c0c070303240f5a074040348180c50498483c400c026030081c0103150024a01080c809140c00118001c0c2d1921101402d000030f5440c14400c09001304c0d502d0381c3c002540c006c080030003002d00b100a0401000c586c030600c4188115a048030403240c035a2000c03100090010560301d00007014260707a0300214000302c400b103410706c11100005000c1050364800d1302900d414404601c20301c050a0041c00141c0c116803002601900400c4c1559100c2c3c0540c00741040742c2d0724010460010942c074114980903821030306ea0b142c0341081104840d02c00d06605420303c080e800d03c1c081c9061094106c1d40810b0148010821460100003186c0e130750355012950f0500040c1060b4254013250802c981c86040c4041c500d40460380c2410a8000c142261085840740d40d42442d40c0b41a050411000f140c054100e1101124400d14120342d442c021182080070307000a081c0d40d940c6524003040514450103070b440021400046800c000c80500c002180003c503848045801c1c40300580300d65540490302407040840c10711406600 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 647851726 1250 647850476 647850479
    0x403022103131401020109081204020102010b040e030c011401030b04030f1b0305041d160c03020a060204090e10021806071b030c17030310050613031703101508070e0316 74
    0xb00c41d003103580441e0031206042d084151064016803d0b00e00681000f031099004004040c072204000072202e4001d070041c4000110980c3d04e0020030704543c02c400c503a40c9968400309803a08050000d000d0003001e441c80113151501c0e545140c0d160740101c2c801801c01414001005900b94019200d020004103035030044c5d0045a1000e003070b01340500395610502a00c0b4a40c0c02c03402417080303402286200207019070847d2800340c1c003020440c9003c0300c0d0655460001c4045008809490000c901c5070300180015000c6008001020040d403201c02c1c3c81d0207410140129042d0052121a90003540d0400005003c0000d45640c4d503520a2841c101c1480302e00042c030004051513121001c0180940c0c80008402c0e2080c40303000050320400055455a640011280c1d280300a1034140144514100322014204100f02001485852a1240c0d68040481c0d511444049000d001100708002e150341c00803481d00400601a40f40280e01b406a8010444c4600031300c4103090081b07a41990030a80c8040091007121046244c00c8003015 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 647852976 1250 647851726 647851747
    0x11b0c060e01050c0a08090307050a2402061006030506180a0e19080d02070305040302180a051806040f0804170606031006060206070315030f2f0102030403022103 71
    0x100040c0200e4001403540710380c501e038650042c3d080712040322a000040517031440c242d44030407103680011109034144c014140e000805468440400002d0088800c01030030b0184005481105145c440c034007441158030103010300c126484142c20900c1510181c0c9004107a5558074408a03003480c10740070b6090001605041080b04655581c0d0080c0c06040d035450039550030b11036142140820144c0300c00041c109000170003101d180034036280d00800000d84242003003800e040d0f8940014030802044610300c50382d2381c03150b0304010703d810765442416072028400f0540c42550074049502a5a2500108020b2906425082d010244030079001a607004103081a003d0b13040010110440780c49000598402e030083c0708130003081000e003015025400984000781d00a200942c0d40090403030140c0170034481752040c00c0c82c404020020555400e07140928a015080754030109020b009202903071550301c10141404010301020700d13801c0e81d02100b2102120340445801038213000c91008002ca04200d120b154105210015030301510 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 647854226 1250 647852976 647852993
    0x50114070c030f0509060d050a090219030c0b040e0112020f0a060c211e050c030307051c050105100f0203040509160212030c0403080c16230409150b011b 67
    0x4240300b5540e00007000d0302518103a1312800f415140d140c0c031070802e000c1e001c400c03a1150301c2942d00c0380c0d0b10000458011000e40204074200400081d45802d880e02d5241030041c000202000001050a0704100b803030f043c82c0605108503c0c2042c0203201809203c80c11541c190341d5503c40400358000000e05040f070013036681d83c0203410b1561403081200c100501e0341900640b5542c80d102c481c5200d00603101c001607400b402007522044000b0b13006503401c0c407000303115061244a080001d10b00ca0641ca4455994800661804541c942e022207210301d400c1c0c0c20000180155200c010044040c80e209091041d02403441800690844c0195000b054001c2c65000402001402e050380d10301c2254016001d407212039250f032980c2e21080c03100302e52481c1240c80411040000880c41c400400c0c52034000c0040d50300409030f00b4074907802d50b4515840400c88c281c00050f10001ca199200754116144000c0350100010903a82d0340350b260340381ea98840d072110282c0d5241c9141059000341985201e0b504408480d0303443c8511890070b44074 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 647855476 1250 647854226 647854247
    0x3020d02240405040e0307021003050601091a04050901080d090306020f07050105090304050f060412030e04020c03030a0c0212090102070e06190b12130f06050c1b210f1605011407 78
    0x41a4100301c40050705c003001004076441c00c3e8004d4502e40030202500000c0c0e0203014060319031810424807010008455000110481812801000340340da1503207400100000c003001138005005035000440d15805040d040450107003203e030700000241e01e440c5e0b0603520080b075005051000c3c182d5400d1004124010501000078415224210b500d1443c40e000c4806001c00b80c043c0f4041c414212521101c81c1000c61700501600303403103101c010805440d00300c48541c05425900246e454009450300c9000ea012103d4040c040c140c03000f254103142c00d041c0b0010f030000035624001442400140d60080300800c0e40b03515140a5000b003d641d01030a140d0603031b82c40b801c0d006107920034440d090190f03080ca000315600c05031160018207095001400300343d1026081d19500002e04c0040c0060100d540200007075070026401c1100b5505800c00b213000780000c1c801c0040407907250305004800b811040c10400c041b14400d0311480940782210420074075480000c8842c5031540c01455440940740c5001c80f000c0821110700c0c0c0c401149074 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 647856726 1250 647855476 647855479
    0x6010b12160e030a150c0e030307081c0c0807020606060a0906050d020d06030b041b15030e0f010e03040f0e40060e010b10020613030215040c0e0705031003020d02240405 74
    0x41b56918582101e504151450043d8503410030410344000c5018440906500c50303909015458440441e0255812200c1911700c6001050010701000210b03501031001700c0d8454816101035141140d202401044202280594000d0000101c0c4150404c201541a24a40310b605401006901e4903424905100a011141100c1d0b540d000505030030141c0c602040001203490608480100c2c090b003060507400f4113a002e0380c01203076104d032031200c0340454024020b03080010100c0e0302440c0d80314100720345010f01c00c1041d042200d400c5003d0081c41503114400780c02c143c06151f21010800c0020343d01d14005c100300148881a081c0d0383c1303400e01010a110440c2e21249004103c40000c011412034201072103440040d0038400b001503041500020319004a69041c00021341c4244151100d405c0302c200c480c02c04000c151415541c940580b0424050002020329042e00281d00d41410b03410351401d05040ca4a030003c90000070301403240a03265404640715401076450724503d49100100e0400e9000008072590003910585 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 647857976 1250 647856726 647856731
    0x90c020f120f03010b1612050c0d032c0f0609100c021b130b06030109021803162705090a02030115140f0f090903070506010b12160e030a15 61
    0x425204561007181c2542e03101a407124116841c0000c08006900310003104841e8003100c1c42c2c40703c001004c41503040d103204003e45130300c1d49801d000c4a150745401040103988080c10319000c071a04100c80400c0e004601125001c10300c51103060403000850405085c0892a0704d2803003208240300035400c02140c40030350703001a8502004190482c0004036900c0b141000b9416075840b00602c80d414038281440104107025484e80d0225294100c1004100b40e0f900982c440350143e50301140b14401c0060352048203030118401c0b001050f003400042c172003101c691900d11540111981c0d85100c403c24041308680b5038100c103c40da05c100618606055025110303020031070200c1c420b520784075904e0178003400b000001e030a80d4500d03d400d40c10b01140070248000b01410409440c0e004980005492030390b40c656201a01c0744405134051900c600f482e01c1c01034582a41070f0410541340c4014041c2c2d84411168035100340c2d11090303034804502008012101524502001d03144241c0600070400440c0621000801101c03084c20740207000c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 647859226 1250 647857976 647857993
    0x307020a02180f28110906071505011a0301180f0603120915050421020d0c0905010b0f0304110d0203120c19050c0904110901120302100504020109090c09090c020f 71
    0x4c00c9030070034079280c502c0601c070941070410901c120b502a05000c0d0300740803400c0c0b40000b80c40000720550401d602c2100c02c0d40700d080c00c10040006d01d016860040ca034032514812211060889100c5900050098164a1100b04550050206640c010151300244004104072036901ca00784035860252900700c2c0e0000c03a40300b1000003040340b0f82520311441d9244a0303880d58189800c1805036051010100d1020100840002c07202015a65131004042e525203e00107141080d403904880500783c5105038407004007021706206002c2180c0d0840d0441b54050707030150b14601043d0710040010000b03a46107034040d406100d1280c041240c00c01010007805401000f00444844500e1a10060203114814038003c11a81244010084904140c16a590400d10805550505900d031a0115403070359026030000d9480b05500c0178420600d40c0600c000f441c1c0c3e5000c0b920a110a140075000030344103401c0d0b0f10403040d082d5591442490083d224509400c041c1c03031903440600144803c00c0c0001d6480e5001a0380380f40a0052400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 647860476 1250 647859226 647859241
    0x360a1818150c08010608150103020c1009140d020a111c030503240d0b19090614070e01090b090114070b0901060e0f0a1d0a050708010f09050a080307020a02180f 70
    0x1032260491701c4d555a601390594607001340d0042d480c0c0c109001070500d5000d01800500740d40901401e030780f01d12001d00000340c818441c141003903041502d03000c3e07000326005000c030814456070210744610400c1e0844041a68001d811000c504180386070514901c250b11000c408004040d0700c1801580150481c41d00b61070341034503040c1039041e0304a038036008603400390800807501c000a10686030030344e015075540030000c01c220440181901b51003c4680c11180b1641d9910692090280c640c10641c10541d140fa111151078a00030000c4c01c011014012a8846c80c004202c2d0800740e031041c100701314411119034110b07440f40b900b450700c00b42c65a400e4840760324550a0400c08554a8007210b01c0b83e00c1840c1b241c001000b40c2d101c00000354010322943c0c11240958450740200c0c03420910810074270308001d01c02d01c0181041441d03d1461400c40324000e440000c00350800524401080000825428182e00006104d50740c0d1150b00c0d060f890643c800700000c0d04078002a82500a070045120010b108a4021550071065541e414 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 647861726 1250 647860476 647860487
    0xf150a0b09061c0b01060504050a090c051c020f041d01090509031209121603030b150904020d0902041d0d0305040305270402360a1818150c 61
    0x1100c580114451001416074500700601400c941c40c3d02c803212030003440d80d880c0e0b8a40c80509030009400f2800c000340801c00703800c0c410742880052010040400c10f0794005140104203224204002c11001d450000150404200d40c3c100c800760581441403940c2c66549151602e40e000d01d440c0d1101458140c2400000c41ca580da00409200340c0301c0c2400380d4035140c04100010444c44024180d12228410014183c0361031070208000d03c001e1024000ca0020440145001000c1d1150804881c0c06020040059203004518005407031462008035009a201d5140b5881c5c8002007240800103584113042036401d4180240b402514182d9111850503134201400100c0240c040d21400d0b01c0041c0021010009640c610100c001000e40d0f08844030141129160380780e0000e0300b80d0b00860482c0015401810f98414606142c1141c0510700d08640b0b1a18801c036100c00000e110904184a85c0e80241c404038441109407040b6488114910500940c00441a550781440c641038442d060450120310b1518003060461f80c00742 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 647862976 1250 647861726 647861741
    0x3060b03070504060c08090d0305030603010b030f0601052431060512070210150819050d050a09080f100c0c21020f01050a0b01180b030105061303050f150a 68
    0x40d212203142c01d01c2c01c00d04481702e201003103066036003050503c800314103641d030410b01005550103656840c7d102d040450405086034074001d82144a41d001c01c8234a650b00e0340c003080030341c116202255401c44403500710462446196025841c0e01605100040c0e0312108086400040f400121304a2043c0e54000b006018401180c0e09000780400314005024007101c2282c440011644005c007481a0b03034a94560100480030303a451703071540c0b000c002e5481500b400105020819400c0c44040e0340c1c0c81c003110b10360300d807a1243c581000316001c0c401c0010018203902c0c1c890140c04100000c018500c1102c0f8a0020705402586400264508250b0310f8285651143c009201d02c8440b10401d81041c8450851810002449407000c10111504258024401582029402885610707c20740040c40041102c83c0000d00040c03000f00c400d03100c0c0342e025803030f41d01c14040c014065058905551099480954851301030741c0b030710b801090035840141b032407003880d010199050000c903503070800d10459103402c034094482849170400d13600312 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 647864226 1250 647862976 647862991
    0x7050a150c08090a0f06020405091003060b0609280b0a09030303051506180a0f0b030a0e0105070504030f050705100315080d0f05090d020402070b010815040b0c2b06050103060b03 78
    0x712803213034086030320007959030401449504010700d05651a00800d4403020b007240e41a240500209040080c00f005000340019403c0807116145045242d000190004017402d5041070031a40302d02d00b0018140b401364104010f09000108103484120780074008000f8040d0340821800682010045070f880280300b900c1a59070100101101c1c01c0038060f0352002c00d0040507145865000d080d00c1c0b000070301c80700c103038450b94090407035010019a01d240c010b420303c066882e0030b0300840c00e981c035160800100542c802c065400f80c0303501c00c01f08509031103e824903602e080701d00c3d008158403034244030740141615015486404040200f0504101c07141c0d440c440b45d52100340401e03900c000300d6810598060624402c40c0200070021004104590002c039503000700d0300302d07003151404840780c6911100501000f0000c03c5101402c004403140b0205600d069510400c9010020704117040541c40461681c0c42201104000208064000d0300c1000e5140d00040d840060600b82c0304250100e4a80400422015041c0c070859225004 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 647865476 1250 647864226 647864233
    0x809030705330c1c1b270302090c07060605030d050a0e0a0305100e010906060b0306011202190e01050c012406050316180b040f0603050a0513031407050a150c0809 71
    0x42c00c80c051813070304040c00f6680425901d0f81e00e07180310410005070381d00011169403400309101e02956490812030042020303404110300b02d002000169920141d0035881210002c009849245a18001340500f030103402295050081400c2244101d5200000d8100d01c03034107980b181056040501480750400550001800030341100c1c1c40311000c40d00641042400c0d20001c400040c04150380d4490100300c40c0c150b081070500040001c1400840e60748003940011243d0035800861a01e80070344c1060029030a0110590280000d12614180d20f038000c0c1d05441981d05288001e01c100d4101c4642e24481d00c0110448421894143c14045003441c0b2a03802ea0b0310405131000c00900400710707080305031030511203010101c511800d0f440022514405900280005042640e2817400b0319007041c40150689100030b00700711009203043c040149001d101162051940d0705410030354105104007459544c80c0c0b09044010b0004d01c103c05419040044401c205407800211102c208507072500c503501100d00c80d1040c0c0b4911621752 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 647866726 1250 647865476 647865487
    0x82b050f0f040b06010302032a19050a050406080c04030b250e09011e1a0a021b011d0a0902040e090c03070302012001091e0c0e06100809030705330c 65
    0x5020340c0c000c6400641805d036044d00030b004035803d003440ca15114070350102540042040c1d0384540306d032b0b1150200b035005800c0c4030b404d062040034014098001c51207250b04001700f84d07010403540e031080c07001c0b54003968102504031490318219a5000c81c400001c40c107510583c4800c0040d840761072043c440c03c41d041c0c00041a414042e40381c50b040100e000c4c1803c01e0b000790301041c074100140850f04104602100d01406020580303859403c040030381403440b000c2c0a040c12a010801c407070030707581e40706541043d41072680990041c0410400040b440703040311038004000c00c600c0020085a058030003294070380f0661942c011900d466032003c0515495110601c0000d000c10300568001c038803140703600e6220b01c0c3c242d00480002103041c000d84818180000c000c0f070b400f07200111081058140305480802070003070f0031111996069401c142c0301040142c03078014103520030072482002080000c50140704070303910150080b0171902c460180c1403442c07404400c040d0264441c9118284100500000148018445c2c0d2140919a0802 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 647867976 1250 647866726 647866729
    0x6020a2d0f110306042015042120040605150304080a0e031014070c0b06040c030f111c11161407080c0103060807050904082b050f0f040b06 61
    0x70340480e03007112032100745016106651030411130320744694001c045401c800009010074078220f41d26961110b0094199005445c00c80d070303001d0122012140310050180ca002d00c07140c00385400d00301980f8010100d5428190b1019080c55402c017400704c008c1d0489007080469a0740080204000e010b500b113192004040c000200070541c030380e01420856101e402c02c01d0b840c144040029003007010039509080c03140e075101d00740d010b44018030400d503034824030301d0402c800040c50f191503a00c8004001800c00d4811034949100c180c001c0c0c801c1c0c1200c404e15030b60020a000071a60059664515004030694842506413101c603c0510200c40c0501101c00030341302400340c0381007a80041010517108000c000c1d00d0340c105104801000c50020003a00d001042141d010344249140d083c001801e903840380c4e01c08020b41c0c0c40700e00240030650750043d030941c2181d4400c0c2c04960760044408024800703401c1d440c85280d4550950418010040984c012510481d5050401d440e81c0d034600b0740841c044841618003a080e6040f81000607ca03 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 647869226 1250 647867976 647867993
    0x160f171203010806101d0f073c05040303050f0901030e1009140f0c060307090806250507080307080615040909060b030703121d06030106020a2d 63
    0x8502202095a030300300c0c4501001891a8002e0b442040b4591150040000f944460300704c440107420062140300340c02c03441d140540c0301c002015000d800c08120140c0402c04450046c450700541c0c40094a038240000360000400642082140030310561904158140c29458404c00c1145c0a4a0380354076554107040c05180d41008540081c124903060541d10780307180700b05207803c0010030f0703120346001c40208880c412442e103441d03501480a000d0209a000301c52010302410701140032a103000094604544075a100402100c043e071341a40580300f18080c840078081d8046100010114400f80b00740300d00c083e80d0340c110741100d103071055541c05020140d0620210728102d118510719600480014090407600d094030760603500e00e620a91244003015681c41003c01000002d01601d40c80000c00c40107011154035540f5101403c6a55401d14400c0044684c04d070710720302c802549544c83c41c00d40544070035100d41e12540c0195660142c04415541909400d00c1800f840078542d007105400c1d00002100c02c10300c141590b84510 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 647870476 1250 647869226 647869259
    0x30309160303021507020a020409050a05010b0a050609010e03010b0a15090806010605181305010906050f09060d080309010f0c090504380103020d050a0501050a1505070818130509160f 80
    0x450103000c1c0d11f10050390750b5000e0403980d50f0203030001d0103c140c8607143c46401c40e4140c00ca40c40c010000b40c0307401c01030769513044140c0c0c4d50820207081101b039040d100000240100030403180036a101501c650b000c41c200103440c0d44044070305403c4e1145022213490310782d82541c0b040c00b40324003000500c003040700d20740d0b00b000455a520040d40103029a52118144158001501c02c01d80010342c12170381c2c0c0d440030811841c10000c1000d841c0c0080d1260002d5007000d1001c1115210600d81c06040150000045601c1000950004110700b181c0c1d04100030718100700c0802481c0712507500c1090f124a040c840c82051804480c4801141d01d031082c2c6080807900e1902030560540c0c0324106000d814076a003404003410174081742c000d071442000700c403800099560601d41001080041c03a0059602c6807050120070070002d4022048400325900444502c0d00da11000c03084d8003090440c2d140e0325410804403a41205000d0103a0442d07401000b4040546010000c0182514001c01044c0302d0000340c41524501001510188603001d003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 647871726 1250 647870476 647870491
    0x303061011010c081504060302130c0c0f0b07030b01020613022107090c09080609060408070809130c1b020f040921050408060f04030518060c0a03020303091603030215 73
    0x103401e048014121400c54080b21a0700001c81c08460420000035400c2c4010690848116000c000c40c40c1150041904103544c0c0035400041c0b0f80d00d000c0d00103c0782c09224018a01688060021601000d07454070740c030401c4040e030740200840d0900381c00880030b41c00806c80c41c1c403480d649d020748503241019030208410402440010b443c402c02200e0300d03a039064018468040035200418000ca00ea04841d90020010f6580e584001110b820400a00c14000300208401e5041904480402d07202e0015080c41c048a11601d092682c2c0000303d030711186540c04081e0071603800d2484c0b40c3c4940e04809040c240c08080c20084000003036000e4001d0000c04058902a4001060303140542108540c90f01d49521050094081020b2140850b001190800c4180b90804c60260300c51181c50240300a420241c0e400340080c05180351500300a40769206c103103c9600d034a401c0c1da080715407140c2100d02220840c1030180d100d03841503d202e443c0f8080c0941d100000d06880c003034041207070f40c154003c00c02124039541480c514000a44030700c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 647872976 1250 647871726 647871737
    0xb06070b15040609140106050301030812040816050c0a0e0105030a02270f04050d02070506030a020a0315061116061e09030f121206051302070618060203012603030610 73
    0x10503040c2c0711480f890004d440007403400240d40102004013000f8010590128042000030001400041c5140042e00e0925a2558a801c9192140c3c034121501d8080c6400b8810340002c400d98001c1803200011700c0f01d00b43c8105647da02280c030f8403203941580347d510902455406600085030385006082c1540d01d00380c0c0c0362880643c045480704a4044e803522840a8442034002c1007200c0a1001348002071000c4403402080e0300080c01d400d45880f0108081d800028160a001ea03400b141850381e41e0700a41099944046001031006911b848004c00b4140c0111141101c16511450000001050024403040c090305c0705038594014141140040d034540b0790a10584e403007040342940c80000020710721000c0c1c076401441880c402038507800901000742040f581d02500c010240c28424104940d881d044124400a015900701507903a00e01402d001015043c443c03140c80034100b2401018080c0036060f400b460503030b5014910f40010380e03c813440106883c9541c07290001039410070400302d901450001c0d1064041705090424 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 647874226 1250 647872976 647873011
    0x1091202011803060c0f020c0d0b0603100e06011a0f0405091f03030234060f02030c06250c032a080a030501081603080d021b030c011a01030b06070b 65
    0x1006800b0105a1048802070788401030b0600c0250000400300030450300b4402016010010400520950704ca10030141000b80c92030082800c41d1400c0c080f010032144881d03001d01088041034000c50307039003100b4860300008801d0030100039588e400b01000c8508601d401001603081c10305040420410700b4025010a0507440502008054083c005019a005500039005404c0c241d03001c12030f50340b0603c04490540b0743c400c001480540c894011400000031340d281850418202c00c0b01d610168614071582c40d6009140c0f0603081000740000180d00303182950203024500c168400f00803041078410151154009011502d030507800d52a1045468103115240000b2040c00803510076a100c02071554011140100025145d00061003d8002000305e030080f00488000400d10b240385449005580c0202c0200314040b54001906031038448a9a45040010208009890755214010841402409450801a0600804401104e4030340c0644540d000c0c141000d03000c145424a10707901c1c18440d401c020700a107000c0c2045940d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 647875476 1250 647874226 647874257
    0x609070501030218100e18061e030604030e131e0c0e01051603140a03020d1a0d03030f0e1218010806060403080706061e0911070c0e07090b0d0b10030b0109120201 71
    0xc02e40090b58964007c403400c0071010b00440c031aa180da520708006030388110a209880000d42c480d485505880c0c1040200744000010b940240c600314100105400c04079048031041d0440c05103505906111004c1111021400c1c0981d65503500300c0d44d80340802d1080c440003607644c00000b01d40e000148a0318150000f0b011007040b14016421642c10400003030b5011600034a0402503104201120316900b40b40100080c9090020303d25128034003005040548a180030500c0c02c400340c10102d1440180003d8840c50160743c000c040d900d40240c0740000c19130b0700c035038804241c41d4002c030840c501132800136049034941400d58864961540c0000300856129039541c40006468060700041442c0d10014040c030300d00603140814140030f40f29505501d5010780010041000080c071300a90240440740c100e1030301d51150740c2d0050180d42d90210350f409000748040004d010511080035602404c100f100031142d8452080000104400310b605081045010030007880e0284103183d5042d0b0b11030400c0744140f401d10f860204180 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 647876726 1250 647875476 647875489
    0x40306021615051006030209031203071e0905060d020c0c0a09060906080c0a27050906040c0602150a050a0e030f090a05060c06010527090609070501030218100e 70
    0xa9200640c801c0111079004100512401c034040c1205140300780304a05040d0400034007240903109007800c1c940d000408070f4003038905005147c0e04001c03696000342c0380c0c0740c100c902401700300c1900c00b480c64141044160244072400b4601d9001a2903014203401e040682130803240f00298049005225039229806604800742d4a42c1c407064041c205001d00030828620703281c480780944840b90031964158000c0390f0100d00c240c4810301c84104171460320740030400134440b40740d84c0c840101d400c80255540b141003a00704031161000085d442d00583c42108008905940d40d03800300e0f10381f0b555000b0784130381b2541640459100f9000380c22098000e401444001090040b0b012801d01d16400041001e00801000c200280c003032034482020701c002d01e0240c91a616003d91421016103c110500419110350b0200c1907080e032000c89440308d010403c2d0107501e54440c07410440c1206540e954219008015803242c908046000e512070b00070384030300c1c900b440f803d4103541401c40100108100c403800c541040003140c02440310a551440c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 647877976 1250 647876726 647876737
    0x90504021c0f12020d0516020604051c0b0705090d0b1b04080105100e0408120c090a0e161e030b0f0316080d0e0f010509040906020406030c02010509010c0206071404030602 75
    0xc002501004000d07290115203030b0883d05000c019508141c503a5031070603410008603050b40341480c980806816103440060850300658000b9500110a00d0503441d101c0020900400c415001d030f080c10020381c1e41d2800485d180d219040881d5040345002c04100005245040c80035000142210481441054019190590b800541c040000b40e9103e40c14400700c3d003031000c1000090702501c40041040d20b8075031204a410712074035005040032042c1c100013510742010003081d40c0907184000c00c244240c035501c402c000030300b44042c0d94100000d00d0712440c011203540600c0d6a1041c42c0080c0d020410140342c0743e042078004000e0703d14980d4100303d981d0846504e664051101d48070080704e00340844101410f058000740345c08035041042e4144589030003204d55543d134205884006050919040340d03101c560102007809800071001c01800700e40080f0f000324007241c040d00703c10364180c030541c020816a56004052401c1c3c40b5840c000c0703005604402e01042d030703003032080d52012003900001c0c4000349004c0d0344eaa6040c0499010 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 647879226 1250 647877976 647877983
    0x712020c0c2d030a03020607140d050109020406182d0905070206010602190305190e03011d101803030509120d06062d050318070e06040e030f04090504021c 68
    0x90b2a00322002c11400000000c80081d0b0041103030044d1598081d640306000782060b402e10010700081c1c0a66111001114000b180041c0c0a0103196903c00030030001c2d4100d40a045c1c007082210890002560025540034200c07400040c040380600340f101c09802c07141c40030901002d410010b541c00810780f141741d80101405104141d0060155600d0160002d003009a03080003806403220a81142010a51001c140c6510b0082c0b5032015586245031503040e04d000004404254041d401c0605410702d0205201c0801081040d41041e50b6031881c0c0d94500b0000ca401c180c040f0400854001404404203108e0740c040c0780c6c4a0711140480d04e02400c50469801c1d650070003004041010b844810910105902045401040300c2d8060354409000d113002c0301504003108052100b041006c0480000c425003203032501000014511801e41d010252210750400340384100700d45840c05642868182d054801c400021a02207414003403c0340d04083c100b00c02c2030042d00d009001071760f0000244014414410700c103035030062843d11 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 647880476 1250 647879226 647879269
    0x18012615040c020d08060603071704030c0308060a030818061201030f0203072c0403140f030912040501020d0f0909020c03030703322a030a0b090712020c0c 68
    0x1003003020030090300d103210210740841d04502886402590040c9116410120841d0310b5038a03030344c400e0412540410b6400d04880360842200c1071005268010103d03901550285d41e90b49600d0341e4003c10b020750030046100042129008100b007140750b803400b60400b03400c484020503003032038610b210340d011000500a80050f110340c043d04140c00110726080000000603d865213051078414400301307107081c8580c480e02e0b0000280c02e40354002030401d480b540c0d410a0421003107143c55190925100f4901041d00200c581006034811070241c80c8102903090292000c41f40141e00030164280416800c942010001c0211028040a1003008c51011603600103042c40a014000440e101c5c64001c0000f010b0f0b96203e108070003c904047c002090390000540000400c0c43d41d0000c0c51b026403515031240500d0b103080000303900c00e2250000607112864102c001503000f9040950180050001d41d010081e00300800d6a90304045000b80714800c841100a4014000e09080042a0f030b2401503110040b466207103000350000711854 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 647881726 1250 647880476 647880511
    0xe040e150406020c030c1c020606012111030a060e0f06031e01200304020f010801053f0a0b0f01060f030b0301090f060204051903110105030402130c050904050903180126 74
    0xd2000d080c01f116005588020080e9086c0352002820802d000700d42c09000c2007640e40c0302c1c00c85071a150807100c0351180d080300c22582d9261540c00440105060b0080e142c0c910000d03804102c1c0151740c120054020340004000d44400d0000410403c015854a200f600c919500c0d08040d5610315506003089003140b5030014134035601c3c07403e03204020000d290803412a045c001054018800364a50340320844105003480c00441440e054500d4421410b940d03402d90313090002e280004503140c0c13940840e025104070f2040001d08069129102c440c4c0c1004424015200001c060507011248544250400120f00902400008134221252030b10440c04504140c02c2e213000d07800060070003690400c070310486500d0a502c40801170302421a581c1310036090220380c3c0f0350f041100203c04030b0700759501d04003070383d0030010a00d200b00b018110162010f80f0b6904218080b0384920701d80800601990408001c03218440510744d800ca070403124100c0156020400c1044030080b10f00c15598243d0700c0b03c3c56603803460185134407025025018 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 647882976 1250 647881726 647881753
    0x81510150315121110170103140c011d100e0414100b0703020703170c030301081b01051801110708011113060e090414010912030c0e040e150406020c030c 67
    0x208540c4801e0102000345400740c040f400303540303401405110403201003110005d070340422145801e10000c841c4641000c940000100031840d002e20414807901d1040e10004500400151580210b54200140000c0c3e654010515071030a011801c02264441c241425000803030750200b000c45600c01880350308090003101307108001d81c03004110402410684105c0340703049031a5800035214401440700030700e03012158841000052400050b80c2e0072450b624102d0303481c2e60350350483c01e50b82c001442c45080d0030b500482e0b030505594402c0003100c20807803c00040102c51246400111440103003c0d203454118041c0080100f2480006e0140da100500c03c0e10040d0b403141500ca444840801c001e0b44650181305025205001c90740301e090a681d8041e40000e00f40708042c03c01c0142c14050f2054200080c2007900e0310022020403601640410407024a41d030b00c10341e100460380c09000483d200364200301e102da4060a801e204c00c44005031282c0c0c0c400d214550160030598002a2549190040041a80d058020aa01640d103 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 647884226 1250 647882976 647883011
    0x60203040206251a070504030b0606041502060412033b0607020106060e0d21030219080118050402010e0f0604350c0906010c0609020306070503060a050603010815101503 74
    0x301c44d000248145404d11540c0078029200d90f20000703040340c005100058891392003609039801001e440c802076052018000c0c00948604003180c003150410903510414003894800d00c100e0f403800c9020306c3c0542103000604000c2a030340d54014690301c0030541500b006200c090003800a6409120150000b149290904101602800c0c0c081c2044e40075002c28069a0041180304615000024040d04540111001150210041d04c0740c48061034800c0c601c03481c8150316a50106500f0f048440602856401c8004441c40b0b400780e500a03103010b40000c1541c0d000c108a4078001c1e15103148058024074003894980c4c0c5985804000c0b00c60400c45440104d0300d1882c0c0d580024902101001140c0310000d0104045060002165114040d14080c100441441d50000b00440d0f50f100488081d0000e0491b0814684000e000b885940104e4406004035420174001900c0d00b0610141c9050301c03906401b40c0345161554030010b04050340100f41089001144c040080c02c5494105280c5142e0819900400c00c80085454500c1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 647885476 1250 647884226 647884253
    0xe01030b031009050708070806060a06030e07361b02061b0703050f191e02120c01090f06020c070510050a03110c1b10021906020304020625 61
    0x51504089428985039008902e12010701d12680e40021446464101a4a009260b03002040d45114440e40810503a90002c2c501e8070a00d000c0705c00b8608251a12800c8003079644034a05c501d81d5a200d180188001d418a41c0d4130400e040803c0c1e200106419240d403d122042c0041c0310a0051342e80e0750720b003c24074070420390034222080020300003020030b802c10410b0820103c1c002e4290800d5150b0203e09081054814000c560101c40010346942e1506144680e03414120011503a80c00814040300781c0ca00180750705130804940b84655000b40010204110101642e030f8000f49a240d010b55a0355042c0300041c3c5c50585040c00c882c0610f070010b84806030b201d8024075085d42d82d0040c42c82940701403150010943d0120407188041214a0040b0b00948403030743c0c0d07203032034025000c00391414002d50158a0324054031041d2501108800c403180500c08403141c00076600c401c0c9141c80c01c010b4201e02d1107100d0118540390015038101e8806440f0619000549030340900c00d0700800e11459500b6001400107050081200c04c080 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 647886726 1250 647885476 647885479
    0x1d0106030212010b0708070b0126070b040e0c0706020423030a1509110a081f0209060702100903060f0e0f070e07030b0a0e0c041a03040507060c051f0c0e 67
    0x145044400440142455414403900401c007800217401c0c81007080e440141d41a6940c030002c1070086503102c44224111000c0101700075000c280703000102aa004000900404552070294943d00e4142030160340c410010001345050001d0b00d08100e9100001c9452005200518131401005401000441280481a07030818000d01c280e01c400611400324002c0510b160300411415000192240c251400800491000e0a03180d805101c0041c0000e00303080114004135095040e000f00c20343c24400b41c400700101e01507550001d410040a100705030050602c42c00c81c5000500710b08000d98007540c0d80c0d072041d0585031101030401032180c89203016001100300700b040c92135102d002d50207040c5081c02c2242005440c900203183d20109601d91104c41100d80f200710709000900a20021a0310620389549600115031041c4038a02d455160380d4100747e101e501038010389002e29440400390003842e00e00f41088032040c01841d01903580340610741b24406805440003c04d149201020000701d01503c0101c009040e42d007100100c0e5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 647887976 1250 647886726 647886731
    0x7060209210c0d230106080d0c0f0b04081e090406080a0302060a0f02043f150c030f020a110706090b04090c1e05030123060315191d010603 61
    0x19520702000b0840c400006001d8602c03c907110840d050045491580300c0b8000d0440a031039041031607016064020780c3c1030f2103242007290150220742400b25980010340502400300056a801d00000854054501750005c1c0100d03100c50500c85c1c000400c44100030306407101000c414000540c0c51490400d4081c440c0106401005030401c450b1548002e921144c0003003919818507920240406003403c940d050350090900520b0002c41e0441c4a55488490300115045030050160302070500351501c07800d0079140c8210790220100340801c010303c41803005080040070140c1459200c154400c034401c000d02c0a0074074941680e403404a104c56000130181042c3c0705410103410410990028402042e10754111021150154030000d619000034100315004880710030010510380c45903140315107007603001000c0c50596134144100e080400c00f40504d4803034800d003400c0740d50b0080f0782403001811003204c8184003000404003800c003201044040e2850300700481075401400f00550014903d8480c0f04903904002c0c098401803c08 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 647889226 1250 647887976 647888029
    0x907090603050d0e0a090c120501300821070f0815060d0b03060103030503010806060f2112030a090b0c16080a0e1504170a02010806010e0102030f07060209 68
    0x240380e10b40c00800c03c0d602c1070000000c51400f035601c03000b64120051030810070400c620080c10000908610110001d40b010310b0a0100103c0c81581c41c0c24650090b40d45603000362003640362610345950000b400281070f182d07081d041c020241c0801c01313030b54200d00c018039541d2004010f18000502610841c1d1808400b410803180c0000c1143d00e001d82500d0200c088402c0720348503150444404d80d040034001001c1c0c200d8141c0540400002017540010107141038400041c00e580c00c50740da18041c4034070b20b15400a45944990200086d46401c0e1804461556407805e20040d64000828a4103940e880e40c0140d40b500d240760354803090003092001c8200080d41101c5030207a030301d203051740c0e218000b85000f81240001d8080c405c000390641c0641e00030201880c0c0c0c044040d064084002950a460351940c21500c9129500e020180071840c0b14500401c11416055050319890000c0d1540001104d08031500001c01e0706511003003110b505111802d5000d842220f2142e000565268420420703c0380b800c4030909008030b00001d0088 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 647890476 1250 647889226 647889233
    0x1f1a041805220c08120304030906020c010206060f190303050306010e030601050906091e0c04061205190e01060306050a06060314010e190902130c142514030a080907090603 75
    0x10403050280c01c821000c00b240380c01c11000c0c2000310390000c0558031582c0d0a070b82c40140c0103c0039500c580c0c065111880d041d80e5a5a050303890308460030070680140c1080c0c1c005031a9140922000740300400150626150413000c0c10740301c0d00c1680d9a002a008a40e0100c00c0000031b6901900c5404072400c04d8018020951400e004100700b2a40a4000c80c030442d60341c40000e500f01e502c440310030030308030540004d5401801d00860341c030f045500c24025000000d4024801d00f00c46a00c50080c05d0140f8034842e004440081e01c2a0001e0040292908900040d500e400000020458030300555000b1508450b001031039074501103015080b100882c129503403401c100e500404c4105003446500750702103500c482360041c01c210901c0c0701008012009c402544004042c03002d4400b1810f545c8070982c000300300d4072080c1c80c0208103d40c0c440300740541140b08002c0034800c042031070b02c020201c036401d1b00c0700d214680c0b0382e14a84680140a040d50401c00402c00054401e20412107503440802c8850001d00c06180300f08041d904544 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 647891726 1250 647890476 647890501
    0x1050414010e061c080a020721020d020a15111504050607122703020106050103020f0d1e0603050a0506060d0b04020d020f03030a05090a09141f1a041805 67
    0x10031248546041c80004500c2e131a5441012072111000104000d00615890400300c01c2d0400e0340c0c4140148690031011a080c6c0d000c0c0728120000c4000c201c0e01500420b15801c00c90001000002203800c03c040383c0002034948641c0c0c20300055002c0030384a0001141000d00070358078080f81d121070104101803510501c004180003084030703074004905107040c4e00914800f02405c0701034a910403048a0300d2030220340003002d891482c079404040070300c03070340c002d101142e9100011000e81c05400e04505007039804024403030160300c2e41d030b03c00b0ba0b25800821188102d256103031540c3c0c04070f41c4503034010340d1560090495081040014801c8941c4500200c80b9280c80c3c00c0c698484103015880207100078060030245d24a8019540e8035180b00c0c400190003400c0b40d98413200480300030030f190082c3da4454011544110081010110781c05650105545a5040c600b80e0307980462104000d8101609910200c600700320116030320ba1292100c030340105007041d041e42d4070b80c50908541c0d65540355207001600309180ca01480241c000e0030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 647892976 1250 647891726 647891729
    0xc02010f140f180705150304020405100b030601050703020708061503160f0b0a05070f05010f0b060f030a050c07050a0818060715050a0b0a12170a14070f02040c0201060e0105041401 79
    0x140032003c000c00d503640c485450306160790011540013a00c81c00c054446180e0703800641c4604d1094805210584803440041d11a1034a8018001c90f0074060002401d503510500107480c0d01406481158061030390303a80320314100350b0142e4102101100084000340c882c00d0411840b0200714a080005079080d180000d0010b00700d8080c001c5103030413800081c07e00d128038860400d64102c1030b000b1400040d107c8440c0b425500030030a00c22030111032802c05a4000980c034240094409920240b0146459951003640000003807030028044021200705011305008a0300c2040102c80d07551049105543d144400c882c1e0045030f00200b0b040c1441000d040001d1000240c0d80090445000c8400a0200b201d440304564140586030071040d82e908032251346800070f685c0e180248d8280040f401840c5104103500010303c104054480c00c003a00c4003040e8804442d580da4016400100342450089600c40100222940050107656260000c207006139140c90307080c001d000e48040d1160040400f06c40070400502c4640500080c403005 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 647894226 1250 647892976 647892991
    0x70f02060a09111818070b070b0a090b0133120b040b060c0c0a090203090d2304060e040f0b1c0c0b120106030e01020721030e010c02010f140f 62
    0x1103151042c20002d01c404035103041e0100130144403a045031002ca40d1000712045981c071100407000c12078444110b40c0400d031001560f07003115440d03142108075200c21120200280c0203014079503950b0312840c00324094503502406040010754000d000004541e400e41d0001d90100b1144010441c001400035480d0090140040300001d408003080150080c4000340c002cec520454003d4000e400010400001c0001161004203420200caa41502ca61215509404ca00046403407040c02d5000c4540444024000c070912080d0102c1d1820710f110305000900c110000d0f8015078828404550841031101052603d40104440e01a09900411258416800164000c818402540101e5a0003442c81d810f20154200340c2024000c1002019030741c98101940b014014002d1103941c00292401d1003980c882141802110807154112524201e42d441c0c11090408070b070150b40d007003807d0590340c0c100021a45000c1c00b54172034400b034039000041c40c400487c0b080010380d00e40a2800d005901c51f4020007010745081030541d90020074 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 647895476 1250 647894226 647894231
    0x30709050f0a0e090f010f021e0a140c010605030a08030403020c01081b0c0a05010603030f080c070f0327080d0210091203021b0601090c1e020604121205040c030209070f02060a 77
    0x22071213800c0e400d00c1c0030f82140c082c0310750802e00d42003414205900200030040d415040d6800e0040c07203a14050041c084c504030b40300010b0326160110504582007011300703140000280001000d036501e20002e854900c50032001c0755070180200410050540520480014580a080107146880c0401354040d80444481e00724000841c0070501c540c21510030172851b100545e014000300701864072810060040360441a016002400500c00160340c14200c9083d1403a1581c040ba00c01c040300004c1da0141e9449440c1e90380d00c800c41c21065a01078031592031b0130002d0300600c825030140c00790940340c5c00e0081c14002003114540140d401c14003554009500c451464000d448980740050700c0721080030001c13540c0802406519018401d50700042203801040d805038400c0b141c2500c6003452581c00b40c000d410107500003405e507805a0051800a0045299035070156002c80d540d207880d100d5001d500da401411660180c3d416903481004980510840c10035115040d00000c5900700758910440c0580000c0d503c020040c50a00100e4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 647896726 1250 647895476 647895481
    0x1d01080a170a03060305100504172113020402072001020c06040e0903040b03011502011b080a0b0f060c010603050c0301180809180a0e0c101b08120408030709050f0a0e 73
    0x43c880e50119018560041c10380d4000450303014180c0c054a002c0e502030729002c00ca0145c184070042040112120400f50b02c600c01900b03a01e20904034855640180002c6103a01010407100050b078440c801030050780d205808003180031101066109101a1202241e41950310a20b103510351651000141e030100d807500349a00b003a41ea00c96600303d0a42c02103a0040c1c8a01d40007100104060040081241142260364000c204c0e00440c2808603200841002c00903010903042004030701010f105400140c1103050103081c0d5040b403050360b40424016400341c0c490054595495000380b04002c010b01c01c204000034128001d128140c0071811501280c09881ca0003044d40b80c000030025060740f5a140910030750300020f03d81208602e0b120641001400038081260994040d504200802d840c2c03541c4284040491503544a50211200301004440810341e4420f072440e0000b8844042c1c00c0c50200c246601c981d2046000e10b880f03042410029201e80a1500403d01c500c2d8801403903402620317403903a4039007141c0703031a01e0900c0140c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 647897976 1250 647896726 647896747
    0x9050a020403022d0904030906180510090807091103010e07030e1b0910030506010b131809031403090d03050408130b190206010b0d02221d01080a17 65
    0x2031103140c0c0000c2d000041150121466140c034100d10122103107910b10304c2110103102d0100320300d521007101c0c000d000c5280c0a0040c0002c1e84260f038046154403050341c40c000116142d900140d101000d01034502d0010380e840d4011310880d203041c0700c880014801c8000900180d0f5070040321801d91302050007140010300400c00059a407504c80e4000c105402c030320340240c40500b000b02c0341c003e0090000e0400c0e14014000342c0c01244000040b68440c4e011682c11070050031003139080601046240d402001d4084008503040c2000c80c95801d00c4c1d503000c81c61440010300250300c0101c4c5c070380500642c4c84400f00380250340040c01004801840401d01d420300000e68a000a1030346d40b00c5c600075000c0d01840c228503010300140780300030890380c110000911035460010612200303100380d030404a9407030b07200b40216054040300340000c0c001070200d07401808500d01c2c010300480540341e0b07120400751600240d1f8002000d05110601010780007402200d040c4c00340c40c044000d4020410203450359040e440c1d00d8403206800c500700007442c6102 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 647899226 1250 647897976 647897981
    0x3051017070b13060305070e10140c03040803030619140607170a02010e12160b040311060709240203090108040602210405010f0b0109180216031106100f09050a 70
    0x1c1e181c0c140300700e070311010f20725280701007681140a0840801d15200c0468000341c0142c0141c00700000081582c482e554451380c08441212100b01e101c41011420b0003861030045090001c1d0016045003070055849140500810203140b900c564065000005008103004540c4640c41d860b030900e03800d40300559112854a0800200302000204a154100100d90358048a030706401581003501c0c0402100c422484601207d40780c3e11400c100c080200c2030b4010311314000342034884080d038000d0080c20f05202000c0041c000038202541100d00340d00117820404d042c80100c040d040e9100705407400705202c03851308c0003808000c3c3d42c4e8401c040540c0d062200c180000b900b004150b07012a100816040c3c1d042d100c92410403c50968039a081c0c0701120594284000320030421043d200d0801340c004140d48030b142481c40c10349104082001e09c40c148031129020041560130035521480c8541c9180309a5548948020316020300f800d0200c00f402c003450041701c200041007652031000b002d605403402c21070002910f8030b41d03c3d01c0900 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 647900476 1250 647899226 647899229
    0x5160b09030d140a050f01080a060f02250302060106020d09260d0216090b06040b07062007030314010503030d0c02010212070c051209090408030402040b030a0602190305101707 77
    0x28254205008600c2d07500e07510f0b1419000d940890814402c1c1e88400c40269006042406180c0d419403080c40302c1c40c080742890b040b03404201000c00c001841d041e6103c2450707640050700103140740c290100c84400c10170103030304115050041525102070b10a890400c5030080103941c15208142a0600c080c050401c8a0301120091b0205c10804040305c06845800c00069124080c0303c0102220100700080010b03074100c0e0b07018141d12614001c00075440c190030503484800170f81042d0410745881c1e98a0040030010144040c9000f004030b4040121034540c0f80c2c1d4076005090b41c1c589400341caa4180f22400400042d200041500d42c0765115000104080310001e80407402405030400c01c400d403880c000144034819030080f950150890007074040e210841841070001520384240c1c080990440710307035000140895090009190003e1000b000418441c0412001034600f010844c0251088d6500162415600501142e051081e1800e07040c24000ba25204030301d403010048500c03850420341c499810300b4029210030f01c4400c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 647901726 1250 647900476 647900497
    0x60e01171e19031d0a05060304030804230109060507030b10050a1809020405012a021306080607020d0e010306030308060d081204030c021c11150d020a0503040b0705160b0903 76
    0x65481c007060800800c035848070001c0d004500c51907130500c805401c002c481682500c60207080246144c84554007103d1401c0000c0080d144402880300d8003c8404040c444a100c8204810000c144020142001d8040300d01c003a0409052500e0401d03031403010340740e260850110b2811400c040342c5400c200c410a45005513100c40c0c03005c40e8024010081000341c0030b03502400c15100e00380d0350303d4100085901031800d0080c0d4030a44800c00303910640040d0061510659844c0c002c04140004680c2c03640d6000b119280c04016105100941c020105a52480d03900c4030455494120034030303060025a04d9900c02034648032003e01040e0180140a8070380060002e00001c9440406075803910105c140707030a040c02070201003011801c030710a20609d0389010703400c020709030240440b90700658016540703580d00c01000050b400c1440204803103003044c00410000e90310743c405400c3c0c1500384d442d0140e99103014540381e0303082a4020009801e0003000d001f1800c002144a0310007681d10352100048145484c3c0b4002e162a500601280e00c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 647902976 1250 647901726 647901763
    0x904150c02030c100e06011512020d06120b0f0906130602090d0209040b0f09010614040e01090c17120a0212181c0b090c010e0409020a050a09060e01171e 67
    0x10410600c3c1350380041403403507088091700d02a9803280d0445070562030030390185000908032400d814404071254010840540c2c102000070781541d40d0044001c0c0304400301d409072007400c1d0361020054031034200140c00f588105107102800662a026600c9a0f403808040c0700505025804204503003503849940d5016007094004080410314600740c030300003180740030403134841000c9800c80e4042414050140104020f586e001d07612000110410001c1c0301c010181010510070179901d9105000200c0c9074160002e01902c000b4103907410141481000920740134440c1861070505c501004400c2d80594040340e840c4d40041d01180d01075582e83e480400c403c4d940305074038030070350320518981001090a09442d0200401d80c45590800ca040d910407841d540c990100007c0a4049000884064058546a8017100245200800003031820f9220030200f90380604507041604801e5440c2c40a02a600d4106011401006014a007105035420015003644501994035061f800c40500741c0441c2c160740c5c0c140b01c1c11460855003500c1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 647904226 1250 647902976 647902993
    0x70c031101060312111c0c1b08010c110303090316051f02031005040b090106110106080f07030c080a080720060d060504051509041407080d0305010609050904150c02030c 74
    0x4100840b640e4240b000b1800e11640204440e6000c6540307000e403c60f240345090700300801d9106481f02c3d412250200c0d441600b840d50f1a1010300208642c0300075102440000501e0503103010702031710010010b5404591a801803040241e225800400c0310080380071403180041b0342c50b85242181c6440c580844840004a5410042450441036800741d4800e03000d5a540c03a001c40d42d40d8003804100c3d0b02100400c1d401840b10f070018050f1600400f544a42030108000020743c4541c1d40c031840b814281078009150729608107a5041050101500c510800f03044041c000d40001009681c91100510a8060013803803a6603d1b600310a0000e07140d450f00d4001c44018162564590700c1d1440040105612300440d44100e180c03401060b2030505281034403008900181c9041d2a80e1105d4403051303000c0e60b102003002441c0c40349038408190540c051207181702c0c429103031302c010502d0350400d500988440600c1e0401030203030703030b0200c01c10000c54403204001201e810203a00015290042c104200d0071441110000d9030305102e49040c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 647905476 1250 647904226 647904233
    0x5040e0307020a1203030b06090f0405180a0804030c0e2406090603071205073917030106030501150e0906031e0a0c081b09100305070e06101403070c0311010603 70
    0x451841d0364442c0d1b80420140a9900410400e40105401c040d0415815080d4018901b055881681c2000d0050b20030703040e41314141c502514100c01c44074115041800410104100308011684401911002240848500e4509450608400b10f45000390001100301101445d80d102e80d0102d0b07481150182c49141e0740e181c00e1401602d0345040b1a0744415031442e100004107600c3c820004440c91508096149003602a101c078444494000d80c4810030a0894920440000600700805107003190001d030409502ca40c9031900c00740840d00164407014900c5d0409902c02c0c3d15a40c0300c48042014541240d00543c29183c00c0046881c0a5260384000d2031940041e1060b00702c0302c40000d0400c03003984980ca10301e01d03035074503110341a8803140910b200803a0700c10300ea044e142032403422555075035100e454203650701c11032540ca880311031030800203034000c0e018214400140501c03404d207041110a4510a41011010036000c0c0440400c1c511004094008125041800d4820140b05040d0307140030300400d0000340f00c11a202e04 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 647906726 1250 647905476 647905499
    0xd0c030314160e0d080a030b0a080a03030915051504050a021c06140109050f040509030d05040303230412080604240608070801030b0411060d05070201060611120405040e0307020a 78
    0x40c4600085074034020070300c0c0e8a203001e20613a00d000e9403090041c2c1c1405140310b803d80141c800c40004c258000c0c9203400c00300b240301040024802d900c0c001c0d580031410140078100b0680781043c0000d89d11400d42080700300144a4141c4c0883d031501101500c1c0002c46685900e5814000e004100c10550000002410454500d445800080594515008581d403201a0400640741d9003090321a064002a00b201d80011a10340369020642c0900c103c400e032450300301007101d02807c0b20802c6800301d0100342c0c0c4101038030003180c000c3c000c0340c00291640c0351302d12541891745907508207403503001c0c0c40010841044c1c002401e81d11107421581180390030045043c10a140000d508108a070325000c0c0c0310010f64420000303402c081c403940400d4101c0e5040301000707005450705d4550410b00c85017000c0040e04000c04000d071000501c01480303914442e5001d5800019000c0c01e20384010510305081480401c181e100c103101918030468001200c003140c0c0c046400103051420540d102d41940102c1a0203907110000c0c01d00050741201c0c1d00d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 647907976 1250 647906726 647906761
    0xa050a020406060906021c020a050307031d060f0702131104030b0f0c0304021e061e0c060603011b1805041e050903130e060a210b180d0c030314 63
    0x301c1d0140300c0310351118000c480561040c4100d0700164440e040410350200201d036000c0c20b0550724816140903040b00d850700c501d140d00c110f4089000421010401d54600070061118242e184221038041c036000c0c1b04086042207000740344002c1d106443c150081c1081d6200d56000d035816102e03441c1442d4440e5502d003001401c081c000c170340703d600400c1840b00240c02074200108403841154003c201031003100c07568444215400d01e562005400103410085200ca100c6071440c6904015070b14106285c1d240c2c601c0d44141d05145c006003041d030181c2c0c10300c103109816256a44120000c49464a480a560400d0250122501c06070f41c0c07205400501d0001c0102e1081c06100d03920301c40700c42c00041405107443e80b01c2095031700c5c42130304441c01c0e0072820b104051004150054000760070003c010b104504164444035046484044010000762a0008040000410070b00302c10307440d4480032040d109034041c0300071b036202c0c2d4075083c0600d000401c1000002d48001050300a070700c65424950250810b40c0340303103081d407070500c0d690aa4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 647909226 1250 647907976 647907979
    0xc080f0606150f030901020d060909020102100b060d020c010617070509070c0803041e022101060b0c07030b0711030a0201060528060e1201090b040b100f030b0a06080a050a02 76
    0x18500000e86505000e00340c600e10b0803040064070f1030165807030300d111880d802c041c041081554082140e401951040d02440340600440000096140303c2403001900c0d080700d0b000b060f88050b0416191262580c0c42c1800c1d0b804034020b00d940540d039990881444c0740141002c0d04540f030140300c8031925035414034000410b101035071800d40d14550302d5210410309a401c0c1848003001000c850b410000603000401403000e2081c1848404810008000c4550000f41d400206d0045545031400c207000c07126041d00c0034010700740140200e9001074542200fa40004da214042e60101034105a084404194050b128007400d03282008c0c0f48041d40d4440540050003406002c8512034507108290b1211400001164107560141d103c2d00718000e0100780d442c018060741c0c1c5009207524194401c440c1c11000705610428018121130510030350740ba200a240c246042241150080c0145c90304001c030740d100f4004010000e214006076908400015050750b01e148248019100c2600907801078010408040100040054414a554070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 647910476 1250 647909226 647909233
    0xe0f0115230904140c0a0c0609150f1802130e0c130b010e040b0f0f1f0305180705010804030806041820030c180c07140304060f0201050c040504050907030c080f 70
    0x340700011071608482690807982c00745d0100607401000d8020003003060b4842c40740f003003c1034041c035076100c1c1d1031408050300906a5960310f80b050483e50646501c20403050b001c00e0f1005065220030f640105030706000b40c401000e40c01d03940c3c51400c607800c0400c00901c0d2a50100510040180901d040800007074258030000300d02190309111240c0d41c03807030b250280e40c22240c0058014003044a40400300a01d4001300c00b07080d90805c07020381c1401a44d411802700b248074060103460118480c10250b03e41134454030104043c50168200380810b02050386d001441c4c54100e509850040442c1d01d48000180c0184001c40f000b005982040d00c498042080303150b911a0700c213650450402c64013009100345070719070608201c041d6010008040840c44c10042d940550b40121f0000f1001382070560300c4d03689030454010b080f000c0581341d20104c0d00b0800b1940c0200400e000c0c01c05c0d48020300c40ca0900d0042c101d100d010b1401024411501c1d000002c07002002085848025900f19980c034622559400e42140c0b00d10200b0706500c0c6502 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 647911726 1250 647910476 647910491
    0x120a080601051602040b0409060c05090f03070317030a2408010c081501030c020f07032301022a0a15051008060103050607110f06150405010e0f0115230904 68
    0x42c0208151080304081030b401c0c610321411039007040004c00146841540c07082d60340c01e40001062a5105608200d500c5455150307945170b54000704a134035140c1d0491035229502507402440000c9801482e050700c00a50349615413a80c0310341981d58041c3c506c64020f605543c242c000c3c0c10002c0350030000c1040031035140c00001c200038450302204071a40308040310b08010f00300c05402180410b52003503101320b00380b4510384191000c00f0700444616050803904d0f0301c10b48203505012544201b40e02a03e8000b5035903201e94000b145000000d08509202d4451800d5141e1440d0304483da01541c924240405005964000500070040f0a00807003100100f600351034500d106012402e0100b4810400101035050b00e40100042006a86074007007280c00b000c11580c400f9103801448008229810704100341070103170300030300c3c004048002c841c014003044441c140d02130103642100d001480428002030601a040d210100007109158460380c0b026583c100044440c441841d04005014400d0040c1601501499004841c18403048 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 647912976 1250 647911726 647911729
    0x110d080a0f03180f02121e060a0b0d03320304060f050a020f181c11091023030f0f0f12030105010f05071104020c1c0201180f060e120a0806 61
    0x3036101c1c0400403c84d003140c0d0340700030161402500e100d086143d24803c5403144040d400b640140818030501c00c6450303a0154040c40310316000d901030843c400f0390540380540b8407280350310001c0c400e40c1040f01032000d21403da03034000011040520308020219a24241d90303541e0825141500050441c8010407103e83c5c508008680c8800c014001c0710303942c40b95101c680c1c1c1044c1510b24040d8000080b1400941d001d040c50841c108580c0c185022040814003944281c5074001c07900041c0224007a008010b0b4000c400140f00c18020b4140c5403a00034541c1c039100c0010004c40c4442d0001ca40b500800400020440c41403548180344500000b907000500b8104d1f505031184010342e2a03021200380402c2c09214081030071054a944014460f40203050010b02800f0344001300219500420704a034414041501590005805004c21400206408203c010284000c00018900404e42a15600c005100030550341c1441070410034410307242c104450000c80d400c25140c0c105500c0d507200c000c80c2d0062219a000c200050001000c2c0d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 647914226 1250 647912976 647913011
    0x40f02040e0a2a1a041a180f0a1203170108240f060d0c0302041109040506090105010e0d15050702030a08011e0306090501140f100b070f110d080a0f03 66
    0xb00400026406190fa0500c03441401046070300103804441d6505010015103a20072000750701c02031000380001c998500c0600100544a0f4010070070794042c044481c160ba60507201c00081000f02c0c2e100300d43c0e0000d485a41e2408030b9a20240c141c0c505c040d203444000100d140c01010820358040006810300c83d02c5d02c00f0303001c9001c12101c1c04840199071200d444001582e1030506001c2c14403402e100d059641d15498580d80050304650819000c2103000b02c000c110810f0a040501c80c00c1d400c02070441d10f1246642c9070000003008800503000840c02181d5142444e002c110132100ca442e10b02000d404140003038a00041c1c025642d822076840c4a00044000c0000955290656100260754000a106c42c100b5070958545038050501280c080f2075565881c0f43c03c515480300b16106601401088400550034103041010b800fa1031406d803c200154141001050000307450402030030b40c415444820001c2d041070890008a55003103104d800b6002400000b0450505075210126100046258808000380100d1081b143c0e80c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 647915476 1250 647914226 647914283
    0x6050906240d12260708060103021602040b010c05010f02070201020118170a11060702070810020a020307020409020315010b09040c0c0b0402150f040f090606030209010c0605040f02040e0a 82
    0x8110b81940022004209419814150315142e814014802e24101020100c04d08160150345501105a000d002c0c03420785c4050140d4114400b46802d50420001c4106c5c0d81c002009a54000d12860791000c0300c00c0c1d2640070b03603200c0641c540c000000302b0850b07440c000414082c0d841000c0881c015440c2890141d40079803404840d41030550000c0c00007459840f000b007404040e6000c5182401804000d945041410f4010803031644180801e601611300c0714940521586055409081070203410300502c4500c1000b60f001094405468044401143c801041d002190034503030100e0324502e8003080d240010441c1241b20004040541003a10304000700c402c0c0031780898441e41c1d0780300c0003807450320304201040140c40c0451422030a802d000200503c1c000c0c0d01c00c0d80d5061a84164006480c1c0003480c0e1041003003220b03c1c45020004c0c5075904065140103540c20008004204103075004010384e941da004039003030000c480503000407140d015200304504551000410f90f10610140e00b203600c454240c2c5249400075014510f02d1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 647916726 1250 647915476 647915479
    0xb060a030c031401090c080115060201020a0e0103020f040305010507270317031e090d021612080a0c120302192309031510030b13030e01050a05070605090624 69
    0x1d2102e007503948441420401d0301c03107402c481d0340343c507843c0c808102e54207941c400402c03014000003100303c40042c500d002500700703904c0711096910510804524070b40205111941010911f00182d5411045400034194001ca41000d4002d43ca040100000c20b600900c840344c4c030040303d54200101c0c000400001001e1121400005c011030008642281c8401c0210055500100200320040c040b0110ba018503d0820040b070301e201042e40512148010349130144000346902107001241c00d0050300f0151242c05d009042c400003405184005141e0b580d05200b10060807510b03038010f071084d40403000100020043d40051701400040007014041d6280d99000d100050340840100704100d0340c41c01100c140a403e07801c00048a5094042d02844201d4066990003140c46880a01200000c4504605240d00d5a030002818254103002400c14180861740004403011802d1013407801c40c1e0f451402c0f803002c03a1180604000244a030b42014240800d9070408030301140318a107103100c0240d4501d18501c40a544050f040f0616 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 647917976 1250 647916726 647916743
    0x50f0a020f040603110d090503040626070e03210a110c03060a0b150d090311060403020703060c0e0910080c01090b09060d06170c03330603010f0e03070b060a03 70
    0x704180ba020390021518249401d0f0f509007048000803880054039001482108c041e00005002d100484e0050145100341c442c941303441d60100101c0d4180074804078054a058244502d00444404036a030401001b4107130b800c400200d2442541c0302100f6011508010485004604132403111002c40c00300299803000d4330300003402007005407601c0200e440100000d880c4560082d10b01d14001900341300d003000500c442c0884c4180003030528031500340140002e20b1034517000f4058000074280408030354001482e1040d81d800030b000062188102400f034404040c4c841b09030390890b011801300420b40b1180c1031a42c08403102a4290307030028440d480119036105060042c03040b08402885000c9407420421702401c659400b50070009902d648804240000020030178440306079034045034040c0e0941c2800e000301e0402003084440e00804a4072512210302c00010080c090718001032646c00500190307401d40007083c04019843d0704102881e44003442c030303882e42d1000c1c0080d20180e01ca400414401c1c1040030043c001c0b01c4c1c104d03809 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 647919226 1250 647917976 647917979
    0x6071a06040c02100906110a090519060504151b030f11010507090306110904050f01090c020c010807030f060b030903041a030c16063b01090b01051009080709050f0a020f04 75
    0xc08009141648094a05030307a200c550948100403d0f0007048c4488464444030001c916003001c120380348403101f603900044510a03100b00802c0fa0001c0c192010b849034489103203902c4440b5802104c0c8000d500c00060400f01074102680c0900da00015440f011340d509276182c40071200811041400d84809540300400a500c40a0170400304c0d02c15070100c08064142c20256107042450b40006050b01c034180e440d80070b0501c0010041081451b0781c4140c0202081a0019080181c1e01500180ca074034001080c2d0400c0c161500340c108160222584584050800030798000c4d01ea04140841d203580e40c100340125403c2201030303103a0700200b004200aa038030642480d5603081c5800e41e5000004000003590104481e840e480d64510001c43d203d06468141c3d200300d011013154044007200d02204038203028555019164904140d003c040b032010486a419503400383c50340e1000c103490744c0084600741129808881140200280403c08400301c0e08558080c610418a41401d030712a550761030200c0c0300b01412010b40b510100300 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 647920476 1250 647919226 647919253
    0xb0307080c0f0102030c06010608240612060613080f070509040b06010c0305041703071101180e13020405090d090b1c050c0f0a0207260c040b040b06071a06040c02 71
    0x1003001c02c0355040c41601e081000c04850145040d41c203801c840081510403041201400707451040030b4004030340c09201c601125031400801c2036841010801c20b00040243d00041d6191200002c40b0702aa0120800200c115a6507042a071100d844030b040034040d0140000002c0d452030480300250046402ca400c4681c107445104c01510100302d171800031001d0140038480080c0c500b0b9030480482c14812003070042d5a4a003105d14107045d49401c030b214407070305000d19a80e5028421210103003034004d07030301000c80340c0c0910346510300444500d2550300002507120b401e02041215240021401c219980d115494030019640c44150260090041e412146a039150340c80001c80d40d43c3c0c0c039820144d0071200d684046884d2800c030704500910b076481018128090b9129140400c02caa0500341c01d40601030954400d0002d02c080d1100054a0701c0080c06c0c024030844d12400209070325079669018001030700340280080d41d01c020304e00e00740c681c41e42002c5d020103105030344c00000f4015051500400800184560140400c2240503c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 647921726 1250 647920476 647920489
    0xa091a0d0501090b090a030207060536030d0302040f0503010e060705130506040308070512040518040512040e0106020c010e060a211109030c0d050a0f0305160b04060b0307080c 77
    0x10040c0d40564864000801180d0341c55a01d5000f8100b000142561800702d0401030320307000c0d451740040100a02043380c5800303000780901c0000110700d4000d55005110540c0c1c8041042002040c01903850f00a10809299a60b0194010412551440e401c074642c5c1780d030380c02018204d508240d26030440b130304644c0c0003688591007440103160240400c101d0f01086078852002c145540c1080d003040b40d040d400005c40b002445010405800c00524800040e4a0030303042101003015134501d00102d8001003117800120301007000c14082084030754200d81103161560355071755010203501c50030322644000d40a8205c540c08a54883c030108003907104040c221030b16110f180d110484076801c489481c0c594031541d8071010300410b01d050003644014072a40f1929520b5003820003c040c102440e03110039900c5403010203001c6000030700c0802c641039096007001d89506131681a00b001e680c14880ca000d681d281251504125003005070940c5e045003e28012503040001216040505a807140c0d00d02070140d0551145007650021314180 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 647922976 1250 647921726 647921749
    0x60b040314100501061d121c0509032d030f1606140906060a0e0f0c0f0c0106030b07031802150a121406030c011e080403031e09020a091a 60
    0x90300302c0708400041c81c0d840c03007142c4083e0000303000501c1441071a0520b0050f5211480d100717038101c0760243c1400702013a001da52050070640154402008403ca10310881c001c8060351030120000d02558442000460003414200c8102415116032014001a449010300003082d070f91010b002002d86031400c040010030007441e8041101c2150003e03100c084200030041e0030880e40f030203207400500400503800e0a10400c20203542a802142c407100d4400104600382035000e80c2c1c42d4110082b100b10039038070080c462483d1458403d000084483d5070900c1400000c1100c240e120a00c200e44d141d03400c000c9c62540390941a0342900440010b5800f4114000c15600c00f00f15600908000402c4d08114019581c08801c1006032607508000f420882d000307a04205a600b420f02c0f0904400a003407808403841c1e4442000c12000300e0f00c5200c80c03010001c01c80005420140250f100ca5104903811187c4007840303040810781c002410520f0401c83c082d104e4148001050f12440c01000c051301e03214000c034642401c4610500c0b0100c42172 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 647924226 1250 647922976 647923013
    0x203040b0d15050402120a0c020f15060312130801150506070b07090515070203060f040305030411011709061f1404020708130b03091204150f0c080a0c15060b0403 71
    0x400b0004199407148002d04442c582103070034900b0740c81d00d040e81d141150b400601c00429908801c034a0a01c0710400300350401c5018890000611688a00000c2854400140c880c000c0561001603440c09482806502408440143c0b0090040210840d210312001da501d2180c0c079000742d004d0001e2030001d203040180307590103192807402180c0380350b0b60000103030f16105400030401c4c011400114142582014400c1a52054045010b60320504050b50018043c0c4401030014050074806042c00781207a05c00e054034405200107928441244c00c00321301c004d85030310301581c1d50819101d04840403035001d030900031424103d07440007803410b0490070000c041c44080c5d80920b504540b032900c10001c50b48120100003905001e00a00c4140d2603c4c1c2c60500511854050020000c480a2000f8841002000c280c5400c0075003201240c50140c0e00c0c0011400305503809440260018042c050100324024801e50012250030f07550b0103a05808000c0c80c10201000c1103401500074154800000c100c1072000c545200b500c0c9035a0000e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 647925476 1250 647924226 647924261
    0xc03070c061701060c150c1206120317010e0402150403050d0801140d020a0603111c020a080f400302010b01180e0c0f070b040309030213020a1e0201020903011802100203040b0d 77
    0x44148c1c800102d0722903070804092007190b502c10784141903001c44a082c3d442c21990740d41c0855410041040000040203100a03c50f4103140c050340c01400000c819600207590160444600c20705449014212131424000c61451607500070b082d03941031407c2c280030300c069a0041d080319031071030901030120041c0111004046415008128104515494040e0912011800a8010384070301030070790003c0c0581006030819004002c0c400c10b00c0628041005e0600100c541a090b450410001b034400d00d207a02511180c1554a007406a00c0000303058041d00712030446d04090303885003801480c00c2d2400748280d0641c065105444040d60026a5a0082c0f60061055540c070049042c1409101d507651029080111822000502800c07800c00842c00c140309259114803c0035020340c1000ca48a0004142049122007900c1c2d002c1c0c0c0750550040381e8001e50407501c0d035140182c000e000090650001800d03240007a00101e010349014150706500901c040140c03402e4a240d03050035803404485100d04005000081e001d1711340c028 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 647926726 1250 647925476 647925497
    0x20429060d11130303020c091e060a090504050606030d030c0c0609020d0206030a0f05100509270f01021e040303082a0c0d110c13020c03070c061701060c150c 69
    0x5002028120710309004280c500f00074214a802400c20809010300390203400301c0c0c401c0c031400c030005910b11502c45c1414104231407a50384050010b100010142e02140c2e80398680b20510003400004115144034030410f90498501010200045003290b0150041d000007403170300f1241d0b400040058010a0b0b03502d00040012035200321a400003039440d8010340b42c05402503a2000841010744690080700e50104010051058561900c1c0103e801c46c100100240e007103421000b200c90100c1141c800341031101c511007084519030200c4008960003580300321038108001840748201c0c0440c030a1074040314150ba90650b245142903d82200100d1804008000010551241c44030011240500c0c8060545002d82d54000c01d49103042c104003600148065140400c5034228180f588403503200c5078040f5001e43c50030500107942d4217000c01d51a04501408200800c1d940451a00241450f800310980d460b07668021203003050382c4da07114003e90310188a84001844c43c2d100c1d620310074507000b840c0e0021401c800c15060016100 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 647927976 1250 647926726 647926751
    0x60e22020d02030f012d030b0a200403170301050f0d0501091208010303180b03010b070609060608030a110d0c03080c0705060c0a030c050c0601090207052503020429060d 74
    0x281c100301d884d1445080d024004010801210350940c80010b80813442d4228620107140d9902000c3c443e000c09840d000b0414080b0711061000c0c1d00c810b03a81e41e4950030407258001444401103040d03009100c16100043c001008420f00707440d0100f228120f88008081c048580209418865060305100050f1090b55a6544503000300780c030000031019503610b59580070780c0e030760661a0103001076200160702e22005400d468180a50080300d02201d0544184411590321800f480c42c110000d82a140c00040009082074400140040c0000c094418440603840301200c0280488105e0b65a101080c100800a8400030050000c280100011500700c4400c2c825940b5011542d160b41c0c1c07074040141c0ba40c1da01d0000c0007030304800780c40d03052003550034540851074503500d0440c082110594a00040c019000020340c000355070001c1040802c003100c5c01d210b411040310b0a100300a42c07449180501d0f07200c2a4002d078100745500700e056a034114094040c0300003440005150f1a60024000300b44c0114a159801654413803850014 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 647929226 1250 647927976 647927981
    0x3052a070c0b0702130e0a140a200906150d1109040c1d0d050c0906060415020a020a050402073207240906140c010b120f0106060e22020d 60
    0x2520b407100005541e03000a01c10700c00383c841081400020185088980000e8500c013241030011290070284039528040c091007102d007071500300c100003400c008411800a01c0e4005400940f45020310407606040303180d07940d5003030102400c41c8406401e0b00f10010020851440c0d55507000703104501c1c50038145820110303080d0115044030313103405000e40466642740e00e01c07221105030032041c203036083d0503102c02c02880c184d40c0c2c1e00c3d03a03a00101e0401a00c200080300020b0115284d110941d4000c040f04199884400c250440294945a01903400e902440481c28089a075050600864110f6980014400106502034180180e400d034600d480101c0ca200021011003d40000c01001c13000d086440e6203140315500c4030400c8007000300d024050a05000318107404119058024a002d0440700f03480c5509035580305c001411a00525803101c9640e4098079550502d0705083d030004080c0c4403900340c01e008010098607000b081d144040c5800c0d0b0350754886000b440400e01640c4201c6010f422074400d00d80076080a5100310100c05 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 647930476 1250 647929226 647929229
    0x21c230711030622030305060607051c020d030606091404330e0106050307141e03090d02010501080316020a030c090e060106050403023a03030f06050103052a070c 71
    0x10300c1e12100d4550842850305020440d08005800c209200b01c044c560621484c504440c1000b03030905903120700007440d0343c841000f140c61150b4410242c070b079401c10350025090401040701f0054010302c00c880141da40c890207807081c80f058074402c0c1c840b07540b61890284403203103840c803894189400c40c0c0c6851284a061415042040c400501c40710320100000c1484405440c0610030780c131030750949415800400a594100003280d800508500e0070a030705803034048042c41c180c072504a8070124501280c26450700041103002450080980d107068071123110075145c0403801d03140280101f58558008100c49903001c02d54104416281e44040d00d1000c81541e00d44400f0040d10255200e04149900c942d114500c64200348005409000b0909003581440d040da00400c0300400840103a52400851051444001500c1d41c4500308410b10750414a07007203c10b5240c0140a00901942013078028100300c0041a95806409554440c042e204400501c0402002e85000441080103c4900e240e42c104402000f10309080f11150 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 647931726 1250 647930476 647930483
    0x504020f030d09210206030601140705030301030f030e01110c060903070b0414010306060507050d0c02060d02072a030b0a0c0e060a0201020c06061e100905040f090501050601021c2307 80
    0x40700f945025915140c88456045200d58034072880400c000582e1281c054070382203c020310f001c008000901807a201103206540002d0503a02c0080000000c12000a68212885119139249001e01840d0401074510038440482e50b542908004802c900c6400d0100c05800c10702d10043c101c805290b514481c014040d4456000a2820005c00280b5200780d601409108024803042c900703107151185036240c580e150754007080d8200c104003801600805550750b03d4141e6040b140c40f00340455441c10980340140d1000948590f01c090440a540c5203034800306c15680760400c8a800c07c0440d5016038072301c02c00400800140700140240001e2510380e481c90707103a09018221605072030300010307a1a1201508980351403001000280719002d4240c00d601a8003d0440c00b094880081d00d4001648030324179010381d09100f0382e800158001d40f600800c4840039810b27401c45900a80100000c01180d25172900481c0c486d41d200000f025117403540410011010b1141071040f00031140b07200348103034883da0511460820380c00041d054 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 647932976 1250 647931726 647931737
    0xd06090b0a0f1d0405030706020c060403030f0507020312180f0619110403111302130311031219030e1009060b01021c1b170415030b06030a0504020f030d 67
    0x3512281486401c0d1009008191007648005140186007108020850545203241c041c480101d400c100c810415500c40a0740204155110100001c03050703a0b452040301c0030703000281005c3c120803100280b8401c1e80d026480e10b034051850608484c0044100100240244408207070f000c03580c0c5881c600522083c4450f05402c030140c20507052120303244c1082c20124020250051500848800c5c401c0354208990880e5444031844001400e038400103080800c0f040000c05810b80000344072480c41710320f0316084043d284122003298442504105040e03542c00b03000c100420b403c504220408030029030090410045045140100e04140010049818140160312040364181c65450117010020180200301701080284007c04040c408051065071025040c3c512409200b110140300210305440e241e820b05480d0402444001034404c0344458446600030706c14042e1004040c0c6801c26170500c41c1c0282203201174024401070861706c600889100070000580226445982003016a40ca6281401320708550301c0c1d40d480301c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 647934226 1250 647932976 647932991
    0x302180403021e0d0e0310060e10080106151b060608011a04090203060402060c070801020310080c010504032121051b07050327060403050a0203010c0c020f150d0609 72
    0x20b0315151a50442d07880082c0740a5450b04031090000b1500200e0813145800380d0464002c01c0401c3c14803803201d03048011a82007000c08076140d00170a512034080c0701e050f801d102940740e4a008850032280a8050f00413041803414801c0340852050005070b01400340b03903840d00900c19040d59400c00300c1e0701c2580440c0161751a54002408285400702c40c40104400f84d40c1404107808560010b80c5a1a00502c000d105c0d2402060010054004100d044013500d5408000c42da68103103030703882407200c002c14441c4c204a44500144c0001c6540b05200380c504803544030b540103d62175114110700840e1000100301004012114a900c60a2001455900c482940130035000074182030038680080118a1020306e00e001480c10490000014800403c5418046081c55030580052100c89a1081c04d1200c00c949a409480450003009100b4017064400d039985c42200204946014800c0645000c2e10200c0c000c2e50081c81d1410b0a03101c0c0c2006402e0300c000441549203189041c8004042034101c52454014a9406070384910 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 647935476 1250 647934226 647934233
    0x180108070f0f06080a11091908060901020a0c060902030102090d03110d03061508060a0f061d2e14030a020c0609011b0c0c151e0c03050a030b060403021804 68
    0x203400014100c0300340d00b04201c90a080025024903c05021042440d998418203418900d020056805a11004000807440388010890004a0b10720340111289802890042030165805200303e440100d0b6646603414020f1054441c1002803261032010398055408002c51035065035a4413060542500c00e0301c5002c112060700203101c0c60450088c215805140c51300200780041820103042c0d0b0901c00301443c2c03c0c542591100c7c041440306080741c0c040b5124000080003c2856904214402c005103070b880400000f40f80c035081040030313500103d03103440b01c040075007481905116010f40c95002c176501d060070080b800100501d80790b82203900c11248220803e9022402900c0100300340045608001c4c4080244092141303200c2d01256501c4210364141800921454001040351128440000704208501c0054400101c10003501c1003c981c510884800103829234459040e0103480000104d541503135415080070a4444150010680c1c0050154000303000c1c000000160340e482c542802c0c015500d0740182080c2010710713 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 647936726 1250 647935476 647935499
    0xc010c030c121e181e030506070309051516030c0e030601140310060b030c0a02121c14040f060b030a0c0b07050706170a0f2a02070f08060c070218010807 67
    0x880200804c1800d07101c0c031038600140c01c5060b510359880c0e480020118000f020050417460344006c0c1580079030800c10892503096032040e828240181d041d00d000c100c4260400c160600105c400c2e00034003140c01d0307615880c01e120781d1028484129070f0500309000c1980d2030001c4d00e0f02d002640041c801908045800003e81003c0c8003c0364045503c1c0002d102041c2425180516400000c010145001011035a820528400c201a40d100f00c4007112013991503440040c1801b0701148800e01c212030504058000311000078134041e075803180750844400500711030f642e46c41030040d259441015905104201020011440203175501000704420001e00e5a1403640d072805034100a40e030340c404428408c0d0015040020220a00c074aa44040768080c001005280365000b00e00414600c07001284440c140c120307101e22181b003d07104145401c500d400b2512200e0f50744c043c4030540300d41402a80490340044010070220440403000e40714003413005080390b981c070706009a00000700500b40c8c04140240d0005504002c150303040b5 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 647937976 1250 647936726 647936777
    0x1401120b011a0912161a031311210d0e01020a020d020f12010f2a0807052709010e0702250b03070504090b0d1208060d0209070908150403020c010c030c12 67
    0x54501b5620401106040c0b080c42c00001c00340c0d00e000c3c0c4458400b2042203030030310504034507850042891001c99085020800401c241083c1c41a481c441c2e109901601da005500c0a190322005034000c141070700d015400c0c8800b610110100701c0e080003040e417440f400e965407040700f04030b00c11420000141d0050104640c10681b8640d801145980c400c45004c09540108200c2c155507003d000c3c200360310142c0361000c044540784116001c801c0ca2502078160b2600902080b01c030406003130400ca0300c90b46143d817181d80c440d0030400b0607108580035900055519540a0380e59041d50501003d403000102034694403003081207950301c03c0300d42c10001280020240680c6000c0d100d6918042c10542e407038906811035940e4203800c2d101d804034040030300c1401800074403d56216488152419809050107803d8108400041c00c0c01c1114014200380c0e00412041d04c40d0a100441c003d845550164010001302d0759010041d10344540c07110041e03040051807161b45011410744214604135001c0c1d0b58404c5010b000d480c00700c80c41e03078405 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 647939226 1250 647937976 647937989
    0x140f0d02010b010318020901031b0f090f1a0a1205030c0d03090212060c03010b0d020d1a210304050103020901120204030c050108070c051209040e0708011401120b011a091216 76
    0xc0c0000547c4840c0c3d031480c1581d80c0552016a210b0a0714a54400d900e11640310131f0501100c040d0205001085411404000407200c43c01d00503aa50003a104641c49120a4a80e401c00d0b0034a1040004040c0d460002c01d071140201c0640e031070301045018a90500d1000d034458008682c0302e001079000c5040100600e8811101e0300084c1c1010f06240c0d43e1424607103c1803190300c50f20039000c00c050701220703d164100c41915540d58410030803054003920b015076078801e04036000c0c440c68179210306c50300c00d0044400010700c2c0f0700020003a40ca06810b001c0190003e4002e407008504001d49e041c01c440c105c4040c0d10050003d18000e109036500e082c42c0c0000104594402840b0104100948d0111000644005040d80511001c92501c1d82c480c0c0c1e50310013050042c010300d01008200d110380d91000031055019400052501c9082002080580e01e54890114101060400415070401a8010002d1015003c0020002e074484d2034039030315140c18440003901c00c0c0c0703204000d1704254100c40d454000301c0309010641c0340107041 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 647940476 1250 647939226 647939261
    0x50a1b060903050c010806010e100c05010c020c2209300c08091521100503190303090f061103060f1e0d02060409020c1c020712140f0d02010b0103 64
    0x95580f560740720780f13641c40c0c002e041c49040004100e09070b00031400002c0d100c00203080000703602a0840c006000000c4e80c0010340e095441d20101c1c91070341c0d10100d280700841c0d0000d401c4070b09114580400307803410514081543c5d5540d41d51051480041c6040b2230118601742c1462000c2214a04802c1c41e1015101012451041c80713458003500000074010b5081d1480080211589c40c4e00c00c00c0810a01121300c03c134000e000b101c00c0d80081800039a440500154068003248520748086601c4109059840078022079410200780e06015074000280319030801903007140308101c080c0f806e49013559194240e40d106000418111804420041702d8104586602d80c98181114110600c044944d40103910300b01405000f402034840909207819501c1c1c01c0112001007116103400c46d0f40d0900c242c040d0361103101c050400301d00e481d4000110a122440007071824181ca10280000b241007690303070748003400e040310310300d8030703507080c0206801040e1001c4148502600e5011980001c540c610201b00010111003801039128000c01 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 647941726 1250 647940476 647940479
    0x6010b0901080c181005070b010b04061e110d0509010e190b0f0702100908070b040b0a21050702012304050303060f0a0f080a230604030e040603050a1b0609 68
    0x30381c0890503c2e0000e074640c0026541d004c203981c481c82940c0702c851469811100426141c0030180d0f110004040141c010b0040703030a20b98036010406c5042c0314910441c0e0010317035124218404200c003100c110001c04207508180035410004113459013000c801c041d4110105401080c01000355030031403c85070660714110340c0c083c0c0d010199820090483e02e02d01481e11081c2e804602100c400295038100c83c1080d40007040b910040d103030100d005200c03d0450080d520a40200b040010b00c1c808a4025034003330301c040f0140c01c0d046c8691446c007220036406069401000c10002000030041100c80d11806004a502c0d038000f290484500c1d04011702144c01054048091410200708000300f0000b10503250005011200e14a44650641c00200040712a4104c03042d104a01c03800050251400916410510300c41c4011110b00000d2100802e15600c3d8040341c4c000741c0e0007034800940060300c1107020001c5020010400100e0985030707140d443c07504003400c404681000a100c1617882d010300e17042040004003950310b07007400c11a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 647942976 1250 647941726 647941729
    0x105030f0d08091014100b070c12030e040f0b010f02031c0c052802190321020f1617040305030a030504020604090903020114160e060d0b03060103080403030206010b09 73
    0x100741d0300208008000122011894154060141070f81c010840b0b2014800060444000901e448007174605811301d030300b6207100007a03031030800e02903a1029401403100c141d4a460450581c101540e01c842c11000c01441d80c420180651351840707070403052505d58400003000300c1d400001501020391f4004600c10b5500c1400200d015440303006101c84400d160010215040c0d076080700c10740d400e00444c03d8a1360100101c2e58440550802115000b1002d010390f03084406000781349000c14050002c040c40900051840c1501908200020001e000902e920000040c0381c054124403c20352a0498000741d103520100380c1e6003406110301c4510034140302c11000881442c040c030b107542d9103a0300d11414a800043c1601c0b000020195555082600c0060510300000d102c00c1c102e40c60001c0c000d110030300d02d01c02d04884180c04600080441c041420031584151a0450101d80034010007000303421100c0f410b050142c0340c1c40c01d60995102884514001c6201b0704005803580c0c01d5190203410290b0580003804405000e03c110003c5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 647944226 1250 647942976 647942983
    0xd050f0c0309061c14191508010c02100c090317090f060a0f021c08132a1d09190c080a0f0b07050f070210020a020a0326030105030c060a09031502070b0105030f 70
    0x82a0a0480000d40001850101f110102c03240d226519135480c150405003107d801003840388110212074010400d07036403008400d40b1a41e24030b01010300880d00b07407441e4080d050020320081204200023089108103455140000d42d05522000c50080060700420741c4c03010860f01044441d010402c1e04601c14012090b000000300748900003030542803880303141d00d01c1c1014072881c0d000c0a0801049901d801400c501103280100c0150050700c620404590302031520001d0215250301a802103000101410311404d0841300344081041041c4213460a030646d410010302c40e68100440340c9400d11440c42001c00c0301060610021115008145409001d010464902e403989000200c8001c02d0b4120383d0007060031f0203918202d140c40c00188000f500140703141e4000c0140061203040035088109000c100982d1030110140c860036000a100d00c07601640075a11440e880c0c03038a00d01400c0168501e150902c48180d40f6256494490000700030003a401c0e50004120003480040c8400501500c41038005022606507000c4066a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 647945476 1250 647944226 647944261
    0x10c1b0209071404080d09091a091503070e0f070503040507031e05010c02060402030c012307021f030c030c03090f02010818030c01021b0d050f0c0309061c14 69
    0x85428940002000c96014043c1414010f4a0304522622561903d191580d41c4030011540c401288451700001105619400b0340c47d01c98000070301007081d0302c2d500800d118040c58040c2c108090048080d00c0d01d13106803400c02ca56002030204e102085c200781400712228030790100190581e4104601001004007103000020070700c040b680e0080c42002c08c00c2da00c01c079072406440c103000300800b00d500b00841c40140c03c3d0300040083c0100e00031816100014003540064490201c0908120380c24104c288020703c4a003c528050403200c2d001030b011004104800c45070152003826038861001091707950098002131035051060f0044442c0606013004403080329101c80a8503140303050003d04000241c0005408030400281403e07003c0e00303d00c00c59480c5c1010301110760203904100c0d040c1c0e400245440d82803500e0000043d08003001c20440e00c6052400e0120000402250700080e0305100300e1104100c64030042e140e41009003441d158415180d51082d010801890903910ba07803010750f40308910b05051003802d4802031503071700 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 647946726 1250 647945476 647945479
    0x9060204140d0b0408091f0807270e061203120a110306060f030402040b040615030e0102040b04170c1c0b0601030504120c060b06030115020601080607090302013b03010c1b02 76
    0x2515a1400030000b100607400c900d0f429003907c01d03c14400541c64103c50400d001d0081c6484440d0407580408009003608140503821844401c1c1c01801c00c58131179014403582d00800041c12480d503c1e003148134401d1641e071028041056041c091020048084210703c188040e03c61248c001919506200b030006116000341d003907142c1026400000f00f021590756902c0411b100d0b4000e403080c0702050356100c0201c8542d41c01943ca2000c02d007448005219010103108403004d60703110b400c210f82402e05003c081402044007032010100c031b20900c94803050070750301c0c05512140296442580c0a0003510340c64242500d82010b0030040c141402d11040c40001101d404071074041c42031501d4428844001400d0910190031400981030300403100100226003440d04110100800103140c003144d070280daa95a02d250b03120301c202c8001c80082c40d04881030005620407241c508800400742030f0b100013040d4180c019401d601d40c00c410021811140701c4500041d00b42802000f0720100141401100c01c1e500d66030311034407031140b030300000d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 647947976 1250 647946726 647946743
    0x3040201051b010504050705040b01050301050306220b0a0b040606051204020603090709020c0604020a0608010f0308030c0f0a030f1a0108060d0c08060411010201050f04020315100909060204140d0b04 87
    0xa602c510b00e030328600c91685582c00901c2141061b0038415210301341350080b6070169060081081c0994020011070b03040307170b40207001007003241e5852441103445071500b401c0c0000c030b10310006403402003403501c002203005401014002a820000e039040100b1146107a00540510000340503480d5001032042d01c482c1e0168041c0e420710369030341c0c42d00003d509203420f03a045030401c2840880c00740741003040081c02520131882641d09906060312220b041c1c500789024031aa205143c10b892040c00000c0151014541180041d0300f65420501400380d01c4100d42c00442c1d014000075903c008a410b10402c3c0e0240444100c0e90b0401d801d01c101e00e10000811221008000a00413600d18000c2c0701008000f880000c001c04544054034500c1c1000d00e00019900d00c1d4000c0c840c019802c00c80440c0d06110a141d42d2801150300600600f60161941442c102850f001048241d0014290200144a04850103404500c0c1e12580005a48600f020310300c02400030b1900603c2e0240408903103c50020310365400140d0040d8100c00310 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 647949226 1250 647947976 647947987
    0x3120f0207080a03020318220b030a02090c03042f0409020d021504170102041d072a06150b09220603060506040506040b03061f090204150809120304020105 68
    0xe920707080495105000a104400e4080103140c0c1c0440a0042d078091041125401083e090400003440d021052072000c14074a001d600358104541d070300203003840ca40503003940e0012510340c0004035040e40031504001c5030f10000042004219400c40741100455240c2c0d0100480e0007101ca02d11100c02c4000d40c828003aa5072520b464007599692a040608245e0044c41010030200c2e15489503510340107449000380400b82ca1010042c015410f0003038400350f4044402910b02413000300107410040c4800b030186001e001c080040d064a540901e0030300400f41c0100c404900081d01d50740341800c100c0c0e072a00080c686200c00c0007001d02407600c480046541e1907104903010501280c03e0b041c0410815904405001180e00d004000401c101c0180c200c648105800c41d01000940e613000c0c00d00003a55081c0c40505d515421450020b41d0303580c2607101c007944003185411071454458680c91040200d034416080342600c224590b581212056029900301e60006600000d40700384c140b005c00042c500c1c007000e003001b070501601054 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 647950476 1250 647949226 647949257
    0x30604080304050f1b1c0c09090c1202031221010e160e0307061419030b0a0e060918010204080105040c1a0406020d05091c11031e030d0f0b1305011e0312 67
    0x1034244501c0d0810031f1003181503074441c41900102043c54080f00c4040101500040f1200d402621400c0c4507000b4025011888840481c0b0310603602c8043e42c80d03210840e1104820802c002c880c9282e0113044000c000d061181851a003009441e112070005c50204003010201c0e41190300c0105810088440c2c1b0b0a20030081c2d541c80301904003901071801840c6480209091000000350301d900044201c41003601c081140a8680042410800c02160000c2d0010032f408041060381200c5c592956150411000060500341c0301e80c04079007524010784042c0e07511442c0c04424040505149203806241c03c5000f081443d241ca0242c000c1d48500d03200010400384013010804210684030703803e80250880040703002d02500540791400207a000d50702e4000c10b00900c50b001c3e80c0701280581a43e1900c0d0800d100c2c00441c24840c1c4210601c01070a801035605003040d890b030a040b038050301e90300d50030141c4031001080400c0075814144042a4000d15262040104030603100030000700d2004814107003211171034a0100198820200e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 647951726 1250 647950476 647950519
    0x60b030313050f1c03021515010219050f1603061104052803020607061e2309070906030f1203050f01030615080616140c070b18030604080304050f1b 65
    0x2190340380d80d61821212000c0650106040760f101021303492000300c0d42c4800d02890702d0000000d40c1e4070f000da407101d0b03000d02f0b0540c040756001e02c04078800d000702e031001441401941e040114924070340c4041c1162580c24000c22103036003d00c41d000440c40503000e09140c40c00c4005048026440583e405010246040030181e01900c06200040d54024019035903e840d00d24108004100d4024209202001c0009844008605000d145000c0075400024244c149800c0f1050020301c40241801a6501c500707800010b00003c603010f03407401107003d04885003091031142030550301c00c02d9486c2320004040c98502008400032036044558150303074102d01c0c00103940f2000c5100c44021038040c1c1004141c0d1069a04000c10300d50707005100c040700109a600d0100706090f541c24a82c450003030351940b80f01c5070400d804c1400b1815400018064130318140c80035400d041d1500703001c241000c80686058800120020400040c05410448200d894803688000d02c030305451b24212030003a0540b046107a2143d844c0c8001c12101d2035014 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 647952976 1250 647951726 647951749
    0x1706060418110a201c050d020d050103031e05070c03110f0d111507020618031006060206010501080c120f0601020c041d06090f03030a090804030605040609060b030313050f 75
    0x85000d260f441a10032005000070280b49001e0700308906000c4003070030703000002c6420070320110391884110001c00d40d080c0c150303465000300c03581c155500d900b8081c0394203400150196134003d6000e0344400b80c2c1c05110390000070000403c038201d0400d002042140c10700203004181400101c070b40142c200c0b001c0c055800c00040709103024580050b44031140b854a2802c1c00000d80e038000e40e08000b11040e08410b2020386a440003405410406944148103110140207440c032180303441000310008091380c850031804000700342240d1603038001c60016400b0300014031032035802004480d00680301a0070f546c2071080045c001100010f0042100048a400030b001c50583d900812641c1d02610000b00240416501000e400c217044d1601c44041040e4402c40340400c3c1442800b02e548a40741140c0d8000d9440c41c2c3d1001159800b41c5090300040310341c04401c203c0000803c003144901e50245205000c046000099800c0090540c3c00915980703200b03801c01c12a280b4007802480c5030108481c0c059800480469010740040c1074141207 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 647954226 1250 647952976 647953001
    0x303191802030102070c050901121509060b0901030f0b070504210204060504020c030315010f0f1b14010b030c03011109010305060d080a0909240330030902011706060418 74
    0x82960717000c1104184106060724010b84910203d030b03070303035808002d0100c0d04043d000e00700601d100d04030b0014480a40002040902400e03021139404030460110f0101d4100364000d0b11000b907048000303003c001ca00030f03a0740d4003c0c44c0d92828604007424481c01c100190020205851640c840c10240c004540300c80e0000c03030040000800864645003800900b90700c0f98000ca0740825061501e0456041c00c1d0f0207103000004071040c541c0c0b1312603844c00140d01644c00c1016082e9403024450042d0b43c02c0c00042003041d034010060070710000420040f81e040c042c0361070302d80c039614068841d90416440c1c840c1041803009407030300d0f1301c024600441e6a8440b14041082d1441d5031002400c00000017460155454101201d8012120101c0c401c200310030300110101e4010000d403820740c1e1409003401080002c903142007000d660400b8020354682c04103440c2649103d0176540c040c4a400440c0c0c82d070b00e0040541da00002102c0b2000040742e010a01ca14000000071360910a038003a20b090000600c080c0c4048805035406102d26110 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 647955476 1250 647954226 647954231
    0x3010501051317030a0e0301060e0f09100213150f1d01030b13020c0601090e030a030506031005010303020f10090b0c0c150c092b24050103110a0803031918020301 71
    0x101d0340c010540705d501000101d0702080c0711503030075181818140700381c074100d45013014038810b2503c841440c000910409440e25041e807048043c044640ac0761440140900143c0e04100e40c8014a0401c1b038008810b1640701800500c69006075852400f50005103480f5845030f515140c400ea18201e1005038001d00c0307007804840e0071403452521901446441c0c0d0040c003660303100c207044444e2680d840302000141d5038103200c035610381d8000b84040c040aa0190300b00c41c0d0066002010f8480344c140841071282214002da0090b00103a00c4018800000c4805111148400003844414880b030221ba44411300400e00c05130800020000028140d48005418000b45010a403a02c0594240e820001801e00c400d070488400c1394410759100c250818080c1d00550351004000711000c04403420080c1d525040030780243c41c8203e580d00348444011150148080c802d42e40650310801d148450882d205081c82100103142d0000071003a40108144420440514102d4506141c900ca0110b603403900380c10303949444600900000d42660 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 647956726 1250 647955476 647955509
    0xd05090102161707051e060d022131200a06030b030115050f0d0311030406020604050606030307020a03080a0504091a1002010c09060c020a260607090b030105010513 72
    0x10f401c0b00c641d00b0800300c0c003811141100d41320010000000d40a03120000e1071201c0414110075418034002a194410ba291001410240e004a03a84a0340f009540c0706001c00e18250100802c10403107039415040803c64203009090b0070400d80d032072001006031940c06401c40489403000341e65600d032250b00f070503035003000b40800464a941c0e2101038090000b0141c4140b00e9424030500d0308803011040c0701001119002001c8000c600809001e00142003862181501004442104204007403020001000140803e900603c103518003030600a05090024084600c41c0d0410088880560f031548102001d0341d81001c640d9980301444071040d2264071403035011014540c01d011605c5030b0001c1c40d4910201b90001520400c0003c10900000c03802c076440e050201c1e010500c1d007441400450320070350501001c940b01500c0c0031341040c1c40c0ca8000c0101620444910101100614820449081400f000e1380140b850b0070040401810203090301514001405140e040120104550b40a4809501440002e105d9500a40800d5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 647957976 1250 647956726 647956739
    0x60909080c0c090705030a0c03060b0c0c011206030f0312020903011b1106091b06071a07170f01030f052a0a0b120408071a1e090f0d0509010216 63
    0x1e4000001440d01402a42140d00e968140520741c10310030102951401c0c5599154001140208812030039a01015902e60010070b140960400820013412043c0c0101911715508000401c0c5029980102d103040f41494809c0001a00104c01d545501c0da041c1080050100e14240d070100a010b6980680e80c95805c000b8582b01c0d203030001010022910050751401d01d205090035a456950310b05840c10103840c6c0c82041c02e4402c0e28000708091380904030040c021071401da15620703031a00c0d106403d40c1d0190003038280024449890703044003003141060082c2800b2426882c2000c5082210716051002074400e1032807504405c2040810310541041030a080345140c040805c4051192618000300f100d6406042d18200210741e140012054408213200040403080d2661256a1020306400c80c81c000c80b00540c4010b403442c25008210f080520900c030401c0c81c18280742540d00020a03264001c0c00050700354100030500000c1c0380e00072580b0a1a0342217410502d43c1c820701900101d1500810510310f15403805131486c04030b882e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 647959226 1250 647957976 647957993
    0x10c1704050f0d02010914060909150102010501051c120c081206010e0a1a0d0e030a02030304060609090f020405060a180f20161703091005090c22060909 67
    0x55441c00d071044001e80601205010050150000190100d07852a104001c0e503422442d00901c0e003030f8081c040c0b0b420119a400403900090058540040603140303040304024a59092140a004002c2181c625410b05503410102424440204020b0b144a906000104041c0d001e030803c3c3c0720083d4850f460556401c2c81c0910b8803009003064400500040c2d00f050107003028036056031060142c0d030b4841595114002c000b0b03141c42c40d40e8003600d0004009500c4400d1000c10a0050028160180458016541d030b071400380741910232141c00da0889801186080390500101d44804107202c411903041d24002007a440f0400003800444869001c0b441945400c2c1550b0020001c0f90400103464100c4030040c0015964010742d1459260100325120401005210018480702d26100d101c1005000c2c0d100405560100340c1000381c1c44d402200d400701c85501c00c1002c01a000c0091085940c004084005000d11103030341c070001114060007080803055281d28100502d200822644080d00400c1660360400500c21603107042c004 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 647960476 1250 647959226 647959229
    0xc0f0c03120109020f0d0b030c0d0b01031e030e0909010905030406031401050a0819060f321006210213080601090207111002010e0f0709060f0308040b09010c1704 71
    0x2841d1a02800022500d0f07a078005d0f81d26030f55a000e1a01c1c1000450b00d04030006100f40312056606102d6800e0503130340340e2500103840440c01d000d91181c0210f98150b040c04890308102007616180113050004a401003617101c6043e602a0004a854080d162190150603015061200001d016400000f8000039540c0d050b6001080c00c1d0310411040d07249a0307070b4004120350014188254102c9070411b12190201900303000040250302e100750b400081420705901210129400c85240c452004060300d945500348403c070300d082d140310315218550107841c0390403c00c2c2d120000a030701c10001840141195140a44140344c00180840c0c41c0c003008540f54543c03403107401c83c00d12483c0b1811425008120000ca0b0005450080318405504580304c8ca004413070324018000c40e407001e02807403421550780e00240340d10303841d09001100054542100400b00141082d4a50b42207074482da0180340e61088c119010000294500140d5017182e004202c0c00c0d450740180f00040c0c403000504032000307050840d40b44040e80c500c43d01801400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 647961726 1250 647960476 647960497
    0x100c03091403101d12040503100b0d08030106050703140a0906110109060e060612030a051210030b0405061f051315050a0b070c05040c050304020d02030705120102090909070e010308030c0f0c03 84
    0x78150360000517051180d101e18005e540d0150003c2c0b9100380304a00642208040344005000010800b4683d250011340703410a800803c00100300180708414941d002403d220a40307400c0103110300d4116000b4002d48a00d45901c50b10060150300280460f104400394444650305d508240700340003044044007207545078142150010700c114001c3d008101d0342d480010030348806400b15240c00349414055204150220002400100705061801001c03001900050585010b948030700b004100c282001105800241030400f26882510f01140c0100069983c81d002d082c0344604040cae0016100c0420719034039000707210300e0f0481d80d0400800c03c00022030086240c01000d110f07028910609043c2c0e115410401038450001c007600000d403007400410058540307440500800ca10090888402c0d60b03840d80030480c8009110b0346214140d50210342c80859040100c1340039400b11030700000d00302503400d020310100340540602010702015004000140684407200071111420074181f03110351142000310417540c2d00e40c0001c00a5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 647962976 1250 647961726 647961733
    0x303072a03050304090902062803050a0e1b0307150c0c06030b09010612060317040f0e070219031103040f14041e02070809120309100c03091403101d 65
    0x1140800e1800e0a9a01569402400365242510740b1140501410704280140c2c0e128600300a2a0b00b980340403240c54040c09a0b92001d8510511641030107001c0307400c010301c01000c003030600e110034254100201d00016041c000070f510019542085011901c0c000c09600410950620039042c9660a07410030300660140e032083e41e6044610361604411001d480341d00068a811080480040c010f05014907210711080d0070300d0000007082983d80e02e4803290850181160911003c1c00202070018402c004407a0014001c031110907046818070b01c00c001c1d81d4400400030f05c000000305842800415201e05080d10441980c00d003166252600c52848500803691441061040b59100d07480c101603040c0344c040c51a0222107a2000c0004e6429000d898020758486c280c200d44000d4100490700c900d5840b500041e86054602c8001d40d00d602c075207810700c050340c0d052408140600959203010f000003a031100591050f5490010001361481e60480420300c2c3c0108040740903542400c3c40049074203645c207046080d05120050086 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 647964226 1250 647962976 647963033
    0x3041112070305060103170d0609021b030c06010e1308040602060601200705061b03032e1a091206040f0308060d0b160507050a050d0801090501050f12010209030307 72
    0x100d076140014400200150404001040031a4051000d81406070320a000b6505c2c1801c613a100808031201e0b074010a04280e4080764410081e12000b84031801c50000744000e520303240f00b407400d2503542c05051203200d20b4040c50701c0019440341e4100c501180d18651101a00351100c0d02c940c0040e48172181220000d0024481c3c0b08420055100c081304040440062030203405001e0408050040c681c1c805203451440b07110344008445540380030001940701d0801806020803d81408002d010303001924606d00b103185191407002d0050081080010a900c903141805c550381d240101c020980040c041c801000150044c07404000c240500b0580810503648290340b09100c0e591007904022040c84104c3c40600307600012030010306004c01051000755080118185681005031940c2c0f1103240100c009800c0b078a036000407045031000c6e9004810113015050580041c446981450081a00703540300304107240c40741151985010107501c081d03040701c48000002e015250344152505200b0031410843e490300b081010004003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 647965476 1250 647964226 647964259
    0x1021e0304031e1e05031803090a0b0d0b0a0323031c0f0914100501050102010b0f040207020a05040e07050a080a05060112050c1801170f031903020d02030411 69
    0x1228800c0d9459216a412aaa092041059015108012000d10849802e40c00d4200701e0300400d04d40b051456690540d81e4a030030008130032408541614202940d10a10141a1340e45d00c852004081c1c0742c550446907140c5100109000180c00091283c0390072202e00b0307401009204180c503103540424003101d851403104075030010341540c038400e40d005201c80d00041c040d1141135078250340021000311421800415540d9258594120b080c1c00d00f11750000366401488410104040b2380502401030809000800242c0c0d400c0d03000c105982c5030040d5051040d54000741d400115550480003401414014004100010b07400002541c1d88a29010301c0b03100300310001001607016000610310200c10f41c0007014140d01c1e4038004024521002199041380d050081d00b0210381e164403941070740c00d251108013410111302c1d403401c2450048201204507080071a008051040700c0384000008a0314159005444041903041a100840003030140500c2a0082e50000051009102001d03902c4a9810130403220f52009208180 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 647966726 1250 647965476 647965537
    0x7061a0315040b190b060f09010807030c02060a020f1c0c02014b020d020a03050106020f12090d0512070507050d171b24060a260c09090102 61
    0x218020140102c010005a08241c504d0071000b084800e91004180000b0890001e40c00d44c024a41d200000d50021914070742540c2e00040340d940000c243e0900b04081025500000e482c0d00008103a814400c0e000070742c00e020401100e0488170511041c3c0100344429010b010400c001c1c02f040c5060a00540c204501100000c44640020380c813030b0050740c401c5a0040a03e036400100483c43c15030503162000c8003a1400d03151190303000401108402000069542e109000013404541040c1c01c003e08540c05040501040400000c07002e980c00141441c160300c07070f81c004c0001004100300b001c004110f40100b2100c051240182c402030204c0e40d2040050b01e11071512601802140c2000d018090034107000340d12000b41d6101d01c1c070014088403405403442450318040452491a0800800c0038440181c24104401212045a0070054004000700e903211901c0c4e140800c58450030f46030402401e40c10080c0f808554003150200b10540820a01804405940c5405400c1c24000d400003040f03110522840c07114450590400c4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 647967976 1250 647966726 647966731
    0xa140c0307050f04020408060f01050a0e0105060306010c05010b1018150507111503090a0201080702030306130b0d05150106030b030a0f0b04030e090c04051513060c0807061a0315 78
    0x150040610910b000100309903c2c02d0f07403100d280c00c00d50800c408a500801486424480e10298003680c109500d00000d008900c0c03159401010504814401480603649035005c49030008824644181f8502150512034010f05c4070a500a50045012043c3c1c42c009801142c3c520a6141c1c0307a403140742d00b80d80d9014215890602489a40c0000c90821900300081c040e03044011140201a2403800c140c1101c25139410654000d5469410b40c0e407001a41c0021036a224414550020540c0302840c00d504001c1c0c042142d0355004a0542c0c4555180d088424130ba0301e604500c9803200342c00c2402c80e5080b03040c20110b440000750a0041c98002824110307128905d0030000f51100040c0c1d48a1900d82d51640f090710391000002020b0011010802c411a080185a40744400729000d80460075025648628140400500203a5001c1c140170746001804450700c1841d90340301c0071045940500745403011007014035018680344500d0300000c0c010341c5070040c140311610300c441c000418948203804452158410080110001e6400c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 647969226 1250 647967976 647967979
    0x90c04230f07050f0a1707021615143f0f130c0806060424060809030d05070c0b0708091b12150406110a0804060207080c0d020a140c 58
    0xc00000c2400503400070702080d0320004900d0040c0c10620018001c4280750301050305800014848400c010384016a5844140c101c1f01394001050302d110241e020418401080c4074011150300510f8250340458003842140c0c4c0b0304144517022a581d401003080b040e0030044000203611502c804442e8950305003030303031015003480d06412184941c840d43e40c1502c0740c502800021f00300e0112907000c0c030b00307500020089e0350303c4009000c281c07029140c03030b203091828803044034001c44610140d061700c510003550200c1a0301c642c1f01550045d207004045659901041440c44c45007040c071208451800082204050b8040e01c4500c0e080d12034020703408240c8075000e00321010a819100071009401107a00405c2702c20020610301c400788006010b95100500b860400c6040890320780700200705003400d104100c00c0051030301c00c400d80d02c2c2c4240d24044c24000c403840010325405008100802c0550700007121403e00407a0380035a0006000c0d403040300c80304524003a00030b444050b0108115200340340600c81e940030010105a21098039030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 647970476 1250 647969226 647969291
    0xb090312040209250201060e1f0504050903070c08010f1b0203030a05040201120c031d0304060f0305041109180c011e080c040e0112110108060a170f0105090c04 70
    0x3659020010f074180302400841413600140d03031903160910070002d40c4e0903500441e00006181e0341781c00074242c400b050050201200d02d0060004180b29030801d4418019610159800100c55880190b014910310070a0009000024080307400100791005400540d03854590043c1480460000f846904481030b41454481c056002400011410b00140e070205038410700514050303503003525102c0154121a4030004600c0001c0e15000d030b1003150780c4455945081c0b4071100b03008500e01450b24000900c903013a03ca40440130140c449010409120703050303800350700594005047c03500a082c10070100e03101c407188407841d900a0168036003008056002d40d8000d601003004800e0680e004508000403111428000d00a84100d07000f0b010202e07111036200e101501810070700428508003125030404140c0102607945560401591030f040040b5905c0b0b40e0b94a01c00c0310382d05c0426038011019031000d1402d0050440b10760a203581b8160810401e00740000d050401071100341c400300a00c42d0301041070007000c6040501d40c0b04d03011 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 647971726 1250 647970476 647970481
    0x711100c0204020a1707020a030206010f0f0e0705191205182d0109060e0709150905040201210f14040b040318030501140a060b1317070f0e040b090312 66
    0x8168000b0030302c0c04c06525240031092040c94803034160790070554294005034401102d040c2015010850180500709049241a020f45031490a4804000900401115010b82000300700d455001ea8140c07548210300e002d518104010b5001c00420401002c0040810b150501c0c0100d060032440000000c054141c80e03018212100304a00720008075005400358a15a110001c0c000080420038400d09485500c50000403540452a002d800e14100d103540000080900d0302002e07003442d107480707007001c41141d03488a4042007503540e5000685070000c003c1e07408c046041c00e071000c40701465000d41c007520440710b051404128100b843c84242455040841700144110903010116000c0707402100d074a54500c6036120b0041c841c548981d15182595154022500c3d90708171141072103200c3d0803d0280c43c01a24006006606110090034003440b8040d0900c181c260b41e6150441c1d81000c03600c24407a8038080c08205040c1804c480d17480111641840c01120155401e00146000c00d503095030100031986180e14401c16a5000d4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 647972976 1250 647971726 647971729
    0xc0304151e110409050c0c1c0203032d04030e090a06080a083f0703020304030e211501050319020102280c030b0a0c0f02030a110c03120711100c02 64
    0x100342800700c1440d0781d4028800013403011101d0003a50310a001640b0035039140c062074001585000242e01c4446a50f05400691081d1a603000064a910402c03265008034803141441d6405007203000768008140d60190002080103064100e1413a056004080e00e140d191951150343c0c060880380a03004012094100428400128000001078455082401d2440343c240101d480102045100c080840c112034418142d034030001e02caa2507045a1048a508056107586000c0ea402412014102c01d0706200d0202400941c610300c0e090307217000705402882c0c01190482e554400710a844408244250b512a118401a40301c1c6000706005d003206050f4181c00800b60461683c409502c040c1e600c08980480d41e800002840200d02109904e40085008100d494070900b40a4416400d4a6006840300c0501c010401000c9503e0360010171101000214540306005a00b10254a410400381e80740d10381e410322034221050085080c48009103502442101d40c10052683c440c01e01c40c21000b0405008046402210316030b015 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 647974226 1250 647972976 647972981
    0x305100b1c0f150e09070b040311130906050106021b0a060801051318060204030b0a0915020c0717070e090d020c0f030a0f240b0916170c0304151e 64
    0xb80303034444401107a0380c154880050350501460b0300050700d81d40110b040c08a031000c180128800340046550f100c6c905130030b40e00c0b80314200c607803800014001c21503140c40c110b051a545e0b00c0540c0e00395000409108959483c02c000795202c40c0e0805042ea420503e039802002d500d000800c9400701c400d0360316846016803920041007004c4030442d00065059844a607484000f00318400aa00300d2441031200603101d60560030400c084260040c4480340d4107184ca2408030114051040811040031201405681c41004a11190410010ba4022039049010340c20303400043c20042071a406079100080001c2003540c4603840c0503500c2200303001010140e000303000c501c0c0c280d05000103c001c41c110090700b11181c1c3c002c6560f503c604444032100503503010500c218041c0031214035861804031080c850760705102d403c92180028041081c003900e149030051804100a00c601d00a0700c08540b10b5503e8104501c07945017108002c03400764800c4170103e8a114001c40d44034040c5103540b14454003243c141c0900d030794038040248034000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 647975476 1250 647974226 647974241
    0x9090a0b070c05070e0a05150a180f06080d0201050606031302100507230c040b031518190c1d07200307050a3c0305090603070305100b1c 60
    0x8000c2d040c10154045801007002c04014030030280c010a441c43c0c07071851841120700140021005107a8040780180316600c03403501d0b800780c418892007008016a4044040001c000e40004482150f0030031800041a000110b1641143c11071a0000d000076070303c942c2003019500c421109640014440c050303c002504003945150320340c0841d810300c0380c03600352241c44041a00e616a844c0e0308945206808803007601c1824042c5040e104021380d02401007a040c400042e48030440703800c5041000301946c00080101882e01110441e00301c07281c0941d50b090f444052100c0310416407400c10746030452004400100d0a02e4a006003441c0040c1d4000d4480c1c82e207a05004070b410116034180e5210b142903002d62100701c041c0600003004607a02c60f50052900511624008040c0345c1c1003804c44540b907111001c5046007840d984e60322620608480380c040c0280700d03c1d140c162041d00503c2c1105400c041c011040004150709540013034050b5101d81084540c440c1d0700c4444141521500fa01c1d480385414009094944c107450b50055403 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 647976726 1250 647975476 647975491
    0x81009051b1309050606010e030f0c06030a0b060a050d05010e04021018030212150f0108030906070c09020409050f06030f0c19081c0f0207060509060a022d010b09090a0b 74
    0xd452100c0b150010b6030784201d030960351a0401c01c140f10f155030304070088402d21712043d400303800095500d0116585500384460120300604c400000035003160b40603807280d038001e0703c0180300589400480070001e09030741008912072110b81c03a1100100e504a280921241f203031350b00402c0303030103180d001e140101d0307113448103403607002c0061a01c150210060350754001c0340102d0200300000344200365403013024001c072000251036400700038580401409007120200486400321010380315241c1c0c8060510381108442402d40c055100c184c404500820707841c3c05034000314000d020034816500203850329010140c603020071200c04d80300d50740110307008070207410300409149503400d480f1082c42d400c3d0b9840c45403a092070902120705081500034403481c00c40c59040404500c3d895050300c0104105800c0c814003616034403500c40154030034032010076082070031352007005580130040d017413440d00c0c02c0890842562b40c030301c2e0380c00f08010030f403942414480e03001401d28544903403240100400508020030f0300c5e118481d4004c001340411 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 647977976 1250 647976726 647976739
    0xb090d060507030209010f0c1a0612030a020705010905010203160605090a0501060b22030f0b04110607030e040605150d0908070506090d02150402031e0304170304081009051b 76
    0x8202044951140c00d100b0074060310302580c0c0c2e0307045c00d0005118042003d042410f0009000240c07002c08d10008030381c01d503d0803041d502000ca44803440069066400c2c07250360401880000707100001c903940480c0c490100d40007038882200075900c032030040e6200d01500344038038030f407440d405207031404103241c0c3c0c000359000040c6c142a134600f109540c4620342035420070340180c000f60b00b000460201003800494140d0100681003d2841c4003421035441e5000c10780c1034000034207001030800105003803220400d0b40d0015200014a09540c0d4016032070b000e020700140044040c031541c90650006a541003601e0b003403003160303541501d051030304816140c0d400003407440076400d0754205000e1003240d000904c00c1000b28012402038006000141510301c00900e00941c81d001c40803074620703400c1440010780b4001814141c085005e8000c15611034203107411495405160310400301440b0100417400c5400c404801001602c95800c2030320030143d046d00c103034401e94203103040081170b83c0d00100d03c02c684128001ca80200601000f4100d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 647979226 1250 647977976 647977999
    0x60103032a1e0c09060602210301061d06040e01031110050a020d05130b04120c0801090809121f092015250c05030114101401090e040c0f06180b09 64
    0x1d4070b080300d070250000c0d805039204112006100e580300402313580c441100350540c0d01d1581084c5005114403001a0310b038501547c102d082c1e1072290b8030202680c02922480d4150b0401d980d590400380705940042000303a000e1400e4028005041d0b12400454101903a5a00140350070074041c2401c42e140e0b0311040614001e080e0314000485d4400c0c007140184000c2542401181d69418142051425081a80d100c031505030302d0041c1e981c00040b41a8191413a0320421561251a2004d4000389410305081800140c4102e8011340c8039610324040394407081e41d02c0e0040d030801c260000c0048104c0882c1e06080c50040d80544440e000b080c2c2c0510450003440f11501004084071050840c1e841c01e0300040d81c200c0101e40b8003070000028413040c1024450020390b00351400d0082018103240d100494090340c42d001c2d40c07901000c0090480101d900422400300140788920b20070150380b4290600a008403264002da00e100354a60340300051a44c82440f04450401c0300118100d0b023180740054559550303000484068028245054 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 647980476 1250 647979226 647979239
    0x1061206090c020304051002160b0d231e01080601030b070210020703021b1c110a051908011409030307050a09030213090b06060f03040204020901030e060103032a1e0c 73
    0x502034400c0e40b0f50000c5482d00c1c01d00702048426078820300d2460440d032007620a500c600c0625401c00c01140d0102c15041c0d61188508110302c00303403c1150341d1580302d0711243c0041040891414541784207040820ba00849003120007501125071401380325000f0950320000050000c82e204075a4107070807400500480ba030a10041c1d14440680c4c00652041c2c001d600000701d6050b1401c034103209807011050844100010031220748240950810a01c0007610041e6130301542e20340b544402000401030140100b442c9004c030700f14512010700c0074003400340c03880c1c2e542085601c0500d400c8220695000e81c0e040b001560640d40d40b40710454207900608151010409d10410010160320746002c40200351043c030401085071810350030866011403001c0c2155009850420008030272034841e4068a8001c1c0e81118090303543c0e000301004902914186403440124020200000704158220309251902d00c906441d890980f6008060180381145800c800340200f0070641e070301c03002c20103d2960a03450902c10210000c0540d00e409 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 647981726 1250 647980476 647980481
    0x90f18150e10030201022116021909020408010606030b010c03030504020f0901032a0815150a0b03040b0915060108060d1202070513060317071104150510030509060106120609 76
    0x15101a00b08480d00001d1003503582c140304500310309038106908008070401c000d0704072840c03203040c0c0c400381c020102e41c422000710355030002030200403081c1e2a0a00130241e12154000e00a600610400d0010b40c80c11400260380b90181c0a5a0300f4010142c4400d801e800181d1015006001d0081080707034400c800c1010f07410142c1d9680c0d03104c2d02841c02021407408031081d0603894081d200f401f40c2c2150850350020380401840d8000500e0b40041e003010a2001d405807115848948441e00c14040554408038600c008180703003c030880514400c44c0502c44403282c4d5102d04140c55141c0030380e42c528115034140e100010b5800e5014010315078101d00094181c2d00e84880075103401280d851022002001030b0040d0504000515042c00700818086541004004691866840e14045541c01c0c4050085c1c800109814061024142c80c4540501004e00188203030002d50704401940c8446005081c403c070111959014402e10038400c041c410241800208056405c1c580140d4403141074070080c5002d0354489801058004150 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 647982976 1250 647981726 647981731
    0xb0a0e1302061b010f0b03120f13030311060a020403020607080a0219060f0608150a1e06080303010306051f06230705010c091a0a030b04020c1b01090f18150e 69
    0x101c0c00762001601014003d0309590243c0100392a0500b461502e4041e0343d030200b10030600a004d003958503541d12140311581d0007801889440128422510000020b05130400a000f101440c40c4040d20400c2d034940350000301303e005500010350440028400c0c2400501800c0007403050344a030b40101c4044003002000003a04c0e404981d000c0360415210351602950002500410001e403410340b01400c0143c9016403800364111000380140462a20b5101ca100c11582040c03240380301342440203045c88000c0d26440003d0f41d9600a120407101c0628040005071502818150404488a000c0b0044003884c174011b01240c203180c9074944030742a0f0440e0b4920505501c0003030014011148200c0002c20310b06841100a0f010940542c0000c04019155900e082079880c0003084a201e050340b41800103800c40a1760108009000e43e02800c0ca051113020070b001d81c143e07000550380114900907621039114507255005000d031600284200ca14001c07000540d0707804881c15400111f007510078074a50410407503903003c0b4200d011005 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 647984226 1250 647982976 647982997
    0x303050922140912090405100b12150a030206070204050910020403110a06080903040e130f0515061f0309080c150a1116080306032a01120b0a0e130206 66
    0xc40542070240b01c01c14140b2580658507030003402034001640d0580d6614400c11545510070390b0b9034800a0b860012200400b0081c4c100a40c00710340b26403440716414030b03e81044d181241c000c0d0303c80d003c55135203203002c10b00304003a42d5024040754109642035082c0030142c01c000c1c01d4283c003401120081080301075244040c0000b1070095642ca0444040c0c4d03018014008155044481080289410407402640010440d0700300e460038048403030141e90381c04410120b8284010010004c0318010307030810a001000034840901c1001c0101d00070181c44607000c110303001e401c50760310401800f4840a0492407a010f41c2c4060003044c05044068540b000680c0824284884844881200c405c0f09090102203a8a0310602603100140070501d4504488010510a00c20707103010b005084400c0000011000d860030320200c00482e850349221101b6040340102c280040712411503284c001008031401c2c40000c06640070340500710b00e010301201c0030340f400c01c0880e140390403005011609031841c0c03200c13010050312142c1c01002400b01 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 647985476 1250 647984226 647984231
    0xa030204050405060603060a1208070f1a060108310f1202060c041212030b04060e01140d11010f050712080a060e1510090503010908030f09060106090303050922 70
    0x7000100401c0b500c01415036030055030b091081000e80d0310b60440e00030a031740c00005040034030581c0707207840d03440380c07041d004000d00110144025004101002040285103191642402e5003039032000c00445142d1421204194049204049004890020791001c15015501c4140000700c5100f43c803407030f61142003040103ca02e0f81860344007140f0140e0500c404d541000c0b403d1006840e080c9481c1e140e010346010100050156440c541c0301440003030095000b02160000034000b80a41c5a540b05a400740c88800d10800d4402d030b6100401e540546000103a0224150384441803203480d05100340110b032000a034103c03007010702c0410002a0041110b000c1d0000722051560381c2c000d040d1401c1240d0000385c9000340e01901134800d0f00c0042c8403d2103215a0704804201c4240c500340c240c40043c01045030402104d501151b05546400654006e02000200552058048035042101c680364450345a513502002d1003640006002d01e2000d10000e44a2001000056001040f1004040048161014074899160360418869 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 647986726 1250 647985476 647985479
    0xc140705180406050c0a02030f0a0302220303030b0d0b0a090c080703050c10050c19020609120319050a08071b0c06030906140c0711180906040c091a0d0510020a030204 73
    0x2c0f10b8000c15500c0703d040c003502400d0109421000c0c3d070f00e004411003000003031000f140b07a1014034460781c15143e1520000c1132a2600c001d2006103140c20752890302040d0006800e00ea141903c6052007119004515400754030300d40c21740e41e104001801458202e404031840585e80c0000601c0340d00401c10074001c1d5001d1005024036800c0b5000701b040d03806030241500144407081c04404500c41022561040700413071582180202610341c40011158440c0402d202c1e401001e180d50304102c40000800b805000d80225a9246c00c1c56000d03c00399142c3c02a280d54074000740d056000250720301d20980100d8040494240002c0854100355203460b22034956410410010b540c804040c0b00b032008a00580c2d00003401d4107404071282c105420350039580d200740280500344240440c0ea60405032203441c1e0304d020701d00c04980b01d02410308100c011140c40320415941901c0c040102803000c07a180040f803042d0803604040094a0020303600e85030500c6455402400240c540e8028a450034401801c14002000106c88991f40180d845 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 647987976 1250 647986726 647986733
    0x10506060a05041e034e080601020a05010c03020913110715090b132102030301151112040e1501090311010521011e050a06030e071805160806010c1407051804 69
    0x21215481c03103e10240030200b1b06800c01040c40c4502c0703414101880c1040da20b94a0300b00503480d0140100c8010120b61800510040b00c561590280c40841000c690307024000c0f0a0f00c43c1e40013915900110040b64481c1007050300c000035840f0052801076259042c0c04158105180c40d01c0c48204000c039028900024440d0080c8204900c0e200b1100342c0d44045041c0742a8103240d104000e51340d000c14081d410a81c01d02045403201c0034000e00d412600004081c0c00c484aa8814400440480d0428810b01056649401c00304111040c2c41c05030701c1c1d0f80c1006a682c55810791070340d100d400364400c82c410201c0c10320108212508400c000c80c9507001c0385407a5807007001c81e95494404140340c1c01901d130880303180504101300c081c071081d81d07840314880c12118185400702d070401c80c003409076052030003032342c84240c04002c01c0b078018800e1b5103c1d811062154020311000d4896814080040d120001c0072202c0d00c0c0028140d4081900040300b0108031000e06138000304a40603591601c002c01c0862080c403100d070f4103800c0e0400420080 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 647989226 1250 647987976 647988053
    0x2180c1b030711011404121b050612130602040806070201090b090f0a080a09150804050705042c07080106091a0a0510030203070210090f0302010506060a05041e03 71
    0x229020360011850001c998584103101c0001e0740906040102c1c4c468900e0010700d000040c1c902030040b26101035114500c130300d011098180c0302070b030b450f42d10305250302c0000c1d19180c5070742590304110345010209440e43e0303600c400000c142e0040c0001c03140b01d6070034000031540203020000d0600c1804c06400008042c40b907801c104511900060a8120640c405c12124100507008100304414940c42040c603922200d0200d4140c8810b11581c12482c01c0040c18145010704650001000e0300803401007094a2596840301d0600c41030325800d116a0759012080340c5c0702c500f440d400c00c10820303080d001c50044d0360b001600c80c4005c034203640c1c041d44400d5141c3c2c0c0b174290010300400000f544034582c0e1022501c01400500e80702c04030b544c0c07111050070309092550100001c0c0c11075009010900040e1140c52042041582c1403a148240c40d9000e60306400542ca0840054002c1c1007480445100d1822926242e051500d0704003154000d03060400c900c5845225008000300180100c80720f5080d80d01c0e2010000000440300740840c2d030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 647990476 1250 647989226 647989267
    0x2070f090c080c03150f040e01022d04060e06031806090a1e0201020c0909010b0d300816030905070e0612120913150902040603060b0309150402180c 65
    0x30250f000300280311010b03505c590003581901c81980c00580e150001c2000030028920140c986101e07500001c0c1d00e003004420300302d407020f0800304a24040001d02d04000349062a00442c0110000310f028804015002e180c1180610303440442d44068200c1400d046484500b03160f01503d44ae83c031544200340102c00c10070300c0d2110400703800450081160000080d00000c0d550010481303c24000e200c040d0100d00032241c02e4111809040019040c00b40b81c034a54507240311200040946c48903980d0700007081640d66208800d901c40c141403255942d017400c1d210203206114403440b00d503004c0181070351000901d00180c0d06100308401086e00c084003403000c0c5006020702150a0054803080b9054210300c0c0e0302c070005841c1d5020399072064010354080f114092203d0060303004000407201000700088400740020150f0994004000b5242c05039003c4c08402e5032031000c1031702c60009403140c42d080c0d00b0030454078881000354100f45a2260000b42801c00701c8809000340c1c9816142551660003da5001a034007100c3c0f01251112403 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 647991726 1250 647990476 647990491
    0x20303090c040b06070308060a1703030a0b100c1e1703011a0a09030b0a021c050603071203090e0a3213020d12050d0f060305190b0103060c02070f090c08 67
    0x403801e0b0f510000078005104000d00101805008008101ea5440799114100509000030a4407014422504180c0da01d400c116000e00485090400421a9003040003560076200ca644d10b500c5150364440c0c3d40c9030190341c0650200018003d131508110f011600c0d4840c13940384008160400d99503541003e10140d2010070850a0850711329040000c01c0700e0070360041c280c00c21079822403241c0a90751034656440019114890140b84058405003c001040c80d860b171049008000440454034503c0e0b9034062881e45804400c0068041080721804200c500443d4610b181d10034805500054107180005a0090102c0069509042442045070011508888014682c1c0007180e42c4a03081c0f215000d46c4c000340900200003030041c50161201416031105020302d040e1200e5020920707003440080d019008a5008005510060b2058860b201e108690070a100000071102170b0886083d02c0160b0850300d8250140c060215040d04611030b080340000c8400841407658054410080040f0f14202107120003040e240c0040c1c20039 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 647992976 1250 647991726 647991731
    0xc21090b010801272f010909060b0f0f0d09050d08010b032214071805130f03080709210b06090603030a0c080d05040821100504051510020303090c04 65
    0xd40180307900145000e264078000c0c3c51503681d421880c085114441c44005051640b82c184440c610711a01750011801046007a42c2d80d02d14180c1c0c420700102030302d000c1d00ca403803504982003217031480d0b154600d80240550110b08a5240c07810300c0c4111060125049001d0959840e00080c0c080c810309a80a10802d0040c078980d0740240c2981001c12074248000310510b1500a400340c06a4090100101514560040c0456500341c81c804d0341e845214045004414022620192030100001c80038180c1c00103100c58150884943c00c03200d60f084d035041e9100c2a010f0450000e01c01040310010384a0329885603090402405c0c2e44025030040c0340d01e00201c4203100030307000c0c0e48610300d54410031115403000015641001c02034a030000c000382c0c2500340103505100d00d55181d154035003840c041006020281000308083c40c2a840071071005481c8015030034022200355086440010041e400b00120714150708010780207a00030b03203500031164000b00010102d8a03000e05650160304084100031070180180304250a0b4070342640c0a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 647994226 1250 647992976 647992991
    0x503061905030c0d0f0b0a05071103130b070f0f03030b09010e151909020706150e15061812100506060403050a120e0618040605011707030c21090b010801 67
    0x41e481e045240030050040c64062a168203201894841c0b041750b94003c00309200c542090b80651015107021203803400800c88070588810000d000104840c409a41710340d4a2000500b0b04486e14002d0340074030b4050b1042011180f540c40800c92003640f08207403500c0707502c000030010301a00c140a0ba10030140c0c0500e03d145042c80c2007282d90034142000300c6000d030048a0800040d810080f1001c85401c25400c03ca404910100f90f1000300702c81c40c0d00200110003201c60560740c140ea690341003d0428001c84820304003401c4400a10018205070000d86280303050400184011680a004207401d411344c01d808848035441070710302c01c03d0a000c4d48503031600150190303082c40c505030450300d0300b543e200c00070320004040e510744903520750189104410710441c0850061001e59030b600510000074011000561880c4102d140c40000a00c9602600c010508401031018083d42c40d640e0760703c294010600340108005100c8048200c1c000720b860f010b281139a180c41d5407000038024180341050060003c050f00000b034141c1c0f50070403 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 647995476 1250 647994226 647994229
    0x1a010e040308040618080405090c030705180303041a0d06091802120a02030d17090309280306230912032d0103080a08060d030e0f0409020604060503061905 68
    0x4a05a10a8050410184540b01e9240c114010810512030030703101c640410001e0300b00b01542000307000722001103900209985030b40c40c8002040c4400c0d034400d000309800f04031070200c84c01c0c0070369240303000c40c0010152401d1a50740c03c5003d0306092408400201d01d000018411034002c072512480c0c0103440148410400d441000015204c8134401141c064481c040343c00b11090b00c10400c209490041d5409010340d0140400c404018148207005891351030b4140b603400001c2c0203c40300100f82c4030500e9005046081010440341450606d0303200001c41c800d541c14400b40400850030601921500c0920050703e9080c000401107094030006001d4a030146030341100c0d04440421320404107603500000100711071880c43c0c00a040c00c05403400541868800300000d0400001444003940242441d16410307226840c00f503a81c48100032841c0d1114200501048240305003840504141640c0100d02d031018200154201d0342ea0001002ca80056002000080001080194904100c1c404481002c80c1d02c0003041c11504010 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 647996726 1250 647995476 647995499
    0xb1218061b13030c090212130309260a050334110303042c090d02060a0f0b06040f030c0e090d030b011707110f03040b04090b040b030303131a01 63
    0x103211144901e0108041099840c040d107084000c551080c8a01503c903076403110741002c1e40002c4c03254103c02c001c80000645020031950715000320741d810369400003114140044000c030701c5412040313140791391112002807d20003000c0290341000307400345005548031080d13a40310b42c1650401c405809846000c60301550760540c01511002d81003a4004e5070900903c01c0000800d196000d103a1040b00c00814140c0804800d0b0180c00e02081c043d01c001c44a6000c540d2411407240d501e000f4001c040d001648520000390214009901000c580940000041048048440040c0c41d42e00706410018040c910103104008101484034584001d100120f40d40e13000d4a000303807010740c0340c491aa5400c000d064981900c401c01c0da104804d1040984200405000b460600307410007000144101542c0c1c02a06c54161501c0e80d280d400000d440450301510302c03007441c05092108034800b5000e032141898016868050112140c0d03414406544a00940b554440140c0c0031400e0030b510810302c0f442138802d04000f94005200b9000c006 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 647997976 1250 647996726 647996761
    0x7201501081b06090111070603020c0c0108010b030f0a0e07061701090b0a0e10050405240f0d1e0506090d030c090614030709150c033c0302040b121806 66
    0xc0751060384400e48100180c070306c07614036040282c080c0645e0002040c50742d0160f028203048007034602228070f50140400195074016007801107404a100a00008004401030101580d200030504400b141445d24241c205280c11019041a0089407a0400a11895030782110a5005102d0200203116940910300461080c0b50705001c0d07100d000b181440010b10070341c1d0071000c1400814028100304142c1ca411390040e001c0c400d0448280511900c000c40e0725038945090b00d10024030440c000d000885d1410b150b07646030b0a03900c00080d1069925107103d20140403e41c140515881801c8034000b40c246001c2e140c2000341215490480c4a0902100c0d03013050017003550018685020007210346480c0e40d00c0d21020401c0d40c1c0c03511a40d115101054a280a003024240e206480548a07403080e240c00d10a80c83c60400c01401c5010f803040e030708810000c0703d40750020014261a144005115040c01442d00392a46d5000e81c490340301c0729110001c3c200c10401e000c1c0109004190f1920301d88220060000b1b400c2c1480c003004a4041c0313 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 647999226 1250 647997976 647997979
    0xf060109030807050102041e06030b010206100b0903010b03011a0109080619020c0a0204110405180f060607140a030c020907030e060a050a150f030303180c0e07201501081b 75
    0x108103c410403200758121409003061501c03a80300c0f0509402d1030f082c444030f0703400354000007820000128080e5000180240c01030392100c6613540e4181c1041011034898108640f010f5040d92180d42e852034584081c45030304212548980c0705000b000e0180e001400305950383e070010819620171010828440d2000c400d02103c518481005603413819114001031400925410181d4000c0c500804020070246400041049800903250080452054602150040b00c01c0b1009058085160006000c0f483d10900400a0500c10041c20880d12204800c1c0c500e401d40411003100802c1c400c1d0b05440c15840c120000d16403090051a05000e554030044400ba1912030140c00410b209848401180b0030201c1900a550f0b0301440c9411010345070b945244461601c14244026804a031070140e402c1c900540b5000b41c039050982000441040d540b40448035004400010110010040d559440c020202e1486c0b6561401c882d181b40201903181a44104d41c2c0c841006920980c52a8007440296276281c1c240640c03590500c00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 648000476 1250 647999226 647999243
    0x20f0304211b030e031f1109060d0b01140408010606080a0b0d02101b030503150105090a03170f0a120b030c0d030825021f02160b1906120302060f06010903 68
    0x402d4035090ba00c4881c4518600c0d450f00130003140e140d45041c0350061059060071058103014800b03030746100c0a0248110751000741c10107820085001d000403e5007285c61141010302d0700c0b180d0003074060641c02041c1c0103908520890f07512a40204003440d400010345130411105401000081d61010010700344229101c030090003601d05002070924140501c1d22014214140084051202801d04d0b00a01035441203404c0e44c2c0f140100b8022503031a51082c019119102c1010385a03111f094156142d0301e654000c5490340740c0651104026405440710041d000d4000f00401d40c070341e81c10001d114414038041d1201090103500903400818008030075502c04110881c82501414040e00540b1061900200310014150341145e20344501c0d0311004c4d495000401428048490f041c040c003140205c1c404200b60b2042c0a100a0014189040384000c90905034020ba0080c0501003000480c1864000313080680c1e1040e404803815840c4901410f081c103405118841d0f000e105540b51504526040c00041e11488050101800510 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 648001726 1250 648000476 648000527
    0xa03060b01031409030c0708060105010503011e03020604060914010315090e0c030d0e2805010f021504030806010e04110301031101051e0405040c031a060c070504020f030421 76
    0x9000364054900c1e185000e468490f64608450740725542e60128000c45400e2040c00070003e608203012410741d0607103105950329461030b440c00500407000049140e41e02c4240038880c000000581e1007000031b100900c080c1e150000e2240c92311811400c4034011540d135506050400c1144030b10840f019080000307450304884005072a02c0d941e075000780740a403500c00b9141c0500c14030702c24000742600056001d402c20411203e5601940d10400040100000b10f00141d0b85900f0300d000a010540c0166460703880025240b04860052040110194406070141c07801d40205031280b00340805940d103c440d0511a4005442c18001d008010a04403110b100510015242000e002c8803491503a105408607550007034901d004414001c84001c0300c00240e4171610895101e5031605907004903240c000c2c040c548800362240b20300e042c8004000700344606e680c40b5540048240c003031104041b4196580307202a00c228040d030311345940c40307190a1800f20541c12078800c00c1407403018802110f01c5015448000074030f005486210b216482e0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 648002976 1250 648001726 648001729
    0x1c02010822060e0106050d0317041713050901052d061207030b0301050f0f16090b0f0d0e0102040f1703120c0d0b10022116081b0106050a03060b 63
    0x71010140945100910503407090141c079410004910400800070001a50359a040005440b10101c00a0114038400440e11038005509220703070b4854000c4000906801c20040203138030560044481301220303200c010013800b083c1001c03550640503010a41c3c13100e00948861040e05c4007003c1203103124a00480030340030b5440e01d49484040d0340c49040324440d10000e80c201510301502919140142a0280d841c100010b000390180b41e10940c050b42000c804103034107450304295030b10140014044102030100030540050001001c4000340b00c0c86801446544e100d0f408614002d042c1ca2000c850f02000c2d0780180800c1c4451300c01c01c00e0b8031044404000101031000f501110171401d5014012112030943c824104003c00803201070020200854003500c104442c3c820701b420810021550703201d2400603030000c02d600291781c1503052100c6100400b07030140d504045141458601c0c5101e10031080b07481040215003042c03140300c9554400d07900c52001000b400113900b4280032803aa0110707440051700713440e102e40f03450406 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 648004226 1250 648002976 648003001
    0x3180a0501090e1003120c0b0f040209060f21010c09080d080c0a0201060306020a03050a0b0405071209020301291e0d110607060923071d04171c0b1c020108 68
    0x11503003e500b140043c8006e0b0b10140400c00e04840684200c2e403000001145054800c01c80c900c56980107142250301d482d40d01c02d00003050a004a5150000e803010030340800161100c149c01c0c038481f0700c1c0340086202c451240f0003c20380c18980e804020707940c1c00822124141608402843c1d032000301061314a0301d50403208000c034003410706030b4406840a480051105c0d6184e6068106034451500c0b408188480a1114180411070340201c8048000070300d0050300404044060700b0605010340020004249014009804a208000e482c02110030301c03c20b01c52250542030080b0001c0403520304070340f0b05803140340040210b00030321820a0024844100c0000700d18035030341c549060316003458004402308642c072402c5c0341074814203240071882c1071960450418a03030801c1b03000549400b9104140d0008010600c00303245140c02260140088031441e29150b100700c41c0d1014030010b09442c24021400a001040c502c141400b20703802010300a008035140c5140070740d48010400b44c40d068590a02e0850301d02da8a03401c64031034 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 648005476 1250 648004226 648004229
    0x7051e100204060207061b03020601031e0b0a0c0e1e0105130816031b0f051c02150307120c0e101b03030912180b03060414070203180a0501090e10 64
    0x103038140301003400700e40345600103510025a02c160322a22a400402500f80540d042c00600080040e885040180001003003107240340a40500203208140302034042c0e03100c07079501e941100e142c40c90300d58581000700940c1e0700051b2405c66840c02e9030444622502103018858010260340b0650500c44000b070b541403042005880c3c14000d025000503540c03100b5105e401c07489505024031040c0d910f00104419429100103000e03000d011501c1103e902c0c44554580360a00001c00c84840c06600c0c04000e889031000940c40701010030040e0700030105183d6070792030896009010040c941c4141c10038146002080c1c0c0c0e0711034124001c000d09020842d050171940f140400200c071100101c2d400a4114000941c82c4001c050300360b0003122540307120b0010001c0310090444100e9001410f40b004420011480c4820440e440e4600020b42d0440005000818020040590780c1280b00d025688500103900010701911008460401484200300840d40440b0381498440020004e0450340079a00841e894000401d04100440c0300400 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 648006726 1250 648005476 648005503
    0x6060d020a05160b1509090c040e010605152d040603020d06091d0106080f0c013204030516030b1503010e071e06030204150c05190b150607051e 63
    0x83c0580d00b03c2c600089904029100401e1400c03c010700b0311401d01d0000c01e09032182c28448001c0169043c181d00700001b804042e07880301e64a5580d0400840c540c3c440a2070400395184a20103c0e82e6021200307504a101c000804284494270342c1c4512007000c04070070030122800c071901c600d0050380340d80f80c00451a0050020750f01c07483d1114942003d68034403026182e81c0c004542854002000b40355507a5601f00e442c4c0b008100e031411660010041403c142d805444000402584420706130070400e106052405080942c4070104405d4002080410401004110580145804031054803200345140d617419207240e009004000881582c80e440180703074138250303c28442e207940041102c1c407499540c40c98400503c0141108404030755000d00c08505c0314040e0084908841079501005148040c00b00226a16240e10404451502030246101c10035640808001c9482d0b0052003003510b142452030ba0f10440042d01d6003164020f0400b4030030b13080032840204a20090340c000503034511800303028803030040c1001c00110403003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 648007976 1250 648006726 648006757
    0x15010509040510090e06010f0b07140337171b0f090103150b04090914010e2b0e1003110d15050f0d121b0f0507050906060d020a05 57
    0x107100f0701c00118640c12107200f4281040301c02c40b600d04054a4034070034002c40c00854644007040160038204001402030f80d0040c6040902154030075142d5043d5440b001841c1020342d90100084d440d0800414030789602941540078205422815901502c1c1da00c191a59803800700300200052000058989406a900da00c540703c3e03695101b42403882486504140140c0740082c0c070307150303995130003149a99001007075514014a03142042c0c600705401c1c002e0145030200700d9403081e1441d00101008824041c1580c0380c85101c01603c0f2030000000d4041d03000c641454000c03880c01c0320700c44a00060b60406510001c1030030585011b50320746002c201c1074000d071200c14060510400300207078100c03020041d41d01030000d902003202d00c0c02e03800703548004000d075503035542c003606921020030124030000801c0b0445a01840c0043c1c24000c641d2170381c04034a082c0c10381c3c0d00320058882c403042140400c200101032003160080c2c07404451551840c2030000204200307000d03003940000b40c50760010f20005214054016145640c4e94030300360 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 648009226 1250 648007976 648007981
    0xb01050c150103110a030203031c02070f12030c0201060f1403070e10080c0a03020f04020c1204121a010303020705010c050109020915031504033e0c01020d02030405030303150105090405 81
    0x1c03103014000d01c001d4071400c04070f000a10b5585007550354101240e400400840c18620b0f4a0294502128182c64640156a00700100800903250b00031034103072a03000b5081e6041c0c0160301103001d01901c803e03842800869140000c03e01c11300c81e00a501f1402d581030031001103600d4400b80042460a0301640000082c884c0c40801c12918500c014140010b03108032005403140003005006111261000d070000940c0031b103411122008a0030325a0103001403100240490300000d08804100d210303a40236801c07400240ca03501010b9414805181120711000c82000110a4290b1458030025264445405076030b041000d804038401c03d00c0400d40082003280d40091803c221420245029420200c800c40c0c4180640189044d1000800003030680c4c502c140d42680310b102c405034401a412440d41c0102c10076803411000c6000645040d4503400e9903003800f0003848014810340d042d034400a89003a458110b030a04560041100b8046a00c0200640e80c03ca4003800c01e03002000ca60100680705406024003454200b840c1504 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 648010476 1250 648009226 648009253
    0x1060e0c090a0b1306080c070f05010f0c081005041e020f1b0109150203060103571b0501090c2102090408030c0f0706090b07080403020c01030b01050c 66
    0x500c5402002c545503807005a4520003000c86004118010302001e4102e0410004140910b2103150321089030400710b46040c20703d42d20056010040f041c1030380c0d80e039903886e0032020003d114400d24042d40701c0c034142012103180c003142c1e9000b000070074081c036401541c5401c40c0341003000364149144841e8807404020340d2204081070007549250001c51350b61494890b020f81a001d440010b206250703000350461540d01c2082189500c000107035101904003810141e603072003100c07080c0d80c94443c0b9013481034540c18125032088000c00d06d10f104800d16000804401211814107100c641c4101003580d940103039040c46a0300c0c000380005442e11458010b000750081d400c2c50150713010040e03500c1c4010192401d000442d15036403008a00c821905540220080d0068040300200e008968554080d5034440c1d104802d00b803405215141002d000d82010308101c1d00135417540705034400c209012070003952184461801d40f03a20714207a14000c0d61500e03248000b5060655615009125904c10411207109480304001c45000500f110f0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 648011726 1250 648010476 648010501
    0xc0309060706090f150c03050105030a0210140f190e010f03050403090308040b130602030307120b0a092306010c02100e15031006030509010b280302150408060f0405190501060e 77
    0x800d0040382461b1454060209000384034040c10303550040c00034050501580c0c240100610b410050000740544542e80d050640392800040c0b0f02c40703008214060f142c141600c6400094400d14200ea018006801d82d418540e0341d00082c45840704810745004941905d07103040545105d40103400190a16a002402040b441c540800900b03030303480d42d41e0311400c0c183e982c1c2030102c1e240d01096030800e0014489410940812040350006400702c0f20041440381200e90f110414021510702000640380e00d00703401307c004d01c110100c607240d0b44c1c003034002c3c03c007034000c1c0e41968005080c0680d14241e10b428011040c1c8a12105d0300c0380c2c100c0c0c04003500081c9009603681081c0c10501d614036014401d820020b820000000d221031410f0144101a00024100c0d5080700d42030103410750300c109149849064014940310010242e40c841c902e54001a130089101513a0b2400c0c1902181041c0000300b81101c1c100079001403000203003000841442c50030300e01da0800035074007007441d040d07001d002d0301d0340181d450f85e20300d009005000e40d001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 648012976 1250 648011726 648011753
    0xe28060503040b0a140112140f0c030f0109030503040f050c040504140708072616030614070e0a14060708030f060f090405070519090f0617030c0309060706090f 70
    0x140e20310780c83d035510144a00203840d098081515070f1403032a4010024000d035180c1d4403001c14840e604501003c1c020301fa0191a2410020101d450341c0c2c0400e102c5a0300c0c1c01c007401003c6008040c0c000a001c001d07510b8402a1175403201800c010400d11840d2400300601006201010740304900800034016400c2030f040542e110000c00c02040c030f0b217003d03800000a05c19000502c0200320746c1504444e01c00c0b022014401146490203d0000c500760107014445480b80700d061003520065841004009024400801211340d0304a00a140d030050048000356691543e03115081d610458010f09070070580300d4012030200b8808e0040d886e0007061280d0100602c5001411034401ca44910b8085d1021140302c0280b00070000c00240698001d40180c1007070402303015904081d000c1c051300c40d40708903001d0161036541c1c0c43d0100315428202c80000c1a41e480300240f000350000e40c3c140308600b619100075400d00d0700b88404145c803071280c154418402d86001a01504001c026002514120382044d0784a48041075401c00c7d140141c2603 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 648014226 1250 648012976 648012983
    0x30604140709091a0402030f0a0507030507062124080a1e02010f0804081306080609010906061d0a05121e070f030b07170109200306010e2806050304 65
    0x20310a001c00c1c1100340348141c81c038407504003c840400c1e086580700d8824000700640140e1f018040d56600c040004401c10a0717282180c45a0002e00c0c1c81c03455814002d0918a0513027010080055030b03141820b541010100c0c4460b0420490303800504055203039100800d011501d5003480c440d40c203500c80001c8a50340410400c281c81c0c0103442c00003c9100e01ca0340c040c02441c0b40a00280829441452010402c0c402c903109940103115805492400031010084520343d1110741c00000000c024800b00b1003642019031360b10b40108140b900501286050043c041c1840050004103281d02070340c02100354aa0741c035500e03842c0c010300d80075000c030038040c64007201a0740760340700b08090495890965034500e100d110001659000c03240030509440400f41195184904484080d009004011100c10321401c07260b0102e0b1043e0007003038100400103e0324125140c0213480300000788400b0745400103000f0094140d03000b41020622030421a880d0341030a050100070503c02044003078051071800b02010116905421000860041c2d00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 648015476 1250 648014226 648014233
    0x1305030105090f070b03100b0a170c031608190209011e2a0b0703020a17100503070f15030504031107030501150504020c0a02060c01020d050907030303050f0f0118020903060414 77
    0x1215240e6134000e220954691f2021403080c441040909540070251445043c6480c05428500114801c0300c00d03101c06554640b450704001041c0300159406104e2203442608a0500c101c00d864200c1003d0b644e03c07132002030480070700d400007a00f84441e8410091510110813003c404107106102c07450040442c0050012803100d4260301c3c84590006907174a10f107003501e40e8407040144999942c24400c40180d04100c80f02e10038010040100304034490508012032080010711001300f059480c00c0b040619002c1300768030510259400002c207200480e00440801e14042190030082078a48852030100c801c402e08d06070440c014010707441302108005040d00b2840c0070047c04400340c41c555482e442040202d10400e01441d1082e0301400355180141414405000640714607400107082c07241543d9210150380c81112006803e4003c2c0b00b09000701074045c4601504019290314031000d928110705402c410143c1806041004600c0803540145000c040e0100c80c0192006000c0c1c46890a00e441e0069114001d101040310500 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 648016726 1250 648015476 648015479
    0x301150206131203020f040521010b01030c0c020d080c073302030901080a021c061502010912180b04090c0f020d2304050414040c0501091a1305030105090f07 69
    0xb410300c89250821508038100506203108540d050300254081e03001d0b003c1e084020301000880390f49255904001781e0a880c0602c1020700354074120360840c1d0100c045641803600e8510425115035120501e506210b5064030800700c00002070400c650b0350700440744190610301c60051b0105651254a84011601c00d1441c440400e00c41319040c0085555003807907003100183c0c030903c0240107941c885c2c400c1c0354005115410040c42c014404000d06041a02502d0030346030503071200020401d8421861000d070f090f0043c0d100821054030140d581c041e41c40201c01c0361508000041000c50140e0054590702e030002d01441c01016900d564402c04000900a03c2d021800418400b200156540c1d0001c5100169641c0c90341d60341622aa070816103085209c506404200c90300818480407401303881d00c0c0709168154074011807000151a05181c00003051039240c008a04002c08100c040011050a6542e401003900224855440d206405200f5600040030b40c045949036007440c00380090303c00c0c00314002d46200780c0f80040d1203445 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 648017976 1250 648016726 648016741
    0x7080f0309010f0f11190308060927030c01050a06170106060516060b190f0b07050703060b0303070606141203040b090d03050c0303190507020f0c01050c0a02060301150206 75
    0x240500c1e80054040303500706604114051082d400d0f280112414101680d80c2020035418034900a201e0307800e0b4038002c1c3c886c4889401d01d0342101f4410742c4000d007240c041150785401400481c4c040e01c050f81c072041840f010601c22030b164800b40143e1b8401e10080b0300803c0146020310460025004030b1040008901600f120145109010702a0109a40d40c40d100e06207403800540c90594510780210095900c0c40e0348503a0400290f07600c4801c0641c420364402c5d01c1c0899424403481c107140f5449640004112001044101e00203503001c29a2400c49411a00000b04e804008020a04621440c00300603c50707403800e100403410034041244140d0f0203100381c51500310168440912582e030b10803401040c1c00f4940c18804401c4500d85650ba090300035101c0c2c600241009254401140fa641040c0c3d00424407041c44407080d4422209840b0b5554010b02c4c0703100030890100301e08082605c90030000d504034108035000858906003e01040800000e039400740c040e5641b5a51100802c0c120400400c1a5005009690218010 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 648019226 1250 648017976 648017983
    0x4110d1e0b100509090c0907020c130203010510050403050601030b15040c0305150109030b0135010c2c0409060b060703051305030c01050d020a0e0a1206061e03060902130e07080f 78
    0x608240001020306c05408010080a400000c0941c81184500341c840ca06035200d000d5910302e84603449201584030f505020406c1000058201e42d182000814032080021660014a42e41180d8022000030384236200c0c610200c103151814010301e90041e0810101d00300741d0f50315501161040e04101001000b580e6110f00458408506101c0542905180380040c410900d0084081541c1091021a40194a52540c4004202c10b402241144607517540e0421100d00d500700295078040f0508184264462469400e044110740b050722450f8080c80e41c0c1c8a04100f0050107a002c0c1a4140d80200181d40341d900310303d0001c00c00d90241e02250003c030903480c0e00060604001a0741c10003407405845050400103692140d40007500030802c4902041036020701c00700c1586841c20004041c1401074840c503000700903401c09000b568100e50000100c40f080a00045c101c450240000041e290300040220b640d40c40c0f40001012280b504d071500c20340d03510700009000500380005140742103803c04420794490240f918070740742d00c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 648020476 1250 648019226 648019231
    0x70506180d110c10020f100504150c020115080a210f0f0e0a0e09060f010b030112050a06050a02040f0602070e15041d0313090504110d1e0b100509 64
    0x19158400210244000e0007070b103503040000e4458044032000e81e084400140d056210401640150308035501e565800780b014401d0f010311041e2060248030341d08003a0384424116507421592400a41c0d200603030a0342c01c1c401c0d0400d8400354050603c40d01081d07101c418068481000d0902140d40c107442c0980d52450807a0400c1c805400308054517061324140c0080026104443d015244000700b12484001602c907640b0005e244001d401981120445464407241e074902d4440040c05042c0300701018801040307020070341c0c4100c0b41034800c007003040c3c0c44280d15441c1242c503103d00d4586c0181542c0c108020411885004d501400440e10348600c1082020750b10442030f40ca0b8803030307406040c840f04455400a16061010b0075469004e640180001410602240003980d400c1d0000391403544a400014501000d154001c0e13008025140400c400c11030f03400c150350360903813030451400d00d50b00031040100c410040c0069040c3c1c460024844000000781d03050107107400030302684102c4c0c0b001c0305a001c001c00801c480c14120060703031 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 648021582 1106 648020476 648020521
    0x19020f13020d06210f110301020d0e030c12040815040206070f0f11030c010804140705090a0b01080c030c03150301290a1a0703110c0a0b070506 63
    0x50718042c4d40d0390307461180b00782803610085040b400d010301384e05901c0380d060030340450414042030180c0205040c1c201d8403031400606440c041d04c0403009048004246c401c3c1c0702640099411200d15000328050041190f0080126400740c0703009080894000e80024999070a2203103581d5541c618603c2d0302c0c4103c030034800c1c2100540070850288500c110740407044002c1c0c0810f841003c0000c10419000300041c00301250f94103245c0945106200c2c05001e004098619812440d00000303420142442c440c9c5580001d10100008400d0450402070341c0c0544101190b9038550348ad40c498045542e1070202d0341d0340c0e16540e55103c0c140340640e0340e001c3c004010005040725034050018803c012061200d54000594070621041401000d290b41c41181c000540c50b044c112044980e00c0007540c609402a804c0b15006010050042440746c040d0000d4407040e80b04400315103c6548824410303010944401030b28 = true := by decide +kernel

theorem cover : BRFrame.Cov 647841726 648021582 := by
  have h0 := BRFrame.cov_init 647841726
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647841726 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 647841726 ≤ n) (h2 : n < 648021582) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
