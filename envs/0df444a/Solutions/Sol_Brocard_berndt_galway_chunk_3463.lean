-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3463
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:43:59.847896+00:00
-- url     : https://prove2.me/submissions/2148c02f-0b73-40f6-bb8a-65826d32aabe

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 622661870 ≤ n < 622841726 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 622663120 1250 622661870 622661881
    0x303090a1214070809030c040504260d09080c0708030702010c0602071b0306050a150e0114032803030605010c03091707051e09090a0302030729090c03060a11090405 72
    0x400c000c0d103003034030a024070b5a42c64200c2c1c149007295030403105550b0300c01d10416821400608090154500955000008100141740ca41e107601d41e1b0080d884c00b042161034140b0569180796401d01641e00c100c1e00491030151b132841c0428609050800c03e8101002982c810040200140d074080d504c1c029041c0c00000c0141c492060b4a401c1c142000d00702c03565042e8550b043d802006000d42a0710050060300081010054a011004181c00f110f460f481082c0c03035550b4820040211201042020310303460710040590705003040810602400c5152085402c418a251001803002c0541500c103480103444c1c00d08180041140c41c0d5002002c08000d4081c07101c200a0150070001c01031010031440025010081610a1400704100f68020046120400510480311100800c0c01c0560105280c100545c08d075024600d0a81c4036264000d01e06924040c0ca8081c000500c0712a905900d1b0440c01c030b004030340f094050010401103c0c1050f142c02000307085200d241380b07050725a0403aa0040421140180f0060340c021130542d40341d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 622664370 1250 622663120 622663127
    0x50a0c090807091515020714011704080901270f05040e0c0d06110a082401051b0705040c0f1d03100b040e01020a09030b010e0f0403050903010b060409060807080303090a12 75
    0x1c2c0e43c041c500d0070111040010750741d9004503003841542d0342c0340c501c581f08c4d1240c100111101c2c1c0d0040b11141c40215030710003190200714114001c1c01c080006041030011404681e1705640f81810034600d800301c001c4403200074458404c00304103580080c882194244004a15004050740742d9416080703017032040900088240801c9002e4000002e10000f55120383e440c2c840011001d80b6074035003143d1103036013000c06a151301007200155810f43e1001e001079550301d0800e04081042c8980a81c080c408074010b1007501000103ca039924040c00c01d0020099444620001d00000702619103010030052400001100f0088003044d10000740d9410508010480130420298a00206004000c00d041b103022a500002d007034007126820010210859201c2d4089280907030b6581034a0188800c181c0301081140c5c04103010401083c480c50203043c0403400203000240c034405140020303080390310a50000711200d07211202000314610030300a20b8010142080034524515005030501e86603d8810030061140100540d520b02d510312 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 622665620 1250 622664370 622664411
    0x40813181a1c02030a020a091d0a030e101701060f2d0f03020f0d061a0702010917100c0f1b0b060904051504060b131a040513020310050a0c09080709 65
    0x10050f14000206494148c500090692200035000e00d42a803004000340000004403030169a40559403080e820b035045080000e400b425480c032504000c85100568540c29910001900a000329110121380102454010b4a08a0304401c03032000c221041103280702040c0c841c460350580c0d0300c03686000d08140300200000e4000340240e4080400141000c110004080403e07070103141503480c014800c000c041e800c150000c0ea03900c2072a000a0000e1001d10302005005002000703401c45802090a6503624031901c0320880c02ca802180c4d0003000a9068a07000703455580050250590462044c2c140000040c103495040000c480641000c0c010501c04001400703002c2c0522420900c980c4e00c0090181d2810a401d1040140c618101c20324421141c44101c0d48070038000740306000500d580d428070901510494410000140350080c1007111014680441600503030f01404001c00e01c0b124110001014107040000504590b80740300190140988400d082c0f00142d00003a0140454000c3d0700046403802001304180341c0c0c0d41 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 622666870 1250 622665620 622665623
    0x1e150503190c0323060307170c040b04020f070c050f030706020a12021c0504080115080d0c14010f09140a030c060f11040b0c0f160e040813181a1c02030a 67
    0x350750549150b20a000001c0d034081d1720104c04840c040c84e1101c2045142144020309486503a1015450750314600341034214440d1420014001401d110740d0440c00c80555001010850381050911420711480c5041401b0220840c0140c2c003c00d0700d40d007000c0d0f01a503588000701c405450b128000504031425442040788803050784c103645080e101c1c20082800500a504180524074030b550821194581984c1482d50700f000b04d40443d4024007426400110a60309402c0c04501a07882d19450403000080c2d4409018000340703a0841480003940d14101e0511801285c4503540d1488039030444814500440c3d030180085080a4012000082221100015034020241500000903641000c01d00082c5400940081d10710180030700103a984c02c45107584486e440304038800f4844840e144d50503040c8000038050b642254002d01c1250090300d41800c4003055212a0380c2a40302c214010811030300080c6250305800f074062100f50260000003220f808400080054122045041e010601c141c02c02080d5903040200c0681c1c103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 622668120 1250 622666870 622666901
    0x1303080f0301080d02061e0a09060c090302030708030712080a09020307091b031515120e01020406090e0601080a2c01020307111f0203101e150503190c03 67
    0x40c0521080500a034209200d880d12600620603103000450021485a00c141e06481c05040c0c40e120203680c85a07404000307003280c02c600c0d64603141d44e400501680b140302c16a80c1c080e00c500990510f50b1042501d0040960003280c3c0f075030814802e02c07002513480c030074081070307000d1a0801300401d5660381d800c01d005102c0190040e5062003000c40001d010030196220315902900b90414010001c41450254140ca000f8a4000701041100c00100040c214501c1d1182040c261880d0003442c40816200113815182c8154400e60f180c0d500241c1005182c0c4c0208000d00102040c41e01c0c14058902140082c008410043c142c0008075150108449000c40c0d18500410a1450f11101f10303070100000b005038000d400031207489010415440a0700880ca0001500e4420340ea41010310a4600c4898492800650000303000404d5030180c200300442c1314404181c080c019901084d44224245103441070b03442001a80e560304000744101041484110582d40004408505066801007540c2111080c110003d21b514040c22480 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 622669370 1250 622668120 622668127
    0x90103020a05121509280e07170304060f140717160c03020306150d02101808010f0501050a060507030815060d0b150909371b0207050303090402130308 66
    0x18090309540110710513001c1c0ca102d120759a41d1042102080c400d0381d0820940103480c000f0064407049a0080610b00a00409580d4440e51710440b079155591518000c0c1040e800100e002e004070703503201d16401c82d203409616110204201000500100c0e11a980b805041c01d02c6400b46001004040e0044030450440c2e080125180f0106007018520f10500d408104c5c440d01441c00031410300f09030070701d1082201c00c0062500307191801640c2000740b0b114409442c0000e21403102d664828424481d9070320700081546038008100e0b020b480140c5011504160071440c40b40c05002424000d8903400000d803911658541071414040d00c55109086407140c0c00110958404400640850351107203075001102d02041c266100008040c0c000a411805d01036005a15005208070000aa0814803500c234258041c415144030345440000c07100c180300d50b03100c58400030a59511500740041c081c42c6c00361000240030b818405000d03500e04203070000342c9911038000c409100d2500850310f030085003034804401d001543d00c08546940c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 622670620 1250 622669370 622669381
    0xf081902010b0a0e010510030b030114070c050706030c050d0c02100524040b2404050612010303020c1008070e04020912070602071d06010f030e01060915050301060803090103020a0512 80
    0x680410a102030060200c500d000488881c4013503654140d440c010900c2d84480c207000401c030010007400040701d61540d00c504540304800d807914280360040c11156541503e142150034a40e1900038190300078401c240c42d11800f40c1009502600f80c444042d000d11010603071203400c0e0400c07490174004003513008030189080709101140c9240350304461150300c090b002c21045c80e094010401142d00e18040315030400c030030b00d4102030100060b00d401801c00c0510960350b030070a9243ea011441c030f504010703209102041108018400c2c1a010407160001c40301c11103208060f1542d0650080030b00b900940307410140030a1308044030b541c2c2e80e16010740e10b019901801c0e80203240d910210466460056100b0396026024407040419802070302018500c101242601d64081c03521841e00440f08500c200c81180109a03907040d00190440c404c0c02000700034020201c02090030340c520200044240c00b15400319109030700d013103010008e011021007910209403090900603161030011505440d640b140120340008007804008000d03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 622671870 1250 622670620 622670623
    0x5060703020c121c03020306300109060b0f0f030c121504080a140406050f0d060b0c011b0f020c041a060c0318010c03081f080a050601050f010c020a030f081902 70
    0x1c1c2e07102c440f41341c403440c404e0142c40290220b20080e2605500600303506101440700b82c0b80070003008980341c034207a1010110203807844942110400032040b0385803a01c83c00ca5004c1840c0010103030345a50000c44203031501d1304010303001a580741044150716000c0c120075080714260b84018081c01d07541c2400d240e041402407602d45006030b000c1e4800b0114201044800d11400c0d850340c40f410541e02501e10948501c0c1c6400021080c0039000e4014517601c4420585900c0085010f050141c0900060510100003160030720503040c100c0c5040c0340300320003a01041582d90140c40c80c0c0760700003881d084d941d03010798002448001c0714070200040c4204000c1c0c42d400c482c0004646010072800030007008540500c0940e90307142c440041c0110b4010b055180d0140000340700402050b855200402c9035480070010b08140c004c0c8650b034004c6603041c04000d2200380c541c0c2c0c004000420042c10903030741d0171000d245c00b442c00d916030034a10740c0000c0d2003c0180c00f016008003815205a8100020103088440345a18807081c41400240740600a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 622673120 1250 622671870 622671883
    0x1112041112010f140703110304080c210c010f02090607020d052401030605010503210c01060f08010207031b020907080c0c01020d0506030d031e02070305040b0301090c090f06050405060703020c12 85
    0x90303440313015220009482910a20071210030544e14050189140c031503448000c102c0c0c000003150308460161100380440a850288500c0b03403000c6981c50561141d601001d054211540c2610041c0c80c1801000314a2450703a402d000c9860207941110500159141c5052030b901e040745080c0030a9058800342c04d00520001440c002c503049034440d900500c03031743c3e03264824151261581d038a00000e5101c0000e01e14030722240d00014240b1245e42000000f01f940e81d035500d0b80041c4100d0b034440500c50750300060520505922902590048010765558014a051580458a010340003480b2008000790880032400c40b01f180030485941c100007130003c0d0344483d4500c09441c014441a40c41070301c40e10404a42d0101580280100440041d058081104031a16507280101a40c03104800301c080210800005c500c4840050166005c0c10b604030000500289030400900f0310156604040c0502d03403030300000c01c050b07603200c0100c1d42540c03415201c45840342118034090349010801d10b0410741c030503c841002c281800d00051741 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 622674370 1250 622673120 622673141
    0x10c09080609030708033913080106150309022d04050901090201021c0e0a0906060201060b0403080904090c080a2a0303021504030c0c08010506041112041112010f 71
    0x40c1ca0300d80d00c441c070307059030b992181040c001c0c1090b40034400611134852502e400c07000411503102e10b0202040404428100314200300f0b00319181ca501042e400800c01e10002e0800c05051003900030070245041c03120403074403040d0502e403103001c054648500304215100d10f217110170341c41c12681082d140b9420031108620407418801d440782c022440c4c60001144840140200701c0c40d2501a0040c00d01c0001c68400341c03101090f00034000040c40f400703a000400075210704002d600101690000041c420303080c0b640081c25140c441d40a480040c4045c402840429081d8045500070142260000703402d000c940f0780782080c00744075031010001740108030511060242900b900d042c1060a50aa040292600f5080c104040d41500000d40141d0214000c4052072a0880026070014003070b0411174040d405c2560303040343c42e0703119410002c405d9454109002590410380580a121584c0c041c119080100b03c6001c2116520014000790815120b400d0602d59600d071480d01c001c28480c1d45c4000e00c2441703103c0340300c0c2003e803000104 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 622675620 1250 622674370 622674373
    0x30403020c0301050a091a06040e0d030203090c06090307140d060c08060a050603010b0a03180203030c1c030908030a090c080610050f120606103c021501090c0e03010c0908 75
    0x741d582c80944606c82400361700c0708101c405103030807581d01da4440400504890700240d581c5d010b071552513804c0004541030743c507540c2d000d6581d02e444140365080040700d0341513900030301d014010441d80e40d9001c600c80c000d585940c01c00c005680000340000b5940c0d0601000942000e10b04080401007580c0061202e110390760503589444416900c0080c400c261000344203140c000003042c401101da0f24070036040b003d00c2c0304c07407480070b0950050729400090440e8011900038034642e001c100507144542000c0c1d46009181321908080120b00182e46070303501c56101c000c1440309000d80c0c85d45100300300200e40360204c01509a5004403019480c2803100280300d09030500070103100e0040d95081501c24540030341c0300340300540e060001e032103c0e8441c0c60500c4101c000da0002802841058a594526070760400718160302c8556003a030481c00b90000c8164400e060b02904444003c6400c860b420b0000079049142c41411680f4448001941c0c41096100b00c8185140c03801e0191b25500348128588003540c040e01481c2079450a10 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 622676870 1250 622675620 622675631
    0x4060504092d1107020a090b01080916060c0302031201080d020c1504060c080d020a03050402100c0b0609060d061a180411010c060b03250f0b0702090a020f030403020c0301 75
    0x40c003203010303a5041a90103141e08403a80c80c41c407040025048059991591110f060424007a41c0c0001c90900715a0056505c4d26a02c440381161036a001c1084c680096441c0060904091070192000303860403940656014408580010340c03c140c030800c2150400c14080701c280030107586070801076480e42140e000c058010700c500020049989071980a20300d080c9415a10135251a01c1c2c49010703a1041e0140c1026074083c04103102000301e1031a1400100303009000e954000805c0d01d05481000040345400b040401044440160303040002c9980d030b00d040d04202c044948400660320400010340c40020358900804040c2020740424060403e802050444001201c4480310552201c85694092208450250030100700c1a02501d40e94007a1031411100c031b0160401081ca040312201103031901c4100400e1402030000481c111036104400007501002c0d01c40325600743c00b990701e4003140e0009405820303406403088800300c001c2094119207904844203580904030340303a1a031519003006525040c40d02c150701d01950810 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 622678120 1250 622676870 622676891
    0x10020f130b03011a18100324050904060f06050d24020306060d051f17120a0215040302010627050108010e070b0f04030c0e0406050702061003030509280f0f0305061801110406050409 79
    0x17207400400d562700a0401c41d19607640d6150307000640014000d5003502a40e4820124864481c00214a901c5010360030002e40804000c204c01a20340f084160743c02ca0910620a201d49540d41c4030803200741c400c09200c04100c94856403103000c000e41c55494a196088042400000e003201e424040c40c0600b04403030107486036402514002c1155104d94508000103070481c4003c15154134130480b8654102d8001c1c0700024944d5250200394440b08803842200c0001041ca41c003006ca1482140103c80c094051700b030003032200003200e40d03605a6401050299102d91000824440c0c180a41c00c3c0a8800464202d65814180c554550b085038401d541510305607802418407001500d42e900000b90b0714002d4000f01e1204550600d50b4070102c4003a004802c059600202034465034880324854410740044c030002c82020b4080700e280040080101c44076500c100c0c0c1403c8429010404280c01158040c2d1160040049031800c000440c14180100032190344101c00c814041404100c442c0d016025000b5034030500c0d2700b08002c1005 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 622679370 1250 622678120 622678181
    0x309030e1908120c0715090801020409050a1a060301050f180a0b1305070914010309050d020609010b040b03280821071e0f0210020f130b03011a181003 66
    0x210440300130258840030040040346044410201400514680380166a49804100c1d080ea40b10750b20a0401a0300d170340a1009004503485000100c000d0b20203d449520301366804190140414410b69105481080102c0c2e203586030b0202e100300c1e0b20142d01e501c4015140001e200001049030340d9186004d482c10516560030101c80740715480c061007042c0c480103483c0c1e1800c0c0d1034140a510215000e8100754541c2c81440016800704207401116045401412113843c00090982c01c4815468100707202d94102518a0102d0b10b0100d186c14012010f00031100002d40c40c080e03000344001c020213004141543c009045501188010b00a000340603840000a01d50784408604444403803202d044250843c000090381c0308101d00030304502845040c2e900648a0f601070030072682c404c03604500c2100c803940c9000109140724104820901c8064409070390101d043d5410103002440e1819109602410460f0002d030480c0f14400004054600401c0213006198110b542e00004010788040c20b00d86a40080400040f41040d44 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 622680620 1250 622679370 622679377
    0xb040207201903150b030a050d2601142206030b010914060d111c14150114040f24050301020406020c010503060a1212080f040f02010309030e190812 65
    0x100d4911542d880750a54a914501c400403032021802d050f42d515a04c0383c0d0741c409005488000e070040e070141880080011015113001c6c1a50340804200100c06084201a0030392074982d415140e2441d0141d10200b0030101240d41c50011505100418894030101e1901c110590412825244540502030141c1d03650010202a2202c11038403a00b4521900002001420007406206900e809000305015141c10500882d800003040c07905800c5c2c00481000322030034004d05c00c20328441250030034010b0040f0710071404610b61078941070003075800c0c6001e041400100d1380c2e1b458100010b040c028507003c001056154031000301c4000c50844c4841d500803500c400146902d01031081d9070483d26240c02038004c000c006801100c45510080846a00041506c4003143c80545210b00b2074500d131184014003004d000010000e01001d0b03000380b03070900c4080000c0800c00043e02400d50400712550a00700421030110781c1c5010384420812006803078100c100188c082502c0e192a0041c2001c882c241d6098520801140c805a002c0b8072 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 622681870 1250 622680620 622680649
    0x609070906090b0a1401140f040602150f040f03050f030a02040503010b01031422050d03021b0c0d0312140405160603150302091b1801080108030a0f030e010b04020720 73
    0x8521113042000441c101412444544149810102c140c204050030b2965006501c00c83c40c1c0501c041014488240c0402c09000300c00841c0c1138a009501d0003820003625000b00038001800d0518040c81841058000c50558090302408a82a070b26407070072a400400035041841003921942c2004018041075000b8420b07140c04603010031850342c40b5a247e480e08040702121800400d441030480003103202144050000140d95212643c0159540844400e0316500441442da011030701d400c01c00328040641d99001186030400d03450b040c42d0b040007100c20503000090001c00c0301045c0500300034080000b04100441d40180b40d03280103400c0c0f0149a10746100700d0444a041031201000620004c0900143c40d14500569111801c1c031a0032a104c018140b0f0030945400240c50340303090480440030b40318a9030f00000040d001d02501c800850901c49001001441004c000c800a002d1580d0f49201100060b400e401a0020680161003555991014903109a07168101c1e400800101e102ca6120007079440c000448102c03c1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 622683120 1250 622681870 622681879
    0x2031f0e070807050c0a080f030105090609010b0d0b0402270915061b19030302030603011407121a06070804030c0b070213020307050d050f041a0705160c080609070906090b 75
    0x25070f5503040c152201e900c21200b2038194450300c9807150008007054020001358441859150300c0707500d49018014078180c080c1500340f06d0101000184007803810142a640300c0c0300c4aa0000ca800325500b00401c1c002d01c50b02100001e07280400000c40c07100c10050a000302c0003581681d00d02e846540d4110300401e04c10f041e540c810360100d4204203062503001b0703484512480c82c003000c095a4910401075140400c0c00c424110032404a9004810403660303180078842e1204d00c80740404106050f16104000800e0200c1003801d0080d207139a03406051a001040600c03000f480440500415558055410701c40c00d660000d00c000c0300c86510a0001003542018030701540c04080c0d0140c50390b060900d00c100b0f1b2502075000204a142000414403103203507000030a0140e00c0c000c24184d060941c443c14541040d00407006881400161039068805110045c4e501104441c4c3d103402046403030580e15401e20344000c0690055000758418403030401030103640070b0301058003011509609400c000c09955200014180c96104075201da20 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 622684370 1250 622683120 622683137
    0x180d050306060d02270f010c0b090a0210050c07090c0903030c0813060509092421060a06170f1002090619020d020d0c0203030d0c0c0602031f0e07 64
    0x56025201a40d049480141002d0811200700052401c03a00300801d08500c4084903400002071050107041c0c0076002c0c03410b0710403120883d106d07000642440b503003490003000c1858880015102a00500201c04000c3d0300800341181c101800000601c15000380c800701c0c0c2c5600030002c000400744205c0c460200610195110050854519103003a522218401400d80c1c0100c0e042050701032074100d0800e4003016240d01e803180b03612640d4a038280300e003070b40000b0442d4001e9603006901d110384205001103160740d2034080301c1144800405c50051515050542c1410311548034210038407120260b40d803c4001603812800c0c02440155044510700c2d9941c8007071080d040b00b80c010005280040c05aa0004e0410042c040c01da40d150074006100c0070280c035404903c8600607000344c0c10200b8055414840c0484d0510300c1c2c90000c90480c0300c0e070002601d80c4100311000540680c0d0f000c14003074660054815000280d00000b04540700d143c55501045c100e0440c041c40030340c0024100b400302e61005006d2140f03000b11a1691407044 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 622685620 1250 622684370 622684393
    0x32406080c010827060403091401120c02010902090c030a0b030a080d0c0903050607020d020d110709150308030910060b16111c060605040c1e030207030315090203090618 74
    0x3201c0b200a1301d00d030318209801041d840c010300d8605820b0125a1418000d001c24641420000d04050f502e4000001d5406050041c0845a074005003150f1036051481c0c0c0040c2007003194005900500300c00e1402508035083d8010010081000382c05148900000c00c024000080d0440406844a00120006084440510083c1400002640614019491401c020402c240c880c0c032140c2c548042203c24400507402041300380a0203a0500c0340b400c0019140c20061280b90500c2d400644948050080030b0000c1d50310742c154100380c400010307041d00550304043d0555030790515041e0180c41324007060003d049107003040000030302c1c103080904581d100207100c40303819840c3d1007590340d070404140c2c0301420320341c0140702d8100081c00160210398240101d10070a4001b44880c0b0b0042400261903500d11001c05211034141c003a43ca00151ba0121746040b1054a00140c2e00c0c0c50926094009001600391004c8605032190302140d00c0403240d004500070703042e031022500d0540c1d81020000d103041003800314961513001200b4250 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 622686870 1250 622685620 622685627
    0x6050403020a0303080a112802010b060403020405090c0d1505010501080708040209060a0806180708030a1e0c05031209100605061602040f02180111010c08011206090b01032406080c01 80
    0x42e044940e01c00f0100b400c084021102c10707c0d8102039450042d0005568104450b4203204a440310913255900003480b102540f80c0000d0498080c0f40b1000e40207d07180c0340010031460040c809032402c99001424413441103480d0502c0406281020903079100e140c50a40085050760044401c18410707040ca03507a07003080350b40e50382c280078038034002800c0d030368000d8126038010905490600c1854800ea000c01c01d99190031400c2c2c14400c0c50240b240e8002c00b020b410801000a106500c5050007400491100350b190716003d0044c01101c0c2c0d0a101e40c00544035000c00f0900c0000b00801c0e200a0340107aa11000f15105171900103146403c544a500c47d482d80403c0802010303070b4407044002200e10050005000040011144e5900d00590b4440d84014910104011100085603004407c050100c0b0441000b0409000035400240841c4810b005416442182c010754070100011500041441648140c01715665603603032800b80003660003000104408040c0004944c1c40040911902084400c0c0400a02d00d5854040054 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 622688120 1250 622686870 622686887
    0x1b07050f1f2c010207060914010c05030408070b070912061a030d0c0201030e1501032d0c05040510171501150e15040f0e010501030f0605010c0b060321090a06050403020a0303 76
    0x480300e55003e001d01d0700070a505201d99a105030207400c6c603490740840c0e044001d0031203c0e010100412f110302801800042501c91065034103560f0301c501110074945680c0d40c281c80043c0b241d40300125004585404808000c0150401403900220144580e8600013a808068861204400ca00005001410303200050361294010181d400043c0056079000c411080140110b080260000c2c1c60703a800c40320301d001a4101c0669010303400120b900c0784c500c01d0105690b4003070010b1401d11820780311384c0c1c4400114044014400300c0c1002005c00d03c1d25180c64007405c88003a0b0700c40c1086600810400d400d940001614092441e94011140301561130603240b0180b001000807030245400000b40040090101041c480b180c04940809402d1001c15001598501000181550345490b402c40c0c1d624103001040100d41d03000303407075406241c1c2c0c4252910500c0da40e08001c02d1034120040100e022445801c40344e000c858040348000c100440d400e441c3ca15481c3c0c4c48800c00c1d40c851155200094101c024400704101192007180c16 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 622689370 1250 622688120 622688201
    0xf040b0f130b0a140f04180f1e12080f060607140a0203030a02030c010b0d0206030105010c02030124060908060405030a140f030a240e1b07050f1f 64
    0x1c850380202d011450000d0642c200c0b00e84446100c0c60071080740343c100820410000c0440b003e0020300002d0151a00700441160001c050b6058402c03c00204266100c03019140240c00490300b04550b100c2c203110b150710b00d0250310300740800d41c6000460103501d100c42c80d051145002415103031130507100355146400254078541c0020603000300030510006070b800380300800c4550380a0340203540740c3c05040441350071100e87c0c9480921440d01c4081010042c2c40318820781c0c1c1150f40900b0700c01110300325800401d0142034100034281c40750b0300000010b01c2da01c0c174103081c02007034030000d03a180d501d0181c03a0b400c420b95600d4280e07406070103680103202c56110300380300301041a103a80c803108403070741440e54411074680240c01c250380159160b5103c21680c00451981c56410004010404180403190b140c40c1440071105000b0b098543c000407001c0e0300c940c000a1345012a003e990740482102c4400080800940d110200c0310440c482c0b440c1800d011a0011546005014007000060040308500b0143d40315503981c0001c0c04e40 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 622690620 1250 622689370 622689409
    0x605040305120a060b1c091401062301090b030a140420041404060507020a080a0302030105040f0c08060114120f1b0a02060f040606031208040c090e0c0607020616110f040b0f 76
    0x58040052800b5a2001c10645180b0001c074296003005040c6041441b00800327408440311b2f080100081e40e9000703008030111400407200a5480d1278542290018041c103901c5008604d5080c42400204400384d81d170b24180080c41c1d03444514440e502d20400095800440c2e103204201460000f10b0040351480d400b1580140d514011224508a5591000104c1d0054228070021030303400f00040102c2d040900030003c0b00e9022407820882c1e1240101702500301d2a005d4455410001a0f400c07410b8480c5070b42c001ca074000074961015464618190701483d251003021149910410044e0001c05100351491040c0c8621101540180a4699139019420743d2080020400c3d20106c3e00c0340d0700000480c8420050100000065460b001945450300306400d040501c2d83c00692014546255450600400300d21101d201c2011911666156101c3c00012800d000d1100c01801c4e02d04440c10b498100680c102001903410301c2541c00403c400e083c0e004000803105240c81d0940c000c2c030005080b50a0b413828405400c4202c02148 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 622691870 1250 622690620 622690631
    0x6012108031315060f050f18060a080109150b0901031a060303090a03060e330405010207021906030e0606180a0608010e070302010201052202100c0605040305120a060b1c 74
    0x1183d80108255185004580f10b40d01c1d5801c5c0300445184203144003174a02030302ca02e0468001c2d1004a882c001004440c607000854000104030a661804c05d280014880a00280000b40385400c00c804507a0700b9902c9400503d18010000049050103031946048030f81203150241c40034000f101100e214540100550340c140400c0000f525035907038048403000914090f03140061801c040b8010a85040600c0d100401c4214444030250712222054501c59049500294810044e480707914044c2d01a0088220095110450010412880c0807a020000c115140c0b954241311012603d05035948941081c0d03200d64005c1c80440760030840d2050b584041e500f0008860b00000c1155841d42010b0031204014004016500400010010340d070782402400d4100c0e01d440c2084032642e140303c0c404002408c2c43d0400a00400c030000440e09014002d2040110150b00043c0074440c524142ca0002e02c030340d0000b04071450031811000031920254061103000165550610110b10740007030b5007031700e10200c052a10f140031a161241e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 622693120 1250 622691870 622691873
    0x14130f0210120908030402100309080904180c0618060302070803220212101113030f0305040b0301060206180303040b0105041e0e0109030806010c12081506130503060121080313 77
    0x5215020505016101e00340c5c60782010320421240e000c120700042c040605250202c004100038008070380803260708a0300024110102044504009403a410240255600c10030000d58950070003103004245e002d024000c61060307114071007507049028024001d803008406000048800c16001c10b000b85002d1103059407030a00c83c050b400141082225a4000c0403030700107d00001000c030881c007e00305107200c0e0524103030070300c846004a64446007561001070580c0100b04001030a01d0b01504c1154043c00101103495520340e100c04000e9034841d8159846c4d4200004640001c024041c04801c6c0c0340a180d00020384010303070b440c010410015000040001005050380b021581034010b451182000a45102c070001c201406607003006410702c40010030f100e0600a58003178032000620214220890030401d410210050b032a568100900215003611081c0c219500042501c0c480400503126070884200302c04850003681c03903640144542009414840c041210902503c00240d40c4002456203c086644c1c0b40c400c04142c2d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 622694370 1250 622693120 622693157
    0x90108090d08010639050111040b0f0702060f041e05060a08060f040f0212010509010e041a070507020a0308030402030d0f051e0c0105010321020304060806010f030605031014130f0210 80
    0x1c00e586118085c6112204003007210a0003280ca11060302c0740c119040600e0241c1c0707000507114040c0d00c20341c07000f00001e04c10704550b580d1054a00500403144041e4907a6154002814008007001240d4440e070700051000449240800403541c0c61401a9164401d54030b500e0140310010040303c004a50003519411020003101d02172002d01007260031a8038880c403551400d001d108031401c068012002e01000b203000c01021540300b07400d14070500d00110401c142613aa0301022945401600d00c02580120007000c00410b1000031030180d07008a008900ba10000350a14000f540c0c0760b0651080c980100c0c01c14004e000060385200340c1d07840c81003050f00000d443c140b44403080500311a4244c0040381d030320804021104000710100c100846804403400110710f0282080d201428960004104604101c940300e88440780300d100e50840c2c0020100a42102c43c030070358400103000901044500c200002503a000040e00040c580340d41c85a51582100300c1030310f210501e40034414034854440603582408141d04512100001 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 622695620 1250 622694370 622694447
    0x30c0d0b12011b03200406050a170f150f031c0512010b1309050912070515040303020901031a090115020f0304060207090f09020f04150306090602090108090d080106 72
    0x144100f1030445040d25081c0070f821111100c4e001503d041c86600995855500c54045070166001c504049807520a012000c507040d0a81c0c519203aa1240c04034107002e140f0408000d203030f000d14826150720310101800810311501d00f900114542c3c0c10361050304170b00c0b194400ba4920708110219490407a01d001010036407041906404ea03c421a11070000681c1c0910007000200036015000590013400f480c100741c9840c6d65a0a601400d030a05c0c41000070301082001410421100c4108420015180b146410304019000b50450240c007400b1a0a103030070030065045500d001760381c0c00e00013480006640d0901c52400e14085101fa401405d52150016a00400c042000540300504140e40180162814448802c050703d900692127840e82d800c2091171070042c0d0710141446840102607500191444043d0700e5842c8500301d907800548400d15214641041c000c0747e400401e44181c0c20f803207003516a2507400016645102d0121104000707004040140440c92195106460708505c00c06030740718984001d840080c0855 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 622696870 1250 622695620 622695641
    0xc0a060504050a020f031501091d0604050106170d050409020307020703020904050609070906050f0d05070b04091a0906090408280804050f0706170415020f031506030c0d0b1201 77
    0x80c0a03d040208519141c074003c899114107601410520f282c1d99030024070b4907410701503944050346401c910010040c41145022451941400f1074a09043c1820054000e0016008125090780d501c8440d044054001940e0003c40d495961001e2400d071a0146a400a4001034039002c114050305400001503500e19054a00850152001c1c241d5404c1c409940c51500f08560f0009109606001b000c00c01592039041c800c0c009001074443d2940c0d25814945a0708098440c1c2100f40710b000003240c0441c01c11140c0d8051280940c40142010760000c07558200018102c046681e180d008804c800000c0002c5e40c400080c01803900d8003c103200c0c401100444000e95545c1d448800b10019408404020034080100105042415000042e02c54142005002440a0441c4d0300c21607484650380041020004070300c81116030403c40b440215140c11a5510381c11450b03206030741c0005001004500b102151422100300da000300c03461040c40b4540522428204003800c0e601036016401040c180c104002c0290a00440c642032 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 622698120 1250 622696870 622696873
    0x90d020604230a0f120213050709061106040203070303050d1401090e19021003020c030408250807050f0d02041b18060c02130b03030705011a09180a080c0a06050405 72
    0x41c02c2581d80080800110003200c3c8036143d25401005015854984041521940108030340066214004546d0a0120800440c0e401d4039010401088980c0900041c096403c6582d500121000902001d27958020a43e006503154102e1001080001d00410040c07404801c44003020568a00440d80810030000907070000802036150021229061000e211013420700002250f02c50715450660046560302803c1c0c1c04000c141a80047c00340c0c1554400c000741e6004000140c02c6511204030701c2cbc0c00c2400c441c4001c55041800e420f0920118504101044000039a01c020b00803e5081f0016030810006405444060747c12035a10481d415411686000c1001603516586071440d407100038225138100720126600030780401c00c0740e51111006988803400c20a400b4005600400d0a9035500006801d522034008024041d620b0310001d10911035060320440d550010441c4c00c1005656061140f50742e0300002d2141d4405504482c00c94400a00c29102512020303844604454500c0310a903540e00c1150801d82d41512503 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 622699370 1250 622698120 622698149
    0x29090d0f060f091a040b07080603010e0f0f01150b03190b0303070c050a060e030c361e090316030e0a0b0d05060d1a1306020d0209090c09010f05090d020604 68
    0x20f10507011031184000840100300c0e90103203491b480300d0110480140c6490204000f16010404a80d025000b407082c440c000302c00d80c0d000303034452401c00e50750b03004004041d0b9695003040d80c1d034140340d01400000000c640c1021003181ca165140b10410011818140d90a880c440d41c443c4114415101000540700301e41c0700c0d070b41a2409600740420000b04c0000b503403100f82009840d9604401c10b480c04500084903500607100e00e20b110360074521514050f44402e070300580101641041d03682680000d107000e405020f01c425900c8002c048a04164541130f0200ca81c805e0039442008000d03020a8403070728001034503029240010500680b03c00040100c0000d5000c3c41b9214004290454110018031440343c004004861005400380e455640308065080700082c040181014800501744004070700d0301d08600766001c1011551600100340c1180207410032250280680d80d80d03800220b450780941c0c00c44140703080585460f8002003c140c8202c506a00c007040041e00325440400220042c0ca80380701800c00b40c000420310216 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 622700620 1250 622699370 622699373
    0x20f0f13080d0c02061308030703020a12090308030f0703110d0903021005062b06180311062404060f030c050913022412010e0129090d0f060f09 63
    0xc290340c00040158000000c2c4650b4560005600b02a06506507141034444107808401244020345a00c5188580000541282010b50124098481078400c500141000892840803101b040c014000104004400c01c080742c000da04013200f040d0700210b1380c40c000c036000140d280c1060894000c0d1000210b502d0315543c40c1c5041580500c402446500c0c410000c0090b0b1a045000510a0320b13400105030260401c0140b111594075546025902140c0110702030240540300b01e0505041400740c01c040e0002045403101030f01410000c502240a03024108800120541703903048002c1c02c3c0d04c500021903219641c0c107400241c0f042c03541c15600085002e5252201c100340f91a003801403100c0002d00140607404400719400040c1e9506113140c124240383d03a82954400c0b00d000c1444114802c030f104501c41210488000640c8010860045050300d84031041d0031704d00f6211805400d41c00d120415034501640041c8540b60741400c1c10341021903440c1c05405280b540424a40341c5a0482d400c6503103900056498018220 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 622701870 1250 622700620 622700647
    0x50a030609050f07200d08010e07021906020903070e040c0e100b0406050d024e0a0b0a03080f18120c04050a0b03120702031e1b04020f0f 60
    0x1c0c041e4800502191418200c0300d10740610080c1480706005642002c40d1110f000090701283c4c4003030510485203508415600a41303105030900c141c840482c1c04000040f0a54070101e00c180249510380c01c04042140d1a950384000303504038980598041c440c0c0c0c03600182c800002a8900c3c081d40c054455040102d0030030451400c0c0702d00007411905066040f80342081001d030741c0c0701206e00b226503500d00ba0fa22021070710a2400030344504140104e0032820740f941400c00808050600c120710900c2003481c0545402054403103d044000612895403502800000380c1611154000e2910b00c07100900c0340368402c0e00c981d01e074060307a000802d114203000c0b00442d4008070048844c5040c40e81c43c504907a00700d0408a00c440881c7d0b52100d012000e8010b80e116400703e221511960415043c041c001425034100812200c200c4442d80c000500c140c2c030074820b5220480350558840c25a0703002a80441c013070315003180b40c110440d01c0c1500d45040c15800c03079420001400c0b1000c07210041e000c00e1020341d90301595454643c0c000d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 622703120 1250 622701870 622701881
    0x90206210411010e0a030311010605040c03150f0521010e0105040c080f0601050a030602090d0c150201050109140c0f0906030a060302030c01022b090807030b0403090b0a020c0f060d0903050a03 84
    0x114140644c440960509070389107a26842240c1e418030b40368034500c0c541440d080c05007001c1e912407500035040c40c000260f80398140d00080c44105001c42c03004540c07940c8044040c40c10140f403080d15044200c0e00710003084c004c184480141240906000464400f04643c603081c04c40300100d609a455010201c0140440d020501001d240c00e4109801088554100030010f202c6000c5031000030499540003074041000d40311001c0541409030000d0040c03540d903540e030340031800140c0307414411303c0103528040010072643d400e4401c4000702c61042c03180e07054941c1c0300005842282c1c0014403018a0340c205100500056580c0740055119070580342011076003500d94418107103130002c01c492443c1950080020120048103039000c950801c4203041e00001002222041076800c91100e40011400b8083c081c00030061108080c28140614400c2d51231070680d90391051800282d0190303041c8040160400741142405150000004224840c001c055502d00188404400d040f10200b000c100c01140e0003142e00d010554151191 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 622704370 1250 622703120 622703153
    0x60a021c08011d090d08090115170d110309010806030a06050c0702090a09200f04091103160303020706030c050c011401050f01020c0108040b0403090e101a04180902062104 75
    0xf0710718a0618420464580a0f582880d8003080358503400255220025000100b0f0b00d40050f403030002c4075443e100c80c4101d40e004081c0365416440b41d00c806100092090741c5d41e05902080e034024504211003400111394100e401741110f40e0611400144a01268213441139034010200000100c2d611074052040c4408054002c040f50036551509010b031011a2114595a00c1c1c8010310340468819401400020030b000c4110300c21581040ca400301c070300104038900d00940241201101100d4460088072414444038904e8003005006820500007045441c0c02a082101071100c03a0920905081229440d41d08540800d28a4130308683d04000411040c00c00d101c11a541c0c04081c8041c0c1104400000083c240441c0984002c0400410400050506110344691405001122107641c500d080900101d0036607510b90040c43c00e01c1c10075070040074a0403c4d4000301e60844140724150b000400800400034003c085d4100140e8105508002d125003900421000f044078102d03007c0d00942e03500f05401c01551020242d0207 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 622705620 1250 622704370 622704419
    0x921071d0709030f020d030201021c05010503061b0f0310180507030c05031302010e030316050633010309051002030901020a0e0a0302090f07051314090a0606080105060a021c0801 78
    0x800d03c0407070203644030001c3d8541c055030724228100c0540303001c0380240f003840e040425461282d080c40315140004c0d042203040b66000c03400ca42c40d540f0307015010820341680c5110615a070f6010440301d00071407556009982d02a100050715004995291107481d41da640c01030080714803a58600400203041e03014859480c055500307107000703411031406101820080802c90700103410b002480c0c0d40504a81c2d410070403600d00d105074009005003c1050b1030803c3d0340d010140c8507200003046071126030f403c03021440041c0500040c0c07200d580300b00d82d0485005500801c00340106450f1402210401c0c2c4100101c0d000450040782d100c0d0005a603039001c0c0b034008207100d60500303800d485042c0204003040942d8031590180e070070104c11407054078207854080c0306954505c01c03031485008080c90380100103041c2941e050703001c0d9610000d480e044810b036200321441c5c0448520380103030780100b80349500600860030820040c1054130300a004407000885008072117a590301c10500150300007124140103100c10003440f007000300d03469802a03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 622706870 1250 622705620 622705637
    0x3030f1903050c0a1b06140f070c031d010e0d120906050405031c0507120c0303140f010e0606070b0906070908030a02032b021206040506030d02030921071d07 69
    0x4085004600c26244c112040081c0c064800425a01400c980644664419800c21805150414007070041c24221028000401048000381e44d11f405001c0210300f00d6810356859140c44940038120454030f06105145042203038075144030188cc2c484e1060140d007640a6074008040380804c41c00145115040c0e0452420480113020820568030300103003070144901141ca0004070380c0c6502c2002c803943e00a03c80003800c5070b02c104c1c0e850310080f5008040c50300c1347c6020f56014880309003d40024072000201390384145010200e5401000b031441c600400c00c0c0c03c0030000300581d14081c0d40340c0b505a21072078103440481c190703040003041c402c18035001003900d80200074800140d800d00030140006912401003803400500c21900815182c0c000d0b004800c20401101002001c544074128801c2031200010100d820500480c60200459a14a8000f80c6491610419401103260210302400d101031090800982c60752004400c02d1031111000901140c4050a00200c003003500d26400035055580010180c00d05042c06400d1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 622708120 1250 622706870 622706881
    0x10c23032d01150912140a0c031406060612070804082106090703200c01090c06121a03070513020408060f040c06180b0c0f030a090906050f0f01120b03030f190305 71
    0x300300c0e0082d0f286e0040e0071a0b9400000d038041c00d003041e507007031402800034812040110030803981d0342080c560740c000182201c9066603079109100aa20816001e42e0700c554038400002e100c544a80030075944540305180321400c1150308a0a2740309602036054051319032440c03000300034450070001c0400394818254034041c04807501c00310f0541c2d004101000c4a080c2c8190010b12411010825040307606880e50054501c5801c1d55980801003d0210380c87d5040051070911101000c041c4001050200308100100a800064500410802040d812003d4005031540a00001503085024004180b0525899500345150700d407610700304202200d280c011b1070034004407180c2600d0800b20120850300b65000b4500f81640c80790840c4500345000402c08261404d0f202c00695182c820f540403c25000729040f07904148000350f15001049000380e03c91040b6900070030074007445d4000b0341c8543c11304800004100e500282141100c40824190f40c02000910040712000664100b440d04220002d076070300c02189030401c0b003800c20 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 622709370 1250 622708120 622708139
    0xb0319030f08040c0f140906030c0109060c110913030206090a110d150606030c09050d050d0806120d050304210c080d0b120a05010c23032d011509 64
    0x2041040300401c01001c002034204400890786201410300014511700e89656907941d01c2099000311407460140b00c4002c04541e8a082c0002c2488100c10141c5402d01d5440c20108100c030350a11140090310410703500b00e800c00842c0c40740009a030080741c003c841c03203456440604029103030640280145c61540c1c07040340c01a002c5a00764094810710743e01216031300034440e641c0c2402003404c00381c55040c880c05890084009801c903090703406000e140c0ea01c0d40f9901003d9035110300308a0140065103001d051758101101c00d040b0305124000301d6510039401411031080310002c9068514000e64071351a40c004c603000206103c140700003504242c10343c2840da83c6420002c0d50b9404001c0c80c6046c03000004164000c003044800c40281941c010044003a4007a160700d1400d444050402d80c0e0303020103d0207486651a004402c8001441889003080b0130402203c0003158402c40c1d6242c524580c0010030115000c248032030207801e024040c1c1a0018010321000064415504042c00390f4140c0000500c144140882420100803642d80c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 622710620 1250 622709370 622709387
    0x92a1703090402070242120a020a021c12060b03071706060910020c04140c040612020d05041104060b21060a0b0703020607080a090305040b07150f0b031903 68
    0x42d500942c940f070703691000c5052003210404c2e14a03c514070a2070300350151151070451030344c110400082007141038a2120309805200702c13008810202907880014041441c40e030001c1050006510440d50b0541d41c8107428000e004040c03011b1800038002c0448050750b0b042038000d1002a00d10006581e1860829107005400f112504011001200c201e0000500e150350b00c030261501d003e07010f80203613000c11000e140291626109040640318a01d02840c188582c810301882e0340c411640145c003185003d0078110140d49208901c1400b0445a400300051254901140500c0d4000e62150480e0700714800d8890800c0242c2e10b05030401c105c0e840061010b8194811082c040c0d000d20231000810804030b4480c80d010036445081c0d030f0401c0300e2505000528404141e0b0018086100e000255108252034403142d100100740c80500402a0000f0014403081c04881700710401031101c1c0e840b44840031000c0e510b245003103003510603190142c081c1e40d0341c0f04900e0003541018448080e5110003068900070b04005950041e00042 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 622711870 1250 622710620 622710637
    0xc0609121909090518060916210519020418020306060103020715050c0316020708030304020909010b041a120111030109091515030c0531092a1703 64
    0x801c0055032220690082c039201020f8440c80d030080c0f00501e4128050710390000740d8201c0340d5952186000085103e071001c580e00520450310a24400a540b62440c0d80e00b40e2682d01e9848214516044040000100104051451407104452000881500c0d00400c0110b6440c0700c001020104101a008010b0707402080d141c2d84041c0074240142c9070003507800e1075aa00c83c62680c0d0300c14242d10701400d02c4a105002c4001d0352140100070854411022404812a22150340d446414a030f90b005002081c014070741000042c0d80b19400f500006101e2079000e0004081d10140c801c20b0301d0507060b50095030042c0c10905085864000114001c0c00014500390341c028441c401440307407040079541d80d4802c034200700d5100101c04030880c01000c24807070240c1130120300c000d9110521045070344000d000c400064500b003041100300c1900541d92110443c030040d0f0500c202c503000270208214810340e5000354500241b4160300100440041250340c86441c42c06614007201101c464000c29980c42004420b070143d41c60020484078a223 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 622713120 1250 622711870 622711897
    0x30b041e170c0a150213150504060e04020d090c0504060f060c020f1203181f05070201110f030a0206040b0601051306030b0d2003010b090c16050c12030c060912 70
    0x40182807001c070b003440c141d804002e160304001c80010150010940240c1502500220881a4241e41c0c3c05a002447c602100e601c01107401403100b0069103008280b90080c6440c058805450320400e46600700c03c965850208944002000e0000d000c1403c10303114081c090582010031211940c1020030242840000800003842101d02e29000150f80d02d40314a000b42543e011001c1369116449030b412a00801c4507002c00b5030064420144680a90003800c0c0c51b50781805194880707516244043c2c0044414003100c05034011180304501d1080c8180c0802c00040c02c2800480e80501a2414180b80c060030801d400782c074a504004c02444600200400f48104400b25282420001512401000481c020b034488200191505207080c0201c3c460070707a02c26810741d20040490080007081990410011210002e076003440300c817402845441352442007090b40c40d9815010b041190004054a4002003a060b0040c101200e140c0003c282400b20820030816590440030b1000a005c0512b110000743c0900d0040b000fa40000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 622714370 1250 622713120 622713127
    0x15021c0b150304050f1207030e0108010e0c091203190806101e09080d110105061e130f020711090f040f03030c030e07031115040f121407030b041e17 65
    0x80100400c0143c81c05c03848a801c0d82c4080301c100b40c50105940006a00303401086c0d40f1100e1401543c401c0741081d0586281c2c542c1d108003034403020204800358000d80c05440e0061140c00c0000e403995010000b130b1146240d258100241383e03a820400a12204000d003003e8001d0485441590900360010241320540d800220040810740880c0c2003154480100c0e440751a1038020541007094440c0c4c400c4130561150291802802191150400d001c101c010849065408128000840303000303281920040344801e80408000c14079550f6040d00308201c1c0e002d00c034201d070000d11000c5d09482a04290201e07a80c000d0488c0c1c190b80d8103190903142c102d180407a0308001810595076090a40c480c600035409840224003c404440d19280c8914002d40541d000c85c078010710070b29010000261441104080381d05840e804004109054900040045803da4100080b120000c40d0014990284010410071005501072440e81500307040c42e05141c00c10560b02d080c010b06040fa1060001c0114400c0c80002d000400804060f955 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 622715620 1250 622714370 622714373
    0x306130803060604170c041d06070e0612131e050a02090a060b070c030c090b0d060f09170a090909080712020709230601020109050604080706020715021c0b150304 71
    0x2003138451a00074505c481d000451803481054009003000b6074880641e41001000010700419152405401241c81c1d42d92220b40001c030228417803c10001c03080000f03801340d820690400d44a01000318100c0318002c581155415101c10310000c0604604061224801062450440d0319100c0d00ea00210340e000e8024400f140c007041e030580c52a400350b00184201250161582034910345034049032520700c400c0d90311400460001c6100c6040e48641d04542c2402840d2070003d1216a4900e0302905440c08001e805030340d45ca05440108200b242100c41c1c0c0820000340c1d5035078071081039001e0030445540d0051081140b0b4040005c000560800413201200c0d040050004208044c1c00c04a1400c400c40e04072258007800c0c0004d1503030350f2a40020070704c00c1c0d080505071000b140d51407600490888002d42e401400a91042000c82c010420800080c501d2038007070440545004116203841c440103400258201c0700c04d03800a061245107085e15840101c101500340306101c00144000000e404030107040c3d90100d80c40c8000007050 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 622716870 1250 622715620 622715629
    0x8040c050d051e01230c0c03040b040303030f0504081b012705060903090d0b1f0e0601121103341107080d0206070c050a0c03060614030613080306 64
    0x100401400c5a03100c071210b02e081a10380d0421150180c250942011502070a1410302590700a18440c0301036090080d00d840c40c840c900c0c00003a0003103141400800001d060984140b00420141039006811541e5919500d0010121703400740b80c80d80c404502d40000d001c0050f010b80100c0e6001c8018105250642c00d061a03a2030042c042030306281c03842c81c0715032188170590b102501c2142d6454062019031380e0703a41e2410a243d0300c03803203808903c90f03204510050040015125008036500240a50380c01307246403400f03a000102d03113580c03030708080c25014012040101035070348600c3d4440412a4850188101d0680c000b50000d03c0c00042c1000191100b001c5007001034840090400885540c003c00d60060042181c101800b9007544243c110864080caa8000c26400c100040e001c10401050380101383c666200c0c00700311801040c0d1102244c060141e0904940840c3e00c10103103401840c00340100191261501c03184070360a28044c5e40e800e000303800c00f4082000541c206501c0d5042260800c00307103039403560781c0d00024 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 622718120 1250 622716870 622716893
    0x3050c1611090f0109110403020f01030903020f150f0601030b130203060112050c28080a1d0123090703151d0a0803040b070804120c1b0602010e1b0a060804 68
    0x9400030342d030004005502212a20040c100d41c00d6003820000e000d2a01c3d9041c2c03813882075020103034004880c0b6402e80c0d07442d407090b401100da903070003803050390310b0482c100403914140f003a4200c0e20610030911005000c2c150302884070b02501b080d402d0900b00300020b19174011620810108954028031940800000e41c5030340500c13052100751210800c00c101c1c501e0901218542a08100c913a0307000040450004503c1541c44a1040c2b088405a00c8094103a580c54051b0b00140181c0c40c042c0c54410100c01c07001d068180240a8482c0e00c5507140d5014054005e141c22041c02d00c03000a0041c45180d00280040022a10181c0c54411084e50320401043d00b1410303032401d074001d581c24050308249106102540301030114030b002950040b8800c1078800015103410008950030503058901034100c5d421f00c2e0b0b038001040e004111208600d40b0440400c0c000d0b00403640c4100c40480c055201d040540d440d21042c80c80614144105150040e45904076281d02c504900030aa601100e0700945090004080200d401d2110340b0303250 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 622719370 1250 622718120 622718153
    0x5062b200411120c030403170a1d0c1203270a03050f06010806061e060306040e16031109010b041224060e090a02100521010e09070603050c16 62
    0x70b200c01c402c0ba0a0082040d400031800c8200f40b0303c0100030a10600c088000c880c01107405a440d12148108080651054400904460b42159031884c1504460143c60b07088500380030300901a10321100c11006011051f06141204405600100028100d5000005401541c41000705454290418600220365608905d070405841403007201242500380d180001c043c0e0680f0180f106848480d219581400003015480c40351541c40051001522024101180916800301c2c00a02c0400c040d04028065420124110010203403410310f0070060050125080303040078003440a8840c17001c1c940c07401d1040352b51800782e030107180b4101c81ca844140003881254504032000c4400141200b0500068100701402082d1500c41c50105007588000103004880200e40e607108160042c084e00e04420407590211070b194070111118401c120400600c2440d8007200c45564041c0401c184c0594643c10701c009000c2c60480303190b000300d0070541050100000741d2805000e07200f140010814a03014201c151804206c1c0542c50001d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 622720620 1250 622719370 622719379
    0x6092b03090b100303090911070f1109040b09010e0f07030f08040305060709090b01110d0e0a09090510110c1506010c14061023060c120a0305062b20 65
    0x107101c540e560360403d110441e80701c5d455440b0081c0c0d440303480c2c0090b00c1080c51941c517000814007100000c6000c1902c103802c0b5612604210240f4682080061110f280545040e1501c5000c0d00c00c011003017000f4402c83e25a041d042c03008158005407a045180d6a280754000140108007401e040d0040010704425980075584c804182c403018505802d0087c42214180b241c1500a42000c940b4507455006141e1b9030703c0d4104113005018211241e200c00d48142d490080020b800030141c000c0010620700034400c08500b68480c17000740c44280c0300c9000030401d44c0c018041d4400206d00800048801207400078000e080e10781380f08034940d8960356a00041e01c0d080861000136050030307ca00083c001d84900459518031807148100d807540743d05e41300d424665000804803030074140104c000003098a00d1800310042c00460071100100d07a8003856191111201e03802455510010907110810b101c19450321352402c82e580c0c00c0344038181c6412820740030380b940045214800688a010604985080b10740f41d94285e00782d100d006032 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 622721870 1250 622720620 622720643
    0x90a1811070b0603060c07051c090801090f02040c18180207140a120306080c130f1e0b190501050705100c1110020a0804021306150c0506092b0309 64
    0x28642e8445600b01d80c050304c28062480004d602816403410740303024940240c0100005400311141c501160007207054076080c030148a0300000c80341424001c4203072851003946259201c200920502043c4c1e021801018180711000040180201c1102c90060440f0b201043c2304256800710503440d4001c1c420f82c08080c00b90452000c48180c03040d0000744507103916109083e10841154503400403401c43d5075034004d184841d0024000925a4905400486000c1620345c9001610343c1c02c4001100448aa100013045210b45050282074655a00c0c85907595510040c1c800e41410301d146071814003580c0a50040398140500403502d04140001040b03242e820805540d0208a00100c0e4203006d403040503230010b03012003441207561000c002c1d0b201d402500d24900300354031215983d40307980d82044209045071110740c8400d507840c00000303802e0b0504070030b0203401036041c2c035144003000f1142070007400c0a5000307107914196030105041170007005c65006070040d42040008124000200f150040300506512407001e04a2200c05 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 622723120 1250 622721870 622721873
    0xa0b0702030d02060c04060c02031014010e130c0608251d010903050a140a0c06030204060e01021b01081008010501030b09010b18010b251505010803090a181107 70
    0x40008169060088040350381c2d4006111040f659190121030308101c200c802e102c200300c450f0282c0708102005100a080e110000304d418200c0088491441d40c0000c0426110300411000c0c03404190250000a40d10040c0315200030780e00e828035010780c54840e040401c0f031060300051050550114041c00d0010b00380381c1c0741525075250f100070180003071500000c1040d000c890100c051980108441c1d400c50740c1c001c025050494558071540400480064010114000d004020300042c6100350a2000f0302a0b0307440058969081450051003042c2e0403210a040d9404010034000c0300c1103d002c000010302c0300f441c04a07616170751750140281c1c01915504c400080d40c20000048108004110356030b00c240381c40002045100101c00c01c1000c0e54545001202c101c1910300d00501c00064200e000340718015020b0b03140c2050703424130108003c52000ca107109032080c008184487c407600030107016150052035a071004601305146200068800b041c280304184004070120760b04181600c868000440603010241d0032900c0740c869 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 622724370 1250 622723120 622723139
    0x12120f140a09260a0602030402041413050606040c170a0b060a0201050f0a140403050304030c020a0311030f070503100209040e0601171615032d02070c1a0a05070c050a 73
    0x114015a422101c511501c807920600060000c00820020f00051000640c5502d5600081d0b0000d4400d030780064440c0121503038240c003448200e0041a001400c0c9200e00d026003406400e1800150103144900d0900752002d280e10743c0211610400080907450100d80d80354144410b00400e40da0000c03039000140441e0b40111950103501451040d40030111644c855a200301c002c0088460160002c3c42c00141203011034013191142c070217980c3c494441c2c2040344146a0940000390021700135403007258022084441c030411400c00780034401ca0905080c3c000d12596007480002900c58400405c40b462a50b03002c20383c0c0003190340d1508090038568040050300c0065840b0714104180758140700c0100c14a10a00480040f102940440700c41103c07003d05003180c3c0500350480c1140940071000c84110b4001c4070300c0d1008070f100005102400040d00c1600010b82d2101145041d0744244041e5000240c5418000550841980d440040790020380940c50715550f83c800030320f0441620f2a141d04082d03000320b00c180e0f001c55003602 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 622725620 1250 622724370 622724387
    0xf13060609091404080d0905030412020f0118050d1b0902090315060901090f0207060c050a090f120303150902040329070c150e03031e0112120f140a 65
    0xa595607401c1c44a030700ca0811105660b1015104800d94955500150219038880d014040140380d004010660302c229444d00c0d851a0401e801260450010300c00c131500714606903e02d103035040130a0800d003001c1e990001c00200700220320700ca654007885c00381c07050a0800802014030700e0000b140403080d100903501c52481100a40080c04035600038070034558001100c03c1c10404161103000018070700485607003807003040005040c080346911403c6800384204400a03007940140403180c0c23001d86d1005c2c0c0726100c0c850014a00581c40c0d202001340300c00313184280700c82d180c0700a921040903050b0401203144e2940813004100c0f040356038020303080f292000c2404801c010f002451150001d019451501801e1301241d000c0300c0d01281076030340b44045020548140005020b00c5004d1000e200b8514000400c4505001d000741154002c4421a180c0d0308848001c28201da040c1000f9400351801c103006140340f06260f544c0c420320100d20901c88003800b1103869030034280351052903890789818503031194035182c0040c010017404030301 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 622726870 1250 622725620 622725629
    0x120905011802030606061e0a090b0a0e0a1508010306180c03110915010206040f0615030b04020a060e1003051b040806271b0402130f0807060c03090509060f1306 70
    0x34038804030b5041e2070040140e48400c07031108404190787d01c0e480d1171041310780e01c420035100911007001e400085440325140500300384401502c42027000c603038400810440c09070315081203117082c01c0d6042c1194100e5000080e141901d5010304000345454800d0b458500c0440c518400400d042c0c412a004402c01c4455141c02e010750b4070030742d400c1a183e141c001010114545d042909030041e40300c1130000d80800d0086c40414174080c06080c0005d501c81c202c85401c40382c0c00d2203420603100c9400c21410311046040020940000b00001d14201400002500010356429200c4414404064a41e000b01d00b0341d41c02c484465100d909850440c640c0d865540c0502d40e1900412102d00c913008854015240070480071701c810110550166020382417840400d6070307142059200000160b04241c1c00c2c40044880320000724000c01030041445584012407900d0122850f0010304d400000820829010050009030807001c81d0f0300741c5004480c03020803955032102080e10704000801e51640440c481c0758005c05100280e002c1c10a0b80e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 622728120 1250 622726870 622726873
    0x91a090f0f010605091306060315061706010b0a0c06060509151f0f030e030405030a060b091617090109060507030f0b090103020a1e0801110a031a0307030312090501180203 75
    0x201c0c048042642202c0c010b1241c1c41c1c101c5582800a290740750032402c1402c04605ca100001010764603602d90230f204000c90b4110344042c5580ba030061001860b00c0190515406249000309510340c10024020940e0240440301402e02847c409000304110454001401a04014103001943d2400910507148a108088450f0107462940c03100d07144150104038003441d002454a4a40408a070307a00c04074010326441142c01050302091001041340c2e5024460b05070068012140403901c1510320003004042c00001c0c1c210300182131150807145031150040c0300743c002403c541c0d10712002c640e42c00c0b0390280900700d101c000a11551408041208468250b40300c1542206480f00030002402c030b0b4030a1105c07620302030202a50201c00c960040111021409400f0032401c1a0b0b02c189070f405035280d80e09425075030103408242a0034004a151001c03154548150b0300761301700e804500c81c080140400400d0b12503203d4007015003005483c5410b03005030401c0707130003c10300c040c1c0c8000200842d520b054400b004403c07001500b00d109 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 622729370 1250 622728120 622728133
    0x11031c060b07021815040501080c010201060e0709120215072105180d0606050319030e0114090103050c1312140a05033009150901061503091a090f 64
    0x2100c41c1d6000d441206a0191002c26503110718400c0b81c06119004000c400490401c14560b00140c5460203054001d1086400400b5a46800400a0709550181e000452000d5080301000111540300d00c0070812a42e0140580030044001c0c00860700c01c0510300f2080d242e164000901a0411240c4180348541488100e0b8143c40040211400c4071284520381c0c03210b841c401540a00b441d14984502024462480b034140000c0c101c0c3c0e100e020a04000c06510003010000701c40e4404000e26800079030701c41c032803042403034400f40d01c403085910516140111a40d080c101030fa03407800032712966404c604840074448556400c1c2042641c0e881c1c1c40c3e05501030300008540c3d00480c1c0600700550800016490070b402e40c09805541040c10320800480c00c802d00d0403003c1c103030700840709164401a03e0340340315a00611113030026000180d803400b10320310800400b0301a80401e80c5403290400091042036a070120311a0381c0e1402250000403070604800041503400462080036520040c0b10300c613940020440c000031003080070f0391030303 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 622730620 1250 622729370 622729379
    0x705031219290402030c0c0a05030a0305150d0b090c031603050c06121605190302040303180609060e130204080d020d0513030201050f12100531050711031c06 69
    0x3403841a1039140b0003008000c400c520b0040c40c09030040c5910840106403141000c00044901c4e00d400e00d8490182c6440c0c00007d50a07000b00e40c10302880d80d001052410810710b09400c40003143c04107400c072802501206c0c0240100300d035050140040181440014111761403071607016080280002c81c0e210131510383c880c0d0f0301020350a0409009071406801800310542031035517a800f00d40d800220792407020f400c02008000d803c0000755403200018024006035001a100c40c01d62902408035296034900c10411980c5240030000d40ea0300c51005015914640781c0041007582200100302c0302d10610311032a1410340085000300342c0000000e400b80040710f581d400c507001d06101100940300751291518040c40072200300c50600165003c0e40003021041c0c254030034a0315014600b0b0030040116020303182c05540c8150040b040000389000000304c288000c14140c038002007800f90a00c2d090111501d202d50b8a00c03078441001034045401004841900b40200c1e059075511403580c82100340c1000300c1851164014503140d000316 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 622731870 1250 622730620 622730651
    0x1090603060b1e04030c0902120609160e0d050f21030103080901030c1b1203050106111b0609030f060106120209180604060506070c140616080705031219 67
    0x3000c0ba850b000c40d29250a6120051140d10007241011030841d0004110003c00144450461801010352080046c1c45d420762101000134030002404491042d5400018030442c4800c6254449880c502800e0a500d010650000f06110080440c005400d600440756641e9000d00c02142c051680c054145a816202004440d403441d80d0200780000f130043e420502041c19503500a500c110090b00f05d50800c0340821040d0651040c00d1111842d04035102480ca00c030300141c1d80d8141c09194058400740c10121900d0445044a5540d0b0b100445000d61102c0845000440d646034082120294034000c2c007610110401e5083c0542c0d202c40030721078040010500c0041210301c4601e4400e40f42104030003441040c602188a008002c603080c0035012641c0556100000100b0743d813004010320115100315904445d03685804040784c4446094540319004000400c2151f2008603620030402e4402d60080c4102d4882c021414140d266000c0d0030803044501044d04280490080c80f03908a0f4034414510000f4065406031081c0300 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 622733120 1250 622731870 622731881
    0x5060f010308040603110f07051f11071118100e0f360d03091104020412170c0304170d090e0a090f0b0c120a05060607061a1206010501090603 62
    0x240008006003c00d00695200b40c00559419071110740c031905011f6012000480e13070f401803000b101c2c281e000600d0b012942d0b251140c1c803071b07580340403c0b4100500c40750000d204500d841192801800050060520680759803510680c0c061041030326900c11891400907404803510b0351600a0714100400e0340000b9000410510030140f180c03108001c84c28259000c0b643c810207410280c0548072418501c4070008260043c204507410684010390340108991143d810480f81d6041000616070003140100400c0c045816411b55000c451940000424507030002c3e1090702c1c003540940059001e0300c5c0400580000e0083c4030702d0214a03004420825201000862003064032900e400e807180301100030110001401d51f13001c0d9800309403228000c1400c3c11540110365180741d0407403411038407403c008602059031449600c910480c0707030740b100240780204424200200020b81c2d138020f20400030b00c0c243e02c400030340d00820450b0741841001030b07010703010400028500c815141c0320202405043d0000d540c0800001d141cbe0710a0084 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 622734370 1250 622733120 622733123
    0xc0a0b011d011203030902120d08010603060f031a0c12010e0709051e010e061b010606110a030215040f02030105041103120915030c071b03020307060c02060306121c02060405060f0103 80
    0x510103d0945035605070080c118036032090380d00c41041520040c6104040c001d8401c096020740d283c0081703605204c0082e0481e2881d130070030a01c4581e241c40600000307684510040d1801c81380e5040c1a40c0356a007000c620160701c280d0511041e025000c40c00019902404040c15006001a40318040c0c042e46800501c005180714140401141241d007000e902e195000e44504140c0d040007405c0350785415072110001e058501e110041c0a21a9503034002001a2034ac06400031441d0f600c81e9029211103411924001d59a05801540841d0048503101080410110000d00e02c0c0e2154064000e011514103802c2000540101d001000d0103400740b000680000b0b1500c00071580d002500602141d1445051303501400c1603007008101e086640000c209c680b010400b503084d41803036030b02e1892105101d2801c42c0b0505041c00300a501c55000c0c400101705000050791840c007500da21000c2600e8600343e105101c060309282403280280885020f0340003141c0d0700003a50200c2c40c3e071b100e81d0140080315000e4840342210500c6d801c00340320 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 622735620 1250 622734370 622734389
    0x605010815040b030c0d0c050f06040828120201150b0f04031e0605101703030c040e070c12020102120105100813210f0f021f0209060c0a0b011d01 64
    0x454490380780ca035205060f81c4001808440f0181e0401011506d1024090001c3d1007005c1849030400107807910201503801544160385445c11f052400d07100c1c0b81e80b01c150010031038041c54191440c544a00c11802a140400d81001207107000952a0401a00910180c0d010f5519050300301130205000840c4400ca85101c07148042452401d8a5074a41004109140b0640c210b0886507409070000700b00d080c0260b90084100d0410004120b1074800303001d1030048180c3d29800c603a0070620400075003035601000e0360102d0301d445080001c0b542e501c0c3c8c0111401c0e903108800410100f0548052420b465055026112000c1c50441703110560b622001008400c50510300300c00c0018130460005400710366040c1c01d00024500c104440030030300708418901c840a50048800800046654a2980804c0d5004d00f842403441940d0002e400840e035940020101002c00d20113400b45180c000889620640356401110090b41d859030070b03a01b41210600c0c0000b000d00c0b0a11a1100c50906030840c1402d000e00124030038101e911952 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 622736870 1250 622735620 622735651
    0xb130515010e4f15020c06070206070c030807181e12151d06010605030a0507081608071101050f0709060f0c060b13020304060b190e180f0313050406050108 68
    0x50007858190112102c3d407201084612099000840506103c0014a141e00c800768842100d4403545103811401480c0004547c095002d100b440c1e030304122000000b642519210403c1d60740c56200ba02c0d401064480a009036032428000100c140c0b130718690415419084200f401451765070f600c2000820000040540f0704217440c110841405d40b1640000c034008071240c08810000b24440c800350801c44264802d001082c0300004208856445204081c0d00c1082c50404001c242484d0a02c201c00c0286040400d06100c2600701044825014040c8501c00e088950020700c05032501401d031714035440d01544c01001080d0000c030085041405410210822035003039441c0c0200003130545814024208100c519a04a1054100c1e0518071040380002e51241d40940c03004950f22203200d05206c0140c44d204e0070070051281740c0c6414803821440c80010343c0c00c40c41c010304140c4d0f00d100395100581054022076100606100000e0318007004000e607810b00048641c112020090a41c2c0c5000650342c40104581040b4403141c00b0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 622738120 1250 622736870 622736971
    0xf03070b03090c0613091d0307031202090a030c0e070215070e15070501020a1205162718060603021305010f0207090f0e0115030b130515010e 62
    0x8806568440c024208a404510255010070b00642c0007171703142841e65840701c03002d2002c03484600904580304070100408940041c060310031912405103003401002c00c96081a50900f41da002d80513181300080003000400c03038030750720f10340a100510103115001c0060355400010b68140d001041d40c41b966541c2d000703000150380e600d030030403140d81142d0040c0f1503100c0103107034003160105800405030200c0352040c0300040c2c0c1e913688402d01034088894855003400d00c0381003d04101e05030b03c000d248040700d82f9160406505156044005941c140e20007400d4100134030b0714001c001041c03540d00c4103194a80003118010040140c9820080381a4402c0e1241d4030401c2018910412955200700c0458009180c40d2043e610000d40f1404210144c80c420890341000c140c1712070b803840d403540c03003131080c40c0d4101d1420403d4025640346a0f142c0701c0900c1c0007000301803c461402c201d58280702d8203012152588445000c400e0140d80c40c0c2c0b08507030b10302c2401d554140001c5401d96450300380600400c40c0c4000007080444007115018203 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 622739370 1250 622738120 622738139
    0x606030706110f16080c0a061b080c03030a091704050904031b12030c03060b030618041a1303110604050601030210030f060f080105071803080a03061e050f0f0307 71
    0x3500b2102007a1203062149000c5100920140f8150041c00d02e09101c66807800b000145012200110070784151084501002982e401050440480f10300f00314941d0a15203034101040503006194602100e13020000801c0001d501e154000c1000310700c1090341c2c2440b903060511200403030080380541d030b800c075903040041000311313000d0542c280707075200104540c1501036642c2d940e000c2c84d9081264880007003034450b082c881040c0d4150042d00081c00103c842c280c00c600e81a0300190603516004d5070480c04140a47c045814003131800f01d2080420340440c0d4080d102e0038200c48441398501407035030641c001240601840900c0d80003140303060055030040000c2140d6401d54080043c003002d1041140e0034903607541c400410340ca03400c0c01000020000c61a44114503403a00b007040342940ea0040060003008042c105815200740b1020b081002ea17600124a60780701c0521036025002045203420412000e1320141d4242c612a81d40205074050701e030192001440301c0d05200600403041d9040a41d982d0540040e0b8040c040001d1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 622740620 1250 622739370 622739387
    0x403081606020d0c08040c05010c0c1e030503070c030309050a051f02031e09091b0a0c060209060d15080106060c03050903161805011202010c0803061824030606030706 73
    0x40d2000503e000d51030080c1030200ca005840722070104651808101c280200c80700c01c030004200a08102101031a1640e030f1425105560281180340801301f0f624040541814507100003441c1c1c41000c8035a0381000d41442007058541d84030071000100307188030118042c1032a260b0b8108a0308050b0151120350010308201190040818400c811888240603022070302a41100380895000208680b545e60000841840b04807840213101008006d000e64a00d2030702000350b42140c0d4035a0462900c03041c80140303442c10b038000c0e20450b0741c4294400004190082c0f024203580c0302c1801601000b6000c928035666102d85420b1352410300c03800000c99800b80310840401d00a13001008603150050690300c1c503c41806040d488100d00b5003002d001c196038110703180c400707804031700c9a40c0c0946910840280c0c00c1c1095030001704130040c55038006026007000f20103d00541c40d400084101c203032007641384010510700241404e0981d0b00b4217811a031065030885100c03007142008204103024010207005800c0d418107141d4103854818 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 622741870 1250 622740620 622740623
    0x90708070f0b03132f011409010c300302030106030e0d020c0f03010f0203040503090120101a091f050a12081b0d02030712051303141908090306070504030816 69
    0x3d04800410b880c6805c41e8000000582c0209100071039580001c000401c85d100790813080101a20410070042aaa04440403002e216404001c1408074000d002450044092080e007410003485091a5200800d80580283d4140d908950f002c20048851101b015078841c603081c09500541c00440c18681d46040c00700c001d03041d083c00580041000c0c0c03034089444080f030740100c905841c260404111039210790383c05141100c80845242580b02480c014008150300c80c910404034020007035940d20510302e452500122098141c000a00e400c0081c40c200c4c100110403034101c006039079034044c44c21000c1140e20780540300e201520400f1691110100050380c403030441c0d501241419030b40302c2d1403c050000c905420402404046410313030155840f83d8407890040680c03c184d20070b03503040c000c0512814241800302480034007100d8101c02c5440060f044005064103103c000350500c184030b030800800d002231142000007400d0804003030f4111205595100002c075001d01450000038001d5504000d0b40311044c0d025850050b002c0d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 622743120 1250 622741870 622741883
    0x90d1712180610090b06130b090a1a09190e09250602060402040b040905030f041e0605161b06080f070c120c05100203040b0405070905060607030c1103010203090708070f0b0313 77
    0x141001f1001105040694400c80c05000005600c800300c0c1003001105c0300030b0100d1142c0440d02c2d0803a007030990302801841c49031401101c0d02c5401d454030801072281c0c0750007031400500c500124240b08450a403202d1a0161058030b0740200701c10f030803010040c0c241c40c408071030065000d000b0a494950822028140158006510039201c1c0b040b88007003034090004080c2e151030706811a990f81c0c54500c00b224807883c9401c00c10780000e05248104800340d0403e0403103464508003450000e070000c051a1039080c0440740d00c4142c101c400081004540c00c3d0300305403814040d10074007440c078040781d0b10503100302c0b0011b008000081201c1185501400414043e02074001090301c07072006d03036035540c034a07082c41c070220b810490b03043d80c505a45030b0074042846806e0110340d0140080031402e0089144c036902091440c860f01c10018108507001c49a802801751540300b0401410b00103000b07543d01c0c10b04450040d81c1d02e03400e0003000d03254050001c0000740d4490700c80c02c02e800c4990101410341503540d0841b045080080d620002c0c0c425 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 622744370 1250 622743120 622743127
    0xe0615060318070b0307030b030307080a030203040516060f03050a0c0c030809031e0403030e040603030813050a05030c070e13050709020a0c05010914010f050903090d1712180610090b06 81
    0x2450042c4583e001404da1582e03055180d28004c040141030300c0c0541e5007140603801c01c20035075002c1148102114110b4083d0305001d43e9a1300e8a151013440c00191240142a81080500102c0d1700e40c0d20211a2894a07075590f001d005c2516003c60707010859401a03075010206440b0302118002034010200c450f400200c032070a8078100041140c00c3d50000512000000348900005414010107401c4854407420250039541041700901759035001e04a040c1c06400740d000e10078190044810084200006d0309001d5215003600e4807000e02ca400160b9501150081e003840300c0041000424215541a80c2702c4000d401500821240d4500240e00b0003d43c454030041080020704100b01b40401d0090042800c414429813524400d0000c00184908654608417000d40b02410b0409010400d840001a1410500d003241d5030748215560780382c1100c0c403803414100c0d5402c50002145e1142540303080604140306e00481041064500e03080400390752240011600e003a07154016000520503c084c991002034400c4000c2c05040c80c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 622745620 1250 622744370 622744411
    0x306250507060603080406080705193e1c081609050d0f0c090c09030b0a020909010e0105010e01050702030d030528020912010603080304060b010c060207080a030e06150603 75
    0x1070301c030780d500305030707801600082c6c1040569800100745901c1001807070101d041c400450300050b031602e02c11840c40200703c884c07004100b0500800300c074698041d0801040010007281129900700400380301e021050b003402042126178100310035102c11a51030003183c1d50702c1e1455850a00350390204d410123070084200101c800002c00c181d21031802c15818076005071000484540c1c18a4225112803158200079100750406640800042c0c01844200a0f00d50003c444070156580070b0700c0c04000c0c00b5802c24594040999000003034070300d10560b03600b41030701c10aa868004101000c40192898458020300a4143e40403220308090203211b40d0000d40c108191100608580400501c1440c00101d04170b1f501c00c02503400108280c8520340201c10140354811800280309040c6907840d0307020180002400544040c0e101c402c0b50125030301c6902c0080e5400e0b4801d0381152180107134201035000c1c0e0000c40400001c02d185c444451403803080018640c1c4184c801c044c0c06440501100144441c0e9007000d03001080e1010b01b03024034007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 622746870 1250 622745620 622745633
    0xf02160f150914060a060f0b1c0c1d03060402010806100306090c0e0102010e060610210906022710030c0e09510102100f0501140306250507 61
    0xb12528003419601d00100400c243d0141400b4018110580c0c2030300d006000c02003404114041001c0f102400c0c00c4035220481c05441070700010900d07076240c0a052a102021212680010014441e41c94140411107050011000c1c188e031044140c1d4080e020803600d40004201c2c1c5080320080c0004113141c5008a0400c1e40c41110200741c55400109034003081000450f0400d40d68244180c8070340913000c500500513030400e0304c0441c400c80c03200076000e0200312001c0802500c0d007c1c60207160440c1c071743d560010400300030745007880c0000b0b4002a241164951603400062101098520440382d10303c00200110084a0172030030581c02000001000c10178041010304aa03020f80c1c80f901c00511070740c50101441008a40240f031080c0240300c94544000f540e00c03030240c06180201408004e00582d00610362070340c4000d18440142e1404410031001c0d2952400c04550100451140c0c00c0b1604813001c02c0100403c945c04101015221075080b1801c0c1c01e4401c0b12022001c203904000d0050b1700d00c8a1500381750b4036019490f100c06 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 622748120 1250 622746870 622746881
    0x702041802040f0605032b0f090f03030201020703080c2109070308040b120606280903060911031c021207060b090903031506030720120406030501090f02160f15 70
    0x2040e03030f80c4d03810703082120742014401071a000e0801d1101c10b00c0100002d03091343c03104034440000320410552040742d14649004080020107005102003039405581c0d07a10f0003c1c00f075400240100c0c000f901007004070340541485002d84418541220544000f503141a07003201c001c0c1401450000944221000040814040802407002d0450452510781da00b41408241d924120080c082d00d00901080003040c01030400a21105c9464005410b5182070a400c1d0004899032401500f0142845140c41100c1d801c01c02c406402c80c2682c0030036010b481106182e900c2c1580301808801c014800f58020754188000c01c10000010314075580b1580c80014801540030100d003489008484074040c960000060229044034842d4036450300008031038091440c5070022004082e000010f14161025452100000400c003081c403a050382080454101600c2e02d0755520010003a160a101d0b000d203451070900800030b11902e50080791750010fa086032400803151140d0b504860300d4010501074070400030540074812551110b0242c1e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 622749370 1250 622748120 622748141
    0x3090909140d020705090a020c010615020d140405010507080904060b0a1d1c021210020d1505030105041a1810390c08091f11070b070204180204 63
    0x214180022040307811841d00d00030310604000d65000b050200655074440443c103a00081c00140941c541111074461400340074141c024040a0f40350090340e89005600044404040e140340d540ca103c504540da5002040d4829409940c4c0010030401071000410744200050801c004082c20001307010395110345844603138100c0d2000400083d0880c01d0321800c800d5070401c00c01d000204035001104a46029010012190594402401802c483c1d0488000e107000780048072141c140d542c3d01f0342d55509400b1272403004248000800c1c0006155810100d141d09051040600c2981c0c0071041b19200490750b0400000c8040040001d81880d1016240100c864024410340d0a941e000510100c1c010786182c9206604117000d00d141c18090b5040200400410780b031036085031008009050200b040303101400c1c84072180c0715940c005a04901d20701104003011a2200c03001080d070f9881d944081c2035040074a903454070707500203220b40701c00b040c03060043c10301500e030592151402605c07d42e050421884694042010b484031241c8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 622750620 1250 622749370 622749383
    0xb03070b070309230d020d050c04091101020f0c0f0904140a08040609081c050a050403050a2006040e07120621020a17280209090604061407021903090909 67
    0x60801030b07a003948503130030380b1003400354441c1000380282d0021800b03131300d90100d020784551811311a80c41802402d1140d280c108101410502280c90942007505442c4c1c003d0b00300394010300c614550358610340008161610f0000005020300d6907181050100500c15038050010b86a00c044030326981080385040080840d4107101d115070030b0700d035454502c01900441e000d501990564000740c004078845c0002c2c50310391003a038185e81842c42e11004100812100c60180e07800c0184144141c1d0400001d00c0000002c0ca9001ca415216020b010000e64080c044180218407400301640c10102c0850006405698a40c025404526000030132541d500080301c42130001c0e0500d1102400c062000c3c13029810403188103409400b0203000307075440400408455035202e030403001d900070a040001c59429240324100146042d550020f24503109400c0150b141a268081640c0407155140b0f0082030442e2131210148c158480d8801e5005048098032800c603211034a400c4110442c100035110a0120700380c0c01610520304070b14000c61 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 622751870 1250 622750620 622750637
    0xb04110d091b030f1407090905010b09010501050c2107020d0b0412140405040e0106030204060305060f060f0105030105060d060e0903040617090c120a050a1a06040507080a0b03070b0703 81
    0x1c0c11404940e40002c48040110002000e0010511000c040c940056004c0360703040c4928404070500b07080c04180d81045410604120071041484415004140441012586440d042e6070360f100541d95880340b1640030040c0e4128010300d00c4105200c400300050610307010010f034074040c80340e8000f03015140303529011a441801c8e0320034002445402000041040031a0030f100700360000d4a04007000f40c0c0282d10410b481552074000500c040e04081d08000002e5038003800c0bd00071b01e500c918050381c440700100c910758241c01c900d1001592234a810b81510f003032840182c40b01842c59007840140301090340a01007000c055030f03c2d00000600080c5201075284110054070107036440741c0c18082c005005030b0307100084c07a4014440340300340480060301250b10008074508a4100c041840140610707802c00154090113082c901030340315170400340801000524650402c2d601090000e030742d80401c03c0100d541c2a611540000c0c030078000150098400c1d84003010a4a0050855403440e5480103140c09039400494110000303402107 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 622753120 1250 622751870 622751873
    0xe070b0c07051314090610261615090f030605041a010303092c010e040f05060f01170102070c03031101020c07030602120f090d0f0314100f0f06080a0b04110d09 70
    0x8406550480c80c1103014106c1802d00c00c105c514013041601030807074058102c0403480ea80703481074101161015010030669403000146403451003400507501c102d400601c080f130f56462409100c1e04203282aa03074000001c400090841d1501002048003d000b02c3d100c00c80381a9060310039110002d114002c41c40780e5202c100c01c0c1e04041c4040182e080c59030241c2060745840c4940d640402156130304905580c20000650080d80c1d840c00c00b08440d00c5101000340c03450041909004103050b0001c401d070f050b650764900755010450340c010908c1c00c034401c000c401f810440c0340100503c0040d1003010f40c913000705034400025061400000080e800c0030741c160300844049034002204010000303200d501d2688240300546164181c44d202c40b5150300c40c1c1a1210001c200036520a100e92254000d91111840d0300c039440200e002403401c200075035110884e0f0f02444000e2a2200b40001e80400298000e105994003980d410701640c655003a01c20141240e0b81240da8001e440f0f00e10b10b800c0c1c00400015000c004c51040010441000d503 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 622754370 1250 622753120 622753151
    0xf0506030c0f0904020609040b18060102060c04030818010e100507020a05040e06010308221502010e0303160c1122060b0304020f060306010c0c120b0603010e070b0c070513 75
    0x6030880030b4001d0034a801c82c44242e58402ca0300e154055016a0071568805451000a00615000201c41d901052010681c0826000040003510605007038088629030307115000392421600030b610005048400812039102500490726143c1d41c1c1c9207040c109070b007404003030f0b40c00100040010065030000520106448081d4503040040340300910055a041040c0c1c01c62140d45919482d0500014000c01c6000500e8190004070b007172600401704e2503c50310340c0703c0c507102c502100940d41085506001503080403806903406a02208507402400010503011140e00000415105142c1000c002d0301c08081c0340304100480e40720803101086009940303210301d5190311001b55010440700c458011320308030348041c010400107807210146c0180f9100c0032603125803640e458000480303201629440091180c500c1441c00a54002c4000400621034860490490295189004e2608860707407a82a50103a40c880f0404010304031000f0010015501002d0664002c81e44030808980c000412718210821583e40780c440d038002604 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 622755620 1250 622754370 622754383
    0x10606021614010207032402040f0806100f051903080c0a03090f030c0302060f091503090c0f0d060510090504081207032c03070605040c03020108010503150114040f0f050603 76
    0x18141c0c01c2c0d0880e0700705400000e6891029000042850207a00e02c00d802c44d903400440c600100c0d5403000b0955a0300e885040c6e6404141c1e1707070300c85d071a1036100742004942c050708124040d8003690031114040c061585488200610100074481100700101030700030110101f912a00200303012480e0f0380003408242c01da07240050401204e688074900c4031031185018400034041d91403290441e0f4045a129844210500f400d44240c41400b5071142c0c840f1151500d08190348010700914031070301041c01a03445c02d8a94000b8003102a5101190552150302138280000003074646d80f1242c1c100d1601502c140d1000c5d181e4140d00100c6806880a0740c4003075000c40c8012007102c00540ca10b0b48030000703180031700030300070f1b0500c2c00003001c0001e0f0b51200d103010b9a9031800c07030170b4042002680c090f0340d0800014400d0381814142503e1003081404140c1c000b81102002143d40e0070005010440380c0400300072500180e28041541d411189038600c8151300c16140c0d501c0840d01540c40c0034072011250300400c0064107042030700030540f8100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 622756870 1250 622755620 622755629
    0x150316080711100908220e01051207090f270605070e0607030309031b0807050105060f1008060d0213051014060a050d0f021204060b0102120a0f09080106060216 70
    0x26049114110b4400301d00d02031111400440451161014030b4201c896025100c450128407111214244c00c00600003804803c40341000c844013240e90321030301400002c160060015019600000b02009032255607809441981094400003c00b410882180399602c031140c4180d01c0c0504900b41600140705107442040d030003011600b800f12036040f08802180d10390280ca40c015080c907a0302c1142c0c005150056080091380c455901d20000342d517503540b80c4120306400c90700c400e50b11586070000241c030701e040c5100c060303012800003000d600308400d98800032280ca00d0b000707090365002a0f600040c000141c40d00003a250301d0a40d41140882e10b80350080c0069200c1a6079400500544087e8801c03071516261001118069041440c0c0b842d558500944400301a1264600380d601851000481c1f01c60112401c0340302c1c0c0940c2c4952424000441046c00480c1d607904132100403181c201d000c001500140740101044805c1401c0c900340f840ca504c0d82d0340c04484c01c44411354802c001517008411143c10010002e1584006030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 622758120 1250 622756870 622756877
    0x1401061b030807053a060b07020d0f051009120201050f0c1c0605060d0c1b030801120f1a0a060b0c03030a15080d050d14130206091503160807 62
    0x10400d84004080c0e140141030f15007800350010700b04010b00d09007254683e20101110f00000d50003500d603018009030340c1d0300409562551030031102049041c00042298034264000b042506415003540740d15030345a842800031180d5101d444030303944071a44a4011540e8050045040780351180d0190350107801d480008104044c1001d5440c10041012a07060076a100c2150311020050740c00280c2482c00000c100d107070000e990081010400e440b07200702e141c12210181b48640d8031204400d200c00708480d4202c407564001804684030400502145203000d003012102401403000c1c1e81255841d448100082c0d81c807400405414200000b0096000f500d8050b0300020015040c00c0e0345009503140d652134481c00301400030341c038103600c1d00c00785030400046460940185c00114260b442d641c14401c0d018100c0d41c081e1050a021030308003103820200d18012107010f445003d21464007000304540b036080148603400000e1007680441544c00c1c0441c0d40d0056400303184a00104103001d4400c1c2c0440c00080d244800081011080 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 622759370 1250 622758120 622758167
    0x50a0f021606020a0504090e03031b1309020a030b04021606060b090916110d0210060b0c03090d151d1e1011041505030a0f060602210409140106 63
    0x10440c0201c07114009400540060b00c40050710001c660324401c640c444043d290900b1907004039079002000440c02a400e01c03078400205400310480c00e800b401078200e0b006054616080411040d2019001803150600301d103800240030414400003000c83e000f00c041d8944103e0b0340b40b014010080c4611440001d400e40340030346030811040d0800245200720040440d041e08012692191041e4004c0d521903441c0e181003030903031700780c0c50b91008003d645000340c0c54900511403d04e140090341c111018220754050100c000558645035100c1c00f480001d40c5550400c80d15199518100d80320b0b44252302c1204407250b1400b07180310403c036034452541c3c900110907103a400f401c041900241e0981c507000800700c2c42c0441c0c0c04000301b8102c1140c2240070b114055076008034072210800144a18248d80080103512030f00040104005984241c1c48480840300103010324409640220f00f0180119024504050440440084c03c0d10b01600d505280701951041070340d07030840603403600050101a407c0360b00040d810b020605640031 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 622760620 1250 622759370 622759387
    0xf05071a070521090c12010902060708131d0420090a02040603060e0c09130e12030106020d0e0306190f0911092508070216170c031605010e0105040801050406050a0f02 73
    0xc6074a14101d07186d1050103035403100d5004107803c0d0030030b1850a400500980d110001030034500540c6d4844079406805200d000008504024120801c81001e00300c1105001607a9803940ca464685a0070f003402450100216180107a170703a122650184105444600580c80b0351030064050141c804a0300440203400000b4100038090040005072801c140003101d00241c002d40904040c40140207014a000c0c45000f060030210000d00d01000840c100c92903a401c1700c0020361100d00840c0c0c0d490100c0c0016625400500128071008241c42c645203405a00c1d41d0006034a0f60b41c0b480000403030760420350032241c92000381f4202196180c2508401c0c2e2282040c905204105280341c05040c43c04900102c0c80b003800505c201217000310317100b00300014030320111507112403685458004003411000188401c4000c0e00c503c4000300194100415034071401121000d22010142c01c00340150381d074034104038030941004014040002d044400340541409607001d240000350604000c03456100303503100b01185140d0355004200001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 622761870 1250 622760620 622760623
    0xc0a08030f0a050901170406091a19230405071505041a0f12040b090d03021201151b080c011529130306060810050402010f05071a07052109 61
    0x82c0403018928000d03545003103003801690701461140c0b442401c00107100030402001526840030140c01d0044070b142c945643c07024050804c074502101d143c6142064200c81020115903500000c0229101103800031055200c0d548660070401d0885d000d54080c3d01030758041000480c1400104038a000f81c0c905035241a040080e05040c40603204509444180c0c000741c03524440702100e05070380c48101352402c0032141c0d08150400e000e50503000d840400113030090407102203030640640b0803a000a1580e805840a40c3e10b05121451460300c4034020005202507881810310300f801c83c142085005202c5d041c00c9848400c0041441d084641d02001160b00304040e14080c4120f1404041e6801c5100341c0c0d17042d0145003010031006c10100c1c002c00202e882c008903020004410000d0380d80203041600c0000080321560441540b540c4180c401c2664042d0110f48101007090001c1c0c0f0032030050540600075802185500100060010240c808561040000b00e011400c6401030a9510405070300c210a00301ca0340450804801e0107 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 622763120 1250 622761870 622761877
    0xa120e0607081b040b030412030c03150e0a060b1b0601140904080c101a031005060a0b0a0c05150601080f01030309051e0a0603230f0408070816050c0a08030f 69
    0xa0f2030800d0582c8800e208078407002ca6000d0300301003071602d441b4103252070015903100240f8104c070b0100f4109090003881c04d10034460300c0c0140c04038003481400d03d440c100400303130321440141c0b80c4040180c80302d8002c00c2e2860a0030003842c01b40c07401d42d05407014945102c1c1d80e0303045c1030b41038110000e18000b604441c03a4036980c4805440d041900041181d41e64100d0090311403402c0414101150114100510b040101c074035440c02c3c035078034842a010340f010464034504c9001111400c0b201650720a0003040144003981a1002400c1d880070541485040200b60781c8a07146481d40b04401c200302c1800c04401c110403540d1080090790007600051550b41c195045da41c1c080e0420440340192400350807a98a041514140f40c0391000210740b015195403000350701d6044c010007a103640c62074030039000ca00b550343c0785500440c2d0070164801c40061b41100d003030751119580c13820a0b5101c1501510bd00b08184584040703100b28101d1144128802d00050860030207040c180000d8045660041c031036500140a04042c401054044 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 622764370 1250 622763120 622763131
    0x4020906011b1205030a0e0f0a030f020a0804080c0406050103050402010804031d040e06070e0a08030a08040f0506130b13051b0d120e011815030e120a120e060708 71
    0x1c201031072241d1400c0d42c000c1048080240011035807400740c0012a030480b000714042d141008050000d1080c107550903940c0d220010aa800c0c1e54010010240420b100d00e0550028100c01d1040d221250601d807a034410680068000302c3c4d00707030800c0010110900c0e00e4402c12004002c00e0030207000034505030300042c000c040b00a10142c180b01010158841c40406507a5403d40084004d2041221900011b0b60a9071441e0803070780440400e85143c54014185801d480510032038010701d0040d450510b2044c003c862003030740a001180d0303c0c0b4200e0360810001b40709006a9100d80e40c0f480e114044003240d400c2c034505001024041031302024019040f4000f2441c00300703007101080c0e01c8a0740c0a8400d0042e82c08203420040100c2d015220404039034458440139030010642d9201c40090382da48107140016000d40600743e0041c440d030044600140513102174517019030002ca0075100c690090315800303155140040c96940c46a0f07400c800041038658012580b01e045d1094403044189034000b04440d260200c4042d1002c01d01400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 622765620 1250 622764370 622764377
    0x7080a0528030e150405120c0a0b190e0301110c0109020901050f030c010e030c03190c090507050909070903122a082b060605120a0e1c03020f042c0402090601 69
    0x1044a45110070744100d170010b04003d071890740c0c04a003255929480d41202002144100700b40c034800200304201d1015162502a010080c2104091442060320340321b0b40c1500c0d0075015502d4820903a0b05007072520140011240c14400805c480c11b10f1b204102c2c2d20181600014880c94400e00c80d08241d440014110000c86030a080650030000c250340024540720403901d1480d070500c10111541c00c1c110746e803140000c010388694800043c0c81d8552242134262142211060001031003801090118540810800e400c4101400d0102080d9107a48612140189070f462100c00701703030400c95100441c034501804105480c0303034a50508130458183e403804041e200760459240c0d911071506103409040500d104032140b001001c1002c001c00c03603651902070f01e16003150f154180c0d032100000008280e80540e02130208040e26110203840000742081c4000d40c1c008141092204241d8280f01d5460345807081c00060024020b0301804c1142510001c0407910300520f00320f6000c01860480b414000141c45031090140c0024003400c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 622766870 1250 622765620 622765639
    0x50106140a0201060519060801060318020409022806020c01051e1c0608010506090702030310050105030703150b09150a0504060525060518010c021c0207080a0528030e 73
    0x8070103d0140c8030a820030b0b1360003401c00701341c0708090842c00140f004030740d51a103c8a500346e0b40c0d02410350441e10000e07001960009001301080051030b0030b0b0b10a15410b84014525604000c0c1c02001509802e11400555241d03503504030140010f98040268215404091030114a0314204825010041700c0d024901c0145d5440408e000081411381da84003800365419120400c03050b03a40d6800310303010340303002c0e60094011402c050100c1c041c00d202000b01d901c210058110354400c03510b49401162590b000400d0541003550783c40f0150398a1a503c0b007000300600d500310031203882ea003107403080001030354458822208050081207107080070b03a040000d91301140c2c00743c24070a407220003008661250303440700048110210036131b80c03507081040300603402140140c9182c0b0a444507499180810750884081e09803d4015a0081c034031224444451800c10000c20f00c18415586840e64880d00107283c000c1e00017084409421200700f4280b620000703007140496040c0925914070703545003501d01a003000209186240502800c0303 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 622768120 1250 622766870 622766887
    0x4030305062218021207030615140d060b10200303091b03031b0114060303030114280f030314040f090b0d080d14010b070210110a051c030b0405010614 66
    0x110f080000e05a00648240e0302c98085424032074a88500740030840d0602e00e804042144d46402c907400700140c0b2a810040d1180b20710311010007030780c0d00000c0c20440d4826121f40d0a2080b54864401a81c40d425058954441141d02e40a20480340406100c42c040190f00034401c010b540c1034002000b0303845241d00c6004116a0940d00046411840b0b914a0003014007d0727100a24820041548000d2442294059400c0180c84442c101911381c8800e00c502e51a05080c0c0c0f4003190325107840d121000589c85c51042e40d01c03400c03e05180390310041159500c00c40920900310410030a25800010200d404904490414942410700340340c508100414000c01c00c01968807080b00b051038580c000c0b9a40e40b01d8002d500c0d2601c0c0e4851414200161060450041c1501c420400009410806105842400380e0003042d1a24103200e0704400c55034a0050403152209210300d1820f2004503001740708010301080e441c1407008100da40450b0282c2a9801071030f1240c0a945030100401195902910500504004050701507903031410 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 622769370 1250 622768120 622768151
    0x2060c0f091e190608182512030c12030b1e030f1e0705090c03070e060f0a121a010c1415100915031109131505040303050622 55
    0x6045250300b05200d180c0d2030010010345108501202d06075514174115a40d0400040c4400e80c03188415242c941c81400c0c40700b002e024000406c0245c43c00e240e10000055954403210700500c03600c5800b98003103440d0402e001c0a210900c0d0a85800e506c1f681030602c006000000840d082c0c4400482050611144103c24540ca0364144410104075040078102c2c1c5010140c0014441d000122f2510305070799120301e140001c0d4900b0203045141c483c070924207925007507640c6c0340341c2070b1040c040b0403c2c0e056100740c04000a0b05016560000350407085140e55503420078a80e080202001c443c0042e82c0100079141482803038509a07802258182c0d125408030100c095a640403020500c3d1446160b020700d8a01c0018041040c1071402082d440126002c0e508140080000340320200c660119500020708031842c48460150b140c1420028190014000d0701d1040e07200c50f55031601610070321200c01180300300d900e41c4140070038140d050040301d0f040030b01115502014455001003400c15a100c9000c10612511041d4001c0214803 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 622770620 1250 622769370 622769419
    0x12071e050316140a11010206061207090515061305040b060c0c04112a0106090507020706050a2a020f12100e1203070f1106060f1c021c0302060c0f09 65
    0x121034040b190804c5007441c0c40400b2910444903540184100d81c0062003d1400c0360429400c05245000f824400b8200790110002d0324009100e180400070740700040381079442e070000a0040c0030013000e06020140c200001c02c810f8492a00a80d841000c080c401c2e0180c0c214081034030203140400300c8001464000c06d5903400c859000e000c0314080f418400340c40400468041c0580c2101204c0400c0003002026200c1002c20100ca2040d140c960060744654400c2c080b003405400280081c4820381880601c8801042506100042060050300c091394010149000c50828004205810704202c5041ca16610900c0c0300d159038200c001c81e820181a100d40312120589024008010380701c10140c03c1c40e03664685808081c03c0103c440b0701c100b00151015507031b11010395002c0340f240d0040c04000d21340002c0c101a281004031510000b00d01103603c412400170080103070398400c01e0814000b102000407425103000d00300641003a03401000c80321200020031030b03040071448443c03c441d54200f048074110030380c0380c492086100521 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 622771870 1250 622770620 622770653
    0x408063412050a0b030c0910030209040312050705070515040321020403080301080a020102160e18031308011508150a09081908010f15020d0e04090512071e050316 71
    0x14a0300e0180f00e44440950014410b4842c01e03022542070160200a11025610407030700c4c202104d084503401e01c01072421540e0290001d000e840c1041a02c4030070402203089640944140b40450b100081700010000144590b19a10440e51034800e0145403e403805404000602101d0080041940036070304c0c02e281c2c680c1600d0107150000c1c0b440c2c0d00d0f580c40b8041156a2420304d042a07000d441000c0c0c1c24600e408081d100941501d4590502d0f09094642130707802e4480d003007040700d24600382c0403d11090000411520f10341006244d4038001042c1828040c0b031a0240700000c0c0c01039151030300401c010090010818160503006a04c442e400180034002d030600e19468082c030018060207858180707410003069071200003d41070701c200c031554814240d0f0720b00001c10314041a00c420030168009299900d0401d00800705504280c001a0001c1403000307881e5a00390411040782000d02034020f0225810040c000f258001851000042d454a0a40980e9883e103d90b42e0140003620450360710700744040c40c100410417a4400401 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 622773120 1250 622771870 622771907
    0x30b060c010905010212060a03030c020d0305040305011a130e0615030a1b0302030c04020a081504110f030f0f04021c0606180b03060a0b0f240f04080634 67
    0xb2450701502035803001407446880700b04071020a10350303d058404002101d6040d22940031a103420b909101840d82425015000d2180500c000404210300380101300880c0b000503112240406164100700220300c0061169114a1405008078403400e0000b4095070045694090041c0010000000901d88801010010114800c02c6d88844d10030041010300f01c1524403c0b0151241e034418103050004034060350052100052001010034503e50031079917070190311a000307031021540c0c20181050401c03036400a002c0405034003000040100314080c44149980040b0800906241c90400d17400180700120203801d5410141c02c80d140440410006c0d41c4490000c21810307030902c004141d1280744400800104c0238603070003030040b0400903440c0c004502c100e034070142d0000c01c4900c1c00c0d80c0386c4060020f9244002d0402491b00c01e8421303500c2084107030381c001c0d0000c04000e0100654403428001c0361824a50007030b1032100c04810802904925084000b010448926200d1086801000c0c188c0c044611551100848500 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 622774370 1250 622773120 622773131
    0x30d0f05240d1703070905090f01060509030111030c0901020c030c01020706081e0414150c1c0b0414040c0b0a21021e250506040303050415050f011403160501030b060c01 74
    0x3a45281c4001c0d5100c1c085c02d850707548046503680144481003e0482e01200d600f02004014015039001d50082c0c090188040d0001444288500d68030b0035582c01601c00144003d00031078170007100e40c0e0402c88107048020a0700a01032540715800040d5454070b0500031a42840b41010005202881709219520020a1408040030504090a206015480c415481c02480c0900ca00070400e052a020070303d401003042c4c80d1070a1400d00301a01c161045008450034188003612490740241d90390760fa00868200003044003008401b800c0c54641398600e0403c0d40c1c04400c044070240003d24400d0341120030b820f20341944450450f000031944102000a2113031400d8a00004549014200c1114040014000d10240114844103800e1000741d8100c49800840004045900c00c02c00103000920075002180c0281c8540100310750100f100c0c1000c42a01c0080f10101041803520b001001500d13100100c0070740c1600143c014100140142420810b002520700905041c10703141c0d60000419110401200c0e21003800c0d02c002c012 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 622775620 1250 622774370 622774403
    0x30d05010303200c012106270b10050702060714060a0f1109281a070c0b0a0f0f0207050d05012a020307030f0309080c030d0f05240d 58
    0x20760382500001440c000310000c10340c04024000b0b01445013910584132542a0741c240c6017a01c40f0064440008141142c548030005407400c2500c408880c3c0c0140c140c41626440b10102c0c003072003102c40d0340c0011481800d1402c2501d4030b06400c001100c44507a0140c80855071000b040c209040420f031070007848a04c034400d0034100140d89450380d0040c0001c20038640140014010351807450303514080c1400c0305901c0f91103403802400c2d54643e00401080180c501c020001c0095589a001c40008021544007205035000a1108100801c88807904080c003128245581407400c90b54000b015942109a10010f201592201010060080041c88000e140041400c000f41c6810320300380d4041d0a0703044c201e0300c8503412038000c4040e2030000c0120680d510002c0d4011401c01080e40c404803071071001c011126092542e26816034020400c040c0084c080c031100d98004594030f80c414002c08046030401120060042c2c540000d102100e05e40c0c0341c0803400c13070740342d60510401c540702240000e82000d200b580040103410300c80759812 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 622776870 1250 622775620 622775627
    0xb04080f0c0d1205010f090e07050a06021c08070e040504030e19063f0b06040e0603190b0117030d0507110f3012010308220e0c07020102030d05010303 66
    0x1407003202d03540b851508204120840140c550a0086e801415010344090000007400c3c0e120064104456040740d5140b9500c4000c28611103c1c0d030080c400503005103004041440c000c1c42c4540c628105860f21028a241401e80109142aa03c28591140b501c0b0004030b024548290300203200039000034044040328411110b0b007450312209109410102d000e10610800702c1e20380b0038210381025082025221610361920400e0002407800d04c0e400310450b9150302e086142e80340d84025101914011210840030b04201c0700301460004d0022508100f42882961040003c40442e075050440324004046400d080e0b0259403070341540125810860b00724074048c1000308480d4024a4960700304040c0e4181c0d00841f500e1440c0d40c1c0c50314490009800d0700d0f0015010114004090a85140603200b840c0e1114201003007422300c0e2042000031380c410b03a0302e4035000c11120b4050512100c1140070480d40c81c0f0030400180b07001310b80a11b01c1c0c8000d1000d06440c1001c034584c800d590090003220310044d540a8100002c0d0303100d00c0c019 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 622778120 1250 622776870 622776883
    0x7051002041502060c0703030b03190506040b0c0c07140406051215071e080408040e070e040e0a0201090b09010e03120d1a011b020102030c2d0313030b04080f0c 70
    0x544081814402d540c0c140040b6030140100000c1000c20b20342113481d2070a4001d000240b2840345c041c41001480e001070030b020400d4113031741d501c104040d010f00e050504001c85000409455000d00b0340b020002c0510b4a040003502c1c90884030100e1048174110300b00300001d00141007990010b0740007903030000b03060400c81010503030091806140d00d031a1150f8a40d21402c4a070302528140360710b0a200206000c1ca00240100c80b143c0e8010302c6815080c0c607180d2203140402c440d41055030400d005ca000030000c200c0c58603081c010201d40c1c0341e068008001000c03980d00000c01451140c4141d8180b51800210380c40944d02c59900c05440090140803101c0d1034a503280d01652a502041400303101038640704003607000b410303900c03410f42940e0416560310f0020821200d1301a107042d82e0b05800ca0552104001000100505200700301c2d5403d00540d1131100c94441303c0f072004180c40007281c001c40c56002044008200001001207405990b000111440d45035a07614200c8014481c080030200c44810208024168840c0050316 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 622779370 1250 622778120 622778129
    0x81906060207150302030606071e061b3b150f0a12050105090115030f0e010603021306030c0b0706020c03040b0306011803050c040b0f04110901080f01120f05030705100204 75
    0x10149003c880003800c0342240800d0310070b15440a0100959030106414200038441b1840052010404c5245569072104803400ca030100c05100307074048801e1008641004040c1149280c1200a000780c01905800c11808000d03c04e01042e041e580001e010501d0b02e92260f00d4940302e10890f1455030360b80400c59600e01c10b402029000f0000342e90f170780344410103a075223001306812a90081c02c3d2900a0342401446c5003010203644800040654800072440c41c140107000310b40c0c90304066000000e001381140148043d11440103030744001136017000340800015000c25062801c07140d40b80c0f80980c642469243c500082c1c4070740c071511030392480049404140c484482009501440c000d0321044038902080c20200c440d80854400030f442d603003040b105103c080c103258101c64401c40e001003c1e0401e90302500005005c407200c51344106803514000c11031a98958005034141d80042c0c1c0001c000b4142d6242c108120100207454070000c20030010950342c40b003048400c10640f14880d5204d4145d40080d010300350340708001c2d04039225 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 622780620 1250 622779370 622779389
    0x60621061a22050f120c0a0f050f0607081210270e01090512180310020a0f022a04020d050f04110109030f3815010f0f081906060207 58
    0xc40e44211600081c0040c103e58010309400801c4006400b082402003c004c3c0c10034450141038000d881030f5944a10030400303029076000e43c040c018184420f01c416040c0145807107010300c038200302c1030303000c01d011905984100022803001c100360350f42c038001d10910383d005034400041c04511500caa82242a25543c806541500700403c20203200c0940f80c0d5401d03100400009400c0e03400c800d82d1a5460001603006082d0740d0001c4290b003d4540178076000c03034604030350306000c00c03101c2c0e07808103012802c10340c84040358400b403186200400d04c072140702d00d0382202e0304d45d4455801071084a04080c0725035a10380d03806441c1c3d58411000100074503c0d00d010308040b0004110780490782494040c2c41d24a056006254850540c0d404c8041c122010480c1d83d071380d4a884001e600c0b09118001424220310346540c0341d0816020200301c2d10b00f555100d040880c0350b891450701650440d81404480301c14841c0269000084004499407480c00d6061070300c0e110349201013036600a0600500c2e50812601180b495000140031046400080 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 622781870 1250 622780620 622780657
    0x30708071a060f090a0e0c060a020a06050703020f0a08070e2106012c060d0602070c090b0a0506031306060f060c30111002030103030306031104060621061a 68
    0x10200040758010307000007640a90781c1400705e066080342d81d0200b42130721010401c680300030140200203009500f04c642c0e80c50050f4044a40f403420805140505508284181801d40c145030700c00241840f0b03030080301d601002b000060b0b00000c1e0105c0c41090400411040035010100d02101d51540290558030821080310b14421500002102040d90511288442400e01c068644641c070103145c544804014284581c003029564058000c10420320003080c0f068441c40c0780d00d1015103020218010b441c00c2d24001031140c0041d000c1000251103610440360300c0310445c0042600d8045510302480209580d402c1a9611403c035100400c0c0c0c26044490140e91500901105031105052601c0212901001000140c08a030101901080c94028400a00312a50000644443e00c614044c0542240c101340e0040e80000d450307100800501203412000010780f41c0503a401d10a05042c81d6025101910081703803502240d980602c1303200203020f030303070b01c55000b0b02842440c0c0410505c0351019816690029240c40110051b2039 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 622783120 1250 622781870 622781881
    0xd050d150308180102060709060c0f20210303010603020307030f090c1a092b080c030304111c0b0c0904140718031e03093201140304060c02030708071a 66
    0x152242c840e0145692350b4011504081080781c011a1009048400c003c0801243e00001e038501c000b01c140f0400c10300c00c000a81d001400b0490301c134031003410f1001c040303503943c4280412120220459040d6102c604015a4985400c00114005d090090885410500d00000101005602e900d91011900e02000901e22000185144000c511801d901503038024440300d130035005180c050580c0c5071240200800001c1e5040c0c41e407500c0d0f81c40e41c1b20340b080da8640d820001c200010402210201c00404005490001c40c82c1c5c0b0090f650f03101503031190809816000302c0d4000890300c551110444241603000340007400350300840d40302c3c6d180300c0b0340940d500c0c40866041c1c0a6460328007500b1a50380101c03501f0107444180321803c4841002c504001e00001e40030807510203404560000c0340f05800e064031200320920817907001091540000070600c00001c81c104101c85000400700c0501c10140e0390042d40140000403003000300c0c54180e1039445a000d00620310f400c00b050130001e101e0030707002401d501d00d02e4070f110050f01d9560 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 622784370 1250 622783120 622783123
    0x1215010504050705090604090c020c18041704030506060906030c06040603050103111f0507060605042c07080a031b0204060611060702010203160503090c09090a1103010209030d050d150308180102 85
    0x160042c1703e030404414441005040e00b2608103459054030780c015a101c4591500228103200c2c2e51411144c82d87c0040c10600080280f20403ea500c12045039000e141413608680d01c03070341c542d0340142c00c941c0700d03000203400300d040741e83c090000071205040189416992a41e410380074014242c240f0042d52001305041d8440441c2c09d200002c624a1a4050460300c0d03a0394400b0300689454100d11001e0f124a0358440000c035030fa440307600c100000021500564030b051403900c11184400c130003544d000c1100f50010b01c8204042c6000042200640703500d8100407100c1000b080d0b80c10740301c80044901961160806100141140e003000200b15080702d4001543d60507511504140d00740e20094035041d80300000c0c40c2200d0001441580a03542004c1120166003208045900254400c00c0c140d6241c074840d0860003010080040d200d062001d03e58081d0700130750829030b040000a0301c840c1105014024001c001a03000002d0640f54408642a013094400945058482c10b00103400c1e0030000f019400b0528000c034100041d0300 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 622785620 1250 622784370 622784377
    0x10c1211090d1713270c020705011b05160305071505030f04060e01091103010b010c0206030103020d0c08060901060609050301050613200712020d050f0a0e1215010504050705 76
    0x2000b8200e81c058a07001d42d14030742c0700b56010031191050102400401c2528100a102c2c1d002444200904074a140300a605500068480224070590602d00483d079100c01e0380104064003181e009003408400c20940c000401d401c42800b0400034994000d040d56000c0f240b05c42c1c0301180999018904640c2ca2030b40390b503009038114803580301903404141b050001030701c6069030044180e80180f0801c0041540010302110900390307001e2600890b0746003040800c4259606007486035401522092030f183c06c0045858010914a200c10701010b07000e50a5030004000303005522942e07500405981b02215018074101c070070304e402400c0030b00807040040d1720717918005441c1c5014090f0b94001c4200408900c1002044e5680c0802045c501e003401e2040410825404c0c025410080a4401c0c036004109034000c3e8101d1002c020b0510180407800000d20a080c4500541c2d202c07035605445441845091160940080b44005020290030002c00403181c41142044a412852100828104c1d0002c0c0c0f0140700c1621000400d40c0c0501 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 622786870 1250 622785620 622785637
    0x80109170a021b0a170601030b150d020415030506070207150306270f020406091d160c020a030c06120b0603061c02060f07080304172a0708010c1211 65
    0x1d000d041d0141540c00b012076403c142900c014a038070059995945038400241c166a5541610f40250004000380641103550540c00600400300000e11187c040c00079401c4425060080d00641d03903240b00003019401c0e485111f004d907400100711196440c01940003551880c26004501a41c09440a141c80550103405660242c1b2a6043c19800c0c14800d0810041041c021104000d01640c9030400c0c0701c00d02c1200e200400c0500400c1d0342d03a544c107070700340a08901c002c01170003416449104104200061001000c82074846880b440c46c041540103418000180c080071960400f80c5084400e4034002200358003c20080002d4904110601140003202e04000d07803400110340715074108400c0c2c2c001001241d040412485805d10040c046030a0407010030006181e900078180c00c4405c0d04000052009201c680c440007132615948000f07483c40c4c02c81c5c140c450040d070ba86c400d66441510100980b0450419001e101501c0a081c0c0301000b0440054981c038024620160082558049841e020b80c8004a80041d4100c86154 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 622788120 1250 622786870 622786873
    0xd08040825051216260f09030708071203083103180f2904030501020915040b07020603061f20030f071403071a1519180b04020301080109170a02 63
    0x40003607220400350324805c2040700c6500307443d00e040006806402002d4100341c04031100c6240c40e860400241480e1004a40140045a111100c10800c242c407200c4170b00405d42d803624110540c4d03241e08140382044402014500140054841003004284813030b00800580c6000c2c0e48d80c6581104100b1408600d01c200b4000c82c84420700344503040c4a1040c000440a0030030019201c90851401885840c000a41080d0021070303260b500000c1841c0d4920f40700c1b91203d10762295003280b51a1600d0210b1410b164421a50001c0c001d035400b1000a07802d80d5002c400180c0e0138240e0040142e401e50b00e0341c0007401c00b20300c40e03142540a0102561070340019000020344240e4041c1c0c09000d842c00030b150701d070b4079841c110010001405220400040d4006444145a41c440c010754032020745e041d040000a5030b81c0c01c1c0d038003d90785008042d02d1000203440603514540200301e0f40441080300782c8120070f40600001e86008078415412030f000000010321103005501920342207004461290180c001c000f0800b400388034401044005 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 622789370 1250 622788120 622788157
    0x30a022502030607180306061403010e1222081504060509013b030a081e07020c0405040204021b160803030405031e0d0504060c0807020f0d080408250512 67
    0x149000c0c810f075541c80e20075800b42100080c1d49a65001c223403541c9800c50b4280c40240001450541001d0081c15403081c4400090b008031920090740f40903034000c09100b020038007030400c0215083d031508482000908070700d50a85460f03d0184440c3c10b0300e0441030380c0c1240c6e1985007a00050444506102c1d144d828880c05045584c06003203e0f15984100b00f02e51542c8842001c082080205032a0800090101d60801e407520715aa28101c0010400b12240a01c01c0005101101c10020032660110b880045000200e07000681c81d00c440c0040b400078014840110001203055510b0199075030002068072044d00d151001740711003525080d0040c2c40c2e000541f001001c130f500a005107202d8558440b2100284100e00e1020b600708a002a075100c165a010390302500c1055407030340c40440d216449031080d944070825000905a0500100005580d1140c0c0c038041020081001c000c581041100000c07104030303403003113040340311100c216000140c101c1b00c5804048802e03101c0c65070400380c040701071001e0f80d030b8a0b5551154401c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 622790620 1250 622789370 622789381
    0x903260f0c03062b20010f232b0c050301150210060801060e13020a0302091312030615090503071e120c05030601090603050d0e0103140a1b1d040c050f030a0225020306 73
    0x240c59004011b4028655060303d0801201d007000c0012704610552081081b40c0d403518107005105000d51207842c1c07940c290428044000050f000b000b224111a16448100f4085442103000c0f0b0800ea110381e60b40503442d007403000c0028400015000301c4207984072a007204041d919080101d2280001c000e05c002d4000010403010030240c6000032609a01810203003c001c0e00003d41c2c0c0d40e0206d030400c411900c0c00801d507540c0f014004058181c965940022503400c00610560402c4002541c541040c403802e030780031303004803100c2e41100380a0707070180c000b411008036a001c40000b5244c030f00c10601c00341c001e142c0079103d00307000042c411074103004a0f4100c0341c1000240c4034145003400c1c102c82ca00113505040341419264070092140c0d0804460892140580c0d01c40042d0001b860010840304c035090880e40000c00102c080c00d10442c042d407001e01c040a030000c990014408042a07003c0e61580650620751081800200400601d60300769001000560181d40c940d21000010184480f0284483c80002c0d405a10020000d031 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 622791870 1250 622790620 622790627
    0x9091415120f1e0114160203121f0603050708061009050303070803010311011427090405070501030b2e0e0d080c120a08040303110408010903260f0c03062b20010f 71
    0x140c1d22400c47c03040c2d910b4040c4002880003d00300540341c480300d6010b0404800603044100c42c800001e030205140c05c2c80745003030451000380306401c0501501e1040b1031000c403030348005008520510003818041c090307903100d40036400c2ca00d01503002444247d4400841c02e0200d00c107588107135004400703603c03818400707401c2074601c0f2031501003408880c5604000d01d41521400425075500211030f0b2085201d14001e10660f03081000050643d00c0e000ba40502440f401c00a281c5100c81d125841d04281c15100316030070319074400d030703504550365440013026641000500100c40709210004000302a081d080c1e90443e6480800440d04030b006202d4682c1500029240345c001c5030009200c0c0d000b111940200000060501e034031448a10b003101c2c0c10450440101d011840c07141c0140540b001050010100804900c0d840c0c0b410307912103005548010812640903100200140c000c1c0d890407140c1c0c1c4140800134620625131040d8090204a4800070303000c0c1e4806407540400250b0000718040000baa1006964201e2442800c80064 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 622793120 1250 622791870 622791901
    0x105010911040b1c050c07020102210d020309100c110705030a030f1d03030d0605090a02070b18011b08150d0809010f03020f0c0102090109091415120f1e0114 69
    0x3140c00c0d40c54041c200324048070900036140a846d2040001e40e603051144006880e07c103090035200c1c0c21040a41032003041c00d04090560b0b40740400b481000d81e50341d0720740d42c55a0420b401c03401d00c2c00c603d03840c120314a200d0f10352000955010b2401782c0c04a91505840309c1c101176a511386c05000800140807804037110b03040c82151040940e07a4400301142c50120140002411a00a082c2d03407400c0d65078980b41040b4038a445c801a40d009490391100710320b00409500e4594188000a040d8040901074030080c0c58202425032100154070030030500707295400a4880002e014142c00c1c1c031010303461302070340280000501e4080450321000e64803079140c520b8050301e84010350b5001504205141032682c01d0184160040e0600000c02122505100050b5142908000504440c4142d080743c040e80d440c0010b003040c4440d80192490300203e0454202140706006000036442061035500d00a11303020b00320b8003901d120800244844400f480c00c44811040c031003284800c3c02c0f1107815000c0100410084081003080740101c0d0803 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 622794370 1250 622793120 622793137
    0x8090f01020c0a080303150406122a03080403060f0b0d0b1008011a030f0706050306010302091c030201050a0f0c080f071701271107140f0a050f0105010911040b 70
    0x50b1060340d0101400905000101c2e407011540340c0000082180a01030884034614603002114104201400d00c4103000104040701c60041610000c1012802c00344000820400341207071001c0d0001080d44c407403819000d02e412520088801c0307400c004003500444030fa03010701c1460300400791a1513070070900ca84905418140141c001256800c0001e0081440d01e428054800308022400203080306502a40605161090040c0c00b202d0a0304914804d001c4994848112500407809103809a150b00751500064480a039200c040f04840c0d00d0741c403907102090b80641140d0310820726004104941e141030b40200c3d0a90b50301c24000400108404001049007908a4249400030001c0c58510700d080c21140050003803103030031b0308401029485a4a06c060500c03005058245003040d55806101c9650441303640c200a0007081401807080162080d0445040703010000006881b80200440b416900b60342041d50f15441c04854007005542040008100c160b000e000e080030040c00100802d2509242225191054002d504c0d03 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 622795620 1250 622794370 622794373
    0x1403010b120c090402070606150206090709020f090a03060c1403060a0504091a18070506040b1206012d170105010c030c0f0203150106032a050f16031107090908090f0102 74
    0x71810940c9691006d0000c280c82444006252414000e030803240c0d49060342020b0441d440a030411001032400300310741c02218420f00002d070300c488640c0070000c40c0f4080e0a81c02604a0840d45000040c860035421845450f240ea40700c480b06140b02084020451004848040e00310700c00760000c00c0141860782c44032030740c02c4c012032031301c00350000c560034030801400b00f558200000d1007041c200c0794a40f0b405000c0e0070024001111490315044c5001524102409030094017101c180001c00000c940d81d002e004050308843c01700303580055403030f00b10710000c00119280d07010b0000601d038071054004040c0b01c0d41846050303540503110300300342d0300c200c0d07904660420280c04122081401e1144000040c1c80401c00070001e900ba04000210f2581003c1000302140c076240d08031340010341e107075920304032214880648035945502c4d4034050b641c881e00400e0308599032003180007001208054003060300c180350b4080b1010030200d011a0540300c890741c0e10040b5005691950741b01030801c800801c50240245010244241107240600 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 622796870 1250 622795620 622795627
    0x9030c06070501020912010b0a0905150a03050d031a0906040513060e07060305061c0b0703060806150109060207080c04020912030c011506030e0606040905032502011403010b120c 78
    0x1021a415811107101181c03140e401181d880c4003851715540012072418541d008101c020000000159015414407813815441d0b07a58001ca40d8105968094402150001d030411030300554078a03005079951810307210b40c00060701c1d041241811035989014000041c1004101d202942c03100403c00c001060f01600d0303203101501da00300030310008134075005800d203d803848406846014a0004c0203415140010105407140b042d400c4940c004860803411098070036006261400c49030340f005415030040c0742a4000b00c2281c8100c404100080d460f40f050070180b07181c281e80e941c29441c2e9400041e07a0384d00d594040c542c0280c120314542981c5082590107000003400c02040c026501590801d22030866000313403801811030b5101d00c5010001d401e1b05610f80010062860200014204840380c5900d132500500454800c03a2501c0409050020410560309a0380300c000b040710100a80011013a00b089075450304a01185c041080c00c070800d40844182c80c100c407420a80b841c500090b00120a480c4900104428541003050 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 622798120 1250 622796870 622796893
    0x80a0c030209150a0206100e1323071d01030503040b0c0114010e1b090f3313060e01050d0e010f02040b071110021906062408090706140903 61
    0x80c2c40f92904908040440da450710001c1e0000d0601d00000d01043c00d0f008418400c01c08400c20500a950041c1c0c03200d0040700100b51440d15603403049002100f00c00d1614581988200168045000c81c2200c0114007100726181c091030021018403024840940103130130078002044144038030001006656801000011070441503e005541100300780c02131000c003a000710820800076004030545103846030b00c8510505180025000450b82000d04450502689020449007240d450507029603050700010342c4040c0101d2606544020f881d00b184006c0020019040d400080e454080c06040304294810794034140742556400ca180c0246c00080c1c62008150359031079050700b803800144060005000d0b000030079070340e9010900b403101030040c15020052050340b81401368550f00c0c0e00014000d841410014503007003400c0c22420290003d181035071042001c9945010142a02d808031420111503040d141c6980344291141d1003a29610b07042c60003401d01191085680402009110b4050842101d00904403003004011 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 622799370 1250 622798120 622798129
    0x203040314120706050601020c1504180b060406030c081812030402011e02010b0a061b06091a070e09010915030305030a110f0d061d011203110f060108010b030d080a0c030209 76
    0x100f0003691040e1391003081c401c0545c0e0500031024207030000c44406c214403400da0700d1095030303110724810700ca540082694114200410741d000080c0d2007800900d00c603252a501c820240141c103240c1c1c607100001d030035800012850441c45140301000d640c5580144402d0160410008990b800030340309078141702c2103000000065180700c86080413824140c1c000306404514a042c401068541d81000e0300b0300c85210071108124954501c40f014140d00122b0204c0c1c0f40c252400c010000e1403a0109900142401e80104a082038200c0c80110410805441d50141c0360382e280403540444214403401c84282c0440e540800100c1d1044001c1c68020380004000202050131889420366a070220f10706000b00321020410302c144c5444c512624004003207034000d481c401240c16608200075a01409001c600510301130620050511641040340400c6141b001c6682800341404800ea4501e003d1207208400d60038444100001d0070046086045100c080d15000c0ca26203880801c1d10103059629a06410540e007402400c205644 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 622800620 1250 622799370 622799377
    0xe1309111822020d060c09170f0613060b0a030317060a05030309090c0c0d081e010e07030911180609011403030f03041a01031b0902040605040314071a0d0f0b01020304031412 76
    0x201e9151f00403000d01e000006e000341c0036402044911500000b0041941c2070300452025400380f003110282083d030712145803050091110006440d0001c5040720048109a04560800c1c1020300300d50240c00c03d65120800c100c0c00e0442c41c040c680e0107810a111030300316400e100f0052a0415849411981071070311480380e040c03030580e00c4403566000661500030320050050902101005181030544400c081d8100a04082e6811025080e401010341c5c0e0514103050150010b0030b030f0007040000306044600c1e0041e05083e00c0c0b03d4010b0310707401e10038580000005041c1e80000403a01d041e03000a4007540c2007049100308030105410003082036508404403820901f5881c043c0d020a4003861081060701c2d2003181e440d0311030050100c1c54100b0085203104010500005802905a800709ca0b800075040005003203d01c102c0c0e0420006601100c0d2001c2d40059000600704032801034200c0030241001002071041b407141410680e80c60603801805a0400c00091001c03450481390008a4040ca0084030030140c048140b40c20b071540f = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 622801870 1250 622800620 622800641
    0x1302030c071403030106080115210219030c0f030b0d020418050d030c020a02060d1d010b0114040302091b04030b041b060804120e1309111822020d06 65
    0x520000d8041c04101242d40010400c6020400450030341d818202c0240c07244106020b501e003640003149120107000d200e584218450a400307115000304c150b1340340b03901010750420300c0d41c0041c2c03001090400300d04610138071560006400b9a51190f404014682c0190010403074043d0540c4c00841020040d00540c4070b60098904410340c00d41c2070321740300178075090250600c012050505c4c00c05003070440015203180c0c002000300c2640d40468500c1e40e901300742c1c84003c006102e505007a86280b03140030260006048190701c00b5074004400c0e21400001d0781100c507040442d100707600009502c0b0510b1008513005c2416102068221340310651424503080d1251183d40c85400101c4080741c2c01041603c0c40a40307848020700f136000800349400d0440c501d080a40d16441c02d43c19244035902006442441e0503841d94400c000961486107030307802001482c5090078850510706081c02c0b4103029182e405008041c014081c0e84261043d81804100e1000e4075a041d000c081010180c402a070380407070181170000204400e403082c0715220 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 622803120 1250 622801870 622801891
    0xd0f02030714062e050114071b0315060e0103060209040e03070609050c010816031512050f010605012c0411120a0509060709050909101125150209130203 67
    0x6150258460321240071000308000004e100c0b1000b80f01d254040102d20050b41c030300b424500c0c0400c4116941034100e00400c0030140c81d01942c05044c0d86118100520760042c0c0f0b019401c61310490321170440a00c00d6980a00c540c00c99440c0000041011940e45d5000d410200c400038000700d242e469010845145412410341540c031503a54140c0300042010801000361200f2003030030004040c4c90444000c80801c480ca1310441300b40358581110441c0b140700f00c40c0c0f840c042d103940d01c00c602c2d031640203041c215651050a80c50312a198039040c8080780342d40c040c2d084d284400e40303416980846a010b00c0c412081003440c92541750f400517107400402e05030855000c05008409581d98a0154038a402480441652030203090f910307040d040b110074842070b2544035a404040e81d10980b200c403495201c001d0307100e02e81f106c1c0c40c2c0d10350603552600c10107a0003c2c11900003466000903030b0b03c0b0310b007080340d401080e0a09416000c030004c02000c08050741400100030b5070050414110020b000f00d0500355000420700c1a80c0c81100c2c003a844 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 622804370 1250 622803120 622803133
    0x10203011e0603110a201b0118030b01061809020f09010807030b090a0c0c120816020d1707020c0a0303180b0c10021e07050a02010e040e0d0f02030714 66
    0x40ea01d14240d0400a20540c5030034016501c108005021078070501850008001d02401868101501410403021801c2010f0899041042e1000d154001c50301000e04940015001c0003418208101241101c0c2925005010809a079207420800e68a051008480304800107180c00c002400902a2029103c0d030300c502103030f442e5940d103548001007000c00010a08030030300d464000301d07961a8448004055100c510042e00190982c3e0304c100545045403040b400030903055034443e9151085a000d4a4036014410300004400007805940060383c552454103070f0000020803084201d2081c64120f00050f420200d1401070311102c4480c02c000c40d22110702d9070000e0700030a0824034400c149504841801c80240481b2961504010040f00e042c0e450b12031001450405940100381185690030611a00d14629038400c0c210b9a00d07007140c60100e4840074500320a0b030100b10a408050104c0c102800340c003a0001000380500707a080040801900c0d808000310445085100038844100055500103541009040c2c62004201 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 622805620 1250 622804370 622804409
    0xf060b0f04261204061707080103080904090602030109060504200d05130f061e020a050909040c0e0901050f150f150f0f0414030106060207030b0618160e0415061202070501020301 78
    0x6c0920078103121599a050404003c0d041ea4400c0340181500e50040d03040d0380c6c5080100006014003c0c0ca03001822041c400000007036801c600e9403000d0211034086e9418860302d0040c1620f04d40c9070480314255a05a03604004003a103500c01030344903070b40c003110341040011840c0f015100c0b1100b0300c504440864880d580c030035203005800c0480a80311440a842d0105500d8142400401005401600082d80c040c41e44100481d0400082c40d40344000741802458800306450206142c1d0701030320043d14041c02a00140020551201030040000d00300d00000d0800d441d404120740c1401514a4580c0380d1440340072081c88441e50311011000100400c08020440544881c18100250554400c0604452013a031400b14100000c980110312207040300d801c100382415654a01d0041195501031112180c203013030000b020401000200340d200040030341aaa0b030f102140d603141090100720f0b0a0b210301c7c0c1c070380e08101d040300304859485440080c640040e1f04402500b0401c0d02e0747c48909a0b04284c00200c06016411142034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 622806870 1250 622805620 622805627
    0x20705010f052706010f05040f0608160603060e04030c0209041703090706080105060309070e0a0603121d040b1e01020f0d110d0201020a230903060103060f060b0f0426120406 76
    0xa07407000f90714020313040d0b55241451011140046100325406151102e180c00b809824561000e00280911001d491407019101e2464500c3d000b10302801001c207140031000301da80b004480d022881142e1544609440301c105400300000060000d2086030764000c0e40ca10b181e0821803010280d8003e900d00002041d00e5820f00c48041d0010740160855030182d07006004004a002000602034200c07500340903122200e807507001140c0084c01b82604050054500961410441544243c400d5807a1441101d804018007003481040181d80e074118031141c1c0981100d490107030004a0802c5104401c00500440e070800030061440750401e9101d00c1c01d0004507421240c4117a2403103081c80401050f2203244001c502e80000c441014040702c283c1606a008002e107a113040c400a100e00044904d61340009003140c80640c1d503480c0c44000340040c80d0001c101c55081210000d03440301c40c0c60039610144510302d5004d042c1030811100c510200d8095500343c1c55003054554440e501c0d1400d0086010104a00d40300d10303612814004040e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 622808120 1250 622806870 622806931
    0x30103080f0c0d1817030702040b0a150507152313061a030d020307210c0b0405010b030f0a020d0227070807031527020d0608031e0418020705010f05 65
    0x1766640c51091500f55481304084200c40019a045170001652200280894042409600460b210085040200e800700e50094081c000d258030072089030140c41640d01c03a210943e6140616080800140410f900e00c900620b0300140d407010b01048940740c4440c59071203290991710101041840700000ea8551404c5040a1140d4807003494140021841d2580325604d840007191000c1001c0d500c4084c2824408100c0d104040500c2c00540081c20600d1600b05800c00c14000c116442e409071083c42000c051091a03a00403507400c8213503070000c260401d0700c551a0240101085500364070021886864148004001103800c603034064101c81d0340c1c80d0414541440060704807401d5030b2029035a08122001001441d50301c0c0c4407201c117416003250119142c5907402a1201074000d507000c2c1d020003801c0180201c0c540100001a22030b080041141d007003010521620112130303124900584400c0c45074415000800b070090b40051032018490030000a0031041b0705124000c441090f40d00e8048500c400740e40c4c0844460800c450b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 622809370 1250 622808120 622808129
    0x9090109090206180301140a02030906090705100302030901090f08030a1a0f0f01120c02160509010608011a04051314060307081e0114010311091803030103080f0c0d18 73
    0x4100c12001d68002408501461140d040780010011400c0e0442d1007e410207070b500b02192154403030508104501d6800303504201d40384405e9102e1705c0000b9003404000031798902200c8014050b0390500d929100c040307020354001045103043c1d40d200c80d902d01c0004c032014400368955000b013003101c1d26424441c03c0b0506455800c0360310b4050901d8588100000d54031192401038003502207681c00400201c010050310450700c010f20071002c051501c1942c0c07410640205101011020b5441581001512201000348401082c084d40c030004e1100b00041c400300c20f80c56140762110445500850034542c1e1000010281d03111492182c00094449520039040d0750003032282a00400c0c01c80181c9001d5041518040e95030032442212281d081e0781e0510998200d00c00e60106108561840c00a4241d685905004c0075180000c0c8070039028040c0c5e5400114a03000d08240c9084022a56028610f140d03c2c68030b4002090b0082c482e2801180001c20401d04d070319908020720716950420340c0302c1e108501000d020301002c03100d03181d10 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 622810620 1250 622809370 622809389
    0x30c0a20010f030c17160311070c03020411040b0a030204091a010f140408031602090709120f03050f0a020a200105030c0d110301030b06030705040b06091e0411090901 73
    0x4032249503a004003002402a01c280f4000482000181c030446640c0340c0d0201281c4100416028000c55090080011158621a84081c01022040d04040c4181d01c0f4007600134010242c860410303c0149041c2c0c200500484d4050103417400c05840b0170240c0840d60001c09000f0100c0d034006002c000c4007030180200c4001381c01801d40d02c00902c107174100203019440403150b121b0403c82e10b403542d8401e045c3c151040d603000e01003410807245c40c0c8522543c2508c01c8802614243e01c140e0307140300000ca00328410b22010041e07840c010200c4000e40303000c0c2d64003c44582c2c40d0303a08400740181800304090918111024284100c4c4660081840100c582001e4040481001c410f41e500b00700c6040303c1469903001001c0300d4000c1940ca020320b5032803501025450081c5801120703038000360400800041072010303821481c1d0188078103c09807050150b4480401045407008410150804000e2081c0c40c0d89150400465082c0100980748041161149000800700c5943d41e08000c003145001c1080b4410f4241104141c0c05010143c4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 622811870 1250 622810620 622810673
    0x5150102031902160902070b0a0504050a0f0203100f1a060406051e0c0105010e01090e010504210c020306010626090705190302060d0f1401050f1c05030c0a 68
    0x140001c0d12071181014560079031440c0d88400103101d10030000d207800c40c414414541405512070951201a620030720f025128906054040b55441c5503c5c4140707030040354001e0003080c446482d40da60818440c59220140d034940a515103000301e800507409080b406001c03522000400300a1000000705452079400707114010201840248480354002c4220b41072441d00c00704c12491086101013a0750700340320310350201004d5401c000c000542d00000c400014182c0d0003510080c000b4002440003542201d00c00c07a80503040041015a0050708c2d802d0340401c08072a00140380208a061082d000b003854a1402c0e4011800141d0b004d110880d40e0400c003600050000603060510410300b08866802d980c0c09560041a20810a842c41c0c2c50280004d10500030085602a010507107441d010000702d00100181103d0452107170a1103c2d01d140480d03945c1c140e606aa40040c061000780f0321501c10700483c0074034811202c40c034200d4000280b01144003080a80002c1d10700304018003d804142ca0031004c81900520303020301029401 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 622813120 1250 622811870 622811911
    0xf071d0604120f200109090c1e0e040c02210c0703111f031505090f01091d030f0d0c14030c070804050d0609050c01050f030f060a050619020105 63
    0x15822541140d40e00c140384440318005081003003103104800c8000340f04c11894003088503090402c3d11640d00c5520309803100a85203075141440b0095a8240100b9030006030005003a80011145200480c1d07011180e00d412000c4040c40c10104041f1144404681d0150313024401c0320085001e4844075862022030366180c41d00389900d000c41207580b0142c07400001c116510680180056440748120034051006114000c810b80002d0207024000384450000d01c0001c0301e40210110301ca00305002c100b07008440ca1110100141c1c43d01386071034020311030b606000b840a150b01400e0b261105003000a00f4501150308080c2c0c0c1d544000d5000d03042110030b04a182e80034004a034000d08100300c00c10050ba54000c1074101e00303a580390b40760300e03001e003851041e41c10055102d42495001018845241c0c4007007905e034828400c0f05c0000400c9801941c050140340c0700104808010000500b0002c01c801d0070a4115001424003410507440e0800200181c11030004082014007001d02d040c4141c3c1c1c24019240c002e641c10703a00140700d8610 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 622814370 1250 622813120 622813129
    0x2d0516050f03070b0703050903030a080906010b03190e160e0129041202011e050c010608010e03070f08041a030405150609060907090305070b0406030e061012060908030f071d 76
    0x1241301da01c0c05840045960800e00d07006104a8141010040540b50748114000c0050100001624010400e11411001180c0c080011086034020100c2454281405005c0144803018240480c8480c1c0da80c051140c0a50315051414001c00c0680141c803403e25041d814140702c0aa000c086e201031000402021520b03040f41021201110169018080c04003150481400169080c01c61801188981c1c0741c03d03850b0a150543c09400707800c241514800907c07406589842003400d0751442d80d01116250010040c140002d074008540006061060328150f04050307460009092016402c2103050810400200300700c100f2005002a01d0750800e1501d581e9000c0c103209000c0350117840002d00346402201000082244039001e00344820045a0100803118142c0d11140700c45040d4025200700d0020a0515100c0e82403200003141c07483c4100411003a02100a280107080c201e21450700a040e60320a540300f0a40700070802e000011032080e1024210690a8240410001e103542800c005008100c0c00010603081141d0300d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 622815620 1250 622814370 622814383
    0x2030d1b0e06030406110d02030609060a030c051306080601080a140a0b060d020301090f150612020f0904030908011b090b0a090b1c0e060a110a0c2d0516050f03 70
    0x60070368140fa225602c0d850300304c005054062451403200c00c0031641c8411b01d11a80c00441c42407009841101580d1100e0041c4100e00c0802e00004001c40c40c40b10003030165040aaa4003c10f0062040c030208149a43d007400c1410204203030403500b4550010a400018410407113000540088140020f251849041c0c032284001040908203e01c900c0c0c100302d42c0b40035503500350031020080d90811486800d4a14525007900740e10800c040444a050808400040c0c500c259442845019009403c034001007028404110aa00c0c00030000c0702400710b24503011840110074030645407000309420032507501d5001c501020308807420551100c2c0ca0400104402c2609907400840c1c0f40440c0c1101d00c0150b110b00c4861034004039071100840d03456816140181c031000710f11000403814000d0b0a007000410008001d2030b1200b19038421b0000d6003010840d0101d241000031b442c07118480804840082d1104502c02c040403654440b03032040c4054a45910003000011014505940100102000c9801c0082c0c1d605d08c43c081303900c41a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 622816870 1250 622815620 622815647
    0xa121b0e010e04020d052406040902010e040f1814060a0506030d0c060f0c030212060105090102280c0303110c0f2803080f0d0507022b0e1002030d1b 65
    0x10000003c40e086444616441002950000942e19030002c0103119851407011407244640999814010030038a0030103100c0c17108c0098042c0e49980d0503001103001d110191110848922940d581c581205143c040c0c254107c40540b4800d0132080b003d45c7c41d03222120f01d407038400341040f29004d240c081884801e64002030094080710841c14107826941c11030901200500d05400341000c15070519240d100495455402032001d041c101072081000d86030382004407200d004446a417405030340800c8500321810196048c042000c078410316104041c04280e80c81c04002c01499004801040c0040750901c100c00302031010399980e00e010780b102202000c1c40400030b0010030740b281645041c124044640f95400c0d0f010940c1c0005990410481580d52405a0500c0029400305010084e6645410301207441c0d1840462130035410080d2040110020300200c8204403115591401d030f0003480303000f81200c5401c0e2103104807421b501e0f102d0f4015544621500b12480b040d12009003484040d002101405000c80b034008903024040b4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 622818120 1250 622816870 622816889
    0x40204061d1c110a032102190203070b0f0403060c050904140415150b1809070203030705071101030b03010c05040821180d051002090109170c09070302090a121b0e01 72
    0x40c4028804a078240b00300317030005407044204070034101c074803914150b01000c510116401c441490b40301e5000710480c8000114001e506400a00040040c00d42ca4405856100310130b0301814a0240d0320b56a0800f00c0e0000390400d4081007001c2202140ca261a1144000f030040d452060421858590b40b0103c080b60001c60300ca510980c3c0f031060a41c00e038881000f080c084c000c0051302c40e40d0b4040d4080200b20b092142040741d03228580c00c000050001e480842a1307030090100d92121410001c0590f2115416007186480a0425650701241040d0b0707036090050308443b011a850b000d5840f0304000b0038a0809115454210b685c0640b00340b4503d440552008442d94039200c0c04a58a07241c0d0084006887e5400740f840181c014400e5901e00c03020000182d0051002c000240c9a00e26050b941e1151070302d0342100d582182d407ca41150682602c1403c00352130003035010f07601d482c0c010302c5c0400c00340014140c100160400c0800102180c0203004110701c4006c000002540d4020352001300c2e1a000010324007103014012880d81 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 622819370 1250 622818120 622818143
    0x150507140a090302090f0105030d11060408091302030703050115110a0605100f031b060809030a0e131404050105010b09030a14030d0509030a14040609050d11040204061d1c 75
    0x41c6104240304006158018442c600d24101074001d07480302c2c0420b00402d8464010b1244030f9018601824440d00301e840c1100140201d41c4c1c46495982080d00181c210a411050040081000180c0c0d1310040d8840d48c0691400a078a50410300044481011064050248448040040c3c284103000805c60195644000041510360b1750050540ca96541640000c0e580194a1408000c01078140504096242d01900300c1c0c9945584d4102210a02001c0d1420480c1c0e420030000f5000c0144507180050259101504440d90004903500040484d4803101616006804440c107100802200303008250050028840c502d042c68002000262134111410005002c2101182c04652400013801030320140300140104101502d03041103101e460790f00003042c1c01d001402e41c1c40c4250107000000141c4090b0b550959a070461507040105012121922610a5945007801d0081155a83d114001031001d000b0f036948a09140c03a880c6044119803d0b259034803403180450b4400340c444500c03a42960342c40b01d80c115810846 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 622820620 1250 622819370 622819387
    0x90207050703141005160912110a080705120607051c2004080f120a0e0102010b0406060c0219081906090b0907081213050f0a1206060315050714 63
    0x5020142c0d0320081c803810710050701140b902404290460210b500d6081445a5950300c002078118000303041107040840d040140600641d01c802003e0f01e0554881d5002c40048040f9200180c10140c0f81ea101400340d41c458039050065041c584905001c800010005002d40d060245001c0c0042c01944000c0c0394000200c0c840d40c002d01d005030460301001c15403043c07000d075500401540c0d54003540140501d440c28410b4031420751004038002802241c48216001e11400c000580c401102c0e20500205507604541d2640c95026040e070f20f0f071040c41c2c001c10164458000d075520038410b0140c0d81d280241c03004c00851040000f0000340b03001242e80a0700c014110310802010b60795144c42c000a00320105d02070101e0100d40200070b0030301000260f00c03042c0c0d2809021103d0110103c0000041d6201e0944030b070201c001402c10800140c101052840000c0d00020504900e40e41c07290708030300f14140f14860582700c95455240070818400401444103522400c07880500081c6006100504868046030340c03e46101c0300019001d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 622821870 1250 622820620 622820623
    0x160e0106052101030f0b010b07031e03230403020d1d040f0212040c0f0803090622030b0405010c031b05032412010509010b0a0302100e03010914010c0f02010e0709020705 74
    0x44140100082c292081d40c40b814154210314489408452600060b030010540010b207034180c1e6540c070303490707034038089a800081c85140f2055014850781c000d050b100c2101200d1401c801c10000040d446024000c000d9183c2418000e103480418019241800100e5800910441c0050642d05503401d0942c1e02281070018000f0f001c0084c8904240840388802c58018070040001040d60001140d0f485500081010386540c1d181d0740b0382c41400742da107a11078020401c0901c0d00b070721000d12105902525800e0748610b41e903503ea001445074101c4040301d280c2d6690300c420a0b01c54040c42080c00340e88078000311010b02000690003421a10014000d00f14101e680c400701144003455000c0c2c1c03000340780042c1090503914580307068180038241c16200006554241598404682400440d003400c4035001008100c86040459065400e0024240140d8065495001007000f0034003071100300c07001d042028000900c80e18184002000600160300c940b0071a4102003414000c50b8000a6036802d9a4545000590350207041c580305 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 622823120 1250 622821870 622821907
    0x14060603131b03050a0c061b170c12071209180e2a0103060518010b1b03030117060901050118020a200304050a0e070f11010f06031202160e010605 64
    0x640322001d8034440841000400320b45c6a01c281c3c880c82d07204004a84a16050f41c030004001041413075400000c141401042c403151b891402c1c844004104e52170f00c00d116045600f0051918000c1002e2000000d01d4001c10009507a00e20761103030079103887c581030b605052400040071880c000300c920943c3c6500c0e1a400312103083c045642008000e0101d85d22800c00d16440b02e400350b00d400c035954003003071600400094905060100456078034240040c1005a0f09044040303d00b07403c40300940c4070800c40c01c481c02141040030001903018200c01503004d0174000405120510f40300006192001d1a41000010402c06c031140350381c48c0c2c41110384440981c43e000f6115049407a610078004525408400e9075107028228400300051040d50000d585501060b61141c1950240385000c0e034880c00000c5a0283c100301c5144902c1204100e00450800440c0004501e0008400d07241e0a0b04241c0348174441c2070746018102c1c2c040000300b140350701c0b90b4210124286002055841d94005200394000c0c0513000824040418024421 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 622824370 1250 622823120 622823153
    0x1270201110f16050109120303090305120408130803090a090e0c03061603182112020310050f270c0c030318011a03100f020d0c0e041406060313 63
    0x11941c80040d248038042e070b1080f04107005080c4140a91021606500c14048001594900710781c880c0200c03001c4d0b804034001c005000c000c3d001c20405001581905010401c064065030050007260345074903062000300800c542c0395110300d800d503004008184141c0c071222001811210f5040300068407080342c1c00b0241c03c200504051562501421301040070781d5000210f01c03000020555410800c1010780e03004c00e04001895000906180003101913200c050f0410710000003d1080c5140075210100d4018608044c2d8100b691900300382d0001c50000d0100f4146109949441e8104030307a031000101c8032240740c0081d00d0301d1420550100c400d203c0020581480341c000c44035404da200c8110380c0d036072412060844603400c0c0c6107080340d003950810384012050a00321606001000b4010081c120110b00d00d4164801418450140020f0765001d20000c1803080061041076022840c90300c13810301035490340040200f00e0b131842e80c250800098603c1072020740d40390103080d282d01010741c15511880c0b501900f81500140c211081 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 622825620 1250 622824370 622824373
    0x21e120a0c08070b0a210b040608060f0705040f09050429010f0501141c0b03010501140405010803030403050f0d02070b0c04030b071e032f0c0f0127020111 68
    0x303003020048011004001c480200c42074520b81d544444042da000d01c01c2194920020b041c0312450310360820040e205100609419100140115045000c14145c4200703500003180d42e0400410802e40b00001004c5c283e2200c8213180c072500e09421310440d038000e003884d4094100a01d90301c1000904200511000b0b200b003200304204200040f003200c40c00b031000e440034001c045640019900010301540900c50260344055034504c0c4604056800c0d40784081000d2200c80b800c16551a1710548000c0d2302c0030320400d406070000f501c041201d10100700920041d01c070181e20591090340b08104100100350f200c800c2d070707618490781c1c2d041d590740e6010f030994071000e07000d2000e02030b1403202c649003072019010300e0000400c202c82c811070401506948480050300c0300c0200c0b456108180140c0003c01c18280e00c031341d00001480d11400320501d01c40d4030040c0101d84058447c003a000c12080c3c005a0f8a007210410810a0101c3c0c014000034031a4907104005110040900200c0715160301c18032908004581c040c6080303080f0340e00d9400 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 622826870 1250 622825620 622825633
    0xa03050601030c08010b10080405100f020306012d08060604080601180f020c0c12101a0a050a1409130609030f0e03120f07030221180904021e12 63
    0x14000d4032010300388400c030740007140800001040c600601525040303040c0140b00e080d10000d191000c0c0c0c0c00042c018030881e01c030f0285d01d46001a000d8907100d0a0b440c1c200c45980141c50b454400005003c8101081003211041c426041415541728003a4051032058844d18010510351161800318203d4083c0e60440b0465014050000c00c000d003440041000a1200c1c00c0c052082e2840b07400003108a100d401c182d6100e54002078250001ca05080d4204c92407031101e00102c4041c034419040c2d4004540050031600d403110002031069919242105001c00581801c0303c0d0b204d803240c039000c18012010140c0420501a403500c500140ca03014580c00041852504000140000f00705441c00034140c0c5114405500070900710142c0b050036050000c0da001b102000d02468514000310290100e43d203400640040341148100c0803250740e0305080c0c600707008007200a0801c1c01d407541d50600c4002c10000d04020154010300c00c0c40e04010260f038501c030b1281284440c940240b002411200c1c0840d081c039a946000c14030b14842c44 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 622828120 1250 622826870 622826873
    0x18070302060a020105070305010e09030d050711010213080c18070c08040302040507020d0305090613030c0609120206040c0b161202010b04230c030912031f030305040303021c091202010e0a03 83
    0x64005d42c2c8100f800b80e90800040e07817200107e0901c09026a00c40c19590300911000c510950941c1c4055041503a50920020103080203002a0aa07881900800c0e13445141110400040100f00b003907800161088a2812a174044840707020895200103200004000e4142c5011061126001c02c94014503000f610601051410200282d604c404003120800041d02c3c280020300d05104c00324100380036204c2c01501e018142e01a481c00c0710710301c0b2051425102182d07540d0000c00058504441410500b6054014044500d080d090008051286d03602403c03245404200151b055000329160f8900c155200086c6200042905002c900601031030304000e07001071820840d550b000480c2c03028800502c0b032020030303903e041e075401211046602003038408400170303800080d516007030300403900c0990761100951b0041078010b02d0403048548036010942c0b042d00420302c000f509000b4540e05004181a0070b4490040b0244400c01000c01404904c5910a141e141b108845210701168481e8103402c14081c0b008104041d83c0740c40c2d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 622829370 1250 622828120 622828123
    0x1225080d0501050316050102030405060d020c060108010605120d0f0c062306040e0a0803010923010b090a06080609071d0301093c0209070c020618040b01050c030318070302060a02 78
    0x203000d590f2003886106207175614040c60010702019035506a000c0c5041130300c0c2005000e1560010000305820701d409014581c1640c0041103c0303030084c01000000b085251600c000c0c0301086c569004410700c582c00c5050708010711072304002c4521101c4454503211156001034103080000300400301488040c040769500182c2410000110302c0d000780c1d0200ca00b0020040d00c081c0460b9a041e9201000340040d109200411148210b50321040850a41d80801c596090301d000309010a91000d800c2a4005030000c03a000c040c9043c8080c9000203001c0310b050100c1d0608014000940c132500080066041000c41e0392203541d001e180011006002c14050028010000e052422811000d2540b0b00c106030f100d01d644114a03d403082400c03651480014406104a60440341c0a00155200040807801480307144441d00703005884401c014651402c03407120103902c400c4800208000d4402071b80000f41000400e00a100b0020408801c507508100c01030303880d141070074545291178240752082d40080d600c01c0b000701c1e482e24010f80 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 622830620 1250 622829370 622829381
    0x210091b0e4515180c040902010c050303010b031b0711040506030c0307080303160201060e0109020f07021e131e0207051204080d080a110a050c0114010f050f031225080d 74
    0x110f440344880c0a5403070903a0240351440340000c1c0e40c1c03141e04c0403032000c59034140b41d0300c00c00500303006251509611100d515900d2840d4005c5c0d00c000c2e103828000040014900707001040380420742c0e5008925140000725103a100c982400d0104a921556456010609968041050840c00d00010f02520403813a41c0f020560348a17001100d452101405e06000c000c840b52041c865241074543c0c0c0518882582d09001026009410900b0902d415460420500c800b51b0303038901003840800b4484650314418080d080501080204c1c00c2c844c488003608100b01510100c0703d8807100500c5240e42c0720f0050700d4000e030b420414503280c500254802201e00010380490700c2440407800240711201619103c1e6a074a681ea4220100c0c4c1044541684480050240b00c9216109400800021400000110300c040c0038292400d00c00000f0390092074120307081d602c1084203080611550b46030030305c110040c0c813440d0b111700c02400040c4249824201c640c0d056038210800110010314030000c00e900000d4003070b102c40844628600500 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 622831870 1250 622830620 622830643
    0xd06051903061407080714040e190f151802040506070318060207050d030f12052a0313060203070c05190b090f0d050a0210091b0e45 58
    0x50615101603011003811610f58090341c0140d4414501d81d5411a08842881c1c400d048a000e050017004009103214804c080c0500655080d484004005000310001048403200710701c1d089110706040c484108030b844400b0f031504480c8564807428003201e0542c45c0000912680c0c001551003140880e0080174998400c039880004d20424190001c096200c40060742d5550301445107550046150145200092051200403011340c0e00d42031120b1604003109029090f40d4040b40d0240c80580d03100c44801030b10030701070b01105082c911600340500d9030419810389081c2c01c88290300a03013282d40001c081001c00d40300e0505409000e8001061382c01d402140718403c0c601c00a000c2065603103804617000f00c0d03520140070034440d0100c0c9030b41c0c0050950031002c04040d10b1b01e4001c1704d6200158000d4120702040d4420b41d01a5041c190711500f0814005103203640c03e001d06d509681c0207010421000e00c00c0084910410401c0084c400305102c822810300106d02512601319903100c0c113000d4030910509014621100061304220350f0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 622833120 1250 622831870 622831883
    0x2040e01060e0d050d050a030b21010c030213150c0c0905100b04120209091606030905060703020301030503040e040f080c1b030c0a05010c21090e150609060d06051903 73
    0xe92002d0b04101c03001c4560400640380340c02842680800c2d0340074070001c25100b00c032401c1c0407542c068214002403400442080f98030250000f51344c0140050820711a1214080c0c43c1c0c01c003103040264000c85c1c0d030303c040d540d801000081d110585002000714002c1c0034000b13900d503000110b04130340e0b44c8560b5550b003c0c01c026034400107803011029021521a080c030782a038064a090009980d0881e40540810007491000780c1000d20b54000e04902d2821303001400d0410018010303d031004903000940b454013600d410b500900d0a000c151061004cc00094804005c032802c541c6800702d248100e072254200340c8424401e40c032008144040019010407018400708a05403a00c490980003503019000c0d1052644650015400b690b0005c41640203120660040020841480c050a00c01d00e50034840340c0004000c20421080d100482c100c19420007038030440480140d44441545c4017408a118200041400c1c0e0145c090841c2c4210804181e0350500032055003c2c3c001040d0040c007040728040300396000f4081e201c19010594a4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 622834370 1250 622833120 622833137
    0xf2506080405030d0203240123090f3a030207060f1106041101080604060501140c0a1709090108030705070311061908071706060d090f08070b060a24030c020106080102040e0106 77
    0x86601030b541001c0000192700c60898013040d60401d44100d5400300810700e0b0300518801c070260301510f40844d511010030101e1a180755100d110014103940d40e1104040365a0014100306240c00a540403544104407101c82c1400c0c11040340100056644410172103102401e4400c0078200000c0c008440c5c44d00c0e002170000c0c0c0721214191502414001035031018020300340400c80c3c06440200d41c0d001d400c0140344880c0e060b415103419400710341d1461040c060890105041d10310114203042a4900b01d2150350041001000462510155940c2d9a80b41c5d4261310001e03128600f417602d8508551518021981d002d0440c00c2040c00171242807902401110003130300c210700000c0083d003407007041c0c0150760b040500480008183e141014000c0d4540c1001d0005407004a40fa42041400200000d20281c041c05107203200f000400e43d585050014010003006603072107540c101d02030041800e000015050b00ca0b03076403005441c002c5011802041c0a80c0900241e0b8050480d0398400600000c0026100500c1d505949203035503520b1b030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 622835620 1250 622834370 622834441
    0xa12120e010c020d14040305150a0525200607080f070c240b1903060b061206120304050a0602010209101119060603140f2506080405030d0203 62
    0xb01d0b0941510000980d0000d13007441c03030f124044c1e5011801030000b00000c5152984960b100c60a2403030144080d80c8500103e001d100c13241160740503051b07010210782a21740f0030b54442c80643d05600d039100040c0080c0414189d40c8002110303049040040040303c1c00484200e4280603200420502080329201c010032441c0e0041410030380700348e400d12400f580080480356001c80901c0400703017030b0702800c4005c2c05c490381e1100d039018a625504c00d07101c04c2d61103072104982c9003450350034140c050303c61960905124200030030150800b51400e5080c076800100a42d0340f01050009071080134590320803508040c0d1b10100001000600c1c03075054006000e014419100382c00c0c01d03440390400b510600e49503c034908003a080400440c142640f6002440c2015010f2200810704558a8070360308046424090078800b5508003100303a089604040052460000d11210f490454811001c0b0050746a601400f88504029442000c602400002c205072011b07850400000c6680c0d08103c400c0c160300d0001907429181c1000a4088801c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 622836870 1250 622835620 622835623
    0x80a0203010b03192d030c03021605090a0203060301061802220608011a19030501060807140a1b02090106080f18060c0f0c0f0618010b18090a12120e 65
    0x214101404c498a8007095483c0d68100c589005810300701080201d43c45c14003042d042444982200354080d4854074502099410001c0c10403041c5142c0380c07600c482e800000c1055480380b13094281c1c0102c403080c0040c0c0380e0b21907a00080c0034040a6114000c0200b030051080300c8901d056008258540c2207203841c550a0141e6140720615000c00d2003000089001c410040042c102e03031000e0205880c0410406500e013401c0c01000800071781540400c81d00103961b0b40014041d072500480d081c1e400000743d0410740428030340002a83d0442c8148140741c020090f00701812001007150f481c2481405c0d5000b0154002c640e180c85005000000c00c95451840c114040302007403044480c20b00f17811805400c00080d12036a91050049103131a8007400101141d08402c20120f04c001c1000d02c41d07100c60584e050f001e44618100004103400103003c4142400c0b26034905004e8900c20340c3c0301d00c50380307111003201d1b0011112969085802420b0691003d0042c0c0402d40b003089680c042a44030600020180080c402040a10b0300500303a603 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 622838120 1250 622836870 622836883
    0x18073606090c0c1101270f0303090509040c0902090609120102070b011508070c0305160302070f080d0c060b04020c0f0105010503010c0306030b0f04080c0f0604061b08070c0606050406080a0203010b03 87
    0xb41c0200c0d4500000c4802d548110188150580c00d41e05090644c06140625402c83c005c60744080181f0207043e509004255100b400400142401c80d044d1099041c282c5500305580814810301400319800908021036482c0d4800b5581d07241c0000307000400c28026100068040d5011200443e2140d100000120741051501c04107003c03107405aa84039002c0d03541183c1070b2550070149209034144a4240201c01e5119102d00c0000d02540c802d50140c001e070741c6040b00611151019402651464000307541e01c83d140c95005c07a01034012030704020085659069003002c0b50091040a071480c16a004036909081d2120054100314101d80042d4020400074895200c00c908030b4280b40002000304a0720008100c503444804442900a401000300926150820304480e1821250f0007100d42e25420400410007800f400e441000c4841104455580f54282c0e142e400601c602e400610b41810b0040d02c00b000300510645920040181c10068002c22807a034413401429031750030f41c06004920075800c0c418910014180860720 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 622839370 1250 622838120 622838123
    0x60504090804033807020304210215041215090f0b070e0a0b0304020105070203160f080f0714010f020109050105072a0b010501110f1e0618073606090c0c 67
    0xc11359000001c440040221010701424110b200c1130002242c03888088440306030080c64230720540d102c80e11070320500821a403000820180004103000821808010b5030b51a180700f68814803200d9440341e00b2010000400c074440c0b0150401900d0100c441c00c005030302040c140182059200c0c0144080c41c8800c1081c040e10502804942c56010300200b4015400380c405815510701c020250742800e03101d6044984402d00c60350100e8034500504800700900e00f0184184100000743d1000307800c0250a0107a444509011441c51504000703103d122240e000b07100303520000c540c550040003804641800003004251710340084140b1080d04510442e110602181420001c4603039020040000582c030304001503030110002c001e460414003602ca103076507050704244031a441c00492015821508207405c41401c4c90804014482408095401480e0003030344000035240c8102c0e0500700c060880c5500d02200300c0d0f6030032154480030040359210030032092400700c10b0300300c01c081e5030a8100c10042c10120150803070303403207624500 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 622840620 1250 622839370 622839443
    0x3141510050108040213050c0d11070b01060e0d060203010902042313110f03010801020c0c010c0b040803040305040e16020d020a0803042603090d18060e100306050409080403 76
    0x204100030b50094180300e82c081d000a00401c2901c810720022406d64108407034055118100080704d00c2008c500d0304c95801011202400309062011566418541600c10b00540c0144952081020075a6944440000005d5131019081d900c07075a4428004000e904280129a65101000c004250b040340c02030034400024001031801800940800041d0300070004406129001d5808010340e01200f800f0500560003003d156000607a81e040d0b0840c000c2c10302c0315541040781000080207010300807540c0c00c0c50780ba40040d00714007210341c0d07a100c0c0d140a446c0ca2050380e10113290a070000b400c008601c00500f00048031100103030251111022041d400301e0300e5041c41300d0000c14160060000c68045444502015492481c007503102d020b69040d01d2981c88950011154024150300c07000e44408132030f601c6143c1e112202c403154071080c60281401d001420200600103160301500000031105900303446600000300515010340304000141071030901c95802c0d44113020940703c00340800380128101c41c800082d201038414629 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 622841726 1106 622840620 622840651
    0xc0e060c07140f0d032d080907080d090902030c0c030c07031e02010906030f150f0806090c280302040614120607080a0c0903050601031415 61
    0x2c038058028100c0011000ca81d455052107010425858140100240460040700d071702030700707807000784c1c03048400c60b420685c0b585800c008007502602800c000e5560003520341d2a03091340c61040390b03643c1d00050b100e4201046500780c0780d800341d60003400f4440164a0400202003051035034001c541c1c801d000307030012001041081b000851043c5000d10700540c021081040707400181090409116110038551a070803102d0110740540d1120070700c0d00c00808208401d03501c0c3c00100704111000c0c080c81585102d40c401044070303800d000500001c098801401c0c50810640302c22441224441c2c01e440c007114840701800400103070b54074003503080540700305c01c0440c213080224420040407000d554080d41068000ca000e01c07a80b07640c00506258016280c1070f002c102040c40030700482c1d11000030b80c8040c00320302070100080200603200d0f5072000420400c104440d1000400001c0c0c0040905c290f40003ea2202c0c03c6 = true := by decide +kernel

theorem cover : BRFrame.Cov 622661870 622841726 := by
  have h0 := BRFrame.cov_init 622661870
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622661870 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 622661870 ≤ n) (h2 : n < 622841726) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
