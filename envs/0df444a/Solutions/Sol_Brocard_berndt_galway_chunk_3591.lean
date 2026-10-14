-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3591
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:06:12.266883+00:00
-- url     : https://prove2.me/submissions/fe52e3f9-931d-447f-87b8-c699e0de575d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 645683453 ≤ n < 645863309 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 645684703 1250 645683453 645683491
    0x60a0e070c05150108070e090708060f010305011a090703021c0c030c090909020102060103080d0b03010509030910091202040b0604080f0307060605030a050d0f03020d060308070b1e04020d030507060203 88
    0x60704042044104443c0b0040b181c0042c09884000507018040f242400324200c0665a90030700704d81840c0185d089184180a0203041c402c480c0400c030744550580380034200810407a030008881514022034654900c0d0005017040000740c0042c043d03405060b0801c00c003001c601c01c19100075214001c0340c4d00c0e640c0600201395903400c05000399500502d0b00c00500140d0a0401040e10203800103560b6060500c00140101d200280203402000d06400111030000f02900a029a0400d060b01030744a0b046035031064041d003410b04003070080350f200f500100211401c4540b200c0107202c2507001d000c0a414000e10540d00203100b0480003881910802401d0005002000a1a151500d45c40d10344151003407a482244a40d0145440c00c1c0420004141100f0164171414136440340011140300740c3c046d0085d410300c10360b654940fa000100781729980c00100003d602c61290103280380d03280341d240528504c0b5440d9030520307450810001401402c0030355140d4005070003810031506069a95440c0016a03004407850344d0b101c4000746040d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 645685953 1250 645684703 645684713
    0xf020d05040b090601030807061a030d080a05150d020d0f0f0c140f0f01030902120d0207140402070c1a071e020f100507110a1d070e180f060a0e070c 65
    0x165000381c83e00c07001e040e540d45180c0728200c041c003070404082d100f543d1311240b83c2010200c3d2664500e590b400070b8180e5401c0c03e000d640203400c1e48000c5541030941c40c2000e00190b02c0c1a010150103403a028000d05203007034220b0503001c0c010841c955102c1200c1c030354658a610800305030180000c622951041c8507441e8441d040c03c045003c0300311280c271500e000d4981070034400001c0c0d641c100840b070b5011083c6400146041c00740002550014003000e80041030280d01e8001c564264081004015100300d890f500c2c5414545105000c201e03c00c020018014100c045000e01c034070541041c128200b440c4500c0458209102600c40c2581010b081140c1220300d030070b043c101400c50500e50b40c40081c0b420b0803145605102041e000160803442000c000602c100e6412031450981c1d9074101964001d45040320700c40140300542c002c0da01e107218060301c0c80c001180c1c1d40f29902c41d003072034202001603214031004502c400e151102c1d4950168040d002c0c1407c0e030b10622040000c202d031032018800500c0b40c0070554902e1440c003428117103 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 645687203 1250 645685953 645685973
    0x20d03020a050703110109061a011e020c01050711100c0501050604060f1701021b0d093f060e07050a0614030c0901021608010b121b010e01030f020d0504 67
    0x410a050050001c0c0c014903802c02e06980345580c240c180542c0600006400034010050014010f0000e49046498500a1803101c2100c1e4084402c2c0ca5000c130488540840c85849090320030a00010b80c012426803000394458070181c40c082c2e02c5804800c1807003140314002031072641c21024400c0018400c990210a009090007181e41260041c2c404000b902e0900400c4c410031620b0703020f081440a035040e24800d00702c609504582c0201990f01c1d044543c0d10b00d00c00219141c0c844001c0c2c8800054100f1800310340442251801480036100d442c41055550030003449c40c05101c41d1725035003411019101d944902086141c02940e6807030220328003400d440b90030401080a00300142d0424000c00210702c00c501e42440d104422250820300903d1038030707150240300c40101e00c0c0607030b0f00590603848014102c1c00540240150040424100d0031140c1c41030503950f40721f5165a8202150300c41c001102d17111000328042d40510102d80c8180418540400c215201e280300c0c0013680d001d18140c2046a59400070001440481c0c01c1d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 645688453 1250 645687203 645687223
    0x11161401091d04141203010f080723010f0c082803020406020a062004030503090a090c08070f1b0305030610050a051e0d0c081801050106090b031306051602 68
    0x24040b8181c04208035580300c40000348000c2000709030035550202d0b03110801254070411603418145a40e581c46004e012041e18103880b61074614412410081081c03901e520000c00900031600d80a00d03401c1d00d11004407180d03074080e4004814043d02c0070700c1c4808200d0103001410303050441d51701100000360f102100420020b50a00c0d04041500c140010f010641d80800e069210640084002c00c9801344030404e0303001e91840202820108400003000000c004010000d405201421524103001569454041042e201222107450015484c2000101141c2c020481e65041042e503141c0b22154045800c12400e85860540c03003540801c0000c001c01c92070b0b00d8220300881c4130900c94500340d42000d9048a004d4164024600b036064102000e540c4014460061020303640c4200614406001c25207510710058000701c029518445240c0c1c007402c202c203150605002e80d604030f0300350703036030f684261890b0038007925903500f0141070a0941d41031403070740074041082030241602601c03420a2240200d1102c000183c40c0c14030041d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 645689703 1250 645688453 645688469
    0xc031b170a030302070812011211030106180f060801020309010e19020a06050319062c01031104090203010b060a08010f0801140a2a050306042007031116140109 70
    0x28628248500c0100c0d41140c010382c141405a140c00c1a40340425040c02140c03070801801c1c0740702000050361002d80c60480000d078012500026030340f186206160030384850b806180d407a0721010f10ba40e00075185603804200002199000044c106031520a21801e81c4d100340c5a45a59a4460708410058074003488804500e100c5030400b80c0b200d10391035022409043c0d00d4443c1c03c06000001c40080d00385501804034041c000e40f1048204006d50b240d05c011006d0040020030542a48011000720003002020034419058a801a104d0080c210f200d0040001600e900c04081b03070555290f400010f840e440c0c0d40050510301c881600c42c80041d40c18031980d80303160341603680140b60aa0612849240048401001c18cc10080c0c1c0d44010071061043c44040c1d20303020b0620071002e00c081400c071202806540c0b01c070280d4000d40c42103d091100c0d02001d804200840f0000b604006e91440400c041c40c0001c0c040d800c0c00c1c42d01155801590306102c441820365105d4411540072420303d0008410340201c0b580c2c00244030000d07012007 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 645690953 1250 645689703 645689729
    0x1140d0b0a02031819150207260409060902071208070c020d0f12180503030a08160903081b010c030203040f0b060a09020c30030417070c031b 62
    0x5500c0d2221140409072005140581c004041144922107100c040c0111135804101c5a000c120048a1034120401d0349058440201c9094211064865402140c501035040303045150049200208650000034040408400765810000000c00c0c1c41540a00c400518a00800603159503990510105c00f03030000c8079040030880c0841c10030003100c0d040304040011940659241e42800110702d0100c28044070148040c12103400d0300c40310b1030300640c8114a05030500307030702c0d0f40c10840c00d564105041d540d000b10215000890000740c00900207411500044032484498074102c041103650752110511a84000d84640e01030100740704030740c0e01103800d01400c42e4054492404518615160311045906030380381e1300080c000c02100d00072940f103658050b50f140140030440f1003196a42451171003c2c0e51001030070070350b410070000001804020940000d004228140c03c62085144d03540302d070f55804210701c0100d4940301001c4180010360200741011484006144a09070b080d030981214260512900a280d00981040d184 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 645692203 1250 645690953 645690979
    0x70303051b0d08010b1804020f030907080f0d050c03040b0f180a1a070f060f14060a150c030201181101120b03030f2d1b150613020c060406050114 64
    0x100c031001d0f50445046800c5030b91141172280011b45050300c041c108503130150000c204000301ca1020306c000e600988401d0300b242d11030781e43ca02a6070744518548401c0900f540142304d100c0c80950156009010842010003500d01d0709460f2900580030750055456901c00d0341c404128612600100c0e10002d880640455031201c6151800188940360000400020801c01002c1107c0301040070390741c2901003442c0e110340c081c82500150300420780144021186041141840f001040e03041c1800400f181c1a00d10b00f80d80f6440554021130152920040d840e0100c08640d0385140b411200c80d0507000c410370b090301c100c200d0001d0210040004003c000a40e050b011090718081d491402981e0000490304103c001151043c2c035602144022486100700b11f000d00030012441000c1c1900110100051a0340081c403940c80c0b1061903144a4030f542c070003142e0f5400e0110f5004001094091810f8410080001040c007009403404514a20441c2020000c1da012510340b601d80c0d006029005210900a000c1001603560801c1902 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 645693453 1250 645692203 645692207
    0x11d06061f0215160201060911040504050711010525020c030a110f040f0c110706080705030604020d14011404110313050c100c05010b100f0f0908070303051b0d 70
    0x5a103a0107070341c1005003000d501060007884040d641c400907415029051522007800c508441950f80c102c801540ba0290208140c0040d200d15503030b800c0b2000c0c500341000e0030304040c032008010107010078040c001880450100e46400b4058644240c030204a0115841c0050030441c118581c8200c4002c10354004c0e0f030100c540383e200060ba404450f07400511403541e041c0d0702808a46424101003100750000e0030300d1003c05900e6507542041c01c240c0c00750b580ea041c51117001d03140c9070b07111040c41c081d031000907402c1c0000c20b90062107080a07541000004100524040319800c0d03490458032010141d02e40850100010081c400641924a49440040e00d06004c1030700140c141c0495407200401e04002401401c0803981402800c0081000c101c00252041040046205026210241c102021203856007050b8604841c1e0420300040c4e40044c5413516242c8103802030404c16501c1d001503200080410416250001e445601040749000560103030f19015520b07491100b050001d0104044600d4882e03025070b11040d0019 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 645694703 1250 645693453 645693469
    0x60c0c061f050411180108190e1504030e091803090111010605120a110d080403020418062c010605060415030b040c09080115032004090b0702011d0606 66
    0x152000500501446000c1c001600810154101c9604107207400f910101a0010800420800e481034414030310710300e8007000468503824126814040c80c40c1c0504070082a80c5103410580e2128040d0094808801d2a480c00c0985240100c409070300040c0840c51080450901c0d0b416150441c8100c0c0c03800700c03070204c0700c054180e0f20302c50fa00c010b504100400c03181014641d029484080a01801050798012180600744a1355808072001c06485c0c410152500312001c1c9050086c8941e45503020b50190301340751468007048005c290342d00d440b1004200401000f0001541442402c2400780b2003102003440c482c11030420840b0102d1403440d003000e0384c54210240129940d2000b900c0032120196000d00082c6c5803c00114040d0281c048201e80090814a440d680135400550345805c0c4ea844c00000c10031034070809400d03030342484244005001043e000740701d000308200106148851110107000407804140e079030781700c041101d8200e502400507503444154901d010302c1101a43c0300048040300400c1a41000c1000071840 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 645695953 1250 645694703 645694711
    0x72006190f11070528080706110c011b0f020d0302011e1406100c060509030a0e01020109030c020f0402040302060f071a0108030a2f15071b02060309010603020d1202060c0c06 76
    0x1000000c02490b140701c040c0320b03007032040f800d00308000b140151340d40e04150780d07158580550004036400d000411840b45002030003203800ac00582d0390802d400301d20a41000e440d9011030050b10300700940900c400160701c4001e80070701113510071760000458002003000051a04602d200e0b440b10a03003020180c07201459000f51968100004480900d80600409401d66000b401714200803c5a400c01702000502c41000c000340012250540b03d0035195541c0d40012422203103040e04c0140030480e1307403a00002504203100c52180405000d000140b40607280d07000a5000e40001807203a000c00c01c0001c4001c10444140d00c803e41300e005070000804154186124a030300ca00403104401e00704904c0c0e00b09074580c50301151081e581d01141e842c0c140d18244450580355190528107860350041e280d082c000c01c02c160300c1403950641c003500621400c50341408560820615078400f81c0b944030159241c0e04040096174a011203c101c841c45003020001c10154024040c0c28281c000305151901c05c0188061440c50b1000b0441a0344 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 645697203 1250 645695953 645695959
    0x3031d12030c07050f0a0c0605030712051017010f0b0603041703060406050a0b070201020d0503060d0f05100216050c0a1202211609061208072006190f110705 69
    0x2250b8820420340a01e020b0314001078868450b609504040e00404158442e80c18024410f10502c1900c4160503503a0307120035a00c010008203203000c07844121856030b21940c2c20400120782030008036910f14410041011512000040313955032407126140412901c01c1d4501d10905540042c11840c05071160700d1820401519041c500c44e00000054040d56194420409000e0040080b0030f800d031549440d1600d0f4000d02400c90162164140c8642070901540c2900e00c0350320020200d21000030a56140008a010081e084450b48500b0004c10b803c00c8450014050500820511000d0300c00c0701d00f41149040c000c5c04880340141d600080c00e22600a2440d0341114103074050316680b12410600c14862010703404090010514001d81802114007a44c418801084840700e030300901c03159898001020800f84003190040074031300100003071301c00500c076030406400c00152400742920b0303515004041165a44512802e02000c041c000c00000020b8000c0720038405036585c2d1070210130030160100459a18100ca000301e901c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 645698453 1250 645697203 645697207
    0x503240f130807031706010c0c050d060609060909020a060c1109190504030e210303060d0c0b070c0303030c1d12120d02041511070303360303031d12 65
    0x200c98081011920714042d803182049a036000c1d40d0800038204440c2c401caa003105c440303060100d001036228494403000c00e80c0242a11200915080c10040b002d0240030b011501705484460014580b02644102001080d0020001c9a003890320f2040022440c1942c01200601412184402c0840c40721420041700100030b540e0820180c07507142d5000c0403100e10030143c43d40b29040c00100300030550700804164031102d00751068260403189110440504001c4c03007015500d80d000780000340e228039010012484041c06403c0c010000d5850340e4a08010358003803102070701c1030329118504104141d450700c41c80030031604910f410210340c0d207c54181c0132803400821145115901c0442550004001444880100300849858950354030340c03104544044c1d003007440f822130341c4525446030900f1640038107010b03a515036024000d05109802c50303038107580c00656080c0d10130354a17183d407091039044044030343c000c2c00820082115258a529600e401000da4009400007080020746644484103140006551810102c41400e916 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 645699703 1250 645698453 645698461
    0x1e0603050c09040e01200703120203070c0506040b0714120619090c0c2907121508010524060a1d09040c2c0a180c080102040503240f 58
    0x15095004520b00390f0303442803030034005620090055101441040380d04a0304904050a00e229450038000c02d60058041000d2007440303090055141d00660344105c660900e11402111a11303154584a8100c4048400c81040c40500242a4004800380595605490103030b241503000144007006040c00780140707004000c5090040c490101402c20100030b4003071107804110241c01c0110003030122400c807030162245c035040c05180c2c0445c40c1000c00c90a040030b255201300c00e85c0e00ea06104440070f841854180d03102540e070708030082c0c0040140140e580148221340000c9243d0500f0312202c800c0d41d040c0c404943c0341443e8860f045003241c03680c6040c4c4a101e0110f003400b00c2d050345008031840444254000a681c8020784108010400603003040340029903c0400c4880220840144100c2980b0700e401d425603805074446002821b01d0b10140c00c9400050800c0001d0304030710302b45075030314520180c03241c00031000307650045418071550404101d694401c640383d424005000d0035007088801242405010301d024058140001 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 645700953 1250 645699703 645699721
    0x110306011d180115050a0e04050c19050a06030b180105132d09140d120f0b031b011403160f050c031c1404120302090f040f050601091e060305 62
    0x1c0e007010319104009014000319600c80704d0001c5814060507210f1040c055001c9403024800000d1441603038020022b0061600003c10043c1c42d50322250000c1480c854050301103a0b5440d10070b8000000c104584002c83e041043d00d081000c500480ca6010396070380e485c88010084d541e1254021003550301001000105403241400d680c3c10f0858000d0f4040825210289034000c0340c0741944070390360007401010600e442e80d40450803117817180440c0001d2070004900c0b1550094044c52070703004640e401c2a203200004d142109102003802c1c43c0000e0304060b84a0060180e1988558100110049000c4960b01d43c51543c40c10700b001c19520504101c0003402c0001c102c0d09011010f01807400c85489200c61021a601c231101d8046900701440c441c0103060440c0d0400d000c201802c82a034920307902660b400303030621415503045030044000350007941184e42e000c9081e68041101351940e10500b00940189030000c030b411319007140090200139003540514000c4051504155400300c80049440c166440c602e808145e07902d45040b1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 645702203 1250 645700953 645700981
    0xb070503060d0c030c170304080d0f030e0607110f0a08030a02070309031a010f0b07240f11030411030d050d0b0f041109190f0b0912030a0507110306011d 67
    0x41043c0b00442001c020b12402c10748550803554041d88070080c01c0e034881100350b03d0340628410300382190b00c142c1e0b440400c1c600840c24070a014806140015400c400d60340c80e03034a044d038141e0700d03500802e9a40c170440c0d035800800e1140110311004180101103900e016952100184001440740d8650b44d4003040700c1013050700c2500c0c0b42c0025500000c007005901100c01d410b804100080c4101d000f0310b00446000a4091029001d80e0380d8940c201074080f1401000040c0840d040600010708910290381c2d0014100d421941d00c52030302c007003200f01d685984a1400d403a180c040c1c00712038840d452091f8402010341401542c04001c6524400d02c846000c01c05404442c04141c90400c0700d5082da070b1050401d0241c0755090300400c090055900121043c0c18000c0742d602d02e808003079400c2e00404048484010302071000d840910002c0c070580c88050312611440049840c1c60782950003500c0214005070002030500184041c0a1000700c90b4031045000c0c180c994503280145201d861901c3d0090002101d040014141d5070540b80 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 645703453 1250 645702203 645702229
    0x1b0c0a180f020309060906010503070617040c0b040902120901050f01171908090118060807111911011d0303030412020a060507030c09060206090c010302070203070b12010504050a090b07050306 84
    0xc07065481c0d00f01900031644900d8100c07900703000352103120000a0580340004a0743c04075025a2100c00300c12000307009032104100c0091040d1fa507555603c2002641c0001e540040c401000e0a48006865000d840b4840920400c00b5059206581c100001e00404900e000720090440d107900c643c41c0d00e4419140665824182081041c01c5074000449085c014017200c07000030a42040260303500038200003c1f038421480c900e01130065000048040380042c00703040c012444d01407840703446801c65141000c0e41d84160a01c925840007100d104004032100d03189035030001c00e0340c2e00d00403147c500c0c0408084079034042641c03400002c0028106010200381c20f19103e000380300040307040750061001d210070f14180902034080d01c420300d0040001820408000781e800d00c04680c1d6806507289802501c1c2883c8135400440c065040b0302c0702642c1c14010300c000000c20135190310003412201d242204036a501e42c548000c02044642c010701c01050070b0b090981d0800000d451041c42035020301213007405e6459840c0d9002050341084118 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 645704703 1250 645703453 645703481
    0x6010503120a092117070f03080709030807050a05121804020702130509072303061308090d0b0604050c07020906041d011a09070e0319020103140106051b0c0a18 70
    0x2004e0140c0d80e000d203034144111140179014060101e198a000c0080c04c1c42000c4015000d100c1c100c1c0c2c0d083c000303481024800d070004032514004071241d40b2034a400c0800e0348403d400310340350f50013002c203d010004140074007050884500f6000d41000d680d00d0540c82c58807201d800b8a44500d41c00204041159642c0c0b00d0080c00c1307032030200100305914000381c0060341d5941a020310300d6100400028998291141e800004003528094064261034842000ca040180c90084084071504414400f448c83c81d00c880c0c0350103500502412030228681800000d0004440b005081200e00420030000701c40903884001405400000c1aa00065081071100e80c0b5007484003010318134081942081e05c4006110f140300c0707031400521801c4407030310840d0301c484805852840d0005210f07034140e00301070b40c13012800c0300c2040494241070041c18041001ca201000c00c1104441c240c1042001c03070310108031038241c900d045180c0e55220007840010071030001030700000f81d040c03804d61141303000e20f86045a0316071041e106900302c1c10990f0119 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 645705953 1250 645704703 645704729
    0xf080a06020f1c0f05060603071d0406030506041a011203050f03060d120f02150f060d03030b030a0c060e010c030e21010929010e04080304020423071106010503120a09 73
    0x201020a0240104030b11355030b000c43c100070114549140c4101201d004030b505071aa1504000564060501c0541003204103a00c40c1d07860a0010105109010b01880303175105074000e00c65940400780382080444180c200d42d800119480f4038400103908082180c900008501c201b03512079039800002180d54041c0e60b001041444243c601d89903141d001080440d0007134154003980d40c0e0990801d0b4500c01442d0884840c2d100d0213185000c54518105446c2c1075500d540a0b29001c03032600018030100c0e1510b1a40c040843e101d2a070f4030703810425641c0c420742b6040d0141003480c2400d25146140c800504042c0070503513180c41407281e40c4030502c10202c4440a4006005680000c0c850344042e0309007105540100010201c0303c0d105540c1d61003460b40780c07440d13540c142c030315202c101a69510b17603854001558200900c2260807076135588460100400c60310204c1180300c8003200040084c0b0b0255070082542250042e6260726038040c600620407580c0201da0100501c140d01d11a940318803081200b141c4d4000640d000c40380000034 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 645707203 1250 645705953 645705997
    0x20f073002030f030a18120212070507050907051b0709140403091e030203070f0503010509070b120601050d0f0603050f0f0a0b27030406020712230f0708030c070f080a06020f 76
    0x801071f207040c4031202070b40036070349c501a1050880310288544140108203030080401400b0320301d0003e05068210550b0315229007080024410702d9020200e9410092445d8080c440801518503103000740c0c00301d402e0645081c40f103428180c0cbd000e09604558082c003401c0115040c60170804102c00c246010046400404507008a541e8040340801c00fa05406028000e50070b0400242c0301d404000380c0c14080716030141d09946042e001101c00c6000700c030082d00023410000104940c0b5a03942c154001d445480d20a04400501ca0b03107103103030981c84c048003086140c2c025003188412000040c004510046026081a9031208907a2065640700c00501608031040d0154402d504966410100101400603613604e41c0865a450b40c60302d0800c60064480807008001d021086200d0400d107600700c1000d9601000881120201e44103a0303200b40c180300c05c9400c110003070750001c034251800c540100000c500514180c904421003d09220b10340b5101d080744500500a150000365041c0f01e2043c41e001c60f060358040c20710b501c05d4404 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 645708453 1250 645707203 645707213
    0xc0c0f131a22050f0105030601031403090627090c040e0c0904050f0403090905010308090d0212030f090411040501080f0c0c06040308040201080a0b1f03020f073002030f030a18 77
    0x400440080c0b081460580081ca000d03024034003c07816500c00400918960386154bd801c030404d0062074400029010501944500f5180ea030040c1150007201130444002041e203044194144400031071541c41941a00d05004c40740e00120704a82c19205000c8041d605a654680c0500b414422195403e0b0068036180c00c20241504950303d0340e000f00d120369126007046548100e0341041e15001c2c007000c1d0070746c4010840801c00f881c0182140408074070203880d01003003221f1004007509503004903da4140b02000010840b560340703400e02c510b1501210468040e4209400d00c00001c1c950040200710789160148800802c0202c00c0800690b402b0041010440d40c1510700b80c50001c01c65141903400724042007080d4042136030404540180000300031b010700340403505034200703208030a000e828046510606600b00580b450103110500200001c602034508221100c1c0b86035004e40c0d22807942d0400c00b840c2d1070380941c80040c659012044a90b0f1108088086840351100582d6000419413015100303800a6841c0401041107 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 645709703 1250 645708453 645708499
    0xa05160b0a091e030e0f0d0210020c04060f0b03040303050711030705010c1b050604240e061f1404020f09030307030e0f03010b0109181b050c0c0f131a 66
    0xc1d116091843ca41905038004804500c4001802400308100030000c004a0601c00b40107405d03804002c11601105a198000c1500c40b2400c682003030050300a1500400c1c1030030b20b0701506006050000400036021315000b0040841e010207000241015140c0b0080f0f805d1500c11100c83d400d862030001580e643ea0024a00b060091041c10724800100d1080421551405215407840d0740558100c030140c1090754413540d031681c0804500308440c426851200d0090311441540c802d10858100d0840103012900b0241c1405404801003c4110107200040d581844451601400140d0081c81501d0150309d50f03900062114041c050048172070307003621001c2205e60a240c1d0045212409a005440d141070f104130742d42c203050903200c5482e00da9010400e582020840c44000d03048500c2c0400440030009000d40311500c02c1020300780e407546902c0c0068008983d0751400103051212920383c0e0310440c1c0c8491a0346144011a1005003003015640c503140d9100c410546042044521040300324000340f48400401d019041c0c42071007 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 645710953 1250 645709703 645709721
    0xb0703021b030a120309110d110d06021b07140d2409060c0c0606350c1903030206010b1204030e0f0405070c150e0a023703060b010f050a05160b0a 64
    0x103040050102c541818023201550060390000c007207203500722481c001d00c078409049034001c03144664200154520a40c5102134000b1100e01c0c40042c00e040c5182a000c03240b00c81e054241c2c0780c07065905001d0100020750b511108140913400004072400d0140924100300207017401709028050508240004900075400580b002085110b05030410689482c1c0b180602d1170780d040030380095008041c2c403150544041e42440d0744441d203500b404403803800912801180c0038690402c40d00315030000844d01801019010321440707002d00003488541e8104503501071003800307060300500080d09010301c8007098201a10f034000d0a140310700b0060402d11840c200080020280195280c054416051066613012103c0140c09460402e01d98a0014801b880c000c3c2c0030000010303030302e1403654604803022910700021000c14000f0b501413803103164042800b91842c1030a00c02e1303071f001e0703030a0a0401c0003a00d10300d038160780c000341981c10100d16840c00703980302c03035200051400c468000d2402030b141a408008000c00c9003103c2d0082040 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 645712203 1250 645710953 645710963
    0xc08090916110c060d150914071b0b0601050d0e15150d0506420406081507050307020705120705030f070f1406090909070f0b0703021b030a120309 64
    0x81540228060b5480f4441e070145a82c1c08507080002488192079078000c1c480c801c021211310014240e07150780641c1207940b61003071741568502840400400940103254400d194140d202050011901a82c4d00d88051000130641810300c480492045003641b1282c0c80020020b41d00c4088800d00c04000c060404030640448014151f014000c0b454034103400c188000c03644065001000700404c2d00ca91100c0d01c070007144522205201000d0300d004a0442045014424007415150840e41e00d0856000511080e140c4680085219a1000402102643c90804100d070322021600d0195102d8860400890030990aa80040c1e0301800010222001160109a01c0c04840d001c5044405941e40c0043e401e464820521404000f0005010300b04201104541c2c480c3c3c0c1018002c102038504881c2000050007110300340d80c00c3d44113a10032941445070301004030f40c84001d4204982c4040c10410590350003541e4040c80400080747d5024810510320607101040f404c05d0460340044d034450300c0c25042e10010010150b20f03105441c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 645713453 1250 645712203 645712217
    0x61811030d03060609050f04110304121d06070303090302030c010903021531110411030a15140f04060506160614011a0901090504020c031803031201060c08090916 71
    0x1c0d4002d00c6a9000c4800603165001150314000401400f150041d2590b42c0250311542c2640420302d01400542c45584105075000d0b60303040d00200100f45040d00f20700c0c01005445103102c2e54107681c2e400242c482880d41882c0200300c0c10501c4c03800328114080c4a54403002503007010041401c150f008101507080c40c1c02d9840a6005640b0066040d480802086218141c7c0c01c0d03d01d400180c0c10303000323050400ca0341d02035071082161090036400306007100c40301e8081012245003c01031200c03039200e82c028420244524440030f03100e03c0c00e0034403924040401c404418840d00ca20b107540c043d10740300c83d04008000d01000b0f0180307440740181102d000102c007030482c00b110a185443c4891001d0403001691034140c1c0c06013800b269100c008590a00d00e141e200444050500a060070002500c0d61980010243c1040310805548c60700001c400440310f1001ca0100d85129030010701107172035030400000c1410f04441c211324094414648a00700040180b00b45881990002111801c02c01c09443c100c4c3c0d800110120765a50030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 645714703 1250 645713453 645713473
    0x2100207030203010f0203060a0614040f0f08010c08041e0204060b2118060105270103030201060f08011a040c050403050d020d140c100515040603200114031306181103 73
    0x40c041f807004a6500d81c0c050050070080c4821407240702d1075245036494210262600e40c440b2029810081141d00072005900c4d098401d025a200c04e000303802042c041e500309001d403801c0a503a035881c10062001300300406003004041c501591344039040740c8000c001140c0b985680b0040325003542c19480c1d660070281403180660010503003090300c0c01e840d801e20000c42d401502450342882d0401c80030600901c40c0c1d0010320031016144180f805400f2015000314469000011241d01d004481c08000d2103580c420b0b807044c0d142c003610441072100b12864603042e0504590000302c01355005419183c074000d503000503045100740200e59010075000654880c111509842e484040d81b079001c1005d540c5c0c40f50140520054014051002c2011500d40041c2e4220b194018140003916070007000c942101d41580c02a248145103c403800b00001c100b000c03900304d1050a10340500c1b031042a207401d14242c84060290072446001d035040c1c20520185a120307525003220303000600d0034804582040c4011164005030716203c0d010b03598000d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 645715953 1250 645714703 645714731
    0xe010f06090f06091a04080f07230105091018030b06131b0e011119140106080a0311010f02030a09020a08010b21190c090b0301020a09120309030210020703020301 71
    0x9030307045592a03a104d200b0103091282c83c0c50070000d400c0445681c40014040070404400038403d1800c164007031001484c08510b03014026940790a00c07401040a250003505825469074400210f036600181942c0b203030b41c04030014804540320020b000714a0842520443c0100130403141c1015103000da10100c529002244812003000112524154007490050100d06490041800781980850044050501c40c10000b00e05a5081c10300b02420030425408a511402104001500c810000000c00e10b00003000414109005282c0e18043d5150180a115450403618100102504a1645514081001d5417a07003080801c00e0043c00510360100c0c4104442d16010441c21014440c80030340e00070040c81c03040e1400f10b400070742980d01c845115101440c01107001400000302007004200002c2d12070058254241d1821b5049000c076805814194070903401042024542d070344c40760a130740550b0145010340740c0d000d01038981a01d1202c1551700094000b592607030301e14401c41e004202d07001100d0080e0020b0124030040f803e1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 645717203 1250 645715953 645715979
    0x1407150519110f09011b0606170106080a0c0e101517090a170702031c050909130b0a1119020d0207090204082d01060909031e080a050601090e010f0609 66
    0x150040051007840701444c558804c1502070150185050b4034920718a09440c0c181c240e81c0c150b001900d019140e107601c50b4403440244540d034001c11120025041c2c1c8001642e4109048185100e4090040c0c450b0002c10841d840040b02e03040104404215a411701180b200050500c001c49c10301e49110300c16010000d01d04e8440411804031040c0e000380c90884a80750a0715a0125400051b410790701440b410304840f1114580d000449070444c61760700c0369034661301044200018440300410522031100c2d04516400000c05551049821803507415021030440c40f05000080d03c1d001e648100c0541111031180c40b0b4685801103040d148000723481e400d444815498000c408140d1046200d586100d0b03010b81070307401c995001013108400c400018101d00206100110384182950141c1e040307040400d41c3c0c1e041c450101900090303101c41180c01410110300722441c0120103849440001c110030700c215219000120030382e102c0c10302c0001603c0a01121465035840d00c1011310809600e016082c0410000c4a020500c03441c4591 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 645718453 1250 645717203 645717217
    0x60c05160f090e012f090d11030606011b080a0309150501030b070f0207030b1e0f01091409060412020c040606020312090a0b0403030f02091c0302010c03020406140715051911 76
    0x40c4505c100c0f0744034000f001c4034944141c1d207800c2c001c0052001803030550b01d20f0001a0041c0c05481000b1940240c0002c00d41081ca004e000503040c0504030b03c000342d00d0b01174203e0308600541c00a18007515600d04600903406040e42c81401400040c10700043c854000c043da00c05816079005c4c00c9002030ba2340d1060800d4034100200032000f009a40f00440800c002840a040d180d8032180d10310810f55081b0480015429000081d54400000d5000c20f00511178a4803130f03c907034012207001080205450030110340b0b0580f00e5001401c0a00301500f8003280328a0b86000704141c2c4032080010740204082a40d90a0094480c0c01905448003240342440200d0604c081c00904032044941201c51500b0a44490381d00b5401040300d034548905c590f070240a03902140c1d0b80c11075070041c041904100740444494900d03000382140c5007403044030107051040c403081c040140d0223287d489842a419400c503070740d0112404d00c0c0900e40d4141c9030135100c081c140700401200507002441c02c101802c00d2242840104510050f11305075005081c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 645719703 1250 645718453 645718481
    0x4020a3501060501050d0f0212090a1509030909020714030a0e030705062b0f020403060b130e03090f040e01020d0c0f0801030b06010f030b13051519060c05160f090e01 73
    0x849041c1c9241100e50056108020f0187c0040c5016920458034501c0113084809541d180c2003030303000d501840000256050440300114042100b902599800340070120707140200d00b03032130780e0100d000e00c20000d19104001100c140c50003183e88403102010014100d14008040a0007405003403400900e604000003950014a00c5002114805e2503d203404001140440c141c101c1c1e9585400b4094486901440184051070290001056400d00345081c4070402da8120412203400303103011684011041e010082c2d4000e410115460303503021001500003000b4101400403a821035100145004800140d51f00c40c0d00c0c10ac011fa1070780d0034040480102920f0600c0d091001400750711040c1d002500d607600c1854011403140e034034100010055180e802050707a0304901d41d105640640c0d07400c103001e01903071141001c803420141103ca5070521648028000c3c800341c2c045c4904002d0090482c003c0040000600c20380d080e5007070650600041c0c070b175900b01003005900e151107400c0745036160000302549200e041c028400709030508 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 645720953 1250 645719703 645719707
    0x504050303040807050a0c03060f05070e0a0302130f15030201020607110304140a08010c03060e011401120b060f070302060105090c03070e010c03050408030f0306030709090b04030804020a350106050105 88
    0x58076884810741c1310b032404031442c0c051341401400141314900c000f406903000c1c03e00040d1400c0004084c0342112009400002808640c00c1544d1030303640c801d207048041e01c1d8107441070703140003111b40c4901c00034040e1840000700550815100c800c071110000b101030200d9001360308880440c0c59240095518822011a0400a420401090003e01d806405403100c2400181400922664a100d01421a603000702c01d400041d48400d8100040413141480034007501207224000b0f1031120705000680044d84511300c24500b99110390303140b010342d950394003035078042c0f0004140642e940d011854025110362003401118490722600e030209201142c40800c0d00d1041061341c4820340610018001507400407948501101084004c01c000b01c1c0940050000d0503071403500c89281a00c03130a050003014200780d410f4005c2c0c3c0d0f4480c0f5040001c0042005107106580007501800c00740c1d820f403628000b00300bc180035a00000d003c465a01144810501081c58041104c205d0b210404c010174406401542610800e02c900d900103101 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 645722203 1250 645720953 645720961
    0x11090d11031203011a030903041203030207050c0609060d0b040902120a06200403301701080604030225050904030509011d0102100b030c0d0b2d070e01030e0115180504050303 76
    0x99103000311f40044050013200d09042d510190380c100b0395103009044001071f40200b40d90003001001c00c0415042e40c02210550305161020010a006001c0c0780b4080b0007841d113600400792a5100c50b4007556002e90050708007030980f0500c040f40fa6650400c07410440d186854044031444100c0c50b004095880c00015442e1440c0c01e28640320140e0b949aa03d41a140100412540603051103584810317035801141502c4500b03c91040b2000c01040b4001680185100e80200701004006940401e4424108550190b13004000549018290842410750041500010318400344028150071401602c44882e099889418105a04051519103800613840314050780c0941c0b6401c0701203650380c1200c0580380002d07088442c00c0030340c58006400005001ea090ba0485511028092034980c80c0e9080300700c0804d00b00340da204885900100c004946001030081041041c07495040030280c0c4a9040a00b03245c04100c02481010600c1c80c010204804c180f150458038000340049040c91521401014451904038002d1415a0f40d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 645723453 1250 645722203 645722249
    0x30c060509040b181005040203041a19020f090a08010209130c230910091203080403090b0c1c021207020d0c030b01090903020d1d0411090d1103120301 66
    0x100c480c240e40d01070b443d50312000440e16103400540c00c3c040f20481e01045402c0034240c541c91030070b85810036800b0320700400c104130100e1500f0007220034041c51900c402c60b123907960720361480c000030194802440c03443c00050610110002100074080c0f50384121080c107001039072401d02a0803486800e800c0c5403c45c0c110111804c514401d40d001c41c00d08102070a151741d11700d40310846121088500c104204500c10003042c0c00e0400d0400a0070740200c903210b403c082500906101d0b050411881c4c070100103040141c3d0034001000c02d4440e500d0701000f0895106256112220106565120b0110200400c8c0d03244906c014040c00c81d100044400d200352810365418505a059028040048840b00701070b1403145482400000048980c01014000c0000300e0380028a107d482c0340080c18201200324040400050100d01c2003602540c0c608040510402c560004040c0758145900415004400146d40d01c803800b45036460510a03451141044c5040032000e0381c041d903603445c6d5508171500080c016606450200d01c1103420f008 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 645724703 1250 645723453 645723457
    0x7120c02010b0a0f080d03020309030d0b0120150609150402090402130f060305130c050118080106080d080901140112170706020d2306010c060b10051b07030c0605 71
    0x14015200118035049580045841403185a2101c0700e260410300081192010a225100c415400c2c1c0c5012351550900c4000c59540340904507440d29480d69079049000568003402000100440f01400022aa00042c1505448251010740302c3c001c1000c041c00136119260246220344102211800204606200c105000c005d4100b038607501e41180d401c100304070300c444020824100405c642c41460250074103160700101602c0d4060b00704414810704100d1907001485002046040e16000c2c030b0a81032115030b1080752a5645480ea000c685d00d54a4071101045801c8003141078240300722281c641c80d4803600c031189c1e49800c81d00040541440c0140030401400303c2c6119442141c001400b50b10036410f0b4295040c00c8144a074048001100c1e00e980c0060001c1c5c8100c6580a18135000241c800410760106242c00005400640102040d04008812640b502003001d1648190b14200380a011030001003031042000d40b032540b0184581200d80c18400c1544070880000400d80c041c0c80e4003051414050b40b030000c00384c03020f0b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 645725953 1250 645724703 645724721
    0xc0f090b1f0e060904142d0402060d02090d14010c090e0c030915071806080603060720100b01020c100203070204050a06080a0f0605071b020d0f051203090705090712 72
    0x2040d0f042244a4096880d030040307480b600010100501a41480741c0505106030b070051110316040c2111100f03494150301000c3d015441501516101c0e52041403100380c800034030030f41c0506035000c0b80040188041c030141c000e1009000001b8002005003003001c100941b002c4c002d510900241e0344100002616440c5040059a00181000c04840c0c180c2c1e104840f0340d08880741142c0c1100090a2480c240c1c03040e240014409004000707030304104c0352508100000c40c0c0c5810005204d50188101c5120822040e0a80001040243c541c40c064410040f50b40604001900000b281c0c01e0040c86418442412407400708a12034240c4501e4004514044469080c40061300e0010039000c034465461100044049050000e681c0b4103104100340ca42104141c0b40a504580d00079082074100a4003034a0140800c0308040280500e61f01103426401544d4a49020b00100c0c1d60610010528000d1203004040a5000800703940a04040400d03210866164428803000b190210741c1200042e40001c3c08a02d2044290300c42900 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 645727203 1250 645725953 645725959
    0x403021c050a08190f030c020316050f07031104050108060f340503070906050301051c0602130f080105091207081303021f03050105030316030f0203070c0f090b1f0e 72
    0x10b122080d441d648403c0c2c120032440f104100940f03165016003680602040d150045500f81040600510440250b407405520807500c10314a9488005052000800c6014500d8503044200c40c00c90f41c8914104000714003140041d4001c0381440000706582c42c02040302d61299500c000a2220b564404980810341840c64914480c0310711070b090b02c1080b0190241c805001c0484a0b02c60310354904000100820365442580442308024042c801409a40d440324002d500750700d1940c03014954051581494030082c030811030360600c10060034400042c02070010b1190403c0ba10610020042c0d0359640300250349890115a510802c42801c02402000615007005003c601e1045060740c00c1d556240d44c0425000e0440c0c00c0d80e021882803142c1c240c3c1e00107a26015160140005902942c14128094400c2c6508410350303000400b401248240c44101e10710800948080c2d64008010404499403402856400182400307050442800c18095a10340c0c00d00010248862810503007007084c520441e002111000e8000c0803080d8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 645728453 1250 645727203 645727213
    0x90b03211602360411150f120103150c020a030309110a0806090d2307081e041401020c09010510091d06010e100503011809020303130305070b0403021c05 67
    0x40942c407402c0d000031210b082c60300d0800f0380c0d451801c80c0d143d20610011180589070b106008010004810404400080c10161404503c03589841902550350182e0010341c0034a19020804041e848100700d0903c1c101ca01410248501d8070700300c0f00200584040c880c048016034895512100028800e80c801000d49000e95000c10344550300c01d0010796903076200da1020305560702c10820b000f80e00c8000d020364200032046003407030300000c400c0004541c5c2c019211502d4195440c4041410300521041c03400b00d55400a80e454a09402ca0100000700400c1d0024005d0010305403401c1c03d80155035000191480703410b107008040c1c1c202a0b2821041048100103511aa010000703020000640c060f04031411050350324201c0580d007524601071000501100c01c013800c50b1f10230615040b41c00d00d100c0c1c2080440f070550708a103145221940c041c90200d80030b050000e5000b5003600c8002044210540300d01100d5003524864801c0c2d44106a445160428900490002a52081e03d17180740710700380c0010000308102c003032080003650 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 645729703 1250 645728453 645728497
    0x1b03030e03030702101505030c04090c03020306090718181103120a030605040b0a05100c1a01030b04030f0e03031c060f180b01032a120f06090b0321 65
    0x3909607002a124100035901507000310900103520b0040074224500000190310142ca0600040d54505003010098052a6a0401c20050200c3e188001000d9500075080341c800d0b0405000f078642d40c200030301c141c04200c4c10806400724003003007a00a2860440c4485441c3e00c02c0712650301c031191034903100039885905114048800e00c44511880140c040100c0603100016070382d1414082c4402e03612020030140c410b03111940c050000b5943c11440d00001c25640c80c2040c80306096160800d611404125802c8100c140f0100000400070181c54030303446207100e55182c201c0800748880641d08642a81c504503403642040c4100a02d401d1a01908813403203207480000300349580d4031886e00480b051190007e07020071003a0100280310142a018160b0010002e10f030401c04950301100502c1c1916802d210900400d12005162542d18400c240c11a8402c00c0c0340c138200300d0400035900707a10050a80c1c1c4a00b106903410108554083c2c40c002c41e0012032070803542400312210401000e03402c0b0580c03184072014840e41600f6915 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 645730953 1250 645729703 645729731
    0xf010501080a0e0706030b04060f0e010303120b1809010c031a0d0302161e08120d0207150f020c010c05031b030705041a2113060c030902041a0f01020303071b0303 71
    0xc0c4d030003002c4c180c50024900c00404244019590a41c0240c902d03003c800f0401c003e032203180840359044035007502d0802001140c403c8810080c006812540d0b5001d42010080e080790700c02515080d000b03041c41c000030400049094410b0f41a20100714500d510f55101c80c40100741760030007226410750700340709205682c1100b2403030103130030740c10449030304a5441614000c01d0808c1054902e13440c100504200e4000300950400c606101c20a841510f40910207190082620010456154007800100803602c0050141c0c0f081c148014000b5041184580742c3d541c20941000c0e1750340c3c011411207001d000780c181e68988500d00f40c500c01c1140da201800700002c201c4108400514981c01c3c0e4801030340c428009810710381e070381c0446050000c00000c2e5a2001c5401032250184083c00100310815442036510800201c0d10140781030080d40200380180c00650014100070103182c03485c0700b04402c0d00c0d4102d4111817140000202c2001282d032408222040408210580e00c58508031041c8101d20350300900c2442c0100f100011103010f = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 645732203 1250 645730953 645730963
    0xa0524210c04031a190c03020d090614160e040203100503070e010315020a0f0e03071205030c060f13030305090a140102130902090604051306080703080703020d02060f010501080a0e 79
    0x40091074045030510410100c42c111000c1c10322070800724000c5050001c1c441164918910044090070f6540040c4001c040c0290142c81c825002e070503041014894900300380e0301400b01c000c202c1300d04003450000190041074008030394078551500c1c3c2d500c408060300042407000030341c40034240c0c8a410f103850100241c9940c0400c0711030003424103981102850352451420f05440a0101e184058050060010500140e80880d207400f1603040c601d04251111119004a4100101d54100b4408016171502c2582070280000051440340301c001c04507100b1b1760300c1d8496110012030039610f0302407480ba12a00100031900c26008560491803607010f481d1841d00c00d41c1d41c9201109103881045041c1d402141d2440078140007c0440020038100409601d405000c1002985911641c09001d01c40c103c240c0320703030482905543c0326001801d02003040b104107540b00c4c02d1042e031a40001904070014803510018404091003c038660340940000240500381d0f908000040d60580002030081d20070700d0351a41042c403001c6007004 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 645733453 1250 645732203 645732211
    0x9060f090830280509010212010b0702011b06020f0703091e08120a0507080414030d180e040f230f01110406210203040605060a052421 59
    0x2003041d079281c108155090611001c482c1007001ea010107000d0501048034050078680c80b4070070f0b10b00000781c00e00000702030701001c18010140145520304010848503400541c02000c1e0f0350300c10036241800d81c0e0b0701e00005005216280d0b000b4000307181007602030f002d000711103031100c0d07407503c119405800e00c2040503034070350035800c04001a40003070003807141041000d05444080103540034001032001c1440c1400103860784d41150b22010904002c000504404440c4110140c0340040d070710446040d0780742c4c1d89041003406540c00e0361800b13100c4d00a400040903110b02400c070703401d5009010104082d4140c9010f20380324109500900079160700c4501c160130070004040c5608104c1d000070380c4a0321503205c40d1640c6d00c90701d0705558034400742d05a85803054460042461030700340e0b01110118900401c2d800b950008550b011200f841421690174004000d02c8100f02060700180e205490a581d9520026070742d4040014a04c0300440001c81d1291066010b240c0c081c3d414000e0101c8070840c0c064018500100031703081100c0d0f004031 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 645734703 1250 645733453 645733463
    0xa05060a090e071d03010b0f010810080610080705010c051b01090914071e0e0d051614090a020403030c111f090503010c0804050712031727060c070609060f09 69
    0x10520f800d404d100c080c0c1c42009030020004142c0d03800104d40d01e4425115403a06002d032440010309082c1000841c03002405408041d2007035400c10344d140c00c4e0650028001c440c43c0c2d004510011496502c903a001000140d009001070980080511911421568540f410b504028001401240310040c40c021903900c2c05542c0c01292040c81c000c5c00041c040303054246190b60380d10300da00b0f5002c4441ea018450f0580d104d421123007260107289902d0810702d072007986020b002e007240100030b0021305808403028041540d081691441c4041d030712000f5043c102e100f54000180851401814031001c5007a055070200c4019014200d00291105c040d11107d0114403000c2010000b4001c0c0c80078080c0b0305084c000e41600c80e079241031003030b034070b060680c1e0b42c54031030142c0c0c05004043d440144880041c54854114040c011103c80b01c3d036103080c01e00061010b201c0710702071000c05128080380f03c490711001c00080c5035486125021130880c00c1807580d5440c1c0b40136140190342a00e0041d283e12101540800c0d0b80b151484861081d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 645735953 1250 645734703 645734717
    0x40623181002010204050a03240e03030a0b030706140c1f0e073003020c040f1a0916110a051b1f050a11010212010e1f050a05060a090e07 60
    0x8441000501c15004003154210790040c003080100da22880c00300700a582e840840c60f10715224030900da800000300710702c007161b1490404840c412032040200040d40103081c058014820314074503205042d43c8000742d01c40c1c0d0000a80170312511010901c0d45000d408035405040503522000c0a07883c5103c202803411404900e441d41d070310640c00015504101680c000c140d04a0b80c0071111180985890442c40b108070750510604d820140201010320030701c4020000032005000b04080c170144c04c1c001d0018000c1c1801c00313014554401c4a140d15140400d1040d2081444002d03000516124420444100703050342e242c08020b00c9041040700c002207040c055010980315034040e103100c80401504110442d9502d88455000ca000f165003010815482021144070207d40d00b4400140040d03c03111038028440e5291300c3ca01d40f03410600100b4940c2e4103101d002d000d0b0404492248003403031a0f6020741755a0744107200303082d0320100b061000c010b03608010006d8070001240e41030071110141e881d402a100b050300cc03110b503c002641 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 645737203 1250 645735953 645735997
    0x206010801150810090804170c10020a1110020f03040e090618060127020307121521021f02070302014109031b09010504050408040623 59
    0x92041c202d4140801c25210300b0035191840b0701d62a4902e07020303d00101e0351030380c6402c02804035010440d001450b45492012000a0b10501e0035110483e22054503c0b401d03000745860044c81c400036212500a0b041071140703030b8505020b010040d40040a44800c0e0030340c0a03159006d0503008090000d00020003076001d5510f1645070801c0001d0a002006200c188203e0541d03a54448000002803034034103640c0701001841305200003110704840458100b42440d5514000010007051641c06102001c0c10241705106020310500728a003480042282d01544402c03442100d030820b1443ca82403910310420b80050f284103d410800d440c2074035480211f413110005a40554410411940c1c84001410b0120308003903480d0b80c014060007080070b851860300d01e2590076200180341c80c1a41c0c501a0884030034080080844440b4000f10000c002c1c104d0b0508006480b41d56075078000595814079001e018812a405441503140c503081c00420f0b0b0f0911a01e8410752220305000c2c070500314144401005180c00c2c00032118034160204 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 645738453 1250 645737203 645737219
    0x111040e0f06150c0309040e0706140a0c12020a0c09050c16021207030c0305060f100902030a0f06091d06040302030f0a03060509010e0f240607020105191e030615050307020a050d020601 81
    0xb05845149031181d1084400b0816168001040141d034011104040cce41c07210424403c403007100781c25401410396601d0303070100160103030002071302e0050300d104e882e0b64240d16584081900c100e807002c40e203442d00c0b04010054101100030403000b80480303910060090040f400c504404a00c0c14410b43c008503040e205030300041c82400820131030760f50b00c54040b00302064149070058807207080c1e10301427080300b02c03858011000c1401c400c415000040d5440300b42d14100300c03181e134809100d805495a101641911107034181c448080c118042041c91040da013607001545003400c80c85007103040c0d50261142c82d04065451070080740540c0c07602c01e404c0c000d0000c24180c031114100b44052064140c400f800900003d0340591015034403107004000035098040440e220b946400007400103030b801d48240300b8a080d8004041e5007000c0c55540041d0280410300d8510981d1125514400040d0100d5402d40100034201080c41410b0948510400c011940442e081c819107140740034550364540b0706401414050003580140005000b054 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 645739703 1250 645738453 645738461
    0x7081603080c07020a06110316061a01030b061801050d060b0301060f05030f060f030f030c030409060e01382106220c050415110111040e0f06150c030904 67
    0x200c2581e404603d400c03002d600003210241c1901c02c0f0401d1001003403941e445c1c0041402901c03d0290f4007403e0008181c028a00840208040c0b010b01100c800692003102255104c1c1c45460b01011700500100d02d030108252004007440340020526040140c06c01c0b6401030b207411405050004d183c8101540d48950500a02a20240883e0f03840c4041280a104010701c55102442241d00041c003583c41d41010b00d4110080b90074042c10102d09e441e944800581d40c82200320000003070044420303103002040095140c03018141040c40a11881800185142d003003920043c244d00c112103501100c41c0002ea800c62280034030803264000035003121450096a074681c011301c0d420681030341d1000c0210b43c2c0d40d9131440f540010b4a10104a41d0400106913500c4000d24001c0c1d00550032100a07003401d62000c4c80c502d1818a0081030846100c4801c5c20315420209203020b004045e00640d4240c0d8a00b02a45001d55105e44041c0519003000385242c2d8031800f000144c0035203a01041c000e040c5110118051076a0b01c07944000c0c04103031 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 645740953 1250 645739703 645739711
    0x161a070e04020f0d0e100e2b02060c090333160504030f05031e070302011a011d0f100c0b2409310303050f06010f12020708160308 57
    0x640c0100f00325070340d0442c0f01c070484000d90241c110000b920a41d601c8003914040300c00c0100b0000525041014100f440d00291403690b40c0d1040b90900700c6c050582d00d00c0d000d02006200f0410140c8e00c000c0104800c1d4103042d01600301843c01408039410268040d0f451441003800240b000c0042d4000d640c030301200061016a1503000d844034191225000b08200000c0043c400c0384409401c9404241c4943c04100043c411611480c00f606824550250940060b4555500000080b005980703400084010b91102243c0201c4d220016103804109086800b04140328858a080035039001c10360000c03440f415610750301552805034403592109820901440c090401d81c3c4003a04401c980010700d90030200d008007121b40d000c13940e00c060f500d82c03145494002031040000340e1440c0000c44026101c0c200c0c201d8408040411198600943d1300f030005031210100d60030321007800d91f8094001110038440c1e0000f40d000d00d1034002a820046e00c0185400f210f92030349002600202c1107604002d9500400f103050607442420386ea00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 645742203 1250 645740953 645740959
    0x120703050601180b2b0c021c030605030703020616060c020106050102190b0703020906040e0106081501081501110304121101090b03010f12030c06090f2307030602161a070e 75
    0x10300c2d130414401e038140d805030f00001d0292541001e9005050b040c0000e01056009038840300780301414040c81c01035100e0000c000e2248009011182e000d5480b8402d01130380e021554003a019220081c115024072045034000c0d0540c6181c3c4081d0080c101c00150140f00d050186075240d40001405810003000a0a2145a0300c907000f000900c500348500ac5101040400d8100c0e2160a00696500204010421038080c03540500c0945000c000000381c0c454000c091648205000c0c180c1d60980540100107440300740c1c0c10f8907100100d04107403e1001195028850000380ca01d0f884003124146652101951604ca203000300031142d10001b100c01c0442940c10500400c0078040810381c107070556040c003522003081e12080c824000c181a410032200d045c1801031400c042c6580e001a001e10141d42c1906040803901d5850380203e0b0038001200700a4200c82019a1091502c0700041c0544805407854035010065000103411501043d40380d501c0174000303000710046400035442c440740e4007014940310303e014000d501c4540300a40 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 645743453 1250 645742203 645742247
    0x50103110418090f050a03080c030405030304020906060c0a0f02040e03040605070f110927070501020c040906141608090604020a0603090507091d071208030f0408120703050601 77
    0x20841090305a40c165645401201c06400c0d664118070081c01e0040b001625202441e490002885070104071910800d000e9220791042da00c411203031103203e10007100d001c2c0041d0030a0001c1001460305220f00f9400c002c00401e0141049481046541090070300c08040310100303905800b0b07030114142401070420501801001d14105840c0c058054801d2003091002000440760200403000c20045015a030744035400900080c0142c0303060301c20441071007681550031b480002c507000c0e2202e041000140880a890060b030140c40c00c0070030081480080d05082404480481c1c6980401c03a80012540c0028818a060040c5402000540710060841300026203c0c80e80ca401040811001da19001768181c1141c842d8500054404441d04020742820303400c1d0890000142000e01c21500c64040c2000c48141c00c00d04000d6520304d0741d40315803031059035403800d400400500051000880305024552450b030302c58000d0140c2c131329040d10260f000e01605003c890301c0b400b0965a4052080d156400800e811780b6400400b0030207 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 645744703 1250 645743453 645743471
    0x7090c030e0a03230708040e01050f04060605160503040e1608100e2d1f1d01142110110705101d1002090f06070b010b37020601050103 59
    0x104101c1300100700c0e074201d44a001507948038441c00022034118076001001a92210780314040710924100c00c1c402e80b4480e00d5203600280080c03409200e22422982c242d00c80500d0700ca580c01c02d10f201c1c039000c4032058a95001c14800000d03d017000c482010311880c7c00c07000c0c060011440e00d1024205440103441a214040d0248003405440844094076800440300078041640c121344068018990b11900340c6104103078007010030301600c00d140411180740f5411400701c001c860b6480c2c18403905e5060503141c0c010300428900c001009568210f18032482c0642016258038001f80720a207425010300c1d49050014131035440100c0c03010b40303005c1600c02c02000101e1640058a400180e440c1c07580d071200c030f108040d40c01039540c002c8a41403012800520b032442e4a0030098955904001c0c2c1e552000350041d0140c40c0c011003241080754620720306a0221362041c2d520846864081c0d082003510140b030b030041107081060707501c80200a031307a51444000c0e80d41015003110688446d1482041d00078280141039104131305250401c4a40 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 645745953 1250 645744703 645744707
    0x301030c1a0d020f040816151d0d020a03020a0b0c0105010b28020f070609030c050909030a030b04060b0315040c110705040504020a09020301080706080705090603010e04020a050307090c030e0a03 85
    0x2d81102c0c4a4820240e21100040104042403141d0350010000e03216600d1060a6912440c508100303c413060440c00c0589525600185c42103d1000301079151001d290300340700e0852a00d10200880540040c10801001d41c59501050010788903400c2280303542004110520400d600740150383c054407040b0078540c24440b10190782116039403000c900300030f44c04c90f4065840203548200005007c41a0b801c04491002d030391038001404046240c0030030340382d01c802118049880e00b00419003600815840b40114507080b00180128000c003101d2400341ea00c42e88441d07002543c404c4203000343d402110350017041191440c2d014108001c588840301e40c102809100c0f1a2281810008100d41044803015074000c00c2d00d03034a600c0040c996903055003042503250320200001c18041c00000b45031064940c0744c1c64204280e22565426145c0380101140a0f40c06003041006000e60590054030700c4e0010310182a9400070780d1903000190402c40d05401c030b030482c1c6e950303201c80701c0d40140e0500030400942c28610181080d1500c680300 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 645747203 1250 645745953 645745957
    0x403110f1003020309160605090f040606020601030f060e072301081b0a0e030303040f030207170703060c110f010c030c0816080408070b0f010e0f1006080a06080a080301030c1a 77
    0x10710030b255010001a00c512030074131a0f0b01008195000060140e0348032500501190415015203000d9640880380c010300e030409104500503500c0c20b07001444281e195580300c144c0c1d814519001c40d0b40f01d8680aa44030000b0007040140c000d0040e08018a184100da003c041080d03030500c4c8119810410100c0601800c6c4031504603034400d00d1900100c0c00d54414104100390f8000398607024640e01803000004200908c0290320011002c644660b080d42c0051759900c02e100003054085018080d1600308507010070008455a0100c12001068280701e1460b44120f0350540c10242000d008030610b0b511506000300d041c4d032620540303c07500d00c5400c020b4180d0421141c0e0780c010700e0220000805006039100800c05002081040da030009134842800340d031074030f04071440ca14003240c00e11031a141c2151450203c1e1b040c04100969a11518006800018503450040d0480d01c616024014007502556910f021803169400d0121031000c50041006955070f502d940781c20319804015501c400160244944550358800029003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 645748453 1250 645747203 645747229
    0x10c090b090f090c030615040305060a1a060309010501090b040c0e15040e16170705030610051308160605120c07020f130c02010522140a060c050403110f 67
    0x506071540110000b164400c070481e00107580c420b16000c200145013245100940c03140e5402c1e15284445181c08a02480901035408000c0c1281c11500015105100d03603809114035243c13959101c51082180e42c041007260f032007a24440d103507944490040c048001c55002d501e030a41c0f0103030380401c52000801002846003688007503461150715000303008060340c110b44055502a16218050010a090814110a500d00f80c1b810410200e64064002201c5c0c190200300248108026202c0a103150b41c1c080c10003817692103d1211b50103000007440351074150702e80103117001c3c050404c29000b03294018275012400c01322595a80310000b0058100681283c01c1002d100c8607800101c0b101000e9128000d0740700107036010800d41d01d500e41200c0000c051002c1051340341c001c15860b01460700200701d55210034085407102440030100014142000d040040042c10410f103040e04c14541c00140c5808041d2990f4440c15a61207444250000d0381c0450280203002c0c054040040b02d0034219103171030130402c0c5180803c0c00000c41c10 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 645749703 1250 645748453 645748469
    0x3200901050304080d060b040806010503120409180501051314030405150c0709020a0e04050a140c0d091202060f130309090b030102070c0b0d060e010302091501180e18010c09 76
    0x44080750801c4504410317150401031000d002d0100c10b072141c43d402c0b0990041c2c86076a5451140b000002203030300b000304031410f542c00c0405070b8514160401a0300005000c07030042d004200b000c1e0125a03000f090080c800e1900030700d9644101103540001c1e06040d001514218641c020a8000308000c1080e40d4640c503d14501d880400b040a459000e500c52050030215650f105850300b9000040c10800d15074800c000303c0c62820111030400c140d0700d88a200c40112101c0703039803412211410402090882c503240d030180151903d12030000c142d11034250703500b0782200c1c4d05003900c0d00036074460400d0003407001032154003642c8031503140780303c50b0082e6151310024105140c0788a00401180e51710581c40c4c0319202074045034503a1741c1050080c1d002540c2c0e0141c103c680d51020400c0b400e0f0600d4640003249074a0484900d0341220b0f002441c01c005515141942541c0c0740b1021502410700c0780d51031104500350410f43da08802460744082103d60781c0b03480c882c0442c03009086265444a03900d4966601030b26900401c0140503614a0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 645750953 1250 645749703 645749707
    0x101e050309030d05042901090501061d010327080406090605190311040506130509010501020a0302060a0b01031407081f060c0f021203121008030310061103090604060f0320090105 78
    0x40c3c00d011700310300c0320030f0b103c25041c2246d03035030000068040e07013840b0313049501082041180b6a60b40c0030171640150381e0310303904040040030b4280300603941c0302340c20422610240c4028038140d84500ea0f80a2184169840202c1b00300303030041800c0150300c0e04848250010305180c01c205240240c0c05036468101e80001c00b4842c14103a50380c42e626203c04045c003d480140c440904155540c03480c0c600c01c015554101d1207120f10800c942e80011a6072351000c603010382d2056042e0003d281c01e86070303201e162020301140d0440e1360402d0f80c2e0703194000000620521850182003140c95840160070042a404106040e00305905500c140c1004c00300010395000b2000e2842c1c580024501082818a20003e01300d8402d140c8425064440412980000c030900f0b404035010340014040306030501da444020603101d0004840c070184841600c1c0c1d0403c4240d01442c1c0d5401c0e504441d000b900d103841250000695107410503004040040c078442040503160350144030300364140b0505c29040104409611405e101440f038592014104900 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 645752203 1250 645750953 645750961
    0x60d021c081e0d052208180612040605010b040302060f031f14130e1507020102091c02040e06040b0606070201032306090f07120911101e050309030d05 66
    0x10000903a481e0307110840410600d1040c01c226a100c641003d0301e0400d00514080101c0c216510441407480c1e107181205415010500c40d4584d201960401242510080c0d9140f000c514540d4444000748035600d00980d5a030305a0801342420000c40d88140c115500102e8100806d20150751120261001895640262a0340e6511022301c40c90700500b880b00d01c0f001145000010912840507801403a030030905841c495141054001e48005450380c5c107480000341d410a9402c5802c1603400c902d11980102140009440c1c1002d603000700703481000704542c1400c25a0002d0081c011840c1c940511300100c00940c000b4031843c10540c031492582600035100c1403060b04001240000c590181c0c0280c455007485045864240c0135031600000c0207a01202d880c2c0c407800d0702d5000600350b0134407000507038019140783e91070f2900686038204c5c40009019019003170342d8151800c8040308040d600e8840c2c0000c2203803180d0b94240030300d401103054000100086194000d0060520030003190400010540741105aa240040b0361621 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 645753453 1250 645752203 645752213
    0x30303050405250b032a040503010b060909040b090f100c080115080c0901110106080d1103070c0b070807080a090906051c0813080312060a063b04091a060d021c 70
    0xa0101c44c2d4051440810002c1b0018030303003003002d002128000d80c000d000c0182ca040c00c02c03030300c0d100340d074040350780038001c5000304021683d48419039901c4000c41c001c94080071071010301d039441c0004904104403202e0b10360b40c0c402e24580c0d2000081d0700504003400c44074044541c00c0c1028200400042c10003803145c0f80843c100500e0b070702ca1031000b03551440d100000c02c030f034540700c1d58041c0d16038402d04103802c042406601000c215100000440340d4040d003014030f4100c0c1506001d00b46010354007a00007aa00200d090180c203000c40d0390900205070740802d6071100303422035142c11030180690303100e0752050748100b07000e495285040d1a8564030386051303070740083c64a0303880d03c42000d40c41d5030580c4d40d04084200c1c071010984c14003a24122569a00130802100e011884503568002105c0700184c440742c1c548503403036200719098801c202c005003e52903101040e42051882c200d0022408035002110107645102c400314004084c11403038500c19404c02025507406410f4200d60b0041054100001c0444001d10720041070340d01800 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 645754703 1250 645753453 645753481
    0x20a031202040f0b030a0501050a0b0a0f05090916090f1503051003061b11060c040e090a050f07030c1401200a0803100806070f0e0105070516030303050405250b03 71
    0x9100c404400030651940106051a0000c0381d8406c0c0080c60b1030004151464220100c8080320098100340c1c1c0342c4107000c10304641e08003014030554144082404044402d07643c450019101d14a010380789804130b181e06000414020482d0f02c040101c401c510300c1481617036162084a04005020704003c980c0342c540d03411b2000c00e10019440070308064944203441c1044802c13000783c19050602d507521200c1d11403420748100d440c0c1605030344503850200c080008002202c003003400640c3c030040700381c10b44441c00b12341d40760541414825400101250001c080070b104001e003100f00c0c01c0162914102c18070102d502d060019180480ba54202885035400455003c2c400b0801c0104042142d030220035261241003600038080c09034614054040e003401035100244d41c052280d12590071210b1207990b880540c240550054a0b1075003e00c009540034001c181e41120020714000d55100110311a590000300362500d8100107050056000d110010034000b124100000140588000d00350342c0100c182c82d503640c43d1089440621 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 645755953 1250 645754703 645754709
    0x30215060913020a0e25030c0c0204050601030f06080c030f0c150714100c09050d260c0a0b0618331c03020607090302013905010209010306050d03020a03120204 70
    0x5e01108020021100302c00c580c1080700900c0b101d4030b0400324003404019426030f40118400e40c00100c04103040c0c405442c1c0b03a0800798011006050002c0c00c103044404000c29142c1503084114503500110b01c2030500d0804001c1d0401083d241400f8041103016038000072403055000c640c000740010b0101d210402d00001000b1001104c01c0803084402e0910940482c102038201407440d04082054003900007020308003070710004e81440d88031000c80241200950486031803129039220881c0f844051100300080c8504014582d46580207000300c0761585002c1c01003002501c08160803040e480e52400c1409800c0c00641d12959441c10060000d45074402009400000490202e07601c81d84045030324503840d4101300321000203162034060b40c2a28440e07650410207807800891480001c0c00664807805200c5500180d44110084403029003880311a00e48284404000d81200e11054500e65400a0007000e2581c140c0301e10300003407005981418a0701100d84010b9107503103021701c01500703001280300541c604480d80e60449000d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 645757203 1250 645755953 645755969
    0x7060b190531090311070303090e0c040f030618021807020601090e0c0114090d03120e0a081209150a0608070902070f080a02101107030215060913020a 66
    0x541000803450180116007845030314080c10900103032450035080022020030a81e000d185803422041e4506801c0010041440158100b1010321220f080c0c800003400002c00648c06544d9805c10a428060100b610b041c01911844030400100001c1140440126900040302d4000c4070005007146140341d0582c003803d08400c002d500072002c0303428104202280b01c405006031000c2e802c50302e96a89586408046555401c110103503680002e4440c0483e6100700070418031642001502c1c0c0c20708a480b404030b2010414400101c0c045204844420120307810ba120b503c0c4403410100c01402060710760b4903003e6585c45010449501f01810303030000385c00c40d8400c00c94080300841204900383d142c0b070a040e02c00010001c0e8080d1194034000d032507001402c00654000d40e8459608800000340803074543e550f0200550001290200f5402840c00707a40e1400018810341074603414440302c2039601c600c07a01d0001c0c249160307501c40c0d94944a0450a01036141c4a50b25115400424050130341d8800b40c1c1030000030304181c465840741c14 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 645758453 1250 645757203 645757219
    0x1a16020301020f0d0f0b010e151b010203041529030a050a03031b090807091d0304061d040c080c0309072c07020a0f150209211213050607060b 62
    0x651801000104005102d1010800408041701800300aa8040080450016841042209140c0390185c6440840d801c01c440d014a044580d0040d00034080b07900c0d0703c00c4c810307960110402003400a440b1401c10001c5030030b00108003405080400b00c2890150105005001c0116107020041d600c04000015900382c0000803942d8111035840c00074041c100c1003004c500c2d26504510150b15142c010803881c001d03299103002a040072030038940101c000b0304540e000e2051030503645005010380a018401003020f01000e07550f80c0280700b4940c4060a0104240e504140600d182680d145031540d803080544d6008004500c1c80f40e9070351030f15607849140c414290040d0018460543e1500c48c0c008144541085002551040d24001c1c0d0390401d00341d0301c0b00014a13000e000390b44a6400200000d0180340088429820303100014100039229022031502204500700b050401042894809601004c1203200281d07001c26505a14020441c03074003040e800b05c64815203002c3c0e14041007010401c17400b508985007044000e01004 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 645759703 1250 645758453 645758467
    0x3190506010b0f2206110106031a0406023007140706150513020c120717030a140106050705100501050303070b0408120f0a0606080c03131a18010e071a1602030102 71
    0x8284c8005100e03101c0490307900008000e000e201800f55104498102c000c40b0307651022103512602d4510010001c40c0e10707a038204001900707007007003030051400f540c07a03001c18061007421038854282207800a4440c400b03000c1031141c8001c1419480303088408041d4010008620706880c42040740c003003400c03900690340c85000c4001040030480c255010b400342040c0d00085030286403811035540400c0c46142005041c9001c11182e401c20380b82144015a0071040d1414006242e820a0303022280000c800e03084040002c0300003550703a051040800c0550304085150004101651400740081d070703a4821b43c1c60045c009182100020305000740c203030a58480802d2601500c1480c0f0348031021840c01c420071540b440b00b440c035021000c04c0e403600c5a48642e200d103480b600514a1602e542031000701a2005000440c1c1c40601c0d40d08004158003c1c80b042402520590340e0404e10800700c68605080d1000000f400c4655440302c0c00c2040040729142440d0070200c1015000d580c0c2d4624850f00c000081c400410181d090b600010b800 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 645760953 1250 645759703 645759757
    0xe240a031b1107050402030405032b0603030f0e0a050a090903120203100612021204081c09030216050303070b07031e18030e01030218010e060d09060b03190506010b0f 73
    0x52001c00302e00400c0e03802c11612001040124003003543c014045038014809413100602e00001c5e4241c5840105994104c14650340d00c2800b611001d4000301e00150b0308014130341b41d0303542101c0e40750741d410004c403900c101d92410700d00440c243d5070940c03040b400455104c0d540300051501403a0205034202007032006640c0e03450300c4049115000c407a44602400110000343c51046c07800c01d0b10980d02d08c0590240a140e0383c0d2100d890300d010b80e030008580055601b480c42c412002d004028460205a81c1c1300360090941041d10001410140c0c0031382e030026010380c000f00140000940d08010312076000815003000240c070b231520140c1004150039003850804c02d6103000c8101030710300403030000070851520a90351210300d0728020340114140e006480c012007009802c406030701e04030340c0105000006000060240d40c24045084101070070744000309000e450080e6542050b023994203050120003003a2002e000305620300d60183d42c40300e40e90307581440780211003040854841100e010510440c2d240d10080034013070702d00d942400781c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 645762203 1250 645760953 645760967
    0x1404090603110108010f0608150f040524030109020102121b07060903121419260a0509160e060307030c180605040606050f03060a170d0e240a031b 64
    0x829002c114a035000150301b442c070483d04002d42c7d0365a62132218580b034045004201e80c805411440e44442400c003071080c2910b40d44690b6208110b543c0303850428518208401c0080c40c4590b0655000b81d04104a100144c0d8000a091526603e2480d15564801c103284003a60031440b80003c0130311038080d0b8a400540300380e100044c08156800707040703a11107100c1c07403840c199105290130b088807000c54820301090349082c25203001010403441034200440394800e901880c10081d0b4201303e003401c1d05d071030354000d00459204901c5030652100c0203600400300c0e501e0704100403130844a0b503c1200c4841440348001841074a06003c29001158000e107694040e640320400c0035000b820032584524210716022000402c0d261500981d01190740c19220107103852404000681a580010481c40e0400c24060b000a40014086940e2940000050150081e00d0004500421a9505905642c0b1802c501043d203400d0200441d0486400f030070124482d40c0e104055941070300903024001d82c9903010f580052540344041d42141c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 645763453 1250 645762203 645762233
    0x10204050d0f05190209040201050c25030c120b1b0705010c030207060c0c030f030e0a02030d2a02030d0804140d110f060f01151707030204180b0f011404090603 70
    0x100380c81383c03002a8450055581e140c2c14020b035000b8000320100d00594020030003004000150015200d1812007009801110110145105071140d14000f0810520000d6160034000c4c100d1854201c4581310982c55035201294040d042004015212850045422042b000c4401c0683e2000c024844d1004030705014000390044c0005845050038140c0c0813490b00d1013403c0d15000d841e45034403152420802998110003d0680c0505009288248401e080141e03030100544c124110b500d03990f40319409480600f50003041d015402ca10800215a680c0500594012501a4012006160416840c0d54a00b485144140d544035881c007503000384000341050030750050b03c8800c075484c80c00071103001d800701d0046650740e80c0341116070500306140040180702c501e10f801400661032095141c501c0e044010440403401110003541c1c42c00101f0307400501084296681070301040c00e41862402048101243d0f4007041c030341406804154108440c2c070401d03807c50420311094078050901400704000c0140c032441d0511006c00160 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 645764703 1250 645763453 645763463
    0x190b0109050a0e0a12020703050303040807110108010f030b06180901050f01051804020f01020313090c030f02090f0f040615021509010509210409050f070e0f03070512010204050d0f 79
    0x2000581445060103600e0007841e04100402d0010000c0e02c44458101071030205c0421405008000000700d5001c2010354011802100b590b941c907156890044081107003034001e40e06000c030030304c010044800c10b201d2150869401c040c0c2803e4030380d10107000481d01030407001d070b014042002030184802d20340150302003440365904a951a64a980710010048440c51055250b00182009400140103040c0101221541ba0301030040302c0c10a00303003011040f6040f01036040000b105a0310b140541c8101d500d070241c0729001c01480c8045150419010100d0701500440214074000e80c0c00095800403a2600d41c0540c0007003851010305011f0050001e0000d480725045503000e001c11a0603c0032844079801803080900800c014070040021520500300d4140041e40c010702420405003e0000045c10700d03590085610844c07407040e9204603440c1c01400582502e801c8420b503401003102845103c0c06403000517099041e5041200d0514116841c00002c43c068880c40e080030341c018481c914902c0803c0307072809069030128454 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 645765953 1250 645764703 645764711
    0xa060e03030c09061e0c060a0507080f2205010e150c090a1a13152304051e0d0501050708180a0803071803080c0709020f03041202190b0109 61
    0x581141a500e0006036581000707158100040821031411200601c030662184500e460780c9070440d804000c80c0c0e000240009540e4000c1c10030840c903001944035081d842941400d0a48190a2010800595690041202c4d08055000740800f225140c1400c00c000003542c07242c028083c0301c10800b209911180d150408844680184000c90040401c1009495a111002c4c0c0b000c02160720300640c804842d2002006525100d40410146480c1c814a01003140500034240380300c0c0b8a0200110000c00340139100806468951001c000d00c2400702030501190219001107408040035a44910b8014515031401c2c80719501107000603c0508204064008500c1071700c3d6501c80c841165120100d000351810500190112034002c0105100003c02d8a8050368000328645050145040c0701c1451b80c034007920075001501d40000c045101102507204001c0d00018090902c0d095043c190000d480740014000940000d01c003084451401d08818420080c0e03442c0880c81c1600c61a900c0001c3c00d000b88140001c1c06551034007410 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 645767203 1250 645765953 645765971
    0xb0d0c06110d1b0305220914010b0703020d0e060c01051609080a03020304050907030b06030a0b03010b06041d09250501020d03060605220b070b09010c02070803161a04050a06 76
    0x30003502c080a01c0401d0b8010301c004803070354104c030140c0c00030301e4001050b008141c02296410340b0341d021b40c014000d48600080d07425860400b0340985001640300a038a00c10812200e000640d021139500d040c51418282140c900205038002045401404080d0b040b961030b150800210300710b60403e40c2d0340c4083c00d0300c82c4c0e590603440c1d00f92140c469003500000b07005a4000c01040255040007c0e00544c4108617160014010f0041800202c15500c1950407543c0c5646448004415107404c0c811031303980300000c80300c86150503e410001c00105e035036410749100800940d400240580c00900000114508038218032019140f01c003600740c030280c802d00649006124043c401c010542c06881001c0a481d82c681381c1d01d0900c540d0340c24601a00e1508102c03848901e01b041000160608400098400c052003032580c44031070700c0c20b0390185003100c0060700000210b500919042080700b1003c03003104c015480c64280310000c0211814000c2c000c542c51524403c4082c0e649040005109010410606a5200d171809010100ca = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 645768453 1250 645767203 645767207
    0x60e1306150b0a03141e0106110a0f05061915060c0212010204030c0602060601230d0b152205010c0209072a0204150501080109090606080703060e0f0d0e040b0d0c06110d 74
    0x920381e0380350340306c018900d401800080d0080c1e070300400010011040354072421141d0780e001c1c0741030801241150680c0c00350050114100051390440403515088008025822040c0603406496460b0310500d404c1c010000302079010754442040c2c80e0001e0701080000e41d5070710303540d14210300426203e204900c01400360001003182903110308002104448110a0710400c0780c0300400310b00c100d40c071402002500d940c0d80d00410615072030b50050f03600c900c00391540d061348442c0621400c1000d0140b4001032081d0110082d0140216030b0001900c841082c0c051350881c0d0155100c2c541a5010345500c0c01c848840c60074441c00805d15292850040807a81c0300352000e00c0301713800501e0300280c8a07010307004a40c0451034020050002c001c90b584070724032488c0201004a0313160b0381d5444c100c0c10b1442981054410f26103a151402c1c4000c420095079000111441c01445003056003070b002801c0c182c41400040c40340351200000407140c3d40b80c0840c684296000101d45a402e0794500b00540500025865001217004403400b11501c54 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 645769703 1250 645768453 645768481
    0x201110a05030409110c070e0a1104180519060e04110f1018030615140d03020a081c0c020607021606020a020d2f0301060e1306150b0a0314 61
    0x107503011004604142c1084070410140a40d8070394041000810311110002c1c0c20f042041c04000c041c0c92042800d2420541140340540304084030500240344200010800b4a626080460003190310030b80c00103450700c0e034440d4801002c0c0030000b940c3c0854202500401c018200080c01c502861007503154201c2d8145080500228043d201031a5074001922001941c400d40528a541f031041900d401403145142caaa80311000c98101c101e007104140c030100c40c24028041d00705480748406000300d8800f01445103960307000355034481d001c10061011030041458010300c3d85808481f2100610400c0910a83d000500c0080d135912086600d48010310031541e854000c1c0403c41920000d03903107154007401c10744465801340075503d210072500716403000c0c0c1c1c198400071115040003000461104030108004c2c0c0a10482010b09507840c541160281c03524440c20720040e83c528815100c1d140342c0c0702c80c0200d0140080201400f105881e81e015040c000c0d030020704014041d505030300140604101c3e0100d0220b60700c451035100c0c041d07 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 645770953 1250 645769703 645769723
    0xb0a09050f040f03020f0a0605191506050c010b1509010822061805010606020d09150807030c020a020603010902122409150d03171609051315080a020111 67
    0x40142000490041801c40384094030460280c0101c903112010512034605d1f0014442c020f42d14103503614244030010044640c1401190100d46040c03000190014400580e00a1032141d08207020000400d0190040290401c0c031038507070b0080103006002440c40814429a0064596600040d40700f0000b406580200d584146000401420004280c0c1541d0380c900050140b40360b41980d42c1040080900091024000e0302e002d0070295015001c150503240c006050480c094000c001143e0301d5100442c0d1144c1c1c01101e041e4080f50a14000c1000854000c040e401e0100b54900a50014400800403803015a150014902100e00013112506a581c203424915034010b118040c01d0305800c402d400c48000e10b0045c0b030079030b089503150000c0140c0d614a10001031001540882c101c01040c0030a89140c0e80c0206000c1150f4410718011184c00c0e0b0003400350f0001c00080381d5000d0644200203050030021803d00a501006409821012100149440707850003a0303903a81001089002400442c0c51130740443e0045685111 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 645772203 1250 645770953 645770971
    0xa030f090809100512040606150e180408120916170703060509030c01180201110c0a090e0c2101050601021b060a03090812070207120b1b04030c090b0a0905 68
    0x5146010042010089481d0100700800038244080352507146039020086c0268460341d80000c00601d04500000160018000340301400303000b11840c0c5c1c05881d2040c02030135201051840000700d580c1d034940441280501362208030394040e5982017102c16a400100c400c40c86010314030000a25a55004400c1081140e41d241030181e00314900070000504075800c280c0d00b0160810503641001242c9e034030142140d0050010342041c400451804041d96008091f15500340e0701c04000d002c0013414140418030b500441c2c803440d040030703a8a80750610610070601541a111000400d820100c2e4032800840c18880c0050b44d40218a5191101042040d800002c040801800000e111500c6110a0007003114079000681c500701819291f20f201400107614400030040c80000380c0b01c40750326080c0500024500300c03107074200444280c0c11081d1600803e0900c10350951003250040f5a88080880700c420708801d02032588020b040c0b0543d00c43c007080032105600b0001101405890b444202c940d50b40c1510b007541c43c00d90f02410 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 645773453 1250 645772203 645772207
    0x41a09070614070c080303070203030403120e0a020904150e070312030203010f0611010f090308041b1a073e0301050103030c060b0102070e1807090203090d0c0c0810020a030f0908 78
    0x4110800700003e810f0450242d480e920540d9610164281194000c6681d040144c0000080000705034011005c80d6901482e00820001d18a00c201420b0344c6041c400c501030311035911030000804200c814030818201102c6900b007407040011f0701805a54401c410f010407503400c0705541982d101c5621030f00c2503d040303a0b000280c0c5081185810401e1701c00b5019500c0800595494500c2c01c00742805c0c6004540400e0722940d00c042c0d80b4607082c10400140c080203034022108482d11981040b0040c1800e00e01c050090300c200d98142e98505925220400e0030510300402c000f42441d40281104014441c00b0b0004600040140c404074281c0c0070825003200e009010007000f06802950b102c001c40c2c074507030003c08128410b004407568075440d4202d0307a2400c041141e1054405d207081c0401d00650405003c5500100180b420550031410310400301ca840d00090040d9600b009000e103020000d0002c0c41c010b181c000c014440544280140c592400800380d801450001c010034140681c02241c82803a1103001c1c1c0c0caa0b04040054 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 645774703 1250 645773453 645773477
    0x1080c160b090f0d0e03160b09040b0303040302090906040201020d090b1b010b040f020901030b04060f0302101407060203010509061210020a03060506040905040b0c070f02040b0414041a090706 84
    0x6408078025001094900c41d4050307150a00c1da0402220103600c02030f448020300480d0f44000c0514181c0401d4080010b2880000d08001d00000d010030395409010455004c911600e080f404a8914010b035400603520109400912903901000704805000318002c0c1c1c03c1d01d1240c5043c0340180c2d0101c280d07109040c5c84d01c2040090012955254200d07000350442c0100200b20381c0e000d100007400361079001d00301e0454180c2c002a1b80d941e1307682510a440500f0001c1c6d4060020510344100005403d00c0c42c40041d00400c4000c0b42c000c0300d944144100c0c0041441304030429103696090400d00d00035082401a10700485003400440d90910380721500340030303959486008003a2306a0a44914010390007603c1040f00341074588002003070300d598080c0a403002c2c001e1110f00003682c0c0380a090502424002a08000c0010810004840412260309031410b89076010349010803011007ca0100b4000c02124a080c00c25010010500003000890307044124865011001e814040d1150003410b41c0b62000303071083c0c0c00030804510303050f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 645775953 1250 645774703 645774713
    0x5030a09030e09090729091507050307060f0b0a051c060608071205070608060d030503040f2306090102190311040b13061832041a01080c16 61
    0xc0c0c0c040910a20707052149001540108201410607100b100040c2c10890040c00200c12100c0018295510001d403c642402056003200355171085683c1a0301800d80211001421400c0c001142c060a60000440366228600e0602074000e00c80c10520044040c01c101c0b50023400d00d800381072041520300041a101c40368045e60b076031070900307200003008503801a10b83c6000500715100f0320082c0300a00311601e10b40040f400915150f030509241e0742105090101d07a200b48100d5031540d180f03002c00c403a810304107141d40e5204d506118400d2600114003d1080d40190464441c0408101070180c1c00710f66041254140d84491a505085c0c0c0255100c025002490415051950344685c01010003100c400c003003a441c00744c032591038002c19800a28a421018a104020414280c1c03081c0295803006001114099481c141042a03041202040754410f9041080d08840a0841507404481350b1800003841003100c20611041a5810071002003100d001c00c0000002451070328141049480341418441140c2c1b002803d5624 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 645777203 1250 645775953 645775961
    0x50406080f0907090c05210906011710050411030c030d12020f040503010908031605030610030c110a0308150f03060c03090a20210c0f030c090a05070809030a05030a 72
    0x41642c0030f03c42e4036400506a603192203000c2080c2655a60300d0b80e034180c1641041000707012040f04448000c1c801041100d44d80012808606541214803404852120340c01c00d40c0c40e2060003443d66010500c0c110610041042415074644050340580541e03480711111400c1544074681d44402c00301144102d0340050760b00d8200e500500b078000e41e00c0019401c040e181e8011a08561460808413034a0100009000400760700120b10700c2c07402c2d15882c090b440c0d4030345680800c17a451420304401003499221808078941a00480340d01d611a041e0754100d0303134402d0403410014900042079460000d10011340200511600741840444810240134009108a460707540c1d1000e4154002021280140108290070000503545a80300d00345d2900c8040950480680fa010000c42c0140704410901081c2d1170b4002c512150b0010030700341d0340d03041c04071a0203842079080780203e41485034078a80c02e640201040700704040344010b580081c1c003403a055914061b1640d150020385541b0b109142070400403401c1030002030380031001600 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 645778453 1250 645777203 645777211
    0xa05010e0d080f090f03060408160303060b0d060f0b0f1204020607020a080f0c0906030a030320040609170109030203030a0507170406050421140d091407080706050406080f 75
    0xe000c0300c2680d54030b4803107068200c07207440303190b07503800003034101031031921074000514418110007074030190503e6038502210f445440e21500c0c1050510704c0d903400340f50107944800c0007002e11122942d69660349104107002803480f0b0085034108240a00040303002d00c079020580d01d6104200c101075280142146010019043c02481240d005904000f41c0e001a01d80d0403440c1d00400e080001000c070f524000003100d003011000303040507005050076170070000a540e0000c0c1080c0400e800d403c0003d8055619080c0041110450900e0300108100242c0000c0340307a4031080c044100c40e44185881d805501c108141800d803040c412001d40164024404101d01e100107900154203c04141010b4000280074030310144c00c01421101500d0b01580d460410051014220301800c0742e250390340b0303a580780e14000c00000d0700005110759160350741400800c40302d8241100d81d00c500c4501740c2021500700e110f401500b40a544191501032411680220100020414004d04c1035809852075901c40e5101652041f45204004038014 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 645779703 1250 645778453 645778459
    0x403170c070f17040b0d06050d0c0e0402040e0d020c0301060f03020d08030a020915041d01080318040e0f0f0d111903180b03011406070f030309031701060203040e150a05010e 76
    0xc0c00503c40d43c040c0041005003082c00c0040e868166010040c0c044580d1948981d01031064108032800145840440c0320a807001c41c1ca000d200c85d140d5001140040941903403440d8240b02e455418036003d6000100c050b508c08044000b405415150b45254075080e4051000030340180030444800e00151250014592000d8407400041c2809034220000d110015003202c0e40c80b4034100058244500304040245200030006040319851651410b1102d55880c4964402414140c4c005031216446540b1900180b52081c8030004030341c42200e4041d080c031b40301c80c0c45018000e50351040e0004915643d000ea100b418011a00c10040c180c104280314842c2c940d418034210850812a01701d004444100c030403c9003101914625070070070b8481d030416201c40d40955000841c07501c114014024940090a4200d0b0200c00c6c0c1d515240c041307440d580918056884204a800d400107400d480c100100c2c42950000c00341c0304942006004884e151a980b2170802c2822a6a00280d0400540001409554060120b60003107020103 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 645780953 1250 645779703 645779723
    0x19050615011e09090b06030621030706150f1d13020a090906141b04121a04050d2d0f1e08090708010513060b180f0403170c070f 56
    0x8200440d40341d00c6459040b10120314190001c2c440fa0180740b051404912050f160f940c41c5003480000200d0840b00000304080004980c1a00e0312034500c10f10a840e0052361140050000300311001d40101700ba00c0074050204168200800000c07024850402c184440170a0001d0a1980d1130710340c001400d088001d0fa00342d03000180071000240d14100c074403440b61814003428001034007070049086940080000740010861b00702c0a501e264800c01000102c40450f200d84e81402e2414105180884c007400c00c031201e24080351628001c00090000c0032900140034641596121404074514454031008000310718840261451030081303681d1035000301c801000c184124245400084d0411805450141801c1d04000018008206104008404000c10700181c00c00030020310451406010f924030300044040c020300801e40324000300403242c9488140c42d4400300900001240da2400301c0030385448000030f41e401c500080142840c035800c035211401450140d26050079880c0b4201e00c40e154100c0d9190706c4e1405586003070345 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 645782203 1250 645780953 645780977
    0x201050c2d030a05060301150f0605161b09110f07030f020a0804080c03100203011409040c0906060503070e0f030d0c060f0e0607090f0e0103080a020f0d09081905061501 74
    0x4480034510580c03100c6008201450901c09060a450000400d6403010440300030074041020201074520944001c0e1502f151240c072211740c1c03100340300784504014002079007440c540c00788914258a00c80a80350150020b024201205546c00c00034400c4c2c44500c00b011109002e0040024800d0740b07c1c800b1000244100c4d00420001d46902c24190310a51161038181d05c0f2840d50300080c00d084c000984451188a0b04600790740c50020724407904880d040282c0c0c4a00c0340c0b880020100496440c4d86ca01421125404020140d02d8440140a981c004e03150400030440a00c2c0c001c08034503007054002103012002e0090310b0301b1400c400c8240c41d2140464800c03503827a0340315521006409814441c1c846140034400062505081c1110003034411425a001001c003188083c0040c010209404c40d0f003411250310076080d80e82c8000d90f034422420300c08440d071003404600500c844110081d070300009850a848468041e0f8104001054858014070b110410007007580c0c01c10300c001189038110380c815120804040c1070203da1890 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 645783453 1250 645782203 645782287
    0x140c0c04141801151203020a3516060b040905030304110f0a150804170c0d0e060a020a0f0c030203060915070e180901060b0a05190201050c 61
    0xc0c0501c00800d004049034200001100c010500e0300307001d407000d4000c1001030350440071580e926100d4024803803160110000001014400c104000d680f07030300544d903200c801c2515040d6482c5ea00382c00b40410180c0701e05c0c5191280700164401142c07101502e050702a0060051503440c000640712418402d41e109588110100c0800c10500045102d03d1050146064103a08103003008010420030140a0061b001c290042c000c6e04d020b001c100510400e1810207020b42d54480c03800424602014400c0762201c0400b01e90702a0b842d03000140c502c0c812050342c85c0daa00f40e1408909209040c020b8946034401a0301000c20040402c80200e01c40803464040c0c2c00c80342d00340e51242c010a1411005607090107c903800210584c40e44154044507541007185850160740051038080002c0030701041860380403083c09132102003500038809600203001020807058081c1c0380d552031000a0110b4111070b04020340d00c8a17a02d50b1012140c4180b1900d440b4550340b01506051140355441c10342d4003699035000484140b5000d5030103100340 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 645784703 1250 645783453 645783461
    0x6040f0906061e050a1404090602070308040c0519060513050603040c0e0a11191707121103090303040f11061c0e06040b070f0315030b0708090a03140c0c04 68
    0x1809000d000c01c00525100c2403030b03200f288078a0f100368002c603400401d010315136070304021804807a40300303464402841003140000c0091403107260041c5490310004d040810103070840c050034416801240c110038a19620f00038041508510001840e81c0c800c01d0506009690151340075014840b2180c02c0101d90607190408120f40360b1044d10b0075101c1406884040008040c1007503182c1c0d001018030401d00140c00c03100308007021401500a032402d4442e003a03201d400001d200714607483c600843d84104904a0402c004041c1004038079038807000c0b085040058100c600006401200e00a11100000750b24540e51030f02c1c0c1c80c0c005008006d003180d0309203a03030030081e00d55654440504014020900720744800300c80101503078103d440d41c46020350607800c03c10070800889d40d031080382540990704e41064407c585026108178000c004013607502840c06040d0b1b001000740300064503002d100b80c20a858602440d03e445d60703410759600f91180e005001904400310311441d150f007000500944106081250119461400000c0580b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 645785953 1250 645784703 645784721
    0xb1206180c1b0a0812060a120f020f01030b030706030b031203040b04030c020d080a020d03180c030201030b060904020706020d1515200f100c0f090504051e13050601050609011706040f 80
    0x171203a42402e2011902d81030848100501595052441c03420283d541c100d0030b000e09102c00381c0319410074803030403006034008e4000300308566008080d16620b9407103100c09001000d40040b814040e100f400d02080c4100842c604407030007a40c0000b0304004541d200c1c1da0840d5034107031032501240c00400701c070710305070004244001510288000360050b00391060942c800500311081a402c044e0303c0400c45005102007141c0c0703500350042d43d40a280100e0444440b1020952601c01c65070726541113480000c09001b4090300d40e02034203100e06501c0081c484401085424195080b10380070305040040003805a003c114001d00d0600362854900c0c0360464211000a481e40c00c00d8142514402207800c04030300d0380c150007840d00c12000b101400741000001c00b03a0750000107100e98014003445001703980d248080344901d040b1a4a0300b080303084984078150945004009200d107580485011526403040d0300c0089428a0580250381380200180e48810f14807a00149002c080308000e04072680043d619409618401c00030b0148d6501 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 645787203 1250 645785953 645785977
    0x909040311060c030c1608040f030c0521030a030f1d03130b041412120f12010e010e070f270806090d0c080a0302040b1206180c1b0a08 59
    0xa074462003020705040a4008001005920080082114040400c0141d6070f80d4002941d01031818212481c14540603c51604803030b8185560242c0013041089811420058580646203400c0000c550032070703521406003403600f005007600144110040d5621170350004020201d40c0c840400d02002d00c1d070013403212640340c81c00107138980c0002821001401c4400304034002848454041441c080c60124451078488a003248039125240c40000764001c60020802206040004c102990342c0b040034500a001d81d80c032000c2c2c0341304810004000081c0da0b440f44a1001c0c102d440003031440f141952500001c41d007803952a60350009000c0030788108c03081480e0b5485e00540903404010010f81ca04e040c1600e051520070300501c406031903403004600c0208294005241c0f0107556000351002e0f1204101001600030f40110382000070004000306503440e03403030b10b1600310314007400c4150354a10320f0500c40c40c040da1401c5012641120b1f070300c0b01001100d415866010b448050381003620b0550f82d0300280c1340c3d1207950581c003041b00518 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 645788453 1250 645787203 645787217
    0x30421090608100807140604030501050f0709080d080a020c0f0106180f0e0d140d050a020405011103070309050f15030f0a0b010c20010908010c08070f0302040308190509090403 77
    0x607454215081c243c100e1102c242c042150740c641840a69605010300410800c3c42c49900c04204c40e4a0380e200750381c007540d80200240719614100700e055400c00d0080340c1000004080c0c0388000741009021609505d10303002aa5180c81d41e0369403101c840065402114504038034810711005c401410760a1280f100030b800490342c5149201030707030f00c5440c05a5102810b40c03901d00345004041070f028000020601e480311003d003042d60320034161281810040c014066444200340c1030504202c064401c42d80100251b46098039507172810020071038590b940307010b214001004208920740a002c0342c5040d96848607080c000a00f02602000b110506401c81d41059854802002e550003d10003c03000600407408610021b10b40200c503114030392104104044090000304020050b628001d0403a4414441305016080300802840940369031200141b0000d41124400c0c0080e050300b2481820b14803a0085a0440c3c0e0043c0e6141c1c104852800000e0106c1345980d40c48040c400e040040d0041901c0740d840e8140708a010342c840034 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 645789703 1250 645788453 645788459
    0x20f0903030705010c0e04020c0304091a18010608070905031905100f050402030d0e0114071e050d0801090b01090501080603191208070813060e0a0c09020c010b1f0503042109 76
    0x64041905003011b1442280140800307002c41e00c000050b24102e60f94550b02040e402e580c42050031803032079502001c3c2c0d00103e2132150301d89142000d1816904841a40d9103044040e0b07203101084070046168040c85a242e0400c41a80f000c2020340c5d1181c2d046207025101b9070f420764441d180390384100d030b05916020340b0f803580719070801043d4a418440500500d4044c00d00501e40442c090008141140b4845a07140d0200041341c0710051020880341004081d000e099980444d21260074000d940341950b500200026030f8100c000300b07007140320b0300618100402c1030711042e40041c02c00c001591f1002008112540512440340821200c0201d13409000b01580108490300d519072080c0d0000341172070705c018804002d0010041c01d2058000d81d20100c000d0542d0015070001b070808103004020704200007464050400d1440d4000810580e040758010714031051644020040180e4050901808086850242c111a9042103100111500800085601a02c221042401c103200100054414688203a942c030000302045001c0c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 645790953 1250 645789703 645789707
    0xa0210060b030402090f1b031915030203060a1d03070c030c0b0301032001020a02040e010c021b1e1c08070b0a0207050a031d2d09090709020f0903030705010c 69
    0x4001500300d03503007401e29602d059004134040e407038054100b10300c02c40c1003000501c0c1d100e000740300c60f84021800000c0c039a890900307440050b40312030885242c4822030301d0001015030f004c802c0c51410040303aa0281c044d0003542c0d100c0a021f002041d40520701694900303015604002005c0a00061a0b83d6200318003100e4800e0441c1802000c4880071b4100700c0c290002040140045506040c0b03a00c561046401200c0e400071040004034107104842400035003041c284400200d00b200d040d080001b600d4030b02d5088603883d100d024200480f0030b500300c0b1110341050180782d843d11101c20310403203007061a1001e442001d80454201034001c50790382e0700c0d01c20381e070070030000c14810100843e120070a500312004440c1581810402d03101c59454252401d801424401c044640c0041d000d460900590022801071959142c41c046503603004405500265104181030814404982890070408660141202c00000c140160030100200000c3d40524080c45881a080c0802140b59030700f007009011045c852070001c1103c0250180c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 645792203 1250 645790953 645790961
    0x9030c0d08040e1b1602150304030c05010b010507020105121e01030305071e11010c15140f0a150e0c16081c02180108060a05040e0f0c01020601050f060912030a0210 72
    0x70000c900503144054245222440f016281094404d401c1c0e130082d10303200d1000901081f00b840081c0405100401008141a0881101401c2c240140300a100b500c220b24011541071140f401c000b800724006003d810300386446200031990040d0a01381010055004020034080380c4400d0380203c0010703400080d41d0042100d00030003407040801082e060105040140c3d101c54408214980c130a0410501411031414003980b100c01e440405100c2104100c81c0700140741130121288200c85010aa4081e20003007085100c10348101081c01601c0c14060720140d0908090320b00c0002c010b450790810301802d001003540f82e00075000700300803184a10781040e0340382d1030070301500d004035481c0c80e1040700540706100d0003103a142c603181c00022100007481c2694960381e41c2d9000501c982000e401c15038201d0702d849011200c1d40c10006041490710113080c11221301039080d000490361100240503803600100034400310110350801d90701074088210700a1010f13552a40184c0c4451441c0c11800140005a2084814a03040005480b0b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 645793453 1250 645792203 645792211
    0xf07080606010c06050703151202030c090618130209070c060b0907051b0f03131a130e040203030c0a1101271716030305130b03100b09030c0d08040e 65
    0x16215034035001001030016203443d200078148903203540005040714802c0e0f0152103410030b000342c0c1861003611050341c80719580414004901034070070400199100e01e490142d840c03040d40010651003110612466800440c0e2003c1d00d081c248554031070700d031070060ba10315400510401d4640c0d917450151086003404010b946914188500491059040c850103a91117002c40d00350a000040703102d943e14134841f84914000454031006204e000c046107070000c43ca03014006004440466825074101004606c0382c08482c82198001025620740e10010045040c0301c601242d8424001000ea0303040c210b85d50798580c10840c01d66000c417100c654810b10310209680103079205204260103d01502d0401c034a030449880d0040e00e00440c0c8059114505088103004204171032140ba603210217013011195540c0c6005040d1750400300c8844895040104081011007000c0d082d64404c1c091110b920359514130b456600e2410f44c1c4031401c0a5018015201c0e02c80d9691684031140e0070142c8600841c556613890084400c49445000d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 645794703 1250 645793453 645793469
    0x705010e12010603150c080f220203030408030717040b12040c030812060907020123130213052a19050d0c020303040510090201211413050c060f0711030109060e0f07 72
    0x5000c0c4048000e40230a100d42c081842c1041c8110340b8180346850480340182c42009516210004004c00d803c14003002410809100700264240003118412000c0e05000e140213a40680e07109000c80c444000081d00c0e4a40c0140c002c82400003056100c2d10303842c180780e02100209600042100c1445050b0401051456002500c2e100820082c00c10652107003c1c10804403480d08042e090001043c000f0045600040603594028203000c0416107003400100604000c8a021240c04860b2100d4410001325800b4816501c5150850034505030621584840c000031041c40030040110901019990320aa4841d405414001c1d0b00155160300c0c1614186284c45c4e801070014103441e00b000061001030340c100c981314400390401c80005100141da1242103004024030340900c0d00ba011480140842402541012481e090103031094035921340b0304400b4000103205218041641840401c4000f0100b19201c00107225520010000703d4451a180c5886060b1004c0300050929908030785007c4010303800030400000100340603 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 645795953 1250 645794703 645794717
    0x50601090c09030615080607020604170a050301030303020d111c0605120c220501030b1f031509020a232407061d061611030c0705010e12010603150c 65
    0x1d200801c0c0310355500c401481c807a21910403015505d1030108001c0940204400c82c2d0903890708090080d9100d900381c1e81510424091500c142d001408042103074243c091944400d0320316444c1d40d5003200298070031907019446540d0760004002c1c0803107220040401503041d48500c08181c0241c00035204a8050b9882540328800c0d10841800301d0001041441340b510f0111100d15103101c020a00b01070918001142c85441450800081f04114841580c9400380d1140b140015080d47c03c508407080e81992400060030030002d0304084400000b40e50010580207101812a8010f1070b6140d0500401031501c003c00000203001080b200200e0414034401c0d404c0000c0c0c140460028503625090802e644078050000d0042e54442c11059424602c2404900446100c04101d94a43c5001c0c000886008141c405403c005807c000300188a040c0c00402c0c2c2c0c0081e00c801000c1c1c200b0700d20308001920711251003008503802040850700145084002e00c144c000450084070940c121044c000c846030212010500e850041c880b503 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 645797203 1250 645795953 645795971
    0x2502061905040f0605040606140603060306010314251401140d2007140d0c020a0b0903012406021203071b05101a0306060904082205100c05060109 64
    0xc000e08400c004502100c0016940d10b86007020880340015202c0038107107600b032100b4842004025070220b404c4a41d4201e19001e03a820140c10460705100c242c8a20b03034198007072401400400d165584801900c3c0410044425500442014000c443c1c1d0428100480012040040180d2408440103580a14007442c2000240d00800301c00003407030040b80c40a00206a803001e104020f00c0e071800045206a44c0c000b03555843e1005840d0601c1340002640c500b140e240211181d00340364a0040c513020382a40c2c2e00401103551607082c1140590260090040c0551564841040780c48140c10b000c000d415181624440d1407403c1d003803110103460074202c0d140c010032600c03081080140c0590310288502241440340c1c0d94a038070f80164180203103041503141b840380c0303000d1508041031404141a11070440360354041d4103036000d698400d02088000402104d01030040001040a070407492007100701075524180c502c042520054940c808140700014030482400450019462101409001c000203801003810b1341080c410303114 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 645798453 1250 645797203 645797221
    0x50a06020a08030c0c01200a0306050103051506030a110c0601030c0506180d0c15020309120f42010e150a1202120d09030b010602060c1c14250206 64
    0x100042000c944c8520104040f4041c0200790020081e82510f402c068502603001016800540d07c10505a40440e10300180050f1550090280f54860050080c40002110031042403084590001b0520b00b0b00994035400c1004500134280070b0701c8082050001000303907606524162110f152180c00040c8030305d006001e10390b10390301a500749980a29054442103902c018520b80301400500741c0d0402680110710038510680700d940040604040e0208852000004103a110220b0312010f08944a401c00d400c299010038119404001c00600d510712070300c002c0030b820141c0400c10550a078495082c0101c0041d500104080c107200d00345d440c2c0061103601028000080100081c80d84030310f600c5254040e50003282e00c1e0f025565140000c8030000209415140b00005008000301008100d003c104e40e184c0c0844000b00d40a032000810920480d40155050300e040c200442420208605604600d8840d450b402104407007074185031702501074050254a200102e00080720724941461070344102c01154040320410200380 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 645799703 1250 645798453 645798457
    0x180a1a03072124050a030b0a15030f08030411040516081009020c03030403020d0c0803070305180f150604090c0509093d06180c09050d030306050a06020a08 68
    0x1400d801c2c150701004460000801c0315040086651146203010103a0a0140500488005014005180e503030881e031914100515050795010207019200c211000521103402940440442c1c500c4245c4490026aa541c60b0100c420340b18508550545c0013200f480104041d141c180c00078880c04407400d0101c0c2c07401500901e88a0078500700e0b40c0c200704410000c0b8813204066000341001d001c100d1701c01d64cd1070498a148503a40e900548080300140304030707540140518440c00400040a0380450424138584440034210b01600f0043c1100001c500700c041401d900d258200121007500040e1405019160341880388000c070201c0041003e40200d040c10083c00000f00103010860603036100b1151100c03d521041c4045241007120300700c2e015150703404400e02e514203440c3e2208100e0052940c0c40d440658026120403810380d14584140104406032904862950034690456445d000041c40c045001e6640c80c0002000b203296000d05602003643d602050150381006400b260141c4440c0c0001d00440b40a070355540c0c3d0718 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 645800953 1250 645799703 645799711
    0xf0405030a03090311250501080f010e0402030c060a020c090a0b0109030b040602130303320d0b130606030902040b100c031119032006040201120b0f06180a1a03 70
    0x141e5900e2030f4404040c040c134000c002c51559003080300e0500d801d0700d45442c0e0720449211308842e400d610070000100c540c860102c1c0d61040100080d2a5816460310105c0751003c540580b00305c2c0c0c540078000005031301d500c0b00e0b00649503481044d0700408500c030001c814031141a40c0517100c1030902c0e040500c0304c6c0d0f0a1344c00009210882e94024a03002880c0d030745042640c02070250041103400d54213402000010b0681c08050107104110300100e514407294442d4020b20814100180d000c00400180002c400150a5910100c610040544807007259540d810750801202c0142c0c0141d80820b0341c810044080d801c061040460403007044e540d5005c0010110406003d24051741070050410844100c51110940103114512a0751650304c0480100c0400b450301400c0d590b9100c07210784950301060540d40744890009641d90040790103843e5187c0a240c1c1348454000b40070000c40d030380d030803142610300c000050310b6400090008070b004002c4409500f11440402030304195607402084403211000f48603d100f40110110380d00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 645802203 1250 645800953 645800957
    0x9030b150f150a0f12020d020c0f0d08060904051c11010c09050f1c0b07121b080c0c280501110a120f0603080309010506010e1518010c170d050f0405030a 67
    0x8a84e00c014044801d04003004413541400d00200342c0d03520754412a0003030007101d010754040d07032031a500034022150b039194032032013000010302c401e804070380d0360b04261480c517410a00400c19901e416504280c0c1501511802c00c080d40050030754a03107004003c5082c0704107180c2d81886d00d8004d16581c645400985e2061000ea81144038006003c0300d0081c6455407941c807110a40c1c4160540c00504d00400050030104000801005050030041d42c501500103c0c80100560801d03615040313155225600014115000064448198460760314007014200080c0580b4020781c52040c1c5c150185e5205250150a442c0b20f1548071010010600405c0d04044d041203284404ca02548000100710401d90b003c20f024010310352000c2c2155400100740680c0c03100641005204910a80b2140900350071201801440704100340609540e410030322840f40d0040d8059144100b5540514190020038075940340c00110b50304140012824410003e620070300089207010b629032008900400202500d8a521200e459105005103102 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 645803453 1250 645802203 645802217
    0x171f29030604020c0f160e04030c060b01030f0603050307210f0c020d0b01091a10350907030c08010c050a1803080c0d08060306040f030f09030b150f150a 67
    0x36075516140d040d500300c41100c1040f03c41c032907501c5070702c5522450803140e415044149031a02041d00040c00d040c2a0183d03078543c0e00c4103080e61003a280d0030010464150030a041540307403003071405040040d005d0305c1e014502890145590f080d49140c0b0f140e401240d04030042c3c06c1d0521041085c005508000641030000d5a030a0040175040c03a403001420848641c00c0040a0302c81d6180049210805948469820101509441d100c400c2c00c00070002142441c0d0389040000b1111a110704442d4070198400d604450310090196401c28441da01d1302500404807614800c99010920810a1000c40c441d490300038101c0a0080040c4101340c0b0008100744182010705090000302e46107512084c0903826100010742e040306070651526400240541c03600c81c0841e801000a80d0100803071042e00c0c01041c0107015075130013002d1101086060390b0594a02d40076203982030500103250400000b003245200024891541c208404c082d0703140a5041080001200e40c295005854030340b22901808850011241852250304102c4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 645804703 1250 645803453 645803461
    0xf090314070311010f050a0e0f250902070b060a09050637030818060405130c051b2116150603060f0501030201080705030408070b040201171f2903 64
    0x1d00c0d5180702803402c04640d845c00020084000060344402c0c0500c0400d0760601400c104900400d07070301c140d904040c00c610380110303822205a003080748254007118188205071026591710240082260800e0006a60541500e01045030703a00d011105c03440503040703161302002941003102c0400d541c0e1003019000340d0074403012904090601c9800301007a200400c0d00544002c000e44900c2c02580301d411180710117807200f0f4075652000c41d500d03054040d1016aa0040c10001c00d010041002401400c6091880030602004000048455500015480d114030501c40100500d1741140e48000150582404810350307441c007801003d0705420b00f0480100d9085c3c12001303c6070040b0784540c00d00010951580f005201c3e13858100613005c0c411481e00aa812203000742c80d1144103940d0020305680c0c0d40320440e801030507803000f0070151000a10201c42c468015006141004040e60a9842d41c4510001590904d400d0340e242080344507104142a02c400251901d842d40c2d011010895080c1844030000c2405000c0b6410044002 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 645805953 1250 645804703 645804707
    0x1806051012120c021c03020f2a040f020405031608061003051b030f07030b0a05010b0705030f030703060b0c0a02030d2a17190909110f030a0e030414040f0903140703 72
    0x16054543c10000c90780d41411502d0083e40d0703404500321950603030192400300b421020244c0c51500c0454518840802d0740300c40c00040ac0014403100798510400741d4280300119494030f003085104202204032901644440c103048601c1c1c900320006000340c141d01e1501c80d051002070740100d081e030844151401c031000583c0082001a0070941d14194003100c1c5e20861800000340004258440c0c000c11140d001001940d0302c0d15800402c910680038003410390b40c01000800750590505005540c01515032400054490310354004820a90242119440ca039001164030002d600d402c0c401c8290710f80c4903040c06050110418030510f101c1c4058000d04e0300c00110b5031580002d0040c402c80f500002000c0f030418070f0b81d80c401b180d41c0000b00c200c200c45100004551000c0841c292043d07104907540036030711450300790500d800060b41c0c160715440144000106901c42a40547c0c1c0d400810140016050b400242e031451403002d0107010444901044107110741c1e05041300318020a070826540c2d1812602c0060340341c3d4a142e1400c013 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 645807203 1250 645805953 645805969
    0x111070e09030a110a0201020a0201122007050114010e0a0f0e030d0516080f040825061a04020702060405060309030f0d1e0c20011806051012120c02 65
    0x1109000038108108622003601000520180c2584c0d00c0b00003000c40140c64040d0b484107030b99002405607001c2c111040141d80100022459021010b501143c00c103090340c3c403000240c5001d50600203000001c45c00301c0800c602801035402c0034140100d10400d45d0300d0407008800341000600b0900c40c1554901c10443d15916680081001e1a00c48045a580d03035000320041c0c0040c002150010994511607640840705485002e00714080c1c00031107034010305500c0c0c6d51034068956001d505503004521986454424051902d1402c502c8207015850000300c20195603100101a000159820301c5648100001401641c4400c180c409480c0280d40e080e44a58460480c01c3c40e5100742005d44c0c188850114503035400c00318541141d8001914246e0200c03515240c0400c0fa020f50301c61003072400c0802c4450f40c5101111442880d00c1120703426030000440c060b03201c00c176030800c0180f40010658846440b40100520b0b140c07480000c2008280900c0a075051100949510030080c165440380e00030401e980a4110544d50798450b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 645808453 1250 645807203 645807209
    0x1d07121a010f0507020d0b18120307181503050106080c091f02031b010209040c1d220903030212070203040b120403090302130903020d05460f02101505011107 69
    0x400101501c0c0a070600050301f54044608810b00070f2040d01c00c69100d2001b01e408240c3c2d042d5051405c2c1591034095041da040687c5854256070950107070750004070041628001e4280c40b032103031000640c80d41081c0004141110003040700c0c00ea40b00800071034502e62119161110300080b005207250301d03400c5011040742140304154101c1460407007450250301001040d402084001b9040703500300005540d07a401900c030100760918000d41d500d1400003502807802d080941b4014402000703500b00e415003141200c20100d070398400e015400698045482e4004071021545160448000e000641c1491700c2c120410140344500c1084403803000e10180030404040c000c2c9108030103503900500d01c80304412090407450081c48081c200703600610507403207802c400d507010b81c04403000c00c201c0700c2c1012050715080f100c0c0b0046e10084540407881541006001c2c85100503a8074014011780700d0751350060181ca004000034607180e803910000c0000c41ca800300c21980845050400e02c200c2d10203003400b204450121364440c0c10400c1c2a8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 645809703 1250 645808453 645808459
    0x1b030509160f150c0c21050d02030c0c150304080f090619031a060a1d090702011407030606080a050c1e1b120409090c1d07121a010f050702 61
    0x90049102005a00c60a0654484005603180140341d014103c1e85130341028070280c001d0f030032444117102c12009160a41c1e040480300740c0c014070136511580c5503403502c185000c4000060f000454011483c0304184040c4c50309100031241c0014a400c400248415884040d10042480c8030000b080c817464401c80c416a041c8400c0141f1041d1210540801d01450001c40d0412100092800c802e800304004103c505202181000d400d071424143c20340000d0300da844000580800c07000118108403090b681d2900c01c188079007060740c00410b0030748032444601d103520805400c0e2001d0500301942842140d90059419510004245022a441c3c0750800000c00070701c03605144e41c00040c1102045aa280311f030320003c0c007000c03040418850071808180715803616204e14245040074a401000200644a155003120150501400708042c1859031071400200e481c0101081c0c40a030b03c510810800c003140c125140480c10071076584180f00d0001201c6c0460b51050f00301c41c1240c140180d04545140141c81070742070b220300076405 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 645810953 1250 645809703 645809743
    0x705090d240c0f020c1002030d020408011506050304051515120c010909060b0f0904060f0f0306050f090a1b090f20070308040b0405031309050405010c02011b030509 72
    0x1044100300001c1c031100c20486041d0808582545551158080200941040d40601362120041c4c040100c06890300307480703c0443c44213120020401030203100401c0100b070150000101155013003032017008640705601910030702c6411300402c4003180d40407540c05491404002e44008560b02e181d080142210281015508140904051401c0701340001342e40d05101000d0f244e00580990741c00980041d101d49000f1440480341c14040b280d0030142000281244060041c804140140c4800d8481d010428581c05032200003c0160200244074407849034641066071020442054074000e5006503440d080c0c0303140109603100f14801c031654900e050042d80c02500e1030300341c00d1000503840001003001c0c140e0a41d0b18076902641a142812454444040f00c5805505448895440d42c460700d07101e90b81755000700161228002000504818000d200344d903000b610b001400003c090510381441400c40751444001415a817602d0f8401d000d0f5900300c1680187d40f10986000f28503a0f903119401818000ca1801001051000c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 645812203 1250 645810953 645810983
    0x201050d0c12140603070503031c02090a090e06070e010e0a0b07060e0709060824070809070302030102030a02040320031b0301090618031d0109030f08070c030c1404140705090d 77
    0x5900a442c0900422012948100d4548040540301d1040e8103d040104403000ac2412a00034160090404090020001c0303410940c3e5031501030988802e010a0000ca80204040000351f6820094820b0320980c02e2900c0d285081100b0003081d42041c85009042c00048046100c00400c241c0d034220113407210304441a100204d0b035550410001d0a100e0281c00e1a90140f5010310b10010b03040c07844500c5440c2c9803400a112030302c40c6142074820f88070181c0b04d004140100e60f008405620240011401203908400040c0c0c4c3d2803450401c091a02c15600080021428511781c50089a80026005516030000f080c002d05240c003000c00030340140030402c0c00800407410051640094000c400b49900c5c124000e841307004400e030300c280d40c01071042c02c2040c40d203002c203101704828804280b0f14070740d202c20207110b0f1811500d89207450301c03003c0c4942030a5104480101d8210b10174031505920409050b1803080981c1e00f84072101d50b801070b0720302d60400149080104100401c80890942d26420f60003407503030b042032180b498504 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 645813453 1250 645812203 645812231
    0x506210106080c031504020405100e0708070f030e070302041d06040f020301180506070c06090b0906070f021908030a0b1002010203061908100f111c0b0405040201050d0c12 75
    0x1c040c42500b845005400b46880b007420049407800f51641c05012041c070650f00c65080000512000d0700e14001e811003201c3c041144003511a1a900803503003600d03002e0603440c2a032002060820765444500402d401d0000140e105080000c0c4041925811140171440340c0c0601090510500340c070001d1203442c401c42050100f4080c03201d00000900e8000c0d0002c2c014a01c661090b2440b0661b018802010740c0d00c81400114810710038a0b1709000340344200c00c0401e0070001d50702e03a40740d150741c01d4802112540000050104950300403000a0403061380340054180c42c1c000301408031604400d104047e240c8140000019031242d560f0b408100e1404000f818900420140c4034001d000790030441e061405149143d000400d9003582c1c0502e00c1c101c85a2070000d00d405000315046002800d03c44140d442a20344441843c0c042d2481c7d100501192101c00e00b110a400c1900e4000d032040e1200303c51002d0250f841c01c0306120250740c0c8141160001c0780100b5010480e022040020ac5880e5501d81e240e8010b24a4180c0c1c2c14440c038 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 645814703 1250 645813453 645813461
    0xf0509030d120b010c08030c0304052d0708120901050d110c100b0906090403030e21070312110403143a030615030b03190f0b07110c0405062101 63
    0x240c0601c0c82004241d00080045d02c41c1004c25a0241403c203083c000200c0c5841c2e02c10045900038860303401c6d240c04449510402170301007001c00e28161001200e013420550348800f0010200105980401080380c44800402108140b00311040c150400c080050b003c00051a103410071030078405184201581c2d6500002550b44540b4140e1050791410f0405d180760714145428006240100c2000385080310f6074480d690180c0060035800d201c83c0480c001c0340f2000e0350300044444031b00131524448221540d41c000600e0002c10203105204650700852034210150201c201c401e0540341503944c41400b000314500414615850b100249100e46042e182d0041c88507141c00d04142100a00c50041c0d1107218440c011100c140d0a40e0141d01812180610408070f0b441c85074440e1308144100700024060700e07040002c6640406121441d4030082c1c40c1d03500040015010032103c00f0660398400c2c2d542c0381285c03201650128040d101d440c0800010311aa440788003050341942c03030f020000b82103890660365450b003200711400c55001e0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 645815953 1250 645814703 645814727
    0x130308060d21180801090309050603040f05060129070f08070201300605060705060c090607020a0b03040c080a08070b04060b060309070509063a02101805010912030f0509030d 76
    0x140f4041e0400981d2210500403d0010341c2d00d503c035040464205024444141c00c020b00c240d8119a0190311500416018009203000e8801400910000c039901c180114100700550039914565508106000104403c95103000b8101e5010b00d0066982005000403918600b1081141d40b0740401400e0407a6140d148400c00d001700402c0c60130038028290340340b08203c1c0f14001d501016226800940000300307040100402001e588800500040c04d19100d9004902034103076075080300c1000e41001050109001c040d00c0355100918000b001451030081568405120340130700711005220a100401140400c0304941000111020103044603850380303070840714a6500e8455106190140e1022404580309080484294102c000d54407104803090010400c05400342080c2c040c4180820200031030300c40180d40d00c6100d040304590640c0d8501c0301540a0004644110040e44142d0512800880411002030315100c0c81640ca40c0500300680c1003c0e40b00800e0314248514240c90f0360500501044000705c0d07800441030020 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 645817203 1250 645815953 645815987
    0x1e0a0f181e09060f1e050c040f330804020a090605210304030501141e01031a18061603110403020307030b07020703080d14130308060d21 60
    0x62210300c0c8405040303800841001c0d0301208540681c6142101a0300030503803441c451480003d204110b50f403110202c403030081039141c900c143d0110840762403409002c4c654001c12100345191034203107000c6038010290098824003105016800310307045c40b1640080440034403000c00d00c0240c0e04003e41d41000388840b074212001c07407060041010100c0d9540303e40c410b1505444029285018400c031034481681504c0400700d0304002440b08020100000e2802c1c060160788011400c6410300714103010481507104104000100221a40b1a004002180380c2c02c4c0c0380c40c00060101140603031900c96010702c940e080600301211015209039010322009040e000d000aa24a11903541040b05440300781b0f140010b07220320310004e90b069001240a001041d04410241c0e00044180110741d0030710360325500c5c0d0400341c010b520202c9040da40c41050303120740e011004070240d01c01c83c83c4582c01021b01195030b02500c510170181403a0301a505005603031080040f182e82e001e0061040c3c004502c1a1584a00c1c014050b0402d0344020745 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 645818453 1250 645817203 645817229
    0x50a02100509120c07180507023706092f010c0c06050f0d060305010f0b03060423150f010302240a080a0216030206090115030807021e0a0f 61
    0x98202400d00c0740394041c02908000c0c10000d81009100d110640081481c04481d001e100b03800174441c1d80d04e035014100b01c2904076011845e80b81a20004c0c4c140100200d5064500079000c51385621440c01c0d503e44244003480005810a01420b81040001420894001030080b00109900e075142c03800d1102c40c007400703c202c0390786c400d00d00340711401181e00300040c6c04002c001d40d00f498414098a80180090000e04819a000c0c604028803070b8900c00c04d4848640c8151503596413403124a01209040c0182d0215803015001841241001d81e10002803c044d218403080150007551202a650400e001004c070316916802443d880d030610f1102d06a0030002803004a2183c410a10300812003071409000004031140090a01d00780841a041070307502103001088040196401c1040c0074012100280000c0c48500076802007441d40b40c4071541c00c0c21990702c80d1032004c9207003401c0747c01c0002a0284003260400d503070503120140200d1078003038061860800010040d600c0707a5111000726840900408502c1202d1505600e00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 645819703 1250 645818453 645818473
    0xb04050a020c03030a050a09050a0803091c020309130f06140f04050402180601030b060706050f0105030105090c040f1d1c0503070504091d01020a020304050a050a0e2706010303050a02 80
    0x50102e00c00c100c03103a00d8581040c4000b1751800e52940c8000e5201074040c10108044609031342c0c50382825004202102d00c554080284200e64000b08200050440840d0002a29003050344010307559015122402e48110101c2c0602100f000080d00a4050030340c06013000d10100c2c2d120b035905000301c0c400c0e0351118010900042486110b141c2802494025a00600b4013030420740005840c15520000520880c141a141c0f9807403031068994000408105001d2000002e290621000c40c042c8030f80d040c3e000b83d00c680e041c030b1b0a010030a0300200f42c0b600000d80c01c80300040c040e9140e0500e040070700708a21070807480c4203001000c01a09100031851601112074421050b540e40820002a6241d0106684460000c0c906000500c1f4820387c2d0347c45840b40c1c940c16003101c00d41500e0340c0c40c1c2a082e644054440c00041c0c102040400140c2804800d400c00f9107011a80c00740d40f1401e1412000424000401d81030801080301500070700111400e482400c40d25081d801d5481c0ca40c0c4a08002d0300b00d9208800038001407049038015 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 645820953 1250 645819703 645819721
    0x14030403031803121103160f0201110a02062d0409020a0207091503080c10050a02091806090411121203150d0c06050d0e070e0601021c020c010c0f02040f0b0405 70
    0x106065a60080d045032050b004050119042102441719201070721003000300800395048440d2400e0014442c00c2e407008043c41b1071000401019071401381030215400304072044010781d03804086c1c0d854081c40c0054086103030380503444103840e540700321920a0001400500499142c0d06a0000e00041c0310a400710b0300d0790f0341c0d00e22025089035004005145a100e0101b4188000340c0982d009005404400b0211403142a80149000460300d081d42d0750b901055000582c90001d040c43d5840407a90241e5101c6061a8500600030882900004200a0480d9501d0804010990310316408011554040302140c00340102c98810380740a0340b0a503084411030b9900482c040361854003605407503800364444005c0c13022900d04081500c150b0058070424049649907480d00603851400c0000c07000414811011112900341880003a0502080d10f40032002c240210b219038204580014001541e40d00078a44010b1042050030a603501da8140000258014140141802f44440316081407045004c225003c0201c0c3e00d5029074 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 645822203 1250 645820953 645820997
    0x1101061e090c111207020f490b070c080a02010e011a0d0605220605160305090d0807050415020d0305010f0f090504140106170c030c0d020d0507031403040303 69
    0x10340e960f294400c0b0040c040d09403003040035011091002d0001000181d0351000590300003841c200304005003a0f00d8100300800d4002000c8821720810300321600d4404061080a095681c00485014003401190b0011403c180e115155a84515401604407a200c0b490410003e02038002254100b12940c2800a1400a48107414444210001c000d01104a8644d030340e85520181000802c00e0b00f29209840404194000400c07104244a03c40c141c0041d880c50029002c1139180076404d1004209481d00d420020650b0300040c00341075050850a041c04079a030745c628101ca40c0d125070b8205440d480c0e0030104071000160002281c4c11440907a0320140150b81c0c0300c8440c1040c0e03910307520840d1000c04070610104025015648120f401a005401c45c04000f002103030454295051503207c0d403200400015403400411090003403151092044000e0040c000e28200064031820350400e02030b114014801031401040000c00407000110341c0550801d051314460400c25490350010f200560206410004525191040c540 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 645823453 1250 645822203 645822227
    0x1207020705010527040507020c01020613030509060f0403020409060c1d0a17010608030c160902121b09030f1f050405060c07031403010f060e09040507061101061e090c 73
    0x14825007406050061600400c0c0c0d403000c0d82c91000300c103004e0300020752100e000d4184145029001001c031000c1181c00240b402d030000307009401a004001e50800040d902c08112284103004817116500d5a80c00401e500700e038070560f403000394010f2078802024108152a0840c2910300c06503141c0400b405801da40314002c1c0000045017035404840328000748250035151941c213202d10801000011312035101d241103803460340440c5070740580e98001e41c058248481c0d10b07072405001d002c0448007541042402d8074060411a8054400b0715030341903104031011010801000d499880e64010308036003590898261083d16030862450765809210711513248082d40705240102070080d40c2c02801402ea594814071800b4841e000329204908200001a10300c03190910300740034501030007240036002000761902d50003520103541c80030f4950207013606808200c00b180000c105d50046400c40c2c204240c040356905031450041c03196800410b0b40100e00e0142c8103141000035641015a19440410000644c3c000416603124030800 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 645824703 1250 645823453 645823457
    0x32e0f060908370c0504060e270a0804081507021b0d082709154e16150e04020c030a080103050c040b1e040908031513020306010e0f13060308120702070501 68
    0x150650952014603e03503e006402c0041d501d6a004ad59a000c2069126a0010501e548070310b1805041c1035258044541003240c5000401c0d070440800404c284a071803240010780303e140c001c400710041c000c0c801c084030300381c15510703840190096040049041c2501481c400f28003440c1c4140014202c00314010391003460041c011f00c50302c2030092200110041c3d500401c0c4a0310174001e02c0001c80c0465245901e2102404900110108141381c0d1059951802654990003c0c4942c40d0110402020b4155200310040e40301519262200c041480007003006441040401065888001104a82d0a601c400c506040c1da118509656004d20260100000c0d591850005035001482140205500104c1500d0000340e0801500c0411240b12548030341030290012501d41d40c15a030b80c104901d10f6890320300f0091403182c140da0400c41c107500385200004c24410040840f80d0003454040d0464515640711041208480c179240000d001254030303884c0c40140c54002907500f204801c5824041504070b0b0011600b141943c6040e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 645825953 1250 645824703 645824731
    0x70b040f050d051005040b0103050c031212090106030503040f090b040204050a150c0812090f160902090301020c1b0a080120032e0f060908370c0504060e 67
    0x60100040c2c500d0180c0121410700c19150b10500c0042e142c0601ca120707a002c1c2000801c40e61560408906000e0309802e128802e0300400c0040c6048403446050b90003c003a07904410b1002c0d03484a00e01c6005109580010b019403101150000c1c11b5140c1050f00c000341d460b0841e09104200b03500c018002a4000d0340101584101e21040500510140c0111b044d050302151a101e02d4844241d1118400c0340d004000c860b80d80c1e808541044090803040001946c645043d00081010385500d441504500003940651400140c000940c44910740d000d4040d1068030081030706843c4000700045070652039079205a9101d0103503031b4000000441c0720040c420b40000b00315800d00c090880c03909404141c42c0c1d034030040c00d802041da0010f80120303501c0305490100154450700c9440a00c0e4500303002c0b54204e400400d90125041100f40d0310140b0426001051000380103940e80250000a40d5130008045140340c641c03445454541900314860501c2104c01da40f0080707500a503420051652036a003903d1181400304c0d0102651441 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 645827203 1250 645825953 645825959
    0x8032a040b070c17010b10020a0506150f04020c1e12030114010c12030507030b0307031e0501090503120106090e2a090303040801021c0b01022e02030711070b040f 71
    0x2000004103890b030301c14641c26280307585070b503075600c2c1c05040c0401202d940c4c0e65580e658403003801c120b15205400060350006064a184a1340c0721555004020510705401c04038070f20341c041c1078856441c5031491900003041552105a042030099a5122811110001001581e1404211480403401c1c0e503007042400002e0703140d41c1c01c2a45d6103442c0031001020301e0402c135071080c0f5580481d4409907032071180010b965020415007403884005040c0d800e040e003107074441d801c040e600308002121540314081196203a0382644a802050038058018810000040c02c01d00000800807c4400e10010890680b400d50322006241d503100d01200ca0000350441d00c04c1e52410b81d42e1203000000b1301c400b842c101e20b45440c0584a14180580003c42c0c11a00f00da80071880b145e401041c0d800725040c2c0300400c48a10118070108000c00088000003d640329407986180f59582030320001d250506601e41e00c0c2c0340380c0e007a655a0a645c0d07404d00c0d28000348202200700c60074219020703140c404144001114200c4040f1040b8400c0300b0f0003541 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 645828453 1250 645827203 645827219
    0x1060e0321160605060a09110a20070806010e13030e010e130c0f0e090411060711040501030f0209090c10050a1b08040503060a0608031b160308032a04 66
    0x1c0d10000c07240000005121503003100b01c159445101c80780c442c9001240c10300f001c00622020001c141c100c01902407c01c40c0084900007600b06070f6580c1c440c07503e01003020058009a0601200c250325595680c0e000314000400c07100d00010380700741290080403a0305003c0e60707980c070782c00102d10302c0c0d01008001039600c1c1030f51085984140d215060940e00249100c02d101c1380c00b8840000c481c1d4881180010810840c0000059500040c112031264001d46807291241f400384d64052100e500081120702c40c00d0040340b010f00703021000300d803210011001351040180756100d0916000703040095004034071034804107001865036240412903c1c544400a0140510040da010342561550401e00020b0704000200c0c48040301074030840e45004c0c0d098015460103035144d0804050604084d401002070028a051803000c100600e030000403685a140d02d00040081401880f01050504540900404000c0401c040110511920f00001c5020701e020700d501030782c86030705128141f12400d2645601d0b0904641480100300c807078 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 645829703 1250 645828453 645828493
    0x301030b01060f0509100e220b0307080703020913081201031202190b0c0c071202100801060801121112011407030c1e14070c1805131203060810021201060e03 69
    0x204141031840700d0002e4803010601807030200c1e0340c8c00c078000b880c0454075002c911103114160222009070003030304a981c1050f102540c1c0c1c880c240303c0240a00c070500002a002c1081d282c420200301c2e4081d0251356200b07003c01510000c210280019106c4180c60b21051805500010304142c1403005803080072142c03100c0391518005e040c030060040c900c1030010000303144082018480304c409003140c040e40d5800280507005000442c3c0d1225601024440d8220060107000c2d0002402411103038041d0030040d54070b149182c00041d48c0a0070303030780503045034418500190014042d0054800e00b01141d01c9119190b13140f501c110240c641040031701c400302d120881d0090202c00c40c800d03620019504c0381000700d800d64511107000416400f8900c1600c401034560814824074542c8141200000c0c2403481c140407d041920210040401d000c100800106410754100382003406a006000144007000580d0040018151010302075402042608004913079900003007481c0d0700508081301c01032406401070600300d0443d40d0300d080b09 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 645830953 1250 645829703 645829729
    0x230f030a02370312032f120c120c030c070213060e1303090b180415051e041506140a0c02090c0a080f0106050f0a170406020301030b01060f0509 63
    0x1c8208a41c403804201100342055040d0180c2c1002500325407031820407a0520000411070002c242c10894031042c14050300310350001c15507040e603402140355050f0044200130b1003003101f28180d0700d00800420800e074868602034484454090780305402035440001c40c08607840308507013015201d8010b0000d5005030505c1c1200c0c0075030000d11600040d000b61112655244a0350803205030200707140c0c940c5048100342c0c0c059000300040c400b00d41c100e41020040c1d82502100065075241718000c2d075480660480e180303c1e00740c501c4000e00c2c0241c80e00440c05a00302c0b0f040e0040103840ca031a400346080c20440003803158003614103402c80e030b0280c0d1402050021142c2c07103a9141d002101c50340c1008090070092015a0740c1340111405100040952740e540d1007510310180c0f041da00106520054603648004000300364000c001c0f03031016005144026540c01c200308084c1c44100707007000a900c8000b940402c10040151603030085046e640500e0507800b417030380e99550031607050500090b4440052000e00200c4c08600300034070002d0300 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 645832203 1250 645830953 645830989
    0x60a03051213080106030b01050117010509040201141e03090f160b03060a0b0a1206060807141c050406021206060f0f160b090a060e070501091502010603050304230f030a02 75
    0x140c03c0d07451101c0b5080d15120f030000d4441850b0340004014175038100a108a5040e440e0351001d20030340c0b40c000010700041000304041d0600c1811451018240f516000710b85c50156100c90b0640702c18407000d203040064004540c01f182521501504098854000440d030704401103140005e03d44070304000000300c05410182c0400c1e00b01003001008660248c032000030f440c100c4002d594443d659803030080c1010588405503c000203100c600001e1001c3c00d6800503136034404402c107100e0507036035010182c0502d8429112410080159103003000344070420035607400510815555034414000ca407103190410110f8450f03000888510a020000080380340803010180a08a42c41c049120050046807a44801c0e04003c49182c03d881d0007146a43c400c00c00c252080a900d2081c4500030850ba50418001800e0750301140500c414801760000c207054814030035048800038690000c1070b00d440c0c5a550001c0c285248402559400e240c1413100d03600c1d080c1c00e0182a40301700b124020001c00000b1159000d01c690380d8821084050 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 645833453 1250 645832203 645832237
    0x1062301030e0303010b13050603010b03150f031e0d090e0117011103040605091b0303070f02040908040303050a080705090d06091b1401030f090308011505091314060a030512 76
    0x2401407004d18003c2001c00c20380e80c0d8480c0464100d41180e0358580020780700d9a414401400590b0004040e2680190020b0585a01402000000c0c1c056100e001c2d00320707410701c1001d0600070968018014882c00c00304820882d1100703040c00d6010342e5030384a07038050416130022401c01004881c08010785481ca1501307402c00020780d080d40040c14456988102e4055426507200c000f8440c029600b044090b070740801c00840b4090f0100c00c03800203900d038440c855000c1d14200700d0140841c155900c6500425441e940300320b40c9583c0700da03645005401d603000001c0d500041001d031400a00ca46010740115860004000c0850750780840c0e96841c0c2d40102a0300d8826034004003034131415090b42481403a00c17005800040300c2e03501000301d03000005054640b01c02c00300d04001d04080000740020f4100109a042d11500d54a4188468080f48125a540200d407103440d84007050a030341040c2810389600415a6046c811419012039660101344030b02c461062100070040c0c1d1180ba044080a03180402522111042c044420 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 645834703 1250 645833453 645833471
    0x40e06010f1413051206010f0611030408030409090b2203080a02120a0b0a061b0b13150209040c020f06010e0a0b0409060e1e0d1d1207030506090106230103 68
    0x100068000e0f0000c2091031454660910080c40c08840b107524211001c2d006040c01d60400381021141c90300d40c8501001d1025600001030700d10000e000740c50103841c02d40122a182d40e41d40d0200380203410714603019100b004000001c83c03103000d220045542100d400380d402c000c04442544d000c680030080101441c20b0b01d80d00703000482c202d03183d10b0105800344141c0440441c41014500c00c001c05882d20341d000c2c10502c046060803150031407001e50300c4180d03a0b410204000b19546d850120001204800780014489550745d190f0342681c4010354040c103000c0070b0540d010820b04240e0101079030349035101f41d203884290740540010000070b44840c400b60390011450002050f810100030101e0141d5268240480e00346464400d00c0003c0c00c010400f58540b54460080b040c050001025829102c03018400c0010801c108031082c040c01400c80c8210810401003d03142000807038440e0109a02c1d00c50900086505020b0680400c1404605000b000c040d41c50346190041c0450342130381450001c0d0b504403101810301d510340e140c3c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 645835953 1250 645834703 645834737
    0xb011d010519050d0c080f0102090f040c110a0602250201171f0e0108100603030f030203090c1201020307080c030c040608090705100504180c0906030f060b0c0a0302060c040e06010f 79
    0x104101e17110310f41c41c034441400c00c1350444c240500070310454041e170301c10f104440c0c031540c580e401007041c0207080c1c0340040d480101900c2228900d89842451915226840000e010000140d005100c1c4028412804d41d1562209421040301e84091b0b80c003a0001c0c1c886681c0d03a1482d0355081140360011203808806010b001c0f07501012035001410741c032565810581000411000d201400072503078545c1480340422120b0704633603002d40805030f002d0300102015400f200003508403c003040741e00100030b001001840410003280009001c0d41c01211050005298280401d2008958071300303076400358a1011070603040500740311081740c0c00713500288008000c0c4954a00050300c2d440710003a04000803420780d500340d81c80e0305044410300000000c3e10200341682c9880074040030180e2013050386064802c0d92901040900081c038901014000d203030001a240a000145c13003501060028600c1c003102d00c01d4080d01c045503510141c420f068025032140126107159400010b1056204130710035440401642001d03c003a565031091 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 645837203 1250 645835953 645835969
    0xa15080624090702060705030a111318090201230409050f0f0906060a1401111209040b04020301030f0204020c100c170a020c1e070816030b011d01051905 67
    0x284450810680705036200c041541c1d518281c04000d0311000542e0405400003951401c004101c0303010000040b004c100c81c440c103508401103a12484c2000350315091106515101d40e44140720300f255114081617400c0345445e440c0101c0243d2501612203070506000061032900300400200310b00700c2a0000c00000c941c405180c4a080e00403080000700c0d00c41440c04c00008c10006001401145460f4419030801159540742203004003510b90445000781c0f11100c81c001a00c035100c050044020034007412046c0000c40c003008000d8603940200702c605215901064090104074402030201414002040c0b10050150030700340c0040c4082a40c0300f00303c07a050442c0d81051000c86000103004400505411607a00071f4441483c00c00e07400c0188a013085261041070300d00c1c00d9440540361029841701c02d5482c942e101e050303018041c4030001e00820741901c442000078031903580c2907200b90000301e841c0c109610022030f14030200c4460800031503101c9280581c1381d0074641080f00d0040403140c540798a65120a01084a44803c50 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 645838453 1250 645837203 645837211
    0x18050603040f11060c0a111807020f0d0c050307020409050307020603150301290f13090b1902040b071509060905010903080c1305060f0403060c050406021902090a150806 74
    0x140b65030039a0740303150685051140803040e42c400c480902c0190071041d40440c80d024442d0f40146c0203038105c10804041074070810880802a004100102004022600801c803500a10014015140c0c000c54043c01592200c9000201601d80c0d032060005000500301a444600800c2c0105c08507818104242d001407211b42c0b00b143d50441280340714000c9401c60509000e11244000207200314401e40051101e040c2008104000040c4602101d402144070350b16014603d80620080390b405005084a500b04907151960175219211014449140c0c040340400d02d10035101901e9032551140e2400d6816210180265404040d030048039981c1d4134400c000810038400d0741c14040c172410010414680c1c80c140a0700307000d4010817116181c3c404100c000d000b40070b41d80d035840c00d88008440f5641c0301c0302050400780d05401907820050a85147c5421a45a103802001a0040ba0740a5089662902507800d00c14400300080f4402504003400002041540880d6009400034102c0c07918092a11561680014a807403001e507 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 645839703 1250 645838453 645838463
    0x30222080a0c0e0606120411040203150a0b0a0f051c090f060b0a0509010506070f0b011d0a06030c050f06130906052701050108040302150c03070f0813031805060304 72
    0x60070040030007003003000c0c0307800400c8038400603a014985070000c5400c03841822066000c440d006800201007202d02096091401c2010340119282d10b0003000c1d036404a008010800c0c030490710003400082c40081001107420510181c0e031450359941c5036500944160308041403620700c40c810071050317601040c07075440f03403126060040007400b500220605103441112441c040c401c2c080d8030701c4c01f030503c40d80d1182c02829045850a803401a5a0f1509040000030b03156003141c01401c6a10580000506806c01c40c910a0400051804032009403607038400306d800c42d40a80b02c020000410020100110b103042c0e031004c030b0071103130141045113087e0b40d9100c44103103458250800d00405560f0308091016041019600200d814065500d001c01c0d8010702051280843c14030a090402c41008005800c042c0309002c035166480341801d05400c503052941030105a07030811285000000c1d502e42c080d640280c440d004c150302802c04108404009542900d0407544035508000221b03c040d20074000180b1b94130b4210055128038020 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 645840953 1250 645839703 645839713
    0x80706050406060b07020a170a0f11010f0206090a0f02130e060f0105030a0507030837030b04020a0c170c0f0f0c0306060a0b0702190b0702010e031204030303022208 72
    0xd8640001101c40b150031400628000380401700050700ea040001c800d440c180e1000c244140d0981c41030728070304000b45400030f000c01030b203651000800008259100002009803680d00c0c0001440c00c040f6607480003120310a019038025049100440e43d0541150003c0740040e1443c41c12000071210401903c0003107600100ea40d020004004940200b0705000b40034140031006051441c4c1180c035542c0c1d6a00c00d40c04080c00340800010500040300e49020586800c0000e0134000c000a070036a00707d903081c042c441c84181d001c01d061400d08010b519091007281c0348084140c441c0e0404045033740720701800c00107004e15800f060400b00143d150040c0d007005040fa2070000200200201040400c070741e420440c400e030b0024025030080c0144001356482c00090402d817569655502e4841246000007070340c043e40061f01501c034401d00709000c952038180c80000c0480718001c2e2641c90401d5948800d040d554410b00703004c41210760702840280000380c0700e50028640150440322000700c101c07590010300b490140036800505180d0103 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 645842203 1250 645840953 645840961
    0x6020705281b050d060203060d0c1d0a02070f1401112709091f090c0e010e0f06090c07080d060f0609080c03030901200d08100b21060d08070605 63
    0x500b0701ca00c00144603a05480380e8041c5800b01081d500e10224034000d003100d401000182503034a803203100f1078100d500503e8080865a03102290300751041a880038410700c604100c0004c80301405802142c3c980c030790000008400c0c81c029100d00c00c41604000d200c0c0c115540300c84c80c07420100040000740000d01d0701c8910b02c0e071080607081d0340d00d00580c0f0851501070040398002d0030098010400305130711076a40742601349055558178801c1c03007000a00700054020826509460007040162100d80214140d464402c000a495114061080241c074012104c2c5540090300b5000204e880d03000401a21a03107101e8204035081c5880944894260f0740180c01c507650303070f481650040140d654815121001000400003400d00e4610701c5010a84900c9814404c60510194040c404080c014445020303404540c2081a1582c505501c18002e101c018107880c0c111407190700c040302041442600b01241c1d030700010030450b00300441d1043c4019900600c02000c041e400780b44403940c0004950030000805030036204450020303141c03030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 645843453 1250 645842203 645842213
    0x103080406122304021c05010507080108012d090c1203080610020c0123130801061401020606040e0a0206040303050a03050a0c170405010b0d111302160602070528 71
    0x141201482d0700d60704251403043c036403d01450901e0800190b01000352541e0b11800400c07401100c62a51441c1d201760764414106008041d4449401041140c0e903458259980d0140c203800c0c1c03543d05e801c5d60701c40007500300101607020180703800d42a1441e1008010035040200c0e00d41c103405030a2644104403181c05c03407a0313140c00c01d64130050040d030010089074135081410350700100a41e501c40e90030070b80c1d050005509028545030841d01c16130000c00d6444aa0559944645c00c418416000900c200005903003008804240040314801402c3d02d040c0c1a402800107a03142e40420001e0640401e0040c418018060428003507101c500c010400b540c020b4581d203a0b2040700c00c0d002002c89000a0050b10414900400340e1100c680c4000341141e104a2601d60008030f071030b58144140180030034281554000c0a482d0740c40c041102e80d030041c45004000320b800000110311451200700703030720030310152942042c91200000002051303035018014640c015001c031185518503042c2c803d20703a0b90661070115801240c0700c0e0482040 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 645844703 1250 645843453 645843467
    0x80a0302061f030f17090a03030e010f03061406030c0903030a050307080f1605030405072c0c0c1c0306180e0c030f030901230d02030117060c04030204050a090b0103080406 75
    0x44100440050344500e55166135031030b1803020314020400c800c040207030300f504400701c010b81d0b1007698003c2099401a64902d009400304040c0403682d0f020031303d0821400306d42e9010303200b20713000c1b5040381034100c42c180344d940104145580700030002003101c00c0c1031010348002e480800242082c01829180c05969082045000d40440340003040138818264010400c218800c40381c3d90901c002c001c1d410215140c1e00d40d854011700f0a00340f0f8001001d13086281310500610070f0f0032411016a5105440c0003640740d10785240b000004d10401110480c1a40441503c05140d2071154247c45a0003162400083e03184d104c1201d64082c100c800c0042985984076055500c10500900106000b000214014418550090300554480c080c010066041c012070b40c00210303141a24600030342c2c10441e148080d40da2840c0f140c0394038000350404c0c05103000304122440c0c0555000000a4450f008040a0140c41c0c01c091441e42080060030b0000d0001018603100c2912000141000340700034040d40c85040000d0703c450900900510803 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 645845953 1250 645844703 645844741
    0x70c030606080f0a05150402010e03010e0309190f1a040b0d05190c0e0f030102040e1305160b07060c030b040f1b03060e01030f0515090d03050f010b031f080a030206 72
    0x90700f1502c84c0f0b0380011400075403401b001d42c8560340c8180c1e0780e4803800140e0f800c184510b200c2d505035003000384071940080040020092200200c603802d40141880a02c1032083c05640503030841d0012941c0c0c11302604849030344104160800c2c04c0624640b580b182c049003c590480815121001c1d00d03001448492900503668084140c151502004070f482d030703060018400d954071500540034001c06040425503880c03e40454002c0d000d4944480f44030b007814950f82480f901160f40507525801009811034111801c1030402044907003240d10203040400c5a15030a0003064100212018517a4561540750039458a0007450360030101d409002482d50412650101c041d0031240c1c0f160308040c5030034418001415400d41c81b50640c0d401c0b40e122042c0a00a192003498220590030344105084c0e10810020084030008200303003440e005540038000c0d44c680001407640300c00c080c00340c071110880c01c2c03000607a49654410504150220248141c5402d51f5482c03500b070400c0e2400c10280c0c010781000d000c000b90703c0105214a041 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 645847203 1250 645845953 645845983
    0x204022104020906090415050901063602040503060a0203130b091606020c01020d14090414011a0403030f03020304030212030106050a030e03071109040f0804091a040b0603070c030203070c03060608 86
    0x40e10307040d6030750000e288141c421509203680d0758010440c5100254400c6016000100207401d8040b01c104000111124131332290390f50060039102070703805001380e0098a04136003003d001880381e074490914036006508000c00d42003800d1003401c00130000c41c0c0e00d00340903406071602c034000c1c20b100241d070514040359002581044040d5030200040d00b5072030741d000403506020009840c0150040c2c04040c903d102c544101460180d02c00d043c4a0200300014180822504903030348846001c2c0b542e01000300d2001076014074400907000c034922075402d4281030b0081e0011a4000e1003841580c1c020011148054007641081e00280c0c0010702c0850380094058151044200520110004504001559840c0e01c0040340354040e080c0607401e0f0074041001c100c415049034081c01c0d40072080a0300c0d6511071060900414004c45c0300802c030306030460034400358181481013082c64480504402c0c40c2d0703501d50340c3c151525648030380120214030082007200b02050402004101451240030b010a803985465221490035000101c8408 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 645848453 1250 645847203 645847219
    0x403030b0a0608090d0816260109020c0d0207030218061903030315090624050f041e090b0f0f0607051507090f0f060f030905030c0a0b010b07080301120204022104020906 74
    0x1d41032800742c80c116002d80709181621100c07008005003908c1c40006c1c4003444a001c1c0170710005c121502c0c09d401410a011205d070407109004e141681c01c0340c1e690b1403844082d40160300b082e400d18248800074a00b43c0d10031805480c8612900c180340c85094001c440d40e02c1600066510b8000108051601480c40028002c0304030500803282403241124518141c074083c004401100551101e5084c050810340704494001c504c031a445a9691051510a034203031a103c0c86142c146a2000c40e00044134031503402211070103000381d10303400e0710315040c0221040b144894030303400320062140000203441002040c1c4502c07082900318600341003d8801801828041c0c1180800b854102e0050207042090950070003280d103145009200a40e04000c198010301c48100040c1c85400b0024038034800c10000503052912a2040d82001c101ea03903038806198182c02900c07002403c5005c10401000f5075102814200951800240700528040f00640f0440e095001d103010b240300c00806034100070640c904074903030341c0d0701010503030b1402 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 645849703 1250 645848453 645848461
    0x91b0303051c0e3307021e0c0307030c1502150415060e24030c031b03010f02030f0114040c0509120a05030c0f0c0a1d0403030b0a0608090d08 62
    0x545140507400c01d000700c5040c2c4001c40d64161040340c002c420b40c1400700098035960400e4940c50440d21590850314910711040d0710701110300704680d141d0369114907001c1c1e003d0300e01940310100090380c3c0c051082580744540710750110003040f5038042c01050f0045200c0e603207201000b403a164000c03e00407804824001950043e05007000480d02d840741d2700c4c0e405075115860510740030344800420028140b41e0007101002c4690030401c05407941c000084080d0b0766034a91140f090103048410543c2d0f074001d5054850309500b100a001c08441110381291018140050001c03030103100c2c7c001307880103d80044602580d1113541400400c0006145080003108002c1030318144901c8081140c0544035210f02042d4034010000b80380c000002e0320b0240000c0e07506035840030590350341c0e072915049240d0ba100310102d8030305d95010717200540f1660300c2e00c13500310710894074a80046003c01e040d5206052403002d004106606140d01c8409803030090390380e503054401400700760b2035040c00750070f004c2402441c20300411241d80502001d40b00344 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 645850953 1250 645849703 645849707
    0x2b030e0604080d2102070812060f061603030e0a06140a110301030b0c070b15040b01110a080307050706180c05220b04140411030d300b03030a0201091b0303 68
    0x6102101541d003400c0c58008060b0740e4404c010f0000c160b5040d8111310216601c030400c0200c000500ba04141e038601e002a0b9100d441c104944040d5004507183d11107800c000d190f58403d444085101d003203020f400d0001d04070070041d810300d040405042084038001da031402c910101c0b0b01e01c10381c46070304140200c0d0200f04601544006030094403043c0405807455003c000020821031181d070887e1800e5500004991050505580d00210300c410030040c40d20580c10201d05800b00d511a000d00003071000c07683e0091074400b481e6242e14009610152000003006030401540003c90300380c0c02540c415006940402100c1a218140905c0140058001d144103101d02c1c00f030600074400c1c40381d6890160540b00400103500d80c0100000300101081605241c690804100700b02c01d000710240031035412030301030b0140d403d0306030381510032074030030007a090340c0749041d0044941900d00400d510002c904d400c0c41624001148080340000a2458100c00300c02c50041c1c1d15644090104008034901d448d41e000d1440c40c014900e81140d0300 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 645852203 1250 645850953 645850963
    0x1212010308161a0907080d022a0d08030709090203060d060b01120609060812030402010912150e0606040c110c04151212031404202b030e060408 63
    0x80c06900000c2652050001c54000c08841c1a43c043e092a5458182035110015800c085840d0b0b12035000b55580003d00e840086110780030501258054021510546005410307044c1d400d40442416841000010041c2c5861030300d610494003a150982d220326180d80300400e00303040d40d00600203044c014010b101c042d440f02c0b921a001c0980c400b0f03000c9000e106143c0100d032482014102c0c1520281424000544044503a002c9004d4403505401c0d0303074100301a0350028041d44003e07100203000600e80007007001404030520341072810030b1082241e801c130b07615450a5503041c0c03860710401e202c042d003140c03091109900d020301c150310130540c46040059012441850ba140c441418101d0719020300d0315100c0403468403c00380c3e80040030b00003d084a80031680c0c107007440c01d010b650380602140400d280c5107a44903501c0403120140d00c41c07036000c0300c103114110000075440d1140141a07107060b0803500400d241c1d4554007401d26408000340740b81589004640081c24003c1060501c406c0079406150100300612201c140850 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 645853453 1250 645852203 645852209
    0x709140105032a0c07050603011214010b0312030115080c04170a020d08030f13200d060c08090c041104090506030a060e06071205070f120e010518121201 67
    0x1c09503125580c42402c0200030b48050740842148030410303000b8208079514806000c0a040b03000840d2042c0d9111382c14082e003840b0a02031914441510b0903d000050759052026048419403400410103172068008240ba00f00840181c06044501000500202d42d140030b5031100c100040c60044598141308074591000c0c42180607121401403020800c40a00004220740fa0b401076000d001480103021a04000c01c15030410b60701c04103818915030200d81400d454841019410b0740281c000340707002100c030742c0b00c1d842001003c1c1c0e29604a40390500714404902c240c8501d00845905850f0300083d441d1016001e13007490070400e142441549810208c82c0b41203107160a9a042e01c4007402c00160544840f400039103404d00708003000b4412410014540d14101010803a44e010311381d5503c40e07036210035005440034282c82040303030072400141c42c4d43c0b0000b000520824168420902100d03000901315240484030382540e50807140c60040c001c03017001e1050000c3c0100a009080010100d40c00c0c20000c2d407600f03c040202c011304c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 645854703 1250 645853453 645853457
    0x140306060d11010c020307120b060105040303170703060b0309160503030c0a0210050903100606020c011e03090309181406060310060f120623100c0623130b07091401 72
    0x1403141c0940f6401180845042c94004040384c0909544a48402d1000c110f8a0103d070860101e4010504a50040d0107a0381560703815291010354101250034030258000042a182c10140c40b000d000605003040d5004602548800f0f002e4407611034068040d501c0722120340d000034044c0d84200b204c04030110001c507448031082e904880005d5100b0442070111b4840c0506003510b0340c54001c9502e948494001c5030b02000442d0420307005c0e00c00e840c00000055941a4105501800810700300e420040074510942c802c03514103102c0d04140389203035240d0f80448040c41c9001d40091040340e40700d000305550b1030400441c3e513000f0801c17250309182d4078081404006489131303441200244104114079003407a40c000e00c06a04c08800c11305042000745e5652071501319a2038605044103141c407452266a1485c100702030301900d1a1840e445180044100e50782da0b50040030700c0c01c520358201c0300d500c200c6640d44658030304903800780041406082c0c1101050034409030155010b0061420b024840e2400c0221030b50400580002803424 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 645855953 1250 645854703 645854723
    0x80606010504090e030d1d1c0c12110d030f0f06030515090a08070f030e18060609041d0a17070201081303030b030f06010f0b1e1c0203040804140306060d 67
    0x490381300c0c4c1c91801149102c12045040000250340503400000000781c014511049568400b02600d501c454001294500400610180b81d098082166010041c1c0c1d880100d00e007600500704034032403007401c1425000a280010361103c4000a2003015070081c000325054440c01000381c14555030300e0b83d546801c842803015068150b03000195072503034144031603445990001041a501c400700c0c90844440c507001c0400320302003000450a043c1c107080180000070010004100c1c5185511090200200c40d0802c0005560290300d400d40b008001c5442c0c2620700074101c940000304500406881c085070f039620f14442c0d10f0621001070140300d0150782d01240c100d0308203451144105121403235003412400303000c03440525074143c441c051001004403400502541220800c0254070102a01e03101c0c600200e106d1040e52030b584903102035110020f2500300707000304400b400304901803080080c4550201d007681c100700d07020365500001150130401c0f080d002200c605080c030201c02422061401000080940147d41b9019001c1000c1e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 645857203 1250 645855953 645855971
    0xc06041202150412061d0d200f0c0102010615080402060a110a0b0f06030a050a020f01050c0708030a0e01030207031b020f220b03010b06070605071701060c05060108060601050409 78
    0x780c2030b0005070540034410a1682c03151111004405540f142004035805443c1c10030701c0b4040b0403003018180c210302c0b806026205030a01c0d003404440c0709503000d4455440321400a00c0e0280c404003000240010340302d1002420100300504000f80c211751040d403204c091054420b0300050305d5640a24404d6109504681703903a101e1041034003c85200300c003c419910240319800c040c505115881794a244103400c1d01090609554506041c180c4032524a1b5004150303900c02003031a4010301d00348024425541040c074003a400c1c803012030f280310310b40911980507031465040051900354055000b42114280c3c2400c0c2401d502d411b070b059900805e00c2c1541445c0110007148008114115916032041c84140c50008140c843c401402d80c52941103480c40c0d9256440c254075100e074503075407402c042c06403454200c00213002c00e0030070003181c4424000e003000a16907810091048018030310f00d0b0588588078060501503884d10011422450a80c2c0f900806070000328455006400f08800d0303a03444400c8038243d80020b8408288280 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 645858453 1250 645857203 645857209
    0x307050d0b0a03050102072d02060c0109050106060822080a03180803090714030111030c03090f0a080405040e0601151404050904060516050c0a0b04021801180b030c06041202 76
    0x2580d540c0b41d00c000c0e0181c00100b07010054000c0e0000d2030107032183c0c25604000c01c1c03481d083e015001e43c80c40c0109403c580075078003510b404005410f421649400100c0da090056a4441c02c603030300350300840045401c500034842ca04203000182c62641020142007500c2e54402c6c2c5580040340141c0d0b102a01309900d50040000c40c034014000010100d0f440f120050b1203051240b52191a88901d0290300c807000001ca40a0074503260500403d134111000000040c40c5032226040080e07103600003000d41407548911000c40c00d0048040111072840b42c000e000d42c6488904001c20403041d00c20700503502c0d5046d800310005204400446100e06d18000c1c0d0382c14a042c20181c920071740c0a46e4000c55000342e60206041c001c103c1408410b0700418070409e208510014500500031050312240107100740c2ca5841da0003100311900085003100e001760030030f0000f0703e21b01201d403841140d2404214240c111010751145917480502c01d4646010b60390880000f20040c210420041300841c103180542e00c0341054401d038900603002551 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 645859703 1250 645858453 645858461
    0x1202010c0b070c05010e0d0210090210030b181018091a090a050708060709060f0503040213060305011a0a050d0201080402150405060c0313050a0b090d05100c1709060c0307050d 77
    0x1644c450001e0144c2450040c006444116050308280940154401789444524500c1004000741e0300400702032102070b0000c2d0481c01400340c607004a8208188404d8144007a150000852003211070038100312500c0d04046070301d607110760700c03c00071868a03041c851484001180541c0c0708191610300843c1c096641d0b038100c0d005207009900708016046e40680000414081000304541d07100307081e40d8803115840d81d0f91721400c50307103415540340c0880000c0c0d0130300114006141140708202c000c02c3e0000b002c074000303451351a02800c44040031840303100c00e501d180c1381d0052814220700100003800229561400248550000380400ba40180002d01c03500c02c03450711181c1008204c0584000e018064961a20f030768940041c9646ca503c100c0000004070b6085c240042c003032501c0d400107005d0310b030888d0305941000c0c00c0781d0511401c0014102e0031112800b80c0458214000d00b54071031220b552030305a9402070413a40000307044941d43c0000c0e01c1851181c10540800820220a20880c1d8021550b4034005a41e241904a440d00034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 645860953 1250 645859703 645859727
    0x15030b030624060d0b030d09081905070b0a080402150c120c030d06031b0b031b0d0615030b1c050a140f0703060507030b030609071e05180f011202010c0b07 68
    0x300301061210104c001a8008108803800750200d8424120780c100640304180c81e44600c0d6800c1d4015014a0b0f0b60040043c0300d0744411b445482203075081600c480140c0c3c0c40c2e4002c8054000000c1c0800204030551030b0071110014940c9113161400c0c0fa0003140d443d80c980301c010a0313040d440304010005092689450800031121100001d0400300040c940303d25181071074401c118484000002030420104204030b0b84012070b409103041d000d80980b442c00d00000030015400190b03002c0c01e91030f5036040024001c520000030a401d403459644c00100d0b4041007080203071589000d240316a200e4801041070000980c00100c0749803e40d00007055244403402030495031715201c04030f041c2c60181d0107840800001c2085030b4001c5409031050f5202070140c4a024014160b9a150882d10700b1079991000004200c0d1803c0e030440d0041c854009207a66161a494101040c00031059942c1070013501c0c504000c003c0800b0150417031b2800350154408624850720aa00024071460404001415111004012502190103891a4250 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 645862203 1250 645860953 645860959
    0x5070503040b0910021b010f020102220501030e06090d0e1306240305040c0e070302221502030319150504090c03050607230c030f0d0615030b030624 65
    0x76503512041000380707a8000c1400d40340140f14030089454554004500c800b0500c05034448294030304c51030401141c80c5604a402c810a55508110b00c445440d541c580d00d445040c1d0307812245c1c4100b8944030005040355814081d0070704e650081c10a0141a05011443e80741143e01454a43d00d00440d8000280d03144111510840e0214940f49001401c074010580c01c600c9000b061070411a210800b120603000e4a50841d40240200b01c800750600070f41000382d0080f60005040c0c41c005042c0700e0b011490b00c40042244000c46c5414130405c07010440e841c0d10f03195144150310305101940c00e5042214503900c8001600c450600303a00e46502903100300705032040303807140103100c0100240000078842c203024071500c8850105555900403075000666050180a0b40d50305028003408000070441101400d2030240c004218140c1c1d980001c00c1550143c11840d8081d05c0b40d5a8094000503940c2d10b007840c3c0305089001101140181802c10a42c001e003654042502607001040303039a8a401e2004242400d00e280c1d40c500c642981c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 645863309 1106 645862203 645862207
    0x311061813020d06030809090703111603050d0c110c0406081b18010618090b0f010809210a0e03060f04170903061521120a05070503 58
    0x10350301e0080980107051010005040e42601c105078410794140c03070041404407003803802c2c1030002e40040c050301b020031031841c1c442100704982c090040503692240c0c100840c0014503010304210343c1c00118401080290120700000a02140103250326242184101c0904542c1410244502020b03910320344020032507190721361000c80d02c0d00c0744a9116034110304070f030800484038400c000d0000d000c0c0459446101e41d5044480c0c0211080017244d216640c0340d4101b51414605881d480708121060200303181003c1d89075908103003540f6240d5003e1201c07c05d02026805500121f01c00c60151000440d01d1340d900d604c182e0f40004050b91800f056170542a907050302c401050014284c09042e40b507500004a40b94142030101d03002034103190003214400d14120140398540c0d298506055002481e801c4502c0c10380d900c0d40f002c0303425561040103003460000c010b000100070701380d03500407801c1d5003407582d001044903 = true := by decide +kernel

theorem cover : BRFrame.Cov 645683453 645863309 := by
  have h0 := BRFrame.cov_init 645683453
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645683453 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 645683453 ≤ n) (h2 : n < 645863309) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
