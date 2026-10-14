-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2352
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:27:09.360244+00:00
-- url     : https://prove2.me/submissions/504465b7-67eb-4a54-8927-2a7dbe06e902

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 422841726 ≤ n < 423021582 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 422842976 1250 422841726 422841841
    0x60e0f0301060939050c070b0d0f1a0a030816050102070f02120607051c02090d050106050102060a0603170306060405101214131b090218030d03060b030708 68
    0x140c0b00440840710081c500c00c41e130b40c10300f40314241c07004101c0310ba41c00b44000d50f07581d0090400109411a40c000100081c41000c8404944000c81c0e80422044070b2512041c1049004c0959a8aa9507125150441c0c202c80c2c00c280150346501a2a810341150700e101c41e001805035200040c034004000c50810b480702d10f1402501c80d4803008030340c1c2010340c1c1d40c0d1000b40d03100350214800344411260840c0a034082040003d0140c2c0c05400c0101807408503c4034142e0002c204c5603651100018071155074104115540b0480d01c58050110502c0c50316048000d1034480c103290b41c1030b100000007607080e858603001c540003800003a00c00c1c0c0d15480381c04802442001055804c034070300b0f0300748041007540030b50303d89013036001d4040e2640401900c5600c0d40c0c1e070f104400741a20341186481c400e100c0080c46c02054406801c4420301280d031038440c54120410076052124100309401411714010041c0102001c03901540c0d401461410305071925260360340c41101d600c01e61600784d00040d41c0255202000200ca110369440c400310031240707 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 422844226 1250 422842976 422843021
    0x50d0b100b0702090f040203030403020a030f150506100c020301061d191b0305040501110a170c07080403080f13170d0807120903090b13080607050f04060e0f03010609 73
    0x122070510032100003075840a0703801c0224544c201d15040c4103420610050440c2d1500303640c1e5004c40c0752100c8aa101356030802d040d0021006210128851f030342e041e070040000f00645e18006000841c030500701d844000030801c603400c3c101e0071928254441c00c0a40b0b00d01c1040c00424100460b4010800b40031a4181140440c400c103502d5101104e0152484103984400071200c0c10306102800c074028070340103005407481d640354503070f0800b030000c0344004081c011026030354129403000d0802c3ea080b040304060302c2215520801c100700ca0100f000e240036601504c3e03210500e917544a05c504002c480a001e9420104812004000005013071002035001e411001075a41c180c40f000c1c98001c000755280740c0c0440c0c0c0c8034049402281030070000c100d40e51103682c09500ca81082c140d06e5131110301c1ca0a481d007182c803004211148044081c0300d0001c1c100825980102103103451031800c140306010000e140154400c54052013075002010360182c1c2d038000b40800d07481c405802080080c0d40c03011820060100072901950403900c00c1c62 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 422845476 1250 422844226 422844239
    0x901110a0302070501080a1d06150f090402010507150e0c0a05010e0f06090604120809090f0403050a051806070303050f010b04230f060301030501051b0a0f0c0804050d0b10 75
    0x501045058160b006841c41d10729000042d25800300003440c0d100c05aa035403c640700c0710350240400c1074035401140c00a15092a00c0c0c1402c0448950f09171302117110304c48110300c02c150b9664142005521a50a10f42107483d1042868404100291134145a40d5503050403241b01c040e010001d0b600d10032600031140c112640303641c2e40041d90703495171400965070010040c40c801c11a81c14450000c107201000070b00400d1a055980c1e4190b101405092800c8900daa00051001014940b4110310b1f900810352041d0201c903070500f1307a0064100e03c40c4410301d1091200216410345881c81d920340d100c0403180003402c1c440d43e8400390b00d8020000c001c12109100c02064203400070072800d000205441c181e5000e910250401c5030082e19800101301c2c0d0889203640300b60402c2200d9540c0e1102c00286009601c100008621810321040740da1450000c50502d01d6650002d02041106079449048842030321385500b070180c014286401c18004520550b00400e8102a0030200d0301e00300b1444d0f10b840341c0315046a503d60b10340d0507120744 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 422846726 1250 422845476 422845483
    0x20a150b01051611030d031b0305090a0b040c0e010801092a05120a0c0b1c0902010504030f0c09021812070b090910080d09031b06021902060f040b090111 67
    0x1030000d00280d01448054100c003a11414004103034012025008034040e0200000c3ca03020750201183c0000740c6030002c80702c0c011000c282d40c0d841300c103103810144001c0c9400381c1080d984a00303a404c05000f01410402060612144c49224405070510b10017000175983c5174480c1d10702034580b000b0200c508241c0c1c9120050240c50070354071703a5044185440701c00d00c040c0c504002c00000d00c210b8084e28100380591a1402d000600c41c1d00e810004020504d4282d44812840200341014a00c207444020310908011207400144ea02c98102c40c1030760b921072000185003010781072210601e68030707401044905100045103509011851460481e030304045500000c5c411003d0f40c0f99481d07103502e01c14003684090070b2108220a18286010039840181412180401030382c03540868505007503960300c0d4011900554043c014131049080f41c900800400d100c880d40a40352100c02580d4850240074060844940f8403544110746d107140403210ba0340c40c0c3d100560f40300c1c1c1c0c0f075131a1684e8691050010300d0120f002d107a02e0551500012 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 422847976 1250 422846726 422846741
    0x3030e030d021501060c060b0d12020d1d10051215040b0f0a1403100c091d100302211605030f060c030a11090d050115381603020a15 58
    0x81c60190b140d139103004010f5960400c10b2204540054403400d8100c6940c8940c0d850360046402807001c1c12000c80c0b81100a810155501004ca040003009840c14583d400c104940415640c0192217422048141d842d08440c42e014040c0400200340314601071021605203510304901010381200c003002003445900c01c01041d01c0e001100b5a40010308507208205410000400190100300902a83c003001c46041e040012606820107110201d4050030703060101000c000d0f2182900c45107060f81841900303107000c000069240900c0020300c1054040c02e03003542482c141e1030f03c458081c008411a0080c41c012013005060100038080c0901903c600d1903981c0c10788100003142d03401240c4074200180346d0344406410002a007500900e555983c081005805900c0e1981c02d52400c0880c0204000a50080350102140c2e0142450340180710840030f2880304204034942d0840840c042c03e60b9a1003d20200070f4208280060041d400c070801c0c00703404400344100381a000700c4d03038034055440303040300b4442101e52603000c904031480c1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 422849226 1250 422847976 422848003
    0x9050f071d040501110a080f160c1202030f120405060a2a0507080a05090306061002070e061206040311011104030c0b0a171f0806011d0417030103030e030d02 69
    0x100462071810307100380307002a50410302503000480c880104041d444040e034840d50707036400040c00c40e200308000812901c2815800c2100d100d80261300b4005408010685541c0c1000503250702030681000d04580e00800c111000c0042d660307595512a080f01500d18262801142c05884178080e03800002c8030802244603050400c007a9402540d08180700c1800b000070010300c14004400e0007820041540864402406840b1005140d42d40b0340c0c0e645800c0c0145070030568060122809290b074446501e407401d0b001f14101d0181c1d281e0401d07401d59a5101c200003511304452240d21000d50140c070b0140000d0503072040600c51000c142000031703c00344481c1403500c40c00d4170581c4800b501a4003142c00904c07000b15200c00a1600ba413040c9032015080c0c55604400d070350b40304165000d0500b44803141c03009070031000500c00e1000900000000d401a5850700742480e000e483d51100100d0003030306480000e02040000c00340070000c1031040140d1500c0e50703160714001d0060728070081c0540c0700e403282e0303582c07102c080d440000c0b40b1454140 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 422850476 1250 422849226 422849249
    0x10f1107080d060506121602120444190213020a030212010e07020706110c0906030f030406051c0203070f08070509040e151803090613031509050f07 65
    0x50340d85075104190400c00c0c288003203d03202d0800051550700e88010300b0a120b030203612004a030800000c00343d8814907088802c42903402c50000c1c50142281e44058900310764405c000c000c0000054286144103008010300c1c03e01030f00400b0400606440000c01030740400c0c44007811146210f060300c519003042102000c00035130002210080c07a6481c400d907005400b000055090160400c2c501c003e1002d0b568009030840c081c003034442410401210740c10050f001c010700c11410210174071000c1e00c07103c603150f184410032580205055000701e009901c003045550302d14568981a01c1d21980c071200010165413118040c8400070b002da00c030301140d2a52601c2200d010711070b680c403140f0703070488e0f0141d007901c108070001c046006002d0103000b104441d880364021140b080007024050440010040070060f1050380203040d82000b894042d0344408000400005c80303a075100c0c11210300d901ca07922040d035015000440e4000400a250341c4014018005090f0040303a001845001914864140d48071400d41d280c2c058810220180c1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 422851726 1250 422850476 422850487
    0x219110304050d0c24030b060a0806043b010b01030c020606010c02010e13240e01060e030a120503040302100b2115070507120c02060715060f0f030203010f11 69
    0x1d0022401c0f01441d12070000302c0303030142d40c0d1200048030391030b5a020078404050b610004a8100e03854030884100e4141100c03510b040003400708000344001c1000304028061559071489011a0800b22030f05180403500c1c2e03a40c01b0030020b1041e00c9040c000003e0b805a2169801d21018240640c003a00030130751800c103a64020841076441c075004550035400041e099050000c0c03107a03042c0440d101e000410503660000003020070992404008468001c11304200700d4180d850422080c050304866411142c11240e15182140c403c1c6e4082d00024101061840c2c003e00310160140043ca089070000d0107544101d0094003907a18100130452108251070a20704030701d9000e000e08285001e260031401180b111907040340c1c00c40b9001e030403455106640101c02d541d503102103100803500b5000c1050ba8401406103420a2401042c06416076000c1f40003801000c4005041c0c0450030a270b41c001d172000303601c52002059808a4004465035542c3c89108010003400160301a50030940100100e160b14040c5480d510065444285801c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 422852976 1250 422851726 422851729
    0x7020a120e0d150c230307050717030a0902100201060602071a040905091e070e04020906010c12050301090c0809070b0a02030d02030708101410052b021911030405 71
    0x54004644469100b545551100003050070301401d440659820500020f0118003200003601c2c0c078991589844d000e180b06928010100b09080660750080e9960410076201e48003442c121611040d0040324a4040743c0200030014a0100da1b004803a04a0095911610010f12800d040342652600e000d03080140e802460100b1220035000980044002c90410f024100303a1a09076200c103486080d90384c212241d00a2441c9138501c030f0810510284042020010000b05141102d00c2340701d0302c00208041e11a001810005529034080c00803600419800146030040b6404035a01810940003801034412542c038042640c1016030013044040e00821522001f000042d00c2c1030942010b680c846000e44c800c6000c20700c6004484941e900185d8060740c00d43c1c40305103242c41d1010725a0000c4110b984500b402c00341c0c1014261071515210034012550455241143e50b502101030002d80081e80915100c09900c2949924080e060966024149115111403034018000c02d80b40c0c00c82d1b0300100031049050903003007000108130760b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 422854226 1250 422852976 422852987
    0x80c060103031b1a190e01020901090f0e0a0b040204050d03111014010e18030307030603050d05030103080a0c020f10031d0c15030901110708090102101109040b04060b0a0507030807020a12 82
    0x2000c0505c4000152810420141c01610000c11102803d42e4003c03070140c2e250341e000b40b8a04080c020011030009194604030441c1c90400c400350072620741640d15080710380140c840350112000b814014220342003205851038024070007603035510604181d004030030007004000c03031074040c800d51074401031a5250b00b0303401c02d420715040140150100c20005942c40c1d00c081d40070703c140050341c0b0510154400051079451400d203036003041040c0d4140001c22800304014000208408152200324940f0304e080403510b1001c0c0b000c20701181d10244034580c0010081c11460856070326421882d600c11540880c40c003603010803a02980d0359041d10382001c0d03000d02d030000356420404124002d1580028a1030010802c0d413461801520941e0000605071040940081d0b6852556010840440d0090300410100a04d04151011032558081d2880c07081c0301d00e8030740700d480320b186da182d4200c2401b80000c841ca60b5510944004050101c0d40b0024086001c06c00e808001070f5164000710b044d003a296000150740245a0200c0700c22203a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 422855476 1250 422854226 422854231
    0x3050c0403080d09061d150f01271e0e0325030c0b0c0405040e2e20120c0a0e01050702010309050607020f07080c030c100507080c060103031b1a 63
    0x580c291399068803808101d140c00749850043c0001c0c500205601c2d588001c0d4104142041e002145010303103014024003038111203266045501340c5880301c40d041200180603c1000c108110211181d040400420188c007094500204c902e00c005010084060804881da40305c1c0110f09115040d94403407144407003001002c18025109500c42e1070142c0034841c065480b403640c00e0007902d81c06810940881c3c140500d00700b41c4102c94005217520000c09903140e0b82110110b448419105142100b41040180e445025454120b1038401448080788280304800f02a2003903d03810909130110340c060150080342c041c01004080715807100981d030b01c544190351703402c2c01500d8591100c2c0040f4100f5960701d4042011031818480240150f2280d4050301d0700300341080b06c00e4540001900015066000044141119500058204440c500941c1c030304009002c0c50000f076940e03000b4000c000c0d22824000500080031600841c010307060728803985441200108565500c1801c8454480040c8507890207074800d00c404003040308455 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 422856726 1250 422855476 422855497
    0xe01030201081f0b0904110711011b1a060f1008010302240a020a1412070204051806010801061d0601050306040506031e070302030706050702010203030a0c0207090908130603050c040308 81
    0x110029500d0f010601e0001035035222005030600410307007003060b29103809040d0102c4506600c803400e00960780c07a003509200418003003506000b0300c41e80040003503000940c1c1c5010960040000b608030b03401c10301da4030700d1214201e40d054482d00702000c8030120703450048031f113003040b644d6075030b0359580c5a086500348a242c9007c88100741c502c0e50001e00f0713400d01c0b00d19400107145002050380074014030341c0c180c940a4508002c20420714020b80000488407036008100d029903d207103804071030104094860351f0324007000d401c00c00ca5034001805580c2c0040b624601c15080b40307049904090540b8007081081698a031200820340346140050303000c00c0418460726107a0810740e000280207003500e071074504000a50301040740c120006200c0c0d400c842400c000750310303060082000402090400502e0700000c2da00003900e910000f80910f50503659441d4900804d4400c2042c98080c08103040104041c403068140316506411224002c030f0015564113010546901c60300485d40114000c0d420a800c00f030075503a80408580040300f504 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 422857976 1250 422856726 422856751
    0x5010e13050a1202010209010806041a01050d1b201216022d040b040212160c0c0b0309010c020a021302070201050904050114100e0904030f1b030302041403070e0103020108 75
    0x240d01060f04040440d9542001c0d8000503640d603031020024212a01c02800c1c2d511072407820104c44100501710411002c2c124092805540c0c40035002e1145000304414940f100f40c0460581980d00c40d01e4100417001c900819800101c4540120000240c0c0d8521881da400176044000340140041e000b080c0322298045d51004118a440b058410708142c2000402c030f400003a04c01070b11100c01600c1c00c040c410300c2408081034905515065020950f010886000b5003082c40007801100e001d819a03201d47c46c5c00d0505a80b054440300d0495036400003c502c0c1c0c002f951042403035482d003550408101c0c0005103079401660702809840341482da10041c40e00a42009009a050000c1080320030003030740d214862180a040710740c6110845901c11018030510952030388a00c420301401c0903d203400d9969800b40c69a00a505141001c0741d0b40c08a20220340c42842074400040f44011f0641c100209030700350b0090403d5881c0c80c0146403103042440101550750b030752480703100003003240303880144055403094a01992060654609 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 422859226 1250 422857976 422857993
    0x20a140c0a0b0a0c031a0a03110a0b0c1b040b0d021509040513060b01020619020a11030310090e030a050d11040b0d0501140604051e031e06040b01080105010e1305 71
    0x2d5440030307402158080c2e034213540c80500042d282d4144c460b00e401c00040c40a14900c9064030b1003c100e6031151400f020b4101c1406286000655a840c0381c0d20300945071614842761520703001e00741d0310383c1c41041e4101e00024120a115110a604041c81040034805c00103004071a03403a501d40a000480f01c030711140d840450810071640080d40ca8070f0140d5409103442104010780008141042c1d402c60b80310001c0130f41150044801d00a8000640091070f4000d01403040060342c1d40382105c8282c80c21041490554030b02d01000c020024402d10410701102200c070240d10038458251021026074803403088081c5840481c2003488040c24030010b95026440c2440c400041078601515110010903035042002d80b10003c0340c940b00180101c0f501c0110180040b0000e940942c1800d0600002905612141042e154003591950031440203070303030410003030502842050b400606001c01c090102d885500c110380c15640034294400020b04908140b2810703040302c890701442055500d0350803861072142d100d01e6060f1441e10403030381c1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 422860476 1250 422859226 422859233
    0xb1302030d0e121f1109150d0204050a03060509010c050f07080313021f02010c020102090a050402030604090b0a09030e0607050c01180e0705120a060317071b06030519020a140c0a 78
    0x321860401c4640c601d0524640f20311080305482030617a043c0030880e01400502d04a858408020340b90071105031200e0746499001082c20001e01445d801141c0c0002810303000004d0004603070000380a65543c0c00280705000c014502511284510782c3c0b214001e00f010040000402c06050103503422485505080b5801000c62700007954404807019203170503941c40c01d014a0030a0741c091241140303001c1c1d280000e5091000e00c0c8001200c142e00c511855000e26000070018840d03640f1a131042002d15807007921074040741019003000c1d0091004800480200d4801e40e078804203071802800fa00d4009500c0002008440d5000004541c0c110074184040c042c400c0714400450414664103c041c4951240c1d500c8940301d040c0303100d102480720005801115110f25000060001c03981000c03029201d0440e502c0a965908454541045039075001c0b0214040d507503080e400420010f1381500614001c04401014113000448811101c1c1244100000d18002c40c2511942d1400c00c14040080c0c10aa04d03118141e80000c500c648 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 422861726 1250 422860476 422860483
    0x240604090b0609060a110f0703032f010f02040609050d0c050607051513060b1f0e0a0506040909020406170c0409020409021e03060c0a140f04050d0f0b1302030d0e12 72
    0x594900426240d401c09044440100080c06203201f90b80000c0c40d4046c80d60f18080c08070510804000794000155a01d5200e04111683c0e03042c0e1070305250020003a0351120a2064006d401c00d014010008090a400140c6858080307070085907540c00141c1e02072102c2c600020007140d035111140c21202d6001c0c0c080c1c000e480c404c101d00c1003482500c1d0100c1d501c650001502e086000c55000540161089021f00f204a0100000c04526a480b00160800500c0480782100041c0301406c030f54045a4422000100800c2550707054011074942c034400d8030284002500d660418401140c1000c0456160b807240825402a1030680c000f494254000740c00003407110490340111300384420989180003442c00760541050242410400285d05c03490502c0c03000d041c54030f4440c0040ca0329150030445092540085889401000503604440003040d0041c4005440c00044c60401c4896954801c29070394500c80100041e806040d950840c022070707600501502e9005120101a1004803176811b40f590404103003c4015140c24040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 422862976 1250 422861726 422861737
    0x908030f090a0503150108060c07030c060c03110703090f060c0f0b0417030406020309100513110a0509040c06180b040902031302040e0c190e06010804080f12240604090b060906 77
    0x6000c030000c0d96060a1131f040c50a0409401101c1200080242c0004a54464118030b5201e07801032010032421407100044000d8501e10380e2a4001c181c000402c10209600541c03040b0450b0381004e0b05007107903aa10308040d42e00d07036114540600100d42d82d15140b80014000011030ba4081d00c03034440c10130303101880d4031428641d40044030221507060b400401d11000d00d00400c8140380441c10b14605115618000803a21541003010100030a44240d009640c1d5559451048650160201810003a910f00d03040c28042141d100c0343c803a10011a0700040d400f820114078000e0708054440d030341d011a2502e0728008140000750310013042d0b201540c035000007034401640c0d0382c01102814490440280f05100d2046d04110000040e0340c3c3c2190080d0000700104410540318a50590022090138140d10659032800c00303110911450841d0a91801c0001d84881e000c4484c10210340104502034810752099120040c081614009000d4036070322003420b000402c03c0740816006a03500500180c0080e003040c00980104400d50000c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 422864226 1250 422862976 422863003
    0x50114070504030506060306070914040b030f0a030921112101060810060e0a020703020f010504030c120206190209060d061409101a130312090e070908030f090a0503 72
    0x14040081c08400c00540380c03c0001200a8230880c1013005014001e040c5501c01c00e1610794401051401581d04c50b0700c0fa019101d009001d0702c0b881001406d02c241c0b200540001200481d2801901003083c07900c0c20362101c0c41032800c0d9000e0102401d5911850769003c54041c5541c1d000619411146940d00401d00c0bc8541c0c5c03030302c2c0b4004140c55040010341402c00714038140111406240c41c07010400700c0c0c4410b101c150480c51b8000300513680c131030a0400300c1c1804414100c04a0315070910301800101644031403105003003409440c04019002c441c0c41c080b0781310b15040c0c0d5010030001c03580307004540f0a62150b000381101c800050200d85018190135103402035070010381c030140319241031040301407060a1200140740d2150740c0d02c07225003880e420038503104881c80c8029440c640302c580210ba5a0040034001c24520b01031138010344442007055440c14000c12004a50084200e0100d00c1c5021490a0303000b00169802e6600d06030185007003007215038207440107401c581c20f1150301c00c850000010300c40c0c40c240002c160304010b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 422865476 1250 422864226 422864237
    0x50a0b0d060c300903020c060c030712030b0918030d0f0605030c0f1305040305040902040909050c060307020a0b040c0b0a021c1d1306030501050a09050105060405040302030f0705011407 81
    0x34a601401d520041d0000303060300106440203c1006544201526041d03442c1100010000020f060407817a01072400e00d030642241000445480401000002d01070842c403426009010001c04101202912108004507402950903404162084066501c00c208803801c04100c90421500c1c200790740c2030303540703901444a04a0791a80d040c891400d0070300000030f5500c02035825405d02c40c14034020403400420b51445034000e990710804202014401c0381120000c00c6c0e40003040d5210703500c94900e14010903420204840c1449418511116814481c095a104507880d0b00545405241d584412070340c0003005104840c000040c00e4086400d0707400c5c8016107504101c84d401404402d01c0807221a40254034000d0403002c1c001390641c44600b48072111022440010151111240010700401c0d6001800050b040103103035500741000c0044180155026a040e41d025000a00540d00c90360b05000c1111030030b45000c2d00503002081403604035a07280300145162071098000051114005504048404041d03031a0000a031 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 422866726 1250 422865476 422865491
    0x80a081b15100f17060408031801110903150408030c0f070203010204151b0b0c07030c05060a05150a030b01121b06090302010f0e09071d0411070203010608070b030703050a0b0d06 78
    0x1010410000281c0340310b0550360010200703113070400e90700d01c8001e10040c1a07007030000015405001c180410100d101808009001c101001040e60321a80c0010b20f070340d0701074030075442010710f031407480e5100ca030140c3d42108035207103143c580060602c172540c031502d00071303016a0013000001c006840c00d00c01000144a880710318110103203a00300092400401c000050301034686d012401c0042900008490740020344c0700610b41d0b17903950f24602604c000144c40c0c0d01030094050942004200f001c0754100c213205d206003049408201450384100000d864103400064620b4a600c40140400441e080300c5c82c9105006030201e800001c806425601c01300d8150700040d0004210b11000c200310b50b009541c4585071013040c18210800d0500300c1c00b00b00102c4006200004101c4402c0e610042181030301040c05905101a009000d5041c1e41e00d9016015401030204034000d6182c1171000030b014201082400645070002440d03450741d00c0308041140548806440c06102035514002c0720303410323540c10b64040d014034428000800c00c0d4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 422867976 1250 422866726 422866739
    0x3070219061b021c18080307060509010b0a03110d0204110403050d182301050f0a0203250302060c07050309180601020f2d030d02030405031201080a081b1510 69
    0x40c8029040c2400d6500500b503100c01e82460052200004c001480c000950042692101811400c0c1c0d82c8692041d0000140600c1030092603040107200d2080131000b030092a00e1881031040c01d000a10000d070807200518102c0300549410540343d0751280c001003002c01c81c140705048420f0564419030040319150701002d82e03507442c1c0341c01601c810641c07a0008113020406240c16014030403903051541da0b07e4024000410500b05030b004800340c0b03803c64401e81e8040c2e10740c43d800001075520b03441005a10101c0019842a0400c0344a1240010005070305038040d02460715003984082c40d03508002d4003122603000078042000142c4400e9a049051b02c251003010f085820724000290400032841c103140e41b10741003040003240510b83c40e03120703d07002092443c00d03080510b09040c80324118040c8000d400c0c281070000090106001000003d042e41c0f050300800a403860341e80e1040195100c21070070300101070700010301c00526031803564480c00700d00c41c40d0030054517907207285072074001d1101504640e0700c880c264841c00c061106 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 422869226 1250 422867976 422868011
    0x2603040b040f090f05040f030f0c0b0a092f1203091c0b13030518040209030f0a14010e0c040f0902030607091401080c03180f07090615050910050307021906 68
    0x2c4c034030001000c04c03080c04c054032164240d01c28010040d040c402c00c0711541212600c94280c00c900300fa004110b1140509001c800f2034050000e98000365015540385107504421102119040203100e81103010b08903030801041805842070041161403007a00091000140945400e24030084145642c5c882c444200c0725454500561140500069081c0362a51100380000b50003604851880200c08604c10b1040c0070f42001402074070500203260b4050250704401000c1000008200030464803030361100da5580b03000e0002908803649510b94856170392000e4000110342c242944074072544100100301045030803a81d00400c0c03070324409840000000300c0c0004204201c0c84421008240300d0002d00e01150f00e41418a0000d901340800707420310f02800007140180c0d0700310700d0401070001c0d5038513441c2c19601c0175943c3c0c21805000f00103520850626003041c1c409851440c1c850012904040c2000700300b0b00981c44c40c61802c40e91904010420015445035042c950210210a00305042c0c00740309070ba010800d40901d0001144 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 422870476 1250 422869226 422869241
    0x9101806060321050702030705060f04030f060e06071d010e01090e24010c08030105190302120d0f0905060a11120412050705090c03011406160803060f06042603040b040f09 75
    0x1304542804a000103a80204800040b114210343c201d4403110510300142070b40c0320f076a2008160040700c03003000701001440d4000e684c202c440300c002d45d401652001c40031b0310306200c5200c40c51810744c03000011641e258018a60402070060600d070107104152100201003481f0020354410142440c106290b0124410364140724000200078a002c402e40c1016607140c0c0c00e6801b060280c54440d091140103110310284d80c800d0a03004503001041c9000310380000f02901e0301c60105c400690001042a441c505e0300c1c60250140e0800c41d580a00641c0c034080c1c00b03800440c0d03180103841c15121240903511307080800c2151400900080c0800b0900051034020f1885d00502d0504070b540018064561542009550703541c00003581d044036000d007120000c2100c04030010344284141804000c03c0114440300500380071604c0c0145205240940c0d00386608040c0710b00700b0209014134400e281d010b428140c0552403003078514140c001c1c0c2c0e440000882c1d04003500e40707040a20a80094101d020440703554407041182910341d004010 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 422871726 1250 422870476 422870543
    0x13080a02061504150504090f05030a0c060e0105010f0506070606090c0f09080c010206012705070306080120030c070201140a05071a0408162f01030b010305091018060603 74
    0xf28050f80040d4580613810180b0a0b80d20841e50b545040b803d21050700c010045aa61010030b40b55102040e0704060040101000161002407600304d40c10900350303051003040d05841000c0c80d4581c2403440c04080001d964459102100c6640e1203410024541c00d4a008003040d5885c580c480110f69070080750000c0c201a010340c44148598000120510141d80120f0124151100340c07050900d2520302e1406400d00c4c9011444400405290008201145a140e4080300564041c1402407007040c422420340543c50001d81a1001c1a280800102d64000c104400500c026803060401c004011601c950f0307000741f40c2003400709102003500040e40e8010406150a890f0000c1c1910840c1e0500c1d042c0380e12030001c40e000345405018801095482ca0041c01035280b4812942160340391105680d00c2150030700089143d050100030f01090800204000540c000d004044c400c001080007006012254124907020749008030203c83c4a40108143c2c0c0003084841c00b5610246010b80b0b1131041e80c0402c2850594150400900f2b0b0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 422872976 1250 422871726 422871731
    0x50c120a0f03270503251205070512180a0b2107050d020a090e0702070e06040212150a0503100501140108010302060a0315080d0207090b0f0d0b13080a02061504 70
    0x11903072000000f03448003003c00c070704040c840c0070110b1800510f50312a05131440d15441949000360b0300c420340d100003442158487c06990703034903482d074190546541c0141240182150028400100b0b0b41a042e4058040046007486000803501c5250114000e54640d030811107032944000765044243c1c0c1c03101c0c040d0343c034405244803511081c41c0c1580000c20b030340100d03c0384540303036900040c0741700b1001d100c0c0710b46401401c0d024103100b01e541403212010303580e040c0c5032140311b03015084d440004009282c2842514a1032142d00b07d605525901e00c0500c2d00c500344081400f9078001400000440e2a0301c04104a9008042044000a50b5410701c190001e581550490850402600d44010b10050f2105c40c05c0c0d40901c1c185040208422800040b5016895042c3d0822800751242e508820000d560024400c0101c3d500e02e10100801402034043c45007540304030b1405034010070200d05440010341380c2c4c045261b10000e2021076404000241c4d07a0007030150702c140c490301c0060344280e00303000460114110605621804403801c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 422874226 1250 422872976 422872991
    0x12100503060711010b1509010305070207142101110c070f2102040b060307020307061404050316060207060f0f050718060f020c03030a031d07030f0f03050c120a0f03 72
    0x281d580500410200400c59000107482e090b4509411a0814140c0140103088a100140201d15550414540790340041d0510001c00c0d9150300115483c41560000c0194080c00384a15051144e411000480e02d040900f03c8400110038080a10504c10803004001626540b02c4400000c640ba04501d600184802a8042020480050706001c82000282c008000802000c2d41d400064020700307140403a2504010000100000c0766400700040200610480d401c20000c182c00d10b00c4403005008460090042d8020410343c80d00c202c81058a03140d051050782c01619001e59035a6410640d40401403150143ea103400251202c8083c9002d0300b68041028503000c205050030b9500d00a00d10010702c2900180007400181c0308500d8406c0c0680910b83c0005800c803983d0350340c103000c0200200100c04424085107240c041c03030211410085091422030340c000c031110200f2030a949560f5206210b1010031001d00004104082d04610107008614100540002c420344a08041c003015200d020800c508504141c0b41404 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 422875476 1250 422874226 422874229
    0x30c1005060a030b0c090a1e1e0b031f030606061704021e0312120103020901080303010e1605090d12020c061606180507090b011206140103050426121005 67
    0x510030101c0e5040f00030800c0603280d030b4201c240c45104101da11504143d010b00b010031040c44400b0b5140080c5000e942d0103100c140ea40c9481001d154405481c14402511035032708224210203003003e140c103c46410310345150b0620302c0040f083c110015034011111035885010800c24940c1299003040d50300c0c5040c4160100c0e02d0154000703800329440301003501100c6030003501d24aa980307003080795201c0d50b0b09100b06150b03030b46905140700012003400d03c4124441c1c140d09002103118400401524129400d01c002e07484036443c3c00c4840019100f4071040c02042110070b008404280d0385900c02c0f03682ca02c0c002c208180410701c01030002812f00c4000304005005604c2000249055000040c0203240240c1000d00013809070140040c40c00c80c0d80b00c0c680c0203856403040e060003080c215050381c015401000e0036244c008406a00940010a0340c800d4890540d1311140807455100710b501030b40000750b0062095192450a030742080b00d5500e008244078040107940c10128880040c0290030ba072140d00b060400603503103d01e501d0b050 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 422876726 1250 422875476 422875489
    0x6131502210c0a0f0305160f12020c010530190e0d0e06090301091b0f050910031b170f07050a0509060d0f0204020f120703290d0c0602030c100506 64
    0x5400504030424104050b09143c490410b841d500c7c0a80003002408100c0c6007020b820003001c6c600140c0d911883c03003003088415400000e03440680581031315014204a080c824a01130140010044c0180c0b108541d81904e41d4198102e0241c0726880261803501c1c1d81440030840d400b25502c64007140c103145e02055036007603155048070151400c620115501e40e076a007004d070080b9002d403420031801041c684510b001c05410218841040003a508681c210262490b035860411592400039907148003549103d0b5000d1022590310300561111400d65143c4211145e076070480000b07000340c0d441003501150002d0800380d1030340c0d5092004070014a01210441c1031982420000350310120040d1400d0302c284000c290381d0f400c02001e0f102032006c054000700300310740310031100410080c20741c0241032103046086c00e480024003403800b03449106440c648041001d0b0b044102000040000e0614011295022040c100320304000f43e40b82c1d4650001d040541c1c003031600e07520030007105441e103080041c0c0708500500744410004c072920f905 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 422877976 1250 422876726 422876743
    0x30303141b2b060602030901170c09042c030a020d0c0b01060e0d050a0b04020901121a09010209090103050132070804080909070305071206060e06131502210c 69
    0x4400101420305030620b0b0400e07480d4081000359441d040ca00001060f0f82c01002030308580e18281c030781071101754a2294011b001e0030b040b20700088071002400007003c1c90070641c2c060b00e80c95440c0c4104405020340881e0320038100d0910079210071a503100040808000794107001d03100d0340844d10304109920003250b656240791b0400500642003002025880e1007402e80d03401c09000d819941003c1036a414000b1405c2250741104220307400d90040700c01d000000b5990300c8103584040c5441d00444c04544d03181900d00c1a00d0a000080d240140c81d43d0284881038041e0380e0703952418025880340000041181040c0c048209101c4c2403080c0c841c1c900031030720410719000704058065501035014606100e882e40e9500c2e00400501443c44510703001892001044600c5070154080c50180d400d646609034044001256141a502c2178014000001d010b90781000031800c10101030150f008000e103d815206485100c00c1d60f5010858041e00d0043c0e000040d1240840d0840442c411502440340460345488a01201c281e42c0c1c10f45e1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 422879226 1250 422877976 422877997
    0xe0c03100203090109080301060c030305060f18100f120c0e0609070e060d09080306010816090e0402060409050403080a11190f1101020c010902040e03090a1208070c030303141b 77
    0x10002d141c1003c00e40c8003000c8950f10006107602c2e07503111040140300000510084000c6441d00300030506500d0041c0c0601042034000746501c00c0300c0c215144070030315030b4001b07400b1f8034441000c0000824040b5014441c500904012001d0f420142b0071030070148115404c1d903000003519540c013424000340d0f032135101c2415440200b90411030702c1800800c0c08540c041c45124032104c1c4544c9001c41c2502000500344c021400780c8030980c2d03803500603120644480d20b4000c2c0d54240102090f200301007080b06a000d400104d0340700d4001000d40e424079035202a80700580704100d40c11030004400008002000156100703100d00040001d20090510f10f50812910502848920310317002d00c1180411301c203203d403050710a400a6a55600250340350303c1e441a042d4003800c07565034100c0c030680c10070104005500c1d000050756400340300100301c074000600c1c041540010501e03c132000d0701c41c00c0c8204285d0011624414109000354400d6a0000c0c1e0282d26482d000c03141da1015102035246c01001000c0d1160940b50303000c0c0c0e80c41100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 422880476 1250 422879226 422879231
    0xa0204050f120705040504062f1801030f020c0a121706090a0207060c020f120f0a0f0207120b060411090d110d060612050d020d02030d090c26010e0c0310 67
    0x2c02c040503191074041d5000341d501c181010100402c104094010004403141425081c941c000012204940220f0007540040c11040074409149813004a181ca01070081060600040140142c105c02051342c1c0a05144100c2e5400340d0441c008004a980d100700c09807a05151910481040321401406060060405445403807810040745501c203050b4122480307207600000411010030490301c060f4840381d5000544100d802020310100c4681120800c650300030346801d282031f140c07101c1000140c80d4489940740e410308610680201103410407001c8104841035020301403620407880c0c15801c01c4140c0e42c1001001804180a00c60111503443e800c1c0b80003142ca500844e030030581224440803400c10f160010000c0d21460500c0c10005024503041d0446641a014030190b455a1207854020799a8101038820080107a104100c0101c0a00f01544000d4a6a00c1400d5240f40c0c207541e5403040046151249281d10088101612031100700001d00c00c4c0f0305214992400303020b6118442d0700003911140b03c9205003100a4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 422881726 1250 422880476 422880499
    0x80325140f090d06090309080a030c0b1503060106090510050f030703050a0b21010c0c020d03080a0609020c010507020f06190513020d0506040506010515071217011403060a0204050f 79
    0x248542503031141c00003d00812205211824480003920700180c2c10340114010b004c000c00c2180700803a01071105500750300ca40038122001e581d600741b05034000300460f59554103588460340550302445050700030702c0d80ba500c0038130240c100420004070820b022070510520100700440500144041e00342c0c0d84c00b655900f00056603030b85100e8518080d00604000e180e20004440c1e60144400364090a00d41c6540e00e54002c0004203c0d44106541100c54124081d40c01045a80603800203445802c0d143c1e071103070b0203a20200f44955545038000998000c95001c0d006c0c1c0c0d450b081040f441c25410460414a4001d180050910b0300f88800203520300041040401c40e1581c50343c00240307190710704181d02c81d04c50b81c3c00341200030f840205042c555200c81c0240c4049405004540000402d03241c03241c0540b4064140c1802d0524160740e80e0389140302c508146208406014461024658511003040f4141c020b00c02c555401d014400f1603002c16040c40c070700400350303400341c0d2043c0b2061140d5100c01c08800800c120a03501e00310180c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 422882976 1250 422881726 422881747
    0x406110a150c210207060b04020306060313050f010204121103120409020a050702182202060a08090c09040b0612030f04050f060d050132010807030c0311030408032514 73
    0x2080460f4450f01500b4580d058880c8001c02d550003000d009014010820945200b0300800080c2c1c072064030700701d901017414004100c61010101042c40e0252042045504090880f001142680c00c07662008560b0103051600105000030004500d81e6401c04402070001407004048003a03441c0100e00032020160390104c1d6100d030080c0030304119018950000c3c60b040307040081e001042d04242044844144031104849501003051106da95a401d06070300400302400d02c40f5807070701112800c40003011420070340303e12001000395446071003046015074080e95094544d854031005010807094041d0700b4441950040141e4111800d00d60b003694103644040740c4003844086240e000903146e0050501c01403140d403402d400007503058408920049141c4994401140c03000880e4054820400d016034141d0210310341d4000181668401c4d071100080780c09500340001c0d40c2c0d000b00402c02aa0700110380444074000000188010225954403500c1040b4081c1d0042d42c03000038251005207a400310600400c1104000300300b60300d00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 422884226 1250 422882976 422882987
    0x21c2f03060a090b03071d010603110a0e0f0a0902070308040219050f10091a030403020705060c1005040503360406031a040303181115040f05060c0309150406110a150c 73
    0x30f0207c20302040b4000a0446036907203510007845900b0110b031034411446500340302c100984110310140e07200c004800d08444180b040e150151f20250750f10100e051310114101c115440603145440c025581e500316490a841441440480d21001100c00c105592040200303507610071008000c103d084d501d01d00451040c0310240d6140039180c20849d9143c0000e2200301c0d152018a003d1449180a642119407896490090085078401c42c48a41c0d00c0b0341001c40006165410758100381e0700588110f0071246800c1c0d1080d100102d5a10074004002905c0030700c035048480c036101c20031400d03240b10121410032241d480e50781ca140418036100801d054180008000809140c06940310700841801c400040c0c607a03088034600400344501c0070884a210340b0200300d003102005200010f5605035034401c2c80c90307404036084c0010044070390001c0b1107880e01d500c4100f2290382039440d011824402c40c03201c0d54200d6103507070500c14060070321058085074142c50791140b02d5440100c2c031030b59010b0740200101e110028a82000c840115103 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 422885476 1250 422884226 422884229
    0x60b0a0f060c060f02040e151509060703140d0204030201033e040806070903030f021506011211040306150819110d051636021c2f03060a090b0307 64
    0x4d89102040005042440b05030741841a9007540040d440044420100b15143c00010707080105035100f80f00d03080160402c80000c0468502906061000c548100c2040e409a0b014004440c0d0700c1c1d8001c00c0800071960540140c0559144d64800b080d08083e150b0000c940c0c13030607800c0e0300c1c0d542d00c0d1180c15200201c020b01d5046801505d00780f0b00395070340351401c0f50026000e030358180700c00c0340042c80810f41d8860003840071403440070100f5150610100c54807000011515900044000940281ea440c2d00f21181070300301008000841c8103a80c003154458000c141240c90900a52001241e07030442d800c820808003841c0800f04213998007215134010840361714081120929803210080442c442c3c3e08185008014203416002114140b0381d072643c40c06003180b1283c1c4440c1403c1c0120341344000400807000d0503480d1780c000d030240f004200c2d28143c0100c1c00900c14016580104909a0382c240b21591030801450580c0020b0290100840200e10303508103440494410310041c480c1c00c4c00903a1310f000001159406005500 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 422886726 1250 422885476 422885501
    0xc0a02100504240e0301050622021c0f0e06040506010303140c10091115030a0e0c03070303030b030607081e090c030114100807120602030c04051c060b0a0f060c06 71
    0x2d40780032074255003100e200b003001c3c0c101250132000d901c060352405000d1284181c0c1d0240461001c607800035220f001c1c50b83c94642c8041426000e101e8031140d044940c40030107211040c2c05c00440d031042071054400807910780c7c0d01504e04c960007820820001c50000201a0304480c0e240c50280885403600b6100c2d01c83e40190400c05800380601c2400005898842e0080c0b9841030081a80c01010010107042007203003d01105040389030714043c40000d0f103504807580004c49550000c0103071040c1c1114000041d007450f0094000b1401b19507510001011030900308010b9600c0551030400e2416400c007030300c40003500c0d50148900c03260b0340c0030000041c002d01000c0c071840c1044400030340280442c803514038940c50300743c008803225042038101440c00200c048000a13810300b01d85040c144980014010748801001e54002886850312241c00c2000190a0301c1c5d80c030070844c401c21190900e114aa001c3d103001000d896540c40410703c601620380060105080f4010181d00b19442824030620350050b80c9000400780c070800c2d0110 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 422887976 1250 422886726 422886749
    0x409060602010b0a0e070e0409020a0314060910020307080103020f19061106100501051c06271401153603051203190b12010f0c030b04020c0a02100504 66
    0xa50141c054020012560303048550004181d00c500c0c00071036516045440d1000248205103400c2c4a040c66408207512a0014295903500303602c0380c9441c48400c2103240506000d903c40020000381c11000d000c442a15009084194514100310300001c0c03d001d41230101900c504010000981507036144500d800825483d00e142c4d544055036400c016004240020300d1000310300500d0005600d443d54144003000b5141c05841d010300b000114041d0301c3c1600e04080700b804400f0380c0c4030800b0a2448200314508040c56492912512025041403040165030029030a44803400b50b0702c2c01440403603080d003001c4414581914003c02203000d180ba006c4401070030440700001000280808209a6411502c45030649024100300d41050190f541803086070b11045030030482010100c00c0c6209856082d4021141c070604c0140f10842d250040708445086444417440000c1c1da990f00c40d22406400c0d0907010f070700c414410454086082c89900052191240c500540c000c0c407800000078132240960050301658054401c0315180d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 422889226 1250 422887976 422887979
    0x21203180d0504050a080303040c091d03031501030e1902041104050a0803090301050903180d08070203010507030f05100b1b01090804060210290f040f0f050f0117030f030a02040906 79
    0xa407650f03029000d03403070080e40310303450200d0315203000411a4000d40d8003a4080c02100e2034403500c0300c010400d00c0907680c4d800568200c54802508108065406000d200f84100d0381845640005001c0f2030100c800c074000e54100c500000d5110f940da41101d4202a015500410b9204102c020201d40384169005a0f0b0300681e455000325010340c002010340744240b01580200a2621f0302e01409640340103401180c01d40c4807442c610040306003488076600385018403a103905410b10103aa4000382c20340380101c1d4001e0010b0781d00d12607a4000407541c040c0d103401c40d50f01045840190705129a5000a01c40d5040c0f640e90a2101c0601400241095000301456900710201d17589646e103e000003500e803502194205c2003603040001030340d02800320000744da80c50035081140c0d04020ba07440c1c0030f00104140b10400c15500a6841d00c1e070410041180c000c1d00304070098501d00090720b00c3c0400448030501b80c184c1040140100090743c0000300400081150585881185901c0d141d03500d404542c0041d12840d045102040d040070130 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 422890476 1250 422889226 422889253
    0xb1503010306060b030f01030602070c0905010e0411041112040c050d0b070e0901050604060f0201060302090a0e060a050601080f04110307031208090d081b070b0c1e03060102120318 79
    0x286050300c0c0b2500040c080c150f540e007060350290005598510b000d906060041000034040d41c004c09040740310b01c100002d007580e213002240c11142e00764450545500800100030070403000100c442c0e1f58400840d002c0105054513403041400f4004e120040510184c800d000c80c1c01c1c003415074000c1c001010001c04000360b58440e0300d03260100c00c506480c000301060022803401104e140c5a40300b40e0507110003400850420f80392000803640e00740d500c0c407180f065541c8d91070007002503100d14410500c0f91030b10002c0458800300101d1070524058000f80140c030224a030806014441c2c0c1d00000b0250009590601840a0f8481b070524058203210f002c0c0301c6034144031341c6200108204140780040d201d14010307220300d40243d0310104560380f260741541805000600c0b900000382d000010b0700a06103c0081d24511500b41056a036511002400940e402c803036848010030110304008030a0989040804c0546400e030460403e000040e548000081c0203008100b4080000b4082583c48041c513010148084100c807001001c281 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 422891726 1250 422890476 422890519
    0xe030709020d1b0c050604020409080c0f160e130b1b0d1b11060103030f09030c14240708071a0709050102070902040609091a061c050f0702030a120b 65
    0x6050b0843d10081012840c3c042c03505088030030b0b00b00c0d01034840380d5110740c01c0100800981100b19080c49050080d404030070360810100544001c1a0003d1003800d507881429078030041154852041d001d03110f810400c4840501c0c01c480d0400e980080c05a0183c0c852506401c00700030020720050301420081114003c00d04c050700300305481c028161082c22107094200e0203c41d0b8015034403a000c43d662250004200091045007221040740c058544a04659281d40c0c07900c0c0022001da002002c010103120700c51000b03240c01c11611079038801c1000e42840c001c0c0c5440c0501d1a500030500e0181180801080d80d000b8008a4407174000c501000e0030907880c07245080c090141000c090b0380283c0d80144a1800c010030741c0705c00c078400c54081d10b64948481003804d1500304444040c040251040560302030f000c14014880d00c5120160240b062500c0c0000b0f04060090a6541107039801040703600c0e2803107624140501c144d0040111610118580313880c10040c0800c41242019142481110b904a0361119039030004c4040781 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 422892976 1250 422891726 422891741
    0x2060712030522020315040606050d0c03050c030a0c03140313080618011802120715020609061608070804410a0b0117160909050c030706050301060e030709020d 70
    0x8010010480f2103c0595a1106400910094140d400703c402a01c040e4249010b40780e00c04c0c0b08240104116454101140c405540300f04211000b00c000b80003881000028040c0c520b2020040d0014009014940c454030b50850442c800036048901c541c000d02d51010060045070000b801440c10b44001d59a1021401e60b281400c032001104032020700d50b0101d07030720810f020ba1101c007080b80c0e103000c0d00c1d440243c0800900d01041c040303508003442040c2001905200c3c44612008108140c0c014101c2490b10110441c14000b0007070107468080d110360300220340c440d042a140f40e04100103203420486075550789000d43c0040006200404a00104c1940d40c10815060076402c0035002c408018200121a1900c07081c1e944800250045c56520800b00511411104c1c040710402800b045040703980c83c0710030711803081f0980342c00d400010340b907610740801e5000e214080082c0c18065030140e0050010030314041d1700410a0106004107070800c01c0200c004410341c1d9040000348058142030108640d9124180900b00041200b0f = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 422894226 1250 422892976 422892991
    0x41401030515010e040c030608101d120a1d0a08010c021014070c020319030906080705071a0705071403071b06020304150924080a0e03090607020607120305 68
    0x10000015000d007142d00340b441503108183c45603400100e00a080001074000050ba0b1000c142d40c44000090541c030130001107020300b00c0e0340310000341c41c5420144804801c00c0f03242c0f03201444e0b002074000000d5a9501c001c6038200351003864810b41840c25050b0032074a124000441c150321003d00c003804201f604040d805105216401d03022140300b42d1048000005a410114000b104032a0000006000ea4095030101810760720090680303204142c640303a101030340510782c031058000076510f541c140043c603082190300ba0058864180b26043c041c1540d156114405c200c021060b401d0468008246898018001d492401c0c0d40005062070034002d07003075400c0c0d40c0d80280105481c3c00ca040c0c1700c10f0b2806e050241039101a18010ba024600c2d0a0602d80340000c415231131003561042042d8480d002806180b112441300220300b00e2030b1008401014800c0080107500041c180003801440d154400d0640b100000c11145178410a5503000c2d160308480c00052814056414090800c40728085103010841e41548800d218a40 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 422895476 1250 422894226 422894231
    0x914160501020705010c0209070504030c03080306090a1806110c010914100b0105070b0606040308030405012a0e1212040e0703200d02090d0510091e05060f0a02040b04140103 76
    0x56038401203981e0b2901c0d228060104040d00c0400000d4100790302403540c0b1031010f04000349071540d80e40d90f040280390240d00680e640b2401006010742880c03c4c405280e0400c841c00000e016103826114544019440c00f00002c0020381e8515208141080c11810b8403044441400200501046030512400c0c00401ca80d00307003514020408064200c40483c03040070780039041a5512410b121040c0c0e0758950030703d0081d0801f43d0114003800004005044030005510a034861030022410080182038411481d0100785113040120500c0141074560b03038031003d0445002c5e0b044400300da030013164400241c108142040c070340c01c00e104001004070b241e1404810090080e130548d901040344a00c3d05068003040c1d400024400d10098017000400300700c0001740c015242d2407038000c046400c06140d039900c4d1898452141000040962148400c1c014810b80e0b55800d048a02e441c0e401e60220b040b50350721342e078484400030f0000755003d0020002c42ca541d0038544c19240a00a202001c0c1e07a19500c8490a040d000d0381120428002070 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 422896726 1250 422895476 422895479
    0x403140d0c030e1c0513080d1115011514130e01050306090303040b010b07020f12010606140f120711151929030a0f0b06091b030613091416 61
    0x840010341000011004180c074008440c2c1d20808503110b40c08074040740d98001c0d040101087e2800b0512812445558507142c02c004013490300001e0b42444504800305c200c504500700100619070b50500c40c005040c060380f8101c2082c002d0454440030a0003409100040c1d00219000450040341141da0b56040c0e8908904a070802e81d80c1d0a00d199803844100d400401441c1f50000410610080c00094105284018000c104014022000c950b01000c0001403214580d1990810070200f9005407030b40d09800c001a2140e0300e000d40303100c202540d03442402c83c0e2181002218000491b502c0c4034541e0018501100400e0311104111040c50640030581910303040c840410742c40d043c100c0340110740304450b000180d8031504200c19480c1102043ca111148002c3d135098001e9010010000342d049002851030303446043e10100307904086090184601006002100300c0124900c00c0c25000210002d80e90301c100c0c02c5503841c19400c0d02000800107094052001003c5c00800307821290248030108407201e9100d00c403041c1c5940607 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 422897976 1250 422896726 422896751
    0x90902040e030f0a081909031d03030a0c08181c020103050606030103020108060d0204021306210c0819090b07020a06150b0d021315020a0c0801050f0a050403140d0c03 73
    0x30b00c40c66544140040003046640300c0c45000b032138100c2e481000481e12403200021076640c00c4c10f42e02484021800110700d91051049c41e4100c0c0e00c040180841500154102164400c01400c022000c807000780c42160f002c11640c806007e0241c2100031214084c0c00c88054401d01d01032000e00b900c03040812400300b0f06003c0002c3c800d00300602034074100e82e0140d43d46071035626020140f00e1440c01410090380c003e174003040346500140402400724014070f0716a444815550320940a810b04041c2c54108071002400c04403032a0500364000b0015812001002c41c000c4a160001a45001030100080041c6a00c1212040001c1c3e29000309034092010300950013800706001441e0a180210703954010000174000605c114040308950b64040c0c0044d03c3d1200403012074584810b00c24456419446040b00140d1150207035408010f0b015841e00000e000b40b01c0244100c0c100104011852900100444101951100018240341c804c851403808000071340101d55070381c0348041070b91010308260b20b5a20003003401c102007400324 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 422899226 1250 422897976 422897983
    0x70e0109141605071a070c0c081c1b0c03080a110c0901060f030e070b0705070611070603110904090303060920070803070c081204060b040c120b010315090902040e 71
    0x19a188012961544642c484243e8454000d02e00a84124068000008000344d66001590042c242500c2d141a919076514112220010640010240e038000da2040a20300301300200b04080a0a1800c0090060500300d0200e4400100c0a001505e00b01c0841c10000c20710900d10000c03c14000250364083d032501000600c40d5981d62603000e144d0b007180000004124143c41959060001c0c00c00e858041040091400c4080c900001504501c46e0010001003440401c82c040121074020882d0342480404084480940c903207070b800074071942c0300741030302c804010342594003c0003141e90200c0c000b07208010b14007880c10000d00402140c0a24240c440c980003040d071001c0010707001c401e000e8a23102d000f0b52070900281e41d44985500080c24075030a1007600d0030880001003c60b4050509400018454411485d06050800903140810001e41c003d51820380324980c2c4543c00f1310482c001c0300041c1004555001c41c800100c0003000d480e00c82c403032900052000802d651b1040d800c0035042d10300880c4c0130700482c0781c9688403948 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 422900476 1250 422899226 422899231
    0x9010207030303021b0715020c100e010c140d0804120c1502070501020c060405010b0a0f0501080402090405120f04050a0e010b040e0603121c0606230c0a05070e010914 73
    0x2680c0040010030020340319800821030038000012042c2c02901240f0312501d8005240c0091140400303028404a103950f04002d1004000001c840454900c05460005010441540240c80c100700c2011a4601032200c81415421080244800c807081d842080b900108080802d44007125a81811101558024440e001e6012030642040c0e0503e22010620b040c28001c0d0300802d400c9855540038410241d801d48284515407207240260000300300e21101d9410807101800580100c0c5403440305031000d000c0d0382d07030021445134442e1303050b501965507884501b0300c0f600d4100c1c0c1000e83c800085001500c808480400006001202c9095980e43c0300305445001c0c0c401416002d00079047c847d0014031041000d03240c59076000d40c101402900b92801031b400c0c03500565950b4041800c95403000103401c62038040c0400391080c08002d10341481c0c92005100d1078010003010711a00c440302900d0003004900700014000606c84076000c00d0b44101100c1c47c203551021f0f0704400d42c50074460915118600008034580c41c000c030403041e2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 422901726 1250 422900476 422900479
    0x402090703110f090d0203160603060504050115081e1609090501050108041707052a030105090d0302090301060b0a030624050915071a1519031101140d0f060b09 70
    0x241040814800840703e0380012200ca58082c2c00c0003d04805030720140021410008101480180d1509101029007600d110b5440240507920b804010410f041410f035007820340c900c0c40d150085075901c0d59250b1034500008070180301c00101091051100032203861a6640c00f07056242c803900402a82d038113201d4100c0d0070910400d80441c21110000d80000c0d000c0200301600d0300340751009410b2180315150103181c69408217491401d213174584c01059140ca07188a2090910310118000d210600c0e16030b511644411b0003080820900d134003ca04422166429000a030242800e01c0a40c1d88a03c080c03080200648050b200b032000c1c401005060624880682050300a0030b0000d840301e902c2d03c04040c0920603840c00c00340c40301901000500c11000010304160510a10450001350109507003440a840410000d0740ca08081c42410310b610003118541201d015082200d800c198882c10007465000162440e02d0147da280c00d26036000900000c528500c0e502280e05507098060400945458400c3d0000b14405c460465 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 422902976 1250 422901726 422901761
    0x81f12020f03013b1b01051905091e0d02150f070f020f01020a0503030408030a1113060807030c0801031202010212090319111005071209030509100507080a08060103090f06050402090703 81
    0xa8502c0441094505d050001854090b00d01034800380350010307a038142190b0b24005031002698200074a00100302c9120304c102e0220f01010516400c0c0040c4940f01c0a0100a00591552040001040b000820713140461b11a4030056640c580310310340f04400b1180346c80c0481c0b06038441c0389600c02070351001030000400341e481030046107036480d1070701d54980c01c1e08001c10041043e622402140c00d401121805000d00a0021050400c1c880c10018058101d0030000c1c910340c09c1514000b02e00242a41c0a0090342c1103a802128010381d034454001c4c101e01a115034050300400d0290710081c40b00c0d8880010040003107078000c4640c0045155450012910100000681b80305540100010003100d01d490380541c3d003000031428502e41e0342450700007070003e8440009080d004140041800602410109036030b80c06c22040d8903050b8035149255942c0d40060089a80d1181007000510002d009079009601c244803594200429100103059807401801070f19040310124000c145020101c0c0d80c19000f401151904540140078 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 422904226 1250 422902976 422902993
    0xb09130b060703200c06031305100c020f06010e10030312090804060908070b03070c02060c010b0907091802040602070b0a1b0c08011b1b030e1807081f12020f03013b 72
    0x1180310404140c10f8905002d039013085112ba50140c403d005500c542e54000c0e010601c1040003060501e90142d101c81c180f0210481040084101000c0410550b48e05040c403160142840d0050300040180510041219a0010f000300740d55401c11800011910790300c0031038450316202c40c01c0b0703425400151495400f080bc0c1c031002c9001494580094220095074100014001000380002496075100b41d8400010070780b1b00106001040c0c400c403140c040d0321072700d01c030075441c0c02c0c0340010081d518000d034490f00446140100e000c901161040c00e00e01c0c400d02d41c05000110401c80c90a0940080f40c03c1d115004d020340c0380101d07001c025804540c50464000458989100c25038001d83ca02c42c68800c400e07005c402300140314180c800180e0b1032003030851310031004e8900c201d420314081c078014240b4800640809a550440c0f52082c1407461281a004140d400000c04164040c901c0e101094012071031540b41a419402c09118030f240d1006100701054106c0314081c2c400340f05c555100391801001b6103200c180003580040301c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 422905476 1250 422904226 422904241
    0xb180f120901110a02100e0406060801050303030a1104080708030d0e01141801020d050f16020703170901050403021e10030e0304120206120f090c0405010b09130b060703200c0603 78
    0x10240c0c0f08030740840581d000e80312981c1c0000e03070502c0b00207408000704031038601440701c50034140301320340151980e030500442035410b040c006940d03800700620038524240c850016034107200112083c3c400500e00070301103a0000c0c2e19040c45640340c1d00124481885140380c08100c1794030342014000c0115000c201c00341c03c0010340b15000d00850544130070444518a40d000c100da500c040ca21881a40d01c540e0100200840307508045d0400348804508048010441d401007106102141400b240038103e02901c4100c01e54604079000165064000c40e40080c0d48034010500f000c0365143c451030f10200e110b404440714003660100e5441a4100c0d40004402400e59000b4001404001c54a0410400d103034001003005007814001442e40700c07800e030115000603110100320700344180701004101d0f0a40a0104442c103000c90360400130b003140d03c0d014801001d407180d4140000c0801c45800c5074400d410032200500307469900c4d603260034042c0480400030391220440581c0d903c1c280381c00e50041412411002c00515041c0b031a2501c56 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 422906726 1250 422905476 422905487
    0x1a01050304060e1c0306050a0b07120e0d0b2806081902030a02060c0d0206070f121d0f0d2a12030b09010f0509060d020f010c050a0b180f120901 63
    0x3c00c40c0c126441803165403081020120100f89141d222a80d0118202d41090203001194416901c4494a46420b01200b400100700045100d805d107182e24100e0f440c44194400610146074551002d8013050b2075034103201c0610032031180f29415064481c840c0c0460725419031b80c1c02c1101d40d0b40c400c1c181190802041b43c2100103c10402d070111500007005c40e1f583e1913682c0c001941540c44001161a0760f8001042c110100d50180441540038145041100505064000292800c0e0b00c00a07109406035482610000483c196070011a84003214400c56410700c010380207059940200c0079528000c101079042800c00342c1164424508541807400d42c505035a01590b035902d9000045038010310901d0b880380c00f024001d0721100c071214001c001300300f0146450f03440c000500610020140900740291424100f940c050780319142560302e400d03028030f4070880d5200e01e0306040e802e04114400003040c0082803414000c600c0b030070707d81200e26200c1e06005d40340201d4201c001d284d920b01000702850000c0c0300a01a8685940c0940c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 422907976 1250 422906726 422906741
    0x406030e010605040509010b010212040f090b12010504060f0b1504090c0c1b06170402030a02060a051c0506030c0303030115050a0302280e06090a0b03040807021206040302011a0105030406 82
    0x384008104035842d180094240d5800312888034a50307644088007251503234100620f00c101c0540100e4949442e00740042d003070881c091405074112240c0c64048200081c3c40b045a07580c00c0411001c001c02c11400e00340340140240c10031004040c90203042a07880a05450540123551070007508074407a40c64a45041c00400180106001d00b00a11007418040004102c4880140302d000e144003001c0c0788690706040000d80803c00c503421820a07260b584042200503100010840941501240c04640b43c0440c03a000300d50390f1188074144030281c90101c82d020084103041c0c0046010306411019160502c0c81d26045c1a9280003d11521091600d070314504450140100018a140c0d00f40d442d015181170b00c00a00d02c0d480c001000c1c040384280707580280300d800d8268000341c0c1e0303183d060048a1051a0505403000126455050b000714a054200000494100a022030807100000c0d0b010b42604c5c414170301150060344610307003207605501550810904801c41040100010341108058440b00e0460b01c49403210704c01851138 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 422909226 1250 422907976 422908001
    0x4050705040b030609071b1511090303070f06150b09040c030c081605040909150c0f05040513020918041b0312180e130212011503020d1a0c0a0f09030503040603 70
    0x7250703141841f03842e034091044602400380e60309082c4140609120384c1103850411548144000038051110b182d5004401c54880541101d240301100b94141070050003445075040c1e40b032041003040c4d00003410340c018501070b210300c9000310b404000441c0b29440503025110824911000940c2500c001100e21045222440202c0c140d460b000d0f0030107803103042c10710031140c20060031f8031203880030152101e4100c003c4c0030f0010f0001c420706d01700740b180100e04c9001d05a03001d180685441441282c000d81e10040d00755056981252005040e075002d81c0c0e20b03d0702000b80720026201034031701808001c1610380d001d4100104d242140c0e4001601070f00010920400c460800c03009100410305003103075100080503590525003d0260000d02e28079238004140e48100300c0c10300640c88240c48180d040c0400b0004025103842140304a87c5c05a8131030004c10000c1c43c0041050380480b060305401c0c3d002c00144890090300d44050000703c2240d03100c5100a180540c02a01d03075400501c0010031035481004103004481c031036001070068465 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 422910476 1250 422909226 422909237
    0x6030a1a040f08070602031f03030504060f02010e10020901020601060c120c05100e3a030b0a1a1308211b120c060106110703020d0f15090204050705040b03060907 71
    0x42642c2c0c1c40e00c80b98031084c001e845140c0c0120038171403080c0040c5050740103e9106905580014074544d0060000d0003184a500148013803600100302c02c034000e40000540112040a0340c03a0b09c020b9140c4100250000d82080d8014426040045111801120803140c1c1ca6004085c1c00b0300400d400c1021550410342ea00c0c1240c0e40e008003245280081e0f2030340140703a0203e4840000c0d1040b40c602d00c803405420783c2400c60040c00e0250340d007a4011780300100a0858899412440c0c0820200c01800124040c0e009a41c840021002804004c00c0843c1c5000050018504030031481136042d982d40462076511480c00720b01e456550301d02e90b0100c50050000f0001c0481c03a0107206580d030b1406490081600346103030001c40e41c1c1103900004079075008950521405014010070704102180c2d10300c5c13411003a42c0d1011404000d0090044010000902190b07100d0980001d03405a900d01400284503902d80251020a000324000c900788408900a90300aa00f65015100c0790402541142d85600802440f940003910003414050b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 422911726 1250 422910476 422910503
    0x6070201170a0903030b0d020d110105040b0309060a060909021e011b0303020c010e07080a0b130b160233040c080102040b070b0a1b03020a11060a09030806030a1a04 72
    0x1d844011a01c114020400040c88040d2030401a060340c498611461140c28681001e0340103030b0b01d41d42c841c9841a000040c200f0040340ba080103a82c035124540140d008120040704102041c40001081c6201c2d40008800703126080d0b48a800c00192010784400944c407910324030154003c4841c00110a442603014036102c8100015550f0b222131840b0076500075000a0b40010b0340b084803000034001d00500c08680001404914900280c81e0740b9100c5c0400010403c681a4007ca0b4241010011542e0002d42124204605042000d44c1c4240207900e004036030054061505c50220501e043c2642400708450650f07422681c0c16070710143e194007540103000302e4000018803000300e00c09a0901c040c3c00502104403600d40c0d62030103800d20880245009011201803401c00e00040648603c0c0c2d142c00100340035030700340580c403255021003d44404480f060804aa48141000c02c02d45004a4005c506658002d407507104a60311420b051580782c0607051030140c415100500c03030081181101d1740b510740c0300e800748024681c0d00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 422912976 1250 422911726 422911757
    0xc03030e04090213270b0609070e090f01050111010c0509060c16031a0c030108070b030c070b040320160527070915020606090c1815070620040506070201 67
    0x104000069005a035070705c8440b60f04d2910945d100d0100c003000c1c140d50812441480c0d071080b210710002003c0354010f10020020902da45d00440d00c112061300001c0c80c040041c60101200441c807402441080d00046035005641000d41c0c061040b8044104203584507490040c0301e00500000354008031030741c1072521890b0002c0040700444a5000c001d14413928541161400821240341000c1000d84007042480d0100010031140000003542012070302000700031900c13956444041c8405000d038000141140c0901c204000405500c050b0800400b400403180070340b0041c14854180d503401d90309840500840445509000700c0c58a810720005203405d9140c030f540760b0321041c1c00c02408072000790b404070082000c4035002c2c0462007a02601c0c1c24000d40d540300821442c46e0210010b005058003070001e0f40b02030000501d000c40f0070f1200f145558000006014040c0450090b803800065600281065a00c0d51038602001c0c0761a039840004914041d07582d0100c2d06090900c02006a590b01c4044101c0c1444008005403540 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 422914226 1250 422912976 422912989
    0x1b0b1009020408010203270705040f090b092506090b07050a080a0c1109040809010c080409060605180108010509180114011202090a0c12020c01090506040b041406040c03030e040902 79
    0xd0f0010100240e12030615440181c40c0c0421b0100980003c2c4070300507106c2e200240042d141c01101e208580c04140d07042c0c1004004010300000a010381510481010401e2103000040c54940d002d1154902c0480256140c9075030b1181260b600980e0002521250b080001e01d08a002420000d8012819140c10001655a80303440e0350140314414007181c0519004c000b40803030240c0c2e80e450001c00342c9002845250642c2c0341544c5200300b4240f1414401024440018016a2002e65020302003a62081181d180c44a802401a800440804054042002841c0342a500c00c0b00c609040761005805030100ea101c500441101c001c841030105000e40da25200e10000c544003030341082c002d0618078a107400c40c1659006000540100a055182c6541400840c2040315403007222a12a04603c610040c2c0740d2050800f0640500b40c180c0d00603013540f107040203110900100450041c01240300340d80f01121000216509038450000721805090050041410004640100000c18107400000e0000400d100709500207a034 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 422915476 1250 422914226 422914229
    0x19050402120f1c020a08090d1407180b04180b2203050c010509060c0301060e01050c06040c0503100b100f02150103030914011e1803061a040501061b0b10090204 70
    0x849074000c1d48940f2007049041c5880244a00c00d1028082c040a41c0c0c4401d0014401c2900590140303606044000078003400c4031544c54166940c106995083d607030344405030044103103101d4681e0140c0c500504000d440c81c1c076110301000c0303440c445c054082c0481141c0701c4140d0800e0041042d034601c28040c0008034844d0300000c00188152094a076603468202002070340b803c44400611211207607000c00d0500141e050f91800780d034110b510078a401b600001064004072414000c84d902d4040500c82c040502c010041e0342c0c2c000900b5120700340c04440505007110b018100303444100c1030068006003000e081e400d5151080c0c550810109060048516500c0410480b51103502e00364010350001d00040c2040c00050a440c1040d90481400d103480f4043c0c0690004503a508420f188039803050143c0034050360030152002c800c443c0199001003042000380a080c2c8240102003d41d10468419441c1400102c0c0b0140541c040b950101c40c900c000d0031540703085a6070001c00e40c20103085500341400222001a802103103000510 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 422916726 1250 422915476 422915503
    0xe2a0a0507030e031506060c030403061404020f0a0303050405010e040605060a0f020132180a060e0607050a1b0c05030f0a020f06030124030b040c0215010b031905040212 74
    0x1d694840314140104100904400e091080c2c11400300c0d85003061007510515000581200c00c26a204100d1014500d5441503510007044030303040040c0000c48489405100744614003d80da1051405054001c0041c090041c2c0001804100c00703110a119a501c180d0141d050040050320025220fa10388001a05a420030240c00e03000903102c001d508003041d420301680c803c000f5200300c504001d1002c0b010b501c05000d6600340c3c01e2901d10b40000011510700718544006a4620b042c4162074010849040c0800038291b0209404050710034003012409840c0304000f207034a80700e02c1e079880000104040341140c58003a07100b00c1c00e650b00316003104080b44680d01030086403a07510b040310040004400d0752041c040422105229907104980510041107001018166080c0340681c034020801c1c2c3c0822800240e004042d0a111950070900e082c0b2491b4a840c1c000a1602000e887c1d642850303500daa84910b280c0c0c5511003184c441e460b01a0b0070300c0e0032032410040e07044a60807620003800c9880c1c0b6002d1807071341c41c580314801103120b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 422917976 1250 422916726 422916737
    0x9060615090e16050c03190f080709050f01050c0a0803010f051e060702092e0e160504050411071709011106160804051516090801060e2a0a 61
    0x241551a044001c1034010811030b16031054038030709080d540321903440200c1e044040c45070009102100004c103108035000e100d04030021001e01e181501c402441c2c02e11021418002c603560360041044640640000e00031190010000341d80d1228103001120a6080501c904000c2d101d14944207000070400b9002d940079040784081e0031207861420b4208844449400d10388100740042d1000c150b00d54450804503003140f5010340d058030041e1035100c01394943c0740100543c04043d8541514540300c0103248800c0c90107d5540c03d20020b1203881e501c000303030350b0050071941c00c0c1c0100300100b01c00c00450403d42c1009003941040c1c00554104403c035150743c0400101105484000d83c40014281100d40e00a02d031034010244900003442c003031030310905882d00e100400602e40305010300f4000040400c5810481000c8001e40204000600c1c1000e221590014003042c548001182414a0103c0c0c0004140729580854601000f00b015a40300c20300f410043c00c07a201c20b86502d10110000368413901440e00004e0840e11100d0303540303 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 422919226 1250 422917976 422918009
    0x80c220614190320030a05010921031e1a090c041a03040c03020d150905060406060506070804260a080702090c190e0301150e010509090a0b01090f090606 67
    0x10015500b002600095042200b0641840440d0b003041c4d4400300852800300c0442d400d000003001a16103d21000c008090790300742030400c410004500310f142c0d400e8662211410341c0c10b040020a0303013591080316001001442120354001c005666030444425802100e080240d00796001010a0594408440345116244009420480700702c0c14510224001014036130365081d82041d65810720710180510019114800c94910101403228071a5400c0c40b5140b2920108002d054a203002034903892300f20380030b44c0c6561422400048a04051044450540e80716410b00d10b001e04208252152040251005490b02d91803002c0141e5080300f0803190b90f8290048102c5030310703104030f4410030004100c01402814440c0782480100c1c410711680d042e10005d00104e007806840400c002c0c001c0b900400181c100781600641c0c000300081c1d4581c0211a0f58141e460544054006940340d036840350ba40d81c0c02250060030300e0003410041000c145907520206445001c100049814001920b40398203952444d0803240800f40005407 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 422920476 1250 422919226 422919229
    0xe0402030709021e0d180f12020c2b050a080c0705150702010f0e0411090a0b030606030412230307081005090105131107030e0118080c220614 62
    0x1c0c45004100c5010158507140310364803850480008107441d851614004684210140f8854000b01c403c0c4121448030007a9000505002481282c0c04406a801c0b211103a0000c03006480812240c8000701c010700712001800c22080080c0202100400c01c030a810440c00c04080082c406211488040703010301d0301640c4541c1c58480030350a000e469030100b13204c0c443c00d88203200446030400c01c6d58409a0242030441180d07242007429141c4140451000e40e1280c40c2c88003003101c0d500840080c240000003130324200c6e11070b0344480901c03201e071006807000d90340b12030148001400113801851902c80c0b94003e140c2030f9644002c0c0c203c107640082040305881019403020003002805644410480d9021a0090900301400d2030310001c15407122040c0609ca000d40480e015022207030300340b9040700445191020600d580c403445403c0003031080d80000c2034940014211200b410b40c800c20342c411076054664074005009942481400c00c140400010040d0045059007a80702008071230a00c6400c0c0100034081c04480d515032140c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 422921726 1250 422920476 422920483
    0x10905060703050f0103241b1403130f1e0602070b06030303060d06050c0f0d1401050a0e16140a02010504031b03050d020c0705090106230307080f0c040f0e040203 71
    0x1481c103010075107403c081051032a40e084c8401d0440c1c1d040b440b81d120070401c5004288080c051943c0c0c2960003400c018071800851000d80c0d0340311403130b21180e1b070340340507041e00d01181034580c4015501052008814410103010840c01003410208512604c1c445041c00342c40c0601102c80d544640301a12540c0d4045038074410300104800744c55100d10101d000e0751940c40e021000480c400c0000f00060074503075136500014600b4295a0480741d1241c1c036018282d4550030020005400b03080c1001d18424802002400040c1c02c0c14030398108802e0350755000120500d9650381540d04100030707c010101e0104152049040c0b07020344080300409010186500100301d0340341a04001d440351040400e020441c500c4540441d01083d44036040c0c90031001b9144c1c0c0560344026409880d45040059006158810540c00c00001d9040c0c205299401e02c00550b0005608440100102207450001b15800000304d410000040c0300d180c4000b440561200c91040e6960510380ca41180d000e8500382a00304404422006003400107502d400c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 422922976 1250 422921726 422921731
    0x503060c07260a030c02070b070503030103150509190606050d05010b040c0f0e1905060f0307031b050301031b0315061a19050c0f0d03020a27062a0501090506 69
    0x403074801c4a52007101615440c3c0c400d02c5810700806039100c0d08031200c58400e000c02001040020800c540750022410a583c499000384000c40b103048044040d456620300c01d01400348101c02d23a0020340f400341d80c4503a44500c00f41700407501b156155510b02d00032519a81d500e180c4070f1814001d800019002c00380405020031078a40b040c500c018401003004841a41c2d500c46c4c1500d803107003400c4d40d02025035241e107016000e58038459000340303a010002140d42d0003500403140146100700000e0b03909025410502e00a101c02c00305d12040440054403c03c018000301e450403214241c0d84415041102d42c1c035503039031203520600c04084004030783c9a464100c100401d002e901d400f081c071020b0a001c1c0c0c600c1c21000000403860940e043d815841404004500d00c2002102407207002400805201900c029504141005000754802c40c22080410345642c1c0c1600a54041001c00308149030f6901c3c1042620f05041c0103581da14413560a50704031058003450400c01c50b8800c946c45950a10407000840d0902c0245400d90604500 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 422924226 1250 422922976 422923013
    0x270c091404141b040b03070809070b04030201051b0a05070308130504060b0901110f01020a03060e130b18010f0e3405130b030f2b0c02190503060c07 65
    0x80002c11000c0314246100310b500080051414034981c0701003a0701c4012070059030321100e0242c001004200505403c1400c0c940304140389010b5804081c0c54064440a60140e808060700040f01401604100c100e55100c0141c400480c20848405c0121596140c0ca080e6450300f0440c0d019101040400d050798084224602608086605200c140e0800382c207225a4040c00ca00a0b040185e20480585581d40074440e00380d1201211000b07641e40c42024401401130404c91041420082540c400a0410511001e40c60b10040e80808110560388070319805000c000004844454195130310080145000054464407101403410005428103c0b40c031400c1205034001c0320b10004d04001c1485078ad81c04200303e01707455410b4900072942d410207110182c01003402441d0b0110003640501c124685585c1d540000504110814403c01e075660140d400030b541165564000300b00301c804121101021001840c042030749150b581614403091a42e1545d03080020b28000c0306480c10b040c0190005203410500c041580e1081107081e6 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 422925476 1250 422924226 422924231
    0xf030b030a0f0615031a0f15040c021f050a0e01090c030f0602130b07110109051005030604140f040611041a030405161e0801090309270c091404 63
    0x568004281c840165860040c80528008540c1c801c03c9040c4d40140c0d0030041c4003c2d0101c00d10780780e06c0c003040e0401c642042401803004001c0000c14003030390501128400c1180016402c00b07561030340140806807401c4007032501035003d04030000480780c1200780410b070800c142032030224044c208240d9034401c41e418442c403690365034100841c84010035514400e80040704d030b001c080341034004d20b9420840000d00480604030141e40328401c001811190800181040c40d0040c1c5801c56040c101c5801034402604a03c201500030f5152060058614040c00255901850140020505115a0389520308504045442a00d0000c2403000e200510403244560444004154103403403070981080c070340c101c503280c1c00900a140c510000000030704010007407066100150354a03200301465611140c101d04018117610803040f1844040b0400221003105001e803a180a406071200341c004ea0524071082103c40080c840340340a0340d0030081031851540c5034401c421910000d5518540d15a05040000d0800003000580d28840c50 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 422926726 1250 422925476 422925491
    0x60b030304030b010324020a1e08041e0f020901080d02070f06080c070201030914010506041505100e011e021609020a1215030b042303030c091c050613030f03 69
    0xc2d40f81050030305694124540d0050314203a0910f0030000c01c8500101701846002123048182c458000c1d0904040c82100c0303001d1111051000700480d80d545085070050030300c0b24001c400b000b1300c1000030429480240100903001070100141c000c03d4101d0420307803109402c0e07032004100c403d20039030602141014000806400c0d10840c5080740c000d000c1e41d8013504900c0450300001d050021a030003588090781180d405400c7d0304400c0344500b20107000380001c40342c4500503810b00c2d801524bc1101c2e03107050819604024000000e8503002c1c1c1040302c1e16503a0200e942d0601c00e05002c0907161200e56030020f50880100e60040000c1605100318107a40c84890303102c41101d0740140500311305283c00c0407181c0c03c64425001c0010b00a0a0a0341174844100c00740d1014088542e240c091009100c1d0360705800394a103034551004203100852010440e9203210441d1200c1007100184102c034140d103048413102d03000f009140208803003503d00b034039881d04060050391140710100c2402c20441c10035030019114440c0a070351303040421256 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 422927976 1250 422926726 422926733
    0x1060801061706040c0e041a010f020f1005060409170711010f020604020123040602030301051819051b12100915030308040c091b0212130b0a120c020109060b03030403 73
    0x21802a001d64413640d255556110418802e07074000c4d08032040140180154004401110707070024055440c2400519050400c07812140005043c0d0310040d20807005108030384410b581c1c14000d260103065546c4c096251583c5201050514580d05840342c55a1003855a800307082c68414011902640356605001200000c1c8613070350340126510703520580a0911240504480040d405034919081c078030024032902190205034035600001a6061350b10035a0052982d2801020400380d4000c201c3d0078160320750241080211140341e9030001c0350003e01070070294000c0940f030911400281c0205109844000c801c40070000084044a8800000c0c20840030401440d00d86440d4101080844d000140138030160f030003c20100706010203031900519040204101c80d81c0585040c003140301d001d507194001446900715981c40c1501681c1101c100c0301403040350510891402649852640160600d40184072101d0100c10311103546014008041800341c1c00000c070101646000c100301d540c13141e05140245d00030300c41807000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 422929226 1250 422927976 422928017
    0x307050d081f050111010b060412020102060c0415050a02120a0c0303050f160507210908070b0307020d0e01020c0a03030503010f120f02061b0a05010515041802150405060c060106080106 81
    0x1501d50030305e400f402140c000c0783d41c0d902414000300d00fa07401c480300140008000c000c000c0720f40a01c174400d07801d441030307a1500c03101113409008034003c2581e00281c04070900d10403030096000303200c0d12009006640c0c68440107014100c483d000a000c507008116108041d0301010b91520400ea48854400007140707a60412024180300154201c09800500c0b5002820006001121407181101e9007800c464103071824070382c04010880c20051203114120b10600c000403900c64040f209a912864541e4001c0603042e030a0318084031002c850030086810741c0644a0442ca1989030b40c0c200e0000355000e40c907140d0383d0394503020401c0184102c40c0e000410400301e24805100040882d2000003945030102d910507125420004210091541c078110324041e0310590b01d0480c10020190006441a5a2559101c0d60001400184001c0d203c4c0740035498800d621140c0c0038001484c1820300c0616040c585408030317007800d880300d001c00c0c0c96030301026078000107030f010308010012035a00c0b80b4103501505a516020300d803544180c20a690 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 422930476 1250 422929226 422929229
    0x504110c0604020f2103070b09030a0c0f080409050f0601020c060a0203092b030809060601080c0703030c09050301020403230703080d1a06030c0a080f01150806120307050d081f 77
    0x85101444d009010b07075510962101d0440c01c0c1050950300340b51840401a6a075480380800300d50b403074848400105251000300503160f020b842034071107000c2c10801d60740b000c21a04142c40c0c200d074500021301010442a60602c0342900c5040d2141a00d030300c90078100c2c0060f1030070300140001340c03194604100200a00b0380c084299400d8440c141c0e0b00d1241507014a0481c3c100d0042028040001d9001c4e130800d005065220503545c2c0110301d40b5080d240c0d01d4071024011181d5080840c1d803100c007500108644070000f407095010824884440c030703140c20200d8031480002c1c2603900c81d80c003e65880f00041c00e8042920503100c2c01d042d002c03013800010990189503139609c002c00e0040b180e030b0b012500c0d42c0c1d08052260240c0502d1004400320002c0529507246420026a907036a044054048001009080080d030200e0090780c00c3c0d0b05950020218401d1010091011520128014061074100d04560800700b90041e0400280c18003901c10b0b40a800d83c041c503204010b040407402042015a06551038480400c402603106000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 422931726 1250 422930476 422930479
    0xf060f120a061208030a06051009060c0c090c020c01030516020703080d0b0402120f09210c070b0a170906040309030308061903141902060417190302070504110c060402 73
    0x12107a03035072055400003820168048400342c052407036030908000030750340103501c12110f4410411805840364280000c20540c1440d00c0d0114081c0c480500456005600451850b0b22604c0340c480408d0f1164181ca065400129418016070b10001c030295041d81c050040c035510900c406d58900d80f0500c1e6060080d5654a2440040c055600000302c40031810b0702508250020480504190b581d44103019400c90340b0441220091900f46100e408160041c0000c01c0307003d40700c103010310125407040c0504c035a6a0b0944c41002c64642c107108001d030000f9254040d1000e07210611403030722941c0030044030900b02c3d42c501c0300c01000c50405401240400c80082e0300f0090b42019079400d8036207490150b4600d0042040b00d8181c03c3d244004604441001040041001400345100c107007409541912042c82c81c0c030080300040b5a802035200000380401d100030701100e5a030a004c42691011107000c9410740100c01407542c20588180c006030024402403100741442c2c0129940005c0b4642d40514100791810b0481c0c27500000f80009 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 422932976 1250 422931726 422931757
    0x110a050d081e1003020f120a0b0a021209030903061015050a030b0d0501060801060b090105041701111603081005060a0e0103020d060803030108011503050a030507021804030804020f060f 81
    0x940302d40a200700c51038510b40d804103030042810035003c04100b4103076a10080707126040070302250600342881c0000c150b200ca6140300034101c0742d1696a8025a402004084800142d8280404070006103000146070043c9034150156035601100401d01d03042c488014805070318211404010030524068141e002144c5a99140042e00c400e107844085003c0c0803107100a5600007001e041c041c041c0101940700c45d0449000314001c00c03e03e96903011118190080c2c2c500d5601050013440308000400c251103124510702c3c0703c0c00002038008070005c1e009140b908030b04070000c90141c00b203002d8030803d500180c0c90307500074004074200e480440c5010f00051161150842c0c8800b0842c030a940090a0713402501a1801140344510500686840340303003c9540707420910591406600300100c520302111403000400c203072500400584102c0c44103890684031a444200304a0300f00c040c05010000040d25004064012446a0b070307402140d041500412103800345026900f4030400041040b503034100c4041089801009402040 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 422934226 1250 422932976 422932981
    0x4030605070e090114040606031b0e0d0b07050d0c08010308090d0c05030d02240c0a0503220c0311040c08160c050708011d01020a0909020d1b02060106110a050d08 71
    0x2ca4021850a0500d0f41140d114800071a9540384e5042d040c28004054400b04200e0399030300360450660703201c042041c0c51000000f40c85a601d910901e00c0f070094010203005002803003190b039a0f1661603542114036600091000c20b031000d806409008041103a03c0c1403411400550454440d0035481c8a4545d28501c1010b1140d41030b41080b03201c02c07848005100003015918611003800c00a51201c050403001c00d0020b6204d1a10350001c5000c60300d00b030281004214990401417003480c25240d41e07002802c08071020035058518400300440d0840d59080701d10841d1503014551a501d0181c840c00100d2903680d01c40c82c20500f031040b119511894030b640c007642c1c03050480c1c178140c4212400d40e16100701c060301808601030f405010444000540041c81c2c0b0300d0008030300130b500e02050500f0a00302d000e410307851400180525410005801c40d07802619541e681d04000142240c0c01000e0400d0440018400714056044040108001c42e0400c1140358030301300020142c00c242d5100d82d102c03510703100e0b165040700a00c02100702 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 422935476 1250 422934226 422934241
    0x907061101090b0f060112050c03011a0409020f0d0608030a1238030607020a0503070b0c0d0c0305010905060406050307090f0e0703142a0f0f0402040b0909160504030605 74
    0x2900d84160400460f51642c10100e5000e031402e601160010301185648503007552240045c440c05100d100e8007441141164282682e40750002c80b0710304007104c0c00c0818800460101c009100411001c0d08252140d50303106103401545054540b2544868a1500706215000c41c07960031541d1a101144825400980905240e008034165141e00401e40070044500301400c1202203800c28151036800214110307011640c035140203e030b1300e00301c480004010b0f0b00709118240000e04020792f0580c01421555055040483e030940035400c8851410200001940745c80c01084004002d100300398010340103441c248007180c01c0402003030340e8560500c40d0f12a0190788151700f01c00305005034490035020140e10b096400035652800c1c20588500e900411423107500030480d0401048040341e544c203281041603105c0045025001040100c404040824035800041d010041a040c1e9941d2008101401440d0003654607070b40303410240020140010b088040000308908141c0f00d054200096800300c07a4480b0021650740d86109 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 422936726 1250 422935476 422935481
    0x206061201020d06061709010e0d0e01031107050a0b0108010e0d0e0a03020405240418060e1219200703170c010203070323070e19080f0708070e0907061101 68
    0x1401c4101e05031070500007051059110446c003421100402c03010a1035100e68241500300c4203940ea5000450f07200c030324040c3e080d6000f41012210b12405040020300f62a1ba03148000f00c59001c0802200c0c43d0b00005280c404000b29003980d5405003c060008102158400c107000d03580d40c600c060300505200d80d5a03c51185950350341500400366a02070810704c00c41c100842034041241e20300812142c45040c1000c11001c5050500c254040340c01c0340d10700c4644114240d207500c0028600e500c0403000ca4000c031440c80c12800301ca2170040035030040706503401c04c1070400701c90b00404102000c0d5002600c04680c0780040070000c0000742e6041a207400030400c1d82844044001260284683c80011009500100800c01401c2e00b5034040075103183c802c6420800403600e5030030240c042004881000100d118021251100e003001c2c0803031000c0544200c41070302d901d519508181e2900200c0180700d044c6500101060000c603005201a100402e03000503101c1181c2400b0f050543c46000b14010041040510a40400b0041094 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 422937976 1250 422936726 422936737
    0x9050f07031b15090306021b0d0906020d05041203300917160b270c10090608060616021f030e0f0a0602090406050306090319030606020606120102 64
    0x501150011907a91414880042550b00e1403003416442c050001590321444403c9406441c06950f4005658250b41e608002074020300305818000907500080c8d0180d803070030001d404802c0c2d1982c03254078102d80740c082d009290101c3c0300c440ba0108002030100300400484044025001ea900d824004034424943c510030201ca03186a00351030705a0407500c0c0301540040f040d8448480079005420902250321030719192010f134416591140a0350040303640d14404600c100103481d801000c28000b1141082020714800c4040e0000312840360160042003014501d850210030380b03031103408a418103a1a107450028090b0100000400d2140103000c0010b19006e000c0749000041f01c031581c0100701200940f40019401d100c014624031140220703181400100c154140062000c440c955864020003844c6980d507982c0d0065000300000e04d422076202c4401080c5070350103000103032081481c0e10003140c90b00604544000507450040002007414074111003802040d50106406500034020340f501d010b812000800380c0d0081c0b00e0f0307 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 422939226 1250 422937976 422938003
    0xf0603090f030a030609060b070f0f03030b0a090b040605190314030d0204061106061f03110415020a050606010305060a05270a0b01110d080612010e0a080712090302030601090905 78
    0x2807042c00144c06900100544800c40001c0040b20344034030310190030f4450f8440c0941b00c418403110a00018450084801030607200b4500030840c10982d8000c111144076580085500548070300c40b4a03120700b01441464000c1000300d03907480228203103128120050301a80400b510300550078291402140082044800c04200030408543c0c450381d40d80000c01050410100000784e0041d0b1011039000d15110341c2a500c0104c1d02000c01400442020303041d40100710300b0035212014801404000341841803a9400c03e0048000c0d0041c08003c40c0b80d14080703060600003803c00d41030601c0c0805109107900d40c5d241c49025140d09480f3368040700c40300c1c40c00030ac80c2c22141a01c230707200051032020045060007940019003015400e0300c03611150305501505946841c14200000300164802c400101d091602408040d13020022800006898140c04642e5007021000c50069640d100f0025601c420810804548001c0850301d10b005c20b1072a055a000070f072280018410f5603061910340441c4414000184080b9861154 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 422940476 1250 422939226 422939233
    0x30f0a090506270609030d0c020c030f01090b07031506080601020109120201150501021506040203061c050106030212010b010f05090418110102071d130f1b0f05030106050f0603090f 79
    0x20a0f500020004100d9084400201240580525141e00005985004048542c0039605044140100200420421050308110b00c41c0c07201d605c825071020b21200c00300c0f205210010a0004950030700d00c4e0705a4001d840502050324040768400742c0558110701805907001740c42c200d07455444000040b0302411007030b400034008402e409402042c00b0780551004e012800c000504000460f034031801661110102d082c3d940c6030300c1001c00000c42c5880c0aa0045600000040159405110b0300710603120060501ca011140380c2c2d9a00c10610641c500704035110316018100000303026a40500340000c003a0401030700c8031402d20901150713030015139589401451900844052500040e0032a0038051401621142098054040c2010100328825000011014410002d80280c85a21411548401200b01d00d80543e40305410b0204c2200181d001107080201c4100345128446642c18480b204803544070941c0b18501c6689002070401194030780c0c0c6000001d00400312a40c503200c1c3e82c2c1c52120340c00d00b4842c2011005c10b01 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 422941726 1250 422940476 422940481
    0xc0803070306030623090111030109050c0705060907050f040b0f0d14030c060115230d1407020606010216080703061e02191704030e040903121107050c15030f0a090506 73
    0x2000c1d048030f12517610441d042d480e454444031302150883c1c4010302010aa100104014800c290301c1d900107541142a00c105145004941e40700c50b420304405460100c401c0c8c00a503000c10440c03070005083e4005010450341006512240d0001580041000d48194028596046805c040c4411000401000f0303001c001940c6c1c3d50366080c0d00c2d40d030300d8010034040ca071294680a00c0e503003102c91050b09000003500600701100c05103a40340b409502c0a41001c40d14449040d111095044492840c040030bc7c051000c9800404580c14080000b90508003030b403501c0c0840101c40101000701c1e4000083c00d00440e6086000002d142150400218204002c030710050503903400010f50781c2500e00d0b4458a10310409480e40d60035281c600440d81d0340b9034000b041d00d0280024103225000811450107030f2012042c00c4c401d08190048020315525101036507100c01059503448000708030b4209228051101c105485402c40f0f101441001c00b605140c2c507400050003000301c401c4900009400046903034001c400881e0850101d03030051 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 422942976 1250 422941726 422941751
    0x316091a1005070b010f0302100c1407060e033a12050c070b0c090109062d0f0306091514061c06180b030d08100e01031406090d0c08030703060306 64
    0x10f5200190403130704a0041c01c00044d1007000c080c0c103c1c050b80d0b80108035031100444540115400c0a0303000c020b4403903005030040d100c0560070806c1460300416031030322405085035503c0f00b01402c08041217545100c1d1451043c06101c090808820b0390850781d801c910200389030034014400c907600c03028100320f9403400c1d10740014040086031820152452031312648440105550f01501c500e060302030b603c0c0725400308840039001d00210340250202c00c4401990100d02e0381da041a5202d070655251806902c07404103c0b11540c101a803603150250501500b5280e400b803048240c601e403101120b50300307440b072165005000710314a0850f940d030078102c1c3c4400c02c03401d8035005408448480580188268410000c11003034103102040c03013200601070210645c0008020307200034403840000380d500e1940140710b90b951100b04400819058252118035001e14059044c1d190b541c81d100540c0da14104e0302901c40820340d800503180d4268254822015440140c2c0101c074144c40352540300059028004d10340000b01594181070525295 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 422944226 1250 422942976 422942987
    0x307061d060903040b0d091406040b01060f45060504080d0905010203091e060703022419020706020d0203090a05010f0b1302180d03080f060316091a10 66
    0x28101a01030700c031541c9618580503524801c0780300b61320046006000303d00d18000701da8403007001c0600552220079020f200544440c140b00c42110100c441c401c03448010702c6059440010110000c0607428031542e00e01074030340200c14140d4441d5074421541100c0100140b25041200e00c504070301d10368000000300c9a00d451014200d07400c94019500d0314407641344109003980c42a840c5030215901070f0050b51505503050140f0003003405001040740b4860b4003070705a507131584a110082441034066409090719115240c4180d220201500300c0c604810858402c0c00305964940f600e00d0700d890440d000040c0e8036004e41c03401b50080e014204013059014404400c018038604045040c0301280d1240c00200200300490100300c040b25070547c00c0b20b0300f2000710782c0801c1c030030f03c0d5940c02010300e900d007100f00b803d6140d160380020710540744824080b40002c051805100c0c9203149580b045070080d0085010348800302c5203410003c0d4102c5540703d810981e80e110359807007108690345c1903505040c20001d843c6580750300402c03001801 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 422945476 1250 422944226 422944271
    0xa06060807140d0b01050108131205130812040e04050715120c03270206040312090f080f030304020108130f0302010e160b040509060a270614030c01030509030706 71
    0x2c045816060b55409440c1042210078400d6202c03410301c0141e42024011941190020710340e000082c000c18074070003c14030a1035180c01c0300e00950388036660b80c8000d40c01200d04056076800362030303279030300034003141061980e4035050b00c058a010700071064a80e40c860500a180c09140d5004000e601e50742049200c8c181d602080c045030704c4a0301c4609000c46028802d04804551203403a1201e091442081001c0c50502c01c0e01211510b00d00040511342800d86070340b520440c107188038034041c02041c007245041061078241c407c010005c01901001d0003c040415880c19103d10000b0002810400c8070782c0040d90341c15440c40d1200380d041d00845420094117843c900a8020038611590311400c0c8540d03800d10584842500454050760108500c0e107040c0340c41d08080c8000e480000d40000e9014181d001c0100d8020910001001040e60309040303090400101c481c041c00f02c0c0c0d2260040058011510a6180540c40020711800700005c02e1800095503503807056079034118092608010801818250f0b0490140b11040b1000f0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 422946726 1250 422945476 422945489
    0x304031b050c0906100905010509150d0e07050d050d3c0206160c0204020a0e1509010909090b06150c0109061406030604032703140a1704050307030809030a06060807 72
    0xa0030351900010020302d545c103900e40c0380000c1c0008030281710340e502c100c0190090580291001408028680781c0c800355800c080c04104800395503d0040b15040c00400c1502d0040100340c42d0710384210000e45070140c0340d0101041724000d1045410500302001001d2800340701c1806240036041010609168030307100d218440c84080010710508003c00e0b091340700e50b01c036100d4410458031411610b0350a82e0a00002c1d4204036104030a1080f07079841c1c1041078481001411250549a407030b0741e0b13101c9403c000074100d181e0b15084071401a2601424200141d05e81c14031641186c021100f04000c19500004010240b1403805641c0d003a501b055288c000700310f0142c12840581211544181140c0c0d1001d003071558851045a001d00022500c9202c004224011050440640d045512000000e9100d0310350000401381c401204403242d0054076450140300c80000038103042e41182d4449441c0500d000d001030f81d1400f03e40000340c44a0340004502140f80d50400030000b00030b87c0200140007895440d0f03111070310707050540320341c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 422947976 1250 422946726 422946739
    0x150a20030c09060a03020d0614060d0e03040812040f060806090703181b0315020f070f03090b040b0301080607030507120e190b072a1707020307090219051c020304031b050c 75
    0x200714503000e41c1540c1c509c0350001e4052070070b00201004603030203489040040281800100000b140c0584107002a100c1080380702138080e40c80785001c2e0b46408003640c0e079104c10200001c0c1000c0c0304840d69000143c0d90800503524000c6000001d05000030720100c0c0c1c010300100320f100c2414441d90407e90a40489040324040c1c860200418110070707407541684a0a4450891400c08000c250006107407502c070400c0700b40c041d1030032540c41921a008450b955000f03800920044101000401813000e0400c0380560003940d46c40c080c0b000c2c0c01e001e50080d10310450030821016454441141110400041200960000a0040b4020043c4650a01c0600110151410800034000c2d20806616050015500041300303034403101080d1110941d103440c1d83c58082c0a04041e4a00001c200050250303404001c444007410314800010799401015041c08000c042c07002d2100140801405102011520035005800001d0001c80240c0c3d642c0c0d481c901100c030f5642400016003980180b5401d00c00307025000411040d100010b541c40b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 422949226 1250 422947976 422947979
    0x70302270a0b12120a050c07030f11040b01030e0c040c020f01060f06090e0c09040b06070b09150115140a0c0206040b0d11030402030d0f02010b0402040305150a20030c09060a03020d06 80
    0x758881407a004c0c00f440000040206603005c0344a0802002241120002d4492070f903225554a09440036000090380c9414520210550506d0f0038480c0d02e0b180c04013420308000b8103039400e8501d07032240e5000404602c6584c3d50401416154000d210381c0e4011501c810081004a40300c403145000c14010340106800034888440108060782c0c030a0235640550140c240301420041140d04000203403d25440303050304100c09012200001c0e0200100c0c0380a41807450240090003810500340c400207030140e1103030b041980708c910300712201e0343c201020091815501406544c1d40001c24001e441403d5000c030b0094000c000094009003100c96103001c0d004a0003100340c18010b80712014008540c1d40015203002c0c0d40354108216101045004200340d142d5031a40740008076081d81c504000030101d8109500684058000000d50074014846400c000e602400b202801c011000b60310308400030611a0010b0402071900000105003054148025502010402800c1603a22001000010040e400030b016001100d800c1190 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 422950476 1250 422949226 422949259
    0x18051005011509150509090411030d0206061003020c070506030f01030302010c02011e0519060b07020102070503060f07081302030a080c0f12091507020d0f0b0711070302270a0b 77
    0x10640d80030029580b603000250600c03c0d00c0d010000304e8080003051000c20481215182c8400c8641842a8080e0804001e1240014281410007146a0010381190480b00c1044619070310010040341d114800d140058880070441112442c0c000f190304519402a07011041040203000c90f081c00c0e050728400d5000b4001c41002000c140d09a0741c1c004401c60300510111000f0034040010750201da40301020058400410000540300003c03030b28560031458200304001400c20035541c04224181c010041940101840d150030100b031210301d00040d04020810940300d020036600130030b810f4030220841d0014140c0780d00126a00d040d035000d90150705240c03c103005411060000010100d1049214011300140c01d151001c18020000b4a640c12001c00c03041c05418800d0f60050303102e10030440142481000c83d583e000740c160070701e801d110900411007010803411903c3c00749080740114a05007103035810381c0c0c9101a809502c81c1008004075134621841c1c6455080c1c1081400c541c950040740c407610b801d41c0c202580d02e141c0740 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 422951726 1250 422950476 422950499
    0x2120f01051015140703030b130c0f05040b0f03090a060507050703030c020a0209041407031406070905120c010e15120718030b0112030e03060708041a060d060b041805100501 76
    0xb0854010504c9003e1001c13041d42640005c180b01c0d4420710340001c0350041000001d0303504540d258000151940c6461000c030700741d00030840c5c400c189407030300301141454600040d1080ca8803a4850100c00500040007007400769204100c90005a030348010244070700c1ca0314040c02041c5405c4410241e000030b0400c0a0146000c1c0041000a14140c016001c900150f543d0b07120441441c00303032004814a840740f014004082a1080460300c4545840c0002e07010b28203100300003d140c40f201d604580e2140100d20404440d151001501a4400d0001c1c2001e824031004000003d0f01140e1101c94821041c4001422025040d51740c428584a0200f0351100c143d100c0e0f916521100480e41808002c082c117900c24018040d02e82c818513111005071003031602d0a60840354501080c100308040c0c2d8410046a106400e001c100b01080744100002c400c5a101e00d02c0d58504600001c00c1e00e0045071001d40103690707961803d903a58031a5003090710340c4050f50740e00545514042c030b02240d841189402ca641d005140c24000708280c103e03103 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 422952976 1250 422951726 422951759
    0x60c0309050a1410111204021f0305090d08090a03080408070c090509010f0c051209030c1501080607031104032303030709031104020c0a0206030a060f090c021b061602120f010510 78
    0x100400d802e00c2440f900e0b5506606c2c000d4000da901460391a00d0280b0000ca0354040d22000b8507036640411641440c400043c68a03040481c0c100034401da034820465044000907141596030b4140c5894000c0c0e49880c1056030140c8035101010b4003211800e40003244070325841d000b440c02000a06c000304141e40b1811080d10464504400b0300c80003480c1040b45000e1040180c0e0455000750010003524980b1600403401d038a0501d0300750103c0c840ea4511b000401c90030b0820300c004d540c80f031081d080603c0090501c0f000c1c02c0700c42c810360000900402c001d62865001568240030014a82c0644040383d03520f0900680c0030309291762a00c0201e070124002c0d403046501d81080d00036961300c0c031170130030003071025140c41c0d800c0040d10b41000b13000b042d4456444100040e01100743c24082d0040c0440c620000307a43d00c112030001d0812609040c1c108602c402442910700035125001210101c400c12120032150000301d10001715401c1c0c11804025407407081d40c0754880c0d502419404036001d103407075001c404603d680d01c8589040501d0003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 422954226 1250 422952976 422953001
    0x90105040206041a040b07052506050345010b040902210a050304030c0302010806040c0906140405040f0f29040f14040308190b0d060c0309050a1410 65
    0x10700c4100031881307410302c41c0600e40505040079820301d83c49010780c007000e4101c8081907480364000c1641c00c0b601b0f20310254210052550701c142040c06030901c100030b4420700c40500001200052152100300c076222800300c0c84a11440708503108503103880300c905100e5090580d12202c6065190003038001c4185007078443c4207000c2d640a00103200d03d6507103420140444d8020078290b5454011100e0001c0003900c01c3c070042019522405075074140604500004281c0030b00140b2050080e460002c044001c1c50300100740c00115040e614044620f403542c0292400341e8042c030750040303030040d040012001016540303410400d0030064440040011800c3d10140218031404105d6403441c1100c0d8908400c0e490502ea0003100a0301c001020100c0d50b41c2003c014039160b240111000d40014401209000074003070307451240e1095005601c41444030104c00000554241c08580f0000c1556584c0d41d0030801441c000d8200c0444c541d00720081e118003031708504084005105078448100180500030000070700417498030800c00321900 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 422955476 1250 422954226 422954239
    0x314070f0618050909010617030322031d1302040603020c010b0604030c06052d07020915011b020d0b090a0606050303120c0702120106080a05070509060108040f060204121a0901050402 80
    0x3600f02448401038000d40b101c80725549903540810026140035000c108014024021070752440e00c0407055052088140c9118901c9000c0700c509408640c1c000d00d0200d141c6070504c0a60300c56030101d8001070703288042c2d6140c09222170001c9400542e854255014040744a8220007d00c60880400100a110701c55400024a47c0340003810500410384101c018040300d00031b9091401000e01e400c001182e04e10794101e1201161080042c0d203030110304201d4034103504180d01c40581c001603008800080d2400c81606034000d28041440e01ca034040d540c1d1034220202c451340202034070125003426041d0715140c2c2a540b60540380c882c1031000028244c2400000c03901c1d480080c0017054903e4a402c0c209070929484500240c0c1d100f105034107000790710b04081c400c02006112000007070480071024580641403200036070000b03228003400001c1043e01d03600b000300c80d0340c4a54080c8100301c8034122860100b00034040c6e03801440010060750758580400c0380720300400d445411500c0710500581da03081221401da60b01190300070b40054 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 422956726 1250 422955476 422955479
    0x9051506151303020a090507020d0306080303072a0605040b0702030408070e0c130905071115150d06090503041d060f040b040609020708181c08130314070f0618 70
    0x90005042820303880840b40d00030a96070f070000341000c900b613040044400c4d0b8440034080b070950100040f00b202e903180d050500115151402d0b448e00c07400001d004000b80240c005109402c08115440070403050219100d840c0c100031141030041c007c140894080380c08042c014040b5a0316800002601c084400300700040c00c00387e09000d915000d40c8070282015108a100344502c100b62a5500308000141080341c030f000032249810718004081640c615260805130b0480003006002c41c0c0130303545190b0f2100400c02014940504140452520b15440c3c1c0003401030341c60140c19408000020000304202c074000942c1460460f0103003400003041d141500c0007a44030b0030041c112480c0741010b40040d68070f0355008000051495691290a060741d003c0360084444800c0000c0030f403c021018101550300100c182d13041c800c0740454224880f62550b03030f090003900303854010a844003560094500c0c08042c40e80180144a143e0340c0c84051a9144564040c20020000c1c03c1c10215905100c1c4000d6030066654003800420715 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 422957976 1250 422956726 422956759
    0x203070506010603110c150f0c070f0f020f0910060f05030702212a0106080f07030b0c0702131506020c03030f130b07030203251518050d0309051506 65
    0x1010400c552085c220414017603c100709505000400c0d11002c80c031000f038654948203c0c02e070394001005142c1c40c1312030828070511010858110217000034952240325403084410078000182180c4041d406558090980c500300090441059032000481d036030ba480301820f03e00c40b84401da51501045078040c006a01248103e540305840188894070710030190708140c507042010b50345a107401da6041c01010b05210aa1400c0701109007441410018002003024000e080590f51045840da16640300c06841886008049074104c0c880e101154407503a4000c0c0341110a140d44081d000180403107800c0e42414210b09080003541c58000b16403c00001e10050145184c00c141079403500058000d0032844641c0d40e2405408a1660f5154000b00748440c082e400445e218001b44480540948150501444080c016549900041c80d101c20403807400c00a010b010650040e16580000c140e040e05501529920840d1030250100741c165205048440c0988107840156841c9103030101403410603501550444150308800280 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 422959226 1250 422957976 422957981
    0xe031908071b140f040b0316050a0f0f06081806010e04020108100305030301150e030a0503071b1404020a050903060c030a0b01020102070f0f02370e060f100e120a030f0203070506010603 81
    0x4e03c000800010f020561580460f01d40342d102d0420751200b0b81420400e11003032500881c0580140104004001c0a605204500d0701c120b04602c00d50040c44a990080703042c807003c0d400500e08c020494012070f00a503a60300881111694166802d0707000c140c03624081026502c0703c00401c0d0503660032200540c5140d2070605902542014812241d0030001402c0307078540b8965040c05000125070184008645683c11402d00114003148041d101200d1080018204144140c51004082d98102242d00507100c0b40c00c40070039650b92103030780503a55040c02400200f0945048a0340a140146d80350801000400d0002006908070f10480101928043c0c10103c5540001c451110080e64280b005c0d1550703220740d12000700422207518400410080310f5644e0f101c000361501c600f41d4500281740001c00395030107081c16008559003d240b000340c54024000701c2e4a101c03a0500600904100c1132018003000105440c00d00320540301e9644803001c40c0081c82884101018520005c1903e00700783d00f000290200380d203032040c141c00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 422960476 1250 422959226 422959249
    0xb100e0906011b05010905010b0a12033903020f0a0302060a1107240c0f050904050901060b0d0228050d05060312070501050f01060801060f0e031908071b14 68
    0x4115040395107002002078035076101c00c3c0074450800461028400c0ca00103007940c4400c13629038000c0e803c50008209840680340c04009540d01410b1100c507034800e14051082c403041504520300c501c03c40000f8607908852012882c9103040c000e90a40307244091007404141c030794060301d0703010b801a808074010448440a591000020401012a0b0f6180034039903134030030580c280e02c00e48440701c00d48801c031400009612409413001303590b102e1030f002c1d50324520f158000d480b034080d40c40102e001c6c42c0d584c4c0000b40c8040c4e0951120002d000084403480d151013503001810069800141500321030300460484034a000c04850820126154945420703042c0030300c003400c210041c440140302503407601c030b041c0c08080d00c10103210050a6850181e000422546007801c8400300544041c1e0000c000c001c043c0d8010849540e110b086003100e0011460a02d4050b00402c2c000792030203c058042900100c240310a80d0100002c8800900080d0b12031000c074420a45022411004500380e0310070b200348014508200390f00c40c90f15911448 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 422961726 1250 422960476 422960479
    0x5060f04080f06010f120210110f120409140105090612100c05040302040506120d0f0e101106010b0304170a022a1809190312020c0601090b100e0906 65
    0x182860303501c116091826030988030303403030282e0000300050040302200a0003c01030084030044150742c0401d9400f059201b62072000c0b0108102e034541e0b000f558200207010b03603507002048000700c0d010400c02c81c400f0b1031154010f02c1041130a40c50003031900504c1e20144038ee00c1c108c40b401132a5a0003551484240700740c902c0003500040850041c1d00d200349214126108512014071903503151510740d402c1d0710501045400151555102e500b80c901001d06070f51000881d20801803d0740703050810744824200a5031010f40440000341d1000e07840b28500c5002d03070f0000e03c1e102c0b21010740c0120341281c1d03690b010007080c07844140e9001e807801000101031101410301000601c400c0005204031044103109a14030585207030300b0503400302c6110036851166440d2030141c0f48019a04030118980719141014407240b50341340401403160001c82d1030400240141030259801c110180701540065503151005440141c0b940c40900504194504e0705003110000e0a0039001c00c0c9a01c2c0c1c164a801c10032000300404c00070051402055603 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 422962976 1250 422961726 422961757
    0x1140102070e04080c150c07060c030b10050903070803040b0a0219030f051e0c0c0a06020d0509041a10030603060c11101509150f050111030f030c1303110f030303010605040506 77
    0x20120b4228101c68644114100c10529403548c45901d05001aa83c107401285c0c2054100302c0300b84110703510200c5011074600a810300c940e0310381c490400700742030070b546510030506408041400580c0340502001080404110760a0703a0074084410f030f10043d2640340d00360290000c1d044103504c03000580614001c0001d4001c104449064502000b8018056800400c406407a50003250b80d80c0000d003408520180686568006000c00034294480100140039020720300303200796251202207207910818281006003a5002e03000c2c2070108003a0300d020b40078100078031080700c80e0362400e0001100d683c401c100c07802c88690044050901154002d20280141401d0751000d0b41e07130150150001800300c00c4d8452507410006d0020505112445c09103840c134408001e902060600c030301080e5070012f4001c00301c1118201034556100d01d807a629400342440903070084800140200135000350100a20245071155031090a0880c0e074041c440c04c1690626403680000c2c805c0d0008140107010038403031490700601a00d204051103004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 422964226 1250 422962976 422962993
    0xe1803070308270c04050903030118090212060c07110306060105160203070f09061701020f1207021005040602180414060f130212070f03062418090501140102070e04080c 74
    0x81110181045000f02e01030780c4030841e500304074241402030301d40c8200038a0103103003107600d03200b02c0200f9040c4d0903070001a0386584100139021544c0740301d81e00300311502a00c03c4450a260a9a04440c15030007808141c540d00e100080c6501c1c07904d03000600521880341070b91110b00f42100c0c1400121003403125101245d0601a08501040080451501c600240015140410928540a60340480e1002c0c41e90409030b50740104170f03500b0300c4240203040360f10f0401c41c101040101c0c1d4512000700c3c2010200310680348010700340b4090000348040c3d83c0262002140d00c1f62050302e0341c0440000c00040304c0007140070a10700d442140005803e84be1095000326144009400004401d10050b0410126841a0307003000c02450410103201000d94021f0240c2c000c60300a0504001c0c840c20401051035000c020302240403044603214034840c07001d116820004d4061407903c0c0c922a22505c41c407055001d002c0900844419203801c0c0301ca0314940d88000303440411150404441a015284c07500c13060501d900560100c0384512030504c1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 422965476 1250 422964226 422964271
    0x60a0909120c2f040c020111070f05031e0406030501060201090b0604050a140a0905010c050c0318010c02040e0a05010f140c03070201090b10060e0d080a1101150b040e1803070308 78
    0x6400030b400380f00e03200d103583e0200710504204c100c1d01e04500203421a8035022000030360031040c40855904075081003000b0141c0e021840e00e24a14401c1040031300b40401254080300d191010500544282c48044e10240b0843c1e0722a00300300d080390341580002e0100c0c00e01ca4007046003803d160303000a03044400703200d0220720401c81c002815251602940c7d00200b00f0754440c82c07041402030038807a200407a0090321b03015103002030079a00a6601e00440c0c10121400c24104031441942c1e0290000b080380d10f5000c0c006101c81d011001415032144400c4d00306990035424070404080c411a10f05c00e1404c0010351310404030340b60729100703581100358000a00000035036582e0300400c0085400b00c036015100d00c180c50f40488006050a900801d0341120004207402962020f5a000004400c50141d841034401864400c1090b00d0150328036000d030005c0d0600b010260400440440d01071110002442681c002c0032162091f034032600b1200014201c80154240341e07807c288900c800091040d117031030386c0003d1000601860701c1d52114 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 422966726 1250 422965476 422965523
    0xa0e0d031d030a2703030203030c0c011409010e0601090203070c17070206031006140f0712121b0305011403030405090c0c0d0f020f060709210b090303060a0909120c 72
    0x940c150041031301191118080000301e41c4031004940724012952a0b6855907a020b543c030f010140242411680102d9907031001c40c801d40c0400c100d0b1950208454850a140006a008181e100250304540c02400000b1800c00340c10b0003164040c107000c0e9609080040c1b240c0b24a00041d0b60b0381d00800700170b00108420f0b00942d4460001c2c40c002d50000090141d058038204c1c000c1c0c61000700c02d0742452142000d010030514694100c00b40d4050300e070041850002141c2c4d408007100c400140c0c9244620261405004124009a42c00b08501903180c503102000540d0b2981d85203020079101255503a81548208070510030342c1442c14030307260001b60449045082a042e00542410140e10300541310000d5080007400c1d0840b5810031800328004090320182c07250f0b00703040f000200600c21600a00c545486901e0307040c0c004041400d08025030310380040b203940050610300e4005860b0ba10613206140702c1d44034403202040141c1c40744101000c5035409080050056000d035015109512128015640b503805110300750480030307901 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 422967976 1250 422966726 422966737
    0x60f0204060504240507080304020111010e0f0c034b0102030402130513032102210105010f1710030203011418150604150f030b010e0a0e0d031d03 64
    0x3510390036203c5040401030488615401e10481100c0c03005010104500d070090704071440716421000b40c903075039951030006070f5410704010a007405640c41c1c10b298900c00e21012550041c450070b503200340c1e10f1503241e0004065075400303c08032050200044a800c0440821000800031444601000410b41d24411300651701340866201484241030350000100030841c50012a002e910410a0030100000d040456920b5244140c62400805010b86081c11039152010310301e9004000280740820b55036942c1803030302c10305101c11049211000c1c000c1c41703002040c0c560091a81540d0609190f540c586030030407844500b51040c6002d001950b0006402c0343c04400750310b080c0990b401201042200c0440d5041800b5015042c1c0c107030004c4055140c0158000801d0840c2d0b500d600b0760000300440c0d003c103003070b140c580640e00c2c1c40c1056881040002c031290380000030004030720005812074036400c0d4420307295681c0d09286002d42e050281ca43c21036400c03a840c0a20440e0003540151400c0c00654141d182440c070b14510300d40303568481e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 422969226 1250 422967976 422967989
    0x30e0a05030c031c0215011206110705102d06052707030b010909020c031801140d110d020c06011d011202190f12061b0207030b13050a031205160207060507060f0204 72
    0x230104141c00b0300c03041d805039040752140000301d50302d003614544030f072a150322005084032151030301c0300d40c801030840b120000301c00c400d0725000c40708184014400c001c078003d1156125040c090f10b040b01d0100250005100001d924102d052544130846e941c1a000714010003030346107c81d0500000580124442c011071000e84100603182c070045a070b46040f110040170002c488440075042051036203460a1921541e0305956211400079004503400082d005054802e0068547d80310b521440820380e00020b900000b01039040f50603000500d440c04000c90f02c050000503090244000c080d807044012001400c0007c040d400b40350251010140b070503140c0c044000b862076141d11a1044d2000c201440d428881d00e485120300c6070400c85c00c445001171039540069160716191102404440c1c44500090201d1400010714075916801410f541c2040c05524018001540722465840c07558504000641d0004100c4a5a4540d0300190002c2507a45e2915200310358aa0203d20122107031604c2e5803c0307009040707070350000c0d0010b00741 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 422970476 1250 422969226 422969249
    0x501140c01020f0d0e012d0209040204080d0203130e01120f0201050702092a070b0115050d0507050a0318030e09070c052b080f0c07060b0607030e0a05030c031c021501 73
    0x5e0383c220150946000d5000030500c0050304070a00040e03a100382044070420401e44000d610b034500400041c00034080d5620100c500d004010902d074245a011001b0b0001003080e40240c46020740b14680058414000d0190303c01501e18031080350b010070201c21038844118070500d091490800c0e15804034a40c52020340307100d081580240070150440c0c0d02c00c2200c80412140c800b6241c10030019803980803000350306200d4400401802d2820002251040341100ea90100e03180040c0044d05040000030400e03445030707400d040001c0c64041101c4000c40620031508401d0342681d2405400d402e00320410041ca400a010282440303041e504c0a400a0300c14080104031170b040f90b003880c51000c0c601d110b040c66860030608100402c2415010001030f890748490043d049055101030a4691480f450000000c1284000c1c10340d0042e008075800e420113500c2050140c0208081d240030716096907a009040d41d88a20300e0301994581c100080a9803155000c1104051600072441180c2c002401d5501000400d00280c100029091 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 422971726 1250 422970476 422970491
    0x712180b090d08280f0c020d14031803010c0c0f12030e010c110c010503010501090b07152c0303010f0506070c030206041e0e2e080d050705160501140c01020f0d 70
    0x1990260181088118249103070302e17400700c0c18014a01d09146000a00c03401d50a01c0794014024408411005540e0000450380d0311010811860a2609800000e81c4a0b40c2000801d075400f80c403502c16680503541c86400c01d11a8410340d1b407801c01800864800c01d040603940d9444102005003401141c070006541e4480c0f590b0703d03e2540e0404d050610f600a983e05104c8108010003c41e648000040300b2200c3e01c0d60440c0c2c4421540c44c010211807442010950110b0520351484803414541e08603000744a40c460740700300c402c280e41450584a000900c030384140c400c1b00500400c00e07030900800508480c0c2c0304a01c282ca0003922640003e48681094001d680350111503001215140301380c21000c1c010b04003410f5240701c545800721403840800389000c0074182c11840c408800307c2d041c41c06407460015100040c140c45070461006802405074028031002e450f607200e8a000052604114080d400c01e565043c9d565204014000d04803c0450b0301c2680764640c259820443c04005200350005828400d500c0701001c0307500e9 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 422972976 1250 422971726 422971777
    0x3070b0409150503120a030207020303120601080a06081002070611040306060314060903070212031e190306141c060519052410020c0a0b0712180b090d08 67
    0xc900c004602c0c1c001c210b6150060146640000703a5201c2c1c03a2000030916a03c40291381c04030068024000001c1d0507200202c0e01250791a00076079610322a400c00c1c4e950000d10b940d0010710728143d0302c1d9403143c410340c1d401500404c40c81c451160003d20815001e201c000c119500e039454202c10990080d4802da551640e600d40c280104100711640e117070603840160082030503040500d01c3ea609c038481e0300d07002407260103048103035040c0142c140700392087e1903100c116082d0b004074a901c41036119132000440580510b00104a005928020b104150036640107601e1400460260b100380501400e0a01100134a000c0c041c120200080c42c41c0186842440c4007003030418400013104006e01682c0014000314103243c0c42d51350706590b0000c0c514500000d0303481115040d043c1c2c00542010b0f0308216407c01902e070000e0001102140034100c09004103000c0b031180b28000e1030142041c0080b0f51084201da042c68054400c1781c810003020740900050309901000078070710091000c05036141005075115101c450461840100c605450 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 422974226 1250 422972976 422972981
    0xf090b030607051903020304020f040e07060206070c0c051201020c06090a02030c041806050a021905030618010302220b0a06020d080a0204050f0d0f062a0c020d1e0203070b0409 77
    0x38480f401d0150610042040d40e004405500101500301035011000405641c1d8000da030300a0391102030810010364559044107174139602c1c00d0140c0c0000d07114120204000c2d03403080710a10310305134000344010540c90505040000c080d8841d00b8224043d9000d200c1140c04190902840b409a0803441c001e00064a651050501b041c1c3c034404103600c614545254003114840b040640d02031541d015200088a40c0e8001d10140240108065620740188400c203203520b4640040003140240b40407541c01e21046501080c40c40405000d02000390415040c0d0303500046010501c11802031a01c040c040455540082d02c04a55907107010b5021030016400742030541c04094101d400c26410ad28800000d40c034050400303001c40c0410410500c41c90248082103070090600c1030b2081e00800d0710f81d11400034000c0c10313010700d609a861842c1200c80d01a02d6400c1c00244403050180c101900a2540940030755480700e11a200c039003012a4541d544c00d080302400075000d00595041c08480068583c1c1011192918140040e086c01c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 422975476 1250 422974226 422974231
    0x30a02040c2304060807050d06030b070207050411030c0913090f03081905060319051014040210020a05060a0203040f0210020f070902031003020d0507120b07080f1003110a0f090b0306 80
    0x2c400c03040005114450b8001d810701c0d400015428850354408a0400c0c9a00030409030380098140001c03603061001c0560701141d900d0486008840521012500611301d030000e100603600389040c000d08020a0782141850034085491111503600000d8a4170580c64401c0d4460013500b0480018083c9803c02c0026032600c1c000b00340746207215030100040d2501d00d01003a030700c100c00480d040f103070b101440e10081040f40402082da03160030f0702032051008521000d107055828800365400c038800d0245803019044d0034400145a0b22031031f0484024050340c2c844030080002544050030664550070440c4640c009030703c81c0305081c1c0548004c0c5e40284210740040d0a500d003842815080b130340700c96004209001c002100302e1044000c1d2030301203c01e624010000e1415600c1c0c0311450b48a10701d03e20480303800000f80203505441c11b2048c0116203d42410390f8900da001c5040900c1124400c142613144139043c4041551064142031402c0060a900071440c2c0b00e181650b00864250702c00c1060984880c021016424203011068 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 422976726 1250 422975476 422975537
    0xf0703030f091d1e04021e24040501091d01060c2325122d06091104050415090602042706050604060203040312140c030c011103090c040b030a02040c 65
    0x951398242503000801c034030900305000f1282464910100d14660342c0701c441c1c01c00c0740854155010b003c0f942010b80b01440d04103125247c0420380d980c1c1c0c0001c01e032340d0050803043c0c5200703012004603d40c0c1c00c007007054481c82101441901d20340e1958800004640741d019480000d0483d11008080012a07010070000011000c000901143c0f0002c02c00c015070084480c002300d0640e8010711405070113031150340e08821410f480e43c0001200e00245115010300400350302422240b40a0a800e412181c004410700041d0780d0265801000e030704074803980034120040340e4045116140b16500140c074060392009a41e00361030320040d660700e03007100c620100d452020b228440d07500141015101c043c2081e02c2c3c000040c2d101d000da80310161612105007120140c880c0305011100549040b00c4801da150000c60340c105a0301e401101d4040c200d50318000c5000360700d4081c44180c030700c036454290060810034070142c1404054003650320b02940520540d030380e4500503511401350b0748401d80307035549442c03000f0000280034055500002218 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 422977976 1250 422976726 422976781
    0x50307060f05071419050d050a091e0b03010f08060105040603050d1b080d0c0f020a0c15021908030f010b090604030f0f0b09010b03010e0f0703030f091d 67
    0x8100e4550860014038000d0300505000c0c0d240c040320304007200c03642010300854086018044100c0c2410000713407064040c0901440864164594040c0103407254442e110303c40011803071003101000541024244241d40c502e16468035014559155180c240c603401c00c0e0411042c1c5c02c4048014480b803a4200069401000c0484051101600c4c1d03490305a2185004440030342045040604052254000348103800c44a0307208650564501034020448000c0c20690503040c0015410070002280307910000c0c981400c0c0d42c1082802404070300c1d2400c44031540c00810103003400e50154594400401c0c0c0003500e01c405950080c128582c2e246042004590311641c140c0041400d9807080c440103800751940c0050f541503d0340910844001079407824240321007510000001c1c11000400d04009403c00d041d000000e14420640090010301c5143c20040e4035107180c940b40f50204c0d48212000c1020a104030303542580e0907050300b0b0601029413209400845500740c00c001c92801460328061048011103a544100700981d190300a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 422979226 1250 422977976 422977979
    0x1e0c040c020a020616020a0807090f06060206070906030f060f1508130c090902130510080c060f191b11010e0f1e0111030703090315020a0807030e0a0206070b040b01050307 75
    0x940d140105d030b8031000c22904042e403100841d200d403072014003d01850411100403a940e402a10082d014918045e07030080e0914000143c2e85000048441c0200c9240c1c440d044620300305101140200001511101005d880e0b010000740010030260103000380a41c0800e1908504a13103901074800300c0c010300815081410300b82d181011500007800742098039801240801e4200303241c00000c42251040c0014901145407034240311020046003281d03801c884404040e210380c400c4981c100240780c058424001500c80c8208500340813007021035411207960f000b5041c032070410403a6101e00700611143d90001c81d0f24401140c1525603560300540c40c0752072003804a4de000340d1102c1c10f00220300e5540c14500100703212030101c01c1700030260b80102c08a1601100b002c040340e8035030825050081c5408040d1005946510801001c4081c003480c48c000c03950400255120090951120312040f001801010000001c80c00341070700361310069581c400100782a0780101314888403400c05027400b4400ca8410b900c00741c8603a111240 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 422980476 1250 422979226 422979229
    0xc05030a050c0a0219020a03150902090108010501140f0a030c0f060e030c060a18050405090318030607020307120203070b0c030106031b08010506130e07050304031706090112051e0c040c020a02 84
    0x100080b4600b0154200030b10105d603407000c100c002069070801010402e007250640074050b1180d0080e41258001c40340c5081e00d990741c02d41e00d405c0310b01c01c0c0a1803000b00103902403e409030801000c050700c0a00060840070005580e520740c1002c00b40ca035046042110000301c1c0401140d54072a1200c0c104242c11070142600c4580da400098480c4500d40c10b2070140b121000e103070b04245804c161013070010500a03000340410310306010002d441764441540d03000304400c1c02d9105d103c1418001204d502c1584180c00852600c900c90302c03070750b105c3c4000030a05011480200403603000505c241d80304d1406101c48140e490344035414030f5005000e0318407584e881c5c1030a1b441c400302200c200b81e02158481c1103c0e4142c0f000b560350725201840d044001c0c1140c000302041d040c034500f400181640300e0029840b1324000d503a421507a40c1c2c01d5090300020742e01611070a1b8004030400052001c000c41420f10308000d84504116024030402c101c5810491a010050003550f0300560b0449800f030501d4080c00003481c42620107010034400310390 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 422981726 1250 422980476 422980483
    0x2d0a0506120105010e040f03020118060b01090b0f1803190507050108070c05100509030d020403050c01080709030b040b070c051c02070611070e13080324040c020604030c0c090c05030a050c0a02 84
    0xd001400c20f410111f9000305060003907105100c100401041109000120b0500d10080e00518100c2c5001802ca1100001c20000b00f2050342e003544170b071400c4207180c0684140c009413141451000175074107000301440ba68105420740c2c1c885900d54424009840900d207803d0024006c245c00600960a000b071040c882d800044010031030102524520740d00060503298003416034518028501c058007403600c0000c0110620030002010043d41c20241ea072841d4640d81d040701155121844e100050034040c8071004200019049031070310394058045e14041c6550b40082e26002e103001103280c1081c4880e6400c030300882d181541403040741c0103003d91303003080c20b000000d40b200e10b5622007442c8610130744202210049140031003040c04007614960026410b50300ca0400049040c68808034405000d00300d02440d09148031420140a10b00109159401411603680c440d10152200030100741c00312046100d07000049000c0c48240300d040d1200f0382c0c65a52507220b01d00740c2090012078802030600301d489101030203814001d07036000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 422982976 1250 422981726 422981731
    0xc0a230904031205101d01090b0f150a1b14010e010b011209052b020d030c080f0604060b0f0a021501030c06050c03040914071806082d0a0506120105010e 67
    0x1c0c00181607550704030041c8200d41c06401800000c440c3d03581c140f4031404246d060b40d040c0c40d14050200300d01d00e255130821000107401c440312504004404271850b100e10807413028044020303460401140581500ba00c2e20070b50004800100d554440c1061a003812242c24401c2c04c006400500081240c580c003200043c01c0c40001000e429805034965200f242000005c1c0a114900c84640c0c01d0410281601001428000e043e0441400144035240c491071041d4400e0240e0340024242d0707241ea400d05c0e158444518a80c142c010300b0300e9007240d11610001103140030000144401105c0d00825074031900f001200070301f0080c040e0012001c0105031001403010402c1441058111481410010382d2100a01e0b2154258012640600f800525106e604c0d90348007461510907208588695420300340000c0d00c04c1400044140e4049e074000207000d4800260b141c6640b84986032080124607031503989840707107002e0f44103522088900c0403025841d00c2c00e104080c18561034492030030301d9440c0284084e6040c10f00240f00b0703a000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 422984226 1250 422982976 422983007
    0x703111504200a120302011d0a0f030f300c231b0106060804210807110106030206071101090e011503020904091e0c14090c0c0c0a23090403 61
    0x140c5000000b80d6540090040043c41642d0135200d450815003000782c000d154510f44100100c41c01d00f805491500040350900c01e45038088900c4080c0c01b140d850440350400b21000000a10103510310300c0e424486603140f20007103464018509801303042003c0d002d81c141d507121200d400a0000340c02e91a58004403407411540f8104840c00d99075116030390241c41c422040390b00004110b0951920102107155507016204a20803405460b20310002e018840704002c2445403107446030005411800400d40852003030a03010f601002441c0041006030301d0b40c0001d141507002e244103d030444c18010f14440d03c2c0d60080b0418005007030803055480d5561511030080000025946800100b5900150861165a83c0d5000152b50f42c0c20a10072a1a50480d507108882d20904840030784150f14140e40004894082c0b80b050008008007610014039511071203040e0300150845011101303d4000e007400300036942c4070485840300420901c142006001000401500034000c0c016120f402026014100b20120b0340154040301c15502 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 422985476 1250 422984226 422984273
    0x10f0b1c050a0209120c010e090402010c0f030203091203130801090c030305030c042105100203100b0c01091a100501020c090403050d060306020a03150503070e24060703111504 77
    0x210204440c00130710404400681c4640000c03d1248006400204070848610a1301d4a6030114851010404060803c440087c00030f070240100b6030024194442343c401d601d100340107ea041031050300002d5110320310382e5840340c607982c400302c1c6c6001400d60441040c001070428000810280d0340390f1301c806c50b200c04c40380009824004004082450440144119002010300c8142200c010b142c80307617448008101218152403500c510740702c020109420344201c900502c0e00401c00300d4410319000e44900a60484ac02038902d6550b02c00403000070503140007504103289014440e5004c186000c030315402c8450f40b0740c0c10590465205d51110700d09034031050f404980207500f42c20300681300c00c8190801005009540c20052405001148201e0a01c1e019000a0500011a1032102a4545500506a4410043c03295440b09485000412401e12a0b10207026030302d80c080354005259588040030039502c1d80300440c101c00040d0b43e51820311b480034050101c40440910030251400d9800c02d9111030b810410760202d552407010 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 422986726 1250 422985476 422985481
    0x110609030a030f0507061503050105061914030312090609060106030219140c0106030503210c1803070806090601030605071106010902180a09090614070f03092405010f0b1c05 76
    0x6004d0400e89612603444003052101204a2070001030f01c0142d480100c90660a00c8081440c901d04030030309001109068039131030422858007421810140000a13500d4040c0030402c080031490492115407403050b41410000c11300ca04115611a01e042c4c8140d1002c01014410701c86500c5c510565000110300310321038070306035225140c04050707452a441440035401256203000400820400d0110240c25042288130103a10528008901510810340450304228200020031a1401161101e102e80b000442c000e411907000320345030031640749401000da0f001c881c40d5006200401c100710341c5004050f4040a0361800800000b0b10452844e036500c0103004076281250046207502c40803024071200f880c580001070039008d0855891a80d0740c020200c0c0c0409036030913401c0a0040c10b84000b01c0410500604082c3c0c1d580c0003007035020004400405071000126400c25640080048501c03401d942c0042c41010b0701c0f4009495490924119101c0300c0760392004200040600c804c49007603140f01e0b000f5007000040d103408038065 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 422987976 1250 422986726 422986757
    0x3010e25020f010b0d0b040803041407080129010e240a05030603160302090a020d020f0304031d0f010516050106092d1a040b0102010906050c07110609030a03 69
    0x4034540c031458105140c641280c05111980001d201c814801d40740c00802410030b1020a2003400c031007500014007106103070000f16000410910040d076000780500c4411740d100403500d022904044e2035500c603840681d1a18003841c012a40751700550b2120b51400c41140d0702440d82000a40001440480b0b1031081402e811501680600400d8203441480010210343d0395032900b00c005409608169010742c001c0c0b140d80d0419880112150341e80e0107598000b07080d01c146a540e030000304041c3d8805185410f95035000d1111320900754942000d103014910036150074055800e031824a4001e080401c0040d4481c2e59a128000101d0341c00c401212800c240c440d0341324a10a540d070510b9400f61120703500c00c1044514200601c1d6141003c00043c0c12213a2651900006a010009a07001681c1003803000240f010140704810f80a0328145c2d015401d80c40040c0008a00e007a141c0d01c6000846204036000740300c0c000005040f204202e080c0d01082c841e07001c1141c102d410640c007c0042699410245c00050621507a603100d0101c1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 422989226 1250 422987976 422988001
    0x5090f0616030f18050108041401050a0917040e13030201090210030903082401030f1d030a1115060f0d02040603080919030b072d0c0c33050409360803010e 68
    0x488800002f4486814946002c00007004034000a960160a581c0700c00b461003c5e8008a9048074000301c14800140c079400040c0412600e2000304605543d0b07a1001d1350010b854040040c41d1151440c3c40001e540d0080e410f001c0c000c1800100040171b40d051140110341000c240d1809020002400e203400200c00e806840b54000808041d00030000800614a8280c04004000003c004c982c3c03199584c51050f005c0300046964408000e0240031403036580c88000751850400341600c0c4070b405801040c00f4040c5078550007080450380150400c3d500403000142040c0b80f810910344841c10b000d40007035035142013861034071800989000a020b81d003c0107101050014644c4102d4140c4410b11030780b0342b00c000002254500500030001e00901114810448600040c11f002040c0400500592454480344d1200500f8100155003d0f1a0007800c10b110040c0030210300261288075004114031441e40d00840d00035515020413242d4483c54071070001e016902c2010002442e2101903a04484082c45c9500d0a038407661040d002 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 422990476 1250 422989226 422989253
    0x60501060810050414070f09050303070f0201111504110409060e0109030908070501090302090a0902090a0b0306071d151923041a0304020d080a0816020607050a05090f0616030f1805010804 82
    0x80c14031002c505440dd000c810000c200c00c00c1e201342c072501c1103c5400c01280da141c47c6540702118003485100000340100d05000701c484c1e80900000d000050850441e902d12044418500c02c00800d81c0d9150183d108164100d15244007038412a4024410a40340a000a181803100e000003405615010003152141440c0d8205030310180d40207003410014500080c482004040080c880f5101c0d220350008900341c0f07401031280319014001800140710181d0008144070444d103144039a004164000c01c8007455942101900c0c80b01c10040b640e481c54003080e03401100b02c041844d07080e1080100300070032041100c82c8440321304450350030703180c0030880e16550745000141c040c210541024019540000d0035294080d0f0000420748210070364459400a6010860b049907070740e2045402401084040100310715043c01000504404e81000f01a10811544040800c60301d8014200e42c014500f1040300f403004141e000710714000451001e25080e418159155100c1c0e219003114072031581881a4240401c0034031411407001070 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 422991726 1250 422990476 422990479
    0x103020f0f03010e070e100801090504030207081b09010b09061606020f0403030504051003090308130f02060406180b09030703060c0512010b0d0e03030c1213060501060810050414070f0905 82
    0xb03441e03696079020080403990881c1c00f40b000030742c0071170f0f2603100389402800100d58040741e9980d04581ea09160b18100105000b0f0710030340070361203030200006007104100841040325020b4042c204815580905200d202070381a0024501070900b40501070140d01c5500540d40e2070b01c0f040a0301503201880342081c80003403060041d589441140083c010052680280082c0103c40040da580f00714040c000308103c1c11202390041c02070010322030f2400301d11840ea585c9190f405103409404290180d50140d070004540f5801603000c8004207110318044880303144801c40c0180240500080c041c5095469030001c2e88a40850000400480d9154041090b0324031580590f203d100c80400511241d50b10790f500c0a516402018200c0314440c2480d04100b100c07000032042d070b4041d100100705607013440000030140d10074010080003155110b400c0c81c10f101c0414600d0184d03d00034800f0b80c0300e001140c00d05903001d141a800d1394020307074040e50810800b5000f41e086140074a510042c2c52034151803140b050342d01254640701540c000c0303 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 422992976 1250 422991726 422991757
    0xc0305040f060305100603020304051509030c100509060105100c022b0c0509011505120405030c030a0c020f09040515060316081014190207050c060403032f07050103020f 74
    0x11030000e400d6400280079410304e05c072030100503503245003c905030711041b500140035401105c4001100b04040701402d070043c41c0c00e03007a02d0510030040420b516001c010440f62141030313101c40501c2060002804001e01400080d28403540841180c50050309102d02d4010090040b40c3c413200d411030000c6100141c290140401c0441e816112840c2400206d0101034051a485210140000540d184402483e9004501d8a40f212424116128040200345000810070f54a6000410111058002c07e00042454a000b6201c0344400381c070a005210081c1c240c0c8c415280030b20031041c2400003152000810001000480d0300b008001c2d81e88802113800c0c00c040c1d0340c03c45078024011701c0108054002040d00340392480311450401c1261017582c440c06c500801614040b40c8020f00242c48090580c498000b040d0f90790080c3c003204c2d200084240414035030f6009078070a40000346a0b40c0c4008502c03800c2c607450300d1110403d000d070200305045514010f41300d20961150b181490381c0003c0e03585468001805613140200000c080 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 422994226 1250 422992976 422992979
    0x1109010303180609060e0118050303070b010f060e01270509071110020a050a0c050a08030408090f0414131704030606050a15080a051e090d0e0f030d0c0305040f 70
    0x1500e600c0d49408241481e050388000030071941d104118000445c0c2499071580700e81c25008005413000d4007011005000100340f05000b03e036a80b010001043c9680c400d201380c2c0141c0d0324014580d80b0208850708100200700c00c10410700d00320b80c0d000c003603208910162105203091024079040444806113580c412034104140400300180302e03030040751604d061812001034130300000e000d4140d507003203202d032102c0400890020f02150000724420008001c0487c450300803904280191b80b181c40c402d800c1180c0450b003500740040e80c01d09a00380380c402c1d100c035640140c8051142d5201c0000503150381400400603a45021340300c51a0303060180180d108189105242c440f503907255100d0074408060700c2c242c000e140c0607006901340090318490f8144481c124040b03944d40c2c40b4082e2070741c1c1b0300180601000b410101e030607101d96a08110b000414207409002d4070101c40141402007808d0800341041d0f14054409124100c00c1c0d0384010720392000716070034002482c03070f01d080c04094865140545e014055074020010b4002c00c0e140 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 422995476 1250 422994226 422994233
    0x315090a0209040617070b0a021203042d210302071b050901060f0c03051602040c030b09150d080703020a051e06062b11060a05030105040b040e060f0411090103 70
    0xc1a2180b0180e4003401215110700b051081c0440f06240d00d40c455204100400035881c500004d44070882040c81920b038500d0649004461581058406482106854183c0f111420503010f44407402850300541c442c0240158507020b650348014103a510400c100c0c0d0080d407000500c03d038111010303541c0c0400c19000c0500240e091100d101c91034000d2600848070100040b401d41e01604042c607100907150f485e02c0b0f01c04456034080710250840003903204040c200c0140740005984500540185551503600007079603980b404200032544c0e4010304000c007071240044100109031112150f03501d02e590007814407503407070a5510f8200d00d00a07800c400036100340517501e0100081c0038001c02e80310094104400b1900d140e2184000c2040c0710549002a02c003c1c1411107244d0075000b1f42c40c2080c04018051424550303080c22060228405506c050050000688008018052481c040c81554003054090700c040009140c92001c150b621705002e0070410484200304001380c1000700304107145a5808000c0d03c0440300b541c1d0fa14 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 422996726 1250 422995476 422995481
    0x21e0a030f090f1d010501030e102a0309060501050a1202150417030c070e060a06030b1915030f0204030209060910080a0b0a0b032d071e031403041401050315090a 71
    0x440c944d02210510000140c20340c030a00402c0300e417803403106c05003480204600d030400082c508000c0d040d0141640c0310031004d1602c40803900d14400b800c0c903100412403151a1800c8011144140c02035803092642d103109100c1c902c503032800c0740b4040b035041e106410140c0e1200700f08207080c0220790055690311014202ca0f5068140030000d054881c41c40c0c030031960695181c4080c50421042110895004a661103003004801e200350440c0c030040c00058400d071a00012013260984c040f8182e0803602c054401030b24610f807a15810302ca410000f4550500440c01c0906690000d01811000303032003244165402c1012a01240c061600ca1008040305002c0310045601454890b5544908681881d0060b00e070030740342500d500380880d403442030800801c083d84c101c484800203200c10021265664196205072440414070102c444003903500b040702e188403e80c0480c5107240000d589041e041905904e03800902c02000369146a0b07401210300c50342401c1c101d07101c1c0d8806104079001c0300c0005885a108815405000402c2c1880c3e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 422997976 1250 422996726 422996759
    0xf0f0304080a260a27050606010f090302180c0c0a0506040b0106051804020f09190305070519090902120d120b0f06040302060703020307050a03050a021e0a030f090f 72
    0x43e2208489090046400300f0440c2c454003946a05081110020f5064505640240f201c0b41100c02502c81d101540d01002e043d10802034421038a0360b0040051040c03640c0c00c0341d0441c48054003464607407955811507006c40c06103660038030b14440403403000c00810320140c02c0605482111103041d08490f1040300707608145584060664041d200d200081001150407481b4404544111102e4211300250503c66010f02c0000d41c40012880314010f000d000c1400b0315580c9403080d5901e490780800c42010705086090940c2410030b96408540f103a10b58001082e014011211034004aaa000500292080b09030022a0b4800314208002e00c40b400ba0301c03200c0d5070741038201882203410000c1810802074081c600052001500d0b18a150310340c0a1003c0c4020001494080001d0000e1882441078908000c0e89640c0c1c1840c103140014110045540401c0741e40821341c1c10040c1c0c003072020030740c04042030070008001d8803529403a40c802e0160810503800c0780030b040f40703009502502c018244245a1074129a0b6040824a200d60700c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 422999226 1250 422997976 422997997
    0x10090519080a1407032007090207080408011a0102060f22030807080a0c020307060209060d090c08060c03010e270f0106090e01051506070c05031219030c050d020f0f030408 75
    0x400d2070f03000045861059510065042e159400342c440070103500c05003000a1000480c551196000219500c0f01c1800505001846005010b4547d030401740d006003522400c6001100d581c1101081e0140c603a80001c0603071f08100c803569520410740300c2c0c182c18864100504804801003496011241c00c1507880486184030b50101e903210340c030035201c80c1c000d2010f51f4101c400b03210041c0d10601849010078010350003082006c100800c030614100b410003081050710800b41d410307207054110200808c00c000f024840c00350300c0744081c1d603018030f15070400035600d40b6014041e1100207400e00b0b00500f10307082d002010004400d180d0303400840c0ca84040c031000c0c5c64060200303400362001450400380b10513000c0754140181401540302d0000003007180c0c0310b03500b03100c1c8940001c0750a0760b018240c0c650029141e101070240015a4400c0d8070340c0d55035865204103606004185140800030185031030ba04c065401c0d44441a203140b00f211941c0943d561170b40342c0d8803030703c24056006450103039500081030204200e0700d90003d1800d61107 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 423000476 1250 422999226 422999237
    0x703090f12020c100527031b0306010b090d080a1110061d15040203041e0b1005060307080708130b010b0c240406183f0210090519080a 59
    0x16809203e4000324031071085002c10800d1000c0c0842e42c0d02e0b91002c0d03014201001d1030b0003800038002d00091503c0114a03000c08400d0300701c41c08e40d000d13050030f100c7c0c14050a1030320405840d001c09113004c1a5003001c0900f000c0e00611020500000302440780c01c611b01c0362242c01c400c031007450882c60100c40081010f885110760910b00b03414984002c0c0c3c1e0b0b030302c4200d10901419102a03050005030080c00041c0d40010800c58a5070320851141070760342040100c141483d07006013403801251800000d000d1a081941d000700b03226460070b000300301000da400000c2d04d42c05140c0f40742001151301c903036034070555920000300001c104000c1540046404062140500103080080003203a514401c1c5245102502c0c140145c000e0000c1d13140000940840d0700e6070000310071910580172440c1210042d03111880025041041c10030b0b003d03d0f42000b80031025014111510074943c0b40c0f40c0002140210348040e54815540103e11a015110080682440401d01100d81036107900e4543c4081d040961a202e880d40e4813100c02d40c0c01158 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 423001726 1250 423000476 423000493
    0x60302120d1b080403120e090103110a0501050f090415050301060b070203010b0913110607060203240316030201200d050a03060906030b0402121c050a0305010911120703090f1202 78
    0x81c040000e0996681c3c0044126141c0742c00c3d034403082058442c0815000600c0f42c07021001855031600e2003514000c40c051503050000180010400803071842070303444203040020500080d81c1d00ca80b070314100c4400718411140000c0c072501d4542203040750001548026459460001c000812480e0f0790000e03c40140301b10020406404600100614803030241d459424100c41d00c2c011000260300d02c081c0e03007411100104180c1c20f020055503842c06036402200e001c0d261440506c00e88003017a46281c0e8861000300d04801401d0301ea061160007482c444240c2c0b0001c3e04100f6280b100000d60420b4003c2e020607005000c0c1a10282a4001000f600035070001c907081c0e00180c030b4075000040080c3c8520404050f40d034005441d0b0040e44480e000c200d20580f8142100209008401c0d402a0940309440f140303440024a440d200e0311040d14071805811650140d014444840c105404001840390060490310090742041d07030104c1c640c0765248218020004280020700031149074034003005000b0420201c52038130600d5421070b5001d4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 423002976 1250 423001726 423001757
    0x180e0105010b1207141c0905060f041e0206090d03020a0c0f0b0306040b1f0f022b03020703140d02071509020f010806010e03070f0e0711070b030a060302120d 69
    0x83c4030301d5a854144115200204403190b00c525010580300203210050342c20040c0c03440385c0c0510f00202c19000c0030140c0d0380b07641a10070040c3c14818540d102e520b0420300a51854503444114120138401d00c100c2040c0d4554904604560b80c00e0103507000010044d05045444040d1302e0b0217136135209005400d8401303c500420000300c0c1803c07598900d0585151204041c2540c0790035003400081c000b525601c03540b103540c1c80c40e0031500400384e80380801c8540b603076a9194103041a100000e410400c0c0142042581c4c80686032210342050207054070343d02d00d40e032440c00594544140c04d00705e03450b4080380c10404e01030300e0026a00e00300c0c0405402400006000d076040d50356090683c5d40c03d40c2240c813401c9000b50080d000e92411401c07503014852169103c4018104403214460101c00070b824a052030300720482030000090280809140e048036250f00800508000c1040146142a00e80d00c02c01842215049003001001544030300058108000650340589008900c0c04424243c5440c1e0041002d80000504044030700c0106 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 423004226 1250 423002976 423002999
    0x80d0b0a050a0f1a0405060712030e0c030a0f1403040801151d0a09060e0111030a0e0c0a03060f0f02070303020705160f210f030503040b060a03080d020a0306180e010501 74
    0x2c40b03040782000a9014070b044014000c3ea54004c0700342803902003d02001a103521070000031f041d441e100d1030441c0c2000c0200310001c0e0460303440800c54000f80d0b011320303400a401d07140010410401c5400c40490384455916103050101940044500130b00c84c00b01150002d02843c054118414061110002048058031507030013400101d40d5039007103002ca40805c40451074588040d80b00c01d401c18040e460110786d0000c500c4c0254217607075503020f84c0900103400108011440c80c0b6481000321164203640030380041191440026581010b0f40000b5003095542c3c2d80d5401c80c41030360b900c4410961480c207000e42d1112a1810f002d8001e41014605447c00d0080440e018501c2d02441c11660680d1810401104101d081040c0b002e11074801c8101040c0e00700e400c040000115034100090050207110b60b980070703503914051400d00036101c40602554000c01d402c00703040c07000640780c0055840e4009a10310050b1102d00101c022000383c41030382d20075034400f404602c95140c0030480c0c5c1c01c15403006c0000b0f0024441c07640d841074483c08 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 423005476 1250 423004226 423004229
    0x14061308090603090705120c010e06090f10300c0305070f0309082a0f010605031005040f0b1609050a12060c021005090a060c05030907150c080d0b0a050a 67
    0x5010080001d51414034001d00a150030036082012100c5450311040031071209280d407111304c41541c1c0100101c501541e030003503004c502060151130003030a02501c0c1c0013040c4984001e40c036084c414014040400d55183c07080b107222122030195016480040020040c1c3d40070252150303100c030b40840c00c080d00801c200b8000d002c0d05015000e19556120820b11080e801c400500b840f14048402440c2040300040441c640d00c07068045040828199038002c041c03031013840c03600030301d10041981641001c1040003240c0e0082150482d58035214004601d550303e40c6840d00b04045110070003406a140c207010711101c11348a2082440003491916040f0015894504100010a5601c45d07175028946001d45000080c1660708411041001070040300d405c1229002c00300140c80040b00c805031a03170b210900c8030301800603138094003065005a0606516608190201036180d0000340104409000e20784440107030070384503e106803500d54000030115160440c07440254040d00c1603407086031080c600c5001c00701d4940752862a034070 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 423006726 1250 423005476 423005483
    0xb010906031e0f030503070c0501020c01050105040b090f01030813080109050c030105090f071e051203130f03151509090b04020f030c061b1c03020d05010f1508090102070f140613 78
    0x403d504a60b8121515440107046108001e82d1914010000300c0900203010441d480758003308040d8180010301c4216111104007501c81c60b03c130303002d112504000a480da41500d400024881c2c1c6c0d8200500840ea40c4210766002c50740070340c60140490180708000ca00340c120040214028001c80c0c039a0003a09a50b140c40280c0740c030381c0d41c01c070010400265001c90100b050f012440d096040c0d1513039580c4009225111040324044983c5c00002c0e2070310070030b0020010038011300240b020300048039085881d002807a40c2c4018032120070036681d18174106002c600541000091032005014010020030307191030000d0a400391030482c0035100040040c903461402241900d45140041c001e54201600142c01d00d6900d41e14040d00304190150361300101c241202145030061001a503180560b031641384031111021184140d00c07500400d06140310a0040449180012003940114a07040c1e2030398960f080c041f030092217032290003040c201d2070424403410081c151048010030000c44003900c050781d80e00706400c00031041244004 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 423007976 1250 423006726 423006743
    0xd050a12140a2f0909090f1e06010b030112111f121104051f0306180614041109011809021201081011071709030f031b160302010311070b010906031e 65
    0x2c2046091480c2c2c1968400492802c5a1fa080ca61092180c1003509040c10342441102c9101e030b4511400d02006030390b0040640c8402a0701c0c641c50565400001001664001d00d84450519284070b10354504039068074481c02030840d898080c626020290410f0054040c100d030007030812a0000383c0d008248281ca0031203002509208151101942030496001311502d000d040c56a51440440d10f00e80c4500c20070300e091314a0700e000032641d003002c65141c4100e10700e00c20709201d6418686100d0348d0068100035101c1d4110282005008818040100403451501e80c0090b1001c40c408104814010b04142820341223900481c10344000d0740c50f8403030a07806c1c0c8140c0c0b0300c07810701400c080005600003021240c9141c410f07000812014102400000041d003001c100c00e400c00340b940d20101c0c120798000706800d029180a0f05900051880c0341c01030403011400902d40c440613051607138841000c0364100d10f050840e80440d40c0010448055a1500808801410b42d8042500c0c003482e80f400c01c80112480c43c2c2603403100e54000c2c031716 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 423009226 1250 423007976 423007987
    0x5071712040f090915050702010c08090613080a090515090a0501020a110d1a070c0c060c210e0a0b0310050603010b070f0204180c05120d050a12140a2f 66
    0x1014080c0900c0701017160a03980340a001e0900e0a02031148074010020741c0d0000c00c40481503100100440c10107041140c01da0040c8041c00f40062051041000140c1c0c03003a01c25886003902441901d840406520841d0130030604002c0c050400b03c080000c0240c9442100c1c114615a150401240d80d00502c41004001d8800740140501c94070b0541ca0100c140b51180d1601d860102482a01501e0042c09031604000700780d03105400c00401c1013404080010b400306150a0070030120715141c1d5041d01d104030000340043c8000400020541d4458110b1082c01d443c05408800c1050f0f40d19002e4409510407550702c15080340c0c2c21800304047c0b5010048074105c5144e8010321313082411030340320300303c0c2e01810380c01c100c1c1c2c0b00381c0e511141011120a083c01c100c1d17480c000c0f00c04d1541c20b450402803107600c07d600303c45400c0c03980259410340c080c1d81d0808240d408409041c0b1b403001058113054810030040c071140c211586060f0100f42005503e0b84241c01c0308031880c42c1da41c4aa20070410484210688640882d0b10080b2084244034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 423010476 1250 423009226 423009239
    0x617060c16140102092d0f0609060d060302060f19090308090118050910090e0f06071404030b01180b0f010e060a09030c300f080d020705071712040f 65
    0x100b4111002003440010f2809200c0c2000561200000d09006205407402514040041c4541c44202640d4025151042d200310300c4400500c851185804032841400081880c400140c3c96a01c4100a0350f800f604195441c080c1d1011f01c0f04a030400102c4030081c044a03842a40c02c40c0c8240785c820110707607000d182c0c182849070324001907400071540004a107501c0d0b103030f440000712035507081c4402d801030b1044020030a0704d90624a000d41601d84603c01e160b80d40d404a02c0c1c0003900a0000341c82c540c8010315182420101034581442c1c036061085500180450ac115000454900010032183c410005007020800000d20160f05001c2c45200512045022404407030b0f51028500303000e0001c10180c050b5113848031046441e9a2a440440c50b20b802000a08101004400f04281020441c241c00d6a080382d441207043c441e503482c0d402c41c1d01c80b100010030044000c2001100002c1c1501542c0781030743e201081d00c4060741c965040d0442e0000101d42116107100d0f80419181180902d001c48081d100c3c0520410300131801e246 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 423011726 1250 423010476 423010493
    0xb0114030a082127030f120403020712050c040c0c0b0c0310030501021801081008060a1a0d06050702120c070e07020a2001030605060a021e0c040617060c16 68
    0x30603100f80401412501d03849000ca5005841a903400111010008401301000310000381074081581a42c01003140010292007007060703d032107407503100d95a0304035911031a0403803c06042e0f5120400000c0c42c50020390030008046000c40d18080195401c200100d81d01000702c400d0052100c0103000000341402103100600c04400465100e1a000c1c50300c0407a0b40c0d680c8c1c40500326404510880038168001d80d2910b400d40e071022507140c108c6403183c0c1691449041a58941c1c6429025000c9501d25640300710540c0d820965141c80d0140301801041d100300d226081c03c00c1805044105c0d1110300501078602c241c0403c0003108103842c070a55461004013140c904018034414038a80c060540c0095226804401d40010740f040a520b101250020300c502c040c4000c4000901507c810b504441c0c4501800d2200c41000d540c0052040490041d441c2c8000c07112460140f01400c01c00c007002019000340c1000d4004c110f4001c039803245000b80c591801145c0050f503c0030511906401114070a1100218148461000c00c0c90f50 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 423012976 1250 423011726 423011737
    0x2091e0108042d050f060609040c0909031205010b0901020127032d05180409031407020f040c031a0a030302071a0f04060e040c02060912070c031e0b0114030a08 70
    0x251402ea0b03480f2001d04901001100c140002c40c2c1650043d4640890035209101c4180c0000055403004c40608103580c2d00404895140180005181d540f6241c0d03007130520030040070b9030f2842d03a128100620358460310603621036444108500d003d5030230094104011044048501e402c0e80300031248411010306982c00300d40d0084040100c800d64100001015480714444582c401d0070200b03038445903034904a02005815030014001330900c200d290001d42c0011070741290f40404080a800340b180c2c0c0c1c030800b510019400c5180190003d81161030300c1c581c4210302e9015484410050356a00e40e003c81c100d000c00421400c0402c03400b0040042c0c2044008204440040c26007a460f207034820940303403c9c101c02058402c1e03950481c1d4413600004032003a001c41e903d81071600c02e26180c0c80d0b181c03001d05007628200000541c2c41c044030a078007a215000288200a0001140300000503650040d805850065500104d501c6c104a00300f0a1f074032880e1810000401151103030100100310b4026020f400d0001140d104c0a80a8009 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 423014226 1250 423012976 423013013
    0x2d0e060606160222050402030607050703020607050906160c060e0402040b0a0309140109050105060a05090f061012061d1006020c010e04020d0e1501230f01050c06040602091e010804 79
    0x202413034100c0780040c18203050603481c21010700090030b29143c010903240600c040c204400340f2900300800710210f64045003036640b02c1c40d241000c542e10514030700402d0040c8203c0040404203900e80204d00200000482020211501959011650030f005002c11007284641c0c880d81500000c10480780c0d0a0354069040207500e98010b01d07a017038403503544828050949000d1841100c082c0d5442c0d0400105251a900c0d06002e8031050b6440b91892408513044002c51402038030385407103014140600c1c01601c1c03088049101041c1251400d00c0043e40c3c1d4040c4640c0c10888411100c0e010445100044070f07a20381e815030700d0443e2035a078002c1003094000b40056921146c02407500780c109408108800001740a07014007903070080d103c0010000032100b00c1103201c0b24181a008650708800c01203644584c41d03c0704500d900d150310212490b1905440841c0103071218400c541c070007110f50003441c08010600c072481d4040c040c600800e03203100d8800c000c2144084201d2103100a101c0c040b6004038045000b081c4030119444038500c1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 423015476 1250 423014226 423014239
    0x14040b030703020904120305070804020904020d020a090204082b17070e1008060108220b1801060609060909110d0e070e0a2711060703032d0e0606061602 67
    0x7201d4003c5401660226010348490441d84a0040f80603410300c58a6442000c2b894213801600303295000544400d40600301911880121103182e00350b5881c814044010400090b046569507520035801351280d0f81c02c4100026805480c90040b1682c819586a488000f150ba503240c1c1c8280c1d05051072103400c10003602450810404580c895425107600808490780d641e03c2c0c035000d0362481c080c0001050202c00406161803000040d100420382814500510141d40d4454040700c016590350400481820b0701c0803007603040b903090540000d2a0b903084a41641030794020f658000e100c986400d90079040d00c00158007810300c00000c01040c0d021110035840340309180440d10a866046035140b1020901c40c0f81613801c1c0c8041e80d03481001006418050418010b0901d80f038060700c2d2580441d0f115401d050003c00c085a020340400290842010f100c2c0c0d0020b500c007030700c40c00350b900c0751424401e01a60100e82002c1c0b2b009140d141030505940f10800288a80c410039000703104e070f071400c00744d100e00340707600c08130741e40100d81002 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 423016726 1250 423015476 423015479
    0x1020408030a09030519020f010f030209090708010305070609060e0d02040e0a03030617010e1506031e0c130b09010b0d09020603012414030a0c11030316030b040614040b0307 76
    0x82007480200540b44035581d91103425030542c2801824076965a03400d40003003c0c0c0000c8440180c0792a541518840300900301038100d80e91042c415400380c40350140196005141404010031980c11500d40340c103030b81c09141295491a00d030481030b40d141650380920380101d00d2000f01042d8514085212612062001c2e10105400303000b82055407a010341c03184200c02198030340000340060501a680c001036510004001d200f05c0401c01c0100303031102443c58407102c140c5603002c00501d241d03c041203100880d40d242d00c0c004480c02d80c1d03d40d030661100d0f40517001a2065440300740078010083c0b14003440317208960090110801da440d200180042e903000158040c10943c9440c500f00269907428040e50090625103242030301c0d1003181c41001030010702c685a9405015031204001000c41c1d210054990240b42040e0000e41c0700741025066440c4010400c0d055560700c00001000300007900a50300130740c81d840c1501e052010081103000c110a0301d00b18041c100500f482d510940509140c03d420114800c400a03003964401c6 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 423017976 1250 423016726 423016739
    0x608091b010905180108010b06182b03120b0105091008040311010e061005100c030804170c03070b0f07170c090415061404030f0605091510050103050606040e0117010204 74
    0x1c81c1090b04004e0020b01c0500108401c8000380200404094200c501c07a150014404100e017080e408200b0280c051210341003501c8007049104d100c43c4101c1108128140e15928501d8020030105042209001060600151084650013403040d100c0c00d80c401051b91600300c004a03402c03903900200820070340070055030000413001c07140280301e0341c62940d0004010706407a24101e40da807140780046510503401034030710011140c503c0d540615400055585841e012030702da2030340d04090190035010019090340034800545031034003103070000c01400786511403503070010156150381000c9190041100c060003c203650903030407a86140305c4002d650b400064401e00303a0420820718007040c201d03014440300108215003040305201c11078220440c416400c06947c0914a072505554508404264104005199a88820210313000d803601b4004040110301220302107001d0304d404107400c1103a60592045a002c64500004a8428207004c42214180c520b035088801e50b0f6440c04503d422003030384400840d400c2d95400c1c040410700 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 423019226 1250 423017976 423017989
    0x4120f060213030b010f06081b0c01060b03010501030506030714040c1107060513080309030307140a02090a02030105150f0318120f0d1b12050604090f06060f0608091b010905 76
    0x203801403140c02c03510080c19460100d210590603000499100a091804c022003940170340720130707403101264070403158464191006d0b52150180c040003010a5003441008075070040e00401944c1256000d98090140307485503000d160b142c41650240c81403e0100c0d0304210224101030300418042c00451070000000d00030070754603a00b07104e0b05400c0b8000049000420305400a4020030103400340202d08003031490400d0146c0000c1d03491003402c17801004840d076010030095001e01485003407806030300500301c14803914014601b03070002d500c24000e144c442c03241c9051200c1c000404500340e0702c901c2c419829041c41c40d19200600c0070f1561011201e80e981c0d100b02448040c1800440000e000310086c40c21360030b0744481540880c0e600ba90700341200500c0e5800e40380301c0050703143d9200c0b03107429810070f1541e40003401c3e07207400001c5005403480e500041e100d0514050b221003046255880f0104852401d85030750039154540310304540421003940e0142440d80805125000c500a4082e4a01c1403034050500b1210301da80c0d0400700d0071 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 423020476 1250 423019226 423019237
    0x206032a04030210091526090705031e120313080d140a18060e0c0a06260c030f070306050907110f0d14090a08120d060909020604120f0602 61
    0x421810200d41081181060b54a1001d40c04c1c0f036040504d00c0b80e092a0708038540d140400714040802100000901a094204003802c26030501c0d00d900c0c20152a00305030319541d800b500d02c03d107800780c4644594020f41900780c00c0c00e9200c1a2003c3c000d084a540311a00809031904058954140e00e40603001000002e103c000051640e0b0740c3d00d4801250f0003840040c81701141c00c008004403011f0381400034400d10005030b160300700c20700382e80a8400540d1110000000e03107481b805651342500203842e40c0011400503000954035006500d448282c00c1c80142210b81202d0350300c419181c0340c1816109102240c0381508005865601540034072300041d059079144c0c00596072a0058a841c2c0c0862008005c10b01c100d031003400110002d0f404040244054414101e0090440a500100b80d040f017030007094004480e0b4600d0403002c02000701c03d041b07c01d80800c03407264140c0e541c000c0448080d0a4a45540003480141c18041c00c029150001c0240381080d103002c00205118951100c11900d903010000c946001400c80c0c4060030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 423021582 1106 423020476 423020551
    0x9040201080c0c071e051e0d020d050115030f1a01180b01020111030109060f140d02040f2306040606020a050d0e0a03120203030609130f020603 63
    0x6090030400c5c0c01924801e0040240b0141103640c09102c8000c0e68421110b012a086500440e00c0c0400703080c080c0b06411003908100480980f03000c0040c002c0e094007810021034044240ca011240200d104c2c2c1080350000829940c40081c45109110001d95040142051995504107407603881e51040c0019900d0416403074502c403043d9030f4400c3d0000c0304031407400c40c4415200d5840ea100800a08000c0c003910005ca000a20009284d00841e00600e0100401429182c4100460703006e02018042129082055981320401052803143da421003125201c440c200074105400e15074100029944075a00c450308550011010341e000c110702182001e03000200d800c0003241540e00901080500302d481d40058050f890040d0000202e03500400114490301040310002841da40c4c01811402d8002d45a001511010100340e0703d41c0142880401960090038460080101700c038240c0c0d24141d046150200807 = true := by decide +kernel

theorem cover : BRFrame.Cov 422841726 423021582 := by
  have h0 := BRFrame.cov_init 422841726
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422841726 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 422841726 ≤ n) (h2 : n < 423021582) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
