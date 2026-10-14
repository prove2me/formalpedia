-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2758
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:39:00.333323+00:00
-- url     : https://prove2.me/submissions/6e0a569d-abfb-4c9e-a7d1-2cc50de464fa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 495863309 ≤ n < 496043165 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 495864559 1250 495863309 495863339
    0xf03160305090606220906020a021002130302040c020a150c090608090a06050603030c071206050c13121406070305040b0604090c23060f0d05100e060d03020f07030c03060501 76
    0x154441c0e0120010584078541002e4040003844030140417006035490404100544507625011101c0030313008a0b440c44640d03018010400345901d1000210708104454004100c01c068a21019004990728210711607001e100344842814590000c4860502d29031200005c3d0080000c001c0e1280066040080844d400b882b46082e20f000740b5840300204640c840d81d071901001000082c0205906220401045d07032010403e001400051102e419070000340c40483c20208107032031000f00350b04200700c02000324594640d0244108401d96010201d40c00000800b4509031910cd2400e60000480c0e1007104200503043e0303810f420880c0b190344030340081f0640e5154041032206450300e4810080840701c030b481c418481c030f9030a14010350b0109a02c4001c12104c0501c000810b010fa03000498407a0340f04400104002c0240450041d690083e5292034008d0b00c40d4a41201f201289401410140c4241460800c11003030602c20408409441c9401094401d940c0d924602800380104602c002c4650703030f00f444000103240c8103a0400c5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 495865809 1250 495864559 495864571
    0x3010c031a0f031603031110020406051210090504050607140309210706092102070b0409020a0903020a0f05011808063d05011b0804091d030f03160305 66
    0x11a401d0a59010400c070007411400341600740c1300d440b02c404190b1040c0b1000310000e501a468100b441401400d0490400a80200011109004110404c42231354020107d0b90681207052504000c2c6d141c1c08010030000a076079200c503468606040038082408404903007a80100000d440e251180a03803d10220054001110014802d070424111801c40c60307070000c0c50029442c0d842c500b051904105aaa58040356124203054901500541c021041107a2889085a540000d8002040d00500d082d0110703200c6c3c452406220308468022422203246402415024081e550081c0103406040d192002c40c0c4883c0010300c00c007030000b000e41d1a43e210141c503040020701030751000c0000d41202da540d0890302c2c0c0011000000d02e0200d002c584d10b441140f0000f0010f00c0d030920a0f0030300c070301c0703101d4078100c0014581c030951178004501c400401625000907081d1011642115003940000c542160340c40c0d035004083c20028003000071404009241100f2041d900300441c030920302a0150030301c0f00c039140030440440340c0c1107840b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 495867059 1250 495865809 495865841
    0x509040c0921020103110d050628091d010c030c1412060904020112060e060108070201021305092805100b07080702011404081b130e030d0911100e03010c03 68
    0x4100d800a0b15510425214010f04000c52100c80c0b6110010840d481070301075a10240d5560300b400361600e008178202c1f402c440c001900010030321510f1070001d0a840389120300900c155030303100412031035646c44254202000411b40200034518014074054054410503041c0c00024402111440c11040e42006441c183c00380d220000c0c4a0799607880c00e1100c400300190069040c0078450302c0360710410381940034000190400c040001c2071420500c0c0003600506024019000b0742e40180b010010030a10440950300300c9004491f104400e84032541c4c0c03107c50103421100d08101901074100b09424558541105005036201500c0c14031142e502d441140c01360140c52001060490100000005503108000d0000940e00c9078046a180c02e6603024080d141401c000310b00000c065148405400c2494413140c1c0c100441035202041c070800e5000706049449119204a50802d9651070310800213010003220042d0445202900c545440d0104001c0580304015400d0142e10a40c00c017426002e5072413080c0100c1e87c10300840b01d4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 495868309 1250 495867059 495867089
    0x30f0105011401021f0f02040302060301090f06092f211803160305090414010303020a030305060f010f1209050f070807090902010c03030b040e031c05090a12080406020d0c0509040c09 80
    0x2217000544107131144048155000c3c000030016a403601e0046000300544080000c5150310303142414190744907584803148440ca05461418003071170802c0342440241c503d00801c2d00203104203031059114000d155144440940c3c00101b80e501000c01c2c5030007070003040c0300301d40ca40f600c2c074007082c580d55284210070045c40540c0000100e100001c0c0140c0c0500000000108049010341c0d0f40c0c170030980021826071040d0016800f441c1110305140d094496150010f0003500e600483e01d05850002c2c2c0031050740700900b0100301080c10708100e480700d15401801519400400c7d0b80c0d510035401500c0381e651241d4010700aa41c0615400004c80d14420b00c038403400698180c6900c003070011681c506a004111036214550050b44031459801150018002400035604c0d00801030407000211440c00200c0d100140002e1281c0d101c840c0600105001902c0304214060610b0040c1e407a036a5481c0c0440a0701901e000c0142140c244000158126081009403c1070b401c199000c10607940c5160080300e0104461150302c208034600300b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 495869559 1250 495868309 495868363
    0x7020f0d24020708070303051609030209180c0604170d02030a0801060e01030e010e0d03060b04230a0e040c150305062404031e05070b07030527030f010501140102 71
    0x11011041440041c8001070078a441a00c485043d0343c000c420482c000b035500d008101900216101e803092070555840d00503211030035503010600c00003020301000c00d9550340250300e911006007001081400300c1d01922a984aa941324503405148503420100001030003400d4800d20709038400010303201846140d40e20703004981d00c0c002065070b21708040201d0604260302d452130b1580c0300c0001d0048582d45000440108010b5009040c000c045070001d40041d2904281000104000c0b5811078801d000d860014003407120f0f0a458000041c8000d80341e03442941071442c0e200030002401181c03c4c01100f168107019101e44060742078a000c0301118411501c10b5400b12072150140c54400d031070100c944041203069089842c2075101c1e1127a0b020755500307510400c031103040008510200714040c41130000801042c07807010709000c03c07a50042c1060060105121114100008800d91610b440418034042d20004d4241c846070044a042d860280c2001d00401c41040c03101c40400c4038075407001450014082660520030071644c0c00c8 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 495870809 1250 495869559 495869603
    0x70207050904330506030307021e060c1207420e1605130e070911070b13030e011409040906060504050106051801180b0c100e0307020f0d 60
    0xd441521a0810300e20701100400b03040d6141040f5040c1c854600e0b070f5042982280000b0756600400e01c5c1c1c0030380c006014000c016110500381c410010399040c0c8000e2a0024980841c299000350307003c4100318403500c1e40150803089400300605003c5d00440003541c803a224603c0c0300e10421440404c64814804007004206428240100b2010041101c0408246070507400341c0146807804510741039034141c5200c03000b00b00515110070740e44a901d183c6c04082c014080d100340e10b41d84444592084038003c940790740c00118a0f02c0d50a085400310381d44603c070102d8608100c5400700441048c0d480480115545041c9141d4647c002c2a401d108070b103545125a280038520b005100c060101c0f00b908440041c0ca80801103080e981d140207507400307018181d40d80c41d00c400e110350090035104441c490141c180103004500038024001c0c403510700240c40501015070b60302d00c1904d900303030714260410022501d40303481c103140100744041c084000d01005000715102044181850100a0300b40b080800040c41f507407000da4100403c0c03030340d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 495872059 1250 495870809 495870811
    0x2061801021002130e090607091a0f0307031a090c180d05011b02060709080604061d010f0f0b040605061206030f07060216120210050d0b0a090203040215030702070509 73
    0x10710640318042c202c1d40031401603801051280b54070300c0b40024188804100c84594a0344840004014990781c2003c8a01402000351401a090700544003181c490b00d51001a0407a211145a00000c565904d04074600400500802219800c00c1b03001c420310f6041c0c2d00e8410b0b405805440d4800c074141c48c241000340024100c006c44140f0790341011a51203084007041081c032400100c0400c20b85d072480e25113030404000f42084001861081801814003082c4650303480080e602d9031140d40501300107864260303115444400c10801200040390f40c00d0200402a075032454028103120f417a2400c0a000c96042101008140e0f10700c1e009450700b0080c1800146041d03402d5090f482d42040020301038a02030706000301d040d81030194641180e405a405065200c88080c1300303a107540c0040000c021410751041e43c030340c0050580180709820004002012072902e0780303606203a100c000305907001040d50030160360f40c0070080c010b500110703400d0b07200d140038042c82121403000c1000c0340c1c800c01c0c031503001c1c0070690f0030705041046c2004 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 495873309 1250 495872059 495872107
    0x6200129011404030c0632130306050709090c03060602060c031b120f010e010303020a123606020c060418110c0f1b03070603020c030f040303080a0c0c0206 68
    0x40010000c030b682400742c0c8001c00145004200303402d1005d040c902c01404a06190321034010350b43c140c15054141140a00c0b507685204000b0540c1550781000c0520b82c5000d040320b40003d040b4502d0300c0300384029a60810341c0307c002c46111000070f001d0071540740019422100240b0450303000d40c1000001a83d40003001c2d0003113038003500001030700400ea141105180c4682d046198600000d100e110203200c05428840d22042c010b15450341c1c00f140f190304550b4002d4a4800151004100950150385002080e000d02c01d070418401046401c0c2c0404402008000c40500c44c0c100c10500030440c25001160842c404100c1019034a00685090f14007403502d4100100300b042c1c07050303001c1156a580c64500f10006010000c0c0710300210ba10080c640d0480d0701e00f00a0038031241e1032403000c2d50303140e19004500b151004644081240c0e0a07050058892401544660a5101d410140c5071640800a408000c01d03411101240c0110580c1d4800c01241d04000c03020740b8055203e250180d4018800e1014910781c078207288181003200 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 495874559 1250 495873309 495873317
    0x31213080301030305040e0f01060e0904060b1c06270f170a05090405060409120c1b0909030212130e06210c030d0311070b060d0803010620012901 64
    0x100240c640440907003007a003088001a000150400501d01c40385001c54220907007106c5c41400754175111003c0e1204161070318140c040e41c0d9082c0000d0078454203a0051312501d8016218403100764413094041040000110211030040c90000e01180f255042880102c0390030301415000d03421b00030754480c03820404101c1c2d0204c030300325001e0061484801c1180040c00b8540c03110384a45813180081e10402c029114002d040900076454107440c04089418000c0703010940071581412000c000c5541086c91540314640b03242c81054501c40300c00200c00c3c03115441021118020741c00e40d02400c219000c00c048502c58032189800001001000303118961040c0d800790b0b00036100400b141c2c109014400700c007901c1e41c0603006d60540d42e001100b40c803840b800d0034080b440726a01e507460200a14031488031b403c2d10718001e0502c043c100104030710005003a5164100c09542041d04203450544943c3e4400e0014040109202e03d5071914119100c1c00030340c1c14050041921462001070344030700210b0641c0030110a150823140030f40c100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 495875809 1250 495874559 495874591
    0xa0501140f0c07050a05120a03120e0303151810150905130606020606010309030516020109170303040c06143a0b031203010807030b0411060415090503030a020312 71
    0x80d0810380010100a00782e0700240603a5803602d01005560f40d85039000702c0c02244281101c3c00d4092010540401299044c01d141c8410550702d001a0000e095480c2c0e59011488004180581110b0341c091290a0200403103d50014295948001446150030b807088258a090040284445150f4403004590760078140742c002c1d00c2e260780f540018130020600c00e0031041c060b038461043c00306550600040c0c1d4850004e00f23013032040303801d19039004106104a080c101c041d80024944242168462011400281451480424036109a4079030a031a41c0c01903e0032514a085120000340742c1e4055011031042c280c2ca44e01c6241030960118601e07007021141c00c082164000010142ea8044004180112001c10900c00014920411805041c50300380c5901c0f02e0a0454828001048200000900c0e0720a80342e022514103a1601d0328501814a0b101590380a5840036010034045590072060400c009081e10b540d4401c0c06042da51000d258880c4140ca840394010303002000a102408919403080303810401c1220300844e2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 495877059 1250 495875809 495875827
    0x601180207021507151104090209040e030a1707081e0a06030c0f0e0a052505210702190320070302040501030809010909060e0103120e0909010f0f06050a050114 70
    0x2d52443c4000541c622140842e91200348683c00d09038010601c50548100903211000c2000c1909014601c40c402d9101d400003000c60254480750000c60b5401001405c5175194944c00c2c0e005065500100380040300070800f000010400b80c410320f4403c1c0640f0840c070b9040c4c1d00100081c0340500301c040003009118000e840d80e40000000d400c0d00a80d000401400482109084c1040c00600f207403940644561680790410042c0301e44c000d0071400904d003117107072400f031a0704080f0b010b141500d02e40a00400c1034851181201c139010034106d02a0020700c500843d600351542d41c001c4200d019449c03115a0f10140010700318a40600540d4012041a034029910400b10740b950341e0b403940010241c82d1300b60004c40b00540041b8800e00d055800c88041c0c409406002809d01015050025603d4880d1052002412801c240486502000d003d000c000184500280104030340c1d181000310035001e40029a003485030245812283c1158091503c035120688500030400d45009142900450b8000000010100d84600030041c0d010 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 495878309 1250 495877059 495877069
    0x801050108010315140108100624050307110d03060608060d030c021207050619020c0909060c0d0e01020a030608210f0307032c0c060c0d0324080303040b06030c03060118020702 77
    0x3c020f047e00c0006144a00700c3c85103003000d42c3e03402d0348003603116401c001c110001c1c00346084003c2800c0b00e01c1e1500b1500c994440301e04035190001d1002044041c020001c2604100d5032540041013502c41c1600c9080880d1110000d0228048030001c000d40005c0b0f240c070340703074005260000e40c26400c10303409030880d54501e07101d1000400581c82050f0900b00d283c0c500c0c40c40c0581c00d030184140d00d0755a00440f840160f5180201e00141c503090000c21102000400007007144a01c82c00e40c2c041003450102500841d25005003410140050015018044d800e08c83c46050b90703880c4030000c904440303401d0700c40000c40c1002d40f621040a4950406404a007e050305d07a90550641a00c0300d01e900480b207800c01c031110140c481c0810321820702d01d020050b140602c0b82044803590404c0e00080100c0384042e107207000500700da403100c10003540e00c03401d4600300002d1140c0c0300d0001e260f850000181d40107a00034082d40550f84c45000415a86500040350f0300e4154101c10010441040c2400d009245625120005032400d005640098 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 495879559 1250 495878309 495878311
    0xc0c131b0302030414030705060f0a090803180f0304150804060605180403110105060108180a02040509160f030c061d04050a090b06190512150106020a12080105010801031514 76
    0x60b40c08010001804104941000b0040c1c1d45805035140121540350140c45940c001c000003d0041c221010840b44e940c580c1c800d803080b58203c4516916418500b00702012001f070010809a14820184400808440401180c00b202c0c140c1e106c3d100081d481c61802d691001000b0019902c407940d074580010162140c050060351440d541c2103031000d038900340c80c001c2d0254440c8040c05200307030701d40b4080061990f0400c905940010020060401c02403414485030300e8044d00c02c0f0020b4216090200f401003040d000501d43c840e4a4034120303007800c1151111803049038070b0f034030784805840c11300602030030071906020303082528480c020a40140d151030002004181660303404d40340c1000e01c3d50354086c04030500152285441c1c005004450400e8038180c9520b010b02d400c046402501d104562540d60f41c0c605442c00c104001c0703c00b942202e140ca696039104000781d1609500303c2c081d50710b840045540c102441c4201c58150513544161551180390b400c1d03403101004900c5200c410010f882d92015100b1989a480c001c032 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 495880809 1250 495879559 495879611
    0xb010f020f2a040c0c1a01120f020424090c0e0612180109030801150314010302010302160204150e01050d050303010b1e07260901090b0c0c0a120303110c0c13 69
    0x10824179410310f0b10381c0113159017603250140c042034003005000031050f02c00c0400070709070400071805603000f0720b0002500401e0400b0408080f1885a030711030748020b088410034400c44080c10420041c00100392401e5810907510300c140c56202c50f0030841032a4951000d6845a0404038904800002001c0d40745241d0071a60900c405070085210300d801040034002c1001a0701115038540ba00340150088401c00602060040c00001c4c185600420000d00184c103200d010100e941d00248144803035459015188003610381c50250000c041e401c43c00126941c103095940c02d0b1695480802589507030b184c001c80d114a6000312030503c81400c4103c41541c42004c010019050b0b0340c4c050013074009610801d06103001e00d94003c10074460038640074050012a80e811418410072551480819607551800104035400e1003101541c01d90b220240e460041601d406070101e003601244207840c10881c01d0f28104401075140140713800c1d0036407980041620407090500490740e06009900000101d6444d004400e030300060512102d032 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 495882059 1250 495880809 495880817
    0x91509050705120a11040605100e0636030d0c03110304030209040803090c0a1d06060d090f0b101202010509010311161709010905060c0705040f0b010f020f2a040c 71
    0x131601480306020791620344000c100e8040080501e8440850b40c0107031001721100a208110f2103ca2031922154200c1e022260f044004169002c42110015141c22960b2010a403101035451071074464107000404003402c4009455100141006a508690074800d000c010b10b0540401d000010042e00c0d000390290140348a541c83c1502da01c0d100440d42d1400400501c454403c5007410020817421600c10070038501550341c1c03074401c440e540d6540080b8105200d00c08d00543ca4514101300070040c4040e00c2608030545110304c1d00c0f0380e00e9445404c0001d904c0445402800340c079011001c2d1a20040d030041004081910040c14041045109600b841080d0740006801520f64500c000f8041d00b0840c000e25415410340740b000301c071420203400400082074404039015041c0100000600420710b218108419401004002c00c14004d4904451100c0060701c40008200c1c0450442c8100c4070025001148034a4040c19503801081d1181c0b002c40c05007036030100e07a0741404155061014030700702c94135103009820760729030203407a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 495883309 1250 495882059 495882073
    0x60506040c0e0108270a05011e05010b0a360501020c0108010b03060108180a0501060303140307080402041d062509082a030d0c020306070309150905070512 68
    0x4280016250407000a20401100c140d104086a8200342443d400201a0500d2011012500400e50702d00c0300700011030145110b07910ba448104601504000c0c1007001d4400c108405c1304918200c00181c6100307002ea092421400e0001d04007031407143d04001104400b500c844001d000c008071a0300541c40d019480540c140c28501814007007541c04100702e0500c41001e1809120642c1361442140460001800302810000601c001c1807452480ea1400501400c03910180d50741c00016190860007881188012008101c09503900c80c1e2040ba03001c01c1d2481810551107080c00d5680360780c204802801d004a06903000d90b201c33210a003000104001c0f880c41801500100095500300240b105810b00e581720541080102440c0c0502c2108401b03e0700441095403140030454508804070004c004241381100d264040c030409459465060344800028001d6000b41c050b551a911030302c0f404c505580c401c5002900c65041e00009489004082d0300c1200d0071402801910604d984400001d040310a910701016082e62001d0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 495884559 1250 495883309 495883321
    0xf070f05010c050a0504050f030717060604110a02060a0921030e010b04020a020a14030706020d020702010905040c050418180302030d1a132d021213021804060908070605 74
    0x110401055040e01e040c00c0e03090044d4940010300d188100e0003540e0090801d1007003401151020854007001d070400341040319402d040101200e40c0c0d580212045407095003040801280d00ca07180044900d1003c0c0e0340d000e000c0ba40e80341034046c0082d081c1060f0460300e01c8a00b003044d002c0c40c0035100030401c0303c010365030f00403038040c0160ba0218251801102002c1c8110720401c00c1c05001d68000804e05203003513110500402c418400c6c0412411409029009407506000203a4041e208030994010320000f80f00b40c80703d5403a5516a824001129a104000ca010074130030001840500c80480510a004481542c041a24901c00402c642000050802140964030124000000780381a0245000e0207110f007034441c0340d18914800040701903904110b04a4402d58409100f0b4048404c00007502c000c15031402110000b001c0210342d00000e42c40302e4005401c4204036000b040840130b100300e440c511960001c0c40d4401c000300c90b44070050f150341c0141c000c0711082d90f5001c058000030300a9000e010440d003e1840010145441 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 495885809 1250 495884559 495884561
    0x21810171f0501080601030209070c02101106090d02030a1107030515071403040c0b0702040f0c0f0f08130303110409050f0103170306030a0b070c17181905010c080f070f0501 76
    0x2501d041c4007524280380050061140000d04241102d40483e01c1e8907264903006002c2da0b01c1c408000000c3d4000e5801400b9004c0145c01180322a08201d640017140c1d0240c2d03510a41300c2d251800c030111100141c004004500342070f44102d0b61442d03149510f00940f540150b8039500c5c68a0140381c00104601c43c1198001c1000c0c81d80c11801c06d05c0480c0c2c1806240e480c51400d99104541781c03504c0c0c020321040381c0d030202d0007001390745480c0c2c0680b07140d50300c400c0700b000100b2022001500c0712040d481c102000404100f400350302940715104841c0540203d01c0148102a65960207030080c0c64100c41d00c41181006000020304152140100ca00a403d00080071071154154100081c115410000341f414942c000c0060080e1603c000a418446c0c540040c0144101d44030307844216540c0c20791510252400311180c840e5058040c904000b030103406001c001c0408980d818801788041c0701d000b00000740788042e200388100100d5001d1601c1e10a654422020140b81c440d03034403154100c2d60407001064869150300d0452004006003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 495887059 1250 495885809 495885853
    0x30e0c040504110420160c05040212150105070332030c0a0f0e0105090d1509150501080105010b0d020307090e09011a0603060d060b060c030f0a030b0d02181017 70
    0x1001815190b40c0171044151061103036240e10303802d4044884075882481100c14a500107800020819561650515400d00c0041816201c12100d0a02e0380c00340041036006400701d0f0603281e85520b0b0725012507442034405110a0240c3d1000000c01400c3c00c42001c2c010783c48001b14402c04040800a459041940004041c034014030420b41c188040282c1d801603c1c2c1c2c105c0184c813120781c800c640742803081c107080c40c05030545600450181c58945c01c2800e500b0812081d180344800503041c2d03150402242e03a8806080e8280d40c0300b03100d050b144400c1000303030038060b00070741d0000c583c4042981400102c2555078541c254000c030f0229030085090b59501c00c5881210034a40a88801c01c0c41110170500750b040c1100041c0c04034010a00060486540d1600704071281c40e490141c2e0b842182841c1a66194681070b1101d40075640f240c516040041c1c035002d20f000451070140c102c11411343c1c016040b0b05002c00f00308150315090502411440c6480c41810340026502c4154044c07100f818020b1000e000c800c3e50000f00d9148105c8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 495888309 1250 495887059 495887081
    0x2070f0c0608011d0f06040c02070b040b0d150b03070807020a17071b050108060d0c1203090f0b19080a1d03131a16151103040b0703020a0f030e0c0405041104 69
    0x20340d403401d00c8900003800000f241c00c003c2c100d0300008e2100202034181d240079099806030956000c0428001044850f000c0903019082508905020a400d4410504125103c60144d251114003c0c00403500301c81c400c180d500c5c2c2c4042c2500403a1510103031500d502c0c1139a0301d00d0f50f03140030039030002407404100a015850000c0800549540040040c200400a04540001440203000704504400b140034440d0494034a4001c0100e00000003c031009070400514210707003070042095007030021900240c9078001790105c440031050403d84080c881101e00c4125060301001c0c080c200d886403110203d4a14000362a4a100a01d550714000e60f91401c0d0700c6090900380140b80d220443c18200c40010400c103212a1049803030310b5540c00ca011401e105a480c04900c0744d500d105c58100503a14005600d002155681c1c0150b015600682c1c03800b00ba6900ca00f4210181c0c4240c0b00d20b5000900030704005803c2500a8100c8101c00140e0000e03201586501004034040303800071182960141c80b0f0441c41911030410f4800d02003030310 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 495889559 1250 495888309 495888359
    0x51603060e06090703031202121009230f060a0819060515060409051b030103050c040b0906010e09040212010c0302070c0e06011413170607020c0f0a0902070f0c060801 73
    0x407a120896548a100c24400907090181741c00c49440c40101236411250000d140303904030b00c0182402405410000c41030300501d035845141000c4000441d103058102a400c0340d41d43c0b1241c2c4a5580c420003078180303c6000d080246c000420141c08600c0b0070050040300b41480152039a08039110031130a0813001e68401508000c3c120403420309841c201c0d1951000c03074055031800726020030315841300c100501806004034100d2240003404000807003000030200d00303858022000c40c1c05120b03041032902080f00b2502e0030759266000c501c085444c095681080056694028001011405007003c449e42c02c1d0309550542c80b400c0d00007640001d044080241d21130040018240d200c01714181c9180a40010709401c00038180801840c03804100c020242c0001c0e241080640340703401c0d80c1c820800b802c11841e0303075485084e507a2001500451041600c1c0303090200060707552000c0103000c220454501400000254400e00b01600c2100e001000b080c00315213100c0ca124014500f541d1603485941c50f240200544505c0519100110 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 495890809 1250 495889559 495889561
    0x604110604050604050d05100e16090b09270102160623040f060b030a03050a030b0409020f0d05070b0415110f06041113090c060e06040819030c051603060e06 69
    0x103860740c41c2554160f0b103050300c10f00f881b944a07082091404020070f5820700d06900304058040d040070045624012034441604503080c8179121140d0000f0380710341d10502d50300106440c00044201c011544100c02c824070074680e16594001c0c0c10766403400c3e0391104d10b042e034043c480090240d0401c80a803203114811000f81c0304a518004142c00c0b0f062403511f010348050300c80f0303003148089002d20009502604000c2002412a106109141b40c06031542c1c12020b05003000c03038a001c0f0701243d80d04050045e030400545c018145441c0b20101d00412407c40402c12040d41c10340700e03410001c26554060340040000e4645648900c440c0c52a082d0002c124055003d218203054010882d00ba040303402c0017560035003241d4802c1132079800c4140000072584820482401560790790800c01ca030024000168842e10940c1c415a42d01c102480092003032242602c03413413042d9803143e0f01141c041e10b681c0448036581c0006600c03e00e4542035803540d90322098a001c0000700d4a11700c2a0701d10781c0420800c0110311408031744021100280c40c403 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 495892059 1250 495890809 495890819
    0x211e080108060406051807090906050112020f01140c0f0102091c0c0e0c070b0403030f0e0a0b010e0604200405041802300f1b03011b0f020102070f050604110604 70
    0x12404080c000404d400d8a0700c0204504203203026035008100c01d40b900b2225401d1752941e01c10068101241d0582c1c95601d0701d000440c64031b21802d804955181c014004403c1150f240004580b4115081c0c7d0f03d0410000600c800c00d0383c1c210034030035a01189585000503807122411000c0041490449590b5140c0b9030310005100006a400b0700c40c14111440e003280b02109903500c0008804921420000411451040042008240d0954041c002d0846442010440ca40009031000d80c0c0d0b180548000d05100302245c0104590011641030300d0307011002601c007040a25004c4a0341c01d0550821882c00d1036268042018440f90400348680417034007203000021083d000898000c10700040d1450306002c0c6000e5070002d08050b03040305100d00300b680b250f428111000511042c201c6030b00c422000f401c1c000002124441c0c901545014040d40401031a82c0c0007501000710386060a07281d40ca5000903130010b5540a110075000715001e081c1a480b814000e030080d200b54502482c021480011890085125900900c81442 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 495893309 1250 495892059 495892063
    0x30b07050a0c0303090501020f04061805010806220e0313090b0102190b0403020c090c070302071d01060804030207122001020a170a120609061d010303140304211e080108 74
    0x440d050700f000074100c5410f04281f8007900c0351070b01403a020700300010005034403640050499009142c81080d001d0594944004440600003641c84582c042d46402c400010700f50a8119460001e1304e5a5000403192204581c250171500496200d2881781d00390368040111002038020742131481401d00c098100d0450030030301003554600744040544100c1e03210000404140c020030000c14000c02c01092801245000c00100c41c3c80d41c01400e0460041c0201d02d00010700008001c410481b80c4802e404910b090381c01d020084a1071400144294218404e0810000da5005042c2d0800905802800c1039440e5660300306030380c2c41d0340324403902003411580a03003100c6002c2443e8070400148400829109652040c2c50002110b508070024942c400203460071900062400d1558007000460302411104405050040d001e880c0320714091002601151039181e05200192002c0300643d0703c00d00c60a9101c40084e14042e109070407072682c01000003c00c02c00f0107015015500949c04420503240c91403c8031540d030500042c95 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 495894559 1250 495893309 495893327
    0x110a03030c020f010509100b0103020f070b0c0f07030302031e0405070e100b0c0c0a050904050a24020a0804172b06080d0503011e0b09210115030b07050a 67
    0x5810195500100003072503200740141985010107200a01003030902501c80c6131680c0d40012500d45c0d044c50b02c0c0e12608a54068000d40e401e000b11914543d08100311503e4400340341100400400c0010410030284100040e00d001070416503009035001178030307840c00b00e180c89112104045013a00d4101450204070000790b00003544015183c05000500c0f803916501342c0941c10b0401c54002d8005070601142c4000d000038002500180c060341142c0826140d0b40d1a0b06000c165503041c0c40150954000e1100c403004525107003a0080901c3c01400030b107009406107a00103013280c10154145000804031410b11007800100d011030030641444a20305458851a003004840c00655040000c2c2090321403100381d1003558482e4440002001e400040c0c5030302100303030340c0c0081140e8000d0240740c4080e01d078800c9410f88840c0d8001014282c55104150700e20b0164041c040102c00c3e0750481518550b10b490006c0e04452860a0080300e88080613100c04519940c1540340030048648024241e4041100c02d00003046443c0d071280307400b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 495895809 1250 495894559 495894563
    0x318061005130f0608070806040b150a0b030601050702060c0f07240c050313080d0f02010213061815021005060f09010b0304150c0906021b0306061201020408010c0e10110a 75
    0x1403e109540320034406003d03035030b00c100d180c1e00400a000030400401308030288558030542480c0d03229507500100400d0f0340c0450340714940244c5000024000f03282002c004541010050401350706100060740000c11550000c00c0700852a0400c0c11000400c150810401c800392130316950844062540c0002d10125448200917001000714001600f001c0c0141030040f01c08010768031080d041c04580300c0c54041d40d2801c0d41000301c00040c402245000f00c49106200360b030170121072841107402c1503107007620803514002c01c0945905685001c070000126881010100da104500540203005c00c100c3c0c00030b01c4000c40d0801002c4c42e00031162110352031000c0e41c540f10314906498514141da600c94440c2c2c2041980035040007119255207140c810001d860071f420541040403281c1036821034103018441c203403c800e499406c442d1503805a10086c04a4028904000d01c40e400305888400107041c1740c1c0d40c0075030b1070a540a03001a100829000e500706440b5003004410301501000301c1c100004a00700c400210b503940c40c2d400d000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 495897059 1250 495895809 495895811
    0x1006030b0f013002070c0f1703030c0a031b09062715020307060924200306040e030712090824040f050a03090906060e0303041403030f031806100513 65
    0xa0500285843c14001652080c150411501c07820149440c3c451258140a800c812100292000a03e0031007201c07240807140b03070744000d541141c490081581c0c6a8010300035110a164880d4241c500c01181c020000ca00d0b030580fa0346050240f03107001c101034802d13505442c12004040e00340100f0700c4604425032000084841040b00e6140e18100d00f035089003980147c09000b0450340c24046080f09002004001c00c20b64421500d10101144c00600e210080700c58031124049440c4005c03d1300c020603041d8002039644600c0241000c102d180c40180e0150031076200313440407581c0d00c0070079038000710242d0300007060005080300320020005020443c420103000354004942010450030400001d0810001d00056903c0603808003c403480441c492401425008a0f40503502c10940b40040c001003241c4112804401c1c0c83c00600078501c2d15003414100c8403050045820103406100c104024804404c0340402544a00c0180e10320b940d0b01c802d0611000d0801c00302a18100c131003040c0390400d0185550f04610703e541c00100440c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 495898309 1250 495897059 495897107
    0x611181315080f060f090a020910081f0609060b1c0603080c030a080c191b0803190b01020307020a05040b040e01020d09030e030604030509010c0602121006030b0f01 72
    0x5100e8080d000144a01481140c44400014200800600d40c09001001029503500f591846001e80e0b05c00340803070b0144040c0d8400c014070000340c00e06100d602d0300030400c4d01c490307002c080c1c0b84c1d901103290410500352f94488160559a0301c80302021403040034003800d0300010a224640c5002c0d0380c6000340c005e400100041d030a00d651a00d03c4044107a0000004541c003850f07c5844004503002e658480d00720301c1c0c0da000843c40d03032400512400f000c401100c5100517981843e92601204002c00c0390f0078a20042c100b019040400e14071030215907194040c500c207030500804e0318203014103202c000d01680c40351805035042d980140920001a0388a41703000040d640d040e100010301d11060320018010301250505a580c551000902040e00601508180400b50098640116060885060640d6403004403000390003c0c0d0180030410066218407a04031810340034030409402c03c0c91403200590050000e40303440702c7c03083d4500000c001050301401499000481207400e41c4898a03404000f03425074400001c1d40c820551550713 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 495899559 1250 495898309 495898339
    0xf26010b0f0d0908210405100903030b1e10210e0c0a0603020a030b0a0b0a0e011806050403170c2d0a080d050903070f0213091509061118 60
    0x540b0a105414041442140b00d1810413413059488005840b448901035400c0014180320500810300075039101d402001c40c0381145002030002e105c0c0782d80403420140c4030900c10840c1d40d241042400741c284610116030919285000700246a8400c4e20018144180321107400500003001c0c02d10507220244803400700e1030440710b04085051901864186074406a24400441c11540c542c0c041d040101954404011230501807042003004000d9104a003045141013051350700700e500c03c2c804080c8211042c1046241445055140c00032400c4580216000400c086410024420082c00600c10012201e0800e85000041c01005484d00c0e15102d64070307804034006a84410140541ca04503100c0d015000c1994494034291400c800142c0c490b8202c2d44005081c04003162140c403021003112005503012035070f59078046030b681c28094205414444040071603a5070503c3c10101d0100c2c4401800c64020000001d03900e20741d49495401c641400300c1300c01c03003001305010302e198500242e050a40401c0044554050300c6e2058 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 495900809 1250 495899559 495899587
    0x106060f0822080a0e0316120204150e0f040b0601110a1407080f100c17071b1502030402030d0305013c031410020a09031b05100f26010b 60
    0x41d4003d00c0002c00241484030a54002c0b888469100111300f92001c40c50302c0f100c0800402c0441c00b4090070b20002c120302d0130040c5095070090301e40708418142d04170407d580704824802c03c8011518000a50b020000300300c10007400030343c45035102c0c0c001d00380381c4850003510030011342d80d0005e002c00a0100224170360040d0411030801c07001004000c010201c62800040708a010303101e000a0003035582140c106161615203e0098020644a5041092031181c1b542d0f82081141c6446484580665901c0106040710108075241c1ca4000341c0702d010100582c1e6401c10f881414508000517004404040c07500b40103009440340d42c46802c02480c4000c03455901c003070305141e02d141944855100c0c141e800d038604c00000304022002d10701100ca002c2c0d00094845103818101d209081e48a00244d00000a01c0403800340002070314080b2007840d0180c02c001d603121541d20b41012070001904101014007048218046a80f400d910074440c09103020000001c5c45200c41149841c46c0200043c019082c0e40c0304003043c00c40841da11 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 495902059 1250 495900809 495900871
    0x10311040f090818120d170a15140f03120a05090a08010606080610030501181d06010e18010b0303070209130803070507030f111b0f060d05090106060f08 67
    0x4500802c1d903c4034130940845550712641c85071405903004014860110201142d80e9a0710301d141d403103000070348604144402c2482001058001050795440c0303450b00ca0042d4141d048040d111092481d13101180c0308040280b140d2085414600c03941c0521030912661182d04240c90060318142840f94444034401c00003618103080e900200360b00e601c2e10800152060380b06002d44d014440c1981e4081c0425900c007411010740704240a65004250f52a4280200002681c00011805c03055054400c182d407410528905041c82a40500c1c881314803c0280729590b0250b05010200082c1c100080215124050100380c4a004068001c0c3c80307412100f00180c030705980400b800600681c403410b0b507543c80c5050750026241d0b40000c24140e00140d004d40c2e0a40e0324900850014540c3c8140200916100c2021040b001595a40c0c0040641001c8202c0c0d0514840c0c4400010b08482c440707007400800c240c501030703024508407059980540104000c4030300e601d40d43c64122030526000300640200d0b82000c0000540d048108174 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 495903309 1250 495902059 495902063
    0x21510080604060605120307030e010c062309070501031806020309030c0d1d010c0201080f090c04020a0c05010f0605090118020f0d0902090f07050a031515050301140108010311040f09 80
    0x1e0368042004200c86030307011909458084943c40c0319445002515582e03401101402000b103034041e45150742960088042c950f41c14810800424031000131095200400c484000c0d8007800f2401c40d00b4041d107070380f060003810040c044c02e180c200140e646a00395020b5060b900d0300c0150441f5030000202e48401c10a000312400700c030850080303611240c403023500100066114030100160700459000c00c58550f2046100800136134050f03540c006291180320038100001c0024003804050b1095000ca0101503c0c1c6002403d1811000d0301c4090840005013445400d50781602c100d04640c600d0240d0901140c0d039000c81e07071810748500c208683c408003011b0010314000d200701002140c0c21500810300072180c0543c0e401c580c0045200b6165000140c42c0c0d04181c12106206480c0100800d0082c08100a0240710741d00c04a0084445022586503d94684100450b4400801d000000400010060000c102c800040c0401d2920a01c1d16a040e0340c55030329001c2c840345901617440e00c6030340c5460303003007040c50210f0b0020081d041e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 495904559 1250 495903309 495903313
    0x906070507080307060e010207031e030b220f0209010c030c0f020301090f020f01020705152a0609060f070207060c02030c12060a060801090503030a05071205090c0a140102151008 78
    0x2c0c0c58082180daa03420052044440c0d9081042c030407003036003041c02a2100b155040d101c00403a0f000e0001e1846420020005142c2010382d10140c1a26035940c2c4020400902032030022110303001507840b0281c0c1030320410202d080415004100006c0741da640f1189202010b505442e15800e17444940c502401080b0790007001035030540c2000d0440742404080d1180e01295482200da01e000c6052450040ea1511182c1c03040d164000c413488021503441c010503000b0401f40d4141c95a075811441403c0d2550708201e2441480c8009921540400000c1001048500c2c0c001040c0f40b8a10100e1809450081d0b4440d002d0141c4810000280c14074021510300304054002c024005100360910240c03009516940e103000c86e6807400320ba081150005105406100f586e480d01e40000c0910700d1540d502141c60050300d80a040031041021020040b900c00880348103070341c003c117a24406080c0d030140400800c01580a03a802c0640200b003245440c020a0307800061801b4001007150301000a60b55002e202020003032640d01c50b11840c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 495905809 1250 495904559 495904573
    0xe010903140c010f031a0112020403020913020a0f0b040315020d020c0a0b070f0806040902010915080108010605060301081b030c13060924180f0216050d031a0609060705 74
    0x210400305081884400a0382c1d405501142807000300d0a4901c4c0300c80c0580c0311b801004134403110b9482623401ca003640100c1c69015240c107680758042400c08608840e039011107040703100c81408519004c2d140d607000340701c01d1401c3c402503803c00d0304600c800d20442c8001010101010628041c41c0f44540580c0c0b00c030f4001d00411500c0310b400000c01525460b461104407540d1001c075002604640c080c1e4003030380c042410355590104030350b959400e000040510f0301050b410703c18211000a001c0c182822070f0101c080c05983d61a00315450889818203603800c41e00860b210344c6040c0018040d510b800204a910100384c46520f00c072451105000c2070801100d80040d41d00400040318042c48034038917400000c00ca0704178820801400c3e0003010070311361081140740c01d03082e5403020070420800c4070454140c07512030400813800042c1e02404c2c50008800c0b83e021000a590308101c3d203c01c00107001044c007803030545c01c0c042d08041c0141180b400c0d0b10b95294001904c11441800e001c0b41121603030300c0d040151340845034030104135442 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 495907059 1250 495905809 495905843
    0x1120507020a0201020d050310030311010b030a21020a022214070908060606090a03030804110402030a05070f110d030e2103060a0b090607021c05010c030c0323070e010903 75
    0x159024480b083c0c0c09446460344400d46036118800700d0f44140c40b4a070004103c0f9042d581d080310100a0700b8240300c40d03507495610001c40350b64207100e51541c00b841080054640300d1000c0d12502a0840910050155004100c40c80c000d40c44010700a2031400c10042c0215083c44024050001042e200400ca16460013190030080c200b034202d41c100081d118a401210600e40e0755108000311403040800e90364000c001010100002030240e0102500715100b01907603061102124041400c07600219081c003009a11081449051074001441c120b0203a69441c050480c000320046983d61224071818480425a45082c80d005400b07082c001c480030743e0045400c02d8008607071201c0c840d071183c0050390842e114540b10403000072840249000c80c1d2107403501900142c01c1c8600340d000c1103c4200d003140d540c10b10048104a82000840a1055407072401694900240000759640002c1c1162403e0407201554101013201e0b0260741e007000000d0f0f070f01800341d00c3c140e1030142076000100c2d003003e1140e00c01480d1200c00c0d040003507 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 495908309 1250 495907059 495907063
    0x90913150f15050a0312090b030703020415050901140313020402070c0305060f0103051b0a090e0a060b011418011107080604150219030504020604180b130212010605090112050702 78
    0x807905000420034882c0000244030382240c4146403103415441410064108002081103180d00c8034401075081070b0000d169501e8038059560f10441d00356000941c002014400c030740803610b0b02c00e04411940b406600b0842d103000040c148100f460f0303941d000c4000120010b01039901c2c11860074491036000c0c1096407079041501c0d04448000d9240012103140c012000018003540102c100503040303a0300324005041800d0203c40d03c0040c02c00b94800c040d000100c41f400442c005400e4018210004c8607400200320100482c20b10008071004900c007641040340401001a54030703440781c03d64501d111072030a80621280d9220050343d440300440e51040c140d0160a00c0010182d50111364103100c1d03030040750850200304480801e4422442200c4404810b00c00160a020119119600240c3d10070320113840c0300e1800c2d444e1b03114201d100c03a61048a080041d02c6681c040c81c1c0d414101409800c00c5548001581010300b00803035804011414041c441c01c002c1c011901c00c6c0668440d6610311382644e42c2040420081c1411a0025 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 495909559 1250 495908309 495908321
    0x270321020a120b0102011b05090307030c120b06040b0a14030a140d080105030a12030e1516020708070b03010302010804030905090c03060325120f05030406020d0f080c09091315 77
    0x51815143c8240024254018054001c1d42c0b003201da030a0382110b40c4c0082c151429005032070034a07010321074004080001140300c601e410140800103011900d0000603d0920310382c0c00010103682c092410060f241410ba250354500400792400101c0c22101d91100b0004130f8a8041c0107d0042c254080300c04036000c0442001c200c0d0451a1982e68418015a803a02c06044c1c0d2101c18600c0140054815a05201c10740d211358031203d4020721150540302044034200301801c42d407409039440d10041b10486c600192694041114a0007005140040d045880c81d005030043c907400140b102a0611869800081c105441090540c01404006049a019047c00d442a0f007064104642c014028480d00750110b10301400d81da40800b0324011042c0d42d094071070400d40c0d807104040c42c1d69030841d80344910000c13802c006241400500041c0c04076034020f04110851060051420308445a041c01703222408080c803080d4405001280c50807107082d664074055444690840012580c000405040c8480b50300c140040c04610750800 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 495910809 1250 495909559 495909587
    0x60d051c0c0c0f0f0311061902010b0f03150406110f0a09060305060103090b04031d0a1706060a0b0415091e0302041d06150105091f0201270321020a 65
    0x1c00e1082c1e00c07003ca10451040c50302418111855103031007040003900d02c00c41b0b11071201c1d024050703d0400c0010142ca030090200080800e026035181e2840410710b0a042010401c0201c044004100c421310401c20a0100b21020700080d204a0301c3d006030b40c42c403007020802c50740c503103010303003003603039840040e00001030904c4001d0048800003410034000c5083c56129021f007404064108008449685880d03400ba40d120f028540e690101d4601125564426514203000800034100049035403680302c050b001007828103400074503851117040c900d10180110301c1c01c50700b5a401c2e18601d5950b811041e0880c20281d0b119090303644494151100f100c91a02c0208a0300450740c116442610144041c0c6080d03864450380f80c46d0041a560313198050300c001088501928440115500107040c95450b00c802000030500810b071003038204941141264128a1803942403107801d181900c03101e65101d41014110004401001000d0050204003070800c160303840082c158178402c61019103110840da680084c1c00040c00c05030106040d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 495912059 1250 495910809 495910823
    0x3060f0c0504031a0405100204030807050f0d0503150105040e04111f050a12020f040f06180323010f0e01060f050a0602030f1b12030a05090c010503060d051c0c 70
    0x10980140703001e003003a1800e50358001508242d940320000c1c81070702410000c2058030188120030307141400d181c1074802040614000d20a040e0756002c18104585040c110500c1c02c02140c1c0062110031005a010003a25040380c041c451840c41541c040300120b880d4000c2e500000300200300a030501c01000503400701c20300110800d480040300b000e620480103210343e03400503941000c03034000c114201c8841e01c1041c1c0b400e0315141d0321314010b04055425001001c1d542154201c480400e0000005015140d0440189510141020f0400e41c9450031555181c0c613104071110207044400c42c80d00420504102908044004455114100021500c002015010b0012845070600e0740c42803640c08191030902107140b40c146c60580c0c0003103103014208602c80394190b004444101c050030601c013245c00018410b0101c1105805400d11954580c100020303600211640a082003480754000c1c0e03000c80701a6040000d40340d03c80710844d00d0409020907800e11a041620309060300c080c5003011145031f03c0d41070b04180945051801110 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 495913309 1250 495912059 495912071
    0x1e04050f180606090c0a03060306020a02060106022b0e030c0d0506150301061526040c061b0c05190306050f010e0f010f05150712030e060c07020f0d03110703060f 71
    0x114507242c0e6403e5804903044661500018500301e054001020400f445240c0000c00340e960b0f4561408a8000400400c0143c22107c0100051390b4100507148407180c40c0303040d40f029036464000380309100c054110180144203503110609020740d4103211040e64400c0c05800d9050701d468074901a0f8682c41c0441d0088800001405152040e040510400c7d003a20301210316010310a0751090103807008151703003000b0007511070400be264510401422013140950721a01e070780341038242046406421200049088901d41c000e01c4440340204010310407070800c0f94004e90312088000010f040c2800240c2e0346403c068401420301d414040080d031a018014103d410030800ba20765515950319008102c00f0038895984900380c42c1c1f9060100f850a84071003e8144000e400a40c6081da0560300d00388481d0344190b550700401c1d07866548100030701c0244143c070341c4249a5403e852802071640c1c005001190360303159060040c010908500c0806004844210200c8080f5044441c2981e6138985000a001c00304241e2502c03600f040 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 495914559 1250 495913309 495913351
    0x302070801110405120c0d11011b020d0b040303020c0a0c1e151209150504120e030d080406020706020f07060e070b19030605062101050a03111e04050f 66
    0x2100724106218501d90b05440c2a18100402603103048209644069019500c03ca481c103a4901400e607003040d1050f5901e80c0014842c0002406114442c244141800411030401300141c1e1803074111241c86500c034071081d0f40c0381c84a080890080c043d024403966140700310540103060142241000341225040e900c505190741d05802031003000b662a214007a1040c03c054030542456018100c004100110041e000608010540b1071005403030698002907000c940e900140002d0100082420400f55079608001400786030010100c3e54501d02e01d595242041520b502150800601e41c04445039190000010354460035034200c00307d01076000700740c1242d000e854580c5505090740c0102e182e03030407100300805503401c18240c0c14048a00d100301ca4800405c040e81c4880108041d51003001a1141070200154038140d22842d0000c41c903400c0040c2c111a105602074002040010003030742c0c40c1301c0501c2003a11203030850491410080469114802c000b036010382084100a00380400000880c440c400c21040c040d500000d10f = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 495915809 1250 495914559 495914561
    0xc0601050607050c12030f1b0f0120070f08040603051e090c090618010e160203180d0c0305070b130905041709011107081608161a040513090302070801 66
    0x100d20001d00c25001180c0307071300861a1000708110842110401d60b441d00c5541080e0790a194013100c403041c03200151820018060740200075450704c1d044480c1c001c1114581140350b16010300c29527140d00500c0800010b076501000400080c0c1e000707903940104940d40391502c4e04805005400c00f1211207020f039101c0c5030b820110a40b4a01c1542c000c1e22418041c00035042140b041c0450f100004081c1d68000a0a569580800085a8084e80284003441e0918441d040c4840d4030311018a0803c0e0120441d8018801c1000c40003141c140400102000c03984e11592054a140003c4c008030281c3c005407240c081e01b840000e58210040041440102d00d100c1d040000c1e4849403450f00304e40b800c4c1c4c6c020303142840c100d0207280c80700030003801480c0400c0c050400b2166170000d41d03101450442039401441c4241c01092034820701a140f02c1509000e0404500540001075480c412400b2000b10381c8220b0940c0b5004d0582d429901e03142d401214003409028041084020113002034034040e0004440440041c0b2603400001915101 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 495917059 1250 495915809 495915817
    0x11d0a0b040f080c0a03080a0b03011406240a0f030b06040b030f0c1611120c01020a0b0c1b030c0d0224100b070f0b010515030406020310050310020c06010506 69
    0x301048092068035a40c855400a205148088402250400008000900400c0103000d0203210341d0f1041100e00e84072582c00290b8005400d410300a0b814440c5060a00540f07803070035580001c09543d8902d040640b210280c9034401d00c1c0c040b2019459000480a0500303078040c15400c107900c1c82d41c4040c41110300a8052007610711803446404039049041c00803403907903130704000803a8010005500c0c0380d0500444003180c050241d4421821694440358101e90f14640c00c1400c00a2060002c550142213255141c2d40043d444154801004011740050350000b800d10500b40709035082070101841002d00c0703d0055010b19580d901448624403e841150080c00031b141c4006072062101300c1c2089000305c03d0300704070708040c03a0880c054600010101d4070a00443c1c01aa030001520109004032903081d40c0744280e0814401200c01070700103500032040300a004001c0d0b4000021a900103911031070069032a80c0c0c7e5030102a480d142038100d40c1d81070240c2c5100003143c800d113802421b20604070109407940f5076683c408200c12841 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 495918309 1250 495917059 495917063
    0x45080d05031609030b0907092a0c080c12030103020310110a050d02070b1f08030406020d050d0b0d031107170703080a12060f03150c0905092205011d0a 66
    0x2420030000c0c03509810159080058500b03400d24031001a00d903030b1405494902240d03000b40b00c1d808104208040300041c01540c00c07814042d04403440c541900030040300851b08511280c81408401410350307040141c01001c03200c6000c02042981d042007054400c0d4244c651003807000342d00c2807190341680c0f209981148600400c021038607143e24a0981034840a4445c1e0300644085020f01d035090002001213400540003e00c98080000d80070712007598441100543c4820f03401050707080e030042c0000d0102540010b00b4042071300180c10b0241e1501080c2a400380901002e1004036045441e251808041541050503248000035420907111110340310560880c00d00500d805204040e40b0040c01000424500f40040c0410941450710510891030913083d00c05890084d44080d00d440301c00e000030010701031102c0800060406414060200d0303000340c24014402e0444c2d006503841000e154000c2244c181c2c60700c40d9070583d5414240385ca400c061080c1401e50082081d10f000ca1180ca12401c000d00c03444601045510040b5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 495919559 1250 495918309 495918317
    0x30e0913020f2b060c170105011803060905010f061401140c0106080706020c04050601052107050c011104030218040c0611010902150c010f11070345080d 67
    0x1662a0302040b150410100c591500206a02d03040f80100400c6009694000e036001c100e0820490186421002c40e14460310b05401c0000c039401d0f4044283c8456041411210240790642c4550036406000706800000c0d44001c00451810030341808001d019002000c0c450200b00d0308000e400d80d11080f01751030040b80d44501c5e00055003c0e44c06442021141d003c0c3c040c3c5110100009646070304c0b22a0070b45400066000000580d00c40981d0150030725090040c2030b4060400c1c03030b0840c1003100034400d00f40c0d142021000c00074503150001c00030301c40354810800e40e51b0429004009020a4004806232141c1d41e1013801309901aa00344450007a4110003118400e0040d40c0c0070f5541c231680c0c0d2610324111880000504100650b54940040401603550110b424038140c400b0707038403a1703590090f072000c180c210f0342c1918a900b0712500307014100360302150302001e40345006d0b01414459810070b80300f01305a8090340c2025a11f22400411f460900c40b4482c440600c00e841003c0c032008407440ba44441006a80300201c80e1400001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 495920809 1250 495919559 495919591
    0xe0c03030909090705030d02060109060b040e04240203070903110301020f0702120f1c0809060702120906040302180402030f010516030902030a0f050d12060b0d20030f04030e09 77
    0x30b402d089020607488503a201c10340d8001c4c0d49030000a404c001d400810f40b0b0060340240c0040c05a00940d1040b24000c0011040e01440c051800025442030003000304040c00d4004541011804401541c40d01c5e9004005000c0c11035580c600804080c0c452181c40c04240c40d81a28001c0c00724071fa040501c00c8071241000d1203511410000b159007000740001141030b541010b40100c3c10003840f111020042c400d1035a20a03070307205001c8050040d0062114000501f264120383c081010310001c0790700421010a0514403595980e951003036000030824502c203945c40250800003da40250114051412981c05a4421419140c0d5601500d104500f070300c10544142079141c0600300d08140180c02980701360285071010f030646941c403803151105c00f202e165442055496422102040c40600e6114090a0250800e4481081454206044031182e8029040701511803135503400380c44403540012180c140211044581a5980d103402400541c0c10841601d007100882c82c0c00c60400c1142c5403c2e50381e94402c2c401292400e5407 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 495922059 1250 495920809 495920827
    0xc0b070f02122502060c0102031905070e0f13061a1b160513090f0308100501020f0a1103010605060c010c02010b0f03030703030f0e0717060702061b0c07090507030b040e0c0303 77
    0x90b10000f0081241d20240411100100d01420b0000e14480c03901d4540c1e00303040d00c0004240505841000300400100480754510100c0303603443e07403011840c0310400ea8201c144401a00000002040103402c03440d1600084031003444240000b10040100c0e4602c50803e0040c54601c0320503d550301c40c0f06038501b000e5801804140243d0034a40a810400e41c82545e010844810645070868400e00c03025003500042d6411040010004550035100000c020a100404144500c101d020761030382400c031802070411b51f801071100c0455030309410035000383c00002d0881c0d0707070b9641c48042c0318020001104400f0165007450400c144500d00350400705071200d0098041c41c6009001d0343d0860003005011002c03044580e0b1181c1d07000b00650304202040140010154850011101c110000d140c030ba4018110002c5600c034a0401040114551140d42140048400e00c0d0b1a0148000c0150519901e6004000c0041c41c01080103030459242c7c1080a9220042d82d04120002520300e00d02e40303c1001c2501c07550940e1041003c00d41c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 495923309 1250 495922059 495922117
    0xc060408090414040b0603060709140108090c12150105010c03090e270f0601080a0f030c1502070317060109050a050d03031404060606170403020705010f0c0b070f0212 73
    0x10a1001400055102c018201403503d081d0151820b5075492080d0f0100001c40c2810040247c100d0300d1420801c4913a4035003a412980c8542040c4500d041020340408140100c400300101c2030b915100500e103c2842040c036045680d18003031040a01107006880c0000a541d50081c0a104040354040c1d07140c190075410039401800c5a00c011381810f15181d418860b0745010f0700008c014608210000024105640d80c2c50303c0c0c14034103001a003012405402042428000403511b020003d00544d01d030600c0c03048400e0600700100100c44251144141900004000d404c140d0701280c40c2c43c01e82d040c034070001585d88a140c011502c224482c001c00d50881038001051100d4035254049510641c0300c1d18011070146540d4200d42d11604080e00c0454020b43c850030140301058121800c1d25207001d83d146101032a1805440c029503900061080a06204641c1d0700d032108039100c0e07240d080d019600005620a14100590003e00382402c442d01140140120001c000c00d40d41808115a582c55401c0c40d0183c00b410b0700c0080c84 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 495924559 1250 495923309 495923317
    0x6030912030c1106070f0f1b02150d090803011a09010801090b04150909171608070201050f2209060e010b091f02010b0f040504030f030f06050a030b0610050c060408 72
    0x14090060f00303005515000300402c085481400d49658220b401071304200d003e00801800f00b656401d209075600e202455003d109881400d02d501100d481d8041820390030300982e640300700700640040030700717081141c0e050050359401181251408408410740790108452504c81d8080c0f0148a40010404001001004a1604140100d500040001030081f0300f030031107020360070420f42c4050340c0d441d144c0e00c16006001116071184100030420482ea450101e00e0407951000e0316904c41c004001000101e41d040540e4882c906980c40c07100e850904659032200d030500311f40200d1807003106d02034407210503d01082a50460059004540302e8040410043c1d09003018000544c2008800582060b0709a01c01801c44200050072003410050782c0001800303410000070700a00350700032017400b8040e90410382488000795215201c0d403d03215441c0343c000b4012402d50701240280c03901e6070206600c0041214003109101460000f50302031a000c540400a140c0010701c2501c00380200c2c0703802c580070f400010000d008286240010 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 495925809 1250 495924559 495924581
    0x1052706190b04080604060c030603030203070f050109060501030503070606060e010e21010c1713080405041505040507050408010b0904051e07030501060b22080d0e180711070603091203 81
    0x36041e694035101c06010300c1d000766000400540c400d40c02d000521001c0c0c40740e00d4622086203004e110a90950b00c2c060354900ca90ba01c010000d03c20100440d09100081d4070032104d25a00c148280903e5940e0308016950f034000b00002d03184c1e0b524040f00045c0c0c1d24080c58090300803c00c181c440c5007240e881c1c9030030040c0300c2e901c07008441010041c0c03080c040c0c6010b0080c444c9e24810410750300c03030317140d50300b85010300d000d9140d4001c00107484241003c0c884804106000151401c80c1c0088401140d01003182c141c04080030200c2d4003040d04181010140b20030241c0041c00361054a050100800c000051102000b2064505940c050440c0c1c01440b1498104850003115180e0181054100d43c0c182d0380d04d9417034a08560507070b03000541d289008200309184003c107440e010011103541c6100e0801a090507002c83e1a03100c0000440280b00c4001001d01c40d9440310b10411200b28000140199180340401000d41282500e4142040340e0080b90300210b0482d01902c140c40103580c205240d10398070a145a4141c0040c00011a5 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 495927059 1250 495925809 495925849
    0x102040302090405030a0914090f0a0e0a03050315090103020a050d1716121d1201110408160807120807060b09040f050d0905150904021e0301052706 65
    0x20120268890140365405148241d0083da07440300380b048000c2c4103103c141c01650740c460f00d0008040740303942c1e0718445680000605500c1e0005407541010500140100c83c801807050240090300700915400101541c8668018401e440fa0081000f00b004407481c02408003d60182494201f0300c100c3c10840e030308100c8284510a500c000f0200001190080d4000301050f0307035000200041d034420001403040314241c4032443e0a10b44090300260004407401c400e4115498029000a003c1001c0c02c0d1003500440a90915500301a640f20746680610381c070341c80c04803517840c80440c081c0400110080b000440b00c0847c0d180c45040da0104420b03950344084c4e41e007c100c09443d0f064031509011110340d50055850302075031080381d00784248040c2d482c025080031002c401101c05d02080fa2001c01080d2100940040711000c0c80d041e10b03540d0101c03400003030002d000308424243c43c0340700700c80910145041140114140c0e501210750b1800b01940440f84c00d0080103000d6901030303c015100100391242094652210902c0000c19 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 495928309 1250 495927059 495927067
    0x3080f04030c030c05011b030f0f021f0506040c020c01050a050f0d0c030e0111040f06050c03130618120822051210060807080a0b0403050409110903011b120e0102 71
    0x154110507941c00e0f003042d2522582020100001d40c1c00a0318000300e0500c40340304461500407901c000c1c001c400c0500c90901404650440c007442107109205d058442000303109007030382c08914190310b040206400c03906180640d2078002104205070000607158140b201c1650f8582c5004807a240895294109501c2101c040c4006e00540030b400700b0501070f1030f0002c4074030743d80042c404c400a00203c1c25999440010908807400308818000c1c10381e1004d40380103682c4182003055403031040c0704401d4a14426200030345240d2850b44000b249855101940540d800d10908101158a80700d9514481e503940d04071b0300502400040100d410583e4280340b0103e652002000e80c00f0083e40c5c2c17400400c500d100d0000700908150014410051988400e11811015105034001803e0076401e1104c0b45940700b54007907002d441802d801d00007a003054810745c1101c014044004084c04100d4440101500d0754000d228000c1c0301e03500f81003100e1074142c015183c02800300c0039a62070a411801ca61a00704c010201480d02d1040340d50208 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 495929559 1250 495928309 495928313
    0xc031b0405060f0d0b09040c05011d090403020a12020303190905010e0703050106170a39152715020a1704031a01081b0406210b06030705030703080f0403 67
    0xc03010b00900a0540f030956070b00c050f01c510040440f040126442d214040c0c1e0800e000c04645030412072019503200f800c01c9604a0001e0705007100148070740207450b034013414401c10031080541c081240809544500e0080c4e000c1c0d410280c1c10b80e26804102c1e0781015508182d00f840d030540c0301641003032103d94014800090144003a504503401e1280c203030819a034aa442e041c04210402000c2c450b1020b040790800901080041a940d41000401c100c1e40c1104401c0d42c4440249141415204011003900707090101c800c6680d202107074101300c900d5031000c41c08200b0f0301d15035000c000455030b6030301c070040c51520803d030440342420885080007003e5000841144590020000022004494500c50303028a0131030030348a600d14030700442c0e10a080000f40c004a03915500400120030002100c036909043c038640e502c00e040001c03010400504069015034140c0342c08042603803d4074494640945014065080002690b662405240d070301c1ea0640308483c0c250340841000c01c0424085801342c040300445505141c5419078036 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 495930809 1250 495929559 495929569
    0x210c0c10060618030203030306060306040b0604140910080a1410020406031508010902010c0f060b0a170c09220503281106070509060304051c030f050c030c031b0405 72
    0xe80003082156440606020840d08003034080e00d00710b410b030103850034142035501007a140e0001400f80c83c06404040086034007075480380c00c1140c10074809800c040c0c490303641d10f503810204a042c100e05402800301101061106034072805000039a440a40100700001c655a0b410070599180807100f1410300500164203044841c41c00204020100c47da40400c900384000b02e800d03000400340c1e00403801c9a140107400c10060740c129450140702070f041041014a90b580f0b0400c08050545101351960184500401041050035000302440007400e000032a102c40c4545420701c80c02c1d13801603e810729144107400c250722000c03108009158040b03108009403410584000c85503142c0460600031441d800c0742030b0000780403103076000480c0352030420400005c00e56824640400707491403040368591409100c0020014007480804c0007035115400181403250f4a03e26600c40c014014414444400d613914105030104500301c02c0300d804e5031b00410640040c2031658443c100c5041c030208a2a000034074100061000080507611 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 495932059 1250 495930809 495930823
    0x7020f0106120c090507140a0c0f0c090f140604090203070e0c0301060206071e0e04021309062102090c09120610030b0c07030f12020d0617070b210c0c 66
    0x4400d0b200e07064940e06140c034510300362140d081600014586010072084941c806003501081c900c1c00380c01940c074891000202c6041503070380d0019100420f01286d1100b0403e07003003440c1c000c440e0780c10707010444012191040e4066403104101000e503900c0f01c2e40070070107503d007035070050b40c1941c07006040300c00d801da40e2000480404001c0341c0300ca080d84004001008425014880140e0020242c940056440c000e83da10007134011032020101c0030003040640480551325290704503500f0801c2c0349105010b0a5550412001a1a2a00a07000340022500990000084100340c210000f5401000e400e5203644080000c41181c2104072840d41c0207041d85034207121002c0c10b00c0000c0c05880e03402e003034940c441e00358102400c8901015190312582d01f41000320b80c000ca03501042500d859942e9203046800e0740d100e06400d20190248001800400d80b40050006022580032805901140ca04017515809c80c2d5809248456000d1410140e90a85443c1012a4841000e884090b441b04103406801d04210a50b0703001072600314 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 495933309 1250 495932059 495932069
    0xa1515080606040506100801140a0905090105090706050a09120606050603040302061e1909150f020909010504090f060f20030a05060a08031206030307020d0c1509050f010807020f0106 80
    0x1050900c101424035015141c2e0151042d50b00101c07261031010002c06007d07052181d034107000780401441c82c0036034a005060b001015108818040c0d030030400102d60003021f05581c0c0c82c0080c402e4883c0000c6040c0560f0944039440f4143c0c07109250f00e03141109100ca001040c1e2800c84219a81e40008601a59540b02560089029a0007003003240341400000f240803c0c901f103840b0b9002c03921410000c5080c4004a41041d00b003100794081170380703012458407005004402034000f84050505c07540940140c3e041d0b0240102c4c003011108003072243d17a1030051008036001844c025103c54524400080410107030340000b10141c4070424001281120158500781020091a80c10081b42d000402e01c119120340e4026680c0014044841e003c9003894145500e42d00d00c030760038900050031200f10016905980900913a0145600175242c3c10300c00041d480c1044841c2280c0c094014080740c0007414503c1c10744212513500030303a60041c00030384808004500645041400070032020440c480c2c680000e0503088213000b6040100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 495934559 1250 495933309 495933313
    0x50d180f090e210a12020304080a031a09090d1403060901030f081204030509030d210b220603031106010513020327010605030106061407030e0109030c0b1b0c030a151508 74
    0x5000344ea0003800d40d618001d8415000c0c0c0140b06000c0400c60725422038681c102582070000d4102034241d004281d80050354090f87c2c0c00061003040040044012901400481680e0340da09600000000313142242d00090340c0181d00080c1f448010300c0090720740c03111003025501901d00a814000010594440e184044a0440005002140522031800c08000c910302c03210041c03c081e44845000d041420312480780038004204551200c0302c1440940700c0f004480c404010511500c40500d905007008001342c4036502c4200d000554002c8240350341000810858140d500080080e0600e034283c000a1019420180582c8080780d501031044c9040c481c03a0342030118902d40100082800b51900042500711581503001c0428889513440306003070101890116460142e0500301003094414610049441d40d0154100030315030a04802d02098a1410388003800e04401c010812500302c1504250440c1c49003810300c44540c15610010300390b40050141034180c001070480b40b0300000e409030010b80030411801680d00c40303d015 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 495935809 1250 495934559 495934567
    0x20316030c2a06030b030303060306070e0a0503100b01091a0406120e030c0a0c06020307031707030603020310020705010c050f1822020705070b0403020a03140316050d180f090e21 78
    0xf98043c040c0b610211000c80185044d4901440400d8450000030a041d007004803000301d950741a83d0b84182580034050103130448100c4c010240001c8001d2100211860202c1c40c43c1c0c500084170850401b06528884a074902c05081c580741080c1076030712404003c09051042d8551007a030491220800c080d24821035620002c001c2c40c1d030300d41070403604281d8a8001038115001084540007090300804888500000c0c841499403907510384908800516068100940c1800b82035540100421140c010300340e1a0700660003041790034010082070b5618401c50110749050312040c459429080f02c154800020106d0107131005c03c1b0410b06124400340380300d211280b0b10303140794042120028071508004c4000600070204e812858076055400003035070310015100c000c10b40100c108030a91710b03d8091054809240b4a80c4841400c4141880c0c1240c455842e1911000082e03000314045800f00100000101203601c1e5080713140019003032070302040207082100c8006903184030704543c070003124000c0b6804410584003042c1c0d10f030720703 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 495937059 1250 495935809 495935819
    0x70203031f060929040b130503010c0e06030a140a150b0f1c061e050f0f060d0e160b090a0801060302100309030c020925020316030c2a 59
    0x100d028030070140021000206001d01080742c0268002d02a141060440a44200843d08428048200c2d440418100fa00071900140050718280a00705c0e020b40108040e4200e030f211810300d0708980d81103000d5800640000e041e520b50b814108000c5800042d002d0000c00c624031070581c4c10300400e001390f42c0340e45050b50783c2030307004800010034500c0303400343c1600702d8000e151105414002798035014803019117440d41c030f0aa41c01d0200d0b8240754042c80c01454400d5042040d1428444250340301e00c4948511402003008885800c0d15140102103128424001000c003810004510034400c0140404007070320300d0034800d5509030501a4003561204004040364003005903692124400d1100500591b400801c10f40e040a01c180010703070368000d40301001400d40ca00042c3c014460304045800c0c24a5101c003a42000c03d00080c8420014021184207250a08203100d00c144052024101d035644a0f008400070211174000180000a20540c01d411030300740604035803010301031031450300780310150001d0140520002503002048 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 495938309 1250 495937059 495937081
    0x5120c0a141309080706020c1c02010f0506090f01090209010921020f031f0b06160f030e0a03051f110309010603020a0608040302100b030f0312010e0604020921030403060507020303 79
    0xb02900c85a40c00b849038850b07a0f60b40400d81d00995900074039407030300400c5100480b941008541d42041d171846180c411000d0009000c0d0003040c20440c0d20700164103040c00290141010b19985000308811192440c241e03180c00b0500c80290014000c2134100308589038000307541c27104c5e203902c9940d528407600704180300081403040180201d84104880c1c06038020310008032010300048564404841e010704040303505090000011100d11a6a81450301c400e0844000014040b6180c1002040c0d0321944030b161503606c014040040a41e04e501c4000e240768410510000c10400b1007025800300d4030040c5003c6902010184100d0698104445c5003003240e44d5075a04000b52310f89020144020f1849082c035600313078241514025144d44c18616010304154950310031803041e403804c00c024030b003000b041000e69071211003e904400c0300d050b0a2003501c00f0081c0c00408903810f49002d208a03244000010a0345500e00c40100947d102041c031801c10545a000501000010501c54050240b081c0015806140d503840e021080b14 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 495939559 1250 495938309 495938329
    0x2250329180732030a020607060507090e0c0a02010509030f04090f0209150705010b040b01080a0b030c0a080d030b04020a090e100503070905010518010f12020604090f020408070602150105120c0a14 86
    0x71303200f580082010400360716498115417501e40c2002c4003040a5072800c00035210a1802e47c0264003000c1c0500400c100384420301d001d40f29040840d0300a10080d2201d40e002c95a1303010b00c0d548080c03908410081007061503450fa2100c101c4402d030610250400340c01c80c001504480b80d01c1d50100020b400003030000d0800800b031140c081206021241004501c541c4e0000800d030300300060024044a541c0c50700321605940400243c110f20000516410078103444940b816291950083d128003c03034140210b00e42c81e46014000d07150540c1c2e01d6980d0510007850244202d1240c0ca010380075060702504039030f021456450a0001c100980912900460594501000d100030143e41581c561100b508800050101c2400400d444041310f00368107400c58181e00d0781c00001c02074480c2d035219102c80c0f03207020201480c04000d9009401140d032035005480903580d840700c0a03a1240d040083c54640c0c1e0000e0b0006002ca4640241c00002e0381d10400d007194540c50b41c000200313454250741c5c0c00c00d6031152007100500c035451818405070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 495940809 1250 495939559 495939659
    0x11415120411030f010504030e0a0b040e071b05010e06061c020904150e1006081c0f030504060603060c090311100c0f03022503291807 59
    0x2062525140032000e191126001c1c100038450742c6400702c02200341c1d50400806200d000040e008001ca401c2170f00d400750203803045040c8103008040350340d0000346d44121401620304585441000e80c07150785ea00c400c222030300d40b80c2e01201d5a020b803d40d1034034030209000b4070914018013034140c0204454280001041026030800f58902d40b55460b109035140183c8641c0c2103a80c026600c44d05c80f1046c01e411804000241508600d4642648288240b10411080030b030002c1d000c0718213020a5404984416005c01c0008604032001c001064000c3c400c0068075100341e02455000d4003503003001540f103840b40e68510a64440a81d4013001075542c000500038000e803500244040ca100b04c420b10980c1482c0c0c28064a004134204010b450058488040c1060500a00403011101451100c103010101001b10f0120445480d00007983c507001400300701140c00d007039a19145030f02006040ad41181c0c1d56898928030710301d00c07070030301c04c1c41940511040000c0407111500c4071030b1000c1c401e1401d8007961505000c104140d007d0050382d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 495942059 1250 495940809 495940849
    0x3040803100b1809060f04020d09020a050409081905040302040c03020a0e0604150e1804080d142e031e02042304021302040305060f0403020d0207061e03140114 70
    0x29000c440c103c849014800400d0a55000002c0c0e0b03143ea0000760b01c0451507080c80d400c00c0c0001135454801005610144d134181c03084070003041468440c414001150300d480c1c00100124010000d25031110745020310102c00c50740703610f804cac1c0c03900d5200da0205040c0c500c803098210219801180420088e50440342c0c0382d591000503164141058600f4400340d0b82c102c5000b82000500012050402d050b4450208040195940512104050509207401104c0e6803101c0103511421f490f1045071600300060f580250f0203080c983c1000302c11403500fa42d64000402004c039143c1145401d8400010000b45030546440e50307034090f41224004200a8010711055500022294009581c5520100014150001003540154040d1080003100c1688005032000b4861900007802610401c800c00150103e0400694802c074880d50944212480a5105903600d03003840c012107001c15940c0a60300d080f140c12010a000000307043c9030115400302426480c00d2120801e8215252201248050350042e04010b80514111005400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 495943309 1250 495942059 495942067
    0xd0209012601180b0415030b010b040b03060f03010b210d0503010f150908030c1f3303020a120203060f0f0a0f020c060f0f0106021f1d0303040803100b 66
    0x405420a2441401a182c03c40c512092501c00c01665038425402032102400412207003504070401d14000700140300c11142d45121030b0003c20040c41c401d06503000c84400c00030381e81c1191110310401c10940f0b048600950199618aa4000142d40700c0d49a2401c00445d1148000d80e40d000704815070824580400040c240403007080104010200201c1c2001225070311070341d6045024402e1404ca0355060140c1c80701f96a8400800c141c007003500e02242c51040c21041c040505010800e030100701e800c1c0c80001c0241038a610680c07880300b920304c00500d40d001e00c1c031080c0020f040c01c0715200da0015400c00ca458110700ca1450f5541c000008500307081080d990441d1102c550210907242c680c03d8041b64071001041d0b51103036603d40c03440843c800c02a8064814100b03c11041d074000d4504508032004034441121814074449400c000060802d00129000140310008040501040e141d5a18034014042c070341c0301111941a10030040c0b030001c00a0024500417032142d0741c0c855a034144441c3c0c100070242c45800003180b00c44c00300 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 495944559 1250 495943309 495943367
    0x6090c06090603110415020a080406051810050d0902061b030c01050a0902090112020102011b0e01090902090109090513080a1107050307050603011e0b04060e09150108040f060b03030d020901 83
    0x9803c5c1c5084510f41d8100320aa20b004a03001c81c00c0c400d1107a00201a50030205000c141c05030088080c0601840d112401c1054640b45000c000482c07039010b110360301180c01006010180d0040350046002e142c0080d0080d86000311842c078200420f1416030360040103401c0400e20100c1d5182c00e018103500494101020300102d1013507000101c040e403042c82000c010004140343d000859000b0340025010304181035011404120101c0090b04518440c0c140307074000b52280030045401c0401d80f080d64440d010694400c2066420155103100404025000100040c3c42d84401c40014280400908501c28150b0304c0d05082c1e11742c51410703450614960840da01c00c3d0040c9205010340c1e2110f4094034110ba400300c29451952110719038020403101d01e0b0704400354038a00040d02054254104440702c40c26030702542c1044c656500d49000c00c94a4030700ca14020f000071180c4000c0b90115500c0d10003803241c103000307810005203107840e0700000b840c50340000c810010480d00440c06422a40c1c100c80101c02c40712034200c11120b018010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 495945809 1250 495944559 495944591
    0x901090b030d121b0e1c050705150c0303070302040315050103030509060d0221090d110618160f090e0303060904060e0c0d1b0614040311040906090c06090603 69
    0x40c690820800000407110003812025130428141c0d00c24043d1815000e10343d00c00c0040860410048140c040c03902c503516030304038000c55054880225040006800b030a800c1004119111404000c0381032411401d0042641001091008600440103620010394552440c5000300d2505a815810310340c1714580001000130030341100403101900307002c17140980d51306203071144100240508030080000a58001058100842e440c003c2c1d03001e0074183c1d00319020300070b62030001c4030841d40700850220260807103408140b108003462203a80d800c0c10480e0035900182c43c40031208455003002d5002030340380440b0a004202d42d800511603090405682d0015516500d080300200b0402e00d0080d000501203070340c078a18400002030a122000400e40b00528000c0d07858500d08044440320701c1e2000300032a00c2601c0307030300003061400341158942012241c5125402d16180d900e81c2d00900e043c49400e203800c00d4403182d0136000100c1500c203038264140f0522603100301e5800c08900802d42e0b8542d4020303505052601c014440300b0658 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 495947059 1250 495945809 495945823
    0x1020706050d020f12090c091501140c15100f1401050702010c022b020306010e0105030a0605090c04020406050a14090109030615030b1312142502030304090603020901090b03 76
    0x84040240c0d680d46020904c8503548660700c4035040c075401a9080c000e45040c04190800145005c0f907140c0c58548803034040768101000c0b03100d401d020602c0f085031603c00201c108082c000d8255120161480b09900142c4010b01000481e0f001140381d01c680024441700f140d2130794601c06001c104041c08091020907001800c0d41c85010300207418412000c0e2280308640c0e44600900e00841c2e0031000b1242c0120b120300d10140ca1103040c2e001c030f100380600d00001c5001d10280b0326803030494000400510800840340c03905001005d000c1c0113100d01e0300072171089505548603400208020f04840d42d8907549d407a1800380013040700b000141c440c1f0440c4010058000243c0c0c0c00010301064981011001960152603c220000020240d0004000ca100ca800b004043e4000c4030720101e006010311b00f140c041c640224811119014508403a03a4102c0d0f040c40041e6010640c03951240c5400345000d4007800b80b2200d0780010b03103190001e070321803a20715848240a10440c203250309118014000448284040459440040e444840d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 495948309 1250 495947059 495947077
    0x702030418020306041e150e09060105060d020408060103080903010516050415050706150e09030307050f0c1501090515010507110d020a090608030702042301150207050402030c040608060102070605 86
    0x18000c00130480a40c0d80e98826890000950400b91014210300c8500300901848803201d4551000303141700080c40424000c0040c450904070300a000941e082004000140d0801c06008082650030320011a9130f0004000f110301841c050403280740c42d16a0340c001c050035108c0003040103041d1900910f0071078005402a094030103640c0341c880b881210720318900f0219030500401c0b0028252a0418900489410b000000f05096919281c42c0510607034503d00c0300c40c0e40b481309840c24000114100030103e00c000d14940075088540ca20002e8812214044940c0950128282c10441d61540d0798000d20910b10110040e200000c136080c01c105040c20015201e61000590503c0305078041c90001c1c6141c030456580907011005414100d404001c425144d10801d5a0303500181e00c220701440c94000202c07110185000c026031200c0300c0400e0703140180c1c00e28003d64603268006000b9025413140410100300c07950380340050b600c0b81e0b0510200e45e8440380740510003410058040c0c0300c1c60543d00180000d0140692007011110414 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 495949559 1250 495948309 495948311
    0x13020c07050f03030c01021303060e06010612110c0102070b1f0e010e1512010911090114100207080d0e0315090d1d0411070303050a0e0309040504050a06061d0702030418 74
    0x45580000b1904601c0744079071481300d1b5480001c0c28280121001c61090540e030080d403080207510540106590303144e1017805201c1c08108011a060704040003a001140b00b8403250103114100310011800c3e0b405d98200000850384601c90b841003090b481150302a402404040c420022a0707145411402402c40c8010b02a88004041010000340c0b10300704401c3c4640c0b40c04018083c0c1030b0b9a0300710b03c0454000d001c2d030f990845420302602a9070040d4030341606014180d44044101d000c0700440241003000601d5004e800e20198041c4200014a0840500a02c0686d10707503030310f428a60398010020582040c03042c0c0c1c48010141c0400c400d000820500081400e841800c81c2086d03400601c248100c0300c80c4c5c00500c412564010709001141f000c40c0c0682c0302030180a03209480500c10750300c4071176051064a0400380d80b9140c0b58400c4c01140359030301e0680c01c880e41181c000c205540300289141c8420043d90066045250752070b013400d01840000741c8402c541d1782d000d51188051070404e1b00b404c0c1c00c100d000185012101000b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 495950809 1250 495949559 495949579
    0x306060f0f07050d050a0f030b0f0d020307050319021f020307031d03060123100f030f0204180603120311031815070f030c090509130f0b0109050613020c0705 69
    0x406100c0d0112042c40760404102c40c54a94401c0c0020441e600c030000c3d520015008130700500059020740100740c18140300808414a80e50701c03106008401e2400c1c102030b40c2c140705290001406460a01c41102c0c054028464061603200d41d005000000e6101c00000314010800c1040702d200503030210942d04a15814078103036001000861240050154050155030b06010320303000010740c1922418803190f482142e20500000302010340402224580c070800c1c40003ca140382684400b45403080e0b0249802811000e401030a00da200c0603040c00088181c0b0900c0e0407103070380f91401c0c4180b211038141c600c0660051300d03081c44000300d95207410b4058000500b401c0001a4020502d00f24000c041c45400800030a1049904d51490031800051420181d00e01d10317404217141460840143c0e1040030180c0a03900301801c1c01d072243d00c9814a00b1018102d8030403c0c0e5880820004110008151407002402043c4010780130501d401d0250130801c16101c82c40c1c009234250300c1000f000b01c00000108201d81100c0040781c16600c8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 495952059 1250 495950809 495950827
    0x20f09040206130e0a18123e06060a0b0f1e070f0215070c1505040312020c0411210603011d0a14121608040f060c0213020306060f 57
    0x1d0144401d0310544106110700403811144d2440307258850100b500090201a00600c20f1096100c000080a40304960b000e9201280303030f00550307940408201c8074800030210040090004031121245400c14040401d400410341c0251041150780d400100481daa601020711f01030340f005040c401c3c5000700c080c03810701140b030320707901d00e0001100e08402d40354001e210340e5001c0c580b51214140540740070403441303840005440c440102000080c2c411aa501034010310080e400c000000000300450030810381009410400480015103107925151042140e40084c05808500300410042d5507800b180b0201c00c02d0103109c12001109005802d003001075108203c4c4440c2d4541a001c6800347c00304020342840c40615070b04502d8540d0b80043e40302c525038054400f05000c810880c80168079580741481080408005101501904041540e41c0ca941d42c421303218186410703600c40d401040000c03d0351110b00841c46100c164403d6003848081c212410341c4c031400444c44c5103403d000050003800740b4510b146020b0408240004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 495953309 1250 495952059 495952069
    0x50106230f04061e0518090a0b0607080c06010b0306010e130609050108070f0b0310031212050c180f01080106030c0c06090c18020a140903100f020a0e0d020f090402 72
    0x4440008800c10541c2c1d192144009880007544a400066940d00303135042d054524440c0d000d41e5400c1c41c00c0410031100d4140794007088141c01020309109101d60b40c2c0d640d40380495462000910f840392040c0c1d0700755102c00301211040e00f0704505034080e45410340200700700822680d1100e545418100e08882880c0030089000030a8001d0201d41c1040b144145000004207004d040002c92078115100c0c0320354910a00d44a485210643c04213031602c00107403990807414000030780600c038040080303e91443d04911111201d14518180d400176100c80790040d00000316009100021602d0789a07407502510401c401040f4040024601c00c8148200c2c4101555001514000c0d4801d0300b140720f01d650071201c10302a4940300e0401d5001c51513141304a19680540724070740044225a0b009980098510791100710300c02c64804403c480381c0d4130070b02c409603150080c40e07840020a6803510442080e07440c030340c40c016100c1e80c1e2444d01030300520030307000198412030005c0761240042c0c1e508402c00d104c07044140c5104106440d81c0c80465 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 495954559 1250 495953309 495953317
    0x807031109130b0d03200705090f130b0412030501150f050f0405061c05060a14040911120d0e041118010e06070503070c0b070b040209060123091305010623 68
    0x44e034841540c482d00804d15a0010003100c40041d0f016294a03140b1403007043e1a13a80f1494403989402c04c00d02d1001440134031810f040142e00c4041c0380c0c203001e00041103a5400301070301401c4404442241041c83e44442c1242d00d03100310782c0501b1408132100380701d001d5560094041e030300740d14030075042000000d010328007801c5240640340102401b4156903245c485010420f43c891071440200019589440d0000c1c185150600522040f6032101000d910301e45021001d20015040b080c1c01610640c151140b070740b0b800c0c3c8800d04050031030060302000d4000000c500000500c14080d290b0800c2c0b040741003c2000203440b1055040340e800681203184d05518142040041e640d452600300420703030204010800ea000d0250100041c400c1034032600c85900340c3d07615031a4055960144540c0a001010341c0400a401401e01c3d0114940080050405807240a4901c40c0078070110304414514009040102d04804141400304600400c204002c0d0f05200c1c542c14076070000c200c02001c445200184001c86020700c0d810f041c03c0111 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 495955809 1250 495954559 495954581
    0x1b01020f0d02071a0a05070f1a04080a0207060e100305060a0b12220f030c03141615020c0c100302120a0c0f020a0209060f041515080703110913 63
    0x181d03440794441600a92103900134458051050341c1d10020032070700210b440448440e0341a9441c2c1d44e007007403c61b4580f02c140170004501102d2240e074111280400a03c60403410f48a907114101580c0d441c9007900c0001d060030610ba01840c21320401e0810b03901035940e002105000b4030000d00e000103041c2d595800140c5802ca441d0f001e00840c8500040751b04148440110192254403c82c05180701e14a90038004101c1c01813113940642091842503222001a00c2044a041c0c0310b030003843c0613030251481c082004030a1303001c0f003100002140880b0700b51080064002c550750f200301c115041181480c1d55018070b90f859904c01046a441084c00c0003000115078003030b034140d9500001100004900e032801c0e01d0a03400500c465076071600455084420103040c984006001d140355540909101c4941d01d4a1081c00803071020f0410030380c1e0040d10381090a0405128200d00001060041c41c50410040d211f00041c2a10a0141c032078000c0505204480103566680f030110740420006480110481c0d11241071072000744207401e15 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 495957059 1250 495955809 495955813
    0x80d0c0909090c06020f0c031c110d0f2006040b0601140a0903031b0c050f06160f020118031e06020702100206010e0c040e0604200403030804060f0606021b01020f 71
    0x40038020303444080c01c251219a02112000354030103440c5030707a0709028207080d23916500030b0042c5006404840c62a08160850341884c009100c0d0784900300d030034081101c0d01000050030608400030341e41d80c4141401090f40b6800f0f00460305029404005890b07600080c0f0103000d00c01d40d08080380e0b070b0340d200300c002c0401207000003101900c804d17200d200100001c0b4144015000620902d80c20118920282522507245c0e6000403070181183c941028401c40d003450302c1c181c95200c103051041c10070032038001103803103402c0341301d9a000c560707002c15440050300070f12002c010212003d40101c0b00384000b4500342c2d65401c504180c041e603000d07111314074a0301101900c90404025000140c0c4100301c01590340004286042e2804030308070120650740d98070708a841d4000c0e4410122003003010b070045001c50801e0307407181a440c1c6019100440781d41250702d16005e0b551207640210300142000c800c220a020443c89440001c249042c000d00c80185000c4d0000d60740d802172804010400c19182c140e0400e68000c110481b5038084808c1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 495958309 1250 495957059 495957071
    0x3060b16050c0d210e03150403110f07080f01060e1b07080a020a02040c02062a04030b10030309060810050f030a05100e010e0f030a080c0f072a03080d0c0909 69
    0x2d481d12910364505072803040ca1211146078500c0300d0203100c81c8114070308050300606030787c48400310303070210300304007500503001c0c0101d85645026220090003c06184560034000300159440c14540525100c0000e60241159141c01001e020f8201da010900c0d4104088440720400c821500b060400c0c5880350300c5006014007000281b2151144e00450800d80c1c40f8000c550402894507400400c3c2d031148000c9410540c0d42c1c001000283c4c0760f00650f070010051040d0041d9076414641c8a0355504c0c0300c0007003a0784224100320000c804004055200c00038001405a514003c0e626081c4032940b803a54207002c1c02180d115143e80100000c40341c82c00c000d81003645401c1404c8494400c0b2103c41a0700419110302150200d50030817240704055071000600c842c0c4024401c00440c54101011400c0b00d0781c0303801a1110307404075400c102115940c600c0c00c003d844841d0003191040e2119900c5036000b281440000c8401034250800e81e0200042240c03901590f1705d40c07002100101d001c2c1c01025048807031500c5500302040031450f040f = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 495959559 1250 495958309 495958313
    0x102130303032c030901050f0c0d0c05060c0703140c01020d0501091e0e06010e10030c031a0106030b101407050105040606030c0506190507060b09090f0d03060b16050c0d 74
    0xa0040329030480c050907220069801d02e007044034080d80c0308940c3c10450b0300c00c1120451a5110b00001c040c1d40c0c48246410b4180540c412041d4140a00480c44030000b513680e0070290305000c0240603907030304190700350481443d017001590064128800f64402694107940443c03104e601403001e404498940021447c108440c1d81c4900004004241c820b08102a0381ea9164000c4110717400c070320440346900740e000c006000aa02e00310007400c03a0030000704069954441040000b0000d941500e145010714442d00b50302200c92481c2ca2080c1540c14141d000004040c05c040c2c940d103841d01d5400c140030010f0451300d0550400550400520050310603524010321640c80d020400c405d1266980c00241682d00c942c86842c2c81b15031784c0e130401c5030318000c424a07009a00f541400c1811a2340c0100001d000040c420807001c1000101d00000032000041121605455000080613092025061100700848441c41c20100905801c1a4a4907003d00900c1180d0826030000c1c3c505c0400e204042165a5908400400c0f401d80e04100b4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 495960809 1250 495959559 495959561
    0x9010507020c01020106050607060c03091e0b0a06051c05030c031204061a0a0e060a050a09050604150f050d171908100509160e130b010e03070302060304080c010213030303 75
    0xc451400041c0616000541d4030b6206004076401c480005141038181007458981c50000d065690040f414903542d22466070015007540c0c1080d942050100b210b8600041c98108100c604d1001800f00b400d044c9004401c1c0031550394180100c010f4a41c403918148103074901c0c0b800910b0343c400c01c0402c1b65544404107180328800f00b01c240991046205000500030440001d4072620109591011760394000c401600501c008941d00e07100e80d9110300c009111703002442c0d0780e0011603120391081c3c00c098001d64903042084110704080c090b005c01603070b62540c1c185c6003600d08850325480c010305000e494402c1403044501c0c418040e074448072003c0806145001c0c6d82d280100d0704011845403405210f0f0000c03543e40c8000910203802c1c0700d081000c90304064003400c07580c6d48001c170070924640302c1e04c4941c05001c0c0e40d4003188410b480c0c5045450a50403210720000345001c1950000d840156419400c034032a0b0301c00b040510040e1208019a0341203a442a8081c2e16151050500e5000e4055000442c9401e6041e000c000b051541c1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 495962059 1250 495960809 495960811
    0x7050d0e250e0103050312070201110f0d1b080c0708120c0712050c19050313141302090f010503060102190c03030e010e0f0f06041a0406080105011704031803050105090105 75
    0x8842405829075036500000328501d10709100152442e00240046204886030401050b4007280c688000215006400705844441d08507902c1b4103408030012519801e25a130b070f4407ca404114503510f807102401a0340d81c009040c528010500000c0e1000842c4130304c00c0200002c19a800110003480182c141d25002002404640040000b130720f8094022030b10f118603d0040c422a400e00b034250300a0a54001101030321b0343d241d4504c22084510348803c0180c0c40c1802411030712400680712240c002104052000200246400031078050710380c06c2d01c10045040103546031b400745d825140082c00d050380c9076919000140e080200180001201040c244d81c3c64041004c500621415644640c4501d50900f81640c01140e0070f8180085543d0401078810f4045298584038440071448040105606d14080e03c03130001204004035046107500c043c0c00401c041c840c0c19002900130340503040c04e10308010080c40180f400700034400702a1020701440365142c608100c81440e02c1e0300342d000d150400c000b4001400c00e092854000d02d0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 495963309 1250 495962059 495962113
    0xf040f0b180915070903082b05060a060f02061b0c12090103050703060e13060209060406020a210c0b101a09090f07021005090102070507081b040902060307050d0e 71
    0x303107128510f100c1080b0f1a964000e10603030b61550340c1d00342180e80e40c0400f031f88201d0764241d403c00704100c400c440c01c0411080650040740328101003104e0030180144580c0320320355007010003401199008004002d90000743c1c0d5034420841c01c0306102c070030070100c0e01112610030522010402c3c011703940c000d40c40400c000000c03c00300c4402c4c0d0f4104555510031404400b295403a000c1c0c2c0d4190131015001c03901941d4600781002207140100401481e00300110000b8205500c42c1e44440c002d45c000c101da00c42032056500c0b003041e490104000ba81e0340d85240e01da0041140c2e41240000702184800300c08150062031074039540000c1c003000d42032120301c820b420201d41415080400c01038851921440001c6100804203c428050074140d0014401c0c190b01100d200d018100050a80c00c00f0b641c01d00c40080826001c01c0218001c1072680080d0071111500001c004145040c064000d0203681841d1240c1c0043e1030700d500700c03a4041c2c003501c1d08585900120f103200d8041c00941c0c2008020384185000482d80590690300e00080d40 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 495964559 1250 495963309 495963313
    0x40b1813050c18040b100807020f010e070906170a0807060603021017060301060e0c0d090b0f01170309030a0305032e05040b030a112b0b06100e0f040f0b1809 69
    0x1c80c20401304003c1d9240c3c0401c198211b040d000102034014094400e064010480c1e0050b42c5c00b580400d1461406c681116500c04240d5001120030006454544111400b400381c0d1400140c100c5c0740c2ea11015980c10007500700030b244005c0044c4401c14000d042d070041000c0c4d07900030700b0740c03002001002006000151034446100c081c0c00e04000f10fa40d52030140718480480f2051607040006a8407a07804460f1030b0003506544501030703191142c10002966030f0807203a22038016000e900105506047e60b44070900189091080744d6841044038002d5551f000510a03582541071500da5a203698600b6003072080c0150008001380150f40080000240c41c034031176542d0a403070050b01c0802c4412600401c066030b510545001400c0c90009036203c0301f050600c16010160407e4020590705440300145c041010414031900581740c5110380c100b481081d1420451003698540980352006200c107400002032011b00340c0e01d03d07091141e41d8a214400c03179081280c004140c8000b0040c803420414029000280ea41303481122a64414 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 495965809 1250 495964559 495964597
    0xc08030310120201020c010e04060b030903031008070e010b0a2015090a020a03020f0d0b040c03060b010f02100515040c080406060b040e070c15020c0a020f06040b1813050c 75
    0x1070300780c02c40032a0b40d0140d009160400703184005440c48850002540e401c1030f01e030034000c41c0c0849201d0085019051150003940c0da03140c507490010600300c03107400c6000b0513000312404004c4020140d00b21815140fa400d10655103590030398040d82c04105070301c107401d503503202004000d941040c089904440d800655854004542d200c1d08000d4880385e000b80b000354461140b8034180098145010258503040000c0c1c01240400389503207030300c21280030032101250110a040303401d004000907802261560142030030106903c44080c2c5010352202c00c4800c0103810300e6503900028030b8007140320360102e00444c4054410001104507000007005800112020340d402400c0c50b10006180f9907541c100c07011560014180314030760321015403c90341510068002d80d44a88a4107000c03aa05481c1e00c02018040c40c81c100030701002c28a4414070810101401c8840c0c8900c005000c100040c440600403640d4038a030300040a80710340d010340c00043e5203103240780881c01901d18040801c84400a25402080160045034600000e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 495967059 1250 495965809 495965819
    0x1090e090d030c020f10020903010b030712150203070f0e010c0c0f141c0201080405030706060b0d0507020d050a032a050417010905211e0a0f0216031e0c08030310 71
    0x1650f013030b21080c171000d50304c00b00c480d07160168190701400071018000c001042d00c01c1d00400192900704940c2004074083c10b403800050400c880313203202c0004003c02c203006500f10704d0281c0300a40b04151020307520003440b06962211f8810b0f0b110f01c0071043c10641c07203c0c154074440c1d141c0781510699682406409428001d0a0030f2102c94500143c0d015006013108044607205200c544c0112210840a0302c22a003500c4180000b10004549001c1c140140c015180d901d6100d550b06940142036a00161040301990841454048250b0f8002c0c125104e01c00241004542c254003188040311041640561140d2000c200900030300055120700180100c0329030035445105105410502030880e011130301c00502c940d102c1a0780e01c00c00c00040d140d40036640300503400785084c803c43d501d41340c51050070869094605440043d4011002e904036165904010f01480207040c01c00f95590340c004a0303c0c40b0b0101a0802c50110050048084000f04a81d861039118040152035941e64890301d0740d9420940350701c0c1d07003010000c2001c14 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 495968309 1250 495967059 495967063
    0x1306020601030f06021c0609270c0927080d050105010216060e010c050d02010c020610080703060e01021314010e0d030f08061f0503040614060307031101090e090d030c02 74
    0x7050b03d4004580b4455000c07265510030003580700030396084120800c0d1199070091549403007240010101000b000c5800b03029554003001c5445030f0508085071a04d455401004100c8405040050310103807503000604001040032142042d620f1480c01d0900c02c0800c01110030480b88201074101c40304100b009001c241d81700e800598840003c4079134010351004000c01080828456031007455440c034107040c042711000107602c8080c2031400d12013030340700983e4450210b4040b0950400150758800164002165001e00713000d50030351a1280e41c40080e240e6502c0e21105240e1070350a504840015400c82c0d5009051b0340e8540c0102c1c44114000200e50118590441e140e07024105004600c2c0031a0341070b40d491110300b0a690064551210151500381c000e1920301c2c4244402161141e070000801c07840e00c86c42e41328034061510740c043c0e680c8003690600e5104014180201d40d10000362450540c4e90121888011503520b100488034060680c0c810740c0c6a04145091008030100418070b01c9501c0c049550a204100903020160307 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 495969559 1250 495968309 495968311
    0xe03070611061f0e0109051608090307020603100b03040b0702010c030b0a150915110c0604121e080a03020d0b010806031f0f0515011e020a11030a140313060206 70
    0x1806642104001030f9420051400e010b18101c043c210b041c200301d40301d40c03c01c00440000d0308004802e40da5030060111004400c41140d0000c1c5461910000c58501011400e4403070040c01e5009000b98004008514a5a4140081005003000000c00ca88902d0941890520590300780c900300003551a00f640c000041707104e40210264601c01400100e0303074511b402c0305081120341c0c200c9181c0030081c220001040c0000120741c18110b900d40d550780c0a50710310642c10494102403610303e103244a08001c03c4100705084a1198051000b50401c07400007500c1050181200a6503500354001c1c001040024501202074255001c6d05292000030b108102c1c468030400103507014003042d2442d40d0f040c1d20582545ca003c2d0b040400c80f8807803010081001c1901c2500541f80e406480003503594600c1c0010b0035002d4600c40d640300c0d01070b1380c584203000d064100f0350380d04581c06911095074010151991a86072a941082e440400490b142c03154084c0381034241c1c0030742c007411f21740381d4000c0d00c6aa030030310018210000d5128400038200d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 495970809 1250 495969559 495969587
    0x8060c0f0d021c1b05030112030809100207050703060f051306050c07020d0c15050304030512041a040b07030b04020c030405060c011b02030919080309240a0e030706 72
    0x1052a040c0e41000044068006007050400c2079000c00002546085060718604543c403a030b0808106000c424500c012644140141c0a0411a0510040200130031001704003c04980508114a4584610040d00e00340821000d01c482d005000045140c1045030000b0340c102201d0240008205103007a51000c801619420383d00c0c1a481042d911540340030a00c61342c8a01e400c034160342c40051400c2c0c4641d01260f100764020600740e41c0444101c00801405029070480c0c188210030b072400501c1e600e80382d42c0c0030f4040c0c002d0391884417140c2c03a0702e00001c08000c04801e0040060946588034500ba00e001c3c80c0c020001c0d1000c403001800242000c40441d0f56050600980d4082d6502c41c025501300360601043c006030b60410f8015440a640300c0711054010f802c02000c444081c07185501440c0d580c480740c000d000b13028035805c00d8032100c410002d0b002c204918001c001d4802200e001c035410305244100d410180b8092039540c503402c000000c00100465242d401a00005500d1400d4050b41d01866903484107442c10344190b010 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 495972059 1250 495970809 495970831
    0x10509010c0b1f0306140c030601020d0f0905040e0f0c1009181409030301030605070824040e06010602070302040f0203010e18031c090204180206041a1905070b010806 73
    0x2800081c000065440c0e2040122486500d05039901040c2c3c900c00240b603005842240e0766507505510301640a80c2650300241c6074003120300d1800d00c01c0c0001e43d60311224105408009550f070000480e58420208800100b03c01001840200301c40d8802544404108088032514421002112000c0c100203810804081c180d0700c0e1402c4807880c02104a40700c20301030315101ea03050317a5074203540c0002000d19402806030402800854503503041d8a000822210040e2400003400000300070040141d5400c04103103c1b40c4030300f0000240000740d00c40840e026000300d000b6112107008000022400c40e070f0000e80c1e030b0100c074000c5800740080d000405400040b8070003800303640c803d401104001400580c0c400404401101e070b49080f42d10b0f100f94098104520341000c40149a07440e15507070b8680a40c5028007500441c0d0b6115140254221000da002400038881c61040180c10100310701e4031080c030b0907503200380c803460420400310410b18070140c1c400400710b07840300000f225072140d80000443c6041000900303501c20540d00d14 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 495973309 1250 495972059 495972077
    0xc0c041d0606031f0c0207030c090506030d1b030e0d060608062a040509040302070b0406050405012a03080702071205060702150c040909080c0d090f05040b010206240a03030f090501050901 82
    0xb02c4e08000c3c1c070701080184158850100000009840e40c81407000134000352100083c00d080040415051070b110b650380c44200209210042c991401011001c201d0551500707241040f0680d07400400c0b2455140c14015044510304200000d030104040340151040c1c0300010746020f5080d10046680c0d880303207042c0c0006019a0207100c1440542041150246c005010303004455140d6034442c80308899070710a8000a00082002c50100001e58101c19030b070350210041071031040300740c1025000c600b1241d400c0001904002100000c103228a0003404248003420b00f00040d103195100c00d00303090b6590301003651800014440c001046030321148030f4901c940a800700e56141850b191901c403100000c3c01c2c51038410307034201c241000320068604081180d500f628444d51914020b0b6481d01000d0060304049600c0940240e05014049a880c7e9021501c40d912003407541e48041f28604e00c01401c420707c40007500d407135007003612007101005254024280f49141100c603030302c65018940f205d0045500d0300907c141c3e00e002c265048 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 495974559 1250 495973309 495973363
    0xf0a110714030405090a060608010902090f01030b0f032b09030b0c030703021306030b011151090d0f0c03051c050106050d0b0907140c0c041d060603 65
    0x206280c48103400c51402ca909160300d442c00651307405d00949021078960341e01d103010001142c05c01642801810043c10450501803203e0203d0901800790340c24504042d600c03840716110703540300844074804060185c01c80c1c0542064410600b0003034401c1c40325134144018030703000e01b8005100d00c0040b07003966817240d5280300a40390601500156000540202d05064003400307480001805800c03034100070a407c0c1d50200e50001d401001620811010701585896084468070900400580d202081d2a5000d207110740d410713100e5580040a40d1201c02e504001d2140221802a0318401c009659401000d07502c0581c3c10b005c08d1044169202c01015100c0d101041301c8a0700d1402080c020700152000110900c0d127404007400003808075044550907080302005c9040424520070021803485416443c0d4000e86070380c0070301d00708102c001d08000070300c0300d007c0014034001401d90740c0ca110910039140b07a03260181c414089074084160760340f0700c0480c50404035141d10850300000c01034900028184541000c5401c10030b070102141c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 495975809 1250 495974559 495974573
    0x90909080f1b0a03080708060a150f030605030f01050f090c0108070c020d060c110f06060927030d020714011a01030515130207050114100e0601090b0705060f0a1107 72
    0x44640d140310100c28201d00ca42d24400344120311105219035915a01480d1000c0060300300e48010b003102d400745441e02ca0600031560000b043c00c6152403a42040a00c0c4800c00200328050561a00807a806006802003401d1000b0150001c9020340172000c10401b542daa00c1c00c605a8456604d4402c1e400144680d01040085005030004c040c5180041c1c000c100c4008903845981c1604e21000705a0001500404840c400d004180310314240104038072702509840c2072120000c0c41000d07000d03040041e0b45c6010581800395002841d10403c41010203802d803921508080440f030001e401c40034041d03d40840030b02e00d5481041301071013807012400c20304901d8810003903840c0044004181c0140000740c1e95941c0a40a8101e40d10303407602282c0321a10441c00750350740c0507070300e0040c0c20f44900780e56203c101c140d20f03c207001100f540102c3c044240c51445641041c140e9030040122020301003544901504000000c05000380f003408100c051099080c40242400790300c5034417054003151036101a130b8000e02400e01000b8002815 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 495977059 1250 495975809 495975817
    0x30f030c030604020f0304200303040317130e010b03010f05040b09070e030c0d0503030412030501120609080d0c170c0324030705041b020610050a1e1a0901090909080f 73
    0x2c041c20040c14028410f21400d0355500a4a0650b6800700340c40320a0324944005880d0400c41d00c064010b942058519a902038510080402e4480091030104462842016150030103000300022070f142441542e5800000149a20a0080040c051445003001c101c074209070141e401c0c1220080c040d06c0e01941c2c1c1500c02c9503070500f140b010075414010300d207100c4010742e82e5000307010240d406a40690b130789040c00c2c6400480703041c0c807c2c0707100c0515040000422081001c8808028102c0e000301010640c02d5541c90200054803c800c020801c592400011201d81a0302561500c010340912041c0c2d07500e91194648843c89000480f440701188036203c010800440814590958090000d01114441611000040c0560b0480c2c030110b56900c6052483e03104141c0c1c1017241b0768204800302c0052904500b8800403812503012030041000c021f0200c806841310b020b40c4c2990000804640900b000c2002c410240345030103901433039695000500075400440c00045500c58040c4959000d80f807039140c880f510a10b100c0c6500 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 495978309 1250 495977059 495977071
    0x3090203011b2f0c010809071e09051b090d0203210c060112030206060904050a0c15121b0e010216090f0c0f0e0108060d0c0f0801050702030f030c03 65
    0x52980c1811039181c04074561912079a10503140c0c50120312030b42c800001c5141c1c025240140031603d03070380903001d000c8000c00d0204581c6801c0c40c244081d503880250303852409856a001340e50300b81c0c40d0703800600a206048500c1c810b0781e80002042c4041c0e22400720a003140b44080044551030001080254590320303014404860316031028094901d921031940c1c041001628050350009020740009429003526020300045014014101c9401c01000b2503440007555164010075080c01603104001041c14010100a030101003a8884000d40501ea1624440c1c20560151009240840e0b1031801581101251b40078011a071400b030400c064004882106c22a443c0c0307000311109041d8010f118100240006c103041e408058244585d0101c2c0050b42404072008480150030328031b0401441d40640c400c904d90000f01500400000d28190038503465600c0015001c0712241760081540c00341c0480001c2001c40074050004803083e0400801041e078607504280e80300c0c4030f11481d84030124000c03c005600107a0b00c2c006560806 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 495979559 1250 495978309 495978311
    0xa080d14072f030408100e0a050d12020f160c121511091507030f140d09030201021c050f0c07020604031209030f06050906012102060912031603020d0215070309020301 73
    0x1002e0049114259031060300800d8054101400c210185030341030140e45400c0a48038000c05041d1200c3c1c80c0e90f5258050721200c9010403000424441c80c2481580643c0c1e4460944a111a66002018201d4009401031101210a0702050000007200408255140b1586403c03403d04003091042d070704001e0044c030307064400d24442d035401e00c010a19922520180701c1d002140d1100c00e603907004039040240011040283c0301c0100321050000034001000d9070141d0790628054003003c10313091858903041e4003a000706c110001030300203400404a42c11071145c0100c1c0c02101104c1580c2c0060301e54810f007070010300c5003500194114408110410004507141230303c440b540c00515018904948075511407030002e10f816001c2d80c01ca9100d006000b85860180650f6005141d03600d1504180c2070400d82d00c09044480c204060b116000101d91000b8540b120509a1001110881500c0d07a9000c0714603101c0315459208000e074014400c2c0f00a11080c01e00004010a005024900c0d000c844d9031401c2040740a031000e07040490300343d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 495980809 1250 495979559 495979637
    0x809070b09090c130303090305151003031b1e200105032d0f04030806040b03100c05133203070312050c01060b03010501020f0106051e0d050a080d1407 66
    0x81c040304c004203010303512942c0d8942500d0319509003d482d100f5402d40301340c0720101344010710094540b40d0440b001125854188007003040030601c01e450003140300c010050604440101112560a1500d202091040c4113040c1c054600f010b03102480b8480f070000141d540483d0080002c40d02c0408103030b0051a120510020350140c08026034001d030340e190340c20341c1d0040c0900c4031a410712013015000403206034000c0307003603808100145540f400280d031200e4039040c05001660712034a484605100703000711100100c0440d0715035000c580c0c910000307002ca2550220405407090504d560101e110501e141c100501000900410140c0d0a6441c2c20f002802c0d80c050319810300c14200300a030926607080c05101c0c02001c460920320784942c03402002906041010300d440560743d14000c4e041c48a59190f91001080801c0301e200002410010404220704201160003e005403141420241c1084102c0c00140500d005005050000001d41c0811098041041d56014049292440081c4418900c015010f1119a00010a00d08 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 495982059 1250 495980809 495980827
    0x90a031404150509040b0f030a0b09010605090114030c030a082502090a05010303080c040308040e091207060501030203011a0f0f011b0f05210307030218060c0105070809070b09090c 79
    0x10071458503058011843c0131400800364030f024031901308043d1003550940d8210b005100041d484800843c00144102142d00205803080400d50269014080c09050001c0c0f0303503101c2e8516628540510381251081c850340981016500b0081348100c031460380b20901900b45000d0280400d080078041d122031400301c24030b030a1305025030780e540d42c1c550058a000c023000079994118200203240700030007425184241000c00c01000014130310002c54040340c0449000c81c0c031907180c41351307071074205081c120031110f0030440462800240b25540c1d00841c1264800c40003001580b44406003104503210900500741c0c00f01c04810105214104080d900030702c14030501d841e0940c014030402c00c046042c400d403429181c807001003010304200701041012243c6c0ca0004a80c0c101c01540540d2804001c4c80000d2400d001c140d004107105180007608460000c0035280149030540351440740610310b0003030070100c61344000100e1031804507420304d0011074034105440c604c010303144ca00200e00741480703204c0d04054016500d03203200300000b0075 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 495983309 1250 495982059 495982079
    0x3080703170705031902040803180a0302091008011a060a030c030f1e0e010b21030c01111c090503030109020f0d0203131712071b1506051305090a031404 67
    0x2114004a0b11000d0301c03402c0040c0d002c80300c080c1c1540170000f1103104100a0000b1100001540e1282c00c000010068501d030b560040f40d10f8031a00c2d44000d4000b03040740e003884450303013100400c80140d07401d21000b0424a041550341c010b42c440c104241d203810400420888030154030a401c500040020750801140a4110050480c200c90880c0016038000b405503004030241e60b1580559074200c880385000303000060000b400a05820f0703400ea101e6040404000b55211540000c3c005d50f07511b966010020001400303400c079400d0b4958804000341000c66140544110390030101c3c4942001075402c03000443c150b03800c08060100941c80340501c1c204814083c41120042912070005601c01c20104401507540c00040c50000400100c1c002d400700646004e0059071610100040c1c2d117070b400354003854284446544404c450152103030004c4081c1045014600303104400d03419070004d80403500295200d042d0765041e0268402251405c0d50b00c00e480360000f8400c040464810b0b00203040c1442c160300b1031480c040d61041e081d4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 495984559 1250 495983309 495983311
    0x30a0b0d0c0504290409020d0f030203070605130b180a020607150606050711100c053c1905030408030d05040b010504060305060402040914010c0207050324010308070317 74
    0x21140e1404401c14007090030300340102510041c40007010100b045080c19158582250340001c0e502807a074402c8070754190741c1e543e50003010850b041808010601c1041c1802500d0742d000700c9050390340b9414203000c0341015003171582d40c0c500c090300802c054256840b03a91400e5400c41d000c40012000b0f100390128400983d8503a0018040e1500c03d500440c4414012181034050711010391102d0207200007401620003155503c603120744c900c42d0440c2d1030309010070103090540c2c42c1045042e010381075226428004402d040d04041c4005d4122900c00003010014807402c4822008002a20b010807940000d11054110200000410031051041e025241416283c01d00a441c43d0000500740c442c1d070380c40e0340911083c0f00307140208034090042900d081c0501c50450f101c15640e002c01410003805695164205407c1c008203295121000107840000e01603400080e0000b540c41c415801550b00c0382c00b0300c4140c5c909080a040c02030b689010501b070680c10f81c1e0700c0c42d20750b06c3d41c50f000b1120179024010818208004d840c100c02c001 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 495985809 1250 495984559 495984563
    0xd200a0503030c160f05030312060112020c010c090506161b270f0c05090105090a031506140a0501092c0c07290105040f020d09080307170615030a0b0d 66
    0x40008001030b000600b0030304c075140e101000701500c0c0007003800942c6010040b24400c5a0f481003c02494840c880100d40201d18640c0f103c01c0f540c0301207030b58040d910042d000000307400f039640e9072858655180c1c1d0800240b44200640684000e040070004030010340c1402018135189055128804000e41da07014810058000c80c40396a0301c0c031190203180b0051460703842228075011084008000f511000130300981319201340c5d1486070600c00e0203c0c4616017a600c0036440c074041c660201000c1e890048160800c005002c4034028101003a0344201c0c10a00c6003000f944141c111032050f07480d51460391802031552444010010010000742c012040c07215204c582c01c2d04030340551049001181e4480a908040400f089030039242e458100151300c200b00d46412941d819815242c045500007140303800f01c0c070400c000b0702c00c0001d000ca5040c1031403000c40c103200c801030107944103d01e10344602e841c5109980b203900e80a0001c56103d980603c4d81c81100c4040b2000d04081e50388618140c90001e410008000001d088403494074003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 495987059 1250 495985809 495985813
    0x4141201090605070f020a080a0e03101103060307090902060304081605030a021605030a15050c070c0f0501110607170c12100f08160909080f0d05090c0d200a0503030c 73
    0x83c0725245500400d494040f00301351000d048500d050703642e040290311610408a0400114515100e0305503028033100041c0885284104070004c855042950284c000b00d41540c030038012850006042e0003a401150041c2303900408440c0b039aa1955664022070300611001421022181d6818000070707070801c000c3c02588060b400400c840c06080060700c5150000380c20032800703a0084030403140000c4103808000012402144040303815036405201c0402c038050707a10003900c14001090009900000c948842c0242c5030700b80d070781c2510031044207403055844030151464000144910b048241e1020a1300c88907400c030599a00350ba1400b00301c200440380d8680b0903038900704212800f070010400400017036051002840d0100240810b40d0a02e182d0b51000b5500c0c0c4203c9a00f541c40b045564200002041101c0c141800c06010036152240404840010082181d0300045446a030410310082e1405800005600b0b6021445900c0030300030310042c000420b07600b40080e82081c040000450a03540c1400030706041d04080b00 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 495988309 1250 495987059 495987061
    0xa14040c0806011406030406050c09150c06010609080601060f05120a05071e141c0509060417040b0304080913111315081b040b03040807050d031104141201090605 71
    0x40d03041100607400350061006600c5110a540c4680c8103a80d1f00039040354000583d41d44054101c010351141d2585164004102107164904d036240380003074440c5170320003011190140c0c0c031440e090722281250702540855500110040002a1090008041c140440d2600c00c1c100045402420303c804d1040d07808a114a4075501001403056110003010607181500ea06000002400300300a0407280e6410354200510340001100c8001d015424110001e2200f0260100f002d483c003d440c49454040980781210450040c2d6608950302e2009000d48050f035050303891252840d1250350ba10a078a07401940460f4100c4a181807006044409208800c0305c040c40100050361190001d03030310404039490b03401483c1c1050340401c9001d02c0c19400003880d903121740103000b41d90507244085a804c509000e01d600444486100204200c10000700c1c10180807214402c004684100c01c03900016000e03102c105040c440448800e00040091841041c00c102800001508042022480840e85400c0d50341e00ba030156403c0751184 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 495989559 1250 495988309 495988319
    0x40f03110109031e060219020106050a1707050906010e03011a0112060f0e0606041e0e09030306100302090a030503030f04020f0618040903110a0606080105160e090a14040c 75
    0x25003820049091900d10394035411561911140045040e20b0312840c0d0b82d8400c440c0801415604a4040f41d0300591016050a0720540007400f8040900545008210f0008005502c0c07680b0242407408031580b00190200c1e13800d00c0144072101200500b41b50400000c0d01d602c0e8001d444c28401c2c81210720740e08108031240403041d000508103488030a00040a02d2805104000083c0d075030321004265404800001c250b0344510300055402e01454214002088000b01082100d6141c0700f9070104849503090410340b0791b40d440b0602d98403800308a8005400280c148600c07280d40384254001c00320908010b10300114141c480e282e032469600100e9400c000c0d928a0b10911003546071041c0b107004088802c8441d203103002d04018081161440440c0c0090080381c544400408060140c545080c04903070920407110440b16a040400180c00688030b00c0205519013004608252005c0d190b40c0480000e039161030080038008401c1c003c11001c01400c0801c4160740d200141907564031000080d0050f030244a06003441800c01c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 495990809 1250 495989559 495989573
    0x141503070c1e1a340509060a030c0206160c0b0910020d0f0b03190605060409020915040e06010b0f0309030f0304080c1005010e061009030204020f181008220602040f03 73
    0x3a0900d01e111386080b481c0700d1000200041306110702c041e40342d03040540030b10711016034a07800b0f421259544144049445645903138503074003485040110340e08071040b6880764107108001e020f402c00d284000070346681500380462201c1855a42100208044440ca214004804000c981007030003804920790321401010390100082c0151a0504011005440c030b10240786800304101382e81c0c1d18001c100e01c4e00c84001580300d55907a440b0303e0000f034024001d80c0b924600145481c0a55041501c3c044c4a1071a01141414074000061164140e912041000b40341c812002403600c2c01d03410040c403500031444204803071250702c0c1074113000d54001ca100d110711540781c01c0504061030512401b945100600c1d4a0000100110001d0b0402d09401c00c2c03041e542880050f60042c02100c1807511740d00003940003400003c2c10711000d07000760004d00e01c1000d00c1c0b02c0b061040b01c040c801c1184071b14148000600141c3c0c00300101728002c5000d800e14041070003241d0010024101555a9420703038221703138402e00c442500b10307034104144091 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 495992059 1250 495990809 495990811
    0x191109042a0f020f160513020c0604080a3002070f14070e0a0507020303010501200604150f09020607030e0d0b0703020418020702100e030709020310141503070c1e1a 72
    0x3c20703405441c0180c8022403040c5c44016074400c1a204964000e2441400c51550b4121403030881424165112032409003084e2701c40b0741c03102c01c0900004220951540b00800f2001c66107482d8180c100c03021103030340c000800b40800303074000354005e892601880940c0c0001828805021004901c03040281c02e421340761810a020000000340300d40155800e1000704181d09501008032815500d090a00c0d00c00018010070101d0301da840301d14020040c1c4294003d01060081c86014145900700c1448240710710441010100256140010000d403c80310034004200002d01605507035114103406440900c01d403886854800f09407000365480d01c04260b00060500000100300f0507680486008541545031011940c08950502c2c4001412002c100d108144513000395018001180100310003a801c4d0340340d091050610041000c2446881030a11078002184a50b007850784d1024641c2280041c05c0b0b0956980c81c60030380351290b201e07804580c42c9610040c0c40c0310007044040c01184c80d6000d143c10036001c01d2203c09036508480 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 495993309 1250 495992059 495992083
    0x608070311041b0c080d090b240d030c02040f0e15040b06010c0b040f11030a0501060f06020106060836101d100b060d090b191109042a0f02 61
    0x103c0d82d5100d050080c1c01c03e50700185030358004a6180e5480040c3c11100043c0040d1000518060040c8203101443c11403420f03014541e04444481200c031600c54040008404103200c1c0140401e02d44541c0201514080d0302030341181d0002e20010400c20340440606052510b4101007200d00000e4205001c10b0080503220781c0d901440c00e0030714862586a913100e8001c08480100018100d040164000040000c95418880810030141c12503000d14030301d26040b8040c040c140121408581d01a000161007481401100101d0385191288001e075201c0c5001460307240d0043c600d58005071019001404003601641403410a4a2940043c1c8003a640101051040c2c84082c0440c10728005914441e60a02c03030041150540102d810794000b80d5810510003161031070082040c10340c0040d10382a8124203000071004031500c00c5000c0c060340a501884003d650b42150070b0720000d21280c10050001e088282440e9100b54083c0300440d081e114100080d070254030506444240c0c04001507404c00c41c10940c0c54040008200c8030b4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 495994559 1250 495993309 495993341
    0xb0a05040308060f030c12030927131106030403080a05070e01022808070503070309060507080f030c120c0c01060501110d0315090203070503060a0b0a020c06090103060807031104 78
    0x824262001094028080c0046100d41d91504005135103613410480121244000340c89030620010080f801a03d0360444600b03140544040e03131811150004a030480985050700c80554a1561a0f50700c03003010110360048110b400100020340030000fa6601005584034610070b030b41e580c103e840c202a60300280c49004d0304071000e10602441c04401c0d83e801044a017414549a9410f2410300300120401c11014001c8201078492903000401300c0c140a008030040c00c01502030f40720051400d0b510142201c0e180700f00000907000344000d010400c544c071002d90007990402d461503c4541820070703071500d050f10b68109407002031025600045c050440c500038011440241000d007825030994040c218400d49405206207d8010180d40751003d0b100c040038020300001520300c80f04119120f00c1c00f9040584950b2003501c205204402c0800009800b03511042191140c0c60154068001400031906110301500321703c02c110f040c15190303500895019000c1220500550140c4201100d040007242440304071001003800030840 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 495995809 1250 495994559 495994561
    0x1150503091e0c0901081e0703030e040207030e031c1103071707020d0f05061b0c100c02030412050c090a091707021f08090f0d210f090b040b0a05 64
    0x560100c0c4280e07094030080e081c80d807650400308040b814540e02c03000d1207501011071320010400c24400074100100741c400b0001400245104401241e44800920005000504907800c2d001281469005400f2180c46410100e200c0f2455000207400d0281142c240311610414140700740d0000e501052254040c035055000e18540b02d0ba544403645020314501035202074900004444045484403500b450340c2541052501300e4614051038030a845200958803090044245c0b410041202082d100700c1d00d0140c0380100500c511124902160080d00d0a0000030042d03010038400040e804000c2d28040e002d051203080501841140391007004401440a808900c1440c41c01c0310303000006902c8094004481018000c03107440d41024400614a42010310a8140028080c0c4810070996004201706004076001e00c190740040d51210314180d500c00c2c2c10425040007608d9503502210091a501c444060260071a0300810304400c1d00300d460b4203a4007440011118160b0920400007400a84a041600040304100600c07403 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 495997059 1250 495995809 495995821
    0x4170301150513080115170606010e010e0f090c041802030705070308100308130e240418051606020d09061d0409020d050f0d0201180305030403050d1401150503 70
    0x2001d1408580703a00b40311000558108440700144502e0041000800a01136441d8420209651415070322a80c80740d00381c80841d00d403040502080b428414081030f580c15001e0ba1007400111051800028040e8001c2c20080280c280307030301c84a00c814440d0304040180703070703485107000c40940490403041d1644204030710500510078240e510a045945580c0c2525100382562504004805110701c40c5d03000400824001a50010b81222f0714a00390072a0148651450030740e039104d401d03260000308030f4000001c051400502032107601e0240d1060300a00d0340c03801c49910340c24841e5034091078a42020319070f6076183e80814003000b90300d42c104500f000305070480c905840014604213010740191005002c0e0440303040c03040402c03015900d4a601c840c4607590020320800000e05107041064841030305134100f40c9280942a030301c1c001c8034014040c0504280901c1017240c240342003501e040f20b071500060f10440801c002000000a40d9015010b40799018505100c68142c0b54502401c0b4070404030010094170900c0303030610070001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 495998309 1250 495997059 495997079
    0x7080c03030d0e0319031e05070905120f0f0a050106050105040b191101330b030c0315060307020c0f040504200f040c0909140921090901080604170301 66
    0x303800161403004202028915043e9043d40a0600398002044040c19031144d015415000080c595100010503449204030200460542c2c5007110600041010042e0800182c2402020000390a142c1c0054a14a445066040b42403c1c1544050121588604010028050284616002070009091251520785003000c0e00002d4001e6603003031800b04e120404404c21150040c0c04d00c08034141002c008228004c1d0b06040b60292001e801c840c20b0b000c1c0c01c00c00c1902400350340100480103540c8190700300381c11551113200b41c03499540002c2c8086980042074280004684520028601841c19030f00644003001160042c0b103000250201c07050303c0f46040c50107110105d49070750210008803d01e80c0d0f0070020341101101159032100209006904145011003d004480d44060f0800c195584e000e0300b07001c00d80031600b1801c000607040d04c5001054015000d415139100c07071205410160b8a0403100141841620342c0003481000090b4800c41164000c5000c02c8100102c08030540c28032088402007608550400708464 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 495999559 1250 495998309 495998317
    0x120d050a0605040b03060a0207020102011e0c030b01080907032006031006020f0a11010f020a140106240504180603150902100804330e031c0c020c060f0d0903050c07080c0303 76
    0x544548d50028000e0b05591013900428414540c0c0c1000790041003401c2844070050104c201c1c203c00082c940645120726620900040d40128001d600500c1c1150643d199a80800301444045c030400100403281c00054a03100051485202003601c0141510f2500c0f10207800d0200a04c4071301e203550071110b003000c0002c2c100c1c060202d86000a00e8403992a2203140c40070391901c41e20f200090010000d90400980d41c0005402c00c0090700c10490040d20002c80c042000d0b0780720b00300c15889001181003880302b03000641100c00841c08242c50841d000c1400e580d292903040c0c600c0c6090001015058a900b0701c0802e6080000003180c0300480340c60000c0e0145400e0305d8076542003e0038a14101e2415040c13401c4004018800e0ba400c511204681e010080015075900ca1031307490f406200c030f51110028900043c03044084038440c600322051290050003011700c4000c20410740381d121500550303042100307211b60074140c401d40c03288184051117038440315510b501c00050301d49071400a5006000030341c010440d0400e41e48000c0113072 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 496000809 1250 495999559 495999571
    0x170a020706020d05100f06020f030a080603120c0303100501081b0c0a140a17210c0f0a080f0606041214010e060c0d060f05030303130302120d050a0605040b0306 70
    0x180c403400c031490040c010348206400c03100c1079030802c0f0510400017404c02140b012140e2071220780003100d60310700c401c0c2d84541c54000c10b07a2a40e0024070240380d03180d00401000e54804402000d440c0420307001100301825411030f4401d81030590003c8200248d0f1024100551302812090800c110b89142c402c124010125330140b082c0c0c03c845000c2081645010300f04010070046a11441c191400010406030320ba5030414103000351b5080c0e442180010060714200d00700c408840030481c01055100350354420356981080540b060061392401c0100d03094411303140c03002d00000400d60b501d0040b242020f600c00560084060a03841c4580420042000800120101000042d50150800601d03071a0541c0c030302d004000d040b070300d007142d40036450412404050000007801c500c3c481c0c10b410081551140000381804520f0301461350190300c10000b20f10700200105491154910038812034801c1300d000c00040109401c60fa1003520540d0300c80c0103000c0f408900f400341901421050340e04200381c801c844000780c0d60791307005488 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 496002059 1250 496000809 496000811
    0x507080c1b12040b19050c060106110a060606020d02210901030906020d0c08040501050c03160c060603050d020c040f110a05180901033203030105130209130204060f170a 74
    0x8072581d48140108480650408102619582d0381c8001c0810b0768000ca080d9182c0349600310422000074080d0042d1113141d10a000246041e0f820003106031030280e240701c01e07660070b445a5029003000070301901540c8080c01c001e601038031840c03c0d0703c0300103490700f81d2301387c00784400703441c00920080504288801d6400904007482c01261143d0310703041c0301000740300350703212482d00c0c40c01c0204820015800072a640e00903071240713008002a03980c00c81203009502040e203031800c2c2190304004402a4a201e0050700c41414000c0c140003842c69543d9031094a0481c810b0b4400c000340e081090031a0741031506e4441e101c0140b084110500c20603448034404607581c441d030310843c0306000000c40c4018149140c00103644a09002074018040da58490030052a11000c20100020304000381d806901c0c2001e918001e0005c0e0030070003006504590900081001540c402c030f185001c542e0b401c0c050b2490303d643c0d0008034039100490369001079850b07061400061103481102c118009200019016500d0005003004095200d8842d03c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 496003309 1250 496002059 496002097
    0x10e0c01050d11090a170607031806050c120103061b1d01080c0c01060b07060506030c01090302040b010c0606030c060221090f0d2f0d0b0f07020c0a180507080c 70
    0x3070315106070041c0c503e55500300e001c00c0d002041b6001d0a000407a50800c1500855000c0d6507043c00803010f0741c9001d03c045811a03070a201c000b0026419400c5141c0119061060310b04240f0340340a4a102c0354826441548c8183c1c0b2a12080e5501c1880c4040302040303401d51400c2100d00007403c0d80c0303c28103800300380340604000784040042d0303030068020152842d008154000b848441c2d5602c084c54405c1c0c01c41c0100fa50b40070f00d8100855000d00d000905551020410b8445d800e00c03500c2e40d002c00008044040c0404d05105100e02001c0c000707405445aa0040c41c8544200c800c000c0c1800340082c9880b4540b0010380c8099071403080e802c80c4c0c81000098905010007150026180c02c2da400c042400582105070052071040107421100c011784030824a01600d61042070441c03180128402000402c0381e1640c000b411034034410000c55904104144e485500404078012106905e949802081040720198440d120031118040031031000c590038000d140d002000c6250803500ca0070520400c0f9600e105040d14031241c2c80e00d0034 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 496004559 1250 496003309 496003331
    0xc330903020d080a261f08030a0503011d01240302211609150e040204050303030c0d0c0804020901060f02070803030a360f0309050301050c0c010e0c01050d 68
    0x8100801566000c1c0003a8071540305440c0808042d0451804030001c582c2492801614800e042c1c01d03000f0443c41d40c0c42509464403954031005400c0407a0a000345500d0f011540800d464408100409000840740d40c0c01e0307500d40c544590086c4010000c1c082d0310290700c1600c010004c2805038210312132036070f8915072444505106180190000d204030780344100c449071110701c01a4541c8021400c41d1103400042d4200600120304103080704e03444e943d4000c40c12061034414202c55145d21400700408010b01c090001403925486100180c41d54004580c0c00c1503c035000501c0e205410024080c0904920707990a12110a081540c0003c20b00c1c20705000d14001c016000104403c0e0910803c0300500500c0030704182c030340e2401d21b004000050040502030046032080030403101c05239512609034100314094840b142801210340d550f200502800200142c08000c3c101c0b5020605a6080c400e4501903403e0420310b41d80e407118100706d40c0c203403058040071a0349608a08030b0700e0403d0341c1090444001d004400c60000d00703a1900703 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 496005809 1250 496004559 496004567
    0x50c010b1c0803070c1505070206100e0c0c0316060510091401030b0603192102071514070501020a030b0f1804080307020111070b0109060f060e0105030411090a05040c33 74
    0x5c1c0101900413500c00c81c803514001c0203a4401e60080819900f03661031551602480c50b92041d0030b105841181000c1c10000710050400c00c05840b150b144036058078039148015130039166501e900d00341518065030300c50520280d4050442c050000305200c000071300010412038003d00c1d080d141480050003160700c02000804a980620192120819921450391050703120700340400130000d22800510010281a0212040c90001601a04660070108104d8003101450812102c00c07140580040d074851007030001e2741c0014002e0001e800c4003a00351303030001030036001d4004120350b94216084460184079003c2031502c185401400703450b80250010340d010740ea900c03800c800702d00401507041021003d20001c0351300c0f0100b000c601e2103141200c0038008240302042d25103081440e0840a482403c2c085002103400d41700b254052000b8550080c0100b030381a00c03004090000c00d488200031900c1d009001d60741e508004c200f2915802d0840036045815100800e107003000c075254641a807284282203005460344001f9007561203 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 496007059 1250 496005809 496005827
    0xc12020f03090d1b020d0c12050c010e040b150d23070207050d0206070b06031603060207020a0e0c0a0305090c0a1502011113030605130f030203070314091f03110a050c010b1c080307 79
    0x700581050340d418401d488690341080f090003d2504330f8000b11a1030140101000302c0802030419010345100348001185030f004503443e041c000d0f15104a030014a1074115400e10440751301d1781840a61810490080c10040240c02c580d1003610140c02910242e11010b0503104050740c003d9412072551038080000340b03000720010002c891b8140c40340c0301000300103850700a840030a03c299009101503403680700d66403a055045898000407001400040740c2184280c00007070700a1200802c0d00c07002d14008020625805107904028088075100301c440954a030b0900c00e040d15050120565410030054802d0815030380034910024004070340318004101d05c08003814080031116400495142c04010506d000307502c03600104825400300708098900070300000c4207001c4500168000300094a92407030300d8041101d030501d00302d00c0b0302055035440d2410041ca010038010a4200c545448bc19250486074540c00d00356109074907860300441d41a5a00390003900c0c0400e4041070564400e6401e602c030f99410704d040710000c030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 496008309 1250 496007059 496007069
    0x80604090c060e0414090316210e01170601020c0111010e03180306220b1e0a020301090b03030403021f140f070311030a0207090c12020f03090d1b020d0c 67
    0x11001c0010b440f41c0124214a02440a550504c902d50803501c82440304a8100c0301c03400607810802040120110304010f64405a01c0380e22200e2040300c910000c1044041c400c0f82c584003051649840078015030f080100d00000b03c021440b0000d680c40c03e41c00007502d426240b001e842c1072020214856110314002e40101c800c0e10314400440e603c8640241e490300c403500310445520302900411000c1001601d8081d0820f40e90403410b10006007151585c1e0f900175040e24001c2a00d1000120051000d50340d00c0d80920381401034000c0d000150b26541402c0c4480304440070740003100d200380e03c200000c10050b11040f081120392010100e030b0b40044124801c0988c1c294200307020300d2042c2c1c400001c89029103508040940306103806942c5206048040340c00e190356034458401c400e009644181e8080014004980191034041d0841c540546510760a00c1428241c4c0c011600304081c07050040100408070784108810341c4010441d240c0120302500c0300a11400c0700001c2e00019005d860000711000610540140e00c000500d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 496009559 1250 496008309 496008323
    0xd0e0f03070b0c0715050403050303070e060403140f0c0307030312050901020f03090106060f03111c1803081e040210180308070302010207350702030f0115060912030f08060409 77
    0xb110b0300d483c454075501140507a0540e0300c180f40c00c08400310f118030191000e0b25408002186036889440c0c01344e8000a0303050505601801c00c000100024028034111081c034844003000388460444c002c201410198231090300c42c00384d4010361041001c030794080150803201c3c20840000800780c9440030500c0c0a03115001d50618020000400e10001650551003101156a59654040c07549860700d07048040d107070606650b14a41006104030020760015a40c1e000000c038420348002a00c03c4c3c1c0e007851808064181e14142d01041d066000c103d0240c100c01001030306400d0402ea6410180f801e49e0010f10f0b242000074042041084038010800c58000d0840311074003a6401c1028243c4801035458000d0103940302010440d0250090803584030111890142c0030002000c00100c1d100c034510181025840e90000401a42c0c5881070400e60482d0803020f1003070880c1c0750f8035000800c4086042400190011115070f00c00110907101e00e41640120b9030010440c281c5952500e8210159200c040002d800780040f090040c00c44 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 496010809 1250 496009559 496009567
    0x60c020402190804050709050f0c09030705040c050c0c031903110106120c0303030b040b010906110a06051023060403060c05120711010e030702090411012102030105040b030d0e0f03070b 81
    0x600d810882561013140b2800490301b600780c0700e00012007900c0c82511b1200245400d4004070f00300c070380c0c0c020142038025000380864042c10b40d1140000d05a480c07007000300e40803540004024003064030511150200e22010b800500300e40c42070f1000a95500c081e404081c0801181c1c24200703418400c203404c01001450203c0545403400340c0c0c1d04001d192910309200c101c0100389445004d030703d54103180c02290b070f107404141c42e0020b4075441d1400c103968548810024402d02d0044000d0b200002c0c0305882035601035229960f04901d038a0070085604a480100303403507040d94108051070001c95a590300b04490a50fa48814046104441c461064a031800784212804054004804001c02c981c0e105500114406070740c0001e21041030700e4100300f038407803190703901c040c2d003000b50740c0300180214401e0750130107084a5041c9420100b04141d200c0311800c00355003602e2140c0c055000001048030349420300860f00e00100803405815490706802024000c0f116203492076001d107100110003481d95409200e00001404203c41c0250f076 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 496012059 1250 496010809 496010857
    0x1806130b0d020a09140108040308070216120210020a20130222290f04080a0507051305060609042d050f1e070c02270f090f0304060c020402 61
    0x2e5001140f40e6000100309000c001a44543c4080c1208040810703110301200e510380d40c5049400a000824030020751080c0d41150081d901c2542c2003800a0100c000341d40070448191042010144140000004550005410002240380d407144039403561704441c184008404c2410200760000c00d102800240c15201007107407800f01c0303500001603042c3d0303000c80310b5103101c281c41d200038a0400d03542da0040070740d8007200c21200c400300720b60030010191103080294040c2000d40d604030740d5142c01e01030f001c00c49168102c0d40081000e030500b80c1441c55580d05d10354061195240c000701050043c09454003d80c4155154110424a4400611030500f8140c0c0d0300204040c3c003000d85a440d000e824151070340c0514040481c00618207000e0b5602552000c480c00c0d072f5480c0546c580d00c0d070440f01d8440c044002d030391002244010b9440615985c0c5403007070f0000c01141c001610f00d068090108038000081c40701c903040c3c00503030403880c03ea0b2021081740c3c01d8840030f0074900c95000071400498000c1c040c03403602061800d48204c807142 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 496013309 1250 496012059 496012061
    0x50109080a030e0c0a1401030b0d020d0f140a1707230106031403030601020303130c05040911040f1a060d09052b0c0506150102010219080610051806130b0d 68
    0x6070750402d03c00c0b69134082e0300c9414030603a80c1903441100900410410000007a40c030035002000240310040000380108500d03000584840074003441103d2540301c441c004010445104840e400b00e0002c41c0c0501120525922a030050138111416031310a074800156560800c25074807449081c4103d0b442101c14030502c1c8004d0380f8000d0105000c15205100000d1107000e074010000f00320fa101e00010388c003541c11901c0d0701b0410403044c84008003c540c0350b031560402280c107072114400c01400342e0040308091031200481c41440200c440013031601e051503003000f9014110545d0116400d0421384143c41c82c0b65540b90382c40d03241c0001e141d6208001c04030701448585c641081165001c140d21800204024003403040e60341e4095908070500800107000390024030008000d070120445090081c0c006000140c90308000d07900650200781801c8040010810100501c4002d0030043d207035054044282c10060703e002c103240741e140d10b080703140182c2910650001030700c1c000501d00c2e507407850001c1228200c0355481d2000410418 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 496014559 1250 496013309 496013321
    0x50304060e0f0115170606180c0d020f250f3504060e0a1505030c07080703020706020606040905060a09020a03050709290105220f030b0906010803030f070c050109080a03 74
    0x2043d800c1c102c251000e0001404131b40c1c0360140c0c000801c400300009004103175160203100100744040c064814400c00358a220103000802c01f21825000ba0b664500c0040344802d1104500100350100d03400c5e005620300050b140080e08240315810201102488140800105094007880c000c0c0c0c41d400580324903846030050040191060301c0c0d894070390281c035802c09002c2c800c0c032015a1280004200c007181d0041c010074003d40007076400134210304c1003618003100394480e051a81d000c0300c01280103901c1600304101d0a0b03414009590001c0c0101c9092141959030f481ea2560f0ba4405849944143c3d91408031100310342e40c510580e4015940801035035513440c0d0720304103040140440345a0030100540a201a80c02d8110355030040c0c91004140c441c1820080344414521605201450591105120f20400714000b040c0d00c075600011841003d0050b0b02d8580444150b00b0001706a101c0d0750540d10074024404007003003882e0020f90100e0303a0314080312003141d10709205003d0243c2035000b9080c54000075005420035499001030f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 496015809 1250 496014559 496014569
    0x1e041e08060402093610091e0804050405040809011d0a050f0f090f0f0604290a09050c0720010e060c150f040201110708121c0e0607081303050304060e0f0115 69
    0x28500341a511100e420981f5903000d030041010000780048046104000c40503590103000341600c1d42015111008902111010742e0309481c142c8004c6104503a42da80b20703450b0f91013208045d070090550030240c4049204503c99000c1c01c0c0c0b040c8600002030443e616021481007540380010400c403141d0428584502000d4002d5801003407849000c0005030803400d1500032406200014600c0b0a00c650b142255048880c04985074543c0c054110312000407030304d03801d0181d14050031a2001716581c130311076841e050b13085801c014a41c3c4422000003075450001d0782c01c04603403a01c0c00b1040c2c4038150f840e040188401d00304500d0f60040b051580181d424462103031100580107105074400e0703c07581c2c40002ca00b080c1a64404941c811001c0c10fa0021305190102d00500c0d000d052080400f85205442d5401c001c41c4805541585c000360300b10b94050f008003c0e08590210303415800104105602c0d00384896901e0041c07003840000e2001d07040544407030021074000e03403c100306810040341034000c00c00b00a1807070340307064407a0306031141c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 496017059 1250 496015809 496015813
    0x3030403030c080c070b010e0c09030109120e0d1707020d0501020703021c0302180f0d021302180d110f0607140601030506070905090a111e041e080604020936 69
    0xaa841504c440488107429000000c0d401c503030303181c01880e01d12008020600c080e100c0c2c09010541040d01c09000d000016031140c2e100040a0040ca0300040681e848910401d10454081480d000070402d4121514001d000e50f011181e514212400410310360b404e41540100f1a46c40003035500181503000c2600c0141c60161000311f00464003c4008030103a00880805001204c20048414000e1903c500000380f404009098105102501c0d0002103000c04000c04030405150001a003920a0b03101e00c881060050b0200d40381c480c150141e446d0f06078030b05244200a80100f090039007400c0030b0f550b410191034600350300810700803044186001c05615a00c0a200440c4c1500c19a00401c40003801a8034030380544c0c90180c4800e1159035022040009002c1d41007006480102c102f03e601011040303025904180600b00000a40c3e40d845d00e0040e08181c01c80828201c021070f0100c0b01402828008110f079038001d501100d000499446816840d8a02c0450450814002000007098410038054002c0f1019611100b41 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 496018309 1250 496017059 496017061
    0x804030c18060b09010206061012021c05060402040806070c0c0312120f06051c0204090611040602160b0a0e181303030e06041e03031e0912090b042603030403030c08 72
    0x10f1050040c0c05207588142c056000000061428203000c05211040e0303480b49000680c6040740b491000407640105080200121a020b0520b0328104a004013038100c01d003540d00310b103064a08820181c80346009015541084401d10140c000d001602441c040550f410040c8690004030030300b806040609030112440c42a030410481540000b140d20032202141c1c0050480307403a20390002003c0040b9a40f07071402300c0c0d210395034030440e60125080307110710300140b6081c0d81d03c50358403414038201910f41007803042c0c41d80c0c8000d4078001c01d1240c203d01c034003568041810745c103104900e030f41e072040014155a400e0f203240c0e40009601003002180d44031000c00840c00b0740240c4040110760030a2101755180c40003290043c1403401620100c5660b104400e040021090003840c000a410f54141741501c900c01d003296101300c4441d12a0311801c00d22101d4103070a0b0503d2a24200400224031780900d01d01c040c0914403c0f11000ca03880d03001003086045100ba0220f41d21290002d5940e246010f10b009402001881041c00000310810 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 496019559 1250 496018309 496018319
    0x30807080a11190b13020a060309060e10050118090c0e04110904080a120501050901211a06040608010c1d01050403240c081506130b0313050c010903080708070804030c1806 75
    0xe80768040b003076006440b40c2c1c0c400e030400d482900034020b400c02c221500ca5482e414cd103440c0c4003e00c1812038815640b00d001c1410f5150583d000c1400403122903600c00c0501d0094007000041000802104990300c12401c440390303a0321800c1005140a00144854204840600300410020322100138941f14005407280c0b090900d00000d071600f2030341d09000f4aa0000b075408014050100701d85040d00603c40f4521815841d10140c5d5501c00103179074600c511002d00200c410170703c4564501400340d4405085100020000d0341c2400340000c049202040510290680b11450100903074850701c100c4000c2c41d0059040c1004803504020000b650032160401c000b003038504510440c1c001e1141400c00d004068941c0701d010b0050480c810001c19510907103580c51800c1e810400022001d144201940c85078110012400081700c42e1704045003051015010281000100e000900000b0110b800b594020341d00440342c91340711005480c294000380b01d00c0e0405420013a6080000401c803c2070715913425140d150380024069181d4403 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 496020809 1250 496019559 496019581
    0x70207120204020714070f03051506091527010302031005040c0608270a0b011e03060218040617010e010b0a0e06180709080105010b04030807080a11190b 67
    0x680104030a014504004501501c1c080d006400e05a010740d242c0c151900b0100da01c140303851955400101400c2940c0020424404280b180410004000c0c00c0001640380250000e46140c100170309290007658006d10001d400e440f80a407102c0c000002c083c020124403041c0640d002d0000c1c007444101d110344945401010785152074002c95000c3c5a0103804288914205242580e020000400f0009860781c800c40c030000d070841005030144690302c40800f421000d02d00f41082105141e05810030030744007940034225213980112103040c0c0300301e030b0b0810300058558008a14100c9402c11542840781c0c06410b200e404100500c5241c0c0b1419146090f0000b0011490324501303041c20389101100c0107034424541581040b28070010f100d030a900c4600140010364002c1d00002014884005075108000600c60700f40138040c005013407041c0381c0901000d403403150909141d81e507680b40520800700d00600c258000704842040b1409021031034044044802a50115170000c4480e01088801c20801d4030b00e0080030700842c01c01441 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 496022059 1250 496020809 496020823
    0x9020a0e06030a020f03010e0106080a2c0102210906090d0203091002011b0302090f030a0803060f01110f1516020a1106090d050c03010c110703110111100606080702 72
    0x1951a01110400c90310100451900010405601070b40c08016403100c0861a8006502811101001c1c0c6890350620f84010090100145061900c40c68208101d494040d5444152a1a504801d0035503024040c0c142450190003140b940400080b95540210322240c0d14001951040c0215000c4980c103a0351b1080e101e603a0b1711168004405600204410702c01c0f03041495280c1e80391b5250340004180d070f50011038005140d80004030607000003540402c0210b041d142070b000154404108a0080088036410386170003099100242041d441007002c0280c1c1d44003a4018a01002e624000c0e07401d40f10150645181144c0f241310081248115940000004101000d4106000e803040300743c2c1c2c000d24911559968603005283c0124601d03034081390500140003d075132488190309c0c58512441c00742a01203060030915095581c1848100709100e04c581d0406181200011032000301d94001d0003080d80b01d005580103940303a000c0114400000d015504614040c146142c02c4901113855540d242c5440e03030b850490880c0c440403 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 496023309 1250 496022059 496022077
    0x1b010c0b040308060109170106050a1406030f0a0e1002120105120c01030f0e010f020d0e010b060f13090504050f0c0901051305060a080d0909060b09100804110613030b010902 76
    0x682940460080b9104078411940001e040c10080d580546171080b02c0c00c54010400c107052103a458103c01c1c44281800300440000b4403030050f1280503041c88070000323006800001c10380020b4968140003c1c00c4000742d501311440060021090701c1c2540c0c014140c404c041d503c1003d4a00001c2c4c20040006542d08240c01b08801500750032016045220a0400441c0602811596541140d032101d981601c1404d00388140b440005090310016500e588601c4090113450312880d560625925104a15a1544520046034804000c4071034445d42c031100d4140c401800544d42d0086c0302010314260802007080b500194440c2c1c2d207500034003152a09142c0104204416009000305c54100c40300704034004100c00c1c0b40d0000da8006400400003030310507403240070a43c0b8002c2c00300610303800124052010422180d00d440b40c003001c1c0c800b8041251600484d900400d842e0b4103200390360f608202424000500f8003081c261018250100140369655030900703040340b544107002e5400700340d4101030000d000181d030065510884003040 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 496024559 1250 496023309 496023323
    0x1b0d05030c0d2a0c110306070e0103021605010507110601140a030213060b040b0705060609013218100807050a0b0d0f14100905090601090e030d0e06071e0c0809061303051b010c 77
    0x100c0c01c9c60045010b500101e816514001014014030700040c0700303001d8544220010381c0c0300740d4a280e003c11082e141290680c0002411007841c2507184560b01c031031480c070051301d4060391a044090001c2813800e00528560b8000701c56000046004540010000c00404a950080b8200c0d80c01c0d440e42c8080100c26a400e1044001030510046c400720a082118180d0300c2c0060050048254100d0403004101c03c410748407040304e5507402c014200808055061040740280103240010a8254140300100b07440501c02d02880900c0c02000c031f4540b03403000d02500004800b0f00324207414401c400d607003204198002c0301625040401881541c02040900c1140304061084003900f00801290b4a406c901c01c1c0103180348550304d10640001c01c074003002c92405000d0440c1c491640c60082c0f16500d88188010f100006480c15000304404a9241c010404c0e40300400481e80c076000610941c1c0e55002d000040c8a034071580c040312813503c00605000003400000b0071003511011070903c000c4d030044c00d120300444031603104a9000b0500c0d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 496025809 1250 496024559 496024577
    0x605040510060810090e0a23150a240f120c0b09030a050322050619030510080d0c02040b010903050a0f0201141b0d05030c0d2a0c11030607 61
    0x10b200b0460190041c4038444100345990300c0d01d2024081e9a451521690598045c0801204001180030031230b07045480030355201105070402c021561550080c81070280ca00c40880c1c0800c801c1d4003543e00c4240006e13007035144d8500751940c034400820310304000e128410603c014600c2c0050b04040c81d21190f43d03104c1c0c2c02039114400d80c2c01c02c0004031494201d82d8009401d8800c058150700029030800041c955000b03000360344030844480034501c04041010780c2216004401c1030194089038410300c05080b40c01e100c213050104017503559001c9070350302d0001e56001903014807500d288994001e42060754014420b001b07440510854144d8001940c13041c0b4203100040040d0b02503115580440c1515401501051051400203002c0010483c000480c0d04900e884c000080e0301881d10019401e020007241d851308440e42001030031071500208000c2c203401240031404a06884242800d0500760101c0040b070740381c0c100720540b00381202c3c0c40030040041c6411201100c1e05566503510044520300028810301c601e9a580d520008 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 496027059 1250 496025809 496025819
    0xb0f1303120b0a0b12060d2001020f190c08070303090e09070504050f190507120908070203061608010819021e0301050109020d180b040b130c0602070303030605040510 73
    0x125410300e41030140c0d016030b1501241455035460150000411520407140e0b11140c80c1303140c01c0d18181c8042c0c462441401c8888990b070000e144081c3e00b541c4074078000080340740441c03c080142d06003071000f040c0148501601c0d000c0602c4403c10b0040020607805000030360051500c0e1164296500100c1c040940410100d1a04004101000d0011680107164400740e505207a502c0c00400c0944109941c00c00800c02e01c0c2081000c40c004108130015025000f000501c11070610100280c4000081e03006482c10740e4884509009109400007100d040a902074200c5949207803841c56040b02c460b07001d00300400a02c218000080d04d2034000369110103c000e11030200301c404565800c0050203940c000c40403051145d28050803142c1d41c0c081c4103c0d8000c12591801680d6030040030b81d040c08a80c5450201c006e42c0208a400c071012031100b102d955485540034608130030b5900d4504200950280080c1c00400100b02800007091075580400c0038011644a0b480034001d0315100c2d0100019204129131994030000100d408100e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 496028309 1250 496027059 496027067
    0x10c03110409020a1701080a060509031305040203060f03030d02030a061203020d05030711190204060f081506010c050d0e0f0a03120e060d0f02040e13122a0f0b0f1303 73
    0xd442c044c1c50805664007900e4108030380541e20264090b00c40c0341c200c0c84c0c8510503c092030180c0e582c0700031824065032401c0a000013010a68036035000f0079000c1c6a000c000101252104d80155042c02802002c40c0d4175070b000d281080029600440b16220981c1c1085d8000480b046500400d101c000e6054014081200c7c1d0494126003542004004108024107441c1c00e40e6200b000303000c584051070005002084409060040c007040e01c45a62101321010031030070f1304116810000c00c46039401c048042c0e004d01c2c65250400100c070f0440a500e409003482c055507912044041d0001006031501c80165500485c40b04454208a00000e01340301c040d0003c03c1014104880b544200f01344200d00c0c400400090425442841d004212540400c02c2150781798005418041000d000c1d42c4030382c1c001307010b0b603c41908508a0b5a580b01c0c0d0071420015109010004800d041140b201d10354038014a00d41000c41c0224901a003420142c2c0d90140400384e60420a0b0800308141e0600010124410840c40200580b076a5942da8111 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 496029559 1250 496028309 496028317
    0x6120b010c020a031b0e0903041208040f0807030606090b0f0103240f090b19060f030f110703031b2001020c0316020112050912070f02040507020f010c0311040902 71
    0x5810850740c00702480c0140e88990304a00594090004000c8115183c06600135130659030708030a00c014004010484602000800c42e003d0701d00c441e1038060110220b203020034250180313400c8502003400d12640801c80f2076000504804890094509000da0f41c0e8514021040351224000b040e0411804120342d80907500a801243c410500000380040c50440040c540b480700506030801c03000c500044500308030003940360203600c40b240c10031034244d44282049138180010040611584042c41003140007590628041d912140d4041c5d00c2e00d00c2840400203660522200754044007003140070a1800741c000c0016510302041da8001d03445501c650f03076440c4024041080c980011611060310359000c108a0b81c0b4581c06001819003403c541211012003005071001401c080005003101c02e41d1490709081191a500010713180d8001d01d005c800003940c5009509210245800c1d62002035003040c102820f201c0c4039540000c100b004400c50f940200492401b5042c21000e4402024865032040000d000600500b1140c1c2c2c010 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 496030809 1250 496029559 496029581
    0x412080706050c03090c010513031103100e060610030911040e01091509020a06140414152b06061709190c1a0c0a14070b041710060612 59
    0x11810050141d0368842a642c0c111007520740900c000c014000d403602c0c100804140c0313650908001d8140001081d402c108058144005031003000e08001100950324184051034440f0505442440b04014000b80903646610941c2c0040c059404041500ea03000d103e07114440c0c4090380804c4003e95800180e080201070800d070355542101d03541e203070180b40005002400110912001d59008101c0304e4185c01044480102c0744e10400520180d2441c0c1c1e83c2c4000000200d4064400015401ca000c0c82c8404c082100e5800d000f0440c0842c0c7c00000c1e990203600d40310940d5040355641903101c0302925192621603429181c045c0328040c04103c054400060b1500c0c0c5000036a84031135013100f1194030f002c0040701e140f0200c07400041583c01c01110081400303100134501c65a800b000b0001e0b102442d0503a800005980d5803c40d0602500d4502000e040c0b000049081c001c16009200200b03220341c8860b02d402d004442c2c20011031116100e0311400312400320b407003403e01402080300c480b622001001c030000c40981020f001c407042c2c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 496032059 1250 496030809 496030823
    0x21c02060d060f0f050105120106080c040b04090f0f02130909290708090a0f0219090e010c09152f03030403030f230601050a03060f0b0702030709110412 67
    0x1000390038aa00d84500302c000d240da200701c02115031818001421001c0c2079005541040300800040607001000d8a085045555a00d404d5243e942d809209003500d000d01e0b000507900310400140007034500e103160020345400310240f000f0424800441448000c80c0f00711002400401c0c00d80c00100004900e962042c421280140c807180303040c0e44c14948000100f5020748140d460300c070043c0305010455500101c010b501c40c00600c01441201040d4076113210200d8442c0c40280b10f01d000e9003c032800d140381e4035000c1004040001e02809040c03980040180a044544d0700b0b000001c81e2110005803410801407100a00300c0346880ea0001101c42d20541a00d004000c00c1c410b64100d81031038441c10b01c80d0108020b610980c0039a500042e503192a407000c6003030b00d40b00716200b600702100b0303e16941e000140c080420b410003800d0030161381d69034404000380d0140c0000e9014600f4241006800501861000c006205841c8204c05940c19140c4030311180c0203c4811521000030b802c8248018060350400c01316009070030f40242c81c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 496033309 1250 496032059 496032067
    0x605040c0809060106050c03120705090409140c0631030c1e140306061201142d090a0602131809050c060c28170a020c0409021c0206 58
    0x101280956100c0161040014081001c01507098800d00245000d8141860994681407006210b56136902800c262003244c5210300000c0b9601502a138111654010080c106010781003460420100b162060710410655004001002c641031809104982d800b44a9464000e0f03804005482c400000490461403002861101c0c03011000c511100754100090800c1240103074910060ba20240c0400c200d6403200190380c0c0010300095180c0d401242c443d900503c281c6030780302d4180790340c5d04840c05040300219040358009080c2c140148a080e00318400b011400c68800c0e0009120709801140700e400d011a07070300e020f0381c100400c0d450006403580c004020030480010038081080d140c0c8080c1d50040003503800500440da482030345d241002011b02000e160b40a00701c4543c0c1c20052642c40f0141c4841c4444041d230400e8070b0201c1c405400c0e04082140308811030b08988455444401c6082d4618541c5c00440090050300c40d0380410304980c40e00340113061b2410b40c064040340240100120b40d80011580c1c1000b00c1e40201c0c240 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 496034559 1250 496033309 496033319
    0x10e040f051b15040303050d0b13060303021c020d0206010303080c0d1107031e02030702010539060603070311011211030903090a09270602041e15090602060c0d06 71
    0x20248400408100b600c80a01c020101046420808079148510070f400600c410000710380c0010a865030707640e05000205900540f280011311021440e00d40480303c031324090022060550004625900100320600340203900d86101c42031307a0305d1080c683c617900141e00200060000074820b03203525401204810f0710340c2c20a6146190003040c0c410690300030b00d0410005ca0441c0c14558086e141944d1604904106114161003105c003e42300c2c441e001d406070601000040d02010845040703d90012176614203c0c605101d0030341d40c00c0183d12503c100042c2000e00c220f8011420360f2502084c1d0904403a84942545408400d4100641d0f0804da030180e650801e541c1d881030b40c1483c480210086103e080e50802a65650115000b00002620741d600502c60403132610942d94014035910b920701c03032440d440d03008580c2042181d01d000400b07485903401044038040920f40d46203c480b0081c4911080e01c41c800400d0060300d6006104541d040900e205010060f40000701080216644800405492a0344480403034070340d0311a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 496035809 1250 496034559 496034563
    0xf1602030d1a011701080d050901020307060c02011d0d08070e01110a050c100e0a05150d11040e0106030b010e0f01270f0503030a020d0f03140406050402120c0108010e040f05 76
    0x54124044202d00840e0420095a4468101c500c5060040580d48855040c600826514240f401280b81404000540090168020020380f009a5400780091200000c85603000703010301008503142404190745445494a4030300422041c1c00485559200c2d0419654940100c1d00380b4464802c43c0d043c030404174214585098140040094940280010034881e0350701d00612010000080c2d903902004803d190340e418a5503114103600840e40c08840e003511000d2807071a00d4429100d406032030300b51503181910016242c5141b101400c111050701003840c0c004e0ba40c3d141c0c150103540307242030001c0c005503005d404101c0902d0422000e25980c03074103142480007401e80080307120711600101c400612101e4600000c02500c5c07010111003010300300650166060400141c4042c0d51954040090420300404218020391503100e41c2c400c0480d008004446000b506050030800028142900e09900410000c410802d81140c001400c142c222070680d07441c8542c1c4e1174506001ca10000281c022a2078900c2528040089201 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 496037059 1250 496035809 496035821
    0x30206030405070e070c020f12070b0c0d0905010905060d110c0703060519060b0f0d200a03060605042603070803040c1401080403052512050c070e0f1602030d 69
    0x403442c01000304500b040305180070240014183d9007080001010700c00140c440340543c0c9a60f83c4141c540502014074041602d0520702c054103c840380e0030020591070310f00400003a00c8100510b69840b0545030750b41320801155803c6841c050700d604180c0030003200c503807004030f68818488070310400078541c00d1194100c0100d003401404c4d40281c2c0c0250326001840116014140325408401042c142044000c0c9481040021030148002c41103a1784004165040c24280715009040c0169007509003280c0452140841c01c01c42d08043e007000f00007450100046031440c0100125010740c1c060440300030300c18020701446480e00441c1d8124007242d0200744000c5000a69540245004512468030712a59904010072100000710402d80d80341000322a501740000f281d0000c040f12440261894504040741084100e011244001c4100a010440d0401d071911540e9105000e0000e01e0090400d4a0400d9034817090300c0800c0000303a0391800038811301800709070b042942080c25801e92071140156410690454002d004441d4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 496038309 1250 496037059 496037063
    0x92102120706030506030d1b0305070c06080103210504051c0b0a0518010203190b1f091502010618150306020f040612181119031103190512130302060304 67
    0x844608144107543c0c241c0a42944124190700030310001c0c0d0110402010314a0b12090744004100c1003030b8136400c0c507105500720b8284503004090070b000c1c0c03a42d490005000300703003d2100b581d41c0d80d20b03010581d1310b00070403810081d0100041d6070355034109800c0208000f0058443d0030410a050031002304900040d14049003144940201000003406240c500002c04085039a40c05c0792140d64410001c018810790344c00e1411200700b5001e11f0005518000758041050000c0741050100140c891b82514440160f002c58402c1c10703a18002486050398000c0582a400c0c1d42040c01454501200e42501254442ca05d610002c4154100d02c2c0c280301e1240d998594404a80c04002039007141000001c00b03018058000c26802e0380391207160310030002500341cad021083c3c00f00300300c00c0001c00c010307002c56000040395214900450b80b000c0c0320495500166482c0340c001c842c50065080d283c000d018901100052a01268141940301c0c0c2041c041c0c030009086071400d44c80da5221281182c2c01c0b100d001c40200168a83c180a144554 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 496039559 1250 496038309 496038313
    0x5010b0c0111070b1504020408031204030912050601030206030406061e1a0918270f010b010203070203031c0603170c010b09010b1215030f16080d09210212 68
    0x9480d000680d00390740c00301400b00c0403a40100140c0c000900180e400765400f03103900e0300c4050007054450020380a440341e50300c03040551101040312003c0c0314503031a085015a01c2500c988080c1d950b1042e01345540a0445000340c1a9001a001040942050303402103a0043c822900002c4035070b01d8404018500c80c2d06c0c51610414400c098050044001e141d010000ba032000e40010307420900c1d203c002a0194001112281c503903491040800c000d075805207034011403900f0302025051200108003000fa0b1f030740c0406613004201c0d800e01c60b9218035035002104840e445038010300658644850700060b11005d4680b040364241d05a5a550b00101003014040241d8001210400c0142c0e034841031180c00707003500c49422505101c1c8000000402c40c4506500859407052000d070001075083d95404030032900d4119008d20a505402034810300c901d40d40c40420240054900441a5207000380c890b400b01c1e9550744503e000c0c1c400301c0c100c184240310604203061502c2e501c004040c48240000030329400300c0d80c44d40486122003103035 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 496040809 1250 496039559 496039567
    0x118050d0f0515130f020d0203070b09190b16051903050a030507080114042c0d0909020a020c090408071208060406050d0f11011101110a08060402070c1505040905010b 73
    0x10805121059200e100d480010215092a030041c00d001d4132540c10081819490800e03803000c64a510f1a8030901c0b03a0000d055903151942c5200088503035001c01900703440f0b8559400d004441242c000303003060940300885550ba085c590311940b0b0b44442071351004180e441d842200c0760740000465080c0740420b0715103e030340c41e01c0e01e031014204080d0550300007600d0a004e0089190042c4901c81400e00c80704034a040440f07000c0740c01c40c120500560b04800704602e200346076400080c0d84420780000100c02140034050359131200080e0765101d040f0200d02807051550010b800c074881040b07007850a41c0b074030390308540074422082c9018010b5a803820b02480002a0401144034407041101d58905481284003c6c0030540b040034204160740d0300d0340e45d84e030800d4200400e002000350307844215900c45c182c000c5103042114002c01981c40c400220b4046508004000000941c0c10300002d40d05050034001e0f941095400300c050f42240f070500382c600310780100c88020340d0700b04007090000007910020b601465000300a40045946da13 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 496042059 1250 496040809 496040813
    0xb0402130e0a020f0915130b0a0b0a080603030313060504060f0c0306030605090f120c16060c1112030304030806040b1908060115050f030603011118010e0306090c0118050d0f 76
    0x291024110b0076846074168078100300108170000060120100105d80742480c1484045540c0c000f011005210b070b4000b0680e2032701191030f820550041107441c10944404140e0354500c2c080565a10080710103000b21030300764a0001c00204680c002c607800134807032000801c0403082c0c01020310841d0720110319a000030740c0390103041041c4140c92041c6504640158080c2014848103021130b40d44294038084031049010005114000c150244062000101d01c0d00302042d00580e5a800280403034844a001d45001c0e01c00940e1000d503282c030400c113545010f0218003460a560315a04c054940590040c42650003640703541c0f40840c3c5a8401029031100000307207140c1c15105081030b17041443c180050300140e2005041400c40d01c4a140c00c603094658001c2d0340d148040d540d0b590040802d01501c04012843c100740d41c08541034150f005103c550f280118802c1ea545520101c0030010907560b804d040e940d00e0044c2d004654041c91030b52086201008400c00c060844c20441d5451001c142030280c1e00b00e055401684c444038401c1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 496043165 1106 496042059 496042069
    0x110f1005030f010608010f060323100e06040e0c0d051006170c040606091202060702030a03020a030f03090c170f0106170d020106120b0402130e0a02 65
    0x1441411240068110740003564044031903010310b0b0010940340d11079840c05040b1144c2c10b20416180c0e1411505034000c01e070141186040b40c4042d000910800c0c03c04840901503154808402c00c02442e00c8108465000007a001c1c0384214209042d010102c200015003524020f01111540d00a049030b2402521b0440f406030110602c9080c0700c030006091030081c00d6076070f0a1150300c003030302d003000c020b401000100c0307105004480115900e03900c20300c441d918441034403940ca031020b0f0001c3e14000407034001030700c0c1041e25001100164490000c0100f05640034140d100e64240900341400703840354659544415000c580210a03800b006c1c040504c0c41d0358070810540500c600c0000081200b503844012200c4008000441c0014610036500c1c0480090702c14880d00c07044034240ca0201da4501e07410780d181c00715041c02a0042c1c0c0d00800b030060040e1205c4241c8100701e06400390324024000c8400d039106101b = true := by decide +kernel

theorem cover : BRFrame.Cov 495863309 496043165 := by
  have h0 := BRFrame.cov_init 495863309
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495863309 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 495863309 ≤ n) (h2 : n < 496043165) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
