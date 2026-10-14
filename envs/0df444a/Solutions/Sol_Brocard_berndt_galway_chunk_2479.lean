-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2479
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:50:09.019019+00:00
-- url     : https://prove2.me/submissions/bd5b6096-1f54-47b4-8868-5c253c7a0297

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 445683453 ≤ n < 445863309 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 445684703 1250 445683453 445683467
    0x1315140f03090c0108010e071b14011409010629090a03060b0a0605030121140a0b0f07051201091104090f050a06050a1a07081c060602060705040602120703030b060703 73
    0x50300036400c40f514412a2801158007500c240f0801002101036004030701c2d2184510160014402c0402c0345c607032586940d07111040301140c641e4180c0896959a142040c0390311265041c1c55002c031126000700503040c036052880d0018104590b20604410010210400401201d025691080d401400030b00340151030b03150003001049244007461060760218000102280f08404407816111001812003103900100c035410082c140e925000c480740410039000c0c14000c0e004000c2952114010140a5030900380f20000d00410301010300301c3c3c001c2000030403040c00801c0031346c040131741114003904000034005241d444000550041d0b0700048016410007020700040c4078203401c9a8001e501032002040402d42d00c0c001c00c030040042c0c1c8a01102d0032400030400202904603005020340c0c9000b403500790b1400c10300a4209201401001502a80c0d5aaa103420b01841d54100312042d801256402c1c10380c5800e04040700607507501b611003545800780c4000140d00b802c16104c1d811104540c000a80b480342c4645983c80c1c044c00407 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 445685953 1250 445684703 445684711
    0x4110621060307090c1d011b0303050604110307050a0f020c030a050102031608060d06090f0b040f1709010210090503090307080f0f0c090f060f0a08010207020909031315140f03 77
    0x280b00c2d100b408200f0000340d2050300502011391b01d440207504c68180100c010315142d141d10905001ba94004545030702c00300400c4241080c4290f03000613282c90100d040208407448058103c0012400380108141c5c10b4010701202c1a052140c00c28606505585004a107800000c107445501402144914410000150051805030303040c0c1c68001c1d69203004107401c41e091682180c503503030312186901e003d101054442d4096144580070f246008a4010f1540342d20007000403e480c103c40070700309150484140808481c100f803135502201d2071580b074008880c00003940c45114100c2c413103155a641807041c0c200001042124008000601070700c03081565080455118078044e4115039090050313242d190120076004c14003004092004104208030303107400030b40030080c14005121070b800c80110342030b00f001c507950440e03c40c0c024a0744c1e400150341e59019205004050502421203c26075000b4000c103083d54400c01c450b84241c81c49130201d0040c5801c80e08044500c2c3e0450f4180c04040100081d4114800340507000a40c42 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 445687203 1250 445685953 445685959
    0x130608250c05010b090603060105061b01020406050a1d060301150e0d050c01110601060f050c0f16080111030c040e062706151c0c1101021917010602060411062106 71
    0x800108102401a001400c90381b0302c0d455080b05005000900e000c20140801c03070040c040800c281e1540e0912142281c3c815000003000c24008284090615070099100c1e407081e0311521403a8443c0803180104955000c10b00449080c46941030001c11181d1040c4d100b0b481024005001203560012400e01540369600402454000f0b240c4558002007a0400196070341210010303a5581a01541c8080881d2203400074080c1c48224040c00b0410300102d00104540c0b500c0c0240c80320440d00c0d603440d0403d036a084407400405409101020f000700918107000e01d0650b02100c8600d000d03e0f4540d40c030080010a07448036070403580092590662044c10401c04412994800c1c42d05641340c640403640000309040f140145102000210125035107800046c40303a4018141500b0305082c03000c00c2c5c3c2d18181c1960300fa40c0241d4107050b8140d04030401c0c0e203101a8060200d070f22001a1220b911b5041d4188080291140b1004202800c0c0808998801c40d40703440b98022103440880062004200001071440c1100c0b0b6002a00d000e44 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 445688453 1250 445687203 445687211
    0x1b02040218280501050705030d0f0e06070801060e0301060303050915090d1a010b07110d0222240501080a110f0c0c03060c0310031b0e1807080102130608250c0501 71
    0xf000d50040e0100d0394100d800c14000d60170003803d454210301134002200740f00344607900d80d130362000d990b4410051540180343c40c0e10303a40c03c55070400c07600401e000d0340c070000d80f48640e04000c020800b00f80c02400701d4042910a03100507949010322046804580b0030020144d03000100100000709016500b81e0b8116404070704980c2c48050303643e03098a00654010000c0207800300d40c2c50407140000703152080300b1404503407000d400c8551020034641c270341210610140d40c1e4849240c803240044540d640340181280c8900700e1084009200d41401d00007050104010920701c038056aa0302c083c0b400e02640c00070344102c1403540c40130aa44a44c14001d803a112040300c07207864002d10900c40441e0080020800380c0780f1a200034490003003050701e16203a40034a41040340814401c0291501c002c00c03461144003409200390143c40d01c0059003a000d1401c185030401030740c801cbc60141d105008001029540350b03000300890740245031a03901740e20f40c1804a42040541700c0c03015240144540f04148954002e000c41e0041401800200 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 445689703 1250 445688453 445688459
    0x100b0c0d020c03012c010b1201020d06120f03080a020c1c0f090510050d151205070b0f090d030302090904050c0f060702090a090312060b030402101b0204021828 70
    0x103099a41c030401821010305c0900401c51004408182403105400c42c00c00032a20740d13040c0c2d000c40c0712502e0903400520107940005003058002c0040c02400014526800c02d42a02c02058541c0131415000441c000d080045403004a04400c0341c0b501941c2c0c4407503000c4191a0210218034903000d03040d18815000340401d5003948085042c0e4040c05a071011160007505010b143e182c080d40c11645603210380700b10190f0b16134914041c6c0c0003034442c0e00030202414001c50b43c082d150b4241e040c4145802165400704024040400011100c0f0029005491460101f61000da492900501d410381c0070f03000b10001507822103180c4003004107200c0009105a0b000e101690047c2c407400448043c80101d00c60f0000184d0420350760b0010407080d06450303025900c61400b030301c1c021540c08480342c0c0d01030640e65264804110050044244010351518800d0454280207600707210301d16100f20007402c0c22450030390801900c2158082141505418401008030400e80001e010b24502d20a17000c8102950f08103011002c8488100340c404 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 445690953 1250 445689703 445689709
    0x13050316051002030f070807060b060c07030b04031e0215010f06170a0905150601020105070516020906240c10060305070e09010624020d02010c0f08100b0c0d020c 71
    0x280500c0d10014440400504010500c01074031041d441c03010440c402000610356030300c203041c042e00900e44201700302c5603284c0c907034100001600c1100c081c861042100300300f95000480700041020403254440c00002541c0d4441c1002e48482c0741c01d050200881440e103940d00c0210794041014803500703d221007a01c51503600c0320b0071120310b00d125000343c03c04100128180320000c40000300c410fa111041c4a00810329aa156035590b043c44800d01d1450300c480d0b880d609101c130307668080c0a00d40d400110340c64083e04090542d506c02100e03818030746020f4003410845010a0fa9a1a09840c440010880079440d14442d207964801e40c0b51640000000e004500130740181060340b00c010700411b0101c0750801c0042c6412070801540c0c004444016124a4a565860100081c681e03803048a00c100000c00ca01ca42c6041d5a0a0350043c0c02c0041c1443d0346000c6915003500c0286480e0840884800100d071407404400700d0f81d076110346690841140d08400d4003203034041a660400c21000400c8810048194203031750004054101f8 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 445692203 1250 445690953 445690963
    0x6020a020c120c060f180a0806010e0105060f0313030c080c07060206100312080a020424030509071505070203010f05041b24050f090a140301180512031b0f130503 71
    0x526407004081110100c00041c45c8060f26288085a4641507113168035400070b81c5035102e46d8400c804a4200c24010006c002c2440c50032801008241d81e16442e116036040004041d100c02030403510382110b07000070b600134144a100155000b030b41c0024070a40d5821210409565402e162040750014818200002e0014143c000c1e0300c8226075000312000b20300e120805040d1103100c7c00400085025609100000d155584103a040e8194001035104000024140350300034159040200b402030942d00440040207904050900e810780d506041c43c1c115101c00c01c520000740504601e0068200d1141020f06100501134021142c168488040040b195000d903104c41c4403001c0d61180102c441080c1c0f48000d402006030043c80100a24034003003c000f441e119000c400108004015003299810009541c0509480d0400b441000e0301825101c03814410300159688580d03840400c0c0d0400c0003c14000302c04a403200524100340d81001c0c203400c3d42e4540307038580600c0b00319141e0401030310400b621481c5540010b141c240811 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 445693453 1250 445692203 445692223
    0xb16030213050135070813050703020105090f120c0916020d120e060711011a06030114030705060409050f01170c150f16120819050a0906020a020c12 65
    0x300d29032201e40340c8001900c444080725012540101c0400d890341c1022401e00c2d41c030340c4c206001e940f01c090703070306103190010100c2100800710100d990703d070b4465901090b000908201201e41c24a0000c0d40d52440c940030960100c3c50040c804c2d045201c1c28203401300040007203000394039039100b034610403e0380d540c00842c9520719000c102c0c1d080250300003003070591815214000c0540444001b9a0200c9c180010faa80e0354a0500b0450b0504c1c000341c005800401200c10a008814550051f182a6001c050051001a10750701c01031050032419403100c0051495500c080c80344000820b8010181a2125a00d0840304050401241c00c0c0c82621034001c00810346403c10700018401d25a0b800003040e9482e041814048071038406403560394154000d0040d40d03c1400400014000e000100d050480a0641c524050307424814201454081c0081d4204001080b031506501b548a904d1400b804a55078445410303010003801100c501410f46030001070700f0080300b600040c1010820b0000e031030750741e40081072801c19611030310814 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 445694703 1250 445693453 445693477
    0x3020310021e03060d08220509070203220b03040302030304110d0b15031e1006300c180b090f09031b070806280612020d1e0b160302 58
    0x40ea0341194002c0d114060341e401070000d840f0101c8200e582e01d612840b03402c40010000060000d0701c0c822883d41000000030300400d4181c42d483c13014100030703502949a0092900084101d0342c0d0020340c0a07081240312140300204501c20400740c0d00d0074581002500c03075100300c6080e500e021180c080c81800d401d0460520700e226400c08100e428603158102d245071070b40744404c0e4882d850321812001111071007444841d1142280881e000302542e103801341000c81500c8040d80036451807040b0140641d158040030601d01000d4085040c0300a1103529072501800204941d04148128a020111300707803640070070303441001410000c0361103807425a102d4044045030502283d00150a1308188201050741d030301c5040c80004810034100344c8000300c1d03e484005240c20401c903003614000c01291740329991101c002100e07a1490f04401010311015003082060f00512481c800003e0260b900501c0302c0303080c07048203406e011080c0501e05071b44811007120f0500405400b01a99a11100060401c039000240d02905c22502800001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 445695953 1250 445694703 445694737
    0x70b120a0903031506050a020c03010515010503191104090b040911060d0b12010213080a081c0b0405070309052401050409020616030207081506060d0b12160302031002 73
    0xa00640c1026200ea000200c06040d2500301c0c00c42031031201da0041d0b001e0034171555a140c440c03c1c8400e000340740074002c0005234040e0b4900024001d01a004440c000b596280c282400740d17803a115181c0c204508030020104800e05032030300c103001c0e81081c841030080c030485400fa88180050b91030a42008111680d9030001400c00700c2e06c11101d01c40b820110083d1514802a15000650784040c001251a50a503884186026580024004100050042c01001401e9040010300d0084465928000c0303501c81e11008424042440e07102d14102003854010000d503a00140c028001420f0000000c3c015100002003180c450048050145403041d4240135036980400304144400b1a03440d04042c080140304248059800620030004c2c0600058854240b150075031017a030080c0700407480c0100c0340c1d0400400341000c804581802080c008650341d044142c0d00d0018400030002103902c02c15000880031105c9095000c1c00d8081d610a4a12031040031080c20202e81c000c0d03003034a01c400ca049803031508038421240140b01900276 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 445697203 1250 445695953 445695961
    0x8070807020606120304180b0909070b0a050c0102130b09010f0201050c070213091703040b0105150a031d0709020a12090309030b150607110f04090213180803010b0408070b12 76
    0x704414003030b0004d0951042c0c91070076495214502000c404291801155a103c1c0080e0506017040e50240e544841c032100500002810a512603015116203985074040140c01f10f040c00041d2400e604803003480c80c03100303407060b04150344407840c201e039030444c3e110103010a5540c2d00c9170106500601440740728000003416039150101395403c009018503210301da240810f584101c204002640c4c040c1200340c1c8003003064915140e24140c82d20303c0410344140c000e20b003e804058690f1640c54030300743c2510307049001c6e4200407601c0300d0307a0240140103050b411001034007480707203282c0018445a15402011000301030ba4030705149071404034105064421213403000b0300040034400c2c1080410300eaa09881c1d0803000004584682d07600240001c1d0f00358000c0001558a0002440c04030308500c3d00c9842c085000340c059a045c041c00709181c0002d088071400ca19506040c5d500c5a11240806180c2d42d40d6240c0b10364860150340d140e5031600360b6019035800900542401d0b1040480100d40032000c202510302c100650400840c1641ea = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 445698453 1250 445697203 445697209
    0xa150f052d160c03051b2d150604020c0703060218010815190824060d1a060102121908010803040f14120118030210142409100608070807020606 63
    0x30106070160100070050141c0c51070409411008040d06d4800c00080048015026840d00711000b01541c40c070000d05001c602050070700f00880c0203400c0c00b80d082100351103030352030001180103031041c0701008025000c0c0320808010414940d0151802c40030107592203260809040064500203c143e80c06034417020000b0100c02c8078075200c415000100d101544031090306039a40c1401e854800c0d13032803042040f1043c003c800b9256082e401c215641c002411a40b031060750305280c48208002242e1200e40078418a2400090556402003198420a424095449076a520700800e030400e581e4090840c0c034005400b050000680520000503101683e81c900d01d28010b091400d02280d885864540101d90480809001c888440f802813003551264080b03060ba5098035459440d0003801c00e04481d9949842614044c90b0081420708a40e960354011089000392a813400e5041164520941c02e06816034070003251810403105001d070b0400f03103040320b4490719035110b82d0b113859609449904040b43d810006a010000240180c0b0b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 445699703 1250 445698453 445698467
    0x5100e060306041409060415060608061002240612010203280605130504111504030305160c120501060e040b0a09030c060c020705130e0a150f052d16 65
    0x2d002000003803001c0c4042c00300190400b08a6020342c99811120800c001d1014810f080714420b220f203401040f4940c03c00700d010380b0b041005050700340900b0900e003644480d24000c000b00f1011802c0d1341000010b000a0441c4482074410441e0300300c0c02a07a40070041c1e0030702d4005000b81ca014240020306141540b08a01041c0d29141c1c8000030f03900b0403901c45c80c0000b4a502d489a401824140391800440c10b450f05060150700c0c102c4000d070031401020144981d00a0f14101e03030070742f810340b549440c0c410359405402c0d800c204404540e000c00383c24468000d500140221814024002140c41038000b031254680c3c440503454035170f03c101d44c00b400300b0b0038220000e00e800a413a80310020140c030170700300310300c4c4004580c403140112032105a42c880503034040e20060026140c0115102c03003c140000c0103010003181d1583c02a218003404400801341c14400141c000c46840742d07001030680301100305040210303140c425541802001407014901150142c20049040c2000c81031241c0c3c450358105a0701c0e180c80f09010004c6a01c5 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 445700953 1250 445699703 445699711
    0x3030612030f1409091905060102071503020c07150504030201140720060c010c020d02150412030b060c01020c07090b0d32150601140304051c03090b0a090c05100e0603 73
    0x10740000c1001c00c0c0e0540c0c90074034041c0181c070410341b100d011011903016403084400241c13800b41558000c2c28208002c041d001c4c0c0e601d042030040e14025032583c100c500e9061030420150042c48405e10420300c0c4402e090303444000742048074001d9036491035000b90303401031540502c60158040c3c07038541860581103840802c00b401103c0c02e240034280c1403501e00300009450860305400140f20060304007010b44034003242c4c1040503000d0f1611101d0268041c0c24181c0d82e031204e4015040040b011b040e00c0b0081070b078075a500c10068400000c540d00081d542d03418495032136516017185000d4001e01c1490080c0500550134600041d40b5180c0d8095140e0044040140100d00c1d261f01e2921074003096080302a828403a040d080c000c0c2c06141c1e5400d003000d41141081400540f03002d03081141c4d40b003100c83c284100008118000f0b045003090a4580c981e01742084219801ca01801000b28003070702c1c900000701885103500c4140d0010440c180a441070550068580003045000001090710b41d0000d82c98031301d5084149481801140c00c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 445702203 1250 445700953 445700987
    0x13061b06090816060617030a02101a090103060c12180b150a0b071a0603031b070e041a070e0d0b191104180204030c0b1615060303030612030f 62
    0x6043e00d40d040c600d0101c4030107000302c503041d0321a0741c1049000807001c18540315149607005107081098641c802584d078246021404422230304e81c0d90003040200100d079901110440a042c10959603103900701800540030291544000820035035040144103003611440a0003200c501ca1004560382913245c440381500041c20354a07072456203002100c2280d607080100c00040c4408414642c6460f0701782003001c00f00712100070010404c1d442100700320041c0c0d40441100c42e200d280740c900c41c0d90b02da090396941d494404681c0014840013112070600c402c0c4005150030320400050008004aa81e86080c0100c5129002c0f031209600103500102000004c4d00c2ca601c1140c0c060343d2408060228003509643c070007601d07400b082c4e05016400015050004440003d526101200c3c030002c150714040c603503074071900c0a8130b003803040d20100300c4003144094000c1d0884025040090b0040e901c0c2480c039201001441c0103000c0340c030088001c2450310b180014550714a09012007260b8250b21031151040f00c0841c15100494641e6550031 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 445703453 1250 445702203 445702207
    0x20d031512050c0909010b03010506030705011e0c021c060e0a05120f1e03010303090f031109090a02131b031a0f03070e0702031305120a1b0806040813061b060908 71
    0x42c03c0d03169411031902c261103003c008660000354006040c21200080c0c0340c140640c1101d8424840f0340d0b00300003000956481c00000c0366040c000c12074120b03034144011500942c485d4040f051805003100143c100f03003005000c0c98003004102c201d0461182d407076040400c000d105802c90f10300341054a055001400001185080712440c11106c040d01c005140c07154103018080d05008001801810303400300346400a00103441c0c1c100c01c01030075500c4540d00406005803407481001110001441040103010f95081a603020380b483e0b1404d6100c101d000054002c03074907641441d00d003082e8180d00c039512902510000541600c1681d02611000045c498080b6091611582500c41e00500141c0180340c607080c07600c1180e036540034644078103262180c4a60002160300c10b46c4542c100380c41c4854030311404036400105650014125200300b00c842141e40c003007921a0f10035000c3c0d00410741000140030303248004041c456050344503610071343d441e038000303940c825001d030005a9481d07254000e8000041243c1d0054a0322401492118 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 445704703 1250 445703453 445703473
    0x20f030616111204080708070e01081002070206091306080d020a0803150607020901080c040501060302040803030f1f030503030f180a0308040302120a05270f010c0609140d020d03151205 81
    0x4001640542c5c00054103600002041200d494140014400f9001d092040c41c01c035403511103640c1da03405081d440003800c81c1d070020f998011540c3c0c480445078220310240c121404610741c3c0107244020300d03092054248902580d01d042074014400710b101541c6580c011a542e06680f15203160090b845e292400043d080a410401d0001594803044014001c082410007030440d22295414441540c034107a00690506005220a10421102105a82d4032110b01500b5100d16600c911b0303242103070071090410740c5244281200c040103102c0048025403040440300c1c00540a9106d900125100c1c0c1c0d80511200015000840c0f0000000d01c190031081d0000d006c0d00c112002c840103400d814444e40c0c8000780f60380101e10001a058803000032700403184218146150034810001c1401c0104454407a04103c0b80d0402034002c080c0130800c40103901420b6030030341090203041000358186945075180b500d013081102610441c4d2928174032602c40d005800c034040e0341c040c44d20410703031420038940340741031002c10125000d005843c0700c5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 445705953 1250 445704703 445704733
    0x110706050f07020f0309180907030c290301080a0f030e090703050114040905070504150803070f0212060c0a050703021e030904111312031b0b04020f03061611 69
    0x16401000c60792540301150521400103450140040e01400180d0400d00c030800d02941d4144039130051401d200b8032022251766140703002e070030241c075600010140103840c00c0105110003c04032244460b007201c507090400a00c0d581d10845240000d108031440c50b48548a40c2000445c0c08800050343c610905040f83c1c580d48140000d03060b0341c011a03821000a55a000420001902c0e10305c03812009030594040190322540e4490a80712001d6003d4240202d0b1280c01d06070040111041400013481e00c03000ba40e403a41224a4aa03106180740349060384900d00c01c0894600d6554003050290040814a8450340750110f00c0d0b00586140d0061305042d020350045c107140d20541e8480030710914095008501442c1e80700c00e40001c0004880b442c1c090012044001d204480103462500480c038196119840544464060391400302c0765200c0c00ba81c6000c802158a884804100e03203100d0740350065100b200c4940c0054500418590380790012500411018008030600da16580140b450b1520001d010302540c40000b6040f0301 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 445707203 1250 445705953 445705961
    0x905030c01030213030609150c0c11010f1206080303090f070807030f0f0812161812170c03190305061011030f2b0504030507060c0509040e0d02010b01090612110706 72
    0x16505030300c84044400c80700559124040b0303640e5480c10300c00c05010154440c000100368544bd00c6060105100c02d05001f107004a40003009460144001d2280a0325178034250f03140d40094034030824030301c940501a180300f6404035000c4162402017009140c142d00c1c640700c0034440c409100d000c0d5000d601c030300300d071201062040004101014100000d0707641420100c41101c400309a101a034020880140c1c40c90881400e0200382500715218260b04200c0c500c514140700000c048d0490000000c80400241c100d80d10b5800300c050310b048541442d00b00b840c5201103200790280e90781219160b507c481020a074054031030140120034412180c0400b10f07801e01d0b083c1c2034101c40f03d50080120f24901e80313089120103994410b0080d4440e42410000c410301280c10310fa0390240c85409203103c02400991114180c0b41d100380308500340c0c0c00e50b0300010010300c5400f0640c601e0390740780d00004541d80015420a103580f9240d5011300036400465050b5591026849044160380b0010f003504100340030600c00800154001c2042806 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 445708453 1250 445707203 445707221
    0x607080403031814130902041b0801030c05030d090603090c031704090e0703020604030f06021201060e09071d010302130f0308091017070528050d0b010905030c010302130306 76
    0x1910005040c01007000700d81500c180c0d11440c0020840c08114006440f003030201000d220f103170a80886d000e030b42880040d02802150703841ca4841c8000400d0a0707101503100149604803401140300b5a42680ca440505807603d440103a80c1000c86e07881c00b0b04000c1e040c46648074181a502802c0484110b40d20380c0d41c0e0184948030030b9011003a0401c080b50a1043c0d2413980f00d10a803c0b1101c0c00200007141c515400b04115010b05c0c4409021410007011180c103000c46501224442200148208229038503010041c003541951044640244403d10010b0503140c01a440c45015101c02810241444a040c0c01103000e03600c40300604010082c107000010b40e045607900d11b040030713500c644070041d00d81c00d0f0380040c4021200501d00c4034041024800400b120070040310000364000351031741740041d0384000c01c104400d0100601c0d48040c0a034600a410182c1065122000d09540080d8480a1041440a10046a00d00a103004041c2e241d00601a6024998040d60003070406511070118010115604d499400403242081 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 445709703 1250 445708453 445708457
    0x1202031c020726100c350901150b0a050706181a0c1e0c15070207080d050306100201140703020a030501060504060507020405040c260601150c030806060708040303 71
    0xb0003842641c14182d58200c03400e11003440c2540500400c800d0350350f1101035202160365142e96400504e011032144400790104441c222816940100c2922200e05842c1c010025071542900038011403440d8030180560300d0040100240005114204103500703074564003031040d480070b205e801c0000000090490003441201c940404104c132301d617406420410b8a5625400e194014410010100a00c2c50529400d0328410031603100c8461080364181c2896075181325903181e019481c41616603190040a1b411090f130f10900135070f0f080c2c83e0300c0d0f90350b03201255845107040c642602182040c80091504c0c10300492585a1005510000c11590300c1c0010030082104280c501da00002d0b00060601e10003030305402494010b141038a49070349010320b0705400418901a00c01e00074440c5844002003401d0202c890400c1002c0c0c031641d4401d05152649800c085400340c16480c0a2809014501c00090100940590320501d9411030f290388000c46601d5030125034035123000b0b0005a1080b403c2c024200450003900142001e10311076 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 445710953 1250 445709703 445709713
    0x703030314010b0a1704030507170a181401121d0d0f1d0f0111011508120403050c0904140a03091706011503180209040b0610030203040206041202031c02 67
    0x70070942100c00305801c040040a020464107030700320361185015000310250f038100c003910784880ca01120300d40705405019054200440c4140503200003000104050300e0103444410036036041da2402d0303c60086074840d640c6c58000051001c500c07035018092244003441e8000c0d000564078100305440c00c004100c1250840c0d10750003200d00c0c40c680d0b0b82000c0040301d034003624208071010b07444003012401c0242410030941d008074030002c040607960740502c40c0104242c3d0718200900c91042c01c1c500c20300700780035280300d000400e2084460395110084400c1c00c403000e03a600f050141c070103410030006001403038401400c00c4031a00c81403003518a10500c2403010103030040c840e90340c01da5103d24140440a4500c02441d9400d13958000d10f004020410307622001b040506020305020983c07044504d45042d801c2c84900019407c8030404042204100403010424401c0d0800c882003000100341007400c8041780400c070380c02904081c04201c103022600c546d0412000161004040b0b50401c08124202d0100a001117000005a805 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 445712203 1250 445710953 445710971
    0x50708041b03050a0f0311070801240f03080304081e0a2006041217040c05090f04082d13030506070c02031c02070b180102060f01030f020108150307030303 68
    0x1003144584000301800641c64508540780c460310340b00d00c0d1500a11012175a100300d000c250140500c80c01260b000000d50b2007482c1c1d911100c9010b030100f0b417441c03d0b038066011480d1410301d8200e00d058043d00e0070400340c071081030f0071a0750701d07003403944090800d440e1018103010250050384000307101d14100b4680300e501c9443d0081000017030401200c203114480c00780006e2031104800305002070006e60040d0826000c5c81c151000d04001d1703c101d11007141a404680c4001c00f00070900000c55801400c6070425a40015181e80d000340c41c1e0720240050314002d15582c1d0803c00c01400c21014105000900502091540d8005001c15490b90584c064941c40103034101c40c6000b0000d000302409100e601410608100c43c00d14242d03400652210040d4041c104000d00078050301d80428800c0000201030311940c940c1a42e03c9034841c404484a40600315802d005100391000229401d05142d5040e040325070020349410803010b10b134019030307503c070300100742d4800315800d442c0625566404114030300c029030290700c00282e6410 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 445713453 1250 445712203 445712213
    0x3020108010902090108060f01090911070b09030f040909021c0b04060608030c0d081329010524090f0603100e0906060918190c06020105090a150f0b030105070804 71
    0x300c16030285140c54410720142081d0703608a90384580c42075040f508416034012050040e985c040041c0c100680e82c601d4000315000a0385403c004001e400d001d41c4034060361703a548041c07140e84e030b1042d4002c0414619092000b08003810180c1c201c1000e040c4002c00300282801e40c0714101640740b074407850648000149406010910085114450140140e540954034150f403944460356240c1c01545040704004511000884980424904d07410403588000880c004210182031200703100c03449010031603100500d100004840c80c040054065101d1074507102e2000caa03034250100701c0e6070051007040b03400400606452841e03944401c02148102043c040001e501401c000c1c4811305d1200061900240380c1c40142407201940d95220f0440c0e00010f02c02421344c00000c01c401e11030400081c40d00c01000002900008410000c400340340006961441e8020405942c846490701d81d107129244010344080c1001c040c4014801c520f400036000003d041d607004c16841c070390380042421640700b00c2d20b40f00040c0c0100d0034402006 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 445714703 1250 445713453 445713467
    0x10140919020a0503060f011112090a0e040303022a060412050d090c0807090212060d0c0b07061a0d0215090105070c0f0302010e0a080312041a040c14060a02190c080703060204030201 79
    0xb81003071030508c446038609010aa6142010455109194030200e8801400d6444c0c40c0440083e186900d0300303030002c0c1005d15010700030350010204c030f04804c010b0300c0b2200104040c942c081c80080800c1801480980c0f290b40b1130743c0d81104c0002e0a6002c1010401c440303940b0340b64900a660f0003500c074109502e1040c1ca032404040c140443c0b501302da48541e004102d201600d48a0141c2290043c000b2128040306580d04c0c6841d0303400b0302c16a840f180180c54089451401e001c0c0c01d41c0554400d0120300f001d10080d4a041c1d0401c2664464030f94020b50040c2400c080c0d000c040817000c042c0584580c181005890000e1649544a81e4040c0342c0c0403411052020809100b107581c03240c20b030382401c482500daa140942c02e0038161034480c0034a802d04047d102c2003200103024000021019183d5405c442114034503400d15003002c0c5841e45541c000c1c0300300501e110303800c00c00c2d0342041702c01c898030880b82d035014008052402070000598142a0410740700d2a059020104078540244041d070000c42c413502c13006035070b01c0c903610026200f4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 445715953 1250 445714703 445714729
    0x501080102130306020f120f01030507170607031a1804140304061403070e0402040b030f060916360810061802030618070309050610140919020a050306 66
    0x10381d0040c0103410600c104152a282a01c1c0e100c8000340e11410440c04107202c038002d410541742d4400445052091a0190801c042e050740c1c020800d41c0c81c5a51540c80085015220b150342d02c00c554460000507036410322940c0700d940402050150940d0711108100081c00c0351500b4400605000109800d01080240080d0036960703400a01010710304281c54408050b0800b0208180701352448000800140c0c0684201c4c15902040070060003151030390703141e0403c403140e0740017116201509031040d40400c405192110b2030078410142c0e140b50070038000f0011001c0f58462141d42401c1c00303103445c1744000132080900c3c40a180e180006d6401a5103290b10b0145202d00e029600904510141d00e0400d003841080c0b0a00b5003545411011200540c2d280c4031040400d048028005883d0441e4000c1c1040c0420b01c1e0341900720b0382d0327000c0c040d40407250300e51600703140074000c0036440c03080d10108a844403000e02d09040103040940d000d80700d80c1d40320500400d440c09605c240c4e4000791072900000d0b8000100405490807035582060 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 445717203 1250 445715953 445715969
    0xe010207080705012016121101021204050d030507290709030201090e07020a0f03030b0a0e0c0a081306050403020d0908031224030708010c030b03030a050a030c1e0809010501 76
    0x110703a1610f40007800c0300c4400003010401841072102145411002c0040240c812108100382044079034840302244000b20011040f542d030340c1d03900d010741034a600c0003da0400700c0d03100591051805141c90700300441c4111944003103040c0402800400c02203480c110b010703540c0071003070403000da24441081d11507002140002c000b0001d1200002092000d40d034801c030800190740341c2002c2901d50f611030841c2a4500f80c0d01420042013084c00e00d000900309a0305402881840b44181c0350300c08115201c0c6c00e004000182102c2e1041c045206021842032039100d00c02554105005aa641c085041151204426900210350550250f80301d584510000303613000c803400b402040b0300c501850420a88080303004401801614a60400b004920301c1c110840c080360309504400700007021280340e60fa50381c140d640a001108852000f180c41c0810400c400d060100840f0401a8155280d625280f1040c0069008141c0c0800c274070708100b4040310720b14100f8001e40e0590384142c1d00d038481404914154644509484c016000046 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 445718453 1250 445717203 445717213
    0x50109120312111306020606010311090f0a050607080301050a050f0d02010818010906061703161b05060301030503030402030c040b03070513020f0f0309120a0e190806070e01020708 79
    0x900c0442a18655000741d152504036801095262000c000c0c00c100355803071003000700018031144039800d580051001c490240d02070b5901307075031060019000c40781e4000310585c04d84020400016180341420000703601040082000c000d0f503482d0750116034190401403003117035200d90000050000740750104a0600a0004036100004121600003040c205513051354000d062200000c0811111205c2040304000125118001c00803801c01d41403036400741ca03051080401d44003d05280d641c2c503010200031100c12600790140100d40c1119580e51032180502c110b40e9400300f5034121004503841d910b040045000714040d0300150340340d040c90700400d400c2c80000030083c0c1c0304030320f07081503066a900e0100c0e030903040b2401144c02c043d0305441003007504080d00c1840c13011046c3e204005035001030030800c800514028600b16080310078849076000050b950344a03100074100454407516400116140461052501900200406844a80d075040c02c91400d82c0540c0d4900c08201b0705054002c542d42e0410414005000440040c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 445719703 1250 445718453 445718459
    0xf0906050409020f06130e13030e030a0c17010b04110306040507081005010f030e03030103030908190b010510030902120601061b08030f0603071a0a170601120b0a090203040c0f050109 80
    0xd00c0c4c04c00c240ba0040d00a0324003143d0000c48604104100e0000e084d07a4040c07400340d240524905640107651102280030400109583c011800c00044129141d030f0f202d514440d016040c0f09040080f480861101220303507480f03c18590240d11640107444250343d130780304901d4513030801000f04015101c1c003e0a49040085480411030000e29030070161045900a08100304006203102c000c07000350101c070300d011000740b06c00030000003010790041906044614000c19141d490004140070804200401030240951000c1c8005010b0703850001c009020800160500040b4410250f000c41e0242003442440071650304004010041190840310030400010455113681d031400340ba0386d9200300d5020240820304580300d1100002da45803410803039100a02070780405112001c0c07440c000814168400b100c000000f5408c0c0069070303401480a281c00c1d011b03480c142c40780c0111100d21041b11009091104101da0b020401c8080000c50a00c42d10046001e0780c05424940311042c00d22516642c09043d6038481410000307455020 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 445720953 1250 445719703 445719709
    0x80304060b030d0905060d020d0908070b0f040f0303051003020d0605190608061306060f17010c090501231b0304150203130b0304051509030d150f03060e01060f0f090605040902 77
    0x704003614411174a147e29500c21007100c400a0140c0414900a01e182440300001d209901d0060030175648942c0da90095503441d000103562201c810346000301103449500880c0c0c006802500201d501c00d045c2c284c94041159a900010101e4284690544c1d41d0307503507030061003480701c81044103181c42201e50500b070018920b0100c8203070ba180d02c02018201a0803a140c80702c02089415000f141c0104800544646100e40701c0d06114400402014104299131070b10484151060080c1418021a03405844004c085015030384400c03407000c0da0800c1424010400c001c50101e001103030780c0400310408030300e008544031030a0510407216110000d80b51420741d40280300003034110306020610350644618041d031580308e44441c0f80c00c510300090b0344e10307003050010b000301008000327039000000d424400100241030040404a80020a0340c0d07001e806460072845024505001081e8260410491030800c40300028100d55030b5451030382ca2200d1900400082000414100440b00a41c0184030140c43d0480b400c1200b44000d40c00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 445722203 1250 445720953 445720967
    0x30403080609070c110a090204060f021b130209030a05030a0c050c120303160e1c0219030309060507080d05010608091209360a1e05041515030f080304060b030d 70
    0xc2404084d03170409080d640310b408171003000302008132095440d0780e2504005007055074241d881d20018801e012000c61010260b83e8100740b402d074050b012008010b0100c2e800c101941c0031030400d42d058410420b1171030001d07800f003000b08503c45555582e541400460314141d401c0417400d140310303441260042407507100b4000210440ba0003468425541c00003403062601038a01171621101564400c0540c0c118611000720700d030b140d04001c0e108440d100711549e001c0c460481c100300c0d140406400100070010034441c20303015400801100e8090420a03081840910b0790f9001d8030401d8110f01d0000f502081808100c510412045052248480700b80341000c4d40e0201043c4415143c840e0b121505061404540000020030f03800d5044903442c0c030300e0400ca032401d690a40d0181500e8806130035041e2a0800790b03807070380e6281c1c07044c2401186d00010030300011050b4481d5402408810b02211020412441c00200150000c081c580c19107100d068804e4a078500b500b440c404442202c1050b42c0250401c210360002c0c0390b80041 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 445723453 1250 445722203 445722227
    0xb0406140c0d08040c080303010e060901050d050a02060d020c100e0f0a1208070302040905090a232d0f0a0c05150a0f09090e0f01110403080414010c0b04030503040308060907 76
    0xe4a407495136510300f05191000c119034403180f11404000000704034001c95000d040d04c0351701c0580711594181d0380c51060141c0c103912071b00c001c0d00940000d4002001403609000506c0003c01d402c1015041ca0134030900c80e400c042c0080c0314040403d03992012124a80e4061020344001344140b8040c04040d140b41d00d0307030134141007030310304842c2003014417070010320418003d6040d100600f840d40c808010903c0e10400c100d0303440b1000c0a050382d040c608000d00208240100e00c180f407001c0024005003004000d000e42d1140d0140c28250303e00c5403100c03070b0a913440c4404810817010700600d410b0f400402c0401214189200044083c0d0482400b464410800007020010041281c0c7d20810303524200364404180e000842c2e000300d064010840140c28441207032581c800000300c102c12100100000c00c44210389200c541c00610071403000030900d90b014881003200c101d4145211840e007406051000303c5c200301c2da4507074428440c201c0d000c6012440102c14802851742c4115110741c0301c0000e407090642400c0c0001e000d052060812 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 445724703 1250 445723453 445723457
    0xb0d050618150621071205070e04050405010209061603030f020703051209150114011103040e180102040305030d020403061505060306130e0d05030f0906061008070302130b0406140c0d 80
    0x68001c2d02516100708844440a00d03011080b4110703a0030350f000d1000311050b1368040000d408840c100e803001d900d5216481c022181d41c0ca49039991114082408090700380100260b915550030702c1214095140d2000502240c01d140800044e0300400d49400b0f021140030240c6c1d20b4130103105000c0440004c2d00a400c83d10740c1c0310304d014a5411907607040c10380da1070031a002d03c20000c9210280000901e1640c80d12003030725141000d032104083c440e150124190360780a203103e8001074014420101d0056001c00803200003c0361075600140c60151280c940b9440d41c0e01c44400780d07220030790008040040c88828401c110030700313050380b000403040381c500350000303405000c083e00c00307846090004100590790380158445480203a00b0406d076103980040010107030090300120f0340101c10b940702c0000151007050201303d10341b0036400100340d427103a0280e01e0400c0303580c98030080140d01499401c101580700c007981d12160000904507006942e90301c44c02c1110090003075001c0d0740003508001c014000c100583d000804c0c60160320300c4074 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 445725953 1250 445724703 445724731
    0x6030d0f09140d05070312031107050a110312040806040201030608010e0d03020903070806010806101203020304270f06030c06030606080c070501020f310302031c03060504060b0d050618 81
    0x1001c00101180440302e001421440b171500b00008100c60303c8000241c21000ea20208107501500000f00d03074620504400600075004001400300141e03880802640d40407002d4111500700c1c02002c0041c005074419040018503500810400c01191780c18000c000150903036000034800150000c19003035944081a02c65018550013207048246900c08128070401000c00008850040d695148450f4a0b40c40030340e61060442807010f00414107492981c041c0c4455a07140c0e005514091425020354248507120341440039684141441040b43ca00d070740110380002821490010f0003a19514101082c8280b60b4009020305040000820040c2c1e00201844d07800761118402e01e5507000c4615100340203110b1450f060071050741c082100e80d44100c0e10300c0d8103416402203139900d0841d001d11000c800c140345003511000398554400c2108088070841c1001d02040070751141000b2944d9500c40b40003a050380d0413a00120003002001c100031490007518010742d0341007401544d5108090a41200d0000f0205005041c03d06144038 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 445727203 1250 445725953 445725989
    0x606042306120a03031406060406050a0e0303120412091509030204091a04031d01022e061715010b090d26070b0402030f1b0f060f04060806030d0f09 65
    0x240000310301d22016484241c8912100318503000c0c00800203030352003c1b4444944c6000139040d0600c84121801e458680c2c407940c3c1880142c880c21148403841c4034820303030903020900080840b03020f400d820074042c074407a074036036400140742540060047c2200d500080940522031000028250004014010750350151004031301c0f2001418552006c200340c010313a507802011001080700345079100040301c0e01d8172a035003801585400f820004a1740d41c00107032101002e00209201e2122000e4060641d1604003221650104030180e441b40076030f0501e803081e01590074a800c4000d107204a0b810140c20540905030b40c1943c1c1c0d0a0801e203030045a00220f1141c0001c05e510344d02c10507840c0050701c40481140c83e1078503070705503540d0b0900751920208020054608a01034441c0c00f10000d10a01c0120341440701042e01c0f00914580c203006002c00101c0201d460f441c54000004200081c1c074200d5180003040a00340c5620f8010307081c01e1102c24107140501c4e408000007009441c041c10100300b076101e54114126060a610f9140c0001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 445728453 1250 445727203 445727209
    0x30106120932070b0a180f2304060803090a0518070f0212030907062606040b0a090e06061915050a0e1c0302070605040f17151302030606042306 63
    0xa0001c40300c2c081031144950004405070302000500c200210f43da1649103081d443c58429905139168002c005041c1c26000b01403000b44c44008240d5801780a0a18032011418504d020800310303119500312003401e81000800c0c0e101c0b0300700404810001c007010790302183e80814907030700c2054221010300004200b02c03074130748200b0032203108012250991240e908540c0d520300340f41c03407075554811151041d0804241c1c3c00c24507423108503900560011031010600c03841007594800e41000014449161015405441e405012804840f00e115031036140302d10310000c05103801d10004114516203a055805a045070f603d005000202004101070407103065030400d141c443d8a800e000743c80c19200440100e0b0480300581c01c0d48001401c09008402d041d000c1d07025129016100c46003201c4601c528001c543e030404da0038400b0892040c061185441005400050754001400d00c01c14500302d000a449501c001051904506c0644c5810710007150048000c680411a0114440e001c4c08038a00c11040080302c0f000c20b03c0003031070a81b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 445729703 1250 445728453 445728533
    0x5060711031e06010e010b0301060e01181503050402040b1012050a060522051015110a080c0f0601060e0906041812051c0605060708160c0306020301061209 68
    0x4111555901100042c0c201c015528002441030108003202440001242e0101404481c1601e07a95550b02e42c04c07060303c1d0015901e650070031aa4610310491322000052a05241c0c441d15000709031542c000c28141818010001500c42e5420720741d2083c2d2500081c81401b58200c08210404503151001103003d40d90480d007040184560b51050340c01c2040c11140c084103400c1d200c2d061000d04606a0100855162208440c1888248e40103580014032801c000c10401070044d00c401b80e440c440d890455500036019520b16903141c101000c42c0180d80d201c0a05200400824819607014044901d00705086094000004140003406448140915903070803804020110302c910720105a608881d1103800200341603401007090340001c100d28004a583c2c140c071007089105004d41400c5600c010202820031f00765844100e225800701c07011a07030350b80d03041d400e900004d2a944080b04c0150b002d81001601d81d850020090000038007030700d940b82d20721300d842c42d00d1002402c0300c1000070041d4849c440303a40016001c010a00000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 445730953 1250 445729703 445729723
    0x5010e03070f05060f0c090411040b0703020f15190903110d080a0b061201090c0207081603030e01230309010e07090510061107060c021c030905190506071103 69
    0x18040041c00209102c0300c0c1e140000d22a110340c04454890352242c1025042043c1a40c144150302c1c0e003004420014903158101c408035400740e02c400c9251641e00c0a42c18101d501030b110031805a0000341d00c5070307030440f01480269068603d060b03091010b13107810800c4600300b00258140e8501160380e013007140c06141c403c2040c80424518a000c85402c0040c209000c0c3c00c1ca042141c40c400f038141840340150b218140b11043c1c5040312150088500c1d1a4200b10003800502046081a01184170704040040c6007607003003040c8001016425001030a850440c28000c1010003c8060b5074103000b81500c84d0402c80180c00281d007490f01d41100015200c0c3c82d44c035429800b4003640d0742d00401c0c130702c1081c2c0c0c04560704880d584101d0048001034880c035600da0f42c0c0e103404e450304402c428500c2c01d650041e0a040242500502c0414a0184003e280d82e1051b880c00340040090b0b601c1740416000998200d41c10f0081d800c20b101401007000400040c20030003858a00020b0f4144107038400244a01c3c0380c05941d125945040010500c4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 445732203 1250 445730953 445730981
    0x30c0c0602030a05190b010e1003110301060302130902030105030316060b040f0218030109030206070807020705060301150305180a08130305070b0d0c0905010e060a140a230301080c0d0501 82
    0xe2414240b241a010f130000b17550001c008000c0501d183c415030b031306210300c103001c101c10303110103010000f840c0403c100d4003895080b900c00d054aa03140400060480c100940c007901c6c0710303100140ca803030070020210140c0d507180c3c02410b01d0030320410040c04a6540003080e280302c1c00c208510784000d8101450400b01410b070640d03401382c210707041c0450710300048059000b90511a00e00005074030f004030190201400d0300c0f2050000340141c1c0007000405c082c02c0c4102403582d40310699004684050303984401190459101742e10070242204d1220800483c0d81d414060030ba00802801d500310900d03000c84640b00e40720080c011004140d031100048901000700e42c680d00c4001990002c065600d0380d07966503203d08043c1d03c00d925050320b1902d01403140810780d00402c8210103481d010394501ca105d001d820240321603036202008800a11030f010301b2003099180307200000c04d044215035460140e520594014500c6a80a6540030380031040d00344018440d0b5500011480c41c1080d080b10303003c031510010b0130a140103045003804209 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 445733453 1250 445732203 445732207
    0x1202220b04020d0605010e0405041703040c031e020301180c17190b0105010f05180f130525091802250c1404050702070504051008061e1f06030c0c0602 66
    0x81e2401141c0c0800205c80c1d0a0302e50950340700014041004503a81190010b00b41101ea11800302c00d0b01302c0001440d0300c40d104258600c0180e4480d1180b61411003110005259100240f00160441c2000e00450501034071840700c140e11b200c1e1541c1d80820500c05d078080d86200c0c0200d517071803070002030080110450b11824414000343c100d4440c01d2828031700744c0900549010400c17480c90800514414030031210310994101114907088041d0042200b90b030b00c0c180c003950f8003d0702e40c20182140145c1e0f1107050f000d90540c8618106c10558590788c060382d901000603040501204440c20400449075021002d0240003401005a85009050045002c0c00600600f51038001521a22004200d02d501c201d905880000740a515010804020070042d190129802c400603000711030100550300341074001e2604507807408544007071140c5071120980307030601c11944020340c0101050305072804000c1d130203180d422070214a42400e60000150855081031664420941010b81e2890400d11043c8a5042d4041d0300c3d5000d50155 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 445734703 1250 445733453 445733467
    0x201c020105131a070309050901060203070201030906061e030314070206034c150219020604080d1d0402090a030f080409020a080a0e010203071b08090909060901061202220b0402 77
    0x140603034101a004401240402202047d1490242c0545048494a5000b0741c60080148d004402428030404121241070312402c0105840401c11119034807110035044400c0340c5495410000c01507400c20040e8184088100301e201d0141e2101004c8980c40207014503081500080c071902c24070002540c82d9040321141c1c14040a0900d8218002d9481c1d00300d906401080310161039540602c9480d0580400c8000342c2e0000803183e8011a0320910303120090b0004200368201f5603210185420002004205030000b940d545811942c1000d2034501e401000098908504080740d140c04039404513080d00010b00b05110400c480c4040040d9030040301e018140407102592602d07440b20300502030304c0c41903c10300902810800e450800100510136a4412b20040c4d4540e0a188800007880a404400640a40303510108000031589034031100384082c001e0780f0450041c030341e41ca0804041400c40b4880c0e009108c1080805034035401603607d181c0358004104101740400c00c5e45070900d8421000b807000d02000c54010b400402e4103 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 445735953 1250 445734703 445734749
    0x13080a02091f1a0f0c060a0b01050906070b070309021504050a090501050d030507210e032a1009050406031119031104020a03020706140612010204180209011b201c02010513 75
    0xc1b0380208000142072203000c85c03c4005460502883e4101c03900581d0501046021074028076456800c82c01030700f800140e24900e9008034400701c140c041291400300c00050200298202241c80000400c44080104010b50400e00000c2844c2c000080280402c080810040b060160540a0305202e00c9880311540102656540c05888981d400710254440d00908808250a22094001c03052500c40c5040401c84802070004200003030b0707042103280041004c0220301080a803694402c0340d0203540505041c1c03041e100031208001c1480070320301c044d04010f190713507004100140e424200c1d221041e03812680583ca40d01c080344118000d016900c2c0c007401041c100320b1035043c40c1e45040c6070075015410075070304410b031441c0408100b400e0f442203204400b120081940050040c030415400b42840f56014034000703030b000e198440303507410b15059040d044d2140010500139125130300500d000444110000c3d1180400b49040d1039040c030555920110183c144407002800e00c0813100030710207420142541080400411078540c03c4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 445737203 1250 445735953 445735963
    0x417030405070e0115080105150d02030f100506040f06051b19050d0314131406010605190c050c0409020406050a031a010f030f1713080a02091f1a0f0c 66
    0xc110340f0140c07550001c42d041101000320a5504541d40f00c0035100e920309010700c44810713610304450804c0542400704040303660150004501510101070398038040e0801800d00d415032001c66001c3d80c40b9075000c00c0100f0071a0484040d40d400c03505035007001500e5074021445020564040f000310705c428082c4618a205000041401842ca54081c0040303903034503800e01c481501203074040f00041f00144003810000d4180c510202e1003c400314850740d00b600300c40c0740d02c100d21480d0040130f8202c079022a9020070300a10a80059030020401c098600c0d00302c84c1305030f20351292038960303400c45102401941c079600c0004c02d54841da0441c1005040141c40d5555582d5603040440c88201206000508082107000001d03420f02c0221b48401503a410690441c0ba000c89650b440c400304040d09105013800e40240404803225008649640041c46024040c0a034a5554410488422401456440000800500102d07800704022508080d00e10040014550403c4d01c40845907502640c28413241c1c2290014407038035030758004a0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 445738453 1250 445737203 445737209
    0x12031107080a08100503190219060c0b13240e0d030605040b1e09130203120a02061b031b09090a15090b090a1a0a03200102011802010305041703040507 66
    0x41d81103810744509480500c85442d521a0513456403082c8001f844c0140040c09440042d440240540410141105c00c84c0c0d00184660004000c41c001c80884000d00c80d44681003980441840303041c0000c06c000e80d544140705a43e07501099161405400b400c082850720b42c0c08040103120a034100c03a038049250800034082d01c40390040d01e0142d42059017900c080d04082401d11181c00c6c40e00001203001d480c4805100868000600201d503400114503014050b85040c000c2d030885519940031280d48120104000c1c0c40d0040c00f030544244100d80e81c64580d440c003e03040a90340c00c0781c0b030304002c0e0401955a5100c00e003540101442582e001035204280003015034a030780300c065021007030704041410540e111400d104541c3d81c2411140c11100078000074a14060b1507004042c0902c5145090a26071901030110701408025002207941e50001d240c000020b164440c0c002062a00c00d01c001e00c4408410002c0030940756407074400134181501c0f600490200040c41400451410340300540d6900c0b403419041003540d542e8148 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 445739703 1250 445738453 445738457
    0x101104050f0d150903090306050a0204052701060e060c010f020d0608160e1803030910050603010605010e21030d0906060b040b120405100c0804050114060102060412031107080a 77
    0x1d4112409414010007400000d40c00c081d1000388025580001c00160802600440c200018000f002c000a4000e10034207002d002005001603c0324181803d0100f85848002e040400c0812300114440c100030400352070b810359020349044112098a100454440e00800a070f14100354200a02c082c002c108903070182a80003a1108140041039a99501c03d0722640803d02980c0a410044c0062001d003200f555400d03008180e03800942d0005034002032186c00d58009039100c074800d0300549a4030004004c14061140c0202e401c40003081002d01d4580080d001c40c0049110601513104940c4446968041e0700700044695030035016640d451030002040344c020954088110750842c40c101e004210882e0210039038059510388000341f850491500302d010907072040104210303010b208003d204c01d55800203004001160781e19031500d4615080518005007540c518843e080602407034101080b01581c0c0c0064015002034008100210030094058120b01519007091211034000340080e5180c2000081c0006002c01c408030b03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 445740953 1250 445739703 445739719
    0x5010318052e0617191707020a12080307030509031305011d040504050303040b010801060506071b0807061d030f06060108090a0b0403091404050412110102130e010812161410110405 79
    0x101d02d80ca000e800d5030340c030140c80710b4104450380d100c6d06a001d004081150009144e6482075548800c0c11000c440a918200d0341424003109100019402d8016280c004040b00003a50401d110b1500c1c0340e041c6c0d912489a6410020070542d91124180e0884180fa40e111000e4802c0c0074910f01414010785c0d0b036000b601c045481c2c564140000951032011b10811381a581c0050444d8a403680d01d8495100388510100c2944072465a920300284440040010400612890303d03546401078080790f03200b88038460440fa442c000d030003041000800100100e40d0075800300090070891450380311a1003051415262004c001c107043d00520602043c10380064003103045581400d03040d013400b01d501c1d00344002d841c020344d0010505e515000d4107140c05405001000c40b84007140c4001130400c060003414814844040d03000d001c0d004509001402400c10074860b40845000c00590180350003002c265a07603100b034482001a06501c10b1310344466411205008072034a0300581e941c1404410a241114403407039000c0d00c10a0b20446030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 445742203 1250 445740953 445740973
    0x1915020a260f070509010c120201020c01060810150e010b0c03041805160e01090e280b040e031606020901050d0509010b03010606110601090c0c0203100605010318052e0617 75
    0x428001c60b5082d405c103a5580d21809103907502c03403031016030598400c2c00b955001d110168409100344250341c001c1400c00b0080502c004072420f010100e600000040071035540418051142c41c8298044030304680c0b0003401240e8401070000c2c25030a41c001c68020345112060540080403494081c0c00960183da600d43c6852109400380000f0303a00c09083c00f003000c0c0400c40d991b104000e1820000c00d15940702846020700c100b100003228038203850071201d090064409988807955190780c249803140e03400c1c100245000b949080c40e41a40b5018240c00544010800e0360009071003401070f40300741e0aa810207045010140000c1c104044124080c01c00400868000d620700400094050f108072501c2106000f60406410316908008a600241001c41c80c884140014000c00c580103031420003106488030154440020401e007044001070680d086c50380a0940e0b84804501d504c082000031420000c0384a0801821b0b10f010100e4103041d49049080074040c44203460581c00180741c9901548010040e002101500e0b06902 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 445743453 1250 445742203 445742207
    0x80c130f080a11100c1202010f0e0604151e0c050d050a09060b1c02041a06041815050f0904020a0905091b031612030c050d0509031915020a260f07 64
    0x2042c1d4513081e0015605450144c04079291400ca0f06c40d2622500c0042464000e0940d29401e41c0c0c40b6140c0414650b211400300014010010b44251410201010620200c40e070040d10b803242c0c140c254684000b072031756100001d1820b80580e00702d0f00c6d10005039106110301c2c038080d5200c0c002400c0c035a109072003507402d080152285150242c0d2458107444008030302c6031002c2035602844020603031100c440c407038891003000c0c1c1c50059540c038028000030040c02d0a4108004906210801aa00e200201011100d182d0009214a5851040000740b0f20401e031081800d03955580009404115594410391405262009001e41480e0100311840c44084150505c005000e20a0506684840f01c1201e00940c903030400060080c4400d0040c070b98142e40c0a07140c030040c042c005407141030600c02c1e03190b0400d01240000403018440c3c00c09001d5851500700c0c0b000d904240d80480d440b0b0900b007070000408040d240d035001074200d0b4a680030f80d1400c04040000d81c0e0000e0400380329600c40760303090b00554030380f102e0800750000100c03203038 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 445744703 1250 445743453 445743469
    0x60f1503010c09060e0303040e0103061e0c120509032818140904051c050d050f040b07032007050102030f010e1504050402060c100504031e080c130f080a11 68
    0x5142640d030b8540e058a440c2081780d800c2c80035132200b54076000070803001849072420500c0b41c0c06180182800255845030701c552002105801c0e80a0060700c2c10604a191129080311904100d040c8200c0c01007401e55691035960309500c1030300e131441a004900c02010000903021582da0f200e41e046900d8040d04002c0704030030314039001002d1046015914540c0619a001d0400c0c80c105500a4030032400c8501180464040714416158451a080029004101ca014442c01402101d030001c080c81b001e0481030501d6150390a1071000100007500b03264841240d6418a90703092824001c001220080326200d040c60324145010303510a0712001c0001610300300120340d540030340d40c0c840c0c0162440d0b00540e15030360118003480050305000300183c2e0f0022060200d002c0d801c806200038552442c4000000620f480c1c540b030050841d441c01020ba04000484038841444a500400314030380142441d0065a21103580c804e0000c149400768003da50118000b0100055112002858600c42d5108281d05481c40d00058140000c0c4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 445745953 1250 445744703 445744721
    0x60307080318060c0a0b0708162105070908070f0f090c02030d0b010e06031303030c0302130504050c0c010903021606020a0b0105010f0c0b100608101a0c0708060f150301 74
    0x10302d54498203001920f030450007800601c00402c262070144906840d00411194104c82400c04500c0640c1041690b500441c0c0410310038080d4101100707100310441c01c101c43c0c1c4060888000d0004e41d50804100c40d0740c003c4125000a020307800450795001c0e210f0301c4445201c2040e1148a1101c1030300d0101050222982c01000f41d802d1b0360340e00441c20f0610b0704c83c2e8600646000d01d00d042c10300142010360307a038584038800114400d00f40d8200714408010f032890010304881c900a1000308061052101d0070690007404e0030182240c0c000c40d4081601c1e20fa8015440c0703140300b000700580556107030240e40381c101030700461200000c4003032018181c515682c403003090380c60b001c150700000e000c0302c010790040c4015801070306c01d11010318180c43c20b045411402d0303507801c100800c1502d942c2c004014188003000031130f41c045c4000d54041000701c1d020310b17400e01d01040c045100310070403c00403201d400071444104006007003018100a01c9802d0441d00d03a4146006403803440d00c1c00b038400fa0440c40da40c4482d42920b0405009112034 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 445747203 1250 445745953 445745977
    0xb090d020a032607030c1d060414130c020601080613030c031b0606032604080303130201020f06041a0109050907050f010201180516170c101e080603070803 68
    0x101c869541e04590790314820310011080c0c142e5844010540d00007400311441601d050701e002034403c45c440406000340b040d07403e080314244103100718603405495000a6034119001204907810354030380a00024080d48030100484286450300031a5a0125400034029049030072103000c0e18205d0b1501721a003001c152100401602040310050002c00003803103003694400102c00041c08203201565552010180c5070141d105840510100e40368488440b90000130010b0b80ba80e48440b0341c90b1502d00610710703071280002049180c2030300f001c500c40000d5900a000c1c00b240048041d00360ba00f035244c140382c951a80d0744264488100500600300200d00a10a403040501650820000b000401d02d8070f010000052a07910300c0c181195211540785e14850783d001d00d91001140702c0c84c058003a9140f521003d001d81282c5906c140d104500810b1200c509a0011400f00c102e8003007600d05450007044039000b41c4913120700b00071000385500b00d80200c107031107603004240500405c0100c080d18055582c1d03a00c265502d000702c0c1c0580c00c2c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 445748453 1250 445747203 445747213
    0x8070c030e0a080319030c0c030c0209060414010b041401030504150903050f040b03060f0f090a09060b0603090c0102060f150f04090c0602030318011b0507050a02100c0b090d02 77
    0x200c1d0180c404503000c1d0500910800400d0707224030401e4115009094031031900724548074946021038060141c030150320024070b003030007880c1c02c02e841c000e0289a801d103019010310002da001c074510380c4a0f41c000511184034603940404959407690b5403c0c40303131301c031f48030305180e40c0c0ca41d007007400d0070b580f0900403240034a4206904030154440340d80c0110041049020403000d1040401074580c00074a2000a0001043d142060540300e1400c1d40c1400451184440560b1040070380075905401c41d034840521a401100d150360008040c5001c0c50684020003600007090341c1700401004106040e000060b2140c188071080e4251101c94640044801b80309005031011034104119005688160805030107010006a0040011800690584410400344843e030040c80045e00000304000480c80c2784490b902e0003c81d440b0080154049120720910750180300b20841041103c000742000900104100100380310b078004010000859800c6005008011000c0341100c14168800006003002c5d4040703104c94856480d500948 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 445749703 1250 445748453 445748477
    0x608070b0729012310020706090e010503060c0c070b160614061507110405010e0708010e070f05090f0405010e1b040b09040c020a0519060f05060a150504082b0807 71
    0x10400482c0c00075200d040f6406419144c441d950f510310384c0403400d03956030040d20641381420002400c19240f0703003182414605210042000351000201182c0c021502341030310780c440c40700f8072105041160591142c0d02001e4041908440c400c10140c80e8161103115031410006800c01018141c00c1c0302044500c56401140048a0002d44080c3d50040c518a4441d40c0403000c8080c003c5c1c00202210001e8101e83c010001074801c00c44482e0b04103003c14003410144413240303050301e010000241540c0050241300300304100403d03003010903240d0392100d14000000a00a00c00ba60b181c140021400d0412981c104411a85c0c01351054103140f40802c5905445445518514151058017070001404010307a0910031407280078074920100c1d40a0050540749a40d6450403080b1a000e420582c0542c0d910085528080c0e160105005051f03a81c42031100456044443c1400c2c03002161000b036415000b02d9100c070306117015160101c0b10141440300341c425481c10701002c101c000078001400b2100c20318101d86440c0820340c03660a0b0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 445750953 1250 445749703 445749719
    0x307061b030920060d09060504050c091306091109090c040b04021c0c140c0303010e0609220c0803120103170327010617030d0e16050d05010608070b072901 68
    0x98500080c00313000c851500724441d1598084070940344059601c140e4a000740420090180907800d01c50500311003101c1175050a01e884901201c030f41100926150355124450b0030450032244007140c0c1d04000f41741c40003616203449099128000180d10074400d511b0f000844050340380510958181c99100040525a100c0381c400b8a8014002c00500c0c10510000208943c42210146d000700030b44001038014540f25450218000103031140a042c16115181340000c000070103800d084901c406000d800e680c0f202c05040c2c0d0929103e105080c2e0051140b5001c009200001003642490007812039105076458181c41060b02a00c42d8140004d60307003072070310903030300100030300b080c11400490040c0d0110a00001011682c07003d403a0341c01c001e0400e114035540c2000c41d0414440340c1c40d20a4041c9041300e04064000455400d0f0f1510300c043c86030040c075104075110044e03036060200c00d40c0000007400100045400454031540c403034405e82c02030700c011030709000d4100c680541054401040b03080e545500c0d600d014240d080c42c0e0300b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 445752203 1250 445750953 445751003
    0x60617150604020f04030c03030807171909080d0605010917150a020c07090504030305100302030d030e150c0915040e040f050307051f0b03070506070b180307061b0309 73
    0x564029000c0c0521074101c04d8680041c00210710a405004c04180307180b0f80a0300c20440145040240240440d0648114981203081d5070b000920803554000740d4400d9210340010003800c20064215580030030100105100c591000c815110240c0741c03041130590b54542c40e40540d10b603181c5000caa0308500907101c1048001500c50381c200203c10409402c01c0c110040d150301d0031a05500c80000b0546540038842419050b104e066080103425000050803070558001c45d589801400c4204105a500c078110b060711300081c03000c2e14a01580e90000012818030001c1c502264000007401c9101e00c0341c92590340d685100c01e904607411035000c00c41003c1d050380c81b500d035003000a8945509803168001040803800090b820705c01005442c50b4030b03020001200c0044402000c41d51140482030207a0b205180c284003540e1920142c820741c56205012241c075590301c9000c0182041c40140102c864400854030500f081070b039405c203c0034406215000800110901803c27400c1c1d4000300400381c849441104000078403a20902 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 445753453 1250 445752203 445752211
    0x2030d1b06050a020301080127030e01121410051207030b06040b030708010e12070b0105090a0207060e0703030f050405010206241507022403070c0c081002120601050702010504180618020706061715 86
    0x10040031000750180dd04055690301d1a40050000a1604002c0f03800d421848680c00340030255051410800040c1e0002d0713945000b40000b03800d009100002a8090b03440350003c5202c4040034058503030103a9184142e81c040c001d40f648403407040c050b1801d54ac409416010596034500c0d00281c1c01d03076a607481c01051142401001d0513060f0349a408008420200d1183c0c080d1812194000004007062440c6060042040394941841c07010032000700410030040c0c0e03000407001e8210100e03030120b41000b0384051005c05015850090702d600104c00c403040d0707021604a803010f4008540203407005c18400c1c41030050b04a420903041241d0702040010305c04039840b144140110244280702d48040340c410380e2284c01441c81e203200001440c05494001070181d611044581115400c44000e080c50f5081000300e500180090083c1d0203240b07450b403890b21178180780c0d10789900148000c022604403a0007113400c115042c4003070b6002032400d5555a0502d000003800c1150011106442ca0900e009008610740700341e940036520f0f4000e0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 445754703 1250 445753453 445753457
    0x2061e090d031107050901180203190e0321010e01030f06150b040503011d0309150d0f0203060315070816020a050d030203010f06090302030d1b06050a020301080127030e01 75
    0x1014099540e260401e6400c8414041d4850750400554805210300d0308551750002c034040d051180041004101c841c00d000c40801c1301540c056140e9503507030140b0301c10200a07201648154188440e0003210744000c0010000c5405a00c000c03c010010460b0020000c06d080c80780c1400b100300040100701044840c40b2031590b45210714000b04222028040c68500c50703055402609113030b00005410045d6103824800c100c803071208180e030020808803440c04c45450f0300800c065980200e0188840240c030f0b240010441e4a06001e0350340400c01d40005d0000c1344000c1d00200d0300b69010703105480f106031100e450100d0140c0304030714640d00c944190b5225610352000c14620f60340281540701d1440c0650010740180003071507480701c2c191340060322507152440f4440c01e0171090b072204013804442070081c4056180450744a10407091410885070389401010080300c2c05005000180009140030b00384250306541d6001107040b626140300a01108481d200c080055a18851304040c1549c00480d50b400001c1c0606c0c0000c440e18014 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 445755953 1250 445754703 445754707
    0x30106030f1e0b030c0d0c0512070e0106050406030c0e09150301090803041a060d03090608041416090506060a050d051503060907030303052503110d181e02061e 70
    0x1c02c1920410a201040148050f1503818071180c5040800003600000000c880e0b05082000c140c072880413403807203402424020060700400d004100c400b08015001030400400301215507a540c50010030507041400b40c54000390415105030340035489281c1804209000400031200c503114007500c69016241c038207580e6015501e0b402c0039808540c094002d503208501034400a090b031129031200020011000745403d10442d44c034620100401e0740030034110160b0b0074906002800e80c640b410501074409030001c0000c0544030706004840c1e80101e080341c00b0304039643c0340070501150b141c140801080d80142d4403810700046007400700c178090030750a41080da0450350300e110510549000b00c0210f420620103c82c2040b6030361100400b0002c1550600c42e07654003504000c0c0c008a00300e05c600c03400f480c5c0c1c0c172034101403020140c445040000c81d00d1004d04580045440343c4003000f0701c0400750401c010f06c840d040002d982840c03c20b40032151820840c9006c01c03a880e40149240e280c402a00101e050071560f500421400441c2 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 445757203 1250 445755953 445755971
    0x3070804110402070308010905010803160803040303141602010e070b1606060806010b1905090f0907020c0a0f380c010b0604090906180c06030905160b03010f09060b030106030f 77
    0x34034401484414040c1c0e888604541c1000c420f001649d0781070780720709915030040190002900800c18201501036000000c0d40d038a4070346090440c05845d000100d00c14014568042c4200320b0f41c007407050a15581c058000f80300341082e11b00400d85995071403040d00e00c140c0c0704000c07101c0c2000740c0b207105d80c0f001c40c414000003868035105d807802840c020090300700280103400002e1484044440140710b0009a2607031908074a00a01400810710fa00900d00b002c60003141d03100b0216030001d009010002100c00c0150a41c41d5169a50a84225500d85271285454002c440b071074092150180c0100c80c22407a00c07005558840c44042180c0244503030081020040079540c8a01140d41c80d56100c0042004000d103000100320b541050030040110b401100c100515481c6911541d000602d00c8440d2a08030b88080c00d00144c501c5060600501300b1140300d0204c21020b01c6c030341c4007003010720031200958180d604680c0440720254440d0070f0001150050b00580300007440501c0100599846500300b0000089075040210710040 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 445758453 1250 445757203 445757209
    0x100c05030c010501030203100510030201080a090f0321140f0c040f0f050111032b0906090605150d0503071704090c020f0c041815021c1406010c03050307080411 70
    0x21050040103a5103c1004000707514080000d00101000300300100b245060210703400e010304045100c0241031140290000d000f14000fa07004c8818260051041c8021701001e28004141e598182c1728180083d01401c0400d03501c10740b9115001180b043c0e19940703121074481242c0c10700f00c0c0f0030003800002100000c00004c00c07100c01c0c02c03078000c008050b00c142d10b10030242040c1c00501f1004038044048855801032101100d8011103140b000040340c491100305a01c0140c0c44000030190a00401c050082030401851008201c040e0b072140e48140703108004400008555001c0081c3c140d0302950140c00ca60042c0880008035803200303549800c84c14070340354880c5020350307038451003081c0c403055a0307000c1c0035030070419800c0a008014011711407602e404890800c4500c0c0c1504030361010003401c02d4013a02c8504602d40d42c10745091180c0c12640744459222541d80b901114100040c0503100c00e9100fa0b59a07280340001c00c603113500070401c0b07580c1c00703a254031840d00f036654411044a1040c80100252400350080e10752150f107072 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 445759703 1250 445758453 445758457
    0xd03110c0304091d1e0105010608070f0e0f041401030b07050c0607080a1401091b02030307120f021b0601060f051801080402010909021b010e0d05040b0a03111206040c090e0105100c0503 81
    0x88044041c010117040484250341c210b9405a00c14020b024884042041240c0e001c80050034410140c1000710300c00c000c00b000320f5004c450840c0c100e60068a043d59100c800908424414100c0c0d00c2290303217000554030300104444901030740c15550000d6004002280703c05008004240d40704446880c002542901e0500102c0560b0080e84400c035159030f110004031130318240c50003503428242640000c61640c2454200100300410107011260035554400c40c007130929003c2e8045580c10144180302c60540440080c4e110b4940000303200f02070100d010254110740c04c501a9042e1240c2d032002c80c40301141c840b0903c0055075a01402042241040300c001000b2510490310303c0038200c074000028101007210100c00015003140da5006040c142d6a0162043c2520345034040110744c2a00c0d101440680c0312195407006902820030241c003044007090204a43d05540303010391480388940e000301c5041c011022040010745290106008400040b5032210048c0b120341003608140b02003c03164a40780740c0c08031150711381c18116 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 445760953 1250 445759703 445759723
    0x20d0503120a020c061509061504050406090c080a11030112061404050c100503010308040b09220c030f0209030721060e060105010906050415081806090d03110c0304091d 74
    0x2c03950201d03210401103420403241d5030000c5611440540d080c03004d400141711070030040c441403040c1c24002c0e0000c858401c1034140c40c020000908184406030b00c0d09100000341884034034510004059400060010700c1500824041b402c1c0f0030b02e250f141d41d08100240024078840342e420340e110f1b40c0301c0100c0c0c500140038000b000d1155001d0790252000000c6102005848040301564104000007400140701003000307401203070119031401300c110f07a0312910b01001c0340c3c0442d2207020301d941070350003400280c014a2454100b000480420350b41084540f010390201022401802d013183c0c1c2641c8840000d000c1008501400102400690044482158182e0740c20040d500c42c200920000e8003c100104201c0d6001840e1001800c03490030603e040601340300034800e00e0140e4201400c1013141150114090103044580310807058105005c0e16014a0941c5c421643d40400d0002c4100081c60215000340d00c49001d130a83d20214001d070040c618052404124038050901a030301d400e180d0020b15004540c90a08000c24041 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 445762203 1250 445760953 445760971
    0x204061d04050c030a0b0a05090f10051b07110114040b18030c01050a0c120e09010e0615040b2704050f04030f020a0b07050a09030b01090605030712050a020d050312 72
    0x16107002e24205040808070040c4902a40c0180c1c0f928000900301d0095680c03040d2404400502c6039503d858182c60191803444076140c80c0100003451141d0501600182c1c030030101c03240c00c62403541d8415540445442030391b4000d13098030190801024650b2145c00071113002e400c4810740c00e0900303407a4040340744650710001c141661010303c0c8040c0401800c062000081084007403d0040c100540c81031b0250100c48000c1c0010708000000b04103004050041d1707042d00c002e40d0058007240066844517100c010640f803c0e6100792042c80d001d07400c0000c68914101f110180c2d00011200307802d24000c0ca060401c0c10bd00c044001503a0300c1c0b008420180f1751514812680b00c0c02320040500b2043c106414085c200502d0010000210740114075020040380c035200e5142d81220f03513440d00c10781d10195440110341d2100a500300801f0005540000208440c2d942c002d0b030199102203082d00c801c1a079a0b281c0280444a2103401890b80d000141c0d8074016207046043c506001e80290b00307507461300c000089a006205412268011 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 445763453 1250 445762203 445762259
    0xb0309070f090203040803130f0b18192001050708210c040b0414010e0306070201060618150c080c03030906040c080105090c09181609110322020406 65
    0x8a0500c0d01e014540c02800500c00440c91030809490388102031000811941208102423400401c20880e141c3e80c0d51080d800903a560624101407000d95040311186100311101d1044040894a107524400c0503e00180e02800e0303e0b980d0748001151804041c0c0b41c10086050000c140308007000702d400312000300100f00c055041c01812841c03524200240c4c0d00c029000a600038003d10040c80305c1041c0b00115020b031030500300110040c0703501c40c0040382c003020400440d03a011b01412080c490340580540040c010b485032605e5141c0f200c1c0980030b203a000f4801c644035540d0702100c2c0ca111203c2242c048c072401d00c01c440c0034a020328540300d0000051440c662065501014580c800c00800c020b000f900c5c910740c000742040078000d004904144849681ea00d801401c1188605200700108000344800d0b0506001c2c145480180c078455840410016004905403261001c4e2500b00030400d40c08001c0b03107040301d01c202601003103c00c0e110090920001d08076003d201c100d03085984d88101040d40170000c016211541c582c0c40c0040c03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 445764703 1250 445763453 445763459
    0x10082d0f0907030c05130b12070f0b0a020316021f090f1401051801120606021e010204030209010e0703022a010f1a1e040e16050a0b070308040302070b030907 69
    0x4804030402816490550060720083c40040c024210120880e28121541790090b01e05464202c001c01e034a04000e41d009445809600d040e58000c2008011141584481c15001b540d4004640b958455161640e0068200b04108020340c034800840044090019103074105581c40d210700303505046044080380300400c0c40e20800f000594a641c203060007a022980c002d1100c194501c3c0042e20382e000700c0481c0d401041131307640c1c4500f1030317442110810440c1644140030b01860f5640c04000c0d4607110031000200c1c01ca50107011000d00840140201c3d01160f40c0680740c03401580c40e00c440000040005400c420401d6000c101c04d048049128901640030800c901001d0022145003140340c0c21140307a120388490413410306680144c1000360300201c5510590540d46400200c28030003109858045c1074800030703070180c5003034032410f4284400200404040c400780213070310703019481c0e03810801c0c01003852064a840c80030402c0302100180c446d0040503081846801110380c40d54440102e03041c1074100301c40704a41503000f15010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 445765953 1250 445764703 445764721
    0x1030f1112091029030c0a14031006060c0203190b24040c0914030615060703020313060917120301091a0a0602030a021005090705010315090f0906061410082d 69
    0x60030010004500a190131020a030201e0045019441408c68441c01440c412155440a0188521034a10080200081516404042e04112005d001a4007030b11a5078aa0400e030808001e103081d07125040241e001640c5c0d5050406d0401d60840b139034039070140018507000703411f0343c50702e028650034841c154031180000780c217002c1955103001c0180c50040c4240d1180e814401c40709241d0302c90410420060321800d030703980e000b801d09030f140d44903181340444804180980054160343c0200d240782590b4840d44c2c0050400034405605948a20351084001c090703900704010030540c076a17540074603c209050355594000c3c0b02c0681c0060b0303600a19601480250700001501d000340c0f40e0511084030114150013041086090000c20103a030b400140c00341074189603072140452407490070300e2829401006009000d004035003164009002900040b1000c803281d50400c0c1000c5814014010009081c8201a0103150340070480c04040b204041c0107440d04d075a0010f10203880381c01d00402d441e01700e20740c00c0c0784041e10724a081502e02 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 445767203 1250 445765953 445766021
    0x303040618020d0201030c020316050114090f0c010e0d02030d0305040b09070e041e15060302011205060303031f091a03060f090a0305280e01030f11120910 68
    0x25440940d040c0a501c0010382e034404005440540a10340069007110b4a02d090f8950310400b084181803c1464580904110b01500300d01b80b0100c5940c400d140a85400c02840e80e1032100003101a40b07504041d424010030f5220700302010b04080010000c0520307007035540200742001c6203035a4880000f03840d00e00704014807803602d0109800190480082000754a010a0340c05050f4010700011703d91110701d0080aa1040410142500302d41c02c081e4640c405454129244001c020300e00c070490119000d580395004048486c46040c0c49500d000d0080c5d0f02d160303600301d0980e8140c200038030305045a003d4968003007201c080c1841010040e0b601002c0f00256480c22108142c03425600400060307401400e20204003030b0b413a000c108d02d040c144e0305003446070f2180c0380c0050b440300d11080950b04050b0444200414803486600c0000350f80044020f0321b04106200102503003009903810020342c0c1c4040e0300100050703960f002c0850510360b800001c00f41070300c2010991540c52000e0754002040c00f590403080c64804041c50225186c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 445768453 1250 445767203 445767221
    0x40302130510210303110c0610080601080a081b12030901020403060b0f0d0305070302070806040c051008090c01050901030615050c0d171504090b04060c0e0102070f0524070503030406 80
    0x40d01d40c00e04038464814075034400309080000c0170107495070504171000740400103441c044400c100030340c0c0d890f10f05031450002c034440e01e03c50a41c60744118000011081340108407032010940080a0340c0c50103540400030006660f0001c1801c0040c440ea483c080c1076a0700c05d6000e5802052000000340e5580d1460404500b43c91282155038440c4010304405002c0b507a901810240c200d6250070500d07111411030a0513421f01d49654011a02400b4440421080100d070103805002d40300101d030109040501000101d0301e00104580d8043c155001000c500305660040001c0d06500c03070145408180a0740f5513500e42101c4422094040103d80301280700801c01206110780410b6801c2c900e81260064030103111900c0c10b40000e0f004050024024600e807489440303e800485200e50003144000507400c1518084006051154125000600784081c2c40380c83d620100300c9508940044004503280c509080401003c0d014030314a0b002150001d00b2150100107901e000760491724014805192a45840d080800c207a0340c100d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 445769703 1250 445768453 445768469
    0x2060f150a090f0b04270305122a0c0c010513090f0912051c090f0b07020a1412030408030702010e070909021527010e1507111f0e0402040302130510 65
    0x5030301b8200054029501c0d51802c02014000101021508003550580300d00701000400d01a0360041000e4140403a44610741064400540c07465280c0e081141413160151044102d141d8100d070f8050030143d8072840c0905000c6130440d5040400308d03940c0441c8401c41d5a80c0881109107900e83c00b0601c2409070380c0048007019446414850b1500d01080601d154040d0b038000c52080c029a2010000c05121802500f503d001e540034201000c18100300b07801a43d01e4034884070480d1300340440103c0100759080894120850100b400c00f035801c503111956070300403c0d0001042c1404540d03079130001d48400c41c800c008000042c000c00400081c10040c0e401881101590011f0801100c14100600e03142162100c102078a4403c0741601c0007401c07811000101c6884032000c7c0c10315400304600d114840541000e400928005104080004510b0510b106000c0d11000c101424000340d1081948512071034080c0c26000b58600004000503c2c1540300d40c001013030074000700c0c1e084c494181d4940401c9407000c880e4001d10090041c4c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 445770953 1250 445769703 445769711
    0x804150207030210020a02030f030702060f01080c03031602132a0e0105040302190312030608060f0c09010c1a0408030703050a060503100207060204030204020c010e100b0102060f150a090f0b04 84
    0x10b610082c1d40e0308096850000426400190540c2951081c000d484c0d1034183c4401c4941d89040012000399280c1c0300342d4500e486151844000103402e0400120006400c3c0058041c50905e000038041200980b88c0600682c0c000441e0000341d5000302c464420b001d24015a0344140350111030340c070500c0100c2031041841030284800c0c107403010204d80e0002d040d1070480354101c070042c600d07141002c4621001009a44000c00c075031501101502c4c00b5400d600941c05684158003150003c0c1c0d955008084c244601761800d2030781c1002040b00c0d0a00e94400d40b03084202c01c4c011040004007006c1107070b42508005080f281511620b4000c03003400b10840c0c1c18080c0c19000804828207102442c10100003940b900e0a95003406901d0f640001e5503410420283c041c0c8000b1a0024408c64442c1c01021102d4082c0000f0301c0ca100c158007549a00c112000e0380ba20070318010800680c010a0740d80e43c0c030400511024009440c3c1d05c02002c06400901081d03442e4150074028000c102004980312005103404400e82d940084298421420 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 445772203 1250 445770953 445770967
    0xa1517130f052406120c0607020415030b070804020909060f0106051b01060f030605010f1409071b15060b0a2f0a0807112d011b0308041502 61
    0x100040c0c16100ea50019030501500a00307240051500050032900074001a044001c0a058010828290302ca07860903a0022881070849564a4951803003128051b4005028040c0300050308082c4e000c4400c85003000300d0066066100d44585035000411590741d800a82418100300850030801c40c400d410100d51402060a801c24400b00002d42c40c05014400410002140380d100d03110525240d407841c240d140008212007501d990840e0806c13102401f083d110941064000503800c0b0910615000701d0f10a04000b0001c1c0721000c0c1040200b840c0540882c0400410350142030b0b11480c8001540055880b4030038100d00040d8000d1030600341d5403554801101076400748100d01da02d5070002d500ae000b160004d403041d056021000c41a450814a1b079030036008500c141c2000c441009500002131000e5801000740140b0100000100840b1081e41c418103003250500c0c0f00380c0c0c0404011a4842d10200005040501da22858940d804034060080791056000846a00034001804034409034000c1c5006803031019031410300 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 445773453 1250 445772203 445772221
    0x40807030309270b0301180311121611040f1a040e0106060e01030914060906100b040f140f120115090c051608040503030d020307020d09031e110a1517 66
    0x620b0f141c075140f2441e00d030800d20b0601d079000c3d4050506441e01042e94611002107080081915007110a01d030410f100c0c0c4210904001148010340c2e081c41b103400c1e5104102e4405039503c4080035003810040760050f8035554007081e020014050794240c1c4486000d280e01c00e03141e18040200f030325014032840819914100381804040c3d406814440c000d8004e080c08038481c041c030b203009941c40ea02079195111074069002400303200d540218695014280240c84061125103070340c01308005201d107100c3c00800711040842004000c0140b804c02c400341d807005000581003030390725001c1000c1c1d10000d5016109039545003002e038407520400080d90702a01d0080802c012138551200090a10300c1280007821403150121128810001034100f190003401c0090103590702c0b560b113018108080d4006407a400098002d01d81780318840b91081c82101c0841e030300f2800c10b0f451081403205000c2c3c02320141c0415100d0ac101014100303110f880b044d8045004200c804103e640c10410f104004110004212011240781480428800707104 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 445774703 1250 445773453 445773509
    0x10b010807120218030a03030b01111b0909190507081006030206090409170c06161110020a1214090d05030115211505010917031b12040807030309 64
    0x21000380c0b0059803880d0700c802038646101d03d00f0106174144680d0621604142e410b80006004007003e0701e0310a54514900d007203070b882d103449003031040c15140d098030340c0c0b0308502d8881212504010b441c0d0030360fa2442c010404c0003440c40301e010826034069000384010403000004005960b110b442e904000c00005056a001038694812146a284110303140c01c200c0c2c00f800070405202c03a04500c4401059903980b4191403003500c0f02001c8034401590303980000b043e00c80900595400c110342c440d050180c10304903500d0060350025040902c00b40200b00034454414a00946803280c2c00d088400602100810f03c1c2c030045032443c04105c00b800400f0408144010010080300c402c000682c0319941c180649006605414503465499990106950b01d050030554041041c01da03000b403041c2ca40a98501d0f0303125031641121024032040c070a462400e9802001060246060f815400c0040754501058130070740342d10206801d20f1074019821815854011483c1001010303000110b2600402c1e031040e20148110403501c03416595 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 445775953 1250 445774703 445774727
    0x30d0e0112020f0f07030e09010e1501030605032518060e01050a0b0a080601120f0213061107030b060d06060e090d09061d0d06020315130203090c010f030e01050106030c02010b010807 80
    0x44004074003170301054062502280c04000290000c1c0c070704e40e0b68200310300c3c2a0301c00750f61224550300c040c0f003c1441035110340110400d41d0703130140041400a0307049021008028403001090b00800b40b840c004182000320b400e01c07419104c0665008070340c483c20080c98044d0602c041c1c0c13005116260809003080300d48010802c0c2c600000032400e25400b60307550b1100503507442c84d000d40360340303501803402c1c040d08045c40096002d800780380c0410030100e8865071101e00c2580d840c3c146a03154441584801030400000700d650002c02d61124014040039181c24950703a5078410b0750703815004088136103840010080000410400d140c0d00907618034000344a40d28104026180c680ca00114402100d800781c0024800e4a52080100d481640b24508540d40e140c144070308540b028803001900d10070408001c9401c60040c09000340e03400b44461101400741d0703000c00f030b005407400e0691001c11030901d070329405070f10b42c0d94a0a1040c0383c001e021a80340403840d0218800c009013116810343d0054103200e0381000307015969500110904038 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 445777203 1250 445775953 445775977
    0x405060f1306080105010f18060b03010b16020d050601081912050306040209030a030816050315061c0501030c06080105060304110909030708070813050d0f030c030e030d0e0112020f 79
    0x4441c0314441070700601120b410240d082d60800300001240f45282e42d40e00101c60b11300c03074511180003140c0c01c3c0d00192207491003608000c850910052092141d00700041a20f0076a40100001800301907020448048103140d0580d99500318600404c0b144200703010070000a9840c40301c5641e0f04000d0b80d01c2090b45000300c0085401c001012000030625196581250190b500c0101240d80c40c1e201464001e207500e00464078000d5603850010090700035809401502d00031100001501101040394090210030f030411840340d01560f40b54290008205028855240a03502940c3d41c002c806003080800381c1380c01410780c021806110304000700300c007003101216180785500c1c040fa0031081c1c90b1a15490a171850044e100050301c14440005c81404201a01c001480212004940240ba00e50f0342c00c1085651200c40c03002038920030094040c900040e11801e840c92202c0d2281c00c02d41000421078010034501101d01e441403020612103060440c8a681203c0d08540f8074118075019441c2c100301194160b60f0340501909004 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 445778453 1250 445777203 445777219
    0x10e15041107050f010605010302130306050402180108030301092910020c030d050c07050301020403050a03051e04150e030304060929030c04210b01031103210a0801050405060f 77
    0x22564898000c0c1407114841030400e5124201c9051032910303074614080e114429880d0202c001012350207402540c4003892124035a0203c40d283d5240d41303011f410300500c05c031f84c402ea20b501100300b100104802c990103011002e005607107a6051285c90400c81e0190b0a021120001c0403c02d110210701c1441402205c0d0b03001d442c1c1001c4503081d204107901d4046103401c0f095060062030860300d5043d5104000e40b803405007040480308141d45d42d83c01d0600302e00c22400003518680100a554000c2800744005041c100410140d003840541c070718441c03070007036009030f00481222045021070221943d4014180a02e602049003d58502440c0040c003514500d86445940102e0b0550182c152600042802420039900c04483c81d0f82d50345410708158100c0d5005025100707025030091b14210641c540d4400610a507548141b5610705642181c07140700c110315039504815458882d0b201900c05040300d902c40c020030003006203040c41c3c40c0c54000c4000743c201d6505802850041d480c1104102c0071f542d0300c9404404606051381d02c44 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 445779703 1250 445778453 445778491
    0xc0b070302100c0f03060f0312050a0207051003020703030b0a0b09011d0a0e01030209010605070302030a0822121b0206070204020306030a05010509242401030612061d06010e 76
    0x1e410700080c0a90188250b1400c0d85410030f40d504075404254101070f59408209880e2900550f140c4240507000c080c0992020320004140c85004400812030342080c0e0040b602890782d82c400013907000c1140b0584000094001c2201003c264141c06040240c0804854541c800b86c100040300c1100e004140301203040002c5000034001c403c40c074640f540d000c800d024040020703842d1a600d61101e242420b2008900030781414000085991241d0180d5901a515501552520728400310480340000c0113040d0400b00c13080e030300c018a0400c4000c1c4000704c0581c45000601300740b241c1d05002400e070364030b2521074420134280c403c080401a1f80e400c0c101c4d054503504540040c1c603500c60001091802e249004010300c02d6290109210783e8542c0064a00d2542c0c41404412010001389140d500b4102016100389082551900105580184940c0002c02082062500103240c03a42d8450005d4198461041902c0050740c940021000340d02d0401d40c611412510703802403409502d0803001d4a03c440d4000c00006034010812001 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 445780953 1250 445779703 445779707
    0x90f0913080705060103112e0905030a121d01081b090306010e041104020a021b1f0924050a030b060d0603110901170a060504141e0709090c0b0703 64
    0x1403995030810140c80e161041480c3c6156140420300058404610180c141da219181c490145800452075a1440040030a1140d2184550413401c4400c01440a08480428075407420480c5104d000c0c001c100794018900c91031005003048090841d1110900071072448c0d06007590300200180c2d040000c20400e0740702035103440000c0c1194060703031f0b0703400790f01d800703400000207074294002038590127140100300b510405030526040100b01d2148101c03840250f0404c40a01015104c2a404048142009081d08911400c01c9000820545056a6200c08207103002c1003805120201c004c0030880f809042441c17000c105082c90045d00c1402881400d00c205030312466501c189440741410b481d076074000d03903000b400807030346a01d858541645095041c07401048220000540000103032060b501a40e81c0350041d20001031113840f000060400100141d440d030340805da601c072800e0313802c00800340203030f00e81940ca0041d81da91130402d50400c44607030b000154403800d151072030022480d444a604102c3d00300750a03259071070300c00e840c007 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 445782203 1250 445780953 445780981
    0x1e03050102070b090105010b130b1e04170705030d080c070f15021c0c080a18050715020709020405010206060d141b0f01030212040318210b0c090f09 65
    0x10081003540080b6401e01005500d110072070280640340000c0c4480d0380c84004000280c06240042c031000070750380780204010a00c500090000300e042844c035402200b80c4e00b081c14104d030b10607407012440c110b0700c405108c10340e0b005000c100b014140031009001d2699001d40c008090b404041c102900051002071860308002d503504030351185540c090004044102c4000c6564002d402c01452005200000c020038005801c6900c507074442048036496880d46038903820304400c024414040e1038503104000906180205900b08016002070000c40181d03242d030440454003d0521200e54040401c1030f0040c4820b02640c0e07000b14800343d200a0540303807440c03800014280340d0f48203d401000d2888074011145a4609802d142c02c1a4000800907102c0550717280409004600b240316a18200c0085101000420000303440f5640c000894100140ba400e00a51a038402c0030f5003829140c100c45201084080d00006c02804060b020352198200c000c490030000d117680440c0c00a014515824414040d08000540c0c00900c198 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 445783453 1250 445782203 445782209
    0x60908031e0f12191404020f121606020303061c030c120909060b0405032808130314010c02190b040206030c04030b070804120c03020a02040c02030d02130305070510091404180b0a0c05131e 82
    0x64ad6401007641c2d02400303526580140c4489000c0c01c11104250251a4680d40030341e6095410b90302c002d8005c100e40c88a40c2c0038218810710004005200c4000038071000305000344009003262000203aa950f14100406103022800c40a200c082c05600700c403002d00d425020000700c5902d810490752940d42c0865000400e1000243d0001404400029450a10f81d01d0551090340005050b03000c0f074a510748590002c006101a01e440201310301c2c50b010004d0011300380100a187c2001b0400c0c0d9160800703440e607440540e028401c607189000101240108401c0c48002c54441003030485c181000301038803c498a000b5192102c190000e0700a580700d00068440e98400c108845407070858000454a45c0b4250903081c5011020380301c1582c2901c581302020a81d4070303144400501d40035545c0ca60750601ca00e410300e080100c40040071401e46c441d903140401c040c109800780340341222a02c0f442014640d80f400558503400c894141513500e04004040c40101650605440308034155400b5280c4d031055814040d80c9010311604070b030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 445784703 1250 445783453 445783483
    0x9010909080a390c05012c03030918070912020a0b030402030f16030212030309070315020705030301060917370c060801060908031e0f12191404020f12 66
    0x2880c20b03001c6030070200c2c0303903001882240004c0c035150340c480c01100d1400034486400403070304582c1c0007011641110090009014800740550741041852800510300503180c640c0380322003544000801c001147c1c00880280600b40e07280b5035110812036a000314008610341e0080c0000001300001150541d0790030030400c5002e00c0c0c1c403002ca8410b40c440010781003114500f03200803030145c0100c41001350901408006e992043c01c800c401001d03410303d980c440b2849084024800e48525500708440c4000c02ca0502c001c40c00307018240c40c2c0041807881c20900303110402d008040d0700b2140e0440304454802c24050201003108400c4040b0750300da03124072400c916204440400000f0300141581c200003075202c1d00700801604941d0192207072800aa0740d800d80da5224070500850841d0324404811484120314040f001c0c1202c40d4580660500f01f400344c80c112001c0ca0000d441c100d66a5841a40a03154110b10b40510750100c28400141e010034240380d40441c003403055003114584111002d0340500f150134420050000180303409 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 445785953 1250 445784703 445784777
    0x60103020f1f020318090f040224040e010f0b1e090a05090f1008060f0a1e02070302010b0a120305040e07050f0307080709150c0605090313031109010909080a 69
    0x240c4000fa50365401482041d4418040700b81054840c0b0b0b01c150744e01c1c85a035084904482541e1950700700849000050030350702807807001c00104550701e080d800240005d040c001401282c1541040c0101c00300c00718a41c0000c00e04c50041107504005014550040c2402c8548015551102c0d5000f0005100c05017035000250001c803504100640241100041409540c00c0c41a8205840e1960b61458451004445c140c1b4284001000b041c1902107560221100c0d81c00c000c65078144003100c08040003a64480182a40180e447d000086841d140c500c0d07504005010642c0f05600c0780c881950040c0884c0518811034181d01a07450014801d41d000745e080300e0b100d03c400c0c4034403035480c03408400c094010b0b1001d80310034001881e04980401d07070042c0900401e0102c182c3d616a013140c0541950740301e014100c018100810340c042403125405140c5500348402c0514404c540e9180a0300541040c0b00306018140c2c4201c003110704048814010a0301641251100c804625082c0c1035080c80c0d01908081403500e0102d41c84881035 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 445787203 1250 445785953 445786009
    0xd080703060b0f030130080903010b040501060806280902070c03050706080a0b0d030c06090f1b080c040615050d060e04060912030905030301140307030b0720010608060103020f 77
    0x3c60340114161601c4450b200030f141180346408100015070144803407143e04100400000c14025070150442003401000800c00c030b5044004941907d0382079005c03101044210060200a141c00b88203205904114030705415005040080d029948043d480b90114031580011440c09000989840300061500035040345d040303680d910b4000702225000c03101e04040e5803800c20113030380303524144440e42161342c1c01d651240e9144426460328402011118821190308020000980000d101c074100d80712442401c0441c00c07403c4e85400341481c1404550808144180e1400b1809d000050003214880d0110b2006d00d491030321030f80550384410007010550050761350030151a08000030880103410141409105840c203c5101d982948103905036843e4000041c4035400902c014050071100035240d000f0190000e080b02c0a0716502d448481c50000c040ea00744000802c0e11052081c4200d040354000b440007562402000800e00c1c3c2000ca58036040103000091285062003007802c600d550301c00d5903000d101c0c480b100260b02544 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 445788453 1250 445787203 445787227
    0x60b0d1211070b190f170601030f09020301050a0f06050406050303040306090312020f0711030c0d060507090b030c0a0305090312040809010507080a090303260604050c070b010303030902090a0c020d080703060b 91
    0x491011401c000b929010303540711a141b1600708042a940101c64404080e15010015000f82c03800300080c04140c0e41c0d500040000d43c2c3c00b40a19401154821000648406400d00e42c03019501075800c050b000b035040c000c0800442e01e00008840450b9044000018821442c1c40c1c221410b8108440c100d034800e000ac141150102c03598001094a1881405110300f00361441c4189130700e80c6880300520341d00813040c859072400308445411407507000d0240d151480b080c0b0b459840c512507079003055400c052158408610000c0c0c480d05481041e41042d0000f00450510603083c106080e4060000c000400000c0c011441103c036900071000e0b070b0040342d407203000740d92500e1108100a240740c840784010380c00903a9440c4070a449490b4000101c0c03805110340340103130031a41c0d00403e02015090203401c00d01f01a100b04a070071f01040b12403c205018504c2950080384405403401001188200605511071a0303150420b4848410b0300028401401a1642003031000341d43c0c0c10300290003c05250344851418600050240300c400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 445789703 1250 445788453 445788487
    0x171204080405130b0d0615050312090307090509030a120b090a050906010b03130b100504050f0f1b030402040911150c1b06030c03040809030712060b0d1211070b 70
    0x2d4420340d9003480040c41010100292104044042d802c66903480303500340441d00c550040845161181018844141d0b6640402d01e070014885044141d40f1001c6000303032684c50180040ca0062440344418000f0f07007060210342d0748a00c100f070341030405d0140145842d1a040219007044c640c4c0e0038024031258092408110072000340c50210b41148050240c000003080705400c0348140c074096400080034031010b02450762107010401c1c01800444a166402d5400900e6943c0c50003200e1203444118810810303400c1c28403503d224110040e10460340080500007000d05101070302e085c4d070f034010f07012100401c001400c2d04181d40f108120000c02c64110200205a40824030804000c052003d014011102c00c203001420141c8000b451044881d4804801c00109141c0c020610103590400e0003587c0da02e1400c0c0c29000080c2c075100b140d610070a80b0b400888001401c2c00000d02c9881415038082c2e440e018594400d44d80d10b0140041790a140c000d02000c60080e40700d40e101001144040d01012860703a41c1e800583c00b94003110 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 445790953 1250 445789703 445789709
    0x23010603061b020d02010e07090e0111190f02150a0f0209040f020c1b180912070606030c05060c06040210110604050a0203060924060d060213050f0f0109031712040804 73
    0x2d0302c200031640c04c1c4103205100300c1c1002c2c5000e801801030541412180c0740038001280302000c0640d02e80c24810804420f14004060b44255a00c105000410b045005881d01ea900f00b041020f542041c1307400c800e500c0304101c1d85a0300042989000480e2454044218000c1c06641d0410340c210f441c00040c29450205907004000195030303030046901c2104d05030480380c0402c0b20b0044894000300d00d40c09146150031114026504491107100340c0d241c4c0c42201c08000850b4009203420780301c0c6600e0303070380400920154004403030103440c003035807081d2402d44400300b85a520350020f04021301400d62516040b450728030503050074080d0340c1403400f0b407540c500b000c1c208141e4a10303030003500740d101c0e0140074046003814400060329443c1d150f0b4480b0100c200c5900c0f56215041c09c000400403500042040f11010000e11a4401050030544206c0d02040480c142400c0c400081401503401c0d02031901e1009011842c2c0e00b050b9950100c0ea2301114640d00c484e0b580741c000040340603000078241d103100714406000822413220040c0042d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 445792203 1250 445790953 445790957
    0x6021804050c0903150601031d030a080106050304021f0e0a1806060809071e05130e06070905130b060d1104180501060c0b0402123723010603061b 64
    0x92074070b982c0040390320b520549462640c075520042ca80f030f0004c1200222503610250506000a030401110881d8851420000c2801a540c0000404081090300602c0a42c007400d580d14005045180c10707800304505002704100d010800d0303e2201084800391050180d01251400036041e04c80701070f139850742c0300d0070340c40c080c1c00400d040703424a8000b01e41d0a11584500d44510300450003481e440d03142c039001d88440d039600201c1c2c0000c0440e16501088a458594440e03485000d90300f40000e800d03011840740e60424030098080010440540410022076665190101031007001400010390301c82010002840380c41441d25044a0a0410710441d60391404000940211b50400034207405c0800c950300d02504481c42401041b0120b45d40c9030b210008580c018032507650042c07010344401d28945040c20744030320b04004401c080103c80031039107500042d0410390300c5092003001e82c1c4c0d01640861500da075a190041c40e0074240101c0c010038426503030100c4442504503030010f64005104021a4001e101c850300b84038510710707007400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 445793453 1250 445792203 445792211
    0xb0c07030b0108030909011e0b070f03021b0a060e043908061e031e01050714040b040b1606050406090b1302010909020a090503070f0305070611030a0c0c0306021804 72
    0x3c403200003100b00d50725004018021440d5a08018800016803146c410b04010b40380c550b04082100c0300e41400801080f400f44004016400c11460020f00d824a0700c0c2e604c40102c44107022143e000e40b10101d5901c01d4a200b4241000380001280204004003049514421400e101c842d00c44040138061414440c0c01c94801c0460b00c155141d004180c50743e08082d6421604802d1000d006004050041d102c0c6c1c2d00418002e090703481081d00880f0020b0302108400741d5010f02d035524401d00045541044214190091007003080b41002d2030452030306d407980100e11804450000009001410720720385000003c1241c0d10020400450816080000003000c803903038101e50300e00d86540800c04110758909008080d550517074a04041500708a9030a003c0d42000300301e9014080041400300e2a80d0301888602c0c00341080140b000c10451440c100907150218551000d810b00448190003409008084100e8140c0d0b401824084140010b900d05402010740301d80c005401ca81c40802d50920012a44649035050b80080350188 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 445794703 1250 445793453 445793459
    0x60103181b0b03090a0f0f0b040b09010c18051020030a0306170a0303091403040803070209130b160c200301060807081009051c11010c03060302061605070b0c07030b01 73
    0x20a0f48029103041d0499070021190b140000d03029050702e0034180c07241ca94180f40c4120307660703082c6280c00d0540f0b08540c8441c101d400c0000c0c40100f44245118940360b85001081c0c10020321142400d0b491900500780200d600b0110b600425015100c902218070300071064041c000b02413203400c2e840b5001030300481d001a003003250015080c05a03095201d00348030001c002d080c016460f5642540240740e03000c0101c40314100341d110402e40d0034090000e00014842c20b0b000e1551002c1074410442900402440f0b0301c4202c501840d1200130130030200c5c0c0740d58084102d24086e4903240b0302d15070694410a82d5080240000d440d8440c400c055540d102c580c60040800b0741c0240300541d196480c2c90748a0105005001c002e9101e0660660355041c150030a00400b80940705840310749240d100030640403000c90504c0c80106144100c001c10081d024480c4a80d4120140740c2003210700e0452340001c0d018810aa03117810091007008402d0f083c0081400703110002c0981e42e40803aa54415001c0460320b81516202c20303a80d08800c80000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 445795953 1250 445794703 445794719
    0xe01080115030203070e031c08011d0c0d0f0f45110a09021b060915060112050f0a1d0304170f0109060f0c022103060103181b 55
    0x1181a100c4950500341d403a140340d001100207420044c81c4604010100c140300078591070038840055240310f0351025020300c003000b990140900c0410390091403200409100c1e14143d48a11000c1508068a94451941d54015101e910040e0140b001b500c02803601e802480002c0000560003040b500c00030b01d6000e1040c070345021107a07004503a011049490b05032a1107581c070021405500784051240301e0b080c104074400d1004003040c0e0b40d5074580c00c54040ca41d80056a0318401392000700410720072443c800200201d00d881c249140c1c4402c00d50708101c07560f41c48a070100e0203583c040c01d410040c105c031014080103285000c01b45071400341016108000107901d0168086c0c1c07410101141208268002d8006520b01854401501c0941c03049024148071801080038090708040c0c02e0048005850044002144005c0d80c0d80030302045039a00e10031101036500c0001d180b400080804644440304007002e80c0c0b1a102e070755640050703000d441000c1000e80c401c1d48854040081203100c020340414584020001e900ca42d40b00c82030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 445797203 1250 445795953 445795967
    0x3121e060612070e130f0b03061008070915080102070b04030807030b03070b0c01021b0606030d0305010311040504020a0f09052d04080c070e011706090105070e1e03030309060103030e01 81
    0x40c28a410391600001409503020780d09a100020025001c0328a641710030301c0010031140b002e0000c00585803640c81f006d213145820840940c10401d0f0300c40710b42900d4907111000e50788103101c1c0b140080c1c0c513071540903464000c60f25128440c02400b0250003075690b41e41c28501000c100c4001c50301200425205000704045611138805c040704400050020400e1707508280456550341c0217400f2499440d9004c0140052244030349a04c00c210030b41a0380100ba0b181452803c06041140c411140c00030140703043c00400100381051103041840c00107860001d4951128004112101c110350008881e603c8015000906043c1960000384284282d42138031407075264a82a44880a1040c401c01c4840040342000c1070204034440001c143c0d1048000460f60055520b0500b056104000d034001b000180c62201d00c484414014000f03039a0006801c0004c10017894401800b4000f003010744c034414040e404001c0110320404900310280c0800100800310798403071400c0d5492994401003400f049001490f501c03040b074215400760798 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 445798453 1250 445797203 445797217
    0x4140a0b031006053403021014150a09020a0f121503121806052107021f091a10080d050d090f0f0803071b05100c0203121e0606 56
    0x654500b40d61410000300d400d074111000c0352031000c4500380301d0b0103100310f004a00c155801d03210034403285585c09410040e04012070114261041c6003060301c1c445c0c42c10f4503540340f00c0d40480c0054030030204203610b80110301031140540022a4031340c0b0000702340c1d204540001d10000c00d004103984a0b08500c0180034040b0640381c02c4841348087c00114a814800610300c55407503080f40300d20b880c21600b00c80010000240c55a816031002c0003103a03002482c0342410340a0114102c03600300c09000511103051200000f5641c240780741d000004282c000c12074214400d0990010700d011744e00813050b60080602c40c503000341b031800d05449500c0f8a00310181c000503038010100b0b0b030080440075922100d081c99040031505020b401e6400c02100d400c0c0d8010900400245156071f0400158020f5107140d4407031600060103410325030403524803a00e001010240d1400548006801d181701c03401e010b0046202d51416900743c1c65402400c07241145210528100f102001080f407030740c0c0820585012100c2d550b2120828002c091240310 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 445799703 1250 445798453 445798471
    0xf030c091617010605030103150e060f190e1b0915011b30020a230106050a060c0b0c04030308150a050d0501060f0605090604140d020604140a0b03 64
    0x103034400052a401c549008250700300621007540e042100748002c0000d8200d0808030780c0120060003400f541044c14064403401143c200040d00042d15000d0307680c0070003013986c50a41c2c20000050f42922000c500c0c8030107440510b2003407240d2410081c105444042451318425000140d00141959281200c0d032180190ba222102804954929004540e840c40a600d038207c413444541980001801200d40007905569942480e01a02985412200801a44100d40701198420b00140011400d444c075114010030203c48480f020188070f560746405006103910290f40141ca01c440052596045a0054100e904ca161011070a540e40b25030003c0318001d602019000603c0c280000d00301c800540004000e00400404441d00700e551000010303041c41c5450004c4441f65103540e01006558800708581003d030016041907400c00c800d00c00402c015014501c10300400b4161510b0841440e15001c0c02038203000d4014101d1580d85440c5c503c500c5078080042006805401085130001e0100000000e0783d009501d48 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 445800953 1250 445799703 445799719
    0x1c020d02340b010e070e1c060b03010c0215090109060608060a050a02130501031806050c040f080f0a030c06140403112b0309151406090f070504030201081503070605090f030c 76
    0x40c2e0142c01e4000170901001e110507403060303015558650740c00d000140301054a100310080503150180c140c6280101480c043d03810701c0705401d84550007141d00c0300300198882640045549213402d940c0500070382070001d00098075108002c50388207004250382c2c4c4224040801449141c84075a000303400c074460a0b00f024580c40e80c0c40c03024480b941c82508440c805a140523015500803030705480c1c880c1200c00950300c0040300e140019041001414184004005040200240001c1400000c00365107820040400904004075090141700b080081c0c4d100303031508208504414598034040c03034081c105000c4442d00d1807441c8103251a01c01c1004070544100814591140401500103800314180c02410541800301c0b00d00b190864220392820303c3d8030401c2007a10901c031000165003811401e02c0501c05c409013801c040c04842d1400c018035a0782100c1114210390b03081c40c148072117503a085140701482e21440c91507a458000c0f03a03000100c40d603001000c0c0101c8030048510b42e08400380f0b081050343d01c800b4412860b0b044655 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 445802203 1250 445800953 445800959
    0x20910030b0c0a0c060c05040602010b01111e030c0706120b040e07060807051216092c040305040506030f06010e030706020703060c0302090a08150a0b061c020d02340b01 74
    0x114001c0c0071080c10074184501c4413a21070351a03a080e10400c882c21000103001040800805509004442c05882c2c01e0030310110000c1ca00600540746e9000d003210400b503140340700c43c03a250341c901001190040a20700e4203440c0c1c1c2ca03490342c07001044040d502180c00204d60900c18001714501d800c0c81001d14821551008001151a195003654082402401c1d80180101407095003203543c12812020311881000c8581c2c0d07080710702c80c1009001542c5030b40001419131b10590252054070f041c595800c01040b2074040c21100e1365107034501140d40b48100d41050350003681c0401840400a105004c1c1402200301340c0390390390130580e004e0616a0b140b140d03210340f000507407254600b0804109254040750540f8083c0c0b4025141121090108203600102e60220540d41d00180b05200f080c8180d00800e60483c03040b01e01401607240407030010344580103c040c0b0f40405440d1070b15254008140340d0440da12036004160079500d1726441c408101004610300c02d005011084401030400030740d070780d81d007014140707602003403400c21030342 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 445803453 1250 445802203 445802221
    0x1f0501020a0b0a15030f170f0304080906070206040909021201021c0509071706010608160c02010503071206081b030f0a120210050117010c110706180302100c020910030b 74
    0x2c0140424603001c0d0340d928000040304501209002031805050a02c996030401e01e840e1034904034a421a001c060401d0298088441245089075000394000003840c0e2203a00503130000f600d51042d10700c000e50120b400100041c0115180d0099040755000729280b049041e400c8461500343e100e2445206150800341440001c082229808a904204100c00721000d094691110980111050150076442d6001d5001005400d07400324415034014040c801e43d82903842c80c09800b42c900c009a0b01c0081c1804008000102d4681c031440032607641004c081810701006540c4d044050300d59840461504100718509151212418001001c0000b208030100418050842da15444c500300410a010021800340d402c81c069100c0a5000301030203031240b400000001481c2503081821244420741031403d12010070400095201d010440008640541c100080c200032032160100c0f50340000d801c021740c0100386054240c2c03503950040700b20030954425259015951240c3d015580c2001461000074842110369001400c002 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 445804703 1250 445803453 445803473
    0x1021903050438090a060f090b070305192a020a0302040207170c031206190e0601020f03070c0e0f04050a0201050f1204060506090a0e03030a0b010908070b031f0501020a 74
    0x20503c150b044003590340d80000c011884000720000d005035600862086500e00d45915550000c014900b4100050b0354610409003016000e480344412000011034520145801032007100c86910002c840403184056240c8060300c04014030000003401e90b840d541c080010015441c03d103901c2034005155400c81451542000042d5100780300403100d40244c42e102e115078110b510040e00b0030448030009107458144010400d0a150340041020b8410b20091400222088100e0110002e48e11003046510543e40c1c2d440050b4030f07100e1440d078081d80502c800a00c0e4000c0c400c2000a0000340c0351168804441500c1e100822601c00c0310607680540580c00007064500150301440007040c1d210101681603041c0700c1540500d0812407070844058804c55220402c1000c5840c0c402c038080d90000c00300500f00404031074890003e51702c1c00f00900c0301c485280e583c031300424160f00981d800320080552004403110940c651918041f641c1041e600402002c00c1d20303940e80300100350120010180d600690050001c1c800d1504c691100c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 445805953 1250 445804703 445804739
    0xf0a06050916020c031002030108010c0302070b1303110a081209010b010f030c0e09162003071403040504150e01230120060903041d090703030c0515010f05010219030504 74
    0x142c480c0707030413220503914284644807803d0890000140c5031340c5403102c044d003591450400c8904061042141000044610480e2904003004104040f000b4000b45010380b0f0f52100d805001c4168400c0181c03001c204540031004082e0540407085d181c03100d40310160f000303090300c0b009840e6601058402c8210203c5620a900420742110b0a24200d0a40840503001c220030701010744100784d49034007802d00c6441041e0080700302514608110342c00358201c0b060107040e0740c0701c0c0900710b002000444100c0c074851f2842c400300255009842c0c018400c000f420400d181480d080d0783e05219801382500020000218030000c28940c0f5400c001503400c05d8490182003004480c09180080610718950b40101045264001046010b1044038010002e558590074211600000c1141079140750f0700d0b10b413450410440c2e01001c40c150003101e2741420251991041c034a03116040c800350b50840040c020044000041d1040c3e108030082c1101d00a07004d4641c650008200d090521010700b002a0200b03031300300410001215907040e0761204c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 445807203 1250 445805953 445805957
    0x30f080f040504020a11150601090510020a02030319020f060106211805060106030b091603050403050d090c03140f250305030304081305060a08040206070c0e09060f0a06050916 77
    0x41c0c69100c00014040383c00c420045c5000402001089003440b0007044a1854035a0503001900070f0314000c00024800300c03ea008150180d00700084210000c1c0c020880c445c02d556000303090b2070702d540b0844049003000089641076001071081254034502d4500100c3c019040e25000e0760b034032460034a903000448000c205545200812035540d03500c03202e080d000d03044010395148a0070180109524000300142a030b40c40168541c442e015100510801c0410055199007100c82820041110307a12402e0603141400780b8218900440e043c08800b404200c40001820150b070320032944a800c00181c0c0224a9842c00c0c0000c1d16200c41d404024802c2004070303070050b0090222100c3c0f010701125600c0e40c0d40e0504503001910101c840084c04124203466141c2c4404040142000351032490070700e001100c0062114070003a2001e401840002800c009000311450000040c2844020551311420000d07403940d92603104640d5103070040b080c040443e0f03420501e401004101d42c0020408841d0381c65869941c0141820350080c041 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 445808453 1250 445807203 445807207
    0x1407150c030503042111070801060b0d0908091203120c120a1a0a14090903090108192901020606030c0d1104020408011d0c0a0e0a18020631030f080f 65
    0xf4150048000504407a5140e075908104200850a11b1b46040c040e900400007607410500705000713086107281503824100d055800400d07204528208401e0a106000c4591b4105641c20f100304401c1c0b80000c020031416001c0140c549040d41d800030141d840d40200e0034803801c80140900481d0f84c410441e00312030410204411800300d001408000108040c146a012002e44003401340401214508074a80c15803106d0240003640c941460080000d00300d200052128180716121b0030000312600042c6e00880c40f607085001c6801481e40701000d007540c9032100c1300546005100c3c00000901d917080110b42c81c0c003041005020207225a94079030310300c0c1c0300ca440307801c120f82c00580c07d01c00041c00380000d0103403891039000306800009401c20102c282c0d04140064134a14050080d0728410001161050070280d0b0240130702e4800642d0906014440100743c00481c3c000e9845030300891201e45851205040d0045465114068030b00d00194841c15040b1074100d1201401001800c807194010030501002054440b480078803141c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 445809703 1250 445808453 445808483
    0x20c1003090c050604080303040b2802123601020c240a0e0304090c17012c0919022407020114181207050901031407150c03050304 57
    0x88101411409040020341c441d0340310400c2c0841030300101d000e8102030300d070303d4540350030051020303513903c00988020320b808040300002e0320b00150b801e20300b041105540030840b031056134400030401035000082e241c0c14244042d0041400c0800301c8103468a80000d2240045602800384402c1107030100f0711500718165502080b1703900117128103009a01d184c03c806204075680c5010b201a0407050000102040c080c185850b45074071038000e0020540701242d8002c1c8000c42d10040c00b0b03200b02c410340c880180503960040c0003c0040380c0d42039003100900e07445002012048108280b51408071100c0000d88017a0007507040301341c0c41c0440040131450400c070180040e012042c62072016501c01c00610740751aa8582a40c03000c2100021036030301505000206046800702414000352200648030f4011651070745204804000320706503900d50030301c00f4500801c001006c1c00c0240d80e581c10200030004100880c0091800703440e03c040340101c00c1c02c8119208800e6507403070504100d842e42d000e0700c199101070419105a68000300301 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 445810953 1250 445809703 445809709
    0xb07020f0c2701030c091404030509190506070c090e0a0c14011403070c0302010b100e10110d0503060f0901060f0516081614011a130e0f071a0702010c06020901020c 72
    0x200f802548a007910003217085c60155030b0360440b9082e500c0d640000980300103010102e6408000c0ea141d1650440e620002c4120111a030080d044941d0300075500200c01240387c400340a40c00c0c4250044400c210014030107215000d0185d40c5800070214000c000318400c060078421070625400c80b402080042c1007010100d1008512092290000c4402100141034000a41c040560a000e100358640e0261140f4180d44c0f83c01501401d012400781c107150280700c807105c03050042c07480340c0845404032801e0313030644070241c1c441c010003003003648221600350007001072013240016802c0180940341290b1490341d51050000c0b01803000c07a43c0d41d10a40d00010080a080a460007195210f030050802120891248400c0c0750146800c800f82c030300031910083d42c0c1c5d140c404452100c0398a010050500102102c200c3c1828800804440003001c4030f00840d03002c0d104504407219008400103034102540d81000260300700401000410603240b01340d490082c00501004030040004240380c0140c64200e1050060b070740c103400ea807408 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 445812203 1250 445810953 445811029
    0x60e07091506031103060f10021f0c080603120f28050301030204050a05010f0b070c030b011203020616020a0602070809311802010f020a0803040b040b07020f0c 70
    0x1507840405034503802c00000c0e403d0b01c036400001e1007800b0307054254030f00007001649415082d400603000b881e0a0401501440c404c1c0103821084103044003012202c8a5100c1040040040e1f03107200010403c1000403484d14640014080034983c000000145040241400989250440c1c0700c621162410008103120703840141000703a6044da002d82e070702c41e12989903004100a07943c02a0440041d40e20308401030100759983c0c00300b081610741c81c0c1d07040c0e50380b980031340743c08a078509071940040d02410510f000804d08146410080b60404d00070350032520316880d07040e41d40c0722138040b0240400250303200b04405000544c82d0740103000c0141c043d180042c18290000c01207041b81c1c1c007401700e201000b1607080b5003021541e100044480c140d2064002005501c1c031142c020f103001c2d07585ea4806810f012041b00007101880c820002d003080564080c080a80340c0c00d0918160744101d50a440c120349001054000842c65440090103888441d44a0010b1400e05000310900ca207244191580d081c1035007590f460301f00d8034401040c2c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 445813453 1250 445812203 445812221
    0xc031404030501050f130f11060405150406030e03250c03080c07060908070f030b0c0f0706020a020c150d09110a0303020c09011d01090209011b142107060e0709 70
    0x4101072902c265150205e13040217015030020001000e00b140850140c107950b4884590010032000c1902c140d40004505000d80c0d400154400e281c041d91400c00203125024104070344d0291030038000101c8083c2d820352240203003401020030149024490a4048a1001c18841240900800d0b0441e5071291070398a0694081c4602c14820b9014403001c000c00c5a20104410051580002400e04a41041c11407018001c60f40f001400b103e00c1d01c0c021600018040b0308807580095060480c0380d855025183c040040d42046c400d003000741c095503144089074104500703c240380c7c00c454032640d4580030b442001c030b000401044205440707014212662489036141d80602c00040e60080e001807843e08280702c10895080700503007140101d2503a041c400000e5a9402c0500c40c152802c0c044090384458045004a03050810783c403c0c126058a0750709a02d050140104c0901d228014440a44104440e041c1c64110b44428816203030342c101e04200803040c08604168080e95440c4402c2060701c000f00d50b034403658420340d03400c00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 445814703 1250 445813453 445813463
    0xd1e0203091b300708030301030c030624030204051323070b040e07120908040b070203010c090303140d2004170705031504080d11030910090f030c03140403 68
    0x1c10710082e100c410a03601d040c0b00504894852420b200c00e60710103240d010010f034940b4158001d4000042d041c00134020003021740042d40489803070b9a034030f00700185112268032007515428034141e00c114203aa46400702c40c130802c04015684142c10716542c244030081c0b40040144040c2000d01c040040000c48400d43c1d0200e58000c82c007104250400e5900d224100802c6501442140e20108020482045849542030b485040b40c10101000351640c40001c0c0a4070104000400c4424001400b1074001240400f80c568140260b00030480c480c030b010b00c141d480b1412404068045283c24510700d191840103001804505510080882d6103000106070b00d00c5400001c102000d6800c001ca0103210721644035803a511f8250403440105281c91402001c00d0302c03541144040c805540e00c5500082c240f001050844004180d4070300f08004a000000d585c5ea080c1c0c005841000300d5010b801e0041c014a1f1182c01800c80071900450320754510f480c075a13416a6080407000c4101c080c0240c20310004d081b820034901400045020b1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 445815953 1250 445814703 445814713
    0x80a0e070b091509100804050f07060810050105120604050a1512031707080708041707051606020114010b09011b060f1107082b0f0b040f0608030d1e020309 68
    0x120100031090450b02207401030f003e001d11240c0c581c0d0b9101190040308001d079007410500d030b0725103040c003d0925503d0f075241a02403040d080002289580640128414406070140321080d64403a07004482c80d128400f15518040c41000104480c2d00d8160b00884d0008200b080000e4880303168890358544591561001034011020f001100505801c00b512a89200120001c0081072500010203410107901601220402a0400c002400c000e9042070b0480d034040c2c1540182d40b201058a040c41e40d50f4200700d449944464a2003001960314014090021207071400301a802c00ca80c00c00e142007506410600c84281004544907030b004001c400f007446e4030904c1d4007a00c0003203100c0302000f0b14002034a1402450400a82c01040440c000c01d1094040d2242c00c43c18144180c0102035155400386400303c121400d14402c0d02d032014214800c080369000c103060a50a40d01801503801114016048405030320804286c1d8000308903060352892650b1220050401848e001410f00c0c150504000498004a407a00019880 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 445817203 1250 445815953 445815967
    0x21020405010504020a0215191b120e0c01030b030c06031305010507050f0a030f0912020a140106030221190807020f09061014070f06060f06020309030304030201080a0e070b 75
    0x129004807805440141c0e015072030309066500096803072603a111112010381c007903008507004044483c11491365003501c0340240511000c1010880d01d02000079900703000b280707030b040d070038a00718201d4014003611030300803c040c2c144003940d08019009490808011a418007584c2e4140d030740750741c0d1390b800345004600100203680c41c02690f00d005403c664004e480003007031010500c4084640c0c100d02007111030a207014500490000b002074a028003820304550700410910b03409500d0103070294000382d01c0109602441807451105007246a42d03080320018000a900300d10a1000b0b005001818803810760b803c03d5840407a4582070b01c21848510381006102c0c04c0350f1206002603188298031304040014034010088841078040c3c10540c00003104c0c0f0b10711100040a00c214503c0a821410341081a43e02c070743d802c039074503200d062290f24080004152303034022404884203114010904510000545100c403101800035443d05041d500150349025000b801d42285a0301c0701c0d004030f460032084c00614020300400c0303000c50711540 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 445818453 1250 445817203 445817209
    0x30a0207090e031c2306030c040b06030f0c25021302030f0411120a060608010c080f15041116050c12030f1b0a051b0a15182102 56
    0x2115501004816040a103007101019021048404418000301e000c070742842e44e441c40c1c0000c0c1c04524072000031500501e4103600e42e826100769840c0b140c40100d0590b02c8107155117003044201c07907400c44d48a410180510000d40040c00b440c0d8500e0308059002121800e04522849604074000d08045111603610f000007044110701f0450b145180c8400c40e56415800c5290040442101c0302000b00b010708142442017106000303864403260001d6107000901a6459581d00e428560054010fa2250034400c0d0721300442c60050500c2170315880d008a00c8084006d15580303038802d2968895085000d0654050f644840341c0c011400c80c14010940030701c0310301000244009608041d41003180b036500303d81c024044440040c042c12000310444081641c20400d0b0342c0c850040d00050204001d1000310104584940e00d134207018020001015656440c0b801100c151045514003484060300851103040d039a03440324120074061070300406c0d080c090031043d528500f102c43c0e902c0c44e155001c600548180400312442e07040c60000d6003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 445819703 1250 445818453 445818463
    0x6020d021629060913140706080603100c050f0d060e070f09050a0f030206070503161b09020708041512060f14030106031115070f081803060402091503120408030a02 72
    0x203041c1050318405803410b940032540d1413000a01d15507450416200181c1082007a09a0310b20100004040715540b40d121003010b4400401566100d219210710482141c00d07086034016075000c102c6941c1c4840c100f204101c65150150400065240c08544030700011568100400081c0d104811b2079036442041c3c03404603000350103900c180e0040c81c01004000d90a0001c8070000d54250300316079040d0341c1c10b41d4a04507800c080382107000300e00c158002c014000d14518103120900240422603500384810061003951050b0f007000b2445000c0c4014840c0072b0030b000800c00d21a09003036141502c0d1143c101442000d41082c0101d0440b810b5422030149008107150500c0500c0310005600b41c0c4e00400d6000300102421602c8000c0c448900c4a006445001030381c8401010721462000d85451070382c003031142080c60304e0304c3c6800240303a000364650120075000b91203020507500d00006c1660296802401e40f845c00e17120850045d0749507070140d2880f40c061190541c18000746803001d00031300c01000e049001e56110100710714000e04107 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 445820953 1250 445819703 445819763
    0x30309060e06010b09060730020615091603020913020d111612120c05120609060d03030f0209062109071409060d02090901060513060806010306020d0216 67
    0x1d0b44440700502500e01c01104841c5219402c548050311007107680b03001c281c42c0054002500706042001425000700811003e004001100c03602036501e1561044c0c4003001034480c28041039404145140841c1603400b2401d0082c070704c44442e240c00341c50401e1803400705111588088602007680e81c0041d074142c0d4800e961040041a00c10b01c4d032810301e13080c08010544a44800300c01c000e0964500340c4030b0342888501510702d000850ba503461060044020402e00234241350000100440c03440c3e803501c00145c0515000415030b1294000414030230402c1283d0310124010602e40300c800c82e94590801011120381c0e950800b414404c1c08402d17038202100400001586518009002c251042d448400c00b40281c480584900462407010340f581c8482d5558603002500a4a800300080d401009110501000309019007003001618800e54200c0188012000702d401110700d01d02c02d0030881c1d080507005100141160300181503070b1081000142c01c1001007000d0010790a40003008031061401070b01d940c1d0000640c3c144a04c40 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 445822203 1250 445820953 445820981
    0x190e10140a050d0b09160b030108060109020403051b0402041a1309050403020712030c080307110c0118030314040b030108060702061005010f0509151902010f02030603030906030c0904020703030906 86
    0x121501c0c0c5008103642e218880f10003440c1280d4180011803181003000701c0c0c41024911014401040c0d070303d8018062a502c28001c410003402054004100365405008071012254894014008040d0b84446180042c080c0c0e03001640c01a02004009201d48000703841c80c292a0b04c03d02050745d607007100c3c02e4034401c41d0b5055101c0b02c00e1170f0501c020000480c0e0080b07075050031205030b409000001742c110f284c00c980c0941010402401405d010051224265214101c4104241c00000f00c9400004403401503468541400105070305014140e01407002910447c0340741c800c034060f18071035401d054403080a41c40315082600106076a42c0070008011903030b981040003030f400c4031490104140301424407000038450400c050062050003000540d145040c0c48030884115849207180465032200102d0b104512642c10710344090005600300b1140710050002807080724003c0070010002c5250020741800c0c4221a040200454000c120911080035507480741d000404003103201e5a400201607903240b4109048440101c02004 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 445823453 1250 445822203 445822219
    0xb0d0b01020106080d2a021009032a0621020d150b031e0c0c010501150f02030c07050d02150c010f0e0a1106090a090905211602190e1014 60
    0x4101790300544588804130310022190380164101c1034030850314008010007508a2401d25003003140795440300c0c0140c144d03849100c204001c5000e000d03004045044140d84d0351183c859440701040380034000e0003805040c0352405948032102114440030b00803a007005d8203c0a000d52941150503c013003421009001900c1e4200e421030450603c0e604281454880c11603580400740c8a2021481c00e16140007940da545110301e000744169070312003101c0ca080100c146601c0012800181813442c5550000c0309032500c0c5802d00e4000c1609514000801426554035001a41c000c0a000480003103210010010811441e0200c00030850340b51402c91201203a008031118500f942260343c8030310008400102c0140a00800c64030b40303403100c280c070300040c0319015240c3c40f55981d06d00d08020b6008000000c0745100e42000810801070440054030084100f611402c0038024140d9441c107034600062800c0c0c491105c0416049007000c1c0219100d01540600750000e5a900c0310340030b110740e02042a55a0900c01c00607050f0240c550003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 445824703 1250 445823453 445823473
    0x609060a061e1203090509090d02191a270c0108070302070209070c0c1e0e06040b22020f032404020a0906120e0a14010b0301051003060c0201060b0d0b0102010608 71
    0x2a03504150154090000b2403410f1141814419503104000e008000c0c0480d9160801308041c2da903800041ea48480503001d4041402e00f201c404402d0148801c0c0c000d18071141c0000e54141d4450f140c035000300b40f041c07038803058201f06001c503000d10200807608452800030000407003900c4c00981000401001c1e0b82c2054010890300c40140c4801c850182c01142d0790600704681207840c500000500c1702c50304170f05054814220780888583e08901104219420403090542e00c0c0c4948040c48240d07103038200b409401c00d40345140c0d183c41c0c0716815039021042c5104171006081c80c5107116110a42e0b07009443c507848018801c500071000f4907000f80f44400c03411048804500e440407510002d03000003a2427040000707001d0502119120405550002c0e6141d80d20342e0f00b81c440d41e203100c1ca0201c586c0c1c0c001c1c0e08110021361034035842c08101d050500c59140114103114454040700e02c4c5039951700141c031082c0c1042d0215500c07084000f6640441d0f0015004032003483d440403c013002c00c0800282154841d03400f61301141d001116607 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 445825953 1250 445824703 445824749
    0x60411091306020a0c122102040e01030803040816060c1b03141615051e0402010909090201020c090403080115051e0f16151d1515030609060a06 63
    0x3078038015912100250315803a504c0410b0398101150352000e4183c10682c1080d0201c1c41d4043d00e00d012405880d90b03104102c07050030440d2000ca005030701982820100840041c17022030b4242010b10391180c80303100312919202c80c510214084100b41481210075a8445140010302a0440801790000d80c901c1407034940e050791920000d0494040740c00a18214200140850010b0018420a0700044c0c20841002100a00405400c01864119026a04c807200340b0140c80803081c064071038a005940503501e6084240c1888000801820b9000049041d803252403801002e03901c6140040e03204038020703152002c0d81c3d0b150440d01050458a0701c243c00c00c101c1c00300003030906520503000d0f043e001c58144c00d55075110310104122035020311800000c00c03000c3c4440400c12080000c22600030454520060051101c4008841e1240c1d9403401c08002c80d05a07003100c03281c0a10316050350031541c1d00003455102040e6030001070703002c2800c2c0300707003039800400c0f40d0070000411240003014068070004007403400b400d080035072900c198 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 445827203 1250 445825953 445825981
    0x40306050603011a28080c090c0a17060a03140109020f01180e07050705060f1005060301180e07090606080a060e06090a02031509090c0301060b03010501270909030206041109 76
    0x1289100303503451290105685c2605101c22200070382406180e505540b00ca82040e80c510701c0404484c0316850001c0042c030340c2800310301900c50b410140c2d107644280c0907040030401245240205020740014400e5000404506809450501104104c0000400e00f01c04c0c01800614400400c0190500c2119001a440310030700b2600c01080380d8454070a20426280c090046566208100001d021842280c003880700303568150b0b8059000d002010f4860345125a54014842140424814401e040c480411404030101403600400c860301c0d00b14098803141031f180c071842021251182c02c0b10000541c4201000805a014810400641010100040e8600d003c41c00a51b010300006e181030106034012001c42c101502c1620980c0c2d0700c0c90010840460b40c034008041c03d41c0c521242c0c0580d03100c1c1d800d040c000181d003070522044038141c0310103075601c5588101020810a12040c0d0725a01620002d40d5840000d21003510311840d81031510130713400b8042c00e05107814441032000e603881c030703551080461100340107580950f411 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 445828453 1250 445827203 445827251
    0x1f09020a0e060415050d0f1109042102061b030a0f1a19030b240a0b120703050705031f0506041d07050906090d1410150e04021e0303041a04030605060301 67
    0x1c0c691080c001d403030491045d044407030410b90044008014401005080c00c0001046601000be801245c0103010080744d580c10291060301c07441e40070308501405820820001c41d0f0200098401180d00e00380915908103d601d901d002902c0d0300507915045804d0715200c40c0341e10400c0079282c05130104a0461319034903d21100503080107084070b6940c150740e5001184200308a4814002040d001005940d40d242440d0380d4800c0002104030300c50b41c0c00141406019106d2a0302a0950703545150445da1101c034940001c454113000d94a060200d1200010385545c0d21000340054100c049040112031304040c005644805c01078848402e205060005456645500050701c642580403039514031080c9541c00d02d60301192104080c02c0c554080e80281c0704030b904d0030b0340201d90384c405c1e0b0b0702e86842082d50f1518800d000d8541030b6002035201c0100050301e060a811031880817543c0900600b030b6850960745a80e02080003440c46100c0c07034408400b04003013083c04864072481c1e034404001d41c002d100b19151180001c00c0d00303021a07 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 445829703 1250 445828453 445828463
    0x90f0b130b130f02121305060c0f0c0f01020a1403012108040e0708090c01030b03060a020d021c060303021b1c2a050f060406021f09020a0e060415050d 66
    0x107251907940340d68018403400031001c0722108000c00700c00c0c020490042e5010040c2d111112004001046001c0b01400e03e451116030800082d00607502c4400d080085a0300410040841d03070018002c1d51544042404024245a42580010707550105410f024020103910f201d002c00c10701042c0300401000346008a014242103120410203800307840c62504071254052074000d420022a82c404004034550400050340c040e004840484030002c440e880110181e801c4407405540541141d0046801c4400a401404c07503803031900405800e1032125841d00c040880701580d03042c3d2480e1038030403c0007415018021081c10225041c14500c5860002001c01d020203d9500038a003048941a050030a2200c10050824250721250394a03044280035980303111403180601510344142c0300c424010665113050021034080301c540b40c000c1c05e0f46003e030b1085114284800c490b503409140d10303207003802c0040c0d840c0602c18000d4454803241d2101800c14106010445402d00c1d0115101c0d01030b0801401659201008101c1d020b030702c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 445830953 1250 445829703 445829711
    0x7050304061101020d050412140c03070219030605040305071403160f05011e0b0a05030c010e010f0c0209040b0103030305070801030302031603051e190f0c1101020c0d060501090f0b13 80
    0x2d01010700912480170b041c0318181c40c140a00007045011858501000e145a030b8400500315140d01e80301c2944601e604e444565841041400014100f622241b45001e00300752020340c0d000e0b507c1c2c40d10f0064420840381100003850000342e4004021a45080c1d12260060710011418184224121446244207210142829842103c10001c001003504005403801400300005a06407204100308083c0070800e0020703100e105450000702e894100001e108081d134405942d070440f4405048015100c0a080501700c5081061034400d150245e241c07404814042d5124070b8203500ca944c0b41d07040017000c03035001400c41d004000790b4000410200ba400000c2d203034500740003481c0403c20b00c0546415600e0348203c005d000c02d5114011090103000503c0c0e03005e0301410300f0580b031200b4031030103555040315907056017103410001c03602e00c44a07000855052850034682240c1801140e05111180780000c482c00101541240d0700c0742c83e00c0040c01080264015801c0034034040c201808502100380005032a401c40a0700503211641c0c0b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 445832203 1250 445830953 445830977
    0x31808070f0b10080601210606150f0e030309010e1341010902130e0a0e070e041703040602040806150a0501020a05060a0209040902060409060e071b15021c0905120705030406 76
    0x4c0792a200e42c0e03880e480745c002c00954ad520303001605481c484148240120301e0380d901020b0741c64001e800300041844014055480c1c401203500664070708420039001c942024000e0306042c17a05083d03105402d416002c042200e50204034120100010891051702101420507001029491511041c0e00c41c0c1540d08181e0050385a2001060402000c0250707484144004445010300a40072483c0c0c0c0710103042180e04040c3d0b459540c0310b80c0c00305800f58041d0350041040040d00d03a03980c07601816030083c582161042d140075180c00c0d42e0384460303860403106482c03060345040e001101c01000d1801c0085900180030a002030302201202e500c91a80382c6100401e20031000303400159060450703945511a42807181d0040441e5116a00c900144005040c40e000c0d1200101c81c13000802d030315600848401200c91905c500044e0049032680e284030340507600c4031640c401680c0030700c402ea00f43c0070440010000c03410254800200d02c10142042840c2c01c02d001d140c035410318000c201d10341c0841c1c0c005c4219001e85019050001450300 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 445833453 1250 445832203 445832249
    0x114030d030504021f050310090b010903030e0102032710080c0a05250b3702070203010f02041413020c1c020f06070f020607090510031808070f0b10080601 68
    0x9420046010b001902c00500401781d0007038051401690310408001101e0b8964007200100e0344110310302404100080001c00000b84036085003c00e042043c07050743c0c10400b00c41c034407103800540c1c004c00c00c0d00e01403150203e1000d420410212810b401503881c048081d400c0c01280504944201e084500c200000055070402100d02186503403c0c3c04000ea901030b1050943d402c018007810320a4840d022440b002020a24440c00300d242c0300d4020741010000001d0008684030507000030f501200d03080340c255403500e0900d10003a640b48003410007440c11400921880c0c0c454010085400c01e805e010040062050103582c030320b400c0003d24041943ea440294020441400b0340503032405484c68012030315440781e00100805240c0c4807440d0000ca403a50f4086800d10b0b1105039040c5c0d00d0785018083c2c29040b20010032411340440c4290416405c45007490110401c084140d220100d05902043c1d017a16609032100c148020020700e03501c099030001c54001d16584180c1450040c0d612003c0600c44e050701c0b4025065a03590101e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 445834703 1250 445833453 445833469
    0x114041104050603010e101a0d0903021c020318041e1509050403020d031409150705070f12090e04050303040605071b061a19090e0c0d0b040b0114030d03050402 70
    0x403000078400f80e2290f82d120051007036010221001400b00e9200314001451200c800c1965021006044c003103428200d91982220040522075000d804500c1580c0d1041258804071442d01840c032901d81c0a50307580c5600002c1c00000c0c048540c0003e024515052514011480030260305d44009000400420303808451080e10200e4102034201c050306c3c1e442c0c40f05100400d0380004540c81c0d0369039141c0b41840780c141d01e020500840b00085031076004603046040d0402c0d034408180c51160b8052500d080c518140f4181d40c890400b041c1880c403040392415445180705400d19008030f4490b000b88041403d0000d0341c40c0c00d40d116905ea00000c1c00003045075440e907020545060142d021100007410303044440790900003e0414001408025221032214181610584041e04020714100c0307a40e0403500542c82d41c1c1d45481400300042628100360b04035400b810710042040d60382da80a421120340203038012259800c103420305000420b070681c40340a80503141c200c002c206480c0443c0c01c00c40554542070001e41c2e940c0340e00225082c5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 445835953 1250 445834703 445834709
    0x30e030f0c01120c300b0105090d0b07030e0706080f0a11040b03040f151e181b09140a0605060703140a09030611040806060d0f1205040f0f05010e090114041104 70
    0x1d0600c2000d20f4402d0a2045000c1702c04030010001072204140e0300c401035502d0300c600180e02c1d410400c030016500c0414070704210070303800001a260010b4003980300402542000e10301e4101a00040c0249d0030b1140c3c415800f030308250868244041000341c1801d4618a20701c502caa40700307008803c0b601100040c01c0c0840408880003040e040082c02200c0b400700c01440c401007107448810f920244446416806110140c881c0901035500140298490121500c0f43c583d8504018040000701c0c42101d0f01195440709801100700e502000340318900c103414450070f00d01c26075016420207400b50200348425004a5400880c075481c6000d0f00c2046661219105d0080315580d4464001030001810304020104424221000700100c139419811380d101d40d16032008011540744a41c0001c1c0501328100815808582d0040414142c1c10b410304000b4680380d50b0302d0380d00c51581c3c00d80d44544548203201c00d0400c03d55800c0f11850f0032400080b2440200e6604118103240003001c0104a64080c660702c10314803040d0441c1da011034010b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 445837203 1250 445835953 445835987
    0x190212010213030c03050d1706060f0d0c020304030209090c09010e0a0207021809010b060c0705010822030c1103060403090623070f14030f0403150216030e030f0c01120c 74
    0x20035031a410000c007245881d10080f5018840d07c2c070340c80001845200070b0700c0616101500781340513840d41c9080040c1e50300030b07420003443e1200802c0300c0c0007200c4c0944506140390383c1c41d8010f96155860b500400c0303e962801003c0001e41d03000740340e81c041c1554800c14807e0548078881701210158070381c80d440314020300a254000790408548112120007070b0b0705803001440341c900c0750001d200e240c1031141480400e0140d0b800c4144039a200d628180419806894103580c00aa0b95082c00c10304040b2030b10410280c80300d06000d038003140c544240003050104580d90741c14141d030207134007c2180e0304195070010603228113031141c80104880b005c0c441d0017045000131034000460002c0c03078068440d800b074103010944645820b8215101100c0c0c000c40040c0c000003000383c0302440401c409241c1060702d9030300c03020b600c3d88420010b16507541d400c2007a1241c00000d05000032a407806540d0703000940c81c0082c2407500c1d00c29258000c1d421035204c485c151a550303a00107074025280759464008144c01007118429910f40d911400c0380d00d8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 445838453 1250 445837203 445837237
    0x8060603120a050d2d060b0901020a12020c150d060614030601031e0e0c091e24041a03101b0509180708090c04090206030705182d031902120102 63
    0x801d005c02c5000007084c42001100400c20b103a52620030f01250f128503501e00303015070460034461000c0746082c0c04c1406e20401c0c0b4011784100030140400a416031202095a84a00b41c01050a100102861140c400504040e06000b03c0700002c44034240c40707074000140078a041540303546882c40040e240e00941641815619001c1c0880c0e106c4a00c0e0544400e0070200440c0640081070019102d80a842d84030305420200407450701441c0c54200e08110320b036a034000f204a002d20764128120f0350b61183e1203036415182201d860855000b07150310405050581c1c0c02d1041081e0b07170501c1c0003081000501012000305043d81c0c2001a44ea07005000031425882071052100120458601000601908506000d11400c60301c0c0554510608120400c411039101880180d003280d01400040c18890240300100f03000c42500c2c4502428440440000309106405601e00342c01c0c02d82002e03c0fa40c110700b02d060302c4009440441c058501810a40f0318031915001105000c1e1144442107404d1114403402e5049a185a0903611595 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 445839703 1250 445838453 445838501
    0x2031b03070803015306060a030b071e0504380a020c0a06080910050411060304020d0c081006080c03100b010504030b0424141911031008060603120a050d 67
    0x174981e003003c100401c5560303401c243d88120303424046a41441240d00500b690506030640d198940410781c0204402c0038400440400e00c540355400d10316040740d80380c5079550341d5540d00b0144d21b203410344641c0c10b0000ca0320440341c480c00f9a1906490751005104040800140c803800200801c81c07800c40303800c80303040e004107640382d01184407907005041718490303c41d000c01c443c210349820741e1610403948200c402a2101100d0003050160f85130480042d908503000818030f4200b50388688960881030b04d5580500c1c080d0f44440740300f00e04080c0901030720008001c40001b40c0b500b0b01840d004a510350580c03200c52600f40f0381d642c1142c01c1030781c0194103403005140c02c841c09681c0740c90b0078608001c80b2051024103025800541001c0e2103180650f026148030405007001000382915003c105d050040c210406283e081c503103e04c0710100814000d0081e45c82044192201c5210920f0250304038140100500443d0090b004005641c580f114400300315030113440c01d890034a0740d4890010820b0001c14100400c01c02201c084da42d1a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 445840953 1250 445839703 445839809
    0x105090d0b010317070510050c09090f091902150304080c060a0207050c0609010c0210030608120721050f0c0a0606080a02011106070e0d170a02031b0307080301 70
    0x1d42c1624803803143d1081c1d80d405113200d0710150061450003009907204c11003204078580c0b581c02440c0c01424000c2141d090011600008140100448501c40024001c10400800c0f1108000c20101c0d000135814040580041e0340200e5558000b40d2080c050181000001c60200020396040380c940600f41d01c10749485003080102d11000c0e41c0704810603141c40c401c09002d0941071078180100c5950110584507821106065400d000082000c0a101018140d0303540000603a031400f8400c0b000440840882c050395034005181c001404000d00e44070032078034840d8201c0245941d40100486680d440040c02c040d03210030000412500d0b0081d051002442749040c002c0c00070344914001102c44905100341c1312041616285039480340c5e04d8208860050000311030002200042c10b10000c0d00d00454001c490060030488540c00c0410a90300802810005a00000341600c80054550352810050a0a005589042038a40328200c070b500040c000c034020581040c1210031250781c442d28941c00410700d407140b81c290b00c9440c501 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 445842203 1250 445840953 445840973
    0xa08031b190c09051005060706050612011503031e0e240a12180309060c050312040b0609070923060702090a0605040e06010806070e0102070f0306060609081b0402090105090d 76
    0x1480c0c0b00f40d0b0604001c1004141c00c040a030041c2d0718003400107801d000940c0c071031030301402e40604055002001c50351082901310003030041c030025000301c1018403d02c2d0700d0352600826180d1030320301da5031861203050355110880703911451600d01c0480071110981003002c181030048109946110001101e00c000820410650f0080f060f10131a0302244010402442c042d44440a50344035860700800107280c80509100490007480c1800c60f09020f032003281d0070103d003132078800200003094a055802c284010100240752501d00c010036448800c500d018a0000d02d480340d0b0004a0709416004006484162550003c0d9241d880559000705c2d0028000441402c0140d4401d004001d1070003114012410100071295441c0005550744c100c507036180c000c0c905903a0f442d0f8101c40200440a95038114025090001105080e50341c4440255009080c001412031603c4400f074149090707940b2145260700720000c00c040b6100c060460b545000c0c0282d9000da0341e20320743c400490f207521481801030340c80007401e81d039041070143d4090 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 445843453 1250 445842203 445842209
    0xd0206120c0409052724100e01030f12090f03021c1208040203160f1a09090a0c0305100510080a0608010606020a05241303090506030c0310050a08031b190c 68
    0x40410008110550035600c6c0d2000000003070030b41207805101c0c451071110601c2903500c07a9604084034100390326500b0101250b034003a030081d00da604121400c1300900120710082e0607000350a003015032101d0318012020090101910000c0e120381290801e1a44405c3e2604400354120350004c21046000154400035001c01402d403000d80c02842610105a0307500c044400c00029200240d504034149460106105200d00000c40340300c2d10400c041c803904149881e15848135010320a13080010030340341d010050041c1201d000500300d549074004418200103130f07155014000222686803601f200e0361b9550f42965030240c080b65008074804c4d03180050012341c0c6a030120326419010701c6041030b24640466030042e29058041c910f820010100340c240414009075030b5849031009140300f070502c0d618981c0d86d0030000384107030421208599070201c000104019001490341c60300c080c0c40308658a000c01410a06080e80d02d014030303419040140c001494038403460780f04000d0588104030740111102d5030b1101e0315000106026900c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 445844703 1250 445843453 445843501
    0x1303030207110928020f0904022d0d110708090f030f0d0203041a040609180b0402040909051903050316030b10030606090905090a0609030e1504140d0206120c040905 72
    0x40c4c40310684031303503008462078140120420342c10056400200402944942c80039150b24010f8082c05103414815920780c955081516400341d1202c1c80070309040280c0b50401c14688804004020841c0040e4030b40013035a211034030a44100e101001910b02003403500b05c0b40c6d002d1180b60320400340152481d42d070010081040d02e007098a202140b03102c109900100307010700e00482011951701d010074032120281d46110f068250501a010444001c0e80010504a903c1900880030464442100c2003c1c81000c00541c1c45603000c44941070044043ca4400a019000140150b55812503508a0700b000510a400407540070358021b041c08110f921180001c4c004107040c0c407404010511162000400f0659441010311900801003d000c231251a0303034940000702044401142880301440d00c1c4500d40d141d090300e0341c2d180341c0c0c0080160390740c80c1444440051803580070000c0c1e1043d00c0d81c3e020100180c49540a84285a1044001e05007540b6039070200c03406030203283c20502409290000b001442c200c44c0c455581c00007844 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 445845953 1250 445844703 445844761
    0x5010f02010605150703180b1e0c060c1c0f020325020604030c170a0f090b07030507021215090a03080106050708030f06130f0f1413030302071109 64
    0x5400240c0c20b0360414480c0d0395002652007194054001c90341d0042204a03c68600318000092890228400083d180c000c40942c2c00041003003841e907001d003141e250051070174040c4c041c1409803c074201d541da500d0003401d090400d140810100340300c081803050311012030414682404154203004030b91000750011514698080b10704500d5911801011056450071011507020b0045a5a291416140c076400d40b03204588a0000001c501111503009001d81080000c0740e642c00205001d881005080e1229a0001158020100175990000fa00300041701d04040d416180202401030b0b54045a0800c4401090000c21a052000700a100310001c6070700c4148a02c80c0c0c8540016981780c200458241c00744d42c01c024211402000803405241002c64070550105c00200b00c130300c0c2010740003007050070f0310510b410f80a901c0380c071403203090584221800b4060300d8000991441c519490140600025444400c1c8007406143c0d001660100740041914074602c2c50340054640b481a080170841d440b01207070000486000e80c841 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 445847203 1250 445845953 445845977
    0x91503050f18030403080f04120308090f160315020d0c11150103030e060306030708100e070b0304020a03120e061803010e06060306071119050607080c04050607060b21070501 76
    0x1040c000c50000c0715200b0019402c2c01d00756942d440d1140d016281079030b62003e0078880000c40c100d00d54616503282d44aa43d84903d04e040c41c244003494042c50b0b4002e00717090303001041c800500c160f4504503081120f40141d1120040c80300d04004200910031103c1c900d40c41400c103d24204a1600450042041c0c1061401c80c0e8003110701450900012400303000080004048030100c0703030320707140c0392021b550401d00060540d103126949803041841e10505580b21511a07440e01c058141d505001d2010350004d04201440c40c0c514a450790010301440b805000042c0015080341c3c24081891141e40392001070342c00500600e685101c1c04030200010242200300f54869804c2802c030160302d03d07020500034000d43c8050000c05e00b07a01c5403102900c03034031101007075400307030780b08240089041d800c8600c0c010241c1070140e4090081410158002031000c0030060104180210030002084a61030751b030304075501d458000200040041e0b5902c009544e918100c148400ba40b4152102c003040d0090100782c61080b030b2803d0300c0341c1a00501c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 445848453 1250 445847203 445847221
    0x702240912161814040303050601020d1e0c0507080304090204050f030a0f0b060303120c030117060f0703020a0309140c13090804090e03070210030608071703030601030b01091503050f 80
    0x303440b690702da0303000103810340c10031034480501c20001c40ca0070710601c00300d1440340400c0390407402c507003c44055000039200c4c0107000700ca58061110b42012a8645840043c042613981c10042024040c0c560070204140320f1007090038080240f1121000e09418800d40f0755491381d505d0104041e400c9802450f00c0340b024540200c000d8600058070341c020b02d611a000b5042004140c640c0c420744540207001a030140000c01c100c60324003500ca07a0f441d205038241e9001035120b5040604500d032074031010b0700134496548428140002c1480d50a0b038503038880c049207005641c0e440000c01c120043e107a8240c0060100800c89070b8030310b15807404140400b49040035035420403001003641201045d42d06509020701920340c200f10900c506400794000c81600c48290040f00e1403c500341d40403403034285511001800003903442800340550b030018030500006095191500121010481113603031248400f80189060503511483d40020f81d0080e400c001c010100000c10b5880540d1100000c1e0180004481388000001c907200080e00d006c0f = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 445849703 1250 445848453 445848463
    0x50d08100f0e0610090504021201030c08030c12160b04050d02010506040506060a1409090f040c0e10120c17100f1424040f0905010b0a0312050702240912 67
    0xa01090b804403a15201c4109002c640014540c10f00e0800154000100d42030b1a64001081542c090941703a104561450030003540262598000005540040101040960340025840ba1781c0064008060380c031050740d6014050000c3daa00c006024101c144100001c3c4040440c0301007807040e00741c009100a41d01d40d0704010482e0412a521907210f5418844500d84074820350381d03000d4004846407481d00d446245c02c001080508102c84581c8840aa48100b1081000c071112440040061058038a814100380c01910300c15046da0160320304003140865004140a512141040104040a1003111075598040460340320003550711200ca10a0034000d040950944611880e80b444040c45400d4503251103240f03035005010300e0f01101014140028105103500c2c0e5561061200316411650005405c1c007240c6411800d44200b0342100788100c01c1d08800700041010b80e00c0b1064a180e403850459a074595510006900b0240c58907900e940e144001401a0b0710030362100144800c2d80e0868001242c42c1c581d0102e2546c031 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 445850953 1250 445849703 445849709
    0x30a1e140603010629090a090b1507020105030105062a010608010b03190602090604081006051305060a0302010525141606090902031e09060105130606021f09050d08100f 74
    0x80c0340c82c160300600c42c8040b01d0202170310005084c61030b00d08094280010b0150140307070005600e0540c1c7d00c0e02240149001d1008011240f2182d8503d0706106651300060001e020502c2402e000707100011390101c03682d40015803c01c40d1032850301051591b004d02d020050081405000c0c00341c8543c80d1501499492500041c0ca80104520902612100d0030a80c0d9240213034001441c1c0c5908084184030129481c0d2051103800c19540c100302000491030702d803200b04196402d044c10000c032860b107801d05001c1981c5492049034245d80c0c0a0810650b01d03c1c096003400b0500080c00f042005d107582080c041400c1110400307005d50070780210b000700d440c4400156032084500342203100346004100940c07001c214465081c0c0185070f01c41c1840d004403d80280c3d4440b0450034210403510b4020f107030003510050140b4035280681d081202d06401c070811049051907806581d8900e56450707040c0c00c40b80803180c0029002140c01c41115030342d206003620200f101c5010301400c114001e490a081e07100109401203030340e4143c0e41801e070803 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 445852203 1250 445850953 445850969
    0x6020a050307140703080f130e13030e030309120c0a0b0a050a0c05070b0a0f02120f0f07170a05180d1e15020309070311030a0c0605030a1e1406030106 66
    0x1401d0000c3e51040481e034524802c645190080319030001c046074500c400f40015202061895995040c1d89405400007a003903040303840c0d881109070a1003400c0041e0340c07450410343d0380b6041c042c01011071030703001a20f1401040c1c8210340c803c0d80f0140d0101c1c64480850503c4604500b41c41044001d6152416800035000d80a444070024200340a840c07465032144010307000d028094810780e5115615903200045035407140c0041c0b00801d200460951106904002202452401c0200a42000100c098000300ca00c03407000d02020b410804a120024030054400044441e070921001c00d9480c901c104c40901580c100070b50010302500011140d0110741080000c40510903800f0741807003d082180c4003076040d410010f40b802c5d00e01e0100300c460000c0300c00f03552008500400c030f600000c007005440c40c5007602c8464070400b80e160080d0007071240c00300040c18030b80d409407d0710845d0400c16200d68480c8501c40041220b014440043c0b0300210050130400e140340e010382403c142d1114581d03259038481080c1401c0c0c0b0000d104d802c503 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 445853453 1250 445852203 445852207
    0xb0103061202011b0309050907051812030301091d0304090522020a0b070602090315010503071d07030b015901030b010908010608030a08010608071b08091c050706020a0503 75
    0x51501d000d420644080c2d4406d040c0a80159200c1007c206001c0040345c0400118800140010b00003e000e00322007003040341250034071960200c0350b00c401d40300d01040c851182c2076038076442c031003078106c041903e180742240c09142102d072a2661a010040036003016100c52034410185078002d904082c204c50681c106c190040e10300210306181603d005200c1e44207100a070340c400d0b4207000031032a9541c14090640d1680c4080c00e1005a9410002054202005944905600700c44241c3c11044040800103044c0c6c8840304c0c0c1400108070f4040801640c41d10310f8031000000107080b031040030101180e0040c0304041d241640099094000c05520503002c010032058880038140300b1441d403410258400d4000c2070000206240c0491038556680d40e103802e40381280c000000c1034001054508200e03070320a030094010001d600d8a040d135400c0c2000084c1041144200c40400241c96110740e009000b106805c4400c000300180c9a004000013940c4080e809480e0b0b103504031114000c0940003c0d1003840064100c45140d013080140d4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 445854703 1250 445853453 445853477
    0xd05010606170442060e0106020a050c0d08040e01030311010c0f0206040f02040f020c01020d0b1c0305130b0408030a020c09010605041809240b090f010e0414030a030b010306120201 79
    0x8040098400d103500f440151842540d0321400720801070b00344c20309805901044080c18020f48503251441604400215800740d191035022490009510300d14080a560b59103075120103040a44682c41560408441c0d86400350000041540c4081282c505030808002080011100c203000c0769100701c000f5004005074044000700c1d01003900d090f262114076100910000d50101120000c07000c5e600a034855120300c2e58080380403900c0c88114040c221500100700e4158812400031290f118001c03c00000c098200500840c5051415040700c080303501070410160180d4031079070b40d1002300e0364079840501d00d80c0040c00b0700b5404001038204500c54134162030711500c0c0d1a0a02f410a400b0081c580d800311681420305484e42d0a8001107480d0740c240003940c0320703103903460f16184818540203000e650103400010b010301c0e811030820000c40c0c10904624159075011602c600395845500301800710034200c8e15030005c58040040d100178629010341c00703241400c3d400c1e02e052050658403104401c41b4040c4000c060f001c5000840c2d88 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 445855953 1250 445854703 445854743
    0x110301063c150e010e030f030a0e060301150809030720270c0a142a0a02060706020f1306080105040608060c04060e03030c0a060506120a021e0d020d050106061704 71
    0x6400f4101040c5070940350030104100007450a085e211a558258000103502c061040d4010012900f03d001610f019241d94544421031400030f945000001c100b01c80000422240242802101c03440758124841400e040b051102e084031984030007000c207205207020095280ca01a00b02d008068440c4614102d036540d648514081801e0f5000c80040d02c07c00c40001111256000003001a04000d1000500889c05603200030300d142075415120700e803101650152510f4001070ba01c0108407424194031000150322182d5100040a1500030002c07042041e4441003000300c1c046030701220260403550203c40030b0002a59401d030700d648405043d50441d003156801c000a0000d907020343e40030303800c10300301030122441d01e00310303030049810105002c1d001c40305941c9841c01d01c21685050003244000030481d0b0007900400d00e041c0d000542c2e0100c1110b01d071111103594110b030341d015981c01c007149c2c40f4241c014202c115022080d1510a00030b11060040d03034007003400d41d0f00c02d641d54406074000341e120340c0e0b221801061012311203040f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 445857203 1250 445855953 445855967
    0x62a08060f0a080703110a060c05030307051b01020316030c0302160b1806090f1204060e12032109070e070f050304080d1112010b090607110301063c15 66
    0x2480d04980780b458000384500d81005100010f501490701e43c1985140f520400030100d82e1644501c0801403281e5500f000700307602004494004005007051590380b40c0751b0b0000506101507500d03d4245510100c10420205500c00600d54220215641040021500341d006d500302d000310100024440c47d10382c01d0030000f9200e80501034000c40c01d5802d610342842d00000c1c05160100032196004160000b002c00311112030308012120400f43d03900183c0e402c0c5401c3c004024001d03045034849a00c81c031040c00c2d003050580c2e020b00885508083c00d1014500240320084a0090600141c03800b04491050381c070b0004403241c5000c5800d0080c2d9665031100c501c2004144103c48d1600040e005541c0e40100300840c2ca903103140c80c442c904081202c14510341d00c4011504078441c3e904030507440303041010010480c002c2c2581e280c02c1102c061690114084d40151304210100340140341c40d401c43c0c24400c042c40c4200940030305640d1126140c0c59410150701342c2e4a06801e81c001200c2141c807519000284d0f41e81c803004400d000d040 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 445858453 1250 445857203 445857229
    0x40b03010f050718150503070f030b100306050108010f0b0412030924020d09062304151707020102070203060a02220e01060e0d0f060504150207062a0806 67
    0x800070503480d4101d00418116501510b14102041c0311050051003c488030400800074641c0f4100c03c090600c0112000d0900d01c4000d240c0020010500000d060950082d0300403501840701800c90380810352031100c0503000707040c580a441e0124000e01c00011f42c280462001c5401d41d448581c0d81d50910f4500b60818844014485013103080c40381011b401700f69a510380000104070343c007248078601424124580603082030719201e000010030043e804184211600081c100140f4004038200f03a0558008250301e01d014040e80d00104000400e2040c200ca020341d014410301500d400b803c0c01ca01c40c644802005908038805d00e00000e4040c1c000a00144032442c443d80545080072890f50b41c0b9252814180c0c071104500b800381c0007501c0b46108100140700b56640004503040115003600e2554011500e6103c12040c5e02460303800400c2c0a031240009001c00040652090f01601081d4040d07441c0d400c0c80c5010405042d05500c0411080070702070a05810041d11070b1070385980712040d201c244098480340144044140d80e22 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 445859703 1250 445858453 445858459
    0x90c0b0717030f04060506030604050c010f050d1a03010e0a0b070e13020304060c020105010603230405030c0708070305060f2406090607030903050c030303010302060f0c01180302010221090c040b 85
    0x48a01c100c0150140118410040030340788410764901407400c0000c5680241035540030b83c0c0f220302040b0020f80c0015102c401d5210900f0504450200000111800d00c9214215400c041c00c0c041b212003120000310300c0c480443d0b800c90090249442c1800301e01c0d0fa4040d0006c01a19103c83c80380402d56440c014254401000340c0500038802e00c071000c040410130b990080d501210751a07940c0186103411507081c0f164602401c028502402440c6c070500e01c00301814502c1e4202405e082c1c03c00c0100b010040b0070021600c501081009640780c131a5201c01080c1c0b80c09040c80107481d240120360028201100d080301151003080b8141103400313a41651030f040c0b03404254024000e90070074800c12003101243d4030203010b442928440e070ba0b000e40103411842c05a062000b10200c05001e0f40c0203000620050b078600b0150b60642d15880c01041e02c400300380d0b2030303140503061012800c6011400d640069090541c1900108040c2003e04201008101c010401648811044490110360781149042e480b030f504d42900200c080032001 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 445860953 1250 445859703 445859723
    0x1b0307300602040f06121a01090b0f040306050c0a02010e03040b03010b09180a020915120c07060b100903140f0c01031817040f140105030a09032304090f090c0b07 71
    0x180c644031445154941000020506c8800b2881d180d42d01401030400c001803410b48018400c41d1100040c03c5080ca502650480c0c0d4400300d00117400c1120201568002c58005c0800d01841c00c005200c0102503000c0846200154240012603140c040300000303c2c0c04855000036503d245030319040c21003c1a80080700155401100001802c44d00e85960070b182e4000c3c41ca4040040c3d59414007004c0200700c2e00c8001d010b000c0c0c0c4405120403184000001c41c0d040d484850001b0540d56007015240c200b004060014401c0c2d4850100c2c805244015030065000064038892425114608141e04d42596200400c140302c40322580120801e501a5209401041480501825000c281d401c143c0c1c1e034030090303204111440012a4042002c0000c240314984010040103d148005410754048000803d00e1000400821449450f40c0d084c408040c407400d0b41d040051703034641064846009030a011941603015101c1c1165403400c0c418015840d040600c04c1c4000c3c03a60105000040b240fa00d0141f614a4104d450185d601c0f030300f0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 445862203 1250 445860953 445860959
    0xb091203010f060828050106170603150402130507050d0e0613081308010618060506120f0c07020d030309020f0613094b0e030306211b030730060204 65
    0x11045117400c42180c2c082c0085595030518400034007844040b0041c6100f10440020322016403000300e0400e4451059141c0030703509690b00d001284c004122141c40e401c60301d02e02401c1004140e44200035011504540c401031101c180b9804186540342419a400c0082086421400c800079031544002c02818410440508030a030399400300354211046644542c0620016110943e008026071049401410044507102d08000c01041a200303000b01c02851801c844044401280039408854152a00a680202040d09208030b900d4001d019007840b407002c1f40603d400c0240740d034651900e402695404820860342c50b0301c0528000e074002c040d143c1c00c0c00e000603015555407003092a54400c1034903002d41c1488010310030390903c070f411b54420404100202e458910320300721003602c0c4800c0c00b00480c1d4102604a845ca4503240e29114024060b586070410784007184160404402d0100702500e69046c0c40c101141031b02c10a42e80c1d45100d400070004103424032035001031007120700750084038078040d01c800901540c2d00500702a1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 445863309 1106 445862203 445862251
    0x70303020f070804060c050f0d021f20040305060c0f090f0114190e1215151306170a0c1a070605040b091203010f0608 52
    0x60000742004841d09281c00b600d5545402c5a60a80e40e16510140506070006400c0c040f5114081d00342042ca05180100700500521802e802800007128004011050f4510310341080b8070640c2c0d509248105100042810322824103240d082c1c13275445081d07041c59464000d00524a40141e0007c0043c60f00001c248400d8070204501a250048000c501d5001694404038a2040b0418900003052417070b500020061b2005200304183c83c3c00046014490902c4110440050540119804010750340030042d1035032071a47e4031800740b90002c03443c005100b0000341810303204881c8669450701c1340024007060130a2444080740c6112140105841c800c6a5148003074036605208030090901b044403000c2d46d0304088011603170101d83c4100100326900e41440c2642852800740c98492262250551a44001808804407410b0b070716600c000a503894070780700c4222030300304d0011304201d41c4231031284c5d1102d441c2c1 = true := by decide +kernel

theorem cover : BRFrame.Cov 445683453 445863309 := by
  have h0 := BRFrame.cov_init 445683453
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445683453 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 445683453 ≤ n) (h2 : n < 445863309) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
