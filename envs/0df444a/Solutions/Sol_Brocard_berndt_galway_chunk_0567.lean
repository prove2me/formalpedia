-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0567
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:29:14.641287+00:00
-- url     : https://prove2.me/submissions/a73e1a0b-6cfa-4dcf-ba45-f0ceab69d336

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 101798561 ≤ n < 101978417 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 101799811 1250 101798561 101798579
    0x61202090609130816060c030e010b09040201050a230f0a09170307030507020f09040b011d01030b06060306030a08030c07060501122001020102130b0304050d14030a020f040e04030306 80
    0x102030107840c007490010b41844080f142102c00161003941088140b03943e516014200c503110040c0d001c002d0805031800c004034003942c0e1300d9049005505a1200280701e02d0440360100030248405480007408030344100300c0300962501a640760380d54580c809120404070300c60843c943c2c031640d002d118011844440041c42d041200c0d00280200050540c01c0c00b40b5840402035008150342e1f10400102900b4808046011001c5680360318007a020b07584050441c880c24202071074403001d040f074280194003110240724001d1002d1844480401e0403a40c008a001500707890f40d00900203c2c0d880600900d4041c01030940040c04518060029401403d00792110380e076480305414820308491040e00401c0f05503610704402c0010602100302030002605652407a10000901c400507402440f071030b9401100c41c0f5403144001903401c1524040c6224034010301c2034a00f12504903504480f07101d0310040e46d600e03880050010422514466028004483c0d0614000f40340a440d000012040c060803202200002d4948906100b074241c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 101801061 1250 101799811 101799829
    0x10903080705041505161a010305060105030309030a021c08032806050603040b1512012406090608060406030b011e050103020306060706020906040f0e0703060e0403140a12061202 78
    0x7285141071820141071045407901c900d00751907910104040480c104404015020b40f05041c01e40c410b4054000e803580d0784e54880e505100b48810358a9000d003000000315400e01000b20740e02d074034009015041c141843d03401c210315091a55101e90381c18004540c403000255814005500805290051401d41000c094599440342050f0800d10525424020b081201d42c4580c42902d4001d50b00c4425564103030b030395114242c1381c2250569425400344219001085d007400640c81001681d0302d4105059400e42c40d0602b1040c45101c3c4e2103010b00040b4001c00400201d0b10413510ba030307084903008001165890383c2ea25190743c1c80500ba0018164407001800304400c4502812a0301e00401c003c2c24127506500d0710100044140c0260b900250000b500011085116550b0008507005082072400c443c0c0020f032111855240000c00701c0d0a50042480c080002c6000d4078219144d0384a242c1c10754402c000361094000301c5845802c080502c1060280408880c00901c0681c003c0c000030f0089107408448c01980c5004100700c80d4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 101802311 1250 101801061 101801071
    0xf0e09150709081903121806020a030f06090908030610020f0d030b010f08040b0c090f09010608040b1008060a020702040902041a0315090303011505040915051005280207080f01090308 80
    0x90074413212900001e4115071801c2c4095618000040c480b0021000040890704040340201454130001d6036029094040d8841c9040d5280000100300d01d54507181d030b060849140704809810b600052002601904d8600101c0c90000e0084c4113490400d0141c3e0840c03458044150142400709468070400d0082d035074445148040d2030050300e05809a82090349035040d840601501048244500003420b14a40e160315813040e6219102030155009580e6505d0010103900701078a00b02c4201c0d1003240482c500201641d410307000d4484c11030141440792614000c2c10025480000100d800945506020000d40d0700c0d44120307030345208050150240c01420004060910344003c4000381801c090406001d80403500205403415203500740300038614030340340c10b00580d26070040d0760220803c5410941e0303665160320300464460454400f5030302005140030140c000c2d81c00c0d0241c51102c0b1221400d071680c1c00e50b0400042140d0001802900507189011b841d030701c14a080c00c8800c01110b426a4490010004055009132079a0b401 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 101803561 1250 101802311 101802343
    0x71e1e110f0f010903060e0f06040503040501140a0806060711040e0c04050a02070b01030813170106090f06081005041509050c09090601050d1515090914070f0e0915070908 75
    0x5a1000c07400a05024134a000180032541da9030301c44000c8110800c002d00d844e241c4501115028a041d00d8860390302d40c07142c01000c2c0010219140039035104020010740300740c13001c1519415090b07035501090002d6500603e906840e51140300c400c2c1d0406071660312800720b0040349030300070b08440380ca6032003408203882000d0303d01c5010300c0c410044d40700815400000e160541e039020031100d958041642ca5102c140c3c210740c121015903100c132520642d40c048150f00030700450320400d40c140919803052081508036641d40c42608440e40040e190700d105540d040d4490341c3d120b03101d40c031440980500400c1c8001210b1001800310f40c2540190a6031550745011005254018080c0004141c95030500020030300103000b2010060030f03101e004c070001c00352a1054110a16110b03450004450079952454400040e1001031000d96200300b80c0c8034460503004c1c000c83c801d0107543d400b0848501484c03501c00c0c200c82e501e000502c0005c00c1e02400b007a00c00c0189206844902a01c1d0f241d0311036644030f08284485080050703400d102454 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 101804811 1250 101803561 101803579
    0x5120303092b030902060d020c0604030f020102031005100309140a0c0909020d0213060801110a0f020c06040b0a030e0709022230021f0207050105071e1e110f 69
    0x1e5100d1100b040b030440c8a9a1038049581c1c4c0b010310200b40140600c40c5148074807030000c6040408050300190003071196000e0b946101022492a406900300d110640d20b001305410782c200d0902140c28104210744600842d40750019111182d078555180280881502d203a5982043e01800b0903c0400107000c0054016844200000c841a500042e014030700c00740000c0c05080c0341d0503034a4170102a640700c400102500e400034080041c1141414046030701c410703800004039030b00f2040c5000e180d200203800400c3e1130014104034909070034140003202c19000800080105500c07804074508450080c00741c84000c1c030b041c0c02c01580382c002d03000d4100f50343c030644610310840ca03038007080801080d0440300340f150744003044486403070080c0540000b402d030780e4011480c040e411550310001e015803006040d00d41d50000041e036003035a45003500d40e40115107074410840060155083d12444240c8088011211060640306070f04c000c84962007109400380c2a40105016034200686211024460400030044034161004a480d004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 101806061 1250 101804811 101804863
    0xf0316270e0a170c06010b0405010f020c030d050c01020d06090605030c0d0f08070206070b0f07030f0903051b0f0601030510060506041d150d0f1101090b030109150512030309 76
    0x2990702d05860016050350240344205100700d0a41c8201c8030200b80c84029a4005d40e1119400440c035407243c2310303132400600003d040c01c004178400b040042103900e0060141070030280b0f0403400c0b2004d030040340101d805958200700c0035040c00410720070345000740000c1100ac1850352901040500740442c5141041c000d00355070130182c00107280c90610306002a40f00e42c90b00c7d2940198000702c1d1240c0103c00b4004d1140408109101404203d050356a04c10401030703800380240c10125951000b500e07600b04004020440a210744414000540000301c0c200d40550300703c840d20420592001d107044800c1c3e100b40d90340c0e04400e17407203410703124035014a01c0606815a0040e281a16125080c41d503503418002d0066142002d00200b41003200d040d0403d40d81d04d8004180d1141000e05042610303400c0c0d41c4038030864140f459240c80048035401003040004441603c11500e00b11f0b0310308000e58006d4100021691700c1d1991108000c52aa42da0f401300c01e403100030700e6004588a00d0103a00c01803401c5640c203052040e403601014a0a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 101807311 1250 101806061 101806063
    0x6050a0b0a021203070915030b0405100f0501120f060f0801060605090906010c0f020423010e0f061002010603150509061f0504110405040513021008150f0316270e 71
    0x2001d0300c1c10655560717a2501000c413030880d038982141622800d03103204150035a5064000303400001003118100600d071268004518001540d1281818051030b034a020001e943c000c5292200c101400f0501107010901100c10004941450b0002910427008040600146809100c0e09015081c54180b0502c0d02d60700d074002410364480148400e0402200301c02070000c01055414080800b82c0c00340040c08895240c41c585030460030480c4148040d941d441e00001076001039800503e0090a00d95001083e03611500144044a0003415142d815992a01300001c005080303030741040986140800c00280f5820000102802c4c460003900d2400b1003034442117445503100301e50203064203c40301100d00103040c901c2e00c1d0310800140182c0d848658030600d0602042aa803c0c0751100100d498403c40f40c018241080c0d12064031031804c00c5d03401240c1c001d451944041c10b070901f100500d003490801812504002404080700c803404807240c00c880f0200040b4441c040c0502001c2c01c003040f001c6a8840b00340882198480c4031 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 101808561 1250 101807311 101807323
    0xf1c0c020c090702010f0510060e1f0804021c0f030806040c080a0e161502060c0307080402040c05091e0103050606041a1303150b09010b0c060711010209030a0606050a0b0a02 76
    0x442c4614800c1c408074680301d0007580800045418101c05000c203103040d054021145895126900101d2035803d900000c1d4a4808a08502e0440400b9010b040d003a18620481d15108028422a04424185960054540d18a0a806c045d521606035440c01d01c550385802001030360050300c5d1030b000310b00f445c5e000c00313607a40c01c0408070390300400c00000051614100c44405107080d102510211801140301c002050514155804000089494003201c160303031240041481a1f20044403c030000602c0440804d0040c40d00e50881425400e1502d000350034458501d00003a020b90741c254002400720107006e250031003542c16001c1d0540c854000c0380d0450a0900d4421950302d101107030009900103260000d08d20410040c003030b103690065a0000788240140000790780d0540206480f0b40d440e40b0502880c8000a80c954a010441c3d03d164100c5024144c3d075220364205607089580d510740910295004d101c0032030907480400000306118050040468041c0c1381c241400030b00600c0707030020003c4000c00c010145c0060380018031 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 101809811 1250 101808561 101808583
    0xc0d0b090f061302130e04022403150307030b010e0405060708011a070204060803030717010f03020604030201030507121a01080a0c09030f0f0b01030b0f07020706090504020904020f0f1c0c02 83
    0x1d00c9528000030302540c0b00a1060940b40c0441c2e140d401000300300c0c1c42840319820710035803081d22003071b05160300460b41c827040798100b400a10100c0d01c10000142070000300d1013800c0f010800901103581490b10399503a1070552800b60070000d004607514080105020341040307400d4100d0128240f040d01c0b075040c15001c4808080c805415520400002108030854403030b54010b000411000080c1d030780328202060f008003507104031000002e81103030700750012840c4084d210f40c1c10212640104000c1c6428075541c0190301404c0001c241c07a040c0a2208440400c108450042d8101c0f013400d80202c40d540e0410500261044502070302c8a2a00c46c0750900c0109101d400c08000010ba941100c40619042c0c0146070035420a602583e004110f00d002c03900005c2001152240940500b540e1002d030b07040da90316000202da032398034184075078000103c002e20100700d1800d2036801000c0e041c002820151501600104440d1181d0012191602044000401d4102001542d00070710040700403810502c001800460b00950320444458 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 101811061 1250 101809811 101809819
    0x5030c0c1501030f0201110c0a05010c05100c030f112508190507031b030210020306060c0f0a0c0b041d1909050a020108070201061a0c150c0d0b090f06 66
    0x2000c10844204209000021041d10030400466860f0310346203201d04a0707040e049001c81d000c1e91101c1064000419101c01c074030300240030282c64620340b40c011207007048202425949402180195a0148450b024481041d01e0036100440c508490301014422100b031348224000b0301c1e809011041c2c829280500306d0f0501060700700c2402990708282805d506906c12018480404190515602d17095900b0101620391580251100c40f14083c00c40142d08040b803c48100a006801c40e0300c610100c0d6000b40d01454000401900d00b9003030062803a0041d150000c0100c028800741d0121031000100100d191885020706103a0b00c0c0035040601c0e100840030110002c07030050300f100a4420020304040004003041d106483c15a80c140140034050170416212513140405034005510040080c21403401401795408455000e040101c442c1d08055101030a5000300880e48440c0c0242145218896800710642d4024250b100781c0aa0b01e4107100142d01c200c0348011071403405042c0103400c105031078511400700f5a0207403080e9 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 101812311 1250 101811061 101811067
    0x206011428080a030c020f0d021309050f0a0804090509010b010c060b0301090606030623270307020402030108030307021605010806100905060f0a0e03030c0601061809020307030e15060105030c 84
    0x10814594080c0d240c2044003180f043c3e101c04014141e002c1d1480d13580034000daa034140320600c40c4061040c207420056020b074001320040d0005500302d01c154417017400d841c000c00c03d60b0049400140030605000f080c00054802c1c3e48007140134040842c492107015088410b5100070801100e1010000e08035003030300900600803603503507180d410198400303400004203140e11840401809849141c44d100500d41c481c1e44044a01e024084000c05a0703010040502810001d2030440d800440c3c0442c1031115140200191480e00081c4025801a00c650024501030100d03440950345906e4040d1000b8980842c400c0344a04110100d1010022640c0051055400010965400c1c8200b55140000e64035074040c0c0d4041ca40140740002c80c4038480c101580640300c0241e095076181300e19500401016607078080e440c00c01165411031300040101c80c2c040c00440075040b406003282d82100d651250600c040b41c000329501c42c0408d84804107550a13043c01e0041245c018602407141140e8280140020031f0703400000d1100101c00000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 101813561 1250 101812311 101812369
    0x120304050309040f021b0d0504210204021201210c0303050903011806051f080303060607140105040606030b071e0e0a03020607050d1e02060c18031b0102060114 70
    0x20300445082d000050001d1042d0b41110000d9002035212402e024608403082d44904008400031805804000c40384da03443c2e04050600c0c0080718804010320000c1e4507031044854040042c2c455001620880301c101d00003000c3c0e503240086400038078a804541c04070081300307203401c240003a074150603500c240c030340620305280c0781c160340000702c2d0040604020009210398442c102400304015900001d1081155511100d1755aa6070543c1e641c0d00101405400700c96042400000e0b018103003400a080b0882c0200c4034401d5100070646000d003120821340701039130b070540c541100340203000c0c0303038802103402041c945015030080484d9014001c08001840d004070030043d07103160310182691503040d42000b85400505181d07988030b1618000b41d44025414002d0041054415140e00d0940211000c84074400650050440d503070340c20007584040d0348000d4840204000b1258025070380c0d1810000c0e244640700344140e101440a441001901d8450b050b40220b1990070f040305900b410740c952000000764090400141c0305c90b1108 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 101814811 1250 101813561 101813563
    0x305030307050a0e030f0a0c1509030b0907031406040209060907050703080405100c0504050a0501020109020102150c161101181202090c1905031e0622090c061106090106060212030405 80
    0xc44e08990349803240e1081c8050b840008661413003c02d2180c0c1c0314884107a070700c5401084943c48080a100403540d01141000490418940d440e840081c545c2500e0803181c4950750310041d109200380e0b4207908c0d03003c0400c220441c10456609604410121419806850314010040c140d21030300400500b0880000d02080400074200450081d0200b28401403116040340c40000300300c4e402c01d00c503040c4203401000300090315500620800360315680680c054408001903411035241c02002400c03041c5a92010814600700ba0f48a03a110780c281440b4102030310541118100050001318040303800903448124100400850b8000550492410750540740c1f1280d56035400d03061110f5015000951340380f0b02001c69203194880d44071005601c992410418101d4000c0c015284030000203049883c1500300702640042c8460f001019418448c5000c4a80c0115500c00340e565245000c0d6219803041d000300fa040107a10098036824050076620100740c0c0000c0000070328002e4020354840056a1508192a0000c049014800 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 101816061 1250 101814811 101814827
    0x80307022b080c15060a0303081f0305010c0e030d090b030a11070209010f0f09020f0d090206090a03080306010e04050603060c13080f1006080d0206010302101205150411040305030307050a 82
    0x14202c0001c5440ba400080c40c151505040005400002071160000e1010318002542ca070649806549064023690751511502040030004010702c10004445000400280d09005010b1947c0c6940d44801481041400f414031344909100084103000403090305100c0352604009595128114040114450346012000c1c00c941c801c203c8080c0d00400c3c3c00300042840c040c07098001d012035598500c50742016985101010803030048120030310110404200071060f0302100e070030003003426000401d0249403401d82000100c0e01490755004444400c80441009174546e08100148505482a1024080c51070901c0009845050003040d0030403401e0701003100f41c00122103c0300c40300580b50320070444800c1100101c1e4169141c0502000004d40303406c0441c0880c4805010a00044035a072940013007469034259401c0002ca4001c1030006c9040001104155103400c0450040600440c0c050041e803007041506000d000581e07030303c2442103101001c10007080001901c0041202c1c0d221409192040e1117041040c0c085031808 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 101817311 1250 101816061 101816063
    0x1106090409150203041a091515040f0606031d0606150f030103030206090d0c02030604021018270b0105040e040204110a05130608090a0201050309030c060709060207080307022b 77
    0x1807a10540781400c820b070f000318001d5001d0100301e0010901d0000014884500310b4140405821075110314054418414807590000340c44040c0b4484c0032403c0010808890440ba520f440c89500c8000404c146501441420202743d4481e0030b080404805115455607683c0c09004503000c2d543d605014601a010700003992022950a0b02d541c0da81d50792810025519038017555002c000c3d00804e401082424001e42c40c403210076a0103005805259503039006c00055500c0c5043c03803014020500218148180407403044000381c44049184d00c1e100d80215250030140f0310702d03585482c0e102c0c541104000b00380c3c0c200041c0c074102c4e01c4822100c25a80d03243d1000c03c018060318248103810032404650f20b0039881d04100546500818030401e203525642d80c0304101c40c030f2503082da481c0805803c080400005548500700032769100d9014412a40751070040c40d4000d00d03068049401a0000e40103903410b1100640c1405080300a000d0386001314281075041c0c0009000c40c5c00e44015100c00d040c011548400b44404071502e254007 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 101818561 1250 101817311 101817323
    0xa0f18170a0f051b0d0f030305130206030106090f05030102121b1312200108010909030215041101170606090d03030b04240e01030510181403130902071106090409 71
    0x4a0b800380303001a07076004000240382000244409043c0b840c14103d4034180319507005880074803040b1b55074400790b0081c10003528203400351020344400d40150302c1d0540114000d140c641d13142124180340504400e00104190041c038403a0740100451007100b4403840f010741d081107000c0b070340f6001c03803000113107116079403092240d40c1c2e94101d82c428000a050341c030303140c440c20110300030f511488102e0310400700c1c80c01210407a000c0d540030030310f41001482899100d501c00402103209004950300105000b0034402506001c51b0f040b0703444102001500901e59008850741100100000300c0b0381c07103040003400106640100210140240c412045030414180310b40c012642c051000340041000d05140401000c0a07064241c414280460707004001801c05807400c5094104d940110140c078421031340c008008040c011102d5000c0301c01290b4190640402ca5a0202c8110130030f81c60000c542e20845c07002c01465145203542704c101c0c62072050110340040f9074031282e0107465820464403c0c0d075942c1110001801080b00b840044d042d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 101819811 1250 101818561 101818583
    0xd050a050106031d060c1b060408030403030e0a0b010510090918050d0c0c0b070606170d0f03060302030a02040c050d060902090a050a0501120b01020705150a0f18170a 73
    0x180900551005060398855602030003150303614800c000c040a40b450b00a003a0741d0000340051800315540340540315001040031503554818021081918000c400d4609403104640001030008240e018400d642000142601500825185850b1078416040521505008010a16040c0c014600c210700d0701001c0c1c4a141b40402c4481c110b00741c00903031400e41c82c01c202c808e80b06651404c00401e0064000064180c3c0c0001d1991000d0700341004441141c11000040b01c500f45c440d10702080d05c0103c445038500d14130260008090304914800010487c0c006004c00b001803628242040c030158601080c0c4400700c9406850110305140400c8040310301e40b0840702401c07005441d10b00080303551085c035002000d05003022145515000d80b2401040342d09030f59840f41d1400701d841013400742c0f4100311b990042c2d1104001401910032480e51040407428485c880c480301402d04000054880580e41c100c031500400d13034114030344420000c0d000da0318049d03140068001e980102d03441c60b4200c50303038040070488030040540c40f59140103 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 101821061 1250 101819811 101819821
    0x5030a0914060403080609150f0f030102070b0a050c04260c0306090f0f010e0a200d0807051c120b04061203020304061d0609131d03090301060902031006030b01050d05 73
    0x2e200c0350161800c50005c2c1d80400407400900e401c410f42030083c4030380036500410b400c0545c10060120032a82c00240c002e0840d52282e81070703517000e1004d00b50040c041c1c8003c00c11880e00304034150072150020300310380d0b4210083c4418803103080d60720588214096003990f41c0340e1082d580160146040c400c05c0440e50b1600c0f46d05c04202030341201182e543e4100d59003904445038622a0000e0500303803042c240b8003410039230200e0741110100d010000c0d4045503284c10184000b0f105903032408540040910300c01548c24030400203030304040000c1009012350103034648101e180140180b0700000d103010b880c80703580320415844c0d540307035280355480d680100028001d0580c1601420107a1801079103d8205e0b00c2a03601081c9441030755040240f03500d242000640008141502d009031701c508200707100c40042c01036100d49030f48420020030040c2c2c0c2d0407400140304002c0015a00e0301c010070300705401c6d03550b1904400e515034014418058100740b2450800103035562802c02040c3c50301301600480d620301071032102186042c10442842 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 101822311 1250 101821061 101821063
    0x2160c06091401020a05190311031216030504150f1401081606080f0423190507091404080a0311030703050703110a0203180111070f08070509010503070605030a0914 72
    0x240c1241d8540b162449401001001680c44202c408000f510a0304600c0c4045400f114010034220880d12078200715441003503070042ca0b45180c114000c600029010b283c01d01045070100e1500c50f0b02115680380c10300462902d59500300710508043e4203e00b00d980c8400f03000c0c0c050300d800d030000003001022080d1146d80c1d41e51058019611001140000380203025400007207070891180c6186031040380550145280b0b911203950b00880220482a2501c403413110303021a0303527015400d00440604150094240c400b036140d80c1081c50808419601c043e20712407520380e01c06400810000c209a0050f000507000341c5619001c0c10a5010706400e03c0108100700c400000c0103501905548000e003e13890079a42048868241021035a241c8101240351016038000e00541201308032030003810003820030601d800c1d81c2001510800a02c1c2c034034140c00c50380c842d038441d0300e082c01304c907008100020007044100e6225083c0c0d49010003194484801c2c1c005e000c00c1240000c0040c1e00c1c6a1190081402141d00c200d002c408071a02040f51 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 101823561 1250 101822311 101822327
    0x5120d0315050612010513020307020d1103040509010305102a120f02030f0f130201080a090c030506090102040305100209010f0f030212010b070201020606040516030b0109081015060215060402160c06 87
    0x46d502c00c0045000f486009111b61084d2072003808690002c24401000301c0c0300713640300700400900c0070b4184010000440c240c1c485415690003144100b004007180a00440700b1b605490300d0000d850005484000f1042a2000d40058000341d5406801c00c500c0c20041c41415201802c00d010784900950300000500c2150b0b0012190613124542c0d40d0704800c070a0301d800300d50001061400d10040d00080c002c0000c110b08407181e0b44844251803181e101c41400319543c1d602c1909040041324a0311045e507002c502081800700512054a510f0790a1400710300d0214000c001034030071000329000e403080244049004220b54002d60480381c049280d00c240307200e19a540e40c1c0c003094551206c4000c82c0180200700125100d030400b4041d850040081e00d00002c2c0c5e21034801030442c0202a00d004d45030410240300400201e214050000e1020fa80c10a1400300300f00720308228000040c2216031090045500c0b40088a21195030020f2a41c0c1280007220003581d1100510403400d01c44c803c025024080c8018134030001809900101d031 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 101824811 1250 101823561 101823569
    0xc0201030f050f04050f15061c0b042315010909030909020f0703090b03070806120316080712080c04030803060f040c080105030d0302090a03060b0d1203060f05120d031505061201 78
    0x11646c00c000f000442d43c1d1a41c00c455202031a61482e040030549919040a03251030143d41c2c0c180303400441841d9144c0134405c1e041610140c030345d842c8095007241180066003008860064034070041030441242c030a41c44a03594140701e502c078402d0751204281e040600c00c603200c00080004034000c0d501c0300c00c09011100554403200048001c2026100300140d10580310301600e100303603040c0e11f0f1070b80e42d03503514800c0c80710546c915246101c2d58003041000c1d4070003460001303041d1000350103a44483d841781c107945440c80300d103007280d9440e60034044400b00708a07074803a150003202e0a50703510044043d00da8541d000071403446100b640400e50301900b4501c82100c45035000d58214101c82c02201110204007840f501a400c911440100ca600010149070902c0440c0e0160001c10300c99501400100e00d410f0151114106010700d03600d400c000a850344410000798004880744009003d080700c88928552103084400e9035545820302c03840138540ca81d0641030000c2d5039980110000c24000d004240d488a64554180006d074090107 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 101826061 1250 101824811 101824813
    0x160804060825030e0705131e02030f040609020301090218070e0f030c120703060204240203030f04030e0307030b0703060515070f1707060f0609050702010b01020d0c0201030f050f0405 80
    0x10014000050b142c5100390b58070100641400010300651045026007421850100030340300b0001c1c0068180c45154604001c4481c8440c00104082440054091a400900c40c00b244900500a0024900c44101003d8102d41d0013180050414110300c04a409403040707640c06988442100308110031020f54002c0f2030b2189019035075070603031764030f1900811002d690504003030745c0c05910910741094113060001c20741e18200008012a808a90b4958450040c2c0e803054010b0300301ca031042d480003548004401c103021840c07520360001e1410343c600400c24081290005202a04001900210b00a0f5071418803440c000381d03070000030380704052a2852014010340708070301c01c00e4003a5010480301c075940303034800056614469100011020000094464428450a90350341904e4a8001c000c5d00f07002039441d100306d080e411207102c0c02185091420066901715180140700c40103590401880303600d9603070b01140e010f4842041b8103050349a42d00d9800120018652960024901881c20040c418840e641440d894441c600c140 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 101827311 1250 101826061 101826077
    0x60e220921030905060106050d0e01050408130b180607020d0b0405012004081507020715080f06040b0f040c050f030112110105040b041802090d0f030905120303041716080406 76
    0x74a04038215501030401800940004006105040c8501c0082082180c4040041050605805840d0841d0380585089035034140019205110b0b0b9800001ca50040080100389400d00b403400e442102000d200703008040c0f10301c00002c1c40c80210f41d0f5100007005403d4000a2000c01440d051030101c4c02410b20214450420070050101842c480d00c2030110307016500e820340035040318080c0e03d0000f800c0380e82c082d21203015800b0311702c00810444102c0054811b045146d65034030742c8908160006403d0340b200500200d004500302843c1001d5a110311003000700207042620006000c07011800211140d020329800d80c04800c80c00000004d00c40f07600202d141c616401025508000303000b80005550a00c5039100b0300c0040a02803000b04041c040d5481e01d100d1401001001602e803046510000301c0f1040c0c0f40e0f1013188c00300880c42d002c5c01419404060400504800d50fa148510b08004000c0c80d564040140010114480e0202c2c00104480100a03904169104641c4161244a0385884075080e013050280c103000608103 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 101828561 1250 101827311 101827373
    0x103090c031a190b1302090f130606030b0607031d0310090c0806131505061906170c130b30040501110901090303050c07180905010b0406060e2209 64
    0x41c85003014103000142580d01070b240820040c03001e0340021f24a40e0f40400e800701d20345281d4030340807416049030203070110000f00319007000740c0541240c42c00741d8001d001d004140072100010f43c00000c070070f01070325003198008000001600003a10300351103010320603a12803c1c60103460800c0030f10f0815005071202d420640340d081d80c0b4600006164020250b01400054084824010a0b0119804150000405001c504002421542102001d200e0b540100005000792143c2c42c03400d40581c40581d0082a400c600520b004015200c0c0d1191103140d0085411485d40080c50300030f5036011406808140c1c1c000e2603881c8494040b480c404104080490703050b6061f50a00c81e80702503c485402c1100e00030305050315150b40c9581991412109d58000d0b900c80c940610a48401159400d00c008451000d14400c3c6000300b2600c9032858240e007584d0070511854003032801d05005001c2e4940181d2002c14205003511741060b0440300c1a1080c0341200c0001041c4055803406c2500414899100809910030b121580400e4000d000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 101829811 1250 101828561 101828611
    0x10206130b06060a0e150a08090f06150402040306060609030314070b0f040201210518060903041505040b070303060302090c0a1403060a03020a08060106021507080103020103090c031a 80
    0x50003081c0180300400141c0c1454548040e080300c04242c500340074400d9400740812280c0f140c0c02c1550480580201d4441c40e1941d00400c000d9101c41003c010303001c01c04202c146c0542d60040a03000e8000400362a5595810752a1507059030020764020100703010a990b0f80300040e0003400e49000a8000415140c2041c0c90300a01008a407100c1d94030005d140302503626040c0c2003080501c0075000301d041200b4640c060720303010700182070444800c3c951100050385d27003420501c81c40c190051140000854101c5001c1140000002c000e8a0440b40c0c0c002c030200420a80c58421541882a50010301549038082140003d05525500c5041600e00c250303110121030711411945052070140030302c420000f848002d030010800c0307421400303547c00c006c000d4800c600c0503440b0360009420f03545c940c00a800c0340d03200c0d00040103801d90400c04183c0b103164040e581d202908040e540248118014040031f03040c5601c44001d00201310301001200700a6401c041d100300140c1c0c442600410400c07007626240340c40c4c190b1019000702c60321 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 101831061 1250 101829811 101829841
    0x7020d152c07150905010807051b010c0914030c0904020316030b06090a090b060103090312021b061003051209031f1e0203090703021e10020a060c020d0e060c010b0307060509010206 79
    0xc0c080d02c0b130b42c5a4904d0038004440d803150041c41c0b0420040107201d943c0310701000d1100e4031500d2200900120b03410034080381c001c6c480111513001c072620001641c58020704c4c2d01c1c00701c0c80341000001650508040d03502d034000300e0b28064207c002542c0301409280c001080c460b0040e40039000c1c10341100c81e4405500d41072500810f84640c1d12000d440d07100240c01040745c40d03001e58042c442d030b00c1c130904090341001c809558140403a0088200d007288242602002e8100980900641e5032004440c10303030240080c1580c44869a03520a40b5841454a40006840c480c3d69002c00540075101c02003d130001ca1001a140080054884c861091041010030021a00790f5041da0099034070802c81c900003041d580f8555020000307003080c06426410b0800c13201001000580700d02c62070400e640c5250b001040700071207a140244c129a90b81159000b150440030304103000d2a4041040b1080d2842215025228801c00100d280181203410301c081e8903204005002075015040300c040c022a0109809440d82c5d9075a00d000220081 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 101832311 1250 101831061 101831099
    0xc0306060f1e0417071e0e090c0a090c0809060103031b02010309060c0f090806071409030c04141801140615040e010b03010302040e0307020d152c07 65
    0x1034414003085001480110140c20310352a5400d4030b255400b0300724141c0b032003a0f10980054924003d129481e80d84040c0402002c0b00420b52000310b41440700340103104c01c0c82403403503000340e90030f904682002c51441282000000066503008009401d040e503228501030003000140301d154045107508000440c1c070200490620304803600b5072100040c295510302400040382169008038141680c90042401051603803090b001d0041494886480b40c0211400141c4180d40b05d40c0400c0e0759178400c900308210709500500ca00310040c84c00d20410b845411450000c3d050011a040543d001441d002d014040604100c4819009060744002c110100060451803420b95401405800d5100100340c045603460410780260351a1480410740b55050603124400c607034290000f039220070b00080021006205610703080c032079410386d261464011807a1842642c00700c1c8800d11900005080c4003495280c10206202640142100c01c0c59000622005650084511303000c510968412079188256a00410b102e5100c0c00340000f0030b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 101833561 1250 101832311 101832319
    0x2405042003060a1104030812010f080304081207020a03050303040b0f180c130e0d020a170c0c040921020f060709080616030f06030f0201030b0901060917010b1807080c0306 75
    0x30380d02d541c1440c014102d10004d54480c00e070100000000700c0d40403401351403006016102c0a803194500303421490350112542010515410400042100e61400104003280411817100241c85001c00e000286100140344d03c0508240400810001003110b8110214440c170031960400c40c1c40d45480f43c081c3d4444a80c1451031020760300407400000249003003500404441c403000404583c00000e00f04060034245141d000c400941d2280c04020704000d428800700f1400d03010754100340c0c10450704002c1030b551600c0309008035020300d0b6181245400e22680b48100c4d81d4540015920849851050000942d1030001001407c1030340255008210f603144900602c034125209080284050b868420b501580782e0207240083c0145a5a42c4a1022100082c01039200850141003000e140c0320403400054180c41c00301c04518854040b100052000640299412041e121a82145038280c543c0443e480c1c014030074490340302d5109002208818521810200d00e521610a596480005459424100395540010784001d0341c4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 101834811 1250 101833561 101833573
    0x4060f0e07090218040912110d0e0402030a0608030a020c0a090506010c03080c0403020910030203010515031f02070c0b041701020a0503061318080d0c020708192405042003 75
    0x20030400780e006452102c802c04400090300031343c0800a0f0444040010458088142c107044180301a0030600e981b17000c0003088041c0441107140d00006010000161003180705a50100229080d49030541c80f0001503c2c0e00c900300c0b981d0380308041010755107030720394440144900c174024000704500140d80280d601895042c3c40b40c040284290390305540c81e03440102980580ca0041c040007025130b0314940d500340500c149103600d901d0582540181425203c008003041d699101c9003440e6001602c0004031540019020303400c40c11424544034850020380f044000107006240c0e0f42a003c80d0a441e40ca0061084039604421090510140c0a0ba82d090b8024038181d80045030080c0009803050a002e28464519a00594005100e95540c03c4919440d40210403d07201d4410100f8402075041d06840b4030b125441e00e40c002011443c1c0781810603980e820b000614110b84602c40406c0d00200090007501c40da5010f50849209035a881c121500001888100c1741a20184d1305110402c03240314010342080c1d1540ca01a000d400 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 101836061 1250 101834811 101834819
    0x50c10021e090607240b010c02030d0f02010204180f0e06160c1703090c03010e0a050619021e0901030f090b0a09020a0801020c03070c170a060c0219080304060f0e07 72
    0x10242c0c11454445030441000c02405000411110f05041c04e640f582d40800d00040034111150b080b02c1c00c8410304ca0501c0290004100580d41c0010b648005a640d46422050f038000401c0c01c0740603004a0f403000c0300102d2000111164000740c3d4200010318442100100040c00315442110782c0ca00c001e8502440100d80b00086000841c4101d1081c115140968168a00a051681c0c060303004e5000b1255400240c111498000e590b180070f0140304107111941009101c3c2c10071544440c2e40f07520020f02900c0704442800700400489545070103583c04000d001d0403000e00402c4487c240403003903001310501c07400a0328010002d201000c0750300c80c1d400c03001d8001202d00b5083c8d8030701c620040140354035001640c1c030414205000aa5120900080070b1341d000e018083c1da00d40c41c680c64080c8848000b504000e0140080611582803a480020050201508104d011486882c0110140d007491800c007012891402e18443d0744042c01400d01c01580210301c141c804024044000c5104000ca800c00c0c2c00da81c099811042c400c02c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 101837311 1250 101836061 101836117
    0x301061d0406110a03021e0306060f0d090204060305060910020f090609030a02041806060503030406020a030507031e0f270504150924060509030726060106050c1002 72
    0x10303078850300c64007000581180c2001103024507080f078005040001d4001500c048103044030464108030a560303052080c11070802c07200040e001c2c0030314030a2404080c0045401040d40295400c40c0d0071054024000b0003005032207040064599000700c901e00d40512138800d408200940c603108841180c102060054180001c010401c2680e45c004110a45d140c49001604005030b503480c4100080700c458481c3c81c00d290891841e020083d01d00650100380700ea0030502040041580100b04040915410720b08296504c6161400742c45501d400921000e120f4081042c0d486100e0b00b1000c0d050360300e051a00c8801c450781d80d86900e9040100d0841b485d181046c1400010422410140c0004040308804c2003200c040d95110400041245d89603252900c80c0c200100b100d0b02000741014002c0c000e40a20b1134910714000303542c004a40d4410f0036200d100c03400c024414500050321700d43e0008284500c2120305481d503959440f1401030030780e080312454070a00c2c000c180156a200742c0900c01ca4918240305000481e413511080e51003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 101838561 1250 101837311 101837369
    0x603060e4b06010627080303150d0606080c041803090e19110a0e01080c121510020c04110903060406020c01020405060a030e01050a0506091311060a0e030606030106 72
    0x115501c0745200e101e45042009000e4107010306101d0f03859440c1d080c5000c80e4102d205050303100341c2c03100190110f018000082c1c0071041300d074403d041c681a0a0506d031841c0214400300540100074040900e40f1101041c80030011880c13031000c1c0400c5400b40030100c004010307052034200c8503d0090110300d03950030400000184005140d03211180c1507004217080581031a40c42070381c1c0500c4042036160800142d4210064100380c2121740b1150a203000b00d003030300d4000d60b9503240707103e0a034200030fa4903a0381e000200078180705904000030200c0a00450800350007044080c0d914030800ba0200e105609243c041051401894241c94813008028000e01442d01d85448242c025070254120019954003008081034030f441e4207000384a041003950b400180984000420b42c00c540002d418008560304040074403009070b07508154190008030410842605000b2454440001c0c1070003594107030030a20210700230038a942c1107010354819010a40682c0d8103961014201400c923500e9001d2520f0340e0300c4109900c08890a01c0c124 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 101839811 1250 101838561 101838673
    0x2180d02031c050702120706050f0c03070c090b0405090303071209050f03120103060506030a0f0204050a201e070b0103140c09180c0a03110103020d0207060603060e 72
    0x140c600c0b4210003030308141030746070054110021a10014101d021400c04c050342810740d134401c038098940d150034a000103101e407241d0b40045a4004c000709250600d80d90034800c48441d00d60140f00745174140da5900489001e0081070103100d119524000008500c1000441107d01c140441c3c2d9495091200b1b00b020100180642c01c010358451185080b4151002c00410081c00c02c04505143c5000a40c5540f40c0141610030013455540070350040040c4400007018050300c1a041a0304031000301e0a030380c44580030001031662143c2c16010615840d4420900c0ba2200000c1080c030060201060440306503c607000400d00c50380f80c00802e138644c40c1d0010004907142c0781202c05041c1d0400150355260700040300041d01d01c40181c4000146964910f450000c0d51030400250920340030585180140900d035032242e100b25401d41c2c00c51410b00d50001086d4207851115030468103260707440340e020046191a810714030010700030002068814420300306065812241030310f800c4061030507188081c500000c02a0210310410328104 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 101841061 1250 101839811 101839813
    0x40e061602100218132c0f01060305060f100501120203040303150603060602070503070b0909070c080c061e19050603120f0405010f140403030f03141e100e0112030c02030f0d090902180d0203 83
    0x5201c0c84802c400c9c0500c2c1300460044008120a00b41200707001004030000c2c10144a0492001041280381d030083c40390851590000d0700140c503035580d42402d4015000c84030f4903202d2002040e078046035068166106074240c2d40550308031802c0f2034954051542d94034680c0210544210f050096070380601d848030f4119481300341c85c9003001c2c0851084d500c1810715040b0360600d00042e0455010400385005844110341445003034a514071460605405400e992070f0803101c065481511100000c0c03182c0c400300503500700c103400c1e554016900c41402c2480145600103010789400528184101c08007d440b0302011825014030404040c5014030315503064800f186600e031030505140e00e132140c0d501d07a0100c6401e503074802d80300c0c80c0301818562007203840040031079401001e070501c1070100c4500b80702002803c4c100ba41500c0d40544c004422691358203090307407a06050072000b94148500003504070382d20030215482c4401d1a46845480c000381d11808498140d000f020f104c1d0000c210901c190148130318200c40c503101c200380098 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 101842311 1250 101841061 101841073
    0x8010218060c1c0905030d09031208072003071209030510091e0f0b09010e0c0f0303040b0415020715170a090b0106090311040e061602100218132c 64
    0x100c50211002c0c0072410200100f091310a04201d14101400081010b02c0c440c904034520500b140c1d64404000102d1811004012498002400b045d0140003850141c9404840d4031002c1440b03103016a50707940c060002260754141030790700a42c0580c01807113060107903644540941010311015812400902e80420203803100f01c089515032041e01e00c03440720900da41e40034428160700248181072290a4610103403032030126070b00d0300c5071818a00101080d100304c015402c4030b40b0186801e0040001e440c6016541042003541e20024001606a5001011608251050302a250100e60b900004860240020f001e00c0c04103141c0e28000400081004955621190000300010911180c1d125050500000d070000d00200b04000000c0c4140a40044945421841200c4c240200710290190f030741c654070050030b0b0801d01e12541c03150340806402403282d0b180c0440070450454403001c6141040303030329034035283c5894050f08400c5a84c210ba1a014001c6110105401c0c0340c089020130a0311007820305a250b40866412800f6136 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 101843561 1250 101842311 101842333
    0xc170c060a030605010219020f150c030a030c0206010e06010203070b0606160b0a0612050d05071514040b060d030906050a110604060c0e030d081909060510080708010218060c 76
    0x40601506569903030000f030f03114204000a482e000342c40950515003080101c041c0f006170348410240c003034140d0a071403100301130708004046001d500030000c507040f0502012941001d610780c10b0703100a03030703018250b402c60302683d0780c2d14500100114281c0f00140140c01c02c122500200d402c2055560304040c01619841c542648240c1e164200d4032005001c8030901c02d860f003800f09603802809020007421800c00314488006007035032790550b2410f20407030036405e0160100d030400510203622030860215041c00000c0c0700348c0241c800c11100b00e140840e001c90314601d08001081d898204810768205e5241c0c191141a25036080c09000e07a402d4100301c11500c100003034075102c4000d403281801014020f510402002c50341c0703030b800311025100c1089640c0c2c080c041d901c182020039199500030b492507001031050903548888450002d002c230240883e00005080e150038002840220b9118207882030480d2440c400f5601d4498440c17641d2800d03485020070110a2a500c10f010f0034592508000804498030700c901291380b26950 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 101844811 1250 101843561 101843569
    0x3021b060414060705041d150d080307030f0e1b0f1503060310021908040309030b0c090f01030e120c010e151b03010e150301060506030a0c090e040c170c 67
    0x3224100e035402c0007000c5a000c41c2d007080040d84d40110b02ca060060419040240c407403c043e80c3c400032000205031080100e0322805080020100c2c0520242c031004103492141080f0a455005841c44000240f5184140544241c288141e00460210001400d5103408614590140c4000400c84d5079122103000c81c0000a599003032610540c842400003816181d10f4410105401d01c0d0304d48001e880d9032401009140d0090003804a840e140e040c4c0c0f070401031500d4a450404407580c0d111904024403040714002800007400141e80503001ca4602294410382c01c030003020045003540e01c03d52032141940d109060003550f2049a00250507101518400007580c503050300d401c1850483e0011170490300d0044041801800003040e043c03402c0315048408014039551400740c0e5840c55a2000b041d2414400e0000c030103445958080d008040203210082105d81c030f1b800c00d44404002000c079510344c41c01040303054030300003001150002120700c034603003001004034020302d403841c800b2003100d0030541c000490190303880c42c400b540c0d2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 101846061 1250 101844811 101844823
    0x801091d0f010921050318010e0a06020c012405010f0e18090d0c030503060402030405250609120503030403050306120109051c020f07060315090618050601080c070303021b 75
    0x907900c000403d03404281c1c2410884501300d851410f0301007100190300102950031008407900540e0002c00e40101d00c0610715414014007028032000118000d03101c80c04240010380d00509a101e181e40d008001c40040d4414400105000503980e02c54003c0c0c0140400040d805860a50a018054180700c582c1d0400640014007400c1d4100021109500c10410300071004000c006100f6400c080307040c004000c00807524040c195000043c41c407840f803900000028200181400805c407202c0390012480014958010b207004450013600500c0300148048000252a0884107421140f0f00e4025016500e0740d00c80c4e440444031944001c003815005400d8000b14121008241308101c4564003610140c44617404d04091828101c0040d441c0204540c04070000003880320300480c150f8111049400c002600704200144107880040503072058409a00d0b21100041c200c400c1d86100c0450047c580040100d55507100065845480582c0c50385c0d0890b00c1402000c000a000b40d0080c48802103c1c40400c6940074600340c601d15002d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 101847311 1250 101846061 101846083
    0x3070f060c051216030c17130f02030109050715030b0906040906060807090f050a0627230603010e03030f13020a0b0d02120906071710050603070207080c03030405010801091d 76
    0xc0d8440e0130a01940d051080c400590681e25001070707500e4091080880031440a4005c60711001a25101c03010014880310058000e039018009005c642c049042c002c1c3c44881398859031119a4034074015003521846442030480ca004001d0890503251a0101070200521002c00126003007983d42c0f101251a0b082003101b18020200d550b00825001c90031001601910b2004c1c200c3d14045d0b04140040c404083c0d0344d4031561682c5003c1124a0080c543d00100801500d031114020040c440c0901080e00446c00c0001d1407031040b1030a40080c44a541000d582a46d80e11044403072a0f402604d245c041658601c100c040c0e08000f0303000402c0e460a903500c4852800345507001e071900c802029030000c0c404011480b003400c050741c0087d00c0c401800c9a890258009803080c40078070b4040c3c8613441e0b0080000d00046c4649124400340c00080c0043c4e4407840d0446000e5920031843c050892284507010f011a1145400000c840654006035242c005a91a1070030450103010141c0c0d000d850400c40c0c400d401c800c40c0781080000d03d40 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 101848561 1250 101847311 101847331
    0xd020d020d020708030a06060e090f040201200705150403050c0907091a07030e030703020f0622060801170102032a0d0c0503060a0803030f0f2e06090803070f060c0512 73
    0x44e00b840460041110100c2d07000c2803d0100449d0f40c81004d9407212800c5a1080a444032114190396910040324030782c03c00c2c40444200c000300d0010340c2c01401e0006180056880079130310040503408100341c110180c06544401001c0c0d0307205241c0f81146003408241e9580002207414204481038442c044250204103100d00b00e0701e103420100b10381c0c084c56444407501c036118138150090246c0754155004540d45900b20010180a48800200a00801e0324000d403002e40c40c00b041e4244102e15240c00004100034020702c1055201d400d11410050303030a00c103100b2607006100b070ba0441c61044110386090103c2c0e40d4500403032281c1c1541030060102e00015402640d4403001581c1e1401e0341c0b0301d07000d0b0030840c1d801e0050b003054440d640240200301c495840b004565401584510b03888580d070f80c81e41e9042e0f1048a910407d010b217801001d00c40400d03c0a11900380c003d0703c00c1c544504034401c0d15004d015540b07002d4004040d01d624205080d610100d031181e0311100d04a2000e16042c1d2500f110744180d10901c010543d242d06203 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 101849811 1250 101848561 101848567
    0x403060c140a02010515123414010e0315070c06020d14100f0e04110f030f0f010b0f030d030515060c0c0f010e01080a020a210911030706050d020d020d020708 69
    0x26403100c03001e031b0b2020048202e0300e000e40c007103420000341e41e81c5210140914403281c0e421840f450441c24065201004072100d0807068119031140982542c0f19038140c252804038400a0310f4924904d408141c407a514400d14840301025944c0f40c404a40c0c0e091002c1c4141e134003c1c1e08115000541c02c1500510780d00d03402500382c0c030606d428400c003000041d0119500040c40b04600100601442c21401549a04290086903d40c0c402110f000000d828048120000364180f08010402c941c240d00454800e0070101c041000300043c04603c0d052110310389000c0406585604400300350f258041c041d40c090f90304a481c2c04a082001001500071071400c0c0e06c0324110301b00743c0e4042e001110951800c039140a0801e003003840d2514161701d09000107455101c001c0c00b41c3e83c0107600855130046040c41081c95400c40603c02001481081240650301c0050991303102c00c0c0d034207101c0105c640045040c00039500088404c140c0d566464184110300311b0b0002d401103800d03142426000c200c480f000101c04d001030480140220320041e6 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 101851061 1250 101849811 101849821
    0x11701091b02070807090902030309030105270a11040e0705150912012703050c010204060e030c040c02030a11010b09040507080708060405030406110a1b06120b060403060c140a020105 80
    0x114110240741000115485500300380b0500e0004600401280d503404c402191b500441c0c4002030540c0100d040041c4c01d036181c101004086103843c0f0005090b56204402d0f1040b41e41000d0620352281e00c1141d000d0849030f0005013603a55800d296020300502d040f28400e5440070794a620015080c00c0700041d190060b12404a050640da1405040340010030403900c008000406080e603610800460101e40011203160399044030041c1070060040b40d824480800085580f5629460054490528043e459019100751510b001030380c1481e1065082c40400c540085007444820001100c0c0c4890250024038195210340040141c0c1d1105a01e20740124070503409810304130304003071160f0711300005a400f88600f64011000d10000c9500030045a040e2901c914043c0034040300888410303c1c1404885d401040c42c1c1070600400c25100c031070300000060390260707510105900e00c07800b41182079a6914000320340c0000100700820000d42c107980040741140c41c505051507585021140b070105ca8001e500691f0140c1d440b641000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 101852311 1250 101851061 101851091
    0x3020d0f0801150503061201051f12020102061504061205010509061f030803042103140c120c16200a0f0303021c0201021608040306060506071208040201170109 70
    0x6220a4514056500b5071400d60901c1c0010404078041041c02400408140e1320380f521581ca0400e09031010084c400c50504c4414141c00302c5009000c0c40281101c0280481c0000140510000c0380750140d009000315118150103083c00c0c8c3c0c240e1140c551041c1c2c0d03601d000030009500b21801001c14041c800004aa1030000915814020021b141c4502a00f81106140301d080707510b07011405407a00034000644035599440d219800303c01380c4070007480760042110003034074495064202c0c1340001c814805000c0e49480c2d0f000e400101c0e0054403604000c011001c00010803a050764000740981c2e00c03e411511144200a440d1280c074a02c9002c0000480d8868055840340c504204841c00004c265a2000403030061454030001d459a582e00d02c6241d20341c82812044040340d00c01d4065550f04424950f0900325a030507440e100703050f68003d01c41100c0362424500b002440d894210251004c59800110b0703003014600c0c0441c00c4903900b0008104038180304148541450305556861524060140d6607000204408050a64 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 101853561 1250 101852311 101852327
    0x5040606030f05180a0305070c09050103080a090b0307022e0203010f030501050105060910050901020a021c0b0603030712141303060c0e0d02010509010c020a05060309160b0c06013003020d 82
    0x82079130030240c1c1c02e8000e41940c0040e0242003950185001c40d2078400601e00858808001d5015003007450410b0000320a001d0000c0013001e06020f1902c0d140301c020b541e4910342d11a40811038500300960031080300c5800d490048192500300d03c80144104001e65400c0c10210100e070800c0e00102981600c44409208101c0f09100340d9002d00022600e003410060341c60300180039580d03000568010040007040b11440750f40208500040b440e401416000c502200140c41000c0b409445029210500d000001c60034a060100449032041d400075002500c80c2e903810000d85007035030451400b030383c0010104400704884400e01d10244c081c40c860400495010426000102409400031009104200d9580004010303a0404c0c1141d44254083c01c0a22104003a0300000740109210b40c8110b030489000003c0200f498804a2418140320450f1008800c454547c00603800070301801c0c202d08034662207140148840c50003059469502d90348111184500340700c41d1350301c208481c2403580441c0580c0c803810360750b903460380c00c0200 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 101854811 1250 101853561 101853571
    0x804090216030246050708010203060f011d01141b03040303080c0a0e0910030209090a05010c0207030b0109110712020c15120109050421020601060f11060a050c0405040606030f05 78
    0x914000ca00342c1107076410b042000f00010604100000303c3c6904e609010542e0407003202d0300710081c1c8061680d1102d1441c040d40c0f003201c10f103201d8050840c84c4d003015070180401031008002011003c25648180c40190368080305007030040417507070007032008038030558000040c44506450100503544440ca10320300903068501c041c0c041000b1900910a6911142d880104425442e10403200c072001c549580d103145100c0845504003a40011100041200240c400105080440c1c81007000304407400410800b241c5502e1355000042465810900404c0f0450840e04204501c043c03100c0e00916040b035560303412090350320b4401c5a401681001041007050318001141c20141d40464143c249070a03c0c0541541c22030205000d44980580d551001c9000c1c07003210b401160015281000b05401d00c01c0c600d0019581d41024829034000800c1d003061811785a2290f5031900729161908014401c6031075108040010b00402004000d500c00c045c0000502c0350344038020b00c0e000701840d4900107804104607150700252400109 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 101856061 1250 101854811 101854843
    0x3030f020414040b0613030308090c01030912050915030a0f050c04050616150e03120a02070b0112140102030109020a020c0301020f04050d030c0b040c0915061b08040902160302 77
    0x802001034525000910241080c11500042c00820343d04c00100365008881100003100b9007182c0200030190090742c280c1c014600d0400312070a41558000440a071040088000c1010000781c44c60b1000c540240060407400f440107100c2c4008100c1c90409082c107400464030032280f0768840b001411400501d104441d007104842483c03524140c1418045010780c881c1c600e0031030b0080741c0031150105210706000c03800c001040401e01880440d0340910f2042c0d0f80c0d00300d44440d40551442c400420320540f07640c42103801040d80040f03c944140e190410101c0e00c0f8101450035125814640300c070b45010902031000b14064004402d00680317503064100020310705003842400c18006d0788100b2404180384080030a550403980e0880e034013000760190345000c60309204090401449041408240030421102d1309140c0c1c1540d81c0003a0030803443e6011480f101c18201248504008905000c064050b240c48254104810f00e0042194a107400d641e112000100c0e0b02c00a04000000e0301500107000b055030501100404c042106 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 101857311 1250 101856061 101856067
    0x320130905030306010c0804090f0204030212061b03060301020c0a0303061706090a11190914150d031b020315040311030c030a0302160501090302060a1805070b07020303040e04080703030f02 83
    0x1070340d000da60f80b00103000141480080c4100c402005043c40481e805084035001c20b00ca900308030700100c0040d400500080f0710034907800c0031074050a000021a644500e038003038100c3c840c1c500b800d10502e07032582c405442c56030955002c00000d255142d04100c21103d0621a540000703220380380a40949d10120603a8025026030031000a0196051000402451050704950465160314000002480c1c115000d06041d5003414021800200381600d940108801105a009031304107a176065080c1d400440c007400ba0540c0104c12105a1001ca031040d2081d85070020106000910341c10f0980009144c080a015840d84100ac954104010180c1c41101046060514801942081303640680c1503124054168031404040d0301081018424401303d500658182d0403000800c000c40341810300a482e14001c4501181540c1884e41076241d81007d150ba04203901e8100d4051300d42c1c2800d11900d51000e501181d0f044ea8544003d200104400300380b2080103000f98803e10036183d4815042c50003405032024501d4480b1400d1040c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 101858561 1250 101857311 101857313
    0x70b12240301090b0603010b0f0105030a0c030605090c07110402030103020d030305101809060c0302030709090e210d0606020f0d1803050f0f060601021501050108040312060602070501200a0f060603201309 89
    0x15a13800658110010ec2c5041d41203001f00c2c02002c2a5015030b50008a0100b030050a000c60401020054001c00c01e03000201c1c00d0200348002d922007171100942040008001a000c07a11036405190011000103840b010303c0d41c0d80c4889800e210000d00000301071551580351204100da94402c506062243e805c040d400c510b0202000f40c044041c0740b04110885840394001c5a80c0d0100f070204408220440d0f0426036003400030b01100ea0150040840403180e1490640c0c00b040a60000174010035040e0350000a1600b825940011158006c118810b1841c0c0b4054400100020344140b061010610b40d5070020100c507800c82c40c00380c3c41d20034082d1850b415500103480d54281e030f0380440c5c0301c9415140c007802c10031140c0c0c81e20719007203c6080c1485078400c841c03417400001003026540841d021040f91401d90303801a1100f5a01d8040035003e21070840b00380c665021420300c1001800b1030010090310b0740109400580f00e5580d8485a03a5414100e15040780002851084402c500d410041010004e4400c5010001c111003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 101859811 1250 101858561 101858567
    0xb0a030b130602070209040c0302030f12040b1e07050109030801170a03030209011107060e03070915050d0201050c010203070302041d040c0b030901060515030405070b12240301090b0603010b0f01 85
    0x10107810100042030205101041c0000340c1c048458060340602001d01c0c901c3c29050a01201c00301d400300302e00c0381c094900155504000040c130350f0080748a510340f080c40c0c40d16040e0701c2c101c564840c0514040c1000d0100060610104020207010942d01400000c80d90b255180380040c14884160000303400400b44110b10508420005012000c06034513060060343d4104d00c10050700c46403110b1040d950240304050001c241280e0180e40b01d01c5080003501141c2042da11081e40d81c041e61501c0c1c60646140c454680204618944030244490480c018103126140c007204288450999104840e0540401e4000800f0002811180707070b80f000317500c0d040342d00483c2814165100705048480d407003139030820780001c80030950783d600a6112200606008200c1c05a00c0c01040c0751b1a03040d04102d070107917218011620005521148441212030302c241d4005040201d54078126000d4201c0201c413900103074854012301f0034905450911500784000c0c0074407840c0c103051800404140c203503404d03058040d008031030540c41c103040b69070 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 101861061 1250 101859811 101859833
    0x10807050703031a09040c0509060102010c0503040204050c0708030703020c06011703070f030302090a032909070b0c12030f090c041e0906020c0a1203050a050106050702060c0f07060e03010b0a03 85
    0x207458940801e400001500444d800311661151552025120007400100102c50b843e610403100191440c164599448005a0803207441d101008003090302040024018901544256440713003091200340d0404100752103c1c64a601300f164110042940000e0f80f000842c400c000ba0760040440300055291384044c0300070961a40102d610013099240010b00c580109806901614051030000d4045103050b6a24113201c01c1940c0070607042c040d5000321044e8031107482c11815038544610185001803080a10709113a80c01e01c2c1e4000300d015260382c014214400c2200808000940c09103d00c51b0f88010780d401e102032950304090340c0320442d0780b03d103241400743c61400300c00e050305000c031013405180010720304580e041901c0a48203040c00d80c0101e014440100c001c00141c0c444048401b440c82e5401c02255640050b860210390080c001c400100304184602001490010024a1202c100a094030302c408002e1f1025441d0008541141c03010400c000c010450302c3c10244244840e04c64221540c0205038519200c40040c48 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 101862311 1250 101861061 101861063
    0x203130e0714160204020c0a170f03160c02090112020108130b13030302070209011e230402070f05011104150e1f05120c1201050d21020a0206070609050105060108070507 74
    0x200c404150b964141e68800a00f0320780980240095684201840000751101441c0c1421a45040d045112600c0c070800f401c25112030030440d910039031554a800f40c1c00c028840703004400e4410454502107140c0144c1b074441c00b8500a103c400581c0f0001d024901c000b41886100400399640d1048804403040801e8004034166003142c4c0c131030240d001c042d2141c00d00328041c1c49011030103500501e20000005000341209445c0f180440300e201c400406035110001d0100042001000070040319003404d40c00c2507032900d90300900c4010f101e060f588628400540c0c0c1c0d00e0030f44030324010709035414034042020082c20980c03810390310495170036113445400240d0b08800a0740e02c0186c138403821907a0841c0a0815200340c010300c200d80c108c1e480c1c1907410042e460030049204c01a03202c4284030f000524110000102800c00c0d422403104207034403a44106250b103c0f482c0dc900d1103260b0952105c01c5201c3e06a5010241c5c4920300180380c154003547e004103416140303081c01429904041c0081d810480ca107000c001116a00500ba0f03140b003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 101863561 1250 101862311 101862347
    0x1606030506060903120306030f0714060918090a050f0114041104091b0518010b0a03151d150d020603011e0f080f0105010f0f030b18010203070203130e07 67
    0x140c441d500860b0b400c0c000c006420360944a20581a0300304a180005144512000c40c100c5400004080072251207071003d12640c542c081014055200314070b41b160250940c05c3e03001c5c08030510402040001045510159090441604454080010b015080c04400042c2c3c285074002d0140460380c0030f18120780000140003404880541071981038a550707581108881a400c00b0504542124030040146d03562183d22030540b107410100d45000360981c1c0340909504842c1d071910340c28146054904c041d405400c003940b4001c3c1c900484040419201184540f0113522410f20a500f8840d16041a0918948200240d0588240020402c0e400140c5e2840210ba05641d1000902e003503003840a414494151b0301c83c1c1003031310949180c2d01e001c150907000044601c0f246a1303810081c010799aa079400c60440719014080d8501c0e68200c1c401c00d10114030f442c2c01080c0c01203089900007002900081000f803c83c1c0007501e0203030042e0400a88c401d10700b141006100090082507900741c50b18108964060540e04c070544001c03007a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 101864811 1250 101863561 101863571
    0x31401180e030d0203010305150105090709060804031e030603020f0301050c1c0b03011a0916050d0b031002180a060e010813021f020105090708011e02090d1502070201090602160603 79
    0x14a540500540f400c40e00c100c80309644a58491419546440326400c42921840d40400001803a251150f01315000d01c003203840b9400010f06204c0b08940b6000024420340500c01d081c8688500507020340701e40302c03800c21507a500045041c203500c10007508409100505110368184402d0203207210a1008865426141901c0c4040042040c0c0440d030203840300030050340e032651030040f0300c807940e100302c01e800710005070308030f0b0074168a41c1c0e07100080307001b082c0280400c0002481070281019420f559030100002d0440101100e141c0d000c11884001689c1c091403403a900c0503c1412070920901301080c6440103000c8900300740c09111107940008001c040020507008000c1c41444070f550954070344001c0d000340d54070300c410800d4400302c880c03102074041d140c00d50741c00f00940320713450300010f03015418410103846400030103584a2186442d102400030390415584144d20054941c031000011b2074200d5000314034024440e0268664002e800090320610b659030001c015500484400c00b10701168071b004905641c440d0900107a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 101866061 1250 101864811 101864831
    0x12020909012c0405060a05090109030e06031f080c01090501110606010c060209040e0f06010f081507090b04080a03080705030c031602010b03100e07050a1508060609180703140118 78
    0x40015100000d40c0d00b00201000d0200340000403804600c500707031104080c0060f80700d07c00c22508807400a100580094001a4994540d01e0300c5001503070080f141040030610b801c1d0b249504802d501d502c1e40690039036400082e03640700c82e58202c524400109403d00745101c43e402042c4143e6110000184080d040003040c041600400508e603043d5500c0c100094000c00000302c03c41000f940d10f841c1640c4254941c0324071800050385d178195081d44e20039501c446000d480d078801c10074428060150040c0c8400300344140807101081d9440041c026100400e0280300a061402c0300e810081c01e8070201501080c1009004c10420000011000499030082d105000064642c001000b0032801400d000d00b44980c18001c040e4110701001491300b100e0002081c03841940c07c00390343c4004101c12010385124030070340d41c071802002070040c1d800703401850b600c100003502d141e14281ca4100040c01c2d081210244941d10b0f0311690900458540c1403154894418041c5d0415000c4e50414120103034203a03440c141404010748804c20700d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 101867311 1250 101866061 101866109
    0x1512090f16090e100903050702040509030c070905061c0c091a09131b0f030605010803041a0a020f070303030516080402010509040b0f040f02040509070e01080703180b0114011202090901 81
    0x2040c40704d4000d104019001c142e01c0c008000e0f90240074246e02c0360b0704100124000007000b100b1950160010300080c0695403920003108041c090040c0969800b40c075040a490105540605500308540f203024040b0390103051203080011188902029500d035800c0c0d4901044540320310203810703041043c80804200020251911384d81614099407041e80201c1059000201840c001d203815040c0c1f4402c49040c41103a0301c6005850780c034011841140d40074a000e030903900b03800742480d0080c002506140f05440c070011141c2241482e000c1590f20440000790349204001c80b40b844000e03014504449444e08002078102a00028014060b04103660710a0b540c51254003c41e564098408448240c090014480511a03907140b6009412500c0f41d103019030000000561120b12580f00702000c0101615079921903190b11400f20010185145000c07141c4009001c22000304424010b43d85c000c002e42070200c1258400580010640300c8081e00c11059640188298400f0742d0f614004141502c0e02c207460160070315803c4041c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 101868561 1250 101867311 101867323
    0x140d080403141b01061502010b0609090612030316030f051603050c1201120209070f080c0f070206180109060c0c1e0506070309030b01050901050d0b061512090f16090e 73
    0x1a16200c819074003e60240141074020404403101c01010203034a04d42404182c0c00c1e52000104a5403191007007220604510f4020034540c4c00c11409403010904601e00b41701d081c5143c2c8162071191043d190042c403e00180e07450301881041e8210900140002c0c00d245084200c1580360b85110011f0685400010b03513148021020343d8803d041c803400c049110350356440c0c1d011008000c20b409a01404002c80020009070050b110740311000c03450380da50303078542d5900030840c151a0889104544420000c100103c00f5030741d658040e101d854081d03418800851006d030009401d19507503510020901c44c0958801c00407031800c5590f0780450300071808990326841c500c0c05845140341143c000c80d901410114601080c503600c4100d950560b4404d040342e0394aa40c80c1d00c10460b928a0903c1001d92280820f0541030008a403403440c680c01182c007419010000301c0c88095481c0940000d090f01e00f1444801c0200301c503820b0100700d4002d0381e807543c60150141154101600c1084e4146006d408007950303c558400705070880c10408 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 101869811 1250 101868561 101868577
    0x240702091521070b13031209050901090506040506030d02030708210c070507091b0f030f06141c0503070215040807090b1f0509011805041107140d08040314 68
    0x5180072607029603120802d41d40200c00d018624031a01102280c07204001c03080f550003600c0d114107004210324584c1c80c10f0303800740616501c0d0100442c0070000200ca44400b142140a04100d21012400d407611005100031504014070b0301d03110394000e60f4100740b560380120490304144d81080303405070f4440311003400300c03000324078950075a40545412040010319032090b005448424410000d540300c565584100d48140c3d1203050300740c4815020301030304180c0240200c9060800188504022030501c00c100b1402044581c607074001801020b048040c0240d074079044d18000a180d804000b541850183c50b11010358130b0084c03083c024000c0c04c1e5030b50161403400f002c905940051800230211140261200464000303856040f03401c034000c60311010b40a0000003005080d00c1c4d04a86640e0700c0341070241c001c0c011100c2200103c100100c010198001050340e407a54080c4140f076070000c0034519501c02040c50913822206229803e0004c94205444040b812584040c200340c00c190140707044211140c2403880c8080511600f0b107 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 101871061 1250 101869811 101869819
    0x4110f030109090b16050a111f0b010905012604020a0305010507020109200d03080a091406040c0f0320040e2506022404030302190804022407020915 65
    0x3503140864200c83c02c110300c074040074210703503c42400032100341d40c05a2884012500078402d5003843d03841100904039001007201260003040100c41c2071510700c5c0803450380d0702c034842d00c03400c0e504d4086d40c00078070900c002c19003031070411007099240303084420000401000803e804250b0b404501903544080800c4099608540208031504000001034001c292550085541031601d1408103403039400303d901c0c0c5c5103c01d0f015000840c00c242c15903007110204001070411000076070b5040c01c1d40202d0710074102c00d110400078030010007290030319090a0400c1c00d11540841c1841e00443c00070304c0010740014111901a207501d50070100e84500384005800341403419400c2e1010300c1501e9810300c018402c01a1010132444e288121a411a1990030881c0c407601c43e01103908000c18000f0b185450340840240e1158828000d250040c20080c4039800e82e03903c80d00c4085500700203151a000d010543c0f41855031030441150104d8142c04807002c0300b58101c0b10707000c0c465000c0c2c82240b004000400d80601da680044903150010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 101872311 1250 101871061 101871067
    0x1120903020705061c06060c030c060e0106080d0804060506150d05040606050409080a030b03010b0a14030a05070608010f060e010c0803041b0b0d0b10021c03060b03190b010f0e04110f 80
    0x203017211280503440c07610621150802c08001852800742c0c80e610082c942551b00c43d000807500d0f48441010303040c032990142d80341d9a031f200c000402c200140550186e18038596909442c40c2443d0400105507480589010300c510300070040d288407400004200c50814100305030100d010358950030b04100415042e0700940d00710742400e100c201000507980041202e81201e13203080000c5602501814201c4074050fa6060304900101c17410701c00e61460b000e100100e030310300804544c400d44070b40e0340e0242021362035488100411611001400002460060b8101810441c582205292031500000703013070680e1440c0203807440c4000408982400104011b080180829000504003a55038080c005c0d10783d40b1400340d07203400c10b1900e0304004840c940390343e0384c071032400d00360b401003102c5a441c80c83d10000c0c010b54155482419502c502c0040c8140a41018611603211810720150410543c100842030b1080b648415040100d400d90100f05540c000d4002030040da4152000980c210010806400b244170b00032103046416404 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 101873561 1250 101872311 101872327
    0x110f030301030209181f05130803150301060909030807110a0803040b0919030518010e0315070c14010605010e030609060c0c0705031603060e030301060507020904020a050d0507050a0f050112090302070506 89
    0x11400441b000c410080d8100007642d20b0788209a81c0e920340840041115008102041441c220300c5922404070900500014949a40d482100110340d26020b0880114100304100068542c202401d040c542c0301c01405421800d0786a42c50041911008100900c00c11000000c00c400c941e041000030350800e402c0d446000503000d58100a0015040a0701c0000742c03042010541c0c45951044c03002c0500264044d004008900c00d0700d85408800038020044000c00c4018400003000c01c1c46004507034043d500ca030b0000262503080038001820f40c4020b0881a000c0e601c0001482943c50f0005003480c1e02c0906145220f4940c0d0350910080c3c20b04c0581c0e0310807a4117225080800110171403a000c02800c0300c1c81040100a001308411455407240403d21404010800600680005d402d01c24034003a0b1083c8020701c1203460640f1071002855031805c3c0602540d00d0380c0065010312150420210a0b4044c00568080b000381c0c81c035100000305500301601480405980782d00038001054020010340014142c02044240c85e0540 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 101874811 1250 101873561 101873593
    0x409060b0904141b012001290a09020f0901030b281404090f06180b04030309020102150115120908040b071101050702060301030209131203090201110f03030103020918 73
    0x103983c0e0743c0300901410135440c1d2560085002d0503005081a10386241054a03810460440354001d85050119506c034411844180c0d4003580071890981519128042c2d03800040074011061000d800144001344104410510380b22203801340c0b81c64a8091a020400e000480c1c0417604c80381c400507131a101e00b5030250040041d00c0191890707109460401c04402c0351302d14442c0801094400000002e41002020305002e40490190b801c0074030010440c0d4842500b04d90a903850b18071000c3c08a0303003035000075560114541150b9040c0720800c400c00204800322400d50420195802003034040c00c10343d0031300903c418003a0040c4c1c5e03103400000c14160800215030700c45603030f029400c1a6901410044802141c0e1618400c400c0d8010b8040c1c503082a00038100a086070300f541d080c00020301d00545088826400b5002540000d4041c41502e41500e000e0b50f004a44910340744005071034400710402c0800980c00c0200c4000c13880a0000589044a804941c0d00f18180c031031401781c0700804602c0c02802681e00490321aa52402d007 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 101876061 1250 101874811 101874833
    0xb010207170a03030b0a0501080c0a0e03100615090503070501030c02100507180603060b03010b030603100c0201150504060b03131a280b03060105040f06090f091202060408090409060b0904 82
    0x3c0603450a00201c10341008111030341210f409168081880400811785010351100504414409800c0052120051400285c40d0807000034080000c152103200500001400f40c6941c00103065900785501d40a080c600003e4640c0400d0040c40e0404d650b804007082494400c05c0046551000d41804020904008800030410300d0203a0341c0c0016405056800500a4428072440307080710300070403615041d079091540c404441d03800980f8455140c82a18801103814400303100b101d507122013a8000284001b010500b40041046070380c0180c3c821480c000d000c218070004441141c0e4040341a210345002c0c2140d9141800d813500624908001c054440803c01c022107221020f4402c058190b0800300300684102c10314081901d04c0c1e400d1244d015040038004024604003600520001c1c505003401085007910f62502c40c0440308940088622039448103007035428000c2d0443e0680751007204d840036281524003070311510920b20400078183d000e540e8600c07158003440401d038808407406900801c4071034103044c24280744c02160 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 101877311 1250 101876061 101876063
    0x30108070312020a0c030209100803031801050114060f0306041e05010915060e0f12030d02180603060117040206040306050a09060608161715090703051b0904060b010207170a 76
    0x203034403a10028401d500002d54110300650151445d812181985c1c24403038500406880c01c20000c604441c0400e5000d4180091445600781940c0202c8506034202050300b9180c0692140441c09414100d0040b40d890700012142c10310400040c1560301c4e02ea01c00894000e28651001c01ca00d07490800405050788840d400c942d04136a0a43e10500001e41c9603c99846c2e05e2160388105d030302003505001d1f400105e0601c401500c1095000038800c00740d5180c0559500d0541d070103622400740c0c0d0340d07000804088012020190103001c6005855007400c45c9440b4002800c2d031500b80c01e902c9244040f000004013151f940d074048801940e4040c02c180518204230f005003000d41a102c0c41216410708102740400d46403400180c04a1044144039081821841d10384064080c1c0380b0030700501d495015200c0d100300148500521603000362103c400401625245042550526060101000301e0010091403c1c07526038840c1003294000381c12500010f003064081c00103034505441c0360310500616040c0c01c15800c0c1090b010803c40c441fa = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 101878561 1250 101877311 101877323
    0x703030f050c040e070e060c07030b0c190804140a0606060e0d0804051519050712030e0d110c10050c010b030109050a03032003010b03190902010c170706020301080703 73
    0x2101803145419518100e4030100e607010107110412642803100241c541002e884d042c045040642c913004510542d2068002c08240e40c0304c080204208005200042e6108822140d80380c100b00070521840700700d0501060480410200f14041424440304082030000f0030804401c841d144c181c50f240c00ea001c1d15051103034001280e0308851112a42c2080030040e054254070544c06172425040008100340c08240c41a0300c0321703d6106000c01e020500c2c0002000790242580d450307c54035141640380140280c510390030400101802e240c882580000001040002800107042424140242030003c51800c10000401039102e860b45800780e0a03140c10400404071702e0105030003805410210414142603507a003100c000e00c254003014646022038401c0c3d20401d210f000303512504070404600110000d154000b13822006c0d0a8400200f8400c070381c0c8411156107035102110f00c0a02440c5410f40019100c0c800264010704401c074030300143c0724081c0960084441c0c46910001c215280e50315240b2090303403608903000c11a01 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 101879811 1250 101878561 101878571
    0x20a09060e01020f0a0303020f07020607081b030403050615121f061202060417150406020d1415190f090b0301050906010f031205042301020606010e0a06031d070308070303 75
    0x10341d440455090500f801360782c010306828002d946e04078000e40c4124880400110144460300c0180d403030b04010505140141c03141da446038440042007040e603288100c0c11103140c0c0208010000101c002c180700785d2103602d0212418a003030760300010580c414210780440d075444c02804a82d10381d402502e01c003180c0c03800c0d040b03404101c8035458000640c1580300068020358070240621040004042c10307003a40f191f20b4100300581b403403105072510010105005840403100715401155081c40700b0712030711807d07261160422440005040640b4420a41e50341c64031300c01d019440360780c0c80520741b0132403400140080c1140c0071030070a10307503480942d0f00c020400500c241d4825400d08000c110341c03000004046040c0c1e0544074444601e075145544840d48c440307064040e081071007014400007070101d2205030f069482c01408844c403d19552080002424104018403041c14000c2c800340f1200c17141c59240b022070554400d0f0500103400341121407490710344082ea10600e00303548a081d9010040012000c064504e0354420b86003404 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 101881061 1250 101879811 101879837
    0x50a050d050a090902030a02131d0a050408040e09010902031f05012405180310020c0d08012706051c120e031b0d0f050606211005090f01020a0906 64
    0x401e40b044a805100050310032400f480700300d503030764011504040d0041c401894084040c514000d007500c540d0121000d0400c1124810003041661000d80d400740510800b00403900d00340c0e551040302d020703501403400c082d66044002004580250310607110300d80c008088420528a000c0300010000010202c8884030f41031200000d20400800d48810310450f00d240c41040b101141d6004076942e4000d9080d0420020200000030030300d803024002c6013005400c520015a898003241c0d400d526081c06684440100901d00c801040881c0401b4420100400070100820b0450b40c28407484003c0c20242d0442ea91008800c02142141e0350303815101e0381e10500c510181059080442070a1751310b81d40f449d4031180c0503005104203814121744440c18010505000f4008400344038103841d001c509454204048419030f00c10401c0c85414a07100352100385680e29228038600c51180201880c1d1240d0010860280c0c0a446d00f0101e40180700138441100e001600c04000c6444044c80000241811a18070401e804140f049070703822 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 101882311 1250 101881061 101881067
    0x60212030402090c0f040f0f050f010f090311030c040e060403031b020718020c030d0e0601080a080409050a0608030a0e010306052d030c120c0906090f010e040816050a050d 75
    0xe44076640081c900d841c1030f65040100480d6901400d41211002002c11021070080d514400c45000b42611811080310700342000c0502440090546c2240d040c40100000d20480c039a2005202e001e50390710010480640b0303012800300c1e00d04884440c03d2a8003605024200303c5802c40054041d1046001c1d69040c0003941580d4528a24803c42c480c002005820130301d4248181104034580f810052440c05c0d0042c503160528401070708580001d4510341d5026141c185552001c24200400d034058203489011300508400da65405441d445a4820b41d5042c64403000040c04e58002c5500c440c005100080030b030303a92094802d01c001e0403505220400d5021a00d03000001c16a03003071506030140281180c0c15205020041c540380b8800c101c1209160591510509865134005c0d141e0300100101c0c613000c14010b0180d070f0203000030400720010040c503490143e00c22808004840036001040c42c119000c07070701c80100380e40ba030b0b082011140c8140041d0045a080c80b01c03c0d2410454005020745940307000c0c405603510740041c2a022 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 101883561 1250 101882311 101882317
    0x160b0406060f0602070e0c040906030803070207090c200304050406030804030b07030209091f03081308060a0b03030a08090102071a0613090b22021f090f0e07050901030b0d0606060212 80
    0x290f80103038031064003800b10002061040f9040300c5000259070901e980e55a052064a01b50740003210030301c5020080c04121a0104110000340c00c3c150000e00c215040310320020407114a01070303142034012886210341001c100070700454000c2e000240050040326140e041848080d446440121000f400b40300020340b00da841ba20980c0c0e2841c50003041542c0c90348441c03840e04103c1075a00d41c02000110030100000020b110701d0010621115441a406e118600e41032007203080004c010b0401070301508041e85500f540e40c0200448130080e80c903041c4580103403501401c1c940203010b5040018015014074001008185122401d1030ac16103003240c10121880e07000000c03100360362445100030800c1c82c0900211f904144c00c2e11403404482c040c003804454940d00ca40004070500442006043c41c200d0b1401c07101d402c2a4003042600c0a441c400305122041443e04170000d030203980c002c01703a804001011422401580c86500007849140005028003440c248a080a40061400d40b05420242c8500c94000d0026100d55082d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 101884811 1250 101883561 101883569
    0x90819120201020c0c04020c031603030e010b1c1202030c070902040f080c0a0509061c0803040c0b0708030a0203070c12090503010c030b2d030a140c01052706160b0406060f 75
    0x19122610000081c44060f40000c1c4c008d40d2540018400e018016040d0206084102e00a9401080781e08407001202d0031140d000100074020540c6c0b16414555646900310b0000013076214600c40c0d81c0310f101540403811401032100c95405030040550000351040c3d29005027080d91503041d1400301e00d5541e040a9540e54100c40a0680c12108142c02085907150000103598044030190111508003168211103410380f2411004480d044404030500007408070350781201000d400200744d02844c2001030340711400d050100415581d08070b0340000002c0c0788188270309803a4121070740c01045808060f000000c090522a9503014841c00381d8604441500203901c00d0281d21007a80014000b030706441c0f0400c0c2160303030300011148261080c580c20084104651420400b4425050150384503210b030341410a82c003400c00501c020850b04000061208150006030b140c2c1c50345c080281d00300305807000407881e00803e00c0380c014036500c13049000f2490701c501d040c001100700c40d52285101e02030400442da100d2a0300e0f0703540710751401 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 101886061 1250 101884811 101884813
    0x190b0901080f1303030c030e030a031401050609010c0618080d09030e041a09040501140f040501050106020c360c0904050903040b030610031104090902030c030f0d0e01090819120201020c 81
    0x103e020103e0300950109aa00e00117280209405200840291841c0c1c0f06180704800256280f41d0711918505031803070180548011103441c0d00d000e2413070000800c00c0c0114000074110656980701c000e00d8294440041403400e034051507054440c0d460440380d1005110340705060340420000e02d4040428602071089007404260880d0804196041900748200620003c100300e5007590b80f030814000300f040e402549407094943e464280701710324103031900d10700350303001a40003509642c44503841201c981e41e82e15150300d124250b001032070500d001d859041c00c01c0090801c0803520711100c02c0c0c24001d100720000014908030030296424412a160b8416407030750392081d881000c000d0202800460040d1030600d440703107141001c0d86004908a80320340114000d582c800d603c8801126940c070001811801c007030081c6a0140004c5024145070500e07407078481e480c0c0003903a281310200501c5269684440c4c3c0125078000140645504a41362400740201080706c10711503010a4426502e0100c980390464814002c5400b1103003864 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 101887311 1250 101886061 101886091
    0xe070f0911090d0807030219020a0b0a0c120807090806090d080601090b19140c07090209060c1005181f0902120a030305010e01090902031506190b0901080f 68
    0x10000300e0003000301010810000301d0410400c08140d8562040301c2e90316010b1007005645041c01e281c042e180030080702106181c0304444107580701680d40c00d40407030221a40d440c41035951b2030101c00215045103c0400007007603920a0741c68004880d5000348514411140c03500c54907036680c3c45d0400340d80d071071008840380307003569100080e144c0c14144a041481c2d006401070422542050b00c4150498240d004014454201240700521462482d40041c85c5d4286100d000c240c030f85070000007a01d6039201c2c21030b805803101c85030b0002a098400e8683c002250390380001d031016520118034143c0b1100190405403503003000c0c005601a203000e0743c4804103481c1010000c52641c0000f0040d0741c50308802601c400386041ea4810201c1c1d0f480d007a10b41c0b041c02075a03159440703580c0003e819810501c2603400d0340b0060308000a020702c2c003081d074030040e2000204108518031404240540360b45a400140007600c5040002818401600700081c5000181025010b41c9070260bc81d9061542d42c282500c0f039440b821281c00c02024051 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 101888561 1250 101887311 101887319
    0x70503030a020919080102071a060325050d060204080705060f044407060f0507020d0f020d0302030c0c040207030807050306010306030503030126030901052505010501180e070f 77
    0x9070b0040c00303100c0000d4050100c6004800c000340e00c0200b160b212600326500096a4010000c12004641c401000038140d03070701a080a4010965441c1d1035942481c400c07104040c2e00146120449803c4014100188803288000170340c40c0c21070280d0800c2c415409940b081090200312803400c1400c2d01c07543d00c0c00400c01070030149040148440401c0e004102904043e02212202c18190003034580d0f007080e50300204404920744507440703582c0780030071680c8148200480c0c441c24854a80d0300c281211000c0303804982c50410703c1c081d8200490200070100009600030ba41e050500c3c01c060b00800502051981d5400380c620344142c0805010985c030030180c00400181d5100c0000350214000e00245030001c0301850005500364a965401d81785a000380c00401407201c200503c9088040c140003501c0718230903e00d000d103060040070700000c1c0c00c0e070107620012003808e071203140c84100c0d44803036401030030030700c0d8201c0024040307035079a280809404610603181100d0ba90402c01e40c07142e0082c001610100301d99059001e000031070b02d4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 101889811 1250 101888561 101888581
    0x2b11030909130f020904030c03200d05090a050303120702060a0b090601080a02160c050f150a0c0510060306020409050c0702030a03030f240e1f0303050a09091e0c020307050303 77
    0x32410103c034105100600f45003d41ca8440040f44200d11075150046014414180540844003200c06016000c40740f040c1c66840d81c82c00f04180302e440c1c00a0034101d490381601000280c0b044104c0c0c0001d031705840003003200d450f0081c0221407140103041940a8481ca0b8850a008800f510b942e102502d401408080210b810f551040c030160340d001c84204401400c0ca46003030646071504902d00401e840b00b40c5101e00511440c030b03201a0300d10142c801110031801402c1e04c0eaa5241c128040e101031141840b0300d8454680a10005203d1f00c021800c0c40101004081d0702c0b031900000075000380c01101d011a2030080059004e25802040755410364000300100300c180215a02140070b0700c46c810080c0c0006445821600350b40c3c01038054103000302d1410780486806070030510841402c5c04010080c0041d94850000603003421610f000c0134003a40e416140542c0e4031045180c09407920400f41d4081000c882c5450784520048581c890040505135a010f010710107030700071850490b81c90090f104080c00c590003c00c046a101c203c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 101891061 1250 101889811 101889841
    0x903070305090d0b040b06010f03020903070e1305030427060b0d150815060f0324130c09020304120305060a0501180f0602030a02010534022b11030909 66
    0x602c188490401c030341d252440344d4800c0e2002c90704408030a040c080c2940c0c104451007072880e03d5140450400038a90700296484500344211119441240080384a00340c940f0511000380e5004011256120340e18408496980310802c110b20340c0c244114445504111940540c81c02c98940d0701000c0e00300300b40c0c0c14014000786415907500b0701040d061800060380a406002d18401c038480c880c294a00352800d0070074020703102e040000303280c0709400c54040f03481911035900040d89100e41c141c0c04456a503a620000341c50410050b0300c0500010b03103c0707000203a044581e400842c80740b0300c11030000310b0b0002144000c0d400c1e164155a0940e0012646100340a01e502c104c2480d03246a196444185080740d40d02043c03200004039030001030040e00f000901d469041e409000c1c56810403185052080b069118102c815150590104070700743c1206590304c0e114196208000324851420500b4400100034203800100340c84078600394983c00410050007014603401c02c0401550491040a03082c40c403240e50300010710701d03442 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 101892311 1250 101891061 101891077
    0x5150703050d06090e010605040605060309030a050304030c050a0b071205040506010909050a0602070302031b0a1203020307050c0105100f140913020a120b10090e0c0f0406080303100e09060903070305 87
    0x41d603c00f00012002540e002e4406448a03000000035201d0820003800306851741d075003200b4042c2d0000c1007800b40742d49000003141c09600d268a02a42c603900c99250485045c16103c1c4060558407840e65168180004080558022512501c0f8100c40126800e0240140d81c42100e0282403604143d00400c2085060742081e26401d11480c20341d0070344200c55031840200c1e0007a00782070780182e00125550310388660040c951f208500e021030081041c00c40e1584c0c1d9405104e16650070804054022004c511210301070010f440555660380024080c1e03203040302c18205e02040c148660345007010103000009030511400e082040000380a0700321103c5039142041d4a0301030854800480c0c01c01403400c400110340300001409444030340f0a0f00103d88501b45400c180609499079042000f0701443e10000a8210300002810f49001100b0b9841c02c580c06031000c0010020301c0c150344520418000002007001d10803004440308190384a140d50520700c0c2d121007106aa440e1021220701100c0d0380100490800303e802400900140 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 101893561 1250 101892311 101892337
    0x10f0f0504092001120f0608010e0703080703120204170c0103051e040b181f060b09030a110f04020403030e10030902010215250c1a060d0204020c010e0a0302070801060515070305 78
    0x105c100112001206c40c81c44451440d5613540d8030503c0400301c28010080040202c100601c41e9500b1621000c00da84180704004086c0076200302808268902c07501960300403d807804031001041c1080401688441100ca070160000b031408000400c520a981c0001840020700c0c0c0110100b982c3ea5a108000140081d0a202d0311009001341e1080c1c00104005404900c01d98229800000c124a100f00003a100b854001503100c0c14140903001301e03034a001503401e01d0140c210f440b041500d1030140204d032020b038010f100142c00c1400042e02205140d0406c81d10009034500383e9025800e4078508108038105c5e0f001410007030068000c03411600c500401034142942088034104c9000c401e40340d041d1103c112070f008403180e030041694003404000344107010082d803070424030302005c004040c5081c40000340d0352102e4903070091141e90301103000360810909510156001d6801d40031079200d4032450402942c1c81e2803500c030300c1380150308000e0040380364104910b510001d940645011030500c0c0540d075056819410002104c907030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 101894811 1250 101893561 101893577
    0xb1602030c040501151e050306010e040f050a0b0a080604020a030b04080d090b190c05030c0706091205070b13110f01030b0a030813050109240203070b010f0f0504092001 74
    0x2a954482c81810b00070450012805d040381c62400e0301a20341c1d0022942e00513007200c0540110752240c0c01404585c2d0000c002d00c0c2c000c44410400e00010028118022617400003858071007044441e4a45901140381404200c40350300069030380d407141d80c0d514002285c0094000d01d00403010400030f03825004a40c0c0043c42000071604214211408000729080c01c601620120720032420300849080070407101c01c003008074a0061000d00b000c5a005080c0c1d10002c3c10740c0b54036003c0001d43d24207100c01548100c04087d4070400302d030303148500700304002e04980040d94140c07074101405004c254000e0000e44205017141d481001a5181d00c0c8110030800910049050b290526031162240c00554bd1031f4110769001c3c0d8400c0010540b18800d8010141c0640c0241e00014144034110201748404641495a21501c24038000c0f100300e4000030000881c11805a00c10040c0703912071100c004a005580500303030009542500c41c00c2c2c0c0446e0360b60320801083d0b910b0040040d041c20300c0c0f04221403011a105241e141d1103c418144aa0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 101896061 1250 101894811 101894833
    0x90b1303060207031202070c030311031608030606040b180117010f120c050306040b09010c1704060e120307020c0906040b0607231006050f0d0c0e1015050309070605040b160203 77
    0xc02e0b0382c06443c040b224603044000070700405400400002108010400450500300302c0b1301d1043c1c804210120262043b413001c000141260b80300c200315030180c1401030040d0303180d50309103c14407104000f0f4511540800d4182d6504d44401c501f281d1118129a00446e954113214035003003490140002c07600c0d00340e41034a1290703070200d61503c00708030301e0703000702d20407501c40c1d00500c1c21444e400c0c21900f100c1c01c608100000c0d005010410b1244400e0181c02c150440300006800ca01d03650784a2030a250303c03068000201c0007204000745580c0209044d907089109441c92200d90b0b032130300b081004450442400f00c2e40b11000b880400c02140c502742d000011900010003101c1041c00d0005540d1900c2090340003408a107849000520450504030000903540d40150f440305407000440d51502c21941d07071400b544010354542c02c00112081d000c1c28006005100010007444d0708104c0360401840f5600448210f000c6115800c4001106441034045a044414085580d4180043c44500c50744404001605a80c944101c0440c40 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 101897311 1250 101896061 101896097
    0x4020d0e030706050a020a0203120c04050306070207090f051006030213030b01180f0c05190c0f0609030e010c0804060509040603150902010f081608071110020406090b130306020703 79
    0x40c040503880115202d0246152a070180d0710001e010328511401032150a103182d4000094401071006540340e2200c965801d40c01003414000e079400766501d0700c01c10041c00302840d00032542205079002c000c0c0510640c00445840d5058403819103101502e40302c818010407400d80f0940c0509401c92034448003403501c43e0790791581901607000303811004031082c0300c5c1300c00b207180003083c4100803100304901400d1240140c609000380c403e02130207100d400484d0b988950002c05c2d500c14641000c4060340203c0780903a0310440e052920042c600700340110042000b01d064801c1c80d6010b004003110950344041001d1415042c504116995004460001e4003d6281e0f103011002891342d88811304034998982d0002602406400010484000400f5000502c1410024803054214800c0109000d043c0f5050031400d9841d060800c4800d01c01200380d6030003c2c0210000e114910115800034002c03200349540362040151070b20002c98a41c400c208010106400e661030410020341150090002c19009007444841c10b40000025 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 101898561 1250 101897311 101897321
    0x2010914010b0f010c0209040b1905090102030f07020f0703150608060408090103051608010905060111100911060405060417010209030313030512040b03060f0303092e030c0210020904020d 82
    0x4004140d440b69101c03803a5003412503e111100c002481c0801e480c00b802c0d004600c03402000380000e49455941000282400c0c6000d05681c40c1a4000c0410000380c030f4541c00150003504159090840100401d01107070400788001843c240e88a01c0308003401d041851a59520700101c0c1c02d02c000c04049840d0400026040ca0030302c125445607016241040e541c00401780010300320b070801441044039a017003c980c80000c0f603200c030110b8195446104000b409449000069415120a4003044040c0c800c0d0700a07a48442c4440d0805441c09115201c0c45000500244c01c0004901941c0a00350308544203220402955400000d004290a0703018001403401e43e1050220b805c66000420300b4691204092003001004130402080d000a0f0384041600c1c180ba0400b03680c5482444058207492040b060b24142002d41d98046c0103c0d05281d030020500119103a15550603604074488107038000d002c0c0c0c00c00b5040121140640034120310510254003814008021910b20b0009401501e42c403034100703038240400b48240400e4400c03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 101899811 1250 101898561 101898593
    0x20c0906011116050406150804060e01091e20150310030507031a0c04060905010c0c09150e0c12011211090414010c0e030607120908030a020901020d0f0207050105030403020109 77
    0x4103002030800c000d00040c0e51440e80141f807035284a10035441026804107403160002d600c142c002c208180189100ca0250a4108000e841789081602a18448407440504244603220750b416203a2a40d8240304d00d07400c5921300c007110b504020300302c4051070008c4080c001140d000a10a01038502030b80c981d21541e140c0811600100c1d5201102d4003800208120320300403541c0201800c54552a00f400c0034001001666907102d081d045c4440c58080c4001c000c40b440e60800503000c400303010060b140c50b144402c0091442032240301303042a440008298205034080840341003024406070811503034078001170400c103160850381c243d46001d04400200e6040c1d0b00d052425001c4c0d0700030640840d90403030002003142140d816650103000c0c002c1003000003a15480c00300700160300c40c4481c100742c00540d401c03c1c4641c0140a818100500307070b03400001000454150380d4068180900700b03a08650681e03c4600c0301392034210b4080b62050240e030000c141004590306c81c07001558814400c1c40085122845035076001c4c03400710140f071 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 101901061 1250 101899811 101899843
    0x20c06010b071a040807032001050a1b02060402060403020d030207120303051b03040203100b12011104030512040806011202011106150102120a12022503050702040605060a020c09060111 81
    0x2d0034000c0c00001200108206401c400814480c10715543c0c54045206131030001b005d20003200004144010301000c603000000c9080000d120300e02d0039000b401d0040c0700e5490740170580d1000030103100805d0702c00100e140c80b032540600340d42c1c074160450f001c01510061902c030443c1103200d0780b10003180104400d000a0340952094070003140d01d05002051308113410800841d6818200140b0070000943d90025038508264403180f070000b95441400c0202d0084002c10740707200619801c003842200c08034100401003044070702070b000750f400074800f0002c1ea8109200d03e104490b5198001030050000019a28054210030320505158a141d0a20031400f0308194049995100c02c52803882089861758040c09002141c002c80500c180c9021180b400203040c02544212841000380e01091a01540821401038041d440303843c034a2603d01c002515000b01203a01400f0101c2c011810400005800d05090098804400c805d0700a00241c91b0501c040c00002d0000074100d0b030400000d490000404030050202c00d100c00900c0c8 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 101902311 1250 101901061 101901067
    0x902070b1b0d090203070f060507060b0f0a0303030b01020102070f0503030f0c0c0706260c0a0f02120d020310090203130303140403170705070b0709060f09030302030306011101020c06010b 82
    0x1080108680d400102034800320080750201c40c07031052a500859507841c2072142c00040021143c00401e14000c01500491034586141002250301e03500100a0708c90f20b4440d100034082d807003d8800f070090b400c0c6120440f9800040000042c80028080e8112008401040c0300060401e202511101c0442401034000e80c1d42c0d030000000e0080d0341e13080094095112488a00182c034001190301a66600e49017403188000700829605e4100c80c034400000e40c4004464098061400c0d81803141c501380c16544207c0c4200045009200102009400400d8003000d0760fa41da02c0c2a030900c40344129003000381d80020050300142c1e54a00f40071414504030310107035004002c0042d8030410682c0a04d409070071100d0062000f010601714004100c0007a9100750940030711a5210414072180e02d072503505440b80c1c01212002003c1c11850810004241d0b4448410780c101c880950702c402d00700b14510b00c00c1e1041d001d10700000d4016081000090034a50062011034101c0500400052800f0300030031007181001400c2c4c015880e851800 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 101903561 1250 101902311 101902313
    0x30c0a050904050c0a0f0e0906220c081002040602070e0709060f18060201050a0f090f060902010513060804030f0c0314030c0405090a02121803030f0a09021806190b0f22090207 77
    0x41f04003a58003d0075000200031500784080c418208000c100c4a543c94500c820010004011464201c903004000714401c035001481c000340d03084003940081c001e4200511401e08009151700000d0f00c00d600607113458558440740390825804603000384203a03080e40c0902c000002074141060106104000410150340001441e050644022050703e0900e1480c0d14020300f4000711380d012401000712007003e940d2103400044d4451580c40140c85500507840410f4123200e40540004255811180d40c030701c528030940c0e900d0039000e00b802c001d4821510651010703001400180415000e99200401103400c40c81d100c5405050680c1c40c00010348100e42214074081607a000300c2e1020203c002c0c0306c4034a4011604c000c5000084401160069403800010702e100810300052011891406482c1c2c4100c001c650050207241190f040703603d60b15169541079030302c9401000302c00c0e0030b80c0e400050251160b042e03403160508103140c4540042c160000c0e810034403112040e1026040c44420707000700302c0da002d4002c004030400540c8450312 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 101904811 1250 101903561 101903579
    0x7020703050c030102040305030d0905011e150b12060f010504050a080f0c0315040b041104020f0315010504051806030708010c0f0306050a05150304051e1506030c0a050904050c0a0f 79
    0x20a070b40b2600030380c01400180f00140c804804d03148140401040050603510720f0030658054a06024202d544001200100c1c511160607003014a08040c8008007110560f514401510684944580c1840100000d0042042481c0040c0c100801d41014074009041c2906c4100085900f09250301619140d84040040100c150050040d4031005008070b001d840d9000d91356141c2d40c0544001080140481c0745400014108412004d00fa440344101800464640000340c000c10750a9200340e071900c01300e1201040c04a442e61084080b07405540c0054010113030f040718240584801940070b8052503040c000c600c4003081305c4009104401118541c0d60b1100d440044102001d412540c25401460144400c59414442030725171920340c080145200040c1ca40e00da0f200e00b010b5082028208910342608080e8201890382070380040c0018801415141c400e0300e50310750804040c1c0c0d8042101015801c1044d010040000d0700d007518a041c1d00074098000d989824942000041e100003017500240e00d0b481d9000c1044c0000a5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 101906061 1250 101904811 101904823
    0x204060503030c07030b07050f0a0815040b0f060706240e0703050405070e130506010f0603060806090a0201050a170f0a050a0509070b0a05040b04030b150618040213030206030702070305 81
    0x34080e0091454881500c000c2600c903c2c00380001313000481c034400440e440910802c2103071641e0007050724103512000c199400805080d01034a522844444000301289103191520414100440050160818007070203003d100c40340d04040c3c03043d91000e46d2141c00e20100144543c1080a42080f40c1912081909002088034142c202030180c00400d03103041d040200040c000034000c000e0342c04009a6512542ea207a00e10223444403e000f0040990264200000f0a81e40610310b060030380b001038409110303a0f81c0f9903c5040c2d03200c0c0c0440711202c039a032005100102550280008000911403490012080381c0c1c0d400d01c1410428054450000401034101082600342032445202c0e008000e120040c0003908202c0368140e5100b8941c00b03100781c90500003070308941c214010360855006181071127516465550301e08010400c2c141c219801c1c000001c0b8101026464581300c401c40e030340034208590b00c038034000e035400c103100094018092004004003022404005a41d5001c06140300e99081e0740103000c6503003185066410300f0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 101907311 1250 101906061 101906069
    0x10603030306121221020720010203070c030609020402041211040c0c0b07111e03070c0801230910060806090d1d0910050a081c090608060d020d02040203090109020406 73
    0xb1007002843c0c2c000603071340e05006282c0e4582e45449048220007601c040412441c903609824072920000d4000c04000703200c90031b400042d084000881034a081c074001a0388074410500000c2001e03030300c041f0a10015a450348488c0e1b0309030000d0030041c142070b2210500807a11406032004e942803d044050b400d600d00d46400f40e0341408896140204541a05070382e8881c501d60050840c6060000110640610840c1000900d00c003000061440b14201c0110080740d40b02d51000314280d6034a042c030132000c03c1c5e0309014021161008601002c2c071441c100e41c0302880c001d45c1000307404c800250082c8028000320809038010b81e0040d142c1400078140d1420007480191400c1c080003030050500491204001c1207101351000c1404089058941507416070b50b01200389200740b80d075000913038061200400030481d4500041c0c1140100750709191403c151110480a541d1706000d03128004c00185004c00088840c203040c41d030b031180d15102500c15240801540c1c0041c0c00d0345c1084444001c169914102d01c1c0562074039001d144024 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 101908561 1250 101907311 101907329
    0x30309010b061206060d33080f030306010c1e060209041b0206010b0c0703060501060c0c06031103130302010209030109080d06051f0305070c05070b0703090501051606150b030405010603030306 84
    0x40c2e8100c0400042040042c8824803580c40852942c2030380801d5004103080024200e9100166468021140f87c070300c0044584803032000c0340c0070b03002c10003881c0000d50f100c00c00c141c0700c011411070b0342d048011101c0084207041101e40d000c00400c2040300026540003101840e12074240943c403910404248006c0320050210040c0d04a05101c9018010303401040580c1500c0c4495515590f409200d8413072460540030750700092600e440c05000051140d03010080d5400140b0bd04c140d00c5076030740d9450003103041c0c40b800c2c88076035003142c000c0002c03c1d00e01540342590350761184240000b42c1441002c100281c211000c101c4103a035000d0700000e0410300300046101d098040c00c0b08454021804241c000701c3c03441090300c480140c06141e520340100c2e400501400035841c0b103075404000c440b0481c1d103414140d03040c4e0300a1401240807410040d008141c5602079000d440807100a03040e071300481d4881c2c3e21644080c001020516548140e900000b0464048100c0114031490185c000410210700e145401002c46800350320009030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 101909811 1250 101908561 101908567
    0x5030c16050114070b07081e0a09050d020a1106030703110c0a0507050a08030f030603010209060f07021801060f0f0306081006051e011d0a12030e09060609010c06021602030d02030309010b06 83
    0x204e4a44019800100031f142662440c1d031032030b090165010074080d00007110940802000381140c01908104103d07441002512852080040140e03030707135854040f0060100c40c450004545905080340656030040640ca000314901030140314007006548000006200e642040c5103500c00d11200f0801e000080ca000c0c0e0301d10100520b00325041c0c2e268091006841c144400000c0070034001d54094044c0d0300110001407005075906d200d1900004682d0160104900840c0002c0d5100043c6100d9040c0ca4100c402e1500c91200c1884280300440c2d10070113003103220081c195241400704000408115490005403d80c000003002803d02d030420100b49102c036200740d290740c56006881c282c1d0740d204078140c200d001034809190180f000b000019102c81c5242d00070f00c401d4003d440c2814103160b4040340b00f08803403c082c0d4031030109442d000c3c140b200c144a194261b902080c030280e24880001d07025401455414050f01410030901e8840d40001e00301120580c00d90016403000c801e21400341700a10807000002001ca0707025203 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 101911061 1250 101909811 101909813
    0x6010501020d0210050a1d0a140c0d02090a06091d07080d0912030519050304020909060105150c16090213080a12080a0906060801020d0b0105070f060905030c1605011407 74
    0x1d0394140750070b0a04c05041e2900081602c02485800584000c0072000512202560040d442691052500320640703e140483d145040407000104040c4020381005c0c10307c0380b0543c40398091049958021303000c01142d99480c000095000010700c03881c03070341400c03d03030744100130f151328400c02454070043d81c00c2491240c000c511840070260b0098020021a11654000c1172665110f0405491034010700700d10400001c1c000005038580382d4800001e511841c030844e0941441d858842185a030341109000d0342d034001710100d818404410001340070300b21508158007220125100c40d403603040c42e008290f00100000303402182101d1400d95140108010708400001020040000c2d181e04024101c190100014410614003003100c0120700d801440384070b40c22081c1444841da584412500035440700740041003d0b0315041129506e5881a004c8800040d0401110707114540940c0f6150010956100c048480e48001c01c414460800e0031701080034605186110001c010f03141000140c0f202040e070107600300c48081004080 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 101912311 1250 101911061 101911063
    0x9050315100314030319021806031b1206042009060d020c0102070507051306050d0602090406180204080705010f170c16060506040b1c1103120a02010e06010501020d02 73
    0x9100c000580c08050080d1154034200030500140e40000d8a40d01da02907001c2c00f0440000021801a04030001d04001140361021010403806410000440800d1441714030a540c41d000c0e01841d04a10500025280302028551158040d48035201d901200d0320100100142460248074648850403105079090264440d246181410304c02c84003114401c12000c2224030000285505072000045140000c540d40c9080b03003084c07941d440c0184201c074072600c10100e0501c80009030b8001c28080311005440c4c90302007000381c0e441d01c001c2d410005101e80c20030341e40d05002a4240c0308030400588440103101c0180c2d5182000c000904200e1103801960601800d060071411007984400300c280d016460070503014050b206d44258400c10b2184240003c5416800d0b6007280504c81c0684c00075000d44004c4a04100c819181130510492910541c0b0306038040c0c0380200080040748407414041440080103045d512420361210a010705038024070344160043c1e5484600314010082044040d025000034001442c0d4050310303481c02 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 101913561 1250 101912311 101912323
    0x61801031e0c0905090a06050702010b0105070311280c0603090f030e01020a140f1501060c030f020309040203040b010e0a0902090115020a0f0b1609031122050f06040c090503 76
    0x314201440c8046a0010700c0440400c8901404000343c06000500b00090401c5e0303144c01001080d542c0524103004192001e0052007500440c990684500f4240700664505a0310340311007202c5004e60b80220403148022a03032035400130711030b05031180c0d4a1440210310308001e15400728980101e0f042c5490b081c861404147d40e046000e90311541803600e001c4078070b18080100e041c014484d03c02407102e08407601d905501603010405500d0180800102c5102c0300b039602082014840a1080700040785500841e0404203100380c000c07011803480c6c0d0040764541040d200c0800d08a9204a6007611149220340040c002038940a1a41d86c000c0c081035424000028107400096503610180304044c0c103180c02da6400400140280712000b078450700080e0036005a8940e0030003207900441210240070104e81d0f0b90744444407078000c0b1507650035250800b200360b01501005060042ea0601e882d042d032410540c90384050b99004290141d07900c150300b400e080d4180c0f41404003d10058410200010701030101100050116440000301 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 101914811 1250 101913561 101913593
    0xb0303030117150405031902072105030c06070c02010f030203071e140706050906060904030c3002070303030501060c0f0209040602090d050d080a1a0918070e06180103 73
    0x15040d080b03a21010010320b42050791845441d08000a400c000500801001814100a40d0f801294038260904005c80e20b81080b40148600001c0183c1300f005184020007040050a1060048034982142c1503140c03403070a00d085074080b0004940b00c03d044110359000c1240e19048003241010350460410500180c8400ca0210004000401c0d02d0b0940c242c081c03081c4006142c40e880721140c01d580d02a50704007100030700781c00c82c0d0701e180f9489240d01240d180d0410442140c0b040f40c0541c2c030300007500d03815038801d40140705008000e019000380780c03007220507603c0c040b81c4028a55095001442403a16501d0090107a850580c170420610010280c101c0203d07002c00c3e600c0c41002d074110b55a070544d0b40e91f031034054001c1c01610603850300166001884020084005060090001a611400c1095030f44444401c250781d504d449070144035120f0500d0107000c0c1080880383d504401ea4855400c5204a1241c840e40703405580d0b440410188020b8003846040d007850070110b0a0181c03003510b00e5180398115164102c040d00304083d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 101916061 1250 101914811 101914829
    0x6091038010909060608090c01020a150b010903150f060b030106120e160b0307080903190c032102040e1302011e0e040f0f0b03060402091303090e07030c0f030b03030301 74
    0x1508490780c860040c01d400381004a0040082a40710780780103208a0b4200c0e56070500384500a00304031213600015103c80c9044e0b1001400700c0e049459130449011700766100c41513051000220004c80040e1400b41501d41c2c985c4058000281d0b140c80c55600b0065803041c0e404468160303820401400034036170200300300806c400341c40b40200300001d50101491501058804460300c2c41b030201c0d404540008140001c500540c180d90f241d04e929242d01079243d1f120300c80c0280101d016003404030f040030202d008041d400c0c0c02d00d0190524280d00d08401c00078060703500b140521076150030740c0001c040c4600c0b03080500c80c44e04945440c1d01d1444203142940041c05000b81d000c2d44c02c1240f0a5410781c1c14140d032017240e90029481001c2d00900c420441a00c0c0c030400341c1140c0c030b0001c0d00ca505220b54070896007070010f450762055400600c0030003581c40744500300459650050b82641007010141d00400c50070b003101c4000f4000c0d003280d6400625070b0000704000385100540b551010070141000300484031130f500002902c1c1075508100d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 101917311 1250 101916061 101916161
    0xc030e0f1003020f130b120906070519020c100207080d0203073306080a0209060f0a0b0d0f02030f01081e100f060302030a0f060605040b0108040b1305060910 69
    0x402c110446000d0000081d03503c6540c80170109420007480083e0103403905021425550b6290b081502d034441c0012901c9100145081c0801075070410100c1c01e80c10518450b0060311a0044404003103030007206040030f9280542d2019104103c4c07600208102e054100c0307684099828030219556035100f40b0b680741c107050410700049280d0540c0c0c101440881d00e4440c030b02c2508001c600d03500c00310f00d51103555441090340300c0c0a615000810500342444809070069004000000990908030740e201c154000d0404940c2071175441d400000495510b1000354058440031031044c1c103941c50410030529040030314a000c0380c50700d00341c4c01c10030600100041415002c0700d0640040713514214a4440001084142d002a5251192121410501241c00606071805001e000203105044e107030010300c401e9178400d07200305000074072100c00503010618000027640c101c04010b000d00360348005521070320b10f40b100070744914031540c0000c00300106008161051100003450300d4009480282820f03048080c0c02c0b543d01154084284503 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 101918561 1250 101917311 101917327
    0x1506031a07021e01050702210d050a0209040609022d0d09020315190605041b0e04020d020301030804060807020c100503040516120501060e0f0c07060b04020301060c030e0f100302 78
    0x1d0003580d101045a4882840c4076440e4403c141c082c08040e02c00380c1c0540511911019000ca1102d48561085032038030725540b420382001400001003000400600880394280100710309541c450040c41c0090207400030143e160310b480321446202002552040e80d0f03888000d1139070220a558001510001d9101d40c41c00180d01c4502e00129007081710b5005080341043d411000c000d21018811003110302079603851420042035441e0740a100c00c81d11030310396002642403c0580c00000340c1c401da04260300f00300041e01c0035040a00407a100e42c10f03a00280c008444001c0080b4062080650206641394040c109200910320b009071355020500d0100e060402108010b4004005410703c5420403030383d041800c081c05190406562481c6c1803603521a85c0004a405500705000080c252081c0c4400c0c6006011b07140445034151034562a041990340102412220700ea10382c0119291541c49102640c020203964aa0320008002031a008040d24410301c415417042e89403c0707000b00d0319200c0300c181000000c0d86007001030fa66421 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 101919811 1250 101918561 101918563
    0x5090901020708071505070e150901021006090e060c07080304060506010e0d0311071d0105060a140418060b030910020f0d06030f14060106050a0e01050403020402161506031a0702 78
    0x280b03440c080c100d140300003108020407588a14551400003254010030039611001412280340c04e42804055101c00b2020081489100503001090581c00c140103e8095070f8802e08a00183c40807580301c040034955417584000c800d4002e2140c0344e0300ca14540c03003c3e40350440a54410483d800090005050642d0750f00010710140d005448000d10000b0003410350080c82100c1c50010310102941d01c02440310b0184090000d20024110700d40e110600d032491504170185e01b00030610059800403009001044041a82c0c000811686401030000e4000804241000ca900d42d1400c01510402d910140002c1d100b00304000c2040c4cc0031a0500d0601907400b000350748c07100600d503060f819008000400d40c03030920b419170020410040d1442268180e101c0d85000c603041d204800d82d42d442d90024030a200108070b0403c404044180300319421a4084014107000307090503140d8011504a1704240b00e41e000c020b450110300e1090209050021034101c3c4c18207001d002060441c0c1d514211000440c03100d21680702d8032001700e400240 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 101921061 1250 101919811 101919817
    0x30c0602120405060a061208090909070302060d060602010b010507030509010e060421050c100819090b010b070201030b040b030c0405060406080a0803100f060905010804030314010b071106070308010509090102 91
    0x40054541501d070510703060031500c07483c05848443c20540340c0180094106039118082030401c1d00075002a06001a00c014010a03000040440c0004c0c051014040010391324136001d40355512000c41c001610768100b003000390031995060704e0b2074180003090100000007548503080721407184080c0380000d00c0311031050200710306009603003158040b4201c4819014240302c038039108422180c0110100c0720420041d405010802044111000020b580703040010b0340304c00c4492100180c0c181100e00040c41c00c030141c450308518602038200001080000401909540c0c1c14080c507002000111000c00003100000002541c40c41110410b07030195840b08006020317a991640044014841c0e07c0075200020018a40000c1c0d40e03008548005500714400004140078074201101420386503503403a01082c00d4101001565421401001101056100d40b014240050720031135460082400350441a00d0b02200d00d07001803032424071042ea501900d814045031002c690700107401411510b043da150215a101c0c0c08080e4007900c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 101922311 1250 101921061 101921077
    0xc0f030a0e010e100e0a0f09090506011706130f0821060405090c01140d060909150e06041401180309060201060915032301050709050f03061501030e1908041d01060c030c0602 76
    0x1c081f90100007041003403600044201c5100e0800d50315a6a03d9030b14415603144110502d24140d4040c40002c3d1400346041405440d1902800c2c10090450b50b50f56401001e9003d00802840b0881c07a40c9a2540c000c1070a100b6500800e040f1418040b52500c02942603880d1410b428041c10000b50459040551100078100c87c2d110300c40e00c4061006a840d503d803030001d403c2942084401a4142c940e118907600f0324850303400e101c02c0180143c109900c45848114040d2080e0a9002855584081d2001d21301200000e0800d40d0748240c8500e1b0324689031040181c02c41310654080d0391100d0803c126008000340004005058942c010010303003000520702c3c4048030f09542e5000d5036140e503203820280040309400c42c01050885100706c6aa43c0101d85242c149500e907242a00c1600c5040f0105240e005698020303048423145d0702c61042101e240c06072441004030614035104080e41d40c50000142030210040c601400c1145802001030409554907121006003002d0502c1005010840d460907600c040221940481d0504 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 101923561 1250 101922311 101922329
    0xe0f0307090501050906100903030f050d020a080619050109171f020903190506130204020d0207060e0115152a0812010603060513020c030c0f030a0e010e100e0a 70
    0x40c503190440d8800402c02802254828851400016120300e404110440454083c0d1745051065103141d40990b141c6c401d07400548284042444031154481040c400b40082d103c556480386582d042240500c4013000c2901c044800c3c000d01c45000f8442079801000c0141121740004007087d40409008040b4200440d00c8048941c0f01d400207603140c481c2e00c00e90054014180101c040d120340e903008603d2640b654108285c0102641c1148001601e0f0104840e840e025032400604003615200210079402e0880c1d001000071124207982c1c01d00f1448000307091241c5a500c216031441610620b0621810f103101c1204000b512003085280c1d808550301e2603c800440d20302404050002c403440000d442c01d08940c2c0c10440007002000c014100002d4001e00c0390041404583e0054100c0009400d2020303031401035030104c1c000d0211440100702c540604001040500c07011200c03d0051030301d9442e072000081c0700c0d0a4084640d4100414030901c41960380d20344100000e0313245141410300c1750f030924102103492860180c0c440516 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 101924811 1250 101923561 101923573
    0x1b0403051509030304230a02060d020406030501080307020a0506030a0608010c05070219060e040b0d021302090315010b0d05041a0709080106060c2a030f081305010e0d02010e0f03 78
    0x3046400210700d941c0040c056184845039a50340c880640c0c0340021100580140c00b40343c42151700c9032801a044204082d98019100c3c0d0091702d030049440760703102c24094520303143d00203020052140c3c980f098038054130110014500d4504640c0019000100364002c5512070400007020a802e049036500441c02851108001d11407030741d0914001d00a030300242c4041e8042c407541c88109285801d40c455003001d481040c0c46000203001503c0501000b030203681055500b259031108070f480545c0d1291200440ea0035905009644c03043c1020a00d820079081d41040030000fa5000c005120b0503030050180c540c0010b0149000a440d50703a030804441c00701d40140d000c003012002006010707440790b000d0b42c060b00360b41e0484000d00a9550344c00d81280c0308400c10001900610403c9511144190300701c8502440d032526407042400982c50ba00d600c214409000b0781180d1085002801440c02800100c550004000c2401d01103200405c000c0420074520521100a040101c0da80c0441850b40d500588608095405021100 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 101926061 1250 101924811 101924813
    0x60203130c1d070e010f0e0402070c0801020304060c0c03021f0204051003090c060212120903040b0310080c01090605160201200f0105130f0b0a1b080f0604060b0703081b0403 76
    0xb02c2d810020080b80300c80e0140c54000b0722101c1c060892641038200c180e5906054210340c04045810341c490480d9154441d400700481d0010468000350280900300709000141c0d00d050070b191940407100380d54050000e1203198412440401e8001c80d0603003428000e020f1105002d180030a0f004000c0c8100d411540c0d10556030b65201852640c1580620240d0b44030729080b5518a403034503c00c0e81d8078401100071804415007040044c940c240e000d012075821400354001c40e07080544444a00e006a04110ba01c9403400001750420451500100401030304032100b0f00f88040c10703a080c058000c0036032244a03d801c01d40d045c0035008004691250301c1c0460647c1c6a07412000c0010100070340980c0300e00c1d030400e05110542c00e00c40400c805650302404048600d500c003500b841681d4665842440400c17008007015680380d52441d5484c11049050307181500810705a4031200e8034581440006443d480203055039000d5440e069080c400050410101c507800350f00f505015a103559a0443c8a1300c050191011950500001c24000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 101927311 1250 101926061 101926079
    0x3060c0804030e030606060a0309020307050901081c030c0e04021309021b1203071e0201090c0e04200109180204050a0b07021002030715050c1308030a0228060203130c 73
    0x180101c0c400c3e40d94514000c05502096500c01043c0c030050f40c0010100900c81402d802944900100341c405400d8800031a07460000031105070099001c00a207403c01031042d00040c0c10342d50318010141040c03c0c100b013400e841e00302c014580034541d80030324021540018440c642000c041030500013010300d080203659562960b41190b10090030744c2e00c4110144a4500b800072038032001800e49109860507907844035480307c45803c41e03165581e0140500309656131800c1240224032440d02d180050480b4200c43c2803181031600d00a0395411081c12810500e5a0842e00c2c40c020340c1c0e12641c41400c1b11501046682c0070740341080701310020b1099520595000d024104000b074080f21400107032030440d008840d8a00341c60f200c00c00a0740c0301c0c45003c80082c40b0080030611072030741c8560780d4040f0340c004054504050501413000324114007164141c00c40c60041c0e2001c956800c2103a4108038040104c0305410715101d006201c2050415481c1400d0402418a50007000061029541114442c442600000f000d62400c0d507401800e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 101928561 1250 101927311 101927327
    0x608040305072109050a180209060d0f0c0e010f0801030201030203070e0301050a09060b101b1403070b090d0f09030b090f0d03020405030606060c0606090a1104030b0115030908180a03060c 82
    0xc10f010a00b00a400541860901e4000d011180742da080c95601c000c20050700b100039032091500d1503102009100c40040b4008510460702044d00000380007948122621000c1d0a0101d200c40080c1000403185c03004440c40d078010750090442e542130a000d03840c2d4032400b0007590500c0388142034a4240d86030004000c02030440f9002591a1400ba110812041d104807051002007618142c4e08004200f803e04d9494000500c81e907071000940c010107101c0000f00c0300c0d10320070341154072064083c1d403060586410300004203030500c20400ca644107403c04003104400000003508002007880b024050090190028442c55801e124400c26014030005940c6400010f42001d4000e40003401428004d2040710000b44450070084111403030041020020002503440d4070410100c00c00081030001c0040c0c98280540c5054500f102a01c081c40c41a110850305605040c040744443c90b600707404600705030a010b03105000c07816802c12a0804403500d9041500559084081034501c121944010981417802c8000b60030594044a8 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 101929811 1250 101928561 101928623
    0x60b1b0f012a0503010b0f070c0b0d0b130e0a1407030203070e0a05070201110909090a080c07090b0301140f07110703060608010e0705010f0e041103090705010f020f07060804030507 79
    0x1a1001400c42e80d01c0c11291070109019130008114100050301e642c607103030780c041d2030344502c80c40780c0002d210385410141c2d03e01c5e00000c1c48141e000d511401106143e10304079112904580114104100403e1b880c81d144d5510960408060301c01c03040c0746002c5c14601c03410f10411002d50f4000d8111045030340e540e056180c00710011a21341c40780c5803528010601242c8180030b0395901c01002100c990403d5849010030007803010103007200c40c96201c1e40014100180010000d881d2036003013034016010702032902038850700ba00c840b01c1d040c510991401a1503c0c4020250704800d41010144c001000c441e40c440000f96410340305072040c08014440d10100204020158100006aa4030b08c0028440760301c1201c0e400744c0c0da21060241a02149490303146964592040703c000090400041010030410035004012000d030f0b005503031156160308070210610003540c2080342c50604034020700c01403221a010b801c2c155116142809200d0400802c0d4000c201403511410030f8490498005d00c84030903c0c0340c0320703c00400c0807030030040b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 101931061 1250 101929811 101929871
    0x30f0a050309071509030201030f1b110f1f0902130f0911010509030d0e01030204050d0812011a03040209041103010c030b12030c060105060f1603020106050f04060b1b0f01 75
    0x110108000d21602001250320020382c075028031490441e80154080c08000303200c0c8030001d07035500031000b040100c02150400b41c041334546200d1041c080d9601400d1845402c001c007400c0c0d001c00a00450f564440e031807142d2428400c0c400040914182c40019440400e440540c0006810b0440d20141400190f00c01600030340305500f030081c00501a4010348650007081070722a4183c0141541f80031807070083d030380b01d4512101403400501c0d00b9254070001d4101c4070290000e58116001003110400c07120300750758983c0035100d12080030844803c3d082c9d10304010b12008100a008050a81c04a404c00c10860900154010700034000e101c20400040300070020700741400c2c100e1288102c0540341070145800b0048400e00c80306a40548820f170308003418000140d10442210f103400808001a80988003560b040ca402944a5030001c50001d20740010040c08205884807140f0441c54203101300601a80c0c1030171200da56811912928045400510603400e008a85904840650800424296151000c1c05e0565504d41081c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 101932311 1250 101931061 101931073
    0x1f0e0114100807150804020d11031f150b180103020d060311010207050f0d020405060f060a0206090132100306020d060501080a05010303080106050c03041a0c1903050318030f0a050309 80
    0x4003a20709107908080580425901000b01d0050305007511300408d81805a2600c0c50551550781c0400e1030440605c00200c5983c140031090640c015282c069490401e0390112100c1001d07040500200d01c0c2e1107841c0c1c0e00d8450039440da02d0340750320341d0103074055500c40c1c08114400c002c3c1e1540c03410422062024401418014001c0c43c070086110304e420551000d51020282c0002600c2105600344401004050700056100c0701a1142070f229507904402084907a00340d602811581c203040c2e01103803d4550142c0001d0548aa00d0a5007880e4841c40306101c124400b0300701c101e001038450b8480c013030418504d0f801c05020b0343c0c000144001482120340140c8101e035005c0c0c1c0c508070b4555690300e22004450082c0802000110010010055584180b02501000400905807864681d490010390151101701a40044680d03000c12100d404010070b02c0b00b41800c106140c103e40c0044070560f4014490310000b40311080c407111140034401d0240c0e04009680341780d0362000100c0e030303118010b040c082d0641d002100c0c0c6000504c00d11b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 101933561 1250 101932311 101932319
    0x60c0201050c09060c0c04020307050405090106020a0206070b1315060f09050c0301060e1513030b090d0e01110106030203030d05060f0607050316020f030a030915021f0e0114100807 79
    0x1481524442c0145008050400072000c0c108800c0d42e0003200c1d51061441031008038280c941d606c5c40254080c0030345407545a541c0d490030051160422050b0311000554014118030320160721040210f074030140d4401102c860a40e0313116800e1107400140000075115041403001208950101d5015005481c8400341c4074a80c3c1d0780d1120140c0984a013121002c4a1070028001045200c1c0a4403c15000600c024146000103054482c0c48c8015007080902202c2040d01d90300c104207005600e1045600149628081c0c035000300d11410160101042d0046a030401c84503c20130217465500b07520040c041c507030080640399030b13410607404100076000a950b5180f02e8003607450701c05524a01102101c0829a002c400b460408102c1c01580140c0e02c007000b016030b005290825903000035038080c0803404146203e600c501031014105090b80300311251204540c1d0540d80700761100d01d00046241c080000b6941c480c4c0c80403c19541d17820034940074000b00d502c5a0081140390050020b0342d200c00c01054152030410040302c40d4240d40e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 101934811 1250 101933561 101933563
    0x60f100e1806090a0f02060d060b070c0306050a0b0306071809090b0907050406180506180403031b030203011202060f040b04060f02010c0c030c0f0f051f0e06100b03070e1903060c02 79
    0x11904e00500866402801c0c50041c10410701624a0300c20360741d000584503503140880c2c0010783c480042200c1200c1c032218140f04000040c031075160844c0008404004007600c41000ca9645d0201a0920040c014105282c990440c000c035020700c0580001e943c24860900e240c50001c1d82000c0c260344027105405042c1c1c010403035003010701c60481143d40074003c44004401300b551250044c24090040307a040030000d0080c82c41c207904046500d0040e17100c0e640006454100c041c0280a810030340c902c050401d0300400040045802e4012031b03000d065011030780c4070341e50b030702c80050503409105a611078880050003080010782d031500041d0001020361140c000340441c00401504440c03002e0a040b0040101e20300611200200ea1001c01112445200e402c100d080000035031074040c5070030040b00050b031000014650400b0107d030315000d08503020012000509150920015030340c4a5038050084510b10600400022070035445801c5c10356040002070440014688048203481c442103643c042520f2150400c0e5110b14001d00c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 101936061 1250 101934811 101934823
    0xc0102130b0c060c0c030412030801090506040902130216020d0b060901080a030f0818010504080306011706090703020f070b0f040311030307090902220e010e09030c060f100e180609 79
    0xc0c2d4032014014682c3e9805005400c0d070405400c0200c9448284400704a03003502403a180403860198940d10110b40c034041c641810303110300510146c01242826074010040c0c5503003421040e010b900006c0961104e0b94844c41c903444941c80d14000e90700000d030201440a000240034028042d46040d41d1440e816a01c0e804183c1d40c41e11641401030001e0100460759403c2d44c8200007103504600c504241d126170600d5699038500791351064500340c820180c000f081c004d0341d68100f4150b010f03150050034075050030b140400c00a100608000c001006041c0c00281001c550107103c2c00320f86d0384d180c0c0050303198020300f00400c01a050050803203049020504018241c14040e000000307891040045a5135480d166041040070006500040c070324401d140040c00c1c48000d0003030140d50300d001411810810326500d601d485040c0c0a07040020b483c100c56908200714a2001d00c10100d80c2551122550a11204c10740b940c0d0a5040d0000255000fa41000e140e14140644805100607040c11f040300101140d00a850b13228145460313507 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 101937311 1250 101936061 101936077
    0xa03090b1609062c060405090f060f0a03030912060b0307030309080d0c02031b4207030207060302090a030b0108031201060206070e040f020904020c030c0111130b070f020301020c0102130b 82
    0x6051320a00300851480c003120415550000d04000d0800742d46201040340400265141c0583c1d0f0915002c000786420f01e0f244aa80108044806c041018515100541302070325601800c4088000094010f040c442c0a8000700002c401c06021585119941c3c2002021174605000c0d825030b500418185100e80307440303080c040356290340040c05016042c4030a00c03d001c83c1c0310751811860b0451060b0400701c1100702c6540007501001c243d180720841e852004158542100940410501009400c0c461000401d60008144042e50701c2d6080060f44d400400000810500183e440180080c00f95000400c0011011024103c01307405000d4485581e40c8456080e62180011544c0500080040d60307012018640341d089851304c01d420340001454041700001040c04d80e881100903e115500000e28600b440b0002d219003803a08030301c40c15850602c41c042d071610681800612510305102404070f9840c0910414090004507907034010003c640c0c884104081c58081d40002ea4126060f1054010020f107855140045036881 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 101938561 1250 101937311 101937347
    0xc090d1104270b010b131203021005070f081e010b0f070813170703080a05160606140901060207080c0121140a06050603040b070f0207030503030403020610061b080a03090b160906 78
    0x1801c110500c82c0741c08074181c0923001c501c50002d0344d582c4030040e44189801f9600549e00c13a408840e91600c040d00c2104040c01c600c0113580c664842c84850245030348064103542c101c100055581400004010840c010700801034014140003980110407065840d01104a804484503c9841c2d60203801c02c5071540c0c581d210292a0b454204030031540c1d83e1207440200000d000c0f5000780d04440170780351603400c2210f0a0350010705880320484503004552800c4001d941c01448184020004141000007413601d400540c405541480400c05020030f49a0740004108400d1018800803c81501030780043c104040781030701d14500380b5180400c04101420031108683c4030356040011520151901e440c01c44407810121741ca481140103001e00403001401c20f00003540928001e0303006090a0403e0702502c4203000b41d9901c1141070161161801d0b0803840c060300b0b0300c00c0c6190080207282e16440c15103c280c02500700640004c1c40100c8410800060018000d0700f0421a04a82d4030310107140c0e00c6010a035100c024400d800b042ca = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 101939811 1250 101938561 101938597
    0x5040e0a02040b010c08040b180909120a030207080a1d040c091406070f030804110f010e0d06020912010204080d050306180c0706050408030604050c090d1104270b010b 73
    0x240c01d190f00300302c11000c01031401c45000e080350b031104202d9811580005600400c0011800300510705251501032100301110300c0c000a051901c0d100740e94884444121075000c8011030320076441130090703055850701038010003a90707501c841a80d0028028040ca00440380c010440d04c0c00e2540c07500707141c0b0030104020075540350000f0301da0030440700304400440f120703089a12070340030001d5200061806000c540001e2081c0c86901e0941450321f0700b102041ca03d101d1543c0504a02c2009a44d03903a800300809168030b1b41034500450f44081802c0440c06132050605041d00070100801600744407105500501c12180320200b560402074109804480b01c0c4401c0d40d55680c000490040d01e00d522070520682a08070a00603600d5103000010381d01c581c20344004aa066800e004040100200ca041600031036500c80a090f10080c5011000800143c0c802c0425202070410a40c040203401c3c2c07511075612a903001880c541c040148a0801e11030300800c0b6214078400c030781c1040060000940780c10000d06660491546080001c4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 101941061 1250 101939811 101939813
    0x20102040609060e030a080a12050901021323090108070303023d0209030106060c110111120901020a0209040f14030f0d09030e040f02040918051015090c0203030f0105040e0a 76
    0x1450700b001e804c0345034103020302c445181c00551010018941c6602c0c0b5207403051113a509000740c00480344020108015a40100010b007060510030b50510306880034044c0303152100c01d0107020010b4140e001041d00f50040000000800d00c03240005c0c00008992096085410040c0030b03010041d80c484640031008440c4449210240c08803c5040c0e00c0c2c1001a01440c0050030505401c0c0007170300355902e541c400c001003005d5400110520004c3c0c110380c1c03440a420b00380000b02c4803c8461142e541da003080201400c480380411004480c0c0e1087c0301d000e1909800510820450506040c00c0c0b006108408088907128800030841c10020700c040142c900c05084003407481d060200d016030100c00341c148100101c04000400219a2260752144120903603181d821400507100c9040c00b96980c200d485500310340480300e0012518a001a03000180066400403030503010502038450208900e0140369900300103103250a0a501641040d400030255105a80400c4030140303590b83c035400d04c0100c50f05494042e00540160103410 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 101942311 1250 101941061 101941067
    0x10060f031106070501020d090c080f0705010806030c0a03080d0b030a0317041e0510060504110f0c0102041206020c070f1214030f131404060b0d0c0219050f06010602010204060906 78
    0x4950700060302041c50700415644070350890f4018440b51007807a0355400c0c1c0310103011f40d0004040140100740010a4030000c01c00401d0b43d0703201180306541c100800b01e8009120780d141800403400070b52000c0d00e1041c0e11512860880003e4000c1c2480c01c0045240044070002807400080c5500d07000d0300350701d521b252a50f25001c020202c000c01001980c514601543c500110003002c0032204006001e0400340110540b02c0d420350003902c07243d070300a0744124242503214130100e6004045440b1005e0040f0311554444408000e40d02a020380d5100c400030b143c5169054040c40ba15400411283e20340e00152450796482d4407481400080da801100209201404800d00180d041015240000c0c000411207041c03247c00c00e041c2076180d2000c0990b070340c1c15143c0481001141c4490b036003980c0d400e000f100c080c4145410038080781154020115100d01154840110710318150003404201140c04040032120240c034403d0070b2041d5116a0304031000c00c035200d5400001915031041c42502d003611000d545076544503240040032 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 101943561 1250 101942311 101942333
    0x170a0203100e0702210d05070e030d0302070213020310080c150a11011e060e0a0c05070305030a1107060902180402060a030b0303040503010204081e070609060503180d0e0310060f03 79
    0x28007507118070b1020030000c91204401c00584001c84509079503461b1941620001c0d1400070302984107100802c80b031103090350b80108401402401510b0016114540d9000140c1d001202c6c0f146180054400000e10040c2c2c80415041029a031480046844889150040c00f1810b00ea1501200d0380c3d410034405003500a01c10400005a10000c0001003986081b000707408078003150001b580d081c52980c6a00c1008901d584ca01c803140d2120028004000c006100342d0041c10034401e260008080000000000d14a42c1050b8070403a80303c40b01d510400c3e203440c0246085030003044850000e070302ca0108200e0a2090140400c119880703660302400700750400d51468010307005804280061a0b15001c28040411951000d1002e04010040c403401000d282e191101c100010fa1005140309202d030704820000c1c0300f1f01d504901214121003081c5003041c2d8035030b01c81080000904c1c04145443d854010034600102c400c1c1c0c0581c180c600340008506654000c60000c90920403102c0c6485030f08045448010100045402c440d45 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 101944811 1250 101943561 101943571
    0xb130305070b0304171812010c1d0d0201080417070302030d140411040507091215060501020303090607080a1d070602010c03200901020109080c1615021905120a170a0203100e 76
    0x404090030006c00004502e5443c640720000b282c0c0d034441c0c0e40b494881e8084200355909180300c6610540303201c01c00114044035201034000e4103100c110740200b01040183c0c00c9864554400720b00381610b4881c140342c001e440340c3c00780102c10800c5082214035081850782001c8540910b60100d5401c03100d1200105100142034010070441c00c0c000c0210000a0b481d0303116044c200e0b40f5224400c8906000c00e1490500109d030101e420050441d48180100503c0081c00100d82c3d4101da22803c240203203649040d44503000d01304007410560040d0881c1041008540009464020303226641c000b40458000700d034085086030300b071405001d1016a80c00900383c032020b4981c014540c0c040180300105e03a1003120f40381d15000358001119428154010044000a980d04910080250505000d00019060104030081d40c540f821120079100780132502c0c00c4c45c2040b50810444192404814502d61a004c001401400c0b107da42c00151201034001400100c4940c1c980c0308884c4165910002c10692070f051104d00a594080109 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 101946061 1250 101944811 101944837
    0xc032404110a050403050105010e06060d0905011803030903030507020607020709240b03040b07030504020d02120a0b07030b011206050105070b0c040b030c09190e010b0f040b130305070b030417 84
    0xc4480481c000400041640910b00e403501d996032441c500d4240c0c211003050b0310810155205a040c00300c1d503915003040340c0903000d0071070011910680c0c07400d2550041c01040528680581110700440405030140c01401c19507000c0d483c1040903668808050381c48540481c1d4040c0140c00c489828412550b266010010002c0301d00d0001e4180302480300d2075160103030705410490394041e011081004000321509090b074807002e6440d0901003804e0039070100703420351148400280329520790704800060700b9082043e00b43e051340241d80715503281400c400c00f030010030903003002500041c034205402c10648064040c1004446040c5e407094030380703251a221020f1032480684040c45501042000003070540c9004c020354000c00618107859522040c10017040102d0b00001720001c80500070042c01c100040912003010f04650b4001446030307440c0070740c04d0116550700c915040703c8507003400800c600e9107541140d040388080d40e1151040b260641d8035160083c0342070204560040c0400554020302122500d06005800d3310740d0610 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 101947311 1250 101946061 101946071
    0x917030409020c0708070902040e0411061603052a0303071812050d0909140403050a0302070821011a04090209040204090504030e090604020901360f030b0c032404 71
    0x100c001c01039a10515028085030300200090002000c140403e1004007940e18086241601d05103098048450003400905081515408281302e612640111403403000145c4984090342118900600141c2200c406100007010360b401845200030010320140e81542e81000a509654503e030702115144000c00d40400300d0004c5a400161820305589c645400b14400c9020f080120018080101035155a42c4104129401c0003504000206c80b420800d420a4241c90300703d40d1600c10807002d902900c16540002d05c491b0300020940044000e40c2c4c0c0c0540011410001c510950b40c0e41c0041d00c105411584c100850580101b03c01c0160044c254010440498060800f5003829603909440007100e4003201c082e00840c030101d21010a52030f02c034007510b41c08403041740c0c00c5081001c520002812400c0008440a24100c0c03049000b503450040e18062007480d01d800300005556803940103110341030245100c2142c40c80d640c03801103003144140390140c922400490480480c0ca4140225000381c0c02006481260020390b00c0f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 101948561 1250 101947311 101947319
    0x80a0c020a0605190905100c02030c13020d060b030609070c05070509071101241a0403080a09061103030714070f05011b1103030402030d12060801290301050709170304 73
    0x145078064020402030302e0303a50b02c8031480c1e401011074400c04011001000b040080c184810707542d8510340b0064402c13a10b401c20017130f4100e20109240403901e420165000c4e1600701c03080b13070a408076002020851070741c8805000741584e03000c80c01c1450100f62100c82d80b110140c800261290f1090798071030002c60140741125a12641c1d01d0100e21039000544c0c1c1a00060928003c44094102c06d001300d1082c0f00070342c0d00301201113070141d458411030056400341e04451014001c0c030050f1004005c0564001c0c40d040ba540383d540703c50104000e00104164450b4102042c40035072110132062010058038451825525060000b4038545910145580124030403109855881142030205000b44147d40c12501041501d6910514011000d0004e40c11a040c9048945c4104100801078401080e0751b0b1799145241010390006644000d02c401a10003034001406662030408400481c40211200b510304140f50540041a41c00b03502c01d06088e50000c403842c0300440c22001c001c1010418196407001110a401d0a4034242500c03 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 101949811 1250 101948561 101948569
    0x201021204080403020909070326070c0f061706060702060318011d150420030709140a0509010c08010e0907120b040b091609020906070501180b09070b0304080a0c02 72
    0x1581c054401030400319042c81103082159103150880c40d200020a00980342d40d40315900c1d94868080044843d144145101c01044a002a038aa440c4c3c0a00c0f0001d203030781c407a80c00c003d0309003c61003202d000800301c0070b08100c07129608910b94082c24004c1c024516003002c540034441d2660000d881d41d200e402915810603080502803265220754400f103a405110340c2d90b1300259521b0a5040c09243e06584040c3c820301000600161142030b4020007207074025003011080c400a4140180c1da0301c4107902e5820010340c8035000400b250f00901c41c19080400b04010b403030300c0c94030508a4041c1c0002d46c0201d00180018401d4a91041180394011210720403150115281e811182e0083c3c103400b0200ea460980d54140002c100710301210b1944900d40f10000d01cae00028107281008520054450b410401340d0010b02001191908400c60b00003a8001d8000d000a4100f5514811750003c0741d00c0c1501e000780c808003c40c1c3c41d5240810703a41c0444900d0746c2c4450840d119070b100c1e0350b4154091250103050010801401c00140c81d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 101951061 1250 101949811 101949847
    0x9020304050d08090d020c0d0305040b0f0d0c0f080402092703090405060d0b0705030403030f06080307030f031b0e030703140d020c040b060d020717030109091401020708070b07020102 80
    0x4030400c06007048801d88003025003d603802805000481c0c2142480d820030550000381c1d00d0200c6011194107100d00c0040c1400c1c1c0d01440b440d000703501a0000002d40081c48040c400041401c0c06262204004551542e08100d07250300e102025940054000b07000b0802500e8665410364210802c60200c43c89802c507072001070314485403850849100c1e00041810340891a1620405520550558249618008556038005070180c0107000c18280540800401c05141c401e50100d0b54950490000b0005c440d00c0c0c0e14410707502d030007100b0214000380c00e01d03600449982c0700e070080300140c1d6100311640720305d4072411000362040501c420003241c25120300c0c9000000f042c0b09405040c141c0c00428040e103042c2100c41c0009003000220240180158149696900e90392070380b004560250b412a1300068440b006480c12014806003c03c1c880c91686002c0000314034580c1e071b81e002c020502d1003080c503011140c04101c6024240d01070024060b12030041403003180f0105250001d41648182548001850000400d002c1030801d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 101952311 1250 101951061 101951063
    0xe0702100c0c031206050a1814040606050f040c020304141f08060108090703050a02060919030809010f020f0703021009030803040c05040606030b090c131208030a0506060703050f090a09020304 84
    0x10101d04840c418103820240c030f000ca142111300280072660402e408541c03004114481c04034181004450030b04030100b00d40c80540f04d483d45901c940b00d41d0501d0700309140541214000e1f03510884d00c2c905265030526191066412466058019604242c43c0450b0808850121904640c200401d0b030403030007c0350821008030244881e0f98880114600700f00c0d00040c0300104c014150305c110b40c4140c2c01840420000214900100e43c1100c4081d60f03800c40c1e00200700c6900806000400f0491225004003c101601010f441d003920b0aa840d1032044c900c03d20200d989026081d849221a08180802d10150520901c030114002135414084d0095949540f026a980d10840f8152181110f000c007d0045150a0241c1070051015107014043c1000d03407800580440c8020b400c00161440c0000d40d50070024008001ea40101003900500211145504000580d540222034141405180c20700081c0329181c44402d4484050b0903075981810b001411182c0550355101d02800e6034004080302d0005662200d07400110f11036 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 101953561 1250 101952311 101952317
    0x61d0303040b222109090507030504060b010f0804020f010c0b0106020115050402030c031306060f0e09010b01090303020d03050c04231207062c06130e07090e010e0702100c 75
    0x251510500640c3c1081c18410100b64008001081c40081650821070000905568118200314030910500b62001032259000b14400360134501006809a095404544640d010351001d102d0455010011140100ca4411100104100034085005400c1200e40c002401c0d2060401d41031401a0b51a1007010403800d17801000180c1d100c1000d0316002c296164440c2c02004203903802e41c10343c1011151039002d0300008088a4440300818880000d01c00d20342c00840007844401400c0720881d0716040c4d00002d01e1021282c44110350f0070100c420744079512445a10040b40c3d0103034042c215a229000003140903220140508031444003d200100e054140d180b540144000450185070300181d4040c11301c2990071030a240c920302600401c03000c1151076041040040040d81451210b0648401d042c4c40f444074040300c080707082c2c01c51008603001c690500d0b21054a0152092440703018115901c1c4101202c0082080c0a1044e12440d00401003090411011910703402400c42d00640d040c102d03100c0341c0941203030f05001c180400 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 101954811 1250 101953561 101953583
    0xa06150f03050307053708071a0924150103150b0702010806060c0613050102070209180f0601050901060c06140f060a1a07020f040e06190b03010b0a060c05190501060906061803061d030304 82
    0x25040003003890920604200d480c0295003040500c1150f00000c00c42001e00482142910f40ccc2e07072095105103190303040d6081c00c1d0000ca480d200803c0c15604420170480c00f081c56040800d0051400c8020350310442400300c001c283d99683c0c40d4826030716610132041241c40c1e6409005100050f95007a29132403140407908840c215650521807242e00e40145411580382070f4100400501c05a00c94480321030540b20103050141024401d443e00000034201a80d8024141c10f01800380301865010041483c00742d00115070b0620324a440f01844040c83c98007814101e60100100016001030030011b084002100e00104005401035041c606141002d908503a6080d00200b03440035100c40700c02c24807031030760303500070036802005062a054045040d640c2c1500030030003440002c07004401000410032269140000e459640301c0b071002c061402a02908081c003821030b115041500c045110303403048005150000e02c441c040c41e04640748d903c40320010704080c04d500040c00c1c03403d0b2070100b0b00380b82080114096403058043c071034 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 101956061 1250 101954811 101954821
    0x1302250303020904051f03120c060e0604030207050a0e0105040506040908120f07030b090a02030406061e06020106060804020612061201020a020c0306010f06020a06150f03050307053708071a 83
    0x2c01c80f0030003000038141b88001d56083d1107000030a5004000d60354060b4001e2088130040c5010341d0400452600208440e041000011007414086a803d02480c0b00e078003150b20300da486d801080700182e85030003500d03860a05000100b0080c034040e00503a4018a015000040c03041c151380f20302405901200c100348815415100380030b40c600b0380c00c40c915448255450300700b000d070405400044848001400500d401c94001c008035003031003000d42c0008001c5c4501c110b0103902d1030025298622100d01881108055440c040c00000d40a0241080310310595006103c903141c00204840440c090001424903600040000384c1c0b4108004248004e10800c3c5854004054520781070041524004050700304840c00f2540000400180741c002480d0381c51203030f101d07034007150381007a150694512240c140d0020402c000c0c040000010301c44007100030074120303015606a03001d4100080100018003400c040d80f800100c140c6c1c3d040100e070401d65041824903407090840724900004d0313480b200d680b0124450301d4000c041d4020f003808 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 101957311 1250 101956061 101956069
    0x27080714010c0e030c030c060331050d0201150302060c07050310020903010501050d050d050a1107060c030e090420030a0602121006080c0d0c020a0b040b150a0513022503030209 77
    0x1000c1c844049000300916405400420349812048000c1c1c0d005800100c0803411034041112b901f2000000250207134000d080392070070080038030b02d2824103483c030b80184112140c4440c030601a50309001160b01400c40a0307817a59091000c641e101541c03c3ea1180035140300403c5c20f54050026641e207070380c108000b42c0c4403000202010300f101c0041e80a84d100315010036141c40000d5011640840090580c20300315150540c1c0c1209459424032400200164050140c001c10500c0c1c20011884400d4020ba507110000c100060502c120060f06440103081006030034149048074035030003405082082c000d020b44007400055074501c5c0c140d0f00403894541c0a0800b900820016802c21510038005120b42c0c6000141810f000b0020807143c030401000280c580d8655880d0701100780204040c4d4001980540c40f40c0aa01e0182050403180b4010384400f0040c0c10b60018148140c40c00520550688000415495110258402800003984900c82c001c80032110203041036508080b65420358103c0e40640c50151792281c4081c200 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 101958561 1250 101957311 101957327
    0x6020c03070510050f04121b090903080f070207080f0106031b0b03010513110d09060e0d050d050a09020315061908030304060c030e0f010614010327080714010c 70
    0x250007a80424400c0109a90b21003071405000e03a2410415505d10004072070407074610442d001914540314030541030782000700a2540100d5960030050100e0b2280c0c541041d0002c1d0b03034002d80081c000030044008907101201101c03010307411860600482c6d100071394415a0f6400d2001c081d8009071544d654a00c03c0050140a01408020b412f0303814208035550304051842d0820f00042c003a10307010311200201ca41d01040203034001100c11121901154448200c0740c100e0000d4011a08115841d0381044105400b034400042c46103046a2642c41d12410090303c1398080380105001003203203000e180c031013150720056113040c07180341e4460f0900006101241390070428441c43c030001004540500145400802c0401d4020003036a81055100300013240c400e00c4031100701c000e002d6403003030104240113183d21003108000c15400b0800b01d4405c10b0001d80501c000340d0064048a080c207900d00760034004442d03550512030030a03d100c2080340c4160420b0b4203015007504c442441c19800c84030204242c0d5503441c00e5007080d8000242d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 101959811 1250 101958561 101958583
    0xc08010c020303100b0705010b1e1219110a0b04150f0206071b17040b040305070905130f210f1209020f0f01090503010905010b01080c04080a15140108070602 69
    0x11482c6040881390802440042d100b5895148000310300b44c41002801c0d007002d6101e020046c80720b542c524240295030100d109589006104400200716100452808a200d0720202c100c510340101e025425211003804180b40c9642e1035100080302d40214180c0720207800341015064203041401c04601c1e640024181c0a0140d062134150341c005c504100e000741e07000d69900d5100c50620308060244046141031120110110180c0114036004140822100f0041c009042101d0041c3c0480c2e10301c50340c0710406021100140e0720072000915200100012420b480d180c0c410040c424031205207500d540124003d0104d59003941040052126010303146d0300f070350001311283c407000398542c1004506104d60010300b10700e24400c5032a00898000c47500b90b42903809180c0c154010400035000348134600721450300b98001c050078007206000c107a8401c0811000d03001001500d05031840c20005101c0e4000c1c54683c0007408803074403d10305819455074407060250128802c01402001904010f01c80c50b8140100030b4200110444 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 101961061 1250 101959811 101959813
    0xf06100803031b090d03031b050f042702030f0411011806030f020f0705070e0f04120804020f10030603050f01290a05060703050406080a110304120216030c08010c02 72
    0x10148500440441200e800904075415101d00d000d000030320b03c040c1d0142c400c00a900008040301d8005240d00343d044191649543c82070445044803004055541e801180c40c0c820810400b4442405141d03070550f9052003104402a10150440752078041c0d800303aa100b2100480d009a04100b440204001481509400d92007400e0118580340380354007000481c0c010740709507402c00d902e03064150502c0103039a04403400001c0c0c6c0d9900c503036164603d00b080340e5100303c64070a4400c04982603000400400101000703c1c050781d4005120106c41040100490700c1e4900503000b680d101c105195071240c1c0365a0300380c004025507200d45020440c14a5070801c1070511344802c0005202e6410070b004c500004401600c1c17400008914821242c00c40101c5010484800e1a81c1010f070b00a400080c01c041456040f8014004507200c0d5038400d030035681c4900003801a00c100300741d100800c5078107102107400200d440c15116401d0401d441226003802d07402e2408108030345658000e42d0792013074240d02031204c0d09003801501da001d40140 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 101962311 1250 101961061 101961091
    0x301060605030402010806092707080d02031318020405062205011e031802090103051006080c0607060f0b190918120c0302010f0f0501150306080309130906020c0f06 72
    0x6000030300080f000400151240005c0d400042501849c500100010000741c0300941c1449424400555640b455024049040c45450400e040484c4004212003220300741410040ca030600d40822907814848150384e805404d6001d20022400340c44100191440b0f45003004940f40030009448442000c59141e00440e041049281c0d80044103032004400c104184900c3c5400100e08113020041703041020481402941300312002c00000030302c280052440c00c1d000e848a010807070b10780c2c1d03000303a03a503101d02d001c902d44d070004000e101607800304840c0da0140301000000440442c011070b1550005948164030003103400c076080d03980c0c030500801c3e24501c01c0340c2060f4034941c2c0780f01040d1116124210f0b0701561410718010490702c040c11310b0030036200b90004100d01708181e200340200c002420341a809000c0c00d0003107a829521718401142124403d0150204807003000015500d810704a00603c81c1403e0b4090852030890340320807000c400941340384000c1100125000250440808201810303083c86c0014103030300351000c291 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 101963561 1250 101962311 101962313
    0x306010e011707090507110f07060801090b240406031805030405060a050c030301150f0c0b0609060103090812010e010b030108030301120c0e0f0702010609060b0913090f06090203010606050304 84
    0x4861040c1c15608850341216000c0c240c509407616000750703500043d2000d0f00300003d100540b90040c61422441d0510416201b0304807030034040d10343e54002c51190b2400200b901004220440103a408203c5c80c28010b80b8401800e8814075010200014845410200200000f03040002e540c3c0f502c5103104038614a0161103000030307162202980e034000c5005440c480d05001402d04d01c00c501610449180742440c1003030300e44039a5182900ea550b8810b40038928081600d0f07120504130b440c410900344c018203602606080349a2504000c0c0711070700c6001003000341815507507813404020411303810180505600e84c08141c452581810794000e880d0300180d0046031050b0080c0014069590040166819503030240100001040305062041d03c1025661100c24014481d80901c4505903105603c00d20072803641c0c000340f1685984014036070455156118001c60100d05011481d8a8500300074018a0203045400c0403850a009440b0150340c641c1c415411940c0b5a03a8180b24021804c1c00c2c003854005100a0030b10a0851410f = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 101964811 1250 101963561 101963579
    0x309020f09310201030b010311031b0903100e010b0d0803040605060105070c06030218190303050705010f0203070206070e0a03030c023c010e03070303090314010e0a031706030601 78
    0x240010107200e044078200140700400000c103200e401124244042c1014030448151030040301c0403480c241d00007070801c01407142d194028051065450030221070365203140d031001c002c0b1905c5103018400040b210800c10092601d40e50420500246900140e0002040c90400480500f1546010303001c07400f60f11813010301008118102c081c2e83d4099080440070034940c0d110340040381c0a210380307440209520030809001c9101030745a4003038410400d00c5034a20041c600d1079410084142040750340401303038500048092001a2261018000c5940314600102d661890b805405041c0e81080341d1341c0c0300690101c410845025032010180810715001c2d14140d40c904d0850300e00030004a15194040e004032103041c103103007280011104070b42c0c0c00c031450782c074403180102300c1103100c01c0f00c000c41803103d400201103260398055490049800300451381d03d915000d00d101d2a5640b902c101c000c0001c1d88003165560303100d115141243c24060640d603c0c0c807a6a84500811041d40750340780c03605020300f03030b607009a10141c0140a070140f = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 101966061 1250 101964811 101964829
    0x200d110a0b040803130204110a02010c140306040c111504170406171509010608010501090b03010b0304020d020105070b010b070c08010516050f1c051608070e19080d020a050d030902 79
    0x1400803c6182d50b50340300219a4001600420000d40051610400341d9401c0703074450181a44421942c0203001d1031180c04d03000c07a000040311503221840c920820100341c040c035069106007a080d0040c02c0242c0c41c00c0d880b90010781014440c1e00c00264200c1008100f0040204c041d500104242e46c02c6038090038039044c107000404002080740c100d202405400c010601c0b900301d4854858050000528882243d80c542500600d403100070b10960b400314407200e1010030021140c10659050f0ba1884a6007030840d03807036800300b20040784640001da040c0003040110502107502a80003501078107606c8911079464001d07252903484080079038010701042c3d142c1003c0c0958991000140d44404080d4a041e50f15400b5840000d481c070f1090b0300c407021200159140c4002429901e80040f44281003581c00300e000b84140d804141c4042c0000c40d41c00000406a00346842c0314540403500901c0c4000100f00350442ca80ca034400e203450010056600b001592150000e001000402c100044003907545140c14000b40450f075001c182210 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 101967311 1250 101966061 101966063
    0x12030703090c0305100608010617030304080f09030604060203010503060a09200a0f0e0105030f01060308041712030c0909150307051e0904031115010e010312200d110a0b04 75
    0x10748071200710040c0104030744000c0c0038681150584035003902e1800aa0020030345c91050b00c00c10b5007020000201001c581c21698011400c00d0059451a619603a030307241c8685c41540749080b03801003401030300e41075101003007140d203c0c0780700e403d00503500d50408003003501d031501c02040074a0b80b500f0310211800142c480e00000c58030a051050900140300501d00043d00e40300190000c0c03d50041440002407030440789804035040756010b0f0b05441c44551690041070a0315954000540f0a40040004106507000c00c4000c0c841d20804005076618000d0141001c426540f007940c407508044008204c84400340f40490040d0307000007c1380e640b90004410500401c0d00e1b0581c0307200b81c83c810542d0300841081c443c900440110102c40007400b071501d501d80b0345400380481d008040203036003d00c0307840c0592407240a1b4401c154180d03a911112240160301e50399841c4c40c030f0140c8d40e8060b0104025090503c403030071030040c00c0d0315001d0b50500281c290350310038403030007803ca12400f5000c0a95038400032001d00130601080603c1e8010f = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 101968561 1250 101967311 101967317
    0xe0f040c031401110307020114060607081e0702060406210c020d030c030b10020f1507082e0f150206130602071e05030d0605090402030d030506030a080f07030809120307 74
    0x2020794280043c0106410038452a040c000007081154180e41988000c855011803441e415032603c1e40c1c81030000c00d000d0501c00070800b60b420803584024844c40806242103803040e0313400900c0c0014641c04030385550420384c84880401e00c85601c40722599480558110b0030250301e60f003002048000f80d030080d9200c001c0420042030503a20859030035414425081f282003200c025003460204444203c0080d5101c0940c14082c18901685407207045620200700224024041e076030724031a403500d94031280b60342c0c45a88982281030442a014614140200e600014010f003c00301d03940c2c452518000c040d268070410003040c0803c6400000400044460a0109a1026400403001070320399589207854810410000424440407140d4003141d000c10174004014031104280c0841072040c0c41ea1501840346013a4155802545070b0043d00c415003c040c803d44c0302c5584080024211400c2403626101d90205030b004c14071807803040b07500041d24401d15070098000d54016030b00000a0001d0010510007103500d0001406007010 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 101969811 1250 101968561 101968583
    0xa14030a0b060d0f0c0512060403020c0603130b16090503010b0a090b04090203060109020c150603030d1104170307110d03140f04030204051e0705040b041802040b0c070e0f040c03 78
    0x5079445003015443e00d039512407590380c44d01d6150300f04414200d20301e10407644280003142259825010204c1ea040c021a45500200494a6140c00300142c0307420017018071010552001045010030100300880b40105d10325007150500e9000010300908491aa40009000340c1c1401184030b40c540391280f11800304e44031041c0c0000c180c8000c00014001d054440700280d4140308940003c103a8060b994010000820400c04a52080c001d50754400348000086030b07426403580050051901005240c1c0005c1c02020682481500d410780b6250580d908407100c284442041d44013094000c20807032140f05400803508115603580d003605941d90014002c4004540d008240d0340003007000c000713201c4c00e1410344014681c005d200303001d0b51410400c01c503605c50170080b4981c2480858000f01c0c01e030318019400c031030542d90740306186480d146c207102000038003624504031402001d83c20400058014070420280a90718801c0c400b03081118580b20b01e0a0020202a14002c651001e40081c00700294111341e100c030469511080041e2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 101971061 1250 101969811 101969821
    0x1e06060415110c0d1a1b030c07020118060509030f160b0a0e04050a0e01180201021e070e090105090609070501231605010b01020d0c050a020405040213060b090a14030a0b 74
    0x1050110303844965402404c040d03018001c210309000310055001c1c00070903a40d0581e0303a8002ca4400c2c6550100d111000d1602000814240c5482200812000307006040041000c00e0601d11003511000551005000440100d0f40c1da24030302d0700b4400710b400b240511000f4040c003000c02c070b0100500001072080650300000011010002401040240a0204014400c108a2600c2000071000d0074031190120215440c0c01d10341c040302000d0642c055425a0103074000d0601200c9402400c0344104462100c031005c0c0b00b59040011007032504914103200b4041600007103440c1c207000e00070a160400240c00200503800480e810f002e2664046400c60324034840806c00c01d070070381e07082c45001802c9c841c5220003000c0c80d020400c00814000c1c15000a214248203034204d03076890101e080c0071104841c546800500d5908055201c3d00545880c2d0000394010b4001003041c0000d8015042c2481110925400f1800d2424007144545952038201140300042c10007080310b0b40b4014810300000c2e00c404090348010082100ea83c0454 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 101972311 1250 101971061 101971063
    0x71107080c1c0c09020d0b1c06051008010207110a0608040b0402090403050c0105040309030507080c0619020c030a060e0105010b0a020d0f031512020a06090b0412050c04051e0606041511 81
    0x4502030303042102d2000f515200d001d02e00107548034a0f90080107034201240c69103903041003403103038031000b034181c030951020617040c0c2e142d80180c00d011300311402c051290b001c04100c03c4001c0c03009004140c41591450200b540500a02c1280c0c4560b42c0400240100b000411020500d000c10943e40300340c1c1180d02d440660b0744c602d015680c60007034041101c855880c01c0c041100301a040000e90080d07a0140301160f041c1c5540b0361a00741d450701c810780f5440d0480e205000007032561038668280d84110700303580103a526031208403001c01d140000d8481c0c1030b52a03544610500c07600c0c550030300c5514050141e441c8841e181c5485500003a5035011319029200c02c00840100141249219900c1304140700c10b07846800c441039584a090082c21603801c0700a0b88181e100e200e00086840c0600d540700d04454040795018145894521030440601c1b08010540e402d0246e01400f4204e0307503480c0310f10381c45207000c0c42c49494040c00000c02c82c0f07101c2c00001c000500078142000288108401c01407144100301083c81c00c0307031240400c81292 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 101973561 1250 101972311 101972359
    0x703030c020319020f01140907060e0a09050f0a06120b040305070f022205010b18060a030b04050a051602010507050910020a0b15030f010c05030402040f09051203071107080c 76
    0x116801841e507565480544d002c160600e00c528500000c2c800d2018013004c148040c0e00030399419150350f11018040080a00038540d03510f040900038210a0303074541c4ca03466503043c0d82003210305914004080b0f080001807190380c402d000143c080703030034100c441c400c4c255182e001d00d00300a000030b41480000310b101d41c200158a03282420741c50740500248800d54116404c40c1d032a244900c100d0b10400e08100000c035401c4d22000035a4070b000400003482c0000030044040c003410358041d141306000c05441d030203a81172a40740da001d1280544d000388030014131071400700340888403214000d803210116410302043c4603002e03170300009403844444100c038054000b0f4900352059107010001440180701e52103c0302080081c4403000c20a501c0302c4d41c2a02558012140944820300703c4100306211404104180301203000b6003060780c003000c1e5070301c5410400035451002e52142ca1030030905000000106500004000c2c000d036002d400c4600b0038419030001d19241b8201040702351903000442c885409011082c210410035104880e903 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 101974811 1250 101973561 101973577
    0x50f07080c0a060507020706080f0f07021501080304090b030d080f090c120f0d020303010608150f0d0605220b060f0301020f070f030813121101110c010506130b060703030c0203 77
    0x701c42e003625462030088080c04085030942c0141c0540c010020f040e83c0255851842804e14000c1185142e03291840541e401a01a0512085206d00444108036580c07490005019240346801162100c1c50000d45c1800c1d9505510303d0343c000d400a04101441c540c20011540d04031f5110a41140a81d403041041490306002d441d000b68072600400340c00388000b01c04a00380342d402c0750410580301c0840d40382200740d0780c0388821711070b0b100004c1c9401c4c0040c420201c2503110701038500c0e0007401c8121000d00c40c000a140c03600c90325070980f0340990380c505000c044031910050310460b00544031207006050894540c040c1a41000b4140e40c06214407520594480d5002c1d8121401005464466526400c0e1428520004030170301c0c00032070100e0f0458002c5103550180741c2881860661040260320b400c40540c0c012505d401c082350415085649034907655442c0800c2201030200c941c0101c00004040c03602c40b041200000c2c00e80c1c0c86020755442c01c0308851490326200100c58655401d8100440d1962180604074514807070016 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 101976061 1250 101974811 101974813
    0x1b050f01021c050703140703090f080a051209191104061703040f1e09090f02030607031a04141605040513050711063c0115090605030601050f07080c 65
    0x60008a980610b81010600742044100700110b54034014142c1c1203a1990450240390307000540000c82d5144203802c0700f9061482040071030821060350361030700007540080392400d001c034501041c0c05182d0000d08010341c2e40034000394020500b500c5480b100404030070b04204050311a00c3c50301d1545000c1c2d02c860f00f121009048000000380808480c0c03d20325100c3c3c015018a980741404600000341d09407900030002081d16400034806e195614000c841c074024804018120b440b5801c92030200090f030780500c40c1c107110740c00a48010900c081284480002841c208007068031507890901c80507584220f0b10601c41c1d004418441a0240840d060016943c500842e030086500c81202c500c03841294000b90401e86c02200d2940300c54407010001c081c1d00d40c4603041200d81c3c126055012440d026100b800aa010343d04921010300c8005c1740380d417a40013141d15802600101312400c101152045401c6e4009440c50051400385007280c11810072000080141c42007524034007039040049400070a005100d0210b80307610381d100b0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 101977311 1250 101976061 101976067
    0x610021204080705120a020612090a060f0f06050a03080301030305030c0d0204080c041118061b03031302010f0f0e0d020105040806040f0c0b1309020309011401060507060f0b011b050f0102 82
    0x3502d61a40c400480c00f4050182644109515240710009105030b0465801800035081214005000602400c01402c000d41842030b00c2510021071454401e408802c007513030340086183d00c00940d003407003614039170740c4054086c0c48030050410100c0c541d60b05a030b0669130b0618180750780b030b141d040e042001801202e106c1e0b0702882c400600041c48580000307034440c8400040c1c81c140113010200440c1800e5000e85c6000d55900340d456941002c1610340300d00148000b10000420814a4402003c2c241c60b5800440c0d03c4901d1300e118000900940d80c008110404d60221031070000340985014500902580400c1c618034021110800000210381c02a01914040e0242c08101c50040c905414000400403881c801a942424911004540344001004442400c0042e480c3c841000303143c07017001402540003c06001c1030f5540c03242c403950050500202e1074000e140540c2c0c1e2035200c000303a041c0082107071081480d180d9a24036019039140d0a9030403940c208441180c80c030038000704c44101e040150a0031818414400e05501c00 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 101978417 1106 101977311 101977319
    0x10309030516050102030f090d0903030c020d06020c01050708060303130605090a030618030f020d08010e06130e07090b09040302030919050a03140105130b0610021204 73
    0xc0e1402501d8001d41c0409101190760a242c21203180c0d40003c00e010321140790b600d04035008550040501006001040003404054281c40000c09020000100400799500c98101402281c1c00c80f10035560369032a840928000d020483e4508003241990b8049202424008181c030380044410160140c040d0070902d0941d16a000342480d554000c1c035280000c00084e00034000c0d03020030401c1d00051102000540380c090141a074600c40c100440d4443c55510010581c020740c828111402c07062400f00750748030302000c07500c0c041daa4203160083d03c1c10008900c1030342c0000600d00e0215050380e54200712040801c0704100d105942500c0103070041c0d100b4007006820345071900c4481d08104400d02c0301f40f44a41d40300081411011641d1007981c603000d12840c003004004080c080e26a0240181000c1d1040b04226a100c2080380b02c043c10442c0280d40809610310ba0038000c02c146003443c0c0c11079004a80f00e95032 = true := by decide +kernel

theorem cover : BRFrame.Cov 101798561 101978417 := by
  have h0 := BRFrame.cov_init 101798561
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101798561 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 101798561 ≤ n) (h2 : n < 101978417) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
