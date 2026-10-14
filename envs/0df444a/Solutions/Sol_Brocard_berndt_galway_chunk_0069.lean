-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0069
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:40:20.525055+00:00
-- url     : https://prove2.me/submissions/b74b7800-0d85-4c8d-86c0-e90c7386daa1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 12230222 ≤ n < 12410078 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 12231472 1250 12230222 12230233
    0x305030c0f010603080409021c0e0c01020c010c11060c190506011d040512090d020307091a01091d040204020702060307020c09070f0503060603041704090b0114030105033c 75
    0x4100041c10301e0829203510032280d040072803c02c08100d140c2d041d00c1c142d038864680180d4070309590202c0d00d13650081507110507003107040c41c0b020860005d002c80ca0310384d00c00d000c1c0c003a43c48800c0f000d001105c40300500c40c4028895504000300e007820307091440c09040900d01c20400c4074415100084400b0813034991000440c0e46a102030014084000040044002c400101400b0001c5040654900d174542401016008802e100800c1d1106a640d0b010b00000c4400d801506580c0c1e11600d031040c51020300130b01c0c81c1820b99804060504a03007135101c2c0101d001101c3d085942c0001515904695044010020304140d074041c0d020720130b250141c0d84d6400151f0003040309030001c0c00010305110a02428000050100c4184040c081001d0106904401102c1d8041c0f01203501598030303544c514002d00d01000f13248400d0a4a0404130f000310b155803840d800070418000c00d1721803901614100d07031001550320090082039015000310252542c00c2d40803401d003050b8034200320140029004e500b0328410710180110f00402c0c460348030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 12232722 1250 12231472 12231487
    0x110f0408010b0103020408150402030c1002010510050108040f060c0c0206030c130503010c020d0806030709050c0d0b0a050a03060c110303070e0f030a031e050c0111030105040c020601030507050d080408010501030503 94
    0x24460300c20803842c01c1c00c085d0f003080e1800c011507441300039990041ca1060144130001c1c0440d5010b111400020700010442904115814070087c000c000854800c04000c40c00600895590302400c80181b040c0e510120f00f003041d4100350354000150100700442014001110345504c01603440c1c00103184124480884c03191107061003d412440c510850340200d0080e40341601e080581580401c11081d02603141c00e00765a5500d6034400700c0d00c1d060702940704850407458030040c0a015180030008210001c0302e440e0038490004094100b0040c2107991040f6079024007094401c00020708141c00c812600030103410300304403052103440c1c21410359004070f58190000398200042e000a21703103620002c1e001071099008040986080d41d0140029010217a29074403041c5084000e20070074030030000c603503500d0302d000300034003003040700c44030140c45a0428080c243c4600d00780240581c8003403001500c541240d400000a004891a000501045100c0428117032403210323003008041000361090056500942c800c1d4001d5558285 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 12233972 1250 12232722 12232739
    0x30309020123041a070b0405070503070807080304090c0201021b0601150504050904020103020306031006030c0303080702061005040b0301060504050c03011a030c04030201180503010c090612021201030807020301110f04 95
    0xc02c0c9090391002c00c00300100311140c4801090340c0580d44241034009050003140e2003c00d907801644401400c846007402048200140071031600704691042d400c42e0310301c5407600f40c466112289402049030544c42030004002c8030740b840d008501722003458000140360020b115600010408040040c030141e901c0003004116401c00321078010300c070a1262502906190800001550101e0050700c080d040640110100380175980034800d03081038041d50b900c00c109466032442c1c040a16141480290080703411040020001d500101c2c41d940304031050002e00301860b0505081100a0588001180e007665030b81c1004940c5885502c501c900518008124944961401480a004182ea024403840c02e150a000380710319403d902090364280c1c0d42c2400e00224400c00201c0c501c450a0040d80b040d40d066081c4181403003079581004010054a090341e880240c43e0720003640c90402c1e031240c00121f20000c00080010004188144003800792144020000304410103001c41c881b031940c206a44100c100c20001408002005 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 12235222 1250 12233972 12233987
    0x70309120c030810030c05040213050916020c04050402010806040509030d0617010509030f1e0d02040b03180601050f010528050315010309080409050a150b0a030e060c0f07050c0d0303090201 83
    0x82e130052414840c0c07400d5680e0905240054800c42d40960703008941c000d28281c0345505480a49400762a0044920b070a9564242450f5460103000c058000c528801101d030401e801014850303034045e1140549526404140401860700814201ea1408203200b01c881d203100a01440f0b008200e0640000041c04400f1a2142141d00c054100b03070880c0d000708000000c522001090f10110aa28000103503169030a0b800044988500c184c1080410b10002e00400c80700c2200c405540608200c4240c111000313052081030740c2e100c20a0103540c1c0c1c4008080d86035082d42d0320403001000d41d005500c20040152460a40c10083c3d4058007100001050012080042d190b10b05201d003003013400c017481c003804800b401d516412154172036070081d0307000300b601c5034001081900301307810151038402c580d95100c4000d80d44030141d1039103400211209000900b0900140a070300400907443c0e009000f19035030146000d07000c0018284503404040308507914000c01c1160f51060340c0303c1c212111058000d813004252228188001060030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 12236472 1250 12235222 12235231
    0x90c03030c0c01090f1d100f090f15050a09020702060702090108010b15190f020102090a0603020301140405061c14060403050a03060b2802101514030a03080c03070309120c0308 77
    0x89021800300400c604901410440140b4601c0b82880350701c1f2180003000400d00c0c2e400c902070611000d480010301e00d4a95204082c40555108208060748042011a02c00b01040c07003043d92100d054002130218901c2c0341d0061181500c01030801d1b2505900d0760100341c40c1d080c00d9204030100d941d2600720a020b0306100340114802140c2c00650392a2050312100e100e05031800700030400c104000c1d0381000c11024002d40c100c8002c0940207009543c4103a07110401006035109000d424160240c0c030307000c02560301f098041c0c50b02590004044002e0b51a500061203080c40c0085020340e044600449840f04408040c48035500483c060350b03442c1d55a40c607c40e405801e4595507800400c12000070050001003403d500c80110b040d10451150414004400741c04030b02c1d0212100e2009401c0d46042d800c2d030007000e0b1155280c42211505a4102050030f03c11041580759045810702070b000c140e610b0001000b00341e0190041d94009054103000626050030341315407503e00700c100c9040000c1580c0d072000c803043c1500b010545501 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 12237722 1250 12236472 12236489
    0x40609050108011b020a0b10050303030a0b100201060f05060904020405060a020703061406011e2f1507140304020d06090501050f0a1a060c12030915060102010501030b0609090c03030c0c0109 83
    0x1113101d030b424000d5590b100b10307001400c102c4400d40456008102c2c41e000c0d4005000041c00c40e80ca0341014030383c000081214102d610b100e40300007199501c1203070060085104840404083c0c2440c90300d82018041660b11540016500039420040824160780c4c1c0c1000d440260300c281c1c01030015600703515014084516036840c4440e8401800108a41681d01041c56082d141e1b40901c5243c10404441302a5183d00d0380148100356540c0d8a1000c049188000701d01d8010003a14408442080700b8138400c0c0d4a07500c0044c0c1e124400200d000103607903141c99102001327640141c4094180c1080d80080e80700c040440d05101c904540d241d4407401440084294202d0b80c030f80140f44084100301c4500d0141e50500641c0d01202c515014810115100f00300e00c0040c040700780c840c0885048960380f403034616a565110b61a1080e0f00e48048080b5000c600d155205115950580c2d038403040008040e114801000a0a00001e0041c81584203403001c41d1400d4034240064041c2d40c5018006011540c035010001d4407100c0c458200905 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 12238972 1250 12237722 12237761
    0x70e041503020d0f0501020408160e04030806220504120810080d030f0213060203071214070206090d0606060503090c0904080304120c080f070c05010c0309030b070201090204060905010801 82
    0x648820220003402100d504454814100d03080f4580100d44440c0004058055407000c0b03000074829402140d108100d088031500500000d4072041600844042500c000e4005004a030029605003403120403191100c15520071405d20440f1260754500f81e84040750102c8000d880820b030403203101d4021600603045068aa0100d02c40d5080c0422940d81c0c50300002e86d0401c054480d41e0007030500c4800d5040b06c4588082d50b82d80b074072654640038065030ba80e210707003411141c140c03581032004405071007080940b0151901c402507914204d01502082919003000b18581c1d07001403120414000a03a00f8401c09000344019110640c903860550340c0d482c14401c400160900442218003040000740301501126030181c0d1114945014502a0300c00311003045445c0002020340c0713800101d0f46010054400500040740c81000e001200d1902d903001141c1c4244455402404503805407020310025181c1c03480f10398002c030248000075416030503070001011345e0019400382c10242d40e00e10042c445c0c40d0080c019080351184842c000003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 12240222 1250 12238972 12238991
    0xf0606030516020a030f050d050f0405060c0c070506090103060e070e03010b0f091306060e0a05060405011d0403030908091c0605060105071502090301061206050f160c031b0804030b070e04 82
    0x4d49a40e0419001410840b4000741c1d0003846015078180c03091407050090410042c42c05112460105a040c2c80683d041d1241c0e000095003040901308403a90420000c02070311030303e41350409211058100150305414140c90740740115103001c610743c119208505036074800f0100b006090a150841d080c088546004000c552035a105070748800300d01e1604080b82502c4040100e5107400c100008060075048800920445018040f02450b603811035406607070121401c01c040c0e42c1c1d6400c00c040035139200191061403286000003d000c203010354444405503002e4180c1a01c0c200742040001d440040c0b081401c411404000054810f00c2102c4c03050950050083c07d000d07140050755180d00120722216840c1c0c00303515800107441c030441d0f1001c0d004032006000780104014100c0b41807400d01e020749000c40b55514080450000078645242010310325585c007102e9140c00c000b5403241c0d01e00700c8031941012650682d182030644101c00140260b80104000c43c0580f4001019040500009021811040209200300c0c141080c42 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 12241472 1250 12240222 12240227
    0x1050301080309011d04020c070603060f05180403020f06010602030a1101050709120f050a03050c010b0109060503130c030506010f080d05040812030601020c181501050c070302040b12010f0606030516 87
    0x1583ea90300e007401c10621124403030713442c02882501c40e9441d581080c008610300481540000307240c01a6020f644003441040c0e190303071000c4150303a618820301e40d01c00c1c0400b9060100ca00e22903282500140070b481136810b40741d1050703001480d1000a90040005074400124084c8882d0300030104811031041d60024000ca0800307060042401003680981340c00380d00703503880c0c84042120380c01c044540b040d03101081e501184003908024115400141c1404400d50a20704c186860b58031031800003003554900d4a80c1130450b160102000c89007030a2010854003411100404404111b007041118000c0411204881c1114181281c441c02d15044503071080501c40c0900c02400f40d0040410b00a40506001c0881600d0b680c07a580102c0c60010503000c4d06822030940311a00c56406284480da501c07500d2680080141c05984800441c0c83e0b11864420003120f070001d00c010700061400b50441000500001d201d804600325a1443c1400c40b0218010440c40d81d03503070175041103010b41601540b9130114001030480b03500b16090001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 12242722 1250 12241472 12241477
    0x150e0316050f010c05010e01021308010209090a0203090a050703200102070f090c051209010606081308070f02060f0307030501090b0607121202190e0f0d020a03060513080703031a010503010803 84
    0x409110764502c094a00709644a0180003005a030884000d10210070f0310b0071824001e40c41414082e480320a804004103100405000321001d0f000090808015030f95450300c0c0d00004d40010b00b43c07488078010f0b400a00d0104104218410165001d00904400d4000701d40e1428041a4600c0380315066400c65a010402d0782045010740007115070002001c030342140c000d10105da1612030320b0059543e80540380305020003c0f00551060042c5ca015480d040700a0f12042280b040d00d84060728000c04480d01003180e54005070312036500703101883c0f0240c4402d080820221900c00c0346e0b00121200d0002980d0381e401045182068020401880b009444292410320710391925291821b118503071030f087c000c1d03081060320181e18950460710301e10511800d584602010707410052101c030291041d00d104506511a2000c02c0c94500c040010981d40206034181080c950381d581000f60000030a13541c1001444245e0b10b0100e4600d4000304510761081e5400140d0f802ca4100d03084c0707400c12071600c02d030410070f0900041c408107000004 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 12243972 1250 12242722 12242729
    0xf09021b0c09010306111308150109020906070f1104141905060603040303052a07060e01060602031603020c13050601030c020d0503060d050c041505100c03020703060506040b0901150e0316 82
    0x1070108454001300c0301c00c0283e101e8400347c00c1038046000740c002081440440c02000315007240070103d0490742d907221520140d00a016a4036031040d0f040002070005080c1340c84290b40c061080c0503480a680c00c101c00502100c03180c2864002c101803280c1088840010380e02e900b68140c41c1400108000d04010001ca055400300070720040030b2540d070b0301c0401c0320101c1c1e49040c40e1848245481c040955481c540e0888401d030000781c000c94000b420b0115107480302c18180210001d07030f8500c0c0c0c021400c00d1032580d03003200d803800b0509007a8294011080d01065540701c0c201055820010624046a981044d0000404845280500d4021500080c18000e4880d510400300c0381c100b601100d200102080e02d0404508207003040d80b400394010b1601c0d50780c5000c8514541d462084070011030b16080c107000d040c0c0043d191006104070040040c3c004c0101400020704d10340c02030ba00210050070028164482002066540a0a80044030071060a41029085550110003110543c5041e00030b001c059a000c40f9841c8914420300 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 12245222 1250 12243972 12243983
    0x50108011b020f030414030c0405090c0a05040b03060402040c2c0a060302130311040e0312040b0702030c070312030605030a05060603010b0d05100f0207050303010303180504090b070311040f09021b0c090103 90
    0x5d0a1b40196404201500c14180020400c00c05801c104148681da107800007001e500072024903000007420314092040068160380900a400d41e81d40b280d08010091034502c58420901401d4003d803003104031204d5070000224925084651103800c03840801c4101e1140e0741c00041050700400844035090401c84950040340d0f4452080314000064000040c00703031040d61031694482c4008070740f8160a030141821103015600442c0170030103540740c0204c126103903c18050008031980c004042000017460704019031462a2440c900025030304e4803040001e08001c0080000d9036503500100501c1a1403800b0b116842d21400e049911900c138400c03941e9086d403141101c48080039520340d1085005d004d00e45580444001e85e0340503007500d07920340c0c4074507000d005000043c1c242541c4a41610012801d801c00e88509004650422403003101c0c0ea80d1000c08a01400180c6602c2003041003d20000681d24454010b21001c1c107426000540c50f5400412801c0f4090200b016602c21680031080d242c40e01c0d22120b40c02415243c002c3c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 12246472 1250 12245222 12245249
    0xb0a020a0f03020708190209060604050907260a02030910061503020708040f030506090105010519030b101a0409050606160b0a02070b0103060605030f010b01080c09030709050108011b020f0304 84
    0xd04069013480e1403584400040c0c003484500c0e201c02840340b998005624821500721803039845001c140009400b89024aa8000d4410400301d06001c3c080c07004100e0800701c00344485c0642c989103405680c9103209031a9480281d030080280200580c09103c0c02c100c1c030003000700801c6011700d080004110640c484000e081895030000e140018018604221800790607a180095100c541c0e1789441540c4a40c01c13564a9620b5107000000b0a140c64001d400214299605442e144107501b1910345e070f111460f01411030750744102200d00000d115500c8115100791039100710911a01c07180b0b8074020405a4a0050099101d0082048040707181d810b2440a00308564100071040f401c0c0c1c0d12a48810002c2c0701d506009040360716140000000c10030690000015600142c042e10801c1803640d140e50700307840720420014085002d4100054020040300050040000020111540310b982c1d200240100c034002c0e080a1040e035111000020815420707414540b88146500c000c2039089601c0c0030140c0c80f400395005845000050 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 12247722 1250 12246472 12246503
    0xc02060c130e01030c0609080c010e1005120906090714061e0408010905030d060902070b06060a0203120916050102030c120304060b0303180a051813030c0b0408130b0a020a 75
    0x10301d401c1030003609110a090b03000303507140c1c100307120800042d00c6500b0008541e841c001c41c9052010800c5e0343c0c1c800040c1c540c0118050084104112890740b41010410840d083c44460304401e100c4a510740140d112a001e0481030420604107420f112003500062002c250300200c001c0300c0d407981c2c0100c0789245c01741c5240c0d0041a031991030030a281d100c0d03580f11049640c2030900380c0040c00404002407603680b404041c20000e00b5034032181a400da00410380701400c0b000c003c00005000342040b100406181b510380c41038130b182c08009000090002d000384c900036100d0703201e40c204a890003107050848024040c240000c0d414550801c1c4103d55468080c03044024142d408400b20781000300507001541d5240c001800d481d1901d040b1500b1400c901c40039612207109848d82d040004190074100c51b00e00401d44080c6000d992940c4003c0182d203a00260300007182081202c411070401b2809076a0034902030381c030070a4500c1e80c1304407480484060304400e4100c1010b0f074208002d0301804580020b4200c080769808040300034103021 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 12248972 1250 12247722 12247747
    0x4050c0105120604180b070201020a0801060e0105090d02060d06170c0402070c14010513030602030702061008070527070f110106050108150d0b01180e0102030f19060503011d010c02010c02060c 84
    0xd0098008104000500c2404001f64048d0007610fa5040550303140c00007683d039181e042352681c4985104a004c20310411585620f0b003061100c900100d400a480d0a14054416801d5011a00300e68051200e18031000c89080701c825042c030600d8a1110102d07000d50901109846003440480d882c0314132140c468020001c00312590003481500c0c0c403600c281a4009800b40c1c5c90070468080e5000721030b140e005010f9040007130325095214108600361254000104140d9081009122a500300305800701c0001c90f4840022140e2200300036034a2203042d0381e56a90100b0825400050545c40042c00858a181d0604609004036644212640d900820350341d1058061035040d4082120300801c104050280307100d150010070a4007a40c0b620729400e00c0c801004004045e06030042508034081a1080400089400c02240d200c13112512040f140854141e00040c0b0295103030b00080c215541c00840740301e08030050110300a012028030402d48040c00500007441550400c6000075226580200340c070000e1400800c07040704401 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 12250222 1250 12248972 12249011
    0x306061603120c03050103211215050a030501020702010f051e070201030f05010305010605030705030303010b090103021321030e0301021309020a0c020306040f1b12020d021503040b04050c0105120604 87
    0x510440b0200305030641004000c0183c5000d010580e03031030040c3c82e03400a884c482c02c180040d10410075550308003001e51842c4108040c040168040b01b42c8010001c003c10aa580c028003d00114824800107a640783c040c1700140044120540c0a07040c403109002c002010b44440400c2d81180c1820924561307948101d02c0181c0c01044120840700740d25142c14004030030810150300444c140c4000301d0445414503902c1040556900c82401030307115100040c0320710300495009801501590140d14000111680c980c1e1814503035070361202032120880303101904c400a16810420190801d4019402503203051803401016030390402c148590b8206e190b0015040e03103c103105001d001019980181038416904040c01c4c8140041500b01c410384a0f50312111009000d0112501341d4000c0320704410180d105094240c00700108408110b00c241d8001c5c1845456800c14210440214460b9201d0440e1100d0b604060178118500811146c0e5141480030420020040041262040f0740c0108221404075511401800000113003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 12251472 1250 12250222 12250247
    0x18090602070c090b0d02011d0f1f03050703020702010813020604080102040e0f06010c0c030b090a0b1f0e060d02090a0e0303041a09010b090408030421020703020f060306061603 77
    0x11440415a1001c00503464068400c8600d0f0a01c1402440003680803c03603007860026009002c943d01007840006a40c2a8004124002c0b005013044417600180f400308074544ca0b05121700504448100ca07246e15a60948540303600501c00346404c5060a21030760002e045100003400f08001c040403030072110115076030081200d01618914000b551030380d554482e48032050744250761510301500760000013070b69544100d410b82d11541d0008440000c05181d070b02d4554204101501c048100e0285201706408110800455405a07100f2520b20005120395080c01d13000038001d4116018440311442030000554403900282c00040d0104c84119094440004160081c26400d12411480c0004400c02003032005002c0394000302007407940324209a5860020f241d003200c0ca1500810782c44500300e8041030118142c84040c59019105007103000904103030304414058244030701c0e09500144d110803030610860800703c010b04c005080030f550044c25403c0080008035103029007803101003c401581c0c404400e044c81102c014010 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 12252722 1250 12251472 12251483
    0x807030b030a061104080106050402090604180e0703030e130c020601140d02090f0103021f090e130506040506010801061703030103110a0b280203120a020306150309030304050706050307091809 84
    0x280c0f100361030000130b9041880781030310341d528080c00015107040a00031621060802000e1a20345810456400b80302c0c0003d01100c07285994031026012000000c0010074040d40c041c0e00ca15500d030006608021380c400343c0c1c00802c80031a060215583d041d640014240c0e054540080314071803044903240104204400910019511606010900c000d1421620009041e00e0094908103c90800745091201954228075000c0004034950310030400070007020784850300142102508085e6034001e450382898039900f0b0f01c0580c0e054100300010840d0080900c9120001c10287c00c10702c0c1609001c60b0740c90b4890005102c082d06140e85d0611032072496554040c00b0003c0d244088845407200c41461781c2042050400c030340c1e491040010152a50024000010f40b007240200110140c3c41d84d9130342e440c80c1c01a4001038155500215403c001d6420722503110060761040e00050020f688a280c00d0810078a0603503035601000510000304148041168800300400685114401043c0c103942c407242400c0040001c680302802c0d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 12253972 1250 12252722 12252731
    0x9010b010f080925060f020a030203040b0a0306080318030115050d02092706010303020d05030115140d0603030206150a05010f03090305040b070305090102070506161e02040905060f0c0a0807030b030a06 88
    0x40c4e00100000e0003a41d07007a5032002040440d041d0241d98680c0183c03000740c00361f0700600041051070980d1005000342c0d004c91501081155580142034035503082140031164460032400c2d425040c3c1400d06c00d03011010319000c1c3d185070301c5140001081d0341c0c2091020190040c0705d10400155004991508410070114200118034036540140d21551140c1003030104038018001d00c900298240c4c494826241610000c610b02144100101d038140c407134030b0310003c1204a8070401e1100012880c2c0b80d00ca25801540690043c087c146010111510b01000c5403140500c10480d02c0c0c42070001d664850344c0b490844441d4107000420f50f0013418150703060702982d4040035040c607002a41d0001c160f0b225000e440080380c00e0302203505264480d07041102500403181d280c2007840d005000500403448920f141d50103000d103d800381310904842d8000c2000d440f05d01e1000e54096000405101c50b000c4411049a07001c41d90900c10f0342005017103103000b132500c003000e01000704164886886500d07982d4140003107030081d40d00000401 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 12255222 1250 12253972 12254023
    0x150910180503010501030b190603061a0108010b0a0206070c05010207170403060c0201050613091110031506080601080a0504030e180907050306010b0703080c070602040801021209010b010f0809 84
    0x424060381010403a5140803880d000003114201406000e05132a0b102c00c1707200c919078520030040c000e074106591071180d640d211100040481d0781031142219200d40c0c62000b03940580c40000141c0b90034010781c41500200c41c2041b440800d01c3d4081100368201c80300d40b805500e5415103042c1f45000e80500407000e05810b103416031035088400c0d007100500c1200e105d2502404441e242d0740c0103030f0803514119074094019002c03510720742400c441680b0001029110741600380405a501e07010600d05143d9881c0180413a96403072102108010b09140c00c40108024038020005203440300009245850252203110f0380c58444010804150003610f01c40b9003d1805800e60300000c1580785001068041038400c88400e0140c002c0108650a000c508241170340c9845a0040c1b900450f590b0403030305e40100404400c0261030503c592000104140001c1004010034000580c6580255990f008010009089095181e15140c9881c94a0740c011000e40b00c41d620398101655940da48941c401d007005a00100109440b172410713440b2 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 12256472 1250 12255222 12255227
    0x7021f0503011502010902010903020108060607060f200a050d020f0708030f0609010909020d1502040506030c09040506010305130f1e03050310061b0803060a09020d020702030c0105040b09150910 85
    0x1141214a40721003c24403d00c1e0701c1059088940001020f4001a4400410700142d400703070714001d40010004e03003130318541103a03a180c850860b4104c008404000391136032a00211300c1001000102e10480200d4060314110107044054a5071044c200c4100086401051804214041400b541c1c1181e820454207035591503d600c020b10300140403101c1c180700c1c603c600008103808610340f2a0300f038030a038080c010000308070140d160407030801e9090006050842d0200000f1070719440340c00203140542c4403454800d072226041c004000c1510402070800f070405d890700003001454820401c0030265180c01140740c00c5605024207140143d00381b038161096204074812180400c05600000551188100c043c06117140c544404080f0380520340d08070003074a070015040720900440c0f002401180c0010004164081c556a280104d906981088000700038840e130101e200001d500b810f1041c0d081c0c1d69000d103401c03858942080d05145240c081c1464440c064841741003513841c03403a4103900700c1d21000001400c00e0001600750800 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 12257722 1250 12256472 12256477
    0x30302030d111903050a020705070806070807020d0903020103020901030b040606050c0105090a050a1416060c1a010f0b090301110c0a1a0c0405010e06071208010f081b040207021f05 79
    0x1544000b407914001d80c403000c04050a94281e2010710003180c8003600418000c8001c0c10000d45400911542044140c00040e82002003500a04030300f070280400d03191051001c0c2858100034400825904240200380d49035034050018000d0720382c2420016110b444c2100100c00070314000d44407640262400c5804258941c002019240080c5440001d000f59950605940d0700c0704170b0450001d0659100324406d4000030240410070080d41151804c80d43d2441070724400c0d03210321840d9807164002c00c0541034640103004141e0500240d603d40c0c0c103956420384d40743c0710700d07091945c260b03103d2003004030000704012105903002e4120200783c0101c14680754440e00482d0156489001c0c1c80012541d21100c8883e00d0000302c600072450303210340c0e01000c00c40c1c141450900152280361210032001d502020400c8500c0000d5100140c181900c401e83c0d41e4081203604118102002c010780b070b00080c4440d0b12000c68900040c14501c584410f51000f85da0140c0c44800b6403000c03c008410065507001000c040c401d03089480781c0d101c0301 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 12258972 1250 12257722 12257737
    0xa020d080309010e060108060910110403060504020d05010501090c0306050103050906061512090c04140705070609060207020d050d0e06070f060b06040f0803030a0506010804110103110f070501090b010902040b0406080613050103030203 102
    0x5644c502c10303220f20040c0c103c58bd0500424480c0c40144010004124241d02c5035602a002030307c0d2054000213541c1d0b00d800c50710240c2203038815551b21521020903603414411940640000e00f001c0245d418902c4445541d640000c0c010b9204140440d40160180c00180548001c000c00c02410781070f5040c40807100e500c500740568414040c5141048000900400c00d03856030060780e1546a0fa46840c5054490344080c0051030070a480b0340c0c0e001c2150200584690011414003802100544660300c900310000344201c44070b503140b074858079003030191002040000003801c0c0c907a5444407000890401e01c0c004108039001d00d0307102d418654102d40001410103000310055114002c3c91400b0855540e17500700540300d5140654004c0c00200322400c0d404070320b50180d03105030140b14000395a0340c2020f6510406098683c0114812540d0782d4541d00c0c0c1c0340c00c00c107602c0101c6000d130042407000d5041c0b0f4108040f200300c901451050004021810300032400c5511281070044002044150601107980c507400c000c3d549902600 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 12260222 1250 12258972 12258991
    0x50705030111040503120a0f0c0f0b040303091a0106050a1d0d0c0305190809091b04080102070201020609060c12070c05060109020301050907030e0d05070804050409050105180a020d080309010e06010806 88
    0x1081e011b840d4590046600410b01c40e1a0105e000b0712201c0704071095a1854000c85c1c9980201c0551004981e0000f901886240b00759800700789000c0781e103000096924072205902640740c444c401800259040025100407a030280740c101c5840c0b12100b0410050041c01c000150099044103001c414406005603200584c0d006034200c80c82c103403017201b4401c5840442603001e00214014400c0080c640343c9154030a40015080d010342c61b254940d00007850143d441903022201d0b07a0b41c0010400119601841110751100d11900030f03080130310300b1155510a41c0f0074804040303540983c140004510f503005824200001d50000d0803580030b580c4030715031903009510a00849200c0c02c542d50000782074134030a000d0615003881810161064005941040c0c84c80c1d0890b400864602000388004100c0c0d444610481d03100501034000412642000e40d003208a040101c0100740e0361fa0044205070001d42c8490943d00c4015074028040c035541d546000b8a1030042c004144c00300580d004840001a2490b00010b016000c1c20002 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 12261472 1250 12260222 12260233
    0x3090b090703110d0501140a0e0106050102150c030702030c030d0b0109080f0a060507020f01020f09010f05030103051207060e062406070b1501050c07030507060e040522050705030111040503 83
    0x510599074410701840018402d8030301402c814464144804220805841a40085400300c0c1c40084000115001c17220000380380c0d1794454082050788240951402802c003800030340500395001d0720070b0b00c00c0b01004041c03814039000040441c070301d00e1081048844581d11a000c2d02e4668090b808040050009116400e001910600f8045419280400c0b40420b41c80c5100040488280d50fa482c1e4002d0400104020150b00a101900480c61020300040070076152000c103507980c1c0e01d035040001d018448681249000c02c8002d000610024400140c06280c010304424407a80b92202880e040c4003400c21890100c8450054a090041504a0f002504071000300701440c86624480c0005209044c094644040c01550b080800f080c42d042c4100200418160306140141c5000c10510110b03140910320ba0044440c1e520802041040f07582c404003040f05100b08031001d03c180e0910180c0b40b0080b1004100e0b40f8106601c103800103040040c20020440103000140090020030011301c00b82102c0e0300640700c0c0e50301a0182 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 12262722 1250 12261472 12261481
    0x3120507050301080d120e030403050a0c0b0702010504030f080f040905090f06060a1e0803041701050106090308070204051e09010b090624070627060c090510030f0603020402070303090b 81
    0x148090b40d0507281410001c0544801040c001c0307071005500d03080d0015043e545d811042180c4801e10040000c0c5008030000c100015080c07815a002003801d43c081001230206200d1280180e134090211000c0380d82280380c01c4d13207041003814052050711a1108010b0341160002d80007400014079040b0a104881c528180c41e5146407800c40c49441744801c80702d065014145110500410a8030403841d0192130034800d0303401d0019100c070401c41c03455005401c0040142c001012400c0c001001340a514094011880d0090040340303180e44d00d40c075901076014000c0c07145840d000003404140e51040d05503407030300080b2980f034820305258000034000c0901641c070500402e0070b04005480ca0518144010b078a04854603188207104d001118101d2035080f03038008580098039409600421207000000402210185c0030100800d080c40ca0300c02e00f00c03142d45544030240300440c40c0030071059032203508040329682c85090104000240e040c004004010640009502510109002081c950300d035004a4000d44151401500d5456 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 12263972 1250 12262722 12262727
    0x903060f060302060d0905010b04090f0b01120803070806060d140601020d03110403020607050307080301030b06090105030f0d030c03270b01050a030b060d0309052e090f031b0302090403120507 84
    0x241d400041d420a50800405069188690051a01a0007440001555106100040d00752a009034050300c0071719901c4080c0c002d008542d00341c40e006040c078190184032524640c0c0c541c001400014026400c1c001d000e4009407007500c451044904441000204208007402c2c0020501e5008059030b4080c0144507007400c94100350700a10a49003902caa20000c1c50900349035900300300b8142e205080480303880c0014070107080011645009940610b01c1450942414641141882040c41d416441a4803070742c030110421989800102e24844000300b64640070600e05ca070300303500b0343c050904162070112014003070190070180c601c030703504001c80790744101c1c400201c03640d03603c08115003240f041c00081e2001d41500c01040051400c00d031607030030140c4039040001d01195610005030381500104045021220300e129060707910752141c580703001071096500305000c0c541d04186004c0174040c01c500005204024203404945295031112025008544c0200822150b203468034000b8100c100c1c050103660314030f0408011845850 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 12265222 1250 12263972 12263981
    0x6150b121f1d04030201020906030a06050102010b0405130308070908100204050301060b090a0e06010c0b190b09070c080304050f010213080c0303071101030209150417060603070302010f0c1704060903060f 89
    0x540092800b0940605520100a101c0c0041d00440c107540d4200040d000399140c0201441c490681d04800094a602c0c2030000390a4a0786481114860f0740340c4410002d02c100080c1c0343e13801e003a0709450310400b260b0b81d81c0e2043d0303150040c0d40c00c82c0c05144100102d8601021054000b0400da4000b0ba00074000d141e43c0b6002c800050107070b5044113038800782012051010383c052417221980060145020344d100802a1035141800100f5242c4549920140d401e042d0f140c0920300a4104a65090b40c80b10701c58a07203140003c4c40000e541600606002000000c0741c00e1000402c5410344030811324000b19944c588541c60b440b040c034040d104500880c010940e00c4e089510300072013651199a0440f4000d002da5043c2c00c01180258007620145600050300042482000c2d00303800030b0001f4002124000700c01143d01d03039109150903c001e188031301c240e000c05010300043c0d0703005aa5010400d281c1c14007402e01c054078a024030b80f401c40340e1598588881702140c00a00c20f544400c41d4821280904410001c0200d524158003e85 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 12266472 1250 12265222 12265229
    0x5060a050301030b0a020708040303050a080f01050a060c020f04181a09030906070204090b040b0a0f05041211071203050301150e030a02060c19061a010801030b0406150b121f 76
    0x550309000420219042200c00b42c1e101c040503000614006c0c00c3c3c5d46104081d00302d900240c0000b0400304080403421b41040c5000c0e0480c40642c1c2000656140c80001102094503000301c3c0104900f40c0301c0003046486041d107001c0ca20300000c00600090300c1c030019a40594441140035a58000480848001c0e10895140305d801150500003940c6051007800600a040d03000d00c0c4100d80159a03201c0400105e00d1040c440390241d4803900110b0890300f0b0105244040da4030603440e05030020718000a010008451036030350300c42086513050901c0016401e145860610b600ca40c40107000d462603507110000c05502100071816a1112121042403c400e90713021240c0b01010050340350568429444a03015140220107410340c09507039001c60b075079106005505802641910812105136803100000101c200e20004050b880b41170a2814004035803442d11003007008080a400030301842c0d59000c84844580005003207401815182441503a90703040010041c000000c00c6607240d101d54a07031a002d040c840e200d4000d00c002c8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 12267722 1250 12266472 12266477
    0x6061203080106030507121b0311090904110109051302070501050705190c080c070806180102031b030408070c060216050102070501020703060e03120106090609050a060c0b04021305130c05060a 84
    0x75a003490010f4004140203008030003071184170403001101c1d52203405403079540d01054410500840240001900f80e8002d516036540302c1006010600c0c4948440e111294040d80100c03421003a2200300c0d006807a040d100341c03c4a5004a00c0503030220f14500c00d50002c2c0000361040008010740d903104078080b40c580c0940e402e2131131030342c0c40e8201011200b0311820f100c501c07041c0103081091404030380c41e8509180c10142c1d40300016640101c02000220061403604090130f8079080000d6103145000892401c0700c000c0c0c628181c00030523012010405220906055544069029140003140d54890102a5650405544150456404050105070307035201103400001c960f8180c000344000303800c568521001e0b104c040756030385c4076203c2400487d60400e211013009000b0030704c03501c502d0b40d85c03403d003200100f40800d1500440d000d200e01c140300300300265100e02c2c1c540c9020340100300300c60301da1911701c00964440104502a040641042c051024007815407007076544d40d5201e81140c1002039030710810b0019501a050301c0401 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 12268972 1250 12267722 12267737
    0x1208060a06030209030f030a0c0b010e090606011206030506070903150603020307091a0a0b0405091006080a0b040e060406050109060602010506030a0f0c0806010603091403070f1101020c0a030f06061203 88
    0x1d40c2d009802500d0410002025900044142c1c042d0b035245400800c92100020300c050944000e03c00000e0182e40900704030303903840030b461503c200569682c0101030300403070402c4170034011003803000889d90016000e55031010a90b603041c1400310b0014210405400180c808907910114810090014820202101d50150140c5510b40c94230110070010311882117905c1840c12140f1452103603942d01040c003009004108600b50702c3e9802c3c4014007051807001405025119841001440265042122981e00003078550001c170310b80d582e5030f0210b405402e1609894501d84543e00c1400100a2150012030507903440c10300c200811a0384d010100c0c01c1c2c50069a81507015080894208081000c4070811100c890160701e80101803552503850500e0000240d0106d00042d07514031115040000183d20050074111001c002e506106030340d00c03440310710a00c0c064010080313401c100c0322280c183d00078400c1a440c031034010483c070f00c00c0d41e807800d1284900300c100c0011a11245800710100e200c95100ba1080c001039010341d9041c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 12270222 1250 12268972 12268979
    0xa14040204020a0c02060c0a060c0f1d04060e090705040e070605040e1003080406030902090a0e1c03060506040303020106090e0106030308010e09010f1d06010f1a0d02160b041208060a 80
    0xf94001c10482c0108081058004050b8030382900070007a22400c50000e10703040d030740e90412000b11380140050358204950b2100f000d00060f803080711020750800c80103200c9254a0303600e00090041800d0751101d002010440c0030410840c00c0820107204503201964107005200c100c1c031135151901104d000380004a2824002030220200403903807598007000c0500c85181d01500c0b5202c6101c2d5800a6000343c001986844180c030841c14140c1d100c83d0810346c48103003407003003040340440e403900c40e110800000c40302d9981e49441000c0b14400d401400c0109800303458969100e89900303000307010700002c2c0546a40c4504000c14004041e00500c2031504603034044d40c92110903400c1c4080300406003001741c0036104541d283d00690201921034450300d0318111900410a5400c3da03e8000541003c0c0705a0203012640300402c0100040c9520213030b00c10b40440103800703599a5461505905000b0b00528403c04030002d00c18a9000803c45c0403d1154040d5000b82c4119207144002181100c0c51b110840c0c0480c0c000c941ba000c2007 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 12271472 1250 12270222 12270229
    0x5040b030402040204050402071b080a0b010509070e0901140108090c0a03021504081006140301143603040303020f0105010602030a0305040602070b040501051b070f170c03130501080a140402 83
    0x950300944010f001602c1d182c4c0c0e9200190a0383c00051003074034850358208400e140c084051141e2801042081c01410300740c03203d40c403183c0070030005102d101d010301c1801e000100703090b101e10400c0c0b4012100600010031541c40300003804101d40e22811a80c003260240003c2558000c00095129901d10001d052102a030708540c240601001e44940b4091107a6051101041c007080c140f180c80c0510301c0c04040001c1035854220444004904404520f00a0f49040700c00000b00e80303d807071046c3d441500800000d09007003003144100400c040c82e81c5c0218103446801943e110803031340132005108907400b9900312540c6900300282a4200c910070f00c140d00140e4802c0210005050003908056405400b58400600b0030308642c5441c5030070403044808440e182d40d0340301085508402c204c80444040980d1802d107080505030b90f80d50b05e01c103542c0e04000c1d00342400300860241881c0118111601d081184003940c1d2150800550585c2c1c000260050f180803a00e9070700040c0d0303106100d12810440e070500030300e00480ba455540a0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 12272722 1250 12271472 12271477
    0x9020f0609010504030605130c05090f01211502030f07020d0807030908090301020a0320040f12020303040b07050703020f092403010204050612040c0501080c040e1302040504030c020102060a020a05040b 88
    0x1c50b051110610001022600d00d01c80c4620886880e407020040d166289800700d00f0078000e8000b907216040071024043d01e00302c07220055043d1280070240040a4040c0c000001d0f001d250fa0600800040041c0c2d0080803814240d0090740c0550101400301c0400c3c1c4071510207986501744940c1d072030700054110000800151107034004115040c06221101d140901410200c0e003641d11010403940469120812a0030343c0801c01e005c544d00c40c00780b200e180c0c2081d052503201c0312000c0303107881503406401c4007510000641d5014421100182103e80c3c2c02550380c1d605107400390f21003c080c07109a100352190b860303030034050400c1e9001600c1150319101c0d030300081500724821142c03020002c404c103400d0365013800702080c5500da02c0020240120070591101d0280f801d0300e0100508245508001d041048080c207000c0c4642c0403005030303800c0d2103200c0200c0d0015a120b03044801440022176001e548a801c0ca01840b0501d600b2102000c4181e0003a401d0314100d41c0c5180b044000e0b4415002c06e41c001600410040101e000480007 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 12273972 1250 12272722 12272737
    0x408090103060f0605070309210807062403050114010308090910080d090e090f0304050d0302010906050109020a020c030c0603060d11040501030309050a080d02030306041d06070504090f09020f06 85
    0x60025006843c0e900c030110040003600020b001c00d00001c0e00d0070500d41c006840c039000304079107400450300380301d01c10f02480d082d200c14034001d00010380880c80004002c201d070041c1d5407800b41050f040c10411000d911005000b00144019151946400b80b0034448402c82c5110728107032508180464903000c0300c10184007501400070903242c0703800c82490300412a42400c4c0030090f0030700c4181c0d840d40c520710b0130605035005680000c0c02400302540824018207200c43c001c000e95049900c11106049800a41c0c2400d9000d040104001000705103044004991102a940900f044100c0c0ba4200c80d01b0702849405d240c1e0314010f1700e10b2554004020700c00200355262004101241034070524102c1c802003443d501240664000f80c0040340440c4a425040c001030800110ac2802803540000501c2091040c082c06502d07840007400c46401952170304030b10050004201c040c2081c12050320215002480d0040006213035804c10b0013030b001c1d07045c02d00f140c124200c41e480c029009031a80042a010b90b404000c400c0100f260300030b14 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 12275222 1250 12273972 12273977
    0x1020c120c03010603031101060915090c050f03010602010c090b07170c03070f050a03020606090c07031d030a03030501060806010903080d0c0c0203060a0501080d03050906060f040b10120b0d020904080901 89
    0x4070454031610700380a034074011071103500d0b8034103400f80325400d150079034034a5041520300b0b40c60a0f44003401a201c00d40050b044940084000030b0000c04c01604951b180b00701001e41c40741d0200000002070a60341580120040b03410381d51103400035521049000103e114030240030705901038441c462500b0b400940d0080c004801c000003104c6c58948213903107103034240d50542020345040e081500c0342c4092503014017500d0b900041c2118852401d10f041c09145025010707864028040182103403004228010a820000c1156401421035081c10300520f0002d0141409001d040e000034007a101241455004040401c00da82c0d01403103c40c00c25090f2203019000b40b00050074042000401c80070840540c42c140102d5009118900002c902076041103071030f40c500019192007404140c504410000007190109606400140403510058203031050000a00501a4100711980c4015903081141c5656003000e000020a00795180c00e015450b600810820030090b003d10117500301507240c00040003d5510b000501000380c050 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 12276472 1250 12275222 12275233
    0x20102040503120904060608010e070c0201020a0b01030b0711010c02030d0902030705150315150301090b010e061803010608010b060f0d02040807090209011d1e0a0308030f07120b01020c12 82
    0x4000107454514010010000a01c3c002018a40d0f41480d001c0d180281c0307080d06101d95107503d0f002c542649810300406107010010a50210421688240940003c50b500810440c8065842e810961902070f420b4400c0c0d4007240c0c0c4850641030700c00043c0140d0ba62003070190013071814042c01d40310400240554400c12a414026030402191790b50340d802c00146602c0c07000c0d81c0551a46440c9903a150f035404030820b010300c21100071844400301600c9004903419aa9282c1c0045160a000001a1418100150f201c1d40c840d0b0081258030301d0f4100300c4444080f602c012402840815039440040d402c0310709030000c003600802c0401101030001200c9000f030104241c410401840e29076170b44006801c0812507080700410940000d0070071003541e44110a680c1d81d581100038504e03a03802d42c3c0001489460100a080d2038000c05200c4021181e640080381e000464010300f0055807494591503817102840300302c0e200c40c04a100645901c0070760403d0701c1003000781b4106030000c184c0045413008105400d211406490000d00c2507 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 12277722 1250 12276472 12276479
    0x1203012706090e0f070b0706020c0a141c0e03060103060519020c03030103060b120705040b01210b0102070e010609050603130501090303090303050115050702060d0204031406190605031c02010204 85
    0x24814180103006030a0000f0f24104070303448003410901c25072254030040d4080318041c8505010300c400c803944580e000c400140d075282015045400e098291074090420300702480c22901c0c1120201d1034810b078003401013124428030100002916100f8242403c0740e0594049070050000031700175408960410402c0300640210b4200300041d0060f40c0c0041114485a000400100104921801803403021001112030014000d0718403141a503e103c24031985104540328148460141d004010b01b03610080b800c9020026102d5202e04d22001e0400440403500510440740006909074403001450b040e030b51036503103c14a041c64501084829000a0010380c50200c0540400d00054002d103c1d41948a1098401107010460b07410007404840f016400b40000064107030b0b007060481e80c448125022950304070b88541d21785a040171002c000340200d4000418501d2540c02e03200b0ba210b400907001d0700c07508808004460543c0c000c6110300581e2601c0c40b40b15055840401c80c00980d80e4648121685d04200d4800103040c00d54 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 12278972 1250 12277722 12277799
    0x102010b030a030c0308010b09100e04060b070804170a0206070b060f0d03030f0506030d020703171608180402040e060d060908040909051606020303040b040c050d1202060603120301 79
    0xc0d40b022804620042d541c4010503400800c200e00501100e4003d0b400c080ca25000300c2c50301a044041e1008200380c98010295641d10741e0b0003040a040ba00b50819102d1a403480c010442d94000c0c081d4003000058000140c0c60300f40000340c11304096601803c224100001542c0740c045000f00904143e9001d6a0200c0001c95505e818000f110001e01a580100f50758100042400440b040600681d0080d0403400361a4001c0d600094400e04403603201513140304404030901100e81c0c600659020b840ca0110040c015401c0c0700e841400303040c40e000c0e000075980340c4c031984804101c1217200718072510b001c80018000107080c5291001c3e081c0a01c5004401c085171403c21590748500c0b940c8a42c000c04c0200c1d42d541c00540511400b00100003410205460305d525503424500081d66900008000810341413421000a04100d4207038206c43c0107140141441038103811034945809a10f90f8492800700612841d40007501610300014504440104096840c0c556402c203520082c4d0902c401c00d1900b000070414015203100c95 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 12280222 1250 12278972 12278983
    0xb0304240b0d060603060c0807080106050a0203090409030206090714090606070203010b0d050601260615011e0504091b0c0204050601031410030201030e070812072103150902040e04060b0102010b03 86
    0x2485040005130361400d61401d60121140fa03011002040050001c000d40250419100d0f8152031813070400b01e0b210380c40c0400892461080e8400d40e504217042c1080e81c0c04140c1c0004805014a000c9010742d0402510b6900001407002c8030442250b0001c2803001192160070298000c1c010280041c00100f06007505201155062041000858181c0d110b0001001441c140307500e68000a079024a401c0302c15002c0903101a038030f4030003070000d600540c00d030502e26005a025018441c8620140020000c0c06245078001410513007161040302e40706070602c0c203050000c4085841c25003040b41c040c3c071000301da50055004e0100074100244081e042c0340d0758061050000121010f924030810a0150b034850b00c2d0300b144001010350b14030840082c443e5101e128140403140d0041402c82441c580042c507180c40f40540c0c108000b00c1c11409428040d4101d00e5903d18240c40d505402200301e10900c0c442e407404403551503e000f8200d01c12880744058090500c004280083c1507500301c100c3c039503030520010400c112414002800d25 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 12281472 1250 12280222 12280249
    0x30c110a120507031709180603030717030708070c05060a05070318060b10020705010804030c05010906050a020304051605030a060e030d140f090606010801030f0c0803040803090a0b0304240b 83
    0x55000c0d107410410012001549031020801e1700c1510b080c41800c03400b1400b107100c0092141c50b0360b84035100045d203945042003a01c9105411005141c4040c485000304c601a90081d103000e070020706c3e5140010101e0340190402114542e004004103516500c282646000305800390500c0100354560021284403610100c254002501600780001c154001c0400c008103050503800110942d001007004101e0f5a07003116685601c1601400c1c030009618080c9805401001041c3d0020701c1140740a0500650101640c05103100b40c0c403d00c2210303e1031070f01c40084c41003440c440c455182d25a128407648000070703a01c0d0b0001c2c00c02c0c045600031030f420700700010780c010103480c169140440d040d51031108001c0f1022404003d107420002c0007000d4005070410303c000a000d5001400b0180c481910308020000708000074810200500316082501d1310b85840d480c0198695100d0302d00117102d210300000101f20000031500b00da0207294014014800f4040f105400f0a100e101a040041816592180b0b00d40076280c14210f9041d8 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 12282722 1250 12281472 12281483
    0xc07200a06020106060201140108070e07050903031206181009020a03090503030a150e04080702040e03090a080c032b030908130e1902071713050303070b0f13030c110a12 74
    0x13402d0806100a0071a05d503400400301c02007642e0010840e564011988105481a0403d02e0406666084050b2864443c141c041a003621000030000b0580c030030306013154040c6408071540c0c00c0c0b02e115034540c658080c0c010341e078404400c450101e0401203901c07281d0050002d05004d00303000c00d081c4884d40764142145c00444002c2c04103a00c1e4005402440030107010a0054056078490b142d04d400d0589500c40340b0700501130700a0045950700f40080d940f070401c000760307918200700411b809030712903e410340c1540744d0340300b681c2c594001e1140d248000c0903041400b40c1c01400c0100681c2c00110020720041c01c901411040006981d002d10801c5034454251031528800c02400301d407141c0000a00340f21030b034841c004054200ca05859841888000f001515207030f02100e4075501d00b4100754032400003550480310b80000ba8881030b0705110010f22802006034540e842c1d84209840d11011030103a8656514440728540c045006002446041845000484482400c0501c0c100502088040303522000744080705444ca81c42542d4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 12283972 1250 12282722 12282731
    0x10c060207150501080703080f0d0b030102181005180d08070503040806040203100204050f0108060402090307120210020706020706031a0a1d1b091c0503030705030f07080c07200a060201 81
    0x88040203406444d0041503114001e0410351719581b18481d5a00902d102540381c981c0000b91443c09059a4014040c80f40f0018001c555540c1c580540614620281401600500c2001c2d030300c09585020b0070035102c1c2a4045036030488144402c00412901c000004000c4501860600485010400400240c409003291b0001000e06007018010145458481f900e0b41c1c171b401d03004220a0005403510341d0700f4031000e00d0070b0820300f03119198540014003030300444076203540522501d1400100035104969402070b641c000d0301c6003c030f01400a00e041380c4a110a0050b02c3c00350340240b00402c6240d200707900141000c224030340d2a10240c006000091101d00700e55018041100d0141e10050402207800d120315004000b0b480d0040740400e00a8400807903018200769584204040c400010f20620071015080b6610f500009032a036914081c40040d0458000356502001e150344000050091806000302a0103400e00076002410102c0582c0c80000b005d040c41c0420ba4600c0401644070450f4451001990251409400104 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 12285222 1250 12283972 12284003
    0x4052407030207170a030f050a02150705070201030e0102040605031f05041104050103050a0b100e030304030b010f081006050306060d020409050d02010f0c0810050405130c090f1103090601060e010c060207 89
    0x1180103401203030038840c2c2100b40d10900003904041040307144180b07408c0c425195424a01300360708141030b804180441104039000c100000c0d6018004000d914401d0320200010031001640034200e01440c003446000c941c042000c40e0400c6954403100203507403684602c03841d0b0780340c0320f9021074140d070341c00e40d2040c080d54008207051107a503806002e02e503801100c807030041009680d400005207205890307030b880b1000c0c40101d000c1c501c0551024001c860165400c584016000d582d50b021040d42180980b080e0017003409208813031184482c0d04d00500049a000900814042c1c51f1402002408280540c04903401680c2d4442003000401c2402540d511000c01d4000064210a0540360b400352180814600c04006c1540200700f101e0f102031502a0507104107680000d5607980c0c1490b01480e1109078040540107074171400f80020b00301c405800a80c00e610b10b1842c1801038008148290b0582c3c0425220032035241c100000500c540340c418694004030303080526081984103600d88812003280d101100c10b8501c01102e05409 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 12286472 1250 12285222 12285239
    0x110301030b090609070303110f1605040b0919050c040305100504020108010503120d020703090506030109060302040b0603010303210b0d030201020304050606060a0f03050901090c080606090c090604052407030207 92
    0xd92100e0b0300c20180409282c580c02c095203451a41c0402024000307400204000e00c401003144900e07000440084131303152104880c0d4094000914810180308a050407180805406d26a098a006076444600c0c2c0d80000d000e080d80201420008080b608010800c3c0800000700300100100d144064480d01d0015150070a40001800c0190581042c0d001780d01a4181114103d626411101076488000005840b000e5030314044900c10100d07030159500040120021682c1500c40e0b00000441b41f0032a0f00700070011194060288038042488081d01043c00c17020742003420620384442c000030078004240080d08405120001c0e0a04450241c141c3c0140c1d408020802008010440a500000102d0f0714909001e4490b500818142c041d9406104060300d58010641c005070035000303a5441580270b25110b05042d20741c4e0b81113548407401c4801c54401e16101001c82c06010900d02241c8400401a0940785020b081809103d040941c000400440313450341581c10100402c0840a041039a2080d0702901c41c803490107118 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 12287722 1250 12286472 12286493
    0xd0c03021c0506031510080d0f0201060f0501090506090f0306010b0706061202220e070303050a08060f0114090f06030901060e0f090d030e0c120706090609030f03030902120111030103 80
    0x203250194500803d001d510b0340c0004130708220031100c2c119080c00366503000d00320007980110351000085110f400219200785421070403c0030b642c02036030300800010b541d4020a50610005102c0c0e540400d80085080c007150400300001d001002c03020304100b4002c024500820f08e8034030261705c01c2640c804041a8501080310500a5100424510914071380107030a580004079507080700740300010710007451a0f82c40380441080d0070000010100405803030401baa00c1c200603010794072400240380003c804100040091515840e80c150880041e982c405d04555403121503038203030303000c8030079654024440c2040a42e680da951008500c40c00c1e074240013280b468a800d202c0e07a0030807000703407071070366203501d1b24040000341c2c240000d401c1c034005c40c1841c3c0403560100750104c03181000c1c0704010040e08185a80b0a0003e078960001e4a1400c940c07071656403022103a030343d000c00c032480782ca40d010040144004802c1400481d10907000104200d000a0501e400e105142c00c3c1c5500b1110311b040220100c0314040010010321144040c0b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 12288972 1250 12287722 12287767
    0x8032d01050411030c0901051317010209010305070c030f030e070e04080901030b010207030809060708070206070605060a060c050601030602092b0210090302060a030507020c040603051605120304090c0201020d0c0302 94
    0xf501411070070a0101040240a40440281004000705803a44000c083e80c480000402c402c2c5d140e41405880b07216100d0107940310401881c046030800c8081203207a440b030a1044155a0195681c5089034100038044014108000c82d02010344204c1002280036004c4600c02c070301651080022954544400300007400761002520304a05540000404201007000d06080b951680c1040321480c0d5588881d15100c20b1600030010301a400260108114007080320303e030300450088008a4428107107030750781e601c126186401c0c18401411604400010400105580c0181224880003040d000080b40d815440c0d0400580e07c5c80d490f80b02c401c2e01d115060560814564000c844c0c441c40c03802a12031801c0d0b4010440768492141c541003010f41c1c0fa4006160305101703120740222100000c200748003155403410120313070340e25003c07807422500400c9010000c1e043c501011000e490014410146003410710f010042401841140e58100035035400b04540388044401e07202c2c02c4034002c4a910700584030686c040c03e040c40c400c100ca1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 12290222 1250 12288972 12289001
    0x5010509030903030403030c0302010204031a1f051c060b09160e0301020313032303011404180302070e0c04030b0708070e030a02010e06090604050603010303110f0c0d08032d010504 79
    0x2280d28120f8030080708560540f501802c0840300b6101d0b40ca4100e0080c41039a002610071141035800204600d04da0303012a000d805800c001104141d4111400041580c00340308031688560317080d25080d0400845045100a103000342800101f00345464040f0340120001c4940c81c80c218411009038040c6038016075903c0090700198000c60440c68603100b40320403440c0641024090000d82259034201c2ea00c2c00340d10b07031200707a00c0100ca15200c1d41d441481000100564100034030840c2070240340341c41c1200560380c0d0103c0942550080c064180781102011410401610400802404001c003002140f824003001c2e00420f15680c4140681c68480c600915810720440818840c2d0084029900541c2e400301e0790864040003212443d503105910f000042080c4240da000036084a4080000014140c01080780034603940420180c8400100b410711a40c0c995000e5003915a01c04140440c1c680881e40000103542d1006410b660301c0020045110001210111726840480d4180d0100060109060030300409400d00d9030341 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 12291472 1250 12290222 12290227
    0x5030412030e06040807050c120f0d050918101d0604060509060a0902030703020702031002040305150405101a03030c0d09060201060605160201170901020301050a0b040303120c0504080d08040501050903 88
    0x2d180c0d0940310703c805440505a200c000ca50001804000e100ca910041802000b41c0000d0106c042c1c400d41301c4042803844102d80c02422000030000b40141c0440d0f0080400030284040e50100342402c9500200c0038158025a01c200c120128905600e244103840144d040ba95444052a00c00100421b5580c01e400881c0076981d00c0c4240842d81d100c1c407c040c415078200e03010241e1255541d510450090050700d502a6042c4281065503040e8074a42e4000c101f83da0144050f914800c00c0055014407860003907400600c19442503c85d0072010007142e003e81d08002c00030b80600310341124903002a203190001c1316043c2042c0c101e05100c80d091500030303080714002d00150000703016013441c2c598060900c1c018107201c0c84007080781011441c04c680c840e80100f005548602e0792960f45040210b400d500030740090113414083d5030750303c1c0c020a01c2000c00e070070398045a6056969054544503e8042d40140c405c80131194103001040c48041200d120900035201600c1c15030f669403c2d185010b041040c25100701030231000568004 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 12292722 1250 12291472 12291491
    0xd0903020f01080601020f03040b040806010e0106050f03040204020d020705010f0605040c020c0405221a07030209090403180b03010b0d15030b06010f050408010c0504170609060604090809060a0503041203 89
    0x9803440c500070078100b401c0400751a901c0e40d005030304051541e40d182041d0b000004011a00d654444013800941e00000c00312001d680c2c0300d0101000400c401e000380c2012810900540280c061500001c6500034405040941010f103000c1c40c3c4001d07a08140e1045501d03944a0b0100403800001d0710500000b031000b1203061051a6600c90043c0d240c80c004e0040501076a19a4002003c0c8020300c0440074030350b1356555001074203c9160803c0c10380200120100141401030310049514240303c0c0c026282050001040000c80c0d44556030117403203e03104604100e120380c000300c10024101e030003000958001c00528080350b55504490018404071168003070301307822100c0d041e0014408250700c010303c90f90003a42828048181500c411065520b070080350720403145076080200e20000aa800700141003260080c4c00e01c403004500ea5408151100f8045584400702d5201000052152400d504010103590085040b0344c80d0070000e00c00305145510104140002c2a00041031104100014401000190b12450100205040e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 12293972 1250 12292722 12292729
    0x30b01020a02090a020a02070e0f010f0b030708070e03190b1501050f0405060a02030f040603061401030c020d080a06080708061008060c0a05090604080109030c02030d020c0105040312030b0d0b0103050d090302 91
    0xa004d0b1042c1d160b60750205149800c03600800c072a40140c20000c9404500340f03013040d24221031010034010080058210400048c0c68210001a82e0194240e522400020340d20140304403490361030141001d0f07041c07140d004080140031400030304203500760003a03c1c0c0e6410391414031400c820200d103817800c3c3c071704006082000d000d4454035a0159425030b03904584544d550384840318120714500484c40e0b40313000030800280c00a03540c1d8041d8055000c982204540002c208102c0e4010340845101040110140e0040340446601d41c0c41040b4080c0c1c03200e840301000480d161940c2000f07107400d0468107d015640c1c0400c00740105000d0f850a130b800201550001404076181c03540400710340d4080c0d81c15984c1030000c0480e1407109540c8450684021703000c82c0d03008210131642420010008844524142e000b0700407081c4c240c04c0c8a10200309000400c00c10b8603460314251640d80e884900e00c2602030000d08155442c65410b00d03541d10402a0700b00140074081e0180741d54114102941418400c00f050340c2401000e50003080180c4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 12295222 1250 12293972 12293989
    0x207050a0509040c03170c060708130b04021908010209030f0f0712060609090503180102010c0912060e0601060c0309230d050c030f030c0601050409080f0304080c070b070201030b01020a02 82
    0x1c1c800ea030145070700e84940c5011014a00e031600018042c5e5608015200308100110140031070310103402c210f541c0d94540000541d41e10b4825210310140c050300c082c054001c20600000c15800a10292600400050207080389000381042d4201c00e2450350005074040042c42d007084804008511800606044400c1e003003c2c1d6503880492007852070b080b0514581c00240841644610300401c0c00120078072500b0640d1908503181c0c5c3c0320350b084280d100380d1007201c402c1030b520510401f84500900c0d280c052269003001d07483d100c9a4400c2c0402c5610503100e6405d444229030a0000c60300818082d03e4614a0840303074940a04039145070740100c0149400140d40890201003c2050340e00450107a07101041c03800c403400c0c00703401e002c4c0e1151443d42611845015071031684000004200311207589003901d40590322102040280c0d240743d1000b4129007401d124500384070800200030754200d032280310143e18203a69000781d1420840c95078844822028003154100c2036582500070012031400c24800f44c4619640c40c0d00044025 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 12296472 1250 12295222 12295229
    0x604050303040e0c0c030d06050306150312161203090c0b030c03010909030519050a030612080304030e130c08180309010f031104030c1419060203030a05060126160207050a 75
    0x80c20358404100010f03d80c034100d179089030038282920340d181400c00003000a040740d4883c69000744201070010b100d0459030a500201840c006011b0302d0b16100c80703c4002003a4101d095142c0b048000070180200181d41102007140c076180603100481c61180340e081c030214a00560b8081c3c416032004204111a6460180441c1c0c15955460700005180502d42802c40b218051948102c01031403511640401041d0481c007d040000c03030300c0d1360a01085846100c580e0303010b031804e2030040400e881403011500090083c100801003c0e00500707050741001c071708840d807000d0707881c0f50246102140b00345007032080d8500c0b82c0607010182c2d4601801140340841c0c00c40024100c0415491030410180d80304540007043c248001114001c5802944501c20036494204503240211491141846445030b4500400c048140085800c12150541c01940c08c0d076076940c40c02c0780540300003490541044540086240d4140050403521801d034000030b102c0307400e49040c090458036001b61181200c15540540b204108503511120800242c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 12297722 1250 12296472 12296489
    0x7050c010810050402120105040e030a020a06020a03020705160603050a09020d0308040305190503100e01031e0c120f140105100603090c080f1605090402010c061d01051005010e060405030304 83
    0x6582d542a01e01c0c51021590080c0341d0140c00051a0348410f01c113101c0c15410b0b290704803810002070407036541243c0c0d41d1040d9080b42025800000002c8040f41e000c2d0701516180d410f0b800d01500d081c0d0142e4507c2d05240d20b5040079003003140792045c14080c3d0b540c5031048a5014103852401c03c81c00d26103800085020081070310007010016a02e00240405109a05982d840c0340c04186070740f0018444034018000d81c00440c1c40240c0a00c00d1000001c0840751091454100c070380100400714541c0b14507101c1d020109021009994814541c1800240304070f41400000d0864060601841b00c8000351500305070849010143e41308a071304000031f0109030b0b0211500a001c03180a03041c0007850241c0703850465441d5400d81d00180302405507002c0c4222464000c40c40703010f081d040203500710416442d4001c210fa039202c1a900640020310b100701c00f20000d03044c0e510015148071928aa00c0031002e04194803402d507401101d0f50644401d10800801a03541c021000b0708000ca0102c0d01541030904010109540740a42d2141160 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 12298972 1250 12297722 12297737
    0x70b120a0b040905030412030e04060e060603090102040b03100e0f1006030c021c05040501080a021306050703020c0d030509040b030705060d02070311100204150c030f03020c0309040207050a020301050c07050c01 92
    0x607554880d804005555840000c0c0c0c0c0d180d50359000900400651210180c000c100480c81d10102d40c641842510b003560500c0f10000021f840340018410250402420705100350360030400801d074645120051032050103c2080050391600303281a0440030b08002d0004086224400148400c4280010312481a1080340c50f002805040000c0101e03d81042c40410084032100007019042c02680000140252102a2100a503075210540a00101d201d030054140c040c060070501886850b02c02c10080580c6400303881280c00b041070f000002100c860200c14101d0208000250680840c2403501400c004054120090003007035151502142c401d100303048103010301d40d500060400426000d80364404031340c01c01404440e443c000d440203000c02580503010f0be000c21440c00540300e1000f4030428000e00a0355040e55030414050300d02100b50043d4122440c02d0721a800140412000343c1c6407440030b44403c0340510010700f034841d81ea006042c01c542014090581614040003000d0218000044950034080c0a2a0154 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 12300222 1250 12298972 12298991
    0xc0705010f0c06050109050702010e06100303050a140a020705030c03070602190203030f0309030306090604090807060c050c01020d020403060e01050c0711010507060e010b03010e0c01121104030204060b0705070b120a 94
    0xe41c01c0911200043c4020300e0f100000c5105101c56000911a480680082104c080c0b071000d81035403807108649600c045010300005000087c4201c0c00f40560a41e1420120303800c40c0040d40400c42c94101d103102100503030050740e04000c0c5240400005049210a4000c1d108081c14484020b485018049040309801d20340030f401c10464804004862403d011001003644070700f0703c1b01549803a0703441600e90030701c1344038030601055561401d8810465542da014080c80d1610800d03031b6860b0301410300340d440c4006100c0148924486c0d14428001000c0e4850b24010050351075085142c50350407111003080c08080c5a14007810007042128a40c101d0784015007003000d00e44001c0028004031079500c00c0540081c0f40504198841c094010150805600f0300b9040f07000b071002200522404e90340c2c2225000540c00a00da0070741c030300901003151b804079031003007201c5070b8142c40e05440b90003050956405903c0b014444600084110920809101d00344c080c04009210303d1424101600c60410b00318081c1c1030001040d510700210 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 12301472 1250 12300222 12300227
    0x2031507020304210c0f090b09060f040c020f060126030a02030301031b05060a03020d0b09061f1419020613050d030b01020102160809010e030c090a09140a0507060e04020c0705010f 79
    0x1800c02d98051404503a032500c0d19102d0146041b907100308400f42d820a0451606c0380740455410b03210b008040d00700c0b10207054020030000a00881c100400a502a400c040c0c00c240c101400054080d00c00a61074611a0f402d10350419440881440002040e80080c00b1032240980c0c08012281140d400c08500f1000c03002d00000020f442107642c2c41150b01c02e10000d00c20140c5078060700682080c1368040d0f001c10800804a0602607408400c841c041d40c0300f17505044c0c402d00c2242401400040c9422481d0494000e01040300c1a17080e030744182c0342d0741003201142941c1196075a041013019485815003a118414025554895540700d5005c8622020f05881d00101c9156910075415540f41203081804040f0442d450305120009030301c43c8030070500040d00e07100000c61500780003401d00012100174084610ba5561042080000c20005000b2110102c0040020f291807030100110745089000d00040d04025161031005081e0003103401c11a0b003d140148200c5000f208041303003500803900282001d561811242204 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 12302722 1250 12301472 12301529
    0x50c090907090e0106060306080d020606040e010207081809070c0b010501050d02090603040c030506060d0f061a03030d06081b0d1202070513021801030e120717120402031507020304 79
    0xc0d03441d2030315201e881e03c2c4030101500031004403900c075101001001d0b04c0f13007403081d00c0b110364400c58000751703104c00d022501038102a4002806444500c000505080301039580f11010f5201004242100140d844412460314000d00aa500705800382810400081c095503120021041446154107105000c81e10507034031403258044503050b5000410300c5540f07250038600620041441e00080e06c091159100056450401d14001075039550410482c9079404c0c03483d0b8820024207199013244400141c04040e1144d030781c408001500903000040c2021680508001920389810558407004140850000400d080d9488604134400d03100d4002045081c44131070703060306034909101c0c5da1141d42c200b00b48000138224007419a001e406444440500c5d07022401e030003401141501d40c00c50030b40070716800218100d420440b08800070300b0814843c0c3d8a00d40d1402002e9650840c6e500f00c2c4119032015040e25042000314a018841040d8030780d206400702001e400c0260300250f8038019802954041c400803009121464000e408 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 12303972 1250 12302722 12302729
    0xc030c090904150f02030705040504020903030c060c07050105070203070807030e041b0c0c0e07090605160204090b04030318030504060e010905040c020f060108030a140901050d0e010b03100504050c090907 89
    0x4a41d059091601c0e041002201e264030f90075481d4580965075000c07000d14002c41e40240c45035130341c2500302800c00301004000e502061459915201c20400c01a40c030105000e43c522a03c100380b078040d11014541011800e44030000c202c4c6085400801512000615285c144d0b980c8a80600d44055124a4440490700404a0a168882c40c200282e001003141d60300101030a072980c410040c401c80507940d203001400c400e0094071241e001c41c0d819807090120178070070b00281400101752400000782006070380203c1c044610031607055580104035002c0200b4107030140a4a120120103224801007202e25440c01400d9001c0e0707015603010030400d05507003442688200e4140c400f4201c0140100310150650101a55412400c0c000181c01e0244400000388204007106070b0380b40c04226200c0d01010090300e00c03504116402610000c0c1404070500030300085501c1407141c403190003800c0d80005501c05001c010036280c90351068000d0112420324081000059001c2203608410710240d40102054441c12105418845240c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 12305222 1250 12303972 12303979
    0x130609020405040803070905121507090b0708070c06080708180705040e01020304020a0b07170d0f020a0207090501050402040b070b0406090f05010507090504020301030b150112090c030209060a06080c030c09 90
    0x803d000500c013005000b5802200243c484002c0981e070340e003e110703011600607034807040358016856410400141c044090390103032140c038050b08002c0d1a00316a00300b9400c00d60003a503031480089402d070b04000c41c0c00b40d0040030b84024103040b0f40c185040300004200060050042c0b11400160b000d030510011304110400281800034000d00c910114a0381d0a4000d420481d4141d02c251079000001410720b500ca0300701e0707100710303000303000d004440110207a003402c3c651204860400040d601d00c614215a00c1c24806044a0917281e40130b040100e18100d041c0e4290340c4182c0100f44501c1c070410007000b845a00c24100e07600254841180c101954440c1092401408190009070840344181c0600040040640c003a504c200050340f11940c41e00c0e111414030007280001d004c000e12800025002c60004810411940076601c03052500256201c1150755040555441c02c3d0112200e88202c003042c8114601384011039406141540c1c5400030701e1a040c0e00400710100a032a0b1540c40d140040401c402c200c1000031602d1109014 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 12306472 1250 12305222 12305231
    0x60e03090a0603020702040506010e03030d050912040803030702060702030f040501260c030103050607031e0b030709060b0c07050402071e0305040503060403170a050105030c130f050906091903081306090204 90
    0x40b440030780650301c80201281b0940c070300340004002e50302641003c075210700c0c064002d5007080585000308000300b2014020102c0380c4500c8251818401c2090010400341050a0295407a070400f914040d01e02140600050155007060026841303101000f82a2021030702d00b46001c03103c0305403d080f880301d4116101400320791b010050080100d0340300490004d50403244078008a400507a2084400c03400c40e0001900c2c900b12018039a59108510300d01c1d0032040d40070000409031000b56036a00310540c22203180354091502c5440205002c401018113212040041c40c0a5a05618000f45030355800f18041c00304c903201d01c8a213800c01c4c600c41414860f1007aa0003401010341290740506050502070940d1f008441c0c000000e4106400081d4880058005e542c100d0324040c00070008102e0350020407201e4801000030800295540850840071645d50003001c0c02101d0b20000340107141415510241084802101c003030982072071032102d0000030f0b031201c000b070380c03040000044500501503844c1c44409031072030f541c001e9070090070f0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 12307722 1250 12306472 12306479
    0x6020408030313050601090209060403060506062206030608030702030709050c040305030d0f050c0c151f15020d050304030e06030621010b0a120309050d02060417030909010f08030304060e03090a 85
    0xb404030103c2805541140c0c1c807a0f80c1c2d00c0c413040a034450108859081070382407004000003400d0b03800458010394024501800d00502d4040050414a4142064058443e90b1400c00c00b66815200318805001c9900c090741c98403000b0340100703540e00f00c80e10400e0141550b90000880034103d020549002e598023030b00340c0341d8030200c240ca41006003004401d2548440e14200100b180544070300115240020180c0140120b80903035405601c00510007001141000101c0081109000240001c80c018102a030284a500603562100901c0c0110340340d58802400010018800030036000717110300422080c12a01c1e80c2da00d60b103840105201c2d40c41c413043d10703a0000345002d1042c8611410740100c6140c0d1b0060700c00001a17961503220390703111055800040c01155400c0028015420600c08000307080e40003500c03003071600381e0b00c00120780d00c0c00c0590259a8541c20100d01ca500e00c1c039203000100c0c018a0640c0300c80a04a0030907c546480744070107000106210717900d40c00080c0d80389040c016251a10402810341d8811641c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 12308972 1250 12307722 12307741
    0x203060106030f06060306080a0609020406090213080d0309030203030117120403050c0f0114070f020406031407060f0e0a06050a030e100903020c0307060206070809120f0c010513150207060204080303 87
    0x5074108984407480c1004c80105042c1d210303203d1003049520910003024045002d484404c0140342424059030030940b24078002c54006110700041100e0400c02280380804d17480e1075415414006603051030810182000081c41c04613074001b080e01c0c19a240340c1c0c5042c050140f1001c0c2545804245192000caa000200e400000c2c000007181d00d007865041030711107012460706c150044503090071404405004640a210343e40101e60591f288460b0390748041c00c00520b158682e10b42152505280c1140c01c0c0d103a111440a1100941c002040d094003180b40c1005008880c40c00c0c00900541c655000344400c100010640680c16842500420301036403982d019120f10541d00c1021102426400381c081d805031140d80e4460030175003000501c440840e07005038050542900c0b0400d04503050395000d003922000d40b0407584441d0154030440d0051039118482d02040d035803102c1041003a420364000420302d2248080030180c00000c54079001006600b03600c00e1a0040e52203c2502d80030009010b00d81041d42544004410890f5121 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 12310222 1250 12308972 12308981
    0x6050d0c0302100c05030d0c0207031401020301031a040b0c07020621070e03070e010623030903070209010909030903170c0105040b06040516090506090604031505011707030503070f0c03020306010603 87
    0xe009981000c005040c02000341c81180704c500300100300713520811440184c005607500c0f0074120f1980d403059030280c640d280c0301e900705000c44030f41e10390781650b0010040080024480340074000c00c55101c80c0d056289400c3c1c44000c50507800420f03140f9400c40c0003802e0000c55683c80d086034003110190501007880700c1e0b41001c14080700422100c0750041a07014254840030315000490a040300d641c1c810340c0149a00703140c011a001c01040a41000307104820021580280114025510071802c50f402192203801078010070401c6403041c0c0c450440300c5e107851940004241d000e8176642c182c9400031401495000c0400c400c0ea818410b4200c4281594a003070180401c01c000b005e140c900403c2c0c1154103000740e440d4040b0085a0481c500d2919001c1103605000304003605100300031b408101c100910341c5090594a8440002c015030b1301e91918045a5101e006000c03050034182180644100034000b80105804c41c1e035495500d00c5403040c06400c0028001c1c000c020405030410403c065903000d802d031480d55035a040040c0191 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 12311472 1250 12310222 12310229
    0x40f09020d05011d0c09061504030b160305100501081302010509030a030c02030d02030a090608090102070c09020306010f08150904060b060406050a08060108150103050a0b040e03040504050c09060f03090106050d0c 93
    0x445154082520007400a151203174904000c0c00f248140d1104c808019600100355a5194407143c02d00001002c65130364400c3c41c1c49000c0e00010007401400306d4600074103da4005003d9282110010741c1800142d078882c4c00154085407480302440700d01200d000507105070244030705495040c8030b039405c18400c040d402503a01826a2082d822541c150071004401d03a240d016980880d400255031001c100080c500c40c0c10b12a802c44e110000040c80d103806600c071000b2490594000901030340d000414003001d944d01100042c0541014a070418490520010421080c12140c00c114442c09082010505004080d80b101b0f0b841e0700700400320341d9103030390743c11029145801c10b2202d180441c1c80c900002c1c0d0b4950052140920414807112481c8250408600545c01003502134100b40f0120340c1c0385c0c540e403802c1d02d942c41b6054a145c0c2c1c01d0000c5841d80c1c940b004010995400420380300e280107090011742c0300350f02d07010709940e1035544a070590b68890b0b460b102018014601c6900c00340d4044040b500302d005105001d414902034 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 12312722 1250 12311472 12311501
    0xa020d090906030b0601081905071707020d02030904020703030213030308180102070b0703020a0201090c030c050301060b0c060403030b03030d060308030f06060306010806060a03060e01090501080607020607050405040f09020d0501 100
    0xa180e6405040701110050f10001c1c1514218400007051584642c04040d4403060743c008144071103502c00b00748812240200c0300d00c0c01080c008010520700840b0080d0980c0d00c40164801481081d00e8090029124003500300004c2c01687c000c1021001c060094050320390300039034040c610301c1c13055481c00d00074645c860076203080d4040c0315059070000401406008459056030401d400080c4d503200c40340300310000e50142c1d085100310355880c0e11180c0050000c00301c0000440c0110110045075040c4070402d800c54105030300c0b0ba000d0ba8410408816103140105086510503050b00300050040510b0010030b0a5204481c441c3c2d4a8070700c1c01c14044100030441c80a1409144061824041d40c0e6844c01442903620050354001e02003014a000039240340b40c58801041455094540401c21941d9050209180c0400f070700410341ca142c031000140b15085003001283c3c2c0c0900707584010003140c104104007410b0340c41640200350066071074034003009107001150800c01e0a00e0f40a1309000528a40c0d040c41ca0007402d95882981c030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 12313972 1250 12312722 12312737
    0x14100e06061f0509010f20060106020c040213030f0203030c070e090c060c1f021308060603010b010207050604030b0c0415030c080f0105011b1406090708010c08010b070602090d02060a020d 82
    0x111000301d00005405624143c840519043c015801910700020180c554005c0240c2c583e0741058194030781c22201c90685078400180500d50600c00b020f41450520382e00ca5010311710501402092500c0d070405481125002700729440e840e211400460704620900713603111004d205664000501e0582e0340d40da0391140850170b003542c00c0840e180040268038424082e07a444a64130030610304d1142c0b00d071489142c1400d00194030052800740780c6000951111001da000810380d4000c0d000708500341c102805884c0031803400744058080d10f0b0400002070b403940200d0001408120b9030400007030000c925002114068040e5011940c0c4004011000602401c03443d80081e00140319800130400415602d15400d050b42c2c4140c40760f50141c0d00c10043d00c40702000096040e40ea038140b008a450305404107106071801400340348080c000c02d604002c1000d007510380c525401020000f614004006e540400d01c00c0c0c501c02c0340c1c000005070340c828040c1c0014100c0240904003035804540007442c2c0c0c1c1066000242e481d416500e980320b144 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 12315222 1250 12313972 12313999
    0x6090609070b0d0f090203010c2006040b0c031003060911010f02060108032205060d060302100509030d0c02010c020a0e0106120603050a03030e120403060903080903070f14100e0606 79
    0x307071951003621409109000520540c00d005425402240d03100c41c0a060000e00d14080d42c00090035240c4050180e0b02065201221880381181c3c0d000004d000b078500300007045c05081903a03900041142c0103004122485003c40410700741000115054000c5d904001d007801201002e04080c0840d48014141d18040344040b0003a2080c42d0011031101d0486800c070015600b07084200e40e4001c4130700c060050300346921001950210300d580e1a08042c01c0440094140000c14904510600103403a110500c1c40e4207116083c400c82080360350003e04030440700351503d045410000d4900c01078503007144071607000f50301003401c5402140d8002c4420840d03040b94543d035200c05060740889800000c48842d808058801d0300001540b10209000c4d8101c4404200000e0480d8020a202041030603e41c1154001712607940e112600701e82803607440001c041c0c01c010701e070010350720b410502d0765074000f20040c4940042c01c00700d45180c01c491120003823040c05a041c00441040c08039000c00d1b0440c81c0c40b900b003250094030448401080e030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 12316472 1250 12315222 12315241
    0x402090a1508011d0709030209060411040e100b040e01030213060504090b0901050a0c02150c0c0717010f0506092a07030e04050106020607021002090f04060806060103060b0c0a060207020d0b0108060906 88
    0x28000d45e10342e180d41e174449042d5002d1090344080146181d80040d200c40040890a14070380c0180010880380e101c07161581061400b04000d51a5a40981030509050000303100110140c5000c43c1100d40c1200d408421140386441080501003962050303520614180721842400700415240344100c039080000c221545d2190401000c903514041241e00607071280b40741175903002c8a050501d07000130701341449a040c40c800300340c0949440b415801505101e0020300c0c00d914856424040e10741c50340318185080c005458440085210041e00030042c0e5160346a040ea45158254000d4542d25051400c0400558441541c00c010b4180d089104040303028500e402c00000b802031007c154540a43c046601070840348220a2168010390480010542d102151003c2c003407c03031381c540c440c0000400b0100040c241d203140000000d030445003c0e60022204000c200100031099402046044109a200d600161100312500128400c0c4140c0c0500400c1050300000100e21980001003903440f6000c40c2040760940e03941c00012 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 12317722 1250 12316472 12316529
    0x20705030d0e0712170c0d05070510110706020d09080d0e060604020301060503040b090c1008041109010303050a05070f020402040b040314010b030601030308090f1203070905010318020402090a150801 87
    0x314058040410001c0300001e200591140002e481004098200a000b80410b410310707186411f46004540b0000b1280c0030042c0a11001c0001855030300308110582c02419188001d12400d00300510041d8002a50313094282658450901550800f1007207444400441c00e803001400d0040642e02580328035000150941783c80d0084174140e5201d50388040c01d54842da40c030840901c801130006801c6001e0030911520549031007582201e40c02442d0764110071030402c2d042c43c801030180a14014064444a001840880e800c0021621140326178600156910100d05214500078804040250b0007400060005090f800e84c401a2046d207025801030800c0304950741e185030803160f0b40350200d605600460010004039010fa10040d034005013880035101a01c03034000f85181003a00c080180c5d246041c000c0301307020000b0381c819007020140000f0b0030104055210455065800e43c203804009204907000107804510361282c5180a004088042c2212240703496068003400d16042400f40c0c0e4072100c130a00e1000c080002c103400 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 12318972 1250 12317722 12317729
    0x70b0a23060607030c050304030503030703150501020109051e0106211403040f050d0206070605070309110f010207170c060a03060305191101080a0e1902030607080106020d0e0310020705030d0e07 85
    0x159490501d01d59005d40e0408006031050350140800e204c0003000c95801c0c80110720500c42c6a500040320500b6440e03281480345c65030825811a03140c0007250002440000b640124140880749180801d5409007140707015107101d410507810b4a90000d4402e150144101c628080c55105000020800c03a0300702006a681c0a1032084c030b05541320141d805c00890800e90900e44041c3d0001d40064074003040c50f12420f00383c030025140c1d03000003a51351500c0340602c03a01030300c1d20700510b200b242d1040e04100d403040000d40c1d403449030080c018001c00382581d000303209404101704459070001400c055141c90311400040c00821061000307541d00d0140e958001d48a43d4101c1d486030040c1c0c0d00210105511a04100440354641c000300305284196450b03d00b459140404c10501c04050301e940036990300c0340b09602c10303d401e050740502154103010f0030b20014024150080f400003103c00c05490803c80250341000000e1400440710b500c480e02c41e2000803c03400740500070005009450300703414180b0040a1400d0100d960321468407 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 12320222 1250 12318972 12318979
    0x51009060f150e0a0603020901020102040909030c02030607050c030a0809150103030f03060801051003030507050c06031302010201060b0906030103021504090f020306100e01120c0c08160201021002072006070b0a2306 94
    0x15401e210442c026405403230100010301c001030030140c54440c400c00b11a800802940400c01c80818082145410400c60303500000d00e00d17255042607a2600c1095403405403407410020b025000c00000c282c0481082281c0000c184c1c403800300c42c656500d04025101e45114503004000904110011500700c10500929024543c049200f04c200e03807440d101150960402e00c3d003120240643c00500c089a6204c502660146d440340881104003103c61002a00b150b1031503005441804040c4410f108030f41e6880160ba0440c2d80503913003039208042651023341d041c030854204481440c40d041401040403203035405540b081c0e5003610410b1454a45200c25a42365103c0d07280280050907924031280048041c0c7c00c03207002450f80d13007404095462142c4d21900190031101680c1110080c4040c04403e40d0703070400180030000b0340034000310316100d207544504070318540103c0400387c0003044099642c2140c0714101200d0341550040c12000301c9050200d400310142c200c0940340800301c2145000500c1c42074086a00500440006 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 12321472 1250 12320222 12320239
    0x10504090c030b0301051008010b090105150307020f030c010501060305130b04060c03060503030c0a060c0809070b16050a05060912040602031806040f15080a0b03060a051009060f150e 80
    0x20600005040750350300e24410151545110b010585090142d1400b8000f2018502a4141883c50050840712501c1c6454800c0308508010002a121400c1140146107084c100d2a5242d0754000281e1804203000e0700d502007480b002441c01c44511042d880f103416141580e0381844a5200c506260103600e222071000f8201140c1c00011400140c1681e01c508048015030a01080e1981d54000090440d0881ca900703080c2a0001c9540e01c0401901c0c0c854180b110344a802c02c2c20040c2080e881081d9111070714007032071081260001314080070710069480148101c0e80501110b1200c89540b07412074503200192011080b9108900d60503010420701004d42e000d40d005030380114201040460194032040005002582241c0d04200204244401f14400e0000d4038014003d4010000c1c0c640c0000c112040051100c2c11030391820b41c100600380c0d0302181958012034180c002140c2910f804d4050b0040705401d9000f8003010345440d5000170380550309440401194451180b03d510391118080640b400c011146c40540d020307849 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 12322722 1250 12321472 12321479
    0x30c03021003051e040204150306091101110703240e010c031407020c041d0307030203131e0e070e03010204090606030b0a0509040305070819110f0a0b060d0204020d0908030402090f06010504 83
    0x1c41342400e9000380024004034038012174000031106180c07107410549105491740324401c103005030841c1c40d1904031400c0c80e01d01904921151180c0e150542800001c0407041004140c1c1102964040d540001a10704441040203100039030900d80200881c0d500750f0042420a0180304541c00e5551125110b2047d58014158600380682080010005230240d42c2070f90114146c50f18100401f04080c0180d40c0c40303070f0002e664400c600907100e0701c09000750f4890000c0054000c500003040e10b4000b5078000312445200b100806443d18003003900d61410383c1652075003543c03000c00c0c0040c10f40c0302c60304054200c1d0700d5a14100008002c140034081400440d0003001d400547c1400400c0c00244640c000300403290155115a00705180070003200280d80342c4d0510100001c41d02e1000c11400c00c3d0070f2000c5411a00079030011308080032269186400004028155031150040ea6420025511150111b803841c0345122010000e4001c20b242400550700240d80c00e030f0042000310001403920101c1031a4078012207058540030704151a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 12323972 1250 12322722 12322771
    0x121509022107050c0613020105040303140c0109060204050406090203090303060108070c05010501030303060f15020607120b030a05060708010b0f030a110409090b0a0e030405010503011203090e01030c0302100305 92
    0x1120550014070030000d4042000601c49800d02e0140e0301c40c3c1e564540d0b0b10000c440b000d29102001c1c1074401c1c00e9800000321130041c0e0308a0100c0f8200c1307905040400400c00c41c1e0300541c2040c092040846259400d1425000410280d0fa0042c4166482150101302d66510340740050100d00046440d109030b0340c02080464001c2d0300500b00c5550000892411000c240b0150355601d0a5960aa1080300482c0c3c50b89818081c0d4808418a40b001c2d2061841d442c0c0b0302846000000d540b56400f41c540803d00484002011103800290080c142d2200c0160482c3c4001000303141842c1d81b14821104100020040c41c000706e017401110080701e85c3c44c507a4011031400c0d62203004d8103900a1500020303420b03144404100014620a51b400745148442c003079206518a8540910085c0580c2e01d48960800983c0040106226907a0444140c078155401240540b04c0711484c3c0c0b03820341d00c80c9403c2c3c014941495001d0b0000080110420064040d20701c00c1e904c058002c88030700002c0d82515429220714146548036110f801c0c2110 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 12325222 1250 12323972 12323977
    0x5070612090206120a06030f0602030702010b090603030a080411060703020313050f090106030b0f0405090114060a06090b371e0903021c06110a08090703020306010314010b060a0f12150902 82
    0x301c4000002c103261f50703941d150700441c46524110781e460340103c10044460303020300c140c22054a06480003042858901c2c00240c882c4102100c18003444024008135041c02094141e03100f5070780c2c000d06460359803c0fa905019580750004e10356180d0108804001042604010001058600010306802056428107000342d014162070712155800400c00011103a00743c1d61805012300440e0190000074403120642d80400b03041c080100700724001d264a1108002e0f0981c0004910201d07003c0c2400c41c1c0e21091210790380d44602054518000705070349000c5080c844064401c00c0020100c0f416218030380c8600c4038468010041c08140c085602080c0c61074400c00260911901b81014501e001044e0746040d00786a40d582d003150070204200c4038008020403401403180e0454501e40d08403113400014010749156500003661054140130050034050724070b224800e4030109412001203147c005050580720b2441200040c9082c15400842002a0740c1580c445641d031035600c1200409099040d4020446040001000c042e5 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 12326472 1250 12325222 12325231
    0x209011701020c010c0c0b0a0506090601050d021308010b3a050c0306010905070306090e0a2411030a05010b030f1f03061107020f010f0f030507090509040507061209020612 75
    0x5540811083e001d0380c03000e12071190403d04648600c80070407024100380f00c00302402000a9802031610b018000540c1d503250110798131a109107003640c1d407840da840c640c50280c05050450b00c1141e1040c42c0201d03006030190480c80d10f00c2c4040e1100070384542004541251109001900b1120040d032410044241030390400d10324ae2640140100c48d022440d00c00401d1500800368428000c559458080c010081ea143c0a0740c8004c00300c5a20a10030756881318074243d114403034503600409035a06040781c44102d981c07088400c40c102c0d0844201b08014041d441c00c001c140d52080300e580c040b00346000008503070440000d0503a80100718400304055036980c1d0940c000850b0051022166404500100000000f001402290658401c2030b180c03540722801e505c18414403620090505045c4070649a0714607640d40d1004050000000c40e00c0e001ca030a0300c0d1514151014511604100d03040340c1c207002040700744140000c40307034200c40e0755554000c4900c0f842410101248c000010080d40864100f000b1124180c44501c2d09421 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 12327722 1250 12326472 12326519
    0x30c03060d11090f06010206010501020312010b0904090f08030f16021c02010f0f0b03011803050d02090604030b04061b030b060a120e0d0c0b060901030c0519090515040b0607020901 79
    0x902280c0c00003695601c8200d0341482008210030421140c6d507414008a4018030007030000350304180d101549445c49072014001c0421490000c00c03d8402542d03250000090303150401200d0851500f01e040c6040190300c112240001ca01c1c01c1d5002c5141a0440c10000040c114694003401240d4040f0404e014800b40348e031402000c540d00c4103c15511820f441c07144040045060600280f0081e400080c1804d40d034441c50780e1044031594211140200382c12604a0301840d042c03c43c01a40c81c8264130029845004035000946030103080d80422040151a9004000d0203090503a402071000c0501e5086081d1000326800d6a04010140b2100f609203010b10744000c1201c200714400300c2c05010070000146014040160711001070b950111440500a1722020707107403c48401e4032592402d60554480a96000301031042c3c50089401090440e10080c04490107400303010400420310160600a0740343c0d6604559510b0705d0f200760300c0d00c0f9031b0040510f04001100c0905501410b209480e0303180907424500c1e801040d903880344 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 12328972 1250 12327722 12327743
    0x60a0302031e0907050111030c0718110d0603060513030203040504090c080607052808040f0807020a06080907080a11040207030903080f040e070f1d060706050108010c08060303030c03060d 82
    0xb250440031801512450440004012007440c020005126070020f07004030146800800c00c0d10041c150124409042d10b00b980750841d004c0e15004543d000400041d0311480e0304440c00320300504859001d41094080f680501018032490322a651007040d002c5802c2c1c4001c0260b40b0812081115003001e4200d012103e029201002d0441d030380b029a5800c003035089940000040c2c0000b60310102a00740f005c0c0602440c0350142c054028035849002500070007014102030400da010780841010840400c0807512201d5002e40046031541e0381d014007525481c0305131544d040c540611980860707800c000003500704cc1c440e08140c1d00494800c844003030200940c046003084e03003000205000803011800204c020321081006054031565645000d0030b48460450290501003004030028000c618a50b001c1040903882c1c24585900103202030b0f1304001140727840755201c0180300d41d00f45400044c00d250194040390400000e500d41900b07659448040588a2004603a800005882400840c5450a00080d5100383d42e103c0d041460 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 12330222 1250 12328972 12329011
    0xc060f0a0213030c0602011d12030c0403061803021903140d11180405060405040503030403200106080f0105060604060c0b0a0902120a050d0912030e0402130f0801050f06060a030203 79
    0x4980750a03541080d9092000304c141004121390900c42c45039400c203040700011038070403102041da40301d985a500003101c007000400415409016801202c0055500103070410192440400c000d00c1d80d001c000702a00507000752500480400c04c0300812000d800d5243c0d691404c07240d03450404100030307003000c06140032890303a50620551021013074005010400420a150646050810402040c1c03413006045501031402d20b401d2000094000041e0b940055042c00c04480c00c040141342e140c08210a090800710540c01d0003c0028000070120740400501050002403203140e44450602031030b40b141d0300c28040010045441c21000c540c0c11044903411481c840030124080c0c140350000360302c002400b100c6500c507030405009081000003c11a09000b410701e0b0401ca03040d40d180810700a0080558100502031000710100c503900c1c4e641b1941110801d82d452103645861a8980b18100042c144500070b0a440f9031170030010880d26034240300c800c1d03c18000201010b1074504103d000700d000e50000b628002515459107480c5 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 12331472 1250 12330222 12330247
    0x1902130801090506190209100e0301200702030f010c0503070f020a05071d06010221070507030203030a0c0b070905030709020904140a0b0411070503160f060501090516050c060f0a02 79
    0x70b003031050180d401403090b42080703601d615003041040420b0051501c10004002c0039112240101c1c1c80d000c6905101d0038031503a00c0082400740c118010119107034246108a0340c2540d10b0380c405400c5060080e4100c500c0021200c03205422a80f860741c03558045201400000c000611494204041311106d10540707400c010705640e80340c901f5100d0f400601000c13a0001c2c0c54514001800c1e111030b4410030034802800c075842c15201c03a281840004040243c80d610004000003032000401201c401103a018040304c0d0745400f0f0500c01481030380c03030030000c59200c8034400115065620400c042000d40d02d00a002c3e100c180d1411410703400135405580002c0c1c001d5104d040040400c40b10307201007441150000d0010038400d65000400049440c2018010200030f002d10243c000300c1c0d4008266280307184180801e0070303940c40c542480307140035a03400f800511090400c03002040c0d001480d0441d90050803111140c8080720103040055889009194031030350203500480004040c0060644455008003180d10014070303084034072991 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 12332722 1250 12331472 12331481
    0x9081b011205070e010311130614040308030f0702071205070909140a1103010606020102070f080702010207081b0307060f020d08150303040906030203070f0302090c0703021603030305060907020102031902130801 92
    0x102c03c007281e083e1060f110f96507010300442d10a0b2444d000d645103041d440441c0b00540304058090542000039440c0e203141c080c14a1001c0750003658003c10050380f2442c0401e024500e50744c5c01c480d42001402a42400079542013038220070100150701c14090100b190400c1640c0c00145200001540d600580000c6403462500622078010054058011440a45001c00a02d800d48040d075020108580c41001808045000340f2854406160b0101405688074200d00040380303050720b160848081d0340a00c02c5001062400c00440c617000d0f68003601503c81d110759492040d24074615150114015070400450f11121310700c1040201e502900410444207503959203000300b460354209400c9185035903626a42801585410400d200003450b01544202c80c03282958013003044d00030040d2151040c0c810104a0bd02058002e0004260712480b6034508030340c40e5603a0030001d0180100703944603030060300d8107404900b4081c410b008480c0303c0c001c00d807800340100c1c403075102c0e41000750f120000140802040c0d02c4046440e05080c0074 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 12333972 1250 12332722 12332731
    0x50904091205070302060106081902070c03020a0b1306050f091c1407030506010503010207121d090a0614010206040c120503040b0f0a0207080f0606010804020409051c0e0109081b011205 81
    0x5540c0d841e0f409604c2c0203440d0000c103070400d4090140d41c0382080603000190360007800c60003c2400150301c3c0c0d51036241a107441030f0030350030003548500060408608190035502411140346810035408280d0780d03072442566184603120316081424410001d1101d14103212591134001c02c10680d00340c0c500350860b00c4100c2038203020302502d251900030100c10800d00200f0001e5901400d0114000c52905070960b40d203691454900003007106100da03022011101c02001c5843e03405000001d00714a03245d1a04140c6013005001c14001e00703d2501c14503031529161351000604074440d03944800e02a03031301801c00340b4106031505280c41c02c43d0284000c100c0441c1c45081240a0100380e2140303082940c90396800038010b0b05040d055004400070b43c1c80102d401080e08400614a0740043c0301b820541034070303112800424060050510058140c0c40f50b40c040c1001c00f0020130740d851400c1c0c0c6c04d940b032a12294940b401110000c0c074a12602d00680d101490294031400005040103042e4014102149200303104840700e01543c0701220b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 12335222 1250 12333972 12333977
    0x903030d09080d0e070806060409080d090303090618020a0302060c030d02160b070c050703031209140d081302030604110409020a030309150507030f030f021308100e010605030601060509040912 84
    0xd1100841c2c9a980a1210150b0750304024200282c01e0005050780c46a008103a644927984030f403080803d0155041c1140c20102001c1c4051240241c1070801402620369084210358161405c13140b41859245d24600480c0076500508003000305142d0707000c04c1140e80040300729001c0c27030004100e030a441d80360b5440200b0070414200c0c54211390341e0305070400c8803204000418030801d0018201e502c40005601080c0c15003600d6050403e038030071a03502204c04005043d0b54000401606c0d07028200e54003810002001040c400e0030380c1c1d030402c0701d41d5200c0c003d10501369044402901640310002140001385034505d4448041c41c003800006144e00c440d00000c480000708d50041c1c0214001c06809e002c8500404506c6c0342c200f6807800d00d245080d0702590024544034000356030b4000c2580c0c1d2103041c0c00030000c640441d500c00440c503c0000b40d651b1116003071500d6806295408180da490300d0303000c0d1203104c41030048208880d4001c014114036860700f0029260382c0c0c001404a0780c8155100b100308000340131025000c00110030355 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 12336472 1250 12335222 12335227
    0xf0e01020a0905040e01020306090a05040303150602160b0910030f15030f0b090309060d18081c06050d050c0d08040e01120302010c08090d0c1b0801050415050103080405060903030d0908 81
    0x43c2440100d40c000300e44809164010020090140c90300001c882d048203003200c0000b0b127561181402c80c02007004000750700400071032200004090b070307001a40032500c42d01141901e12440d81d80f0050701852082542d4540c01c01410742008400b0342c0264040c12103012883c5020400400c04518032004243c0307504103d5813080745a80c42010303c5800705c1510b900074186001180351210380d80c0002c0203400382600515219881d4140204400c9203140c015a0300740e44560829141c42c0312148040f1130f180460001000e00b0320303102001030703580f418060380c1d4403107a0000b000d00030400c02c403c2440341c4075130440000e40f01c00008100c0011000b184184060080141118165071004a81b90003403d60750030b103042c1e0f801c0000400900114030303030104260b0f034020186c1c20001040074003440c0c0b0180006403110030320540c0c02603000000f0307502130641060b0301c03881c40b1703030350040d0800554668001280c00078000500841c400f80320078001400c02100504c0320800040450741044040c0180c40c00341c4031141030403200740402 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 12337722 1250 12336472 12336479
    0x1030602040602070602012318010e031801020303041709010504030f0606090b0d020901090509190c030c0b0f09011407020306040f03090f0605030c0a031407020a0506070302031303030f0e01020a09 86
    0x6012600280510340b002340903e0000070881c52541d0f0442d19500c1284021a000c501c0da6110900b46101c0980c08100902041c02c070340c00710307640f41c0c1c000241200c03070181d05c001486c0e0f441d032011088900c01c2d41d02543d5100452840c0601c0d400940002c040300e0b051101c10003010000c02d0305407800c0355400c0d10410005c11000d00707100840040d240c0811034180a660440440c0e80160f4410001074196001110002040e80e2071030001e5140c6081076019407018401400144207003c0c0030141501a031380035401d206a00703a59100e0347d207414418410110001e64050200350455031243c05005158546080000d0808000750002403c040d019681180e00704184101c2d042050380161180f401042440d00c4803046a142c4030002c2e02901c0300400300c1421207800540c5941a41c003c1e4090194101003001442e800c0ca0020310203035031a20404000d0b980d5100c1c11001814507486402101e00c122403003281203a11000e10395054001c0c0010055141d245c1d900c031260054247d00074809000c4509090303a07140b155514 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 12338972 1250 12337722 12337727
    0x1503171b061303140702010c0b040204020409060f03021005030c04090510091b0e0f01020a020f04020714060a0f021614070305061f0e010b0f0313020604060e130501050120011103010306020406 84
    0x4410303ea612040085c06181d0150ba00702151415158103c03082d0202a81da40c40020024801c942000c213503686060b001090181082142c50141c0c0d00c03e880343c1040121440382619a80002c698203c60074904010a101c141b100b5006550000ca114042c00480f580b03441201702a520848085040380000c00c2048041e80d90003018141614001e4500e507580d1110040001d44034110000043e000e25101907040042d0b80b1141d04444500d50000300c1d10080404c0701c5403054a514054401d4101c0070308001c40005450403901c01c40340005d9042e100765400303281070350380c2c03645601c007545503441da0340640800080440c900b03100143c400c0030038803500c2c0e40003a02c405480c2e010382d0311a008881890011401802403180d1002200c01c1002612207450301e95903146e001c10b81200380340750001d40014012400152541d00700103401c0a80324112000c86010051040203000ca4100b40704407800510801e9101000e21044503820ad03041c1485c0002080b202d520426480c3d8a0340700f030f482120015400101002801e5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 12340222 1250 12338972 12338987
    0x1030f0f0f021324030b071b060f0e0d0509060d0b0f0d050f0f030408030409150f030b0403080c09010903080307090e010f080d090f0603020901050c1504061503171b061303 75
    0xea0403c42c54807039174115180d0f01c1c0301c03810091100c4180f12482d001021910b00170351000241c6035110406000d1414030180d40f1010703003035001d001c1d60544104940c28400350b0160040c2d84c2e6070040500b42c1d500b0b00103441060009001d9101c80b00c0e4001c03582c442d084e01c5a847d20044254100d00940081603440405568145041d24901c054401c60f0002c5c0702c02e02c00c00502004840032268104000306003108500711050310592154032a1618440100d40001008079180419110705d000c0d842d00725440d501c10100344c4041c49070303c0549002442c210380c1400056422006140c1021035440c0c4002041e4880c604451031170020307002200c481c500c0d00000c02c001c1c03504000030b1012400071700c1c018000d00d1405480d40750301d10803030081c402419008654a40e580e441001034404000b00e50046400782e511000055503104402d8a003951324508100b100150840080d054a0461ba0300c4402d01711513034001a526125500001448009907150482c00c2030303150420000d85000e000188261402000c0c1d61401400c0729 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 12341472 1250 12340222 12340271
    0x4030209041109070f0903061a090115080a0c080f0a0f0e0102030a0c020c0108010e0601031506030209030706030b01020c0108090a0f080307030b010f080a090302010e0313050f03010501030f0f0f0213 87
    0x1203600c0b21700d101c03103a20980d900c2c00c8079440030000c17411035045e4220401c206142002c0c503130014180030001400c02c0d068400080c540245464107900e07500c44208200544680e110785801007441c283c0840d00020302c0702c3e844c42d8840d0300c8040020310006130030320301000d6030301d41c50030340c0001d81d004030510900180c1441403200d08522230004000c80b401c3c000020780780800500c58606944442c40000e6040d9000f50410b8407a6000054400c3c006030302c6950240003500040f1100d8040d1045074804107945010740f0a0040d1128140c0007424802e035106d004503a00381d03000340703044080d000d809541c80014152050001d401da100e04500f680341d1504142c010101e1780c0e0010081d04104100c00320f00d8000e5004074000e500f04880b0800418880c800c0d060583c050505194003401a200c00034106805142c0501744400b61201203900502a241c00000c15081c1d6100f0b000141c00e1500158042d400590801b00c1098110b10501750356403092020b0700050b0720354030185198800d254890300c120f1002d0100550316643d5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 12342722 1250 12341472 12341477
    0x90209060603090a0807081218060f01180c0e0a03050303010e0c04120201110a1209260c011110050708150d030e010e0a030c0306020c16080c0d06020403020904110907 73
    0x2945400c0c03c8541da203611200024104c0e92000541e04144042d40e01101c2c880f81c00e85013642c1950419000801e00320780600c40009250164501140c1d0310000310184034100d507600380c082e01c0c041c80065007540017802489d549001380234204604c84d90a48030200300390004d5020380301a40d01c2e50705d011240c0707042c0c2030001c00c0400703a03003001c201c01d000d11081d021480b05d605070286000240c03030f551050010b10b07001c1005030213000618a10840100c0c19404801c4000340c1c0d1400215846501800085401344082e880051285802c50a506510b55104da403180c0d0129415004445a440032081010f0480300c00f0748031000041c080a0800411402c0c0b0350080c1941c181c00d6070070000a030000d8500038a1211692041810416010b149940c03d9035004c02c01806150800c406014142d03881c50800025071028040c90001c0c000d40061560605441c5000c0044601c10f2028103805d808403001c004011424074011224240c0c24040880582c5500c50014451480b5200360040c055010040000d80400145007804 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 12343972 1250 12342722 12342727
    0x24030a0b1f0b04030602070305040305010516020f0721020102071503050a0c0c050a02131104080a020301150b070b040614150901140f060306030304080d0507110105030709150306050301020a030902090606 89
    0x2000d00810b0440d4103c1360030901c01030f143c403194601106c880c030075640003a00ea0f41c03d02e000e000c0688401d402080310040c00d0f40840394031b51403480881c2e4072282e10707219038461030f0200b541c14050250103044030b2020358030500c1034408054680039280c901c00c1202c000c2800182e46c170000c12101122610401c4403121140c10100540409551419520007031084000e002c0d892a906000e407035503941c3c009005201000d0000d641781c40c0c0700d015065903203448a106034409e42c00e1040e848544040c42d80c1d01015154501c003001d00d00074880c0c44001c4800340140c4200d90050303680c0d043d101d405d40ca81d20800c0c06a000743c40d12566601d83c80303082005446041e003146824458041101650f681d80caa1100d50700201514140c1d2a0341d03071200001d046021380e60213440507000e070401d50000b8640c450002c05019100300300c0c001910f010325004442c02d0008498000c007181031000306100c071f500350710320b00c1800500e58580842d2441d1074002003030076604081a810013003500c40b2980c0703086191280c80c803640403500396526030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 12345222 1250 12343972 12343979
    0x50c030a0b01090b030703080313060b100806010815040606080601030c02010b032802030109030302030f0703060b030a0504020d121101060503011e090312020c030307120504020924030a0b1f 83
    0x10040350040c4100c18500b0b60b5903131014000d4805200c02c0300110b0b00a180180c0700d241c5075113111304841c0f0520301121420314000b140c42075450140c039203040d6103116545000b05a0b42c1c81e001503e280c00003a200f444200c9042910104955a5009130340280070319907564121418007500140596640e9094a410359040111200c2d0b2074500042504149424848045010844004095803040c442002075010350801010310300b8144c064004600407100c540a52080d135079105400c5080710420f000d81041ca0300100085001202c0750b8108a400500040990b0002d044668035070100c00030510840c40030444030900c100c0701980a01c108001032005070000e1001c3c07002c91030b10102c0e6040c1406003949003943d83c10b034501814860b441a890080000c0002c541d103803094a1495601d8000315006400609024154071220405005240c06154058441e04040d02c0b00094104892902c02c90860000d80d03040c013011255401700072090b0707254000c01810450b07003840c059802d850044d100c0d4081c85109100800c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 12346472 1250 12345222 12345233
    0x2041404050603010c1d0112020c010510170a020402030a0e030d090605060d1a041b0807030c060c08120408090d06020702041803020307150204050604060201020306030106140303040308090301020d0903020604050c030a 95
    0x4110b06c1001c1c48406045414050040e2881c00c0c0381b0301000f417030610108207900c401c5d04c15403140c0d01808904103400b11044d070700c10100c000141c0c107242c0307081c8640120884030010b0070f103a009142c04c80200034000c6000b2030410407451a40d044811a0048541c0340c1684905201d52807081d10780181e010f4496034070100c139a4032a00d80d0250307412840340c045407140d4005001c0c08008a00e01c8403115000316150000c943d10700c021a600c8002c0e00054076140b895030000540c031401022113108242d0700c841c055082c40c11110b03440ca0702007030040081c0c3e5800010080c2001a60301c6508104440d80705800050b100c00700790060000711111201e109016094500407640031940010070303a0080b581c08000b072115940c245034134001a01890744010b07048500494082502c0360107402652041341c06600030001e0b00e17034603803a016440d80d980071080d406030000c010038004206204010030b50070344090009841c0c24002030081003164074110b020790058004a003030008015042c04841c1000c5000c80091002c2c49254861 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 12347722 1250 12346472 12346487
    0x60105060a180911030106141c090606030c171203040305030f0717040602040806130c0504020a05090a030f0201120203070906110a0b0423031201090203040f050102041404050603010c 80
    0x144000d105401d0751110541c01d80c42d032440081c00d0002030030710210002d00c0d59042c50390400c0c0030701000701750b01440c0f0306014603001d425600c401961030034503a802e0019a4015004054100c1c0c00d5414540300c002c080013203014a00040020b00e04611403002c0280090551b50420000100940203448100280b0000c650b0140c00d607900a03070312110420140d152074005440840b010b078881c4d0105a902d07420002480020f9000e0800c58000c60240d4100fa41c8a442400048903540c00090901d42c0c480030522503400c0690142c03030004428209145400402c03070000d40402243d600031140b1808071400c2c801156402890110300141c0d0103015415410b094101804001440c000c40040040195002080107000c00c1050f04540c1c2007048403c203403c2a041611109030040c4100014000b008000c81c03158500004486040b03540111000d2180d0a240d0068065070020f04107032803031010201c4a60105000f84010401410210070030845860802c0602c410b45d000182054466490001c082c04100e40103040e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 12348972 1250 12347722 12347737
    0x30f03030f130f030f0e0405060102060a0f0b0409060605030c09070e0906060f0703020d02070609050a140102070513020307020601120b04060b060c030706060f0b070515071403040b0703060806010506 87
    0x2408005640301401c81d10752294001001c1e042e424008018014540c02c81000038403103c51b035071108118601003007440152403003640c000e40103030b108000103030f5110303020b9005846101800e0320205000400350002010380740490380581d4103a0b5246010400c40c81d0401035a403c0e280155140e156900c5c000c3c01c00b5100d17411103040070b4000c0101c540081d00c80c0d41c0b0281211503082100c414503488003040d040082d0340b610704440340c001522a200e0b011803580d00404050b000c6541c0106040b40a50030104d40380d12200216908034194071030400086111340da25450742010700c0d100000140c4a00d40100c0080c540301040e4402c05065004401d100c0100d010306109caa40503030440c83c041a02a0480049003851144c110780081500020800e0402c011058000b40d04a5a40f00340c41d1401c41c2d182d420540c942cac82441c000615903400441e00380d141000e0408000e61085003402c4c0390940030407024045600d45c1c81110202c0700081648204103600c1d07094030a00700a00800c0006105543c1007401203221882400c4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 12350222 1250 12348972 12348991
    0xa03020709060e10150203120406150501020106080a080c1e0a050601050a1d0402010e0a090606020609010c05190909020403111c030203040501050f0c0a03020607140702010e090408070b090f010605030f0303 90
    0x11950418179008004450303458a105482402a00c0d150428400400601d60400c103c941c0c540000100c540c4140203000603a4480701c0a481044031039500d0b0300d20b0358010300d802a042c0c050118a81c54100010083d021107807189006006014614542a420044140c000a110f1a202801404030001c3d038219a0786480a00900703070000c0e2683d00069503030000d00c3e049150720030003104010036038442c19040201225020b030211040c580790041814240d5031072801c5000001c1080c809482d40c620605c2c03810080303542c10700746600015103d10840069038030a030000d4803d201c60548440c0303a130500d1400648024140c2c00821040881d0f0f96000352244114802c0c141040000303e0000c207041031440460701c042d41000c0850b4902d1209280180d1210800c80e030103008101000345040d00d00002c10122040a64142c0d2176071415480c0c0700c104076040708083c0c000e50f841030050164100260200c400c00e070141403d80005d103140c103001e810040c2503442c40d410450081d000b1410040d00040c1c00015030750010f0014 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 12351472 1250 12350222 12350249
    0x60708070e03010c0e0406080703020f0d080705010207051e0f1b010306090e0609010506090c040303030507051603022503050606091e131104020906070f02060c0a03020709060e10 78
    0x380801c4810214801d0a00e906510b0301e6030800107943c00000c4030300c0f01c0a05031000c0c0401c0f952000003035256078907440040d410600459024900d0700d04070040301c0c4914450507501d13081000540380c20782260402e00007101c3c1e66002044402032001d20b8401500d520070404000c00012051101554903101d40b9444208a0719541d8030307088551f8040c1c2c01c2040600480c210070040b903010350f540e80d541e810041d140d000c519403a20f0003141c2d181c2888640c1e103108420a0000c03c0c40e051565030110f00400004002c1710411200380000c003103005050f120726003e280694001d09248001e801505000400b80311a000110006882080098000710f13009600c01c4040341c1042c0030380d07070300014400030110a080d05841001d0300410050040790140070040c105001d4064a0002c082410034003040b4401d40034000e9000c10f0074010500082d0050804000c2140701070041400e01900328400c0d0305d80364074061f0460168002030018445802e10388615801004070308115401428442c803000c680071068003d000511244 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 12352722 1250 12351472 12351481
    0x60a080402040b190906120c030b0a060f08060601020706081003170705030a020f0c06070b13021f090501080a02040509040b100803030c07030e0307030201052208060103050102030702100905060708 86
    0xc903400b100381840d001d040128407084828194240000301c0c01200740e0301e4a0a1b0011030305010607090340380d44035441440c4071851070650b01c2d0645030010040001480da52266004510300103400c81c440014114040240b131641880c500280c1400810381090741006214000c00201c030050403241d10440c0d4200a41007410400d220000344c00703104000c8003400314480046c400c030500b90b00080300c0b01c18143c0310003038404110386401086205d21034081c2c00342100d80d461001c240c0051809240002039407000b4001c0c0340c28491000d001d4520100d440d0b210010988144c400c04c21945c002c24441c0d07009918013411440c050610001a400100c00703400989110244c80001c2c1e44280b00c003400307202070f0005200300d0341c4a2510003520703c0325600507071088000600701c203e0007525040014442042d6075050b12070600346868507203000d0155200d5010381210a901183c0094611010300605020f18010381c005aa40e00d094407010386000055419400444d03d40103444001c03070008610150094454500704a26869 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 12353972 1250 12352722 12352729
    0x41406090a0b03010e030a0f0801060804030c0b090c040f0204180908041403030c060a060f06020318040506010e04050a0c030b0d03050301030b060103020405180a0e03120112020a150306080c0f060a080402 89
    0x81c81c817100100b44800101a00c455070011001405d1a000740d4510074160380f118805ca40c840307401e40e002008549602012000030355038028680d8060b031450211040002441d0000d0281ca044c0c4103e840c03101d90004050204148009442c0514200080c0900401d4026541c41c4103912403881280d403405c038407906040042d0303014000c4400d41d40180c0c0490f00c06081c035880e020028426489055420182442c00040450020060701c2454003a5001200a01c85210520010f810002c12140c108140080090501d5480f40700e1540a00201100003400e8010a000941141d8401503407900c1081070100c02d40009034003100301c80c150f03503006c2d640390180d03210070380181c0c0603025503000b07a0b0344a9261071030003144000b5002c82e00c0c0300f54a10340e024003000c16034415482e124441d90403004d82c7c1c1c0300c45034010320007607200350104451144050301100280307988861002d144450100c031031000a072100740410442d0783c00c00400311400d100f151240c421012580000301d8074450a00700300705100c403800c0064150355 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 12355222 1250 12353972 12353981
    0x10e0a0204090f0c030b0106020705010c02030d08041e030503090c0303070b04060f060909050a0b0f010602120c21040303030b0405060603040f11040c02010903030e010e0d110f0307060209041406090a0b0301 90
    0x3e61104d6440d0a1070348a103884401805e0034003620300144150500000d42c0d6100340061810a0340240250540511050081381c1e9460001d200703454440380d468203884140364400302500b10f107000e50303107031501d07400c2c0b1000b21801d121000d65114443d0b40180002004030f41c68112080d001a40804e00060241d0780000d124013611040d8403145800d4a0402ca0000380100031a00c040140e100d4220740c500c035a03508512080c10381080c090000141e001c51a0300daa84502c0034000c10280500c0c5c41120308400481501c920442030044403001901004101001010380600a0308802c000841e4140102d2400d440410b40354040188064410702c2000401400d001540d030030301c00558009002888540c02d00b103000780c040c00c0105812400a8900200110072000c107104a01c605c498100c061f000c10296030701d084485101070048801540a12030000e14820810401412010301c15803000d40c88607400c100700403c94425070501d10802921000f00f03c2141d603008041c0d6441242d81c5800911880404042130040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 12356472 1250 12355222 12355253
    0x291807090c0c03030507031a060f07020d03030b120d02100203060105120406020406090e100b0903030c010905070315020306010210020d02040905040606050a080f03070b07030908030f0a050702010e0a020409 90
    0x41e00d4086440074003a880485080c86500070b0b142071002d40c4078102d0440c21900c602c0082c0491520400301050a40380184c01001f6503031451034014104017041d000140b0088001e0009c40200703503101c240c0380403802c041d18030030117140188000d0314400354001c2001e52070f001d1402e40c6000b070b030340c0c000001103150f0302507402d032062488454200c40e041d15062800e40000e5000d402102e000ca00c144070000f4030403400c030400724480d556140d0300c80c0a240c6862005075017504103801c0340b941400280050742640c0d000f4811054414001c03002009030516505140b180d0100040002c0602401081005281d0740c002998160001242c00d0040c0e580d8030082d0361200034002c44c0c000e1074001d8103200034401404125041030781948c800311100c00c0a02d90701c00c0d20782c1e40c60450079104486a0001e21101000c9602e0300c0d42568080d21900740030814580558480c410b41c3c0c003c60f1140003400c0481c043c0606e6130b000d845003c0e44003916000801405008100e100d42d50100789034000d1040d9260b8041760b0800500c0460050070 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 12357722 1250 12356472 12356489
    0x40c03061a0108060a0b0f030601090e0403020a060f0506010e010e010212040e01080c0a0f03030503040501060e0702010213170705040207050f010203090307110406060804020405070201110a0507291807 88
    0x341018007440c070005008200e040ca00091200c030115081d86410410b038070445403140b014914004516040202c1a000104000d041c018402030014652a0030003900388103900c80e50140441c1e0880d89058001c940d1032585c08040b0070b2403e410008540d81000750312042203400d00304081d01012800040703190000e03000c189400250040780c001480041c10300704074180c2d82100182c0d0031480c0d01c034060011120040c810f002c55240745420400c0843c0c003510003590440d000b10000308905465442a4000d944181d40c07500c0142e500107051005c005a00b64148050300c0d9054200c0c403145a00217900b0741c0e524850050501c00e590000b4100100f010411166114241f000002c0d0b44034030740100d440b5100c0d0400c0354143c03464105900039181915041c030448060f100280c9031031509442d150203205c014070005025505566842643c0300b01d4445a20141441400b40d64a0f0b0b983c6080c6803820f0030303c1c03d051200007441030302d449490907607810307441340d410f9444940c28048800203280f01e1903907458180503a001c03159 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 12358972 1250 12357722 12357731
    0x1d0f010b0f0421050d020a0209160e06030709030605010e1911040603021605070803090111030903060a090204020d06140f06120402040c0c14070f0501110a060c03060b030c0c0106080f0a030305040c0306 88
    0x100c5c1c1d000f1510161146c021150180c0b169174200000480000c4812050006100020060b003149000000303550803a582d4540402c16948960f541005c80d0000e0300480c4c042c50520b010041c503442195801c0002802100c410320201f00c0d100002074141c095802660141500407907240d107007202d5031183c049150741003c1120303183c035550700c08030351203500ca01300071030014a500030b2405402d4400801c8840d4118058010001a62405024001460005003c03603000707400b00940f2121410a000d0341d00584000010504450346240400c104011444c400500422042c0141c3c07412a07040700200d580181c0581c0c01042e8980c1900c012600c05181c26001080701d107071840440025000002c0300f0702904c00c603c178030a0442d40c0b5480151440500109013100c141c1c018481000002c040350880a071130200c40c1400300360540c440e1040d0901e600101c0d54405c80e1400441c1d20925032909010b500001d084c4100600169a00300345055240d040816025040c907884801040400240303080000055412240410 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 12360222 1250 12358972 12358993
    0x131a15030703080405010305090f06040809060c1501060f020a020901030f020303070209070c0302060615030403030c03020d020c03120a050601090e040c170102030405070b0306061803071d0f010b0f042105 89
    0x64030f81080c01017a000a14002c00145a4a000208002c0c020f40c080300904141d500d940d5504026481080c00b250421005e2050100c070480805c8000444081514141c1c403c0d8100b42000b41210042c220280c01c41d0300071a4410056228209014103480e04200190461404d43c00840d20794468540000d420400c110100300074242e001a0b4106024403c1d801e45425403602c0040280300002442c00500c120b004002140000340254040d00e15060b45090260511f8000c44502e4101d800404040420707400026400ca1a1200c60b106e05500c941c450a0401040c20300d200020040d41c140c5c010b026012107190301080601100454041c0200601042c4400940c0c100ba03a2034040e400640703003180c0134132030900041150300b4103006030b074410940642030700d041507281e0201d9102081c281d80c803640c0602442c480850096120740d4203104240c400701c80c9040f503080c204411130400105900081031004148907498900203244200c0b412201c0b0707502100961070104803445040d07056500028001d124080c5440c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 12361472 1250 12360222 12360233
    0x30c0a050a060b060304020a0e180d0e040f0501060525050a0303140601020d0e060a030605060412030f0509150a02190506060103180b01060c030c08040e0a05131a15030703 75
    0x34181e14407401060104000301da007030040c4c901007918025400b203100b18050007041d55234010294400c2c0f201e080c195012104a540a007001c5240c0b11050018005406107041803c16000b0038015110b0807104010075850180c0003082409a14561103003004178502800c1e8640301c09500003103094006054130b000403810701e0003070010314040c0080c00c2410352440000f1565030004c2013140060300385072214113600050504224560303103d83c004c88181940d480f00492140ca03014050400b40c2012541c03460441d5503400c002e41032462700c170729070000c01804000115941d100c4039020034504d2401980f882c1c8500c4050000d81c24200700b00e0803003000c421014144010b0020004441c0e00592081e00c081040d4028550003966070328405901500d444804001005620310805c0d1403802c240c080d03d04042601090fa4400c4010340c020303441088012219401e00607100c0681c451141c0080501d480c80c240d441155845012011143d0328518000f01841c0004211911b100312a80304480001c0c1601d000720b4691070301 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 12362722 1250 12361472 12361483
    0xc03070c09020901140901020604080306030a080c01090c05090c07020405040311010207030906030e0102040b030610020304030506040309050901050108060d03120608030c03030103060b0108010503030711030a021c0b10060f0e03030c0a05 103
    0xa044c0040d000450a500400b282c0c8100c904024060303001e055140d580c0d07119003500c0e52014080782c3c1c0510880c005603001c1510180640002c01501c000070840300103074104407540704100e0300310611481c900c01c14041168401011503400070b40c1038602207015903440c10b003960050300400780b0050030b500029840c801c040c1e06c000280161203c507141080000060700c1c0c00360803401240070300f08128404001190f202e2030150300a840034001031044074a0f190322640c0c0c41c1e00f06401030f02c048001c203040003000e001514100c0e0885025190a2802c40818540200001d1100c450b40002505110310300300749a080c0030440e001100035000201c201c0307a587c202d00000503034030380c024441903604600e082030000752584a6110207040b40e00040003541441d030140c46440706410011000d591500c90f0581d4079005807981200308094807166a034070800d503901400c010741100c00080c0340b0002020b100f0400c1c408640c0141c80001a04410b10b040d0802100c7c0e400841c0c51481040c2d103c84035841500080700803c0f80c0041c0303 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 12363972 1250 12362722 12362737
    0x1060503090f010516030b06090402071a010503010c080705070302071707090f020a0207061b020409060506010809010e06150102160306060501021603080901080a020904060602010b0f0901030b010501050c03070c0902 94
    0x1100c400301d242e01d8000303088520584040440d448001103581d1101c3c4207400c8544605402429549400712800001e4105d031711451003103c010f06c0c140c000e807400070500d040a500402c4190300070302040036010001007000320010041d1082c064082055001c0c18420049803000d084080e1501aa0380f58158100342d554400c1c2c458100410306141541c1e181001d41e009480c01410036400401045041a20544107400b07280c52106840c9020307603040c0b01503902c6000c7c142c0c07d24024103000600303003032020004082850080400710180e05152403000d007540005041c59111011040515100f006040100d06219004c0c0c0210b80007001661b011081c0700007944550700700c4000741c00316a554440ba944540d81d9400710b10010b02414002d100034402c035400303211001ea12084040d001480c2c41d40b000c0c001000c0300e056401100060390340305141d1680d800c1c11740581100e603404844100c801c3d8559560203c5407801405014100440410041d080710020829101001d50060071114000d40301e038001d1009410808 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 12365222 1250 12363972 12363991
    0x905010f1b02010605030a12020f06070c0c050108040c0308030601050405090c090f0a060507030503060d02030d08040203010518030f090117040f02030706030203220206041707091406030604171201060503 89
    0x72540001c031401480340300c08982000e8040e180303421050710b0704601c1210300312a10056000d180000c01100005014113803043c00c00d625098400103440c2041903002c20f090308020306010065040c880465203031600901100e40c409021944c030340d01c60004071224059580101c0c1c0003480d070780c240480d015483c0094001310b00103075070980a200c0322100300024010107124040114800301710400109214100460b44a600600380c1181044598046440d009081c056103001520340420b202c110316081c0141500f14034141c200c1050f58000322a415200e1044589a01c0c050702e00192070011640100f1862186805c1007069a03110300c0c2c0b60510105014403d00102d03c40e014a08010407458068400c0d240200c800c4001c001a201c0099003010110504140a981c40700c400e1200141d0a9944120300d40d2003102c800240440b03601d480c460b9400ea030907440072a1106191142040340c0c54400080c8180d01a400840d40100044040f088041c2d6101d2012480501d000217000462055088070040d8094058034 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 12366472 1250 12365222 12365261
    0xf0a1203030603050d08010e070318081207080c19050304050c09040b040501050a0207200a0305030309011a03010603080901050d0609050c071202060403020606010e0a0801050906060a0801020405030709020d0905010f 94
    0xb12041b00c0c46c079000d00540310811707096404100e1081c8039a00c510001f4507100104090341129454070790b400c0e00030140340305e00050260200980240e200b49001d42100c2c8021605050034000301803080041c078035001000401401000180030310004028141c403640002c1c2101901d418607003000c1d50b0070301d0100c030199001c1d802c2c1000f046900189101321901d050b0040f22804801c5a0100d60429001e044684541c0c441e01120020000c030f030381480114010b440c0c0c0400000d2844a002168000c41080c500c441d01c0380e4036010301000170034854000c4a0841400b403820660b43c520102c43d0200a20454103c5200750785070104100101399540000c040040c000c00c841d00c20780048400c2265590b1b0100c60050040e04000f000c240b095006030620010800020010007540f5240d1304914211841113500d42813550151043c0a114185907842c8400340050070001c2d4903041c10000840c3d03540e800380c480c0e241a1a030000b580700355541a61b00c03c40c10141e0000003400b41c5401a140c01001e071070101d20f0a201d501c040b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 12367722 1250 12366472 12366493
    0x603020a080607080103020d030314070201061a0304020907031104230103050c03101a0904090605060906100509010513050405150a080703020a0e070302040815091e030304020f0a120303060305 84
    0x30070038401d43c40d036a82c1a4103a821075080c031020f0300c000c0c80d04509050b00c8034900380d03842603801c505502c12420f507800014424902408000003142c00d031410710801c40100240405a200e0461581e840441400e01081c080302070241e80055106a52214018503241255080d1000131500c141c803c01200360307070902207615003100c0c24480d888141c80e10940003210320410070002010031280351401c00104851800c11807528046003e03146102821607105546400300509440c01d250602c1e0012800c0d58000c1c010805401c014003140300344480c07581840404585440c688821490000107031102900c103222604001050401c0d244d8280c546511901d4101d0022410b03440c00610385048070703002003002c59032a28000b911400208068000710425808020110307031018100411b080c00702c458100f6044a03e032000401e802c1c0700180f41c00d825003402c1c00c620294044c5001040c0d94100760110350066221085c02c00080500303519512881a01d605910401c06046d015401380301241d002c0c40a840d9403580 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 12368972 1250 12367722 12367739
    0x30403020a050708010c03140c07030c020301020904020c01090c1e060e031009060b040501140d020108060604030501020703090303030c0e09010e060d050d020f0f061003030809010b0402040905040201180b040603020a05040506070302010603020a 106
    0x444154410f001e0038012140881c1c40cc900d075212460000c0d0005140803c00710115059a00c030340b401070f8a5a45035041d100400c41c0d14032881000f0460b0081d403d2401c2400c804049000343e851103180100b014010241c0c9542d039050100c1c1e445441d41d21020040c01d0503600d8090090090340c1c8a075803055250400010341001103a82003600b41c14001c1c6150b10000c1e03079900549003403034090203c80e00440300340008170010b07500344001c0c003e150203a280c400c000c51a500d0024142c400091082c000c101c030756083c2c08196203495045c54103440403c0a008041e07500c080200d202000341560142c680c1c41b0716070b4840a019000b0600c50219682c00046d41c21078030312008456603418041d9029100703d85401c03410004603204008080d080a041d40000c80c1c2c0d14001e40c0002d041e60056041559299510b00a001c215070304040f203081c0300219090003002903031410680000a0040c0c2c403611051580000d200c1d070350103109500320f4001d408020181620b030714003401c009000f0140c42c00704a00071000403201250007031 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 12370222 1250 12368972 12369011
    0xa0e07050d0c1d0a05091618080102040e01090e120705010b100801050a09060b030c13150315082103060d020a080601032609010f120207030c05010b0105040503030708030403020a050708010c03 84
    0x100050042c600e01d80b0340e0390ba000c9006d090100091308000003075841b60b2300103140b0800380b401841450b0001d601d0301d08041403501010f0060744440380003868103605207070071180030800f050303603060300c0400390388aa119080217405004038040984d0700400301540f0b498039603080780c1c1550507107400781ca200c0c04c00f0380c840859100f01e54080c009c0310050407042c4000b5159440130b83c020006100c0f0601c5140902c0d0340d500004680e24031030000c90703000c00e45810f00b9003245014201d080d8010300000000788110903610090003c04400d481440581c4079002000805d291120750028001030380c06400e480340550348455454542c9800e00045401041c00c250394075220006043c00c1000056101526241044400041d50317180d030603001201c14041403080c41c800040651028045550003921101c004550515116013100d2402420074140403040c0030500a1341c40003c1170b1610f556201403055a02d07104c6080681c03410016040040c1030784200c0c04045486001074200e1003506480b500c0502124004200c01180344 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 12371472 1250 12370222 12370229
    0x1030b0108030c0a060917040306020c06240405041e080702032506050904060906091b0201020f0d05060604030209070507030206070801050108070302180a0f0602100603020a0e07050d0c1d0a 83
    0xe074031944c1081e000c241d181d4040c5c0c208a100e040c0c48150740990b10290403168026a0042e40c0b02540801c1810b11120180301956102d02e44040c10000d1040707a241d414100c0380303a5040301e40150b6460002404100600d07141850203805800c016040082e40c4c038200340541d10441b01203000307020f000c90b180342171505a4203140754215401c2c00b0001203401d020b804c441310f4002d181100c1d0b00a41b10940081c5815041c842c0c04060f015074070700440c49154090482c01c4100c07109150f0303021680704201040c41c0403e0102541c84440204c00017003042e89554000840600807504040d6001c42141c081c044000e42050081c90f200b4400e80940f90542d444420544001c6424410140411401000524040d10941c002d00c100c1c0d104d007a0384110385400002040060b030080e0010101c00c2140b403c2401040e4040020b8600224011800d01070107040d64041407007518070b4031827010820044800b0880300d030300030020f440c1491891103041154048051005001d854000e1001d42104c81c0f50400070901d090415500054 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 12372722 1250 12371472 12371497
    0x408100209101b0813060e0a06020c0f04020d0e030703120504110918011a01020f0303160f020f060403031a0301140708100503070e040302010615020a03050702220501030b010803 78
    0x3890b5002002e0398094070450644209095940d041c030005002040503100c0d000d040c50015414605210b4098021079030300d09258401c0a50302e00820185500003250441c002054654020074014030380410043d00410b00161000740c289102c0ca94001400000703070090500a0382d4a00e0b083c0c0c103400361441211820346015200440c0b03092540c1d12420820911604103290642c6541c0480c0e00da078080e82100c04e0072840c1031580c2480014020b266a04010007890000044013451a5040c400c80d104541e00c950081e02d42806404040344d00120700901c030300e44d0401903032001c1d1901c0f854980b400030000c1ca182507640d0382080c000d68812100742814810300090800d00e0032802900d45a4940036202400d00400030909842c0b64040481c0035102030240300e00038021080c0f101c46500f041d15000c0e007558203540080b20401d64407201d10310079039400224500513981500308981d0303c84450001c6042003220019244c195201c030303031038240c06104651019040340d009488103d0b4507600c84010079140d2117802200202c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 12373972 1250 12372722 12372739
    0xb0702011407060203070305071e080411010315090b040c0503040803130204020d0903050316080c19090e04050c0907020318061812030406030c02030301030308010b0a0e150408100209 80
    0x550148806a0001c1a69801d090401d1082e0303441509a80c0304840b210000f82c0c4580a1280403034100614440801101e1040040340f5502275004014400040000d001c480c40112243c52030f9000390701c165040066000540c3c1c90945440d0340c000903000d090f9045024518000d03240102c40e11403001d8034029a44001e1580c50360304d650900e0000103e00b03000507a4000d500700f0048001d81c1551250107041c921036100e03240c0701d24040404040440c949002c05003802840000c00001000d40d00c1280e15041001c5c903012002c40e4504821501c000186e085146030616010900040c03100008034410361180c12a10500280d8400d8012600c0c0d004202c0565815040307101240880c1c030b44000a024680c0b484c0301d0f40407031050400009105840705048184507600001014800141d240c01541d83d02035450005610755455a41c0082034104c05116006556402090306180203106580c0b82c1c0e181500107040780e140c10300c0c005032074410b035100e8464414681700704011380044004500a503500848010140030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 12375222 1250 12373972 12373987
    0xb0703091509152f0406020304060c060f1a030123060d0201020c0603040f0510020304020d030507020d120f0f140702040b010210060b04031202010b0906120a0206030a02030a0507090b 80
    0x10142c028514200ca104848079103008614480340301c0d195521254290102c55690b04d100c1039541c880152120f80390340641008180403564001085500321382c2c0620b8030415490603414070400408683c1005426181004084101180701c14a03441d00c10400320f00070082509181040d4400d508213002e81d014401a80f00003a02c00d00c2d010160100c0c0c1401030040d10744910207080051aa0740c0215402c0356204d41c1600c000c824401d080003c025007400c854030861450500e41c000420101a000000b410403800040b800215103c460383c0c0c001301e40d0b0007441c05c407603001610030140c0380310001c107070b04000a8516401850400d101d01911724100303100d5000c25180110b80d8003800054015410340d82d043d4030407400c20810030051446250010640340e07094036100d90451800350383c5040e01c1030002c021a030401e0103c01d0b882c0d403030f42c0c40076401c440d08484050722040040b0344241021400b2a0195100001100708005020243c004520034034002c10b00300695601c2d40c909030344c0e403101401801c104400a00071070 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 12376472 1250 12375222 12375263
    0xf09020a0b0f0705060f0702010b010804080306040b13020c0c011206030309120615090c02070501030207031d03190f050705030303040b04061509020406170105040b060a0c0602091c0b070309 83
    0x14501542000c003150b20f400c0c5141c54a5103080001c0c0c2e800b80b5096200020405aa9130a201c2d00aa1100c2441e041c0028240340d100c0170035a00010700628480c03175450004000d56034844051100c0c1400d003503030035515400110b10858a55100a040c01c2c0410340b00c0c02c448601c6001f0344191410759600d0b031035207103000d410511841c8030036110400884078140e6504000100306c02c08042e031001400300c043d000c180c0e00781d44c60b03000741840900d62081e414140140a81310009400200500388643e000501c4802c1c00303460000a8501003100300c0c909000c61894040c0703400c2c821203070019141c040c0940c0480724155990b00c01d160f0349210880f0007410004800001c180011650340000000c00e043d0f000c1079112a03280d11502c0101d80c040d90010b8085040c0558944192140d41e003c280140012a0100142807110001c110203104007002c072004c01408079504420400a613040d60700d01d0304081e020541c8650f00c130b000a507444a4510f01502c070360710441c0005d6440d40c840e00801c0d0000e941300f86140f0640c901a10030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 12377722 1250 12376472 12376477
    0x12030302090a120c0f210809031606030204030203070e0408070206030a0608030307090311010801060e010f030906020304060e1504030507110d150203071206051503040201200c01030f09020a0b 84
    0x200d0b488201801d0010380d02e10325011084095016016515005180008060100f07000d40c0c486600c28400c0711711005a074036030412200c0c20030340103080a83d0300e40b640e20019060500d02c006000344c01800c1c04000c5010b60f85503000e0702c1520b10940c03c44034200d45612040448100458004081c0341082103c0c100604000300030710742160b507901022070386d5512100034900b5500202d45200005d90446030810030300c2180f1045044110082c03c19510703139410180014000c4003095042814452500e081410907442030707000c0c1c0c08298000104540b40c0c18245003000c00f80c40c03120704111961140910b000310300604c0303030003103406941e06480d59494825640e0f99002c0342c06004404560000c8018080c4011510520060404241c00329005036240b425440c054090f600d50700000103c61724210060007140c40300e100c084424160882100d46039622032004a8403019100b25460608055a140109038800000c0e9103010b0002601d0522424142035500070031103860400196000030300360340400c9030200c078200 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 12378972 1250 12377722 12377737
    0x6020706030b03070b281d0405040c05060307020c0607060204080c01080c040e060f0904030201060f0b0403051b040b060f03040605150d020103050a020c0d0c050c0303070b010b0906120a02071a0112030302 89
    0x10815414400010141952441d601c6d800b046401c02503964401d0103c060800c0b01204441c1005582010707118043e52410354002d083c0a020b000010079201c60007001300c01d2005030000c002a0b0789283d00c0c40e26101079003182c03042c03604901c40e164000c1140e60180da10640329208034040b640c205403810400030007988000e441c0d250458050001044c081c1c176106103480c0b180340207400100310240f4000e204202011190b2040d50320070700034001840081c00c0820310400d61110824910b110001020001d070040c01c00418149e4090400503400240b820500080d40c82280550001c019a0352041c0780201100c5407455103540c801880c10205005600030b5100c01e800900b242c400500f0403495060301482d0840000303000300441c0503001d20008000d03080181448400301070300618145081075950715801c1e401800f0f80340e140381011640c0406031312251b081d107070030321031100012100c0d00b81100b46000035480082c00f500c1901c443d90008900600400c1a03070f04031402c908820b508110642c40031402134200c4070 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 12380222 1250 12378972 12378997
    0x604080d09020406030605060f010203030118050405070b03010303080106030f0504150207030207050603010f170c0f12030c060a060806070e030c1512040303020405010206091605060d02070c0f06020706030b03070b 93
    0x1c64030241c1c880e4402d110117903114040001d1a81007039003c003d0203080621205045520400051000282c18414840205600000410561154540103040ca441c58008903c0420088000030503d58480c4100e412108a40c40400400b100244040240c0f00200c4002d0458013a98075001610380c9182e0043c18502e020b48159111281c9a20008030703903600030f9222013402207400c9818070000750400b03102d41c113421000d4020705500008a011680302c2b105070107118803844500030300701c030a10014070443d5500b110200c1650000e14185503648002e04c558003403c0f090344282d00004074041d0140107004129a0000d0003428098181000c102c400103525909014240041c440c400d0980d00305807000d03025a110752409a1247d0404000915040e40140002a04c1d4012191410341c020020300c000144d03041910900e68580030000140040d11070650010309000d10860001420100c035441081510015030a0702c50143c2d072444100c05446074040354a60640243c00100301704c2c95160014114015810b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 12381472 1250 12380222 12380231
    0x1403070509090408090f030303060a03022e021b011b140307060204030614071706010302160b0405060603071505040b0304050705030303070e01030f020403030206130201020f1f0f06080604080d 84
    0x50101d0450310b015602290100000b007180c107001e141001c0c000c43d030070006078020340c1940341c4540096480145844007034080c11041e0030018024180f820102782211001c02040030320b040c0860000d42c0c802d11005031200301c81070650000718562054003175806c0040c01c2f40c40c0d0207501403181c480751806107035001c1c02202807108002c1503000680c3c0340082c00c02107001d034100144280304c100700c00d10810801441078040159801d181e91174079082940d0a60005c1c4207282c01a2220340d100c520f041010031801c0084c0c2030030148400c110403c40001401485201b0950944040f140e0b2040040e031440c8501941f44003044040c0424406c3c0c000a00186034082d0040e803c4a2540f65658007103400d5034000e842c0100080c0324004112440d5806002d41900000344500451400e0702c0c584000351a000080c04010b08044100e05000a680c4200000c80354560001b0690f5140100c0410512030903071002d280b5040c031342c206043c540010840c0c3c4116402c5502903c09030601e50707251344d00c022080d03000c071107901700c0c0d2547c4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 12382722 1250 12381472 12381487
    0x9080a030b01110708010905060105010201150b0309010b0d050a110402030603030a14070c06050a0306051c030804030306080f01020901080f0405060606030a0e100207020102150403050d0b0604181506020d14030705 93
    0x1300b001d84000c0c1008030001902100c5824241e0a003101604418150383c106081941c0034141d030100d80040300c140d0381c10b442c3c5a031900390450b070140c529421001d03401008559002c0520034042105050b09106074092900e0705c9143c0180816030000700c0b806541504184000c055031809101d4090080781d80d128868a82681640d81c614411810b41003800011004283e12103469050720410000d09011150b40e10000e901c0c816620100d28881d20080800c0040d02c04601018020b400c40406071585c5000d0781d4a0000c862015030003034120081c086e0019a03400d0103c0c41c4145d00840407030189400c44041c190566942061248581c130181506001503500c42290046c81f100340100a802c0b005080c0c0503a844070280002454414440c0003002d01e801e0a1040c000040d8100e4102c80040c1035611000c0750348001c0301c00280c03c1e0700070713a0f001411019044c03491100d001165488440031082d03030b00400e05c2c880d4660b4403c0341e90308020303c10180803d02c240000c1c0c000081c03150256a01611914100e49085507 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 12383972 1250 12382722 12382757
    0x314060d02010c0204020f09190b030a02180301060602010b0316050f010f11150106080109020a020d0807090b040b040f0807030302280212060108010f020a02033708100909080a030b01 80
    0x1d8503034120900c0c023140043d4a0729242c00d100e000008481102074006050038015086c62001401200c5a554005540c4070302c00ca40b1020b02115480083c020085c1d20b42d1104003902030404620310610a02548088411090382c01e0800001c3c0d0300044d00e100e400c0000c0728015a00100c002c0c0c0d460042c0040862142c41c0c1e000304102c1c0b05c0c7ca0704da440364038007542c1d45006005002c1c10010303002001d40c180144404a202a0f0000301032a20a11914149045454410302607079140c1c21900312000000c0d0010b8082441c3c504000107000701c0700400603c071011981c0c1d10840751265094040240181c21101191a920007541c07070b000b01510b89035150540c0040c15a00250781036245030310076803040d0401b60040003525070a00c207030b125041d4040c0055180006400b4001d461b03124505585866118845004800070002d02c2c082c400100c0910301c0c0201c4c02589070001c1d01c90032003110700d090b1850039040c0101700c00c04d040c0220b241c840e0b800464903090081c0c00c0780507805032020202d00c43c1085414645184102d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 12385222 1250 12383972 12383977
    0x15050609030102091f020c2704020a08011103150f0114090402120103030309050c01020309030a0803090a05010212010f0f0303050a0c15051305010b0f0a0e1005060a03020c06070314060d02010c020402 87
    0xda05d01c9441e0040050a01a0821207040d104a00c212403403001c01c1c0403c08044020b803042c41d02c020a0040703954580c4000b5a01081035048a48607600e0840c02c010241842001140100d071908113050807455040100310030307a0706003200c650002d0040c200d0074aa00008901a041c030500041016090590307440f11110071300c900764003e50000c0d0312500c095046c400280a04c1032404002c0c8041c3d450583c4d24808640c0d100302d81500103000d644000009040950107100202d84668400f000703541d220200211020340440a00541d0002c0c02501c400180d401460f82d01c25080780c2c0d16071202801c10821600c26503200010040644442200c5c0406003115a4648102d40c4914101d485045c00e050203401d11600711102040842d0045000c9040044942c2e1031a4200044a0080b1440001552362280700b0944640744d5004603003060f808240c00300c429425801030316540090b103040394090365692404409507045582c0e1421141d08000100e00c190802403101403c69006040c1640d0710903082d400320f4100d9 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 12386472 1250 12385222 12385249
    0x1511070809040b0406050604150302090301090c1d160807020a0c0303020721050c04020901021c0801030212010c0f0518090a020301050f0a0e060d0609080715050a1505060903010209 79
    0x422000800001c20302e4284110750f28440103490400c00b1a0810010a006120b940074022103005140b00c01d00c00144240c0403140c1c2c00310054001d0101c8041c40c50030f110950405c0c00384454540340106806001c2da44ac4402038810840707880c0e01c8100900c0303010113a5100c480600508110301070100c00002180c02c04403013100031031013a4004d101051a01c1e10406011a228085245900079240502c004c50000100780a46134001c40e00140d07074000d8100181c2c9000c1360400c901c404a8440c1c40304501103900130030500d048900940784280c2400b19104d10718221a05489803402040d0a6401e43d25450300c114083e000c1114420582070503081c492001a44800c811901c001d00d00380c000005001c1400c2508160f00c00001c00da4000c00000e04040781ca00c201d01c8010451030040101180e01c005100c084e80151000340d4015603a40da0395401400e0107141d0101142c1c07044603030360038140801e680195a115555441d8404451880300a06200401203254000e41810340d0540d02070140010b01c3da20b840360140711 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 12387722 1250 12386472 12386483
    0x503010c020c040e0106030c030228060302120f091c090807080a06060905010308220b18010305010f0506090105180405011805010803071104020a02100c090303170c07151107 76
    0xd0b00790000c00c2000f954600c0c411001c2c140d0400d202000003c10b1600a203066950403030702d40e41100c88030200184c4081107481e51030382500030f8031000134032542c05600425215500c695141120b607039400a14004050075a030346244d590251925200c82201c00d0611485043c203840e00d03840c8070350789041281c607240c899041907006801c049180000c0000798803c4900800c5a00414401507241d501d4041d8a40a040c5103101d503185080403285005911780300d410044e20b141e1403019250541400220414940c090405010078a820004031740716442c007408204407100200a40c2c50300e41188011200780d00084600846000d541031a4501961140a1603029100441032242c0c540340100518042e641d041e030040e5032070b0b0001c0120300d000c1000902c680b8030395107060310007503030341d9030144403c0b460006480b085025640ca0900003a010941c004405001c481c0a55104011140501d589041c8a0826500b80389000310400c40c8100003110303007070410800c152506000ad40d4103100d084a0803203900c640b03800ca40 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 12388972 1250 12387722 12387733
    0x2031305010e010c090e04080a050d0f0c0c02040f0e0c04020c0c030a0f0312020a0804021507060510050f06090603040605060a0f06020325030906031a0411190503090303010e07090503010c02 83
    0x440c55070190901004080504d000c3c6d025040544070207010788a002014410010002024040401c0c130790001010304041e0740c020000e0018200f00200a0b881400d0308034800c0d401d10303480304c4114500d40601e0303030b540c9541d0b80038000c0d080e00c3c0c03002c0200951016040b442c9500403500d04a0f00c039501808043d181c103000300885400c903134140c40c00524004410401c00c52251062090754403d5600c250300342d03071080c1d05540707444241d903030104018514040c049008103a5420181005080d401444016007200c4c0c0565000110490031403c000d041d0082d00384954220809000144c0032407403941003182c02102c003034510840710f9200e4803c1043e503a210b030400d00c0540d2001507100c1001d04041c10b070b4400291101100030703c0354004d50b00244060128420340003050f890700c0903611010690940c1e600c101d600140b04000742d559404540085c1d0f04440ca040040311a1140a103044d04e0180048a2194013104041e502e543e0910310794100c12440034040f0000c01c01c58920104a54600b403041380c1c0c034005503800a21 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 12390222 1250 12388972 12388991
    0xf010f030b12011407170f070c1506050102010e01091703040c170f06010e010605070f0303060f0603090506010605030403140705120f030906090c03030d05090c0a030c080d0512010902031305010e01 86
    0x9000317005281000300078001e07102d01400c0a00101d40000d0305480c03900841e220034600b2140560404030280065064607113075101c25515600110484000387c001b0700030041600085422108052409403031280507010080104000d000256030040c03041e0b100b401d155460b4101d000d4515540b551342d1000c1c0c0c2c0406200700d00c0d20400c000060045c900c2e807584401c21b42c14481c00030494022500005e04c8113805c841090304042c026049000030303007410019030b06800e5543c84000c0141103c7c40090ba0305006003000410f9151044007101d2280782c1603101c800e460086145e40c5001d96211920648050090100d40c91a12381010f004162490840401c41d40f2070500c00411820301c4000741c40e80072640e10501500c0c0440d24044107607000700c00d80711000502a55140c020505181c010301007140c1c0041d03002030100402040f5101d00003903440080c01c8490281201ca81a80c1e64400c221102101d01018030040101d9840c640055503c40490121000c0e6021a680d5007401c1d56a5410744403050f0351543c1620 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 12391472 1250 12390222 12390251
    0x1401030606090b010c020d0204090204050903120903030708131a0f04020f010306061209020a05100206040507080a02060d020a050d0e0304080c01020105040b070806061b01020a0908010b0f010f030b1201 88
    0x51010308121442041140f041800203440c0317401e081402400b442030311407a0001d640e2654065034034140c0141040c0311a02d400b0000075120b503c4030017002102c00b1440003254040e0790000a9074450000c84c3c5900e034190312a031982c41c09445c600b0208490180085000307501044140c03942d2809840505001c00d0241454070400041c40703901c015045c1094074040c810403070300d544100c442030007003151840001c40403414008a02c09106640000e42c0007004403009040c031a44c0005d11a11a501550580b00070340e848120740c60700d4016420300654803135820312a00d80807040c954020311400f401c0f41041d600d4103980740707800300c00c0e60f1618606038242c1d0070102e01080100e0042c8409018604248020012880c0c030703941d0780354401801fa0119040200300000a41e141e10b07540c0c01c03588480c0851416030030700c801070326295010f98440310380c240014042c4900050804c0c0e05000305600600001c2c0382d448101d201e5001114840c42a021100c04c241d01e03100304099603150303003800c00c0d05030100c0c0307002062240c01c400e0003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 12392722 1250 12391472 12391481
    0x501030b01021515040e0303040506101e0b1b0a0309050306090a0c0308030c04080f03030108010c080106021005060619050717120a02090d060204060e0a08070605090111010e0114010306 81
    0x10605640011840c0456102020a02d036031000112002c80c008484d158080b070010100424100840d220010a0100344140020310790320400303403203118080e401c0d00c0b80000c15009030b001c9a034101c0c1e41c82200d4144901c8408401410240c803816100f81650b55000b10080c1c6031042d22001500801c940300e40600244c01d060240d298404015001400030072802c0c2d903032500a40300f903c0050603000c008000b1076600c214085c01c450082c0012804c4814021039014a241c49a10a105001040d0319100c407001225014400d410f040752011340260100c00c030720b48481e074045d02c0c0040c04581d2040c410041c84d801d041e0400410115590f40380e0756a03441e2022441e140382209a076941d44018540c0c18010910814500101d507940104000d00150b01e07400309202203241e014007003400a00043c008600031600d41e0b03205413025014182120000c1840c2d6480707401c5074031031a480c05100c0008004012000319035025092440c82010844000101040351850302421030300c01c00f03402c802296614004000f8440503004 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 12393972 1250 12392722 12392741
    0x11202090607110303040302041e18021c030207030210030c0306050409050c06070501020403080304060f1b0207090b060403020a030308090f010e03030402100e03060a0e010c08060a0e04080c120301050103 89
    0x218034255030322001030141d010703a4400a200c0c20340c407071010b9019142807090f40c00450b03015100340044418045d0814050141c03909030f07040c1078070380060580c0c42d11034103501070710058000e048902c21100d06404020045074900d400e5095204242000005031111070f109018104250740000b24070b100c900004054504d198440e9105034104144040030a4000c41c8402658900b12403085d5941c10500e0240d0284c01580d0000e88612004820441405150340008408900c801d6081041c883d2501c948070080400e110501d0050748610b074280702015459005080c0d10200a000604041d80c942c0011034000d03050304201c001034489002c0c014080000c01410342d121841078002e000110b40d0707010440d903d000040c0301134461580c58501c40b140b1800340d6609200c071790016050340d0492034001c41c0c440c060400d052400403030798a031011600509100d174040900950000380b40001c40c614000142d00060006003040d141072900700035994542d6400c0048441907240060b205450358501000982103e0a155 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 12395222 1250 12393972 12394007
    0x1203160206010f06030c180b040509071805040c0e030a050c0102070602030a05030c090418051b010309080306210601060c020a0902070312051503011a0405010f06020a06050c1608030601 81
    0x10050000c24102290304044c1c1c1c1041c81c0010304070007841304c11140600a2090a1150100c5540200d807800201008200ba1a011703620a12282c80c0c012040703420518194009112100d0201d0900c020301c0d19030071500d4a111145000070031000881d00090904854040c100c1d4950b00205d440103095805226100c02016680060760034042090009000c9120050004211031000940ca11070ba6889070300200d0000c840d402165450000380c075215980d003481d04880b601d40c100c030348400c100540c428000d41b660740340c2c880341490840c0c80b1007003071011420003030f03031840a0808080e0200e4240501041341500810517680d0b250240540da006001a90301541c01480000c0d004000e00c2c00460341190541042d4030105000090759900c0700c41d55086001401040e40d8954205510a225908500586c20107800120b80402c102e07640d40407001c0d041501c6104020150700603900d0344001c904998091a4041039005415140482896070701c0c5142300c11440465200b00084148030300c1e541d00c1641c0240792880358 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 12396472 1250 12395222 12395233
    0xb06040204061b020301060e0c07110a050a0308030603010906090c06030f0203040201080103020f031c050d0b0301020a08040b10080706030204060314150f04060f090207031d01090501140c12031602 86
    0x710002c040c1c40300c883d100024200d4210181d811034500350701c0386000700058028600a0f04000c00714040c280d0183c00700751030b4031720307002008101450b04041400c101c910080c02908600e2079a034480590713400c02021580c1c95544c650011020519a000302541039200c0c0582180035030034480040d0499944401500e401c502c1441044010b0341c0150788281901e40468404140540741c10000789082d000c40d14000c404049981400c0020380c100c8050f20340e05000e030a050000c41c0f420018507080b4040c3d0620341e4001503200000c9030106900c9112035420521014001000c0c5465010851070310302c04d41d20038000654000707810825113a041c80380903000c101c04c6000d40d250303082c0190600207180303e80c04042e02c00c10501f840c05a15a65603031100b401850408020311046640301c00b090000d411501e010b5021a100081d8014000ba589031924480360b4141c40b100c0e00d190800c1c00464014400000c1501c000310208011030f20610304200300e5488621091441c2d58901c1c018a0b038844000d0003007107003415035004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 12397722 1250 12396472 12396479
    0x60f080907030b0a02031515030a0c050c0706050c120406090e070804020a060806032404020117090303070503070509060705070603060b090d15140103050708010c0f0c0f060b100c0b06040204 83
    0xa055083e003198034402d003d078498840980000529a800d1001540310342c0311480441044a0300009d98495101c421040040d000690740560702485491021400743d005103c2c1400b0302c038040c0c005070403240c951004440c846010070f561002190302c0398200704c0200c2c3c1641300401c20200203443d49580b005191419007442e05256000c03440324440c5006080c02e01800f200054215101040502098403803069070600360140e81c880038102d0a4140c1d402c4e400929404140d11034840f0540e410303801550440004e603d165918903048840707400142c05582002010403130748043c0e64400c0d01500000307005070054001c00740f071b010b03026080342e0700d0340c0c070480050070300380441000b5a55444105025680041c44000c05903040384940004050940c0c1c000000340b0684004002d119001030440c4c242c41044000700034104100c0c000741e460941422003a1f0000ea108403070a0001800e00e880c0b120020700c12503020400880590020f00c0500030621600c0000d0070a81001062044001c005a00960140e030118036241c04c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 12398972 1250 12397722 12397733
    0x30a050a0b010f081f12050d020c0109030f02010c0b0109140a0b06040605090a03060213081005011202010c020d06020d0c0e0a0b091c0b01030b0a0b040b0303090d050106090204060f08090703 83
    0xb0f14546000c18080301e00001800c9140f152010300d050201103401140075030b1149400d094142c10300c1000c0d1203a01c162102c240742d0038000989804e5280050310356942c124038550b102d407001540081c04904000c01c0d40c0040000404101c02e540c0a080340900210385d804490582110404000301264042820081d0080040d00c0720340844050707030914a8810796901285010902003001980000c2200d880090901543c05007480280151600001510003003101a0155010b0391403e01611400340c4125189100642c0a00d4252064a00c0580301d05a1800340d51a540200d0700000010180103403105030300e0741702d07952240b00302009460403070340c01d24001e06002c3c41d02c0032401030340320882c0540c1130a0000b00240408401c0032818641c04209181c0030b603141d10f4241c1c04414183c13507980c2a01d0802036050041d103854052403901d210084c000310300388078140d020400285a008001d0340c0320355950002184c904620b00003000a81020780320750b02d020000003401410110700070080c2c81250007601c014400281c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 12400222 1250 12398972 12398987
    0x8160504030f11031c050318010615090618031104050403021005040b090c0109030506010b0903120f0702010e030316080f0412080c060c0a0507060c110105040b09011a01020a020402070c030209010803030a050a0b01 93
    0x80c4e000a095204091036003a0780c0c01000076800c02c1c10703403100e1030b00e0289038039a10012200a8074200d93b60000d40c0c1d088515050072a003040d020061445403071071040441c80c00c0c0365005030350050091049542811421410300111882a9025a9103460305020030440c0d0b441080410310b204c42c20728008005a1640e12469260203040c01802c81c20750300021000320030b03a010040c5490000c0020462940c03501a003054007155032020504902040d40b40c3c100c02c20614011003500c0101d084070a450300e1a032481c2d90740d02e0f440d44c00854146d4090500f4480070850030950740208900714441ca5001ea9610401d2103400d00d010030041015034000810007407243e00e10b41c80810740740401e0b8080000704405c3c0c1d551405039001100350134261895883c04040206101d061412140100c441c100200038010410301c100c0d100c03101c144e44207400750344542040b070014103195000300f0030716008441c66214a07403070b40d0010319414000e0384003095a5001105124800c81039214181d0407445d5144100300700e0040900180110 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 12401472 1250 12400222 12400231
    0xc01020d0503011505040f0f09110408030a03051f080a02040f020304030c080a1403070c11010504050a05011b1202060a0b01030b0d0807060f020a02010c030b1008160504030f11031c0503 81
    0x1c2e996134000c1d1400d517014009850150040351400050780b501c80e1100f220884846c404c550700743c0d0401030030107460300d0394108403010f8404810203185086001403054000d864050310740054010f506076130344d03002408100310705e02510541c80501640039260040000b43d0b40c03142d017003a0850b03204105001c0001d40007222203030080c2c0e020304059180c401c009415a29001c0721441d442c85404000100690b940e8880b601c9140a44910040300c10803506800444084c082d9020711070304451803401c184210342c01800550501031000386c001ca00340c0d005980b003958001c1380103080005a4084405d204402d50700c3c0c00b40c4d03030400c8001c5c0b070100001c0c41030030f000425000896001034412030300011103800380030890700700650504840c0c2d0b0075591144180002030003040070324071850009180016100051402d40d40d003020f5074240c6c0d52400b546895600c0e4440e01d02c1e49480c080400c0c810100000800208281785210030a4000d25160505807100c0303081c5420555030010143c003026a00c1a150505508601503e410 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 12402722 1250 12401472 12401489
    0x402010c1106030403030c020607090b0a0e040609020d14011202130903030b0301050405030d0606050301080a080c07120602090a06030504020d080a030e03040e18060103051527070302030c01020d050301 88
    0x884826041ca600d4404000000940014000042006054054101244c00d05d91030303085a50783e0392100400c891032090740c020304091450400914010031311403c03022041460003000080c22a41d14814007040f64400c00240a0098884204030145040003079494010955650304403000c00d41c1d540000c0c10b8030000b11512052a41d14002c0703405161203988110341952025000b0070003828242401903aa80041542c41d80140c2051800700301c441c8200300703482c100e4010b03000504d541d0703095507a1725140d0341003264401103510170200001502d0a50518280b0202d00580700180d440c0c0b034000a00a4542d41070300880185070506050100603150040c1104205400403103441d21409401c001302c1c00780c125410050090310002c0b801003a402c03106580180039075802c124a502605074104001d80701d20003417001901540041c4604030014980b451250780c400c4040700c100762004806200c0b9004019a08440002980203800600c214141002581241d401c02d0005042e0380b031902400a2080c801405950f10 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 12403972 1250 12402722 12402737
    0x30f06040f08040503060a05010302040b01052502030a1203020702040b0f060703030e01060503100b0406080d080f150402070503090316050a03080c01110c030304060605060a080a0507020a141506090609040201 91
    0x2030081020030744020313041c0241030b1a02400e080e0031580142c6420b001c181d00c9946880c40107511507029104990300811000503804d00e05800030130025612201c080d05a8050240911040c00030f10000d6020210b0021500e0051b100d0200c4d0051000329100381644a01420b010451030140f569010151413015a0502e00803580c4c0503810b1145005d8059548110340501c0340d21200306102c00c3c6030304106c1041c2e43c155010496295904415943e520388441008045003c000208d0552404a80f446511500c415000d01c3d80fa018900401c080341c1c002001030f01d10303420202e2600c42a290602a0810b4031242e4101d0381c4000c1c1c10f003400244803d030944001400c00700005100d8110000c01c0d0001d2000c0858030203150348903544000456200c0d44200d900b10740607460800c000c40d0b01e1925a003030b82e503641d50316030700c0c5105503035412922402407402401c2c02c020351041c2c101d80000582d10511410785400788001810002c5c60344058044085405001988102815010854591100303401158001d0302443e0441 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 12405222 1250 12403972 12404003
    0x2070b0418060b0a0f1701060512040503040509071e111207030210020310030c0b04080309010c140d0320070206070201080601090e040b06090622051005031b0f030f0604 74
    0x600400c0b80e544680351604012501c0041650808110104c525803501d650989801d1603521540c001800d028100200d8402d204c1004203d1100500941c06072180701107915141d243c900013841c014003200c00c08001900c00300d2058a650742011207a0f2800d445061541440d4404191035460703402d0415441c604480104940060620070080001d13451700222045549050560011b03580012602090340c4012002c68009600b0300c081c3d040714100d0b41010003031402c1000072801120300044440c2c05035060004511001a205028407a017042051503450004a19440201c4541e4880400c8244252054144400000f680765a42100c021a038240b85c14a05a503c2c0001600d070304006410000c210081d200400080040c0310000c1405403008803030001c1c85660790805c2201e0b032001c40d1034518806e00c2200c80700c0b02c5400541c00c10b0343c0282c04581403020f882c0e00d1360082450160451300312060550111100301a6090400d680b01078103000343c02034602c03100c3d40e0351125036038007020784002c144103140329410 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 12406472 1250 12405222 12405269
    0x80102031e0f010608090a06050a0e010b01051207140712020a15060501080402060f040b03041a060f0d150b060c070e010f0503060c030c07120503070801091a0111010e060103030c0506060102070b04 86
    0x651f003a95203d101040242441d040080042154507170354080f561030301c000340c88598010805d803880e400880011140300c3d42c41038421a64242d00500240030700e441801039400099104207107440b0386085500801c91440203003001c000700780c00381c01800c400c0c42c074148061243d03992004c0010342c0f20350180c5001e5035404941b1224402c031700c680d42c0a02220903021041c0800c204031208624800194581c0360b01c6207032240780403c4400b40107002c800350f008040c0b19000c4000352510074100d00010728808001241b01e000d07004959150b000000d8581c45801603107041c0b000701c0254a01e5405003185a2410b41e14070308080100e992542c000c0c024000d20640400007030300b0108110101e900e290740c010b1201c2480114a0b201400c540c01c02d49110340800c40500022468109910030128144416490264040000001075985c44440b1504902c0d40d5262040e40b210b01608109060080d88290b640c0405240c0320700b403150800202034240b60442d00059010001042504140c5091343c0e103010b0744141f09520500032 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 12407722 1250 12406472 12406483
    0x1203100806011e0806010e04031d100c0b01080102070503090d0c1d0403020609061005010e01020111040b04080d050a020705010f05071202010209030106090204030209040605040807050304080102031e0f01060809 92
    0x2485600c500c0c8000f250346141004410700c0180592100607000361690000b07900c4070001d00840800f024040000303004a4802c118010051100c44481c00f28070550801054400701c006000002003015001c0b40b00c1004440000c0c1e07170042480c00001c6041c110aa41d82c1912440303081481d42c0b0904002302c0110078480740412000080c043c01d80d8500a076803503060100d0000808071030a030098001d007000100d014002007415485400800035118400d410b02005642d03a0000020660440d941d07901702000340a0035100402c00392506c11350454a45103414000e81c680201d050404040203070900c4040040e5400160401c281e80013401c001d049160b09040c126103070302503240050007a0b03250f0845101d0850f0198014891001f0560003440320544600c00d0809910580c0b000a412070404000280807450a502940e0090310074440e4901d001c0142e2a46851500607402402b10790b540001804801018205044c50901100c0000c03545e503d4031a045104180c070510840c024030041100141018000b07000b03 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 12408972 1250 12407722 12407729
    0x1050106121b180801180c050907021c050409020304110a0f0e0613090602070b01050a1208030c09010903050f060f010e010503060411040b0402040807080f0a050601090902060409020d020702040f0b03120310 90
    0xc104940700381b1200313008030508240c2500d04802c2520003051a0410b0307452940715255540081410306c1d808000d4401c115503440c4100100002030001046892050000b940200d001c4d5440c10300c1c40c40e4210400009040315482081d10329038600c0104054051801c2982d03111004440e43c00ac030383d9084042d80081c00010304002d00481c40003403020200111030758558141e5078141d0b035524090fa201d20304004084a01a006002001c1c2400002e00b41e510031030007805161818503195240d0b554a03959180b038003a5103030224645412110810404200c0011843e0040c554072800b60220351601c0042500c0f00009003016000c01c21110000180307403241d4200d0801c221010740215601d981c0c905500f0303158100340c02058282e005072070b441490000000391110200d41c1100192000d6440c00d40c400c3d00400d4000d200b00e803c150700780400140d14a0b18405030240c00030400740541d0390001032040004545406400b5030740a442c107040f988164178009000304402002d054482d641743c60b00204100341c610076a0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 12410078 1106 12408972 12408989
    0x30106060e04090507030209010605030114040603020f0f0406050924030d020303070f0903060606030506090618060d060f02030103080405031605010c020906010c1401050106121b18 79
    0x50143c4503883c81030b012154400e9507680401c0451a090f070250011135400f0004000e40058840d006081c40000c68081040b94103642c0010000202025401d002d03401a4020048944907039101070003410006041d51218035120410010b40e5048000903c5441c600c2c00d09241d142c200012480c50007500341d0083c50450392102d90440380c454044a4240800040802c0040400e0300391040303030301400c89030340e000c00c03245044000c0c0130085001418503802441c40c80340444984080703210032500040200d892040111180c20702101525400c084405010301c00400041080500c00041c8202c0d003080d002d2720066030240c099040502e440748122404210f223307080000516100b0f8146c1c0d03010105061208000b000e546a082c503d000c40c400030805603560b2401402415003040c0008014041d14100384045003e0000d0181106016050700301800307400700040035614a0540f905002c0c22240 = true := by decide +kernel

theorem cover : BRFrame.Cov 12230222 12410078 := by
  have h0 := BRFrame.cov_init 12230222
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12230222 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 12230222 ≤ n) (h2 : n < 12410078) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
