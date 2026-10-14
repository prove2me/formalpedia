-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3326
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:19:50.154032+00:00
-- url     : https://prove2.me/submissions/21dbff0b-691a-4fd3-9c1a-9e102472bc7e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 598021582 ≤ n < 598201438 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 598022832 1250 598021582 598021601
    0x318010c090e1008060c0408010510061e110115031403070209270307061b140a05130315021216020a0b06060d11090a080703050a03080705070c06020102041701 70
    0xc40505050005140c0b8202454002d0350118402c40c0c03060300c811880e42407000560b4881c520700700025042011042c207001d610780c400201c07000001201d25040001d003080d10b60500a4103002212004100c00a00940c214034145003160700030400701c1e4807045025280c0c00300740000e440c07048804109400003500007045030b0032194083c280241c1c50300c5c4c501c2447c462b0000e200b0f81c040d480c1003245148090725410009407008500958002c111090900d0410a04000c006000010488000f0154950084600c102c5940382c556103801e030b0341c031304602c40c0c680007144050704002c004c0c0045a0940c070801038550040c101e05030780458201d10079200c85001c01001100516031401613000040614045019420b805500c4100a002149840050340c0e981040f0350f4040c000004070140400c3c8240b407814000c480202a0003000d006041d806e00f140c032059603503074070810020200080c120014490b140305806650526174444007886449482da44064040d410900a04924003110303103030303501c0d448014007414000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 598024082 1250 598022832 598022837
    0x503030f0a030e0f0f0102030402120a02151b010203010b0c07062604020d0510050901060605070b0f1b04140f012a110a0303020f0f0111040909110a0b0318010c 70
    0x74a01c609009401a1001003e030070514080c1c5a8485081d5909000c011848484103000503641d1500744108041c031070f0b81088400c040d03404400c0c22001601e400702013000c00941d8400312901d8a010610b140030644e5a1201c2c0e12065001000008100c50f1070005043c40e0461141030f5038441d034950100f03d50001d81c540c0e407420704841da1352800f581c0444080c40103400c2400982a200c4070b0f00d4a440d041d00e48003950071041c04440da188104040f02c8800e10928028000703078600349281c801385889803a00100c000e05499010300000000c1110480c041340b00700b6417100c03840301403520303166a05030441005601403441405101c003503e240e00d1540c03168600200c21044864040c0500101c040000030680295004460081500610308000c1e48c440c10040d00640c0b00342d0007444032180360000142415400404031015a04190444126150420030765090b59111031001a00084ca400d01c00701e0000d00c5200705401414401c2c010a03140c00410040d4802c0100055030043c42004d65080e40c2240c000d25142c400 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 598025332 1250 598024082 598024087
    0x9050c090d1104060f12120e03250323010c0302040b0403080304020d06050c0a1b03020a03081f0b0909150109140a0306020c0c010f050703090501081905070809070503030f 75
    0x6140600307684141c500540000303000e80d101c00d01a5a690b2194002801100006e4100030070000c040c46040800c845520700000f07250640300109582c5c002003c0c0d0300c40001032018421407410047c050540045401884a070350201d075414035640c02c0c0c10400c5d43d09946508100103107144501034021102107a05504500f49000d15503242e452142d000030b0802c9034080d0301480f031031000c03403114091240a4440c42441c01d54401e6110406020302d00d4182a90401c6003ca20003100403c0e00403c08540c081e8242c1044111342d55020309150703005854080b40d08804160420110700461020040e003c0c8003c161220282d03910344001107044000080c280a0008003030317207414440c228044030001c954110107450994665140e40d0f5540a98014000090b0713103a01250040340e407981e010349400c40c9001141080f40c41e1141c01e440080009456004031070503c50b01310040b4076903108050301c108101298030410421030800e600c00800a02c4180d413101a42d100309031000c20740e4600482108c1648008041261 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 598026582 1250 598025332 598025359
    0x1d06030112060216060c321e0d05041103030c060103060f0f06090203070e0a120303050c09041404030809030406052a060103030c1704031203050910090c09050c09 71
    0x40702426950011140381d90244031207400400401c485041c8188100000b04d140f043d80c120092804844d030110710000320352030941c800c8041c1c40c458126601e21180c07000700e59580c50a030840c00d0014503084040c003804000992441b1510080d07008170301a610580440c030760100c544040642c0d03402086040c0c01c41c7d8004500410000b0510390208200041c6054040340368028806070008070b0b080d650149941350340000800802961124000c074050b1011030b03504a5a03810104c500d007140710307103c000405055444c400314000011a400b038920604004009000300754540c980c1666210080e9411004a9880404a01480800b006a0302503030311980d00c4504059840103c140c4400c012410303a240000000c0420f100a02e0038070a00340a54040c0d21400100d08852405002c200d10700c1032034980e100d01c180410310015880320713042a005a22403402183e1030704e907907607060b04004c2486201e0150601d8840d44c0003c02c42d00c0d00e001d01c00c40b545428200080d03513440201007014130030003005c5a8895126034825 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 598027832 1250 598026582 598026599
    0x302060a0e0f0724020d1407020d0b130c0605030705070201030b130e06100f030c051e041d0114041703070309120306080d09050604210b040609031d060301 68
    0x894500d0754901c210303400084851405414000c05800000c8000e05038803142440124801004404049501c01019400c07401d07000101140315420a40c41c45000000d000c40941d03643c551606c103d6504039003090303110306200103460070714580103030211080c25540030009a15409030096a00c594699240e0314031b00240e5500440080c0b94141005138045480c04a04800710940d00c5080349505281c4020005400c10030800710090f0300640c00002d00c6070b00180240001400e5525000480b83e09940141108a80030a40d0000819000c0e0194216140540c0c60840458207415070448140780d100030061540c035290bc071070f560324080750003804050101c1882d4500b400c81000441d8820000d01d400900090b4559412040d0030818540b140001d032a014103000c80b090600848580840c58200040c0032460007010840d01d0003a88104060020802079014075030001465041074143d201c0d07050070b0280f8091400b0002002c400d5000d90028105800c0c0144120805d4500c0c000b0400042140b403c6d41c3c60074804 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 598029082 1250 598027832 598027841
    0xc020607092702030a201314030f0a052404050304060c170a02151608010b030a0f020706050a060b0324010c02101112091f110a03180506070302060a 65
    0x1801c10341848100150b081038007602c05540201c00f031650105038484038002115006018807003a280203c0b042002801c05c40003186a41e00300c03500b9100d0710103120414000203060258654644041d0700880d1001c40c20848007041d0300c0340c031441c0809048440506400d921101d80b1081700c00510744d604c2040b061000d54041e192074410b4912610304c004550000180f50045500400c0300c02c40036038021400c0b00c440da1882c601c025440420003c03170605070303070fa00d003001403141c1011710174034612950010219140071500d0308501d010b000d100f20159074a8105103030950040600700c4511020610b402c6011640c100038170f0031030b8000d00002c50003c00818001c1542c51842615140450510141050b1180180c58554501c191029030781c840340aa0320128056a041241d0a02e0f00d2400b000200709000c03131030380d8810361100c0300390b10504040c00d801c001c12015500135280403c04e8243d4032645d43c4040c20581e000d43c1c0c21501440600c014180d007603942007840b03494000d900c002000b681003c4001022000c55511 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 598030332 1250 598029082 598029119
    0x604290702150114280f09060303022803030b01050408010213050f030a0f080f0d061404241a0c03040803040314060c070b060f040c17090604110105031509190c02060709 74
    0x5c0e51204980c0c802c1100725441c030070340c00001c03140d403209003c105042d01403000810f183c8000e02e803090940e0428461000c00030003003200400703159a410005c2c0003640705509030340140020000031592640000214030030000184521403080c2035611007008071307080c085510b240c3d03164807043d20100c4510356607404405400a8009a4030480c0501001e4500606401018001d01540740000c003c0c03210041400141c40c2090f00b0103002c0440700c00200cae08284540700500803900160031140000d85030042c03490b0707244110300f0700a440d0f02c408200450818008002001103d10030000c0821561550102540300c1c8003c0303613900c025050a00c0000080380314101015403210006080070803500c11500080d040700c0540304080c0000b9030003c158112102c1c0702d008503402001e20340080c016843c1c20340d14088100310b09580c0d10f04025021003c941d0f012450426041c1c1c0d210b0080020480c0c0c50110030b84c00e81031200c150103c41c01340c10282d26110241c00800c00380d00940c841d0340c0302c0f64031908001d80c60118610402 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 598031582 1250 598030332 598030399
    0x702150705071a0c010f0204080d0305060a05040c03150f052112070302100527070f030305070f05120a080f0906180f1f05180604290702150114 63
    0x881d1340c00e0000300381302c0d12920308002d5500503295030500200754a0300709102039080c141494003050003034903a902d86c0404c04440d012240885c80f01c141031005c5014104098011540750840b41c00458841030004070305007a078005039002480c1c00800b40d00030304500445210749034142c001107822780854802d280180040350003401103504131000483c104007203602c01c40b00070080d42d8212413200400380480d0302e5554908d2102000301031441c10301d18801d0048a8a10000707050280014a0804000319400d544406640007400d85108402502003003071168000c01c0703100000344180002988003080e0003c00c0f8003a41c1844010036003070b5104104074608503904104642688074070b40f81c020030402d040080da001e20f6041101d4070300c03041240101c0b600317891010301444c2c5040440018948100030020350317180d225030080e401c1c00001d00380f25a6085426001e040c4140241039103000c0003941c50700010004c005c581c0202800009a1b602c0b440e0f85641c040440341c481d4450070100f1002140c00b540c0058207000b0b807001 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 598032832 1250 598031582 598031587
    0x3141003060c0c021002070602120406050d02030a1b0906080a0c0806130f020408030408150118110403080403110922060207080d09031716051615050901020702150705071a 75
    0x16000101d80182000740b03840187d00c482c10500c21150705000d207482c1d5400203007080d400e1034104800606107010340020094500d41c040700040300080180c0114054140c920700c0303d00c0640e100200200420f81b64061400407a03042004074000c08500d01c5030244007107030380d510104135485050812902c140300340d100c2e00380c0b1511501050481000c0f84005e20013051b00740000d42d590b80c6040041410700f0f441d416a8005d4001c10b80040040d01a07001d5400111042184001040b250502031300d4414000d5420103003400300041004020071414150380884800300301c800844d6542c900002c00c818011280f941c0c5494075841c080180020030fa44c010709030662040b40890306103443d5500b0503040314003905080e0b00050140044011006082e5034550b08991070000341c801c13840d9101c102030028810b40c16403024151901c24103e09200c9081d44a03801c1c0b12840500703114900f002103445001c3d400c00c0600340d100d01d514100d9044521809801c03a015642e00030f015001c4580341c80c9160100e2400c0911103110711204 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 598034082 1250 598032832 598032857
    0x317090d05160e01080106060203030f0901090803100501030b10021b030a02030105041a07020105060a050105210103150c0219080901180e040c21120201090f05060703141003060c 78
    0xe12001c100203030034400070802507103090a200b03d400d0040c1d12501d850792401780140002e9a010040340c0d4042c3d500440410302e9110b44681030f0041c86042005072150001009214144a42c0c40240003251400d03a4288051507078681084420f40203035090700d0260384690441940080448104071005134000c0681d09010059004207007582d104550481c0c0b00c00150f0101d030300b0303444444099a0400414402000240740080106615240c1e0340101414000c0200d1484580c8103130601c1a44c445440010f41190703540d4911308894000d411042000c0800e08100a001c42c840c400600703510020307139043c0324050003201512009101d0b402a2846410400038004412040c0f10303c61801008040e561402e424038a410b0521003c0154681c10400d4206449101003038546100614240600d800801a8020b50002c03502a401002030300c030010613900310956400d040c800e010800700c2c401d84050b1018403248881ca410b40003107400c2101d182d4110000f4135824030120b90f15910000681c50181000f0691250 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 598035332 1250 598034082 598034093
    0x60509030a022403090d0f090f12080c1e0c0d0206030613270302150405060711010b0409050114010503060421050d1404030e010f0207210f050a1a010317090d 69
    0x10448217604030360b029070208100070340c1c8a1800c05109145207400803446080401e954106c0600d8450366401c00d401030302480030b0140e000b080b80e200c031f8040c004480e40c44a10070401c02c101001c8104003589805118608209401c03c9030303042003c1a4000c00f910f245035600300030060101000b4803030b0320803203541e045860313031140c4400d034540401031100d0b070422040006462300900e010803e509043e4480a500144400030328001826900201c06081040c00b40b208150102c2c01070800041444d803140c141740d010000d1000640c003019900c0c00b04071488180760780f2030040c96512141914010010650110140c040207a0100a041100076a18061b484c2c08142a1400141d440e0f2104522441007144240010150002440300d40c48a0030301704038940000c0010302940721040741c0301c1e1010502c5011000280c55401024900441e07074010003000c6000450706000e99505c61249045648076044a00e49000c0004104854100da922000503040d0186440c0d81d103030550000800c0540240d40040032000040 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 598036582 1250 598035332 598035337
    0x207050a1b091a0402030601020a062f250c0909030327031416170309070e010807090e150a0e0c01031406011b0b040506010f060509030a0224 62
    0xa0088100300c481031412544001d400c00c4581c8456409481c0c101581d02030502d40700e86a1951100303c0300186c0380d54030fa000607410412040c90003400c8130b140903d85030001000d14900540c0c0c0c1500380a0b44858201c90b540700c180c03485002e280000f4003d200c0081e1300c5420201400d0000103201d501d111418a40c0c99140c1c406403998260100c2c08607803980b03102080c4264104650f001c0000e042444071819009807005031400c0e640c0c11100014150024406081d181103082c080c00b40b640c800b404aa640c0c03060340343c139003540e0410340316800c4900940600207201c40000080700c1c181c8140034060401141b61410a800801c044884205c0313a01a04110160300408103952504c2018200000720f6010b00038110340b0705100c1c0c003614250600d032030300e4034a0101c214074000440d8003a10030300b0078107903240140da5010340000b42e40790300400b40c0d0701903810001000b00c0031510354100c0b990021640c1c0619100c1c40156542d02031006850707050342c400d52804016140903074a68149003801d024544413400c036070154003210b5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 598037832 1250 598036582 598036603
    0xf19020a0906110a0f1b08061f05030f1015120312050615030109050402010e03060711011103040201020a031215030311071413200a03050601180f0513020705 69
    0x166001420080030f9040618601c11654140250020700300a40d00c0b04001010100040c1c440d1740f81560031440c090074183c800010344040f0044131138900d08440072401005d1260406c07030016240e0500040c0ca402c0015120701c0c0402110040c0c6004503c6401e85002000250751100410b001444001001080040303034145450003550740e004251049200d800540b00e0103840ca900408000c10b40c0800c4908841c03c1d681505e20444001c00d1036203072400101d030154203004d5810340c1800f03403105112099070000319840581820398000d01910a090245411078001110040c0c0580c1100c401040040d2180403c1e41822484030400540e11501c0041c2a03a0743c074a40e0000c50215214002e41c410810f0304000b900000c00d162100107611400da6004070303c6403004100a018440d8030f5401c2080300701604468150030600d1035907001d03280c18078007c1c01009446c1c140c1d960b03804503031700c0c60414480c1222290400e041e01e41003170311103100e945000180004658200904440300c0d50034406030303000032020b01c030290340b2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 598039082 1250 598037832 598037837
    0x70209010b0306040c020304050a060c0f02040513111c06020d0615020a03020106050f0f09040609080f0706050603011b0f051c0203010e010f0302030c101808032703060f19020a 77
    0x140e00c1c100b41804105d550704aa035200355407040c00208166034581c0c0d00d80c4240d8a03146401c074081141840c22024810354490f000f5440341c1810108070207a1202d116080d1098040c0d0801d6501c01d4011041c0101454a44e07800741103031000ea24070202040d2150002c00402c2149400000c0307803961254a40d902e00c1d41250307400c00503086081140c0500d98240941c00203044110b4144030341e0bda401002809034034408003c41d006400000c0051706000003030340280c0c2c0540d00300c80d51030741c0c40550224480c1036900c5850100c030a0744c40d0070040766607030030305206091400c9a4115800e500d0000300070141d600c1c2d10000041c2d000c01004010b071540c42d038a1100804a55902014090b0726035040502401c4859070580180c1002160f8482c20409690000342c102111300b03081c4e410321170100c101402220440d45104007001509440c800010340194000002e00302c041e00f00d83d2602c0148140715081d482010170303c8040d941948071001080100018401e401e801c5003580100481c602c9010442105907002071141501 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 598040332 1250 598039082 598039087
    0x1d0f0a0323060610140f070804050a08062e090e0102030108122b0f1a01030518070b0313050601030b010303080a0c05030f06012304031b060f080606070209010b 70
    0xd20301e8050600441a03141c00e0241c50b2034a0000040303002414185450810400c0081c00b0003d4840c01004840e0000104002d16903507554505042d00d81c0e5200e44a51809050783c51000900d4600108035280101807402e10102001c80c0407010f41c2d0202d20720907222080581d00440001c3d1a0074510079114480781e410700258032580350480302c605003015800164040c2008100410341810034450780b078858202c210321203400e0f0700a4030741d000c010711408255240791807034200c0141c0f0300803101040380c8006d90243d0b0113103d16650340c004022444a00d4100340c42c5075200c2038007440310344882400f0315880607403094103000c00706c12622003600d059400c0e40250341000b8200014014558441001640b00300c407440706001c030700d5400c1d00042c46480024170503554040010701040c00c980c8074942d00c21000d0a4100620038804004040320900c0d442840101c0d06101c0d2801544080044418200304848442d04c900602d4100c8002c252106400107140c1940402d081040100517901e40c0841030280c0001d508858 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 598041582 1250 598040332 598040363
    0xb04090f050a050717150607031106090304050f1e0402130305070e0f01060c02030f0f0c0109140d0b0403090810050402040c0804110d020103020d1404051203071d0f0a03 74
    0x89440c05000d4111090501c810040b0030368015038001c10181c80200d16082aa907886d0b444030300d01c80c07030036141984400001820401e262340050307000c0e410b00441e0705465003601d130454602d80d0380c0305034440e4030b81258032074180e44a14509002110602000e441c141200010004005030480c0e00004031000d0420001006105010040100304054101860004000d00348051801002c240510a400400811210b281304540742800300c83c1c43c800c00c003802c481841918034051501c45041c030351020700044840c0000a5440d104951844043c1806480b5940d40c03003950b101c0b1005020010015030070300105020001d00d40340200611640d001e209600000c03141402d1040206464004041c44200004081030102113400c0c0f031051400410308450ba280b440c2400e00c01030b00603005a0a9103140c3c1460000402e504100e000c14a91050784a14207460342e1802c85a01100240000c0d02c60800007900891180f07070303001d00300c5140c2d85141e000900403c041908040019040c02c5c2c5c50b0012030305e84442c9c04140 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 598042832 1250 598041582 598041611
    0x50d0c150905060d050c0904050a020a020114061e15191412061c08031005030c031605101707020a060f09080711040b0a0e0f0109110a0e0301060b0409 66
    0xc6200040078038026201510300700004109004964014041d1070361400842c00b2a507000003110303000c040142c014040b520309002ca0100030740040c840c0802550802081354450000d2048641c855030008154004280580c0c3e089000f00b0400003000ea04048001d5000d201046000d0180414400c0e950b2008160000d0349070040142d500d0820400101d00700f80180745011400b03005483e031041c41a110a2440c002c014010010f610b00e07128060b0454134000184500198001110b0094074016422144101c6803201810342c1c841e01c2c20800c0082a080c07070010b03c02481c0151300122110744601c1c0a036401c002c10450035403145d0080d265032025a008201340740821205000e62409000c0301d0000b00080c0696444648051081d584003d0092000d203a069042e65a1a3f0012580110140c10010080e8641000600d06030342aa0401da003440700700c000081c6481c240c000c079000e02c85251400c070f0038201c20b00400da0345100001e10381607155499003030104e44900c21401600043c00700e04d02c046003022480048 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 598044082 1250 598042832 598042859
    0xb0307210c15120b060f121b0304080313150c03020a0f11070924030b01030302061f06050309070e0c0a0e0a03170c010603060911030f1b0613050d0c 65
    0x8401d0000420a4006a500000060000200c0c607002090343c130049000501c041c46403075000c0e41e40410104540442c400c030f10903168410340c80c1c400581012100c00c541d503032030703800300300c0e4010039901003000090020031003031b485401c81034880c1041c03014407081080e4040560b145414080000b0303901040c0b20840c00d030310004088085119007810382c0b820041c680c80c2c9841e82d000340545140c0540310300d49103034041e05845600c11a2854109400003080e240d20340300c2c01e1500d0078171083d0014403c000119000198101d60402c1e12040102500c035918a040001d45203a00014901c80590060360400a80d0744040300f140380c03050f600380c2d406542e20304012030040c4c60004403036546030058960140520000315102c9011a04a05042e40661221140d5004601428054100818043c1043c610000704502c0346000070704810101d00b9581c072210842c0c0100c1da100f040e20220503220600c1c03014801981400f80c01801e00000b0071810b100d0207070b200e50216200c03003108102142d0580d1480010494410000704 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 598045332 1250 598044082 598044089
    0x503011a040b0904020901170a0533011508060609090702010c022e02070c090c030603300e0103140906010f0b0c061f090c11120405010c060b0307210c 66
    0x118400d0a042903008686c2c260414022000540e07000b80411000b4a8200001c1200940c054111303240180c088807102c0400351002100300a0040340f1480d500c1d400c114010950580362070388002c50301805200c0003280c01d10740103401560002c4082240e0403039506c4e01c1d44040d2181c903241d000440d404290000007894440d05941c078005100101c030306100f42041200c5408203a010031200035840d55144e0500c00100c0038654044050030f8a02850810001e0b015000301085030b026441a805106440c0c1c20507a0071a0070b640344c9541030399142d0703032440503600849425500320018900000d490501c001d060996034425520000c555101100400c401640303554a18090f143d4007024508009444000355915100503102a9102000c003844022004210408400500d107500f81071200c1582b246000d840708411060306a5940250000142d109030645c044408484041e52410310b05180d03a10f4880042030441481613150040000000f54404501c0300c014850f0380c961010000700a0901e01300082c001c1561 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 598046582 1250 598045332 598045339
    0x60216020a140102151b211003020d060504032c0405090a0c120204090b16031b2a060606050a020c030a03170432010b1519090503011a040b 61
    0x1003411102e642d0100d0f031200070680708022030a0701c0d00d130215034080000c0d0111006c01c81e07001c040f0300c401c41da10f000c02d0b03010400121092036640c5a21966060f2808405501002c0d4204000c02100d80004400e03a2107a988140a0700d0442807a244105060301c00c42401220403110811595006030b40349001d10511750003d4003903006210326580360b81e030010031101900c1420000643c1240110554682e80c01103d103c9902a0b0040004d15209426110194440c886600000d280c06003107409103203600f6100c506021a0f880c0c03070000c00c1d83d800090354640740381c40403007400031040304150002490070300524000c2c0c480b6440341d544030b41c0c848400070f1a0504021255100360310010200c0c000c01c0c2c0080340c0790401d84130b0f82a248015035660820a85070103240c129035074002c03011002c0e0550340171441c4a424038140250028012626040f040041c613094915220148540800c1203110301007051028200303c0420381440e0403c9540c0300c0002e821900c61610010420400c0c140e400c81d54034062042200c0400101d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 598047832 1250 598046582 598046609
    0x80705040207050703031413090c080603060417090105120702010204030308240d03020a0c45022214040c020307110f2107030b010b07051506040207060216020a 70
    0x140ca0f082c2d540c6490b0310001d07003480b000c07010043c4462584800c54400325105c03240b002c1c3c020754400b05203008000740034071240001d041a010510a10b00820000d0169030040c0c104a01d0118046003400c0c1540104151030601000300032510004100c0e0801038824006a000161518a1130030090600e480040802d202001c079003a00d8003c004160203c0c684500007030320303800e06070041e915007685042c18130100644801d20010001800f07100c41c00d2181018201c580c2c00d620140c1c45803400900c4000c4202c240100f10b40b50307014502801085501174541d01c01c0c0c20740240d4000451005822000815801c484000d694080b452840790070f090081d14070036201c0d44000c0d4a88001c507100c00050002d0b110515101310600b0001150725901d51914080001540010108806217408140e07038071841448101e40c8014060000aa001050000d40e15003d8102c4080c1645848100c5078017030004c001062558070a500384039120100f003052014003020407001c440d17441c443c0d41c1801000308042c4507030312803001e90844 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 598049082 1250 598047832 598047847
    0x50d08011d07050a0509060304050601140315060d0501061d01140f06160206040b1602130b09040f080d020c101103011d090c10090e0f0601080f060a0803130807050402 73
    0x19000d941d40c480e02e145042c03512800355180884062154041907640003001205020912402203940d6049501f282d4004111480c0581811346884c140000c40715011600000150103080102c003060019121713000010318507840e05803603003421015204980d007200c0724800501c04451a0344130700300c4105007115102c1e50402c1c5100018481d11600c0c1c00c917240d000d5000c52007001c64990005543c05000e12405050b2941c28800034201444070506090b4400c41140001c134240304424400ca01180340003505844941e580c41e1590504400d140e04215220441003006200c4615244040d0028600d4000944508038482000c0c1094543c4002181a00401007004010320700300300c640e02c03004005202d11030085a8403403015605007900c00d002d140c1c0100c5003500b050b0980c0e500c01500402d40f07a5603000300d4180d840d1078040d03002d03036201250842e002c103060101050100241400302a41700d01d00900b294521a05c0780661420342d000b06804528140d03078403409000700e11046c0402009854142c5046040040 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 598050332 1250 598049082 598049129
    0x110103110d0216080d0b0a121e030e04050106080f0f150d03091e080d17040f0212070602030c0c03030c10200403050703141b100504030c03050d0801 65
    0x40c4001c07038510581c001110b40600061072051240190842645a16410f01c40c4800c000b038202014100d00c100307013410b0046102d048200412540c1c0342c102c2d4100503840501e00c1072800c43c140f80c1005030705024241508800c60b940b41c4c01210301900042e956000070f8107101e51450140700c0e024181c2c1d070b45c080c4068208400452100d0820074107440446d400076060300c090605440d03007501608134003203000307a0100052943c484155010200c1355894121600301d039a50500b160781c0070510b10b40c400b60140e90000b1502042c1d00210906510b40020011007000c2d44500b41249400d84c0c50740090096040458900d46440f02409150800b01c0c00b0b901031450a4403030350342241c8404c480104088a07580c0c50001d6180f030b0890810704a00500300c1d01c15943e4603901c038140701c6e94074085031000312581c911030006440030210100c3c001101c01501034100200c090b080007007011075030080c040b01003007103814480000419614000c450045000b20003411140030000001044084141c00c4402172040220303a4030351500 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 598051582 1250 598050332 598050337
    0xb0108070c11090c040801050a2703020d0c080405040e0610050d02010e131e15210210050f120402090c040b222403050708130f08071e11010311 63
    0x240c00f1100d5a0141e618021140141c0c019900064090b40c0b03002d08100002400d0343c04007100d4950700b0716581c5941c1d04860f941440080d00c000060040e000000082c0040d8010341510032424415040c841c102911000800e007119900c1c03072545030b954050400c0c440c40c0c502c407421b1103024110035a0324075803014a40d00083d02c0c903031080031024020ba0000e001c20041c002e1a9003d4074460000b04017541100c16600a01f002600302c001002a032a58102000150030004041c00b2258201610045001004680800240d010401c03941003c0c02410086900ca50f023088004100c0550746000882140c1440e005118000d20000d2100c00a00d20411050140344000016030303021200d00c07524030038004916408903c10380c03c0c0c0d5101c184d111111401c552001095405c40e40c000601c242e400300066a0f51020890341c140007502c034034010046524508012488403042505660b00811229141a00c2c6e562160a1000d04103d9003018402810700401042011620440e400e9401d02e42449404030b010741c008001d1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 598052832 1250 598051582 598051613
    0x1239120203101e0909052b08190f180b010b040302010e21070b031f272903190b13030e030105010305071a0c03040b090a0e0a0b0108070c 60
    0x80c5038501c003042d030103d00090010080d05402c00306000000d11407502c1c1d5500d481402170700c2214040f0a42032032103c401041034100038480740c0e0b501c0fa025180c0195821602e4403003645004215181c4611500801d200e0040403483c4c0045105401c201509091024180c481078202d07610940007040200050b0ba8003146900001b40125945c030f00800d6045110300a06109035800f0025001d42d00c3e00048880c205005075104a8084d04103100d003840041000d1980c1800f0b00605e800c0624809880d0080c504505810f1000c4030309807000540128460010440c4040780e0140fa034044070200d40c6034955050600080c0210041141c400071220310030b03a01c1410218005020f040c140d83d460200c41c080c0342c41100300d0640c8100240080199585034207201d0b480303118a0291842c2003801c011200301c0d10280000315440b1580c41c0c1e0246003454209151440d1561081d003845601200854001c10720380040041c150040d9402da000017140502580090410580142544180082d295030b04d008900300c40c980c42d005 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 598054082 1250 598052832 598052849
    0x2030705011115070302070c054204080a020f03070605190905040507081501090f030b1b0c0106150903020609010c0201020f0a060e0f060403123912020310 68
    0x106181107480c0d180c039890301c0c403082d454000f40d03041c001c460380c1590080c81c00c580100e11045c40d403034607030047c002c4103090410f03507413100e10010010100f01c1540f034189200c2d03040203241d16180450b070801003002d0380d08160080184d41c0c000921450840c0742c215040d00075802c0580251644030315009020b0030501800346600b1740802100380d111101c901c6003026601a00c0014400c005600340320100030881002101d980003240101060b00b80741e1360140001c80111900c42403400199811a07031681410b181c0074243c00c00c01c40586201c5409400d8081c058014a44484000104a46401c0590a50342c12071800003062000e40c18043c40980c80b00c80480f5000e88003803c00c56000002840100e01d00306843d450203040d030103400a900204401900b010780346940c410111900d440080680701e4445030240d500070049002d404403120800711a8000544400e112a4480c42c040e88031030903041c3d001c0031a5050303484a0b142c42d90004443da00030481e039401c10100a001c50031361508001140c110710190007030140 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 598055332 1250 598054082 598054097
    0xc03030e010908070f060b0f030d11190f0308130804060503091005150906030f2107080a03020903010f0c0f0c080d0e0307031b0c0b071a07020c040b0d0203070501 71
    0xd10002508011003143d88050380650790441410403074005181664210740c46400c200c2a5011450110007080419000802803d100c40350583c0a1351030f020904800c20f424010b9501604004002201d0100018054907203640002030900d0002e2100320000d290480c03d000070161500420800e100b07840503500c1d24200b0030307565100d641036249800d40500c1c8000391a420041040078014400c0c1d19103c070200c0a8582140a844560405440703002100e10220154440000443c2c0e807a182c80e0f40c4006103810003049841c20744c0a407a420041d61010002d000866000107944469007000d109003042c072906100c0800540344280c000038021403403e14603504200300c0420920030304ca015012141c008160207801c00210b5030300d02e41a07499401141054020812518a600c2407280303620b2040f02c1c0b298408503170010b40381045507e000b240c00020741580c3d05104026450800007282c01900e01401241d001070803104801c408010a40340342e0f000c62070060b40c01c0411000180c800158000c1610701c2424040e0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 598056582 1250 598055332 598055351
    0xa082a030a0e010e03090a05010c02130c0507122a0f060e030f070b01300303090312020a0c050c220b01052101050f040b03061b093106060c0303 63
    0x50181c14900540d0410f940307080000180345a0002c010411294282c4640c081580d030f58005460f18036640740c0c06500a9201d002900602540e980485107000c1c4070300f8a01d0402d400c2e07440f502041100c4880c43d0f80403d540080401c202400c071880e046801c107079903540e0002c80c00309580d686100040f000005241c40c2c0c41c2c0c030041035804824029100c0c030012004041d51903000174205211448070a2280078025600d042c20b4550388020448180144200d03c524460490002e980c118001c007101403081d03003040303180c003044007a41c0d449000038403e0603c5d5944007181c1e5031090a1560030082148080b52140042c4404020340c0000442288002c010081c3c0001d07202d2a084010795292103207100e400ca48001c0180140c1c0c0d04403c403c0000c0c10b8070400d44810420820000a000440e0400c500156042e408a000910300010741e6100d01c40c65501c4090f00c40c00c021030200810403001c0c2d1031000680041030b4a111030b0801c1d100c03401002100120302d0007800b50b5460008081c00c803807204540601010344600900 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 598057832 1250 598056582 598056601
    0x909030f0c0519030206010312020604080a1b02040e030711030c1003050903040305071d060a050108040f2102072d05100302070503120702010e070803030117071a0a082a03 75
    0x2c0d0b0440070040c407541201101c514001b9240d0409000c100c44443c1d540c00d20104491000030081c0c803460b030081d5050324040010320240c401c10002c000341c0284501107080b107401a1101d004450301c01a00c000203684032526441c00b10030b0403000742d940a01075440390b02100400c0d600c2e61038605072240300303080008180e12a0320f8800e080d031240d42c0000d0a40d1140110004d420214000720000c040d0b00003c401005031500401c014140075940710f200e00184180010a01081c50511383c20001c620801c2c040303c404a031030b00b000228041c01100d071000b58200b00801c11502ca40c1600034520442080340030f41c3e510f01d84500034810301e0000c0c0605401420078256064407036000b0b9045488440e005001c60f80c80d800302c120864280c0300b080302c02c80011f50800d0303004460541e001922a0603581140e000d107046a0170405628261000d107114000782d4468500c000a0807008100402822400001c2d86039403009121009840510702810540071100201a40c03200d88581c2c1c1034107250842200750882c1d8070380f900c1220303 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 598059082 1250 598057832 598057843
    0xb0702010911041a04050403020f12040b0a050f1b010b0f01050304050a111513050f1f030c120908090405010e070207030201031a100810080c090402130e250909030f0c05 74
    0x1c280d00941b03800e0600c014142c00059050900d403405040321013144400e132040342e1600552140203000758051041d680c01c2030049000e403aa62103c000340c2420522011107c50001c5c2c03079000020703441c1e5903404084c0c12030b00340703980021001d10003070a0051450405e0b030345250b03a4036600b10001d004a00201400f9140d070340e642e4168a4082c0c48040001c0e212141d003900d03010281030030300c11544101480348a0360581d0500103440d003469441103e030343c030000c030130f2880c2035000c3c098111164003000b1640152082d00e042501c00c401e03603a8010b0000646900044041c0805c0b55030681040700c0600c0c1130810003807117542c00100d541c1941d41c28a030104402c42030110300e50180a0012400394801c0c04080b03101440b030741c0a400395120301009010310f40c22507580c8083c5621074404240d1aa0002814000500541070201107500340c030060100004e610b54910755068140600b101488078800d80e5031444540681403a4100c1c005083d440c802040f10000300c3d0750213003a03484090707402010302011108580601400780207 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 598060332 1250 598059082 598059131
    0xf3c022101060f03110a050909100510080a240209062b0e0c3c030f030301080706030e03090a060e0d0510450c08190b070201091104 58
    0x625a00f15100d2420720150f1442601040c0945c8140c24002a01e10303003011401d0107402100050310350b842d101c41c0c0380d002a080050500804810010340000e031035504000305039503a401360b4030140150071403400210b0303012000c1180340d030f6140c01070100790116503d0008841d06032004c85501d0064100d110480d911915015003021202442c20a01d100e4400d400700760483d40880445e80c070352146c20b500c100c0f500080d070310014107201500d1961203070382030343c203204102401d02c1d47c0141100c2c02030700c61180080c0703160300c03d0b0408105138000c1441044603a801d401a4094000d0142c055801c0204d418003190340c0034180d109100402003c8000c480203606d8031680030310f1098114040d200381c135600c2c10700316000c1c1c07005458035980c112002e9440c04441c0000001c4402010302110a0849081c1c40080080381c001b800b21309a5460041200007d002c920800c04008140c40070864110300354064186401d54000081c50705040d641000b01e4903000500c0351148413207402049a001031140e1421440042c0c2c08403110 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 598061582 1250 598060332 598060349
    0x51303060f06080c0a0f061d0a0f06080a06140607110d0308100f050a060e06040f24030506010206010603020d0e03031302040b011409010302070f3c02210106 69
    0x2001c20710980c0207400582c2980c150700d00f02c6154150359418032200c2e005038070698206c4a140b5000313001c03551003080300b018414100131851180000ca6000600c450401d680314800645100d00b04000094218100692100d1a9070080120f60f01d0f0070300030500741684090700c0b4802c0130005056001c11000c510ba011030441d0213411080075000e01e140280080c04140c818020500003d100003401c031201a400a00344d4902401058419241041c269003a40703880c581590311903030a00c0042a061280e04514004043c2d49103162542c400391a000d1165445000040003054103040400c0f40301c0c0d0300001c050f411030b1518613005907202c0c1a07110450040010046481890000009002491114251440686000b1030701044500c03044001942c41010300c288000348110203001004440d1f02945c09410300742d0203048005002000c5a503061002c603041e0301002c0d40390400142844020041c403400201070540c01a00b510030004540000e42e615441c4030300f030110790301c009014200c2200203401601c020031b8107a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 598062832 1250 598061582 598061591
    0xe0d03120f0c08130c090504060b0303070609031701080a140f1f060801020a0f030203251215050604030204020f0f0f181e040902151b0606060a0f05130306 68
    0x1018007030040e00c1c9603108500020204008200c8032031181c00040c07145580b0502a5142a24100301217001e080c00800c243d075415641c0d6181034060310144018130520f4480c200c0060054601d25002d007d9822501c0c003414003022030341c010b00840c1c00018110342c0203a00142d0702e207584103030205803030701c1c0c03101c554105c00490080ac00501d40c80c1c08814030011410b0740301031061260742c1d10f80901c14200e0050002c0c481c00140050711410105002e0380c01103411030f9001d880b0200c2c40348486000c00a41040c1c545600000d071861005041c010b04521564014840c0200d03255161450310000800380d0095000103071003240e001840b02510b044810072640c0304a401c1501507111a02c1c40c24141e019000038032030720202003041d540d29101d46440005c00000c490f8101c00005201441e1b002d00004004203041240c02890003c02441846503810103080b80340012050030034030b40f0f80c200f01d0030708200340688a640900c2c0305002542c56070f074104124142e07140080c80c1450304d0348486075404802d9401c580c00903003041e150 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 598064082 1250 598062832 598062851
    0x1a041103070621090525080106060e120f070902091809070303020f06100902161a100b030105030a06020c0a08030c040f0b0703120b0409021c030e030604030e0d0312 72
    0x3140c0d0100c0c1c440007285008014400000c4609a504e030309001400358000b0448a84034180032041000d042c18050401031109031503490306401c540180d0001c101180100803513110b01e01d011400b142080e18441d020301070948040420030b947c0c078000e0184454045d0082540c0803180c50380c40c6003e502c0740d54a46d05414a0a01c00704080e165913681c00b040e40140035000c8201e440e400c00150f4603000c0c14841115040403403402030344e203000707401080011040881c4000e2450200742000740074110130444140c0420b00e401c260141400b0074000c2c6d400507107030500610040015039004110708840981141000da503400b292070317005003411030320340740188880c40200601c0344000b044d002503c01d4884d01c42074154110384070450582a4000d003400240055003444090242c90841e80080a1500001d800071035050301e02d6000440d001e44503240480f541d00c0000c403090a01d948071008110304801600900200d081603100280061100800c49028a1080ca0200105445501041c1e4409102d80003040312150 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 598065332 1250 598064082 598064087
    0x106031a060702010e1005160614130c06080406020d02190e0a1a03040c03050a0f02040c080f06011206121a0106090501080c090114030c07111203180d0c0e0f0a0203041a0411030706 79
    0x5852b0303102c1100c0d40483e0300144000502a803260b03081c940203018101202c0c0b80230b1040702e041100620407100107400b40403a50f5501001c1c0086d000043d40003444101308031616000829a0f280050440d2094500130020041d21040f811405002204801d65990b20394440c2040c6d007009150ba403004009128000b003d10900803070082c1700310f80d03d1080f5810b01c009010070004440d04003007900c2041e41d200c1c1c03907808150150300070b882040d51107142c10000f113103e0f9562030204543c07900c807a4003500e00424044504646080c179410742030241046082451416040c000000e083d418010520114064001002c820350b070301901c0301c45008025808000d94902e45000c0d41e180b5070f04070120440e01601d4580c800c100d1858105c40c00b401a00342c94006500700710307204070308140510481100c80d0704059403410410101d140c80002c013020302507000e209011800e00280780c0030030150052030f0140c02c40c81803003403200081c89904102c22403d8030720062801a1150700b01805500c41e180c045070b61600c948100001c800d41c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 598066582 1250 598065332 598065341
    0xf0212030d060e01150c0f02091009050a020421050c0307090207110108010803030a1a0a060804120e0303070809130906060609090e07031b0801050106031a060702010e10051606 77
    0x25400c503014042c407a40d030f0101040008080c0105040d40281d0707110380d0390f4070344504201c0007943d0040e1040d140b44102a004030700b692406071885807035103420120511503442c0310301805410071400c400441c600382c5001c00000740081c0032400201d90021705c2480c0e03000d10004200341102402c00400342e4100c155110071404c020b520076902107855006014504080b9030280031180c0c12103100030003852456175201c64440080428031010784503081d103804001143d4496112120160031640c4410165081c641010a40b501c8805030107800c000740d24050205c661000700c02e9404113644034049613266060318001a0b1038160309110b026026103898045401d000e03403038011104907841500e440516035210051f0704140d860f84514900301c0d0340805e4040000a590740c0b403848030a1a814204600d2546405c1d0203400c3d80d000781d2180c000039032031301c502056584250a0031446414111041842c1002c81e0740068101b44400c12251720a441e44198607000c0c50151046500820b4028900000c00c441407801d01c0051 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 598067832 1250 598066582 598066597
    0xf0c0309040f020c060c0c011e05071b050712060f02070302010c1112030609220f0c05060c0d1107170f070609030b0f06041103010801050f0a0c0e0103090f021203 71
    0x89007080c4011411030710500c01c483c4d001000201820f415940e00d002c3d42c15603848002450255940e40300d0005010f841c8400354031076408512404666070600c0d0360f0041000c521a9080a001d42c110400c00d000600300080101c2140c50515070903600465504003200100031180000d00110b0001407a0801c0560640c00103100021607168012452504030390702c0c1e504c032500c100403040b0081c1000400c030f840c039103124200c0e448842c8042c0c51500552110304062509100503089464003135200c081d10030090580101e40c040c0c4004d480e1a402e100c042210550380310b119a40201c00e1000e51106080700d072000303204950203000002c1c90302ca510a07188200a968015081080c201c2d40903424010441c544a520281e08a80c0c103c403564001d9104c00510742c540107405801c440e40a56180c8071b40071012044009180281094030000985280c0305016001c2c00e4401498401d811b850710404000e0290464a0321508000078a80018021220325100b1b01c0d0420382000658404d1100200d4041c0c00400001080e00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 598069082 1250 598067832 598067839
    0x712031b020d11030a0f1202071a15060f07020103181e1104020a0f1b200319020307140a0306060305010e0d02010b0a050f1c030305160c02180c0f0c0309 67
    0x80c0f4003184102d0380c590045086110024003c084100c3c0303d5442000e4500e4112440a80140790507669503886d05803a2164104d400d021003003101300040c101e981c1c48000c10642082e078035145801c040e041150000d00c46c6510080c181a82c420140000380c142a00e1280180c4d40140d540c0c41f680561403a6480d80840300208641c489000001d110740350a19009a81d481807543c0c44040400c0c20307105054030b00c030004030161050440b04494440100d03114209540700c4030010501d81035215258400c0c10b0a10410b9403102d42032290460b62140143c4000880b01d044900c00300042d0222006640040d40d118140d80c00502101e050800c08014002d0641c44042480c5050b41240d858400019040c1c1c280c030001c005003544800c0c110360402a50909e0305400d81804001408039814640401400c1113800714100c3c16800030381c1c0c1d1410080d41a00046c00e50071001450304000e8212807160303000030902440303c8c4041d812003c00001049482c125001a1440c006c143ca494688803280407204503500d030001c42000d0705c0f = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 598070332 1250 598069082 598069097
    0x9080d06180606020a080a0323160306050102010b0d0b0a1416030b03060c07060203070525020306010b3c07031110050c12061302071113060503030712031b020d 70
    0x2043d80c00011418a4146d01c0345101d41052217a031002e50062038070310700100a480040041c1042c0382d503104059445110988a64000712564410050403501941c2000d4150383c0b5164007138040b59602c440e2601c840354412042d201c0d03a500d842101c4060420341055241343c1d070301c0e0400c0c8864a1280c0c1005030740344c01c15950410407010980209590cc0b403081d51260003042d030421a070701c04100c80703800031684000d00c1e05041d0b103082111f9050801d0760342c0c07a0a102940c5401c4140c01c408501d401d201550041103c80e804900341103507004000211450700070409810402a04428403200070038072040721242000c000300c2d407035002908010304464032507482c2032910700410245089140c090703ca564082c0c0800d94140e814416036031840d4102410280c1081c2d03011314465a10f02c2da2a1040c001041c24030320485e209420310545a003400700f5044008200350040742422020300003501c3c0003064484898010744101e809122100e400d50040082c030100c44e00030205491046c0c662600062800480043c0359150603 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 598071582 1250 598070332 598070339
    0x30718081e01020c1618051312032c011410050405060325151d0f01020a12020309040e030405010e0603280203240a050d0602190207030c080708060a09080d061806 71
    0xf400c94104031905031002071140c038248e000c540b140d40090448015410005001880001c5100600c0340d51400700c1c2e900b444c0b00c82903c61100081c006c5804e240b820180b0721005040401c48400c01a215005181c02940d8034130010752a0342d4200020700b40016070201c480d50046c0212222100c00c2c003e801951208003c8181c003419461180f900080880c0562030901e84040f420300401280344018030078135045210702c41d0f41001040c0c1c035002000f40c1250680040d9a41c8403000180801e90301c0700c01c0bc600380c6400c2800104613030307604aa204200e401c402c58400780d50742d641000e004006410b845074000b01500c000f580c10100000c3e540110700610b070400c156116000b160300400c64443d00302441c1500a03450842c02c00071070500c100701d01038591003000d0240c20095600c5d1591345c107103030620340300e801a807201c0030030024429084000005040c810010f01a0316041400311703562014094802e5890540d0781d4210f100740441c43c0280e94002c00394000510010382e84841740c4000d91116600302904a00d40361001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 598072832 1250 598071582 598071629
    0xc02071a090609042009030d1e110a05030c06041502090d150f0f060e0603070f0e06010e03010912030b03010603030c06020c0c15030718081e01020c16 66
    0x103080ca1802100e4500701c0309109000c003a4004003016600103440b102c0c960721021404d07079800a1007650b12080340c0c6a942c10010503291120080150003440090000b0618888031203026410603081c60030234080707400d61081c2c0c480c03a00f403402401800d00d020204009201041c046182802a13000e117242c0d031884002c1c1e2101c08101c0c03103806000e40d8080040d043c00f00010ba0140606204c00100c560001000c81d0700c0707208501583c3c0340203280008a80d403a041408860382c2c1c5003850340c0106080c1d00810301d0301c2c1040d001c2034010b5114054103614540003000940702d40c1c132a01c2100f42c10b00026000b0322141e40d0a2600d10500d03000044810080303414414162807a040500c142401c403501030703854a6503101103464848c0254005104040c190240300d03046280f40c0c5a240c5103110701c9466a02c150355130701d4190300050240303000055140a00b40d1701841008040000501200c4a5148030720081980c0e0544801500a224014105401b40240c5518951074084c140810040720194001340080c0d0340c041200 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 598074082 1250 598072832 598072859
    0x10e0c0405060712050d020f0301030606080105060108243d02031c0f11030f0a090c0605090118060c110909032d07120f18051201060b0a030c0207 64
    0x11036400c64418070401000c121300c130071a03265001c01820b04074600030304406800140c0c1c0c40440042d000d581d0010040041058a02c03411005000c840000c110074203104000034140c100151509014451f00005000c0c4120224900c1c6401c0d800104a0325141d2004400c4501c4400048010303003400c00d01c1c8120003043c1c0c0c00200c004a00300c10030350141d460b0040c0404000c000b804c44d40094031800b56514240340079044284a41d07410360405440c041d44a18100320010340384000142002210341c10010100300003802541e1a100340c40c1030341412500c5022540040701c3c804106500940c080302c3d4001d00145160308500e180d8881030083c0c844848407040c45040c0315260b10140e4450b106035004008030090f024072403038000180714112405c00071000024100036119000b150083e5116601c00036420b03c45508600900d8001c00390342410b1180b0030100380c4250322030010f03210325409040c00314403402c1001000e42c0541c1c0941130300e200c41521031810080080041000380c441d10094400c602020a109080701d40 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 598075332 1250 598074082 598074089
    0x9041a03240703021308070905101211060c0c090f1e0f0105040905100606170a09020a050f030114090c0102010608070e01090f0b09070c021f02060c03091c0503010e0c04 74
    0x1d0100c09030700e0769030044000754000d4070000400031480501082406d41404910000e0041c010041503078107001040c4905641b0319408203a41e0f21901c00354600090500d40250601d80046034916100c00e009120b160602d503502609a40c010304450070405114080803e950050f1886036403070822001210a4121203501659005080d40b00301300100107524091b004150301510810a4401080c420030a00060f552240c111038007050864810094080840700020340c0b002105200f030024400940100da00240707503005640c011452902c03420308030b84094200c0b11035046404100c81036807030030f030710250b85807208035440d01d0040d400e141c00015048000500303601581d03008180700d000399103444c04080c000e01c0049042c08038140c5070708000305950303291034050b4030613005a110858040040c2c810800303c03c40c21140c00d2035014058600501c41035000811550000e0700765906556034440047e80352130300b1440307400429440d000c1da411221959100d80514104c40480c03141c0c951079110526010040e0280c2d00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 598076582 1250 598075332 598075393
    0x6061002031603140307080f0c0a170604021902010e011103010e0f0a1416031407171005030102040308210106050a18090c030209120105040209130809041a03 69
    0x5010200301e0030484900c460b074482e0600c14500c2c4600c07003041d10340b500116040c801041c0507004001c10343d025142038035406450041d13480d00e000003448010f0a8541c06800f15480070000c800091042e17269030381101c403010000411140c212500c060024060030742049584690f5091050300000030940d0310680c2e041e140040c0c4080d510380e503a40305210851400418050182d92030755082c07220f030b51034076543e03a00a5640381000154905102e0b80070303080d9403e46407840755985a00c0104460103070300c903900c0340a0000580700c089060701d84100002d0700e01d0550700300c1a4194400500001004004401840500c4000e0400030044c507034501107280c0100c09200e03035004904c00300209840244100407100c0200d0b00380903507107200b039190000d0104070b901c00c400000100ba40043c0c0f8141c80d151184c2000100d40030b59000740a10b10740741d03010890341e04014100b500400c107180d0700d100404c40030070b080d5908440040d00400c01840d000c0c10202500300c000050a0103405000801a9503140c4144520340c1d58855a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 598077832 1250 598076582 598076587
    0x801020f0903011d190503090904030c051c0f0c110301020309010504170405010c11120601080f0f011b0e0604030501090f0b010608090a03080901200a090b04120303021312140606100203 81
    0x40c1241c80042440074041b04c59000801000b006035030f4031501c0e00e00480c020340e43e40d1041c0040e480e1583c07a1180d0100e81c0701d210820415034241607640074200103540911840c1c05140d044280c501921a44515003185901d9400481004241c07401540700364890303406100700c0040c002c00241420800d00c03c2d0b005440c0000e8400d61000c000c982c280039684019a030140c400d140c1702c0e03c8034800c141010001c1c0c00c9407d8541280d284c04883e100200100c0111a0b8840c00811840c8503821210001c41220760712001407182c011613505066565600b91001036420100070f00015070341d80b514841207203c0350002c0311b01040c0c0f040040380c664441c14101c1d1190944c40020100e00700b60307440c252408400100b1004c055901c3da2132144001d4800c3d04024242e0060300c1c0300e540c50f5174000300050308802454011881084050004101c46000081160240d0350581001680c4000c4d0016040a00503950009003688030351101c104200000390104041801034031040c0c0d45140c0b20f44c42040200c0c41084600c00050380b05 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 598079082 1250 598077832 598077853
    0x50f010c0c08031f030f2303122e090603030906030903080609040204020d02040303020c0f010c050a150213081014070c08030a0b090712140105061c060801020f0903011d 74
    0x4000e130415903421010303040e03103001c0d42c0c0d940348000c00c0340e1001c0c201c8170000e20703480000705080e06070514440f6407030540156007001405143c982100c100204030920010b462505c900c030340000740600901c8048902050404140c40d0014035001c5c04140c4821400200741d00300000d2241d12920520f201e40764184d44100305601c50780100540d12802500aa9000d40d080110b8805144148000c0c002588682c025000d4141d5440400403901040240603040c400a0982c1100286001c0340503003a0701c0d80007640181180304400c1d0300000380502002410f409101d42c0001c21946400102e8540c09501d0300018420761095490300c1c2ca1659040d0f079180007040d1785030411750000f0080005968044080c03000010349891900c001a00d954040c0c40500100740c50921403241d819043c00f035440250030309000c1107a1545400c021540c1c0d4410320090756017000d074080760a4011070309904a4402400310500035921040054680403481c0d101d0b03408070f4425840c2066010f0800c980c03200c01d80d1b80d040c940010303004007a103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 598080332 1250 598079082 598079101
    0x40b030a15050a090b040f02090f060304060939180b011b03080f0c0405150702010e090f0a0b09040f020d030504170a03030e2a03030903010603050f010c0c0803 70
    0x1c1d07003440c12a220201086607120044407400810150b940451092400c005110403503ca8040a001107801003024125945030b60595400b80102511030315a00d6035541800001132a098030020300211081006d4034803420941148011400c00042008a5001110304d008141e0150300c1800c0642c252214080d503140000c0e44131907425441814000b298000891684c0b901e10211034088012178040014840c0c41c1d0054000b0b1035202d2810880c1900c0d1600740300000c0e10307448180040340790503900000d9201c21a48242e40c0035001903c040c1500000f8202080d10b006041c0c02110300c19065440c0c804400d41500d4200b2105000310f81210710300315840311917002d210921007440010b400340300c000c11000507412007410700fa0403800c83e140058400740c12185402026140404031004640d13000792032080e109030348858040101808401610500821400400d0450103204141c0b40d1551801a0000c240040030500000072051703c1c00030800e0403001e130810b03072300c5070b9200c1c1000e8800e4070140006400d204 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 598081582 1250 598080332 598080341
    0x161101021204260d1a01050a1416050a03020c030d0c08030c0c12070804030b01060c0819120e030c0d02060c0714010b060d0c02300702060d0603030f020c0303040b030a 73
    0xd00e082c0075500c060b92402e8601d4010f500044c0c40700000340c1d507500d4940800d000110746403403d440c2460424500707455500e0041041050041c01c092401001505c41c100c000340b55400a4a250700500303880c43c91105040207501e50b00b034899540d020f805584448503249108038001d0301020741c40300c10641161600c440509054204100300c403498801c80d00c502c0c1b881341840c400750403c2c51140c0442e5594a0952409800a44041e8820340038003810b41040c070005001d440a846000070140b0304100d000d41c2c010000c981d94402e80036240c020600e000c0c6030047e070300c4010008120ba5525a411226070203580c20080383c1c4c0365000c884c40400c00c03600340f00300c800003035046100c8005265a0710002ca80007462500003201544281e85102f8920707a1090070300032054042c44500781121510120074490081c0d4809081420000580f00320360980001d0380303a045684000644042150290080200c0c903201d10b000780070350640007400000341c8118042c9170110b00d400000c80382a10748001e00c2c20b0841d15a000c62a0290 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 598082832 1250 598081582 598081613
    0x4210503040905091c080c0708070c0f09020d0501150c02010807020f19110904020604120f1707150504050a0204110d0507033204080a1205161101021204 67
    0x140820803001a419002d8020103010302c0d9440042d12145800703a0340c4003169150401c00609116912003040a01a000c005680b003050704420103507580c451074644151446115003119280b001d40103008900c40030140e018201581c5824800c20070b998a50750103c502e41003002c451800228541c01d824019403080502580003071850049440368101c549003117062291188a803000410140070407030503c0000303c06035101e1003003a2100180c41c10141c0104010b4466805240c4084545441d002c0030481c000d40040049904130250f96003a600c4c0000511203030b4046202a2945a40b1040c041c2600015110f0907000d282d0241c02800d403140c507036080c480030341755802f20100c40b00d10904c030901b0703030030310b00d004943c03203050641d40010b14105010b0f1810f00f0384010031345019600b880b45590b01f11080000c40f03019002504030f0015529114501000c586032218600c04c00b034214202014004003050400322100385040684900308140d007400c2116080b40541007040301a5122840400c0110f80000710b03400c1035 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 598084082 1250 598082832 598082843
    0xb030a03050c07090504060c0e1f0f090e090706080c0f0d09332f090f0307090504030206180c0d03020313030b090601050a0e01060503060102011b030906060b0421 71
    0xf11603540944c942150350480e400c0e02c00c59100c0c001c24a14503070002290101207011100f000c1c140c0d06003070605244402c41c10440c070600c07205140404200e4007401188000b810780c40182583c0c0d1400001690719114a48501ca01191001011405070000d6078151000851713030982141c20854129140c00c0034110000d0240d44038900303980d81d0140d88064482c4a4840401c2c41e10107241da1004500b0201202c4d0f95080c00981ca07040401200b41420307001740d04c00d01d80758101c021582c89880034800101450369242405525210f58680003c7d060703071542226101c2c0d4040d8007950640c0c0c1d20502103010012541480b41348941140d407203002d46107010b10a001600340248103c1e03080031a041302c08503c0202541003680c0003403202d801c010f110380d000c0116501401d81038880300a40c0d031408404403a004d0341805807405016000c000a83c941e4800d620020380380b01101a101c551119800c8080c0c024125541e00f40c681c0d0b802c1c2100815030307600c5c40046404039000c0c61003560b5201601154807088244042c0110341 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 598085332 1250 598084082 598084093
    0x140a0905330604030b04020f030d0219020a08030304030914060f0a0324080c040b18130f020904080415030b010219140f0d020d0207050a050f03031c0209040b040b030a03050c 76
    0xc0d03111070340940f000c0c600c902214241030400f80100010407101d02c50151280e0300016004000c5507010441e48101c11707458202c0030b0b80d14a94400908603038615003140c0310902c008802c00c01415032001120007240e400a001d002101c200c00244503561007034221b00c0280c440200003940603941309030b0102c44e10107025032100b0b06840c28408540c1003907440b40e00100f503a41c009441c0e004649400c2c0300300014101c00b15800c080d0130a802040840000703000f031003001030b920240c1441d010702001c540266403031070b030040280110389042c0c58600003580081c0a0b034038800c041e1100742040c1d00c0c028400c0e003a584505030000c254801c005210042ca210f441101140e2581010001d1000e03040e04100420714100c40b14013410304501000c0c0c000b403034101e841d1440307011580808410480340e00e800240a045d280240c0300a4440301e0310001181c034501c03820443e031050082400d1180c08210f040d90140000d00000c43d81480810344080410061300c4082264075070680240700d608000030f02030402080080700d034400303841 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 598086582 1250 598085332 598085431
    0xc09020f0d111312030912140708010b03070504090c03020d030210090803011d06032808160201083403020c030a080402010e1512271014090c1513140a0905 68
    0x41c100a003a07807222b20687c1d103c4d205000603241c00c0c0480405400140c400300100d82c902c0c1c075005118000d610000e0301904c802500441418800d220340c2901c042580405d101c650380c1c0c1d01e0603000582c002d1080c10540504204a446459480e500b01d600400004005021030440d1030074039080c00d0b0090910244003c00950545d0008401d100503050390b030007461208101020500000d00380030401000d1803541201ca00801c40004d202d24160401140401c2e40d000c604040b01c10264002e11481c103e5070348510002c600880c0c0c1940c0200201e124a1003a0f0707482c2141000001801080d42e044c0720043c002400a00403003a11002860700703d03902207000e00e10000c1000c0a6139000f200d407142151400c4468000c2d08007540310104501a110b00b41600d2581800c4d84c0c035002200b5174403019203e551510405024407240480e84615080e1201c041c1c01c20032103607885603150344005407400008080381c01882180c3e0b00184180080c450b1911502d80c4542c3c00029000e80e45040b4121130940f504c115400e200310b41102e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 598087832 1250 598086582 598086623
    0x100b130e1f0f0609060f1520010920010210150f0e010807120c031b05040203010b070302062d07090f090b1206040c09020f0d111312030912 61
    0x4a0a50030407040003442c0d0045010070310540c2d84a8200f03250031820003070200003004000713400c0c0c011a604101d02c0b9107040104041101d40000310b402c40300400a0150540e414110194020315140c1d01c82e082401040c104c4402d000c4050341c100d107000740541c0108100314000d00554100c4100c1c0e4042400c01c2e0a80c980350744061100600c1600075201c1c111074440148505641040103d010b001041c20040740100d055851f01064503942c040140528100b01c124140c1c4400c100511016040c000d00035501c82d0303103480d0001c49541142ea01600148269404070301c0043d90035101c0400e20360b456110001401d181c01ca082c41840c40a088007040181401001801d451051211400b03460303c84404100442e0040402840034a001802d0845410400c10b00c00058960072039602103c0c0c4034080544c8881ca64048400940036044011403900d04190003441c0300301d140c4005028501d005c100c0c14031901d031078808080e4034907404c0c00d002300450300744001031010349100340c400901e0794811751703540d041c0a1323114100 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 598089082 1250 598087832 598087873
    0x203120d060f0e040b01030809120f0102090a060311040b030601170f012c0711120f12090f150604020702040911040e0c011d0402040510080108100b130e 67
    0x219604507a90700d0090040e081d41100840042042d00540c203550304150f1500071120006100c02440f811000414084680b9480821440168008181c0e00e928080c640003602075070002c444d2500c504451000413405600030301c5129103441f810404541450300308104006103078000742c841030600c0001c1400071403140007200f08034401d482e041140840355140c00070103407005010300070074040304000e6100300f00104441a0f000d940980c80d46085c0c1c010302d0744441c0d89803c0c0f04017000d4214034901d0002c0c1c600a80242d000091000c6001071060116a80d2203d075040c0d120006201c80081e540c00c8018200001d00710f9940b60b540100c4020401464040140d000904607000c048084405074420300e078000d03243c609449400b115840620103480f80300311034000200007184007003003110400002c0e2065801602e4903410f4078045c000181c40c0e203601390141c002c05800c41900744103641c418441c4001d40340082000d8014103000903400b4220b840d6928042c880d0001420908142c0c2d4000d12402244600d8103114104 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 598090332 1250 598089082 598089097
    0xa020f0316090b040501050d02090f070e030a0303061e0305071401260601110606010e060c030d140a0c021203011403010f020d0e0708070305030403080c030919090b0904031b020312 79
    0x40000d0880020001e100545d041680420700c10b25021480700f001d41c484000065001014140802c03040c1d40d00340041e0360700e260000e840c42e010f1203a48070341010190107034800703410703039251000c0444a9542140038803100010390000909540288008210101c0c42c1805045000414184080703a9034420f0964080d18421741e0031a51100000009e008081d601301825802221151010305071b2490500c0000c1c00e06a0b42000c3c3c18010040007440b8030101d1020b0040c2c4642600214060200d04000d504111240406440540c1c10b1031503c802d0304c12560000480d00d10303614004003400c0c250380c0b800c03103902000b010f203045054240d500c54403e400350100c40d200504800070360110008180358010303035491a01442d900706510a503c06d54040c00401c1d00001902c049075885030666039600d00e11100f080c15409100112600004003501015480725200f00e139806407040745504008070301040c1d0800c00000c030141c8000d0049106901c240240040135044c81001d42c0c00981140d0301c1e0b00e030075500c0c98144d500908 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 598091582 1250 598090332 598090349
    0x23030a08040b07030e06150d020301020d060303080906100e040f051c030b032d03070f050a02010f080f18010908070f1e050c0f0f0303070c030506010501050c0a020f0316 74
    0x408110400ca9002e0030b003500903085203020000e44040300a0a41c1e0303980003511000e01c002e8111861500ca40e54000c2c06401e10750b0141c001d40d150f45444510201a1086020480c0130908100000b840d0031030001c1c8091140d440d008541c0c4d000c5241c01c0240c41420740140041d00d000c2d41c1c201c0c08001180307041244600100211920301110f2407584002000c903840d900031517120360000d4185200c0300700c00516203d40800001c10840c2080c06001c1c9843c6140304008005000c4415901a0420710101180843c4164000c3e256109200c0364484100d84c5403204036810804041018040307440909013028a54cd102c40401c0001018040c80d01d40303000a0300310710310071140c141216103440104035040c4405061580c40741c4d039124071000075550340c54450002c0c044940c019074016455407902c1d6521101d400707d404001e4240ca42c0c4241e07500b8040c0c1071000710700098905114400000400703500c9003040f40d05500c0d402d809481c00c5010b03a420099140c440c003040b158107106080b0f1183c500741495018400418048 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 598092832 1250 598091582 598091597
    0xc01180b180f01030c020a061d060c0405090a0b030a030810080712021503010605040e27010f0c2f010204150906020f0109020d0605070c05010219030b0a08030723030a 73
    0x40c00c210100c20b22068150416042c0a15404560317000a8140b103410f44c0000041140990100c51058804030701ca4144028401c0d207042c03103018450305009000342c030400d40f2100034550b580d480000a4034100e50398150541d0000c0000008a4801e91001e030300014811800d4001542da040b00ca440c2c058103401c06125042c00804500031894010014002005006511401e542c900700f009000e03030099205401742841c8600c00a0700b084c02003511240c4030308030801c4220700000d8041c0d409008120000c60500614640b680c1002454000c44a10b076141e0340d02c030300e00b5a02884225402c441201c1d4580c00c40d400d90340034000481c032032807403071000c3c403020085603501510189806c40083c603008072101c406038141d2500c843c1101588035912066025070300003201103629101c0d04801c032000441c8540c0a0301c503510100e050130031180b201190003c503010300e6a090000083c91001c04c55409441e2080510395801044001d0001c0c1444a034040300d03245600c05502e90000000e6540e04592102ca40030700002c184 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 598094082 1250 598092832 598092877
    0x80a020711041a060d0b030f0616050c030d0501060905090a201c0908090307090212130302031215040b0108060f0f0a0f080703060c020a0f0b1f030f230c01180b 70
    0x80082c4654603013818000c0030300c0d02b40315500700d5001907461800004c00c080000d2180e0041710800460343c1041001204016560b1b44500081600c8924040c803032003481268049004000c66000d2000034100440c100729105003080488a62640003030207411410f25504c1025002c0f01c000d12a00c00190301812009950744405001c040c102215600103060403072040c00800650a4002022035000300e4054100300c602d40306040c141e1540c0190f0b43c01c4040c0300008810496110364031103c1501841c0107840c14005403010400548030484c00f1101950400c425285c85041403070192844c60091001801c4100b001d500d42c4140000d0f41001d0b0040c41203584880b000301704001103403169601c0340c0c00380d02c050540750300d85a0351641140e0310100e020307040000100214a2008007010324010804402e0415170781142d81c0d00e046030751007100ca103003507424884000440020141400c101c0a01d540024050000602807800640b521b02101180e8031500703040c800301151001c020b00003480b0000e80000e040c1202d206 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 598095332 1250 598094082 598094089
    0x1308100c032306060904090b0a060f14030c0d020a030b070315061e0f2c1806060304080d0212091608030906121f030c06080a020711041a060d0b 63
    0x1d05014525507501421082c410380700032000c486421000441c2c0b450340e542e13200c2c400130700607005010018101d00110020311440304825070096049500303d02110810507a2110703001c0c84400c01043d00d54060300000c821155500e03001d400b280e5803034170051804510503185d0f150310405480c12100c810200e5a648172280011105444c0c51004000341c1c0341031160703003140c0500c1305461040035001105110222100c91340e118020744041e404018211194185a02040c0001003500321100d00c04c0d0062410074184880d000003030b00024030403e806040c9903c0c1da20b6560790b0a02c0740d41f01e248800a00c560a109082c01d05404100746030180c05140b00404a46c1d000000d9241022603a80c4030341800d5004001e02c0e2501d44900c01900e106614100034545179682e400c0da294403040f1480080080d03480e5000000c820494aa0140419541d6035500c82142d6503c0003c00000c91041217005040e9007283d262a405c2c178509504922041c0548551904018071440042111078110800154040b41c40340c04d002d04504 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 598096582 1250 598095332 598095341
    0x30f0d0203040612060f03030819051023030a02060c0106030203010c03050901050907030b0610140f030906090106180218090f0603150f0106270e1603090213021308100c03 75
    0x803100e603040080350b14009044046c2e41c81c0344002014000c0440c0010341e0b2200090074010058510702041c4030910b41141c4c1203044018034040c00d842506c0300001c50328030295202010004160181c018078580c0925000c119040d00107028a4180b503484046c044010780f42805024074403461a20701003214100621a182500c1c00248003010603802680104080703908103000a4200905883d0000d10b00c01c1d16000f2140c036a4840e58044100c031001581d1a034082d01e010041d80300b10420300548490361607803040282030f58003a100d034440351400e1411641003544140e00909400c0f013180985111a101d8001080c81d0300c1040754031401e40e200700810800729050a21003014000c20308001c4201f03a140c0032031220350082c0b0600a080402010390714501c0009a0300155414241c005038800300390907515440d1030f612000c11280002c03032002c1203543c1d11071305000340100903082e5401010401840321000680000b508152590b41848980c070388001601001070141d481c0c410f20340c0b0404a007035804000080c05a4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 598097832 1250 598096582 598096607
    0x21f05090f0108070f270e070e10022e150f1a040b0a0302070807050d1b211b06060305240a0f0908120603100608120306030f0d02030406 60
    0x401d0010404c00380e541d003c0306140b41500f240c00e1120700000390400e4818405800600302105109644000c42c50341c0410300900d208064036551405500c0e086000c0c0141d0f003161428400150b481070901c41420400e4920348030100c24403c0c00000d0030482d0b140c2502c1952200e181030324071009490400c5c09070140316400305019024018210000002401001c1607910551040b01d2444e2804280004220710030340440d21500c1d045110280c07a0300f614207060782c81d0017944200c00c005c600008034026000660284c0c14101c0c1e40c01950f030000c0d010180803111420786c0c81c84407101c2000841003800070080d01a06055030050300030100010340c0740c02c5143c81443c0c80e40c1a902610321001540c0c0205203d21014803040d8412002100468910040d40d01c0001400e55020007c1034203034040f80030744100141104241c807681c1c040b4125000541101401c10031522180900c4102c1d070070550041c0301c1c840308200110340000001d011901c1410320782c00c1c80d60900804424030001a0000a001c00181d0b91241064208 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 598099082 1250 598097832 598097837
    0x6050a030b090f0402100f02030a0318020d08030f100b071202120c0106290915091c031d03030313020310020409061703120a05070302090910090e011505010c021f05090f01 75
    0x741c07041c7c0e0195503030140f200c03044201a19118102d41c4144501074200d68180d015080c0c041501e403038500b0340c41c150011601062005145000540c4840d00381c5005000c0f1010401d1007403138615962240c0c20b40310840180381003588100c444402002c200000108141c0031040000a280e0303080200c04400144003654000d1403c100841d4507030381109910403591141000c40d50000f10751520400484280500501d00c0d9018210840c0303805aa0300d200701d40c40351540b00317907102200b10949904d03022400308081445500f65109200190110b040710b40920100780c0000d0490f0380d25000c200102080e80d225820500390552509020424800180940944886032101841c104004040848644500107140480a0b030300d4201041c0c003240a41d045441a041c05030640500d80ba0500e00d50040022902c0341414051400c416031070402418071990689510404420a03034618100044a45408400f03050343d0120656a9843c0040030014107034075403524613291252503d1601080110141c10300c0c450905 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 598100332 1250 598099082 598099097
    0x61201061d030f2d0d0504050f0907080117031608090f0a030305031f0302101829090114031602070501030e1f020d020a03020d0f0209030706050a030b090f040210 71
    0xf82c03050108880b66184800041c0d6203000d2540206000d5020700001d1448281c0100c1315404401c0f0b50200041c0265481501d00008000703842c81405014207044803e100000c0b61100140556030845000d801030700c9200c001c4078102240009480e05c10303260507038101c48070140026200d0560408021542c15440125686002c003441c41e10041c166101c000c0c04526a0a903e404100003004411034120186130040d01034039a0303054141024000c607145140c2c0e10146a408000041d0300c000003100b200c4404080c0800303418250480c00000c0c5150040d203000c505000d0780c03010000c05a00707024091442650034010b00e2200e18543da1000e81401d0481c0c221504250406211503e41100080d1f02c00500101201d01404810f9505030380780240030302b0031100d9050703000280b8211020781c150058258400003900801c0b0003075010312501d0407482482001a010340280c601000528007540280115400030f0501081d0441c0280c00142014803c503258590301900e10180029270800c48840b048422440c10b1282 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 598101582 1250 598100332 598100353
    0x6030614040e0d0e010c0f2019030605090705060c1005060906010f0e010c020a08160807060e06070f06020d020d2316022a030d0305060a030201030902061201061d03 72
    0x140c031a4059040c0c02c003448814441380d11142d105150000903640c2100c442c1d48003600c03501d00000255000240c00031080032030522010246425400c170180c580309c038103141c0b000320320315510b45000c0d080050041b1140d0058410000d02e5480e100014101611080e02419000800c03401c900100c880161140d80074292030801c12980ba604100001c03038980c16803d200e1000680040101c03940c540c1108020b4010240a90000d03603c00c0015154442c4456031124810254488040c07641c1c0b807020f8441d000015030410010b1846003401d40c003c00c0301a0040c050012180055211402a41d224915011402c3e0340000d2070440c000c00e0384683c0401080c0445c2c0d44981000381540319661440280004c0c844070043d6240c80c009900030001010031000ca135204002101071460310001500100345a2406070041100d100e10082c428441e4034070411004010608807070642d0011001808117481c200e8208804101d0641d089a001c100c80d4002e02099a40c8407038170f04c00790302c0511000310704a0811b0090303000c1007003403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 598102832 1250 598101582 598101611
    0x307240f090e13050d0f0f020f0a08030c0d020c0a11011e030e0a060608160501050703050d05040c08030310051302130b03040807142b0507060e01060f0603061404 71
    0x44201e440d541c0d03503805142c031495808034501a40340001052449100c800008461b00300900d40e401c40d001e92112200719032031000c143c1c0c454898008026860b0001406040050b51000203150170106d00003c0f1824011b100c0860012a40304100114055000036a06800c00000c00035250704000c0038a0070f0016007803507442c01180d0700100c0d0b0303c08084c1501c4280b82c1c03c20f071408228040c03e19402c0101030202c20764408032682c49451080f0304034414450004045110350003242107440e800e60665580340b0f001c08200d8010010030018000300c031000c031001030018501800b04040c5010306010540885090314000810100201500502640300d005014040349000b02030380480c2240c0050040303581c0c1e40d0b510326000c05c26200ea1075008040d5030501e0316404c800307000040ca0249070a44800040003400080e18990300588000c210200018000c0022070001841034000000d02007810001103507c07a1a0700520500300115002000040d503113480400c49241c1d51210b07850048416101080b4004002c60403 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 598104082 1250 598102832 598102847
    0x10c110a02090405010b04021201050a1e0920030108010b0109080f07050f0a15020604110f09130303090c0b0901090e09121b1207060c020f060a090606050307240f 71
    0x181c81036140b24001014840c0a401c820b019800080046640b244407540c54450f0b54001c1c06814001d03c8110300101d0001d6043c814002100124440ea00002c1d00d03009580001c2d1030b070780c0d6601200907140303503140d9200e1018070701450203089074400100391480760364001409603101d540a0030301036105d80d0142c00400c1c030104401003036460545003800405031503004200d00b00060380c4045200c10114200c6010154007080d11402148510403c202c244020b00c200800c02c40240e0b0381542c00801d0f000465200080129507803115803181c00c0128280b402c54031001080d480c564400102d905002621901669000c0805006030480301890310450818141c003a64a071075003400740c01103020000324035025003031142140c0d0303851000c0c9040702d40c02c16448080c0441600030300707021200c181c20f0000c4042003074000300f00c0070080c0f08100001c0801f682c1e44885c8002402c074540d801ea5007565525408100c0d6282030001001034641401546502d084008032001d513003408280036020456040808603250f40e12000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 598105332 1250 598104082 598104103
    0x150a0b09091f020c010e0d090602190b0a0b030a052b0207031505180a050a0311030a0f031d1e060c030c1e190903110111060c0304050703020a0602010e010c11 69
    0x50058940f424444c801c0e00605504041c2400c070300c00c0c000ba030040c072070707101000e10207448580c0c0c02d4405c02c20300400403440100c07200d03000400e151011400206804d02c01e80c01024070300341c01070455500a206888041c200080769922103443c44d800e0103141303d402c803440312000c008402ca200034803186207540c460711120b0083c00a4020407a13200c0000c9400394a81c1c1450311000d0701120305841840c4890b241c000d075140404403085000c1804214640707481c03d00030050b20008029030700c95100b000030040d070481c02001c1000702460b140102c4a40d00004540c2000b03005120024000140c051321010b1401c00c0c40c01900400d0000450010410011006581d03800d940e80442d10704904a03040c800910040541d0140345205440500c05085100069512060400c03c407070082254080c5251134070011154850040100c000079403041000c15250380192000b5540280a001607590254a03940003441d040c04542c48a40141e440d440f03510f06c0381c2400e04c503107070410405041840c81100309041c40e584074040583d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 598106582 1250 598105332 598105393
    0x20109060e030c090c070210020106140406140d080f1303020f060702010f1407151a0436081204060b030105060904120e091303170f0f0405150a0b0909 66
    0x40c04205000c048000791b03400c2a900402a0602c44c15406000f030080166101e0b807404184c0303020301000941414802e503000d442030074001801c00399284040c0101c1005a05080381d00070803c0001c9050040c46c032000d05034001d9a0b00300a2802c81c9140100b10b500d0025404583c40b89504221020050380c102e0445103140708075003400100300f030004e0380e8050345019007040a001140c0308259240301d040140d015240150502c07200e031900c00240c01c00e000440b40300540301c219000c0c03545600031401ca03406201c0311420348601c40002c401e50b056545e81016400c420981d10307401e04503509100800c1042d0040340c0c2100307030a9000300f255251185c00103042000c0504040d00c1004010200b0340708500c1021032142d40f14029002d0500e5050114480c4202c0c1c0a0500c00d4000803903c2d14030b480d8903a002e54049000e0001004118000e0b00d0b50113410140c0200604100c54500c41d00f80000d414070b0340c1124403481103000354000584031502d0414007030203003030042c50703a9419000050a0f45200412500d001411003100 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 598107832 1250 598106582 598106599
    0xc0905010f15050c01060314160602030d200d020403170c03030604021b0105010305070602150105090105060f040801050c03161e08150306011e080601140d02040f090f020109060e030c 80
    0x82c0c0003520355101d80360041e5259420600040f06012110541400e0b03c4100e1013181d203030050000b91806082218010070006030010051801e8240313490f0000f928040d903407218103001c00b00ca11906001da078070035242c12181c00d4010074201f003403046038165040a44107581d02945420500680c564407480010031040c0714560220324091001145810107120f640160002c0085507142d0402e80d683d50748d1032141c0b00051180410010301c3c01440074000d412580060702c4003145908103000c000c00d580214103c070601038400d11000031124000d0240a000d09161111145d03030741401c000089501080a84010a02c84c42110906200111741c0810741c4100080c64800344035110114443e076681c038040141c42e03040c800c080c0007103055003000b04080301e403604000c85207611035590800980c03501e40900c00c0344040084004040c500381081094040306070320040c000152200c298903240100e80c0d101c042500e814104200c81c000315600580c01c0e00c0035205508003d0b41152020780041d0fa1f8200101c04640150000b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 598109082 1250 598107832 598107869
    0x6010c0c0501180b160501110a170606070b070f1205090307061d030a05030603010b0f010512190608030d060e130f060207080a0809070f0501080403031a03190c0905010f 74
    0xa5041801820702404842e07034410742d005210800c0c10111350155815403902034954a070945c09030855a811800e6140e0907100d410300c4282b02c52400300104840c1c2c104004004090004114415042c456180d94449402000c4d00040040c02c1d0208403003c80f01480c0740c1400c0c0041c18200109907500e0580c081408070752000354000951251082c41d81c84101c512000c20710600307641d0848043c0d0300c5048250000c020100c07810042104541246e803c460210b80c0400c220b0003580107a10186a0290f03034030915500444491860004560f00c641c41001d00340c0010490464401450240700028030502c51a0b02c1141080801c1c4503114081c03440c02403120303120034207040801c0015015038560603004001c9a8a0f441d10f890f0160600700100c030301100034068582c0108000c056024040160399060b543c0000e50b54031944c0550052640d503d84d00c50141c46003000780f00990301005600b007501e11102e108107522000e46051410180745030024110981440010310030312072191400802c40c0c03003d040041120a4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 598110332 1250 598109082 598109117
    0x180a051e1225140c01030b0a14060307030912080103050120040618050612011701061805130b2502030f0f0a0c1a0f061c060c092c06010c0c0501 63
    0x100c0c1070000d108068240c0c9014a803000411345800300741d02a2800e0064030500b80400c070102101c0d0064255111040c01c0b00040e80c203019010350ba100b801c608000440480d035456403a010310b0240107d4000814100050041060030300a0200702610380c020400035a55030100c0004500842c061141003114058a240c1f08031400c4400400528002d490140d0341c4c41d605540f021416824001d099244c40e401d41002d8652005104250440f1b11a030081d102d1034030894228000360070701410700d029000c800010351010580e400348640c001c82d64820f8000405010b10b600d00e601c8003c00e81c010065400503c945030181d02d003d000c0700c410000d1200c0c3c55644c0c131400340003941c11582c1c0c10000f41100401003118400c036805d074041240100e91002480e201d5948000c200030103c50b0001c10025000c20050509000501d20307040b0f20841d180500784050030b40d4072100e000000c5000303103072610640c640d005140c0c035185c0c841c41007042e0014002e181c142c4030780c601c0b6102d1803007480084c840c4504000306805861030000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 598111582 1250 598110332 598110397
    0x706080705070c03113c190801020a02010606080408093c12071202060c072102010219200103020d180b06030601031208100306020d022101120209180a051e12 69
    0x2403a14980c1911f944401080f4001d410043da2800998602803011030854010794295201e02e03030160301140b5007a182c03000c0c028045100140c030b00f100c001d0040c0c81c0c88190b00e540c80e151810302c1c5050780c08107058040020400d00c203210051a03071054000507400d002080250b0300c200001c2d41c040e9521542c40a0441c2c00c0d61a1100d1a40f015182034101440500088500444001e00f02d000740e007194110442c041c60094112480c2d00020b0002080c1c00ca1030344889180401c02c3c014140504005061030880081c0d1015542d1101886030711003c0806607400b00f0170070341040c6411101c1500100802d605594035000d000ca480c80c1641d003401441c400207140074140002c0722014540c05a0300b551241c19900e503401c040d400424100e540c3c50b480c8810041c100940503810782c1280c4401d00c0341214008150244091440d0181c2040341c800020488200054010000580083c0c03046c0001c20745d40181c00c450700150f6104802d841d11a40010341041c00850242050b2022a0f045140d11281e880c07002e0200c0c203924 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 598112832 1250 598111582 598111609
    0x706141b0301140d1406090a03170f1914280501060c0b041e0b010806060904020a180b0a030b01080d08060d11061e0903010c020a050706080705070c03113c 68
    0x18451b610800c405d200b804141d07002101c1c400c1c1c80d00310f180c04041110700d0045100700d480078866100000003e40e40303820410100101490398000180b421814003801d01e000c1411030701405100001034580c00003642c400400300040c085000204410b506220000f02003480d84c3c0c1024040100030000b04090009002002803211039800d8078079482001850082c0f80d001c1c0902c02c410b01c0303028820005483c3c3c2824241c0e41e102e2980241424105800c2140c9001c42e40c2146202030130040c2d403824021400c0d01d41c91491009980984003800041d032621440d5883e0014900105041102071014400b203034966004402c3c280c2e9020703560009010546001c03800f140107454201e60300c8010b40d20300c6020701400b80010709480d64254000d0044d400c00d500160703994044c0c0040204168400d00e070401c0101c1c41400ca941d004409450680e02d08035036074983d42414038043e0003c1d241a20022010769007458002c1d42540c8420709030010071000440049141d50b00218807109a014600144070b0852580d03c0d1406100389 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 598114082 1250 598112832 598112873
    0x28050714421c05071b0203070303110705041805070602280f201203040e0f180717070509040503400312050f1e0706141b0301140d 57
    0x2041e0242d00001a00080d111007000c02c0e14100c10307840c444410100860000e8001c0c000b007541ca861564111840080c10840b900540612000461642e80d2801391803c18050f843c6462414113103030514500b85401035018005641c4861605400c0e04c80f03d00705105001e02c105c0642c0c0108035107090616091448403002003200003501403680d00002e6907645c5000340381c0300355040c0300141d0311a03010035540c2c40746005001481c82c100300000c50b0340c0703e001082d5610600d040c2031701075a4841035200600d0020349801441828000344404000e14038104000c200421085908001784c0c10261201922882240e08050a90b00ca6a19407042d10601d10b803500072220707405580141c517107207000007881c40744d850f0f02045401d071100d24007059600388034806031a4218401000e16140c1040a060b00d032032002c03d00710001510000703000360800318800381b00e010520004032404c0d030024a003c1c0d000c52003151600c2c0c210b20032044280014081c2070b01d0240f0b05418258184c840e20510129410022000c04101c0c5072800c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 598115332 1250 598114082 598114117
    0x9021615020705060a0b01171b0f120a09150203060a0515071412091c0c0b040501020c150f0904110c011d010606022805071442 56
    0x500c00d400340e0060650901a106a401e640c0b5030100c0b050694082ea64001d0020700c8030523540060346495050700782c00c40f028103800e00713041500b0788020340c0700d07041002c01d951101004070b000c055540360b2101d110340c00000d00004022003c05a5034160454202e171025038013540c1d0110028001c0c0e2142da841c01d014240007846400e151b0f5546000f208158041c0c40111041054840045052000014038070070404d80380b0101e5051100c0300302440748900c01c02840c0c203c580442d21305d140c04208075103400000f0701480c102c0e181d40ca40c00c04001a280641d580c010034081c1c1d0b0549107400c10b444411081d50a00103400b5000d940c0e0f407150b180024003070417090608406500c00040d5003445000150300040e1698041d011070300180645032101800c03904a84100009604195521019030610801560f0324102c25400b0342c03000c210b5034035900e10301445c1d50004407a9005a20390314580e4a05564044241025038a5100d02a401003807107004120110035060f01c2da14030814001e50342c907035003410b0ba500078034031120000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 598116582 1250 598115332 598115363
    0xc0f05012a020d051201091808030403020303040204050c280908120d050f0f0103030507030c120305040b0c1e03090a02090408030402090f010308160809030d021005150a090216 77
    0x141c1000d8072208500162095100c0312040d02d000300151a010503443c030b04843d540c0e1a0100e440003400b800d4515a40c00c1800640240014276110040c0d400346001e98000c64892400d403050008903080a0620740c60b6141c18400d001c0c030042a440388040d001e000030740b00e007003844c0301c42d5056a0001042d0441c10301c5004a007402611091110050002e9011011090002d9210000b244400e07070004e41d8070010783d1407102d0041c008a0700800041c5070140c803c2c5004a10044035440390300c0d40342d0000305644c000070b17101e00900051151070000203401100100c9030901e02500e11607008081419012403008107000440000c80100d010300c41450b40c0e039005800000c2b240b0317051030a040141c1c0203c0301240315905880118800c18580700d8814166075024407c02d00d004602954042d0381c3e0542c0004542a2038104140c01460310300f40501151461150001c4c00801d02101814056503401010180140c6519521300115640c440c8400101e40e5000c030016502d039030350300145000e0080202d0203004c0035003450101c0c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 598117832 1250 598116582 598116641
    0xf2402010e0d03090b07031814030405090a05060102070b0f070209090c040903080a0513080f2802100f09030801060818031215010206070206070318020915010f030501060c0f0501 78
    0x480721720514280119903100d40007601242d80d02031045584521084259001543c503114040b50b00303002354110390070300783d0b10000070341804e50880340c02e0080c03034450040c0549075070100004405440900720351400c200100000c081039005e510b0003e0300c2052006c0c041a607030b540600805500d030314003a2084c01906114100542068426100135419600d408001072100001100740040703254020261842c0c804030110114441e00032210551080742c80c1c41c607207107030200100104162850650040c0400c44c0e003621003e0100c1302c2e11965282864104141e01c00042d0b40103070700d00c1c1942c0c0181480c51160303c4004074242280041c9044100a11000078142c1445036480c601911031884104803183d9180c440d001287c43d100c0c1920f2103805a80440c001c80c5003140a41c000d0b03000a141c4284020114919400041c54014240c507034641000f5103184001103940d10610100401100c0c1c1000e22555142050040c1442404100900320b02142070380d800400800703410909800209610300518449400d104 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 598119082 1250 598117832 598117841
    0xc07030308070509100e030f0a06200310121b06080f0105011e0e1804080921030414061210260c10030e0307060b0a0f2402010e0d03 58
    0x10340101e802400040c0e48240318074100d8015040240102c03010210710041919048071203402c01e945805101d68204010780200641c0941c14081d030f0011500480400c3e1141e4500e035a003c1ca0032064408108200328440281181021601d00d450030b05489869414240d441110b0107801000600f0a40c400141142e84043c1590080500003411000350340d8907030040d1003034415992403200c50035018009485843c000e0545101d000806031190681c980312181a2030b988100b11821202204042907031091801d11802c08029502030b404281c00350b22051980d00e94a000718454140300030280645a82175840f102c085e1030210003c0c2221075041c2c00e050300c104e607841d01a4044c4a043d003002006580e82e803620840c2086030718003d6405041011000c405100245805030445410315803620710340c00c0c00700e50030001440c0107401414005401074030b44040082c2510164060903070340710445401e020340044482c410b41c0e0b60f000280d0518903420b07030f5001130380500035601c459039440c0030b98060311a666825411 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 598120332 1250 598119082 598119089
    0xc03010608160c060b030f25061704110a0b0a0309050c01020102130611071e060e0f0913050c030706020a0605010e04030804260d060e09210d110c07 65
    0xa41e010385550702040e02800001601402c400a80d1000035000440c05540c40303242240c6010342510880104118214542580000703100b030b443c0280c039400702061815144072400350140d4588681c0100c0006441040270310050006800d6a4503100d0711902540c072881c07164010104110b41c181c0f100103080b00a4024100e0000c1581d036030007a40b00c00c0003650301c18800c5800602c040380550956606080b411141403210265825646c880c1e03a6000c00c2c80c2c0b800007099444103c0c2e401400d0142c500700900140910000341d006030046070100942e04081e602d524041d41d203e000c45010801c0132010342052031038107100d1400c00b07426001d101c1c40440c1c402d80c0800d07081030b4079000b0f240a202c1a6070303440403000180801c9901800140c0a00045000038a44c0080a014040f181e14540b000b21456441007800c4d510403051700d01102d503650380800429080ca0380700f96000c12000e016012040c890000e86d9104203164080048101c00060359818000266200b403519180b44080e06032a041c00d00401943e5404501 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 598121582 1250 598120332 598120337
    0x3090509060108160e0303090409050f15150f0f0a030c0501031103010e040b1317030a05011d060f0a080610030c08070612151e060e010914090a140c030106 68
    0x4001076825406240007601448a405407080030181440c0c08039800b40803a034090351b150004000c1041642c3e6039004845241e80a2000303000d0009641107540e2500c0344008604040d19043c404000b9641050711426003803000c1501c10074001c40c0c01000049020140c1d04401d948900744000210500c0750300201141074074406e0302e0811800d031a0003030080450100344a1a80c2010341c5100180000c0c001201c02030300496810600104204a583c500191102080040e070b0940c00200030003c4140060092a004241152601000301500b03425000301e100d000b00124096800c00c10446820b0300d8041002009109440940740c00e420011401e0400300f41510080e40c00c684504404281d0900229024040780c1040e11000400c2d140165180040e021940b140e81e5003500d260720019410721002107803c600201035030380020141c00c20001030074220fa28005c03a8100b00381e904040c08000503d18140810460484100d201da548140800000e040d00c800c03002d11010280007408000c04020000d18103854054 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 598122832 1250 598121582 598121599
    0xd0c11060a150b0d0e0706110c0a1203110f01060b040306110f0d09050a06140402090a060602030906070c17030a080f10030813050907090303020c0a080d12020412030905 74
    0x141940340580d002419200200c0c0300691041002000800040c000800b13901c50118100c14405005410050590320201c00301c0d41c809141c144800c0b003809840001c2130111a8079070440d007003080a03420130000701c000a00f0300490031707000c0c661000d0030402c00a14460f0000240001611542200313100e400901c0f085403c0c5040c40cbc4c2c095480d105440070b0741d1555030308002c20382c1002c40f000408406000040000e4070680903a0134000081405030156151001c2d0481507076110341414410b0000710f140c01000100c145280c82e6042c400c8a43c084111004080c04980c0580c4a424500f46008c080a8650101d034240c0c1303070f019a00b01a00c40220203054201c0190701d810459560f111010403c45100b1612440c50062000e010b00c0050502c0c00036054000c4042002d4220f036071038102281c4511340c00d039080d0740418150242003040503070410044400c1301c02610588840341c60100702d680d40342d07039440b0b400c018860542d4842e003100a456042c3c80042c8003500da070f51b41159007414060401c3e5001e0080314041c8054 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 598124082 1250 598122832 598122841
    0x1180f0e1f02030403080c030a0b040216020f0a0b0a0f02100e06240f0409060b09040605060f0d02030307080a1103030106030903081501020d0f020703300224040201050d0c1106 77
    0x700d109481c8030344e03050b84036181a9070b1410302c24103565000504200780a03964601100c1d40c1d44440c4050910740074200b00d00554101240104580d9266000202d4414510100b051000e0092903060350180c441c00d080c00c0000c03990b001c00a0342801c40c0860848241ca2900c03008414841703001a8883c003451038540c2007000d89006a00d9041540742c400c6189030060400d030129041414543d103c3c8002c0d43c020a0001001030446001854440080d14142c49141d15501031000302c0c81c3c079009074666111301729504210740c9290740c00700b0b403240105400903200b64004200341054901600080d03158003210810b8990341d40c1c6a440150040a01c00000d90002d80c8100000d800d03081341c5c4905500d1404141c0040c041c450b003960301160070381c02d841502000c40c0521040000054074a40500c903001100090000c0120040d100c04c107004000c80102c50219440f4a00c0254144541d0001030600e554414101c0360603039541c001610381c2d1082038801c140085c03820044002c01b070380c8002000103005c018810b0754980c0d1217 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 598125332 1250 598124082 598124143
    0x318120c140d170a12020a0804050c010903030909050a140103080c0106170307170d0606030b190f0e0604060522050c0c1209190308030109060506040e01180f0e 70
    0x11031910042c1943c000e15010f003c410741050140098581901c0d2002480071804580c0c016030300b2800b01d0402190b210401e01c410080c080c4040c0200400030f18140c140103140d0348004143d00c80920448c400740c0d55940200e0300e01c4040313801108243c8030346401e90169503074034901156194811840b03400b482d4a4a940802c115a03c040e0710403441007200e0041d0308220940e00c40b00c03204407421000c2c140d584410061980c20a8a50048200804403a1000180fa000003003d0181f14281050590340d8100410800d00000c5051005041605c02141d0210304030342d40c00300810000d04141d04401c2d8001c2064a540e507081b80d0104920a1440d2480d20034070241d2241030312042d644c001c180c41014580c0040c1d443c0c0c00d0300c2d0400009051900c00060450000201c440c5030100202101e40013640c071000d0000040c40910f5a9010300b80050200341c60700d0745010320b030800c9031010310418090000d04072010b1402803462006608140074142c4019020000748030b01c03156066440d90442c03020400b03450b15101c550a07160 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 598126582 1250 598125332 598125349
    0x6150607030806120705100c02011e050a1409090c030a0c080124020c06040611060108031309020d150f0503010608060903221a030a0b0d03020a0318120c14 68
    0x50389030302c41c0e000c0ea803248030400c550403e02500342010b9124030400010155503128400700c0b80041070f150614010f249000041400c06000c61103602c102910341c1d000110b661040c00c89001200610f458280c1410301d844050192040204041e030200075030f400d1100c200c10743c40045001d90400300040010300322502d010788404109114400061007038082902c40c2c0e211000302c44000640910540750403c180000107040c981145d0814000140c800c0e00900a6070b01c03c02003e4050907006000f0342c18419102c660508140307150060240007a000324608200e80b480d07400c1a00400c0d0501c00780c1c0c2265440e202e01e01811001442000d100b0741c24844001010007000c0340c00e6000d030440502445c648080000003240d274040729941c40c9181101040c0000d240744051015189240d400c2200580d20308020421030140c88810503c548109040300c1c01d44002390700040c01520442d4142010103050914007206030300c8050ba580074a14020550f1480c2e0300b000b8205020405071b030104c0d41d83c00700f80f00c842c80500a0300d0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 598127832 1250 598126582 598126597
    0xa02030a0f0c02100e0c040515030c09040f020402071509051c030c09150903050d08010e0f191104121a010b0702060f28020a03020601062c0301020f0705061506 70
    0x44e000b6070300c51070400d803050700106420241982250f580304001c0c0d01160845504403a10560341c1c2540b1199220380c1703400e21405204040845008000741820b03152414104031129000f446280d00050043c10400400c6401000701c01d03400b400c010000407814490307142c007e144580484240d80c1000308003020300a1003200c504500340da4a40114900700a107032407011070344d074100c003050010008000000410030000a448801796658490655140550510070355402401050050084404220511010a00310f20302d0201c843c1c80410311100740c1d94409802c5c4110b0f0003000f00b840000140c103051040d042080305000445495820907a0b80c1c0d2440c0d040507015a0b940223612035402c200e514a00200b40004d4140c52120080503030f1109844840051f074000340c0901d42c0d000d6002001c07000207054061040c0b0740100010304060038200d5007080204404d031080100c076054003444e48a80501f9840950654035106850f80c003d60795a101da06100396210f50484590000311241062050541005801d9400c0d4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 598129082 1250 598127832 598127837
    0x312080f011202060f0f03070c0c0503150f070c17071506060207060f02010b090a0e01051302011b0c03080408150907030804120f020d0809040e010203010e01030b18060a02030a0f0c 79
    0x10b00400e07402c01455600104000c09584401d20480e422000001d0007140140340e16150a161040503251181000b2660781c0980c0c405c0d00400015000c1c50b00030399207071360f100c0b01c4e41c500380d211540d601d541600c0c10102c1c10b42c0078114406075400340d0403001c0041c004142c1070f40101d01c0e8049041d402021582031720342e2400f4820050300182002c0200c2c900441101c0b25142c0c0034000401c10030701c06000300b010040200c0d0b09804203601c40c000726901d00020701c01c0340c1d00004494020405c0070b94640018040500da865030000c1c4030141c6810009001034240103102855103e2001503486a844602650b1540070303184001c190b595a0004c11401e500c0002c0d40c008a82d44100141c8c10b00f032400401615400c00103406959455284c83d500c801a560b010010002900c10704801d91103555801c24803007100c400208082891b17204000500640603030768802c90440f60f00104005d025a9000000791140500060301e8206104400a0022402c81c035005513103d840b405504110600550100c80700b5900442c440a01 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 598130332 1250 598129082 598129109
    0xf0c0f0e090c0a0807200706030e010515090c0c03120105010225030809061b060405011503021507030e190501180e0f06190b03180d090605130504060312080f01 70
    0xc8640160841c2c0d501c8401741c10100380e40000040170202d8103e02c01c0c5030080a400030801400f085402d48201d0b040c0f1a8010000c201c40c1c50050034000d946a003031680117104020700c000156100a00b202215680c09078581aa074541c1c0020050b40e080345001c7c01180e0140c0150300d00c08075004046800304582d0406c10402407a454919103030507002d0741c420420b554018404024014230441241c203480c0060708594024402c0f4030306070a000b402c4695180c2c04803d21803109104101503940c20b800406845040d0110075a0b41c2810300c2d0603150343d40041c40f429001400b0a90380d24009004104460071200203881c1d5030500f00c46c11030124580991360003070500b14501c03040030542d41c061803100c03158060409003821002094908640c407040741580d22100f4015000003c018820120715030031002a68154010b00513205e50303040280c4600c1260281c3c81c10000c2c04108880b01c03d0900c0c07200d4004040280041252070713100e0403c05e1080c1048a4081e0114000d040402d400e0b80c40da41d9814100c4840e1032803031a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 598131582 1250 598130332 598130347
    0x603090a0f17070308090d080705120c121608010617040b1905010f051c030905060a0e0411071208071b0f0803070906021b030a060207060f0c0f0e090c 66
    0x4900c030503003040540d41e207601050481d4082d0140d5008105041c000d49a1104502d007403a500f84c40c00c1d592030188010001c03c4010b01c031301c594004041e5a0303100e803442c030350701d07195940c80f0300040040c0115500d140d4030124440521280d41081307006000551819681c038112a80c0352442a81c0b045880356031240601d0000300014003280f61140c14540044c1041d54590b00030b500d4091860580390b00380c000084200c0c0e002c10411561420b0410014460031304000080811a2501d02030030b40318131442910f01030000010b20900785442a0034241410b030006204000403003400d030507a005030b08200400c8501044412149a00710300803070303007140304400e95075513003149030f10400300303d042c4101b0040201c0e1740c034518040d4600054040c1d4040e5105444640c0c0303134240f072898100002c1c500328000e4003901b180d460901c0f0340c00d01c6440204011040e99040400940c0d00d20700d61074400b00810711542d20b20807480c07505161a00032a130140c0f8030444034600e5503408400300300e080c2c10025611825641092a4a030401412 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 598132832 1250 598131582 598131593
    0x1060b340b130b0a05011508010f140a03060212060a050f0907110a0c14010225050411160302070f1e0311061e090307060f08041b09060e0a05060603090a 67
    0x1503030041c20440b001010100998403145000b800790b40c04a0300c00d441c3c80040c01109800d440c6841c58161603e0072005551401c0c1c81d0880c0b0ba0818090300440d0b000c10443c0c0c02c1d4039107440440b0b50066134030420841d0f035000814013a601540090301c10500c140010b0300005aa45081e02080041c071200400381040390b110490b040d02c0f000c3c06848030002c00d000d541c840802041400e841c00008014080410428120000c0028185520b44071b5040d031070000030700074840b000301070f4505400355142620009583d41080001706000d0003124020100880c9129424081542c0810450101c1d403508801c1d4906540310300400c40c0300001429080a5003004220800c0420003c0f9041010107001902c014548001174680c50001400d80d610a1006100061100070354181008020001d103180d290424031000d805000401a03880a08042c110000e1078000e21102c109464015000300342e0102c00f0090f041c3c3e180c5e80110001c80031229141a0343c03410300000c0560402d0b004607403140c2c4a24001d0103200c00c00b603840303 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 598134082 1250 598132832 598132853
    0x114010e0f091f08010905010606051201121a1e091903050706020706020f22060e010f02070e0112050106050a050a062006040605151e010f02030c01060b34 68
    0xc80c98030000d0314400701c28070343d0840c005015440f001140c0881541091400c3d00c8031030388840c1c01c0040410181501e80f915048807070643c0c0b11000c06040909442c1031003111000000c6482c4070381070344441400810a085c04c10044442c2c2c905103110b0a41e41c401c2d54507030312024400444015105070b6100c0c240003a1040c0010601940300b240e005042443c50307240c1c402280c10003d0407011303160002450b00303550f0a1900404044440c0c10115815850411200504003012043d0442c1800440350144820b06c1c024040c03070010702514440f003d41503a40303281203401200c2d407074402c0c4c40d40e5280c280d01150b1400c1c00a601e409484d0f005e05210000c5150040c112105ca18900b00c000500c0e0055041c02c008160900000d4003e601504001c14203041650141c3c1c203110540300b20600c9900c0c1c5980310410704500c02c1c0b50b030340e5000003401d040083c049c039242c0907800d40c4124001003400f5442c20f10080303100003011000e003945110b11190255025003042020882c5000768000b80b4908007105609070005002102 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 598135332 1250 598134082 598134091
    0x13020114280f180506090409022d01410d11130504050f0a05060d020301060e01150216050d150f1e0902130b1203030705030114010e0f09 60
    0x707000014485403a50000360070041d4180308000707455103500b45a501c1c0c0c84104081c120b107415082d540803d143c500019840d00c210011039002c2c03034450203440d00b59a00c1b0781d814041070454884840f409910191403100c808484414103010580c03040c1c03068081130f054074001d00d0302e000e28046441246c3d1802e0b000342c0054415080c5080d106401c1200040814450085400c103100710350009803a500d0990402e840100d040e04514000c600e45020005110001c10300305030805602000094252960000b0410390b1041c1100a03400d5820510000340401c8aa65514100d400c4420241400c1c0604001240c49d8031408005c00702c044800c503000e01039841e00030701d10301d84648a0b5038200362002076a80c9c3c1c58155640000721141d441d64460b002c2490082103070b2545003004812604000700c0120381d002030740c0c2e44072491350304080c180c6c1d40d042c060701a11013040d03021a10034801c0c201c07a12454195001059940240144407100c01004072000055028070200c0f6800b44008190905103001c0b1020710400100080 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 598136582 1250 598135332 598135357
    0x160e040f050a0b0601080c070b0a1512080301091103040201083c060a050f010212130f0b0c0c0103062d1511070509010506030612071d0f13020114 64
    0x44026000403401c0001682043c49003500a0443c5040c80014004100c01000c1d1100010308100841c005002100e1140d401300b560130000075030409458007899504941e40002446a03c030410030010720a0407400f4604a9001040c1400007a40f0110303001d29901003900c1c0240820072580214000d1a418403007805103440d2203620b00c3c4011159036031f40e00244007508080362240c1c0034005104090078038001d5030000d04010b8072921640140000000e541e010000e1020790f0110b03010130252400d02140955600800c10a4402462213440d005050419448040c070f0030035a02c0303401400080c650090040b00203e441c00400005c803815042107401c80209001ca4021103041c6103200455043d1004240000c1080160742d00301a41c9044480c02e484c000c0d41d1780105201d2444203004108030b035103c01c00c40740c0c003800c10303600d03802000030b4044610b2500c11075420102c0400c2139100301051401d00c1150243c070801e50f0440507a981c0d140c464504450094505019000858a001c615482000b400041c417010316a01e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 598137832 1250 598136582 598136603
    0x180f061213060c08040b06010207032006190302090a3809030f0c1002010b030a030e061309090605160f031a0307030b04060e160312050d020723160e04 66
    0x503074819007150a100f90110104000c00d0038403052101d40440c5640c0302400f030008140e42811612042d00d40101c8404054803019008000c409030b840e0041035850042500800c00d01c0d1b960103040150203500900d2400380241c0e400d4000050540d085030314040440c54080c42104020818801c2001200010400d43c14000080249000380c0e02e040110202950500c40a003060118030300c10058001d103621281c400316030602082072040c1d50049a40c42e4099417505240f40c103102010301069040c05440f1611900001c0d00ca00003c941e90302e82c004208a03803154000300a41d82c1d5117400c41000710701c1008050700240191065020b507074000d070b11680c08000352820481c105141f40000902d01a650381007150a000c45005220421415004041c4080c000300003410340843c4051703d440d04514a84400740c1400e62045c0c603881c40703034010706c00c4440554940b00c0640d510b402a04002840f01c00c00780c400b180c9001031000020404101150320440c201d002c4c42012449450f0000907400c0c5480548113490a40b0780 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 598139082 1250 598137832 598137871
    0x60d0209120705040e0c030c09070c170d140c0d1104050604140a0504090b0703020f120103050f100b0612150303070c030c0b1306030e070317180f0612 66
    0x5621882071a039014100502c0c5035420403082c001a9a010140030b2066481602c4183c410381c1c000c10704907100c030002d40d2000510780d607400d81150325032003510f4040c1071071541944201c400d18401c4010206514084006d01810300c01c02983c0c007816a0485041195040c240700c82142c040a80d007010010074940d822080c1025100d40003d64940e02540c85444240c03042c80a002540c204488001c000f450200d404210240c0701d51103408070014010158404c055002407510107400b0308000f50760b0040303129040c6403c50360312458090741d500d25115100445110340d01c1d032070403140b0850140b00c2e074003940680741c00e06260f10505510402040a030029142c00d10383c002c540031a40301000903120842c0502500c000322441c3d0305140c10300d810750382c00c82282407201300303c0b419000414030744a0080314010300e0b0001d040411554098142503054000070060083d1015000d16503c0890183c1074410480081c10303644030f00c8030108050008400c2d10150070a1080c000384820426000340c00da4000001e40d00010744003071 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 598140332 1250 598139082 598139089
    0xc0a1a270f0d02071805010e040b0c19051b010c090504090312052502030906070828051312020a061110060308070b1602060f0c1204060e21030402060d0209 68
    0x100011190050340454810048a44c80d03c0c65160954005e920810155043c5078a031134070800300a1000e024031460070b01140626030070310300315001c1500352003a1a0400d00f01100080c1182d1250310002014025500b00800030103040c8129052404c680d150450014944003d1001408544100341c041c406e00120402210080d400340d1803041d401000c21803400c0103001980c20208030030140c07107021075205002c0d041103a22014219004150002d424645540a202000d45400c0241a0f80c10300201410030a0b00c0791500500a42800e5081c0210107030003a0719410080f01014400101039841008110104545401445641020b044c00410b0b50440303404d050a54055039030300d90003190030341e00000d040000c1c403505c3c44100e070300107440500700000032814180080d600c940141c500e02212840a01003500c202c00c00e800c5500102c8030440712041460300381850801026a0400384a00d4000c0180405000780b600d42c00d00900f030030340754440d0b00f552529007d000781da0700306800340400c5030703401c000c11603043d50f = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 598141582 1250 598140332 598140343
    0x1706011d04140f0a061a03041104090203030c1006061b1728031b1e0207080a1407140a0315090c030605041719050306030c060c0a1a270f 60
    0x1082034140c21503900b88054220708854684e4000e0b146c203104c40011031005849031302181c0c0c000d030300003030209a901c0036100044c000f8075541000030361510000552551a1401094040d01264403140410010340d44042c140d40b1420001c10041c0c90b40102076190b000140d480b0b100300c01c0c0d00c1d0111075150525070400c000343d48541080c80441f10142800024076040d55050043e0380c4a0502e00003690096162180068420606003d5130045100d602c0f0080e05041d10801980008003002000c5130340242c03180c03d01e910400311820310030645004004011030101e020800c103960b6800094214083c480c6907869403070030b00002500b02000c058880e02420046807186e01990301850080c100020b00e800c0502d4005e0a04485450160394490148400380701490b240c1c2168064019604066940303a69207000a41846250420513500000204010b1f9054400041c03000300c09200340b03410702035829644540103045e1800c491301b07512140c0b00c1e00400300d00602001005079020340312081301c44000c0405501c0c3c0c10300 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 598142832 1250 598141582 598141591
    0xc030503070b150d0f0f080406050c12070506220b04150b19151403010e160201050606092b08220e2701050a020405011706011d0414 58
    0x2503201207507940901641c10707001074203c0900c003150000b0711410008200c000141c041c02804c10303102c5040c080309000070741c0d0280c1a59030307000d8100d0740d466454541c058080d41041001040602c5140b03006032100488030308542d41c00390000c004080613600c4a044004808000d94524103c204003107009002950b40660240a00d00c19000c1e5041ea482c1b180c1c41608589003290064420703590950111030310101408200103039981407500b01320f6844810340c1560414155031000e08444400030000404120008803e030050f50210403a820f605640384c401c030300b654000c0e01c2041c0d00c540708002c00c440914100350348600042842c0000e002c049c5651a03005110300c00044140e454260000d003003c2d842915004100040740e01628480b082c0741810449072042c44020403034a602504c990b01c2c842043e482848203608510410000c0c0540e250526440380030303421600c101030208401500a50f185011310391494410709060b55405003507001140085005030800b0071442d00599100d90f1030140113010105603118 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 598144082 1250 598142832 598142843
    0x190501021908040f080c01320c04061e0905030307300203030103110a051e09060906090402150d06060201140c0a082d09010b01121b08130c03 62
    0x1680400e9001104603a6088884020000d000b000c100000740d036110034900c10340c3c020355540c0e02c4041c1d04020070700500300b00103071380c500c061154803070980710341e10b00f20f5514089100000c0440d251107062144516010700c0c02603c020801c00002c40340c0300d20140603c01c41c89012450200f8000c0e560b03101003800d40c0e124401c19150314500d0403841c1c0f100508084910312440c072042e91420f002e85400c07402520303400306010090000f80c040d0b4610749190f482c3c1d400e99010300002080303401d40d0110103c108000980c0e6507038281c01100403800051007460807041c154465800a401b045455890fa404c02c040900860702004085000340807001c0d0750786451042402070402030300009814808141489801e881c0100810556141001000b401541c8002144c2d00404180800c03145008044a103100c2802150b68204050704c101301007081000054012280c19203081e00d841140360ba910540e1000d44124640b6014610040b9010035521881030101c564810252689908070710107694900404110030307030080e01c2 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 598145332 1250 598144082 598144087
    0x2030919030e06223c030b011818030e1c06050a06140603040f022101050c2709190b1306080d0305070c080c0102210118150302040203060319050102 65
    0x20740c4d0300c3c0060040060302a608001e54182012201007204d40004408803602104404070345000300a007a0a1401a41c1c0c03140e0428465a10392940c03040308400030340b486166a0510307100000b482c00092070602d11a0f0150780d40b815903070b5240140030500e50709602c492820b448000c1100041031461081d40e01641d070004c008107555242214103401d00b081340039194803c103010001d0000007442d2215545a5a0341600c810180f18242081443c0d0340340c00b04080310484d400e110803c03030f44186000041806681c181e10000045a0388010041e070080241c49064000b022a40402c14480052400702001c803c1c0c01d00c04241d480c513040110b03803c5d2245036107030000399443d94410b00903490b003404186008102d5140421075494000001031607030303d0601000d05913400010761031085800a404403800310400d104008102c035202c20341c800100500340300d4085200d00c10b07402c014803e0824003542400e425110040c2e10b00340d055400300301c002d41c009003000da0b041c82501e0108012262100c05000c415009130001038 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 598146582 1250 598145332 598145377
    0x702031b0f0c0109121419110a06050705060a0b0d080c030a0f08040b06060322050d0e0420091f120b0f1c05010f090506010f0902030919030e06 63
    0xa00d010b040260442c180040b0350800d0044445800406000a802041001c4040380c5503400b6401c240a507125004d410103800058400d01c44080c0302e00038074003425517420640c203030790f0001194580030b543d80c01049a0050710104d0781008ec50340040c0c4242d82e0080020080c000740c1c2d07582c550142e120303490f8072195400114440200c2908040446250446030624913980c7c500780d6203015410b10f00500380b81c460500030ac003081c072b072a0400e04a204241006400100c8010b400e0802030742d02d030011044c4000260392400c0d492001d0501c0c0c010003080441c1101d1244103268811031040c1030fa0824042c103600041c00203594507000f80d174440480b80746807403601e41c035481c040b07280c1c4020150342041542e680580c030380042c0c94140f80c80d81e014598412445661821003014245001805032400100716014a4102a980c800f80079003ca01e142c122038480141ea14800d035100c3c4110160b00086801c1d81494001992401d02e1180d000124082d1610070700d490b10456061348001920354102407156075140310b0119041 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 598147832 1250 598146582 598146613
    0x20718060e010509010b07120e09130b06030c101409040207080c0705031f05060d02210115080c0d05100615020c0a0e130501021606050f10120303050702031b 69
    0x120b0140c00156102a00b80d810207050002512815000800398600081c10a03191441245030a598040c014101140d904184d941d01010001c0d02c007060b81d400800a010800f64980003c1c0b4500c400c102030300e483c008000e180403c2d0354100003030303000d00a174000c104008081d40d41d5920042501038072038003a09490b0303400782d400705e442c1581c2c64021600035448903000e030702d001a8464000c0c05000c0b5501d00440c140e500c10340814606a010f00340250400ca14014034214141300d0024120b01401d024000c014648500300aa250203c1600c2284095040380c40c103504281440c6008411250091080300c068080340d02d95501200c4041e40002c07242451103803031402c010350500c10a0f01100d401c82e40000018100003250100c8000503009130344120304640154200a4207405035542e051201c0450000361844e414410090a001c0354604541159000001c20010000408409030381c0c8208001030a43c0303d03035400f940240700140a02041d880103106603840c6684102040d07404405d01b0001d06040007c11920 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 598149082 1250 598147832 598147859
    0x1204030825080c030c0c0f0102041a090a060f0c1236090b010c1e02040b191503061707090c030c05070f020105040f0905101202030606010c0302071806 66
    0x200080c104840050802142d20400d80e58002100b01c2e166907803a02d0700032051601e8807a2880b81001c500038031141c84c120400c10360251080f603159242003141101e0b0251496403a11544503400c1c0d111082100174049644540b0001c83c04110504005c441031081c4d0b2501503411211521030302c005080e812107901d400c0144421018503110401c45003031381c1c003080701c06184c90000a00a002d200e0b0b07a50050800c1c540c1c46034060300b400741d802403031022249003900c00016240d644020103a00442c20159400d0141c240100c03c10982411000c60130710321400e00e00c1e070081d0501041011401c254031200082000602c00c010712104107a0b840050038210710b0101c0c1001030f1510340c0103005c01e0514249040710300580103400c503502c0da40d000703c3e11520b40d0b003036100503074250256170484d10b00d42640403030210b180f031203650180e40580b4404809210260703460121100303002080400035050b40280011694550281c180040424442e0065603803403511624000f030b111070810842030f50709845d98020030449002500 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 598150332 1250 598149082 598149121
    0x6090603020c0d080606190201050f01060e030307030503070c15020702041109030703020d29180111122a18040e07050907050c0714040f05060f130212040308 69
    0x40940c2805803a10040d40c40f84443c0202c1c0d4180321303041d000900039036500346c1242c00c405060304004004030070601000b4001d19085842520441d600c07400401e085014884034280b5401c010021850714000303540440b030700d400103000401449162004400021a803d0000c1c800003164030700140c40e0b80f0b141c0100400c2e981410a03c0c15050010010100380b914045007810640c0c3c1c064400c035055840d14500542d482080b0a80c002c495a01c4030010f100c04502000140e01549900c00d98800507844109070310b00300c400c0704115003a00c1c20104140007a80c016851650303403101c440840414901c403100303007031080c100000100544410340000c0c00c0240441e00c407140002042c0c15101048200c0c2c0300080107035121280d004940c41210800009605a88160100e40358a00c0040541307400755034403c80c00700c80390b07030391901184214203180304440240803500c151489448010000306890664106210941e4400710071040c0c000c0c0c00700302c0e91204004561059000c3c61080e581e4201d18078200fa90ba9600762410729 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 598151582 1250 598150332 598150337
    0x60415020c0d0c060c05031c06080607050c0c092a030717040b06011b0501060305030310090213090c05090a0b0735090109031505011701090503070609020424060906 72
    0x550380701080790060501d050ba05282080d511103c01ca01b40f851450094401d00752070101c80c044055440c24468214800b01c58103601202d449440b81202030301d050282c1d041d5104107505c04203c18449244c094003640d0003003120400b401440c1c80600b07482103450000d00c18204240e20000c140507985a204513005030940c0d02d80501e500f00e062558550840300000b8280c2e41c1004030310030900014903240403940c80259403000003048070507071341d21341962a03800c11200c04054040e4410002a03d40b054000c03650042c49500c0f5881145061001440040000549203010020180a4011a91200c07541d410141105031402a00c0f40705901d8044400d640300b5202640829440c000014010707030300d00800c034100c1d040d45011a101d500070401250010242c1e8405030100036581030103089250142d200034140c40c80c49003e0a00d01d04d0100a9a080c0d4036081c40040203030b881040402c01042046c1e1002c1040f902c000d0000c030310b9062811613800c46010100034954103440c1d013030007005219000421003000f1710300c60 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 598152832 1250 598151582 598151599
    0x30207080d05040b160c08030313050114090a020d03230702150a08070521010b0304030e121e12190306141c050a0204110703020601081623060415020c 66
    0xc1300100500030101c8140c50004036004840404c030b500c0168502600a400c00c407900c1c1d16110100c4e5230313103200035842501c0d95440d10000600710008855480d01c910303440c0340107000e040381c5a424050b440030b101105030100b05410340f8045100741c010701c0342410240208180380e100c0c402070040025003090040d0074500450704000380131905410400d5a68018030038141151140e61859054105c043c1002a0050445a2000120380c5041c03070000b80d8059030081c0d03140d0002280f910240311950030403100c519200d501c459900780443c0c000003000d404464007041a80c0c02001c1019456407140c108201d41030049420f03000c4981c2155040c415140144100145240804100300c04102c07074100d91003500e900c000c0000b034502c00f0b0003c20400001002da028004200d000d8071541d4003082604483c004030010b008083c00011840340015034480e11018010305800c0152800c11800703402080701901c0c15034110860481401c1e5695000540020500c02c0581c00b070480301d01c1002030070256800c880a1086400d03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 598154082 1250 598152832 598152839
    0x302010e041a010c050c090403090e1003170a03020c120c160506180f0a03030306050f0405150105070512122205070b090a0320091b0909060d0f030207080d0504 70
    0x26803034252030001382801c0c66403007420300b840780c10603104020854001507030600748401c046d03012030410200c075211550034286481e007503035a40804011b440003401c0040d0241e03800103103035003450041110b0580ba0070014135044407460300d039040c00ca00a10798440c1d0390340461901854101032100003001801d00c0300708100300b03080400050b140e0140440c60300c00c0d5010b00070502001d40f50b49408994800006240c0d2258a60324a802809403030a801800d00880401031551058106400b845010380b03440341c2403407419100754004451316001300380103407034600c107214081200600060041250003d40c06098801b40b4200034141c4001c5640c5c0e03012905040702c0c1d080350003c983e003c152942503585032421b20341d880c4c04103c002220b0325010f40000d8580c1c0c41203c0148440e075100211603a0004041d513002001d582e803810f186c1b003a180c0c03210b1280c400344030820030400c00d07240c0440c04607801600107020015240550b160014103441b649411005644019400c0c449440f040014100e0f42d1100c1c5841c40c0341c9810b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 598155332 1250 598154082 598154111
    0x30506010809070b0d020403150c09121502030408070b040f020405150619050c100b1008060d0f08192003030705041a07080a1d0108010e0112051f060302010e04 70
    0x4144c031030f9110640c0081001030140b01c0580498004540190704038006101e5a8413007002071102c5004c80700810385519002070101c60154490401030b4000e200c184104541c440140c010350f20040c800c98001c0005c00c08400010f408001c41c3c0d01950003845e105098680900c184070841e40d020b0900860000040420740c030b03d83d681000c5980c80007c0d008608551015044151018001c01c40440c0c9035000300300810400010b6a80300f220002130482d007580b11007040e49010307a100305081e910140c202c1d00c00c94203880800c94211050b05030034458400140f401c50700340c8020321040c0508032044001a010103030008a80007081c2c0a80c0c4c051682c0c0084e41c0f0f0347c208071001a085100b030b4410105a58a48034618040c910450700fa14100f98100040c141e07901100c0100511000740c020301100d86002c070300c001c4006944940d5081d03050b90306014102540381d0070b15141c2003200b0307004141203901d48900c00109401420541034040d203d04140004254141148000b40c00e444034030900c24095842c10b40c40140300503 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 598156582 1250 598155332 598155343
    0xf0b06030a090309080d27050907110a080708030603010c0201110d0c0e1215010602030c0703030509040b211e0607030b01050f0a020c0a090b03060703020a050d0501080d030506010809 80
    0x1c07049003000540c2c0b03000b4038041c0d44180880e030051100d0b0080d14000d08041d40c02400300b10201d540200c400488110410340c528809002c0c0c043e050b00480003000254445010383c095080e4428500101e9031000c909584180d01580900012103100b000807040c802a82002d018050784010140001d204020044038451580d00a1102294145444d80c01c4050414020800c04c034800c4001741104120351000071407503548490b68111690360850900000500e42d20210580b0081c014000250400b20f156840c101c1e0355811602c00c990380140d82d524201196910104003082c448105a881b1880c0f000c8640c00034240b044600b26030342000340c0401000085c80d000700d400c5901ca11681000500c9100e07480040700c00b4054220540c80ad0710b0700090540c59660009090319034440210342d000d00594585800710152030380340034200d404d80d0200e00460001c9003e5009010b03071040c940390440c206100d081c50320082d14001e80c055921900305225555603980e2600840c0e5200800b070801d034500f400d06070035195951 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 598157832 1250 598156582 598156591
    0xc182c060c0906040302031207030f080705030712020f030a0903030506030102041202060d09050d050705071203020a121209030809250312051b0d0809211b010e100f0b0603 75
    0x101e6000544501582d150b00a560107181c000c3c1c2100d001004c040e000181c507911109054000c0355000003500700342c038810721549208440690703509055171194503041d9201403c00088030807098090002d07440c00401103015620400710a1004200070300941005003c23140d0181106010741d00400051241100f51004600c0d09581a21000d03900d440f134026050081956890082c81c1d8050352001218540e070090281402d2030084082e030ba401a40c0e0030040c46030003a501c0c001009a041512100c001c41c4101054482101081c20880d0510304c50141c0e10301102c10b020400c4003c2001e91092114100b000c0001c030b49a40302c1080010302c001d051071403501072a9401c0c0b100074403900c040d011010361580728100751481c0c1d0b540d404c00454010f01a030b00702c0e900c603003c0070982c03000034508000060350b03c0f0300001c3c06202081f03000255001202980c1224140e5482a2168407940c20324007032032010600c00f41f2070300301c49039000382c007406103246441c0a2400b074440802e1500c03441414047c1038840c55590a040741d822 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 598159082 1250 598157832 598157851
    0x30807030c09050d02130e0604150506040615081e0106180509040f08030901060e040b060108060306040c1a0f0c030a110c010914011107060801060e091b070c182c06 72
    0x6c107074000c20101a19820f000c0c0503007400b4a8040c00100941481d41c00e80039000a0030078451380d81c905091008072021807151076a6010380c43c00c455280b6002d4544150002c0351011000f0000d803280340803404d007a400707074840f03030015501c10f20600481605040340e5000d80400c4031030790554140b688940318002c030982d6000e0310300840000800d5020a003544036500900e070251a0705a1407804c0d05111a030248200c800f103001c1044000001d5075481d0108005104580c0039040300d0200341002d040c0b249620400b03c07007945a8404010300c509849030000904400080308009540c1d50001000c020101c0803610710000741a40445a004006e81c2c114a440d001d45079040015003410b580000101c54807240700c039907004c280c09115030100d44154000c0c6410705840d01a1a01003069a0310024000d00100450300b0500a01c860340418000459400c000c10265005220800c001a1505136410341c6440c2203102c03442c1d25686407400c440490721b00d802c0740b0361110106c200070b2201a540c29032544542c4001c148411 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 598160332 1250 598159082 598159099
    0x2010f0905061f12032102092d130501090e070f060807032901080c070f0b04080f030f0714190e030f12120c0705071a04030f030807030c09050d02 64
    0x40581103e18000018800b80718040740030003140c103024040840d1005060340e0b40c00e100e52154032402e40c900031101460b4000e409003480c84096003000d0305210306500c03c80000b10343c6064086103661400d8003840c4c200c0d240d101c00250f42d4942900b03882107c1c05101140240e13005a030081200395110121401182d940e0b0500d0042c9039140700007103000382170313084084210440c5064025001e060350f10b80380c801c0342800c0e00d5501e2a501c442054004c5805101c0c00202586194804180000c0042080e07503040381c4120b824504020b40b07102555010b4004882061140704900c0401070394980c40410a0126000c1c030a07005c0c0f4101c201e065407210000c54400c40c80c148140c0d1022203802d52010400c800100e120001035402080305a040310940c1d90040d2601060001040046001e4650603001c442505034094010054075141110f1300c41e400c4205908445014014080000815402220612014420fa07600d032202c1c80d0411014044802d4541d007481005210942404540c40d000c05e540f4580703030125403084 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 598161582 1250 598160332 598160371
    0x7030309050c0d061a03070f0303050705030724110906040504150e0702100b04140106120f050a05160903030914040f020a05030907060512010501050702030f010e0d02010f090506 78
    0x40c50a14800940c40c0c00a00f240c41c0c0c00103210056100c1801100c1403030303580c00d000e0160b41c101136880d00d0340d0090b00240c01d41e00764200300090050740249184c6115000b80c0341000c00c2520b4041c203400d02e244051540b07281101440c20b821145202d00000c0c003400340340181c2056282c10206099001c0d80c0152401242d80d00815420318808501c490700411200e1101c891902e00310030001e485001402e40355401c0d90402140c1985441c040c0102e9140542e981d41d820034070f80c031b089400c81e400c1c0f0b840a89003610307a507110100c12140529018941c441c2200000202d540e040020304000d0395002000d06c5020401034160500001c0e603c40d41141c00c90b800d41c0c1011455141c804005402404a0000000328602c00245942c5040e0040d016501c140b88801c161011155120426603952281d041098150700d0090010320040d1f000e640540041c90019086510710402c0a950030300b118902c9514400c5980682050550325074240100f406060b00340c0c80c2071001251315920349503107401c090701000c04645183d8045 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 598162832 1250 598161582 598161593
    0x140a0c120c050c010f0b03010c0e13050c13030507050f190608180f071406070308190f0f14060f031009051c080a050c030919150f06090e011107030309 66
    0x1644440fa14400070081610003001400081ca01400168025400c1142c2186202c1c050160401121809800e5154010407130200d40010580140803a131000ea06120f290a04403a80000d4009903108000504280c0d081c1400c1089652554013298802e802c4003c40310500b0907a103115800b120b0032400c00d02c1890310303000851081c010792040240e103d485000450290402c00240300310803158001810540030300d1a0f01480300c941318406000c2c02050006003c905c10709007117000d48207102d60f401d0000921441c001807200c01d4510b01201c3c0301d030107921802d6194101d900f10310003e41210741150940040c0c018103000c241c440c60b0486030210b6441d9500c01c10700501206000200b407040d51092082e4010b400404040c055000c203032a00308603540342070001032030400d04804590240c40d840008003c0141180e4113002c041c0001d2000311280004e04a8890b40d0809901400807910240c1c100490040d0800c000e160440303451506411040c0e04042c40aa15949400e00704c40a440c0c05143c045807030701090600 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 598164082 1250 598162832 598162837
    0x80c0d030e0409260d11070f0b0613060e0603161a16020901060503011a281107080718020307050703080c12040b0601030c0c02030601091a060d140a0c120c05 69
    0x8404281d13150441c600c80c0201550050195666400c001c01c10444226180701e01ca00030400001d1402e2885082100072594650440394003080040c40410f01c81441d5010348140c8906a212a18507408030081c015a4901170141445090740b03038002e8030803249844400000006003607a0881d06800c00249094000f1400c0410706c080c07038000e032001c211565103107401042c03540244500350000e00c0e6034031102079040310780c0c0131141c110801550701d160041d003915060521f03900791a045014070482c0e8180216010052003080d00034a000405460b501c2d180035400d0b110403145d04851a08103104000b00845030390800165520aa05440d00444950350700904250302e00c10420180ba5604140041004200c3d84a9200780300322030a80c1d00b0b00518030280001c1c0c1c0d602c03000c81d10003036041c1c11480052150001c1641f006041c0c01c10041040500400308021600b150301c100c4003400010344407140008100080748030a50010105d0004101004004070002c000013100350b10f010000e0303100c0c0c0b03403a00e505214505 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 598165332 1250 598164082 598164113
    0xa050403030846141f050f06030a0b0d060e0c0303040305030d0c110601090c03180c050108130b040b1602070e06041806020a0905030d09030302030f071b0b0301080c0d030e0409 77
    0x341003040004816444d407503148103c0d1501c180780302d10505d04121024040d004c0d01210302c058000e01030304094604010107900000c1104c0c900c256601e441c11032903510219001803407030140d0340015450b20041c02c071a003031107141100c45d4040e510400c010400130702c0000448240880c48900018000c0b48102c045031a0404901c1d010100d01ca12400404c030443c86921495440046450410108100b4040c0407050121000042c0c41c1203082401084954001c064056000340b0b11031001c4c00c1d000140d503a4400d8102c0903038041d15100314000410403440101c00004588040134002019414a40f5884d2151444001e204600807611303503010804001c524100c450201c4d038810303020354840d40300701401840f410075441030500c05d12904460f003141e103004508040507603816a0286290100031000035409a0040310708682800071403107291004030304000d2002c040d0294011869407549084034a520b0454035603c040d00c02c07280c0103d14000240c20030014601c240c016a400310313424405047c40c4904009211 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 598166582 1250 598165332 598165471
    0x20127080f0c160f060806090c040b0c0f120301210303020d0f0b180115030e0708030304030f020d0216170f010216210e06030c0f0a0504030308 63
    0x1540d90864880030408484480c3e20800c05291103030b0b500803d4601002a11030324012910050128a00e8103104200940c402e00410340a0b2800b40da40c00b41100903444405454a1504110078000e440c1d00180712581050034501c0c14a8199410a00e4810100030782d203111001d80860492000101402a01600c51060394410200683d1060403c0700380a81749011002c0d1080701c3c01400d030305503a14081c1c0b0303441c181d40c11407000055041419a05900801c411100400315102d81c1600040c4d03071404100451065220b5a581407680700c9148019241c10502c110b618255001011420344402800403007000700d0b103000c0b095441d018001a03800381054048429864654000694408100840340c06000c05500c07415290f5130703032042c10f01c520700e48525850030440003e8200c0c168078418035202c0c0203150002002c0c100186003055480c8441515031200e031501d000701c0c2010a08100b4103821480c2e4540c40100c0030382100d401ca161881035600e204510200700101103160004950718503005607403140103007104 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 598167832 1250 598166582 598166587
    0xa030b03011d16030c060c110a0303020102130e090318010e031b0112021e071a19060b0307140a020708060f100807060f0302161a07030c020127080f 65
    0x101004450800d034910032078000e128901d4403e080912500d640030483e80c110142c443c007941040c00c21209a07450306015a00c1c1800c510a4140c250348000100d4011442a00010780d90541d400c1403c2212903682d010301d00c10840c4104020045201104480e26800100304000c62003043c0001039844180329881681c040c4160802c4110b40d5400329101e41d03041900740c031503141e00c2450103002400e80c81030394403c0007200e00588842d250900c404014250310b41c42540d00e45140c0e010000c02400c0b03402c0855507000d404a100c8141101402203128001c0600100c241551840c5801c2c0800390400000010100c2c00d260006a40c0d80c1140c424031100e00585044415680709042099891170790030803e413611008000d0029001400d2100003820100700c400a03160324001e64081d050070780094200e051000c41940320141110001030090300b1000c0e110084050b146550f082400c0001c00b141e1000d0304910941e8506240d151290016643d82218103c0d204e45011290009192003004d501400310740000d0030002 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 598169082 1250 598167832 598167851
    0xc05041d01081c1d030f06090a3e030f0102040e0a0c090f03060903020c1201020c120f1803070b0a08040302010b0d150c0207230f090412050a030b0301 66
    0x2006005040316490b50840d07621480ca0080100440c58800380f0501140c142221100e551000740001031039402e00400340d8001e490601d45107410705108980310036060300200208020407a90b00d080c3c103000350511092403019201580103200e041251103400845a40c1c030031200c0c00642d410080400d40c001581c0c000e540799542c44e00f540c48031503000d483c0142041d0034080d00214a41c401c0701c46008031061410b803000d45c0c501e107803103060081201c51816021401181c800503080e803240c0c800841c990f0001c0e0700040e605c3c0841d8401a04045c1915458204450204250400c0000700d40c203641244041481142612460b280040c1c84d14403180d020380c2d040040881e0700750415401044e8988900c2c000e8000307100e240940701c00c101e8603108440005207400c0300408002e0582446502442c150421030040780d0742161208000304000204581150b00c540406443c00d50728184482103602154040e208031003c1d06041ea2001d88101d00801d0703010030000c3c0070640c1c03651203210740c02c080160740026000300b10714804c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 598170332 1250 598169082 598169129
    0x3010f1b0806040b0102060103021203071a04031701180f14041a010b090303030f060d0c0f080c010206270307201017070e06070506010b030a1b050406030c0504 70
    0x10358694120100d03a01000080071030425000300d0040c844141d0241070a41c1c00c0d0780c200f00741191000b265103501c0c4000e10800c400101c21524149070905000789154146c40c161a00903c01210900303039015000c0e050380100074618121207444003000f1600c81c00b083d00c042c3e04901d18001c000e00c59002004c190349405110a015400c3c004620307017400203803014502da0b25402c0309105d0340310b4020000d415610810004540505800b030041d0046c3c4000c000808082150302e88a45d100070307542005540c80070001c801c0048100c04c0100480c4d403102800075001c1c614000031501080c07800b0782c052074501c1c1c003200e8050f154040c041c8100c0c0e4070349038007041c03d8035601c482d614130320032120900660500a41c00344c18040c3c1000d0150099229034000b10561320110740d03810404844445a0380001c0d500540280031190000e601481014043e084145180ba16850b0004520b42541c0340c407990400217602c080103104c05071b41e0081c1150181d40003810081b80300f11600808840c1c40c4a55408803484035a600b100854001 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 598171582 1250 598170332 598170371
    0x60705010f0605011806080109020904020c1f0b010e0603130606050604080c09070518220e06060a0515030c0a09030c0b0310090b1305041703010f0317040312030203040203010f 77
    0x25420b1741d8040c0a0300c414401101e210802d40103410100342e140004010003006c0e0340041c07900c2d000241015051200c060402803030400962070700b0441c0e40e59000195110340040c03140400300c3e14246000381c288101e00012810500c000340c15115884004408a000d2150fa9000000203000240c41213a4607540c480782c03151211911200035204048902c080ba9016115505949685800306000804121110204120000c5414490703074860710078501d40140400d1840344580c207150300300c05003085107042030401400b04400e82090b880b44880c0400c009139040010142da40c000d541044082d914600c04100f51220815640010300e44c20700c148000c265911854041c50140316940070003a0034a40f200d03414003d41710091841074100d0300001d0500c045038840d0304070342d403c140184004640f12030304410740140703a8802d81140740800c1c901c26040040042d805082c421414140c0d907800e041504540c3c40d042d400d0110400da01c205034020000c1000d544d0207500030101c40c83d00032002c12011040b66050580c11 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 598172832 1250 598171582 598171589
    0x913360303060f050609041a1306081c020c010804061b09360c0c06180203070909080d09030509120f01150e06040203041505040308160c120806060705010f06 69
    0xe801c142c00010b01d11481ca01070f8040d904000c01c4281000b003080213000080014800d030103440b6802203e140004c1d00c5218100d4052845203d0100c4d00b141401401444d103001c445d500c8007513106500d2030060855000c20408024602464445c00300e446909040003d4409203403070140c4c0a064280b07038544107820444040841d1039695010300810306612500038000e81c0c507007904608c0c9982440c094004e032450381c041c08039104036051a5019103544d880d98411a454802c02c000302483c1c50302040d05518007000500c004202c913400c2400030114643d01d40046006907451041540d44070960041050301800c00c1d243e43e00c001424200501c02100303030103a40c840040c50f01881c0765107031517100c82a405400301a00140c1d032450040c8000d5440d410288802540003c100f81c80041d480c8016004012550089034010340c000c1da01c41e0a0340c1000038082c0f4914191104000078031424502c01c100261150b04c1d20814003d907402c102e001940e8140c085892072090038001030465181208038000707001d03180c0c480000d4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 598174082 1250 598172832 598172837
    0x1009052107060c020a05250f0b070209220f02060702060307120b030c1f020a3314070e01120207032304180b040b0915090a0209133603 59
    0x30f110091041e6201e4041c0c90001c3d100d90841840c074aa915a2489090074404010b5417a940d199581e000c100442c10064112045090340012800d080d482d01035041500b1600c20289103c059041e02e040c02042140d030f2030000c0c800743c0c000599006641ea00300641c0c0505801a0003140d03285010301c1c0040503c98190106501c01d40381098001007820006100d2030000c81c00790107000210171081c811080c525138010030200b18800c01c644540001c00000310034000764296040e4019035130101c001408185000592200d0391071405111305100070312400c04580246c4203087c541885c82c0d09500480d426180980003d06550000984004260340b101d0744141c40c19410400030000700c01d01140e50f055200b02d205003a011880500d88840030107895112940f44030008100048000f03001010502d2000100e81134004581c1c4c4d10780c0d40020f42400281c032a44108100401c5203040007500000780e007a1480c144040c00550f403080444080d20034501c944a055401d0b91989000990f0046e42100d108040c100c206d00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 598175332 1250 598174082 598174091
    0x114040b0a06060f0e210f03030103030219080901030903090504060b040302030106090228020708060a05180109080a1b020303191b0b040f1a0c0901090b04030203100905210706 77
    0x400a2240c0c4103840304c80c05507507407a0703c01c001741420800d100343c0011440008a03184a1484041c00b0204030f24080c0d00300a0001e591a513142d410081d046c52643c40071a41c0303a032001805031000511a004842c14040242400140f0100900701112006116085281c129180020200c2c940c0c0c641d40103002101e00c210001d01090351581e4103002a409140c645001c9a1600801010b10110144110032002200c1c4120b03198650784080841c945803065616082440e56101400000680541e202000042c118002d001d1569a65680e020610410302e1400420601c0d550400400701100f21440d41c0c02c1d00101102d0725900f844540d4842c40c0303c502407000100392025a8a0121420a508502c0e0a07400c00e050607242c0c0e0b03680c2c0300e02d50300c9112943c080303800c601c0380001d8250601c1c107852203500401d0265280d82d2603e900400150454000d030b000381d0180304003880200010303640082c40245022032803e01003210800352614074a00410304000c112480084140700c4503502a24025121081c000d400610 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 598176582 1250 598175332 598175339
    0x90b090c03122a1006140604050f12030f03010504060b0316051b03040311030c0a08061311100e0112200c0313150e0405040b0708070e1903060522060b030114040b0a06 73
    0x900c0406c0c9545030303800900c03d10080085141880c000800750300060500d14a01680d0784000e8216405140f012030700c0d100c080300504c503e042c070380301e00006460300e100000c0c41c0d400c20b940c0251520091301910404c014001070103204004000328400d00001c0018100d0ba11036440e4a0040441c0c0c420008441c0280f040d0809a0b5443c5091040c40040380e000308080c05580d225880b0129038020030302000c0d155030b0b00c407400e0102c0310744072000385c041e103046540d4440829882c1c18000400012080841d140801c0c01d146100342e0744202d11004040404501d88410b0b07548690a08240c21400350111500c4888800b03000010307482d540e60384c2c940b00b00e402555100040010a000c00c801c82d00159000b40c1004220720010760090302440352581c004405003060302c013404000e0001020b154190540019444541204000704180381c02000d40001e8042e464400e08122189210000740040002030605525160781a90b0780e01c0a600c0021030100348002489507242505064031032807025614030f802d2030700e400d8000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 598177832 1250 598176582 598176599
    0x180501020c0d05130b180a15030b09090c091e100e0108031e160512040816050f100909050a05010816030804050618030f01090b090c03122a1006 63
    0x12002044c81c207a0500c0120f0520004078440d800c464418600007102e1001243c1701c1c3d0b551240c1100424044488081e40c100041d001015610504e450a01580600b42402000305011038540b507010000e84426025585070401c108141d610a1200c15072125a001849400e030102e40300e10090303e58840b01c044003666070308003540d924030440700c40340c103102403e852a103d10582000100041c010090408914400580342d40d410130281042000783e0400c001030800c590407092020045041c0e00d445070484081c5050007041808a215a500d1700c40c402104280e092079000b2808600541413030042008286005840342d0010b02080c003075000e04d44905001c1c008240040d020707000560f54041c3d40307a0300301480d04081c44140d4000c0c108005003141c80d207841c4005510304001c02c0205982520011501d1400c85c1400140054082c0608115030420380c020045034500041c441c03010b901450707e031550b03000e810092600c90b0072030080090b02003500703030011500303040005106034407604116000c10041d40e6800b4003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 598179082 1250 598177832 598177837
    0x15040605030114031e0106050a120c260a0b10050d210e060d090b18070506031302040510081b0901030f020102010e070306050a0b010302040e0a0f180501020c0d05 71
    0x2100005001040103103c0000030402a0b8030000000e0226504a02c010320303041030643c0030f0085082140c0d5134070001c001c50314004864000400400f010660034122039107a448084e001801281d18601c000c5805030341540c8924030101450f0620402d441147c1c0c45482c007114144001d49200720051032100000c5142c0c40e0013403074120303800d50280403003407100c001d04468030180800d40301d402d0a2250380018803a880e25500010010b101141c000000c1203095460700b050800b4000e8561130003179102c880018038031000011620103544048480c04d0300d03962085080c8181c0ca04202000303421600308002d00141c4581c40711500c05544442094814080c0300c0f9858140382c0306224242c0754021111030041020994a40d450340d0a28011b10000c0340c3c941c40300030786c68900304155004039400e954890800400c420f01d03100d6604070360707802d1a09516040c581881950208000303080c03210310307560300d08420741403240315070144a203075540c01640b449a04040c10a00d001350405050078200d030203242e00700c1c004144940b08 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 598180332 1250 598179082 598179089
    0x606050903061f0807060e0a060201090803150604051806010206090105070c0323030124020a0317090c0405070309030e030d0f0c0809060d2a2a1505061504 68
    0x40029950f401a10082d1440540b0b43d103907025076074100401c2e10300301401010301a08250b01e80b03082d401c44402c1401004402544010110b92410711038000003105c0508503908580079400d120f925108000000301039105583c40030707500081440c541c85090640349240fa104070000d0302501e02c0b60740d0b20300032103090b10760494085e40007840c09152400000d0080340e407292051b11449010001d1640301c00c00004550082e006070841c44000983c4903102c200c00080d17007000d0005440a45010704103944c000d005110100100201101c140c030004660304400c10080a0321140100f06100c02d05041202400404011000b03600046002c0c600e0140313400c0c0040d9101c0380d214555201c460502c1081800c40e4008181001294184802c2100035102e030740d054084e00340380100c004000754040301401002d403125000c1140101a83e02221409072680d0020281d81034240b0140780c0c094010b05000038406401c090000c010403841d0642041d26030303504942c3c8042d20594040e110b40005261200240040d4002c520 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 598181582 1250 598180332 598180339
    0xc1e0f070e0916380c071503090503120702010239010506150903070f260d020a140c040f0510050109081f0e030c100c050f12070c02120c030106060509 66
    0x18900b0442c03c0c1d00301001c107001111254001c10903014010307224140d800020080340991003051b0030b02042402007600c0318540094201008103034400c2c0e60341034480c05050b024804800b00080000c000302d00179012522000b036941c06482302d83c0342c0e40490039880d403161040a1101d01141d61a0b8075403000500c10f0f240611001041e0480c1080301e031800d0700680d80b11170792158041c000d100d00099450000b03006c0304040e08031034007000e4859400b0400e085052048124080d102c1d0f006082001c442c58010440c20f500c0c3d078004544440d20018203080c680340c806400381c07154100e498105803481d0f030020381d0b100c9405800c0f040100d140241e9104011242c160741409110030a402130707100c485d05600170300015000b42d5090400411211146c1d80118110342101101c4034142e084070a890703449190314461900c82c104c0f40d04040b4100010064540100d0007140c59486c82d2505207004100b91500880510741d22a038002c103103000076200000c40e2900c2d52140e4014a001c0d608240d00802c4071402001941d80c11507015 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 598182832 1250 598181582 598181609
    0x30a050601090908070c080a020915090f0406060b0c01050115030c05030c0c10060603020c0610120201212406050307050702040c090312170c0c1e0f070e0916 69
    0xd03081c03000410143d41e04882c109020058480003400b4281040c006102d008003404070002c80d40180203144000502c03c0401c07100c01085a003660b42c036800980d40102100300001070658070f500c2d00304010b06c881d0304100e400717407004100400500c605421040c10303142d0440c08400a07990ba200305900f610301c00001c4a010920500c005041605090090400c00108070b080f20351031120f6860b160b0403238050f40c0241c0c0000c0e400244071031182100700320094000301c8a100c0382d8240c1d8540403d10381c000d2813417240281002030445d00c0210301d00040a40b40c0c100c1d03031001000c0003066069160b07011070881824005002e4840100d000600300c1c05241605e100303154030f407240e03454000703d90300b003000800c1c0910b1003d090007440ba02c04400314081c0310004150ba802c9d03480300c4214114226440403124001040c00004110401030b4040300d03200480e807009240c0000310100d100011652029040085941c10b01031184945040014468286402a0b004600d80c500340c034030020100e00c509120505034003c107421480341c0c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 598184082 1250 598182832 598182839
    0xe3001051302030c0d1e03020703060c0504050f0f0102070b07020612011202030609011503060905030705011a0a17191a0703020d050f060307060e0105160c03021216050f0f12010606030b030a050601 86
    0xc1b0601180258400d205823580303944c582d80e80404440c01100c0c1500003c501180038270030790603c00103e2082c0102291202900303001d50300000d5407402c00e4011114007032000300300347c0c0c11074680006440c404541000c07441082c1d07840700c0c013040022005080581c86440341d003002c0303402e40c2810702c80c0030025030034246c01c8402141107850304405807a0442048410344404c00550020030828818a00781c5540c0900e42007000140c1c50030014102160340001590503601c1410b101101e034000b40450119403841050900191a0b083c8400ca00c0d4080c25040000c080000c02c00c64160b034190300818910203080070400040e1542c0010043c5d1200841c0c000c0e4043e031003108248001c901500484540000514005190454619003900b40c0004154201c41d144441c480030301c114175000610414204081c802445104042544140000c2c2c4521805010b1940d000f80c0b03180c207407501e240240102034040c0840240010608200b070003001c1c030780304900010f441c3c0303250040c1c03074540861400400b039080001001c040e400c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 598185332 1250 598184082 598184123
    0x70501022a0604120c05010f1b03020a02031e09030a03020c010f03060b0a031d0a03171e0408030603193f1803021906030b010e3001051302030c0d 64
    0x192030003201e0a000300ca480680000d1b1090180191984800d28081103d80d0114003181c0098494142c000a00d0300501c484840c00745c0c000141e0b0700e8416800505007404000030a0075040b4815006c002e5018002d1094841c14180c00054100d02d40200303036241d5441201c41c40003201150840d01407890394820800005405c24400d82002d0881807440d0b4104810b54102c04001d4517042d40300350300f00c01107403201d81000c818607880700f600c81d400344a10032144ea100d810400c0710003880000500c001d03d900303004800300d007442d1810000701d480c00b41c03000c41008640c1d140d401c000000c1c5001d88462050007000700300084c440c0c07103018100c1e02010310a01c41c0d180302050310f4200741e45082c90f03801510300d054210440000540e031000088a101d041c2c0c40c0c400c11400b41000d00040070390f0310a420550601100030718407043e80e1540c0d500722031030341c1e00e0107440c001c05454054003510740d1980f8000400d6560a00090101e20045945600b5440b4801c03000c541ca050810310a004641410a0010304600049940c09004c502e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 598186582 1250 598185332 598185353
    0x30b04020d03090f082d03030103200406060519030e0c040e150a050f010801060f210b0c1305030a02090f071e031413020d021e06070501022a0604 64
    0xe1090411801003a01d4071351818246540390b0101da2a603000b4864001d4075404806d8009000740a0b8141072a00c0c6800b10340140e8a21041c400100040781054080c0719001d07030701d004440501001401804081c2c1d5405000344140c02840c132102095803100d11044500740240300b00d121596000c005031070680c20317203020040100719000059445000d0003a01ca4618070030038220900c2103c20420010315402d02d1462400300c0344058100d41c1c41d5070302d044005d2250b06001a980b204031a0800980c5c84d61040480d01c4101414010310300405e20b440200038041115010005000e40301124100f40c061b40e541c450415503500d00810001e5042030000b8040780c00c41410209559010f40e0b2420460006003818881c3d0113180a0510441d00083da03512024010f000300300191038100a1103808a40c1c044440d8000404018404000074820705c0c185107041c4403c3d5170036100811418000700881c2d2110510f0800b40e010354050000000301e6054450901d004a1191100c150007170703155001890750365100e40c4c810f076444 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 598187832 1250 598186582 598186609
    0xf101a011125090207061a010c08030c1305030a0f0314090d06110910020d0e0108280b1c0c0605071a07140c2506120b0f030106150e0406030b0402 64
    0x5030b00d034402181d40c00860004103503141c85204001124182044070f5400a944010100d0400c5600d000c44ca0120300c48000341d0380c0080d030400c1c07480e644d4000f110001d00e41418960203150140201c50b2b400701840a000c001024040c000d440e2980001090014140727140300b280003040d4071003440485800440e40d183d008030315242d0013200d000d14040500c400603080700303140300131a00164420359603156115404405081040001e08290002c1d041403500d00901d4034500d00c41c50001c0c0b0031041035095801c065040000d980001400581e01588c0310b80c0b000e02c000094036010b4404428021002039201d104208507050f050b00700301e004040c000d00000c00e81d50400b02800d09820000ba401887d030194605200911003040700c0c90061000070400440c0d03100140740044285035810240e0030400c0155001000407104440c03810300007800110b444002021065011803a41d05586066404210607008001104003604241c66203012011003004000a8030010b0000070075941e030200200c1d0050420741a009880c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 598189082 1250 598187832 598187893
    0xd0e0d0314071a190506010e0108151341130c092f03131e08030106021614040c3f0608070312020f101a0111 48
    0x14002c0640301d0603500070503807164071107a060a000f4808003402064030307091032a0408000303003e6481c3c58070000e401b0740349040b1131074144429080001d03008009065030030b0b04450001d004175400da0180503803000604c401a440c03560b60540d04e00115100e01112907200c1ca05171070041050f440104040c0d188414078001d09030502554040c18a400040e60b9005141c0c0540140800000c048110402540d490242c1c55400c0300041ea410001c415001051030440c0c0c0d0281c04800f13950015a407500d0902031207000d490307006030543c003410070030380820145100860480c0d190b9403c80d1849119101030106040a600c500051003002094081403030806412101c407401c0242024141c464190f401c1d08040c0d0f101c10b40840c2800826480514000c40e0150042c030381005400c0100080c0381851440b5540310035a000103040408200d0030180b0551081060102d82c50b040e10688904400c0c2019400140c01e40d0410300c51061b544180588407035218210802c023000d401002041c226282d6042d04802e41400c2c2030325242c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 598190332 1250 598189082 598189087
    0x10c080c030c0a030306050f01090509060f12030a03060803032505070f06050702060a090503070213091506030b16021b0102030409020c0a1407031208130b09060402030d0e0d0314 78
    0x5490382440640000440c14001d84680665850024215481600705a10030104180d0030300d400d99201c1c61860035110103a800107016201c000003d12000c41d050040c03031780b0621b0f0101010740f000021028012020140c4c8081c003220f51147e9203980c480c0411500c080b00a20140c1034a00b04007010340c080590030344035040039444c001c0c00ea10790035110040d11005544041e110b100780714800394100900d82d401003100100b0031140038156503007034880c8900d410280c400d81140b200315820300610b5218001c042e912602101010007103111090241440e031100303446203461030001555045402d80c29114001c1c250f03002c1d12013032028004032a000345000540a045110070300002c0f6080f5010310080c00105003690040581896501e4901203a0004ac45110f140c0d8000b1501040060324000351104840e0003401c080d8003955030f1030f4060100f5001c051020b402d2440f1841802141640418854003036402941507070380300f0402d00000d9524100c50040241c01c40724480e03080010038452800110002600c0400a2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 598191582 1250 598190332 598190347
    0x3040605030723030901020c0609030307091710021210210f0c05060d0f0608030901080f04080705030d0c110a0308160c120f020d020c0f1215010b220302030705010c08 73
    0x407113410445500e0080c0c0e50001d4103038200c210821649070b0152804004500d0b51a0400340240019441d104030346001620702e0414042183c1400381c1460b66601d05011500c80c1000000d88042c01403d80304c0121020705510003040380c1c45810900000000d10103142c940c00e0762150346081c004814680305862402c182c41b8041029620113008000d000700b4000301241d580090b414442c100c80507580480840d600c100309036007490743c010305259403000030344c4011582680e65003000e103400d100c0c4000040143c000003070418400900d0350320400d0398069036940c3c0101d00004c0300a0b56031310384880f0406004100f030000000c00203105036071ba0f01404102031618110b907509658030040003505d811107800114043c03400103c600c0d47d0400021800d00014802489001c0b00c02021420b21100503031058050f144600c4141c144440c200070022002c10700c01c80c0f40707009680d9045070f141c098000070112200348641e4104130724024080d030904c10a407500280a404054600401035907584180360302181c00c40c1c004c0c000d44 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 598192832 1250 598191582 598191647
    0x8040b15040f0f0c23130b04030501020a200a1112100e0c15040902160803090c010e030307211e0f0306060906020a021509030a1a09030406050307 64
    0x303140d00540c0d00441d40403e101c6101042d1612000c0c61300030810403414113003643d002030031901610a0700c2e45125a450b1041c0ca2242030000441c0c010402c039900004000082002c1540100b40c410311a995521080d4002c030160401c0002010745138049600051154020031703103400d580041d806004000010581d02e2001040c280010700d40040e819581c0c502201c46407080901ca12031300d2500c02c0340c02030003023445185094168059030254640b4140e000c2004240402c00b6019031941d0f0740c0150b00191645040c400f00b6903038104034049070b800928100c0401f031040c203000040d90319040c1d1084c0c084031543c80d00580502c1403500352222000b08080c041903189502100c02e110110b404250782ca52031828021a0081c1c2900d0466000c00c080000c081c0042200f15400305d400c21443c0d070b0441d4005080400403a075541c00c0c1c01241c442a6050103220308103010040d50602c0f45481c02105203414001d0780d00d444286440c1c1c002e0348580300105000300002108144102030542020782c041000507054800401c80 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 598194082 1250 598192832 598192841
    0x70f0b06010509220c0503090a121b110f030c13020702040f021902060603150f100315020702030f0102040605070f0f08070f02120c060a0513090507210c08040b1504 72
    0x1c812100c0c55104501314900510411401908015145080801c1135030b555800d0410003605039007032059004c541c540f00b004010b000805428440c040f460150404500c00c4060040c5148541100307081c0c05001e0901149040e540d890040c440703008d1a0030045034102030350040034203c0e445079850201e44103108051001d40b500055400000300942d07080c03040a0700e80000584054840d511484501c5042e01c829072141e503000c0e911780c0d420080394a420102c041c0e50000c5420003004008080b015040c0720590794043d181d868001c400300c030340d5220b0f4400784900300e101e280902070010f40c00300100e1003c149104d9521003501e200700420305196409485401c0150450003044843e680102d410000b94034281007060110f80189015101241c0c8000002d54988141103070007040c0000890340064a1207451501002409954014045858100b00050510345002666000d00c0114000c02403c102c1c5440f91290b0100302e9102d16805441d10744030405c6c8e004c0001d10301c440702015100035200759100c070f004 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 598195332 1250 598194082 598194109
    0xf060409050105090f0c07151508160f0821040e090102070204050c2b06030512090a081204060c0c080d08010807090902010813050c09010303110c06070f0b06010509 72
    0x80008840d41002c04001c003140000e84418541000181403041b000e00c103404641e4416030189100707108900d09406000904a000300d4052901e180000009060b000866100000102803041001791512801e49012110841c016002c0c1035202c14102401d07414405050244090140301d883e0810390f46140c170b100c1c0b1410488014000345d4000c1850011420907004141d041413541c0d03091410620300807403600c8940d251a41480124075880d0314500d507651650f2000014580040907541d04011800c088034265110640c00c0b4052101440e000600f000041546c550444020415910301440c1070011a0074180c7c80405a4041495903000115940e003001541401815a141c4c03206030761410721001d051807030543c0030040d01414003d16200507a800f0202c1ca0b4007900068505540b42e49504010f46481500c000f40c0c1e42000305100003205041d00060300030340d0400c6030740445400415032410b00c9942d02a07860000e00c0ca0100c850a03900107001002083d07400f050624001d03040c50400c1b070002e0706100070040d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 598196582 1250 598195332 598195349
    0x160f060207050f010c0b0a0b03010c050711010309020907050913021818060604030b1302151207020109030903021017070c03021c05190207120b01060815011d0f0604 72
    0x40200a81034050060400412003290150b60000403200003030208509aa0020003c0d407290340000da030054194803203066194041c00802480d4001c00c005403d41d405140b040c1d030320001302286000d1540c424015101e5072030b8081c10403840ca4549140c1070742c0320b801000942e81c3c8049404d256000c850a248040c02d180200d42ca80c80847d1040d04091000318010090b441c50b022200d0720030800e86d62035403001c8600b101e50002c01c8d00055078031b8000c655011170f0021402035009544110100c0c0c0d0010540c00b03009805020b440c070100300d86600400307a00325800c401004010860382901007000d8079080861000b0708116042410803051a00c0d00660f810b0011580c02001c80c14002c1d01c801419810083c0503a206000c0900d18007401c0030100181c818084d4001c02c0f450302c01c3c0350b144204590b01c2400320500030f04030380b49440b031000000d00c0d007211040000d00460001a02040000c0c0d0402004140082303c400183c590307080e00c85001c001c1c20b451201141c0c0361a08800c01512034405030b20f50000034401042105c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 598197832 1250 598196582 598196609
    0x1b09060e0a0b18120105070e01090806071205060301020904150602101103010b0a090909110f0d031d010c0f260304050c0105091c050601030506011d06040c0216 70
    0x144050200d1800c400c1040c0503040e0008248100c408903402c540e00c1100510129400102070000108108140c2403400d03025402d200501081903040280c0c0520301e00243c94000c80b081d2206000307942c5070300032582ca4002031840d018100800c0750039070100342c0220015002610b040306a034042801d0b1480541048141c20420408100c46581801010003030038200304240450100c0e58602003140c001801070561620000a060350800c0c041c07001d04000b0701d03000345c090040920301d0400c0107500c400700380b601c0c0c09443c421008000c1461f0005140070b105505440c3c9003551003500c44140340c5a0140d501640c1404040807030301c004078604620001074544105420a9105c162000200e1000034104a5001040e0140b003400300045000c61405040c00003841c055440e050207400258000440041c04c11046030540d00c000107001d40802c50034160782c002c508032492070345d1700d440345854014075240740c01025440c0c0020407134601d02034112510940085c8100c2d0094031a014401c2c116000d19448425441c410 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 598199082 1250 598197832 598197839
    0x50702070501030507050414060a0203130f06140f0a0309022709150103030801090504030207050d0501020c0f1204050402070f060203090d090509130b091618060911040b07061b09 78
    0x9406a185e0007400c4d807a0181c1003c0c07610814840c5003400c001e07680d01c80e0030701144031901144208107550058602c3d440701540382e41d039107214001c60310150145000003944801040300500e5880111f4208600c440c648514040004030110000d00007041e00b242d10040c480500c41500400c000c460499101075100019241403120a540c82e0154400001e00740741c07902001000440d81043d09141101c2c000c050206281d69545401c0303050208640089034080e810b18802014481e0560281001c1c920031800c507568036080580c0c00fa940e04070701520445510b820482482107041c00c0c0c016150f1948151080c20a0800c550b481c5400da80080380c110b89940d000c0c0d032010301d0007640102800d00a06d0165616021030804940c0d04200c0c00b540000034003032103070050204180100030800c45c2901c2c1d0b50703004a400b04540311030704580440d0b4042d01c03d4500609091000c03842c0d60b040c2c82800e008000a400041c40c081c0707003410f01c0007a6001032005503441a62000c150484034000504008000007941c2c41180c0c0504 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 598200332 1250 598199082 598199087
    0x509010f0c090e01091401031e05060c03070f0914040f151d0106030c17040f0f0804180b0a060e18041a0915010306110d1401050a06050703020d031509050702070501 72
    0x41640800400c506046204049048a40c86e070790540350040040310b100e002c071600c0c02030b00d002c00c4200140303607120f03280800c400e03451b0356805580201061fa9801802100c415411500d4500030b005001c2d00c0b580c143c150b1031070340c0341990000c4031440840d070022445110022004844180036800149888d8074200e40c0d090100040c51540d001d04420308041101c6401800000c00204104c0c6100102c00c0040c00810140125000c6507000590311070041c8859003100c0c50b000c030582c1c10620541441c90303154200a900407009014103802d4442c09408040c1c40c2e480d1100407103d10032082003107900040c25004000031903000b120380f9407265000b001030031000b00115800044100c070003400303051a50401d481c0d2003060000320303a541e41103c0d0000760205566800301c007040d42c1c6205100708036400c545440001c6414075820101c0c507040300c004407002c074122956800c1c281c40c1e51044150090045c2c0060f8607003815140643d01c001c1190700c2c0c444043c082642c8a0170a001290300542d207050150b072201400b08001c1d83d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 598201438 1106 598200332 598200359
    0x20f1f060312030c030501060c0f150213060302191b06051b0d061a030601080f0a090c030803101e2d15020f1507030509010f0c09 57
    0x70b99445025004205000b44940800d040000000c1c800d4000c0301c0700c02c646a0010000351440f9156654004c40030790b1603d0300b0448550a01c0400c1050a219160801408036034500507990401c05c1c440207044444404c0203020800c9503000100148401c0d0401282e0b141c1c491408107aa84a102c5150400c1d80c0f004070302e000ca0403021454000008080d08030380100c0b6082c9142e01810002c407120070309544402c8500c280812076210110341010664098180c0c000481300340059007000036507400c80165066801034581c0c09022090086045000c40704800030002100a6910b10081e001c91045041e100d02c1400d201c2e2548500041c10304000c1c441018542c20400d590a41c441e4503403420752880c140b01121500184580d01107209201e10001e88000541708003140144140d54200c03088000d030000803e408899503d4403207594a81c211400380010f5400d15498190449051100210906 = true := by decide +kernel

theorem cover : BRFrame.Cov 598021582 598201438 := by
  have h0 := BRFrame.cov_init 598021582
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598021582 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 598021582 ≤ n) (h2 : n < 598201438) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
