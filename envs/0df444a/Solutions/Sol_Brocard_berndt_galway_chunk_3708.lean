-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3708
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:26:47.26482+00:00
-- url     : https://prove2.me/submissions/fe419895-bce5-43ae-b2c7-5f8c6f7a76bd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 666726618 ≤ n < 666906474 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 666727868 1250 666726618 666726629
    0x15090e06040b1305060405010609050105100f0e0a0909150f09051906110a05040609060c03020c0405060f150306030c03010b0901182703080903041805090304050405270c010504 77
    0x8102c1e010681c0020481161034105500c14101d640301c1c5020318055000e000b00b445100d01c8030341000300100e42817802d080c0c0d0214650040d80c40c10040c1c0c4a034001150090b45281c6030344d800420915004c542c80d112405035401d95801340010080c0c000012604600b15081d449141d0052440c043c0e4950000c0c40108640700110000c590f480d041d03420b2405d145000b000208502c4900c0400007904076549508013025004955898440e986000c3c0d42e40020303500360f8492000180140c200c038501040d5485c0503400185c109001410304a04902580b0116880c21030f80c0e108115a580d001c0304012075807504100b40c0d0340983c4254020300042c00640080388601c1f01c10b000c0d0308181c0c9140c50340d0105680c180c3e40040280d2103207031200391a40070701d41d11310204040a0003060700000d100380001079456000004880c100d5400b03c1c0b0220610f64451032003001014050f0802d2880d000400c8001907607503a43c02118010802c4a44100e411140710900e9030400b0368002c1c80c20715907001400c070010035a0300300e0181da04440 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 666729118 1250 666727868 666727883
    0x9061e040f0f0c080702070501140412030210060b1804020c120d0b15030105091b0301050d080d02030f1905010b0313232406030705010c0206070b0a15090e0604 70
    0x403286001c4401508a15448003003540c80e1420a4000036400f07810580108090b400381d031003007034036080111071f51812012801c00000c410002081000c04240701c40c01e085001e441581c3c000ba00300c0c03c004054460691210303440003130109405035092042c0d2103034440003800300d80842c500024000f20640301c800d00c5025074051000403485409403501604103642d043c01c0204210090071761140040416007007030088078000c250540029006440485251150448002c10a41543e203032108001c8181070301c25084910010074864006504882d001a600034042001402c106d0700c2c0c141007034540404002c1540f6031032820480100f0800b0107440c1101e810091120b6100340c0980356051143c000d085140100144149415100d401c4a5000c03034040904600200000352441c08003d400700c1c0e212058410543c50741080000b004558010380d407840002e031001e000907040410039210a80300b688103c420000c8141c85004080f4400300310100b00001c2c083c6103200f00315039146860f605a40710300c000e00080144 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 666730368 1250 666729118 666729131
    0x509030c0a0e280e060106120527070b2802070e07121121011d0a020a0e0d050c1c0308040b0411060c010608160602120a0309080c0c09061e04 62
    0x121038006940c03c0300c106254148000030b070389251680c1d280f80900c640c00010380301c040d0788010341707055001d075074002c404c000d41c9403480542241c4039101019448029a40600c10301400081d0044800701a003500038001d801559005074038000d040302c1e071249120141c11500710304807d01001d0013502046410540c0d03450407002c100d00040000c0001c8c5944602d407aa900d5000c0ba80341205081c20048000c0003c0f2030a4010059a031a103d03046c4142001c4071440c000b03407001c40094011030301030380500740900d0305241c5001507608081c0031031030320703c20000280c580313411481034090113007000c1030821503904215a5100c4070354825100207100000151000707100d040d080002c0340170310500a0340c02ca110340d0010080342d92404464800d0b4001e1100313110301e82640c011540041031101040720b440d800c40b00c03a9009042001c081c507062a04036408108000141a03560441e080440c0d07040001e0544811207900500b100c52000042016046009284900c10840030241885208000ca2040e01521003a80d011942 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 666731618 1250 666730368 666730411
    0x4200a03201e1b06100e0412030f02090603131a06032104120f03140a0912020d050613060b04060302220e120309010b0a0303231b0a0c08010c0f08250509030c0a0e 71
    0xbc0e200d604042c5620200100501ca0f9003922500744000062140700c40141400560f50001d408000c102c031001d606030400b07491899020150361504820740401001c00d450a030326012480c0c0340200f200b0040e40e04020600040b420503800813000b41c1c141290402007170030508640c80040080742a0301903545015480e0920b40210348074003038111080c3d603100313007540c0d035528040c1e1880e88921290001074400038113000c0002c1c02403d1074454403054a0300545101d840d407000c050490b04607030717944200104440d9a605804400d1000713028100c280ca464201c207681d0b9050038095107094800201003a40301d4591040c0170000039400003002c40452400c60001ca04d02c860b1540c4c114101d010b01c6c0040b0001008000400000150200d14104490311030f2443d0560780e500c4101060885450b920b0604c04261007030620f9910900501289600810607040d11002d0f28161509041c43c075100c5ea0880c02040020940303618620341400010705000040d01d001c2070302e500d8182210b28200340a0000820326aa40020842c03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 666732868 1250 666731618 666731621
    0xe1603120f1817010b0105030c070803040f05011e06091a0909070f0305030406021915090204061e0504060602150c0904200a03201e1b06100e0412030f 66
    0x11802c005890900d42d240e941290105048140b003003000103518081095141c0e6000c1e80076603014a1240305803905021040d80c0305c000d41e81c800390040d00d0042d40104000000345090084410302102002c4403401d003000b140c82c072020b450094201ea9645400c0845030500e00249480b8080c011104540702022500e844e041113080c001395800180d000c0e654004c020050110002c010b004484840e03088401044600c0454040000c5000c1d0081c40d0003daa0610b02c0f500c50036802115025000074800290746696450500d003d84800482c0f91041108000401c810702c0c041c840d040086c602c50003c1d2051842002a40f09020001002d04049800114400750b00fa203440d0310191030174540c0c0031005d00c010040510340b0389035009501e0a40000c0e0425100394407400f2008412481c1c045112491810b020424000d8402105140810307501664140068a0083c040860300080c0385038a101038a920305015036044d0303000816030000d0003200175407018440000c042c14020341004030b4504c0c0008481e9901c807103910 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 666734118 1250 666732868 666732887
    0x61505071b05030a080301080f030f030718051804020f0301110703270b0c0c03030712050307032705060108010b01051e160303050f1005030c130603050a060e1603120f 73
    0x90300f40c0700c0c05150b001000800c200a5050382c440c1022100d40b14021246c660b542d120714203060a84020600114078041d0145550200b09040c40450710a4541c0300c0002c140503406614030402c02940300007c0c881541482d82c0300040e1030304190b000f400030088200c05000329200e101c600a040200d251151030b002e6080c20f10940c0145244c0320400040703984c0d0300f08040250002d140b02403290203140280740c0d00740f4000003121011a0b000520440a8010031400d44054200030681801e02d61690806075150f400f00817546e0000030000c0312180c020704c6500f86503142260580103011035a140860325086aa001320a0320480219983c1038440c51035115850081402003042c0f0f84490741a0145007410943c05401c1540308924020702c180d55941c0e00c072001c8803d03400381d100d00398054120308818509410090301d603180040c4c100b100895040d41d20781d10640380c03020304002a903480d81d580d06103903807400051007411106010718012142150460315400d04458004503001c003030104100d4403010140c060034084 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 666735368 1250 666734118 666734129
    0x2030c010c08090907020303100603060e0a110d0501240e1c0f050d0e0108090d0804030e03011503080703080123011d0d060e06010b04030b010909260d061505071b 71
    0x81304c14101160040d6480c0c0007501c0d0400d21080b60400401c00900ca4403c560417a04035008405603a160400381c50024005800880000074003041010783e50070f06402500d00900740020019250036125055500c603103c1e90000600b004980f040203159a43c8503924a0b010303d010071410710924141d460800269030120000400c54000e100d900345059400031000d402150080e00e0b070308903540c1c4220300d035615070b10030303840740c42c0468009400300f80400d10450703280306085c1000d400080c0c00031a00707070074200f140803980c802c032102100001c0f428101640100b62900505c01d4a05a45d4070001100c03607005c2c01303024400d44904022a140300408400440007501d20000c40c0a00740c0000341c885170030100081d000825500c0b9151003450b00000702d06016404942c100d0390025082c480c1c43c0d003082040000342c544200266400400c1c4c9246c901e408660501c183e808080a41c041e95070780c10301c054644180c030140c1e404a403483c1d02c030803c1100f0311500001210540c0b54440d055090525140d1040112502c064018 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 666736618 1250 666735368 666735379
    0xf0f050114160b0f1e010501020a0b102d080c0114070f060f020325120e0c0916020f010b15031308041202011409311e0e0a02030c010c0809 61
    0xd100050a49a1542d40500095500c0c2841081400d1942c102c45d4028801e00780140d00c0001c07070308003140c1c03200c20722a0009003101f2510900ca035220b03000081e4111042514001800034032401c0000d0040a45c1400204405005003401c6102c00c00060920300314282880c1c12124005011400c0107220740710038031083d512000c10080200e40d00b040000942044424030310b0b02d0040d07070340d02d0b05a00066080400f404c01d035a955040908400c041c140c0a08500c01240a180c0310311200e90b06a81d0328009094032032074058080001c0310b03802c180002d00d000700d01246140b081e4902601c1507185e4881c900c10903241c0e801f104403161307a511160781c070701c81c0001d00304405014990081400300d01805054a42c110881c000d0780c40c8800382ca905042c1821520035402d065504c00f041d5007107030200700e07044903844400d42040080940b41c84604d052410a8410a140840c0a5001c2005070071004545200e01c8a911003810028081b400c842e5022a0380c807400386c0c21071410303c410340003180100080034044400e2100041c00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 666737868 1250 666736618 666736621
    0x303111204061d03060114040b030307140f12030903040b0f070501060e1509010f090e0307120e1c03020714031f020a1e05030c0f040905100f0f050114160b 68
    0x80081048180314445008a882d540035100680b50004295046c0c1c0c0810801f101c02c21201c0003004024002d40c031150303405010911043c0c0101c3c0c440442c8103540d03000c0c1c0024290503910b2020050a020f0707808510448410207209200b10401300000340c2e4107464140405650700c80c3c100365047c04030700070f03004024000d40c280240841c07201020240d8500a0803240c02141150285008200c04940700740181b03403401c80303c0042040710380d8030380d000782800400400550b403902c038282c2c4440b00001003451034440440d1407102414005d0034a030355182515443d408026041c103050b950b00035100e2105218000f022070880c941c00545540c240550b03409104a143d040785950071410010300603401c104610320125941d1030b07103070320486080c0c42c256101b42c1d000d564440c0f442d070741c1c20308844460f000fa04d0441c02d1503005000205070420070780300e610300030503011800c030a1051a095000600403055044202c0213081034508022a03604100303410307986a03210302c0968541008881c0c100080390380c2c0794040c044c60050f00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 666739118 1250 666737868 666737879
    0x201030902031614030304081c090e040605060324040f021207240f020a08030c09090a090605071e080405010905120a0f020604120309110604180e070503070303111204 73
    0x881074412034103440d810105000500e41011b880380524031400c0501e81150030000d2444000501d4002c0329035590809065003902e9503100030038640c0480d8211440342e07445040c401140307000c2003407000041e1009001c0e0191545580e5082017000050801800d007201860458215903070303240b8400180800c0e07030403103074181d40c1c0f00b40c1d860788285104112003900b900016210806881b030100c04600a070f40d42c0042000400c1540c610610354030003842e096890806100300e000e55682c481007140241c101603c01b05085d105801d11108440026044105000c074041e1511004041d4040c5141c1c0e801c05414900c0c00e40d5160f0500c68090320345003500400c1400703601584681d01401c00c001d407650820507610074080c0c2681d80020b0782d8840c4169009410808a10645c0c001a0301c0394014400040c407910101c1410303541e08012030810740150f04816a01002e21011700960403003442940c1504c400480102811032511303010a48908050002404100e407a194807003011a04004920003080d00d02e40c010760312640d52 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 666740368 1250 666739118 666739153
    0x5060109150941060403170d090b16080103050c120a082b090302030301120312060303020c01120b1005070822090e03190e01030f02070609020411040602030306010c020103090203 78
    0xc04140c3c1c80c06604001c2a800c20301c1c1c188010101041c06030800d4681801c5896004211152045841c1c0301c00d8200a035082c0d01c04a03006425600344250394100e42424418864000b61941d2407201c020071420000410115000066240c0205003c2c2d9440e14a01e4400ca0440d0400c21031120280c000e0703200050845000d03c000040192501d45041901008508882610f0070303907865400240059200740300501030340d0302c104000010a8460304204110302043c0d8440004d50b4030340d41c02900503802c080004009540c1001e1103128012801c801002000751042c00113040c07030800401c80e0304211010070640200003880c400c88110941e42c0022080c0480e480c0300c008424161030050b49149420180201d5010000005aa554403440e0000c1d40300c20007000000c440620004510504040e1140c00f070181a00640c0300030314101d80510310109035800c071401440140d8802122546840038208010800680d020056030780009007460894105210303400100c015210720b82e000303945406000c01606601d640c5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 666741618 1250 666740368 666740429
    0x110306130312060b040f0306180f0b0c090915040b0303070f0b0703060506040f05100c0b06100525060c0f080f091507030506030d1110021312030c0b010504050601091509 74
    0x60402032025110340e5225012700001e681005140103070300c001d0440001c40600401e54081008071409041000036400a2310040013659010550526481c00303c19a040c94022701602c20420b50003185490480d665180454403c0c200190801c001040841d28191107a0000c07401040d0042000d0745564641c4a001c800e1041c0d0710800303100c0d13203c1040d0b4030b2145000c1d040302c3c00341e00c2d00401034024594170001840309031100340341540c042000030401c00241503808003060a03628004100036680d400c0b00d2402804075585601c0000a02c4507103403038a0340b2240c1c41400d2641c41000c280710242030b900c400c5003251400740280390100508000d601040910361f03065000c503100309011030031a800c0000e0201c00707580703180c440340030740b10203401c110b00144059100342c0042246d1061494013004c581c1d5101f81c01d483d0220030510480000d10041d0901d03091000aa4030603000d000d04550421040c180100003805403880c51085038444500303814081c01d0307603001e076402c000103094030a000d411043c52510070118000c0c8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 666742868 1250 666741618 666741623
    0x21010204050a032f1e0f03010203130b0612071a070b15010810050604062a0813060206010b040312030b09040605090706050f1b070f0b030103110306130312060b040f03 73
    0x51015400c009800902e840c214424007603c06a00b0703280c5180354003080d85c41c000b1200d070410382801ca081c1580d102407006610400e406000c4514103a05481c20000d446806020740d485603141800003020040c002c40d44904032440a08850001c05641000700300138040d040c4040c3c400c0c0c80d41401c200b00c10022a0010001d00c0c0266140440d030381c1c1c0c0040500b840da0442c054039400c11401d100c24010705020f00900005801c8641111403115074074140030303560038400041102d4040011a404203410300ca580e00c1300262030207001500540d070500c02e05401e1b83c0190700c000780c51580b0030784004401d18000da0060f1100000501580c2c070a28090502e040500400ea4094601c2e00c10a1b0000844c0d600c268296840116041040c1c0d2500001c08040e04820204007030181c500d000c1c010300010030700c4181450300014241407071020348a6140d42014012a1040c0781200d000c4c0d0040401c000345c1443e445d1404201650506100000e0183c0b007040ba8001d041e1070300032441e1040006004601c40c02c0d8000000c04891 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 666744118 1250 666742868 666742913
    0x14010506120a030e01050f0408030d0905060c250c0801050a200c25080a03020d02010506010815090c25060c03060b030f040602070f120207050f21010204050a03 70
    0x200c030380d400542d144114100600051070a01e842c500a600c0ba070b0062015003003103404c0900785a100e80c1c03c582168405004460100c0d41c0d0940e0b1001c10070300f84802e544c0111910b20309410440c0d0b1480d410140c103d80c140041e1150b0b0341c3e02c041e608004020140c940600708102c020031031803608126620040590848111035245c09224060300c000308141152106140c0d1130242501204013190708051641c003e2030070202c1e2410710b10108400c41f0402100610f580298020040c40340d5a510281c21182d01400c403504001198040003010500c20803401001d1005455204659a40c00a078003c940070300c10f075000d403049408806180c40d000e0b000b1282019401940200031035404260254210340a521451034818030500c0014090701030112110742c040c0c007980025150101d242d503001c429a0714000121100002141c101211a50420480c0007908055464422501e0100c001414240da100c0b108040c4448601000000000c2034054074002e00024010103401c688a19000581d402c04078000c03407201 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 666745368 1250 666744118 666744139
    0xb0c0f18031219050c070518070e0a030c2705070c0c08030a1422030303020c1e060c070c030b040605011802030c0702010c02030a1a0601021b06030a051314010506 71
    0x4800344401c4949034019201e43c600024070700c240603a070326004204000010700072000b00107070a403a008505010052841072012151415040141021085111060150300844014400aa0741003264010344120890144000081200300f4121090f0107114201440c18481800b80309604040005200c0d88645800c6280302e4031044599500e02440f00c2000001d843d00903c211241c0d5800c3c024000000d0120b841d0a41d00e041040d45030850300190b000f01c00082d800185071101d040d09110540045e030140780d0300000f0203400e1400a584d20005448030031100400034501c410000c41000d00c000966204030b0085aa1910381001002404240304440740141800c1d54072400d0882c920072a80300d001000300035070409004d6001113030900f0319400d08036014070910035440f011551200700d115142c00c100780001a18503003039000a081118500104400b0a07044042400d503070790b01c5059036809135006100041c241e8507401d03c05003280d00518013411041480c4800104d01c4010342245101d003100b5505503620 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 666746618 1250 666745368 666745393
    0x13050d0e010e06070203060403110a080408071a2a0c1206070f020d0504031511180307080a020f0d0809100f0806010813060f02040b120a060e040f0b0c0f1803 69
    0x3039110b04c040c003d60680001c4006400207004010101c00d00c130000c411180c29082c5a03070b4482c140d500a03000800158000c141c108016100c10014243c45800c030200b42d0309194240f10001c2c6a000720a2001041546040c0c0461000e50f0410081c0401d5200400b517961425041c141d5903110f003029240000000d4031500c0400c20a400002c0d020306544280c1d64071442c0c1451a1607001a0741800c07854507030510344a16600b8840c03100d0740045c01119000300007840300c03404441c00701445c041c3c0341c0d40640301e6070b00090340711b00141c1d6859a105600e0401502c0426549041d480c28200521070402c050764000140302043c404c4030361182c68401c94190075201c980560722458015200001d040f0b902c1400c2d984000e42c0080012801d4212103695410400003500341074030b4918801c850703000b80b414002c0c43c00d4640c0821000320958090701c801060400e460300d0003070505440c0d00c0603c0d400310394040c00304004580030605041d14602100c242d50502a00035454825200380d4524910a44a030079200b0301c14801014603 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 666747868 1250 666746618 666746629
    0x1e0308180c0102030409020a090f0b0a0206160c060b03070e010b070c0902120402042003010b0c06010b090a03030804170f0a030f14060409020105070506040501050709080102090a05060313050d0e010e 87
    0x1c405800035805e242c58405100043e5222030865020040c2c41c607000074041040c0c86128024081190105490341301160000340380c59030080c1400071007045000d85c01d6078160031040010301590004000b08a0780c10f07c00119150000d541c1c440030340c2076035010000030400c1710320740079180b030ba4400c11080c5407495a440c006416401a8800e602c00e00760281c0110300103260541c850030040300d00009280b030000d01000348003101e40090380418511200014403517230703c2c281401060701400400f41450b04094900303021801402c00ca0000400f0f0000c030760b011905000c042070190b0402c440ba45426580e0b0305c14903852001030380100841d20046420f008544101c2c40843c045d1f0940500c5202c0a00300e26507074182004003030440e00d0001c1c1c0c10320400b00480808600c09215203407045000f03070000300311405c0c2143c0c014000c81d940c0c6d1003c0096403060254104e242c4d100907803601222000c8890310703226128601d00c0d1900303c3d00100014030521844001c11120b5030440c68255210000342c07900d0b01c80240410a100 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 666749118 1250 666747868 666747883
    0x8100207030806040f23090f0712020d0c080f0a032a060c0c0b0c040305070b03100b03060a091b020d030212060d141e1212070c1e030818 60
    0x2008600140c000991609040c2d203c0d03c44040e417810046200b1111030b48070080f501b1468984810b00e0503c0c400c00c031028108000c03a000707480ca044001d00c1e030f09141400c04d990064401a009100c1c4802682e03120900111101360303005014450252404814a0b1020950f100e1403114100e021600e81c8000c0c071a20340750f01e1030034a041d032094a0012540ca059a4407800107011042074134042c407402a174100c0c04100c068005a114001c0c481e80c5581d0795080d4240710345004140c0e4405c520402c1d04004016001203032060a03800c031002c1000081d00e0740c0b203c0c400181b203440d0581142103401d140c003c800d402c8000030281980602169025621000e541c00401c4090348546a030410310b03102e803a00031031041c0c20000141d4045034002c494254094490492070350609001c0a90a01c0c200128112002003910501c203134411b00b03900f61030303007072070648001d07003190040341c00619103414002642882403d208211048924200141d10224054a00c5107409003032080280c0c0d091b8040c515158140b95921400603a14 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 666750368 1250 666749118 666749123
    0xc0702040f0b090a0c031b0c11030705010215040c0506030901090c050303040f060c02030312130605071b02010e0102070302100f110102160803070507060908040311040510150c150608100207 83
    0x19081d0790b5520306000504a040134145c10560b41e101840556085a59908884c0920356603c0d0911106814031400f19401c0d2103100d40300b500035560403c1680e8000490000c0d101000000708115522800c21600c40c142aa0026410960000030080302140651100010034451040722b04a652290241a80d03405907000c0c0d0054132a410a0601c001c600640d0381c2404c00340700400b2603207800101c0c2c0e03140e811840103403041644400014050002c00c80c15020341580000245006081130f00007500356140c5001c0400c002e4140810f44000c0f000591090243c0f00155401030880c00940500c2d10004041c1110003411270000751040b14036600251041c003c40b0005618a201c2841e5180e0301c1c1c8481c149544080d1505007032003020011000007404502880355001d00a02103580c84600c1c50409648903d11400d0080c032a6191074200050108000c0450090300c1c04080881d540036000641a9801140f40c10041e143d68200441c8007a0b1460740d0f00810140c5240302c0c00d90b456a80c00c5516401a8021880c00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 666751618 1250 666750368 666750379
    0x1006080118110408010c02100c05070809060d0e030901180315020a11070902040e010b09031b01170f07021c05090f18072a1505040606030b0c0702040f0b 67
    0x40010494840507820250075084001a40c0030b1a0102000140d0040d4406040c90b511400e1044c1102d4040c000b0700343d4a45086410300c14019a19002003561088540040a1410105440b0800d8841005a880361200600d04201440d64a51003641d00c2d003048011500090300030200340c040b00d00300c401c41001c81e035101d0807040701c10503a01a40006904076929101c20040c0549284940d900100071540040c84038120043e0396500300740c010304544005030408401418100009140e9440c00a024510410450300c0740b000a84160012100402c00b40e021100c00034051080c4680e20086626003405440c154007100d40404070400c00d60080000c0d00e050b100450700500c0802c6180c144510102c041c50b2006004441181611348084441d4000b9505200080d2903100d02c60440c0c4c8481901c420790149043e062441210a0383c1c44445100d142000002001c0d1224081010050107070002c2001d10344c000c4480c40e2902e80b00300c040e5119000387c40141d10490605001e0007c00581d032041c0c044110b4080d10 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 666752868 1250 666751618 666751621
    0xb010f060824091006090b090d0303090203010609021b0613020a060c02150c030306100914131b121407090501050c0a1502071407080613050f06040609030206100608 72
    0x740e0000045100028110341c402c508052041569002000c0f8400d10400039608100e0b4209a4020b11003072030368103d0f04007000300704803003452aa22250b103da02c8543c90710303001c00c50300da080c80824003400e40c80c1e105140043c00442c421114440e044401f030b10314034040c1c040340c0c0c0c02c0d500c41401280404041001039004080d041c400d01200b44a105c00340d02550002d41105950058804a480c95a1240001d82443c2e080030003442031500e050032b12a400c1d50400c0c6400c24801d8281440c6012180c02040500c0c400d11a000805005851980001030550b104040780d10050b6003031000a0076180e080d4082c040c01528203c1940c0384180c100d000180141c9081da50505441c0c10440127454a03030101c06900d10a12560424800184c2c5507110b913a50b000c4400809a201e1a10303262005004038007040c082e200b500328078000d011071080080c0381580f00c800030300031200500d8103060050911104400c2d0308803034001c06040000380401504095404c030300c00c0c1d0899206546400d8211111000e41c012400003c11400 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 666754118 1250 666752868 666752881
    0x70e09070e361305100506010f0804230708070f030b01290a050d15050f0301020721140d0603170702100e010e0d0f0201110f070501200a0f0b010f0608 66
    0xd810b0359120821290b9540301140c181c80300c61401c0500308000010326111010070146507800a5044e00b2440d00b410034440a05159030307050118200b154618010403070076007203400010410842e2500600014040e940815140c903101c295660312800143c42000b0500000180c1000003200341101204418054400c1201900440150344c410410300d400c000d01403000440783e840d1841000c1d4080b0001c00303000b50540c0b4040038842002020348400384242d20521500c0d012803109407132540080642c40d1550003a41030040c0a9074440c0c04205501846c403008500700f107424086074007040550740141f04200600c003641c4400002403055040c001c0d0868003228482502d14010308014a01c4072381410407000c6e40382a00040307418140304d1399003511400440c034070500035541c10000000080e0224405803800352850042c0c45e41c1d440c1c551141a0401000d448000d000021031035442000e1000d000540f541821241000b444200d00315109880c51f55800000080c1c00580421200c01c940703582d10390590075035411 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 666755368 1250 666754118 666754219
    0x90d081302041a19030308130b0117070e090f01050a020403051506010519031a090103121b12050306190f0303050309010207050604151404020612070e09070e 69
    0x4900042003d444102c0e1810640c1d60440766038240e40314143d4919046255080c02040180050b040500a0780421140f0f00868a40d2884034196100c860107000c6040551000e42d180a0040d030104c0c200700180310a02c042e003003000c96419407a080b80402880301e501ea040303001c1c3c201c0c0704920000b09640d2000108900030032045213101d90102d070505003582400907240c0250b25404c100810403000070365501c0000c4840c2c8000c0c0060880c4001a505c254aa41c10f55442c1420011803c00b042d0501c65166850707a9560200030700b565040e58001400003540c008190007030b0142d0030903907945100d284401c0140c1e450080c04041041150410118112802d142d078600303481a03070001c0c11002540d50208040404a50204a680e01031031050b81e0006148059885c024111414048050000c000c00c0c0d00f4000036940d0700040e40c040c4410356139202c086e0748130098103032901c04480309040d81024419080056407508440d032481d520205880c003084044407014003030448500300c07440601e10b4202072403000108052 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 666756618 1250 666755368 666755381
    0xa0908150112110d15090b0109061a03220b0609180709020c01020c0d051b1b0909152a1218030705030301030627020d140c0612090d08130204 62
    0x40c2c11602c0d090000c1d1545c1c040104410118405161241c1060703042180c1f8100440c01087c1c42e1504218550820401490180641c1c0800840d03800100c04207602c84c1c000d001241d4092401011540c0401481c03030002043c5904032482031260002e20005000c20701c40c1494a01e1100004010340021410004210004d4000c0c45000038151f60900682c01600010014582818a10307241c007615038900b034007519564585041000e40f40c1d08032000701c41040184400c3c201841710200c2d4a1107169072086121403070007114102001080c8a41c600380051800142001603200300ca4001221034101400c0c0100c800d44150200048004148400620040480c4801c003203025030100c1940d140c0b07005903c5040c0345030001e80099505c1966844003801c1c045d0b030712140034103440c0c0c401030b030181d8824190005411a40c9801015010120324007410511010500c64007055030300081141d0f13283c00803403141c0c8452200460f13141d5528481c034400344040a010b01ea4551045661500848042d0340c568203000c05401c9 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 666757868 1250 666756618 666756653
    0xa03031803050f01050a050106090b03280c030905010b010c0c0b030903070b0c0c1501150e03162402060103020a120303020d05010602030a09141809070801020a0908150112 75
    0x1054001c800580107021a0315005041c1c00003040c942022000301c0304070399041e40710b10180b06003034000700004084401903c0d44035403c10f03031085000c1800c8905000309034096403c0c583c3c4500c1e21290010f41034240d800461030900540080042c078007a8401540e000c000381038080c2c0038000c00002009500c00f00700040d5440001a42564104109699584079158040d42d0003155404046440104040100310700c031080e14039448505041d524201d04500740c2c0c0c020410181c10481461018045500c00b000694034910302c1c02d180800a913981c910a01032014500503001031800da40d10102512413001070458140c0360001e24003100706281040216271260740500c21411b040d000d012010f9810820300c40d01d07009140c0d54018540c0c0c1da00b01c410041c840252500031152a5051001c1202161590b14111464801d40c201c1c0c000c8585031401e20354a019000d0303000000c55800010118501070344011b2400071604d0746800ca0f14561805039904e8042074090007050742142e8801001c0c808200e0f041e010148290 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 666759118 1250 666757868 666757907
    0x101a090d050106120b060a030308070e0109170a0209090120070f06060f05120f0601092708070c08010c0507030c03030b0a0e011805090d180b031f080a020a0303 70
    0x100da41e80e002c2c02d503003a40c1d1151a080d031030400140180640c410442d41e200b0f2048a8000759141540d5000e0a403120140c6090b040101d00906001c0f40d90241d8222405098120b041000d2188402d107a26911220050704030b010b0140c0c83c022a4001d681409071400c502050080d0b103982840d000c04943c10741d0042c81050302c18000803066500030070820300c00c141c0a4400d81d6020045a41411306124903400760304500c0481d030703100b003025610780b400100e242d070f0564050400100c1c04001d000100d020164000f4039a03007000f005004130b202001324110083c0891071203582c2058501c3ea03a001e0042c2220746110301500803070f800b0490200003911440004003428441d08000446240010124554100c1500b080d41804442401070008103000d4156006d03400d42075009202900c0c08103200c51700c48244060200a1104454a5010417545004441e0107850200301c500d803a440d051103984103440f034549100701000d403c03840c0490064008105007050a0300541081c0b0f10a141d650100d45910b03410a03101c1001 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 666760368 1250 666759118 666759139
    0x1014092103060409020117270f120a2003041d07090e040c030b04060504020906030d050d051803070614010902030103200307090c2d02060103060c0c0206040602010c08101a09 76
    0xb144000003050040c1140885d50710b84200b100220078482c54501204238103507100181180c210800025004c8200d0702c03006110303450b01d040c0c035006e840303c0780300c1c0c2e080315401c2034002945d074420100040038000f11150b000302c0301c21803150b001c0030300c41040c41a2a4880000c0044006103c2c101c1b05207000c580140c0301d42c1070214441d6a94481581d200303000e640488643c1c0e105c07001e000a40c500340900c04d8100c24101c002d003c03000721000c40540359204844482c0080c0352220001041c0e8801c070702207084c1034002081a02d80c0c03088146029001840442c0c2c682201a045100100340e6410038403e4034142d83d0f02c82252707500414034880c500820001d241c07407240d01d40300e00140450040b05a008040121699440d103450300e100f414003440f03041750320320010840410b549010010b582e50009285046075000400010b1052521401300c900003003210000e50032400c002030006025a05500500f0b07202c1d080d590b83c1005841d009248102e54000d480b4440717501112204028102104800401c40701800401e416042c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 666761618 1250 666760368 666760397
    0x60804050d03090302190510050a27021906021e071202040209042d0f0506010e19030b10030302011401060e040e030d1109151312030210140921030604090201 69
    0x402d241031b004035819045101c0001040b811400741a400540b0041c007072011054031207800d0212010300100d00c0328088000401011b6403103468030480301c0f14101c0910b01110391a4000a075890b01060f45400306501941003030220444e001c00d840082c0c8074500001d00b080c1c8040e40030800070303422010085500c2076540414a140b11802d0202d5541e00325890015074144c0c8811030310b2011107003e03040e052142030411003008007603a440307910070140c03076400c1b100f0003100240d01c00c0c0d801003030104c0c0c0c100414581890090120900c51aa4444100d9100754000c2c0300642d580b9040c1149d846081c400c04000c02c100202c040001d00d0a500410041000c0e0720440c1e0400c00f040e01450241c861001c1a6046000000ba0740344807030800790031030003c0c07440e040b03030300e0345805c1200580f0340c0307806014800c03126201c070310003c2d00301014824050760b00700c0e05807400c062069144940c80380322038078030580b078a6003641309881035103140130080200c103d00d000740d80b03210a0030350f699081444050130b03403400124100032240620502 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 666762868 1250 666761618 666761653
    0xc090a0b1c0507110c030105060a050913050a0302031c0e0d051803060c1b030a05030f0406021b010b0405130b011505070f0302030702010801050f0603151f1701060804050d03090302 79
    0x3c1030089036161549503803840c4801e4205040b1129007406a4100400c1000c1c54840c84485800c981e0241e0b04d104e075030388d11109060700b01a0760b294000c056000708540c0380241a8004083c0420202d01c181d501000043d040e186405c44204613130b000c0840c0c0002c0c40d000401030081018041030348501d83d04110713407440440001e0401c80304a504460402d070100e48030302d600041513420084400030030001c1d032400070915400f9055010050840402c40402c0000034208080c1c7d0301698a400a80034080304209084c3e04018064490313040c6172405a490321000a15081000e00d0f00e603112a00210390840d140d003071056500041031082116001c1c80020885000020041204a040140079038069900c442c03140c8001081c00300c040e840310b40705403042d000560490317a40d4800c0742d0300207144000d0501b046154502082480c0140c1c0e0000a40e60307000081c01e03039400d03000404494000e150101c0c03450300e6070320781c10b05071601041510081c0c0350358400c01d208038125000382e0140103034074000c0c011a401014100d04204 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 666764118 1250 666762868 666762871
    0x1031b05130609080a060f1803031a01140d09050c090c0720060d0209150c010902040608030708040510050c1c020f010e1902010306090608070e0c090a0b1c05 69
    0xa00061000885006041654401501800c11450581d0615140040c0740f80d46410012000e428140c0d11a174812401e04030f80d201c4090045241910103458040d0306014004119a441e202d0a0001100c8820490f41c804c90301e01c0c1c240d01c402c0304014202500d5840031402040704070400c4601d4403e0440c64105969007514051090581c01c0ca01c0380d0300c0c1d2061400c00d10940c4020070904001c5807000d00c05c3c01030740d135450030ba40142d00e00107070042c0c840f424071000840c00304020681c01002500080d907108100c0c019001915054029039040c8085907844214503a644695030000c2c1c0032500501c02030210f0b00d0849000e203125501132402030b0400c1140020742d424901d8010313009114103140d042d942101501445030341d0f81c0c00c91020082002c0441c0c4202c40da104e1a02c0c0300d0031032104d9044c1d944802160701a40c099000b8014032034082044980f1108a141e845049008907034540200c0c400044e101a010703000c072500301c0c00142001441516003040383c1190b8000308285201c2405030500184607009502c20b65 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 666765368 1250 666764118 666764171
    0x2111030109050f1606050405040e0309101116051503040c090f05100b0c0619060315021806040f0b031302040c090f09091e02041104031a060607110f0103 67
    0x4203080b100d0a0843d41c0b82039840d0b1400c1041100e404d204115083d0402c0c251412100b040d01d0100d003101402c00d00701d05510070400e00f03a500032000030740c50b40c89030380c030003220ac0202070343c5000c44c2c0c0c00b400a504145000b200d0b0788200d50344281d4140072510562030034400303940c20522031080c0d51001500c4d01c980d8810380d200b003400f1442079580d400c01c002500c1154200c500041c092607060314a0940781d10407490312080024100f2400084100e54411014010b51001b80110b8000d42c5009190100d1b00048010b035000c2c1021001110381d46803c0001464990212822181c1040140740e40e035141203844901e64000515034601c1800560143d8056200d6000d0700e800c101950356003a051908200e80c085d003035801c0e40c2180041614084000000500000c100d60183e000144040542500c9200040240c00c11107a0b902e450500403500108120300c045015136044000441640b441e5075020030300c0b1140c02981c0000e440382c4401002c605c0541040400c2d400c20100615000c14054010340c4c981c40c0c0e1030503000c0c0d41c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 666766618 1250 666765368 666765373
    0x10905030312160519030506120a03031d010c2307021507030906020111070201031a19081b0f040b0409080a020309040e070e061c0b0a060510020106211103010905 71
    0x1000b40740da03104420007074070750401e042003405c040890140703008a18504004105140d5580045111a0740d00d10710312180d01840801c0f9442c0f0034075072a009016280d800f990849036028186001201d0300c040c00f880da20307041940c0d250042140050084554040c0c503031501c81d07640e501001701c600581c84024543d00400a1100d070740e5a120700614004240c0380150b03221200b10391420943c10210100581115000c81d02480c01041401d089809151400d003141032095110007216200745415400c05144000c42d0800000c0e01d900402000312024900d80d10030b10300c0e62110004480c40b40b44d00d801c3c3d00c0500c1c150f1000d040001c1e00c030726654030160b80381d00201840e0056440490401642c4c0381c41d014000c072038800c0c0d070043c00101e03140180342032840002511051007051111003440415411221054500341c000c40c2d221202e0038003c1d1a403001f041980522070184080428400e481d0b030050040e80c007142c98906c980d48205070303000c0c04808070100d81041140c0c000f141c9a0013401c5035509015200405002d01c01 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 666767868 1250 666766618 666766621
    0x1609180b09060307230a1707330f0e1018050f09010504230709060807020f0d0806010912050c0405061e010e0d0b13020901060516080702010905030312 66
    0x100321508030020000d5201e944007100a02070605d600c0340341c0d540000c3d070308804003506401c000003d100541d685c00c110304020241c8088200800d000643d801201c140708d003186000c5618a0402e9107411940b103000300011380c8482001c100ca442044912441606031901000d6600050700203002c5426030000b071030010b100004080354040e818003000380140b4040394400001c8500c0404142032076414807a49201d1035640490110707140702c103004952005240d140300030f0185041c80014210720128002c05002842041c0014416800000c040d07a400032007030020801418400400c483d80c0740020085070400980200010b110340c100c0c81d94183c8a07100d00081d05c0c00c80030100c18882107540c000d0100d40b050300100c0c65400b04811355680c10201100a02e014902d071410403010541300000000e0040140240000f049903000c0c01030300c1c00c01d44600c01c41740c03a000ca990380c04c4200c8882c080c40c2c0d07103104042c00c054071050000c4d21241c01821100c0c810f04011101076542c000290440c2c01c40408580c9a030400310 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 666769118 1250 666767868 666767891
    0x617010504031d1c050102070f200f0f040b150d05012d14180a02031b0a091e0f0b07030207050409080318072705060d0b160918 56
    0x1c000068541803015100160b5120000544008015003240e10513006a245210070b0090a4040380d0006400005001c8103904601d04010310041411224440040d40c020368002d41c81c0403000f17403007220030080c83c2055241e482020080149107501541c0d501204d0030314103401703400700e0002410a403220503000013019854010040950035220340c02003203150351a40401c081d002d01e081c010055a9044411135880b51280c03020074240c080603d04030441080c000c04200b0f10424a40055100d0120b4001c4001c112140089440280c06681640d2020404500c018080140320004c00c0d08821400240352120b40c0daaa81d420010b03002c560030100c0c900d1400600c050074180c0400007100140400c4d1410003d0900b20340740c440742c601000d0180752800500a402e21032b40941003180c4d4000d0140c10440c0c200c00700c044200319450f0401c45003010b0704a401c0c00001342440c6000b903080c20002d074005000200603030b2124004d210403421587c4a8051026491001c22802a55020078603a140440800603c060050 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 666770368 1250 666769118 666769127
    0x3060f2d030d02031207050913060306150f050d11090108060912070803070509010201090203070e18070b030403050c07121a0906130305130e0a15080d1d0103061701050403 75
    0x1842501d009030720506003026010303400403c840d02280580041c40c05a11021402c0301e191160440c42541310000040e5181000c40b16881881107a01c82d003400c010902e605d000301440306040340b040120799210f00c1c80c10085800c4c007a050040141c4110488403807084c50800050523404281c112140d180d01144c20854850002c2000e9541c155140e00a1401c1c00792a695402140c8001020741c0c0810002042d601c1d1580d000350020102c02c3c2e401800d40b072400c2d0322400d2420300c12404503000f0001c0340318090240a5100046000e50a546a850540c2d00e0b554460310300380c4456101d02403041551182d000c00107241d103075020707011040c18070a10340c500e0064070b542e8200a40440c0038220605075000101030000b00c00380c0d0702c1058001c55250901940710000035001c61003013202980441c01040405007004a6518590f1207142248803019402c103c054503000340c96641c00c0d100b05003102240b03964006a00040803d410440f1000c4140b4000c6a1181c688641c21072600d8120380017840d0382c0d11241403108040e0031 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 666771618 1250 666770368 666770449
    0x60f02070e102c06040903050d09060f0c030908090f010903050f030a1d031b0a1a0306120a0803010608040503070c03050d1d06041a0c03030412021005041703060f 71
    0x14040443c10451030001c0003555043c00303051548596a0f840700b0208040c080c405036011071001748402c01400049003891009021007101284102d880c2400304600d450091248452044c1c020b000c490403c021a0306001c0703001400710409060081d2110f0010002c0e5041151034042441500595181c00c007240001e004c6600300700c050105c482c041c00c0800c243c1c1e01d00158111003039a00d014521b080c03902200c04290754500c1d580000d07102071401c1ca8809140d400d041c0c001c3d4003503901a01c1012204c20303000798480d251620804020f014600c100010480c0d14454040b080d08280541d0940785085141da6074104042c9180c3e108540c10703040004210310480d0480c20002411507204000f08103040c11600007607041c4034070700400c07015005403000e120070480b10206942e94414402d0850380e6a003081d0a001024100381d04030b0130014820b01c142201c00c0b0015006080c015070303008880030b0003065007a641d040c1c650401889581c2001144083c04403907a00d01540c81d12144142c46100040041e900105000500 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 666772868 1250 666771618 666771659
    0x604080d02061b1213050106120317010609231801090f050106050910020703060905150c1312020f03070303031b170402060702011803030519020d0207060f02070e10 72
    0xc90340c5a140881c03c8038401c90301078425481e6a150240d41d1380c40c519110503080c500c0500550b02c4c082c0042540b02c1c05941c050b0302c280c06510350864481c0740e60301d2518000d2003400741000055030300f84100171041c2c074189144c001e01034580e900f280401d92032010540301e0507030440c40c0814503124801041900642d108044041014400910807036050080181c518402c4071182c030f0260316440800b01d201403090050401441d409401404a44410708020390345404001201c1207024030b01010420b00b22140d42200c40812446a4001e1300e546801540443c0c030401c0082a03030880d6040a600c0c4480c0d42c288000c2d030245110740c80011342d540020380c1001d40300003000104801c0c45482ca04140c01040f18190345035006504980159450b0001c1c80103d8000807481c00d60800384800d414040200764000300a024959a10301503402c09900b902c104903603580503560b80780b0150700400b50612400f40300d10507000c0380030aa8011034010716079917034049524140c110340409070388296130000d10490cc1c04103104004041c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 666774118 1250 666772868 666772891
    0x316200409030903080a0e090f041704030f170c16150e0d06020903010209060f0c10050f0609090313060c0203060105150f03190c020a1101140a080a0b0604080d0206 72
    0x220140c2c0c02800d6001a800080c0940901140302d2245038482d159401b001c80002d41000f03502d00b48419503003819001507074100c2d00c0d05060b012400002d07031200180d4049035040801c0b800d1094007a2030780618040380d1001000000000c1120340113035601080200002c1c011b41321807103aa60324040107150704a09903280001044510280c4a80d103135907504d00300000980000300141c0d00c0c0c40100002e402072081d0900b1a0b009034011a20b60342d40007011010300b180c0e9145406680200c100644042c0c211081185c00c10110480107011400508080300000c2d0703c440d1010031286001d0039107140c01540400e59100b400040c030768100b1710b4110b040502c007131401441c0a442c041c012641c2e8040b040c0090140443c10b00000c02d002c40082d4040348114100018403412160411681c1d410303120080d00c43c0140300041c3c0701c0521180700e01c10294410020710990342d07001c00425081c0407550303500700d54265020702001c1e2655101e0454002540d15540180002c2c1903900c01040d01146546010307040100c010001000c54 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 666775368 1250 666774118 666774131
    0x90913030e04020c0709050c070c0b0a3506030a1e020111030408030f070606030c0e040501050709060f20060702010c0f0503060a05060d18050d110325020303162004 72
    0x19a0300060b0700e03082e54a14200072800323a584600c1040c250040c0b103005812180c00c840700052001c001c0c4020504443e195807104d06000d480484401c1e500f002051041d4207038035640940032143d019103641c0f0f401c4a002416240300c0e00c030a860382034810f03802907602114480300c14070210841d0380005541c00504140c001460415217011100f640307034080d4071503c43c41036100280c0741040101903808a005154412881c180e00ca40380d102250b40040203e43c110385075803803c400720340f1050068144004842182d618100b40c0c06032000c040f1103802c091358060040c0300700c0026001d4089801d110b0584240400e40c00080c45c1d1240f078a00621b070852406080c0c007409010000e02030a0f84071205120300b95a402d0b43c805940e02241c10b000c04c001d00e820541c07040c4a070210079a43c01001804a142e0400007110742e502411000c141c200140c4030b115423220100c40b02c0680701d91000003001110103201e950f0005090700d05207490100c401002502180d021562003000406450a0040c40c1030b50781d510340c00a540401c000d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 666776618 1250 666775368 666775387
    0x40501030c0e100e13050906040c05060702030c060f120108061005090103050a1b0521070f060e09060d08070303140709080303040308060a080d020303041118040f08090913030e0402 79
    0x100b4074202c8030002005940542d5072040c0d02d85840c0e0800c3c07120f082c4806c000d180743c1000d04684914007a5000c44407144440c100060034949681520b2a0310340080c06041d09050030402c010450340b0a041000c1810424003001490b4115241928000e1041030041e00c684d01e0104004030000310741c2e13000f03039224414290050001c24800a40c181c031141e440341044210000c1694244002d421590100740c2c40101c020107200400d4401181505e0700380001c048540964441702c04998151490003007900043c0610170310b00d070a107001d4406541207a806044500886503d03107501d40c640c0d03c4520b042c1e0200c4e843da52102096880c00d10b50985c400640c1c600340d2015400c008050391644409040502044040383c04103a072603981079490070081c0400701c2190548054030300040e4807070700122015554800e403c1c0c0000c902d400d005a440001c031000101c1c0e503110369502d54a4150905828005131400c22051040b081c6980307802d1002d0b4000e20711a0142c0390501002e02d8000c00e4422185440c502450050005c10312 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 666777868 1250 666776618 666776629
    0x6030102040e011e030209011d0708070c020607060b04050709080c0d110603090705091009060f080c060a030221090f16060c03120606080702060106020d0915110d0203040501030c0e 79
    0x150b941c0c421400d5400e0303940300b04ca12800103440e04040e510034a00c0d00001900460310f100b4003081d00202000f01c42c90394800800352030000089a0000c04a66460a4080140303000401000c079988a0f440018181d064000428116241190100040313031002c85c0500a10208100d000c5d40300c001160004106240d60743c030704450000c4008800e0081e540032000c40c0c1030782030500466000d004040c21034101d43c680740d5401240700041d40b00f07101109117400d8000c9041821040410182c400f52001440c0140348102400004e0b031015680008065080c089184001100d102e481c0c400070700d0102d02c0540d0306041002c0e608003131408405808070303804288100403200441407030b10300f02e0741281040305900c2450704054503049000008203840f0303881c081011613050703003101300b0301c0c060541a801c441240c2c0e00c0f400103036074585462401c0c2d0f0114420520400c11118407201d11000000c01d443e1001d81405100044d6203044411042440580c20206051189507030502c2041c84108591900c00c04c1410084042103 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 666779118 1250 666777868 666777871
    0x111010b01120f0e0604061514090c0a051204080a031b170a060b27011407060b0d0204020c010e010c050f04030b0702010b060304060b09010609031a09010b0607060f0506030102040e 79
    0x71102e500c5129044004440c0e034003440c52420900d01350303650391816103000c8004003480811498810000c1e2800304412600344160305540001a0440c8000e40340c1c13541d48141034008001600c20000200465101c8440e80c42d428dd000740d120f00642900c3ea60b00c8034000d001e456100c1504038040c646115071031041944200440d0146c444800c0b1002c07151070fa0740308400640060381040c810880001090260704011182020a0104840d2001580441e0100465692403c4004c910f15045e00b4401480070072031642c010040313054000c1000d283c5106a0b40881c080e608203480f1018582d43d1668403402c203406c01e010f0850884030910301145404c440d003541c001c0c5400b1703501000e014019900f000410060003503024092a43d00100340c3d03a01ca02c1d092500c00090004c59040c03d000310710071000022441d0248140c14190390b4000500020303000019007000f07404800900081e0b0564982682c11010b444240c01000036901420740410302d011540c003260280c640c007400c80ca010380c1c410801044000110901e00c0d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 666780368 1250 666779118 666779147
    0x70807030b060c01110414060a0210020903010902210d020106050a0306050a150b03101536180b0d0228180506010f1d010c03030e0f010b0111010b01 65
    0x24070207185030202d0000d0042115401580d0328140d650210b88401c0d00181c01240d0f0240e0640303030b07102410b2040c40603500070f800e010790150b400090114503101c01034000d454458006000000c1c041920740010702c117216481101e0304064561105032003c11024840f801d9011424002031003240d2401d004650314410741d10001c0d19259079400841e20241440d0000401214562504c0320700c1502c444d0380854960041d5003458480162100009040c070302c0380300b03c21035501d10307845001c03a01100b8002031802c1c0c4121020b014081d440f0380f050509804e0b2412424010300700e003a0403d103030b00d20580240402c03100c80d80a018450021389896400507911502c0818001ca011040303062021401070380345001c1c88654006c51b05651074040d18000c01e00031688418030541c0f09981d0001100d0f4a010141c8540006000455010f503400340c100700341d540209200860207103e40382c0010448141f512550400c0141280d51042d41d440d078544040c6980d10138501d5036482c400c80020030011030000b001034800c4030521240d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 666781618 1250 666780368 666780371
    0x319080a180b06012105040303060612060e010b0a030e0d02010506030705012c030a12030b130b0a0504020f0f040905070806031c0e041d0c04060f0e0103110a03020d0c03051507080703 80
    0x4800743d085001d41d0341224507080e00103005501f0b00707140142c0503100900441d800a034418035000c87d002d090303014034022102d080013204501e03400c14902c219541c2c8412044818141c959048001c84402004040480900c0b82d00000743c504200d0105030608505078040e90400074030000310070004805000840e0400c1b005250307104400704000100e4100f50b02205c0241400600d41201d110154054100700f174104001c49410808000180c0100304403540034003000d0300300750009814805410705a000304007440200561506003004580e40e581164410b0308900500c1d034842d02071010300d80d0010112500104110085e10340c40d8003080c45150303039240c06206501007182e0240821026115a44207481580411000085180d0890940c0c5e6442c19000b080d40d00884c6000d80c00289034003460446e00c01c2e10007101c5140d403240d10717640b140441d44022980303050340090307202e80001c0142d503405000c1c058903214610480026255082841c00c0032a40002c1440400d4200c0411004c694040d103070590203015401d0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 666782868 1250 666781618 666781637
    0x9270e1b0f01020f061321050d050c0f0427023f150306090f0c040f02130305060109110702210f0304120606050f09180319080a180b0601 60
    0x40707107041c8030f13051044c0d0300780100024881c00c0e0100c00b0340d9000190044100f45803c4003510200194000c0e0301055000103a0b0501004074000d1841e040030350444880b0101c00d00301805404d1800030b07548954002c04d140074070102494503c0c20280e2040b101980110021410000c0c0d07210000c0c10400003074514092916400d107162640f0001d0380300121420440300381d1303d42602d005100c0004901e007603400d0301d10a100b07210019040c071a000501c0d03150f8400c51006400002400d1092001404120340c03000b868580034400b03204400700c5a100301d0300a40c0500014102d40d45005a08001c0310443c041d0800503c1c810041c0c070001d40c6030446d1012030190080c141140d081074800b8001d060a080b001040900d00001400140c03003d4884540d0000d940500c0c0c013002038542c0c41c0c041000d06d080d0140c0d40c40c0c11108440c00180c2c049001544201620a4507050f45e1034030b02445403180240c030911002601180020061244080f114030032290300311601c4408584c0bc1d00c240d04c50101e500c0c07004040718100510b966 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 666784118 1250 666782868 666782899
    0x7120b19120f050114090105060a2607031e0308070c20031603050f070f0312140412080417150c09060d18020415061b020109270e1b 58
    0x400c0b803020b6800c0300080280a81c5c40c3c50000b28410181c0d51041c80e0340c00d09010612034034140c1039403000c8074141e800215420302c002c071420754482c0c0c3d04103c030601c50190030740c00004144441c444500d10b0916611201e00d0754503602c0c01400d041c50203844207040250b02d02841d8005440621901a070b03c0c01c100e007581c120711440000914140c810811b860a811143c42c000040241c00107459925582074402d980065441c1d411001c4504000e11011300082c00c0d41a00d403186a000d00801a2640c240f03003581443c240d11040c10319003095400380d0440f80076000280c10040121000100d48203010b1410180611903500d900ca140c0007400a80503107800c1c00c00092103200b90303a4480407141d508680340414402c1110194100d000110f00250a0703002d9420011180200c0085010340e000b621050b031150800e0170300b03079074040c00121890b001c00c9050204a5502040e0410f904149420a403c4102c407070b51109080440312040d102a4900200c0c103520441d1000107800e44500c0e00319400d081501e1030406582c045c0e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 666785368 1250 666784118 666784133
    0x41205070b0403031d0616050c041808121e071d010906120b010504050a0f030506090c090103030522140102011406060703030f230a061202010801151707120b1912 71
    0x491075074131100547c0c1200701c204034011880c2c400c00d143c00c840c00c2204810865036901d0300e0890840040c0034034000c0000f041d0401c03440d2042d542021001d601409200d44402902c0c01e08102036803018080b500a070005007500c0840b07040c0c0e0075044428613141c4211841c00201900d0541401c1d0b11590703036522805c5084990748079a09072401400000d1403451850b546469013400310080f4007041d10140140c5000488a4000140c2a242c103000902154016843c0d07850483d000e81101c101c154101071203520b00d10342040b0b0b4500a0001d4442c0c64250400c020700140068211401080914011029102044107907640c0800ba58800c80d054100842c0810102d000000201100d11210200401800601907064044080140b1814425501304640c81c1c68843c1d404100611200003400100a04014810200140c01a1116015908000c06940b18007000c52142c928126104000248401e00340300c0d002c0114000e01c038465000fa112200c1400423200749403200c0358a40110019502e107920820300b0091007 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 666786618 1250 666785368 666785377
    0xf080c0c010b0411040e1305120309010f0504030e030609010522060207050a0308270d0309080c071518080d0f0203070506011d06040c0e0f030a08041205070b0403031d06 74
    0x3e1040114403d10144011150498000e03200c00007950000940008050519081d034580c2001c010451500100002e00031588000e16940c0340c1d540322104d103000d0034500d015450103184a51078240013030180c0c205061800e10000c2101c1810703030411081c4454072000d5040d102c0321615202c0400c6002e69107003040c002030301c600c2c03500500c07900c82e25889030706044d48001120f000b21a0b0180c1903000c0c03e038601c4482e51055200700e080c8503941140401410450103039220035500740c445c08002d414050071000d11070901c14039500c000416040c20045940f441c0e802a4082c5c01446030000040d50203003000c0e0300b02c0c0c1d03600741c0c4107900007400038488a05841600802c15108401d90009c1294101e685807c1c00d440302c080710844040c010401c100100c2d031280380501613050441c681e591024810009503003080081807003280d040e038041c00750a20620100f100b0b0350080000e465807402182d661300240c40c000345820010340c040600c085040c8800c3c40043d501103600e0900809002245007090300c0c0000040c5203219 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 666787868 1250 666786618 666786641
    0x806010305180a08030109240b07030e041802090606040e06101707022d10110415021f060302011707020115031407080c010e13090209190c0f080c0c01 66
    0x2440f00c114040045400055040e101c45090130f10480f112404d01d40c0900d504482d103040c01e0124808107008917005180a0222140645045c41c140c00c05c04c0f000c10110303080b05081c1510100350300000700641c1003115440740c02060544000345001d1400c41d0009507040c010300550b1090780040ca035480d80c01d100d03140610007500e40c00f0242400d8106408040c4d954801c0c089091103515560120402c4212500207034406808180c016110400c460003102005124041100b21303188001d0002040f241e00310301c088109860141c0007000640307d0300072a410400318446d0b4004d1403600340354040c0010303640034450000b08810031108032001e48644500b40e02505c00d000071000603100081c4000180009101440c2440b00c07000c0a41d88126211503105858101a441960200f4003e14283c090b030304241078008042c140c01c0800080002c83c0da13001610200007994240c130b10b182091030a040092480c4070b004a8a40c036820070340504042900060001c20340180602443c03000480d008001100071f4000001894 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 666789118 1250 666787868 666787873
    0x1003030e0312120f09030f0412020d05011104330c030e040903121508030f0702030a150608060a0e0a0f0609050616020c06040b04030b1f240f080601030518 68
    0x43c200c0318141c180020480e5400281c40361640400d2241e0004412940e24041c1d14441c02c3c075040c00c001c40355002114260b000ca0304500307400403020100d1800c0c801c0e0000080c1142070300e5034031450300d03107010440300103000150191904501194500300e5130f450f008401d5010740c01c00d43d090300d64605042c0c7d41e1040030700041e5042800c1044003020541e21581d905e02c400d0704030008020302c0e041d820060300e03400c180307015801c541e034010071440d180b082804014002c640d100400311819a0740035542d407100300340500f0344007102c3d603107070b00c003e01c517001080c001c4950200700c01004101c1407180040e031a6940c0c1080130003070a90b24100d00c03038100b4003059400040300c4039002000c64803070703080048880c0d00031104885000010b0195030000b49040c6000d10440d01140c15441416003002d007187c0354002d001c0406003d0303011500d091203002e11070040b041905030003400740050a803c9001180004c0b4890405103510008000e501142c44070010b82159034280c02010a1800003210b641c5c081c000c64100c1c511568826191 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 666790368 1250 666789118 666789127
    0x4020a09090c0312111b030a080c06011a07081204060e061302010306060e1f1107090b130626010605040e061e040b0408030c0d020d140105091003030e0312 68
    0xa034048080d0440344105581062400351040413140c1e5040743d110126190400e2402c1c40c10081074001c0700304403d034001c7c00e960070302d025613480c04000ea000c070700c03540c1d6140c010100400a5280d0700001034240d0301c1d0341e040300c0d24040007070b0359000ca140305080c003801b54241204045810720020384d10521240060307500b1130302c503402c000403040e854070060a82280003174100040414135034462405585100d20140c140c0d5500403441c48003070112010140e0140030403910b18002074004104001800051004010000d4002408002d03c00c040765504108000103080c0340e0b003040f003d8103103c0e00348207070b02c0807a030765000c914041308002d13014003c0c90b803000e07501c1420001815030125000c031b00c00d4029400c0c403013070002800d40456a43c07541801140d024044002601c000f602003044200250b501000159440d031418070081420401c82c1c01034000f40400541d91210340810441e180110303070140404403041421854180d1030f0182c0042a4080182041041484030101d03031010001e0784803401c071103900d440c0c56 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 666791618 1250 666790368 666790373
    0x21504060504022e031a0d15050a021207030c090b130e09070e040f03020c150706200904020c0304050d06020a1d010804060b120106030303020310091503020904020a0909 74
    0x50203003503609130f228241080c40307140d00c0f800141d0224054215041c00741c040f8a1240c100b43c009200d4008030f4000180e11041e10740040c1e60b007502d2950400e00c105004c1280400703207084d92040347c10042010340c0e601e03c10004039911702160907000341d00461615000c84d00301d1940d90225031043c019406070f29a8100400c00d10619598070780040240c4004407000c50040c0d0360075540355603408041c419101007040040220b0f0115042c05002d01d6607501170300403501801c905401003015004060046011104080383e003c2c1040301c14007982daa400181401011082d004200000180c8124101c0601c03555002031201c02e60142881540c0003481e0041c04400c200d800303410100041d601800f84400090003000c2000509102e110f0900c02098060b9180c81c1d26581d50b543d080d0040100700410303903005005800055172400309000f1807010714440d030350158803170524070300b200e60300704442e00040070660400198008400d60848210100ca404590010766034441e800401d5403034a49401150101d0b0401100400f03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 666792868 1250 666791618 666791621
    0x2040e07081c02031213080c0d05030412020607092705041a130804090b01140711030606060a1409040902060a0207050109060c02030a060b150d060f0603020406050f030702150406 78
    0xba50610404030722440007800b0422602c034404c1601c4800f40c035440d10701160f48041d1405c1c81d4503841c1c0c850314109182c1048500c00e1860b21082d0400030b000550000200006c0081c10a140204000c540c0014141402c11400103013109243e0b00400c0c58000d028800c00005002c8520107000f058104001080a41000c0c00c103030320348109160340d0200c80d075200400b0450b40c01e0507240c10302602d90030903880313030416041ca96050050a01c500d00700e4104555401440302c2c06191400030600d40b0302c14094001e161610600703240c100031000341313924410001030185049054100e6560f079204602c02c0441550703104038400260003050003010180d0041c0300821201c0c21580c00041c9c0109884098860806c44e6944420840d540d46c11240300942640045030300100142d4160400340043d01c00400140d08681e02140c1450203402040c903548501c0d440340301c100607c041201c800c0000e0440c07880c1c00d510342820150090200d1013013500c4070012403800800940000d00c06d00284000340c0c1d03003081c00c041d03604103401d0a00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 666794118 1250 666792868 666792883
    0xf021e0909010816150e0603010603051005150a0507020a030b0f010905010e01030314031315020702040e161a09191422020a0903050109140d0e0d08030402040e0708 72
    0x5000d1012000040f0b82c64600155004c5444007000800b140f031403c4c101d800d180f80c40300138458010702007840070488840d0b13140c0703002e14060203495074002520300d0848820941c000c4168011406000c501588540b1808244100c40070740d5040e080c03145d92ba020034808500904815800500065028424400245241c103c017604032240054203001c00d907241d007484140c2c1e031000e1000401040301c110410501b4408180915400404c04d1079501003403038242c50326a071040c0180c500c0e0f03e40a500048010851070948140e01900c01c4050003030080d81c649241004411a9a000b40c800c01c0190151009000c280301f13044030103050b0007400b0308640280c1400c00d18402071030360007000c0a0250080703005005041c510010144024030300724800100c00210b207044002e6008048000c00c03c0306513180030001c83d90900a1220807840b0700f0b0a0412500040595800e0403100300404c410880040081112940c50b601d50b201c525401045040c3d0700d490b075100040082c01180001c031040e000311003000405000101c0c056 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 666795368 1250 666794118 666794137
    0x14011e0b0a0503040b1f060f110a080c010c020304030b2a1804110a121512050f01060e0f01030825051b0315130c2304060b070807060f021e 61
    0x40c0f0180d206c80303040307080c1301408904012244410107010054140700750460b1032504201d0900c50545140900b03c14280704880c002a00c000e00300141001c001c2809200320040503450748099818681507907541d44030b80c60060081004107122085c0441d8503801c0361140010444580341c010340d2850b540f0011104903070705000107442130b03103000720303c05213500c0c2001254441034840e5119a13620f584c0140c1c21009188280071518191504400465174040003100300c908c0304c0c02240280284140600c403282520102d4202028050324903080c0a00019003081c501d0659070701005030703a2500e202c130a001021100320421071003200d860032042418064086400b40d461900340f4102130302a12a0070506550f0800e1201d018042018140007034200072005442e41041803140c0b42d804003039503842014104a4035100c0704400c0c1c00f00342d00500e100525092144d00000e00c0390038030190404405486580702801a40800340209850f8140c6040301061a4120b841c83e101d90031031101c50780303880c5003400c50790340008204 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 666796618 1250 666795368 666795383
    0x6180902041401030c0201110d020403170c0d03110d110c010501170a14120a050d0b01020106030213050601030905061801050a0b030a0f1406070806040f14011e0b0a050304 75
    0x820460068021282610701580900d50000062801140109a0090160210355852400111746a501e500801100c41700000241c0c032030303055081241200c2c50580303200b02d000004000c50401203002003070b000094211030900041168141003020168031505142ca903000707262200000007407810354041d10907040c40300001c00c2181e803030b1986410440c0741010144002e9014600e424001110032805006440641080e1104200400d20030305240c0c0000e0b01d00004542d0105698058140038072035442003020910091110301d1131034011603196600c80441b616020303150000030b44030785d001ea0002c105084d8440b080381d1641c03900503c00e000034500c108241009500300f002150755403516008040e2075072001800f428900b09079654000d0300e00b400c104104e40480301e40d0307443c420b2039005000b0f440c4201d2031a01c817004d0300d24103441004120380c110901400302615014901840c4a0b10302d0b01d56064030350304002903094032001c403a01e010a030019808810002d42c0006d41e503044a038001b0245008605c9a002c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 666797868 1250 666796618 666796667
    0x50c10031b1403060f030a060e010c080f1603020f1b0c040b18061215101809210318110910030503070605100e07020706020f0f030306060a020309030706 67
    0x1000c88849403a82d2120700464000d1020800520f02074500f451102001412100c0b6158075645a03400d845020301190103695641050a80068000800c9903004901c240100c14130700c0c14442071401e0058404d07040080660200301c04040340340003012500903442604840c0340d04507015402d10781e0313050801c00640c00707107082c031035a5211410705409040301e0038510300900c90305030b40700401d02c030050b8400d0100b142d00b842514040900d810152880b6405410307403070004040503041141e00350414070b001128140c400e18003074600780412400248245103160105100310010801081100078003c0e003079104980c1c0d0403042c00c0404200030030030401426401910301c04c0302556050342c0301c20900071921020700743d0f8100f00414000510554821544850800204000d0316204c0b120215a081e04403544400f690202e2401e0140c00c0e0100410107400c261540240a03062070001140e03100d00015016900425021a441d12090300910036904401d10140441e94041e0741c5e4000200440e4045190308130b50262401c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 666799118 1250 666797868 666797921
    0x10e0607051f0c0c120203041206021206060f0a140d1109030c0d0215160c03050d110309210f030a092c01032003071419050d0f050c1003 60
    0x40c0035241c01140c1c071303000c801c804c198031100c00e00000410900c0440c00200000f0aa0a1000400384c05903405440d00603120b03482d5600c1020349004c0500840d200d040c0a105942c0c400309031008442d045680c0380b40c00040280024180b41c00c0740285803680010030300f000300b07810101c1100e8025299840d030440880300d140140b4024080c0780c82d689400030390040c404820001c48024a0340007852450f507054141c2500074029210401143c0594208a865801c00e81641c0c110f507510003009510300000c0400307149001c405400240c21540446540e5500381701010fa042500038042c0880a81c034411034090703030750b0340e0710001000f045010b96019800326980b000c0848000002800e0b42d10121150880201c0483c0c0d0840d1501c21942d07122464414030401c0031620307840c5c01d40301402641c004101c030002945505485000300102e090340c440d141468214800c00401c9207581e2500c8088503107401a604a00d000024140182800105c004068100f0b05219040205a80c998040121004140c03070b072080c12114103 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 666800368 1250 666799118 666799121
    0x131d0a03020712030929070b07020618030306120c0d051e0304151407150c0e04090804092c060406060e150111010608100605030c01022a010e0607051f 66
    0x844011340040c409140c14032221001346800c960009001052000645a03052914441d6200c03410441e000c440340010b01565507010044e0640000c040c0b03100710b9508101401a030380d00d0000400c2e5501c0b81c08181045030188134140240f10a401c030191086880b0071090600583d00c1c50100203061035095410070404402c1008020b580070349030032403001c15134124021400c9842c8548801c410b030a16208004250010f0303240021460200c1040102140040000c035026242c56952503a20303000c8d5052924410014100000301c6080d07950f100800120120414201080f41000040c130a0440c441e4210b000054a00051b02c42d114a00c01c5030b051000d40d4480030380102c0d01380142d1300141c1d0100c043c802c1000b2580600004d500001d0b107000001260341c1e480080916113112a024050700f140d5400307040c045410140044c0200003000c1c0000d08000350308041903000c40040212a03d6100701400011510741c0c07044050504603400181440d0b03d48017641001600e03003903a240d981c54444040141d030040d11409 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 666801618 1250 666800368 666800399
    0x20c090c030406111209060a1b08010b0d02070c09020c06060d030e12030f0d05011503020a0203030408090f1f02070f05150d0f0903120b0301020315131d0a030207 71
    0xc0204841c1952255030700c0d8805000b0f0120104082c0c28140104140858030119039441142c90708000c1a00341481809001202c004030350032190802070030201044075800041141c111740003140865680c19500444030024010100000d044103003140e170000d00c00003660040c3c0060070210007511240d0b11030b82d00700844806100001004561b41801800705407401401c0c0784e8a404059040c0e924200d0700001035183c0d41c0c800ca00541b455a5920010f201d00980303080700040c81d86580c14214a000c0e500390000e540c900000344010311145000600c80542d80300c100c201d00c02003a01a1408081c00310041100302d100a011030f088006200d48031001136032040200c0300004036000075108101c44452003000c11440e900214505500980302c0c0b2200c41665004d114411120f4041d66078440c400c04030b492030009503000c9450040c4641e0050003440048425400c1c10003c1c48012075000492a100803c0709000e8160321280d032401040480c0d00003c5014046000381703a141c400d60950b220140c881d03858810b10f441 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 666802868 1250 666801618 666801631
    0x70f03080c010c17130f051c090b130b03040c05040c05071a01030201120902120607090f08060f0a0b010314010e190203130b070c0807050325050a020603060a0302090f07020c09 77
    0x416000c41c80390b03150105c124080b20300075010071090307189a4480d2480c0c0780c2ca40c0c00e10501824403035184113070325034081d1606c0301414040e4201031414019085102140f80c06000b050341e00c05000011400b040781d0f00039102c00030400600244800c01c1100405005038002020a80b0548400307841c403110b070076002d00200d050703e505031920b80d480c0c00f00412440c001c083c01c4a089030040161143c40040300d0042109621620250760f0300403501c0e00b0410080c800320015405000c0030751058045c0007550b56000c070403d900c580b2603d00092a03248241c0101d0140a02c00c480d045070f462604000314443c2c1c20818000d00c03603000740c0080f00445c1c0b5100c0034082240702c00c880c07200f4801d151040100000e2041060560001e03001d10f440f13041000d60707844080456001030421981580300140c005200e9040d0f0400c0c1c40610091302c580d00140d115511080d0320703007040000c001e00c1101d0001c00110a9650042540003464024000c070381e070380c82c080c21140c0305c08800b80c42e20b030302610501d10301198518004854510904d0f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 666804118 1250 666802868 666802907
    0x120509040b0d0521040b040b0a020d0807020d0f09030b10081e1b0a030209011206050105040b010c0f03050d061d0603010506012c060c03070c0e0c0703050c070f03080c010c 75
    0x10300304c00441c81042c4900b00c0f1182001010040000c0039550b0601400c081c00c48203c00599a11b01144042d140ca040101c8420501400c030703041040302900848c10141c64005814909004002140d04640000349a00300a184013011014007a89000e110f09103c240c4134444102c0d401d00c6255064013201080f1490b0340b00540c1d2103840c1540d03032a003100c00f0185444102802c001b400d103849a00047d26a40d090b009020091344104404091007220700038540105802e84003084000340d03240000303014502c040b101901c5a442510800c007014400c01c120740100801d00001c129403a00c035010540c1901142d00880750b1400200c010400914040c811700c0d0080505844401203203040d840141c1c4901c40001007003891550f040b02100e61790301c3d0b0000510340421010003455880c540d034503120700422125040714042d60300a03810041c0f04c04040303048131545a014202181c0f41e040e01e000c1180340900e00d411401c0c51240b203440000401141c00040c0410300c81100003800502030ba19002c985490700d02c10f24001c3c00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 666805368 1250 666804118 666804133
    0x9240501081209120601060210140105010c0206090315070c031d030a17040902071a070e132a082e23040e030a021b0922120509040b0d05 60
    0x441ca18010a01c405002d41144c607080c02c1810b106007480ca090b4440b0300560481c0c0080ca44c60f100c03901c190b400780556054103a01550505000a1140081e19002070007070720002100f0b4010341d002c00c0712004440c600000c02641d4646214020148000f00c2811004139206980c401c032101c81c0d0420400c0e0068018008000f12100d81c1c440b44d102c0043c491078460108000c00000ca9140041e00060011174090380d82035002d0108861418980701e070081c1020104412494100801d54034802c40e101d6950384854045102003803002035080342103003580100c196426016007400420341281e14a44a0900c00012003c1c100b4489240d40d00c00400407030040010302040c00620130300f400300840c802141004542d082000400501207401c80304454814491984045174046c90039034104103204c0340c80e1000300312200054003c00070070341c3d050000d80181890303034094200c120b540503007400701d0381c0454009042c0c1c140c081e140d1034090300e1640318411150042d41445c90542c41070070469104064154002c00a0400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 666806618 1250 666805368 666805393
    0xf0305060906060703050714030702011101150b090316090c02060105120601061211131701020405010c140f0a061a0f0d150e07061101200d09020103020d0924050108 72
    0x41c1e10504c1d04805011080c003a103c0450f4001144036510260321004541d54152800050b1428510010350780d046e80c10300007411008201984628211a40d507107515440b114040b0002e4103000742c4820010300051921800900b205c115004016440c1e801d03000d59880341d0b03c5105002c2005451804c0c440070f0f901960040003494420035a40c4100841d4180c00130780a54185400345c4170307a00003c2c150001c0c9a420100380b04030011700c070031111450182c5001314501481c0400182030070040180180c164410402c0005442c003090050000d08010f035001d44000c068140340904c000c00110003020340201d80014a01045d0a00b800c054000d0030004012000640c081d6851200702c907021a807109490361144c4581e508246c3c00c02c44000034154035225101d007494042c1615003180c04e00400d000107803203009a4032012189080407a540c0c50740001c40172850360301900050340a80710301050012118644403464041c80b00003040e11508118080980c9245683c8681c14810b581081c010500d1036044114034500 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 666807868 1250 666806618 666806629
    0x30a091203021603030c0c0e01050102121c020708030108070503060601081602010e1c020c0409020d08130b0315040c181401020f060f0f0106090305030901120f0509010c0f0305060906 80
    0x44061092040f1800c1c00900d41c401142607119034012404100c020b800c02c01004082e001c50006440c00f0300c0500a59890040001d5031a44514242d2000325800a001c0c00110707441259100e4441f20075170203550303d01d0703c1d2400c04401c4e402440380500d113006401c0d010826103008a062405440140d40d050041e03102c031030440c5203c0c1407046030b90f0107540d40c4403410070282200340f0002021418107443c50f1500b01042d100641010320240707015100b41e00d00701d595401691042c0300e103980b4941181c103003612034100c10f1174007110035030b5500104104000842000a14603000d1249004604260381c1804050b00400040e85c05841e84518480380c00d030105070038031485000030800041a5414030403503020000f103044041c107203401640c200ea4844003582c00c0000c0202c864642a0040032a4a0b18030509032075611041c0c0c0300d02070980d100c1d0400c2040c04d440201240d490300012a42020403074100314904000342c003180203040b500442004900c4100c400c038040c500030701c01c2500c03901c0c02901c0d031407195035154200306 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 666809118 1250 666807868 666807899
    0x10905040515120d02010c0801081c050417070617040c0b18060c061605161e05010f090203190515070c1a091c1205270717030a09 57
    0x9000ba1401c0c1d003248640d076030203c001d8501c10300c42d020f8800c0e0810608001c0c02e507041e81ca2001d042c0000000104011680081c041c504412002e00b4080b43d4940e06400b2111807240354051443ca0101d00d108031410440803450704219009034a8942d40c07103800f0725400003280d00c01c0b68040c1100b61820780801c0786d165140c0041a800a207042c1201480341e040c80041d0f000c0d0050095081c065000030304118000d079840d60303020b41c985014141281851401040c1507440d00c509032000b80316500c60504403074030f00210032411004540c071100038031888454003410b00040c02500000da10a01c521840100c2c0c030380c800d004041140c0d4010014115030003000795503404c150b102801c1c2c14204200c044c02a0040f07405940403201d88040c5101c400304c00c0c2801c0e840c0614080700c0d01c120b00d41b074407c011054004103400400402a40451084c0482d40713545100b5102a0031101031800c62080140301d92140c60700001050003000d40b148800750400f01050f00e00656030300d0085038590000301d04c200c0814802100c0c1c0c0a90720 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 666810368 1250 666809118 666809131
    0xb030d1224080c0108190902010c020d080a0f05040f031e0b040f030e011d1011010c050406080108010902030c1e041404050d0f0801060e060705191502090109050405 72
    0x220303442885001141c910381000080c07032500410120203100401c1c041c03009451411003460000840d003840e40010640c07440d1442c031044466034800941741164000c0e43c540c01240d030000c04440c100000381c200440c05034028600040011345580c5005200d90140068030103443e152941c204000703085540e81051031510164407040041004000000900c01c0340e1080d110f0382c4aa04040700d40096803502412071055500300f14103020301e0100741043c0500100e600200700600f180c50322103112001400361a1140c003089101d00395420f1142d029001c1d50054014022504c06984d00070840e03a88001c3c0508850001030007c0d450b81103d0741c0da03440d40c03820008038008091f00d5450500035040303d10024049400840c0661040400b40c4100030602000f400000c800450500300300070784100781d01d40200710b9001402440b0502c6806000300718a900c44005540340a81c2c07110445504440a00309459406096030089807607000c001d4200492041074000c0d43c000c124180c403566481c40c20402040060040200745 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 666811618 1250 666810368 666810371
    0x1210020c07120804051804030516031e03020315090f010b09120a0308010302041409150c07050106030b040b070c03080a0b040b090a0f052a0a02030c070807060f030b030d12 75
    0x20416900651002c1840380c410441075655a20708401c2c01072014034000f03200760030032441c4100310200360060704607130f022203009200710030b0307146140313003e9480b04044525200600c4000341c03101ca400303406038019401072994142c0724855003c500c081022410040320b048018000c004d00411040e0004005810041d10082c40c1011900844140d5442d18600540507000140810300400940c00c081c86030315112015001500c1c01454001e01299542c000810103200d03169a10300015182c1c001081a20200b81e0b00c50300a0007110350b00d040c4001e01c50020740e4299141150035020030300c500d004040302c0303200c1c070341c113840322121a5901d14040b40280401549035420a407122090780e2075950344e418651182072b1141d00001d0090030700c80c4800403504002c144980120007154040703d400380140c000da40d1040860300542d03880030302140881c214010414034000c584941640401c3e240700c0880c806044d0703140d0344c2c0e0702203240d139a4440803400d1740c41c501c0300b45416802020103045801c0c4200c5841a29243c500300 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 666812868 1250 666811618 666811633
    0x6140c010908070c0f0b1603110705040207150605032b170702030d0f0606020a08030606040306021303031101180b060d12030606020708010917031b180f1210020c 71
    0x40b05411a4400d840841c0c00c03d40f103400501c039180058524001610008090398100401c03851400c103007144000f40601801480146408924010002072002c4e180281080d52034040c145003943c004240103000b5070306c45007407800125207410300017200c80032080c0005001c280e41e500c4000700d004120307410301241c1c02c0021a9441c04d50012107281181c0c081c40365603001310758a840e00070a030411079161141c0b260150707007070050820100d540011881c19081d000107201e69030703450f0400010394922456100030801030010a288032036031801c418507000c0b02e009481e041003c1400c443d5003803c0360602c0d4005507816481850550100f40a001100d030300501c00341c0500e05086194803508120f904144062002a8603074030103110b1140d05100d9503000f001480001d020101203039a4040900d15940c503d20b250710400300c002441e0000d4011842001c001000b103096540000c4410405141c0c04100f00d03e0040510071010401400c013a81d117640d11898100150036a8070548003280042d51120700e4000042c4100403 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 666814118 1250 666812868 666812873
    0x8160302010f02161a04020102060a1d0d080108060109060b070602070221010c170c0a0f171501090e0f0105090a020918042f010e040204080d032406140c0109 69
    0xc0241420700310119207080f0881c85140000d200e6045c02c1202071644024030078040180d8001610315041401c03050f004c40d403841c10703082030805d00391703c500b80304514032481c8001c660081c1c0000944c0e060b01c5100040e100c1c60381e00d51048230181c1e40d0610404000400400c150b001141e41503010f4034121b0b200500f640ca080f2015401001d609031091a80d002e281d65a0b9090541550415a065240d80d280002c00f0500c0c0f500e4072401403140214190752090002c3343c00350a01c06442120016412a03003002c114401c3d040907541301c0d41400400e91014007107503035040042013044506401c03e124069541000c0c400342e003030000f407144083e4040d01d2001d5440d003d1281389207175038502c0c00100b01780742c655114030098545410700765080c00700c0744248504a14811001c072240400d01c010b90701c41200038207140c07880461010104000344100da0041d4410300605c100c40f041e082c0c1c560040c2601c0e10b10344040d000d8012141d90402c0501e0641d208200c00300c1c9048038000586440c4d400a0310046d80c84800000c0c1710070064 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 666815368 1250 666814118 666814121
    0x3020103020f04051e0405071103161704090524062a010e0a0501050619120c090c0e010e01021f0908091005030f0a0501140112060902040803040501030b060708160302010f 75
    0x3944440b800801c52041200c807806c1a00c01d150780240e10f0f14140c040b24083c120a16145c0c4140f101000c0400d25100c080780500c117014030000b00c00f00081d00d0300c40e907503a0f507083ca1100030130054902c1703490303003104070400758980e100100d0340802040c0061555142883e003c00c00011500d0000c003103806007004280d04009907034207200c0d002c03880551a02401d070b5100c0a1403c0c2d401c5a400407c5548140307418490528043c000c1d1042c0d5054031035080f1100c090320356500740341d0100d0345e1070703804013100c00e040203036007280c080d40503562801003203080c0c984001d42d14503103005a1304c515030359241aa003401c001c1c2d268039102003140c0007007409034000c20520785040001d10201c1c048039060310300c0030003040c2e000040c40008100744101380d5000c1030040e000c10055041c0804034411060010f085410846040c84481000301a03921510041000f25411561241c0d20256a9180e40103440380c00d01085c0b40580d5220542050411503091507407103501c0d0362800106282c0b08021100c1c10b4015021036603104140340744904a03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 666816618 1250 666815368 666815389
    0x108070e240f040f06092316030e012d0c08070c020d1713080a080405060f090a0e0726040212070f030303090b09030705100c020f0a0b040c050a030c03020103020f0405 73
    0xa45030045591804c081c2c0d4a42507074260348810b141910000c07c1070005040400450390008410000f410707102000301c00c1103014009601d81c6050395441c03d05c0c0c425080d450074440c0c607401c1c0d10140d035024032145900000c400303e41d001c1a260001c00e000400094000b403103015001030071840100f82c0d500b509110b0310381c004040392407513681f502e1550000c1c0182002501c42458030007454240010000c1d440f0030342e0365403881d010300c3c46510302604001c15180200b802c40c0b070544454480242a00b4a09030380c03000201292101955240080754208655a10350200c10b88603012808002c4914802034035280d09000c500480741d80307c140140900480810b15502da400b803400198003075131700400c82d11000c0c1001524040d014140081d15802040288009103001c10343d000d4051300c01c280050490350a900c264142914605403084900501526804220795041b00ca03025a0040701d022080c40d4070340c030500c40355504900020302450260b0104200540c42500100050140340009506290741d402c04203400460 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 666817868 1250 666816618 666816641
    0x170c04170607090512070b1305100804060c110a0f08190f03180f0209060a050d0602280c1415090a0302010b2b060b090c030108070e240f04 61
    0x1021042c0700010741c0c0080d2000180604640000c0c000782009010360303a0f51918412100d144d8000b02d000d20300c90b0303c2c13814044010403014000483c1c03052001e400802508044400315003c0d0706d4000b450030283e02c2000101d400c400c80c0310060600513100e848035280d00e41c2c0d001003100d052600704900e8500b01540e408c1d4552070710306034450b2000d007103880601905071980007954800c03054402c5050720208182d03031081d603601c2e90156603510361512034030081800301c0c901740c00194200d281020030400f001299402003520302d00c0c0343d1555a040c2041000d0b0042101d1002c213031000240c3d2044100040f880100e0701c000b198175201d007124103003840e603486681c01b20421201003000c1e420600500040c0f540a002e01d0b540314070122920700002c40500c1e040c05441150240449549003180c5e40c2c04204070242c0d000401c1c5c3d0b0001040300c4030074030b0180c9000005a20902440d0304074010b14900041030300548003064000c101c0001400d81c01c0c0260f8080410031010002440d5001455041c0c4034000d0301c8038403c15081c42e1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 666819118 1250 666817868 666817873
    0x60516150f0c020706231b07030b100306050c1e03070e0405070f0201050a050c0418150311152b091b1403030c031b2107030801060f170c0417 62
    0x10f292610203005c0355842428211b0b02007400007810240440d0b8000c643c50900c52513945003031000d4862a1030310300006900001c0060f051042407181512602500703004681c8203441c1884695100600120b03a40030360003480c1400d50307403a01c10421000014014580c00281480d10f41901c040c8200060140d0388184c6414000c40c178000004d202940e420f008082c0d0141184105110fa410039880d248036510552040750748100603440d91810300c0404d90018441c0304008419401181d80303034140a000040003022540c80340b8100c80e0110b00d01c007000815121049404080074400300c8204203200c6c000c00c1600c20750f41201e0759410311080017071040030038035003082011802c541c562030625030203007010822100220701c60380c000c0c0003650b8044400011030300009403501008001c42030401c109890104007003080c4802c981e5112600390b410208078064a40c0c02d000b56039018460760b0301c000540b900301a0009141c005202c504001c011000d0038900c4a41060f50503261b070389042c0d0385000754905da5514483c11079164 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 666820368 1250 666819118 666819133
    0xb091f0c060b0103050402030c2403100f060813060b0609030a060b030c0301060f09020d0e03040902070c050427030e031b0306061f030e030412051006060516150f0c02 73
    0x3005100c2c1c403030300410a08041050b4101500082c0ea40d454035520684a04c64141034201c2c10f20b10121380d0315030810b0410600713032241001000c00e01c1c0d01c0c80e2405203001d0a5000c84000031001e208030b030118000e403d000d0003400c0d0605186c403850080d02c01441c00c1a00840100300820b566101000400d403410f006810000c1c0301c0d201002018104590360019520070780c10054140404440601c0b0781c03040b01c2c04807600680d21010160304401801001045080d68000414006044d140c10303001810117510851b01c09440a40381c40410048580c0c614078544550400100c4c60440c00b12594403524450090030490075907040344001078507084400c0075201c1c0766440034826002071b040402416800000807660380c1459500f01e100341c2c00c0300000070300403030401d502c54120180c007803000c0c002c403000340a07482ca1211103207100e4105140c0d0f035003000046400300751500500060051040c41900c04254120410030510421030719908003403182005e001490555a05058240c07180c1841b41d800038101a03000b40000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 666821618 1250 666820368 666820373
    0x70c080303040209101503051009060806040614150121020318070503071203200a06050f07030b030318280314030c0712030c02100e100314010b091f0c 66
    0x7440203003000044040a51040c014070404400d8600006c2440c9800100c1d96035548030f00301c41c2c0c5956800f40204a14204020400c401c020690a22441c01950700340303c0c0c00205064050303010740841d6440000420049200350795031080c1043c0f5184010b002e601c903a0001101e52603000c3381c0c010b940e42c0d5039911005101c501c070990300b40100c00040c10210080c01c05e6074500f18407010728120100c0b000381040950840d00f581044901043e8542d22800c50403120010490b00e804d8000344401d03280850103002e240700140c50307684280250180204c002d070155045c072000c50312401008100c41c10061b40070f0216109014107001444010b0044444074040070185403550400d189503426100311180940c00401c006c1c4055500010703007608688050814030030824480c14212086400c03144000c1d448a0128911001c03298000c52554010700f044403565007800f00300d101a0100c4404440428200180c0e4004000d20308a800241912000180c403d250500304503d40c0c0304652400b4414002081c0084441c005 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 666822868 1250 666821618 666821629
    0xd15080c0118061103070f03031e05040f0201050d061e0e0c03010605040b0306130c02070f15092d0e0403080711060415110406091701050f0a090503070c0803030402 72
    0x8100000703080c41c994181d660a40e500800e0760600803c414010984411109101d040040711813141d080f000c4910170840c0c0d0b02d0020040c0c800c088040c0c0349226000c0b002c8443c40c80c2c0d44280d60080b5485140f032804a900c69005440c56007010b803034074200c5a99034100143c040d00c800d070000034000f0360740754401d0384e1420007810030040d84001c0c0080c011004140300502100e90000121030a840c4a00102601ca56032103000820b6002d010440034981c606000700c12800580002e070700360580311400d8ad9403e00c075864003010310869004c40c070600c000a0140000700088485c6080703a80c182c00488813402030000003a02d600011888a500103d00070316140100f10034503610040950300000030345080c0d06034102c840340c2c0c0c81e500c69014101528610404021442d8400b050340a01c51007052025401c1d21140d4904025000b0009842082c50310340300c141e90b0304050241846001d22585014584402d1600d91191703080003402405021142ea02c8108000804140c00c00303aa40c0042819500941d41d0303181902c103004 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 666824118 1250 666822868 666822883
    0x3190b090105012106020708040906030b160206090a02011101151d060904020a0e28060518070807140408070306021b0109050d051812061611060105010e04020d1508 72
    0x41d0208001c0c996010b244c12441440709400c0d0406009622042c0d54240200a0301c6154810390015103030601c000304100003400b400d4824a411469480250b240d0fa4090342c60b21400c0f102032085800c00c0400707000540c01402c0490200c849100001190000f0081c0c3c03520301c4485400080e1120408042c0c03003481540d2042e4907a0165098419a100c0d082075804a031510846004200c6020030f62300c0041c08844174482e500400e0014618128915150350a107040103102c203000d807500490100c04802200d1204481140c00742c4007da036040015a116101101c5000c0703205c12444249604120005061200300070307103006107000e100700680c1c6a0490081114648078150010201c4e4100884017020a0011903040002002401d00c3e50352220a40410360406180c01191a4020605a14403000040001e14180700700c034440111461740006a0b401d480380c4030071454007a2581c0c0500014011540300d01c05404a114000d0005800d101c190801941991016404500050147c500c1000f031554100101c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 666825368 1250 666824118 666824129
    0x70212010c05120a0e010c180603110915070605040c17210f0c070906030b010e043c060c02121806030601020c1201020904050105090108060f0603190b09010501 70
    0x2002401c0c98100040c00b1400750340d1403004400314540000b10202c1554001001c0d5410f00700081069034a051005802c00040b005c84040d81c89850b04045801c50107481503403450140315007421f0910f01004c0403c003441c42542e415000902007031052400040e454001d0034065446910b441002d1820985a81041c8030b441c40e0b04146030380f00c0e4001508200040b404811a50250200180e662803010200310103480b800701c00151900c20700707500140d0b004855000100b0349104101e011120b9a0b1825016000c3d5001d47e005040f0404403039118060002c800c06103685c42c0210441e118050710201c403000030111000006482240c2c99419040034264140720b0180710421445506040c40c10040c1e4942c00e05802c020842d018180001c00b082c0680c0c000c00c131110003680c0080c8160000703030510014502030740060000e00c0c011030408002040b1840d1205056041c0c8810b0300082941e582e44190103850028041c0043d42c060080b0004070510a041e9510b0a2140d80102d00f1414641041d101080c2100c005a110 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 666826618 1250 666825368 666825371
    0x150f060108040b0601120b100503090d0203041805060d0803360c09040f05060124050a080f0403090806010602011d0610030f1505010905070e030a08030a1e020a030207021201 76
    0x1084000769000044a0300010701b0301c2c10015031398600903954020082c884002c0d40c003600c4c0d0030031804025031100007544070340b00c3c100690b20342c00e0718001d042c2e940380168016a128412040d004100d414555031202b5400f000041c4190000d1030140c86107102e030ba00c161003400908001c7d6503c12a50f0305603803012098855030703d00d011150718820180b5501c0d04003d0b2205071107600034001042c18030200c01151071b2200e4101040e03070300b9540d5620300701d041000e10121103801061041c84505444c0c0c051026202c4800c800d4a65040950f0780f035101203a4010b00800c21001c0c0f014940003c80c83c081c01f040003d0203030a02d0b030000a03c0c0340da65905481e503401038040071040c9500034000c1104c508541a403480480b548030311a000c8580d103515007541203c10b2903060703040003440c100000903c004c090b00202e0044189498a4905501c014145505c410040070040c2c129641040400c5480c071117a80400074401a9980501d800c032070302603001040c2c0e4000303034668000940100300300c010f51510b64003801204048100 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 666827868 1250 666826618 666826621
    0x803040b070e21060f07230903031603021b01080f060d050a0c060306140a05150c030a0c0b010506030f0f0703180804210c030209100518070801061812020a0503150f060108 75
    0x20005c2c20687c42102a403014002106048522880302055803034030600101582e13201c5109160322041013140c16025070052240c81d2400c0c404946002c0c8181d03020f101030303445940954034020804c88116000d80026003022650074079801043d020300c04500b900e442114040d00d02454602c0003025503103280c0180c0301c034020301d2425650682c1c40c0301c104070172a08192140c80014100180070740f00c40c01552041c3e080340c00000390f1302c0440ba0303200c880214241e114a640045590301d4806010355400100ca082e2222111070700480c26a5081c034030010344c405114035003c03409090304c56094140703100100044480000c0800c1c140303c6580c5031215401d03203007107001c860010004643c0321200350000c0d501c4003900402407040400d80d10945000c0b80005801c014003072485440301010f514202c041e0880e02200080c0c0ca89002060051244200c0c48110f9584210061a94102613012107102d406090881e4030000c5504006075945040c0100d5007420300c5401d03a8000b601c0c1000f000c8a2200c4010443c0781040107400 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 666829118 1250 666827868 666827881
    0x609010510080c0907090b0d0902041a01020d181a030a0501060203070209040f0c03080c061b0406092112120609050103080703081902030c0a0905030a0803040b070e21060f 75
    0x500d40103e01000c94600b18181c80706441611040791580107008000030000390802182c100744c1080d803410381b00703031010800c3c841c0c8228011840380c08855083d0068100c2c90340110103600c2000c2005038000c2041c1c80c12007175941c1d1400100e00c0340020b4106001c00a02008100981e202445494014521030016501d0952250b00080d0f840400402c0148044654000c1c0d1003400508481207000e1940000819591800440c3d03440da00c910890380e801c0c42c5031003500c038040312010200c1036504654441d01d40d80310060500c03003500740c00300d50540341e0704040e0803035a0030301b001c1075144034030f20714840c12600c440b1022800d10200c0029104190002004075042200400001e84d03048120703136100b40c051505105580b141000b081c40d0001e11400e140f0490700200070307c010700c04841e000b80702c0601079455103c03603942d90304113260300c0d59203e610140014200740300007000b180310448810382c03050300c0740741c900215440e1b50001800c440d082085900350082e42c404000e0481c600300701203900402014042c030f5103841c0c8034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 666830368 1250 666829118 666829123
    0xc09040f03050c1c050c060604090c121502040e0103120f02030f030703021909050f0306090d0309080d0c020c1314310812010b0301030b0c130512060901051008 70
    0x40400408120000900b071440c2e0300188406440c0d00084152002d1341d200c0602d000b0010307003120962500b1809904d010603d0f515141c461801101c2c1d10041030070010f850405180a2542e208005032800d1b07207200124088403005100a00240044280c130000070350540c10900c101d601b10080c02014001c80c20025410707c2d0f00002560b6042c240041080e40c0d0760b0f500c2c1c00440c0a03000c3c940c015090100350100e0030300d1540c2c005c0400400c2d110305a42403444e017500f4204041d528070054a000009811a80041e08400e1194200210690180c9140c504e005103140c426800c451180021200580106004c40726a02e4404064594200141018000c000311400345030403200c0082e224180f00c9500c400c0340c241c14450601d81e0106440d1000300307900c01481e64103107454207901c05c01d4080501610740c400032500c030f0209000c0d60306a075040009141c0f40e58610000000d83d40c03203040766060b036018010300025039a8842d0000c0c03001480000c0981614189000a5400d59001078401141134030360701e00030700101400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 666831618 1250 666830368 666830393
    0x1e080f0c0c012105191a03010e010b150f090a08010c20250b040b0301090e06010308071412031302010e1e01390b01120308010e0a2c0c0904 61
    0x7030000000d0281c55001c0c3e49600303106840c05d401145418110680000855001d5540c40104d040d402840340040c181c003102e007201d103407954280d80b10f0b07034035a2810309903100c000140c01ca11040d9a4054501240300c400180703070031443d43c841540e40e03456502c2e801d00c80354071540145400d091421401c03000112800d9240d12034086089002184500c0041200c0822240c141c4034000c0c103225070110b503200d840742c62034030041d44240100302a080c00c0003c0c900344a007000ad602c80c103c941044401c0c0c14503c480e520301160007000304044910b8401c60003c40d20005002d0000d50041924030404e00c001182440050204840e40810f5445036481c0c120300e108030540d84d04002c50a41c001d190810142c00300340d0004013400b2803150344207079402e8004285665003600f5101210103038000c0b41082075a80e0784119000000107078100040008840000401000c0e4620b002280c01051240020170a0303414681d0340765109840c1d80000030001445081509000800d1240041c154010b5620200c03d241580356805120701e07 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 666832868 1250 666831618 666831677
    0x50d180528170304150e160506030f1909120305180c0604092a0c15050601210f110405040f020301030206160212030409150504090507031e080f0c0c01 66
    0x50000c0090200203c0d1502c142801748040300421000016140c2c0390350360905003084000394001c0c45c1000c0f03868502102520321500e0341303105030503141da280d0036040b1090303000040c282d41c15510344540c000011080303010003440c144956400070705494603100320580117901b01c3d038034034450300104c03010075058580500321826110035010101e0b04040d010b1a030120717542800c000090390368040b000c8051160b402040500c0d070502550103155891884520308049032800c0d51540d021034042e4100c00030103001c09075098004004200005400030780d8652610503560a0070405101c41000603050240707103014442e00b002d401518000b10308541c11640820ba0620404ca20300038004c500440201c215500d820035024124450000c0d40d8503240d50718495409000c1e95411303551700900d000000f00b21422702d407148510b815000401000d50350b140d41c540d641320b02100c500c1d0007202c103041ca40380c0020510309e10040020004100246695008070b420140c1401003101c9070ba8100540346003142150190131860348032255 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 666834118 1250 666832868 666832913
    0x30602270d03080c1b0304170d090303081e0a050103141617071a0a1d130c02070f061805030601060804110a03060908190f02030a050d180528 62
    0x8650002246803030281111174601c0c100300394945449200d01002030800c032514015881008955010259142c41d0382040c80384c0010480081080030030700ca030750056080240001080c1d00d0b4007511f600d0702e4003810b0807108894016255001001084003540060501c1f21120010b44140c4079090349100040f2a203204503542c4406103890b624000c403080c4103401c002c08610321040007400c0c3d07100085245400074590a4081a580400015000701009203007806000041c03032912021104049000149000c290000852041c1c21010503030380702041d904005001a900e81c4842c581d20101030120a030004e03000640079422860040040c16007000209401c2a4402c407001303801c00b41800800c406e0110350b803002d40103600349407000c1c091002010003001215040b04a0f05103054036000c080d900115490a0040141d10801603901a6441100600091451074202041700c50350030300c1e203102c0700c0d00700d03501643d40b50810500114401c15007100310442600405800141c45001d440d40c1c202002d00724003400501 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 666835368 1250 666834118 666834121
    0x7031a090c0a030f0e1507140906090103050a060807060203270918010e03130311030a020108070c02030a0c060809061006050a080705120c1306180302150f04030602270d0308 76
    0x140881c0c0c1103080601c042c42d0403131b03c80403804084038640f00c80690350600850100e04444800c6100350b0101c49901d10040c01c8549001401d81c0114001c2030000c005200c250381d00d00700030036100c1c0240103507c02054240d000310303120000c4c254003442d40d800d02c440300c04c00305070b00e803454801c82c0c0c8900140c107a00c03181c40c1121503200b43c10f0307003d11805410034440b460918000041d49520080d100c400703103804d4a000300b0400c5030414031102810703030f2094002c02c0640450301013000150740c68482c3e441078811500c00760594500b01c04560b1841500c20094104c4400700c0d00d4141002007400c020444280c5c48400c441c8140031061030100007400c14452041580c00b04006a400030391128002c2c01110b040860f107031060b40c086e141030b0004100603002515101000700c61000c000510a12642c0350050b010000440010881c1c6154204500003501c0d441d031180b0804244210349082e004400644001c5000f00000359541e4900d00c00c101d00e486102590300c010002c01c420749031090f101c5568103080a0703810300f8001200d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 666836618 1250 666835368 666835391
    0x324030b0f040507090e07151b080c1908071b030b011517070e010906030c08060607030c0f05030c1c230c010f0f0b0f10030216080307031a090c0a03 65
    0x104130054200d03004e0341d800e0000455103100000f42910403180c1c1101c0c14003d041d03040c8004c6a100184140c2c128403c0f5098048901007008000180001c01c6408120368100c2542468004806161007040c5c030300407408144141407150500356000c5003580d084001207542d0441c0e41d007200c1660107024044411001c01048440301c0c0c0240500091340c49910040001841c00c000000c00d800081d1043c00d001540c04580083d800d0701902079084100085c2d2152190780c2c0c1d1350310a00400c0d03005a03105408010b91901c00c440440c03e224085900b180c040c00140d40c1d0381e80c60341321452520960041240c40f640c040008107220301e0340302030f80c4001604440e25612552412100d5141180500c03040c0540d0b0394039140341005602c60951015003d00e440810902c41103c18a080207007117454100c625030071810351164804014400d500902800c0d500c00c20152000b1101d0701c0b0000b094100711344401c0401d07698403020424506414606034114021a004031b010302e00320700c003106070340107056401041c5a201c0350980d00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 666837868 1250 666836618 666836623
    0xe0403020a030f051b060702160f0501030e0c19080d08010b1213140d030e06011505070516030f200604261c180608040b13050109030324030b0f0405 65
    0x315125205c1207003071581482031540343c075090700b659201c1c050b110b8490358201a202100c020000ca4122510301d2404c9450100150013508448002107400d01542e050f210f0a6601ca115003441d0420140041d43c03000d09000c03007180340491008a2031b00b4050260010040e90404404071414890300d4110f04240b070b01c400c0c141074103c5400382c60003030000308909001d1780002400102c5c1a24800d0740da805101209000d100c441c2c68460a014034141c0740400381741400d4080c094002000d22520600807620401c41c00407a06c0b81c18480303a001280c01e113139950310800038402d402c0c03e01d0076410b00505200400094800004000c2d1050784145519807501030700c584000094881280d5100b40d001d429500b42103404240121100304c2078801001143e811209000d402c50005100c800b07844a90710b0f0b4848a4603651100d5001407401858a83e202a400b114000025401e0094100c030074825100840c500099003011407418004012075030100006400400118107108005a00401c000158400903143c0c1d0404a0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 666839118 1250 666837868 666837877
    0x1b020f2205010b030a060e01150c03051c060f08150105090903120a0902040507180306020f071509050705060c070306020711030607090602061b0a0807120c180e0403020a030f05 77
    0x100424503207070000801c600180011803040007041004c211141c0c03201101e407043c4400307015011441092142d2031248a01036110080303050301a0910a08000340c0218004203d641c202e401050251070710000c01c501044562800d01611060000c0d008482100c038220200e40320511603144254003450100324046c500b0300c21281c062000c3e480b030b82c42600d003043c2800b0143c00c100030124000c3e85014000f4800503c01d40051004825502281040c00d15640300d401c0a500140f04030700307000500b00500740016480170304880044c0c00103a00450f04103200e050050500909070b000c14010a0700700460100e4000103d45041980d03404400141c9603072160804e2000b10b101000c103e6054855007040c84001d6403c880700c0d40c100d4049a0844041d5529191050400302c02030080e000c041c2424010031501e1401408055441040780c070340300600f095182c000c40140c5041c169172002060f01d5006c0f0f5070f44c00410400a04c00741c9003480d5001014101a50300079510681070001408001c0240c4003071a01503c03a40454 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 666840368 1250 666839118 666839179
    0x1c0302160309151d21030d0209090a0908031501031b020619021312060f020403050f070b090d0f020d060203280605010206010e100e010e010e06031b06070c081009031b020f 75
    0x50b516440d4141c2604001c0d400274404600c01c0b034a010000d0f0608045004940c01c00385e209010780c0c2162640f0b0581c05000d100380d000c2d641416261f8400385144e9090008003480740752158000d005a00b0011119010200311404000e6054010010025215141e034004400c84421b1600103000200e0740c1011130040c901030040b1000c0d20700014002003404070004200501529070001d5402542d0b490f100640103100d1110302503000110b03810001d01281303900c0d003148441d60000e0700c02c3c005040140d0307484d81203078011103a0b19802103910584040400f29641040c0c040b40800781304004c083d05150005c0d64403c01445080d010166100000c3d80d20b0755050022002000c0100724a091941c445070301c815005024090007081141050011340b55180000751001c10b41300d080000c5c074041e031848003400555480000c0644060040640014060601300480865000740c46d800194907441850000d00000f580703e040d00c4004001101000540e4450b481507500c0c001c100c891728420150a200034828040c4c06114 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 666841618 1250 666840368 666840373
    0x60d080912012009090108060112060b18070201020a171b09010203040306090b040b130f030e060c070e060f0d030807051c0504030f031d1c0302160309151d21 69
    0x1070905030b02031030003400c0c013684115140d2695a8a40340031a80c0c1384000d206400d40140100031600110307916610074800281d0241c03901d842015910110030124030240c816800607940000d111603001d85c081da4407598200b01c4403190b031803401d2541c00d54030079070300c0704880c4180ca040000c1c90700c0c41e5a000f003003114000c580c08503041c800052503080c0321035940c0d402c07035003903ca40800030000350306803602050361108194051480c0300426010344080741d20290205600d500100d0400c00401c0054080254000070b00010b0020700c800d18000050200121209000601880410100800090300040000e50010340c0385800e903143c8a8001200203038014440703881980314900340c1070100345544030708100c5100420362020700200c464107000042043c0103050802d0780f03410041000c131a0b6100c05150200103860ba240145c20948108145a5a40d0110b0012400b013000a2400c1141c40107000400d107000c07000303003440d282e00c46146c4280451411080e0340c0394070600b10340310a024002030044488504201e40c1c000c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 666842868 1250 666841618 666841661
    0x1f05090d0c12170f0f0703020c0d030c120e010509100b010f0f0212030711070506040506041a070501021306020f061e0403140a030c11060c0714010209031005040209060d08091201 78
    0xb84004c28000c0e02c09031545a80741d00001c80b00381c024022503004103520030050601c1a114001200101240d4000d6010060100e60040801815025101c0c0c1c400300d0000010749410f0100e0780074036020645030383c1c50b29942002031040c8140e802099160700c600c031034103100520b800d456404034200508481d078101d2107070010040c02082079110002003d05040b200440f4501c0b92520b041203014000c030301c1003540c171a80c108020b01005215004840c1d00350b0514010360304240481c0c2c4da1500f6a044121250348100b2280300400c041981085545401e4007040040c02041c14442c04615460444800d2464401c1c0a000880d0415200d0100c20704005481030105464166070103009002d0080c03940c03108000361070218501e02016020a600c0e0240b407559040134a090b070b80780d6802a4136102180b0400595500380000d4540741c409111585101e500141c001905280510420116810103800c003400341d4601e41081000406110894202d210f048621400082400c9082030240c6640085d0120380c464254 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 666844118 1250 666842868 666842881
    0xa0c06021207201209030c0a030303021317070905040203100f0c020732150c012003040309140621100e10051507051f05090d0c1217 58
    0x14125010744243e5a980046011100e40240b41c0c0151904181031038000207a64004480341000421280002a0640d1840d03034000001420768407481d84254082900040d5100340700004541c4c0002400f8040c03007001d280c1c00340101407565402c80b030084d0403030255a0404101995410050101c416038000740512132251071007491800b0700345040075180580b04246c4045210001d144030f058440b9961040f40615031102c07140740c10484c8400d005c240d007022162445030389072540c1c0c0008140c261007400c00460501f030401c06060200b80c00240c4c1444030348080c810b102c002903000c40394400322400c0358032070f6090281541c00101103210788100c0c04640014144d01e108481589a021441240100c1070380121940d500c0004450790021034100b03500780300e10304042c84146410140c40c400904106c081a04051071550b41e28078150321100c0120030540c020272401c8082103079001d82c41e80118071402915000002800240c06500c071210b0080001c0000310003200309a120f1500030101442440382c00b112420540b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 666845368 1250 666844118 666844147
    0x2040213031b030b070c08090904030e0307030503090a14100305061c03090311040c1b06020f0a0c060b010f050a0c080904090f05101803122a121a060a0c0602 69
    0x1480304540325402e1314000340b25503000d40c00b40030045422001451400003440300300b1002c3c00b00148100d003400039040d040803140c0c03070802c0740f40702440c0300e07200940d503070072a5108000c0c1d43c116035409540e86141d40361500c007140d140e60440b492080181d06010a10303031101800203e00c80c40c07080c0a903a54801421414080c164025000c04c202d80c09070f4003030150b80740c015041c842034452000e19800410142400800c0390701b8105820307004540513420040c14141641160809584000100710005206080007410302a0a03c01d504510009090128582280c45006403440c081c100c0300106104101c0a068148106542140c040000081080050158a1a1640c03a500491009070b03903520901380c9a411600807441000c0c6c44400002080f184480d40ba45d003101c1c2d0f8002c014189a50b0358031024040448031103200c482d440b111000480c540e8940d030304103005040d02d100400800c00f90307080070758040951100700ea0190200c44165000766031085054404d076400341c480c00004080620009640311060b004 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 666846618 1250 666845368 666845423
    0xd0e0f0a06050c01322a0c0c060d0c080f01080d030b03010b040e160e090a0b0a020d0911121504020418050a1115121503012307020f060c070204021303 66
    0x40030a008155210500d80801c1540941d5042d0861007911941b60030b00c41d00342c4040c0103041e0540080320200d600010200700660007102c4800145a142d43c0e10404103038000b11400e03171120700c41c0480d00b500d41c9400c4d500d540d02c05100301000c2c11f040e5600394120994034290880540d041d005007081c050801500c81181da5502200e40c041c801101c005004980001d407103094034080c40c0b21400404058045403103081030b030031000d403c1c4151036030308005181c0001000d026030300595000e1103c512020300700409000d888040c540072900c05400a0b0b5010440b43c000e802155001034058800288103035408100c9950040600d40242013480340341501401c1040d802c80c40740f208401a0350350480780c2494210750105010b00b914072458150390500050040c0402080940c240301d0040000c2802c04108140c5011540200c48441d0103102030b4003040319181c0c04015800d511035211005242c80d1501400c6030035940601100288503540000c0c031307600c4610803410264040c5030440441c900c0b610600c01d560015001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 666847868 1250 666846618 666846701
    0x1e0504060f060c03050d02190c03180e010b0c15010e06041a100c0204060504020408010209030706080403080412170901020c06010e070e15040b0304050d0e0f0a06050c01 74
    0x10300001103042a01014030404440032500c550a1285080d41d065901d03410809071101103a90030300c801d1764590000c0f20100030090384c03512040351044450800500b410720300c4c080c40a9210b070b090002c20000d0035201089044a0004941d2520358489540481c00c2c51000b06401000000483c00881c0c035000d950340791805020101c808000230707080005403420890b031a10315258010780c003024400025000d408400105480204000703080e07600c3d00001000c81c0c00582150560369030114445207203042c03c10507e00548030318103154800f443e04e983c00414210b00204028901c001c4407484424890081c0300000040c00c12044c104110701c4d104900a0007500550107440e0244910000000c0b50055541003600030a1650344690b900019601481b11070070a01d5100d61500000b008001840c00d238043c091409a0300c01c0c40036110150b155007000f42100b00f180e60262080d680680c20706426900c1d44180c0d0304488142c100713903031510b1001002c07074010041e08100c854000010015800181200840b04200a0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 666849118 1250 666847868 666847871
    0x1502160b012103050409020a0c020301051905060d0507060f0e090118050f100605091f030207140309130e1c0306060216080d0e06070606120210020d120b0a1e0504 71
    0x30700b500d12800d152028444080e02150b0104401d12900c5859001842c0d10741490401c1c02c426052079011a08655049031100880c02030b902d01c2c09048082c48c09900c1c2c100e54112001562000940c4941d500e074030852041c4018040c510311341c00c04240c01100b03000c13003410300201700035020f42e55040d1068184424040e140003541c0760000080c0c060504140c00c0b030081d104550110782241c10000d085d52107a11448c859030380300030400c84810800c2100090071a03007084595004da04d0380301d540b500c1849040b00300141400b9070400e02c0240e0103511034050140c400c01c5000c0f00441d000e9111144181020201480c03440c101461680031260300381c241d0001e1080b1102c40d42181c00018044150f00c00c0306880d409081907582000091140c800e2003103080303070110507000300143c3c80e0031880da07542070456040da840300803040c901c02500b0055150a2000900e45019800580020750000c81c000704008080103800803100e5945000e080300303847e080110409001c1a5505072500700b001c02c000305030545c85114003840795 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 666850368 1250 666849118 666849149
    0x19110f01051e0412080a0204170c030106050328020d0f0530041505191e080f0f0403030b03190c060903081801050f0f0703081807031502160b01 63
    0x3200718890640c8200d0700000035130b803d0841c9003c1151800005002209016000d10010908242d2925117845078280800200440101001407600351060795012601c40c4d086034200240c0100522502c00007400300c9601002002d00903c0090310031100c0050241100e07014244038010000001031240244440707284040d0198000100d417606400d410300802101c0c4401c4c807003046290086000e4078100e6000f03081c0607082000040621340c000020ba10840700080110181c8610030305401c90b0030255800524103801c85240110754481180c8000c0d2109a1200c0094005000e15200c0e9220180d0041c0080c19107030301d26407030604012442e82e60310042e2003411800c0700000c2c145000d084040100c030303808041c40d400c05000c440c60190910700901001d0502804014441282444100410025009113a801c1e01c54030b1500b0010603520008001092000344140b100c10f202000086841c226a44403c2080942d42140d00c3c0d040a8001c0000398244110000302e00801c00088240b154140c4103907400b2042c06 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 666851618 1250 666850368 666850411
    0x9030c150219081003240509072403060801052d060306040320030406030204090531030203070b010e010503120f0414210f01060f03020619110f0105 65
    0x201d1190b4800c0541d00a0034041d408501030260b0480390780b0620304c15022200c25640c0e11043c04a903411000302c0080b08007030009490303e000510803942c0100c00d00c4014040d860030b2a0b20352103080d090080420300d020000c800380c5403041c4a40c11902c09400d00c24000d001c141400c03440c58800c0260450400d04581c0f4000b0f02c009142c0c1801c240603c00c2e83c00800400658486480c02d030340691001001e2000310110501c41403480004000400041045541c016942c43c82d05031a802140e0780a0044009020280e5107003049400140c000c40c440e0b0346021805010304000d00e016031440c411284024420042d650000445046c0000362504030350080d41940e01d5001c102c0c1d1242c02d50710803072601030010075003800240b1a18070b03403c04003003000001408000c0c4400661010a20406101421155940c060b1854402804c3c080c00395000500c051340c44202003904690001c2c1840c016035a80038108c1452000388030b0034620942d00c0c0051003400d038003601e110551940b01240645000c03100e072042906460101c41c0c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 666852868 1250 666851618 666851621
    0x51311040f1a03150609010303201903030507021b010f02010b040f0b03010b0102030301180f06080a050f010c0903020102150903130303020606190e0f0601020c03070f1a0c071e0909030c15 82
    0x2281000400400b06d070307800e540d000d4034a140c040c89044540c0440e41601d014080d410080303080d0200c141e560a0310440310b40d01e40141a901300030004001c540024000304107c103500c00300100b9011013400c00c046e60761540c040407401001c1da80d5940b54081e081102c0c400e00c42e6825030142504050560091164803102401643d884c4803e101d8440c440b400e91010038091001640148071031605410302003440750355016801e20300b111026041c0c4a50b00036035950091103100340f08068038240d450038000b403081d14680000c0c0d200c200c14106904001d208a000882c0850148120340703010f51044c00c074003800794603420001d50b601c0007158114082d2820868800d88000c1ca440c3c4802111446480ca103000c0ea1280c2031000280b0016000c0b034150702ca0024070341483c0e0350034420013016101c000494860035180c01112411403015200802c50340c04200200c80b000361b4041602070550305800001c101007921000c0c0102188103030b07403101d003442d440c1a8040c820558041620341842c2e0144d01c6030a042d046140f050030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 666854118 1250 666852868 666852871
    0x609010c050712120218040c0816030203100f060c0c0501020105010b0702040f0f020309010b01090504050c27090a0614040c0f0f0e0d03090513051311040f1a0315 71
    0x1c20014041100040c50000240c1c01c514242d25003100b070320922004820590b000790f040e8805020000400440c0340c1460b116966407100345141c12052405c200700118244400c2d46a01e40400d900040010002204100c0f1100202940c03103c18018a5903808010309090890700101c2e0844009500029690b01c1405240e059a040c0014607180c40c03001d03400c000c0100389007003a2902d103070b89600c103030350030180c892010750b1044d540c0400109044240400041548280c4c0d000a0f104038584014003134603170089070039284105586e610f00c0355845a0303051885407400d4000384880d804500790703007080088885900b02c9401c4500e6141c24524000c0c589003003100303650b01071105a00281440c0c00c0082c0307032889040800200482401c00c0f81100c44040041075031160341c60000d0b00030642c900020043e80c00e1041800880c0840c0d4401000242081201c01c840010701c080058003400044880400c1540c8542c03003104060200b010801c010000c0d24001c03130350114030100840c03282c041e49807050451700b841c03034025 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 666855368 1250 666854118 666854141
    0x3090b100308030a0911090c041401031103040209190218090702032106010516050c0f0a0e070e010516110306070903082d041d180a0f0203101d060901 66
    0x1030300310795588004c54002c01c0c8001c07081d14000a55081c8041c07645403900c1c3d6034000c0c1500d4413299903a9050180b110a01d199a9201c141014500020b202a80303900b8016039410507412611900140c0740c1403000b0340051403110f05210351a100003260340d658841c00c861b0340b941c000e050f03030320404903621128180d803240284210080c0030851120b00204080c441c4100a5108005040280c14a50500000248082c0326481200e040c0e1212480041d903181400403400c18010844c1c2c07040220f402c03c820600050000b8120720140643d0414598a580c050010340c0c803000ea000b0b01c0029188070b1410690410408558418000c0c0078000116800c184a881d00605690708020700c10319145102c00000207052801034000318010920710785201001085000304020a512000c1d803900403d48201c12414800103050b00621041e0b42d0741100f5201c01c0850080162900103094808242e1240042401d0180554054880b0382c5484100501401c100c00304221003003644044580d41c9c0c2d24400c0041c201c038240b00b0b00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 666856618 1250 666855368 666855383
    0x5060f0f070305100f090906111908040204090f15060e060d03110a061e060503010b0f060706200408010b060301061707030e0607030f0e150c071e0303090b1003 70
    0x1441c03540250001500300078201510907205a8503131002000750500d4100e11009501c608000092201601032100b40615049885241c0269508103040c0c0ca2400248801400904070028040d956075a0060704c0e000d0f00510b1131181c0c0440d51404c541c0d44400040c240c0c5c84240740c6000400d00246145c0a07a101c0c80c0040c0404940c0005031310300743d9124050007008401c52103589c910100151705030042c1c101c034025040d2001080302d80441003c050341e40b00c3d00003a02a070716103450400103985200741401041d5058031520f5507034042c0c1c281440a4030303e0703900500c0c12008002c80c1c45417682001d0020400c42c1c3c80d04000304440100c1d402040420304c000c1c4518030001c1d482c80400f5144610041c0d403140c0100007401d0000d000040715030090301300f6200b11a0780d80400c1d903c2e00041d07012240f5028a845002089026140c81325510802c4034500c200a4000c00500001080540c01c00801d86071540b00c5280c002e002c541c21106a103401000750403800c4088815010400201c0c2400b0580c0d00640c0c00c0d40e0740160b0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 666857868 1250 666856618 666856621
    0x70501090b18061603091e140103020c0f0c010f0c080a0503090a0b07090e0702060433020c010209180702030d1109100f03050903040b07060902040e061305060f0f 71
    0x440507880c0c1044503500d402c0098111010300c1d0b940c8110003418984006450340b03020300d0003410b02405442065000c00d4851000300e0f003c4849589030202038003078800d00504007000701d111800490090092240390002c501c2142d0030040755800024807541d09181c241e0340c108800b404400b040701e5410032003030003c0481d4014000803c0c1c20f401070f40615400922a4221120020310b502e0300a840141541d425004c00d5441130140319020b2048082a44066136000500303160800d40c1d540c0f0702101c002114240c400c040d0310403501040d0503280e990120b186009406548483c0f244d072005000354007032142c03a48102119500f15039017000c4104d09500c01c101e00e80180d4200078000e031401c800f0b80b046400c0780d00903000821100e0307500d90700d03051081400542c035550303010b0b0641c4945020381119000340082c490380c0e0062001300160703074503442210030030b80e8007440202d52b4131882d1011a02070424408001c19601518081000e42008040c140d01064090400c94201e40c403640c0304460071001c1070b6828044600090b0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 666859118 1250 666857868 666857879
    0x9020a03021e0a0b030103021302030705030402120c040905100f0b181909030305150f0f0f03121605390a050604090905061501050921100204150207050109 68
    0x20000d448944000da44900b101d100b4100056036242c0d190804413140700c01000600035420050304007035030805000003c40c59402c0c0684050f0090000a10080c030a41195940e4101444240a4241c0304800031300140104411464800d444200140303c00c42e44920740525003d54013414001c2845881010307103442980c0c88842081c0c1c540c00b100501d00d000c2104031018000c07030100e081c498010000e000344c4d030000351414101c180c07542c0c9050092249124241143d03c00d2407998803800100304a0030111000044200403101003070030302c2607074480f2203449103010440c050100300a94210f445d4a220318140c0b00112101c103040a244080f400d210043c4e1000f03038110601c0c540e2402c0c40e031009800020b210400750356903030300010703110381c806d07004103045136144c010440400c0010048030b0f0300101d0091600c60b10000442c0000c166004402d0352a04c20150050161001c180c070902c0000c02c622944269071503280c0c04030345080694054400d8051181e11000855a4a4800300d803a4080e03e805075109034181c3d240c003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 666860368 1250 666859118 666859129
    0xc0f060c03221b0612110d090204090b01080717010e03041502160f06030b040b030a020103050c0409110406140324010909090605060427062307111009020a0302 70
    0x84890341c02c030200c00401c01c00070450591010701c80102074046501d0842c100300d0002c1000b204418401119810001c0b0a0b030040a000182d0702d04603420000014000c5d55400001c2c0030340b090b050054400404030002055403800807030008241ca881d00d907100c0d00ca4150322445070880301c122039030310b0803034000380006d200d000900100341040701c3c107030302c1200c00c96483c50000424810745036215051803220701c601080041c1e0903000d580e034000b50440f0304000004400001c02d8548010031002410969550700103801a4005401d50b000707030070304590070844070001d50359025881d44203018480100c0c2180d1110486145e110044900c076200803010114000303082c0740701c0285168a052914180032451201143c5846e02e03200c4c0c42c5207d4054040403441e401c018041c80700311100e105809080f407603200400d0034001c408140d804401544510001303110021690386486084059403038141c3c5030724002c14841544da00030850962603009070107807031440881440f100100ca80080c0001c2d008140b0100400251920 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 666861618 1250 666860368 666860401
    0x50c07110915090a1d070305150403210506040f020c0a0219090c08060f01020f120d060902120411010f0f08100503071d061012150803030c0c0f060c03 66
    0x140b0301070300005501e96000406140c000ca40c54100a43d4400001900b8006050754815410030900030b0700e00c2c80c2c1503442d051b488140d11181c141d02108210041420548614200b500403142d00003e4200b2043d100780c100050201960080e100320300300032055013400b40d1882200d070340140441c000c00c1e14030042d07400c0c011240500010035180581d04400010200d07071038010680300360515640c002061900b03400300f001d11185d009c01d903411540300700c90560b80c8150005084010402c0c0201c55a00c484513035034020090a4190021518240041040c4201116800c201d6000358424135200e0744c3e11801c0001141c040e1005203134100000c0b1310600000d00c10340116942c680195881440303a4800e5116008131b480c205c0c1039849078010703203101e03042c1c040720740b8403003140c65007000d42120315080c240d409400c010302e8400495040894655075078070054410300c00c038011100030040e0b081520740740c0c503014291911941008421035640d0040c030000450501c40403540c1407154000b5841c49081d6152030500100300d810 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 666862868 1250 666861618 666861631
    0x41b0e0a090f05061008070902070305030601120905011803030b0d11040218030607090e0f0106090303050f0723010c390f05031c0e0c010f0203040f0e0406050c071109 73
    0x40c250100000318100340071451040711417140340d505051500b0031a030300c0c0204a90003900030f00e1060080d440003983c80012240c00005c24a0806038081c58501e1b480c005003010b00c401412507290200540340750b0281603841d00d0aa010385c900300880c8500406011092522181c0100108010400e400c52860a6030161860140085101b0149042c9101080c0703031440946421022415006040080003103941d02145e12035402480561903514061019040c3e29a60000805020020501c26a0307219002c040d250034540008490f01c2074882d0f0b90984014000b60a0803800700c2d400d04469008160140107030200c0c4001892021200344280c0410344181c08100748044146104c000c0601c1c0402d104d000c50024090040c00a59603640218410100e42e00c1c0c03d4100700e20306030400005482810303012034585014a000e0070300c981c803a400e035807003282540700e1a0003640003c0c9400c0f10205495200402c910310072445950100202d841d408040004c0340038260004210104a4078090400e06203022420303040380 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 666864118 1250 666862868 666862883
    0x61428090803030c070605100f05361f03150b030c062107030507080a09051609060f0b0702061b0132010b0f1e0d0212041b0e0a09 57
    0x15160481c0380d08550056070910b00862003c658081804071501c6919044140011070390710080c03621130356a00c1c071182d80c4181351040c5501c01081144442c041d4020700c11161100c0801104260b828140041000540d602c104108950300c000c080c07514003950310741c180c98221965803082c2d00c80719030ba080607003103541c0c8254040c01581e01540780c0d6100c0b80301502c00851041c00304001c0b184001402658a540140b5104c00c0500344401c1c4150b01c0d8010322040e400c02c000e1040410165440d081191600c110b80150400103200c07440b00144c508001d030b12490a07101e07000180c42103241e594840100a0084000c040c2d800304007000507182680310036011000c91000030300040780b00821410700c0843c90a900d1003421004000d4130030101941e03036413804640075103810400c560034094414035904660245182250401111040401d85540c1803401d403465000162001e550364100350507400750074001600e0444540007541070b5220107034004542c201c16600681ea0058181e40c4141100028102044050710b0b8030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 666865368 1250 666864118 666864137
    0x1021f0207080f0307081b0313020603090f16050405010e0603070612090b07110c0102010c050d0f0902030f010606110d050f030c13170714030c0d1713061428 69
    0x501c881c3c01075486a6169200c1490b41c1c50460240c020412007000f0484400354104100030314a000c41c9101c00143e0307010340d8515126582d1140c818685940100f00b10418800c04001c810244e008841031002d642050340c060006983c1c8107000c18154009660300e80d4140c22400090108511452070911200e90074100403035032503a0380c0c8444c00926401c1d944000000d580112202000500300040c49a9032828030007004008200031005045005051041c54100d0703c0705100c1c01c030107405030014140290010181c1d05190121100c2c9030003042140700d404040303404c140100201441c04900a02044146e844007440d02c0c082e0480140d90f50300c01403010349500b506109144001410b0340c00400039242c40d600c8220070032150784c440f41c902074095200c078140c1c079110030307031071000d51004a80015039180a4440c2c048504040c07800c005c203181d4a01134010340c24004600c00016210445150045991a45801002012410010307145110b84900f0360701e0400030403800061400d00d00180d0710071410030726000034603 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 666866618 1250 666865368 666865387
    0xf2407020109091a011409090c0c01020706020309060402190b0a140f0706060f050a0b19110f010f11030402030a141c0507020a090b100302030a110412050c01021f020708 74
    0x120b400c0d00750b0284040412400d80511541c0210b601c0340b5141b01c0d0710b5104d0a02508000240003981300030302c0c0012000c00402c00f088500c801350190b078003c5a016000795203a1610038855036660384201d400b684070300f2007428600090144040810161b5401030b45c024501110301d14261003002c0000356282d0492801c0011240016005018103e007034414440031410918103100700c1c498214030b4110038419010940100100c00c2140c080b04c8400341c0d44c034084c80782d500043c103050311611070011400105001d44092180c000b0b1041d0700c50b017001c0c202e8a2042080300f031880d10503600c078002220f0080d0035034803142c017640c0401e4240a03031505012060045890b401040360692240700c51504025000c258003180c84030444c600b080c030800203094020400c1201c003c1810004820201c415200c1052603400800300d0350307030f05030b5400028081100301d208561f581d503141d44001c08031440807800e40341c60080c1c0641204641c404110760001d05023030b010074044503003500c4020000b9404944200c2d82c0b00010050143e1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 666867868 1250 666866618 666866621
    0x24090a05221a0c03060f12010b040c0507060507090e040f14031603020c060c0a17040e15030d0f121d06040c05010801060e2b020a090501050f240702010909 68
    0x886208030344018001c80300d8a0000d41d0b064000c2d05540030aa000e00c10000540c07600b401840d94420100c3c2c0c0c80c852070a054500c00d0040c00b4064049800c54145070b2083c45594200c0c00034643c1e40d00c41d82d03040140f641c81d440216074402d0113008140400c5403040201c6c0103e0500d015a0144c43c0c051a640d589060351004178614661000c0101c3d41145107000f018400d242d010300600c2000c801c00d0301c06070710f0034014403201c0d6224400440c0003002d204400b0b04070b2a403110300505450103030445410791309150408009c0d0040420b660740440348203203e2501541c400503c01c0c1080d01d540100d50300c03502c040c00c920b03030b022a01070009514840c035000084000d44a484408110030350041d4000d9104003070840c14100010100c90058000c034050000b0300444040c80d4031703038403034000c940780c001070344000c203040c120300c841d04200d0144a02960100760f040d0003141c0c1c0003d950016040b10030480364030f0001000f581c1031090000c15450301c00e90107101400820042c0e07020000404a19105150546000b501c8450301c20 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 666869118 1250 666867868 666867931
    0xf0608010b030a0e070806161b080a050c03160b131a070201090b04080a021207030206010e07090801020d0506010927050601031407030510090603081c11070b24090a05 73
    0x30807580420148203003800580382008c20f0400600d032100d03603401c001c0088002e4124104c8018100600018800343d694440c40540300da24002c041134030364400302c0c0740b91421444580340d000e81d001c0c0700507004600480448150081d15551000ba042100e9004003140000203070300401900565480b6116440011a441a0584101d11441c134045d2a5002e1a030005e1410120746802d148100c03041180b40301007600025000d0440d0081c40c4250303e9659115011a40c0304616403100c050b0f58004641843c600f0f007103810441c8629401e980d103100711683c40038050795485420302c224840c1e528482500b40d0a42281d084541d110106040200b4950002240300d040304008403462170009954005202c0d0800307c0005034002054011030600171141107840300f103107911840c440c20700aa803465902d1103100c50941c02444100000c03c000a1b2600707818103060011143c12520b150810030403a003644140448a1051071403100060440781c3d0b166103e06c254401040060800040300020104540d1141504403a02 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 666870368 1250 666869118 666869129
    0x71b06091509200102060106171e010306020a0206070e01170406020f030903030103030e030c0603011e0305030a03061703070804120c211e02240403060617070f0608010b030a0e07 78
    0x45541d0903110083c80c40700c022038000700341107400c050010020f2a602500c03c807040300c4205595521515403040072410303800d880b10b01d2620015a1000002070000301c0c0c2c09402c44040381d8080c0d602e290784051088072a429a2a040e60100b921080c6142c610803c414040d84c0c4644106001882c006c15058006825041107070014400d910010041c010107500600c044801202a80146040682c074000980c250105000c0c0e0304642041c020071503041500211a50011600001500d9803000d0450004001d8405409445640d640c5081584441300001040303600107600f005600d81094100028400340701030303940c02501c414809080c0803452140c26072401d003004c50707034540301408250149400203c091501402d0541c0c100390030103460150321030000c40110408502072030310b03042e1040d41005503140246d800c0500084c1c03500301e01003031514000714826100040301c0110f911556842061625050032402458001a250070042110483c039202075608222041c0000c6190918200c14514140c685d034400f = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 666871618 1250 666870368 666870383
    0x201020d1b1106040807110d1b05150924040b0c0709060b03150907051204051629030a110304050d120c051803190b04020405071b06091509 61
    0x41d2409802116181c62000c0550152540d441d081c1c0311800c003030203600c0020b030060200300c80206003607680d420740380001548904c80e16115200d084a802c072551007401864081d809118281007140c006a003903c0b079240c0010012450030358101003070568903d542c0104c030301010042c00003240380042c1c0c0c00604142003c52004205052070040204182c5049901c000002d10f0100140000070514420054080d80240c4071800d10340c0714601d0840e001d21807824920b2500191100384400c2041c08108100150b1000034100100c0382c9a61001d05d201e4100341050801024141802d580041540050340d40310000036000501c0071a0368016800d1a4800c4404407000e40014901c1c540c09900006080c106024a0318104208646680f000d810b510940010300603154480b403819000f5501041a0340e80100e100c40382c562928610314125102080a5804074403d0b03081000040a00d44220580f02010020a0b00030074a92066100e810051819400c140d0321324004241160708035030640548424241b16168 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 666872868 1250 666871618 666871661
    0x1c0308090c0a030f0b070203130b07050c0306070912050a060504030509030111090f041503050307150c180e04033f0c0e09100906090c0215040506160201020d 69
    0x20260500034501c0c00a8800d50000c2030901c00f150206210f5a0080d500c1055038581c3d4a03660170591540c05085002c0c1e01040c410100481c0650143c03001d080924031520803034200070b09040c03c0540b104e1040f1003980010320f0003907041058048405a0010050048041e44c0301140280c4412041da5401c94050f80030400c0080c40001c02e00742481940c801c0d501c3e4079103090402c2100e00009126888140d200b40c4100c0e1a244001c8081641c0700365100215482800c407503641880303281c80030b01e500281c1c202001191410900216540c018111650032034011019041910300b0070000808211014109404002c5443c002e002040042e5041854003020008141c5e00042030520b81587d4212500b070301c6181c603007000040f04500342c00c40981c8003414812550b4668950740d058902049020540c8040e041c1810020002440801a40310149a8100d6826100c028105031501401d0b4403050b0f8000300640c0c81500021080e01501e500c5820101e40782c40050300c0e002180c114501500c0c42283c0800440303140707a5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 666874118 1250 666872868 666872881
    0x1d0f2d06071419020109090f0e0316030807090305190302010b18090c0307180504080d020a0503040204050906041a0c04030c350c06090a0302130f050a06231c0308 71
    0xc110300b503080c503c1c0c03441408107286600080a031040340c0329001d00d1517101c3c18091004105904500b1204022104480d02c0c1c02040140c082101c0200d841600481c1498000c142c0b014498071401050b030341c02000400c2c4108420414204028000c44c06030215503030303450401300c155180c2c104200e00e500c111070280c6281c10201140781c189161506098032aa0102a00708485034a07109442421010b000740014290707918200070700c42d80704d51a41010158400102d450745c0980050186015030300a880c2007009980340100980e94000a03200544408250500441d0301c0ca50740c984240c1c80141204d1090a1981c0c9650b010010b403015008200d030b50800b282c1c81c074035001e0703114249408004401c851849803c030f0310340c01c44d403a41d1286064a005d61400206d540c3c494451031382d0403004507409442c44c50f4140c144614000100310303119030104994144008504e046186018070310a54200d8224040c40321082d82d0301c100111044403240741c00c0728541098048400f4800e240e10515400790b1110a613078600315 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 666875368 1250 666874118 666874123
    0xa09050607050109150c02341502330402041d03090405070309170f041a1b1209040b0f0306240a0f12051c1d0f2d060714 53
    0x9009009040d4a800c88000301103a0025200885904100d9123407800304006440f02c91122100426507000040003e000600d20000540044402d88a46c00da0b040c0001e9540591148070170511560310351724011104c0c804c0100808803107504144002c3c4006141920040e107072220351400c0c1c1d0f2541460b000418640c10714181801001c0d401001c510b020080c4443c10f07510b58101504c0d00761031920031040841d86842d650084021240501700e000c0d0024000450801861800d0340600c040c0038a04241600d001d1080100062a00d041410a0059424801c400080c40014410200c445600c46900c5001d443d650710203022260084011745414540f080304000902e03940c619004401d07005801c6420200801e0f00040320b50b4080e5140c088140081d00c04601f0314070318000e42c559060301c0340180e00e000b075600c48d40c02500c11018503580c01d0103400d55034003242c2004420711110080d04d41000030340b6400711584022000a00401c06034403e111382400c0e01d8070105400f6080041c00715400070b090040440c840008 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 666876618 1250 666875368 666875393
    0x120102070308130803010e1e01030f1401140106050a0212120601200606010c030315080c03010f050108070902090112060f090e030901020c270c030f0601020303011a0a09050607050109 80
    0x21920688845203e652a842644014800c40c14050045000704141c4007941c524480c0c6080d9100511034256101d08005c018204045000c6803541d40c041000801d140040c001d801d807890311040f0300700d00303a03181c05003e1f66943e014000c24811406064041d4000001010140408007a080810801c1d407404030005000345003611414120311003010b104800b02c1000040a80c1e003c40280303054000c0300d08624065004c1d124146605011554181000c500c2c5240026001a1050102c000740700354200000c030441141c100b03004129454000500c02d2048655580080108403c10300d003a0740d207000316000e040c088800e140c1001501484405c810003014140b4000e01541400d200091441e10105200203565001001e200e0f0b4000c1c03190031110b1080840c1580340041d1800d0286a00900f8a0580d60012031a801117404843c05003005010a06551001040d00d05807408447d49445101e030f41d01000489400070b80c00f480410014010204030b42d21410007806001f031013000041259890b41c0782c9a600c2020 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 666877868 1250 666876618 666876631
    0x7050106170f0607050a0c0b07030c1b0b0c09010c0822150e012708060402030607110607081b2a0c0105090402031b070b0124080c18120102070308 64
    0x7003000c0001100b18003203449500180f444c180146c0e0b400c0840740c1520070084008024100c009580100703d03c65405030014075000000c0e0399600050003811303410006022408001405800780b0000080700f01c40003200808200c5014142140c00710410b40e10121144e0180201032440c20a500c448204903c8005440c0d0282400d28002c800b1075016000044c080101300183c80d0401444076845005d030140142c0e1601e0044a08242c00541b40e00e60503040d96540050350100d000740715120000d00034a00c501c0f81d03500e00701e0404020740050703218610101d030072800103400c03140340400102c680d244c4009032400900105603c0c405c0c500f011180101e0340c40400c5244050002d1a410034a450901607a000b0201ca046c000f08650041c0c8035241d130051032100c0798450720a0b03a101100054401c003403162404846040b2212500080d0810101c104c0e5496031080c42c805070404111500040b03002d0101500107049002c00c80d01c1620f03103404515000036101c401c00010110182d500003021014160702840346948142c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 666879118 1250 666877868 666877873
    0x15090602030f09061b03030709031502070b0c0a030609050f0702060711210d050a050609071d0d3e2b0804030f0c05100e0a03140c0301020705010617 65
    0x341c2c000c41c121050701c120081580709540000e0501c0d1810301a8001c15800d4420317104480d01d07450300c5030b03000e401021540001d0b10307000d100e402441307640c1d4030900071135403201c1c2c2c814100c40d680c0d01c4030317076625210f50050134014044c1a00d0750004180c00e4514807600d80300d8400f0715444522030820b0603000e403d02c00e001c0c0c403460070001d80840c5220358182c002445030030400255080060300318500011a6180542e03580000f070700d410901030008640c49900700b203018240494095505407290801a00c040c00b581507010141c14542409c84280e24094000560700c1c0d009008119040c44070b4800c0d10b0208880311169084c1d610464a00703001c0d01490303100464880d00550f8668561824001c0c20f2410380c402c185400c40180c00090b14404100248058800856100c86540d015000b58605050000e02c68054203005280200e20b1450142c0b103204900614840a0100250f2a00f1612141e0388000d642c400c00c48240b1031140c00c07400c0c07170301c0910007420755034001c000006e0038a0500c601e40c11009509000d060055 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 666880368 1250 666879118 666879127
    0xf011e02031b09030f0111040602150106090b0304150207030807180f0e22030306300b15031006030515010510030e100c0302130f121103010b04061509060203 69
    0xc10b10300382150420040b611407540c540c00c030b20000a10344030305800b0360851035080841c5502c0c840c2082d00608152115602070b6074119901c1e80c15a0400782091081000248440a003084424282d00045410501508901031000100402c2000703903400b9030781c06c03000500034100f007001e0030380e21000200240780c2507035503075040d240b9007a01042c0714455070007224106129940442c0485100440c04442500c0100000315192098280503004201601c05c0e6030f10081003003290200c611140e203140e0310000b07640c84c1d290740c0c078070380ca03295072041c414010060350750600001300c40c00140d541040a8825201a50004150b0368103514105040845150765001e090301801c0051100d6650180c104034603c00f90302d0002100f0402c07496092412061a201d620316926004005898a034150010310503414407000b461040c955403000e80340c0c00340c80391080e6458020014040f0002032020004011205001000803c80464110004046404603408500c01c52011149094142d0304400c22030000c041900245090 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 666881618 1250 666880368 666880381
    0x20717060a0b03070b04180f18060c17161403180705040207121101150b040312080115120f0608010b0315041505041e0302060a15030c0b0306120f011e0203 68
    0x41c006c5014242481201c444001d4548025900c184c0c0c9140c0322600034004141c07135040b034044c1c8588101e030540303400d03003054880c0ea03c540c0100102d00e404002c3d80c880032501e66403401101e069100c5c504401c010400c640c00700d4094410010051401011b228500004804500c0d151a2520304903601c013500650040c04140d01103202c0701c0c0c0348198148107080007040d0103541d400726401448a47c408103240c0031070090201d03454100f14090030a80344207554080d9001e500b564142c0c0c1c9600240310707404040f0b820300c445001c0c040c032030414034800b40710014020940f040d40300308201c2074031510381002030f0136075541d4050001d500c1c08109403c4030705044c0c421603845080c60b445000c0c1030360180c2c100150042d16003011400b004030340c5610116480760f03a803001d00c104241e0300d0f00035120301060f01c4100c0d0003030070111040040c241020400e81107039803164001c0300007482c141e044440c50300020850380d4400d0148104c0084a4010b03c8a1030340d04100d900002843c6c51100041e00f2403e5185e0020005640b051040080 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 666882868 1250 666881618 666881639
    0x190810090b030618070801060e06010306063018050318100504091109180105120d02060f0c0f070c0e0106080103080702010c02030c13050412050a0f0c03020717060a0b0307 75
    0x700013000704400000e02d11200192464208168071801d155840c04000113066010703084c8260041000b41e90520020b56644c1d07048401340070680101e004001c0000341590740000d03140154a40040741003000c24a0010405540396810004800b6140390f0800607030348903202000c52600708600c0040b100c0303019401103820020b055004a00500c00003541d0f540028108080d50307010350b44001c0300180640840806004610b5078071074284a42c50060303400c41c400319901c40c80030031060085030740c60740101980d9440c401c1602c03443e10003070440c90000c0c9040161000100c46034004210460290751000d040529041041f043d640059200381d081154000040c8002090a401c58000030b8092234a04220005400002e00f000c80701c80c81558015842d0050105241080d08414403ca000d0243c110250307928110507585403061243c880009072021024015840c0104180e01c101d80c0244102e80c403042e02c41d0101405100600b402154640c0403500f08401088035000b034044800c1301350050910700749881108017 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 666884118 1250 666882868 666882871
    0x390d140c04090e0a0602040b07050f280c050a03030503180109020f12010b0406094802030f030c091e01020309060d020c010501032108131106190810090b0306 69
    0x24840c2c4032140041c5a8208020b40303d0f013690032180031036865946014085995010306400c403a54010700420b800c403020f0210b50105481180305568100304805082c0a082c0341881c00c044510b10045c0402152984469042002031807081e2500c82d540c2c2081d8412050b95407013194000c202e0303030500944200580b62000d611140c41015076841030040c1201d0002c50240480740c0c03003681c01502d801000280b1587d81e80283c00d08140081404034250140c022841ca000440c014016801d5500780d41e82c554a062a0b240c00d41e8005544182c90510102c02c0040d0ba1551058548849284001c00c080081d480c1c908071200e6812142d0b0139101c040c0d840440084d40381d000325003040b0700c43d52010606201d4808107404541003511100c008110039a12460100184001ea0301d0000c90020081c3d481070700d06010b4002c0c1809669121041a5204265920540c1c1e20400e00c400680110051004440310401142c601c7ca07519506c0e1140291b501d0900241c1040e0b51182c1d10400700181480700c0c10310705440c04503409 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 666885368 1250 666884118 666884129
    0x30403120c350405010c090602060f13050709180b01080f0a1403072906120303010b03070c0807202e1e09140f0108390d140c04 56
    0x18800b029441420300c2c0c009803100c50a410500c5010820042103010362240042906586aa00721183c40e18002c031b0350b4600072101040c41d2401304003c00c036081c04582c04822458850002c0380c0fa41920f86080c40c0c03d5400e807112008140004010900c20445182034a03409082c0c4807004100030612200b2540d07955242c41d070081d04d0a02021880629044203108503001d164214440240215200f070f84503103946803404041032100c1c2d48402260842c0340000002d50f019403004001c50441c1d08080109202d5800900700b02c0c1032040e02e01031100050321020180401e6801500d100240c502c20791b64002e10650406041440703000c4030004103243c200507001c4500f041364642c0d04e880b0a4207425100340c5100e85030900700e9584411851486002c281c2c80080c00d42600c80c40380240c408440300c04180241d40c2040c24029004c50760030000200030102ca202449420030a4108159a00e9154400c004040805034501c100a45000418180da000c642c000c2c017507451440441c1d0240d03441c008030390700210302940c0034a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 666886618 1250 666885368 666885407
    0x709020c100207031710050a1d0703050c18010207030b1f1a070f080c0105012301030c1b1502041203030e0c030c01180b16031101060506090d02030f06070203030403120c 74
    0x108110282c4081b121000e41005041101040d4075000704640c03505000c4010188030307010900080b820391107400b80c540221441c0b0303111800c104c000345e0008040201c2d008080e04500c28898000b000c60304001486005d2070350700c07019401c103840641c20800382c19003035086000015014040d41040140c1c110494102542205a403604038069181843c0140f00f600034a0b4515820f101c00428280d02c2056414240d81030301c550454604005001035007038880704401040440c1e0312080c1031a80558407400f62030307080d101c1c011084210801d803080900720f82207600924580c0031202405010146c0602c10080f000f0000802010034491940c0000c2c1d451000025442c10400c3c0d8082001c0c103044e0551800014080c14000d03d5120042104500003030786560401f0780c00900c2c600fa60103c11081841032030203507030014201501d000d002500340f010036080c2e10000c80c0c0600c148040000988418403103c0d015000e9580070b982daa05140c1001800d187c4104400c482181c60521942105900942d170010003c060001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 666887868 1250 666886618 666886621
    0x8150609010225210b01060e010507050106030305040f0614030406090201050d061203080612101e063302070302040c17090601030201180b030c16050709020c1002070317 74
    0x100d04150420710090840041c3c1001e0b41c0b0b400181c64070b6282038034099608510f82c0807100c4e00789818404021000343c200d41480005020003841520720162011042c1003080ca402c5140d543c2c982122110b40c4182e0000d4804181485041004c1c5a0500101240e00c0c4c0809902a01404d503401440058070040140340c1d60600c01045901540a64201e10302d0759008000c5c0c1a0358000414110345040c4c421000036440310005081480c0403189250a444040d0040503079868230801c45000301464103521246c919040040f81100e1100d010351800351030314203c14004141e082c111041007941c10440c10300410410418684030701d03400074554046940460700071503a0001c1c0b160666540101001030398410400004000050b4800507540341200c0c401e903500a204800c2d00300781d501084040c007071a00600b034100045401481440050420214600001041640b141da50f240c5810812707800744007030740e4011900c0764034110240b00007005086a41000c3d03140c40240c0d0340041c104c81806c1403600d0311042150 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 666889118 1250 666887868 666887887
    0x20c03180409080d050910020c030d1508011a12011e150302060f0a181a030a060b030124020c0904230d1206050a06051c1b050403030e01081506 63
    0x810121606400481c5660b5039070030504c0d414040d020889124159114901026926074400c1c0308560122020601035800c000040a6840140000d10700c510800001c0740302c0402c110745c01388181c10010070080301c98000d209560040c000c280c83c0001c81491541d2404045d000e9281c48004500b143c0200301c0700004411400051440020107903400194000e500801c000310412160380c02849111800c1e1a01d024280c0000112544660b6074000e60f00300302480c0480ca680c0c1a00700c000b230b64129004440124803240c55001c1c0c00d03070300d8109038081518800344030400d03840d10b040f106a5091182c5280701610701e00c100140440d4100a01410080c00d0707902000b4102d507100000e13142c4d1902c250540d03040e44c00e146d800501c02040703081141c2907035024510b0a40002014504440b960007203c1c40b80d250941000d60905010840110141c1c00d112410b0f100c46030400341004401e4001114070098860903212811418000c100b80082182541441001800e002646c001d540180c00207010032104d032581d0f1030500 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 666890368 1250 666889118 666889121
    0x7050307050c0304030305071b0b0d110f0304030306061b0305040e13020a0803130503030711151603020a0309090e30040e041b182c06070e04020c031804 67
    0x2c2c0080046000c00b00f404020140e010004101041c0501c072111500742400c458511781c0e000610800001d420300300106a00c074007107078000320390740c154000210342842d0000030290b030a03a10485085000135a6481c00b401215003040f10444055020186611605040e54001d002c03071086029211089420341e0001e190ba0040c00400300c6029409013401c40b20360394450005940c1c0d0070036401c21820f0344140380b01044c14103001064619540d0080b45500300070300c840c0c0a0114050800401a000020400480208020118080d109580320341e0090507441840c0c21700504e240c542d9001030310501d052280381d501b0303000000f40040346003c60003150000da0580103207440f0960000c0c0402c1c100d0307a002040010304c0b400350816882c8264014030a031044448065680350a15800340a44418059400d82c005030500301d903031050700c1e00101001403c07000401c5105a40d4906100245103081c0d41c043c00420102e2030707204001c424055001c5d00c1c103508001054114648900801400d034840c0d008042201070a6030b2035 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 666891618 1250 666890368 666890377
    0xc0108040c090914010e0a0c090b0f0916030f0506240c0d0302040f050910140d0f0f03031b020c040f0f0509030705010b0102030a05120612120702190e0705030705 71
    0x102c8010850600703603240c0002600020503505925500e40901c450007400007003040e40c002584800780c40350060900302030768000c040340489940c008003406150741070764843e2603c160251408041e0040319016a61008081d520504000d9401e181041c05111198403040301080250851080c03010000e04c070300d00e4aa01c2030160280c403040e80d2286ca00f4200c0c8039a015402401a28500c075407101040d6203800500c00781ca4025a441c100c0c4001c0160104145080d010080740803d4006240003030303a48254407848080000d003601940d45400341c040d040c0826402d0b2041c01c0307003074511407462030101c5542c03c4080e4852004508040c010380c2c9603420030607074050a5110764a4039036004000c000d6070070814171050382c07508250021601d84d882c02c2d10700c40741c07580000b066030003032003140e80c865103040041e4440b2000100050b1110340c00004008800d10804014002070300b08035941369040303460358014010050500c2c0702c1052044545005041844512a240304159000c202824031607541d44561400300c0d1a40314 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 666892868 1250 666891618 666891629
    0x10f090f150b09161101021e0706060302040507050409050612060112021206040503041a0322030c02040f240e04030c020315090714030c0d02040c05040b1801020715020c0108040c 78
    0x45002c02c003c42805603e0f4030307907214104d03551005244120001564200e1041c00c00c8c00107240070082807401c15002080c02810114810400418450350740c0d40481c055030380c165584404104042010300c4516418410507901004c100c0309528440421071860340c5440e410f005000072108140c19010075500c2d4900c0360f114685440040314200e14041c2001741d22034000b400789600ca4001c01d18402c100e40c1d00c0105030ad002d01d060448183c688a01c4c158600544445090200e040c014204480c5e8050f07550f5104500e18030900311004180044103c04005c1100701200103590750200f0110280001203000030042e62069050a101310703e80a14000646802108007030421a00c54180422203076010202d154001c4520202c81c60007074941110400d81c581c80c840341c0b0103402034501602c502c0985065005100d6035002418828542070700d80703611040300e900c0301c0c454000030206200a500c0c0341d40d0400100d40207003000d0b00d038084203a298250017511006c004000c3c5041100320b40100b418850001c8400c4000d09 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 666894118 1250 666892868 666892879
    0x6040b1302130305100605030c0d0b0f04150c0207050415080705120f0a1401050112050a0f06060503070b130f033f020c040c05131e0312050c010f090f150b 68
    0x28403c0d1704a50141c2094001d2034001c0c02411038803040750030408408048075502c420141810b40c2d6102031503542c40c100810540f41a031800d0b500c0940300d000c61095600041c0a80c0c040c2c26114241802d09c0f00380c4800c4d45c00240c401d48d00b14010040c03100046400f90588204440c3c0e50020045180c2c2c00e8517280e180c010501140c0265000c000821010b03841c4001c3c0c02c1001c00090200b60fa884242c0c414003230b0407001c0035060360000400200014482045550482d00c41c003c0002c2072034403030380400d10701102d540000680210002d9030301c42001c00c44907080014240350002e404142d08503034528000c2960300011901e2840c0c40108002280501c0d14900d13012141d00c5030032111200c40324002543c1e6403502c003003140a0340c83c3c0101280583c1c03003841102e1003003100703c5442000d5454100c00310f030132000c00b4842c41100400d40b500403000034852801901602030540c0d500c1d46402c0440200303804c580d8449054400740340360054420014013146040301f143c542004098031082800c4500c440a040842c0e000c030780c0308 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 666895368 1250 666894118 666894133
    0x80904060b0d05010506070309260115050405092b0309080708040315050402010f180503250f0f1205031c1d01020f220b0c1506040b1302130305 63
    0x4558038001c2e1540c03080004052000b03036690824462644584517014000801d00541031004110306882080c041012403160002800c2d00c190250841d100303000e5040d05400342103001c02091400c0d019440d0400b660354041c1c0801d68501d01b26501c1e180345540b06140d00300c05003d02081d11030081d8001400d0700e4018103002e0b030311101d610303105d90150f0003400f0480f10291481c0c0802d00740a03061040c00c0c4540d43c103840e100181e0140300002d4600c01c0418049001d401c1c2d115030080769a4030140808086000340303100c54000002440b00ea152840c4464003c00c00c0c015040800b00f0661851181e444111034009407403007861040c50506600f184140217120f603070f612500f4000b48805400f64400040352401c081051035070700380320b40031500340e114981e4070043d4060140001000e1a480314040030310303101031080e1041e0741070340c40181c122160030070340c012a1250000703102c01c0300c520a81e96409511081c1214200510f95005000445040400c00c052010f40c2e40850b00350080200945024007845d0020100c40c100c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 666896618 1250 666895368 666895379
    0x503010e030c1507200703030f0813080f1b0a02010906080702030304291009050a1406090907030f03020a06060e040f060b040b0a080f01060e2401030b1c030806060a140708090406 78
    0x45806e03911084000400345800e03d95941c1c801e41080c0d00424686904a0b0041056141c3c0c0002d038002e64000e0801907070802c8103010714000301c5480c50300500d5a070b028104841044c000981015065170100c01402441c07410000303015404400c8a602075808110034800a1442600d110748a642e0a000c160080d030302c2c0c09010b04640c41c1c6940d001150306409080c03182d60340d5404400182e44040380c40e8070401041c0c0740070880500c2d0005040d035211420004980c48a9502d444400001c8018202500941c121802e40418049603000d48c0015041180d40e05510b0309059885015844401c0805440343e40d490300e00f01d841da80ca0f50400070701004010808440c0d1501e40391116101c00c01c5d00e11300b01580d860803000203102181c1030515442500c903c002030f030460480200240c200020345040c1410965650926078075561034a0f514544240c1c06007000842060340d18000c0c6c11201d000e03103818851a401d0200f00c000a07808104030701030018071058541c0314502c030325001149020b4145002d81c064103100700802e0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 666897868 1250 666896618 666896623
    0xf0b09040803061318080f250c05041b051e0a030e0c04090201020d05030717040c060f0c0b13020a0306020f0c0d03060803090405070c020307060206010503010e030c150720 75
    0xb00401c5548a100381101c0c0c1070b6200b00e41707041c005180302041026094002c10014005800e004014600c003d10b41307103e003901e000c10100b03048084c0c45a01d500212210901c041c00d50100050101500c04226005c100521a8000804025540d0410000003000b03480b400c0c0720181452010660b42070303642c0b541e180000250144c22407401c07192961260b46030050a510b0035015590002c1d4042c1c02802d031101c6010030803034007a07000900500c00c0c4290070309035a5001c080050520f01c101d01450125810302d0401d0001410200d9048401082000c0030980c40c000c00c04128160f9045824a442418107100900c003181d01384a070b0348d002500040c804513a80c41c00307000c14001042d980400e04160b88070840c0140060702107601c113006a01070340d40240b000d880740d401c0c2030b8011ba0300b0501c541880001d400c09680060301e0042207810210058100c403004001c54202402101400308500c4080c609000c2d00383c05660b9200100394140d00b02e8071820020680711802401040c50402a11590a05410300c031004550f = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 666899118 1250 666897868 666897871
    0x60912010e010b040b0904060203040c080d030204030611070215030603120c06100f0e0f15120c0f0d02090a1107020d03021c030204060509010e0604050406060e0414190f0b09040803 79
    0x1529400c09601c0c0c141440c04e8460280d0071a80104034000c00c2d00c1319281e01c402034000400849500c0700342c3d4030210755200e0401040a00000d107980c0542d9840c00c62400c0d80666140340400342001c0c2040c080d0b43d0042c0c1c1e98076a0b000d0035141880c0340710f4481e52000000f9140a00442590180d1640050002c60110000c6841c0f4803404e06c2d00d01c040b06150740c0707855543c1c000c5800e100300b50301c842042001c252981c11220510380c00c41c120014200c40c244400c40010300340c2d082e00f050300e58694440c1074140d40741e0511800307020312410f00300c80c00b445400d120b80115140da40020043c0c5686640c440142c01540c400c10140e59409401030f0074500075849030f01c1c0180d07803062094501d1609000d440e0008038014400e008a43c26180d05590342030814010200556801e00e40062540d8072540621022815442d2131040344010702c0c0a54580d0202002c00090204031080c8041d440701500f40c080c02c0120090035035402c040a0443c070f080010b00c000c43d40d40b500d0020020000519484030140c030038403040c88584e0003e50f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 666900368 1250 666899118 666899141
    0xf0308040906060503011d040c17060702010b060906070212250e01080303190b0a0b0c03180a030c050d08040b0a030b0102011d0601060f02120412150501051c0206091201 74
    0x2c000c0c580c1c03034200c00d54103400240316010700f40c03540c816000341041c3c4041c0b0294215219075030341d41565441c1c1461180d50030102c040e0b4086548440200005254240620701150005854652928070f03d42c020031000c2c840c4242c040e008484480e202c10307015004003c4061903491143c0242080c04040c40c0032400d8000511070440c441c0c140c8800419124404001c9074003501220040038039000001e141580682180b500042d84889820000505002d1100061031050000e001039035540741d120300c0d0300b600d51382d004d03000324041e1907802c07070500006080344091b4041c1d40049490001c00c40329071900c91f44a1055400c0401c400ca0007240c81400c281d0503400a1035004000d80082c0404404103003420342c83d0307070390246071201d0340d004000400c1440e00490b0304036104101e602c16140e401c603100b0303401015940241d00040b0307581084a40c400c180b15010b02e01058400340070006104a5142c08005940903034400700101540340004414401c65440f9401ca580d0b014010b4400c41c0d00b03d4413001064020400b00302c50 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 666901618 1250 666900368 666900371
    0x190503160e07081909050307120807020706020f060c030615041508070318021e0d0b0115050f040915030204050403030c230304080c190f0302071a1903060f03080409 72
    0x4961014002c0c03a403070748240800d404103244c0300c04101d0000007a1400c2841030f60140020003100002c96181c5440c50203002141e1030386151818403003070083ca0b00700c0c03d92180085402c04031070044901f4001c92425001014901903d449403500c1c40082c840d901c2c0c4040b408849a400640007480d00450110030b60210382c152221401a0744445082e4141d134010224141306c0f502201d040340051905800400000b56921101014011440003046140d88000ea054407420b15070401080b01c6030040e11501c1c680840e0340760a07401c10324182d0b40004075000c0e40c0100342c0c030b25403202408070341c14007031400c46402190014028000303424142409001030044440200008400c120084106209920040740040400c1da2051942e5a9034645014640200c0910b500078003a10260003042008468001c2c582401000300d0450300001d40b40191601c05190301c01c0c0ea92106060b10b0800304607800f13041d40c00fa14903484a030008140c03200c0044000f01b40b9500715424420004d41d021051050020152040d600d410b43e0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 666902868 1250 666901618 666901621
    0xb0909070315050c0a230705100e010b0918030909010b0a0801051f0c02060903010c2c01080c03060310020406020d020c060909070c08070210030203060f01030c020606190503160e 78
    0x21600c03c2c1c0d08101d42008611404004021200744126019120080e101b448058855400d200908065006000981c1c055001c03000c070721540f51062160304030911100c4003c0241030383d607001281000310000e103c485040f515800240c5d0100c021b00403129407400c001c00f1388060390384801c0e0303418460700440119000100c94400205440c01c10b001080c08045a1044610301c06040300c00c22244c11301510002c0703801c0842402051103a4500740120551491261901c0d294010407070069296008010b082d240c0212400d88102080c0c0d07008003805810148110f401e42d40c030f0740d4a00109182032071f02e100d0240c1d89403001800044890b03001c982003060204075400d4444a48000c070420603240543c2103a164000c41400201e0401401021140d442920902415041520315000110942c29299031030000c20f40000070011145007025407480c0350384090900304104d014441009644040050440f0300900845d0784503072900c0808000c0000070200117048414070301d0040c01075800c4c40c2c0c003845480b0f008900c0301c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 666904118 1250 666902868 666902903
    0x101206020d240b0a0c06062903040b015303040305121303050a0b0a0e030a020a03050a05040905010f0303020f030f0313034d03120a0b09090703 63
    0x6102c00700d2081003002400c0070580342d043c1e40070100c10401d008134104400001480c6004803c0102640d204010403820040401d209000f1560002c03a0075840402c100300024501c0841a41503407145804002001d000d00d00341c000480c40c07028181200d03e00d5140078045030000100c040c0710003c0340841141c10120300740c1c2c0c0951721700950000400c1600a05c1c0c0e210410701c01403000d4151129800c070342004c0e02d941c80e1035060905840c2442505c440c403600d0104590800e40d8060b811411040740002e61504140c90300085d201c01320394170010f080080010307941090500c01e4040d600034000600c0300300440d50b5038144c010b0403840f5501c401c60140c0940c0c1d240c2492044044144d07607800307003e944254950b0303680003c40388000f41000c404405010010400040d405440540030b0f07404101119080190301a00c0711500400303150110039500b080303488515515011010003a206800c440400f600110348600007090041e1005483ca240c00007101c00c100704c100e0780009100002c6034010007007440d5484101 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 666905368 1250 666904118 666904151
    0x70b251b030c08120711030309100203042111010c210809010b040903021c02010f05181606020a0b09010f050c0304121b020909010b03071503110a090e101206020d 71
    0x44000001d1002c140003078004031b0804029448222002010341c3c1c0360122250004100120007441040141e00225040c003103d045090040300d601c2c0140014039681c440c0d907862190009a8400740c50411041144200410000da2500003003114151a80000d08104140c01003521008440408140d07013401c00040d11341c201f40c401c0401c003a406502401902d00e240003040c03e50045000e203402190750324000300c01011002c3c800d880c081c44818002d04251a0b41001003450441c0d2103508001a505014042107050340018a00340d02503072008001416036240c1d03060500600d00c991203401e00500303210030001c848400304021841a446030941d026400140c8100315210311100d4000c07030030031090188190141c5040701905910000309000400c407810300d503012030b00f000103980c450003a002d4140b11107014950140035080f4441120406641030034441d100041095070a803041280302075401e800303e44400c00801c0801c2c00b50403000d503101c407405900c7c64408000e6100c4442e00e01018030f0624898218180c1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 666906474 1106 666905368 666905383
    0xa090c0e030706050307030b040608070e07140304020a1202030c36390a050714150415090512040801060503070b251b030c08 55
    0x5440644254034031410280310703400409060000960000076254008518078020540c0342007000407034014000c603007103861140190303000810098544800b5a000350015640c81e0080106450306204030300007a00c0003503000180300d10800002c034038007a2860700b2900040540e4444902e15002401001c1c0340c0c244081451009000c25984041004000d120020003141030300042c64840042d214030700105401100000c4145010451070072038010742d5803040c4d800d819541d03031024100005881074001c080b0848041d070301d00f4000105a20081807005081c440300c041c0c0c551a403074555900c1161000d000000c0c403120b81d21000c0700085602004031030054245a0001031b82c40d0300304200c60b42910b07000e402c0f05000340c0c03103c101000050306d800100c54490107200e0160191100d0001685070a00300b8a0014046825042c10038840c005c80c0e1a00d0b500300c0f407064013420303401ca03035071004507444518 = true := by decide +kernel

theorem cover : BRFrame.Cov 666726618 666906474 := by
  have h0 := BRFrame.cov_init 666726618
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666726618 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 666726618 ≤ n) (h2 : n < 666906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
