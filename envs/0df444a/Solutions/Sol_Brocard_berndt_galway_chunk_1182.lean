-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1182
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:38:29.831491+00:00
-- url     : https://prove2.me/submissions/d221183c-ea0b-4219-aed6-716f974a0801

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 212410071 ≤ n < 212589928 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 212411321 1250 212410071 212410073
    0x2b06020c0f0604030504092f1b03030c030a140907180204030c08060a0605010908121b030a0801051003021c050c0903030c0706030b0a08030a0c0c1e080d050a0503040609 74
    0x2441040d048003600015070300c01c1d24140c9401050703a0f2150091604030380c98400f60326021070584184d802820b1108040c803054103948d055034041c0382c0041594505402c0d04403007c0041001c1030004d90300500f9502c0c40140c0703900701101ca03c0d054031800c01841c115600041c3c20441d5001c1d00090103001c9a0aa40341e03519030f000130303569000180c0b140350006080c0d5070304200c0016840000049852080544000c03c020580c0c4800044505241030f100b5400141d1050126000005401d40103000c1d0703015101c502c40d190b9081000c9181190400340c4000041240040104000d003082d4400914864051808600d007540e45840d450310900d06100d45009940d035070300018114030101c000c80e07904081c01801c40e521407244581d50b40c4d944529005490000342000c0c15406142005690a000c0d200010003543c1080c800e0501284d101028801c25940c080000800041d0303a010f07011109260459107842803c0d903801c04028500d007202c612210710410008001140900343c1c003105407030304940e008601185041c00c2d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 212412571 1250 212411321 212411323
    0x4050702160b030a0f051308030705040f03050a060c02010203130f05071a03091b0a030312091506170304060801050105131e03121806050f040e070c022b06020c 70
    0x203280940710080c0000c6004102ca42251002e14414100d02000b0701c02003d50340f02010541e5000d41d510003d580c0182c9020000400d5a000345030f00501a01c0c1150500340d5912404210000d40d074003e64064010300311010074001d6074011080409503e0000b5865410810a211001c241401c0b014020701050220601000021300c42180104066450b4070514540c071030480095074015140c0914501c281296513961802800000d0888500205103d0b2480d2554506840190440071841c030803d641e001e00c10000303003d116850b4042c82e68900d0018106080180082c0540000310041e021644280000c000142e4000e00741410f4440a00e413042c3c581d0080c040d01c06424019802c1030f49040c034a480032007401700300e90041c00c00701e9004a011160b80113000078250b5080303100315a041c410700c50010003071144c00d01820040110440120000b0324255444a5100200030140e480d440010f0360028014151300d40050000b08841c441c0c205111007a00815400c05007050440001f0105a0081810182500 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 212413821 1250 212412571 212412583
    0x30a12022718061f20071e06020303070f031b0503070216120f03050d09030c0b16020706050c0708030c010902010801051504060c02040209040c091505090a1716060503011a0702030c04050702 83
    0x13180304404801a516031503540d8a84086c0d00074007030182d810b207134801c0a6502136665a8101c8041d6000703145035848000046551038030b10b160507018140c440000711180c8540e03410b80003100700655280f0b80c41c2d040885000b0304004940d106400b2004030020240079040e034030117021000903844414208410000e15003600d43c0e000f14160b50007a103140c505200305254000060110052048603981019034803800f0548400003007100c40e000681c0076038014850503014000604049084200f22080e096070b95501525691100583c0c01c4c540c1d440e8180c0c803003156000b0404c2030152000f210108490342c901d100f1049070b4001c5101d030301d00300003024400b0015500d0b250304607402c0b440007501c1440301902042001e092940d1130320421103401f814001d17594480e8450000c2d11702c400d00007401c4a403002c1c5016005e05c01c41310b14403a1852540240351080e400000d16a006000801c11a200c0607120741c9800401c601d54201310b9214010010304000380401641c022a0a05c03e1000482e40050542c6400c4000c0345000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 212415071 1250 212413821 212413847
    0x60d11030c120703020c0a1202030d060b0c0607021c051606060905040510020a3002040e040606050901050907200d022d030a12022718061f 61
    0x26000014080300c0e51a16004000303014001092000945450340220300303d02c03030782c0240c151540003007108100140011038070b54800340c003901c1100c1c1084a8012200200c550a60008902c4400003c0f0b50009a01c148100d661200f014005030220038080e051500c0c2c51701c0010004020003800052540818003c0344950002c260042020010a519101d00c0c0000740001d031810750303591180131064608000c490003181c101400c103070b4500c48814400301c0001ca10140b29041c4c0c000c030121031492020200c0c0144058402410541c410003500e041a090a60031a12290010360040305590700501031501c41001e6990485014030f450651342c03610a14510303581e901c00010840320f0003403800780d0000030780c0011000004400d49800300d2811f80c04180041d040b6541101149103a00103004030300755680242220710804925400252a00d0100d0311907034000940d26405003c441c54910129445042c02c050104000da22805040c0c1241084070008004090025000c107600b05240401a4010310440f0700c040d550b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 212416321 1250 212415071 212415101
    0x2031c18060501030228050609150c0a0b0a0614010f030e0a060b120601030b0c0c030412050703060e06190b042c0d050f0d0f0e0a030305040c050a14060d 67
    0x400a6481d01c200030308401c3c03100740e12910901c1c024001000b00221000003c680701589030407507515080030702c43c01d03401c10710905601c0404840202c4a1445060040c4404569100a8200d1002a24240220100181051031101d2034400140868460320805040000e0300342411442030001000c12805441301112040460003805804010800c80e90489810300c1412034402d8a064881d0b400346545090910001d07140d044078001080c0f403030028000812003410000c0c00c2c0c0749010b0b220515820b0302d50040d40d04031b90b15070000c031042050018501c2509aa142003901401060401411a6a6081121030150303061030751801150340c00d5035580e0140203481c02181d000c861309841c0c2c08500c80c0c020006c403081d0025020f2618441600341c465022603c0c0d070307241020410700f00090386400c0c00050000f0040c141d0500c0ea200030003015607201700003030074025101e942e0100b02c0e03107024a8a2007142c44598401030007290105000c2c040d1001c1c9014660951900703403102a21000d85c01003610107056940c800701d80e4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 212417571 1250 212416321 212416361
    0xf1209080403050a110f010c030e040b0406081c020d080906190219021c030209060a080606090a030f03030b0f01120e070510021b090c030a02070303090602180109050a050102031c 78
    0x1084a25203602c1c150f071000700c6d48031414005880055030402000c4000038006002110100380c1c2c4e19066004500400c405000090f5440d142c00c100c40c80c100c800d1007440c01d80c08142a441c00b005604201da001c10843c0da00d450205400c084040580d0707880c0140c5117003000c143c0c80c0d0341d081da80d4145505896603640400918103c2c94030110019444481c075070550760100b818440346040d468001e000b2110380c80805060b852038107003a80c1c41250300407005400103600076000c000b980c6d0243d5400740e103500954024103000001840500c4c000e41100c0020684501401d07980740003803040d03a049041c2c06030b40c0343c1d440c0001c00c030788420201322820241290040c6900242c40c504503008503038001010424039000080e242003030740000c001c0240c0e13921308072510040c002d003c100280071543c07580c0103000558403904000c2010002503880300146e0b00254000001e0100c004041c550640e8800c400310001c000945e8881171840c20280001e460340300316541a071112500c6031010f0010107199001192008444d0030b4188 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 212418821 1250 212417571 212417573
    0x3090f1b0a0905010602070b070302010f05040308150420091305040302030306010212090303090f190b34080325050301090c0503060a091e06080309030105070f1209080403050a 77
    0x620030541411190003554000e0001c103000e0068492541a111140c004024142c940222455250310044080b0119501c030741c01da03241c1c480b440c01000c6c0124800e40381e018080c40e0105221f103811004986084c4101e0030302c04001440d84940226941001030316441c59680c0304036502003410600c00d1034010420600e040c0070001070583c04009507001e448242e02390b03183e02c03100300e03000403940c0a101752140d03042e00200508106403802d41000812100060704011280c5a50107403001c00d01d841d503100c1c502d2804005041000d50100c0d4242c10342c000703c03003040c035421408007034a000b058001a9200400d071040c0080031030402c070415000203d24000181e0795040a186200d0300a05c6904203108404555081508030610540a80c003076031b11038174000e40f841c1c056929250078030303000d8840741030240b010800310041c0caa500d15041c0034000203401201c000b10740ea074201200741400c440004200071704100c4994000003501d940290318034112682d583c004214904682080701e954071441c1c1c0010024403c002e0950 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 212420071 1250 212418821 212418853
    0x3020f041e0b100c050c09250f1e09030212160303121401030206090d060b0a141201110301270914010c180b0309100e060405010f0b0a0b03090f 63
    0x200300c03040070748010500040c0303070100b130340c10780003407071009101b0b400c034402078a15420161803295010409600c25240c41140030815110107881540000010f8040d0031841e03072494012900d90040302444101032070b005010340c00108038ac001d5000c020722428100312500c82440d401c201d9211640d086040c05c101c4a0b41d41c3c640640880b08460500d40c505041190010041010042c40750480350080c0c070351441d00384a4401c0040304004c440c022a40503a07a460000480e8403039400d01000b821580f19401000d242d041c08110501d0104c4c003885009a0528100001b142d42080641c4e0446148610142c0b480030046c02c2c02405080015003862410715203440d640502204450441541d101c910080101c06902c003c100c490a80c46040c6ca00307101c00b424420452444040021540405c4650030344803030141c1444948141e0745c0001d5900381903070200d01400b081c01801e103d4000c441080c40d00420070400f2402c04695480c00a00c1042000d000100000382d44c21420300015101b0001201590302e0f103c5440030701 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 212421321 1250 212420071 212420081
    0x915090501122904060902030708070f0302090a020c070512030d020310090b010305360a0c060908070311010f0c0b01090c110c030307060504081207090e0a0c0903020f041e 75
    0xd481944000805000c0034440b0100100d0110142400d240c513a13545445102c0940504d100882e010f201c1c1d4080040d07003039018400080601102c8815034286880d44c01081903844014050880c3d40d0701c1001440303001c0c200000d4000c111601510743c00c10952010090700d0460040b04485000756000000b0492008034071002030040d1a40d07400100240381d038000046007220422202d10004500c1e407105c055031a03502840d155010344801100c0386056003401603190400303100a2080300d0380141d6160134040785030040142c0c009480c44000410340e05155480d0040030070152600c1d24180400166200304d01403051480200725500030018001659681895500806502132004001151100d681d0301000c03002c64118640b1100038001c40c04c11400c0c0d141e05004002c094030803a12503204010308003006207403d0400c0e00c2035005880381003040e464480c20a003845d100a1401c10100d24017403403401110340126440050301c0e0192146a81ca03441c1030089402010206d0860f80000d110b110080d0035103480c5c1d000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 212422571 1250 212421321 212421323
    0x5071806030c080a02090f06030f030409020703110d090b0703030b03010509100c140f0325031407080c0714070b180406050a0b190c0c17150c04091509050112 69
    0x40c5441043d0b46100d440d80f40e129581e0001c0d4400d0b01500480c0c1200b05048110381c002c50000d05803000b0001c200340107442c5030700030b41c080054a60042100e0f411b050301702d040138940c1240314010f072a100301c2814004113011010b01170049400c001040600506100c1e44c8480c9a030600600208000d0508407074440c0c0c3d4601451404d1003160400d1003500400b84541000c01171020302e22031450604a07078644032142074000070701d454000103040c45148102c0c80300c04240d600850440d100050000d400c020404c508080040c040024800008248118080700b00c04880c01940c0158144114041083d00c045c00c000c0154011032aa0b05c0210f000e14a110303415010a2030168121800c20405079548180507401c809031041098458082c0006000b00c0d001c460003030f8110750a0701d0141d418130015590401d100c0059080241c490140078102c0440c540204999070141181146200c09813a00000654982c8aa0300071180707141e4075800da8102c07038525000c851010f8004920148450740e103440c0c0584d2810743d5160 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 212423821 1250 212422571 212422583
    0x6010c15061706180f12071703040b01140913020d031110060f0806010812070302010b09040804050102150f06010e010210020a0203121e0a0c0c050a060606020c03280507180603 77
    0x107040060300720001800c10b03800070340130040c000742c5c2800d0f21803041a42145109a2300f10388500d956106e01e41c12000110b218a1041c0034071406035041078101200108102c122f140680b40a40c140f042c24000d00548013070050381140c20f0b0090301071501d82124030b06010110304100e031054181815404074280c11040603a444801e0104001da59142c0c4580c6c0d440c0700f03104003881600903115002c0041901e81c020b1458074000d00001c61008030141c041607480e642201c094541c0400400c0a04c403130342e0706208042428020401e5017091f4181603191032104140034241a05120042084841c0d6034020701880160792800101151a00d8042601940f66440001c544a10110140c0003802c00103000c24500141c082c03102d040030040c3d88a120240040c41f00202e41d005100e560562071002a80803c00301071171611411010881d1032030442c010380303041c0c0b03c402a544650441d07051b000602c440c0d94007a46e295400b02c0e610810800281c2070190800329190054240c109000c60520710505198100c0012284030f00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 212425071 1250 212423821 212423851
    0xc030b040b04060e0105040504051203040f0c0e071202030907030f230f03040303030b0406050619021b180c090907021c0c11091b04081b040506010c15061706 69
    0x10704010849009000720641103003028014040350500e03a021541c000c0c455021110812a4048032030714581085a04460560f00549541e041010f0000804003e2944110780100c13130900c41000b4101c20282e01c2a41e041c0d5502000050050300d0401180004641000c282488140326060501010016150300c0986c0c1501d02d1a0000390640001c040418041d410003460070641142e500300e0280824040699002c2d417109804030703c076551a40105045071003900e44101040d40d1400c040d0610240080a07004090800d01241d025201c60504603800c80c1044080c1c00c0681d030701084403400d4041c038a16190001c14080420010300c0d0001291b000058070081c1000800076481c804891590079028014810ba1130410900142e00342002e0351034000c950055140302492a0000140640c0c010340e0240046510601444810303a002c181e0142005a0030ba40512003403501c20b0001e0501017806000404883e6a03070032450348104a40c0c0000064050700380c009000c1000c82d40300319030b01c0c10103450003090000f0302 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 212426321 1250 212425071 212425091
    0x30915041409040510020705070e0f04030e1203090112020708130608131208060a0306050c04140609060307050d0204031a07020615010f051317030a120209090a0b040f0c030b04 77
    0x100c440184241d50003001170480360800c6243c04040e400140c0101c030144a54076011500168032042180b003016603c801003a5031401d4140203088516074132845003e19400c4403c91412a400b0044541c081c8003070924601c0030b0f1030203024400920a80401404004000c210a42090144241c003400c4440c20b80d1011900d4071803100341410808082030060026002603080310031280240301441d0b1107940100004e000558949403241691011504465003001c0000d040c00780744410010a078480b002500c00c5418211221b010605a00c0041c00e0082840004a0f190300c0e54012901102c01944d402040300344526a103001903c1100c005440c0d41000d40141400501c000400c41044403480b0030595030801501b0b00c266042d6040d51284003c0c1e00e4100442501264822109010f00d603900c0c1d0640003107660b607000346001003070300c4d40c8544404c201c1e500411050006070303941756065811940c1c031440000d0400030300c4000f40060a480d16030050040c10040c400c0001178050f88034000e24282501c0900c209216 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 212427571 1250 212426321 212426329
    0x7030c080607090905130f0606080d05030c0301091e0c05040303090e040507151403090d0207120309140d1406010905060d0308041104020c0a0b07030f0c120c020309150414 75
    0x8201d0b9807000141c8a00020060b1000c543c01040e0803141006000e000464541c4801c1098408141d060703609546440b0100704405c803c01120501000511f131250841c14004d001c0c42079480188aa880520713180c0c0715031640c0031401841d0305130ba01c8011a08100c504a50701003d0480d07000b910050303012941c07003040050520300015006104603484409000c103607042107151509404400202c2081258021000d070b130801c20103006502980180300102031080c0c0c055002494401c50f6007010710500c0ac5810000c000a4003c64a002500c140e0620415208010004295a5503403490060b140c41090624034020f80004220241078840494040c0081da845005000560f40c81c04c1c0f0080009a9040c00140400c0f2011854060303048000d001620308078500a285181019450003951011205028004421342501ca840e4113121950b4003481180d41564010b000d0385000c5c400102903d44904040c50558403d10490303281c40c4c4020448907101980f10340c6513801c2d820a0040c50081a480d184a039060f2030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 212428821 1250 212427571 212427583
    0x20f10170f0a0f06051f03180c090605010201020f0301090e030d11090901060f0c02011202090a0b0d05071b08090411040605040906050d051e070306021c180c1e0b070507030c08 77
    0x4010b03042942003850440200e86c080d4000c61003008155580c0004031000324000c41040f0818024610302c91214180580380e804ca0f4290750180b41035a10400480c2c0c0c02031440410307030381180e41210000030340c5100004098214491b80c0c0018643ca440d082004480b001e402018102d0745005903010149aa20f4090582d1035a003000b001c1000b02741d032000d0503c0103610524448602100a40c0094140000c00b400308540722000c0d00900c00d4900c01040300038421205100311075020620b03181c8a211004144170034010440f4a07035003d441c0380000118456240c64070741200750b4040742d1062040c2da5568a83c03006003e600580198641e4504007500055245003000c40c54904a80110141c60910b0914181c102c071404500d05500440c0906ca0001000c100ba91025102d84802c500242ea90049445a0311044508040d030601d01c02c80b44041e2040407810302c2030500243e80300c0e045a81e80c0300d040c010140040d11a19480301e0750420300040c0701d4040100110301103045034414400306494a0300e52603050784980c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 212430071 1250 212428821 212428829
    0x9180209100f0e10141b0a050f1b0a06050304050a0c03051606020109110f0d0c09020304030e030615040f0b0d0f0209010b030c07060b061c0e07080a020f10170f0a0f06 73
    0xa51508005c07003022603d8401041c00d158012216a014030852001c41d04007034055070107884941000d43c2c036009107001400394002040d001c450214003030302c0c081300244411805024a10810002100042c100700c02005428280b0b0341050584205030340d00d00e021507803103c0c12981400b004200100014000d03005010b9500d50302d42c000c10000180910005200b0800c01503480b00ea0720a40208180d000b2502d10000d6101600070740c0c4016980703142c10b04001c1c00c800c51464219000f6481f1400304003c24583c1c00300064080011200460307240d00b0800c0310005446002c3e00c0c10380c06410086032a0030051204c1030321100030300c26103040c400c581ea1610280824081140c05500e6014200910000601c003035124000c145001800a81400c01002d0002c3d14400141c844407522941c0b185500c841040802010004010102c02032030f80c0700c01030740410141d43c81e954425025002440580c0e083c07500904042c2c0412988100f00181484c200c410020a66000d0364045074440c0781040400070051a4010b9005507 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 212431321 1250 212430071 212430077
    0x503030f0d090309240e060405030a11060c030406080603150403210603061a04060e1006030b030c09041a060f01090303050714030a02070501031b09180209100f0e10 72
    0xc10241e4a004002d020200800ca0410428075000b161782540d071010321400203074207004e210041c1e40044001c2d0903440240c80c11842850180001c0210303a5001031614a6542c1c0a848503008559403000b1030603600440d0102c0a1600000c41d020502c1030303211020038032035603003182141e0075031964581880b2100025200a4001092415840c00001c2d411500c9882c01c0403400c17000904540e41c0e1100b008460030340c00e1881000c85403054916461500c2d02851019242c18040480b1506101c0101072984200d0b10442e8140764594102641507034050022950a81d03001c0c0800f8094a450301d041448089104411140c060040d000300f0041d041c04080b04c841100c0686078103244c1411520b05842e19088030354201e0700ca041441303807c070800700148040e20f403001c502e0f00141145800e100000d0203444602c11881400748256100341040c590000d210000c5502e01d40c0c108130003804000120010f480362460194000b04910b401649250340688102c41c81810396840c01d4449004108104400752420040000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 212432571 1250 212431321 212431327
    0xf030921021213060c1b06110c0306010b16111807140c0c0607080d060f090e060c0f090a0b03131505090c01110a02030f0a0507080d1737060503030f 65
    0x801409840e171042824001d0218000036458a450068220303520f400140000340404601c0d1140e840803c5075081c0b800044010789038660602045124034029450054000d0f201c0b1603445c018410300920381c0c46e450030060301200c20f280c010340100030601d6040e80d0100029a5600b61041e21210000a44150f02c101b4005040510110b07006c110507078100c1c20b429500da200c10412403d0802a40c400c080c020711042501c0f000e41071401c180303582100e070003c0514185801610030448080358810845045a00e40d0031103d0b1500001c902051080c0314980207180100c100100b480103d44003034070500e005912800d003200d1201c00c0f06a429051320b105640305981603120700c010546d0f80d80100381c810009240c10040b985941e0840c2c002030320300241c0c000c40b2540d0303070880301880e824006d0500c03000d00603140241c002c081c3c4441c11100280f19064008031079071035010340310200e1101050303000f01c600d801000710b00c20320103c8660780c240304294103261a606481454101e000501c0d040c0801522408c1c0c0380520303000c2c2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 212433821 1250 212432571 212432579
    0x914011215020a14070c08010507180e1015050304110d0809010c0204020f040e1015020604080d0f0e0d09060305070e091312021b0105040e01060f030921021213 70
    0x194010304004400d0100c4221300c042c481c00c009001e0529140503410020600d441c0c890408d085a0014280f141007000340b4007400c07400a050421401100c40f00000c140701903659100c001041c0180e0b070024810300f0745824140c90410b03400405140a0750007545560811610402080600b8818000003000a40c0034009c6c51890360140340074964040c000303040540741020900150b51070303030301941100020280c42000d10002c40c00c2804441c0203030022852100303000c480c20a01a680321070080c002850314100294601c0e4000c034179000140041e42c0c5076400d00c40c0712444910982c40f0709980b0300ca000080c0c050030000400d6071207806064000e180d80d0725158440391703840041c440100002082c41000d0041c101819001449071030010300410440d501404c881d52203051285134181c0750060080c10800240070500c5108004401141110243c3c140b81c085581d804a064001d403042c400c0141c409502c0a034403086e10041045c404000403100d5003a6401180c420100040c80d00560181481e01218414140 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 212435071 1250 212433821 212433863
    0x112090209091516090e0709081c030e0f0316050102040923070e1c03030b06070f0203061e2202090109060918050a0311030d0615080105030c092a0409140112 69
    0x250300114107140420798070351120301c081e203441d180ac224940394046002440c2a0b5541c140305425000311520007802e41041c000c1a080da40303014414a03c20001038961501c0104982581110000c20f0540000e103d07100c1212046820030b00c0e0226180c0031511060001484288141924010380f48010164280d00240642004c400700c880142102132503641c0740340d021142e44440141030150311901c6150f00140c1c0741c0c4141818401d0140c40c19454103420042c0e4212011840010390780000c0c044d1040c00c00242415080e5481c04444e0300103504001c1e40d900100e0406402c2d045034007605c109800601021101500103040ca5a038408098000e81000d404400044d100e02000c6096451160880382030030b81058802c4101c030700035441303102164410341c3c180180c9a00a41e030140140001c5002c0e0840c481ca0360040f40403054003c2000c3d002c103850f00c0960041c0b411518002c4454015180d5040e2901c0c1c50f440c601008003605e001c9240345c1d070024400061424640c8100d80c0c4010b510554031156186a18901 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 212436321 1250 212435071 212435099
    0x70e0f061012061701050129030606070609020904050114010501020c0a151701090e0c040c1b05070902070813080304080a080d27030917030702011209020909151609 72
    0xc40c4540e20382d1800602d4001803c0b804c11003041410002540f5403410b40c01240e880c43c141071804e080582802c0c42d5070131140c11001c0d84d6001d01d040d40c83c540e071035445181140050604441c000c0d400110b110a21091001c154024070803861201901d228170390700c4600690350740f09125100c95208030b046d0402c1c03281c0103103c0c0248200c0003107800d0071150043d2503050410200e00903002801381c1944c464448514030300811104000d00030685003008055104800245032003004460081054200f180c5c0c8010010208604c400510450000315110415454410801d83c0100d01113503a0304848400801c1d85900802140d04131501900105014a000d9aa4050541009444030304140c0d480c4808180b941c0d035000000500e240c0e20070488201c1180c2d14010f403a1130b4694102a0081d841170001660707400b0004121480707241c0900744a02e6000c140c20400b0040e003c5030318000c0d040380d0f52138244801018000341051014401d14000c80c4241e40d0010002e0001703c5404508000400301171040042c90150303080 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 212437571 1250 212436321 212436347
    0x70b180706030e030d052a040501050d0c0c02040c0504031703090303130507080703030c200102031c021c090c060e01120e16030506180a02060906030601170108070e0f0610 75
    0xb0b03a401e00c0d03000d04000c0210f071804c641446040c3d403581100821044868020080750900b02501f81c00c05003001d00003441805543e080c080b5a50340c4e007010802c41d901079410310b401554018014441c2d82d468100041990b04540310881c2c82c000d407486001e90b020343d44030640b840f80c03640d90000c506541d11200e1688100b40c1c0f0640036162030244410100c4e0014040c458040030790300035107030000380010916103010814144e00d0400300800c41c60344840305981c0d0100440d2307844180e1031000c000480d01040100000e118100c0400b80e400701042e849410240550401e8107128000e03d026103007180d40c0c51050704c1c5000315200c220f00080300d00c640c0450810655122581000e8040c04072402001025155152856035400598456020804000d112401d400700445410007281c040d04501c4070395800b1078020b00409403418410100400002c01c20b034822180810100251013000340956515074034251608040d0081c8042d402200d0000b0f4940e240043c4d000c0e005000c094801d041010f2012000c4500140d1608 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 212438821 1250 212437571 212437573
    0x30c0801051513080d020d200d0f03020c0129030a170f1207030e07170a06111303030c06050601030212060907030b1e10090b12070203120a02070b180706030e 69
    0x10613180400c2154541c1600590020300800001e032001800c1e94070f00c041c0c68851086032a503450354008c1d020949900386001c80c2410321161121364000d8010b80100d02d21150b0030761070b00012011608200c2404100340500c04290000f500d002e8082c1603c600e1340c0c2001515078080c4000382c1001c074007844020050340a0070104142018241c1580c10001c5600b95480c03000a40c40744a40341d01008140000c0005100040701c0b10000055407030143e4540a002c0009000c1c01c2d900e208035080514003c04454041c0207136220500d80f11703141e10f0050f1034101035103415601c0618000004035154001c6c8200c0b040d072461241d00b400c6550303030001000005100145600201515414501d41ca070700e8041d10041104000d907060754a00315458103102c3c03054100100e91081160509040200314084011584280c0078140900d059a4401d0301c160310f58442c410703411302c0b481050410080300c1d010a0b4048e04042d8807a60860b549611045110207000e00006c03008401a004440e0030001e15000b94022100f10351031070 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 212440071 1250 212438821 212438857
    0x209070f1d0d020d08071a01060c020f18010608090d09030c0b2212260301030f0f020306010b030a0b010314060103021b03070c06080a0207050d0804050307061a01030c08010515 77
    0xa4045242005602411034445e617000c1121001c000c0307040014448000741101e541002e40c50040c004190300b09040001c0e014004c50182110745442e1042862180400111401c0041d607458100802d401f204a4945185020341c802e040b00710b40c07103401071030102c1350001001c4000d10f0407c03902880d140d0006000c0003503441480300b01103c4190101c440d40083c0b8400d000c032502e113181800d2019074500550030300c2c004450600d02c07182100b55000b00340c80c10742c0d03040303096010b145c045480d000400103040c0c600603505100f0035000007181d14032040214401e1500110a01100551100640c165a03000594601d400c0381c500014107194802d50103400004558419060310700301004099007107520040040c0d400041c0001c0500c1600d070003400150f0050f4090340114a010030740d454190311010111403400c10003d4603130209003030040800c01c0c0c0d18803d40202c41089215068400000c820100e400380d02d0120b4180300d44440650301a00e1034038100d03800605030403d1000300300c406004690280d00f2841f00c0d44040 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 212441321 1250 212440071 212440073
    0x311010f0912021b0a03080f0d1806060e0f160309020604030c05041d3d06080c03120306060304050304030804080a02090a09050a15061d040209070f1d0d 67
    0x15000d0009014001c0200d1030888064400090034420b0511074010baa860344c8100d012107440718402c400450750004809912080424154415407040340e140c15407080c1080030840451040341c05c0c0c88000c9102d0641003001c00d907a841402100c2c482150b900280c1501640050b00347c800c804404500001e10b460300290028096000030429002a0800d444d00c1070303106c4c1b040c800e0741080d106040c1e01c00140d031100c0c2c3c403030010880c000343e698aa41d151034055101240f60054840900200b40c0601045110540313900900c55190b84005c00844c41046010311808403595006d0030301140c00c81c0026003020704245196902c0b42030114691000c0d1084030503220070400007011880443c06440030740b00b80c2000d03001002407401040310009001e4900444146800c6640002580c005003154100754031030001000001810107800c0109016404510401041d0b012401c403640b0b403080c1d4510030b40c401c64088450303890340071040310760580e103001c01000701318540c10b42c040c44a15464022a4140000c2101405001b9 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 212442571 1250 212441321 212441351
    0x1e030b060d050a15051507030c0c080a06060b0a020309012105100e06041103010e060d05030310091b141b16030201030f0c08060d0501020c0703080705100501030f031101 74
    0x250110719281540e0702d0a001d41c030b6015028800d4080c5000b13082a8945082c280001d60f084032110061000000c00903800b003c1601907585000419000800d500c442d580c1c881010792102890750081b50b1061806c900491082030b010180c3c0c40d0500154000c5007070100782c81c01942c0300034030b95409402087d6aa14083c685403954019103101e0036542030a08040e5140034110742d010392001c3d02461046040c80a030140c010b0020301a41d044415079110301086448440c0400c6000c0c003a05006026800000704000e1442c081d03450320303800c440c0c91a408208045030754000604d8120709138440d400251801d945030300a0620035010b01600800c60307041d81003602d03041038213a2404549105416541225507000c2003590703050b01c540d1203840c80c0504240704059800b1002844424014000d52003400315846401c18000254142c5105100080860f112580c880c01c100030541c00402c0b04807038034400c03103410440382c03105405442d040329881816441d05083d59601914007441c980340743e20f00d542d6104040124050 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 212443821 1250 212442571 212442577
    0x9150403060c02070e0f0c0a03020f1e18060c070303050a020f0f1e0f2a060715050c070b0406021c051602010e0c0303040b0d11040b091309031e030b06 66
    0xba00d50000d0a074a80780041c0610301c010000c080716000f042d1002004002c2501d182180c038241240d1030016911044d008801c466401030b400d80c1c04103441d00a040200d000c540d10b009041d200600d561450403141080200403403445500c040c43c64070f40000e4001c20002c5c9c01640601510089401664200c560f484016803030a140380060848a52152580700d1641408010300c0088120381d00240201501281d552035070b445254031080c05a40c2844607640840780800700454071100000c010541c0d4180030304103603461036501c0100000c42803600b80440e400f0703840310040f100d0103035008406156a980d5626014000d4103c8000ca44e0001c80113008198140b06510985100b400032020500c584d025541009084400101120b5410b80c04062a44c9060346c3c000f05480448401034100d50303462040b00321840103454241241d142801c000321340840d03007001c9d4001408008106542e00109501c08a440500740d41855802034049500e5625030301000b085102d14003444000350801082d03038105840440e41681c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 212445071 1250 212443821 212443841
    0x504150302270a05060d03270602070515040302010c1e0206030117010e07050a030b09010e12030117070b030a090c0e0106020109110d0c121b03030306031202120915040306 75
    0x26404a800e154101150a0b20319048071200008001510307028000c11841d03d0840c2000d018810100100305810100c000091030203000801560360305c555464000e0b584088501400344900d60360342d000c000220120341039030207c03501650340100c24010781d15611104000d8440300e2540402c43c0ea102070150326540c00450080000c1c610b1130b603140001c4403e0f01e00f1641c06a03903140c0c3c04e0700040000c000607500c0660413002c2c3e0760414000301040d01c401c0c06480c01094a100282080c3c021304000c0840781c0041c4000c0c1d03049031104040b0640280059103d681c5503c614061850702a41c10700100751009400e81c40301c1e03042407007008041007241e1120006101410260300c4240140e440da6058410450f024201d0031410750305690100d9403201c5691200600d641c13a015480c480400c0c00c030b44e01c1c10f004000440c4030003084081c3c2c0c3c42c9407194032801c005000e0305a5010a075000842c0c6c0c0c0035041d069100003005803440000032081410001c4450800c581e0824480d80b508012400380404000701d20b451140c007081d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 212446321 1250 212445071 212445109
    0xa050306010201152303010b0a1508070c0803010902090d02030f03030a060b09060405040b010c1a0402091f05150913020c010e061308090d0f0302070f1205070504150302 74
    0x80e2514000081c2518200a00d140701c0c1c03d4107035020000e0800b05074280300d01540c030004404081e419074000c24014078881040a61000c2d9548000514030720748034604d201c400c0b03e565219156130300c0e1a025036800c00150001080d1071010001040310b00d450394040c00250a000f80078003141012900024540803007190444600d800000034020529002d02c80d01c1300601c0c070a070041d03082003e5140010300d41e005c2d9110f0980915107500b45400568424400c00304c1659001140d00c00c14912088910038041c8122001c070300032040c030700200b00c0080000c0790780f0340410b40000390a8802030805060007502c08a0b4607500c0c444030010300010344e0f41c1c5e40341d9800e100300d4468110010b0301d55070036022150135990340611040c210341002088c8034482c1d51002c1000c00c0d0f650404411f40d664403070417001c1065452104809420804200b0b082000c0560110f0401c089807036851480c4c445c96151060900440040d0400600c2c661006408220302d0802c5d810140260304e1040035824069901c1d00800d601f014411415801 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 212447571 1250 212446321 212446327
    0x40b0a1715011202090409050601030c061205150f04110a030209032107030c0213020c0c09010602010c0507020d060e0706020d090807120b0402040605061306020f0a030f05031503030a05 81
    0x498800200d4066120241c032040400601c4040006483c00d45041c2c040d0a00640008030306110361126001920f0443e40081124099a5207040429841c041805140c00080740d049140c5094855402040d0142c4002d60362141a182d0791410481d503002c0020041e44c04c05d40790b40450214070080c0d8050071184030f0540300565130b01e20381c0d8209414401941080641001044070410744942c1590036652084d1341803e20385000349003400054a9208158165100c1c9400020f20143c18600811482851001580e211342c0c56601d6450503800c4e1080300080b40009001400303001c1c058581100b041c00e600707001d41c60001c0d290052060b500d0801202d0741200c000f5a212440881c0c0090340160508020141640074000350350a01310700c0b0211001d030300702c00307804147c04001260965540e50b00050081c01d0042040f0790b507031040c041f9115005424880c40c00580a101d0101a141402003021981c141d8107070b4039030031440e407015800d031260703003028011624840b11441c50300040e840400060000200170348800d91 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 212448821 1250 212447571 212447597
    0x30c0a120b06041b0f0507080703051b0604020609060901090806010b0a090e0f070507050114040c0503152e1e0e0601020d02070504020f130e0403030b0613030f08040b0a 74
    0x10001c00141c0102c1c0250300d40104c8040002d00780024a00004143c54031003e1010104001c036800d00500c640a80443c000060030b5003090380100003410008a40d0318815000089000c1040e00d41500b15806074021500700a1100d040c5840001000c1a481c141441c094040d01e07000310a10b401c000760442c142d903034800501d0b666000d422254240c02080b0000c00400395141100141b207064001506000c1400008200300b8104842074018884150103800185110714041c10079502098462040398000c3c05081c080000701141c0708202c502c41c90054495000980341d08200c4c3c00309480c440c07081150703049201008110581208503010040c81c00100781c00a03d03003007500c80541d4040140001d41994402101da181e22600412103e040b21400c0f54010b8a903446c8002281030391051104e04078603c081424085400646a1318250040d8020b56041052840140c24040030784a00d50004000060740c1344100006480342c031301038001030306c1106c41e10705003a42d070107480c41c264012a014401203400b400c0006 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 212450071 1250 212448821 212448833
    0x150139080306030f1b1504030602161203020a050f030c1209030d18110d03020708120d050106080103150e0a02060d05070228060e010e1204030b0609010b03011202030c0a12 75
    0x8003422800b1400740a45c00e40c40807070340e2240e821040c005805901d100e1500000162500291b400a50300014199a640314440340c5411998210310120399280b043c1e07040014181c0300340b00303981c043c6045448080c64080350841044560300b008080e03c2c01c07288100003010070304110f01030840c001c80f100c20080d42c40707c0861580405550b5281c1404140d940f00d100a900454014412203e00c0c02047d600e8008504850038200d0406040e90400343d40b9108008032a00280d2842005100304529003604002598070380300e045400c0c200078403000d82089a50180340c01044025030150007441004021204003844a502141351038205401c10348030340b940d80b03080160543d014400d10713649046c0c070361007028a00e00a031140740c0c5149150801900181d50b80d594650040406d600007000d0001c102c044414115803801609070681c02408101d98891502021520710300300401ca082c16121100c04807801c41c0e00f00f500c900c03e0401100005ea1f890321806420002e0354403510302c4080a030220501c0f450203070103035082003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 212451321 1250 212450071 212450083
    0x9030d0914030c010905010509031c0c061a0307180f0908120a05010503060c0c01060521192303090d08130e04020303070f14010e06070815013908030603 67
    0x590b000f40c100c8241411160b038450004400d4510908009845001d60f1000c60316105c10700340d8012029101c2c2010f440d1440e000350140c11054400c49040c4005401101d110030b01050b81d241882d0186e0003110180b15415403505500400c0380c0050001861903542c0341100e040e1200c041056580b94400945803070849410081c1940c06049900700340019490103011a03541d40008080d40124003010541d46000d00e02904040d0042000a061070841c49000b42c01c2103504002c3d51014200340302d00011141c44100d03001409031090f41010460005641a00d10600c18402e440100e941d9400100402c07032a40c0d407000e119421140c0245d09803170300c50721840c1c0c2c0e80054405a07001940381030030900230007005a400200302c07844c0d150b011411103041c50451800041b0181011400c20031942401d1030b11704008400a40c4600c20710380c0365113008543e100d503a0544082c880d0540741c280014500340c460664000101c51141e520000f1003100794281a50440c6198034a003141000c40e4003480000034172520385020010 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 212452571 1250 212451321 212451359
    0x1051e220801140c0d06080f011407020a0305030606030a060b0a0306080d05070f020d0201030617030d18020102100506010e120c040f180b0403020307140a05060f010b0406080c09030d09 81
    0x1c008035106803800700c0310f507a4014012001c488000490158901d0b10340c0001c80186440b034115a4480241010340d03010b440110030b0413000c0c10300c800002e4102c520005803843c286406888640c50342e00c07a4000e215107036000030240350800ea19070ad800500c14001c007005044440c95940e0004045043c0001d103400d1584d0f18000c0000c100c428011000031a450191203602d0f40c0d4100c5a1000300e03521840140c018100380c2d031000081030004103c00c5d82d0584080018160034844031000c0103003040301000c000d280440c00002900681c814803c194651651b0391009411060506000c07900b10649000103201802c1c1e1644552207800c80d0440a03c10f05080c040c0c000d00070103940c001c0c4400b140c021114a10704000101c040d02c0131588a001c541458001d000b00d41e01d00350444140c040107010518a655035030000d500c2158540724040010301c11180d69a1a40d05841d41600000d1034146010012143c206000d03104200f0342500300305003002d030740d001c01091141d146141c07a480441031402d04030351181d80e4a800 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 212453821 1250 212452571 212452573
    0x12150b090307063603080412050c06040303080703020307110f030c1207030c0b070309060501030804060e040e031e0906030a060807080703050703150e0609032502090601051e2208 78
    0x44800900c1584444d029409050711621580740e42242c81114156040d51025105400005012034080000409880558025012941c181e0300003400c0c4811413149202c09000500c40b00003140d00d6a10a400440c2c0014840c900400c2c1b5540c403108550a104061400500d03d40c0700060301c07502d015040c880300c0d0326009140001070a101090300c010f8400c082c0c2000c014017010502d400101a1800303035111444242d0020b03401c001c25a100e10708034501d85e010f4091440030804540d4540c9180c509402106100c0c900840a14104031380750641404540801c0d0b800030408005111081ca6074a42c00c1c080c600c00c00400902141451915401600346891600701038074030b400c00311007400410400900700040f80d030312040040391000c40355444130052411b000e840d1520300031402400383c0200004003419000c05103030124009000f4100d0b04072500301504200a400074800d0001030300540c00340c400b5140c519910328020042e140c21440b411010380c4280124107510b660700c000707030645007840f444540c00791032414 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 212455071 1250 212453821 212453837
    0x509091c1d0909070312021920040902010c06021e0d060608090a030804080a0912030e0a05041e0209030c030303010306060816030809130b0d2d021012150b09030706 72
    0x3c00c08944a4003d0700001c2d2000281d07000300800c2d6407003000310680b81c108a105e42e1240141900c2c0c020460904921802035440c980f035400d0362a0b250521a1480b031030f034140c507500c100c00d482d40c2c3d4540294110348010454085101208944c1c0070a00c00200191080b03640c0010742c25061440c06030103960090404a01c551000322070600207074000c103520340c03c103422090254450004110840746440582c110f052404000e88a180070036030814038030260700e40e0803100410301c15102d80900c011a580c850b088c1c24030716030060200034019200d500510b0010000303000c0ea1440030b45003012070300e103500a078001c48000c0d64421041002c45000d00070721420296420950100301c2c40e54492038054050810b041e48100c64100708040e000285500040d140b06000e80781500301c894906082e1082c040130040320360141c003c0c4010000a02e50b50006d600901d80c01401a02c0707500c8280c3c02100c03290440780c0e00d0031421313644a20b0841d0b80702000102c90001c00065004aa49480031401d05081c02c0312607010005004c0da072 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 212456321 1250 212455071 212455081
    0xf0103020d0308130212030a0215100e0c04030c030c080c1e01180f062102040305121804060306020705010e0d020601060c050a0602030a0c02120a090509091c1d09 71
    0x41c0d03007003209440d0140ba0020b043d0b215400f25543c1c1d0b03004000001d42c008280580090480b2011010b040c04a4058081c0c0e042d2001844510045c0c0e1405c856204c45100d03400f0080c0501c442000c0a10341048a0340805400e00f500c96030745610804958109844d080c0c102d072001c0010240410a1001c00001640c3c41070110303007000401046201c2d040040c0e07050000c00760701030742031901d051200f5000b442400e5844810960b1000c002d40324100d41f00039880e061890200009048201d070080380c084940c000d000300040b20043c201e10031144c01014200a2454210380302410039911805040b028500031600140c2e10402440c1103421105a40c2c0f10b03028580080c1000940b80b40c010840e181104d41d20700b4070b41441d0100b460504d05000700000010b00e40c2c0d1001c42800a0701c0d506500c0041c51700980c7e02201c0030100c0e00a06004540207060440c7e0004200c010103200a06010510366000407130304048507901c0308001170f29407400d00ea0000000005040e41b8201210840c2a041034104810507500b0b80744038204 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 212457571 1250 212456321 212456329
    0x5100302040303140304020f040c050c010b0307030b01140a080a080a0e0108061020160f050a0b19110114060a0b0703020304050607030c020913031202040e06040c050f0a030501030204050f010302 85
    0x94804e068120500400001c0030341d110360314406a803070801007040140090380800a080703a0008d060281142d8a080103000c01800c0000ea402d040e2034000510340c126a10702112030040422041c91980c001e51b604100041c003580030010340000c94842c1d0080340e11111640001003201e43e0450941c2c0c1003107400401c0c4505500c2c0d50044224003103862414803400604072036178400341d40c100c0207140c06c03500c240c02c0741a505034a004000070507111034000d050aa80c1d070740d404012142d0001d014103040d00104000700351130082120070800440381142428a0750602c0401c845007150710110301d000f001c0c10b5040400001c0d01e045d40306a800380803001c000030704045081c0c4001307640f405140160b5008602c0061180b0500d070240314500c0440d90300a04101d441e207030002000b0101541840c04a0108a040542a581c0300711030080d00c0079282c0400c3c000e051a80c03200e0800c0050603811000d42c0c14000c0c20001a0703090a8801c008005040b0b440c1c82c0483c082d40741d0f04c10f2000b1100e0040003480c00010140c0141300590b5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 212458821 1250 212457571 212457587
    0x80c031509040503090d0c090c020f15040321020910050408030d09020a050a0b0d0b040603170d200705071401090302280603140a09050705060d0e010501090605100302040303 76
    0x4800c0d41c80c1215039860f440c01038035500c1030812480e03202c850350100c4810400611001020303140004400d002c0605d0098007130f42d1ba00300102d400e03842d54021b0000720902d85486002030398000d02901d001e11012454140b95071003101a500120300d61600001d040185040003500003845030282d01e0814946494100259228040c000091481c05c1c0c44000755020340d034401001e00701a110040004a8150380c1340c9400410358400c0b001030540c00e0811014031054074217407003040f04998001070801500910050800299801139150340c1c1d0041e500c00c203d99010180788821a402c40e44044441d540d680c050a04c2d41ca000001e5200d0188e80410315001c00190b41d11101c42c1088a50540c1e0b044410180030001c41801c1d1605456803008601091002580c186d264005404032104490003508a8a504400e8001d032100c1601c050495803040c41e0410160404100400c0030b2940b0100010340d445010300001d00f540e000303030b204040c0300b501c40005115515012891004608007814210b10302451030307802a1043d030b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 212460071 1250 212458821 212458861
    0x9121e0e0103110c01020c0d050c0714010c0501060609140603190902010504180c0e060c0c060f0c07030b0601031d0a020402091804061517100c020a080406020d080c03 73
    0x100600c6941d03400394005075060381020a40d280c583d881940454000c0d080000021554803c3c11105908107005408403a101038070310003e071513441d04148070300921031143c400031410000c003040000040b44d000c0c031903540901083d54400402d0b620707041da07d0170038400384d81c059841031030108244500003101100941c81d141900c1408581e0000c0d0380010396a80c01207070701540100404044601d00c5003107660000d0000042a22440304030340b0303002d00348044c0340122148035080b07602281c0c0d42d0415107004405801e881c440005840c0c80c000b8034010745400c1610590040714140070110038044c0e65a0180910014841d05030750505003914000b80ca03070340d034858400340640115400248480c06461701c01d40501030840f0301c4081000c5003030a24000008000f00c9050300c0c4210945100400c8030380e240301d180030304031001d84002c040441480e01e900005203a1070724a0030550ac1007122402c001201e082c00341008041c5600900719a0364045c8001c1c06c115401400180c1c0c90308100100720b080f104400c0855104 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 212461321 1250 212460071 212460077
    0x1422020f1503040309060906050a0507150e070902070501050a05130b1308031504060e270304030506010b0d052a0d0b030105090c040605030109030503061302090402030a09121e 77
    0x15110200400c00300c11000703103454840c00001080000703045c1c0285045045901e20303502c1075001c590714081114217000d00c0c81c581000501c108130070701c0417601c5002c50400c60701c42880c2c0028940002c10a561030401c04d41d1081485680110781300d802d0000030300c84c50380e01c40384049044c4098070380503101483c1002d80c03910043c00b281d44040800c185044215840d407000d076001610710358070704101c2c40340c6c01c0500c0a4442d051043c0d0400d1800300e01420b107021114028124088090b0001403881d042100c1c008441040448032f21061100001244041003024001e20b5051809692051000c1c03110707013900c200509a20072811001140255110800c52843d012440c41040342e444000e8141000090203d10309255410341c00c00007800002c010118401c03c1a0354100d40070081ca83e80d0320107245c26a540c0c208041d0102c0e40500c0000d485081c684c1100c080c0c1d001030400149443e0034500028101c0c0c0050b14245c81803a500c422141c100302d86104001b00d0350605041c44464010303403807140804568141580010 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 212462571 1250 212461321 212461339
    0xc0a030c061407390303140906130609061412060d050c04050f01050102010e01140109092402070b090109050604080a03060308070b0f010f0b04060e0121142202 70
    0x10303840b0040030303204115441048003841e183e130350340c105010052003007540f0b1980082d480d821607013603c1051501c0c2200d0b4035440700c041e501300c1d80391140c2e403641099503a00e4004504114525580607024002009401d050b01c80c480e0071800d00c0401444811000030b0000070120401420070f4800751940c92130fa0000048035682c1e9100d01610700b5900706114000e105810909100502450a4400e02020705807642a402000b40902d22214136099404020078049018903c0005100410380c58001824140c0100a80c030403c1c861903a195441746404800c81001a0380855600b0410499520341508200720303c0c000d0010a02980f103942c3c441e0806080101405800107240d2031250103a0045e800440e005281c0b143c6408180c1022031100000722940042c00007030340d00101c1e542004c1d82070041520780400010f828181852401d035903451456400d20b041c802110107064103000d0241000c04450150080420318100301e413030fa2860b8040107050040c010310928000b296841c10b1444125a60b030f011200610 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 212463821 1250 212462571 212462597
    0x2030405040c03061e0819201807030903020d050f09011206091107020f2e0915030b03010516140304060204090c1706091306050a110d0e0c0a030c06 65
    0x11300c50b66105c804420850440100c28002d07020200301201c2d030420070b0ba080108010000c0d58680c4c100a001060f041c88031040c1940301c0030409601010840c00307441c051082a00030358400c0c91000071503020001075112104032007013690520010140302210700b019410032249200389101805540304441c100422000c800310480555080a0001c01000b8001c001202c2c03991080e04c95684a000140e000b00030620b0000c4543c10b00313151146c030210080a002c1900c042803221481c20b5901070840b081000843c02e808200d0281c6030304038a00d0f800d025100050612080024142580c000401c800400403000300f0000c5281c0c1c0104110104441d401142542e0f1f5455141004c000d00407a00008100752500c1411344500360001041d502c0b00c3d044e154042c54036a182020802400b8045450100c1760003116a0440080d041d9000641c0104081e640810501110810500641c11808503060300685883e00c0c100c030200140913640e04860155940c070f002ca4110344480326881c1ba1482503500704071079403429070 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 212465071 1250 212463821 212463827
    0x10207140d05010b102c0906010c080c150105040e01061a07030207180b030f01020309030d0209040902031006060e1e01050313060204081e03070f0b10030506090304090510030302030405040c 83
    0xc4009100240440000e00354640000c000044031060940d5070b40c0ba41000b01c181200300c0c181c1030700c401d20080c807c0703000d0ba45007001102c0c18484d1480403160a1014844915149020f100010305511242102d00c1c0075071600f0208405d5540312011031600d43d141c0942031250385440c854240e000740e641c124850f940d103410f10b8100c3c0b61050940c0b00c0b04444404014440307000700180c000344a00348049040360803e006180d581d500302d10042c1c071410820b0b4020408400001199005010300d400c0c010000a000403958000c80d0a000103a402c03075014643c0c58100744104c1d03401c80380c04c2d1041fa009880f2001e04209207860032100c0714035440c005050000c08400500c48c810008130400382d5540c0190103644035607032420441ea8808020003400d89001700e215640b008060000151840c00b0f401000c4410741203c180c5401e642a030b00a04a001c044112480100c0810000c10260f4012980078004684d950b10740104d0008a4502409400d0703003c0f07400c2c0c01000030a1b40002070700c1c10b807032044500040d10450700c0700035 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 212466321 1250 212465071 212465081
    0x316030e15270309031e0c010c1112060603010e0a17072604090501120f0212030405120307060c0207030203032205041a04061a120a090605090f0705010207140d0501 72
    0x146504090740101c050442c0001c0007070030000409404880790340021941b10118403620b0007250705241e03c0100748445a40c4212522040c1a004a5681040c161200c020440b560103048004446a001c4070502100c2e040c24842e005040c1c183c08060940005180d5511035824848524004901c0001c83c40d2001c0c81800e180c1d036015114000221310300c0200104046c034990b0802d11900e100300d49404000140391650307501c40c03a140d5900282c020708400495080102e416a03101175581c0900c8188004285500c6020514030300090700b40046880c5c0c051440d00c041929030de42e079130f0011500002c3c400c0005840c00001c0c1c6a0f5000c00b07210b42c40740c80245005c0300f240f04100e9840b41e54020304010b002d40300550407c0300d008030b4400c1a00c00380041501c5217600f1081a0b0070608017502d880c1e00708051006007031003004c0180c11204070400810048915110042903a8050b02c400c5403680002d0283c085400c0c04008000040200380040c102081c070344040300c04808210b21a43d4060020440003104202007076100c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 212467571 1250 212466321 212466361
    0x70b06060c0715090f0e0a240b0711040c020307020d050a080a120c090506041502010213170609010b091b160507090617060402150c03030106050316030e15 68
    0x101e031012a43c031144002d081000000c9600403030a500800328040c1105074000081d92000812010203451b00c1c41c0400c000d0549001c400c10b240c020803030048c2060000320120b0010002400c0094880205061145403420340811071403040b4a440c440c60390b441e030003205807181181c0444034a0301001082c180103091076036000740207207198000903090740b8050700020340302c01001680c0001c0000240980040d00c580c0c24a0140c1580101c5c10301c02006403030100303069407060025600c000360614090708103900c07a007441c80d0040c40c2e440f41c4131000020b03c100100b200960000845000344550110400030a0a912000e0301e400f2a07144c88182e00003000132000d0445000e40441d03d161806440345041194071a0940d0248074030017800c082c00011100088100c1c80300c0585610040c00310b170344a035820407000c0c030f10406001940a0043c844002201ca003071001e5030003002c460720b8075079076864001c2e1340a01c1c0181c56020700303003414940040b800e030b03401c1d0010300001e00352884080c0c4200341e2184a156040e030180300035 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 212468821 1250 212467571 212467573
    0x6211112010c05030411090f040b09150414010b151804110307020709060f08031b0715020f07090204031a060f03030d0b1201020712050a0c0209041a090111070b06060c 73
    0x94080c2480381d014004510403402100c07400c040010b141c01f0000312101c1607400c400d50700c1420020801103217101c0c00194002403004101c0f000200c1c1461201c694071400c5030203850b011403104150050031804c0c0203154050f002120074691000b00c4014029447c081d01c0c4141801941c10100307030300d10352503a50285001d82201c80c11552649040c0a0095641c942805280c811608046000462604401d00d810954907080b02079800d20003050b0026118540100c03000c542c45c4615480000d0358030440705500425030385603002e04541f8818490a03071a240181d8000000244104000c001142c442c02041c80031a00000c148100da40b18180095840c103103080c2c5240d80342c000011302102c20032042c2d10040410b401544c00f484c12201c0055031a01301c0c021400090302250f01200d070307284060310410003005c601d0001d0820f490107280c0e0fa00440c51842017154104c8040300c2d64070191006c0c10114407000d0b032000084001340048034284100b103001d8000c00344000c280c2411100462895915141035034000c400040c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 212470071 1250 212468821 212468831
    0x40c1a0a0507080f12180303090a06020d1d03070c0e0106120c020a1403070201020f012f1e0c061b0f090a0302030d02010203071b020109030305220b0903010621111201 73
    0x991540203174030309440810084488041e103070710000001c002e89100d50740c50300160a40501944495020750301c029040340303907190303101c03c040c440103100300d08120b840d40d00c00021602c8820514150b0403200c403075000140c00400300d4004200c2154894120200d250308080d01158160341004c2c00c0e0702c3c161501c00010f241950b4030341c54510507400000904a0103000f42e088920610508100d2807c0b56000060380c00c2c501944581c3d02040425450390b00c511030412001c00f45801008410104520030101c05030402207c000f0f4004490641001182d401004400070440c2400c41312444903001d2196405002c0184e202061051040d0307183d29000c0c00a40d0007509036102c00fa107068000f0700035030003220340c0790101e200c2140171455010070003d44860181e060711000d200c1811030714155000e0700090b414111141202c8008922882c10803040c400030401c600d2616122000301c8105030a64005821042046040307036039100410303101c1c05c455a20a6000b6849003040390028000c110242604c52000049600340 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 212471321 1250 212470071 212470087
    0x3070507051005010312020c0105030c030a0903020a0f0b151027080f06010e0709030b06041a030a0b15010302120a05090309061611061c05060f100206040c1a0a0507080f 74
    0xf600c2d06c108050165400e0f904690441030066a59001c1601c01e11220a800d00c005401c1041a90004880310300a00442e0a0f0701b1f0303250f0f10490350b4000b01a00300c41c4400c4100c14032014100c00e448004a40708100e51803404d8404061f00241024000241448408030b404080c108035800848400098003220301910707460303020006c841c1c3d90f41d4028132840100700110000921400c1c81000c902040c1d9900010512440d19400200006032025026440481c00300c607a801c555550100410030030f480c0700e0740202050b49040e0103a0031000381c1c18034400e0f040c980100301d400240d03846100304a41c00441008009040c1e291184d41d58514082c184035540c100c40002540c50901149580d200c040d540710b51140d6407076000807014411036002e10580390340700e42c03200e02140040c45016000760ba80320001400e000c0c0030448040004081000104021f00560000400e00c404c3c00718801900001c2d041018250780368004801c8100f005100e2035070020704001c0041000340c2005408001c43d5070070341e0440001500e4000b1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 212472571 1250 212471321 212471333
    0x11070303090c0605040f0b030603031c0c11012c030f0408060907120b010b0703030b04060f0e1302030c010503190212091501030201021f0f0f0504050d080408030705070510050103 78
    0x10700c1c00545050718031080004440303100d03004407010740c3c0607140f21a41d024a0140044150780014042503030500003480180c620400b02c0c408500001d0080c42c0c0425004030340380014041c03120720210680d2a90501e0a12641640d95001c6903065100c2c507801c280e45022040d00c900e045000d80c1d40000281c541c00100001e82c0032002a8160050554000380c5051503a80c0d8560502c2944d0041c0081458801c5401041b85824010140c044280079050204001140000040803292207420000c19035099030b1050050b4201402029440101440702401c80c14a0707800007a500d08180500a040000001c001244105819101c0c04101c41480d402e544640c62504018000142169407220b544034210744002c6041101906074107c07901a00548104414000203446108028140703c501070340300d0403c421039101c00e00c0f034284278501d0914001038508240c503100c0d08007181d031200402009072040511020404d00c6049075040415818071039500e001c3d51401c64140201290101d1603103181c0000003080c000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 212473821 1250 212472571 212472581
    0x9070311160c180509071d161110020414010504080c0f011101090f11011809051e0a05180604080d0506040608010c0e27040f1b1202090a1a040f11070303 67
    0x80e0b490a403000c00351a0802100001c0c80301d104030365030803500d1008c42c08201003003001001288962030301100510001251501c3c0c10900c0d554440d0322940081e08010500c4030050300881c840c02468440d24140c0f90100c255a81c2d10303014003081c42110364261030306081e0300030002841c0da1107040009011a54407410905000d5840b400305440c1c10b001a42c4543c4903600c2090205460030070f20044030500c07070402d2036040c01040c0040114a00c404c00b004031503016981800d0a80c415550310402003902e01d018030743c00b04802001d08441d00c040d070201092100052460094a031a450040381c00616560391200040241c030161b40b00c00815442c21070b40c204500e130b0050200c2400807040d954416040004804a24020402045100040400d0f40400c0000340541070f50221180501043d9007210502941210300000d941c0c82100316409021600c811414a1038442da407203948410b041101d4010200d9080360b000250700c0d003910a55540d602440c214150741c0c41003880c0009100502c0d12130581d40341c0070300201 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 212475071 1250 212473821 212473831
    0x1507090e040c06030b06030609070c030504080a0b010503010b1804081c0218011d01090b070c1e0305010f051003140a06180311070302030304060c030306050301020f070209070311160c1805 82
    0x1303402d1201c1e0190900700720b012a1300a41010304241d04580d0f1300042100c0c03500c8010421805c0040402000513003040c2004080c42140c000c00803031005500d40b40c2014215141380000c0f83c001c2250803961002d00312600314050f802078111a0807651684008032601c0304141d4801100c545d0382c4003041c030303000308a00107140300f0f550742c820b07202d901d00072406d0000d80d80c84081604009000802595042c001c0994880180c12420f100d074a0080e004d130b448100494105410f500c004008030fa80f000c041052120900076101496a0240e00b04080d050103242c0c0354807410700c1d001c080c144005c1c100074104055401c001e5812616004002000304020885018618040590098000407600c018600314000701060300c404407940100114645844c0420960b850103548100750141030703540310002003c3e20b00380002d25450700c0d40c2c101c65a070307102c2620400c0041d480203482002014a00f624180d1140c41c3c04007244c0580100c540031110700074440c680803401c8601e0750462607020013030a01e400d030240020340046001d0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 212476321 1250 212475071 212475077
    0x31002040501080f010e0a1a04051509070f0f0516060c09141203040e06010516051005070302090904060e0a24140f0402060a0c0807030f031a031507090e040c06 70
    0x2130b89400c1403d4405480a00070b44882c2110440840c1c3c500c0c4050f8041c11001040f003503520348194485001400f140d8048510040000c000040b401440c603180600c45d40c009090300704088900d1103840002d141d0100d8207103d0041c40b07800100302d1280c86d001c04030443c20355030200c0e090061080d038000c0146203080d070f0300c22543c0ca42800610080c0d94640a189801423400c1c000003982405d2400345007003682040070702980e0500001700800f10303030801c0000c6100c0340a03000306d00404164040340c0c1c0020031078030020400804c0610500c03951800b6550504a540c102d6081080801e84402c91500982404001c2500030102500f007000c180d000302c15030b2000c80c00002030f8101001080c002030310703111146004441d010491a040d5000800510b4800003424a4010501d4112802403e603941c52156034045001074002c01c4001c90940689a0301d402802c44021008240620203500300700400e44c2c440307408040d00090f000403400116140d10606400b0024011901910018241400c10140c16130543c0202000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 212477571 1250 212476321 212476337
    0x40e0c01110d0206240a032001030506010c0b07051c1a0301021606020310050402030103060207060e07180e0c04020a050d060f0302060403140718060602071d0705130302031002040501 80
    0x1038090210301c08640a500342c028044941e180200700d09400d01d03c0c14800018030400c0b03100c2105803a03032281b2002840c1b1070030610b12014529220103001503003e505c480c0c101820b00d000c00c112640d104180c00c80461340b00f46031101c01d4507405415102c901070341500b0000e03c02060052209040260010103148900300c0300f041602c06002d05050030b03031207440303400c0a14013145038400000410790f5004540c00300341e20f07020b0002691a20001000c1c0c2e0b000307900903608150041442824084588203074041d40d02000010044e40d4078204e584e1665140201043c10004da4440803000000303001d126070515044010400c40d56442c20307040151140d00201d84103184540f07045070106802d0040100001501e03001448281010302e1541c1d0006074280d180259a9540540f0000141008518200050781200841c010071a1400c0400080c9000c01e10303407001c283d1101c0040e148003540b22607505a03410500c28030301a03698015125500d011140c0b6540300075054403d00d5505002648036034054001d440003680c80d40c01d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 212478821 1250 212477571 212477597
    0x29090105040c05120a06030501021201170601180f06090c08010f06030b01081303110703060506181314071e060807030c0f0807120504080a02010c08090703021e040e0c01 74
    0x1110111400800464000c00144d0509092405019400040f00320089070264482d5074046c00d82e00300904038440c0c4005d00c1c0040c0000d1078800030510340c041450b0010404c640c5891801d5400d286c510aa0640300d030368545020300606038903080000940783c20081881801e107074440040446009124a150b84d40c03c5050100c0c0f0310f44203004e0f140c0c20000580d00e16000351030780c0000d6020300036500310803410700005100e1891603640520404c801540101310008803480e003401400b034071040c034003010705d401000c000412002303108582145054070340160000c4131306448503805074a010241d4001100e0050814070100c617890219000c0c100b50341e902e6540d4a425200d89400382c042e01c3e8086a40720105801201e0701015900c241c02c0ba6601c1032052824801141c0c041e851041102c000342d50070b564140000030000151902401014145038003854030b4412403030040d003429220040d80c00003c2c0300303003002c80f40012031140000e0340781c24080b0003c0007005038490380012250b079150b84d9511a4082008010500 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 212480071 1250 212478821 212478829
    0x50a02040516020a021903060f1d0102070206040b0f0f0d0f0c0e0d060c09260606030c06030c030a0609020c2401050607030e0d0f0b0108060a050408090f0429090105 72
    0x240c2c2500100f03040841e81e800c000080310f50081c0c1c68138038942100000b001c01c03501e010351034400d5220791000803220120021003060f981c40c40d0242200d41e00401090006881d81d10864044444d40c1445a444d440d00d88107004203480b03404100301002c0f1002c40c501400c41d41c40d40c03010021a000d031104204501400400f900c640e48000d010a500400404518000c181281c01c4264240c51301e1424251040d260490100f40c03184c41280074407216100c000d0498441c2c020020240c1060003140200714030341e501000035900380f1004001864004021011038180201608110b0140122440075502c0d40c1580e6400e0340d441d605032035102d5402054140c41c005850041d0000b030b05860300500414500039103914207441804084840540000c13180398114042124505100d1005100344800c07181c1c1e515003441540750140c0175004240300c0f403400090100141c00d031821240c1c15842542c00ca000344140c900000c0080c00c182a9908007041e581c65444210340f00c0e80e2000040500c1280d1441c410398840c4144 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 212481321 1250 212480071 212480101
    0x20c0f0409480e06030a0c0f05030f031306050c0a050d030b030c010c031e0c0203060f0412020606030a020904110a080304050a0b07150e1608150114090f070302070f050a020405 77
    0x1010120401405101404110f502d40b50b0200300038040320800f444030b50710000d006e081a400104d45050008081c41146014403880c920901c0b5800110305002000204411901c858442c401c01c2c0170001030201c09004c024882100380580103000c0d918440400749014000c1c11079984a1486409402c0042c11a980076009001c800c0384c01d55540340322443c0e00301058000c1042042d012041c810071003540001a98100044e41c81841d10300c2015882d03080c42d24040c468030301442044000c4d0741025040001544000910301c211030b4045406198036142d44c200300b888160031200c100c0c0c0100e45c03800c01040c0310030004020700c1112025070b4260f0b005680e40b4402482405165401007000c1e0111000707498451050700400741c241206020341e174030791174160302818240c003190380081c0c0c072900800c1c00c04101c0100490058010a1441c1c041c205000034400003d800400081280a2800072a008541c8003031099041d5125076500129003500300107181081692a10751100491082d8200400180b03003d9080c054 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 212482571 1250 212481321 212481443
    0xc01110a0b0601050309072705010e040317100509090c0a0803040b040b0a091d04051903121a040204140a0f081903030f051602070504020406020c0f0409 67
    0x15907142a11054011540c0f0f50020b059003005110740b01c00030a0812843c40c004044c404020b0f408420359000c01681820385105a00c1061820110010030000c29000051a410a07a641e407001019035a00c03140141c0310003181c0c00407604078004c7c100300040090300045000d031403102159002b05050380c40d054256684a240904140e0b0801440200b00000308440504055015424505261500c076441482048142503030f207006400b68109000500074280213400d0502041c1401000112041e180075140c1c1241c24a954916aa2034002c13001405010f1200301080100800070b6680c1c40da1650303074000c210b280e440124480e202a4400182c0c4502c23440002040312040c102030495a1802c130002130f102c99841e14203500b41512040d018215040d24840d081c03207580c0450050300307610462800240703804515000607004510401052101a800140240003a40219a125140c0c407100c0c0224014002d400750003030a0346001c03100c14004106142180114168528142d441c0c4118840c01c05419681100c4c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 212483821 1250 212482571 212482583
    0x608040605091911060705010c1707091a03070905030d020109050606060405010e121501030b04050c030c130b01110105161b0305030103020d1b06121410050904140706020c01110a 78
    0x4401400a42c2c8013603000c03911400105903900f48009615100d080d41e1071964408000380b10070240c8240f01c00b410034001e4201c881441c0c2480c0e02400c0c0144070354200c541101ea803202001c0800015012403151550b98060000581502c0041c40e240b94080d002e04102e2100f15214000c150008100e802c040301600d040300d40503507500c0350100195081c484501d03483e0404491a0190740040815514070011003402144240c02c02c0c49145400e060050801c91280384c0e0030300c203400680d408182076a840a140310400954540011103544160050707070341480110102d1401e500f40720402540f00c1600c10280c0304034a072601d501480c10400181d4200c1502038010007008118284018000f508015090076041c038862250301d0009130b07101da00310705225000d50210f400645142401c004010f014061481503448550342030540d4103100001104101e41800b90a002d080c0d100002001c0c80b040f80040c40e0080a040c0c20f40e0180340e01e8000083d110096200400e0208440c0c9210031103800001a45c4151260490 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 212485071 1250 212483821 212483863
    0x7020d0206100512030f0a0509010305130209270613020108070206010e22080c010b010e01050c0a0f110a060e1f120504060f14060405060a030f0f0813060804060509 72
    0xb60404c200b4505040310030701035100600118880e0070100c07000b8401c5000c1a15080c3c1c03100c800c2000141656401400710406000740d241c424016290b03000001c0e04840140d101e40c0840e0f1020b130b01400600010400d0840074440c02080c492164040e202545002e4000e98402c6041d58071518260ba4962082c40ac9035650400c078000500411004d82d4040100660b125240940751a1920b403450550000280072103140d5607000c0c5203010b981c0204101d09a16030a00342780f42001c1900b1041503c42c1150080030f000c0b10717180940c4004015880c090700c182c01e0740003400403050a403508001032170800b1111900e401490385000300e101c00d05544d441002c1c070b850030307580c3c0c8a0a21110300d40007000d011301030800c5511545412002019040c1350190b003100c4100c001020880740340c40070800c0152400580080e0007660885414400704030388210782d030000c1d42c00500c0050000824074109405104500380342d103415204042c0825016441401c0303602035030040e8020302498440020080d00c415081030103604040c612 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 212486321 1250 212485071 212485079
    0x9030604030c0f08040815010f0f060e0319050f0d03090206090409110901060e01120b06030f07090b0f0309010b042a0c05010f05070f030c0507030e0409060606020607020d020610 78
    0x500d03242c030a59842103c41d010180c0c4603544031136243d0055001103116400150a0b854102a01c4401c1d600401b941d011141c142c82c0760141200c034005850156504204500f9070303072582a03c0070400141c03034500c003026403103031009581481915403052400b003039a14020071031007508283c4280079982e066500101481c1c98200c1c880d08200080015200485000112a441603500d41d50400114000c00064940b145108a44800104071240b00d08541c0d50181c501880000b040c5c6645080c1c03517005031a0705e0114a10703110f00c41d082d103491100358441000140700040501101030f02201550003001060000d1181c04030001c10042510004680c04040c9861900c3c0d0b8074020249030844074001740c2d03a003403008a43e0590f40f03a0310b0030b5404601c3e9202d009500c400034455000e503c07500c9110728011a10741003140c4601007200929602c0340d07001c064108400012904900c0c0c2d038541c8000a241e9004a042010683d184400380d21202c089442902500411410030800d03070011425070300c6007454903001c1c2091820 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 212487571 1250 212486321 212486327
    0x40f021807080a05040f020d0b01140a030b070516060f02040501090608091209270417032206060905041104050c0a02071502011805030423030c04090302010b06040b1306050903060403 80
    0x10820b854a1642c403401031b001d40c513074450120089000311a2050780390b0500b2001607010780e040c102c031401000600010008100c941104581241491804990358840c3c0490f0700410f8091480240000c0e21701001c2c152440750507801001150420703201c2c040c10541e14041900c2181c4108c0ba441141e42040e07020301000ca03d200300034614080c004202c0c482d280c0e010719000e64a103847c0c24581d0848000c00f0103020030f2100c24800c044403501816400c91443c0380240320a920000c59003010085d1045044000c810000180c001d40c003e882c01c48020415441c0500302180354681c1c041d40240290300e0400860b01006900c011100e02c3e84441c0c00902e4413a150080c281ca100040c15070010865596080c01c0581c000d9107000340c860f413401107000310385890504004244401c2440710100540f44586184403ca03280812010300c414811540002c0351111820140e003d00801501150320440002d00814045074980140144c60100d007416031420703071945015075171445038031042a41540020700040000348 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 212488821 1250 212487571 212487581
    0x6080307060906230a0b030313030b040c1703030601030c09050a0b130b03010807031217040803060d0b0a06080708030a021509030f030403050c15060a060521040f021807080a 76
    0x100c61040050b00000807132854031450f902c43c01c08810150f8450603c1a0b4050a00594020410031005545010000c1215000e0ba40051100500080303007100014140f000e1501200c1c02800c111844c008031960f4000c00c642c4a0b4002c40e0114082813900000005161140c0d40c1482076480c060668800c00e4286640c448031a04030320311a04550110032008a150003019010314028840b10380288260340c19480c4c400850721120000604001c00c003280c14000030074010240ea00036030050f0490750f8940300e480111784441080742e005041c0e03a24041c180f01260000c2c0d03100504892100301505d042c3d42d1540c2c1c000d0785910425514000507030042009402000b902d00c4e40b41e4102c0310440c01c80340b801000d80e403100d18903082140e080d4040341020581c91010385051190b61003410803603d24a400b4540070002030350001c102c0c02100e013001004070780e58080d0454071401c018540d40030000718505103060b143c200d4034200486403c1303010390010300521140c845443c200302d014544586410b40166551426000100 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 212490071 1250 212488821 212488823
    0x1e0106050c0111040f030c09020f09060918010303020d140c0c06090a08061302090c0901120c0c0204050405030304050708031305101223070f020c04050402030f03040902040e0604060803070609 84
    0x2560714040d040c1c28000c00f00042000340b42d0002100d00043c41c40c1403d4a084800e640108121401008240d031003514403001c445410000f224019290311241010420061a450712502d411403190700202c2411f40004506040b500982c0e140f01640e81e8a501c0501d07940180c0140c251954021401c2d8210303071070b008000e01022440640201c58081e07503806a00d1400c0c00513601d0400007911315603080d065040005074540e00a9029030070501d4040b042c00020300402c029010020080d50314041522018807445030001d04640081050006e4107090801d16181e610681e0b040300e55224803040007511050102c256460711407040002c43c0700383c0c504000d200d00c1e81d034179030005000c110300c074130301c02c03812030340c4c1d8030508111140d40e5504e0008810300444045204c50041c14503414030855500d00f41c812540060140c840e00e4064070041640d445a202192415200220403401404042030101e103d5809a02a0007250040000d800d00341d21080140002c0710940d025403105500204000070202d4140e070064000306d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 212491321 1250 212490071 212490073
    0x6070f061a0603040b150117072307031713030903080c010603060c05180a0803090415090905030c0105060906010c060e0705060316030e0309010c170403080f070b1e0106050c 76
    0x107000c1100090b00991045808a0b600c01442060180640401103540301852080c00e01a4880010301c0100e01c1a400c02801001001295200740440e410b901d100007600c051121040340d04c58486d454080c1109030340c40760140744450280300146108071032415021169406880e07040c60281962a0704140390300c800040a425900d52000000192441c0f040044840050b5201030b04c40b200b14040b050810030010409100341c1000308180f145203004806c4400b020421640090103010003d2603c403c026141d101030750152a201070300c424404040700409644004030001c010740d55031103040000041054449074005118451400c0c00184030b944220003044072402280c000b50341d544002903480c0d01c01c54000d02c0402608002644444d01802000c3d11019003d010314146400c5000080000760560f40240120000c030000601004a11089030055900004581d944061288070403106901c00d0100321a08803640c0b00007a0326103010b8149003441c400380060009030780d1810740112000e4019400d40c2c1f140d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 212492571 1250 212491321 212491361
    0x3060d03170f0105090901140c090f030f0d081006050a111c020c0411191b06020d02180609010215090f0f01060e1f121703130b0606070f06 61
    0x2254505001c14410280202c00705580c3d810502408000384003d4061030060781444010501c4180000720f841e80502e0081e490750f1034045440000d030807451715589058140c003c0c070000c20742484001c81c00b0ba4203503041307440c3c000068881290050012442e8403481e000104c0521504450f07a00c252000c650300e01400302200e10700802805031200c0144189035210150344004030001d164100303405103504c0010b40b20721441c144183d2841400c40c50081301c180608025444208008072811480714004058120008649032100d50f034600c0000d600910444c58800c808240d444440d01c1c0c40c404032400703076006a01030314052018100703da46558011700b852091f03000f0040032405001042003d54503c0c0301c41400400c00502c0c100940729060b0b0060502809031074101d001e00101144007032080115022410050004541810500e0039201107001c04c180201e000010300030300c0000c258214042c0c1d4003450f164051a1595020803500348600341006001c0d41d1030103144000708880ea800616080886140550 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 212493821 1250 212492571 212492597
    0x1107030204020d09050105090105010302030d0306050102250f0b03011a0c0d0309050708101e05010501051204110405070e030f0105070e04090204020c01090f060b0108100e0a0b0613030b0a020f03060d03 88
    0x825504102d40402c07d40e034ad00c0c4010415031404002d201d40c0d140c15030500300b000328140f000007915120515a41d1004d05661081d00140014a2407000300130101e410001070b40644420702c5607850390089c49880c007540450301102c10b40d251080300300c80000080c400107041c0a40020b01c00c2d0040c042c600341c20b80d028090444000344603070040c04501003003c0d2400700019411000101d4040c20380d420300080c103801c0d251000500159800c401140e4081850700d4111800382d0f520710781203540c282106c09044c0c1060414042c442c1d4130350000c2420080d07403400c43c140c480b904659010b00c0e08907a030469904002a2180d4a07910700c604107a0303c05001c0c0c900251002d807804201c404001c3c02d407203030b80c203040703805a15425070745050040390310554144030310929008690b030030543c03801160213080340100201c402941c804a180303203200d60721000c42150054101900d40d02c0301c2444a0603c10700f403000350748400c2000c00213448454140308551103a00c004036501d0440e182e000a00840d24040d203021401c2c001c0c40742d1101 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 212495071 1250 212493821 212493823
    0x51012050a0209040f050108030a0c0c0807030305040303112107030c0206130509090705010c03050a03090c06030203090f03250c17030301060e03010203040b24270105011107030204020d0905 83
    0x1601c101400c400141e0744070796000c148801c9810220040050b140b81030f0060140f800040102c50004440d86442d03072032015075092120a0059640c8100034034400c0f04000410143c1000240c02124041c4c6c54841aa5a51040e41c0352101d401e010b214075241816240e0b000f103a0782c0e42002e4844540039291031700e05540c0d00d03404290141c1c0130030400680750140f094100150326107003c2c403682c450111b401518034285000006024819001c5008081c0300020410340d02007442540122a940d4204603001c078120f9543e04041d000350b205490188150164110f01d4004100010072114480c00380c81d0005d04003911841c0d0110318200114040711146000803000910072511100401c030210550b002d1a80c9504d0b110000d407004210304c412600907401403081101240744114501e42c812207150f4002072490149c0030031082c0810704200607134003880340c4032214000304d012400f540581020402ca4000c50740c9a1005480c41f1290103071220031035008950074801401c10f50003401c9810301d00701000c036160344183e07101 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 212496321 1250 212495071 212495081
    0xc060721050f1623071106030a150807030c170708060108030d0b04090807120504120f0614090a110301020424020c06030c0708030903091207060210020a09051012 71
    0x244412541018000940220300c01c035a084083c60400c0c0190103d104071401805a540d91590182d03040400d4582c00d00901880350300900b100200101c2d1b80745080d80030070700200080c4003405e0318403900d8076001c1407040b80015a03074245c940041c02d1b11252854480484041c2c010003244201c203028100000800c40d50810900340a05501030140d6102c80003610100119141c05105610940c1400484070115200e00200c1d2607003034204541408150000d081a1210300c15a4405088201984251010f110203d4480d1642c1441001c05004e90340c5c0d095940c0e081d252090b40c074034003180c03c40300341e0f035000070280c40703080782003003c080c001604041c0c2d41c062500120600e05c00a442c609540052103400320782c1886480e00c0040101c81702e508604041d1508086800703913007002042c61b84000080b611140d403c1065400a0b2402031446100005014a45851368410b20500016101b14031003407462100e14000c0e2100728038503641e950300c000d2800c8204100c0e05164030102040c4048010504012010f40c014 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 212497571 1250 212496321 212496331
    0x20310150306200d020c010912030b09090d0f050a030e07090204150c0c051203040e01030c080d03050403020d0e1206010608060112090809060717120118020c06072105 73
    0xd400840d495824108181d40541c4010354141840e03401d12254604440c0540321502e240c4800140ca802251215034014000c001000e07104072003103c5e5240d401580358100c84903c240a4843c0c840c2501c0740842c1d6036944a4141c44e00c404101e0305004081d030340340b20b0400b4240070398182ca00807079030114800b03c0d40c1c1040c0203a0040070513641c0000b02032020003114030602c0d84101d85482c02800d10101516860109011801aa44600b10080f04074214003410404e40c0c01402d0565240c143c0d030350b501d11301602914001e00c500c18180c010684806030036070103803103175174812509070f0080d042c5500c20f6078048522103500100b0640c8a111140c2c80d840c5c02d281081101d000e0b0409031034006903400d0107000074040303138520400d1420050030107443c500010032800c2512620842544c555480307800614022034104d07040c8061520030364001c5032403805159041070702c504a5028181c0c40f0280f81e80903102205a209a03001c650ba1b5500c510041403240340f0030510296803c200400080e80e4070540c0d00640141c41c01920 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 212498821 1250 212497571 212497601
    0x30206060406050d0c0302090a0e0717010c05040f0b030402061626210705160f020913020607020d15060306090c0503010c120203040213061503050c09030a060207020310 74
    0x104000c0c00d0700305442140c02501048400c164512a6556070014084081c000240914204004280d94a50540150401210010a0700c1191342c0385d4039410610030600e400c0c41c0702c0c0d41c02c0414079144680681e0494003a550b5103040e154000d030800c40304c0402984054403c91b00030800b040003500c1e44070184c8800048600c034580455907402c070b9151032035881c0700075007440800203010480440c101103a403a410810f8a90720f41c1d0105195200c0f0790a80305400b44044849404120404e81d00400c01007424558119100b200c2d2403c3e43d80340c420f8030702d2112040300802034208104004400140c03034a94440e080c0c99101d6028590702400a1440d401513842c0c0b50302c11211691035004031030402c441c807a02c610150005a00821185080c00030050001c1021660040d4131070307001002c01e0135501c900601c024640e100c41c409100c00c59031110b6081a104040e11001c0000b0b1409012804a100110841c2d20303540c0300400600494000f81c540400039800f03c40c2c1241c1c10300c20340c000c4440d409070078003418611484441c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 212500071 1250 212498821 212498833
    0x703021815160507030b01030503120a023406060f0303030b0306070f14070204050c04060e010c030203090f040204050405040305070201022b05030612011e0b06040f0608041e0302 78
    0x8900c03040380c040428441c070180c4040800503007010080d034462002d001c0142c8058042800c045081604030340019196081c0712001009004c0300000605001540c841607074030030790301c4041d02e004a01400514800324000d4074100d41c203008000c00e1801c0c041170ba00d41c80050022442d59414100c40141c0c4c000011780c200c1240410500d5014412080702400981c0036024511306004010600440c14000c0d405100c203051041d05985540016504c140b94007038810403050402854036249608544540030000d03606050240c140d502c2643c0c10f0041a6064004600b09440003040056241ca447d841582244e400e01c03002813a941d0320700803680110f00a80315180e4800c510300009050004e0746041c501040c10403820780e199041c002d000d4840300410391401c81d40701c6d110070300018010940ca582c7c1051039820402c0300300c0508015030000038290070703841d01007002030760361024032025020310321800d44050386580003002800c0c00758006a500038854005401045460400010b141c0300700e44040e00180d00003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 212501321 1250 212500071 212500087
    0x100203120a0b19210510050c04050f010512040803090a060f02040f0e041101030b01031d010b0f0d150c0e060301030303152111030c030d0810060e01140906090603070302 74
    0x4484020700803840f00c1d286424500b4145040c0701c04a650401003c241101d00ca6001480340a0150030074091858a040c0810304110440e055160030500a5074858918668042180e60151044401c403c41c02000110150341f1506c0f0b800704c40c0c0008004901c1e40c000d1018040001e17402d407080f0030907031035521070050f200da05020a951161405e9006444038604200c2484081600c0c1101942a01400d01c0c010034081700c42e10048002e41044010b844500350311401c101c1607110306401120f0407907400c2c0c504816000000040200d030010030003010f010000c010710401005040c40c2c104421400c428180100b1482c9500c02042c1668000d90007a000656248000d400d08040303407403054010440f442d6040e50046241d02d070b981e518400404002e0100c1c50390400644552004d001d4141c0d50100142543c1850309182c501500002d4200c41c021401e9141003004904503004a41c5030220300d0041c0d4411454520183e02004283d201c008101da00003014814180a0360310b10006500c58103065402507120111 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 212502571 1250 212501321 212501329
    0x1020c0a1707080c03070b0d0603020901030f060c030b060403140a020619020f07031709010306050a060306080c0603040b040b0403050c07090f38130603060207030809011a100203120a0b 81
    0x74581080c42181c2060042c0d150917a0001006400d0b14824403d083c1d840407000d09140050083d644001c1d080059100000180100c030040604524004c080034031901c180d64900310110b030003402c14103900c440140030600106a040e00c100e810900394004a8040e14450f070001401a007101c41813860080410010400d040d905024000041810500070682c060562b5100c0c0b809000004c0303d041000b0780403c0401081c0e10035000b403401000040d260050094032501d00402503d611b000e000a2823050f000c0f821a982001d4040b2403140d0781084c1c018540740c841c1c0c0c0ea40010040050700c2502004010300602e68410410302c81140148440d6900142002403126210b041c1c480c0700c4000c3c0d0490504108058019620071f00b64100c0805445000350305a03807440004411100701099204602d24140d8007200300b21995005012260103619003041581d207201890782a900d0800700f600984d056002c08003101e061003003130500c400c40301c3e006890410752741020184036008115255840702c4e03211002e0341440d043c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 212503821 1250 212502571 212502583
    0x18100504110a0e010506040e0705160c061d0a0608091203090a0b18060a180b0a0c11340e100306060b0c0618010923150402130b01020c0a17 61
    0x3d00c403110a003d0398508000200d0354011440341032501030f41c01d8000b0781d070103100d401201c11580314620f5542030784215050110f483c0813140902c038082010300000c0740c0803c100148001d41c0102c010640e117403250078054111a24603010703000c001c140c8121030000001e0b16522001d188250301840041c0000f032000d00b0001c6002c04003900008149900800c0c8111007070000c5030569001c0400600400d440c0d5907c14101c0f81101d5054026041d140c03007106010202000d604440f0341443c060384ca0300201f01101e1103c5440e00385d0281811401e4034003603100d511868000001034070550014990b086540ea8a450f062081c0204483c801c0803503841d40b0f001c1c01004003e04c00c6102500c284403c01c2e00344101c501010b036503004050141c29013004410b400918240e400d41010010941c404000f08486640005a510f030013400052a0954001c012190244103c0512020b00c21500180591a4444519034103c000c2a00c08280d9045014080151145e62900d00d640d00c01000d103005c61000074400c603a440b904200d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 212505071 1250 212503821 212503829
    0x180f0203120c06060114191416050c1908030a081905070201050402090c0a0c1401111909060c0807020d020d0b15040b04090b0402013002040e070903030818100504110a 73
    0x200087c00202c0c65200505101004030102e400c0480b0310005007042e4401034090031400e2102050341544400070000b02060f107000341351041d00c3c0b100000c1480407030681c3c0000a030068842951051000c40a528411542d454001030040703803500411801c40200002d0350001c442460150307444905010850420244047d880314000240904003520b083c80202200e940c031402501051170700c03180054105080d8003003405c8140605a060f50f800d011080ca00020310b1440d011804240d000000151545c01213451070281c41c2d00c035100130b1520403035500b000929030454106903040300c0510441c800041101040b240640882e404075079040c140d900c100b00a5400340401c3d80e000c0c9040050701130009128400ca25042a0309081c0318140070103090b40080c1d00d075036a5841c00085884c60850f0f95180c1c0e840c0e40100141d44021880490760341d1820070907103407000184001000620400e000075900c100c0b4040e400703200b43c1140180e4136420031000d100300c2900c805440c00e8640e8401d07001c010f10a4a00481640010 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 212506321 1250 212505071 212505107
    0x415140418051f0b19110106030302010605120f030301090c030b031b120a020604060c031205070e152704020409060b0c0c030a12030f0b0306070c0c09180f0203120c060601 75
    0x144e041850881881c080c03c158582c8480c0d42021880c80d290181c06145078403020f42c802004090317941d090090203000c0903c43d4500034544801296803400c0c001c41c810034010600b8004500d96460840400003c3c030140c4c40020806a881c840c81c1d04680d4184010701d011401003100c025407035894410040901c00181d04c9003a2036200c2d21000c001030303d0700400d9030101c450504007025950b0950405452034150910000724261900c01003142c86500019824111001a00d80d105500c01c401c502c148180706259215018054040c80500104490b80401021202c00382c4094103050340c41d800c1a0030b5400980009000400100c1c1e200e00c070303210403c200d242417001100108600100c2d600c1d900180d0b190381b421042010b4550140200c00d10903504414520500503007103c10314900781c0c00045c043c4280003c01c884e03a080301c190008102400b07018200405240358240747e10341c8140e46c2c1e10004406030042c200d03010302940082e610365046200203480001e043c100070340640c1c60214001884d501e0070350790744162 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 212507571 1250 212506321 212506381
    0x50612030918100308040810050f0906060f0103061d011401030605130525020303040c05040b030309041d0102160b070206190f20120903041514041805 66
    0x96560b40c0402c0b04801889040c20b040c16450b1030b841842d6201d010b40000c0c3c181c00b0000b0300083c40d00c03400940d0510f000b003203210400240d191001c1056840c0803d40300340c000c0d43e00101c040344a524021407000c124540506000074000d5980e1305988488881d00408010030100030700401240c07000850300855507800b4a0200090782c1070034001600c0b039005503560010307141e50700700103107044851600f0001d002404003c004d200c0c03ca19a8000d42d2940211002c484954048000040c035040c07178082e0802d81d00000b0051410f0510500901004101615451000c1482c004208262a00038402440c00c408002601342a50445061003403040001500d01e10131588644200848100010740305c0c9015003262a002c2046074140065002421700c10070f000012260480c80404c807419400014000d02c00c00d011840a183c1d01d10101c2d5480780581c2c401c0e00052b5610129080f2040e2041c00d01045400c01c51020b01d00340fa840d114003030360b1103200e03540c1140a15500c2c014021003490748802d0841c001c501c0080b41711 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 212508821 1250 212507571 212507587
    0x1d01120e010f2a320708030402041d0c0d1a0711150609072d031b090e0601030221010603090b0a090f0809010203160807021807020a0b0c0408010c0305061203 69
    0x1021488030715134128004282c046044115090002d284504500001d0b819215000c0342000002680103407006c030320440c50100c90301d00c11108041c143c0e681901850150080d407052070180851200c075030400b100d00760181e4030880c44404130307601c142d80a0491030f0b5681d007078903400f5000f19261410703100850740300d03000d900104946580e41c0c904d0641c2c081140c0c44c000103201f040c2170030b4048400c0111400380001c02c603142e90340c10241d8150b011140c080c17820100c000b03c411a07142c050b6601040307401460420803850340098040c0d402a001048483e0340c880308180c2d005003403c040c0807410f00a030000c0e030009403034050a20a0007202020705400220548081011301120f1380d0700c07051162980300c010b005007000300320062103038000c0c400e45609001030703203046042c10103070315001c4050340c00074408178450341c1c2d0f00c04a440400100c4121520410042d001451aa1030075201d8408408008010000c280400c0001040c045428000d06001b00b080740c5000c074403418803e0070880d4402c1030181100c1075a0003448510307 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 212510071 1250 212508821 212508827
    0x30303010806011e08030a03050702010f0e06010b091801080d08070f05121503101b0e0a12020d0218070311130603020306040e0312070801061d01120e010f2a 69
    0x1e04455813041c6003802400060000d007041e4160f40e019041a00010a990103070b20f0f01500001e2260318154000c02c00d01000b4050381c0100d4004050140c07140d4800c40060290b0b030038003002000c0b54030005128051a003404e040d240300e6188260040c05594004440e042c89240c1c02079217890f005400703810304030960402c03181d004080e40a90750703400c550180303080c0110381d40d100043c0ca24040010701409940c2900d04100810000d0803486d0340c3d42d00060340c84038030a40c15a200340010050001c0080c9507886c662f180112241000300020700683e80282da081048005a40b405c003141c054500e4606a14031500e0310420207001c40388a510322512440e4104880100880316009201c1a62100e040c01a120f403240e0b4003107070003403c0285a495080c0b00004412403500d01d05001d0301e1241c40b45503501035240c0e88031201140e680d81000e8500031840146054450700c0d60140200c04101900b881e00040e00070110901903094a0902c003240440969070501130414500e1690300501010b80700d119401200d194140c01 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 212511321 1250 212510071 212510083
    0x307080a050a06081b01090b03090601051207090f05061e060f22030b010f0b0a090b03090a020a030b06040c0c020904030f140d0501060e030c131a090c04090b0303030108 74
    0x821541e441c0000c64100480d80000c002c0c200d0a4111054100c1056800a0341c407501100b083c08188200c0c2c0010341e40300c100c012a0300c5520074030083c010036482c3c1018003290024519903900940908a030100351504544550101c802c0405c01c003107118100f18061007000c621803080302d04020001d242d900069180c07202102d01180a800351f0980e01c00d4904070807828100c503c036100312003081031140041880a5000c1c0c42d410b81d00c01c50504200c1d941d846100c061584500e034602c03c00714030001010080961140003541d40a032610003a2108410103500241c0509041e400c03ca03000c041070814483d00b4201449002ca02484608200036000803940004080d0741d4004e00c010b04125034410703001c1145100c0c1e0000080d8a030641e0360961606480341403080a09400d0081178001180491160140d180000d4500d80c0c2a5025051408a01120042c0300c00380c4019250300f002c1c00d020380700c40d04442c0c94009580748610700203246a602e03517003088075000544086400341172280d40309100502041c4030104031 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 212512571 1250 212511321 212511331
    0x501110706120b06040b070c0509130303020a110f0d1206061d0307030f030504030204110316081510080906010504062412050711060f090d050c010902030d0203040f0506030708 77
    0xc0410b0458581502d6409030410844030390700440c010900103240b00c1008080c2c80854407c00d610300e00e040e10394081c045c5001d81115000780c044040c05041000c41e019900402c0320340d0032480e010084020138802c9c2803401515541d4541c240d440890741c0550280c3c4600f1301c0d246141000000d01606180040c010000124082e41304100440030703d40004940d4108200c0c40150351150100400700500d09000e402c0c1d070054401a4050340c03d1000307100301c0c05910000c0b03a01c01c0d400910011038100d03101c00103c0340391078010546001c0002c0c5100d92009540c41100c0505040d541e9900c0f620b081c5080100142844010390203140680c1c245203007403041c400e0a644a8401d401c2c480f043c506c95000e90b08089036034030030424034002d400d031500b801d0100b600c0d48100c945100c48000e00480344151074149211700b01d010222007948854108050b0000014420310003402c04013840400070510a0940d00042c0c10a0550034451002da84009020840041c0c4c00658200825048460508500d40010090301d11100101 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 212513821 1250 212512571 212512577
    0x903130302041e050705070c060806010503070f0309150207060609020c0c060c0102090405040809010e190909031115180a050d0e040905010603060f0b0a050f0909031c150501110706 79
    0x19001e0090585103900340342d0480900b00713014a0400e10005029a0305c40f240580d1100440e4002142d418051f403201070044106039619032442d503624030222440480c90213040105520b40500902041400100c146504200d00006130741c4d03111480c08034200c480c01c1d80044c9200c0c0c0180301d88044000007043c030724075030714040e01d0060b07540c5001d501310f40c0203101d0292013039070280c07820062005208000b4050b08200341c003a05c0701001101c86004100d00804516504440301407400800c3c00704450607001060140c0c400e04006855100b50200710341005540d8000e84444c100000c00c10a001c81c036150a1494410f460000d808010036588481e5181c05180950a0600030041d11500164541ea4461030b0010b42250007080001d4607071804a002d0801c440e000c0890f1803c2c440003160030302e0551518421510300615070030744107a01d01d0034130919000c010107240280c00144007813030900c4607544550b00c01c11842040025101d40c0d40c400f00130409542d0700042d041060300d884480390060002400780c1a18410f003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 212515071 1250 212513821 212513831
    0xd110d030c090b0309030403060609200906041a0d053d12031205010501110601030b0408070b040303090c1a03181e0a0b0c0901051c020d0501030515090313030204 71
    0x101c2514240080d5010001d00040001044031381c81020000c1c0094a2042c0024480142d036440d010056681b001c078410300311125a51411000e485000003810710102c0a080942050358400c0019a2503503421a0305454583c00034403c008031035248901d80e4000d409400946102110340070043d11b00d401303141c04050f0712140c03c100f1040d90b100e0030706400050280c45441102c4038040e2400401c01030701c0d444213011003820714001064a40c099884240600c00041c010001c40c1e02e903885014140d00080c0c000e80d03040d07008014100c041224144a103209a000340ca01081e0205146002c00d5404055806400788030811305a2410680e040001c480e0011101800641380c9480e01d13074107030700707060858200300c5542c5c01e107284400d1000008034124000750f01840080c2c079290340d211094400c40c46080b0304030317000802c10130034845840c3c819460011480821720006007001010900d1000300c035001c0e003040e102a4020588000508101c003050b0358400030400185003003e403844601d905002c2c003800f000307204580750 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 212516321 1250 212515071 212515091
    0x1605090102120a031a01020c0f0f13180b1e15030c03030c01060806060a030807021005071a0108011503031b02040219030501150c0b0403030b04200c0d110d03 69
    0xc0142c1203858040103951641c503c490000a0010100306070220040007004041040c10340c0041943d0326807020142540b04074524280030407000384810000140d122002c207034007040d001941d20440071842034405400341040702071308200e101100d005080c1d40c10042800d044004854200804d41c1d0401d5a07251303600790307040e001c40c0040c0c02e15910484554245c4000b0840c900e0840054000c0b504982e00d075002d40d0a507450740c07024810260010300021b441c1c4001000408018148559807603001255850581c3c01c00b891540c840d03184ac0402d212140000d0328100040c0443c00c0300b80700e07104200c0c4000381844041851641c0140002c881034103000aa0704000000405644a0380c045070180b41111f20f803201105a904006001001c0170b0040c910f40305c0320141d00c614114001c000394815250004041110340d544c40e03600b00c0141400300401c1d03811984075080303e41954880fa50508102c5031900e051a10b5004042c1c3c1d99103040c0607500e50904100c9030700400f400c0c2840215084030707001d8070741c940800d1604103 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 212517571 1250 212516321 212516323
    0x40503070209100603060b0708030114120d03091101030218010809010902041b020d0507050601050904110603070f03150e0406090515131205090609120c1003050108060702061605090102 81
    0x45190180d0401490b00810080d02e010800d040140e418a4a040080c652500b48201c16130145130001000c0c25020001030110308031205110009490007000000346126500385070381004440144200441c0d106c1c4e0b039240401c07030400f40700c03503400c80c007807808609007000b000e90754400c0c019642d0b60038180030352200821803800d070079081b241450f600036009004d03c0c1c4005a05021680590348090014040c1c2440c01420380d03c81c2044500880c0c00c0303030041280364200420440320b0726025100312800c204100407120030762105c1005d540700354416160641c140d00600f9028040c1c4400c0049011a114145002e00c90f1649041d03000d90401d420120015014000f803a2039450441d4407010481000c0041c0c00b0420224100c44826026074405c42e96221445a6040c06403118040c0c10542030703004005004081c41d80c10104017407644840600201d9001040900126800d88450415400026104c0c0b005002c0d09204110107038002c9100c0c40100000e1400070b8912580b84446000303070301044800100000c0d1a0700c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 212518821 1250 212517571 212517577
    0x11d0307060e03161a09120403061104030c06120f020a02070b03041502030c1b010203010501080f04052803090807050d0f15020f0a020c150307051c09050d02070e070c0209040503 78
    0x10310801c0c1381400f14070740d0500203034241d21040041c4003403181d1400280314841c0843c64100841d03e0004490419095030745210103031920180040460303105010000c04900c12520200040150343c80e5503040341c0100001105540707402000b020302600400007076800c0c2c5d9001070031070200c4041c441d40c4c0340c4985840c601040198108208600050300104c14821030f020510010045a08000c480045400c0c5100486090b40401d100d1540450f2641002405641d101d2502c190301078484d0b000c1d00c6200001c205038803a60740e40176038605014202c5c02d410b001010340000a000c090f10700c5d00c005103055490040041e14094420100800c811402c03070860081003940d8104401c403c6a105041d03456007000b440c040d889800c03114061005124100184034181442e080c1c42d0050000c02c0101491030b5913a450a41d52503010483d401c680b58070210744002984081d208010b08940b192000e0004040030301d800a140842c142c12448080f01d401050055442d0003c0352203000560642e0001107503526810310a040d80 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 212520071 1250 212518821 212518837
    0x703020903011808040e070c0c05010c02061c15060206100b0c03160605040b1f0302060306030c1c0c0e010605030105010e060408150406200906031312020d02011d0307060e03 76
    0x40f85201d03e04116040024105a905030101751442e0f0361090001c40d80204598405895501d1041040c03040354450007028402d82d002404043c80e1040c1041c80411101c003c901040209d036a405c45800042d440c03100c1c200007041540f0043c040c42c28034241044c0c5100803440f0302480c900000038583e0b0101402d00542d0f808640b805880203030fa02241c104100038240864040300d03d4140c610000d1206072803110243c410414403e1400042d504560034004180c0c40640081e41c584500903d40a45558100c3d1034400d0b124803610422102c0142d14111181000d03c1d007088140f2801d00d801404105d52050943c6d04440091074203802c42e082c40030101e000703441a5040002c2d1805014075810500c11080356540c05244a607200300042904e81001480b81003100c04071018a9104000c421201e10303000e0091a0000c0f0303034040b003106141140c6c0e40c0c0240c0d510400444005a04002400741a00d1f8080c42030380c900c103610590b06100c0402d80c0c1c00040d124824003000405017556848200e07501c5104101b528021 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 212521321 1250 212520071 212520101
    0x60a051003020a0e0609061806010807050c0703060204030b071e050702210307031d010e040905190506040303050a1a0103090c05030607111212040803090c0603070f02190b070302090301 81
    0x625111911394410000071030b140d034010210640414414204000041ca15a911092440c02c7d41c8503680110365581000e0708074420410144202c40c0201e00501c00700e0011071140c0c400603500e620394908054840e0000f13082006001d00c83d66108008003003020340c40c00e18910341ca800d03a510344140c0f00258940710380503241e040d441d00c0c10081c101c6200000000300241406920340340a00300700302000440c510a80300100e40003820903010456107041c29000b03101a40e01c01c209407072004000b00312036240024800030544140c0e000e101800309168140c8902900400450810b0140c01d250900034030740004143d41d06030400d07030354001c2c80c2d045c82203030b0002e0740103401c0040c19244a41458507000b4030040508841032003901904945c1402100c14200700d55111985030b520606c16503694850141d541c01c001c0a441040c0100e000c01c1c80d00b0350b1101c00039407182c074a9490f46c09001c1d0100307000a1508030201c180000141c2d10140450208400c0c9100550000c43c0303240241e41c800100b00404e0240280700d07004441 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 212522571 1250 212521321 212521339
    0x30306121207031d040e0c010e06041805040311010905030f0a050c070308270d060207020a0f06091d04050a08160b131b0f090c090302120604030e01050a02060a05100302 74
    0x816030310100b50760800c50450b440b07000b0942c401042008981052461400550002c1f2204401e540500034a07071603500002d003640c3c10a913450450300c08404403d180082404d80d280300b08000c242c1c02440c01c025554026008200700d80240d5100d0350744c0e02c54114280101c0e1001705680040364880c200b111001044e440036901100c0c4d60340380c90000c9400001440d0414400c0b1111a51501c4407e6580c5200380001080081c01d1041074450f40c000790301c100d6007a03810000d00c29000c224a00c582d4440746c010b105c596600a00c0a1801d40411807111300c0300040d560303a4040394203100210700001160982950407456140d035031158016803400c0192000c00c000c02041d0309504000c40e40d6029080c000865006003804584403020214086095450380542900144079640c10f1203c03001981c031019240390340b030a0072201940c07aa00090210301000b01c0d00400c03a0b00c080104020158410305034a144d401c01c0c20024100881528041c0d10342000074080310525030345800280406d03803d0031200005507000341c00e00360 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 212523821 1250 212522571 212522573
    0xb06070308011401020a020d120c05031803010f1a010e030c03010603140f0d0215070509090a0207020f09010b0f070501110c0601060207060512010608100f06020a030210020408030306121207 83
    0x101800d01c6104020f01c1281c803294071035400491031000055004003509522183c983d541034039428944801c0003081010f5929030002401040103090f1021a028650180b8491000701400c0d2484540ea0149081c1003d0048004030044058800010400d013001241d05402801091510b0b1400300e059a056003406800801d100c440d41c003441c440006d0000380c55400c2110b42c2c849a9441000c05031a005032b201c0c0000404120140030090b822504070328015140006010000e1441c0740140c4220108030350010311041146008aa0721414640a442c4100c1e03031f40c07504502c101c0c140508082031450003c0012900d0401c1804e52285071800c40c000031460f00c500c42428515681c44ac24010200503205950002c20054012015a00c0c00340f11000240042da0030940c080350405005005174102044001d4013040310142c0d80c480e0030103032100c8e0340280861240c9080013841d240d19010340981540c0304020034030440e82c1c0402143e50000c03003030307034480340180e200e110341450851008803081220101181d424 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 212525071 1250 212523821 212523827
    0x801092a0c1b050102030a05070c0f0308090301050a1a04090f020301020f0702090f0c0a0c11031e0106050402090d120207030b0a0203060109090b0310051b071101030516021f0b060703 80
    0x90046001d107521542d80e0090102040101006000e40d50140e0b2041c460b074580b1030b109200400c00548142e12542071181d1f41e0314182c055195940040700c085101040060490500348178255201410460900110306169801c2168441c0180340700e0160f51900c1495081c801040c102d42c64403070780a0003c540d1409008007104140d004600202d01c595526000700c0c81d482d84541d00366010f0b40c1ca80e030646142c115640404e9035041e8a0702c1381100c46003203028814202c0d80d401d0080e8044a110108000c0d40800140c0c003107821906030741c20091050340b0500c403440031526404803001a107684044509000024480e00342e03d801040c0c1d1008000e002d00d44108000400c454001d140208404c1c1c880c12840394503588180c040d98040c0c0030241e00359104007400a0b00e031190750082e80d00003000c00040103000030120401003843d0300c960016540d030b803540c44940401e56450312840764400b10303080001d4004002401c0c02034031140c1c08404554200c00c400282541c0310507a5000d030750a0794004040c207075508250301e00a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 212526321 1250 212525071 212525087
    0x200f1203041a01150c0c05060a020c0103061203020601030212010e06010801090b0f040206031302010e12060105100c200406091b080a0209150c1e1501060c030801092a 73
    0x4945111101d80240341c65000480c02c141030701c8006066090185940100311004860043c1c203039044212400b00240075141c031401450501e009a024146852404001406680682e80012400c1000307502e07000121340c1c0461a241500d9049440c040c140b4901402240585068030318401c4034003c1600000705140705501502c21030384034846080310b99403660148622000c0884020350092404c000160910307241d84489188a0301c1410126180c0694101041003400342c0c102100c0d01c1d6002e000140458907126984024808252400402807002c5030f450504019000011070440e07a2180c05018441d503403a00004080e00c0303100d20803c40141d114110f03d041c4410307a031821020420140218500701c0c40c034001c85402000240c808507240300b5010240b0450760048003031210038000c0100151400c404041032204014050008201041c4106036010800806a000c0300912501d6068a00025081011641141c1401c400041c51401810340c603d0008080031000790801030403464040031b140c101c0b0103 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 212527571 1250 212526321 212526323
    0x7060903062007060905011506091a03070219051c0504060f030b03031b070e040506010305070b090a0302040902031504080307020709020f0d0209010909060b03011d07200f120304 78
    0x40c01004030061000d840015402d2680c24090740c20400800840c80c2c5400c07100c8180c1c400d0000261510401d258643e02c840c0c2a0060000501f51100401000303580c0090071044412001103a41740d41003d08010356034036140014002c2c0d001200056209001050000b1a44500055400790316080301150040042d4002d000c0d690100385500e0342d55240c10b100e481000803201c03000d4021071070001d030380c0407001c008000038003e88039911403030700c001c00c056021213149270185100790014003640d4114680a07091000c10f40183d040704030305100c00360250b541c8071503400c2260340603280020308002d40e0020a00f422031203500500e01e0f0300c001041c8010030201134015845a20f0726400d641e000317034503041244103038070a448104610040511550503164a9507005103c4a40c05040501406030b03650b5400007526069400144003800100041115000f401c151705180410120340f100780e440e100b10003070071011062001c5405400402c8208000410801882d50113420446c1107c5207184845100c00d816070045030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 212528821 1250 212527571 212527583
    0x305071d0a15030b0a0f020d020a031107030801050913050d0f030501080f100b1219060b010813030c05031c0e0d080c1804060b0705031209160302040203090f07060903 73
    0x400150001d1007803103584007050011081442c0c0d28a5510f646014180180188812075036406940d000c80da0382e403000f090b0300301c1c61010158a40141040c040c0458086085580c0400420495000040d43c02503503141550000c8403000040d850b99014034075210071b40c0800815034413501001e01e200a4101030380d241c010544cd942442540e88680c006900c4200b05816440981d006801200034070215810100c5108070180c400441c009030300380141c0c03501c0c0201c180b62089000b41154034013030000034010b01d924000700303007001e11060074502044450030b42440c2002c0e04201c02d803e210340802100b4030484500449004808481c500040746007001481031050600051103100030200c4090301a03c080f52155041c121000d083c44100803403004081c0b0514a1198019a0381d1004299222000050600710740100c00640c1ca0b4254640d4140084a01a104851a50100610851035808400c0d45410349506840c0580c51352203c0c0407580c58044141c0e207415560050100108a07103a00c61608811280118 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 212530071 1250 212528821 212528879
    0x6030515030316140f12120a021806031b030a06050a080f1c0c0f110102060916211425030c05100c05011b110303060a140a030507 57
    0x11041580d01c0c41100c0d41d40301080c00c400c8800307020568454020440101050598212100200101d0b0600d00d040040aa04000126607920b44035403000b12030380d01c00c003441d80443c030303000e24030340c000400001c00204140301c0d20340003000030314042c442d5400003c104003c50344dc0ba16800c103800e8202c050b11103070007060302408100d44005110300d000503c03e480c03c0c0b0080050202c6626103a04100c01281d01f00881c000d1115900b0700e000021800c2040c4003005015112280740041420002824400e010302149290392000302f040507040390000c1030000700c43c018030080303c031031001900c41e10000038071480140c0038000395000e0219256001c21424203520301881000010345c46201c0c480d0741850a03000241800440407001c5c40642030010304400020b42030b01300815640c5d07480c0d450b142580d5a55045a00e0160640228040580c0040c8104220701410b03000d103045182460101d50162524818510701c4101812801d010713417140c0e80c80c20b0140d5040415907450a854080401c2010f42d5460600c501103809 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 212531321 1250 212530071 212530111
    0x200706031413020418080a0f0906050c1005270601080c090903040303140d1a0102060a02040b0d05040206130801060608160c060902010302090d0309030605010e010b0d11070c060305 79
    0x2561503102d00d0501036900410141034003408010321445c02c0c04192070070384250010201360020f002e0260761403242d0b10180a17100f0311800608296082d031001041c44000d01516035a540003140e14040c1990544c000185591070307802c282c00a800300c0c2d0302c02501d840302c1404050352400126146041c0c076003040880d003d000c40e500138030942003411100141550003d01040c00042e10034041c0c002e010201c04243c0342040c0d440c101c44411111032801d80c003a80340ea01c01d0072404558061021a41c0043c0150013181031903c2c00103010002d2096007601c8801d50b948400003802c660f00d01d000e031240411401802104603440700100341c001c016601540c00400c07460000180402d54120751032080355000e035a1901e11711695a101c0d03002d00860702c412418103400b17001c0700e8500d88850208444183c000ea80d04020319145080540880c1d00c1a04002d00d161021001132244003001411942888483d420003e0141805808600d8074000c0c00c0303009141007040c00c03000802640c15085180241c5920428504040d42 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 212532571 1250 212531321 212531351
    0x3090f06081b1602060c01020a030c03051e0402150a0203030711010903170709030803090c090906040f020603070201020409021c0e060402030d140c03030711150408070b0720070603 79
    0x403500401e0b040c00e1500180000900c81016090100035950f074008880c00c15800156681c100703211b00d080d147c3d07003c21660f440702d45c507001c3e40c1202a800d007400c203d00d040805440b690000e4003083c0c40c03190b40e07500001c101107403509000600c40c9040544241e0b21980a198000d40f072781d01c1612990002440c0103180a11f490043c4640390360190f054035000c54481c2d041c4180c044001c4010821000c2c824800d80020205008030015841107030000b024100c403003502c01c2007111000b805090170800343d003e01c040000041c5802c2c021a801a01154415140d580e0944228003920880c0c12943e0040d002040700385181002c2132010007040d004140c00d10480141c220f16903a15601120080d52561103e5442c141003800b41600d9010602d0300101e05240c0503001d2080d0385950300645100001a031503511124060f20b042c80b84040070000f2103048007082c20240c82c0c0071803230f009004001d4098000500070415045c09268a00510842c043c04a2003400000040c143c90740264481c004c080b0b82400c8502c41c441503 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 212533821 1250 212532571 212532587
    0x402030a062c0a0c0519050910090e010302040506030a1a1801020a0f14090a0b03060108330a0e04030c020a092f0403050a11030d08090a02090a0b0a0303090f06 70
    0x6a51010780020b83d5940890320701030302c1400301050610408009500c50341c50001080b0700e4022068a03100e40c0e48a03201c01b80304003141c01c130060404000010405201041080b50503a0460350100d601183d1038030740341d0021b420555103440007000c1c100c9007044e58125440380c4121900c210145c41c21404e0303040d4022150b0342130b4495801d100300000d0000c0420802280513001041060500c1c60881c1e041c0b445200120303031100c1c030311b810500e4020b5010040120540c4c3c09040282e00c0031680e88100f180c142c1100c0e5180c0c240c040382c100c5000400d0040c98131241915403e001e84c008100d070262030b41c85810030303045c040c0100d5500d0f41f007640115410100410084228042e80840d0300740c00c8080c3d150881040d40012075000d100c220f100c1011402c010020110b0010852820344034003941c45891085211001c2600d460b400410301300034400c824080003000100410a5207060b50152000ca50f240e071000160f000414000500540c400c00707001c004001d05900c556600c0555103101140c4c000b40740c0b550300680d1704c42 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 212535071 1250 212533821 212533889
    0x10090b060307020a020d050f0a050313050103090b07030209042c010b0102190816080a08070908280203011401090903030609060506041505040b0d0b281202030c0402030a06 75
    0x20b401014513100509100482040c403601071810350340c40500341c4000d20b0a104c02c1750307010380c2c150384003056540d503c1c01141031030001070209003410000c50300160348a411280c0018456010701d0f0740801ca500658507241c118582045881c0302c2d0040498403510903084c9503c03040e9101c1070719880c14044107429400000c0c1551240c9481ea0704507030114076982c4a08080e4002c9812034482c01d801c2029000250166000d44400d82c03194480598a00e09514010900c0d03002c0e6010006541c48088803103845441d0911494000c110342c110380202e4180350020902400d902d103000c1011240500000502c90610391240b62190700c0b0381e40601086035240008015505603003d0fa03075220804000411282080c90b44070591008182000c41c01c0c1582d510400d509500241d034220323840c0d61141a003509510380404401d1104a0381e070074883c03008a1541b000010122140180c04ca03010ac106400415960200121a84034500400565a81c80d2104000703003c2c0c1090300c00c061a00c5010070003035100c44a000390150000d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 212536321 1250 212535071 212535073
    0x15091506090c0d02070203031317120a1101090c08010b0a080708060115120903091a130b0a090b04030f022103161106030a0c0806061c0c030209060310090b06030702 72
    0x142d191201d1108181e8030035804441460360801c03903c001a2000d01c00b81c050b807100c1d20f800c0d2056514041815070400f06280403100b00d034001011815400c0160b10540c1e00d031003020301c2c0404000ca43e46001ca0f004040788103001c2e210141d895000100d89005410014010509860326a0415965403e25940303010902941c0420f0300107000510180484500d81460981070345440c0700c800700c00310f00c010304981c0c216506a00081c401c0c2401d00064109110b001001c0c2802002c4c0b902d010400907150600400d81e02034459107100000301d200c6124403500500d0041c085415419039183d17030724600098102c070210b008174003401d034041c0035588007007078420018400340c40300010f10f10f401e04085101801c0c0c001c00c030003107035031a2102c4040f403803035150a4084c504c901c54880001440c200d40301e00c0500310701070041c049485820100011914011704031244885801c68100104240c0340c0318105030068003408013101c0d08240084100813000c0c440104000c00c95514601c100881c4c0c0b510000e00c04030b07100403a41e41000d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 212537571 1250 212536321 212536339
    0x27080d0905011704031404090501231011010f110c010c0801030c09020c0703060e03071a09030f031e071d030c0a03120311160308100305061b0c15091506 67
    0x20440072071800f180d0080c07003032800100e030100c030386003101d541c0d00141c01c94010b1569860051184c5602d010b903c2881306003040d03034401542000000640649040c2d001c840406c4085005540f51941c02d4002c44136410301351105200320b04014031084440d030403d40340030086d5800c0024407850540100d0882c2e050380e401c01c2080240c9405c041d440b0001e5408584000128072400c00004046039052281e040524880006150b440807142010900c4007844070038160245078000601c079071104000116954804407000982d2295034146040c0c0498a280c00c040712200072403010810a00e92140c260300c4185802c80681400040307038404e140e174880d83c0040640c5c10005580c820700100300c1e00d190121960b03400c1d184c0460034590340c048041e1203030014600714102c0252005440c0401d2780000403c4d40c06410040305032503140c55a2a02030380c550003e4551070122002000f0307240ca410b0718408641c0b030300c4981c80c11645042c90f94a100b22104c2401c950f208500d01410600502c01c52600b401a4090799006100d00c031 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 212538821 1250 212537571 212537597
    0xb0301060926060c04180507120b01050403230706020c0d020120160503010608030c1c020a050f0a1a040c060f032307110a0f0f0327080d090501 63
    0x180d080310415180c21403011000c52101e0b1100c208003042c4505407120942d600c0702d24000d03e056440000040d280768030307801d080030480b486510044201621054160100700c032480c0d100180e5070b07407003190409483c0b104000050858140701000c002c6507001a07000f1034280c1d690b0b4980c00c0340c035019074030522540f020100d030505000d0342c400c03180b108112505410b29680503261460191801c010505045080d00403002e0400803440c0c00c0c40303400c00816003800514909034200c2c3c4040d803101d8801ca08507404001c42580801d00754820030034540440e0780f0004486180a107000300c559205010101256803503580c1d00c641c04803854404485010700d901c01c0700c002c0c015003401c03000c0c1d8400d000a10000105075841c0b603804424003d840070b10b400403051a401d00010700f05000b009003160320111040c140c40d4800c0c588031300056101003004d1183c03038100c10100b04030b1143e845c01300c81c0403030348600713264445c1c1c028511030070107130340c00c1c448601220300002c00c0b81e085d12203010040d1440c116512585012a51181c1001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 212540071 1250 212538821 212538839
    0x20111060106021b041b021f0903020a08031b031e07030c0c140f010617010c0804020a0b09040b040906020307170603030409020c0f0d1809021611030f0105150108010b03010609 77
    0x311038050300810201302c0a0741580b95803d4501c0d504010801644068420076040c03c004208148507231841308284442100e5807006035582c1302240c001021240c000002480d211280d0035048074440700448003960341e041c0f0700e512085081080021146201102d00843c0005003e4816500d0901254554001e0001503031100020b24145003c018460301800902d9480243d080c464100500000080c0d1221a100c10041d60f003100c114854403c00d00003e03006100259403266150000c444056480a07514059417000c24040e010100d00160818284903583d010851150051842038001d592007015600420f241c81c6034111080d18100d80541080005000445040e002400703029110002c0755800383c4030115891411000440714400100d9101c0c0148101d85620a550000c010044056040002020380f407008402d01c450000c0c0780c0400ba40003211251814003440394041d1001c8005c01c0710386014201411400c58140e00d00d40000c404000100d090300185040d20306039401640c4a18245007440b03140 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 212541321 1250 212540071 212540113
    0x110a1203051e070521060a03020d060e01060905040506130b070309060e0d0f0f020d0f030b19090b24030402040e0a0807060b1509220e0303010b0702011106010602 71
    0x69503151115010001201c15405400f050741c5907551840b600089042404082d4260071003c890003041c08603d0307584035401c00950f81c041f0344891401c00700d490304070000c01404511005c15428241e0020300030076503501242c8114050b40503500340c0c0c2c0d00c814910714000721401d0f0050200b101100454482c40c4213074025006984540380000702d40c00c03003c08507071508240440784000a464600e2518603641d00c000314010341d55041c0010442d8402803000505200507644094003010f65171140128242d4400c0c90301c05070300001d0621442a1500d5581c904003800003040c0b280c1c0200d40d00c040c08200301083c00b1220020b9000903650740c0c21a262542040003074002c80071a48a41c2c80340c0303c008004582e2480051404c10311500300001c04041410078007120403000c1011050000301404862003949032843d007101c41c00e24440c0880e1010b58990801c4004101115040180c0d220200c00800c2d0344800d8001400e46500036220751901441c000c800035a94202402003100580054500a03017208148000e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 212542571 1250 212541321 212541331
    0x907020a11030f0703050c0f03070e0105010507080d0c0309031e050d0b12160914160315080d0201020408010f0b1507031704030e12060903090d0804091b110a120305 72
    0x40e0340c0c0740c00c1143c2c4050300d440700c03a0304292441e0b000420018190300d0101f840710f107020001c0c1d0160501c1840d00d1540c07a02c08205102d010306001e400250503041281c480308a0b024511821410805100703121070060040c03078034000440200351035880343c0104100c4400780c006040120f0303451914040703a0b2003500b80a0300d1031755101c0b600910201d107000c0c880340d418001d6030041d131100c0002ca45550702d0940c50400f074405524080c40d60681090a100a01c89071407071b0500201b0762414080b6078500003003504c540710b026a51005401c0e00501d80d0714014580e0640081044407620b10090080340c1450700050100ca01481c2045e500402400390740002019110203010b2450203801d0442051110700b03240c03043e034481150200c0c002602d181030206946402010700001c002c0c2c000c0109420700c0d160084542c0c1e4400c48264034801c142c821990750801525004480142a00000a004c102416840441c180e0010031400000c14000c0325180e104045c00203110248035005122444d1580410005034018400504 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 212543821 1250 212542571 212542573
    0xf140a0905010e0f070e060711010905030d1205060406060e090a2301060f0e0913020a0305011406120f03180f0909100c0903050c0105030c0d0e1b0907020a1103 70
    0x1001a40c80500e1241c140204828a100000c1d4030300003501c104c1c203410041c1010144102c2031701c48611a00c411040d16059a4080c0b1000b0503420381c180182e4009040c1e90000740d041c410380e520390ba1030b142e03c000590364485010005110903290002004145c0d4810b000d000c001800c83e842c241500c0c9031152200f60041c1010b81d0000f019500c200c014000414000b104c0c94480310ba03e001000466130100700b403001d1146611b402e15041003424001043c82d0030141c001080d240b41117848001b990b0342c000b440f10003141d01c0f8001700150380c034000d50700580c001c00300c82c4541704513203080c50140b45601c0070072107031039440c40701c1c018514010840030708030302482c1c02003003030354005080841c04441c03610b0f00850103008041d000010103424100c0480c800641d401e85000c00d0400030030150030400030720002500b10315440300f400d001d038403a621256603034518012a08104686814241010400072000c140e1101c000c505000d8103104004240600c07211039015204840103038041342c1d064002c22054501402c005900030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 212545071 1250 212543821 212543839
    0x90601050a0909110405011b020f2b0609050c10020601030b0a0207050109111302160f0303090206041211010305010b12060303090432040f030804050a0b0903030f0901060f14 76
    0x11004044603c01c007400c1070b0050000401b48055a000b41c200040c41c00952410320003e00b01e5404500d03444004407043e401043c00d81410f104038230207080030056011103040042c0d180d42c6182414409407104940686150007110300c3d0910504080119801300f4cc01c0f2f40050a261b40b950b540c1168498008102c2c00c030244d030900962001840038050b8480c45ea00860f15201500142c9041002903862402d041c210244100000f01e1521890440444806c1c1c009856400040e03080c00d06401800b02c2d118000d500034800600403481d50a1001c0d5050814003900543d4001c4a900e001902140e40038003540d25030483c2400030005a86482034010707800b03117001d81564202400e81d40400c0c10b071707041c646c10140c90401c401e4140421880701800c0458402080c18440590b05043d240c00300740f0b052100c4050108107044c03000074140300c2c1c204140c0b440550301c00c0d603504503032611004060b22501b0641e1f0500c0a0306110000c0307409e60105000c1d03042a15201c00c0c1d100790180c03070000c424000c50782900e88a074000c1d0a03d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 212546321 1250 212545071 212545079
    0x15030708130c1511060f0105010c0f1a09060a050618010909050708160e250c08040503030a05030f07090806180a0507270c050301061202070f060e100506090601050a09 73
    0x2081c00c1030496110f9144c2c81c0b245240d8010940c10214001c012818100c40c52004010f00d81e400026800510b4001e1501030505280c0e04003050b03500d0940b500e146d00040040144500f10b54000303142481513114031810401e589070002005107100c0f06440f41010b112008006000782c490300e62011a490344640101c48000365680041c3d400c1c00040221401008214103080101d0a0f44d61441640100211041210202c940074005000506452a00c0401044004010800c0b800c0000c40d00a4400242288d4441e40340c1100200341d0b82c801c40c1c6040411440c800800d41c404e0040a050069a40c100080d06656865401d800c608504c1525100c0f05840381c0d40400c00820024030a2801134851090b410070911040e01c444200300d5003540320000c501c1d00d02a5003803592030380304c4140d0381581c24528258100380040004000607029080002c0c140c0002c2517040b104000b030319801140c1e81031014040c1c8412014140c56042102c40407500d42d82c21a000c2800514198400c0d0014090440710303040c03d002311919 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 212547571 1250 212546321 212546339
    0x12050a14030915180916020d050702150310090603050102180f1003020c0c1201050603160e010b03070e03010e010609060f0608040b0601020f0d0e010327060915150515030708130c 78
    0x800d0b86c0650b11194100003d1080030350510420b05181450700304503161628035408142c2c6000700c0310310409a100c0100c086642a00c032080400010828410140222500c90424600070b5101c0861007012140c0c05c02c034410f050904090380700f413081c40101603600c80d844120040c2e01a50164180750030600484180d007441d07948401250004c06080c1000150724900041071500d40000b13588030341052a50174804100b01c14600070241d05445107003070010b440e6180c0c20820f684c5030f4400ba80090740743d4240903001014150561140080350310131142840190350b20a89588190f0181c01014006070b6000001400301c0c5440c1c121b00e80080301881180c1c440012507410742e0904088650a00000d600d0301da4650301987d0500a06807080b17001c80241008030704040c00c00e02e01e0001000000e00c5186c0b10030810050000c01c0841241a40e5401d105000c550007901c001101d401ca580141442081642c07030078070039868020240e0344030703240c3d980340d40700c85031107551548414a0750040d0803190881d4003480402c0d0a04 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 212548821 1250 212547571 212547589
    0x60831050c06040f031401090f060b1f030f0606050906090613080703050601030524070c020112020d020912060408120405032701031d0606120712050a1403091518 71
    0x105920703d00d10b01c45e09510740350070341002044a00c0200e0303042500241c0407070000c04010400652281d40090110991b4001c00c200c0302a200c99440c03044040345440300000e4040d0403501c0043d040180402c403a07920f4640c1940e0318000d400c0c80c41d421400900120750582030540007010410309403002d02551075a141103c5181440b40c1e00115a90b4000100420070440100414618600004084100030312082c104501c6000014844410049100e01820642e40a1088040c002d8250f0b0001e651b01c48100c0d80d00360181d400b1051701400780041401041c440c0714003060301c80c00b0304d50081e03525150101040714002d100740007130010780b89800304001e80031202e421383e0403581801001c030b04410300c1050400009012925016100c2a000b1040144c400718003101050741540201d003166219086101605051300d002d501da0414005200c3c401c41d041c003070102c0040d80d84805840b03911180007407103040ca0895240e008425641b904081900e1155950403101c1e406000300100b400b0310844000c108100080300340c2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 212550071 1250 212548821 212548829
    0x130c1a040b071b0b03090616030e070e090705011409150f040e01030201110102030402130e0c0a170106170303130602070b0a140a02040b0702060904140a06060831050c0604 75
    0x600b18192000c50200c04814500041210840c4c290441c03400c0504103440340c40051050006102410100304014065801703980f03074102c1d00e01203442d01610b4103100032020b081654400414030804400248540c4a481c14410103181300041d00c2c2040842c3c1c060180c2010707500901c090350303801404510140854400544000c03d440840700d03950b545075000140104480c00040303507590f4010070400002d03868502c0c0485d101400d5500008a00144c59450b50804081d0302c0d1030750380540400c00000b10b8691039030701540b40308180300c002c100f8195551000c42d0340c01015515264160824400140d400b00041207010341a801131002501e031031125510301828003803c95920004507a500b203800546079812550b15440740300940c04514060034480f04482d18025414000c1c8155030000c1e40382ea813500c45401015100c0c90741030220245091019220000c0c01480c0240300000b10481d0009500e4425080100340b100b6080c0100341c21014030b804406490b0400d600169058810951101801d46840004000034 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 212551321 1250 212550071 212550083
    0x403050d0f031b0206060f0406090606081b04050a0315090b07050a090e09030d050c0409090515060108041502070302120f1b03030622060302030312060306130c1a040b07 74
    0x442007451001e000c9039107040c50300c40034a04506012400903000203c1c1a00040c04a03040941441c0000004029080e43d4108248050600c10300156180e00510014000c030580718070f03401c0d0301c00ea1803c008060300880c8140ca5002d103810100b080890f141315125604a00380303680104145140e92541500610141c0300c400c002000001c005110301d6101840c0303030203000340c040d0180c090b060040e960f594030300a1a5141c0d070b0b1981c1d5803000c40e26034841c0008032002050047c100b4400040d0501700951912103107901100c0071280c00b40059000d43c8502c80c44c40c45641d00c102c44494240c0f03180000402900b00000407020f51154560780c02014010380080c2c401c0104880e80142c2d14144805d6018079a450980f421100780c1c000d10903c0b0840e50313440800b11031a105d154010270028104452580584a59030019404d400001180903d102100f85070a200344819401c07250b0503140d00251844544843d030014109580e1035206011194914410000001c850260103040540b244285a05580000012264 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 212552571 1250 212551321 212551337
    0xd031b030914010908060c0a02031213021e060d0c121a0102100e0c0427080304060b121f1d030d0e0601031502090109030f1103060a2a050403050d 64
    0x82c540c0c1048031032031460000c2c42d008030901e00d0f01a40a0351a035021f090003504003004541c08000d41d01c20802c2e9100340d002c1e505c0d01c18003070520403041e807003c040c11002a130140c60120a001c02405040c140c1c1d0485e4800604900c1c505403010382210010507070203162104121032000054522207141c0988401c0b181150310a810701000c00002a182002c142c030100305080c00e0511b03445183c400400c1800c14100151404900c14960419141a02a80706200419202c03000c848a00341300000e0050b40c415440f4500c200100b19401c400c0002806481c0e008181c02d41c00242c042c45a80701916030300c00035034140640800d900f1442c1d50300e5204910300982c0031115074404030382c0c0350107040d0368042c402c00071000300042e0040354116101c1e1140d081c1039844001420b85c001880a040e82d11840d4040000e40c0c01c040c454000140030700d007080d0030191110000e4800c0c810200807414902c503510a150044203182e103510740d181007410526510a00103070356031044c0402800300202144080c070120380650129a51010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 212553821 1250 212552571 212552579
    0x30703050702061608010e04080403080a02030408010c0e100c0602090411220b0d0509070e0103060b040c0504060e0f04090b07050c06010b040608011e15050408071a0403020d031b0309 80
    0x100c3e0000c020150710500c0c28201a00e0110380e044110b20341940c4040301d20640c0c640e0b960500c0b440030312031070f400207000703c000007401d4420542c0400900280c50305800244001c0384800c00458404030250350003a401030810b4100c00405000e035141d41c031290301c40c810250401140c100001e0884400b610201120400082d81241d07050312240e5810002810354124640a802c043d80202d4038024414001c0c1d403569200701160000c541000400010b20700d0944410300c07907840380b8103035000e040d001d6103ca0103542460108680300f80100d040da0261000d0b952420100080d040402500c03c81400c0131541041c5c1e42d900803800b0070003c2c40c800303201d0744c02c50b12007a3b0340e2100342001d2840c01805078481000d0120074801400519401101141110b030f01840f100340103540c01b40e10301452107880d07104020010603d000074800035000f10182c0121030f1400d040c3c5070615600d50fa4000c0c080f0a1021400a45408110900040c0f4204500c040028001c0c81d15000d106c015030368a81007000c400c0c00c20f402040e10000100 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 212555071 1250 212553821 212553823
    0xb07060b0306010b12151c0605070305010509060103090804030b01030b06030607142a07170c04060f060c2f040f091505090a02130209011e08011514030703050702 71
    0x2000040c0c06500812030381d13242002c0340d1070600480004400101192001c280301400803960100380401c024182411401d40205030a900b0f0100074048641a017060000703003406010b4800c0c0c9040340d101805511060341c4044c01107000b030520520485141d0810f110100120307221b100700f14040e42c82889182c60300e00b041e10800d0316002c0028200c60030031510484180c108010141615143c0034542080c490518200c4074003221074492b440300c205144942c0300f0004400e0141c5003030640700b02500c9c0545501040420910007500c040d802050101c014a100400055204020030f8091500840c0100d00c4c0703100c00003407075103080300c800e00120090b030040b2a4001940b4081c803540030100e00b800310400440b031a44c0e40d1480020312001c2d03034a18140c0c7d40c400050b0051403e014040341c003540100010311080444000d40d00139000204498009600901256100d1800d000b580f41030807010384900d0032a030720b400144240d00d0445580300f0100140109a80300c0604030380701960240c445510701081d01c1c43d2224000b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 212556321 1250 212555071 212555081
    0x31407200307050a030f080702210c040507030606082a0406090504111612091a040f050303070302030d0e2b0311091806040e0a0506100b04030c050d0507030c0b0706 72
    0x1184c800d522021040000a00324004a007400398030100186d1900310b64000130306083d00c1c10f214084403c903040c0c07201091100c0441c410f84140c40c1202d00b040152241c00d0100c0c2240d07020300584011407240c10114808003074000c15150920814484021034144802800c1c81c190400e0384040041a0038110030f021625241c0a6002d00d5203c0b20b0b4104d051030301040100c0c4c46118414409440e40c401000154203140c4111101c6002e0140e40c005908055030804d1204182c1d03006104402d2405160700d40402c2078074000c011180c0e034540650040d81020100f1010714010500c14961182134421801c505c07030b02900c1151810a440080000741410b820341804c058242c912000400600020404c0320b070030b050b501c4040d64005001004401c442e01d6481c0b00c0480d00030150b00500e040c081c82a814084200f0400048451084124808030090b030f0769220910007141c0250302009103000c00c41e000a0000d8102619029450703401402103a0142c1e075280c80312880d100f4250400c03078002c50005140d80c1880018011 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 212557571 1250 212556321 212556329
    0xc06061e08061f05010c110405240307052d0a0605031f051f0302070c0f0f080303040506070e030c041109040c09030b0610050c070b04030b0603010e0604031407200307 73
    0xb542001440c804000901501402201e0620046c0240c81050240d8180d035400b41c180050030800071410001808080d10207504203840405558007800c40f2141400300c1e0503401c954000c0d00b070758020030701c0510854102c03c44c08403054003860112502c0b1003564a6901078070003480180c80315a90ba04101c9100d041c256210b48220b03215a84091041103161102c43c81150204480d4080d048104031030003003140603105003400605404101e200110302142c1d2041c0b0031045800705d100710300a20365251170320741d160b00007180d0191054100c20001202e01c1e0042c029400c0030400242070310026514100028220303040c3d420a0030039800082500c04682c100707441030f2245c8030000d00f0700300041407450b9200600b406009054a0041601d00d1840c1b0401d0b0080c400c0d1640f00c0128001d440100d500e642c400d1490790081d2100b17540c07000101001c580c0a0406101c2c41d0b602180110160032250780c0c1f900d054814030211400c7c580c10404c100298008220300030324014407055184900c7c02000c08000405142500d2030700 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 212558821 1250 212557571 212557591
    0x110405060f0d06150b180f011d0f0a03060c271a090613030b09071d0a050612250503010c02060112020f090403030f06090b030d0c06061e0806 62
    0xd041c0d100c942d0341070340d4012030036030190011403ea840400003c42c034032030707561140b100c1203004900c000910300c4500c0004025281643ea12800603a00e00044515514461600d4200390a04c0350220103410000c0141d080284050314116100740e0301c6d43c6841c1281d44050500c0d00094a10386150080a102c0c0c42c42c681e1412050100c1c8201824910206030300000b1624001300d07034000186545542e11403100b65000c41100000a00b200783d501c0c1400c0d00310030401c4036079003282d0041203004100c1d0b031906481112a00074940c2c1302c902c0b60b60b40c00c0e20800200405070207a94002e40d085420382d08403100308206d507100312076264600e1806000100f15640847c4a4104c02e2080e4100800040f00c6030740010b10904448044000c2c110070209070000c2008003000000717142d049480d0340108400d154158114650101090204000d43c03551490444c1c00c85165551a030380c5a003001d107151070721034800c81190309508d018101c00986c01e0f580b07900c58409150b103400e020008181c0244204405d00003070005c2e0343d2141c0341d1a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 212560071 1250 212558821 212558839
    0xb01020105090309012d020d02160b0702010e01090b0f270325050315011419090b04140a2c070e0403021f0501140612010902071401050411040506 64
    0x8000181c0720b019074a104c42c10801216446031180c54802c801d503804402500744462801410f040013510381d00002d01d507201611500c0c801c0344008071007811120440c2d86803603040e41046903590044402c5100101e20b181000004074021480041c198010701210500b24252079440907140c0190744c04500e02108100151825166403000b6107020a45a0701a8400c4800154010941ca40d6582180c0c1d10f0700415014411900e40084d81a0a03191441c142c43c049d000d1a0000010b01c42048400c20000c0002480700441000130444581d580d00504180c107001400482d82c0f03601e8203150508404101c500d8014981c84007030b40341d09880401c030803a1609100510034160b2009860059688907110f00c91052900e000e4000281814820b0140d415140401b90025412600c0d490000c4050314081c0135111440800600b000e007540360410071196583e41408524845a2821a02800075009801d040e901203c02c4035500d1100c1d5402c2c0702d41c0b80b003644a1402d030404a000308051004480c1d00403c0c0a005180c64 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 212561321 1250 212560071 212560081
    0x90c03090803060d02130507050307080108061003030509030a060f15060903050a1112060a09110604080601120305090a060f1202040302011b050c030a0b01051009050d060b0d02060d050a0b01020105 86
    0x7110460754081003d031241e881e149090310106420b4802c800440715403500d800c062203502d0707034820300850198070170756180324840e600d501103152250000d81c0d0181c0c07007a6400404000213805031010f44030160b0f0040c2540d8020106032200030544c1c1500e980c10305c081c3d6451814003030070000b195001c000b0b4075003460a2155281075031f56055890506202c080d01482c0d07090318004d1159600007102c0170403202001038031540d0030041400b07400380440920844104043d4100400c15040010944040301c00400080100d41d2070302809210142e10080240c0401c0b0742041100c8641c0c07a011185401050184d8640c0c07100c010f0b022000b0309005980c030204845c01e00400003000541ea1250448498060400d0507a000c00c0300351503c40e282c4280801040c1e0540039030b4006a00348500611003604070f44090380c030024004140f900850302400240991680300c50000c080101050290b070040301d003280054403d8a0103c5c260700050096004524022140c03600c80081020750500740c000d12100c0c49003030000744098148 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 212562571 1250 212561321 212561333
    0x30f19051b0102190809120f2503170c0a14010606020304060512100510050702040f0c020a140102040f0b0406020f1501090b04110c0a0c080a03020303061003140c04090c0309 76
    0x69118044880c4e4500d600103040c000d01100710b5244050051020a0150398501c2454031400b44084400050007003c0156080e041100032080c0c0c081c4015901c4c00b819800c56680301688034042c20501103206d801c5c00f00e801e04460030045086268000d69008460000c250341c2c803800d49202d0740010b001c641081c402040703100d4000301030b00c074482107000c1c9040c026a110600080c0c41078455010341d83c00010104080c03121504100100074071802070700d0501c01001a400c1a03000d81d09100c0002c00164070030200034001ca5882c80b1101a61907135040094901a030381c07600d01d400c85642da002594000c00c00101044410340400011100e0124100500360401426608420160051040c00541915103120014640d500d078403210f418840340d014140c4906e9090b58407a580e550f07058080720b04c1d080c0380300081014200012008400c039855402540f5555415003800407a80034034250009054440341030890f0000400c2d40c45206404105000f9107940c40d00406034190383c2000c0546041c589881104000300c1d003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 212563821 1250 212562571 212562583
    0xc0f04052710152d1805010305040818061606051504050f070e03070305011506090b160809040b030a0b250815030705060a03060320010c02010e030f19051b0102 70
    0x1002d400d2101c0c9542e244140350328120303c000780341c0c2c1c4992030150080031056045402d17900b40b010302e5030107120440c0e01ca40c0198121032090f1000343c140388044c40785200c0c02c0d0010005c196030305c202030176850800c1d500311407040403081041c0040f509161a80d0030809441428007104080038030881d002e000301d0800420801d400000542400308100d10390100880031380342003100c80000c43c0e0201c002c10000c4081180c1109019060094000061003c4800156290b142082e160f205581c8810440c0d01001a50f8550403a40407942d2590050740311041d020440c0c0d400c2c89200c0b049400b840461100e45072845085c0f101140101141145030b25482c2218012a0700c2221144d1003c400d4655626048400d0002843c1801607800540c4c03110700020000c405e21344c150041000c6902c112011560200c0d01c14071042d0b8501c4101030540040c4820390301c50055842081454280742c0042c0070360320b807a0760700c001050410056829a0032400655606030007041010000500c0340070003000320744000c00c89000000d4440e4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 212565071 1250 212563821 212563859
    0x203061c080a080907080307061505060c1b0d060203010b0909090f0c010c170c0a060b01030902011b26070201091703031602010608060123030105040b0c0f04052710 72
    0x8800320f030000c0c0003c0c108011041c0603004880460b41c680050341380c098094009031401203ea0101101300084a0501e0019900400e05800181085207030740c0700c1d031004450316042c240d40c9c8005d40c001d201020030142d100540c0607250803503800c0d80d80c03035a48083c050420406000c1d140070b9440013402800c841000310340084040b00900e01315050001c00e0428907115001402c1d803000c1440001014521001d0001c0c002014a01c1007005011a04001c00150100e49041a0182c08100300f408028207a903281100140214070521804101980e2540844d01340dc40701c91000c1d6881400240c12429982c114076520024800c40800b2081c00c0c50a0032595242d0002400900000c40301d0754403a03614500170340107075018041e610100c510b25079483c3e85043c0e030990100e4411075140c00440100e002810b041c02518461500040742c0076850f01c400010a54035070150000d05144142400041050741d01c280c0798904885504d070410803101c02e5298a104848005041c0226025a85004016135141606110030234 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 212566321 1250 212565071 212565077
    0xb0603010c0c12110309062d030f01260d030510080c0f012a03050301031202030c0a120c020d0f05010c0906020d050d140405010e0106080120030703060f090203061c080a 74
    0x5a003045013852850080c410015404000800d900b4902c903c403280701c00a903140004912142405081100c00503c01590040e69505110005000c2e10201040c203403080b491010404049040c0805181d0400c41014142000039490301e0a0090240300e4500803406046640003902c2c1070b15950001800000074030341e5550521841d840660f01d1b850184001c40552b0116061001401c0302034500109a0b500c24001251084200b041c6502e10340d20000540d40740c0d0000100810310f0b60002c0d01d501c203059402464440400000b41403400060b194241c2994044c0d00c2000045030000440c5042c0707094600714100c034420003819178410000c00d5800644149009004e080c90307076480000c440d4010142107202c55039130408000d2010b1004000e01507100161403d4004020020251039111183c20b03692000c645411a01c11400e01c0403d08400100460700080941400107403036a0342d580c64101103155900c27402c815503003c420428141440c0400c543c20305461610f500801085580308140b034042e030b600843c20 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 212567571 1250 212566321 212566337
    0xc17010807050f092706010e0c04080d0c020a0f0b0d0c0e060d0506030109060c0c020127030308180d090905060103020909040f140f0714100203030414010b0406030b0603010c0c12 78
    0x9050b052402c070030b05c03904810741039102d0203e042c1d602c0d56954028400c0e6004181c0d008005202e00c050202900c00f56444a00a00410f07644082c00310380c900349484059074040f800400025841518005407001010310003040358403504801e11a1044400144600062151041c1c14843c20b81d00d0504a03038880048082c0000c144d1194000b0a0040c259030500900c403603d45075004185982000c0c100c80c00b82d100b6680c1c05020f4429204c0c43c044ca0021000b008201410080140f000038016004154072001784107030404208002d900a070b01c2c0c2030014181c20041010080240840c2c0e03294041c143d03120000b17083c20341c54015440c0118041c0400107001030107140001050f84100000c8502c2ca00c2c2c01d5458070225505c04064082058564102d4826520407c003241d44046480c104603181ca62403001c01d802943c21580c03280c607000480c107106002c580c02d55594000d03051440da42c41c81250f0295008000300300c075a281c0391050508454002d01d40c0b4041c041d001205900107503444e0030780e01010105161280ba = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 212568821 1250 212567571 212567581
    0xc25080c190306020301090605120c100c031806050306280504020f0909010306051906081203070917011505030a150209060d0204090e070b0c07060c0c0305010c17010807050f09 77
    0x5580e2080d08014100f500000c00002c0000440d0424400d40b902154115040050180b03c07580c2c5003d141400ea800140c507181002100740140504c3c0d000c84d01a00300b08419403d290400070580901c1d8005a000c1440030041c010f15040294000e98902c04206107416134010708400c68071850010321649102f4ad80010b240d10446165206031050300380044c103040401d584a1030150301501c8101c41980803c0d0039114540041c0c1c13082c2c0907603001c441495020704100c1d035040510781c102d9400100780710305115460304000f0706c0d06000c00c4010080c011107800069100044154070215243c2540164840c0d4082e0b00c005005c6195001c0e403007014203250000698070301c40350000c5465030149112800141e0310200e0001101c4806400c224034442144060300c030456201c90101c0c003580248011b126076a44051014401c10740900c1021164600500218002c155a96030301800d4581042d88400001e0400594165843c48802140e014100d114080c03d4554140f00100c0e00c248a0702c80c1d150300c68029040419 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 212570071 1250 212568821 212568859
    0x110306040309030b180318040e0304030215180901080609150403120c1806030f05010e010f140301020904021902120a0f0813021f0807050f07110f060c25080c 69
    0x340c172a0440c02c2940d0320380d5040064040010003224030a0300440c2004a4131a41030000320890701034076401001c2c4141144034080c0720400303400c551684101903040071147c60140d694412081d0007020303200e0040040d46005603066051000b60b00c601441800e038a07080c000001c0d0840100c045c40120850001454400300c401202da04409201c203451941900308041030040c1d05801070030400c0201c990520059a940d800d03072441c11002d04c280458018028400c0c0040c1d40c00c5d003000030701004010b0000d4105554100018100c1c1d0150001002c84100607544000103a018007007040d01c00041a40c403820070441c008090034014148007004200681280007401180801000300d0b001600070708060325050b05c00c0c030030340800c0780450702c2c40d40896030090004060912860449401400d050a55800d1031070940e5901554048500002d07032109080385207444a845000140a104420034001e19456150104002c00d4503900071a0030604813003010306010503d4009580c16076540161403082ca00181240c10b5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 212571321 1250 212570071 212570101
    0x501081512070e01080d050702010513081b1002010c050319090b0a06030308100605070b09010906141905040818060403080c0706120e060109110c0604060603110306040309030b 77
    0x264804980c00d50340302540400210701050f1072030b007615500d00340d0f207504400e0741d602030704402c5000140c030400003880154130a101800c442c0f11140304490045482d0f114031414034900304024514401034401c1e446144c035100d520013010300018002003109059024006085100080400c00c03201c00c401080401c4c40c40c681c0c80070025540241081c2d006042444050303000e807043e0720081d4005584103020a000429140c192012694942c59070361800310b003540c5890095400605503000c81d5600c43d40c02e00801d40601801c454120111041c0c40c0b546400c0d54051b003003201764040000c150380740c2401c000c0041c01200484a0f81520000742d1503640180310300081941c40359402c000c1c494140461000030320f0400203202c00541e440e0303403190030301886e40b842001c044550525000e490b903400320700100709100055111100450122280503c1c107803050340e4042c58094140c4049541030344c0c0c0c001c10014022040c101c0912450124007914a604040c3c50042c0b80400e41c0c00040c20030403180300403035400d107401120 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 212572571 1250 212571321 212571361
    0x1c0b030706030509030f0d0b0108101401030f020f070f02030f0109080301030b060307030218010503060f0403210204150809071706070f2001151703040b13030804151215050108 77
    0x11565034013299503030301c001c8e04190883e9804140d080307000c581d0a103100c41112041d00c0818901082a45001d001100a00450100c04185907401c10401034419500c6004141e06030041100a0310740c185407041c989440001c040b02071450b45003282e003100007848041241d04403030b08000300c9140350712804006030406406a000941c40140d50a01e00c90a6000d0040c480c1220001c40079542c01da035401203840c000400403100280024074089046401c808051680c0c009000110001070900351514250702c00403619060b8007001c80c09d02010484040382c2040071b01d000d001c003016002240c0e00301c61449666064003404c440140000e110b004812079100360344a400804400c043c1e0811640c0300d40480740280400300c4580b071180400c0d00041404d514001d103241040c6200001540b0300b80c58820605002d8210607602a080e07549000d0000101c0c0c5000d003c0c00181901c04401441201c0620300130380a030700c0801d408a0700f81d040c080d006a1041c0e040d161001110700a08001034140d40300d5222240c07601c44821 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 212573821 1250 212572571 212572597
    0x90209120a14010b010f0806010813080301061808120703080921030429070e0111010504061d1504020405040819030209130603050a0206130f08031c0b03070603050903 73
    0x30581400a6400d44541d1061550003c0040e013140700300440d007141b481d901c640c020805030408240554841c0d00f04692046d400c9589103807440c5a030f607580f40710307074000e80c4820000707050115440024030402150000034960080100180c0c030310342c202c01d00c0e58019002c001d014400d140d00040c040003020300ca407010410309800700c04000d45d00403111a82d26042500e080d13954981c002d5451031411400b400c41c41e00d00c000d084d81c1880340c1da02c0300320444580b41c00105190400500c0801e65a10a100340209030017507100b03490115001540d04026002481c11505d41c1c0341ca94400d0300c810106403c1c060b507444e00250180e80c0490a5a15802d000c42c2c50b12402071a469041554041c00311081c2c0e01d07502600681900300c0d031280230030010642047c1510740c0d80c00041c0098110300e00d02c8006160040c014175032500320214072040d8560384e01035074070310314141e902a0f8166000054005c03042c4805c0031407840c1d221030100b410030402c0c0703020300826900e800c540240f400b03159031035000c249401403c106582003018804 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 212575071 1250 212573821 212573833
    0x11030409060f06030507120f060305010207141606080f0c3705070803011206110415080c071112010b0627030303040807060908190f090f0f09020912 65
    0x140c0000024541c42c401d154103600c00c203901081491281c02910700400b01c07660303014251058114148024264001180491940c0e542c00000140b802e001415401d1f008500f84c1280c40c070b1066101381015100c10700e602c14038400100510615030486c5041e9004482509010710580d40c802c07400071244920341d0000740d00c2002040040341c07280350200c01d11000501c41060101141c080300180c2c0d143c010350030001e040c0c0d21b052005010351500c40c42202c421600400001c6245061381c0100802c9501c2030700402c00c502000e0120213a125002942c551300b018450004a00d050b02584406024900c480c108a02c1100c0300c0d00440c3d078a1000350000081014028503066450002c41701c440250cc441c50450551542040c5a40040c0d20b000301c1942d10654009440b140351000d03d5464100421b070f8580c04548148040c400c03140d8090041d004e9280340b00c2070b40c03903490000d080c0240c050030200b440d41c03207001d4075026860203001504000f070321003049501000c00561203120f110300203070070482c2a072030440842c4141 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 212576321 1250 212575071 212575079
    0xe04050a031101020906070b130209010e01090516080a05070c150e0606031903050a14130302090f090c0f030f030c1c11070e18100c02010608070302150a110304 70
    0x40303421001035100340c0351500c040300e030085680d090340100e1100e641c0c0a2405d0020b40045400b05a001303034070156880700040d188040e58001842d5410a8010326251520540180310b941c1c024402c0342d07004020744041d484c0340807820800401170300006010610325503d81001c502024000d0001c403440541c00702480d003a050810301000010300168071002007078442d0201041140c1000f248101d1100c101c400c1c10b107440800c588003a41c0641c8402c01e04001c004038286803042050705000a01869080c1e003c2c2c844142c1e146004215001401601e40d025402c0c00e10b0500501003000a01d0044c0c0c1c1609984105d40c4115800010b420300303610300029000c502001841c2c085952021401c2212001900540f205210389500100c500c0b050201c1d01c402c03298080341051018800010700300754080361601c0751218502c956403906007003250128031003c400e074490000300801e81d028007038200076251600080c031100703141d90001842181e428141c0040c100c80041d080042c80c0c803655804002c52140401c072955944c0d0307 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 212577571 1250 212576321 212576323
    0x60405010b0406060512070e0a08030c06040b0a02090f10050d0f1407051809220f0201110c010e0d020d1709130b0d061e090c090501050a120b09070e0405 67
    0x28108a648a5490058081641030240040da1121b40d51011108041e0360f96880694124000191065010303006c01070000b0b60240400c0100000180200036103018181480e02c1c1c409203034040e100e030031107034014130010b0040d817034501114441074030403500c5245001d402c035000d81740ca11541f00358030f284900340914004c01d009950005d203c41c03c1700d0070386149a40e960100494842c0140c0b000b0003220b0048020010491030552103068001074601048200320a958900494500280c00221440c0301050000c03003c5d90b801c8902014182c1c2c031301000d03104052548000034100c036061551140f0550914014509540f90b00540a41d1540d001d0710810000c415403a528440360440c40b0903512841002940310145001402449114000545200000c000e0703a075880015042124804901c0942107160004050a40c01510807a60040c0f145801c518103101c00304040c0c400513002540529111442000140d148403180f440d80c0da001b0b582c106158454a0713640c1d041094640c090303040400364005000070b12074 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 212578821 1250 212577571 212577581
    0xf0513120e04320609040609020a0b040e1f0b04051e04090305031f0510120f020d092a06051303120305070806090105101409040203070203070b070804150f02070506040501 75
    0xa102042e0040b205a0000f110f119220201e0310f4903041102d1201007400298240c0000407420b10050070b82070340c2603c0b1300340c1030419002a44007003580090a018003204102580c414501c5118458446402e00d0400c845801284120700c6240d0150110600009031550001d070034018040303006005110000e25403c0086c46a001a203106141d4000c0d4603000b820b000301e0050820840701d02a0240215558840d0141c850040070785510b0b14680d12003044050302c03c3e0510082581558000b00042e81d81d03a0b500f0140c50746c02c0340b040c2031002d507080c080451918070406405502298050300d0704a90b203884408118000d602d09030700c002c00c0b1040788031904802c240c15800c002e01c1342c1c03e190b503183d07203a5503242c041104042081c4505504003007107400660300d081c46070420908141c0035450791450f040e02203001c141242d004441000068101081880800190b40e40682d00701066181912590910f0385801264100d10000c8480e150360b06c603d40b580d102c142c1e030169204550800242c0d9210700d0070b0b04056028107 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 212580071 1250 212578821 212578871
    0xe070f0c140105041b120303021c06031211070308030615040e010f03140a110108090109050f1c09152003031312050c06060f0d0c08030d0f0513120e04 66
    0xe00100c1c0100c000030f017140030141c1251040c02103503984594588055000307600030681e0150224400603079601141700c030f0041d00011807103001150203004400c84000c00301820103500000980010b803080020036100c01c2901c2c3c00c01070441d40c0d00e046202c4925940600c0c481d039440b606c03030f4a21a100024070240e1500043d0101c174014000340444041000c01162901d0541c07100030b010380c0052160000035485007150076803002c2004000a60500e26131a414034041d04041c0115455000d881c00c900407202c0800c1201c40c514060800c020104d0800c100342036660725600d031b480c1c01c2217000524580c5200c000038050340d200c0c14603c00e403540c90030400700b0161514ac0c8060300b41c1d10b40c101d082c08401d803580700340304540a61180310050301c240d44421003000389081d66207148030b50200d000c0c0312800220707241083c0c0c0d00080c8024001141d40c0c0c080007460005546500c1e40314400c842c684800c01c940e102025201c0002c4e151308c400409200300442d079081d201c400c0001c401c160050300e0401071074821a6040d03c2b01c5564 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 212581321 1250 212580071 212580083
    0x2190801150b0307030506041811030d02010b15070602040e01080a17031005040509070503030307050a090e070e010c03121a040e06040f14010e0d26010e070f0c14010504 74
    0x190724000d864203003070301a8840e00001420400c0041c13011807080d0300c25074000c48020804038040800010550106000d03000035074101d003155074004004d01c0e0030400301101038800e00083c091015003200242098801e40f4240c8540c13000054500c00b00142541140c018005000a000c81541c480c05100c1c2e84402d4010210340b01c41e0000c2144c0c04010b403102c00c0e20702c076a0f01000c451090904107000d0101a10000d070410070700c0d218030f03140421f00b03079020700c040c501c41c4000d603603a1034642c0030b50340005003190310a0f070008148201d200240001c85600200c600301d42c8600f800d05184640d15880c08448642160306c299814130b103841501c1c58002119440b00030f400348200c03014000c0c046080191034480c4d01c25100109908039171001e80707002624a0f901204c000c03900000009052068511003410300c0010346014000484494075402800030300d5501c019287da034545150481d40c1030200c98a4070900c050f1020040c820b0301c6100d011a035220300d05d030b241156800f2080a1505108100041c06847e00703550898a03 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 212582571 1250 212581321 212581331
    0x1021c1a15030a0f140610020a050303150406030804140913020a05060304080d0c0f140405030d0c050703060c120e010507020a02210a08041a070f1104020405180109061508060405070c02190801 84
    0x1a1070700c0049c4010100d45c01038040c603d0343e16030700010a040e028007210150043e0300c0e403c0000c0401c0c2c035100030304014601d092520043c40e081070100001e42400520003144111558910800340e110a1a11003e0328001d0396080d030341c0d413254108401c2070700130350130310b1550ba5003031128009a0303983c003c0d210703d0000c190b40c841c0c590000c0c158070522002e01650150316010381c040100d62000e988640c40c00841740f80650b05a4020540340c0c0c842c031781135031980e11002d8007013420880020404c0c2101d10640501c40840d1000700102e00f80044020749078803031428044c0c030941e403480300301280b00511241d41d0701ca00800c104407546080300f80b4040c56a50068441c210122300201504419459042d0480b421560f106c0312041c417600b07144d81c0c2d001c00114049802504142d00340804a66600e40c42c168810040f0314a004c1c07080c640c9040089011b03140c5135002420f4081c081440114000d802118080e04104111404186339482c40d100702c032044c007c05006540321000c0054100014029000041500c0500d4000e00c1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 212583821 1250 212582571 212582599
    0xc030a03080609040609050f0610050109060509011805030a11100c02060301060c11130e010b0102160512031909140315011e0801021c1a15030a0f1406 66
    0xa2214a81500640070500400000d6024a4503424182d485031086400080b05003542d03c5003407805008800361000340d0321000030301c4110640708100038004c0800f46014000e01d8100a4014503071701036103010711b06004081280c0d1801749003a112003805400044c049625808450800c00492590b04024501a03010085220750280c410422002803540240000e1f00d03603403800404445c5008071740d00c00d40b41c8007412030328248035030345a07800c2c0029a44131400c081903041ca041031003402c4844015000307055501202404401e52000d901c01c10403075a088510f5515003a540d400c0608500c2028400c50402000c1b0341440c01e204d411880c11416038407e100880c1080314070f00705155584031345280b07140882d14110010400c49500034039040200719002d10b00c01200d65540d4926007a6005114a841d01012a0f145411031b1ba0750307441150142889103144000c840c00304004a2103d0560f50b11060301d07100000002051540c00340c006600445a0380c20811401c6041c1e88100c2c0790120588485106150000c1012 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 212585071 1250 212583821 212583823
    0xf0c091b1805221a010c021507171b0f1e0c060a05040f170a06050a0e2a0105030610050708041d0a0c08090c01210f1a01110a0204020706021b0f0c03 65
    0x8507103c182c441808140740c035001c00901081d01030b110440c14004008410000f01400e00c101c42c802426003051b03446c1d0100c001100e1205d0000d540405e10cd40c00308022120041c0e0018029201464250f840c14400004d0003186052002814540350000c1c0d0000e002e031402c950100c004c0040703c3d040c00400385103645403060205c0d5034079034401d48219940050b800340b01060701d40e84070640042ca058800582800a1481c06042003070030984c42c000e506d03500b0720000b25144032020030030a48909180c0740349145030080c002014840d002150108000e80400c0c01402c00c0b1311a000c80d00500882042290280c05c228024480c0107411120344003014140040d0004047c0205c0c105402210408042d10310000b207600110340112521080c0c4502c3e070b6107588488080c05052040505a41c0400310220303c5001c140f004e801311500d07402080c0d04009042c1356240c0305c02400720b20a4901a4111405644d80000d42442c4002e8010050080b800060300c509075208850009081045502804280e0740b0004040d8101 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 212586321 1250 212585071 212585111
    0x3010608010506091c060b0102010c0207080601030b220503070c1220060d0f150503061009020f0906040b07020a0b0906070204090501180f0c091b180522 67
    0x4a011604650060040e40f0300380c009410090b4000d00b0b1460405040d80f440b20800c80c40d00001d0f5603055031106982207a59080c080da444c14a16400100601d514025001c0ea03188414440984940c0341540480c0d418000d80035004104849955030824658840c18069100e81c0520300403280da0600210016205120550a42c580c0750004103e910701c00404a12802015403000301030f60000e410400410a80b1461040d030001110070400090440c006002251289030b99811041c429841502002042c0c038510349080190341c3d5560000d03807200e104004d40a4580142510f56030701c2400451b0128002da001c2000d8412940215514080300355160f541481521820740c80b140c0001c0108520710140c00c080c1c00c0ba11042c0d1040000152000d203540013004001e004000c1100c01400400c400400e02c21402795410281030701e101e041080b821325075200304200d40c031403030000280100c07468a03040c00c194114400008103405070400e0f600b00449818150840303081c0a031407003640c5c980041c10062a0a04041d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 212587571 1250 212586321 212586329
    0x90510050f010e0102010b04020d0905210f0a03060f03060c020624010509030304030605010b0307020f030f1204020d0f031e0903120e0d1403030601110d020a0b060303040801060e010f0b0301 83
    0x40c03070400c1d000d40c800450b03401c610302c955141590b4840d00f041c244d6032aa4402010000480d080000305a401d502e032240c03c10f0301c05041d01e42810340740d459940c982d813040001c4038032500c0e680080940e1610040d0301a400740046900103200341440b0000001480090380002c07a000403a94250f98555499601d80b20a180b103888603a0300c0161080e00f8950103502600060000e2140241100d04041c1d9a0341ca000582e03200b42c00130690681c1c0402408a840d40400c070344050100c0103400b07103040000706040001c050245002c000790804449002c1020354407001c40c1c243e03031981c001d60440c40328800c03410060100c44002610a03000c000e03030030f5803c607058031500320207068035031229174529030000d01c01e402c13607084001a40440d03000d038503171401000040f42500006c0340302c2c103030001651300da01c2c0c41c0c0b002502040152480729080e412010b6100c00b003580c045041f006050f800040c106403a100c0401080c6580602e03000f00716250710300080031a80c45444c1600c0b904035000b008038005d5a03911040c0c028800d00081c41 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 212588821 1250 212587571 212587579
    0x1a070815060c01110c030c15010608131403070b010e09031309020d1503050f01051503100903180e10050121020a02100903081801020c070501110705030d020709051005 73
    0x400581440c0400050500c2c0001a00101e001480c0140d002e001d98488910ba19503607100042c3d0001d80e407030612003d0205a00202c50800562500b00050000c00c0d00070240500e4000d80089042005a001304c4411f03e403c091045a44544032443d00c1042c000084c0544800d01c4101000a00f540c1400001c0303404800c030780e441a085441c40d150240020f5001000350a8900707840300708000c14004e03e40c2c041d900450154004107070203041100d0342401c540c4040c2820b052000a00034405594400141c8611402c3c0300d908001101c000609084a0310011540003483c00c2401c440300084400750154414024505032030004c51055403400199450080080c4040c1310307100e450f0301c4a90382410384d030250003007040c2401910322814003681c00204550229208a000c15010001d1001c401d03100d00503006a0b809440c021450440d1a41c40306a90719110712800307041007844e1140301c401100920520000b49030180071105c040e00303504070103501c0d45400c3c051950074514082c00141c4140c0c0b0842d8020890301d01070 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 212589928 1107 212588821 212588851
    0x31302062101050f0609011d06030c090a080a03020705281502160e150616060603170403030905060f190509040c020105150105070c0801091a0708 64
    0x1a00715134041d51259502942c107440d02c1040b40c44007442424088041200030006c501502e82108506401c0480407041c4000822400b001d0450380e081262100821a2143e410a80c1c03441707614406001039100c144202301508016001040c3d2062a034400b08d5041c0701409641c4c41c00d0070070303802410704018050585c0c0482e03905002201d041f606903e01550601c0c9085981213a00a010740110007000004003035400685e5201708a603461444030310f200f08043c601b4180a40180a07901c0180c5000f8640d042101e803240b0303c101101c0a5030b1b41602c075940c58505160500485821000403e50100c00411100011056940390858429460341d1256540c1c501001844184c1c4c5040ca01c68080da0b040c00d0510060700c0c861001807500120030703c0c01c292a10750505000b5482401c96000501135484c02e80c4800034030840341902c5070051300b5420390341082d0303c50000486603000226010100c00c1181 = true := by decide +kernel

theorem cover : BRFrame.Cov 212410071 212589928 := by
  have h0 := BRFrame.cov_init 212410071
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212410071 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 212410071 ≤ n) (h2 : n < 212589928) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
