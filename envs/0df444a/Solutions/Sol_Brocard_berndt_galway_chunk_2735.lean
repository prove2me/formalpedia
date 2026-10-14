-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2735
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:35:02.93983+00:00
-- url     : https://prove2.me/submissions/58eef428-0506-4e72-9d98-05ced7ee1e5c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 491726618 ≤ n < 491906474 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 491727868 1250 491726618 491726621
    0xa0809100e0d110106060e060307031e05150a05090c070302100c020c010f030203152211031f0503100902150f2802150a0914030414011106010303140c01 67
    0x1000c45594042d004600c02e5850007000304520340810f1015070304041c0100001500b08080c10095031050364401c0e40c0e40d0f50440705034054143c0007850326045a0162649510350301690286024221040100181d01805801c105410f40140140d613405880780c40880c82d02050000100b0348a442070041e240b06865000c01c88040b24244940c440c0940c0064045a010350ba0200503018440c3c0582000c42c00d60402488a000d10340e5804801350060381e4500100051041583c920301814243d0700c030521880410610141d2590000d6030042600c04c2400a581640170540d840241600e40c003070010b202641d4040d8041740581300090040ea000500350800c01c074150703100c0c8020811101e8402c2031581e41c4544134440040c01c030200d180c01d43c07903411810803e000141d0115542510242c10302e41c014180e141c000d4040020300c603003070f4001e000401d1030f43c908822110100c041c10844258403402d00402c48520015030f00301201d404800340380c0d0400401840040d0003940740340c00248460034202e041c500740c80d03e12030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 491729118 1250 491727868 491727881
    0x90b0406180f0b030d020604030c02010512070c060f020c10150b04060f08150d02040c11030a0314011505270405072708340e011a030105060a080910 65
    0x425881d02c6040c2c00c4081c8100e03000762403c02e03a0503402480c40080d103482c000e407514400741c002000c010100c400d9000351780c07050060300c219400b01f081c0301900d1309113160003405084260300d0486401d410620a081c0410161007641d580344441c0010340301c40450203059100528001d28198044040c024010a600b0026030250020781465120402c0460400c40064592040103200f5046194244111411915261090741032154140d4001c80e140020b81e50548600d40354081c0600300b484040381821010380e0580107035910041940901c8416622108180c1d20b00342001409004204100002c80741c18030340c200100c64100c87c040c2c80c40300407992500010300303840d4142c540d000003841d00350800798100b0350340f0a151001c840f140d10100c0305502d084034494542c800042e1a05d091042c6031040c003802d203490400ca00b0343c1c0c80d2a0920081003030b1101c0368900240301c28081e10b18140c0321202986042d0000d070341228140e6400900b410704207094200215024100200078428074003559803148500b44d01d80c080d04 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 491730368 1250 491729118 491729159
    0x8091e030f130603110415112814010b010c03120b06041404050f060112020a11030f1c0e120708120406020c0f060f0105090c12010303030209131401090b0406 69
    0x1410b54614140008043d9090542d031204000c00c02c00c01008180d54880d98596070712624100380183c0c1d51002041c0381000640c040d8a24911605411500c0c00700c116031081c00450b1044106010300390980c3c5900d802c80e618003441c140410010244080440e0140f031145440b222105804030f40d0f540798401284140d0000d52191244040c2004000100d240a00409a0048071045640c009141c0000024aa0100b007a507403440b8540c0000d1201895205a01c0c00200e401d1240c1120b80e9000201c40240442d400542d1b41c031000c5142586030f0300b5103030350390180000c00b0340640000c1280b4058814820800d0b1700860f000c03141d82c041042161100c844a80c940d61003107000300ca0045e111451810078605044080041100e5a003050003000301c0c401c90128498159401903031440195926514005018401e61080d0021010208000010182d06030018030100034151002151814004041c0302558510b01680d02d6491a020051140d01003a5010510491009001150340c40d40c441350f5101c0d01d0104040c4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 491731618 1250 491730368 491730397
    0x130c06020106061d0d0b150909062d27010c0216050411030a0e0a0515040302281103120c0303061005070c0b070f020a090e060708091e030f 61
    0x20030a144e0894807800c091074a4060f03007503801d0080c40c0080c60000030b0000c0100104c03440c50200d00039000c114403a07a05664040c012a02034184108940d40c1c0384011200114070191402400030340c4a401030b0383c40141c12064080b4000b035150403c0c11134040d03800360310039046907110b1102084090000d0040e00c0750008540c0141580800024100090426a1700000e0055007045101400c10001e1001c882d0302130300304080028440c241642407420003004806c05419446020311588135034640c015040d0069202e81c0841da03082071500c1c0320b02c90172100110040003070602081e50fa008603d4403001644070140040a41d00064259418010b05400c080d0402110350700201c20441d144c1001c100c00c8201c651603040090512140f40d079640303080030f16806110540a80450b26030204a4000146912030b43d00400c6002c8040d04c4034140700090450168a81007489803c000c18505806044c1641c00b813040703d0090304e0141c14120940b820354410f9840052148002c010b204a0711545d40082d201540c0c07000384 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 491732868 1250 491731618 491731631
    0xf081b0117010612050c1303021509030307031d090415090c0305120409050f060f06251103060a0e0715020a0507030302010b031b030a030e0d02030607021018050a0b130c060201 77
    0x13000003200c0d00103151101001c820014a061052145c0c0c1140c120780c2c1c126080008114404101402801095481c64140c8408204001050b070401420407051082a03540e940030311400c010442c5ca102c0aa90181140b0315007008031400da03d03180c0001d40441e0040d50508040341c0d580d07072501d24003070132422036983d40b0034042404d002208590261580200e292102d01540d03003820300005400402d1009942e10850001030322010207a841c03110710707501c0c1541c248042c0d0000d0302c41c28001c2c1d41042c8070350443e200e4010480010300e001c034903201e0401551402d000a020300b0b82004900d00300680c2441002007544250b4131108001001048500055407280d030001c2060280c50040c50b160502c0035590441c42c0c07409001c811343c0c0340c0b00040c2050450360035150140510780c030700c0c001c20444809002c019400d401110200100c03150001909071200b4200304040007400b0040107518000c5032400c900500c00d41081c00003a010409007501c4541107800301c0c0c1361a40c01e40d081e0b40c1c0c1d4541480f15600540c00343c1d440d00c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 491734118 1250 491732868 491732897
    0xe0c18090d0224072a02041118060a090503030d060501030b01140a2a030f020601050409080d1d0a110102060f0423030c0d05130f081b01170106 63
    0x800c0720703040007090008004888502c0504030302c0c94001000440c403100c01c60b0004405500c50208004402d0302217198030190b4480302811a801402e2400c00c0e4001c80c101000304502c00c100104079020103441e10002c044a01c07552041003c554008030414040180505010030181c0d014002040c280020303410000e065840d100015007500c4c41039038a80c1c140b080740c40b0181e410b0b03a0f00c482103074011041d032316144080a40030b582002e210a500800e20540e50340d80030428081603003108800b05404031715000c13030322542c4e614401c010a44c1d2103544010520354060010143c0882c0f150072800c0c04d07130500d0b100340707890302e01e521000f038500544880291181c00e0a414010800c4d41c051142c0750f008007081259801c540303055255000302c0d056034848a40c600e20840160f5441003c24030940c0c0a482d6098180c40d0580c1444170028040d81020070318040820b0303e0400002e00901c1a0114400c0702d000700e01a120412059501c6030f00c0552121100d03040c8110f00b44c80c0703082d0b4151800818040d00054895a81311113071301 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 491735368 1250 491734118 491734123
    0x30b0a0b130501050a0518011709010f1a0f0d05100e100506040903092102030f0106090f06080d0f18060c03201e0f1c14040f0302040e0c1809 62
    0x203610a82c107000c2d0800403a01700d0f44d4010100c5907204000f119000d440755500b00120341d03040b0094007540e9140c490fa41803204003a41034029120304901c0d9030b030034801011200c00442a00c00c0248000384d02503d207074895006401c0030841045690b0084c4252110514075131045801d49500d183c401445802003503062151107070620442d904510140c4082241d0f08160b90003808503400b9000c1c0c007508000c06007003000c0c0f201c0102004044940d003d02560f030254001300780580a001540151345a0a0801160517012100ca100e65022a90450011f044485034441d003551603050410360340003003008d094694400c00c00040c1ca110b004010325500d10f800480f1900f402003010040211078070405450300280c00803082c0024a42582d00300641d042c8982e56000720b00b071031070304080401c2d001a500480485040c80c0c15000c01c8900585202d80f41c041c80c0b0502d98141400d244518020301c0031f06004004213002500780750748075150000c818030454581050381c00000700130300e10b070b05941c3e4000c2c9403180030004128010f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 491736618 1250 491735368 491735407
    0x80901020d09050a050f041b030b0103140c030f060303040321030f02180603072705030d0903120305220b04030e060c06010311030114090a031d03031603030b0a0b 71
    0x12450040e1000d81841c00080304c2840074402d5034424092091840095a5550301011400381460010340e59421140e00103400740400b100601d011900d000c1c113040d61800301d8104244a200c1d49400389107103a440c0c02801c0c81010001d050035401d031200b4000440003031400040719003030690600c0f003400406080200201580c01c4102c10200c514018842c5000c1805210641078209400722000340d02c9039070740c5101711200301c00c1940d4a0420500100c0400c241c00c1f0b60a140e90503100c00340c081d0703440501c2005040c2c0f40c00c00e45100040550303080341800700e0134912a43c0b001e5003000441039980c03100881410845881c050114040c0c4040c9007110501c0101038101c54480c44084050320494141510b0b43e866a403118070502c0301400c0324001c404610a42d58080d404904400c801d81c0e51000c0f00d05140e01065501d80d00e814003100031503248030310560041c0400d080c104420303500078011442d180300075800d60210403c1c120201c0078107445110f4004240d0b1015038a01c0600512750056450746034a82100d51002c59 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 491737868 1250 491736618 491736643
    0x421030b010c030c0201030f022107020a0206041401022109012a030311191e02070e010b07050109080d091e030504260303040b0a0b091501181208090102 67
    0x80c0c04035103155640c005440c1100181c15041a0440e01042e0006074054290600e82454880c80002e40c0f00c0d000401d28410364003400340e142c101c5134a5448110903a6150204000654071020912007004203201420000080341c0e01803040e104889224110382a141c3c0c8400d0842d03a5100c004510941c180d603000031611210b00100d5440c0807522411100b1681c05520071402174209925880d18000c6001b022003100c8211035140003160740e0000030013000b0104404881d105c01007010701d90740b00341c905200044003025607000e0740d01c0c0e2449910b480c0d10818180d005a134119015500c2d000c080c40420601c401412606003101c82c08154180c032813821091390881100c498041c4c0002c1c02c0002c0c04690700006036403d0790f00039121803021030000841d1840c40d4141c2000c070001e0384000020482003041c2c00942038019030442c0402d200d8045140c00b0420003040445070b5004606a0030808074040d84690b407540d4030001d111180648840c0c42d99001d50740514500780599000800017040c80d0b46507030401c0104000113 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 491739118 1250 491737868 491737871
    0xe060f09210409021e0408070e010e0108070b0306040e0d0f110a1e0c080a1a010905040f11062208070e010b1909080303100806010b07020112050403090806042103 71
    0x18001c0c12807040c0201c2c0685401681c0c00700d0784103e404141400440d0f00e0807000080c60b00c0740d99841c10b03035544058602410303070480403020002a00a01c40e60a041c180c80d4641c018010300c0c0e00381407000c00c264000034110b40e072141e210f6000c0c0c40408024842004092243d076170310004900703268805081c810b0240c080320140d1344000101808600d003c80585444080c0024000d50010346083c01401070000b074004c084680101b0901c801002030f905c403501c075104948000e0007aa60398907070411b012038030100c2c2c008d42001c0825101c40c00164032580400d445900c000e10090600b2100101e02d140100400e18072590001d4140c001e00182c00304102650051480c02102c44003507040000100003030081c001c2071143c2080c4480c00112403401081c131b40e00945841e0044a45038076011003004200c0000c2e00c10700314140a184004241106400c0480d0200c64068403042d8120080c209200014000100140e00300140544d011178035240030b00146018a01039038554000590603030b00d440c000c280040341c000c03d05 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 491740368 1250 491739118 491739163
    0x3060f052202060d09241b09030b0f0402041d0606120607090303051e0d0c030f02040f0b09030705030106060807030c021b0103150e01150207140109180e060f09 70
    0x1643d0301c1d81144e1151840a01c003003009845881e108506854200c440c222207a00500c100c03240c00100c1d880a0202c1d001c200348000c01c201c4042050b10101c841e400054490011400001c00308a518a103103504188060000902504014900d04c00c121171022650665042002842024a44070020140c0c54141e0409406d203801c01200c05440d03c406480001e042c030401144481403403107050b00c6c9200840a000500d40e41c7d00c07407052110000d100a01d030b4640440e10b05445004204074620030348041c1c80601610b08402030400d0841040c3e41c010085565040c80740c900045540d032800c0c02808001c01c0a1744583d109410103240113001c1d03494082c0d00f54210360011303154021501c2c0300786640106040a0800103200410100c41c040c1150150b00314001e04de440400010301080000351605502a19900b61100a502c400c01c03a1b034502c502c0200039000030010030040c06003d00c20040300c4101c0240d920f0000f0204406101d081c1420001c0b00c50000c0b00000300d0070080f09030018000c6440742810381500040c01c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 491741618 1250 491740368 491740373
    0xa080f0405270610020c041814010504030504050607080d020a02071805160e030a061a01090b0301180c0c050105040f1a0603062406030103061d06090307020103090c03060f0522 77
    0x40c01000f0f24a9104404000c45410654020300030200d10640103001808059641182d10002e881c14041c02c131008e901410004070741660602c21350b0300480c2c1c19a182440c0906c1c0c6010001d998012402c240e034400300401127001c0c400c02134401460003d8a0340c01a2819a00d0a102d20b910100807940c0e0000c400c0c20300f0308000c0403510040822304d5102540c1060017000780c102021a141c6040039100603da2441e1018026500c41c0180c03103620508000d9031503401302d40d10b420025042d400300303102d01c2c40f42484080c0a583e0000c01500300103401d10180c5003062000416444e050b09445096505461021884288205001540c1200d5192a900c008820150704003440401d41e101030051290120260f031121491020600c0b9687e1111a540100b80c5600e03540c490070214024440000e10200147c10114085031400d004030b02e10b8400c6040b0b00140d4101400f50300190041c024805003184c5007190301c2000b00001d42d451040003004005900700160703518040240051100584a0743c00c0c0c401305003031640d0b00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 491742868 1250 491741618 491741689
    0x50601080d2d09030503120f1e04080306030109122607080a051906080c09090601030203070b0a140a02010e010c140906070204020405090c03160915110a080f0405 71
    0x50400a880602c030380340340710302201c1501c1160402482e90100040c030420706500750702210b0050340004600d519586511002d00c0c030701110107181403108250000040e000c100320102460348070710068000300c1c002001b5903c400d8001228200603010600d41003c60303091910440d803212100c620f4640307040050038042e40241c007102c0c0051030b1007815910345000842c5a44100c10f00c07401e00000712420b008840c2c9030841d90b0b484810507468280201c4101001641e905400540b5504803500540648103e5080c100d1648150303106405410901218480340311489990000501d8280d40907400004c04200040c0454203540c0121250b60400050b042c9050385000001c040725020305c0210b442036a55000d510200e030103806550311041e48900080104000701c0c0000303004601c281140c96004d41d4168541209891511190003207121110110f40d02c1c0c2c44890107842098030403001d09080b941401d60a40d150703892a48205d0750821240000310b010046414512480da400d03290600c0d20654101c80c0289018 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 491744118 1250 491742868 491742917
    0x150c0703050313020f060a0903140109080405010518030619050711060c0c010902190e13080306131d010f0b01020f100902010c0b09010b13090308041704090504050601080d 75
    0x543c941a0001c046013150355405064000441c050100e60b00c446000038041d1410b19144429a040e11003500c81c0d0442c44410321808015580c0400f04d81e08180c1010011143c540282d80d40e201d14142030b1810402c2c591707003005104d11440c0f81085000c420f02100d80103c0607100b0140c415418080da500800b03403c91804a00590702c1104007801d181c58107881e40b9400c0c098000b0401c06034000341441f0b0741c0b43c14414800792503000e0300d000041031840d98503442c0341542c210340c001c50302a0400f034003400030800e6490400d0324174106254104c808030b070102280428210000200c0200d01c110b079075070705c0a90301140c45400740640d5a0740c09d0001d454825004448151100c244049102d4902c2d5910041011a0b0160121150890f0003018101d20761801c04000c50080002c0d498051146207001c2008c4000781707880c0111020301740e140e076a4000c0c0351181d6440c902000e0a060f241e4004070310501010414400900c01c15201e1800b0710002d0501d03502d030101c00c03410328460b9141d440803c040440210650401a00d191 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 491745368 1250 491744118 491744131
    0x903120f05220c05130908310b07020f040b090a09150e1c1e0c06050105060301050117090102221d090a170403060608030a03060522021608030405150c07030503 70
    0x45c007061000429400c010f03c03522800604805002c1850700c01c5402c0e50940074141d101c12407422a951800c0c1e200c05080c03592501c2040d2041c0000c100714030050030200c50b20304141c9400703400820300241d5540001c0008034111040b010380c5035200381000070300c01c01c00c1050008500356081000b400c082d500b91144c640541200a42d0000040c910701150144101030414603107500381740d4a08500710000c07000304004000741058620f0b40c20f0200104072464180103c03412210161034841d1071158130007504440640040511a265500b401300d50035003c80c9001001c88043e0f0190385074409402d01c110402600c030741c20f642c0e094201120381004a0404001344000c046c130381000822901c0d111810044000388541d0304000c00c210b06014000030b1003000040688000c0e4541e8070180704143d01c802c02d000040d804250114004601c0c04620303011340d0555401808104044c001100e400e011580741d80034168001d540485940d13000044d00100d410b0b5006121350003428505940303140090703a40300180b0030300018001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 491746618 1250 491745368 491745379
    0x3040b0c030712050a030b042f1e07030201230a0e07030b0705090306100608040201050c1603060629090409030302120c0a0f020114010303080711010e031306020c03060a0903120f05220c05 82
    0x8200d4401c00100352142d600c20384100d40300d070ac4040c0d00d03840d02980098408401560802c4440340310520f01030040082e810041c11440099a56449400041d01001d00351412500500c0b0000c03000c61450b0084d14411030198070f41c0c0c3d6861100e038050515103a4014510100380e03103260020322589910071000c68000b902440c0450711034550b18011030401c0030040c417021183c0740707100d000030403c03010f50071800449541c0c000e41c2300c03c400b104603004501c840f00c801071101ea000400200e801c0749410303888084164024503006041030b099024400d0203030790035201c1402809000c141c044149074441e01c0001e00c2c0802e44001d0008800c80401e01c4950001800000c0034409404009106284200188022015690024088413490240302c544039030102c0b0451424201484e40400d020b070000446130020704020700102947d59400480c60b00901c844201101085018055010b84200500529600c0e1100110006240c10003403882c4403070040405111a490303071a050032002262002004008495060300c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 491747868 1250 491746618 491746691
    0x801150618150206190b090c0d0b06130e33010e1906030b0f09040602161b140a0308091012090c0314030c03040b0c030712050a030b04 59
    0x10307000a429190044011040b03580c041c00a8140d00040541c0a041c20400b110041c0c80a25403203020703a9903220b03805400c0070004d00410100d0324550000c0c0845609081c0c00100030f80e181001480c2580720340440c0f903040808030b01c14402c090801c06c0d1b40344c001803541e40c0d0b5001041c0c040170510301c1c00d40103000c0340410b49562503a140070ba4082c0061001d0007030010008480200d032013001c2450a203072409240d0000b0f2400c0003094150410300c0b11070021200040560bc40e6640708da41d0040654000e0481c000740e07035654041c000005040240403824124100b1141d00c41a0500b400800b80d40c05c3c1091443c03240d00c00c00410804900e1001c22559015815644100c41445a020686410b80241d0b10b0840d0240307410401002c0c4100500d10344241c1e40b20355060440030038526071080c3c0e0390240b400e03204d10a0700200420805d14112400400381c2040c24001c2d030307003441020307140c0e101540103038114600462800100000c1d8503525110310801280e080b28200883c55200300341804144110010b0050b0b42c6a046 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 491749118 1250 491747868 491747897
    0x307090207150204030f140607020c120c09010b1206010c0f02121e150105090919050709020f0c010b030d21020d0207080a12060e06010c021908010b0a08011506 70
    0x40c60310b00d00100480d02595640d43c2d070b1504810000b0206410740f900d046a00313004d11860408a40c0501035000380d4000c0482010802c100304207180b00b9288600c480c41443d00e1000951034444c001c500030301030a0400c40d210072400c00d8580001100900090400c5004c0c840c0364002a940516119110740590351030030748122402c83d903440c0545410020304500205248824410000205209031040340744c0d40002c641d1760344081c0909880103403080310843e004622100c1e17108054202c25403000b4055003c4031490303992070110108a900040e13855881c810700240e0900081030900072882400b0042e07004242c1c041c0d151900034003511144103240c00c10080300c40c810712800920b8041c0c45078108244c4086540d040320f0314150034141d001c807421102068224140c90320003081c921441003122000b01a41c800c6a644200458914040881c12139000c039800012102c6840414400400307050030303034000a403c003c01c104101c8004207960001410b41e041024000e080030003400c0da07004071265410841c000103c0c04 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 491750368 1250 491749118 491749133
    0x102061b0f180d0501020d0e01021206060f040e0a05010302010306061b060234230a02130207080c07080606040e030d020708280305010b271314040b0709050307090207 73
    0x20382c02c0c16401507200c190b44040c0706041d0300401480080040821181d0401e50416080c1c0c0116500c00d86c02d900341000040e00d500707000e802032000c51891004245405d03110200d000740309209032003514695a44c2d400620440d60903104000c0501203e092404103002014210764050801042c0204000d40200d507040900405c07200040a80389410180050701032003403080500507a0700c50056a0083c501400c0c050340ca803207110245208181e00001d0200f08032103409000360140d070a1901d42e03e09074200310410100f6403e04c060600c912810b0007400126260030401d03443c101c40641024815481c000c85403e65100010848a03440c0a90501685030040e40c104407525016501040c0301040f148189a8080a03d00042e01d2440e03c580e2010001c0740d03228016064a806082d8a1582460f412010304070f0085101000d2101000f00400d211030300f00c060310410303051360f4085418105855800050000704020068030b44c7d8040c030180761011b02c50b840c000c006540c0d03080920460b6800c0b64001049014000300 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 491751618 1250 491750368 491750407
    0x10507021c0507080d18050a1220180a0b0306090c040e0f03030f0702011109060f0306041104060207051c021f0c06060f06020c0906010801051306031e020102061b0f 72
    0x7035409817031000808038400b1700244448901da20900f0619000400c0501d842d03007400d03047d0741400150341401a04d0350f580301c1344441000350180401c044210f1071192a51100d883c141c1c030b0081c401031810142042c0c0004800d4800d0000d00912a40080e0f04018003004000741d90980c0840441d804103140000030803060910380440c0c0000081c2c00000b040008642003886050300440c560345c02000a03201052030301056014000949078458000c2003c0c5a000303c0180207184c10240003400080c41c42040c04482045d03a0050380100d000da00420b000f000140740c00280440e4460095001030883e00c02c1d0350015030031080c840702c000f001403c008241d2494501c5004000441c42e07101a00304040c030340b1861000040c0c6401e1280000510842040c401c1e9400c16000b040c1c095030040c2c46800150f4280410003654407000502c40809695510001012915100014904046001c041030704001c150000901301000100400700019402c07403407000b08640c40088031113070080107110315200d030401d21400f81d41102c0c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 491752868 1250 491751618 491751629
    0x1309060207050604020a0e01081f1506081b0705061b0d05010f0e01060201200306040902090c07060e1506061b0d090f06020c010905040c0309020d030806030c010507021c0507 76
    0x400300e07480081040000e10302d0b002e14001c44407000401e43e07038402c0942e017035070074014455250861261702d6103940040d20b28240c4040000004a010b540080c250070400300640d018200060745102482042154000da20910454410b03055241000e151102c03a41c84801401700142c0d0011241c010100c2010714058030b139410324514003800913503134840c4202c080744c0d0f10707008503101c1d14070700f00001495500520079001c5011072200540381000644990940ea07800041600d5041501c9040400050340c2d01020584110410b000c4c0700c0d06c65803e8102801291081c80c4015402c2d404613001f0708003080d450780f04a80c88401194655501e210502c0756070344040005070b010401d440b4580750f4006954120b001d0f46c0680c0d0480d03080d030341401e0369018201c1c1e03668000f07075650f408544001000d1106040540001c4035058081c04c0100e0810341a60104120002440c0141c0004581d1820301110f40740a0001100e41442460040d0078070990380c000888140d018030960183c0d0307201c200c44200700b03d028080d42d0000c24 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 491754118 1250 491752868 491752871
    0x609031204121a150d140708030c06090a170d0212040503030708060105091e041d0a0c0906030b011205011d1f050106080402060706020405030105010315050a05010e06130906 76
    0x60b514160016658001c1208075011038114100d410f01c20200820b240c421031340c03150349800f03a144c4503060001d10381529a09075241c0b94117031881c6000c6242004039034001c08001e401556194200e030315407070401001a050179000d41110150b03401007a03c10048080d258a10b8120a54581c080451003000b0f11035107a100700c2a180e500d0800c01442004405148901a41e844407155035507400c0c01140d031403142d07c000c030341d0000c40d4449a810b00186403440006800d0040d00024a02d41c01c81c3c8000f401c40c1b80f2410308000f590240c1c0c040010810322061050040410741418030007142950f42d49040c100341402002e81c4c15026010100c14000b00350800c0010740d1450ba06440b01e550349811540d203620b903642d11a52808045006e0004114951080d24100c40300e95440b260386444076820482e69500a079019a0182c2e002d010100d5103a401384100d5000707522845681010081e51442c1ea01030701c8008215441403480c1c14010800320314045141640218125807031342400290701c02880040609400140449 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 491755368 1250 491754118 491754127
    0x1f0302090414091608060c0703030905100b10030203010b030708071e08150909060114011211041706060109051210021303140a32060420100e06090312 66
    0x12400c1c02c40241c0100d80f50015a2800d11300c0c0c0320109080003591050b0915039000e440003461a58204015020641c86444c0214001ca200e480c2c0340d150424a0030381650240c0d540f0404d002600e850381d001440548607040550940d813424605081c5030000038800740a002d10400080e030828410090341090b00d09001400074070a1358244010040d40d012110194450300030350003550686061600b27203108000000c020841c580c00c00f400301040c04005a18203050007076a000404d555001802001c0c103030306201000c562100e151a0311500440c10907812082c0c65000001031100c1c51b60302000d010155134050300c1b0142c582d00c4480c01c0c140707040138210410030840d10203d04070500300301c85281e440880c0e004081000d0b031010000000c58031040d110708024070003040c0ca038104250f001d0400b1a400c030804800c0c41d4901910560405d141443c0b8205d030220340c100c114844070b165503241404e400d0400030f401c0e40d45000d41c004481c40541019850480c241c420500414a04499941000018020135940c04200c1e01e8 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 491756618 1250 491755368 491755391
    0xa0e3303030304050d120605030307120c0c08010c0e04060806040f0201210605040e010c1b0602040302040903110601080d3221090109170c0a050613140304051f03020904 74
    0x141c0e07011034071800018035800146c1901140500403039054510040246103880c41590f108884032040e03102410034071095000c0e002c085141e90720a0002000c1040000c10751824801c0300615603a0b8001156100d140351180c14440c40800148240e03205921680b2880681071600050340c80d400003040e0040c40c11400a0301c0311b038500c0a500300004135541038a05004405035200745d242603503500d1009000140313524003170980720504a0300b0189042e00a410051510b0b441c0d40110741914207000083e0081021000c5900200008200541c010030080004c0d00414403200001080c2558100000710300b100340480300503900026010340c0c1c0a10b4008822150789040d0500790f07a4040008c0243d0380c50107ca000c002490300c02d011b006040c0443c3c0c1c8540740c0203138031140c0031a8104a03000410014928481c5001c550700040082000e280900c403a1004880c00c0c90851034941d100700c00c1409000740540081c032040002d0386403611001041c1c00e0900c60398101001040084009000340c0e401c0d258024100a0704019 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 491757868 1250 491756618 491756623
    0x9040e010608070515122406070606260c04020c0708060726100b0705100c0315050604050f040b030a17040e16020a03030c0c0b01140a0e330303030405 66
    0x1c8071401e84412080c0b8109107003400b075600441000d8004c1e441042d00007200c0303042040302858040080c07001c105202e24000c02140ca0b89d0031400e0102c41181d0f50303410500c007140c0c060b4031790343d450706080c0f2254030b500b200c05056a44178602c40c0b644074041d44c2c0118014406220601a00d0082c201c140116502850072040042ca070000c0d001ca1340c0400350008108a0740864810140c41c4143e0010700341c600754524142d8200d00315401100f00f82d80328090b1401d500221b142501440d10314604594001c58085450041d0041c46409544807610070310042108006680314814014004c06046800090401e40d0102090a0280a010042414011820060f1401015005030051f03c4491203452030700d543c2e9002c4096000d601a8a070301c090380c04000b1281c00688603800044103200217250003101701c00c51350344205040d4400e0300402290a02c02c0c018050905082c2405d000920016805a44034105545800842c040075080d2800003103c607030004c40420041181450010000360403a59a0326150511a8 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 491759118 1250 491757868 491757883
    0x3060907060e0603040f1707080c0a030f030e1005090102040305030f1207030b1f031b031406010f0504090c0c021806190503030409150b070c0306050f100b09040e010608 74
    0x7001c50b00b039241002841c1080010349110b01e0744101946817090700c40d10303a201500c0700060001c5200500b049007000058104d406400600319400007081019454030380940004008030140d009c146c0b80820340c0e101b0041c0000c40341300f00603000030b001806803a07801840340680b00e02d800250940c172001440340082800500201a0ba020501c108416a100c148084090340e0188003a954008660080e08230700355108040aa1a90414280011045101d41d248102c4c0340319004000c000c20364542e00c41c0c6500600c50a01ea601071000d11f4503030100b2a001c04040c1440c00340740211104241d481000741000c40c010324a040c1c0540d0000d20641038100c083c0c5a401c1100000c54070381707000c0c058040800e520071004030119400d40d034004001d14109828030340b00d40000c0c0749291500d1f0a51a00103400903049070040d0080030003d014004401c1c00e9400c608000f0190760010380121401d4541c0c00c10840706c81844c0c000d0b01c1c03c0e501e0a0302c1041d5541090000a000380c800760b010491103510b00180000da038000001c000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 491760368 1250 491759118 491759129
    0x306071205060a0303050306100207030b07091d010b041205012304020f042904090803250c021c15060b03100501020f100e0a05010e0304050f041802010e040b03060907 73
    0x502150382c1d400c083c000003603110f210041c0491802c2c03020035040d28001000f100020134910440300150381d2502c40114003c400e80c0c401c80401c401100900c088064403070000b100010a074808034441d458000100300c24490f500c0f6040c070f019540c00352041001803e400402110f0400f1101428000214140604021003034508074131482c030004a020060030540130f4803403031042440c01e080f1107880740c6200000000300200b0890348a541c4000c0350380000e821002a5000e0691010f060161101b880914042140705103406000d210307403140380c080141d4a00904411500d492a89144010080d1811032000100c0940c6000c4031401c018020915524a01c061403140c0305400305602d0542c1e5078401640c403902e14800e18082c40e0803103442ea100300103194001c00c1e043e240c00c800b2601e0b05076441e00c40301d0031900031244a020075040050100810301c0c080122487c90076045900708410380514820805090b407504c0001c0c140480700c2c801d5902a6203c0d40002c804440c06020b445e1146884c29007203861f00c0c10f50262 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 491761618 1250 491760368 491760371
    0x120b210f06090105100510210902031c08011a0304030507150218031c0c0f14060c07020315060105030a050a020d0c020304050a06090509071416140607110d050c01060503060712 77
    0x14040c80d0003510a01840c420b501e802310f1200040c0a110309502d403030044044495180e1354a2001610304002400003a01c3c60b02e8107122100e10090010422101a4400203110140c1081d240d4901813031400c8a410690605281d580c0d55990b150841c0e801181d00c0e60583c0c45803002c513983e85005d1644c10b5803e10440110181c400c4450103c0002500c202611503070300001c2c0988200000051003500c085034010302031700141c170004000032101403900c0d004590300b0555003c0816600300314142084860850703c040940c3d040316146c044002000f5000040044c030304903071503201040c103103001ea5040318039a5a00c600288841405c151010b0b41e030f44d0041c49218010402042d00068640c401c070240e8054070402803034401140c032180c404480747c0340c1c1c018402164200410404913a10703011002c05420921543c510410b912210051074201f440040456090280308001c0d10007145011800804400c038500b090790b01d0741030700700001c3e0050000b030b004241c052160750103001002c2d402469103405029944030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 491762868 1250 491761618 491761651
    0x803040b010905070c06090602040b0a11011b08131403030c0c0f010905070e07050d02070c09200301091505060a080609070c050a0b0403050d0912120b210f06090105 72
    0x1d400b401c03103004030381107030008484c00c142c1c0002403056004010039502a0101600f03241d26913900c0300395944403602110128001010308440c220007030086075004020904101104c8100c00300107401140c00030b10f15561491000c0c0c506040220b49103083c81814800c000300ca80343d180144102c0300d44e074064203185445201d501403145041c001405800c0025034410050200d8a01e015891400e04401904000900000f4030116240c0700c0301c0d1015054080c041c032008201313685040050303011a440640001c2c00c640800c507403100c018a214045a0441b00040000560459600f49034030207458250005a030165000a090107030640c0082250b0044004a6580314662141c00b02070700d80e0209480011703d1904001028408a1564505164814060306040d8034040c0f6141060080342c0a25204440800303154080c60fa60342d501020a801411520310200008044c000000b103642170489949038034071510782c024001c001c000b80084a5401262001c6418504041c69a01c0c0030b0081100c2901c1034440d8402e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 491764118 1250 491762868 491762879
    0x6030b0a080708030f0a1b0302010209130c09050907020a1a06011e1706040e01020a170c04120f020d02060d050105191805090f1f05010515030a0b0d0f0803040b01 71
    0x1152801c80e00f503a4000c528110f0825410b0205030010b43c2240180500c1608556012000d0200c3e00c140a210303600050341c07108150100025111380c030006400061a2070a02c0c3e140a0708015140103a80044400300e50a9513046404c82c50482e0040740201a0908208820620142e40344540d02410003602d85c600421800d00038102d16a03d0030072a40002000504082c6400201c12039840d04003001520204261907000310311403d985c040303002e200c0000c0c017481004450506000c041c41c2c021025070002807a041c542034609504150030313800945030000043e61a82103545a07622021241e45c00b401070f0341c41e420600001ca0051009110303a82c007a890070302c1707810b9400c80c3e0042004140d500500c5000102c92680381c40900501c4010302250742449441d103007100d440f600700940558074031401c4c400b1441010980c416001d554040e0700c064050f000c0c0100d040b83c0c9070b10807816242d02045504002079030000842c00075285404d035030b60203030401c000301070a0020700010307100030b40c442c6010f0228400b4a90b40c85 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 491765368 1250 491764118 491764123
    0x6090411090a27051005060408030a08060906030c01141204080403061802010c0f11030102220506040e010608101203080f10050a12060f020c0609190213050c1306030b0a08 75
    0x1443c034244007003544140b0901c243d56074015034101038103420880030540c0b01d0780850b03602d5000340c10088141c1d00119072020410b511003601c42d80000162407804541c10322001095685040b1b18100341449607009842103094121801d0b942c40c045058000c01c41800c05050030281c0b54058001511224100100001280c2110580b1540c0703e6042c0c0d103c4009035129221b040c89541d5142c0304482d10180646400015a003d0014044c0310815143e01c0070510602d40314003000120980c13100e4003561050004000f444284d5000d141100e000e400c02c0245a55503c800545407985500031480c0f68071400021000d05500c510303182d100340060500a2a1911401200d2000010741c4c0b0a56500140901060140c160031640791000a0720452001c00d448a40010304400c3c1d0704141030f000a43e82c0607004000d60241c04000c81580c010b804802c17505115203036004948080a038903c141c03800c03529500070503002030051040b1510ba03140300000100003500c030315004024044540d0034610428030b942002c612141c01 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 491766618 1250 491765368 491765399
    0x9050d03030f2d020315040b040b090406020d06050d0b1b0c030d090627200402030f060913052a0301091b0b0c06150d020a031103060123010e06090411090a 68
    0x44500750083d02161b010040035042e110549a0459210307040284070b03803034814a10780540e10800d0b0260301c0c1e40004052000b01c600b180c0c0028401d120040b45e04c0c02281c0301c2c401c0c417504401c20340c96a11401c840b80c8100e00f4584100341d00c107819484001040c4000401e03d6010300d9a01e4841d080c24031095010022654200010178440c000011003125144005058101620850204001e11035428000140001c4c100d8000311400c0180c10942c40400c601803401851180c1d21210112a4030001ca00c507448455503810748071001c0c258901440034600545401c3d054141c02420002d009124810503840d01c11080c007444071100c00e002603903500100d08166420281c2c0d400104010007403d80da03540074004148281680e420366040310710b450444001d611100440000b40d40540308254400c2d000b86c0034580381c11016846951240800040c005c0080324110340524200c80901c1c10903264081e07240010120700c60301c010a94407510740740481d621039031414050000340c85d088031502009590390004a0b4074402 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 491767868 1250 491766618 491766631
    0x1b09080607210519090b06100305041a06010531060e01140f0702090c19020d141c021602040f051e0408070501020301030320010c09050d03030f2d0203 66
    0x2d840381c41002c2c100d41d4001944080c3e00034a51342c1c89100c424445080707800b81042624801c0c402400c00c46541071660600c155140c892070200058070349034445410000d850540c480c5007440484c007041c0d4581c4a1030613039220700701d0302980301c20164010000d4210b401c41d005000030203a0401800003103c0e40110384c84503100e4010b071100171149108001c2c2c0c00d00d0354060210019003800074450800980c0700c11280398814070310544450356900c08030000302c1c1e0000c00c0390b400380115031040009496241d840b040540409143d1580d090700d51001184400e542d407100c080041290b48007003959141e90403032540e028481402920f041141b85001201310060307079401c035100c0880c16010f01c05c0c0440c0d80382440d0400da21900030b0101504048035561000c0c20383c0d0083c4e0064001516012820142d500c02ca041ca80590020100822405002030f801030601b50482c403459215040307101c500001d041c000e801c0000000c2d280e8404000d12010b900e4071500810008008248000031400100200d800a108481c00f81070f = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 491769118 1250 491767868 491767907
    0xe01020a0503040b1606090f05070f050319060b1207060e06070b070807140f030a0e03090a0501050901030209040e06071112030610091805090c0a1a0c011b09080607 72
    0x1030070415051007991140c402162401716001002c0302050041c49042d062501c200021450300d201d9041442c0b46ca02c85400803641100385050400550340c001840b62404548107051040c1655a410100c00510032000381c140c1100a400000380c045401154900a0b1384290719080645030400f01800342c2402070103001409152101e0100720254061594642c0c0b014040c036002001220560458005030401e5080ca4100d00e404000c0c844409007030300503400700a002c0c000a41c10042203c0009051501030700c126814000001655003169200e03804070384295001a1040c02010380d0346007483da8912003101d0007400514100d64141380c00c000440c402060306240d031640b604544501c1c042080b407000c010018818481c2c08400011508a10014040e040b84d42041c005800c0c601800c0071410100c0e0030241078030a440b0f928090100050b204019000002480e24403921003142111183c01410091640001d10740201004851907a2094091041d2261141541d410382c90f21041900c44081c864029840d0b10b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 491770368 1250 491769118 491769127
    0x6030e0d051204081b0c1f0804020127080304050907020c090429010801020c010c020f0d0c080c012a090b090904030e090106020d0212090d0b07020a0816030e01020a0503 74
    0x580000b4243e0070501030310b90f951a000000d103040c0b04542c940d07003080f082504281002c01e568038080181d507410b0090020307031040c21828010005c244510040c0b000f4107100584206401d01004031400c182507016404888503415181c1002950f66041445a18824a43e110018000920208240c01c00c0c01c4040d1441c0d480740c48655440b00020405c1603445c8805d0341c41e03c0383d02d0024404940c138074003e0040f5400140e5400000f402582502d02d45d1040c607065500c5400714503480c517000900d659000e41c8600c0e24040d121840d20340b03075003d8414a00e000126608084600c207144407070803089404c0e0403813aa8100c0400720341d00c0040d00c024000f8815520342000a01c8501918104900042e92061080c50100c3c1030024030340010780244c0f820f81000005074080160580d42c4d68041120304405211108803600300504540010280c80d801c0e200200801010008150038034000c2052680c0310350b2050f00d8944424517217403030b200402141501540041d05c0c40f403c1d0f60695002040603030b6001c2e0850080c6180 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 491771618 1250 491770368 491770387
    0x3021e0f01211503051618020d0e01050f012408010501030f18030809070e0105031b0112090812070e09040b10030c030501050f090d0e0907050f031006030e0d05 70
    0x4061490205001c0351041d58007407500054180302c0c40c84103045004218080c141917040061604004516030120014031500a01205921001005e11030b44034907005680c8080c030301404001350641030000c0c00c40d5803d01089c401c0c0d840344032440506840c5482000b4499544403a0401d110251129901c001715944200500482d40301e0341008060249104020910a6404c0d100c064900041d0505500250f0100203020420707800b40b041000506e2502070b05089075042c078000a80300c2501155050189044201d101400c0e4001d01004442c40d102c20000c000c01c050030300700881ea9138012048000d141d601c0324005120300c0e001c1c244441c03200001902e40222643d0700e5031b4115501c000640308522004122800100081038880d0f90006140b258001143d60700f4841040d542003000505600b080d80c0164140d021080d40c86580c81000c100100d9003075019440300035003511640300d4030002140300b483c0003080110883d042d000c240122a140e95041290307800c1200142e4861089200f00c5e80021801c00a0056 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 491772868 1250 491771618 491771627
    0x702030f0703030b0d08070f110301020a1e020f1218010914040f0e0d020109200d081c111206040203101206020c0307031106010e072a150603021e0f01 66
    0x2168102401342c1000c2e2417243c8032542150810202102c0c001c08111007401008110180c010300e41009500a42c02e2a0396032001a2801881c00c9916144200030000b4032140c40c401c1002d05121010602968561031004091810035403000c160407500031a0800303520450b5208201c0c01e400c554254091245200c00d00c8104009000e60030030680002d501d80c15095070400061110689000d62a000020907291518201c0310021000101c01c141140c1004d4903803868540d140000c070a00d6015041650304e80b60002c0055440456407141c0c50410b2030802c00880c0e00c80201c0c000d150114501c03200c40000e41d91700c801c11081e1b2004a442d04541c80e100c0000f0482c11008180d0303001130718070a4901500344034000055503d160404c001c241c00051410b40c0d840f103900010300a01d400340100c1c2d4003410140c0b0b02014041c000c1a008902941d1550b008102414034080020560300d6566021441d00043e91545441d01c0142c01c1501050303105d0803d505518204100c00e1441c4601484090034404210b03c0480c019213 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 491774118 1250 491772868 491772881
    0xc0803070308131109010b18120c010f11010c0c05011d0d050f09032e060b03070e0f102006010510080402150706141e01030b130f050f060702030f070303 67
    0x42d07064013a007031540707003075036540703102901030480070b8292511f030500701c00a90310400700e041003030f0b008020107090260340480118070721f48519021b0809082c0071001c060110351071103030030480490303d51808030000015030780405a121860b0281c002030207035441c4008004180090840500b00c5603001404059070b19000d5009041500c50b008071031400c00c2e480c0804242080358501d03400d1103070409404020595803e060001582c620707030340810409079003099081c0c0c00500c03000c0d002a081c0107480c40840303201e98170321040a111020181c41000000c94481016080c080382d26a0001110501580c1c1018150001405030480b08028070345000301f02180310990715901d0217807042e42c00c1b000340020020344800004c0102200c034415040058540900c54107a00c050b5805070a013241c0044005560000390302000c401030640c2d0701b24114181c55121081164200712449000420508a490303610f004c0c01800b0501c0c0f41d20055040130b4232840d64403208103d840344110b401320207152206104035004244254000c5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 491775368 1250 491774118 491774123
    0x20a0f060c03031b09170f0f01020712050c06040206070213140a05011505092808030a08010e010506070b0c04170f07050a0518060d3005041d0915010e040c080307030813 74
    0x4503d98400080c82c5401c00c3d80d0001201412780d00001c0900c100500c1c0340b0700407046010361400a0a01c941c01c1f4206031510b401410183c82001d010a4900079595041c4125240c080d00210820100310700c00c062001d5410120b409003c0d8502d820300001d50074001c40c4a031030012a0994510745420070403410001d88070146641c40500203c1c0720f080b40d951106030b10108014102c20002503464001d681030043c9031640c140c000c80e8032055024010001030300c1e00b4068405043e400030070462a03035950070070021540a542e0055042a03260b07185944000d001141c5020303031310400010780e44019224014000d00c01803d1003000e801503000b20300c0500460264100d1500100002e00c031500e55001612620301d2a18850b1000820441980d408403035000c0d81d60540c821078030a800d00509080c03a000c41c000318600c7c0d01091001e02200480041c81c01c074000c0c0040341518048404449895841d04883d00c0a4081118112080000c3c81c5003c6138404000098031b01c803d600d41e42d5181c3ca555030414281d40b01c103c0100c00c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 491776618 1250 491775368 491775373
    0xd0e010617030c010e150109021b1e0606030607080c03070c0819020105090d0509100e0d060501210f0311030d1e0f0225020a0f060c03031b0917 63
    0x109007015400001c012003038011006544541031038181508580c141540340e0015481011040c050007100c1101c0c6044411010340140c451860584460b4100440c0348070350f07076034003d0054065075038240c0d542413030800e101d040480740702d80d942c1c1c0107141d03542c50700391780c075201269010000810090841c00195030000d0a46454a1325951642c0c4a6105030081c0301e007a80100400c0d041500307619424491680c0c0600f90100030680134a007100702400620415a900d80512a00054010245d00a898080c02140090500303d0044a24180100200001c0c040c4e00c6119024079403803d02c40240c090781c00b5400d1b80140c2005007903515a907050760740c00c0030260700b5030513408140904442000c5038801c2e10010296404200d580e1200c101c0d10800f1290101c0d0301801e010306c144190b092819958680010300240ba010100004c01c15000081008070103a10020300c0030080300c0041805603124000e140039507c40e40702440704d5202294140140c0d2a40c42c80580020b000350400c0049140c60107516003008544000d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 491777868 1250 491776618 491776631
    0x2030a111201060602030702040e0105040b0a05150303030c040305072c04031119062f030619090b090109050c070609060213080a0c0b070309140103110d090213110d0e01 74
    0x140c0310b0075514980d100c14007507080403540c50b00b542014004c0d000c08524001c02000107160035500c2041c500d1010b4000d044180d42c503070009161600c41006400404002030850342c8034074010f1003150031640903000413251800340e400c00080c3d1740c40ca00d00c0303c1c40d598050120b81c0c60301c0305c42e260042c0340e04500800035070400c860b0b84944004a50180714008001001c07410b10a20101c06c3d0410304283c1e50a01c258038881c0680e5503c01d0582400b00b50110010503c142d40c503503603501ca1307000050042c1d403031102200c0305a0700e914001404c2d01e0180d006c03490484058841042c0340c2e9036034003407000704d40b812518081d04100410035140000c03004c0c0d00900b201c502c01c0c00c005040611059070400b0b40201604040103e500407107a880900c40c1d803100c0e10f00148031508e0203a2421200760b800504990706489090040350b402e05150714568081e40000540600414020380c4828110040002418100c3c03030a0340a61412001d10f0312060310f40c01100e0f0362025007421180751001901090f0000d08020640b0540e6540c0e41d003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 491779118 1250 491777868 491777899
    0x70f02040609021605070608070e010c0f051603050105060a050a0b03061504140f033004031b140d02010f05090a0302040501060206041a060f06070302010e070f08010c0c02030a11 78
    0xb0140040000810030b101018220b17180c007528007243e5030030000030300101100300f203459980304081d600d10540030303c0c1c8a01d0654452030443c80100d41088010210f0085080042403e00420103c00403603000b88004c0c0003544032601402000400d80c00365a8114000c4c80041c042e51004200840d005000030b401080c103003107020710000d8190000d81100d401548298102c0b400303494440705140d54207204a024110041c3c1180702e20b001c1488550b400010004491807000098039a041641c00654000c041d000c5007041e000521002c11420380148000c00d0030421031444c0d02d0074900c7d0406101541a1580501c0c0031007408241ca4980098040039070219184002000680300c60103580d0091030b041d0000d150606141c5000304061103440e000d82418254401080250356810a041801820644d14150784500f03e0a040f40034107412141c0c0780503441507407000902040209000802c40d900c0500810070044005d81c01c130f40014096101950583c40681c04502085c1c000da4110290300c00103090920350449032 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 491780368 1250 491779118 491779121
    0x150903190e0a3615210f0c0e04060902040c11070b0d060803071104060509040f030f030b060307080402030607020703150525020109060b0a080615131d0f060c070f02040609 75
    0x2011490500d034461000b07960f240901a1210050180581c64041780541c2182010040d12010b0016099a01600c1403500740240f0710340a130068102c000844945107002e05221019040c0250100d000d14602004409014890155401c1191100c07000e0000c4c94030300001c0344216000074841c040d07213555821001520400402c01030880303d2254501d9a11001030b01d0030041221441d41c0018022410b07101000002001e034a03010540c264541010149040c6004e000c9000301a81915541c02203000014040244c0d00000160b00c00c030310840803a4020b42d2511000c03626180240702c0140f01002c0d4114040481d02c42d41c018035400741284070340344201d200b0049142680c0f40c0c1c448001e40541d544010441c00e01006020b020f84842e029038680800519000d1025500c0780c1c010712a01c00d041d0544581041c0c0c1d81c1d500600a03240002010900010109651580f0b4680c4e405080c40c04502c15100b400700010808540d480c45641e50306202400c004140c0c41e0001c3d099032080049900984e40d40b404075405006 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 491781618 1250 491780368 491780459
    0x180c0a09060f08030901050f180a08010902030705040c090302090c070c03031808010b1804060e060106020f0c0904120c08220603290111150903190e0a 66
    0x1100011072803602d4036404500b4407442c0d800c6000540c00411181c010340c0d0b0082d0403036109a920449140c0c0c3c0d45040d1103040900003849c40409e500c00c4080e540000c0000054112401d658000c9080e103103800e6940e01003102722140301e001c610200301c0310303a0f08201518080409650004546a00c00c2c0f8102480c0d03200c00e00c940d8507400450200701d00a40c1c40c14900e0000601002901c0c0ca10001c00c80140548009684c80c00070350411090528501d0014081200541201e4a0841c000c400c0710030350f584a0001940b200d88965408000c1d20a0802e0030303441e8036003811494000d0340c00c0642001d10220f640c000b146d00510303440082d02d540c00d0402211203007030191085244d9860540380d0b18440346042100c01419215061007401c0da00e11412050b24404464115181d0704c100c007400d0544001c10000001401d008011700d006005045e14820042019000f00080071145220119100e9814280c4410360708020b01e44e0b40700d41c00c00c0a000c0d0038000788019010101d005070b4040c100d690701580994066264211 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 491782868 1250 491781618 491781629
    0x20c0109080406081e04061a030a06020903161505090105130603060e060301050405151b0c01062603030c0a110d02071514090d0606031a0924180c0a 65
    0x74002010000154040521070304485a8080c005500c4042641034481c2038004e0006081240c2d1440c2014000000c003443c0100400040c003503c500c0c1710701d4201400250841c1c6400345c028008c081030b0303204d11f2000031844e9059030f1010811410004c3c0784901241e081c1c1110340d119051101c200f02001d030801040117034500500160360007089560420442c65001d400140050303000780e0401301884005040850310071004000640000070650710800c10035440141d14440b0b10140310b0000309120f11030b5064018500b5600d20000742c04040b08a40300c420f515450101002d041f0740c01c00e0012640b0150480300601801c03a00b03280c02d5803140e2503c1401c5052203500000c0c0b601690100c0c07002c01c040140d1b010301d44000c079083c1c2480303000d8075020380d42c45c4003510a20b1043d030b00c9902d070307280850300700070340c40e4841030182d41c01c0541409404032801c0242e020810507102c0a03024460318110310240d414040c0d0034100151081440307a12900c03a000c610010404018240c0707060f010b640c0a0f0341c1c86898100b82c0200510 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 491784118 1250 491782868 491782883
    0x2d140604050c1e10120207060e0c0a0518060a09020a02100c0e03070b09180106090603060e10030305031806070c110901080309010513150c02030606010c02091306020c0109 75
    0x3003501d001454070115900e054011000b10b40040c00e0b078814440c48048500080d1180c100c000032001c81243d5150150420903406403020800409010319544207901c4440d1080488807082c1c007040401125800c1486440c1d400b181844a504e0a9941c4800054016401810b81184603450701c958070f0507604402440030069101100900718002e2600804d0340c10606030901c42120b80282c1c0209407a10310324000c15600b91000600300076592280500543c100012201c40280c5507103d120080091071244107034000030f07040100c0410f11040c40b6850303600514820807286019413543d0390517213417030704000d01500d1420029900ca0910241c10302251380b0651640c0d030303080c0c501492481d20f8940841c602c110b0f01c1c0126040c0c0010300c0140000800c41d02d0030346090a205413249106001c503406000150084441c4c400c0076001c0b0414290031101d02810544210207550700340e0b07a80d00044841c1c0200304c001070340c80b20124022403848000010440d020340d02404005d40b902d80f020a4040c25a040840200c039103d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 491785368 1250 491784118 491784121
    0x414040209060103050103020a170f01060f060809031801080a0b030f0309120613170c0f070302100f02120c0f03040f030b0603060f0a0b0a03050f0a0b0a092d1406 71
    0x1890801c0c5142d62100c000d08040280d941160041141c000d554007036221a07180c0440c1d5245102c2d02003088090f040e01a400a1200c01d444d00b4003094451894854040441e0002c800705214460200c107a03003603032501c0b0000d0305000b0340314401103c0000b8040c00074a0071a5480c0d401c0315546c2c030140b21a06003081da110041da5225010018030100090310010012290409002d10a191184180b106485900701c00c484108042e031502c60055881504016401d5210310307080411000d002090440441c0d0003218203d41d0300c020704805540451100b40c2040058001288001180c01c0e0180641000b10400084074001c42080b049580b0350360154000703c450010740b000410402081695140c0d000400760003502950400c4d080a40c10440c0c05030044e906541c030340440d41400d48600d8400001140c016003201c0c000c44003110250b45411101c1d606a80c4244005d00082c144001c5028149045500c42941620850150300c2c4800d5100404e00341100fa5030501445004a40780d450100d041d8404a0b0291155 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 491786618 1250 491785368 491785373
    0xc1a070e130624020a060c030b060307030905060a02040e1807170a0c1212030e1c21050c040504021c020a022a01050909060406080f010c020c192102041404 68
    0x410f0420204035103814280700c9101100d0b501084000c2141e5100c040852104030058050b4082c0c2440c81c0b050350400c1c400300401200c03036416003044400b24080e40581d00c55840b01c41100c01a03105a0203080042d5101c18003007100d4540156501d03c01c0a181d0b029981d58603245e0300110740a40b4204501d0144c0c2e0300c4200c103401401000b8205400400804001d25010317a03243d41c0d0440c02c8078103400080d050641e100410380910b9000d11081c0030340c41c0e180b41c62007601c40c200c80c8068039561060071034a01c80c10500f0741701003400c1c2003846402d0140000c43c98040c100362506c8100000303980301c1c441403000f00305906046084082580080c00030800ea54000d40f09103100980740c00d1180030341d445510140341981044030000d903048401c5851125007510340070b060781e0300c1a01160240215600c1400207108110f402849000194020860785036580c3c02c0c0e4020034054820801c001c185212034600c8107a000070201305030150740c0182001390525511400c10b6031003a400142c11a82e8104100c2d407028041000c1204 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 491787868 1250 491786618 491786639
    0x81c15080c0a09020a20070b0d051f03080301050f0111060c070311030405092410110c040204181805030a09060e10120f091704150c1a070e1306 63
    0x1d000711030b03804c40c00c103005500002d00e0103506c003a41032012415030103c00c01d44074061044101500209041c00d80c0c07100210a04c20041000716115a20301110402c0e07440c0f403003441c207011422039400030501c0d030443c3d08000812000201002c0014140910442d42440d600000d101d2170303110700b1020111907200d41413801c1c003030070b1601d40e208a02c0315500100414402507a44001540d0400d4008034241000d1100240000341d003086164a280d008028241c208a200d922a8407031943c1440002924080c03c0c2d25010721084c0d0140317000f207500c00c03084520003424090060f070100040c0c030b00c0090241c5020209487d8a410750780110028400580342c400180002500000052075941e4191980003501000407001400d00d040180c10150080d2140700b0086860501d4000306035032030b04065102e4100301503000303540307250741b2611600c501c0000c2808010301440c000c182c504200f6820203c07051000603102400c074040710004260406001010446955a031542e140d502c45003800e02800260003403d10b0500d24 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 491789118 1250 491787868 491787889
    0xe060109050105010e030d0f0e04060b0c1b0109050a030f020f130203100f05090601080403181715060a090c120e0102030414070b0a110106050402190f050403081c15080c 74
    0x280287d10180e1320080761544a60001d405a00c9071034400f1004070040300080192005a0284161354000715100c0001c54000c11000300300d45c111850380389030550010054416031154800d842c4d204035000c00030008075071005048803407a80300070490020b5102c803400080c1c55403100204400419404000c2003c0c0080d800304040c00b9001d140625080b6a00e020000b0350b8511001f00b0f0141000001e0001c00c04040c0140794940a074401900100d543c0d640718228008600040c507c1042603109854880201004001450740076000c0681010462810a0003e001070407101080a0030400c15540c20b5401e90140e00c514100c404c1c01000150b680c1c1011708101d20310042c04009c2c114690040c84c001c0100410004c21a00b00401c0390810002c0d070030f0301028090040c109a44a290400d0002032040020002c1911b13174916041c040c0c480701c3e102481603a040b1101c1c0154000201448801c0044064172860039045050b5004091004a003d18000c903200911482690040441c3d500207000c4c04d03001d150420030340 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 491790368 1250 491789118 491789147
    0x30a0909060f0308042303060c0a0914010915140307050702040b090f0a0f090507030c061202030c040302010507051f0e1207080901140403120f0e0607150f0e06010905010501 76
    0x5050366411521081034904c917921a011000080118005d001c10030400001c400344002400d845940c0b8003541c0602c1e03164030803040f10b40019182140030030342c429407008041080380107950305080d142c03c00802c4070048d00e6804059090100d102c40521b404140d040007548580354581d100c1c0c0c1c031100544140019640e45190b000d02c40e000c1141044100f40c00984040c0e0701401042010441c5619010842c00500c840d50024180d03015080010091011079000076080351195603d1494002400b5041c0c0101d00041d6000031910710200401c2000d903209901801c02c0500070020740b000004040c000b030500319081110022980d03100c2c1c0c1c0e180304801040c04000074a60031403840603e0540303070b03550382241840b48000303203410710015501c0080d001040c801a1006103900c64200615100c0c0d00102a0540401200d03500001f4854803a00c10203081440544130103990044495000d0341e8204c140d4000b44c0080d0508144847d5a10340d000c92401c1c00b006003900902080100042c9941400001003c1513040443c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 491791618 1250 491790368 491790389
    0x21b010201020a1413050901030f0c050108040302060c0d0e190302240103020904060e0a06050a1802300d0c020a0608060a0909080f12070e01020d0e120f030a090906 72
    0x1901040381c1100c5a403100c8011003030308542d6a826032801d1503111035150881d541287d00200044200100c0c101d01d24056400350080303c1e00c040d40c400044596640c1201c00400603040307240805ea8041d1108050203c9402c481004150f0003a0311461600d80f240660018410703219030100c9009158050140c1c01c01c40c14020b0034003144090398144101c41b52810303c00280104c150708000b409028160b1b0040d08140f46003003e880390f030040750600b0380c050001503c1c064211460260740840a141c0030794041d4119902414281d41c00c034004410040b00d01800d030501c01350042c0d0800d00178058070140403844082c0b103540c440440da4003a600604c650041250881310602082609008066680d06450404c0380e11112c0f002c51070440c50300d0400140c0c06900b0300c11a02140200301801e58085880c0800e120345440d95800a900c0d110000484c3d48404e5200b420300800c002c010a40100c2c2854000300e40c024034020212400c00031140c1d2072900c0c540c082c5c5c2c1c0070ac00089643c00280301c1e800ca540103400041440881 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 491792868 1250 491791618 491791627
    0xc0a0305150f130906090f0c0501021c180b130806010506070c17030904050a0e06070804080a0c11060c16060504030b06131803050309010c0908071505040801050106021b01020102 78
    0x452542c1c554014941d10a00319180c9503160303201c050b0001406a58486014080000d09203001010101400d004407081081c020000c10994400100418814003000c44a000350144901c00d03985003010705408034080031a55000f0449a159000a001c07201d41500480c503003903c0d00c8621030610b101030300310350310480742003003c0008294004a10000c0d62070b040703004a83e4221550f0344d10f155200d404c00e0250040d003400d003001682d11040d0b002280781c40d40c00099405907034444404581c0721f001201c008208075020312958030b04078842e074195040184140c254803441111f041c00180683c004503494407455000c440085041e00d0f10044200081165061050903e820f540d6492a032040080a46000e014030038107900902c840d0790001845d040304200c42c46401046030800400035401103503048500d600300b000915500c2d10604804084601c1d44016040d0203007000449090b404044c514002080420711011644040070301c5803a008203a150000c040010603480f4041c0c02034106020a41503910600 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 491794118 1250 491792868 491792911
    0x20114040c090e0f06100905060603041a06010e030f0706091508011a0f0705010c022104050f010e0a081c032a0918021e0a0906180e0c0a0305 62
    0x44151042d120084004180340389090340203403401c20440600e18081c031070302c4180584400180700080540394050307002d0150755500c0e01402440d11040da001414034621503002e5100c2901c00000316000281450800c551004040c00289050400c004401c03483c2c00c40d24042120541054200300248845040320780e240c10350820146c2020014490101070040c4a40b48038501540141242d015107881004c00e505c45e80603051081c000d041020462001d44902621586808150301560708003c009504a51900f800c1c88140413014582c3c0300c41c18144805064010155070b20010000301420b00c001c0104041034035542c02c08400f000d1144008149890009010101c1131401a5100d070f442d0455503c03018110100402c43e032065540c2e020b604184c245449211810701c0b030340c00510303810003982c02a801c48248042c6140c9075100e1285c0382d00104030070380400c1281368092170364507040c00b03271010041c081c1640c0c0c0e0a41e4501c42c0317000c4600001448000071200403481d09403040d6034000c224000d10140010b62003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 491795368 1250 491794118 491794133
    0x604020102060f040c0f0e041203112205060c0a120e090a0c020f07080f06010812070b0a11120106170f010b0f0c0106090b03071502070b160f05060702011404 69
    0xf030207411101e9189000901030000c1e0403d084003d0080540d074440c0f0551b40d861100d40c03d00d083d0b0b400c5070007440015410383c0300d5100340114000340c20180083c91903e4402c920a03000e48800c044504014000e41c940090703150f8404000d040040f25400180210b00840e01e4584c6801140c0325490302400210b03544007020362146103074180d0141c401400007038004241c040a900d000c00c1e101503c4002d2092940114000340d021a12000e80c1004008035580c5903254502e06446540d19409000580028440840441d11300003040f5000b41c030b50540094405100e00c0b90395043e03442100b0b181d0b02135100e0f10041024603485088403140c8000c0340103d00140c01c01c1395184002c0b10341886101401a40450211804d84502088a00354111803000700304d400e6031142000013078014486007034480d010388000082c46502e061031840c220241d5070702410701213081c001e01b044c098003c101c51900810761800030200142082d12680a01802031004085614103504024250345869540c1807000460f20244030008181 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 491796618 1250 491795368 491795371
    0x5040f092a020124080303070e120f0109030e0121020c030d020c0106080d0906390b061e0a030837081005010837020c0d02060402010206 60
    0x2980481c104074100c285072401151403601e8040e01844120030808150154407069440b6207098042c0310051840c0d0124101a41c0f6205050b902c0c0c004100080300680700f0181ca00c01d983c2e00410391291607d0390400107240c052860300003c4169900d400380010305801824510012400746094142080700d100b0042031007950a0312602c0180e00460050010801441680d0500004940c110b44401d07100d00e0b4035000c2c10071441140c23940e02035103058100c0b241c03040401009540150f1a02603248000140308034850f000306076a45101451002c00358015601b03900105407a501400410b0001e06040041141c200703503c22284c050184910404042d90700c0b00342c90101104e4011242c5a150780e0041c8129208410a200403559510107140c40c154808081d924500040030707644d42c9410700d41e41e83c022501408503a0040b1030221710310000140210044c81608604400600c1c18095040071103c007001030110060266090325402149084031000300708014201c9150f6840180040d040c5600081d40300d1b0390 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 491797868 1250 491796618 491796629
    0x1090b031906050609061c0b12010501030b070f08010e100b040e0610231b0708250e040f030c050610060e030a020609091b0708220602033103060207030f05040f 70
    0x7ca8181101d095249030380b0641008001500b10020801101c40503802130009020440e02d121004002c101180d1240721100020b41c019203d600359030342080c540d4106c10000505841c03000180960100350103241602900003400502d00234070362410407008112101011103642c06c20031000c0d245032800500c001c10240d1410305c1d01c14865035038000c00e40a6410302740d01e04900a48a11030024006803481d000292031030410080c0048040c48841c20307240380702ea05158801d5682000c201e80100f80032444452090898600ca4109103581f02200c2d070b643d5041c807034221400c110098003003104000c06600488084c0070b10100324080c00e0000f02960020740c0da4006c160000b4014080540040e0001e14080400c00e1035240900b01c1c07a031503030100d2400e8016540f1460400c00100505484542d2140e0950a03c60565800c3e80141d03040c80600f40d0007504402c0008a0161307105003a05000926106902007400954043c60001d42d0b07840c0d0303505018050202c0b00e101d00d000c10004010801c09940e249014406490 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 491799118 1250 491797868 491797897
    0x606030a0c0908030a111912030e0f06071107090e120a0207090e07051203030f04032111121e0112080705030a030e0705040e0303041101090b03190605060906 69
    0xc441d0100300c42503641074000007540c0c8400580070840f20780001569101c16a03500840b055089441d070074802c81000d0b160000e10981400150400c203d000340c1285d0040c4025104170b800042e00c68000c18600030060340d907400403841e070079990b00c8020801d2141c0000b800d030000061201c1408001c007181c0e59070054262035101c600100746010180c0c42840024000c1c0342080051110b4989074115640303c034034a00c07809124204450342c11041d0754011003901d219540314038001200b61b5503903e050340c0d01e40070345a5803808004103000d14040e20401e44104040e5108024006440e407102410b817441c0c4080c0504600e400150600049081401314081d0b68107423508100d16082080b120b142080241c0120340b40100309010114850010640c942e02072402454208100c8983c130f592603046c013044400c12040914150000c000003004582c3c4a0840004081c0625007049030551b0303940310000d903420603145443e0000d6401d010204001d513a00a030409001c04841072441c1c101c000b0002005886141d54201c00d00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 491800368 1250 491799118 491799131
    0xc09020c190302160e150109050d0303091b06050301090b0a03051b03010f0c1d0109140609030f03070302100b0a05060715060e160306080c011403040f06141e0606030a 73
    0x61081c40400010325004605584541d1107100003644100200c40001c12010051b00e03c10456114000703003003c545000d080e00300c040165481c114007034420003c0c20b40341c0481500c0242060300038107000e6001444240e40d41a03c0394100f00130101521200b034080381c4280342600c4140701003100400da10b99409802a9100901104d0f140880e000d0000c0c1d1407992130b8245446040c40c6043e4000e441506c0b0540b420042c10350000300400103680924943c0540100020078a41d0380080c1c0c144000101140040102103925600304004610310356403020004030010b070000d000a000f800340900441112200071240c2000e51410007010031603034043d4041c0904202c1d40c1880701c001000003940920003a20100c104041d107494040700d800c110760802c65600e40000c0c0b4110000881c0c442c00304402180340c0c4169102c03564030b10145a440d8040c3c002070001e540c149003944407900090020303ca06424041d90032144429032419400f03000401c0059468200c048030540200b044555842048070f0344801c03440b0001604 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 491801618 1250 491800368 491800373
    0x9051005060f0a121505010e0301140a0f02090a2601140406050406020c0604030e0a08070b090f03030c0714150712030c0e030f1506060f04050d0f02060d0501030c09020c19 75
    0xa403100c0000b078505107103005c00780748913a02e0249140041d103e0a0b02c036040c060b06640309040c209d4805403d400d1007104a24040781030241941c001070b400812a44015040c88000f0780000c2d01d03101d495103d0b00d001803031320180000501c0b94031000e2820400500c001c02c912103000b4104420700c4401400180380341c1c1d5078030004040101d40e0b4103035981d02d8411400c4450601d404d180240007411007100d0b40e407144174400c00016004d0f50010b03141b030a940034408100d06040c2c0e04014014207407000110366605001c144100c04500c401001032100070501220101e43c01650001404040c8217040040b0f4010307541004403e011400d0710004840c4000f0306c2c94005a4404041c0049070762402c42900107034503002c1c82c100015401c0000412900300203440f205029151607440c01c0100a1040060040110b50240070401151a001c50450740c094011441c00c1180100c03a80000d95540c414840203a0742d569410060091029929030034000c0c2c140035404524041203104082e0791429a00d0101352000140000d80d000c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 491802868 1250 491801618 491801627
    0x6100f020615041d06040204181e061b02010b040b0a080606280e150d12050708040902070f0312020a09050d080c0f030301060f0509010c03080601031b030609051005060f0a 75
    0xb06110341e880c01381c0320601840d1540da1140803d9905a11540c2004900040520f00d00201503400341d0003510b00c0d0020b07900e860500303451a8820020b8032229a00c0c52510055078443c11001c0002e00654000215210004100300c12122501045c90259a43e40005d104104002464030380082040310300b038000c0000002c2526125150000400039a2074104001481c14000b03115a405454069038040c2c059170607805000400d52922005095081302e0107003402e0341d5000d400200650750040e0040d61800e600d518419050340d002ca81708556a20208034800c0a1503482138000c450b1014043c8103520b410321342100100002218020184600c3c0b04801003410441d0701800c0b950140b20481c1074640d010150b4a810791250024807400e0b01281c888500018078a00c40c100310790702e03040161100c206110650320200c0344810010701903030500d907a401600700c0740d4400241c902203030125070390007240301810881e0701000d94801034000c1c0b403c0e44807614240070954803001550100c0000348016511241a0f49080700c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 491804118 1250 491802868 491802881
    0xf070c0f1403070c120f240504030503010905160e01030b0607061d0f010c050f0d093002060108070b0a17010f1a03090705190305030c010506100f02061504 68
    0x40c5100030744580c1c1012a400032002d0040c0d10300403081e84489542d1000c2c00810000a460001c200e440c11424070000218011410f50f201f046140032210b401e07003142a2041200d2003640c0a80203d00040010803d40348980542075100c0001c10381442c41e200b1254001e001c1588014406042c152213103007024842d210f40c019504d08a4020a007030000001d002d507100c0c07400d001a000340065008410900c241480140503542c0741940355981c4525102a8008000b0f81d60404039881c0301550321100e507180440c080075070323a2581580c000f00342c62400410512054142e010240040250b40109004002c5c0d0f10000c105503003200c10080e0780a69441000008540d09110020f0205040c1c000300004640031044100781425541041500c240c0c4030f981c0c0704102c0702c038041120004072961106d40c0030702050420f00d03c0100c03941c40c00e620790a012910307a90f8490640e000009a10940d81d51070003000158a000f504107440c00e12142040081034085920094035410300624005e00b80345d201009208540b0740f6070114 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 491805368 1250 491804118 491804123
    0x60607020306060f060706110a03060f031a06180a0e0d03151206020c030a0201060602013803010e0312060405010e04050d05030c1303210e03070e1803030f0405060f0f070c0f 76
    0x10000c001301d00700240c0003504040c5049c4000f0340761501c0403030000071000409090700d40000281c2c1c4802c440100300e080d1460010100b6410a200f6440000c500801c00d410328040d0b0151038001c642c043d030180c0384600c1c00c04443d00b1032042504000c1c6808520340410284402e641c0010300c0c070304140500f418403d002c0d01c6407820f00e508500c00010b2860800748e06600c81c0082c0c0d98681c0c028041d114a103404041d102c5e0807445400c890503802c180319042c03800cbc1d650b442c4028034000f400101d015030b00d074003001b03046812030305200101b64000b8040102902c2e00340f0601e409083c000040c3c05880c20f254440c29528040c0001910a00c41e0000c0455040f83d0000242c80310038240555411902d5201d1400c0901000100c00c0b06c081d5050703516409251500841e2118441040a4010101c0b1490090712a20b0660094000e4540d42120305c2c2804201e03400b40019449243c4648540c4a981401d141951a00710005c0c11500d804171040148200714080c0b1582d15007020a5180c0300a0172881401c080e068070031240d400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 491806618 1250 491805368 491805371
    0x30209060d0515190b0a060c050c03031602041103130f0c0510112e090606050604120b0c0705030a08060117042a03020a0323010e0114060607020306060f060706 70
    0x40f80150741d0441c02d00c1548011311400c02d0141c1a186402510401c041d101c1e402184d0980074000b0718405c0c4801045a80030b001140c15001d01c50300840d045a00800034074440e51040c07203850042d1b040901424111300c0c19000d4040c81d601d004909401c1c5600d4842d001804507444115070300600000700140000750030001c0c8104000300c01c0c2c520150205203142d08002c3c0714000d1256180c0c80d4404090358200400461240c112985250b0000740010400c14070704a4a1035030b9841c0c0410701d9182c0b1030203000a410b03842e5200140000381d00b403d10386903100078036a9090a50410800d07000410200960710803980d54180b50031603485010040c0e503c4070542c16a030883c190210100704c28844050141140c0c1140c200258040079103902c02c40454241900010390050b00603081000080c0303c84120260079108201c1444c1c074041c44848650a44d02131100981036a03440c3c00d2010b12010904025941008045035070728a810100d501103915000c000f0800c0e480344654520300c06503529031f142101c3c60544e20010 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 491807868 1250 491806618 491806633
    0xc06020102070b0f040c0e070225080c0a03030c0b04020f0405092506092d08010917090d06051b0d0e15071403040c12050a0b060613030209060d05 64
    0x500038002d410001056035408205404502915100000301c1d014642042d036001c02d0381d0500c52400001c44018201c1804c41c400e8100d480c0c41c80020501d61155011a04c07140e941d41880c00208508d0450501c0d0068031440c14201c040002a0b040075580d000c1d15444119441c041e501c078000908401e6208180342e41141c10801046040580410000c083c01c00d00000003003071075030420314079142c1c6200340220408508506418000240f840200400c9205a40d0007502c405043d40c02a1025101d907034400750706031f0745804601c0f04000541000d602854011700750a41440341710702c006040001c410201510a0b69108081440300880152180340800840851a510f280ca054020002d081440c6801254016000703e415070094507400640201840d5988110400350340240c503403160b002500490b4803a141c1e07400010284074400541c01850b000f00e010b06102022420180c02510005000038031854042004000d01d0a29000c0740081d80d0b01038480181ea69100000304800040100c0094150702c100c51 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 491809118 1250 491807868 491807879
    0xf050c1011100509030d270812060102061006211505040b0402030606041a09090f07020f1507030b1305100303120603020d292505040f0e0c070c 63
    0x8118420300d98400080714a040680c0010030100c600968011003545c0040000180c40c0110f904004640804c40810801d04c0d04000701081c09488034400841d0402d102040d1b001d02d100c144810300b82e0001081c0080c2800e840d003c0d49450002e2482d019101c1031204030702d441c0c40c4805420b01d0201c0c1e1480c0c41c0e201082800241031140801c40828401c1c14466410407621401604090080e60b014040261101d800c0c103040c00e9601207aa40d03400d0f07402140310340a11205000f9a204041d0794000c0401d0f0b1a03a24441c10948002800d107803010300b808106a00003142c103c1e540e0001184103900000310311340001c2031032080703001a000c0e448404008100c94149401e10140c0109070390785c001100d204c0c0c3c80e48004215800f031481c09407229840003941c4200a03005040128221190780303030151003001e00140da0340c50015178011842e0000c1d10b284509404901c4a1a4902490080c1d00103042e45400e000d41068039120303180c2884c1c105400345842e42640c40c40032445c0c0c0c0740d005043d00e1b81503502030406944192240c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 491810368 1250 491809118 491809127
    0x705240915090f0f090a05090307050105070e040513020a060f02101b030c08091b0d1203151e1203050c0a0b07180503060604050702070f26070609030f050c10 69
    0xb4014144a2095210310a6542c0390160354110044005842038800396507200014005010017084c90605d80801c102c00000034200303118480c441d82c0a41c40d5512002c21a6040c40101d981c000e0012861024541862006d41d0307440107a8000c03100c2910b481590702802c400d00b203041c6142c07810301284440c1070401c00d4402c210700c100f1240340d100c55603904012490304018121060403081d50f2200356030300301c5c819003c0d1900b100ea28600d207000c3c002c0c2c00342d2460000c2d56500c40d001c4019400a200003a51925141d00030141080e12200501581014143c014a84020180c42e586980b090810041e00c0d02402d004250040065a00e04089001918420729140c140039895010880e80400056013401c1c81c44a084c0d0800480d0040d240090020300c01c2c0da507034505010007000c000d40748d00154170034481d0005288401402a0018065640c02110585682c0c00c41d030b0000601d14500085a40110506000040c0c0c4014448222504044c600d0750b980001c0c28194103104040030341a40100b0782100b0400d41d01d070031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 491811618 1250 491810368 491810377
    0x40818030c030a031d0307031709040207020d080d11030633040806151009051915020d02010f020309061f090c0e010e03070609140303190201050609090705240915 71
    0x20f03140b05c8181002010561a000c041c00018410388a481e0440001041640a08040c480240005240141540001e5410f5090701c10446038090b0008110040c0f034098040e0811003460100c07a60b00b10304160002806010290034003048003200c00c662030b0803e68501100d2800314125444461780e594031a01c600361580012151f1824120001c42c40120303900b03000c4a0f18070780000c140d6800e07103c20f040004216032401d0150440803a0354844001160880c800c2414040d04007031900208a800301c440006403d444c503c0d4045440ba61051041080114011401030342c021110f00b1041001030300c9001c100f0030070740c00c0e401814110b850889525000e5800c0079588180ca0030903216028854004000c0680c2c0d401e503070080500142c0014000c202c14540804040c41101d002001d0324104082c1203d02580440400c102000507034460342804914182500b445812800190151403494145804240c01c69041110010010141001382d6440320075070040c1d80d082c0100424005088a12216080c150b822 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 491812868 1250 491811618 491811647
    0x2a19032003091e1509010f030b040b1201060f0504360b13020f0607050705190306050a470a0509130312020a0e0d1103061806010905040818030c030a03 66
    0x4c40c1d2221042e12880f0304140c40326043d0507034070003c012100748811406804070032215a0060340302c80002120369901103c01d4491968400005035441c40d20402c0030508403554403c0e03021300c4c076000482041d904140c000440e500c0c114072036008082d6003642c0a221084a540018041d05800c10a01440c40c140600d0060054001c035555400006d4250401106101c0e50500134800d500c100c4080029041000008000d060303a2042082070300c0d52929410251402200c121100d00e0b1340313a1900205604038080103011000e6103200705800d200380b031080c01128000011200101c1c4244803940380c0c6035910780d05003018141c045c18102481c141984480c4c0e95038036210007180841c80c58603d0130b40d1074000740b00359401c11030a0f0340e450710003070040c50038002c1400c80306405036120240002d038480380d51002c2102e24040e0605000e80c0c0781c000c941d000524103041d810b800a100303841c2400180400315a0f40380a5a408011600b0201c06040b100e1001a2034030b00100003298050151900100506401c40c06d220000c00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 491814118 1250 491812868 491812879
    0xb040201080114010804020103090302030405040f060f06030905150a02090a090e010e011803050304020a09060b0705010b01030204052b05010e0d12050c0406050c032a19032003091e 79
    0x1d032224440800f000070745503103078000346901c400100550301ca500011803490103401580e00c0c1c0394460300450700390b60726044008280c5460b00c0003040b12800c1c3c109083c0040c4064030b8104800c1038181e45882e11004c881030034400d850703000408504c0841d0107904803043c6d09402030580071581c6c5e95a054401820010881801d40e5103010407a098812042c001c00c0c4c0072013008800c804403210345135010f031050340002c1e1080c0d800980311540070654507418482c0381c015105500b200c944a5407035141060035a03006110840c10036005100030041030f114400c00d200141c00500d408031024410180e016400722403c00d025205600303140e41c1d80130449020410583c03001d51681d404028104000621701950000d9914040c10f2201300800c00ca664814006800d10b100000c060741d20307000701540204131102803030010b030000c081d10521700040188104800c0341d8039003810340050100e050b1031302c010b0712a028160101c05030310b401e00681c030030024042c01103e90b0054028060b0311a1070100022540a0840310003950159 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 491815368 1250 491814118 491814121
    0x3130914061005070302030c010203040b09160e06061b1c0e0612070c020307091e0501090c141c060b03061507110630040507060905181e01030b04020108 67
    0x4210a00d1840c8907800140c956a00d6202c0c2c8102107440798807032441502140420701ca0024205828001140581d001d081101c5503401e0414103603007890b131070042c00b0748030100c28201007050f4150541c01c15444001203e416444a422001141001c500440c0360711207070048c28007000090320070b5820700d1030940c040da4130401d05450850901803103100302500304520b140043c000501e420310030351041642c58809415075001030354034181601134822030085840940d008150101d0003a03498401c0c6030040400c07401c1800b510000401c0984403404d00c420801d0307140d02c00140f1f900c400310303810702c0070301024281d80d410481c00d80c0e1044103c078550815144e65101c0c52060080c00d002c000710707000b0303600910b030000c00040464503403508011003580000c059610000070703400c40100d59a03821007200302601400c00c480b0300314900382c6007440c1081e41581100c028401040800d000540f290340c4a840e5401c2034050114064441e010144450700742800204141f00c1c0d840d0000c81049145203400d0701592003a00c440816 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 491816618 1250 491815368 491815391
    0x120b030c0d06020a0509060706050105010305060603010e0411030f19060c0c20130c02060703141e1f0314060f07120b0a0b0a020f0c15040611010e031309 67
    0xa540e03000d95200d038411908080300303020440d01c1d4014a48042c0908005182060010100d80c0e80e07046841c003550100d98640041169581502803035910001c12580c552456061a40c0003c492a01501c0500200c51032400070750240c4041007034034444000801240c00c0350400310f04004804c04030510450340302c3c2c141602040014050030b0290f26942c0c1c040d8800c007001c4011210321441a1000c031180da4401d84104a4a41c4503c1d1886841d0700c0c082e459014140d0340c900b800c1c02030140c4401200d00300d9490008020001c074400c0d440c00702d104080a4442c42c1c40d542c2c8904020f1034a09801d10340410280d07000100001c10802034041c5000c540702031400b610340c513945008020000035021070302e00703000c5000c100c0c2205114049070300041581070010300b05407015895a8200c240c580190702d9140250348880071203603d8007800c0281c08905034044031003414801100508411500980c49400d05000b498103611003080300a4004d030300100c04040131242c481c0712000042015400a00c14101f8a514103c02c0084 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 491817868 1250 491816618 491816623
    0x120510020d1e020a0206190f06030c03021f020304050402091912021f02100e100501030b0604060801050103020607021c0b041b05030102030405150a0207060e071a07030e0108070c02060a120b03 84
    0x141c030b13401d03600134040c0c1d561000d04184400d1000320030880200e990301c0b018003221801d4807468001d1030084405491942c11441030083da00c40e01d8002c1c5a600c05018450448940d0000460f025950203840141e19010120007050f40042580e5110003074840400000c07a540658183c0c00e118107000700c42d40041c0c04021400c2c0007546010a40080c01604009a4069070040c1900801d6401c002c03002120b1040c106204014100c0d5030070b0300102d0300316001c18180311080c038040c01130b01e000c2d00d8010001c0000c6c1d40b56a0003e0004d200703000700240100c2c040c4240742140034030410036500345500800409900d02c2e00c0e01d44451740002c83c2c04102d801d13620600010646080501c2600d2003a0350020040401442c0880080101d240040104914540811607240082d01a020300001c41c14448010040f0f03500f021080410a8454803441002c1c5c60103001a5000c254800781e001804842800d151250313446801c0e080300d400d040c051001c2d40015000408201d0345030f11580c0c0d4141038080080070031480c84080704054 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 491819118 1250 491817868 491817877
    0x190e032e06380a0c020105031801050709060e0a0b04030b1b040e071706030631080c15060108012321060f09030706023001061215120510020d1e02 64
    0x500103044c1014900040d40100b0066070010011004e10861680491590382035540444070800001e0340c0c00030800c200c0f508110b544020941c1112500c0c412420103070b072281d090203035104c050246060b540c0812078a02c03009825a0b05985444042a0713500d0f1624581e88016001382c0705200000d50300d880620b00d90f0781009100340188001400b50041c0c0c0c0362090032107100148441080480c11034008030b08054003c03c480101000e1103106450380320428880601d04000e060955413086c60715203020061180e070f0221801d815a0400714001c4031006500f80c0c40042e00e6014601550400d04400846001d9001c00d40607045a1f40c4600480d0080d0350760303160030b040083e02a01e405456901c14800d901c00914941c003d445140c2603070020f2450a122100c5005080b5601c0c0703080c03007142c0c00c1c4100510015500428012069054410900600104c428648034008440c41a015040c1720402d03400d0400505110007011650300503029519080070381601001041c44c1500325071100111100300108841a00940c0e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 491820368 1250 491819118 491819137
    0x609030a110a1119051c03080109110306060a05040905010b0711012309030c1503040b09010926090d050606030d020105040c0608090304030602190e032e0638 69
    0x61103d1403007400e1001a0064040c45520b0710200c1001244545a0442c01c07003240540104000e15500300c1d0801600080b0306070030240815082441070140c8030200400c5981294050b20215962142c8840c00c4607180181d4100008850500d000010101148409042246d0245410195a41e40d0b500156041d8101038040c0b0039014050342111190341426010349848600581628144a2400001200c1c440c1d40f01c40440b12600201c140003e104c100002141d02115030b030300030401c4840c9500c034401c08032103c01c50042c4150000e01d40300110110182507400d004005004119642600e10b00305031203400c1151140c0c00b0f03104500041a6092050054600581e04030b0460350401c0e0610504a4124500038100b8245100400000001405c00c0c4010302140d00d1300403910b503c03414001c0b4001c3c01080004000d510075031212440f0b202c26840d490013601940980880b4030003400e040503001016007215481680000d004440f81c00903680007207104440f41c150442c03248000e82c030901c01940d440c082c14461 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 491821618 1250 491820368 491820383
    0x7120201230a0204180912020a150f0204080d0c0308060319201305060a1202030d20010f0f11210a0b0405010312170c09130e0609030a110a 61
    0x101ea5054001c05803590450403074400540f40139107401440e600c609005010208159a07030940b48140f1243e01d0302d49444aa0b07610182001c074155854140c00000603d2815120310b90303d051182c0311003540d42c12200200300850544048171000040501100443d0fa07041d40030811035000694589804a0700b0003003070000d00d4441c11200380e244c0f140110f6440418240c40c04c001441700002081d0707182c0e40c1929215003110800310725403401030300340942c00249501642d0402c402c0072404005076008143c1c140300140c14a000403070b2206251000006000181c480d0405501c3c014148c805c0c54400d4104401c403100155041c0175110302e4045102c0a4441d210004d240c00844003810b0307a101c11000600f540061803200c0110f143c00c5503d0026044032400e9104480c81000782c1080b04220f03400000d0b12085082040c041c1c2400c0c03a03c0f030400490307440344004041c41504040001d84400099601c5803160404002c03c9a0350781c5400700a5698aa12140c0d800f00403544050345030840040000d003e4074819801200b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 491822868 1250 491821618 491821661
    0x40e0c0103110a141e0304150c0203030c09130b0a09020409050f010f1502151303020c01020a0309090c02031e04080f011506050f0c011e0c0c1a0c071707120201 70
    0x2082d1500b2094004a4904046105850501345c40c4040d501980c0607540380440b00340c1d04a021401c1300c0c1d12030403a0f0b0664200b84108030784000504103444045000303850300d807a00c034500c000c0381005280c0c1e51541580300541c80004604600302d0f60240044d00c3c010841084580c54069600b8403080c4248640c061041c04258148103804200c0303660007211119004465404281c80c02c860b228810450f020401010769420780401c5c50340c10000d10880c03640030700140c03845a0b41030710004c1040c0307084d0040288550b190682c030101d0f10700c20000c58a00c0042c0c2102c080e01607540110f40f050f194014440d040707543c0b140900e4203840e030303406108060b004109100c03d02d00f21450040c0584035504000315102001c0001c1c030106084103005e0080040070700d09400380d04120546040c141d000c4030514400b050030480c500c204000090311810a04404034200c0c0c1388420160f890301d102070650f1180310300042880055805c03070b100e01c0c18030074042d201071441100b078042404040e403000c034226a60700c4a0310401c4079043c0c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 491824118 1250 491822868 491822897
    0x703080927010305010c090b030f1b07020d08030405010501060f0215070309140c15070b01092c0d14180f0604090c021006080f0714010c02040e0c0103110a 68
    0xc01d012041806580c00c1e1100010107508078660a1090b481039403e030b5103400902240e2644400204060143d1035032a48c21803c2503008542014001000030502c40e52110303619540b0303000001902c80966006004291010302441c3c40505a00700b514125210360074440042815802075400e002e91045540c02081e550b8001c42428480d0140075094009165580043d180401d1809036680121000a030042c000f0325000c00a0200c060700414005402c14800e00c500c00000395042e212904607031280e6000b090780c2c020701c0078101180c0c050046000c03807429005004094610040340d28040c140560315028950354691560001d03620591a03100300f01030340610307002c41c06d00c1d00040001c20708102610107400c10b6180e042c0c1500300c4e03258144450141c2c0c01340c00c9816202d0400e0280d180503214140150400c01a06002540d5503040c40c007031190052800c0c00520b01c240d119100104032150010410704c2101c0700b61059070748500c0c520204500090804221810301d040c490100c0e60640441d90b24030034000b9829 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 491825368 1250 491824118 491824129
    0x11040e030427061518170d02100204050109060503060307090504050601140f0108041b09110c070f03031b06110d0f0c1e110f0d05040503160305030306011b0605090f0106050307030809 80
    0xf04e5400c0036400c0000041b941050305041007181204a400500d80c031101d40d0000382c43c04140c900342c0142140100010f01c0141d922485060403145541030840c0c0320746840d00040c4c2051442d400068102d4a0041000103005002503014100c0d0080c019640c48908403905010b00c0402da0740425000c5030001380030800180c9030803903150780c910300c4e580325580c025103501c98201174586910580394070110118047c0040503051011b00000c141880409500500c0c60f40d0140c60f1080312008040110341c411064806d109041d000a0060180000718550b9107140070103002c0186440c4204100107441c001c5a040181c1c0034403800c4d4502440d1610b000b03071000d12550100d031041c0101c03112a500c0d000f8402454031004040103008140407181e21469240d50030710050501d400c2100c00d034040300e0103886600700003060b0007000704d0390020402e1805100d1910303004000c1903100d407610002844a4a40f0b001c00001c101e0109210303009885120080c84026603800400d591580507010183c82c49008018910007442c02 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 491826618 1250 491825368 491825387
    0x1201090807080a120c0201060609051f0e030a0816030906030b090103060c0c06061d061012270501090201030b060711040b01030b090709030b0f0f0411040e0304270615 73
    0x807454418400882500d0940c00e84801d1550317400580e45649051042e1a00946c04001030701c02992348201c00c1900d101c00b180c00c40b16600707181b8203102103008111030645050003005080b075040040c3c00d0741c1e03201c1e03050b0b64601c2014042c020741c0050000300c0042f130402d00c240038034441070800410603042c690070750300c800f8000c0403540c40c401c0500c21020300c6800092540d0042000404110000100115055030b000c2401d000042c1000d20418050301e00480c2c0c184c0042e00030404108109001031101440e20301400100741004140c40c882042c0300415040000c15000303444858400c2c1d03000d011003001c8005201e07450046480081ca030070100f0185091a003007030750085444002c145008a41d2800c10004075110381420f840c948005100c1705003c0c0305000e0300c0c41c0110780000703c0d41e52101851601d10800c2900440240c402801c500002c0c60310070680e9a00e8024a00d64134210041d03d0b50350b0349c1c4600e5452401000c13400c40344181c140950360303c4041c2080c89401c08850080900c04c108440280d000c80d034681a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 491827868 1250 491826618 491826637
    0xa02070e01120b071814030f011509150f0305010515010201020a1403130819031404021f031e020a14040b0a050c01091e150b03031902010f020a0e120109080708 70
    0x1900d00441c0d40303845248880f00040400b5a496404c022501050500307081480e10300c403230302d40c0c117040c100c1d41c4540c0340382c0c110000c450318450001b03018010181118500c01c07070341d0300c003801c60510790b03002006001041d0300050107041941e091002090340d5500580c00d038003c206400010400215001041030303c0c0c0002141d0095038814041501d0006d6668410250007054800c0500440086801203580d00b6214810940c1c00d171401c4400307685015030014044002030001c54030004240785240038881d00030342102d01c1411020001144e041e4000032103600035000151001d000950701c1003c5482c4641d80003c4030f040e40d000454041c40c01100c850266030395030184425860940d40c0e0111140400e03c10380c60203020001c501da40f920ba00401303081004e0050300b50000344802034944402001150b80000c03c56070840c1c0d1901c1803440c100b481940a0f40109659004002620b0000500545040d804040c85e000c1d40b4048519030004441141a5070803102241d034010510301040000c200030514900141c4400310 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 491829118 1250 491827868 491827877
    0x80301090f02041d07141228050114010f08040b0106080408070c03081c0b1011011508030927010603090c08010f0b0906040b0303071e02060a050a02070e01120b07 71
    0x1691148613074000003070382e03404071070700c801c06401e00071070716800b10b0740718016000881d000e0706091422601441c904006170840710400c0050500a142c2c00259100c05682c40c4004000c218540e9960500f00d4850404040139000410204400b85910f01822005001e0791700310600c081a0703802d0100594070341d40d02900a441461082c024080010b00d14120710700514410300340282c03104608100e81c0c00ca1491359808895103800c1240c01061500e4080c00601005004e00e060036038280b0500e029401008200c07030400d40e004c0750102c0420401030000007400440d0301512a0415101e5002c00c030400010031003030002c8100700b0704c8010401d95200350440308076940140c42d080754455482c0762482c21640c119980104407610b86050180900d42005025400441510140503500034140001c0c0c6a20504a00400612003101041007003034902403944500c03980a48103680d621000c2d080641240c21980440005210302c080100358904001c01080c102c4903461584007203444596208240c22000621050400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 491830368 1250 491829118 491829127
    0x303070507091a09070905150c030a0309022232010b22080f010c1b1b0e01120c0f03020a09020a210e0606030c01090b031510030225080301090f02 64
    0x10b076640d8410314005c2c5401d45a80d50307200e2820060040d1580003c10b9401107160500000c440c2007404412207190707116900e800240d5084500c00110b0381410104091007100d0140700c11035450849501154081c0c0061001c0a1446a003030000c42c40b100a140002240101900040201c00c00380e00203440c0100e4030408626580b1200d8840b220003000541c0050040c3c1d010000004c092342c400c0c810203610380d282c1d141203003004800e0300300001c00c0303219044000d110b03101e40a00d00002080413840c09000e4887c0c802c2c4140e003940d558070388041038070100200390b8034800c1c413000000740d10ba2444024011681d01610165046180840081c02034110164009c10b100617912104800e080a840f02c0a411902d03220024400740c0840150345452402040503005ea8859800c041c800d0703802c032a0707c4046903031820049560342c1e03c80c0242c0e4001c10040c9603044c2c00040e05000d0304d45a54041d00900180b40030340c2440e1782c4c60f50313504284442032082100301800c400030820041c01072030b4040d0404065a02242c0300503280 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 491831618 1250 491830368 491830421
    0xf04050606121306140624220306020d0504140706020a0b041b0e010815010e06221505180621070e04050a110105030c0f090406090e011a030307050709 66
    0x29074a5070301a0703a81e400420f100300b01e03076454070242c2c0070099410328891411015402e040c07400c46105e1002d640108e11140150040e6050031022001c01440e4032a100b5521400c03040c9192019040503102201c1414880018403840c4200042c0041181d9036940204150000b5441300594510050415520300c1220701140141c0c940f941c58090082000a410740d88540c5441c803442e082c400d40741692513041019200401441203402e41c025049401201c0200b00c1c49050002000c0354141800c00080d0036062640400c0000c1002c10100221f4005840c1c0c400070f00814110749041020848020b540a00003544031050310248254400500700f8607403c0b80d000546030b030741d030a900c55003c0b201110282c0c081c0ca5072604100165250210311082030030074070300f035043c103a50303610071030040b032205001440d170100304c00d041e40c3d8030385c2c01080040030220b0040004c20032100001e400b070326203500424000c4440850308007981c00e0000854103070640240160042a081420840c0070300780208681c0d9442c10511119903a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 491832868 1250 491831618 491831621
    0x3090603090609142b1d06071202010203070e01110a0b0405071a0c010f051e090309060406020d08060f0114031306020c03040305060912030403050306031002040b090f04050606121306 80
    0x1007001101c0091a10200c0c0eaa04a01c0c40941c0c4100c14845055170790740c0c0315240d03810100c0e1a84441a02885000c9100c00a0103c1c2881c01100d201a00850501c00000055901940150f00441881c0e56110001459000560300085c031840c2243d000d034840407005010410400e01990064400c90585110f01e584018244400302c28021200401500048104040b00d0900ca4a180c4c0c45094030288050315240b40000e0500c1c58031100c1b000c0031040742d000501050010720441c1c0e825640200040e485503202c0030300a642c6c2800543c0359000c5000340c0f010590f289018a00440708103416510244004500d81e1444001d80025207001d4800e5003003440395000401c00e001402004840100444d100d03407450a207a8a0594040c002c036200c5d0300000d074408480300944088030782c03003600340c00c00b40e03500c0e2a1140401d01d007440d01c1441b680700314400703d408119044000010442802c04031040c0080310f0400f020401200c2c801e403020303a4001820000c442e66090f283e510076510000312900c0020b4042d0382d4507900d0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 491834118 1250 491832868 491832893
    0x13030203011b0809060106050912150f0103140f1009060902060708120c0301080d03021819080106091109010311210709060509010e09060f03160602061303090603090609 74
    0xe0b1042c07100101542016401810150710018080040c070240d40b4001014045101c4c1e40d0700f40b0b010364400e030303040304010008000305442c40245245a40c1c15103040c60201d80d681d6000e001c01c8802071080da54403a6207100015180c890f05106c40040d1240381044005c800041550901c100d4140e034445115102698849003d4507855002c2e50301c0c299105440b10058070b00c400010102841440c0a000503c124200015034072022070726420016038840d803140c50b03a4004851760581c2030384a40c08503042d1120120f100300300f400300e451b610000d01203543c5801804061306e189080100004006010710b100562080c0c0090105c000c42c00e186500c1c0121894030308500040d2506a410701c8440b540034800581d070b00c1a20500180a545011070400d205140028031507200540c3c00d500c01c00415011400c42d40d254542c02e00c035141c0040c1107540c007000740c5114241c5101248200d1b001b44c01240001064842c16034955109564165034400b031050400f81c058000305030468041d29456031f1030700d140000a10b05501c28 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 491835368 1250 491834118 491834141
    0x90222060801170a23011112040c050108070c020d0c050d2f0102150703110a05091e091f0803180a05090402090a02030703020f07080909060105160201030902030a0507031a0901020f03010b1303020301 87
    0x142c031645442d04ac603505d0000940d00039810040762900300580254881d501b03002c80e03603048524500b0307440c81d802d1034400b01480c1e40215600056600e0080204030031440740d403840c450720015400d20300480440030508a0610500180581c100c4194a5440108050100c0c0e00c2101420001403038400c0042c0102d4907005104d50f0310100e00e002030f40c10550b20b49825035200d4114800d032090008003c1c0d501050015902070442135440d100101d10340c0386201c1180d8040050000042201d03118900188080300d2500846401d40c050301d20040b0105103810620540d47c8555005800c01c003c075111511a54003e510007042c100405909100c581e44060383e0500030482c10780182d140b0b5459a0081c4100011464050000781c1400410848848480c41c0754198046407030302401c00148902d80790000c2070809690741001456405500d001004004020b000c0907409d1780c04501880b0070f5581c4102103402c174820b00c07001e410b0780751007440100080e940400003081c0803080d00d1059078520755240e01203805c2d1508410314 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 491836618 1250 491835368 491835397
    0xa02070302090405190b0f0907060e040914060c0405040609020f120a0e100e010b0a0612020715060e180a030503010317070c0b031801020f04090222060801170a230111 73
    0xa000500c64407e040c0c5800c4070052000c6c1802d68038149001c3e1802811800c0e50b8003903a15942000248021000100c00c1003a0440503200315103481c18000c040c5910034044c0794411441c2c0b80011500f1a501d109854500700030f07031300152034801d5030504c03460003c50080844c030a642c1c8035449415020014041054205c84191000c01c0c05212082c00e5425200003110382405012000010030170290b00145000080e10030510050b900d040c01e060400240341c85245103050282060000500c3e02c111100c028441d04555140c00d81600d810403600e0b031240311504002d8001401171005002099082805101c03c04e106400c00b031a000071a80c54620440c0998080c01002c7d10100c10809800b0440040800c180442d01c000c525040c0280140100b80c065400340001301e55000c582d41d25a50340d81c400786c2c2c8640004902c1c0ca103189980750001030001c0c109018170b540403440440e590742a450000b88282c02d29a010f2980d444035039401445009460b01e48540b441c00d5074845414a074603091400050070304503a40c0c0345 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 491837868 1250 491836618 491836621
    0xd020c030a080601020d080a11040806010b07140303010605030f1305060a0c03050709050a0b0903030424020c0414041103011535030a05130b0a03150503030a02070302090405190b 78
    0x42c106120003043c0c40e05541108501418065110b5101030303200b90034110010340c050301050480030038000c64100030a144039410011500e0310808000e890300714070038101c03518940c0d00c418200e91680000c0c8124008500c091010484006a803103219611003558039480898010580740c05140c104e0503621088032940d2111000320850f85070066603402046410910409460100850f880900d40e02c00c00300021808952000550b405004032001450031006201203032001a0407079004c1005035081d40050b02c2164058446030506009240a1014900340c0ba51543e440351951011315030b80030744a5926550302e4074250261281c610039440030300a10308600080c030220404010f011172110030030861001022010000c2d6000000031595514813510b05240c8441d1812221111000705401c04521a070000c105119669850b13440417581701c81010011100035500c40a00da01c91107254008030041e006400240f002d0b09180c40020b80052040301281c000b0001c0203000c81c420700112404565a5a5040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 491839118 1250 491837868 491837887
    0xc030f03010e1906080d110a0206030408130509130609020a09020c100e190f0f0501060b091309170702011704030c051c0f20120c010e060103080901140d020c03 70
    0x688034103402c0c0d0b001003041045c0c10701148507a038140300e640b16820805201c81d010b0700d2200034000079a1f20740d070280200340c0368146440d18810941241001100810300080c002034245412040c1c240120307282c0016114040c504e8032001d0103414114401da0b000141d0b031a0002e0062074500c020004690360340d000d00040c00e00019a20255460220280015030051400104410420b81c80180d19a80120384807014401c078603100c3c42031540107030007030210b520f0404001003101c0c0e001d0040401490484a002e40c400d00400f01004030f030540c18010302082112184412405a102e005080150050404411564521a89035244c500454003100059111415002080001c204034450781c01045078100d062980703200d000340358900d15800c64081000c6030301c0d00410440901951100da402d2072069030b0784280300d0410100245d110052664056292000d84a29000c010646034181ca900c48040c0380f601d03a41303000445a10302c000b041c011031108208030b00c0c505401c4620040c50031041980245882d40060f0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 491840368 1250 491839118 491839141
    0x210103210201050c0d05070909021207030507020607020a060c05070606090204060314011406031909030201200708040e1e09010522030f0c051c082e09020c030f03010e 73
    0x540d0094103580c10700e0103201d12061142c090340d42a903400000014141c3d81c6441c22200c0d41241d45c41007001c50f100041b12070b644c902c07412090b4822030990302d0500541d15206412070743c0b440c040b9240401a04950803044c0021020307003000c44202030504d03010341082e010303480381821030700c1c0c540c0319a540310390016003000f10381c1d0980100e444090401010188540c0f400880b001031000c0c40c68168814600040050110002c40410140f560415402040f402c1803500e000790003046c003145400e400032007035030158440d210000c0484a00c158004c2410b400d05150143c09030012001602c600301c55081000c00d1231015070340031407403403042c00c000f400480c0d01e040041e01003400b4424103445140e510800c000e90070110b9000307025600c82d4032141c502140342d0072030380c10036600781407040303181152040100504c001300991100303956000b450101240390700b50000740c8a15a00380d0268042c0071020590000c07c12071680154060b02203441400d040d03030700c1c100745c40300120b0b02540242c1001c603010200000344940000a03 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 491841618 1250 491840368 491840423
    0x4061b200706050a03090201030f09060c1d03030d1503050619060501030603030c02010f090509100501110304050f060d020705010203010b19020d1b050109140a02011b17210103 77
    0x408015101079410640010305070b20800c9141c105064980200342c0859200794403ca40380c0304141010407451034545400c8001c3c1444801410008030a8016030245c280e14a80d03441141900600651610341c806448602030091410040705e440d00495000000c40d405000641c45451b00c40000f40c01d407440e4101002c1180c855400c01410585011030520002c0c2d00032106021071b5409080c02c08609034001812501d445031600616002100c2005001880c50351910500664000340c99111403068a411050703540e002c0d6118441d032104510b110211907091610040402d56588800580351551350340f201402d80e4000e074007221201301d0000d6002c1c403214040b6600d1b60503030f03200e00c06042621100c3e2001880b0300d54800008110064051001003044002d46c40f40c4001c5500848500c110790740310180320746804a03035200380e0124120742124450b80060b044400619607004209103d902c1d008034002106030070403110702d290641810000306607400c001040c9402107204480c05111b07150282c0015000b07070503 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 491842868 1250 491841618 491841677
    0xe060d062009100c080715020c010e030405030c19152615060705071701150f09060b07210c02030609060a06080706120b181503070b09060d0504061b 65
    0x2d02c840d84d80004e50650403a129190041806412601200c5591000744288001d20005610f014a862085640030010380100c481c100d050b91681980c4409102103480841c2580c3c481c40c5081c4401e00c4881201901396982100524041040c458058109416181034185001200c1300d0b190030045041858800312400d08010303210b0368105400390f030340c0e16038507032042c0108001160307440c0608804c50000d500200d1040206c17422180d20703560381c001c400483c62890140000c04c0c0e0601c01c0c0800d0018100b01155140f0f640202d503845400c10340413403080e42886001498082020b02003010002d65030030492140500303101c84c0136084905194030381c00e089500300d6001140c283c03c00d0504002c06600039640b0f280c0c1c0b10035000c0118201000740005008a022083d1440c0d03002c51160502c0600c01000d000880c0c1c0745021703011501c296032910b20a07001f81c0240300300e2980c8880204010110022540c110301e8001e8070940001c00d4101030344464181142045200c0e40020b1581c9a0f81607119140400403914400e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 491844118 1250 491842868 491842877
    0x1008070611061321030506030106050402070305071b1203031406031b0f0607081902120f072003010f09030810030f030503180a0606080f070e060d06200910 68
    0x240106807150700c99400414003164200300c0203d003824801800c1d059a11009144007400b05410070000c050000c020684165000e50719010001c9060308041c4200d5a8290301622298145421030342c0d08040842c495602c5146002c442c40e001030358090340c3d848900307400c1c401d0b20042021500944030294102d001000e0900c6030340a0384030240c14100c904480c00341403900b0740d070f80c2d8180c000d40030119a16100740f600050034480001482820203400c0c0070305040b0900d50380e081e508005c407100711150060180440500d60208104900c000181650704103a082c41440c0c40c4000044214200013030031036040c0c000500e07106854584220425a01c6100f03c2c1e4040e540481d1710b4407007401c1d925922100710366501c0080910034000086044074480100c0c0880c21150242140c005003024502030025184600c00c100181c41241c1075008490008a07444003079079804c0c11004500e40d03c00c810070090a03034251058400715518052007148a040801400040c9603201030180d41d200d1400601c090000180d04400820 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 491845368 1250 491844118 491844137
    0x120403060c0309080a030207080c0609150f070e0105030603211b010911010e0a031b0e0106080609190e0105042d0503030402130e03031006020f0f1c0e0910080706 71
    0x80110b07083e12017082c1285401030300d4508030316111050703104454203c807040c451030040159030f200000d080d901044948901c0702da281c6030104041012401600c0c00004503800024101c060351041001c0c59100c40c006046039400c101e00143c0501d10307034040c1241040802d001440c0c3d003114046040500f00b4001210081044200300c0e11454515100c02600504004d540d0900d24815900d403d03200001d0340d00050350b00d800b03000c003a0b4480b8001d40706109000840c02030b1400013851a0081000d00d20841d00500881c80541d03850380101c50b0b005941400210700d960314600c50001140034441e281c461486190300c80d141541000c1c28490790036004007800c554040c260303000c5000a0001c400d50f900564151a40b10080d102403420401a285201c0403c00c03d1001008100daa85614400481280c885400761820042c0f0703040749030340f00c41540410101c290f010410078821403007102c68030715030040185040300341006510000382c40c2e408283d079440c580400c911014040303840103024000042096060038040c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 491846618 1250 491845368 491845373
    0xc1e030b060105072009072a060b12030c0c010509010804020111070b0f03060a050901030515040f08033d03080705010e0f07091a0a12020a0e0901091a04020a0e0a0608120403060c0309 80
    0x183d41880400c2d401660320b60710232000c0210310b401003400d07010010040b031403480040840a540b0f4000d800c50342581e2213140c0301d58140e540500704403243c070903040e902c451469442d6001074417040c4440c83c54254512844200041e030080a070064900800e0b2040099540d040120402401c00d0f565001244510110001040080d1001a041c0e030802411201c140107a525410701c0c2c0c0a803e800b001c05402401e002013088960420601010a6003041226480c07511000135601c0002c2d001c0d0751003480d610803a803039040c80410540030152038424403850000c01c000c0002d82119003000ca002d041041c4d1588800d10134004074841c1d0045403900c82040e68090281c818640006000002da4802d0824075000e2100d601d0654503140310910203031405903064141c1742440c811050090220b000305980d20b448034943d0100442d141c81c0100d016a40040c014a412414203020807407403640503040002c215a504030002c6d10391000d011001c5400300310711203181c5407491400c25009960088450700304251801061200 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 491847868 1250 491846618 491846657
    0x1d01020c030406080a02090a0e1801090312020c030403020d0c030515190c0203090a17070b070f03081f1814331c0c1e030b06010507200907 61
    0x1110705910381101c0d19110b01c42545c000340304002109800110300306000ca51841c0c5600210300819615400301e01c1d1a828450320790882e070410780002d001541040c01e8100c01e04d582d03001b406580c0206000d50349410f960703600140b482e1b202e02d0421034181500500030000e00000340100c50138158040c2c003980c054a032041754400192042884d407002907a403a20b000844c07078030804c2525084003000e4806140c0701d41701d141640301d55401c95107103411440340200105520241c4400d544000d54480e0100180038107070b541c10b8550050017010700c809250716450b5030310401400394502005000d10044a00c0803408101298240d968120011140012800602c0083e0011220340c20020600c02d8800080c11042c4d8030401031100c03002300c0706a10518503229060142c88904e03501c0b852500c61a501100d85680b13100c40401d03643c551704070711503000705201c00300040b5840a1025900060500d003161506601e03903544031015a00040c19204408100201c020b941040007005403c41c00ca0b05224020601e800500306 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 491849118 1250 491847868 491847877
    0x2030105220b07140310030c050a0b0912010b061804050708090a02091f090f060602120d1119120501051c060e01020405031c02010b04180b060112050a1d01020c03 71
    0x300800c80480000701a280f01e1000a800c060160725640d6131303801e001d01b0350454245117000c06d41303071114104000545444d1440264080700e00005916042042c0d450402c5481d00c1c2001d804d01d81c5540325224454141d6440700104080d03040041d84507100041d520612045030390042c00d0a041c0000300090240030746c0c0c005031a911a139811030b0010740c0d9a8418802e0f0048040859100140120161000ca81d52581c1e2b000f0b03203010b1040c005e003005019034650041307a5403e84048021403416041100620708881500441c80e41d1100ea00c0d090b20b000d0340050503130150001400c19800140d001c1c442c030355400340180141401400b0480e030042059050410b260001c180c0040000d044640d504a440740c810f400303406540051500400f03a0314071044916800c03107841c030300000001c01540ba0241c210303924a8035100b04491501000c240d0200b9115581c0c4008034035202414803810300c10807450350489541c290007254803400e0304c0341c400309602c01c07009403422802d00f9000c41d03c41d0740e03401800702d002034060000540d0b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 491850368 1250 491849118 491849123
    0x3040906050a0f0b0c0a0204050c222904030c0b1209120901030c02120408030c0d02010c050d020d020d050c0c2e0b011202072303280306050a0905040203010522 70
    0x217a61040300c42c07101c034681204810000d401c03605100070052510050800f50900341c85c22030300d040410040303050b4503032280307460b000354200c80d40700b0361034412086240d150b41620080c081e00d0341c0d450151683c691132480f007420790110440701e00004041091581c41c607170785904042010001c3c1540c0f890303103110181500440d00f582e410180e0310400c5802e214801c00143c10b42c2d017880e81c1d696550303c2c1c4502c5526103d6000c82e102d00813a109000c8000079691051040b030701c42c0240c60340c0c3c10b0f00348052400010003030b50094a82c0c2c100c00d5000d10480c002548a4412a801641e2941b8603642d034500c25040a0308003402c0030320740028100713800d00d040400ca0a180041d1141001c5250005074060f0090050b00c0014448104003184c1e4404520766042080a141000306240101000a0a161038000fa25507900c07807103081442081c04107021807005944d81c09c0080141c2c440e41004904141c681c0b01242e5400102e07401003902c0b41e219000e10095003820b10605803c001c014860841d81e1000007090744002e400c00000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 491851618 1250 491850368 491850389
    0xf03011508330913020420040b030408040e07030603170a050301050907170703060311090601120b0a05031203040614040203070608270a0302070e07090b1309020c03040906050a0f 78
    0x1422401c94030240c103415510000f003d0103010304041095890040320303c40200e00691400c10081c42400d09101c1030100c101200040c0c43c6807506040354103036150000b410480d502d060911010035801c1a004206d44034107800e5600189403861403d01d0f0514007001c8601c0d80710b6003001c00010001542c05403c59055600981e07032003a81e03444889086404820358140d140b014840001404129a4182c000c2c03820ad90051b0385000501c0c1c0f064080203c0c2d6001580c98502150b600f1456040c0010643c000c80700da2003005103200800d9503107201203420074107184401c2c09245000410401001101c0c030842580072141c1ca031101d29031070954046680c58280d4012082444803880001d40c80b10515651440d580b074100d05209524030030400825070355010280b01f14098000c01a01069a580c2c0b40c020398890081c540d520a0004c0ca82142069a030b40990143c0c84042806000451448241d0000b00890443c020041d550782c0c3c508001e44044407983d401407442865107000820a5610b03881800046e510300c0c054 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 491852868 1250 491851618 491851681
    0x7080105030c060c0f0102040605071202030a0c0b0a0902030d020a1b0305072907080408010b012c0a1a03070807090e06040b0f040e030c0f010608210403080f03011508 73
    0x3078075250002170000a400342d800060007045059102c006444068030a48403d0b00394000400300303036102c1c0a854000000507980d900d40c840460804d2130300d5074200032050740000c0c2026003034000c41d040c9a5010b030b01402580c841c28469040000104074403c0038240a280e4092903421995415111000d51040c240c1206101d20b4200245e01da615080f40d500c0c000c958031540ea000d8503c1c00d0507581d0002d1080e800ca5521340380c0441c0d055400b803800d811802d41c909000c00840030b2013440902401402000c1a0781118900f140418075981c50000d94005419041540c1d8892828540013070004100411902c01c000010100700301e0040e01014040e00050221070110301c40e4060700200d544034900342401503203e0305003d14129007540100c014242c0140042c01da0f02518030200c016404e80310f4074450504d403035200100040c2e62100c03940b10b40546102842c00030303150507560b03260105a13400c001d180f04440312002004101000020095020302e408070700300810380b49000c0c8000103240b503400042018084a006 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 491854118 1250 491852868 491852887
    0x7080c10230a020c0f0301090f1b090e0114061c0b060d081605010f060b0306120109050a05060108061e13050c040603030e19030b04030c0c091b020607080105030c06 72
    0x8600300341e00c5484802992039041da100020341e0340d490825400d020b08a41500d042e218241805440c0000c1e1300090500814405603031201203000080c5101054031405200106903e0001d010703524011b034849001094002120291141c0780c0005845244101405258901c220040c10b03018030513a40c00001e18207441c0c1d01d40001c5442e5811b104c10042c042d190024000401c8508502c0e0803030070302d000c3c1c1d000b0000d030050000e2080880c1c4044c0a6940006c1040c0300240d82854010b003407500c2d4011010000c0781e0380042e1f0780c45034940070f0002030480c0c8507040b100060000c00c0d0301300001d6a001158000c542e0001964048030a40c9440282c24800320a544c0c250304001c4c0300b0104122106048094810050103550b410000c064100c2c0c2c40140344608c520701800703001b440c03183e003010301541e401403034100c02904ea80da000d4425000381b00b021165403100e1180068000e08034451500f40020007051050031500b100e40080c00d281000b031584c4203001d14517006200580b0f00140400d1941400d40f040ca07620b06890 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 491855368 1250 491854118 491854157
    0x60f0601030b12010c020f030f16050705361006030b031507090515070309150c0c0b04150f021b041e0b030d020c0f010c0615150207080c10 61
    0x9000e950003242d20300c0c95068070101544081081c4170a070b801d0f98070f0032410060050f282d118070708842210440034020243c082000d8100d405289204c0c5d000c9a000c80ea40e00080f034103000c0090b0308101440c42a031072010003101c6a4466412004100708219682e20381665900d10300381c0c0c140140e008042d03a610111a803920204194009100030041d40c441c0f914017120001d0100d1b11501940c2d0043c0c000320700c800b0321a00c2c00c000b80d41c1b030180e0503100c07005020b0410840d01c400240d14040b0741c08000081c0f40b5100855181e00030480500034259000b5940c509050b0180380760200300501504100c10000c40c90122640031890801400001100b0440c49414600240181c00840c00e02800c829440ca00d180704014aa440003480300c01c141e05407011081c2d0604166100d060301034805800040d02154403140d50f02c5480340d034440c1e6201e6000040c8040d13068140b0b40340741d101d50308401a41e40400e4050280c550f010840d110003040b20100500302d2912000c0820a8250314494002c140000020401c6001030710 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 491856618 1250 491855368 491855381
    0xf060b0301091b0602060c04060807140408060f0105060702030c06030c070506130c060207030503120703180b010302010905100c02100c020d05160e07021b0609040c08090d0c0203060f060103 83
    0xd00901c50780209050401001d03018007100c0741d0346507440500281c12070010420314490f070b400f005110b003440e1030000306031606d1400134188410802200d9441c810f0342d8003c4060805000c0d014000c0140703141405400650b0201038104510581d018800c030801a070b00001c2c2c000300f15206540321900ca0302c441207004c2d5940295000140b49000d440c081119a0034000e800d44a014010000607950340e9907050280d071100da117804054100c3d041040b5048501d4a0411b01c640c0017000c0e4540000c80c0322403202c04040c60904008100c45807030380f1200410070356a04c511008045c3c4000c4900082c003100a06000d0510120303414000c0c0141010300080b520301d03000c2c0e110480196000b0f4621a00b40009141c0107072105040c1e0b103141082c130118180441c0401c85414a5449140550000e0018110980c0f1201200c00200a03403540301d101000643c00540b07d5004620150500791950f09031070406041482c00c103180181e945081200e00c903901c3d009aa400152680c010500b0b409101c42034540c080102c014040 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 491857868 1250 491856618 491856641
    0x901021203010905010801050c0403110d1b090203060f0d0206030103030804030c080a0203030a0509030a0927050c0c0607020d0e06030a06090f020703030f09030807210c2f0c0628020a0b010902070f0f06 88
    0x744001c00044440450f0001c40c46034800b00d40101d05c5804080c100480e100c584038025b03402c46400d0005000007401480b80a802902034203010141c1c01c0181d4078468103500c2001194016000842440480304c0f45d80071b11508000d0f440059410b0400c500030080c0000c03018400d40450920342e02002182c4600c8400c0302c07171400301040c4140824030344581440f019030b004d6070b0207032168450344000504c03662000c82c202c0b01c030074080d90b02c10407000303034850070024207400145c500da010329502c00000030200b10b40d11a41c842c0c1d040300000075032180a5410003038122520340b010300414034208444040001d61140c1100c0d4405440e05144035402c4104000404041500040c86481d5287c031b41c02500c3c16800410071145e92101c5000c01e01d10304408541401c0d0090120001c4020343c1c0080d0343d481042ca0184090000741d02c514501da00b00001043c0c1a8440451030718988000d600403ca202082c040300c01402c9007d041e04042c2507181c21036654400c906984580d0002d0003c00b20350311002d0400815420a01c041c90 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 491859118 1250 491857868 491857913
    0x3110904060603020c0d0809031206010201140f10050d15230709170f120903190b011502280206040902030a15060f0c080901021203010905010801050c0403110d 70
    0x15102e4001034000c0d48810040c080324800c031021100d120703105410542c403500e05003010354141048074060303461005018100c14159501d81c1c0e240000c1c103a0399182d05201c0c809803150b09016040020a00e2019000d07508401c1c09072200070017079008244e1201d510743d407410028000140c0c03145200d111070b040c0c80c000c501d60700e03220300190248481c2641c040d02890943e2281043c81010002024080369034000c1c0d108441c5582c0c002e240c031800700b5014000078018a80c0c0240c01d6840b101007081c5802d03003c0c0300c4c0310011103003807142400600900005d940409064003150000340400320ba00c6070100c41c08525810081e031001316103a104021501c4640582c0c1c020070803d1010754581c00e180209001520f01000d5000003940b1200c0000780543c850800b14102401c41e844084140c05251a100200e6220b6824181941300303c10150101c001d1001c0114000c00350000001425414213170440d00390794000e001c7d0540c6101c140002c0c000720301c5480380404911011103480010340d06c1ea03d0b081c888440c80109040c10003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 491860368 1250 491859118 491859131
    0xa050601150216140405010504060e0402010c0212010e010212090a0b0c03070c0b0a1a0109140607061b110715050406050d1407021b04141305031204200f090703110904 73
    0x50043c0702d65511380d504480500c5540e0300c1c0c405020480c0c0151281c2000002858040740265000e0a410304140c3d0001d807088241c0001d109840b429218858204d840f160b50002d0b5010000e0064403000e500070350480c02500008440c0e803568141c540024169540007000040898161405115030740250360b4041704014513890918880c00042a508054540094044c451b2000b15072007815000b0035142d09541c131891240d00711050102641010310200d03040390365009032034080500d0304414002c0345c04541d00d24440f01a50000c02d41045401d90154a90301c03140034580303101c250488181d4040c0c8419290094890103c801e40c0740151a051020000c50071205090200d09640400d01d24040d841c0320340e040807aa03100c20140006c592200484a04400418000c9a60802040009400c10b40a00100d80c00c1900785012039003800002e45048580600714180805420710750b54022100100440e00c02c450601c06502107007102500500500030550364903c1001d40b00100025245010800b42040104 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 491861618 1250 491860368 491860379
    0xc190f02130e190209070807080c0c0109050a0501060314070612020a030912020309042a11070812180612043c050c0a060f03051308180a080a050601150216 68
    0x143d1035081c0160f01130703410600000c0505004042c05c50044045a465101507030300d0030b81841e8190400000c03070790903548414905000c110104404110705004400000d080e515501c2d10350607420321341c001c00320b031038000d401c0030415541c10840d00c0d244031080d4003015036075070f04441048004010b1184000c010141d00084010800d034000084e020120b03007940e08004040c8800d030100a00f00030507980c08101201034480d00a0144517000200031a0740e22001c4950181d01c0d44022401c00010b00100e074000d00012034030480c007069040c8248160901698030525048a84c41d850190742c4c80200060407504954400d24aa00403190711108079014445090640328910550786001800fa14400e440d1031180d28000030b0340d46004038010040710f01907180d000c02c9084900055000d000010300d040f1181040340031180c08240f42c2c40041c0100c0c0700c600150207882e0140306c100f203101901600424102d501490800001440008940e0b05499080340460080080c02d242240350403043d0460712601311941100195 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 491862868 1250 491861618 491861653
    0x41406090601090f02090a0b090d14030c0c010801080307170903031206030d03180303050c1201060e190b1204020d12020706023a030b150c190f02130e 66
    0x143c0c1d20000040c400802c251508505030301920804541c064865082005180c1450000f003e0580c00a46440c0c15003100b52200c1007001a49a0b401e400750b00001010b010300703402408040e00509090078000d4940d4104814036a41c0d005c1c4910062603100f0a0001400d0020070b60103640c04c1035002000c503a662600f107038411002c6e00041e6440f034080d01c80d01e0024402140a400b41a199920b00d18034034041c0301c800d440c202c004e0038000e081022210f4040100341459143c8948080c0a40410f4545044524a60b4284210300c00d004481d4010b12032407800901002c0750703a508840c04800102110700241d1118000250511040304c00101a008122310119001e40c000c202082241c45c140c00f95000d9490100d0000304851025084240640d45400304443c6204440d50203e03001909140010300d09090001091504c1e52481400621507030100f41c800c0d1109042000340c0010010102d01e4a92807541c4e44c0b0503000e680584802841281140321044100050380e201e1503000307940308e080b1041c88224952100c13 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 491864118 1250 491862868 491862871
    0xc0c05010606030207230309060f07062a0908030f0f04080a06050115020102030114210607020f0d03020403050c270a0204140f09010501110705040e0d111b06030414060906 75
    0x864075040c01071b1100c0001680c40c0003076103882d0284041c0d444e11407103408110070795112952500b8486000c0c4002008955103210318200f2026030702d0f60301c0030000c1e004a2490410441c40c4100108481014140200f0901106a0301d41d01d0340a540f00e0f0301c4908407059200640225003000c1c0e1030707106451190090118a4100c14121103110714100c05411100f20300701c3c01d038442400f80c039911b51840601c40e0a5802c0240c0080c1d000010003d407840d81500c148111414100141c91450050340122001c44006105000800164049003021803a041c42d43d41c130213444440400c2014803036072a1403801c0340c503a0b56032f00c1c462284214851881aa901d40904498000e42003400351044404904655502d1818440d4480b006060000d1080f452680780400440e0880e2690040d00c0c054051060000760350f0704c841c02500200ca0040c0c1c042c248409401c000140841d00d64075941403d94005400000e50140c04030400b120a2070945030f543c1c1d40d0b41c46d41804c80c60042e0044100d07899100c2d09040100b60000440d03d103 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 491865368 1250 491864118 491864123
    0x30a05061203180d0809030a06090c080a02090406090302010b0916021006060c0b0c0c030c010603050f030f030103140a0c0621060b042108130f0f0e07030c0c05010606030207 76
    0x10041006801d01c0c95a2400398030000301c0c10700300c0c00c4400f244a18000203001049403042c0d41191800900d4004241000109402201d0154807600340d20200001e10600c0301c00342c285100241481e024940004081290140c0040d0407035640d0b407a0b40040c14070039000020702030006803080707140f0306007400c0902400e00c0b1100e9850050095a100898103030f250b000b41400c5610b10b9441a0a101140c0ca48818400002c0c1040031589820862405000400c0c4054480c81c2114000054000c0c40c50809030304241c0c00c90003102440c0c10402001c2140c0d4400c038183c90540e500020140e500030300c2c5801d03461410240c180d025065860841000441590083d0f107002e02030540b0480e04424280039034458195036050082964941c014841803101d8414101460244044520880807080d0243c98010296001403840c02c003007104100c0510500000003208801411251104170311245844411440003402510010405403503042032502c1a100b200c046100d03d0f00403000300003099444502038020b43c03099004 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 491866618 1250 491865368 491865379
    0x120506010f1a09010918060e01090b1c0f051207140604030f0e0a031403030601091703072405150a0501031e1503081801080a0c020a121202030a0506 65
    0x481e20300209800303807048407a402c0110207803451948a41040d5000620f070281049111440014240f5000c0589000403515000000f0b049007052140c10032108142c02c42860b060030503000400c40c0d201c00307021015030071110681483c052000e140c50614512000c10251142c0f01e075214039a603060315040240b030340c240710390130300e10050091510464445604840141c0441e40080b0303091017080c003984100380f440000500f011710064413030b50703050556074500031050890381c0040200146940c00034107090281100c00101c00d0741c038110b0754a1559911a03402c005180e41601016072800381980d450244241d29115014001817501c03003a076850740c0d02d140070100c3c410070710b4060000319940a8450030190030050800c0c01c2081080c90410301c0500b50340452940400584400040840c0c41c4902802098030f80c0b01c000044550b00030001080d89601810820001e8680300f02c0079001500083d41d0403a0542c009490400c1c00c1039402c06959808894a002032914000800c201880d94030781d10903442102c080341c1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 491867868 1250 491866618 491866621
    0x204150816050f163206010501081801111207020a0c090c0c05030706050603011503050703200d060501091103060d020f031204030323041d2a0306040b040c0e060706020d06120506 78
    0x80c2e40f1030078a80a45c04c030031500100c00600c12544140343d8264010a01e000171602030a600c08403d0840d4042c41541790301c2840850340c0301c0c0c0e028000590300d400061600c0100710a030065110000350341c00300e1181c403a445a80d0281041624020001c440c55150420107580c6c03100824200b6a0140c4070848000e4070030b500e00580010007480341c00b8101300b9a50800c0c010480e1500f50360303541350442d89682c07914000d001507150000d0141e5900c0e50f580744640c071840022509502d0a240f81045d41c86045203600074103000d0041002036240c21108075074298040b0380190580c641c0c80b0100b8142020818a85c40c1100c0004010080c15040b8600c4480141512148441c1c903407018000110350090f8041d00703190926044540c0c0364000c0518080c0d4001c9065007007110001080c0c84450038103450a04940c16508000c400c000480c0f4103440b640480010a9030144040881c40f030005065181c141e900d144a0680400e0781414800c4503410380d40044c09007141040a00c1d1120b1000c0400300111004a60742d129100 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 491869118 1250 491867868 491867933
    0x30f0c0605031302061b0d050a02190809010e0a1806030311190b150d12031a0f13021603030e0d03090515060d060606030204150816050f16 61
    0x30440b4483c4208941801003880c0c2907007045055807225900c414040000794083c2610390342445003507008401d03602d070741e40d41c0c60420030041d003811100440304461324502c0c1c00c800081446c480881c2c1c040002440c0c0240050f00080000e01610541c4d001440908544000a260020580c0c0004180d0f0701a07101d003203204130724401f40b56030365010003000310301180d0105102c000a0b01c841801900440380c0c192420111100502094401246034004d80b0010450140c4203021a058401e140b82c0305a581c071800b40300e20250303001c2103020b110112800d014100350410071086040716070540d0580741441c1a442801c4007031b03040041c0a403650720004203c40c002c0e0813900c20464001c0c410300c402168400b0140c4000038440c41c0f0144000401000c0300d0708030041076800d200080542c461080a0301c46501c0c01a1900d050000000503000400780640a020b5803800380068031400c0038640c050004d85240956591400c1890405140034440081280d52146910310003040000a647c86c404440420b00c1014003d14a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 491870368 1250 491869118 491869127
    0x4060311130e09070b2808090a030e0f0303070f230705131e1e02270d05161805061003092d0b0703110a1107030b01030f0c06 55
    0x40011000005582000304038824100034a0b40d880120740703043e2007810340e842c1401d81c3c06034001c04110301c01170a04a640348040a40c00002c041d1016146050304044c607180b0038103a510b60a83c60701409003e030801f1091402d55035240b0304149904003805598031400c05203070441901c240c1d8042214190342e22101e11251101c00c415900e10380901c40001c3c50860f14100a01150001080e40740d0012070301e8030080b820022101c804001000d80c507407000200b00002d0303001c0c81d401c680c416008840507401004024031308202d8145401003030308011011007182d1040000546c5130000990024140e00916483c0c51900341d0108030030040314070141c0001060040c0500400031514105d078090741c00142c1100000d00240300c2da0004171070a00c81c003180342e40341040030080070f40034021216204626031040710190401106c11141070f0081c506050078840c242c4502c07112112070090008440c102718030a2949502c010381003041a0095400c5600e81d50b0390358413410b007981c40034a804001e40f4014001c48000840920a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 491871618 1250 491870368 491870377
    0x5270307091b1407140a0f050a02030d021b15160503040602061f06050912033906070f0221040602150103020109121502031609060903110409080c0a060204060311 71
    0x1400c5070b444d0250945d141c20b1180b01c8220002c9442c401c81c1100000960000d482c8443d03580a20018031301c0c0712640c4101440c0907082005101190415450300020044c8495010b1803074004540030104620303000b1000f1828000c40c009210b1404030b00c0d00b400305000c004070041007a25081d03401d036100380d543c1d179440700e080d820010001c42d40010010310800416102d0300241c034010500410004490028002841c5140c00421070041c81c4c416000002d01d034070064010400c1d041c43e0120301840040000c5041e6a100c1d04020139070030901090a00c1d02d400340d031003444901c0b140c001480301c55030a03082814842031260000d00441d800351140020f50041c0305450200681269030507515180c0d1341c0d0405401580e11008140201e81016010401126444250000d14864018001c0d50044200940313802099031185901000c03d00440d400c0c24004038920701c55482100f5010384000c5000703e1603160108441c403801c00c112500c8d0080ca2400000c1152580042c4215652a901070101d00210f240c80c10b2a8400c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 491872868 1250 491871618 491871647
    0x8010b0408030f030a0b0a0906140906210322030215031501030f060803040b0a0e0904051c1e02070816180e34090204030305270307091b 60
    0x700744120040f0300004801550300410039900854450410030105044000581100c880d25460780000c0c0510005d99103210f082010440d03400b4114105200865180301c131a00c428590564024034901c2c001e0010411589039444500071040c1424980c5e402420504440c00f0880c411020704003010a034200d00d00540340100000a21012003210700401500100070680d183d6a10720344580c000650110140b01510040c446410031595078010503400511945009142d0b601c1802c40c00e050001089001915107604000310110183c030210014040d1001d404080100d0f0036100006d1030615100c2d40400c3e2001100e0316542191600d0000400a010070724503400344110300171200c41c4400e1580707160381190300030640c00e00540d452003050980d5515601607484424070b600c4003401880c80c440b8000140c0e4001400404011070402b0b0659800920b00d102e00009000003000311010a4089007040e01441d503210401000c5482282e910003050303000e880d520300400544520743c500c488102d40140a440800c00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 491874118 1250 491872868 491872873
    0xc090601080a200711270a090c12050c010e01020105070c15020403051c11010c0c030507060b0402041d1005010801060f09050907120b010c0804210204050c070308010b0408 75
    0x752030601d502c008041d089a0096411101000e40c000504184001d0600c2c1d4001c0e65183d201021440c00d014010b01629814580b02c003030290a4070100100040f90340c0c0000b113005022402c44160309281c0700c00350b16034001e900260840c46040c010400006650b041c81c6400ba01c0340321040e02094016400c80780110b0340000400c04042c2594006807088842001030110200300608064990312001d01e0801981001c7d000640c45400c0485101c0e082610340c400080018024410060345030300040002d6400c1034020240305010401608016441d00560300040740a04210b44660350f58404100041c21007000e40c16413104030001c180c20030380400d03142e400e441042c1c495950f140d01e466412555041d8080442e000c02c03800c3e2401186a44d14101042c4c09002c440d52501401c0c1c5c0c003603103100100c0c0c40701e07461241445008006000001d01c84030540342201c8000b040e6490307208074400c5290350351060b080004e600c245003000308076400703000001414910b8085d944280260fa00e901d081c030303032038891405040c4469 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 491875368 1250 491874118 491874121
    0x60504180b1f170f010c1106090601080705091302041509060b0c07060810150203030412030b01020a060b03030c150a140c0306130912020607030510030c03110102010b0604030605090c09060108 84
    0x100f8802009050070b0800c212008100705944003400c40c2c0c50042d00c540014917141c8030a1014000f00040f541025503000a40301a500d07013940140da406a520505019900343c0c0e00003042d494070441c01003000341c0c000d002400b0007086800c0810a1019602903011880d181c81008106050418185c0d90740d044080028050a4200081692440d4008020500401c1c403500f011401900748108100c0c40700321034000b1030b1207080a05c2c0c03241845804110840c1058a048420740850303074006401807206810003000200b40c1100404a8150720824103606980e2090390b080540070380000e0301a034400c5200500c04c0000c10785100c00785e001da58042d100c44d0100c18040c0041261032400f040c4401d0003020820f40024034841940d9a60150f444000c498405a00041d04105070350b90580506a404020b440402c2220740c1555a000031507441e078000a01000c03103040402c50306074001d40c0900106c550050803151215a24a001e030041c00c0229004e19540c01174894004503414542d20281c000c1030161a0255076 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 491876618 1250 491875368 491875379
    0xc0c09360c180216060c08150d0f080f04080f190f110f090115030b0301180609060204330824040f0e01020706060506040308040e0a060504180b1f 64
    0x201e1034518501c2c1140342d0800c141401c011040c2c20074010140b254002003142440c10002404002009241028090b0400b802c419195954400c1c4964a58006140c540341d0449040c100c000d8003a0303925170340c05e80307000050210b2190f50010340440030401c0a81101c0c10380e0524689840815082c01006002c1c1940c4c42c406000920b10003a21201030781c014020983c251803060000f41d4640342a0312041d07100103d440d40310030b15607050080c0300300004150000d01984d032440642055802079110040c2501e079440d15010b08200950b01110010719003414140c3e540382c0441d0b50038007002030200c0082950034001c10794940c014000c80b0344921401c0e854803001f403540103001905841d09005102e056203d541d40d0108000d20310b182c4540259a94948001a110820703403070284211080e076001148100c5083c00b007000081c02400448055840903100780c0a81d0300c075151900054107a60700626403050030b245288200b8804201191911401381503800743c26180d140f00100420b88078110012075043d80c00040c000c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 491877868 1250 491876618 491876639
    0x10060602120703030b040504150b030d081902040f081f05060f0d030e0d08090a08010204180b120f0318010e0a0302060903070905090102043002010c0c09360c 69
    0xb2118000d04010642030086070008044801c2194202c460501141c0c2a0b140d0804a12a01502d20020b80c01026001c0003880d028110b010f0007007407808000d070740402c8003180300c03101d4042d00c00900140000d45146c5031649920340d280e480f1002401a000941e840b801240d041c280501405004003420752103506040c9070038403103076043c07500c001d9041c4003e81001c2080e545540d042070009078002d0b444d01e500d4804110130003c00c0816513001e290141e006120074004610900c2204070340780e4444100041c4910050081090540080503c0c4468041c103802010148404001400482d034a0855140500345403001901c400c0712001041d6003000c2030308028001424550024402c00d48000c00b1954401d07175030b84483c015a44200c821103096500400d00700010960510722a442c2426100f20301c800c480075501c0701403070b945071000180c10048194141001e11411108800c0680078410081c0002d079074010300c01d10419822140300c40d480c8800e81d026070356001580c098604c0c9030b0703114160400f154906880b419 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 491879118 1250 491877868 491877877
    0xc0613030803071e1e02030a051611090c0a020c041e050c0d15030203010c020309060d020a050f0d0c11060712050c0f1308100504020a0e1305030a111006060212 70
    0x1804c0c09490700d62600c494615001c4148042c00d541c2d10ba1140404589801c03a403596550820341c255481032041c00d100e25000400d64100315420080d510005000c0e0501d1300e494901d035046980c21140305000d010941c2c04000080c440c1c0e40054080701c184080000600c012580d042889100b14131540900701c4040240d608129000b50300d45000758145001000c004048650400811a51a05290301001182400c1c0154110100d01d40007650404404001103001449202c00d01000c0317a50014011003001c1c040d1083c0d400c0c00111059403610307400d156a002c402070070104400b5000c81d04000000002260000d42e07603202da265503542182343c062140c00f0201402000e00811004e01081c0511600001c3c1c83c8083e0200d00c9076403034401c00c1c47d864008160b0600e0000514a05154102400c20015890345000707103084400541111035582d8400560800d49116031900030100c3c0400901d0000341035001c4041d00d00744070305409803008074190f44d08000c1110658810007000d03801401181c0701c188112000340 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 491880368 1250 491879118 491879131
    0x307022d1c0201031a030f0a02031209150a020a0510020403060515030d0e0a0519060906050a0905091504060b03010504060b090f012006010303080a0515031203070c1a01080c0613030803 81
    0x1e40540c0642001030700f087d2080750703804080e51080c080c14080d032508116242c0b0b015240590343e4580f92200010440200d9030141c035814900c030024015900c03078401c00c185008250400c0079200000510740e4401c020b9441444180c0f403003424000070401c03850480c80b00d184820f40040c02068265201a010360706030109a01c2c0a0340540312a000081c0c13504c0e010080c2d9140c2080240d5500340b14182a4040c025091940150007000b1040c04042042c50304021100244c0b0401c0300c200f840c1d0b40d2410262104aa00d11103640d8019040c400002698800980510f041c0c031401c0354144000c586550102e1058081c0000b141d40c00704008007481540e5018094001155a214034080320001103100300c00c1c034000080e401100090000801c0103030660751845100d8000301c40c0490f600102034403100003644c0b090300580c0c10341d00701c00010100b80c80f2400380f0b942004031030384070790304c2821040080014035104009100b00344be1402500c0700031000d07142100032201d0000d481c5a4102c1c0075401c0d902c9600300f80c0c0005000c0d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 491881618 1250 491880368 491880401
    0xf0219080c2a07060f0e061317010b09090a0b0f0c041205161202010807031a030a0302060f070801050d110303090409051b061c0e0307022d1c020103 65
    0xe0604070250704601d40b51280c074007101c600e0300b9607450720304101c42d03004500700a500b0103211081c550180c90120061022100c1c0c0352901c409100c0b400da4010315910404046c01d8580c03c1c3c402d0000103401158914200700c0c0e006000e96100e0710050740342c8045010040c0b03120301450000b950014050300042d0025101c2e60040d04054035008130301500d0f44115020381d180c2e406801c00b6140b114145002c0d0740501320100165015254990000e800c0d805c014050342d06051722900b60007c0c0050112003050f04c407400401310781800c451030402a448a409a40c4201204820400946440c1c05110942c1c101c2c0d00281c41f24082c0ca50300d8640402c07010307040d003802e941800700300328007070880d55940101554680514050210740f01800089000080c81d8a00617010f10014000440b03a44940c041403100c4804040b4003050040d5003042540c00c610405000961021014260b403814009070f02c141c404d00d456085502c100c1c10b45600400000301000f2030108104035010010341c00551080e0004030007907074500d48 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 491882868 1250 491881618 491881627
    0xf07020d1805010c050c06070c030b010b0405011407020409050313080606040c2705130204090b011e030902130f060f0603061203030b190806061e0306130c170102030103060f0219080c 80
    0x4020b54040c2c94191420b1270044001d10901c204409100c7c010124400c2143c82c05140c980060218880f142c803003c2c480f400840c50070107544454110b00c203503d6000c0d064aa07075080c0f440c035085070185a8000d003003a61181400003a1281030034845e010a0450584a070701c8861102c890507241100101c004000310310b52088006040c0d143e100300c3c01c030920400800503844505241040e821180013524480c10444040c0913115112145040942c42d0072203854045010901d034008903c003480030307418220b032481c5803101036004c0c0d01c0d05038802d4094844211890f42c41135a9540114195180783c001c14840103141655800044d002e0380c80b203021000b024280346600350401d08072509200c90359100c514190001c90030400c07180f400d038801c41d0440300c5540c080790611072240080b80d92604000e1040707807001030030b16842d01481100340c5100002c1800d04e240004100c61048402d000c0d40081c4030031110142480032610040002c5e0080c0c4082c0045403c5100c4145116501112000e00242a040241c0340400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 491884118 1250 491882868 491882893
    0x10809030316090b0a03020406112a0f06030a060f0b120c090d080a0903050706030608030f0c0307081321050613030e04060306050f010b040810230f07020d1805010c05 73
    0x18064040c0b4171454400584031031404a006d00741a070b54203109509078001c1d86014003400846d4428004440200303801d1200c04c0e02d0100400d4031a84110201544004080b0030410381d00041d4100034141e920100f0074405455827050000e02d0f0303000d42c014030961141d108001881d4407154002400305c1c144000c01080e0400a1901e480b1001d511400d2510b000a8400d0000d01c244074040000c600140410302e003c201d010b00d00910755440b0300500341100b120b5a80044d8070b00803c2010002e8408903604000201e5a40d9403c4c06103c910100902c68043c40b240d041d43c0000116081c40c0c100400c45811101030119955004407003940040e0883c001c506100d40180d101a141d01d0790310408001d54400d4034001183d0915980881d407880c0144c0c440186084100000d0014030310100300d10041105901c004903242c0003042c5500072001c1d6800c0b00e001c1000880c020410102320301b0007040c0c0240a241c0a4038070138118451f0448803958101d9415680d9518103100704031310b510908541040074000c4098601030000f02 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 491885368 1250 491884118 491884139
    0x130507090e09060a06060906090b0c030424020d02010506100c1506090e10060308070b041a0403121508190f0803070203071a07080705070f151a01080903031609 70
    0x15605103006034801804c01c1340d407900601c103140140029062064043d4a800740c02404031115002c1e0702c100b40004100000143e00070003c3c1c0d00034154561012110440000311036150061b5400440d0040c400c040f00400650f00603c10715000305400780070081564119102a9581e4583d11411916011801a00303484d418052040703c000e4980140f0110300028003100b101e14212900d4120101c052400000b000014003410803100d01c154010b80400040d0354a00303241d1140544100c0c50581c50018404010030190303c0551380218800103402040403120034a80800399404034000c00c0e4699002501d481141124002040f06071403084948104014465882c04001e40055403e1b00c0542c0c40850f001d400c001990340741e41c00c0c0c14204c6807043d80f82d02e0302d02d5004203140400b9002e6400c4c4203000075440284000c00300d01401844c2c2103c035001d0114001c40c40c4900a00001c41701c0c0101c019103d0036207400d90302c40c1c003049021341c1a12000754103603100c6080c2079400310088046072061102c070380800503502e40030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 491886618 1250 491885368 491885371
    0x1e07050424200615121c110102070b070801120c030b060d0c030f0b0f24060c2d0703080d11090a06050901140901020a120909090c08070608010302130507090e 69
    0x5002a080905001a8110041c50f8134000217101c1c007815031002805000c00503408064207040c1803c003048a680c0d40041e03485d100c41884003561175000050200078840c0e40c01c10240951030640c2d48102d242c0c1e031070310184e1100c0d201f0b10700248070b28411402080800d128146058226000400b1011003010326030380d0800c008420761044849500350350612050024100c040d40c1d110016400c440b040d40b40100b014400604078032031803030385004080e00c4031040e034640341c09448004601004035000381c0c2c9141e211070342490804540141c4150600c400140700c541c00700c4c180c0122640306501c0c40c1804000d0840c00b000e00121410319a0046080c001e05201350380e540d01a10040c20283c5a0320703515021400010001000700701c00c152400c03070401502000383d0340002c11007850350304a144003e0180180400702c804a003154404428281082d503084144840041440c00b00c8408404443c40705507101000d41d6001c034243310103540001901c02c072108582c115001282d110b01c3e5482c0051256886510084240a0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 491887868 1250 491886618 491886677
    0x3031a041e06060216170c040e1b010318150b090f010303020606040b090103030e030f1c031a0102032505070303030e0c030111091002070e1e07050424 66
    0x7004008201c41e0303169200340c001415a610240000d00c1d06103020607600c0405109000c040380f911055a1700702182800403e800c1c2d44018001d0184942c000d8074156500803081c0e44d07001e8a0141d042c00600ba602a201e448a205603988a41030407100544824a00143c030031130002d041501c3d0020a40300766100082d2522404040c02e070700c5107035411420024a09a0002c1a00b406180b400300d10b52081e40d44c040813981160303494504240300101c2480400e0401c4c2d001604852103126002c0b4000c1084101c0702613164001342942e0401600e00a1500c108144003d0210359016130810006003101c15062040c82c25007a058208003043c610061b56038602d00b0b0a26403054000968401c1e2801c8581000c1c0001004200120700900070030124135000340700da03c241d20300b0900c144401d01190030258000d110f003c00402607450b501c81c0340c1c5018800c840842a440c40d441015004007000a80ca0500070b6054605030383d109104103400c0c0004581417200c03c603801050701e060194074403140c5d9064488204000c00b498 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 491889118 1250 491887868 491887901
    0xe01020a290f0609010509280b1302031905061206010801150e060901141c11010f02121e1c0605030c041a060d09051204030c09060302010c03031a04 65
    0xc1c030300e07003000c0c55004000d40340001202d6040c0030f101290303a621181c00d05440d0100d6040b40d0680340e18089910031010280c2c0c800640e840c2103c5130520081c0c5078048540414252039801e240c0e0120040c2108074442115041400c40d00d456560030402e0056228623801080070304003001c2250001d2800345014400da1003400240c0d10744d24a0104092100d004400a118070118007000741410ac0c001002c4c04014040d41c0490840c180c2c0e4290a1340e25801c0c0603614541d00542840a92014101401c40c100039008281c04900d07079040480301036200103800844003094050351030500c408540c0c0c04403003016259280070003d100340710540c2804c0a2801001c01c0c001012000100d0901d49800e0508211401c0032151203540351260040010040c0002d14900660449100355030f41961860780008080000c0d010f80684201000c001d09079120700001c10550340940d00c1595403a9403040c030700040c1e852901000340040c2c8122038240000e8001d8103e401030031440c254460403940104040350494003594404071868 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 491890368 1250 491889118 491889173
    0x30c0f06021603020d060b040f0c030518030a020a030f0507060c021b040b010c080c011815050f041a15090702010903080c04060c020d0c09180308100806070e01020a 72
    0x41d07010807030b000354640c4048040c00400e10b1600068041d5829850181403640c41c2e071a80d4840340c0d950b5206422420f07802400f04461010074a00030002c00c41207848074158400c0031041440b40314008103030390314540c1950040c04085500c2d030341120310682c1081440240041400420001501c5020300090a0700310b03030007030841e03c42c0c0c5402203070000344d149801806545001c200b01247e90340030000100d010340050f81c0f195070b152140d51860052211071080c011600800a100081000e51865034002c4003680000380943e03100e03080d20588d0a07409540c01088400c40240c07801c10704004200f1039503c20b04418400c00d1800344000400c83d6184202d8120703005035501c075031182c20150007031910760704400080c90301c40c1010b0410300060900d441480c4040d202e0080b00c0d1046c000c001403640e0000240034030203014000070b400c04022804500d0002c07011000309862400049881900d04a41c8045490800040c1403545801500f5220107500035200740c11801b6400101001c1504042c10b428261110506070714007 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 491891618 1250 491890368 491890379
    0x806010b0715061d181018060905150a05010b04030204090201020c0415080f0613060b22020d0f1e0209040e0609071419060503070504031a0405100207031b0804030c0f 73
    0xb610b0003d101c2c0c0901d011308010421741d44c03c0002c51814039411070700006484080d60078222008100c4e40703801040281414494030400c0313000b15003050800001c1051032444c0d1181c0b030f9802c05a91b0240644080b00f80140020130144c41c2903045504880e0041c0150b50764004d9180101c1c003510907401100402c034103a0365003001801c404101401464102a0185c100c5046c0b00d50a0400d0540300480604038603214904c001456644060365003198054900e480c00900b201c2c0c4080d0080e4100c2e56041d4800b500c1c10181d010440c2c158003c1e5094001003040d40c10710a1420b0030140000d4014188072500325581d61814400f0090800110340141c1154000f0280680380a0b0a80b0349034982026842c0504011044100c0c3c0581a00450096500d9070514039103940e1800c008440500550b4005401d00d034000c1c050540391004081071601a5000b942921040100107100000ba482141001400600d440c601c0c2000615861107140d0054032031440c5600e0030f6500c1d104d983c900e07041070b00070020540800504216 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 491892868 1250 491891618 491891669
    0x2070b040308060103020702030c210304061119020303120406110406030222030803010303050c15011706010812090925020f07050114030a0b1f0507030311040806010b071506 76
    0xd0000c0b09203400d40c80d0031f03d2076000c00d880b00b20b4841c0c840e00404136541e184480503409210840007005000c03c13691242d6440900910f582e12040481126001d80d68195808100700500b1244046d00030f0002d51038200e80c1d03001c1d04107200300100269040382d43c1d020044640501c05006100500055401580b11000705c40c1c0341d60012801070742404c0d14100301c0c5003003001840301c600341c1e030449802d81000da880d010051002c908201e030140c000583c07024150004155a00c0c0303081c0c03000c504c41000080350708907038030b800c0c10720759440041100b250300400a20682580b81f800b600c116074070070750705941210141d01a10850500400010303140000d41c112203022145d003401041408010402440c119044882e0a00444140d10000d89241d00040e100e85010410b40c656859444605d5140003440c03070b000903041c100a0450b0481d41c2d086000900740160b10f03c0b000c01e0141558183d0b00c0c10409400030741d180c1160106654450001183d1035003a051820852455500c81d0324014501000340d08a24040c1251210 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 491894118 1250 491892868 491892871
    0x10e07020c06030a0b0a1415030c041e0320011407080f071110230706150902030a0f0504120516060905030403300e120f0d0e0a140103050c0d02070b040308 68
    0x20142e10050071540349946d8415240c54030323040040c07c84d17941c2e407603c104020081c4586e810a29402035803030150480d104455004e202120300031a03116407000942d0300b004566030055011140011f104a40035480b0001c0300c070042c0b00700c9100d2034405180040700c460310091500b08820903184020240007244840c14821410321031030300b50745895291004461984030b08000f04d80d820b0080004040707640385c01c010841d8041000d8404030021103c5941c0c2d0782c041200030358001c5a04401d1507007800c0c100b00051400c0d010340b500942d40a10006c10300b000258007169560488901c101100b6058449500072580300c4c803400c01400d004034081d66850307065081058020524585110805507000803080310045000020000c000c0d0b50700e400da0910440700005019120907109100c0e481c0501e02540d00740840c006a001c160003844d84910b100c14030040c00304440d5074594030500041d0b003100c1851109a40c400e9002541c425003210100317041055002c21881260030081040307030009509801e120a0542049009 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 491895368 1250 491894118 491894129
    0x151a12131b06021914010203090604060605011403041b0b03041b050f010e040e0708030a020a1211030d0e0307080a020a0303140606090f1c240c08010e07020c06030a0b0a 74
    0x4100c2032804000a41c1d44c2810303000c041000c2c1d181d40300001044644651003114900e080000d54036410810741182d1035903016242103400601d0702000081c00d50281d80600758400e914444503040d661360791207254590525262090f149000c92001241301f035400b001943c00341c1c0c040d49403054248180080c6145404054010718032035412580f15403101e82e4054181b2038484001d079401300c2c000038a83c003d02c0c641f4080d0340000619010101e0380c1c0041950020740c3d010194050b24100003050340b0301c002035940c00e55502078121250020015502e4080c0141c00204c648050b6200b12407074120180c4420038190400f049040060b004000c009040c1540350140707620b4800d55400307110480c02c0c8100050003030b1249280c010701640010104880f2542c40030303410080d000014016100d500aa0303e06800c00b041c60321020011000c182c0000031201e1242d00c00c407400c000040d1a140e590742d09201080c00000c00c0284514114441c1592a80b05e0f911008051409076401c6035012a42ea884042001b08183c40d54002 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 491896618 1250 491895368 491895413
    0x803150a0605041d0c0a0c020409080a030f060b1207050a11030703050406120618090507030606171522020613030602091c050307120c051f0b0301151a1213 68
    0x2c3c000400e85d0401142c2e01100e01d814a600400b6403440410054640c411014111050103c1d0020039103804d50400c902d0800300100401c60a5110800300555000d1040f0003030040c220040005d40c114000c2008049400c81c605041903411880381c030007407070b5521005044000460214082140c20707002445110307200d640e00d40a000260a20700d11545d903c0001d02100a825200e01c801c0c030034081d0a20400c40a5074110a05000341c5460b0300004070810702d02c02205003140308e81c04c09581070484600555004800e91000414240700340342c1802c0710782c0c00210059038000c0041080e14950b6074011030500085205110160f2958203900c200200b80300c4000250083d50440c5201e880058408400c4815640c0d1103100f2400e103101c000421101c0800742c0000509500c100041140c500d030700b0401a18886403010030a000c107980c0101498203031101e25541d6001d84030300c448140404580a9550102051b403152410b0420b5086900610800b03019a41090300c41000d4400700e06001c1206811512554400203 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 491897868 1250 491896618 491896621
    0x30302030d0e06161805190f0e0f04080f09030102030a06030519030512090c031501090b120606010f1b0303140c07170d060302040614120105090a0803150a0605041d 72
    0x22000b00b000040204403081108174a944130b408074984101038090200500008690906c0749440d0840020038050300a801181d03500000f45003039007102d85489120412500841ca03115560b5442c2290800706400e040c00310280b00c08003c0380c0302440035511442c007a14002c41c01c0d52031402d04c9420f14401961001c980290300c0f101401003900141125801c04240c026040380d41d03141e241d1281030045060215526000c0c07000c0044264118403413150580741485010090200d0a008128104240c6e011070740440d0045800038050f5806031018142c848460b0400d00d891805444510205450f072410480100340e0311a1521102004100482d2303020003000100340ca08001912020050056450007441c1900c00064140440a4030780092000303650180040c810b0548402c042d02c60800414482c07400748035114403040413200140940b03406a251100640081100c0352074200d0580c0c001000900c507071040144c004115114069034500500c2160740b6982c50b1424115080703140d0510200c12000c5c05d443c0750 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 491899118 1250 491897868 491897881
    0x510051305030c060f2208100b010207180c12110a0318020906120f120a0f0e090619051f120203040b060f0102101406010306080102120f041b030302030d0e06 69
    0xc01722401c840c1e00c845295207030703002d0140d8649641140501004a18001840081e580600180c10740b0785401b00c150501c042c00e281001280c1d580781c580b01d4207003004c45040e50140c8112040d4404900c01410341b404004400c00c040c084801e45e1519a04840880b0000030b11001c0e090303041c410090401281116101401c5660300012212400035203064401e8200f1014011094410009406803440d20400c1d1550f58600480038045900f00008441c040303441c603c410394200b0310401208000d0700000301714000548907030090240416880030b00c00b44040300a20301044983c1c0e69a50702d004110018000e20078103100200c014a40100d40f255841e5590051081c03100042d208009590701c07a80c140c0c0c03c946d040c0240301c0100d103814001040d8860f518900301904032040b840030304040c881c400a803000c0c0700c503d9485030b06508038455a28000042e008100100f0100708202c081c2d56001801650020102c0c0e825949048401d10f841e80308030056880011401c0594040340148840b0110f8580030304010300e01031 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 491900368 1250 491899118 491899129
    0x120612080f0307050412080301030611030906011e0b18240a140d1a030c010f02070b07140d050301030204110301150f020148020a110301060510051305030c 68
    0x200000c0d4841c032010000640c81c0f4450401e4030010700007000120358103011401c050003164000c5c0000c2d152541421030001c01122150308603809820800d0003094260301e0300c10f50100200034006688030200c80c245001035050b0154014000110602c0c803002401c0e8101c1c810002c840700050005a10b0042103502880b0b140081c3e01554581d640b1410440072428407080c0015003442202092402c00e460710103102d902e0702c40042000301c0b40e141074048411050b0030400640303c01c015006030710010303800745500f400070307081043c090103c0d00e102e6031504414883d00781200b800c009004840c040040e9000c4010019850103010b10f04081c00c1e00804589594145a04001030518803c009024000d00d40c00d00a40503100b50b1044030102c550442034922031079058030f04041e00110010036005e015011100f480e800002c1c0300c540c4070340000c54000f070940da82c0d281c0d2488c4100c02c0d440c59150f4036540c0c84c0400502c41e203602c2034081220002d80d40b940d9a031141004203540d81d01c00c50300810302981c085500c0480c90b8940 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 491901618 1250 491900368 491900377
    0x1050f010e040f11040f0501080a0501050a0b1e030304080616020105011217030619091406040b0f15130b0720010914040f0204080c1305060d06050c0903070612061208 73
    0x50344c00600505841c010034050040303650801c181034601130000400c100e021550710101c503c030740002e000030b03240c0c3c4c51074070213441d02800d44503400045035101d14000c100360018964111405000d0f42e00b020303945c401c01d0742003881c01c85d003504001c1c80ca840442c0c0704684c28810207000d441c40e84c0805401000310384410380d82c42c0340d40d060307804012000004101d4603070361110942140b01d034800d98003000710340b22050700001e002034201c080d0090350003201203105441c0c00d00420701c1e4600c000c4c02601c2c401240300108030b08401c6150030399071081c00800450701880e003020f401d24090050038160a0391156a8501810414000820f40701c150174600c0d00044c40303aa000304c0c0981105c000350300b1580f0340c0c050301000074010b024108905542d01d200180c00203400001150b241003100086503149601d80c2c0d031080c0041540c1d82203445c17580c40f00407a100000040c0d101c1c1e02054020340c842c0c408030704000442020900c0c1c100305e600300801044044103c0388100501d4040c907070140c445200400d41c06940d0b0f0365450401e004 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 491902868 1250 491901618 491901623
    0x30705180111120d0b0604180207020d0c060e010e060705060105300c01170f04120e030a0c380c0312100e101202100207080f01050f010e040f 62
    0x10241440c03103a00c540c540001a40181e4261001a0410903180006500c040d80c116005410060104120703d8100e040c0c0b0100c4658104040c16880d10200001c0298040c006c1268080d410300014070202c1c010085620140c01c07a91583c042d44040c240000d4690340000500f548141d070100480400104041409411120203135040c0d102c2021104c44206503003807078441051180204108203001540004001c200c0708400e0320341c50b1007219441c406420040d400c41c0c3c80f078801c0021a0101b4001500703030815201c50b4290746407101e6040710080020b820f1950b011000c2c4c039925200f000510524541903125a03c0e02039402d02d02030a5017504121038031b04040740542001880f804641c1d02520801032049807806511031600304840e1411418842d03201090f8050030001e00c0d0600c0010740d4107000541410b00351544d0400c1c210030b4012170b44c200001c1d40a02c0c00251300b1402943d40010302d8200405c200283c2600e40d1001180c2d0f49824040e0b00e510110581c000c1489404080c2400045204d0044e10f150564 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 491904118 1250 491902868 491902897
    0xf02040507050c0f0610120305071b0302040507031b0f020a0f0c0306020a18091a0f0a030804090b1813140c030304090f0c14040b0703020a0b160f0203030705 69
    0x41c1c9010080ea07541c05030381c603480d20ba400b03100e00149029030041910342c81a01200c207040030145d21114062121501d0040080c042001000f03d940810701c1c081c1020f401090700e61342c00e803080d622680401d05446054030740c500480e071264003c0da0007404001c1411074598007481c203410703409181d034402513440f012050068241c11040e6000f03410300110131040ca018540101055588040b440c4005001a402c40100a5038480070f010205044805000701b5a604101f409455480d10003d070410501c1e554411170198000c4010340d0000c00a0725400103800107010070300000914010790030a0200c140711000c50b40f01000100c80410131212800303a0289040c64000c0315402e41d50322140300241c40c03c1c9601681c540d0511012400140049030380d04419003031a9038140c1402202d495400c06c0c0c0d10110124040300c000c0005000078800101c000015190301030107031040356034802c06a168025802e07800da540c2c1c84800300d4070380ca00141e150070020803415a203491008519514203440b0003012405209202d02110 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 491905368 1250 491904118 491904121
    0x14092e0c0c05010309020f1807020d170604020a0315090b1203090618010528140315041e11040f0e011d151201050406052805221109060d0f020405 64
    0x1910781c0d0003001700e1f13800064072420781d50700e80e146a92818401211800300511558041c92001449840f140c500341c007040d040e4150a407100c10411029400c170311210801c0603952040c0700000c40d81415501c0c01800381450009803880070070184040300300b40c0481c4907043d80c010002541140c0310481200c00f540a02200005000010300c0101d1f000d00c5200340300d00c40200035440711804070f0203a10014180c904140c481400711205140303803200e180011203001071102104004044641403e41040096003c0a4500b9810026110014003202e011060101580c07001140600000240d161020064000741135454165890000100d00702c0031440d20076841460480d0104680f1f480c80611010892001424600701c4005044458000c0000b283c003510100d0809000c110004044c000c04980140d0110849041c0789401407440058000034203003000c921041101011301265015410000500c9a040c003c2001d0040c010400d40c043d014206901c50001d010f000c2000036008025854810743c141c4000c03ca9 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 491906474 1106 491905368 491905373
    0xd0801030320010617031c020c071206060b07080c0d2303041502040305070609150e042018150a020d14092e0c0c05010309 54
    0x89002c0951680c00b11000780300c05440c0e841107a001203030443e911600302c0e810b00510317810301c100e42d00702090441c001303003101c040903400c03101e40f0100303609024a0640441d00d43d01103114000d1301003800c07503105080110a801400051100c41e180702c1d20344115040c0710042d0350201e1252025405081c0c01c0030810b50260130400008101c00361611030100324800e203440700340c2c0003030400d4a18000306280b03588849180d00041c005144208080c0c0007030380c030706080a01581006d400207504500003443c12101c20b540440c07103a500ca0340884021400d0048400445011107002040200411000480700d11486085080e00104c0209441c101402d0244070200e0340d80703029002c15000181c210400c842c400303610a0604090310300826a91a25103030000d0b00203203941d00c000701481c0c10780c0c419040c41d1030740804900300c1034986000e03400c200e43c030994603a841e40842d003454083c0a0515070380b003d21406 = true := by decide +kernel

theorem cover : BRFrame.Cov 491726618 491906474 := by
  have h0 := BRFrame.cov_init 491726618
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491726618 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 491726618 ≤ n) (h2 : n < 491906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
