-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0115
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:55:15.113994+00:00
-- url     : https://prove2.me/submissions/0bce06d9-4c03-4c2c-a6bd-080b3571c1f8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 20503603 ≤ n < 20683459 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 20504853 1250 20503603 20503619
    0x40f030212010204031e210e040b0310020f040e07080408071103011404080a02010b0301020c4209060703090305040501081816050102060604060621020c070308120916050105071704 79
    0x244941003107404059170a402d04c40e01da28401d18059069158988c5c0c40207403800c605000c0201000030b1081d0303040c440d039800048003118a20043c400354400d0305a181d070316810700e02c12510513000504504100081e460802000c40e403510196440103030300030140c140030b1100100090241c0079210b25040722542840a010800c40e00400510700000305400a04c20031000c102054200d018243ca0fe0205801003007444401c04561548210040d565400040c409000d940c444c80014080700d405400b0500c0020500c221100104000c2c0d0740220f440c901800004142c0c0c0d4002c049014901c5618180b0054102151841520b03006100d28000414110f91407220440c840f001c40451502c183c6000d4000c02000c152241058000c03081664915100c08040803800004035005510306040300c0c5c14240d080c44030360425801884000011070103400310030780b42d000740d0905e1604081d010f0201e185a50080c401803100d4500c1c0002e000840f0000d09201e5100e290700d0504101c8010818140c0034513510000340071440320303 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 20506103 1250 20504853 20504903
    0x10905011d06070801030308010504091509030f0908010501050a03021318030806120a020a030b2502010207020109090b0f090a111303030206010605040303020c06030c0c010203041104050c040f03021201020403 91
    0x5080004030b40c0c0c2d940300c0080c1542c0070302080c00b0103400544104014441800c140d0031854055100d10013200e40ca41260b40d0300310450340c4044040300001c20003400c0000c9913a110094201624802c00208010751400001600c3e40342c2602c0300070f0140186020242c80910243c2c8541d03401d412107072800d00c01e11841d01d8002c1c00b1000c201c0c0c2c12841038920301d111842100e80060b00103c200d5000d411203420909584607640d50030402803100c4c900621344c2e06500c0c60101d09900d0b690303d0304103d070005a19503000e840050401002504240e15130340c40c081045000c1d5a07640d5482c40300b500300b90b54002840c0c44e100b000c04044c0c0000c2100c4800754038002250302d9160840003080d4102c0c0e00175820b82d0b00503605c4640c202c810f0302c1a0311001c0e005900000034080c15180c1000156040000e070081c0c00d1a004c2c15141c0300c7d003660030494050f02c0e000381d0b20021007002d08081c010300c5c0d403029440e04400c0c586802d01182062442480c0000382c02258503484040b00c6e1042581103402864100084000e0035280700000c90f000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 20507353 1250 20506103 20506151
    0x50907030b040e150402040f0e101e021c09060204050604080304030b0c0a02060f060d020405090309030f03091003111b0d020d0e0907050a0314010603020408070e060102150901090501 80
    0x61407070b080031150003400c080781401c44e207800740c00c0500003521942c007004058088010001e402e03a07552111050081d0b0204860896801d0043d4040f070b103000108580e807603590800e2003500c4414010001400214002c60808041c04000d000000f06a009030405000038000c0380c001e00d401200008011a1203070300040680200c6c1d100b007245981c90782c0c6130b40c81404240118149840581c5c0440d020488064420054550000d0702600c40008450346400040941e2029a44210f0542002903e03035030390b0900f071000302c0e04503101da001507240101d2903011a00520075202078804244d070305c511002190399441d0454901c06440c0c603502000a50710b41c0883d07100d01c112210345025200b03109418a070907000300041804070742d000340b0072421581e40c004190780f5907110181741c02c00c06681c1ca8020034080e1700c111045001e01410b0b0380058980f8280301040303103000d9031600502d070320020000800400d0303a400920301c2081445083d02d0348294698100030f41c0500b400c1030300145a1b500b4401e0181c04a41944070301504 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 20508603 1250 20507353 20507359
    0x5190c0215091005011d04020607050a0b0a09110f100e04060302040207080a0f1b0f060905011508071d01090c0504150201050601080c0a080103140c03150405060106020d0c0615050907030b 82
    0x540e0f6600c0710420300c00704186d050031440c98012000175001d41340400282050f036004bc02550b000c44c3c019541c2c00035880c03040340c000b901d85545c0c80707500d014448860300f075490f070140564441a581d03c1d2100050a5040040d800104010300b09500d41310350f8549400c1100250b030b0241055403940d20342d1425051980262445900040c0780168500080703124100c1188280c461160202090040751601c0c040040000303025184149c5074144040025000d214a100000702620b0241d00349041014040c1010207541c410700c10000e1100404410742c0071401d54504454207480300085081c04c0103c140d88501542c1d110303a0b00f01d070303290300129038090b01900014800e0000342d07030380c408a03650014000c03800d01a04524200241d20440144001410020140b1951182904580c00f02c440080083d1600344218114450305208200b8031007088810070a280c090100b90000c1e1100d0081500014030340415080007800640d19085101440c200040c6003502501c0c01500c41070079071505d0900500507103020601240 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 20509853 1250 20508603 20508611
    0x601080618061302010c060204031b080106060509060316020a0c060e01021018020f0109050406090f0e03040602060c07020105040e0c1e0319020c010204050301020c0a0b0a05190c02150910 82
    0x5100800c034a8071900c3c050040c82c06202050300110340c0c00c012050120760030b80c1e0802001c404603240441c801c100c0341040c1d000e80300e2241401982404d45e00c02d0792141e420b0103400d0002070b16654500060300c2c2c1c00915412035425408429408a181500c0300c40c019000c840101c1001c2072582c0c2c0300c7c00c800148142a001c440741500f009100c3c1c01100d2184d9803c030500c10040116100500c2d141c00c0c2c904641c07005140400540341c5480004007101d445500020100d5503c0400e000042c00b20700941290104580246041c1841c044000c2d4641c00000c06080e9031307910016070502160700800907203028001000110502d443c3c07011b80194180e00c660414081410425003911100e4182d4048a2142011155034007050b034100301400069000f01040b0119950244800300c1c00741c800344080c1000200450050a0001c003e050100ca00c030000b51054586504000030813a203588020b1902d10490f60701140041c1180406030300700d051003040a10380c0ca42e150540181b10548c000000caa41c4c40c1270b6001c10800c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 20511103 1250 20509853 20509891
    0x21e07060b030a12030507030605031b03072405030c0d02040f05030f070303050d0b0102030c1005070908030301060801050d02011107290405030709020f040b2101080d17071106010806 80
    0x250f500e00e40f076940208014040007a01c00403910a0b0882ea80000f014100411001e85a0300024244107244c03103540c03004c0490b1400c10b1041d150810045008252640d15911049a03989500d185004211000004d000001002c521404150402c81e10441c086041c00c5482d03d8031603403a088901a10300c5030034402c1c483c07180c85c2d009609004c41c0311170849a0580b64545070a0a003040c070000341c04e00412079415400305002e03e542c00f05041c00b50004c4c1c8031442400140f5490805405040d5081030703081b06201e54010710052042030341002d03d103810745108850b505074111041c401210301e1203018a800f50a4040d00000041814151140c103e4410014a054000c004024860810707401030780b04050b41540494420000302809500806114280c034940130704c0c0540ba66800c071616408004050b1324101d01c54007600304680b4100d01a405020480c0240101a11008004104440140c18500c3c0840341e8004901e2040c0180c8a0090b00408102551a9513035201d240c142c545008454082d03001da0340100342 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 20512353 1250 20511103 20511109
    0x406080102090108070e01020a020301090506010504060f1a07151b021207050705090a060825060c0203060402090604020904112205060f0a2a03030b0f130f021e07060b 73
    0x511007011060390388034107550b2004001c1b690310300c08060341410b601441103401d0240c0c9003070248007041e0b4000c80c01024154501814003080741c0c03d0764000b03c12114040818040c41140c8500340584001d0081410b454184500304800781104016000600e40c4c649008041a594000c4082d4070012864013523880c92645030703005072118400c20300002c00d56001600240f20501c2c0c000120754104400340350002d280780e1651440c0307103800c0100c0801400c00e205240c441e000c0445401100002e80594a090100f90b06030303601081d91010083c02c000d118903a4840061401d4480b6410303260800c4c0000e10600c0074000e0110b12040d154061109116038083c000d410302d151510120007a0101c3e01c0c060160741c034103901c09210610682100300481e041243c2014542d01601c401d5680205050380301d000c482c2c20b0540340c42d0150840c3e035845255401103202212800056490443c1102803985400d4042425000402400024840d0f54191901c1c552490000742a04818001030107140d803041100308a880b06203810 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 20513603 1250 20512353 20512357
    0x106030e0309010302030a091a0103050606010c0b0f070c021003020d1407200a050601060905090a05090304050f010c0605070323010b0304080a0309052a0603090706030507090b04030b04020406080102 87
    0x1100e03a6503442007050116035482503009642c0046507642c001260141503440e50401140f100c41102105040001030080c480e040c400142c010b507090078075103c04130f030a50700c8018510380284100c107110400c0340004d140a000d800c8254019900a00c1d00720060100f14024000b0340028145030300003881e14000355000015460080d00807991038440070402a08002c0444c04084400015092405001e044000150381040300314041c200589035000814140020b1041c3e41c50020b00490080741008148250180040102d80c00d440040d03d506c02049040382c01030320400e4049500030240c600c0c20040001841c2d00d03610080043c1c0b00784840340d020008502548072405801c1c040c152100c5c004001180008200c5401003464003030b1414080b8000c1d00940f45c041c144201c110302c0d6142d09031032105800e08408107114102c0c5600d012907440342982030030480c00b0b69810150055806040d921408a03049138001c02c158401403001840083e41c2d01d460b0321b8020094034058604a00075400c000e4041100901802 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 20514853 1250 20513603 20513621
    0xb0705060402150f0304120f1d0108070201020c060901090201140301030b060409060f05040b0603060603011e02070c17070504050109090305090d1509030306140303040e04060213150e09010603 84
    0x103018a07103440e001c00c004250444a00103d81d0000c2120306080140c85010314800c900948424000d9812118082c00c0c80507240c003086d003009110690440207a402d01c01c8034038501c0c020719024240c0d5a820500780d009210300d2180845030320036403040005031001508032584842c0300b0b0b038456030412001c50f8520b4050000380001002d00f451031000805a081c56030082074100d00132500480c14030300184145044410941d015103900d14481c003049100c0c241005003c0c2c000700294000c00c9910100410400d02c104c4202041241d0f0b5000210142401803c40200d40503020384003510009040558005035151454131821f8011414440001844001445940711640e0551036862420030100d0800c0008104034070116440140c100002840c0340b40c1e0310868080c0c40c400e40700007038402d042030074103142e403060050204d2007035104020030f00054405565a0381c005902010168940c1c1d200451134400c03a603241c006070a002a202e8111000c0c0740e1040160000810980d00940030340d89850044094a01c0e4ac1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 20516103 1250 20514853 20514863
    0x50c010c080d02030705040f15110303010501020c0d080903011407090f050a14010201060e10030b0a090302030723060703020301140904110d080f0c0304030b070e091302010e1002010c03060b07 84
    0x1010311200b036502500159801541d924006240a4490701c4040d2210301c40d030860f080d01c1200c813542041d40e40d00f00d1038111540250360005c0d41958503020000b50364030b01c980032190090604102d00b10400c41168180c40c00208003c00912500955110440301c0e00d07003ca41c0c0000144c514040026a030545510700d070155603014003402c440c2070400200785d03142c04211035a03604641d40e0f07a80004a00b10070b0388580303006880505000482c549142040c40d860304025020040181ca400000e5001903000811140155444500c0b540c243d07000034880310f4814202640d034070b00c50040004000d82c060b85640118140d0f07035084440c0359001082da0a002200c1401c4600503c4911420202003c520300ba00494040a2061301d5007440c101500031981961707003140d48040030540c400b080500401405d00e241e241d200149140c102504210f000002d40301000240400d00f04000207000407056900c0703039602409000c405400d440300c07002c94840c000d00070300030710240f07a0002c0d24103400803e1030720720313541164080c81d002 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 20517353 1250 20516103 20516107
    0x90a0605010e0108090a0c080c03010b03030c0312061504060302031017070e0c0d0603060e0613080f070204240915080304170118030f02010c030509150402010e0303070f050c010c08 79
    0x403000540700130a0282080c01940f048404142c0080c180440d00e0016003011400f800001a42009060a480020384118441d4200344885240100008280d400165281380080d4150700c4490201d40b41640010345501e1001000801107889509a0011070081d4841005840c00c1c41d900c441010070018285090314564000d0803080140781d1441d24510341148403898020300d840d20046010341217802d80c1c1e004440c0c00f0703201c0ca0b00c50220081800305503400b51a1a44801c113044041d0741c2ca4100d13200701b0520740c0e82c04001260440554035254403040d05841c8416100321030031282e8030003101840c050f10440d40303103d081c2803403180b110101120800c11103030002e0003107050604000e0b410003000c05070001401c89642e10036056940c0e10802e02019501c9000391640d24030000314060082c00c2d5592040040207040c100810700030520030014881200e010842a0300d0301c1c82d1100e01c0100e903c048500d614990512002c0340311414800c480d031480640602c18012198041c000b5401920030000c90f9502034040b0000f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 20518603 1250 20517353 20517377
    0x90f060901120c18030f051002030606030403030e100c0305060a080106060c02060c0f060c0703030e03040f030b0601030b06030a0c0806030105060a03030f02071508060405060d05030a030c0c06050109020306090a060501 95
    0x41608200d560300003600313007161819480704110001070700c1c0d640203540e05034100c011001401401d001c0e41d14001c0091406528602e80000407681034480a03000030704040c0c1e1058900e000040600c02c00c80070940d0004d0030300c6880724445008028101c2954043e119805480000031540340c14800d003012546a80c5501c80319160795000c010b5150001006100340d40196001c10110400500c080740c800e01c203682001d80c882a02e418010103c0311040e182510720f61042100b841407040c0c00c00038108036039000300c0c1904156901c1d00100c0140050000164010300301009124022140fa00090b48150040d51501d03042e681e850201800d81d2800d46072241c000e1070382d200601c0401d105503140150420507004a030340d026669000d241d50480120010f100003581d09051007850318080c0075060308040102d81c00280322580da220b03607032240301c0e40d2001405e140d501e0010700d180ca4003e110400340c0c660000d40c100159a540c030311140107540300701d41385403103010000c0018109103400e100700800c2d5081a96034110030741c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 20519853 1250 20518603 20518637
    0x7050609040f0e03030711060103020f0603070e1915080f04060c02030c030f04030c080303040b0114030f0102040f0f0b070807020112020c0307110306090109151113080102090f060901 80
    0x2100c851515001501c444008019070050302805003c1103006004590344d10708103100038078010030130040300341c01c0c1c21031001040507a0351700d15100c50107103040b10440d94039207524000b5211003580071545c030780200104a961160701200c642e46002c0b542192105a50b400300c915045403803a10454100c5450000c4d00c001c1404101283c0c04003045040e580104d0f440d0100e144100351a6801840c1070400c1818006014004c01c40e20105030401003205600940c01d5003001e0780c2b0050170100c140503101101c2c90754188200d450390200001b0b1100c8a114000719a1a0380340c095042c42c00c040ca00078086001043d02000504000d4070741260001d0790840d03141800e040e055401112a41e00e0002841c0d803080d020f01020100c40010700040004074071072890101c2d10000b260900d400c1c080010301c040410f902d000e0261f00030880c10420301020300301500000404210640080c07000d4086c81482d007610000780e16000c81c08100540c000c2c105110111480d00c0342e03428074010440c991003103030251400a84131032084d000c2c400d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 20521103 1250 20519853 20519857
    0x20a0203180d020307030f060f06030503120603010b0d05010614010c15050709030c1d0106020d0203040521060405071a090105040501030207030e040509010606031d0c0603040501061a09040c0305040203070506 91
    0x50340c001c002c00411a00d0360006494403200b03410a43c1c0c040d0b031003020705003081141c1c42528200118520184409440e6031503942d1240906000e589840031180d0005415035020350003000800c20003880c00c0114409803c040b8001c1ca07281c090700780301706520044015158007450002203413660105860603054480b2204001602c4054403003002e01c0119100031001584806075000609821400343c030f1001400d80c0340290f03000040e4881010f640181655604980e030120848040e03400507030740800d0071104501754181452400091015070701440040c0410841d010840707200b04c03101e070008240d8607000840d19880e207114107440309012800802007000780f5406a00a40b003a14080c1c00c3c01890a44480c0104050300d034100d880d8003160f55201000d1001c107806202d1929a47c415a40c142032a20702d0a004503543e090f0550036078460040440060100002508118041e0041007100c81c001d075019240b1840d103400c15040d5500c1503060046001d100c038400d100303d6206540080c01403480c240380406001d401c1d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 20522353 1250 20521103 20521147
    0x21c05011b0512060a05010518030c030f070509010602120307270603060501030609020f0f07051603050105060f030a05061506091203090a0503070311040b040906091212020a0203 78
    0x5552103000c0900081c52241428400d05690345072583d80703450800c902c49040c2d100520b42d42c4111051403040c001c0da6400002d031811140e1016000b00302611800000c0e1800e50040e81d00e41e03152084105143e4201e20208a00048403002d441c01d5486c0e9880d014241d07181d12200b407008a0043c0c0c00d10000e0030661058201c0b811104c0e000c40070700394601840b244c804032040b1f9900320f88046038aa480030491540e03d84141d500400c000b48045040900291026606129006c1c0001c1040d00200e914003d000c0c040c4500e820001102c5140b82080e652882e0141c06010b04440b400e100d04140640c90006003804918040c060342d201c1c0161026a0300c21181079440200f03080030a8000a0034007412240f0b844100c102001c0503615802580c64a40d0720742041041e031000c1c3c0040b0300a81028804000203401d11180f204403600448011510641c61000f0400402c03036858050112824401d01405010442940800e220410b503a140f1801c0e011200c40003d9102d0b0084a1006a00810105250f542d1440340d0104d1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 20523603 1250 20522353 20522363
    0x3090a020d060905030a0804030e0103060503070905070e09090a030905120607030905030f040308040807060c21050d050118050708012105030c01050115020106050a0b041e030506070f0e0a03021c 85
    0xd00f80151101e40c50741c1c00485521002c40e9140703091005058101d03c501250000918052000c2d604100c046908c50712644100003000b61148082002280224aa031001c14030240510942c0d1520a081d41c0e03032100200e005602041c22114041460704142e0017044007181a803001b08215155503a040f40102a1401c081d12035000c107001c1200800b02590003000258003030811551200d0400c03e5031424000781d9440b25003840448010040060515034480d84e20500f9416000c41850001c54240c40703e1040d444141c1405d0700d8880042544420540b01145481c00070742d00b0490b07a641c4860948e00110203029901c0c0020f02d080c02c0e092600583e10503c10711a101d40c0641e420300000342c4801d804c1d5202a003020740c510341c5801301d68240950910800e030040c00e0446000640c030385041c1004c041441540906045005000d0030804031401021440000710fa110041321418641031900600d016180030082c000240000506403140c90f20761525000d90740c00809000c24a0201ca0400122040c400c80c1121 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 20524853 1250 20523603 20523611
    0xf030702010b1201090209101d070e0a032904020a18020702040504120f02120f090409050a031d09040203060a0b010c050703050c040f0c0905100504090221090303090a020d06 76
    0x1c041d480b2070a00724009103c035400841c41c0e204610401941200003810303410390791a80601040607100e111130001608004a04022868982200c00ca600b030200800060300981d24401c00001c001c8814606001c007518202003180c104440150300b0f60600050724041c0d808003010000303111b09003800100742c00c0c81d00f00c02001464650983d01007015500102d8060382c90381c090201d03030864103400ca807030f6211010303e42c400390050081c0a809424207000d00e00d10195490801320340c24651f502c40c1d600105c05a9004811956035440c20b00c0c0003810a0a42500d464207051101c640032214240070569500440e8020054070481d076801c1c8080000386000c1c3c042d00d0400203802c00c03030800310f44203103c208003450142010f041030f03603142020f010944865450100300d0901d0249558038043c0d2180b540001e0390700c100c030103940e001c1c80b2200480b00340c01035030801c0d460a0310020300c201c401071000504100c003106914030710078203641d4981c41c10b440c2d0004840250040d044405c00c0740c01441c0031070003c01c1c03141c82014005 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 20526103 1250 20524853 20524871
    0x9020c0a03030528060501081e0f060d140705040b0402090102060103260307020a0506070507050606090a02130b03010503010605010305010b120402060d050a090c0f0f0e04080c1204090e01020307050f03070201 91
    0x425030410355003400300d65403020248107c4d603110f007000d940b0461861060780b07440054034030121081c4004003a0b0410506840115201c0d644131f940091009410503c6009145560500c044d11084140f042c140304a207444200025800c00d0f0003900c094020503000717040d06a03c1e40e1500601049404c000f908030b410041031240c41c90b01d910021714000e145580c0101101c1c0218648203180040107030010052103424800301000a500240003a031040b01591505419125084840080c4c098904400110b82d03a950f0041418141080618101c0300100c000b4041d0b61f5540d001901100c03406e004545000001b00302c8114040034801c101900944060030044c40c1810705c0f103441c01100c50a95100703803415240c081d00818880d550b40c103178018002d12003807052901d14000e0840d52a0826100d004264140b00000500b8840500182e610b0034124109507030740c14201d528406201e60050298040c000e16015680071081014801c0d40c3c810007880d212103142001552401040340c0008081104641d00d4181d02 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 20527353 1250 20526103 20526151
    0x30d03020906040b0a0203040f12020d02010e010e03030a11120a02030f0a09050904060207021806091815100503060901020a051c18110a0909080a0f090b030906070909020c0a030305 79
    0x20f05c410401d50303000d5601c0e070b410103008403100210341c1d10448040c00b05c03108c5800035a81e0044044900b41d42403c00740c4120154900503260504041ca002c4e80c1400080303100008503402040c03140f0410700c150142c51108529101400c03840c0224085a0012b074014030013140b140003510004d00c0080e42600380602041d81c1c3c1e81c00140b2164003210225031440c0c010074400b00b141000b903030021078200501c0c03204040d45090800f00d100c0c460300404403144502185141f209140c4140f00c1860102c4d044059414146000300b000c034074000c02032090701d010b0712508000802c03864040c17003610080c1200e661143d24040cae581c8106500509084c1caa54074442d41e4440b446030340c101d10341521011605c41ca40c040034a4482c01c0403c00e10194607407080440c1800d29841c800012a24800ca4540401300c0c14402480c05241004850034045504450313a2100d0020038030030800300c00100c16100f59000d940351000641c4a030307440c0081c0e020f85074800140b507002c0325403000080d000e0b81006038480c01070b4502c014021120440c1c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 20528603 1250 20527353 20527357
    0x2030c0f010c0806030d0c06020901090306060f1508010e070818102a020304090504051507050d0b04060605091011070906050a05040c090909020102010f020304030e03060114030d03020906040b 84
    0x20821241c0d0345190b094025a000b00750941d0050f4110050080310340c00c0c40001c0d0008240c804001c200940c0052607581d160700a10700ca4019640095080189545032007603811524904d010781100005408007225265105980e4641a030304c91281c081c3c1e15458060042c0d41707180c2e020780415490601004000a060307400c0040c40030112005101054812440006c51010070300e12001c031603031107550303500140c01c03603000803c440445950002c0003582d940c03941000e90a18807410076045d5204030032004d00c8041036121000d00070025003000d04011110740c060400046400030f10031000824024000704003185025402c441d642501c07810110f11855a8a01c50390074008140c010f4442d1990b540401e0066080c49846c840c09400b0940b800c0240600c125400f6203002c50b14410030100988898460045910039003011940101103130f029502d0b401d0034500a0042c407000f081c03460207403003103000000341240c48594030700b01610b000d00034200e2107088902c102d01960000c400c46402020030000001e00d40941c00c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 20529853 1250 20528603 20528623
    0x1401030f0f1a0a080726161703040f05040504020d0b0108030a0306081219030207021305040b072309010c0b040c03170702030709020309161511030c0606010f02030c 72
    0x80000d01075030082601505821020b41c881c0102800c000c10310903400d002411030251002e40110440100d091041c001d42010044a607080e03502603031000c1c2029000c042d00a006480b03070140c90394014501d610003d55240660b11900413150130786141001581096840590402d0000d403a10210441a48408030700541c20b030311003010b03a8400149403a0300b541c1441004043d00c001c00180c82004452001c0b052140036902015a014408415011110740241d048807061580030b40031880400b00980f05800a0000b1101a40c001030101e001440305032195100c05400c1c4895040201030314200d9100c18001d4004402260501a40c0c40f11200455810008035118600c508540c0c07101a0462402d00c8100701c803126030340c04059082c44804016900483c40d042540d41d501001601c03591104004c40c0342003045424440c461802e95404140a00d4032036200f240128580c941c9e5404030300080d6039039920f110f4911010250b030850f001085944d880758980c90101042c2c4d2040321708255100c05901c1c1456103041e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 20531103 1250 20529853 20529881
    0x30f062004050f1212090d060608010501090f02160b06121902190305120706060510030c020d02030a1709010207020909060709050904080703030b0406081b09010e09071401030f 77
    0x4070301000186002e07051007901003402d403401508800209442503940c4030248814910a03808201d09100f40c80d03410300e14002075080742c0d045c090f0b03d1362ba10489000709400c6c000c4815180c20b0085400d01403082e8004c030b40240f6200180030b8170454458549401e800030180c103c581c00110f07500301c0c1550420400c110042d5a0507015864402e0040784100700c0403822180d42801c5c4629002c40800125001181d40c0d54070010744012141e40d50344130b10f044801004103810440d44130904983c1c48031043d5040d4071008071075605400b00d07680140640c105903074034001c0170416000640c88540e80040c551840ca80703550001c00400c00542803120640c005103000f90b0403511061a50f0080c020080160fa10408440041c0030903a268100c81c00c0644850406105d001e2005d01855150074400026450701d41c452001010b000084d00c411400e8142d00300e07001200080d18510404584001050761a40040c14074000c0d00242c000700384240c0385c1008240c0b180c0711861218141650b0b458142440c6038203001d9003104011030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 20532353 1250 20531103 20531107
    0xc021908030a0e06060901030f03120c02030702030601090b0f060d0608011118090103030e19031202010c0206060a05011b050a0f0b0108010c140301062003191b0c030f0620 75
    0x41000e012540302d00d443e03070000e50029040c0229616001c5e0454152504001c40080101d020305040e100082001c4070380d2070a91800c000c0482d415804000f130f081b168402c40683c0c03080d99995501d04280c90124508a50012881081c4401407400708010400043c3c2c10b88040b82c1140c0d076040260864007030680b1215402000510b1114401510111608919080b10103400d02c0d41540c50050490484210241c01003441a24804d50700303d40c00e0500006541c0200c021400607201100280607001480d0b42d0b2000d40300741800b00b0302c0c0d803130150301e120240c0d403040c2c1d50301044011300030140b003c1d64217190b400c0d0303403a004003c141000700c2e071300c4034250100c58090f0b502d40e42c044d458488050b0844071300513080400c011040503d881035500c041c0c1100d0458030310346000000c0d000030400c8080d0301e03000208004514840094400250344888035a0b00d82e49840791144d0710394910740d4000c03040c0100c8013440100740c5031016506000045505038100d10b444d004a0000800e410030112029209050790a101c09032140 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 20533603 1250 20532353 20532361
    0x80601080a0312090b06040f0209040c120605040b06030601080c0d09051b09040c1707180f05061002030f031003050a0302010b09070302090607150e161a03190c02190803 74
    0x40f01007082400303d40d0b04108210082501ca01042c190081e1019104039118905240d0200f07580d01035030321b0300b00004c10030006003004d540302502e2a20344822841c01e0b5410001c000605140ca03109486040b80003410307440c0b9698a1500460301044010304d4010020020b100207140d01d0003904c07800402522400062004450301da036003017200220000218410b410132810000019181c01c141012100030080d544041201091450300b0b0440700e411602411241e0440c04191500b903411660010600b004200401e44400c0b0a004c03a038007018040e200540c0c4100100b000d842c010100a603480340100283c0480a40c513541c0f030608002503840258010303915000d00c842c0900c0c19101d555048a82402c1c1146403140b5903021410130700406401a054001032004511072180c160084d94030920341400b0384004003540c1c50b442e500c18449008501001000c0c0d0320f01220f40044c01d04584c000c0b9268030387d02e0403002c2480080d070003034903050102d0800c5014400d80000540711403080711941c284102c3c00c480e12890 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 20534853 1250 20533603 20533607
    0x31407050102070906060c0f02010905030111030121030f0c020301150902030907080d0e0108060d0b0103080a0f0e060d150803040906050f060403080915070803010e04030e010c050c0105070507080601080a03 90
    0x3c110307040381c0c000c98904241040482d81012400c40c07110340c000618202213080380016550700d08264041c541650900082d15440051480118140d40811074400341a01e4541d1860001075400700004001c00c3c92803507000002e5014420415600c1c1c401000800c98600809501007141c0ca00e501400070250044148551540e0511480c00034290305401404008040c0d40002c0440014444013410310001e40c0119480780c07144a2480061a081500440554be41c0e1a07d080305a00643e045000500c0d0b42420000880c41101c1c05469000024001410002c0c040340c20f400422140c014040700064020b030003e0707001c00c113101400003400e04050006000b441c00d420300c44400102401244221b40400050000030946025201240c50549800070425081205903810b840307001e6000d49a9a40400009140a04454001e21070361080e513800040b901044019606081a114000c1c00d641160004036955449140500740060240e41202d0b403c503980c3c0142c900780b1001ba08070200301d410101c041002c5c16 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 20536103 1250 20534853 20534863
    0xa061d1005090316210903030807020705090a020a031b030606090e0103021503070210090f020a0504181106090d0f020306090607050307050702060409050709050906030f06010902030709031407050102 87
    0x1240300304180000d16111a54580b00e2240c100300440d0081000d508006210080d007000584003148034000d000c80050b020068070303012241c4000c80006a0b0900000c2c265480410420100c41000e012004913482c1c0103ca0400794120000b8001055503c60540460148514400f08203a0281d10001241c3e410031100601100040c1c000c110b84070849401000142c54508008001c0d00020510350f072641c554490890038072102c1c0351682e1182e41040e9a05042c003410f00101d040c207d10032104a9481681c400c10700054407030a480c01a0f0149400d5640e00c08108031002006001200404c010700d8640321000040d040400440e058440d00b032100f4404045003010450a600030358214000c0509140800b4002c1ca103100007031281003007040c0495504210340f5644140c40203080745c20740c14090f529203e08004c1500b0041c1c41241c0c4503010a0700410030604011402c1441a074035580600f40603801e010020020b5480602a00d08000320f0600000c0419120855038020a56400103040820300d03100c002803400b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 20537353 1250 20536103 20536123
    0x140f0a0c020a0803160c0804030c06030b040e0a030c020406050406081509030304020a1505040314010f0b0402190c08040b04150e0315070e040e060a06030201031a18090a061d 76
    0x1540c4032101110110300e2003c292a800504030501809105070f0010803200384071030000017094440041404000c0190b0b038008442694500d503801c00400d14044100010740b1952501200c543e040322100310301081c0b16100c01c9040c5400a403011621070b075181c01145c2144c01540c01104503401085070250032407113100740079030031484990080d4150b040c00c1d000a2140c007650f101b070003900b10b4841000f103a080d0150091720000e541111044428484803140d50780600b19802c034014256103041c0e40016146440c1c8203603504800d00400600030466510001d441d07141d05900c05a4030340c94203101c00260400800024401b4003402c40c0d05101044004a0180030088130030017003031013900000c851404819854a65030340c40314040c0f03000099400d050000c94004d201840d144ca4040c0110001c00401011541020040324800e076010003400761103003e150102030340ca00034103501ca00850141840d030a00729010070341000080064035003848080d0380d110215904c1c81440d0021010307040c400600c11205224032010 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 20538603 1250 20537353 20537357
    0xb091929090f060a1a10030906090809010f0215011401050c1605090c030103080703030209210c0a09060803090f1305090604140309030c0613080a110a0602150a020706140f0a0c 77
    0x3a50866180005e80004003c0214000d00815040d2540c1c50300c260010302c842c036000041000030000c1c901b0f00c000240d00949601740031450b00f001ca4403500340300103000344e140c40c014480346529900304801c1c103262a028409450400c0000e212044202030b0600c0a00540c0c0d0003141060000d900c2c000074019045402840405010307014001080031030413003000c6814a9600d0704c2d0060361810200d00055884042200301c0071500f005080480c44070700002407003c90300404a0b10320380842d651382651380c150f90090203940015001800004490f051200065140910080c118455140c801007600300f11201183d6250303441e4029418401484903003400000e04003103a0000d181f03000d4640740400d565000c54a101070048000265800c0d501001a51080140a02c402501c0405503181041c402001d0256000c500c2001005800180c282c00002c1c00c09030b6100c003807890400c65a030700141c2030094010070740942da1291903003140c0075100c0301e800b42c1c00d208108d000c0540450781880300e4440100ca01050501d81 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 20539853 1250 20538603 20538611
    0x14010203130302060a0306090212010f12030e040b150304080904180308070e0105190507060e010903091401120204090e07090e0a08090604030203010501030b040b091929090f060a 78
    0x1c032100c210714500282c0e50140d440341d644594081d4100c0040ca219407119075500c0c40480d5030001c080d441c040d2281250b00d1030301040e0815407203601c400002110b4020040105e0440351030340d1105d00306034008a9030103000800ba80c01064000c800d06203207500032142114040342c0022285003501c1e0500c01c000656402e03840881c5045650341c1d02a218a030060119030034000b4031070242903180e02c41c030111040f44078000004e480518403008041c0042d0002c4104480407400c1108450700900e0520644d580b032a01642c40300202c61400c1211194401110012030401140d90b02c009609101400104001c0c025484001a6101c01011090402c401a00001c04450600040c101c1403030001884415003504446196981c1625030002400c07881103034002505542000f000000348011186000c0c490390003190401c0a9135210f04605459105461482960350385000400e004600142244102d00c1d500b4003903500031040b920404003039403d089030110010392124007103d200140a0008039041108568184 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 20541103 1250 20539853 20539867
    0x20703180e0f0c0c0a05070b040305010f0209030a0b07030213030b0708060a1802090a0305070902070309080604020108010306050601020a140601051206010e01030204020913050a02040e011403120a020708030c0714010203 96
    0x20300300b50000d40300d000d9901c00450081d00041051084074030305548001143d40d0b19035588404419500240b00c08d44a551a103d602800d110031402219407020004002d041010401d13070702c02c003100101610120816a081c444004048800d902c6240994042c0318040101c0c03800560082581200800e1a40910b910303031010809210010841122020021005602c508007500800d4002c5000e51000d4031500c5400e400017504071041e07005180c0503019540728001140c903051102d6641105907002070015641d100104041581da501c020b0300580144141c0b801030000b0344540a45040464040255803c1180100801c3c80c0000050100d244608082c00300f41d0f140c0321420000a005100c007034020f43d0000382141d095611a00724100084090104000714144842d090000390000e00503940028084800881c0c4203554140c9048034010017401480b428410024405071038200d03ca000303065204040b40403820380800d10161281800b850010030b40c01d40b030f0440c03000301600c61070b24190541d0000c0000d0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 20542353 1250 20541103 20541121
    0x2180105070c030605130c03140613051b0d06051510020c1804030201090b0106030b0f010509030d030f020f0408010203090607110607180906060c0203010b0108070507110d06020703180e 81
    0xb6012280c00134000159a5a26900360a00c1c009044c001400809184404420404034500642035040540200e854a03600c000c131a8040021b0130700003920f00d40c0144015030899150b501c9007881500050314a10051000b41c0d01d140076180107a030b00704580d410040c06455941000701c01711410081320700c018504022a00081506400c054030b02d91040f2a10700e00081c241030003500408030159005002500540e5141d000800810010380301e540301d03035040506103c5940c4110142c9280c114003c0c050901801515401d5006050459554100c0d580900410005500311030240006044842c0007507564503000c0e8103141400d20003404241407020b03854408969210014010368022002c4c10312250400d10104100304002d403a5201240035807c000723005c0b404551103100e101c8081d20075402806416940d100554400000b25070701000108184085030100300c0c0c00c041d40881c502c024298200c0da29868888605036849a003050300031030140000c40780c2e15101140c49900410003804010000d0a00102c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 20543603 1250 20542353 20542373
    0x907090f090504020f061909080607080a090f0501020301150908060c09060c0102090d0f061a01020d030b1903110909010b090a05061c050601080f07080709050903040e0405010218010507 81
    0x1e5001003a502c00004045488062404040030303c018042c545401d50080086a0040c0c00360000b00001e001140000b0740f2800068000d00502c155120407041d81c0e240c06003c0010700c0500d406441c800c80001d60703500030910078401140a09000c604a0160b1200581c0280280745c090303100001c00ea10460030820203045035000c0d14040081119401e039580080e0715801d0180c0145101140e2141c0300d042c43c4c070100328140046200c041c0c4038400511485407018010f0510199404005015030000380100498502c65840034402c480300400d0240071003502c0c00020411790450300120399590010200c0c41c80c9240c4191001c0e8840d943c100288202c11821011a0302d11002402c02c00ca20b5403900c0c049126540e480750201d151007030003602c1000c130720518206165150302c280700d0320400703000b5000355040907140840e0130401d55120000400b155445c0244000042900500444440c041808045000340c0c8140c0c2c91806140035100240c0c80c5c1018900210f819981d04400a0600004000c0180000c1c00208 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 20544853 1250 20543603 20543609
    0x120501140a0f0513110408010204080a12030c0918140108030c0111030411060f0417010b0a080f06040f050c19030606050f010c060510080102070312050601020708030d0c030204030c090b0907090f 85
    0x101044c41522200210061b000741d411400c034550000c5004602d800c1c000809400750b5000d941000c000d40f80028056084510360070030140041d4040c10140409542d04a80500140589000044110320000b840250350401e8000e91000e40001410420604d002d005003209242d000000c01d01d9410640e4a0401c07031200c84a09900071030020901001c0360f8071213000e6070010120120070801003000000494024203661801ca03100b11646000821206000952000580a80001840c003038840c0c4c3c90340320719501d80784000c41e024810240e40101e141c554540000c0c2c8041c544a600e92600d055203003e80a0b15142d0b0080d0740038405150854600740c1e884424000220b401c02c00c0019151510400000d8984c4a0f0700030b01c081e0741c0001184410580d00686400c0b1600498200300305e1616075000490700c5605070300c80e91000341e00501124241b000103600942d800111410b0042c64190b40303030b0380c41307980350400d0748581d241039916040c4845904203410b00c4ca0780032005103001c2c00c905d03051110340141109280 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 20546103 1250 20544853 20544889
    0x106020714061b21090109060c061506050d05011d01050103020c1c050c15130305160506010e0108100b030d050a02030f0309010605030d0f1707120501140a0f05 70
    0x414905560345800003122000341d0b2403843d0520070760f80001d0a50341c031403401e00003000080307010401503500e45000342540c1e8031420503511070b260b003483c0c070000b143c0042514070b05480303540e80d17295000c5d0101500c0403400c0017089030b070b200e607520f550900600f202221016800030b8544c0e50700ca11620f0070155040241c07819200c2c00d0a0040e1119036005055241000942d0244c09118900e00c0c0c000c140d82d01f190240c80144445011101034010a40e0004140e6505558040c400b0080c1d202510005c0d01840140010440e05d82c80040c215801c2c0c2c0b00e007860000c00381e001d1043e0380c5246006002074401401140341c080c03510b080a006552070100420b5443c542034002e80100710003c40c01e0b0020600c00c3c0111840880c3d420081500da04100c19100c1c0204054800c69200340304580d03c02d499940220b04232420040c0079200c4140001200070f0340b8101d040018090401c00003a407408407800c0700355102d142e003e881400e00e038400c03003410782040c07000762801600545082514101c00708469640c0040c8208013140d00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 20547353 1250 20546103 20546129
    0x102091804050f011104051201020408190219030f02040e0f06040206030a06090f0e060f0106050706020912100903020d020729070215030a0f02040e040303051504020a020105040c0e01060207 83
    0x3410a241802100f0030900f929508103000f98102c0c480c00d00103030055030700440c0d0b107021106100c207034039080744103902c141080e94100c108640724003600712010100080c005401d00c10200782c0c0141809815080e5041210389000c2c0100e03400660500d03200306821002007000804e2050140d8801580e9040001c000a00c150000800607100d10300c0d0350401d60080800c8801800402501480074000e00441b400c2c00c0121712030140028000a0412001c0d4101c407030b141c440c07503d0a00240c84202c0a544211070311600f1038416415151042c40c1000200d400540c91000014004040c0c034000341003808511280c1c045604c80003080c09024003035000d0000075044024140d040301c0040b403850742c0358080e000010b0b51201e02c0403030041d0914204001144940080341082003a2507680c200001240640d0203070284111011000500090103948103a4004a200c1c040000114032580060140e81c021b011040050351203500380001c22420042081c094154104039440c6581003c3c4020754404251007150045400 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 20548603 1250 20547353 20547361
    0x9060d140a0302060405010c0e0a030813051003090213050601050a0809070e0c0a090501050f070602070515160306080d0c020d0305090301020a030c02060709050a140a0801090c06020f01020918 84
    0x84440c0550314154008203548944070107040103520350702c040341c09640a5003040074400025100e42070303000711114010300c051441c4e401d503140c1202c0c0b900070000e103100745400700e0b41c0400c90341e4900840c540d8100441c0d0b00402c0e080007501c14868903041c03075021402c1081c10b11050140c0d0340c0e00001030b514140001e1034084695600d01c4146c0f441c1098036031040f010301d2456002d0140080c9400002c00c004980d94841219041c0e580e07004486601c42c8841d90340f1a940e0501187d000960290002c0030014040c1c01200e0703505241340c0d08082000019aa04843c1c0c0412100c464a61a090300070303030004007069406481c500044640190042c6481940248101505805401014060310a0325041d400190085403600302c20900503004180e40884100036100b04400109580d1182600320f041d220040c01600e007c0d8584040c0c1001070f01c20019450740500d06200100700d1042c24421120030502401c20b40c40d07414a03158020b814241d40100c807403096401000a0030558035451004a0841c50418690141d555 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 20549853 1250 20548603 20548613
    0x9090609080706090b0f01080303010902070503120108010c020d020303040209040b04080706020d09060501120317060103061706042901150c02040e0105100902040f1401020304080d03051e01030209060d 88
    0x2529020061141c44007042c00c2081c062a0741c441031020f032090140b440180c0301e8036000d4001000034811159640d00c02c00061203508510380191860500c40c1048030b0600700140115486104240c014580036956140404903d40d030400c14004d0350602070019516509068012455071000240040c10328800701e8045010000c0e840200d03006103822030011501c40241907086405852000300075035070340381000001303c1ca0443e088255000d40f549a00c90302e8640b041a4120040a04020f04050605030f440c8000a09a658000d60322818040140682040e08d0946171808200002e16010b0000d44441c14084280501000800b0b042d82c1403d0985000034048110803909104c42d800020f400c507007400013295501505400442c002c00c10440721081039921480078904078010f03031140c9a011112010b007000710403400392440c008500107105483c40d00c1d40716010702d498140103c4185e00040e42d20010043c0e03540c80c900215507000c00581c01282c2951440c1c00007010301c0d2005d00480d00c100520310310181001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 20551103 1250 20549853 20549861
    0xb0c0c0f1c030305040c0603021c0c03180318090506061204061104080d09061409040e0705030a031106070f090509060109080f0304052718010f020f0405040b0306040c090906 76
    0xd40030700150500c50106181c014042c20056500300d45c41032a4000101b0b1340e034082d000341d42c602130320740da5042510098402484003800c44c0000c4082490340c0c0390a142041d101c08403d0043d03250280d15508100c01d01c103020280301d00000d0303110740400303460502403140c1c41da80c050481d2410481d0400342c2c6e000e0b496038181240240140b10044803001400031b0006400391011a0b01124500300c1d031a50840195508400d403008640407044450b1a001002100d4140c9040d604c0314254101ca0403c4540c2592150042840d100d0600c2068011400750808800406010801c4540c02803e034035040050302644840038003460380318040c00744201a51400551564459020f03007000300961407c84094003c07010b0b415803aa8410f0080e0390140418101500c07240000402001050038110000d02c219540d4040040707400500100c1d501d00c6540320003148078103400700d00180400300b0032100c6055071145004204412070755034441c618040c1c5c000600300404900c0e121842c2c0101c425001d00843c0e22080c91503c90001c0c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 20552353 1250 20551103 20551129
    0xf010c031d04050103151524030b03030a11061e010b0d090501060303080106030c0c020901051c0f031e08070206060108130609080409050c0705030a200d0c030305010b0c0c0f 76
    0x2041c5004000028040586628000034070994002c00c015030041030060450b01c2c1500407640018141101d03e07100c0000440323024070000f0a403400140504489001a08590000c070141c4000303203d407889130a0901081c4081a000498001601c01c040f1080b0207820541d4014071901080c800e0100e2070203203510090b04000c140550110080081d03d49a160241000e05d084c001c4000007840c1c00e412076038182c02600c1c01428680c00400c640704a03880c0108000888c410f000451100b041d42420080016a05018140c80d0034841e84682c40e00d0509000d410aa2500d0f914007042003100c8502841006600814030f031360450001c2c80c1284880c3e9440ca107840080c954581c0080034546000303048401d01c400c06002e0001c1c0c9901080078003a0340c403850701c40d10280c020158050704540081003a481402c2c018081c41c894441402d01a0b20015000700348a410314041031080e0001c01d49280040c4209a031601c912405404088072880c10f2023510700032103039a14010544640694070040102169948070a0b080c504 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 20553603 1250 20552353 20552359
    0x6160c02060c0106060e040207020a0302040504052401030b0f070c060c1814030d09080304060c0c0302040203090102031503010612030806040e07150e03060c09010810080304080102070b060f010c031d 87
    0xda28104103402c0d008190f40d03c24540082c504194000c0c1e98903082c000c0321071043d0001d0119101904580800c4000c000140048910344682041e1b8200c9401e040014038240406800304142d0790700d18141311203075240003801c2d0702e8148440d0042000300381e08440d202e000e940d080000040e186076440002c0c1c840740c85030026031a150104150001d041089016085c039100d6007542034640203280010142c07103807a954014440c0d0760304148014051140f01d0302c0141a01e074010044407901c0c640e20380100d02283d009a4010344c0d079035000420840040503840191301d260400354000c11202d80340c0b103072803221003500c05070080030021000701142031ba50312078200c4813500d20f405041c0d50a450b501d10542d82c3c00d04601f0341000115090030401e00c4030303103800305006100f19a0042000d1a14030307000011036904400500403201c0981d803080c040b4104e00700b00068006030100100041e50350949041502043d00018122881500e800e0320400e00f590340055404d42081e81030414200140751030f404400807200441100350 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 20554853 1250 20553603 20553607
    0x3010903050415030e3007081905040302060d0207021c020a060c03050c060106030e0d02070608010b03060d0c0303030506010e03010e07060c0507120c0510020102031303110309031203041103030a0206160c0206 91
    0x80c11409410701d21205c84541940007000c003000e1014100240114031f0081c200700018081d112950780c01400e85000c52003607141c441e16054584c2c2c00246543c02690f4000012079010074034104508200818403454941484030810803901c0d41e00141e00040700d8001c600130003103220242410940541c0c10b980310150310900340c44d240d40e1038403070041c003c01d07044210342440c0c0b02e06c25080315060b0000c50490b0130354080755074580701c583c03e081e10001f295002030b12842c0c02001c03060400700400c94108a0402440c03080d5030124441c2802c1000401066083e01e602d0700c40c1e45003080c06021080700240c132508540040c10302c403042c41c0d0f403800c24034107102c0c0302d0340040480398000c4c02c0e081c100f080384160242a01c0301140d01c2c494903541800700300c1c200d010482d440814403140c419602c000c42d0080480640c0c0317600440803a4500800040403e050900650480c20810004410301c0104040dda00c0c1c0c3d000210290010342c101441d902d00207645203009428681140c0c9071015100310f40d0302c00c020f18144030780c0180c6816 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 20556103 1250 20554853 20554873
    0x10f170c040f060e04110a05090403090e07050c01050723040e0112020118090f05150906090c0c0106060c050d05070203070b0c0c1804030206010503060c0a031d01051f0503010903050415030e 83
    0x5180301d41c2040c85104031f086a001181500d4500102d41c0103c0d011303602e000b103860612501c042c201e44042c01100600c14240001e1101443c01d009180c8155020703038030070b650f401c0701000b43e1884022808141500b04c03420311080c03040701c14048401d41142c008101c4411b0002079400141c1c0c000c16030785001900c16070100004210300d04140c00150205400031000c010300c0d03645a0050101e1851050060307400070358200403440e035150100300b035500540b60b030007140d1501100507041402c50700650700060226501b800310200340441402503c42454160500b00d01d008810f6001075103e4107a8014002d00b8000030529131074032442000340070003008000d428158105032012800b8007044040b5004c400520074007001080c5414041003243c050f18081700140e0419890750810360141007200c002e0200800c1c041d0141080c0c000074060b05000c0d00100204641074882c0301031000400c11660082d600a80c18141c03c0000a6444001c8a046600c4260607031001d44071102c081780504400e12580020313200d082c00300 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 20557353 1250 20556103 20556113
    0xe0102120405070f051309020102010f0507020c0f040204060806010c050c0301061211030a030e040b0105090d12080901020a0e01051c050406020c010606110c0105032a03010f170c040f060e04 83
    0x1401240202d045419095803008891640c190501500750008801440d1a0321041c1e00d4100d070007a94414000891141c041003081310454401701c0b0307030600607030200440701543e00381103191079822042642c06500d000e082000140000c10003070146030402150030000410b0190a103c40712116000030000e004080d40c45444400c1d0710030564094428030b01c0401c1404103032400243c2040b00e07527496151200641c03841d000300070041804010302c50602504200703a40c110790320089a81e807c10300c02c0f02070912480f64610010001c101c02020842168030410940f45445c1c0c210400c038403040300901c1d05036980c404040c40310309811200ca2110007120f05040902c002c01035143c000d800e0300c007007000c0200140e560b900c01c11a0b1480b40d007802b60710907405c68004003400c0c3d44107000460780844202c1600300c98942e023203070500c00c8071780244071000034100100040c45404605030001c401403040b0b0101359403000000f94201e840c0c066020501d0b00c244c2d6242c02c021080307100303500000020a401c2e0804030b41481d0504107 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 20558603 1250 20557353 20557387
    0x418020d05070203391c17010e0105100c050607080103050c030a020f060906090a0303020a030206010f050108070804110325050405070c0b040302030f0304062009060706020d0e0102 79
    0x6581030341c1001e002036142032002040e03034001220744280080c0000300240311810011a0b080b2071101840c00d490003003d42004014500c2e076150400071a003080c0d502010020320021a02c0403002030740d10003400400c202c2c6c0000a1a42c1911412207000c03454030b020721810b451010045000800600030401045101a00010120304a0b4003403401c2d104841c140c90304240d1102d4010f58025840a6a00031000042c1400c001230700310490050245480c084520000401c80322050340f0407001a44078064200406a0620089004040c401c070610300d01e90520700082d2440c01d008015008100d40507000400744074009581c00d0000348040e00359981c0c41c980b0745807440b0f4000002000c8145030b143c620001402d052520510b4401c581c1e070354a00a802031941c0e100c2102d040301400035011440705000c80440310410303000840c0120300c15800000c88206002c038074588460f6921035920344460500c501d40050b05d03010112648194005001603a0b003c81e4040000108100d20000f00a903102042500100c0c00c0703600 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 20559853 1250 20558603 20558617
    0x15011b030215100b0f0c0a02040e07090f02070201090303030b010207031b0602060c0a082e12050f01110f07170307031e0506030c010f1209080301060f1103031803041802 74
    0x180004503680d03041c001d0f05407a185100e10703031002004011490000c448140a41000243c0c14281d0341d003025690001400d0300c184190a0036290000303401004104058441c0402c08080204254140100c0d0340010780183d00a20014081c50f072184002c445583c0700340b005101031517005800200840301156020f0700d005a90207004054898640420160000441038600c5007490340c0d03480a0660306c0925000012044941c41500c01d0501c029260500701000c00312000f90945082c000711004c42801c00601d82200181420010b0745040121020800a441103031058040201c0c555a210906d18110a140d0398404100101950210500411a505402a20805141d6080302c0900d0320300d110303100222141500c503a913065025000e0907206501400c00200c0c00780701824613040010742d8801003c00e480745480c00301c5000c40000010301070f054004280703261107034062038001004c420102120b507892001800388031021040c3d04030000b41c0728040003204c01a040180c0840642808210620040d4005403 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 20561103 1250 20559853 20559883
    0x40c0f02010e0106080a0809061b060604060b07030906053403110601180906110a0f1e0c080304020f130b030d1103070303050a0b040e03030105040b0a080615011b0302 73
    0x5160b080300110140140002e44800301c0280400b0f103e41e985d10312031603110b403080c11f800c85400c1c0038200014501e4074031100c1112a403000b9001d546429801c000880c0d070160010021010180710b080080784c2d04c0b1001c0030550b02c890800c9076070b03260f00680c54082409413209050f00c40001d02d403c40000f0080c2000b0050039031003500e4200300c06062480d02902c070384090142c003288860a02080790050403e801084546016400024400c48030034001c0c03210741d00000241d40450194000c0e10409075001030455801c040303c2c0d68850b460030188000078040140b0300d40c05040302d0000700101e010b40d03840c10020201424018120000944c030300b0100e07000b51020703200d024072a004030510348900c0360044030360303944420302040503600d02101c0395411b500400c1d006c3c01030181c0c00c3d5501903260b85520b4074410242400039100046031203614180402042d5020a03003102d008950500c0c0c10040031034001a00340d00a21910210200340b0f58400040314014004010044c0001e81200722a05240d00440d034441404140 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 20562353 1250 20561103 20561111
    0x20a020f0a030209160e04090807031d010207050d02030709062402030304120c050c060a0302070b0105060702030a0807060b0a0306060801050a05090303070c03020313090b01080a0905030901080a0b040c0f0201 91
    0x2604001809101e4480690446000380001d030822560311106401c520b840e0802c42004c2000e900418200e9030b00910480d02100000303802c00a0603000810600100100a04c121038131403800d000039110b074024411a0f0040030041c900c03004540c0e052104070090603004404001d42651003005443d080d0081d07107100c00f41c41c1c01b0690781d100b440c0701004581c8100d4000c2c01c8540740c4480300c40304503250f81034808203a4242c014070314191071580c3d51500421100295580c0580c403111181421850a10181d101c61300c030346010400800141c40204a020000b50403401c080e48401050405030094900c1505140e031081400303101000b04000c070340c005015200e108000f008280d842d91444400c442c002e40300010702d98803e1000540c40303031003142c0307070480b040c860320569041039039104661640113a01e0304084503803900c9001c41600e80d64800b0380e0a40c8420049000d000e980b440342c8401d0307180d200301d8104604101000002031403141c01600200001040640304200321504400010400060b41944400650030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 20563603 1250 20562353 20562379
    0x70f05070201090302060904090605071d0405040203060403050703180b180d0b010302040c0504051503070f020303070503220807050604030f0507050601050f041103040c03110a03110904060209040606020a02 90
    0x10540640da881a030684803411014195006c11085400041c180e91340b00340c8546003000014282c0c060725000c0c2c0c40903154200c5203c41004000d101522134800316010b9480c2c0b07010800507a800048442e0070a416080c100e0743c1e07640380d0904480f800303d2100f00e280071440c00140024800300f500c00030701400f00700125840410701e01604003c0c2c480d8580e04041d110b60480001480545820707170100b04a00d000b8104a80707030659490204042d1030300140e041810410100400013000d4111000c015400e950b807016614603c0d02c0f40018009000103005000380d40a1602018103030038401c41d1540380a81c110f20303a25150569071600300d82d03d1004490032400103107503040b1000800e006005503008198400c1c0900f009a09240c288005000300c2000c2e29031140d15080740003688031203040212302803802030310a5044030b421130030401c002c04880301c022400741000910400101c1e0642c284c80d034120b242169401c00070f44072803d00308061701548090350f03442840d09600054850b0005049080d442c82543d189210303580d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 20564853 1250 20563603 20563607
    0x1090e09070503010c0e030d200d27080a06050406180b09070e1005010e13020f030123010906030c0c050d030605090109140103021c0b010605040810091106070213020c010203070f 78
    0x6c44254056109955040c2858003c240d1200c050442a01828420010952461610109104400114a4100e101d28078180000d10320300030705074a04030024025180420065660f80040805071005a885010800300102600403034205100418802c84840050a0a692888081e00c24000c107100f041030018801c142600190720420042c1801c0b00351a10b00801034440382c06da54140c80d401079240e44015455191032010b0320118801c0c21100303440e5810915a208200d01c02c4584074041400300a009400f6a07003ca484001d03035000d450041800850b500082d60205400b200007400c60103410500078442ea41a84018211170b01280d032402aa41d0b9038034a4130449440c80d02c4080070014160040c809410002e90000d804079030316041e00c0c18a0a5600d40ad0400c000a03081900040c000050403c90240204294100540310240400046160385d5075a9030300c2c20003000142c058080801c00038295611040c1ca242d03038100042043d0354503041000800c3c000c0d80216880e01c00320b000090003c02c400c0c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 20566103 1250 20564853 20564867
    0xf03010c020705061309090320070b03040215090d0602030703060506030c040b0c030f0409050103030306170a0210020a050114040b010e0c1206040902060c0c01030509240601090e09070503010c 84
    0xe0180d0080d0800c5820002489401e6000c540380300300c4180302d1700001910b0000ca114403400d0724026910101131000b0105010210324814031084002d0388640e00c18400100748000322608a83d044407640326400300c040c810b19040c028000c100303500154800d031103001e000d034980046200e000300340d07000c0101e661100c04010786030009070341c03003010084140418422140709100412300070f02c1d03480407242441300c401000c65681e4065042298032603240c0b0010402c26405005031805002d02d140381c5840009403000442e035901110202a00c038010301c074004c420190080c4004480180c0000092000c06d9105d1940744e46510241e600302c0380088007000000b0200d807503c151500480808113035501c1c0940a1500c180c840c04041c202c203500603070780d6480780010f90303a6000a021800b1400301400b0701501110014041b074100808030003060304940c40b034904c0b0700d082004c032042103421074108a40303503180c1d50012a00106960040e504105042d020f1000d501400200101210802c030000e101d0b4a20031001140c201d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 20567353 1250 20566103 20566121
    0x13060306050c04061704020d0b01060309050709060b1806040906080601050a05010201051312050d02030703150f050102120304080d090b09010f0209090612160909020112200d18060203060f0301 84
    0x1242c11080c00c1c0c5c1e8403102e941c0c032a0414001031040d202203d107516810a2800300380d004a010a940b610500c1c00c101d41480302034003c00d0341c0740d0100301292a0400e000440e00ca010850010003070513040460540d5155400d950150806c6002000083c0d16905544daa410084c0500342c420202d42c0c50010b142d6105002c2ca43c4100012095a043c101310340d42c0b100b03407050449250b01c06200003400b0b80b0448140b03d101841c07080f8002d503004126011000c8204400c1101c60300101120384811701c0511a86e600081c44450140310701d81c0d4103a69556500700540c00d8061594100310b5a8240070601b400e00c2400c00304a401504040700030004160061420b5040748100c01076160025580d4001500724500f410b1459030880044085c2c515840b03c841c180603050400350011000d43e40d5075034030700d425946c3c803c1d070310070310340040290400c150b00001d644046404103600600f80100400250760b215940103070080952819095054040a8294548000a90000c5a0072406261045009100c40c50140180060 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 20568603 1250 20567353 20567357
    0x40203060117070c1212050f0f1807030606060503090d0801081507030e060403021c050309061602100c0503060405060405100302060c030903070f0504050c0406021c090513060306050c0406 82
    0xc441402c20341a0760851009101c4000d000c00314016070041120504101c038921003075900c010318048400c500c0000c540d006000318413650241020001c66101525003d07800c8480b00c90101c041c5007824407058a01030302900000c2c905410b0140006020303422001950241c0c0e94142569020b8450500449244109208024140c2c0c4000082c1c82c0046c0882c80d070640020311ba1602150a00b1191400b40c0f40c24000e440403001680314018402e61404c1d1190324200c0004142703492407a60400007032256480310050a0515600c40503003484074018001c2210f0144c13a140d0b48418000e00d07108800240036034108456440c021801c010014a10345020311659219000030b9a008040c242144c080c030106411111a2040621080004a5483e07030100032140c010225589940407060904d0288404d44201920b10120500203100030701c24a0340208507281d070000980041146058105c800316641d070408d6003e10340161500945070507080d040e4021006990181d0000e010075103070075621070998400c51103500c0c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 20569853 1250 20568603 20568617
    0x6040b211c0905132a0e060a05040905100509040302030306010201050717040f0804050a0b1b0106030b070c0302030403080f281b02030106050301020f03090105090a02060f0c010e01051003020306060402030601 91
    0x2200c1c4c83d0114102c00118240840007404070b0000c0f0414100d880300000c1c4a0b4021010300b564050180c3c00001d8040810301a204076051611403800507029016034024170700e1050f181c030001210704800e0f0300441c0c0203220080005c000780c205410040d45a9105880080c01035007071600040e04d0301d00864441c0707155020300141048170707950790b00c803000e09401a031030407102c8130410000000c041d03981104200140461042440d03070390105050030350220900d1186c0725016414601c0c10000f103459130f080940c1c81042c0c0e040400042d4400e01d4202e0070b520071600000c03c14140810000303011050103001c0e01001502c985182c805100481c0d28110100150000d040014802c03141191030840d500c006100007803028001141032074494000030309903001030f4405108900080108040d11000340600c9400c203010002410502001780c0104942d442440320042003072000242001240c0c0095006200d8800800000c00240c1403241080000c5207461109a1181c822070b0f01080081c46e2920031a03001e0038058503104 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 20571103 1250 20569853 20569859
    0x30a030504270c020c0f0f0604031509020910030b0703060305030904020c03130803030f011a0a05090d0204050106050c010f0506060414060f0703030219080402030d0806040b211c09 79
    0x255a0744001c003100741d00e1030b0700200c02564100c0b6a002d044507918081d000f43c4141c4440030180502402031100c0303144954650707440850207441e40c10465058940007042c400c1c142994100040c09081c0401d00290040052805c003c007681c0501d00c01000c0d2807042108240c96210311604405540c0ba9000240898100708290407036482c04e5130040024003070712419281000c4540540a1008038660301403a0650000010000e40d800c0500d280c9001d403c220a0700301600722400d0f00892180550100302d4144000060410003590754820760420160f4001c00074001c0b5a107852004005030007041c08000c0960801041c0715040401e4091248a8503001e05140d00342072606890703104424400d02c1c0700d03400c2001000b090218280b148002c00015010361070150f0b40e0119802a201c070407003c81e004108100d40c00d41400300503500810b240c3c4405c2c0b041d10f000d03005074466000040050400070081e43e070180315420000c0c0c1d2001e56540f42417203c65032100383c440f072441c0c403032411500c003040407010340004420600c24 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 20572353 1250 20571103 20571119
    0xf090105010807090504110903010b0102070602030304060207060b0306040f02030c01050a0804080708040305030301140a0f0302010c02040509030409090303140115080103080304030216030303090203010501050a061407050f031314030a030504 105
    0xb82c0d030300003110318210301c01175980d40101c4c00301e540c15200d948105400041500c175038102401005450f40b82071004010041c03620348000d440e800060710050626030001502c0060040f20307088884030b00c0d4014161481c6080601d040302400382031300c8040b0301a0003010780001d030a40c000e0090340c141000c80e03116103040b0b030380c1c40d56080710f6540324031001c40348030307900f070002001185040016501a06680000006100c1e0240030442c510003203a10024600368031110510050340d010803401403c0d9415900401c036038690b540c4642c110702498011001c81440c00041c042803680c940c22040034000b0003003814026980f00c81612034040260140a00420010801040021045070007151302c10b000f48142d90b40402e1180350364802078031580c400d0300000c0d2111610b6042d4507084c41103c0c0141421285035040f94900a4040c008880200701b220200300003082c1d410a00c44107000700512035002c142583c3d40ca0305040f04a8403805064014038014455411000744c0c03908001038628000fa4054490b41d04051400c900 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 20573603 1250 20572353 20572367
    0xc08010b07031b0c060206091002030415050712020307050403060b0a08032205041a04050f010e280906050414010204060509040b030a020a06030e0118020616020303070819030b0f09010501 82
    0x3845800001145401041c4111138400203030503d94003500c0306040454801e4549040b050384916040c0c410403c1c040091130007200301c041c0d1101020702042079034038072205955a050820440c607243d40008100003d0580c80740040c405d5910428007003110010320018804401600c0c014103040e6801081080e8483740340500128000102c2e0b1849401180c84001080030740391041c5c03030f5060356032050030510f0b814034242c0500e66001c2051190002c1170740c9070544076528041d01038101442e01984c010085040e01584850001c40c117803403d02440801101c1c6080002007104450988010240c565050b00915060003118111001c6a4a040c1404030700c1041000400d48040b1650381482003500034001070301c5400b1705000900780c2c0c3d01c1c00900c88170110301d001d09607820080b05108041040020308016035900d400d41e0540242d05082d074802101901c0841d240d8883e00318007402c0300501081c7e8641034110400320390901806940c0c1807003c0e4801e0000d105141c50400d0182e54404422001400f0651250f44 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 20574853 1250 20573603 20573627
    0xd1d071e0608041403070b01090c020f0c01140d0e060109110c10020d0b041407030b030d051209030c06010906030218040b040b0a0209040f06031b050105071e140c040c08010b0703 78
    0x244d0f0300010180e40e60360500e150b206100450340384811800411884030b85d885054a05102030028048480d0006841c1361030301048900307241840b800391208208242c0c0e1109032856012140c90400c0208900810590307250b03400d202d01c100f42d908000d1540340d5005c0c1e100030744030130074a03c0c0001d04505100d010040e0194101915901c10f2079070781c41145405554502900c22011490001c480c2c0790301f040c10005090351100da00032170207980016100d1843c9580a81203411440401e2050180c0b902e81c465180e045100301300101d0ac1c148103520011404800310350204040300d00c01c0326540c110201400303141034075040807100a40207070010b4000402098501c3d07103540e40446481001842d143c0d441c0c00040071034070140320310751604e5540c88050081041803aa40c4178840d4a000c0c580c1ca0091130240002d0092045680091001c054101c8070704000c110395000d116400d17444003c0c42041e40700015130540e03038160202c00314400c1c1e04103910468400e00501195040c0e402c046c2d120740c54668191001e84114550034 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 20576103 1250 20574853 20574863
    0x8090f03040e0a050403230306010801090506030d140c07080d18050105030a0b03010605060a031d010216030c030c0c030f050105061002101505040f050403080f0f130201050d1d071e060804 82
    0x180b15500042030180500042c140d540c00341c0e00c90174052700040404005030042c1804901e840e050203443ea0b00000c803041e001c0001d1030b262450104c0088007a0842c000e5402600641c8142c0001040441c40810900703907084a40e507070001c0c0c0345219003521410b19038a104032800320b1400c01c0071514010981d08803808800002e80046007207507403407003c100c2da81d2012510300700080d618004100c004420100030428285903000039130801480a107130b600c8003a20f118004090000c001d4a5008145c00b919202d1a000e030000c98007400c076640c82c200b408541e44a8003045a0b55464100012414a400640321280218650050403411412501040203141301c100761200c40300360460024180e610b50044d62809007100c0d40218081c00c00349000383c81e18101500e000c100c0c2c0c50034810010074a01d403000c142d40c0312640211310031a036452800160b605102c0e010885041c1c90030300d1092012a10000307140c508002e011402c507001182c0d03a011150501c1628502c40f1080b07426a58104000c1f80300d2607507250064092 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 20577353 1250 20576103 20576117
    0x60f0a151401021507030606030c0e3106080c04061707030b0a06080304030807060c050703050d11090306150108070c021509040204120501200708070201030f0e030a08090f03040e0a050403 82
    0x48015881c1c4100305c07a4030000988404052001035854021402c1e212007908100b00c90311000c0c000590080da071a0301100e001040041301e0064801a2800c01c8654031240340100003d94880c40340e03e80b43c01c5a8004240200e00f000d0001400107443d124000105c8440006402002c1c00c0d6900d070810824050b10b8802074a88074580440d80a40500c010700003035105c0c004c0c5a907200700781c2c03400c40e0980300072000e500c05100c400d00420b0b0219030070a003210582440c6803000504c84043c00114215409034090160b010321500d410000c6401d00d02c01403040040b0243c031036410958900c401110002c00e4400300a4000740c203580300d0b80c5400c41070000b6100d0210000d01c0941826100c84403814801d4042c0320544443c1e468a001d00c2402500507002804040c00c0d0045130701c0d00700703951540e10f014410020700a04065407410785440c0ca000650090809405203010b5950758003c0150041483c0300958003104580114030189200750400421a002c941954182e06040e40d18052010b00070300005006500784030728 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 20578603 1250 20577353 20577373
    0xc040305191b08031c110a12060f03030507061103070e061303051c0f020a030905060304020f0a1d010902070c051c0602040603050f09070605030118020403050304030302060f0a15140102 81
    0xb03030403051000c0d01c5620002c640302e008a401c103101c2c482e060407000310140d00d005141c0f0031134000403044503000d01603828601014032210441c200100b40c240c0c050107650a8410307000c030815510100030000c1500580c414800451000000903a40c4000c0c3e030188040741c05006558a1401c1885c00f405100b440c01c500f20000b00d0350307500c600d400e0400c0e90500b15a031900c03604a0509041d000900c0806665152005207481c0040d540c002e01014118000c4e148110310200001d421907803018411034805002514203d041170796018013804071812a1494403400036140008954404688295401e040d04110000c003418a0034091041180c90f07030842c03a0030012186c5000c0c02107400c034002000100400e80d0009520f180003000c82c030040e00c001e0001010364100340c4082107506c0c0d11a09807410b480d200c01d250b01d0032f4000000300c00020712559000802a0101140020906401007951841003e8150703140c00b05540d646500c00450382c808080c00d0312980701c54018442c10b80003000219400030107004403415085 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 20579853 1250 20578603 20578643
    0xf05030307020a120801060e04050405100e07050f0603060d0813030b0c040f08030306090406051008070311011b050607030b0103022109070504150e1005060409090303050c04030519 79
    0x200c2101d01802680c4440d00400802c030035044600e0701c110721483c0c4590340f541003510050906a4040c440c910681d1681c0c0403d061050038840110810f607007a00070000b0365504030329181c80d0380c0c0ca440ba451183c0a5044001502d041c540212841450300416141070307029142d440d1031254000760580c0d0020014084080009442c40c1303da42d001d10003031042540c54602c0c20024281c894101d410078038080d0000c1c014081030f40c98060340741c0d40081e4002000319095503060135402d5255442c0d0b1089140307100300e020000a110400300e01c03c0f40c006003030380c0307102440c0502d06105c01000c3c02c20000502c4d50384004002090315100c1e60040ca03c0a0381450050326014407103200203c0b4031592021071600551640520541d44070821541d002880d050307074107002000140501704061802445001d5034400c1e440001b41d40d2501c001800c10140500400380e50711141c44460920041100000c103c01103843c002c0072a1030402c11a0071f40c0c080380c0c1e000c00240030f81c0c0604091541210603030b820460b00318807405051500b40c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 20581103 1250 20579853 20579857
    0x3060d0519060203060901060504080309010c02010e0a06030e0d0306060c0308090c060c0c090619031b030605090d02070503120904020a0c0203011109041508120703090b030a020901120506060a0c0f0503 88
    0x54042d0070056100c0c1000380820046036010382c0100c4c148003040104010710b0002005136032101d4030900301080084014001a26003078407286a90b5800101d80c1da01041d0b142e01640b14000000194040382c1028002c600c00ba011203225008800120b1a0b191040000030b114001309584000240d090341d480ca9035000204000380c101c0d07058069140c1000040e170505040004666900c690101c1e0050a071420101140c10400c00710f0002801c1802c9184840600c500c01201010085078071603002c00032490003829542d245d8140d01c5d0000014011105c00084900d0700007845202d0050399091249007407001001c100095020140a1040c80606141d460141e42c00b84102d20203503400415003a59160410100811207201c2841440c405c0b64522041c02810700025040708001d03111000d0319030301d00c075506081c0c81f114000e60000b02c117000004100321146200340c0180110308030a8803107882096103e0030341c80c06e4440495605800c02c07824131650001394402c125250348035020710841035170340c0c800e82c03915402c40d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 20582353 1250 20581103 20581153
    0x2505031f05060102070317070305070f0c1e0609090506040f0903050408010f14040204111c06030b0703050411011206030b04050102040e011a0304020907111c0207081203060d05 77
    0x1002080121040804141c0562039000d90b003480984080f508640c0d8403541c12840c1c8410b21184170000c14803d00b050b0254044a840039008003a54984042a103006500340300345028920441e400c407000c0500707061911081206444030707901d48a405500700303d42d80703009000003070401d03a000b40c030303100c031001e545000780703d10b0300003500030361b00c0310707502d40c186584070303003590000c0782d075202004c3c45c00105002298064030340c107420980c11200494030384144480401070f806107158000c200d0240041189004c181580014105c0c2e00c00c22001c43c09640340079040d021110102d074040c245030640d5024581940c071514032040103000f41c0000041c2d00340c030380d265014900c0080710202d0300b0769800101405a210303440d8075a40104610700e0003114015240d4002c822500024000038010110742c40807800c802d00441c82c1c40400c00d0120120303170701c4452010f100b590b6044892510000340c01031071000718603804d001c5070300741040d1118009a441c58441400f80107601c4880042540c041c047c3c40400307040304a00404e02802 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 20583603 1250 20582353 20582383
    0x2d0f0132043215030d020a150204030b0a090308070302030403020a061d01020d050109061707090207020a0509090a12020c030d14040f0806010603240b03040501110d0f0612020102250503 81
    0x220b07141540800184008000f850351080c0e0003124800d07981940001c180c0341d1075902024000030300d4103d50030b4078080c0c050303500000d01402c0c2032410002000916441401102d0082d641d001188e02d80c81c00907000c9205c2510060016005102000041482034206900307400c445800c0da00c424104041e468226003003042c9010425403280010000c40c0c41c1e42c0540005803a491281c0c60b001c1080c0c3c0d0300d99903500801d10600c05140e8010601e0002d55580906010082c2070140040000d89002c5946079210011004101e600c10450f15061800510000b442c4038036042c040d00422464560720360a960040e402512900402c0c010840414000e240041902c01000120024801035050441c098241c0f0180601d0300380c0d5000300d00042c064015a0200181201c6c540303007642d81e8a8940d414840d0241109554141c0710b400e000031030081e40c102c140c0c04028108100001000080e072034584030b8041000c80c0c1c50103801a4042e1a091b80b03519002d804420404080301c06030146581d860300446d061582c82075090803 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 20584853 1250 20583603 20583701
    0x903081b030c0a020316050102031e07020a03030e040507030b060a0507050a050d08010e01080a03020303010b0a02011d030306040e030c060a02280503040303061401082d0f013204 78
    0x1103017010030007079020070072542c1c0880c0300e20b04004c0000d64034000d501c1c000044039090b020b09941007071000c00300d5114a80141148490710340b242000b92464505d101264041c3e840d08002608445c03080c89140040342d0f0050415141070801c83c41207a068106020946181c040c240400300020f00c100300100d000d061544481c9215854181001c223071000c141d00880d00d0343c1042032000002a070210840c1d0541c4c00740c5080e01c1d218040d0040c102e0040c4a02c461091058000582d000941400000558403962041790f042c824000351031340c90794a0b03004d0412081c030168450300201d084d454550300604856030700c00707841a1170b0311b004038001085c00030701c4060700001c0350b4000180700505606009513005400301e2202c260715200d0b008002400c0c10401445910350070b0307080880e01d503d0460900200301990900010203050b061075116001050700c01c0c403420303c005542c05810100721900c88000c100513581c6500381c01000449d6000e00c00585410b0300d2144c0000417060f4500500550942003903415610010300d82 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 20586103 1250 20584853 20584873
    0x4050112020108010e0c04060c170318060105060702180a15060804030e04020a0c03120e0d030e0709060f06031a12011b0207080d03021305040903020a050d03020a0903081b030c 77
    0xb503c08036040e0803030010744040d035081009011003041103e08494962a00700e40089803401e046511034108510400c4494000061294445a51074200848007400d8265020750341c0c4e0764104610f074800c04c3c4001b500800c5050084151200c0c3d54001c0e540300703401881c0456100f66569401000580a41144020620040521003410350140205901030b106a0f0704518002c40e500e4003401d64500240d0040c200803c10403100c1489480360003c40e9001c4550013150a902401080174003c3c1c623101d0030030030b25446038280000350000d0b507005000c1214001c4100c5080c80d824010110041c0c84040f42d01000118000030b012596110041d42d445040c14002c0001001d0f18080c6d5001400d106103e421021075000100074008100c0109030940b40552500380107a0303d007900c40312035954400541c002d0b070f802898541e010b0149900840c1030450b140c031803019299484d40c0110260100d010b0700b405c0ea400200301110900000701c0700c00042c501d000c42c003200750013a40030a050947c550390101415440ca1b80200d4251 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 20587353 1250 20586103 20586107
    0x5010219090501090b18010c02040515090907060504150203040503060a0207141605210a030503090f01110306040c0e040501030804050307060215070e0a0e010806100e10030206030603010209040501120201 89
    0x1e00680000d01e089002d4a01c0c005448169004d04c08103518a07082c40c00ca0b1391807903800f9042c0e800380c02d81e010b4020b0190340381c9007a010b14018421800f0900a41c250000a1014100821182c0a84045441d080c0c00c03e4284500340101000003494541588010040403034540e408002c031030700c20704c0301d50000742e92400b00d4607083d0f000c001c180459010719032002c010355082e05d180c07600c0b00040e601c041e00c228020844c0301402d4810440f011040c21f400c0e01400640e507040c507600000a40c8218491012102040b8850101600700d4000c2c1c420040e05c0807051012402619060f0040042c80c04545022100381034140006011103200381d00880e84240001006c1009090901801c00108854000b0f810044070540e11401914001070025040100d154007080d42030303070f0f400700440150910f405440080e685a100303c540d2054251041c1e0305488680301c00041d00c40c4001d00ca24461080800030a00d51459907003844855080074103166031554080c40540c40a0f1511312500d80200003452070300a210080e4000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 20588603 1250 20587353 20587367
    0x150408060106030b060c280602030a050405160f05090601050f03130c050a050105090603040c0803070812010e090c0907140a05090a080a0807080304060603020409030519020607020d12020705010219 86
    0x20704c90180c14280030b0f82c51009804100c142e00c2c4111501c1d185044121022540210460541e0080c1114804004d002e00040d0640c0400d100324032030002c45508200c0b90300310140001e81e40c800d07416415403010f0700b0710881c108150110707004074041c10541d0528080800c4001b60390011100310760700d400c6201ea2102400310030310b811001804152090034605051000003002886801400e070300445001000c10100321851942c0d00041482d4000e6940310b02c0b9614021040384d10400c030840c685845100086401808901031034000c0c0d000100402400c040c22052240c295030081101043c040109510400188580024250700390141d40c1c0680e103800504c204850349040b604158519444106180c001800da2022212001d810500345500e9aa80345080340280a071504001d4000e8100105101019080001742c500e8502000e076000d584005400102e9070380c501190704000507407140c540e0841c41030142d800e41c0d2400c1d1840c5d80152502c0030603140c260a86c0c1c0000078000030034011180384410345501c951 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 20589853 1250 20588603 20588621
    0x7061b080702030405040b031501060f120203010b09090a0e0d09080115050d020111010905030a0809010e06040206030c071112150106020706050f0c030d0501080601050f030102030402060d0b15040806010603 90
    0x1000c024034104807a00070350f03c1c095405a00d00442c1d840c509003d26507000c0100a0300215400807251107903845080042010003990345000114090825880710443d440c02a43d0603205001200c6051248400404c0103149010b408000c4207547d820103004078250600100e82d01050a0300c0e8050400c1c5003451090071904d0346440310076900c8560005000300d560b070407207030f24a05409282451141c0c04d002ca1040c010900c80d0001840c2d4400014414545a0414440c0c1e2240c103450300200003003035100014a84440c42110000d602800805c002020f80080201400d03450703002da0300180f190290513010030035082e10040d035510241c0c401c09888001520340c09001d4007514191000d003982c1032030440c0203402030007040810940c1070800b02d02c032800300360100159410386001b61014011965545410354559100b80140c40c0103460303032500c194440c1070500840340126805042103241020700740058004041960407140c3c0b046c150310303c3e010502c100c4c4000e08054026080640030f55450058094100e40d4030704 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 20591103 1250 20589853 20589857
    0x5010e0405040b0106050f04090c0e0406080a0201020a021c0b0405011506021207060c03020903010510030b0108030a0905090c091002030309010501051c060506060c07030309031b0503031806090607061b 88
    0x240c100310010f1010f002050440f01c036403d0082c0c0754145080c90070300324026a0055140140f610306c0e211142d0340d00c0b04121003a08002c2e14100515a181d1104540303405500c0707406400b5a011030107460060800380165600d00d41e00b1340c003e0039009000e6503800d04010094400b62403507074441c40031551800c20701c55090020041070006080c881c0a002e1080b03c18081c081010389959a90f0035103100441c0690100d8160080040081050707240c5440d081440d500f090205642d910000000820b50020001c1140c05040032a00c802065038030742010041010801801c410003484188140d8199490f0018004002c0155402a42c0c0344c2c0341004c105402c54005034002d500c6040070062007111030710000420b070a1603400000100321940c90602194492051a2680e8030303610661000100b030540c0b100304003043e00e201d400900d000c80040e04101c41e1207090b034000c56a05400421803440300c00045030a05022003006816142000401c4000507011f40040005850054442407140e0000341d110360099070181c03080c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 20592353 1250 20591103 20591111
    0x609010303080a0506040b09091006060e01090302060c0109060504080c0610030308070309140d020a0b0c04030809061305060403060b0103053402120f0909010b070519020d06050a020405010e04 84
    0x150318014540c0c0005030645100c9a13031000401c940d41c032250400701c800300015269408500340034540c51b655006890300608040d240a60202e21075215a441207956176050307452000c0103003160200700c25588a411025101d6689925030000980d040c042d0a01c00c5009403591929036030242109400c100e00140001c18a6640101c140001303500f01e800160803580515000030105c0440c90030a240020040040c180351040000142800e5070014034885583c1c400c15a46134583c45c0d51030143c1c2580142e004c0204007000c240410400307428940c02400c19600025402a5569641d201051041d48a0307041036480588271161b418a558250150541266103e901c154054941c0c1c0d0b09a05201c1c0e030100022002c0900c0c106141009108120040b05c001803060b030107555480c10100c54803907910034801e4a00400240c03000080401c00c11060b65200341c3c01c44080e0940580c0144d50454480d0386200c1280e006180000d03200108116108075032140e86185401a07499007002c00242142c1031b6074202c03074419410 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 20593603 1250 20592353 20592359
    0x1150b070c0807060f0c0f050616020d0804080a0804051218101d040b03011d03040503120a020a230a0b010305010b041a10021207030306030308060604060f08061f030204030b060901 79
    0x1120040c031641c65007605d40409102403510f0301406061f83d500300a042d41c8101e02c14451514031991800046419035000ca8044070140c4000b6034817a1000c59014054000074015180740c6406100c01d290f0180c13203603043d10214000c0a16500e019000b508462150700c0101210120509007818010b00c24162420000b1142c0b050070304d050301400120290500451300d030761030445161400d403c0003c110707104190813502d04844034040c95881d007041c42641d00c24403458560301c24851120307044621510342580540f4501c0280d8032120340001c019601000000c0f0f11b4410900312000c284400900c440c422200034032154954101a801d407030000441c0c0340319070310300200301544204030304031141c0011007558042d4050a40510076818040c040e10b03000d8001d00000358210404d641933100c0000c1c2ca100382c4801e01079071a41e4003030040501070b5000301c20104221000e01100c86000d2401c555009400404550f9501d0b0032200000c20313642d0701241d00020903000b08060007009504d00e6056441302c001e070b50030045585 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 20594853 1250 20593603 20593607
    0x60a0e03030a200f0d140402031207030207030803040b0405060601110c010305060415120b070c080304030315081002040602060105030f030a18080303070c140105060306070e010201150b070c080706 86
    0x100292490b200c56a40f030720102c2e152090341240340300d038104010f1a50785400807405807001a40c0008092455680750188480040080042d09401290040e00400020a10080e2202c0c2903000140a0702544034085001000800b0b9030001c5105a101d808150f815081a28095252078000340580b41400051005902101f000241c0702d2520002482c001ca115298070011400500f140700c420403002010001c0440c86d0002d48596007601803040308002e00c5a034801c4000c40703415520b040c004140880400204000c40c0c4a500422042c0d01e40044801225640303e515038500302c04060304000b42074020408000007a01400303014010603054010700200c0075452241d03912445000c040e90b00344001c8004105d148100c80701c00740c020303140600c2103030303900d0914106c06071011a94640031110340d0815243c4861185042c066103002c0d0348054028034241e250500c0c01e540c00300307816904604665a90071803a4060720f603072644500500c48402000c0e921040c600309032001d808030760000116680840f0b0f080103666 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 20596103 1250 20594853 20594857
    0x50108060a090309080d0908060f0103080306090a0f09201804060c0c08070503091c0f0204020a0c0503030f01050f010804030909050402210c09010f12020607050705030703080a02060a0e03 82
    0x1c010400002204902460b0940e403004180d00720350580d00c80d0114044841d60420050030a50325039100b2600c1d140c0d541d451f08a0341c00d1003400300500020050010039600d081106c0705503000358134080d0200746091107102e1700c02125803d110507078041091174090402240301d21201100c480050350742015074071020b420150180030161008012580d0b0301e20700c9900601c110f1015910301d610208241c0e884040b800c0c001c1c1d0340e030051103241e8860030034203581c03403600102e4220000c51580d02124a9089554a0702044000d41080c2c1219040c0909408020300040c0188011846210544101c4030b0550403c014010f10b52181403125050059803010b000200b50000b4084048038554030000c41e4541d114400305051188005001c2800c0040300401441e5450106400020315001e450441c0540e90f14200d07e080c48910b4800d07009500c85a01d20b010242c00c0c044c00400304035008070704403201540e50740040707458810a0382c03095951010203e03244084540c180510f40d040b051a841c1413000e80d0403519400e80f03034 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 20597353 1250 20596103 20596111
    0x1003020408190515071d0405070f08060604050a0e01030b070804051b03031905090f06040506040501031d0303010e01060e030703020a05060c0a05010f020c12040614070c03060c03020d0b010305010806 87
    0xe1540180b0642000380070441c90450024141d00c00c2181e04200704050708009422141c544202407070314a28030036040c680310f000d100c2c540c1940c0d2048905070340341301580c04040160509810202c104000300703980c3c4400c0e008100421100c04c1c080e10540c0b46050a06008401a1401041216103414800030807000a8051102c403100b50100e11203074002c0c000030340745201d9001d407149003945040407124103076046000f402a014041d03402068011f5030324100311481c03141d40550365108030248000d00c45544039600a004c0700510440070300d5945a0045150b16580023640300104082e000340043c051103601840744d0005010a0b002807244030706580c0041e22242e840d008050041d000414400f1710040c2c204000e4020a42050003000402d0800003500060760010190f400c0e1840341d060081e0013200b040040764103c6500395641c0c0d401c58082c00042c3d4080d031003100140c8000509100c0400030810328460200900207503180103035611403190071041034583c00202d141c10b1501e45801004240d40c0420b0b05584 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 20598603 1250 20597353 20597383
    0x30f02060c01060302030a060f180b0a0c050d0e0609070f0e0105060f12010602160515030f040f1704030209010801020a020a121205010f030606080f030d0906060506030a06051003020408 81
    0x310101d0000c09401000c8940c00a90f2511540c1403080c18449541e05c517100413803030808140b02c4402244200c074510300764076500500002050700010500c070310310303071189045050380c0c500750345840d550b0484642a1501290010030540107078091060413a42004810010007070001c00034030462034544800000803052003110301850000444240c0c400c0404222419a8a102c04101440d41c5031600295a860144050501300403829004281454080c00074840448400d8015286039129982300d1794a800140003210034480d00700c64000002d000306109500e12203d4000d880d01ca41c40c40c01040224441a130100c0c5a40e4410443c00035045c0c0d0103d0902c42c0c4c80d8202c040803001d004a004111b4035541200d50a0210b540b0300b40c00414200346210003001128001c500c18804e2907140d0f42480e8072266414401b011603402004408a54103150300400030341da01908000844560703c00104020360f108807a56540e9035651030003440340e4a424040707091180f1241c42c08600349410000d1541c2e45405421148c4030f = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 20599853 1250 20598603 20598607
    0x30e0402090d0602130e06030f19050c031b01020c04091a0415020403060605040c090f0e100b04080a1406090705040e010b0406030506090d030b0901050907030f150501020115030f0206 80
    0x141c503241c9058480440340d02c59402c559446101064a0701c64041e801100581086400460007030b150028403000480a000b010b040d00b02c480c454040005055040115014002c030340440c1241c1d80c2c1440b14010a500e41942030341401c840c00002402c01c90b2725012940b08074641441c200101c3e2190b0110f022031444c05061040c0794a9a0030001e151810036400a02000c0c000a408006c2080a40001e812208252000d01402101d00305c00e983d120202e0040c40e104070405841040f0320341c45141410b400804c0c446080d584545c5840c0341901560141d005402c1560158a4100402c10000e00d50452002d040025105a0922544143e04e424052281d28451501c6030501180d02e402903100070341d640d100400c1003000c01da41c0c1ca482501d40c0003c88803102c880c0602034a00791000c0c00b038085c401601c140203089040c540c2c00c2008000311180003806d200201035441921051080c020301c1359000380d41030410080001c40c503081c002429900c000c0c480c1c3ca181e4207116010000079501491110440b5411901c9035 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 20601103 1250 20599853 20599867
    0x1090303052715040317040b12040f080a0e09181b06040806010311011205060906040f0b090c0c0706090b070201030b0111100218060a0206070f03180501060f0e0103030e0402 76
    0x260342030b1404804294400c0c1da9040710503220b440d030302c000c2085034421540741c0072411006501e00c081d0300662182d0003201c1c004001500c1c004001450041d40b00d8801c107031102c00380e001c42d142c08469410246400020640050348010289816480f0913804544003180111580021075070503106d83c1416088800d1032030243d40c05074140d503200f05545c05440d1780380c100d50366580d6a080c154110f00c1e2903146035000ca0300a80c0150440640e0340151413050710003914404494035901d013800010b04841c4d54601469503170380010301c5103648030001030b030050145200080c0c6440c0c007046520b0030501141d2040e014002c046004001c1c2124040548168503024280024140b240f5030060720340c405030750724030190b90150803000080c451f25075014201c04665450401504080d203c20320a0b540719800b81600568443c00014102c3d47c1300e4410704883ca0b640b4540071994400e0303100d021440b0030580408070303070f80d9458400034450624510382e284001c21581c2d980450075450743c2c03405010011505a4940140e400150745 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 20602353 1250 20601103 20601157
    0x6060b0c071a090d0803070809030703050910110a030e1903020a0302090a020408060901020c011112060409141219020a170705030405060711090a060b16021203030c03040b060109030305 81
    0xd50503c01d0042c12101ca10070b4a840c1a0310a948100c03903040c00301d141c1c0c002243d4901c000005981c102541910781e039251800b41e50130001c01070803000f50f0303004000007441d14803147c010030301124151034031903202d00e0150400d05042054034084049072420707039030445004001503500c1230508000c03650180c941c02200d80380d840954001e8440c9411030909032017509c0900601c201c0550040009545460082181d07980109105402e4800c0c0b4440c403a43c40060404a040f41c60140d0080d103045100d5419200e002d00281510f50274106c055408041203003012401e0804251200c10000c0c03444e09620207071141d481d06665039590721162000134022814045030380810002d00b041100c0141c01c2c014000c644406c1540f4102c0014000103c0b26802401e028001c900c003840540a0030701501e134810340755810400100009159070f00f50340010307179001102140c19111031809000850180012507070347c0741e03240345c5428881d070f41910290440d0f0400c0b400080400110b5444410744e40d401100c0403250740c1c8410745441d1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 20603603 1250 20602353 20602357
    0xb070609140f0601080106030308010e070e10030c090e131e020a0f0302041a01020303070509040f060b07171608031f0618080109080403020d02011b05010906060b0c071a 74
    0x200420001d401e15200d040e01100103989440420080122401a0b880d070344e0090a0310400c0c030008000c58400d400500038061100b1400d6030218080c0f42884c4480c24680000c0d0500320714228200c0400da840d000c0c40038640e0f02c204004040d20400c45046031509284111404881001e100585034074100c001489a032802d0140600500ea001090204199100c28030020080361600c01244203510700035145100003034404855198150580245085960381c20050724254008004541d00565504e4164110a02849203001038001420150b03201c1c0e5103403601e035801c0d02c8195081b1202083c02e0168103140030320380c2c01425525501020446d1603803207000303002c8003210078820890300701203001d0004a010f03070307100704400f07045d40344215044851561040d169007290340100c0c014020003000c100078409070811901941c001441072400e50091038041890700c42030280700c901122a80d458201d4041072003000c0c0107000242c11044405440c05507000419039490b0114442c40b0f21f15203112050140c10141001 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 20604853 1250 20603603 20603621
    0x117070e072d0206010e070c0c030b0621060105040b010503011202150c010c1805010f090b0f12040303090c0501030c1e0e0301090803010e07050c0307060b060d02040608060405010b03100b0706 84
    0x182d14881c21214810184d21580309000391240380c6a5400003c044900c41c05400980c2303034101c400e00c83d0316403c51710b540c540c8075001400f55800844143c81e12210150700000c0481c0da0340070501a041a504007010171060b1034000c03519504025050005024031404024600388892781111000140c400e42001c130102402a0402d1034000d518100002034641d81010450640103010400d20304035079190401900c19900b03014480d00010307030800b010310408552100410119000c00741e82814031401004610f01204200c5003100060740347d5001c6010031030b100100f1800b0700000d08080c810031100a60061143d13600c001c03840ca0b401034801280028900480321413060b40b00c0580203100c820b070941402e40072039100307216048d030b083d1285002501c03c41c40768042d121581280b0026602d090900d44074403028103402502c0644c0204104546d10b50110644018001401c00703803260005881c006040104455050784003c071088030800400c50311190b2000d00038141c2d91a5010716842c1d01403230070300c00000d04401c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 20606103 1250 20604853 20604917
    0x6030e010b0a080a170406020a030e03011d030408010e07050904030c030309021314090106050108040b1b0721031505060d060506130e090c0105180d020d0b0117070e07 73
    0x4603c01c003002c02c0840f1a24041c0e09203000b980d2010000c001e551041d071080c040185c201c1c0060000103441600803040c0d42000070004039121141c7d800b01050791651900008e000c0d400014100710044081c0500030f080704190010703202d034074500000300749000f00c020f1004041100580c1e8403401c0601a600440d066900607142139501e2854540017001086c0c09040c02c00c01900440004481e6541400ba80040d03c80c1a07581103080e40302c698468210310000f84c54540711075a00a041081e5601e208080c0010324060b4401c00d0070b030000000300320f2821a503044071008050405050186416003803804500322502aa2103555420f14400480010000e40d003240354081c00c00210202c0e55014410720340d0a8807031000311600181c44140446076594007144004d400f2840501c414056010303c004210b200420207400c0042d44c8555078006502c000090004480d9001243e0051041c6600100782d12064030150004140321404c007000300c030200384020201e5041000e10b024a1040c206002c1c1f14808120441d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 20607353 1250 20606103 20606119
    0xa020603041a0703050604140412110f06070509120604020a0b0a050f0409020901080106051606020708090909010f1b20030f1204020306100302180718080a12090b030106030e010b 78
    0x82c3d0002005084161011442a030030503040d10442c415506105004640c81056030160140456007a01c03c42d00c3c00c40e2a10b11801800078184d40041c080c080c2612821090760307400e070341c0c6001c0c0040100b05801030228211540c454002c110041e00c80d4400102a0f41b41c501d5003d4072030540a10850341ca10030000450039800001c2000514408681c0241410b107009032a50002d5a8031118221058011962851400020203080801082066004203c2c06001c1e01c00a85401c5501c404518810000d4401c40d24a80d0755540003014001d85200b00c442e5010802a0500007003154007009016920445c030380c03080c551a0000858090b10100110341c2440d0b0354500c06602c0b4040b00286801a22046500343e01038001c0c4000524202d40000c19181903e078024151400b240300d1440010400300028002c2d401e1000d030140c505900306900c0350610082c00000010080c03034074a445c101c1d20fa040b501c0001d00c240021845c00f07210341c20361002a1780c151034003440d0005050000310506c0340544104d4450030303001915 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 20608603 1250 20607353 20607361
    0x2150a02162301020a05030c0c070f0b070c24030b0a05030d1805010315031203140a0e070902090d0308040812070801050906121009060603060f020406020607020f0a020603041a 77
    0xa0001c85030b40d00d0654040b405119000a00154281d128100a5800260041000904200d005001b404440400e001250001605c40061000000c030031b40004010740808161030041002e5525008050030418002c03006941803044000c000d43c3d00140380308245030300c424450405440311862040108002002c561414043e0040076045015108400030700020000d004520b950103401907210f2160b1078540d01c100c051940c2c5611185074400303c0c1507810191640c0041400701e5030313040e000c2e0041d42280300020b00440341c52209450040c15500440102d07005118400240d90f0705540c032034695415042c0080507a4403440d01200d00d105840c850102c0015120501c25126405400941a60030684600c4400d03124901040711000d0455003101e0030350f208104040d55900703036403c041e01c21445940702260507516961244181c03a01e1600b407008c1c140d03021074100503c5e41e040100c0d54000002e4005084654202d40c076a40e01c0700b590751800b23402108004040340400c5540c40c84500c842145080f29005820 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 20609853 1250 20608603 20608613
    0x302030f0f03180616030c1505010302030a030f03020c0f071d04020d02100903120807030c2f0a020301140708010e0103050303040f0218070201050108071a1b01110705060a05150102150a0216 83
    0x141580250b400c05234909402a0b4401ca9105050507a44c0080085c144091035036403c640380c1d00b40d00c42c0c4204154007402501e84003082000070547d400030f400058501d050034031503c5403a0940c0d403100d40303410b05410401e001c05a114220310a80c003136010b56002c0b00106640328140e50050b09070f800101401c902c0030b203201c080766121808074000c1d0324aa80511040c002420100c0302d5038a0700500084c2d60b440c19014401c41600807002c0d1104014003401e491040c551900001d084800c55104520ba9110716810007040c150701544480c09005040c0c944c440d0341d410f68a503903540f404002c000401281c04000f40c03034152340c0e86210b459900c81442000001e9840c140c80001d02a00082c80b5008a5105900780440c5000070760001c0c0141241360030300355007051000184103c211240100007240741d5038400a40c0e100d50080c000402003907020300020081c50504020034001c5030300003004100d0443c0e05881700340c0b41d680c0c040381c401610a1406042d80f0240c80b010900ea00074071401b90718911002d401054202042 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 20611103 1250 20609853 20609867
    0x8070303080604060b0c0d0c020103060503070303030f0b0303030403120207080f040b0702150a0c020d020a03050708070e06010201020a05030a0c1106090a06050c03060a0e10030b010f0302030f0f0318061603 90
    0x144041d20140301c00340c0d480e10700c0c0f59640121b86c2090001e41007a8182040588141c060039030480c01458041401603454000c2070402175a600705400094581410b05184041c80c05a8032301500141c0040d4510714103600d0003040d07151280012040150009055001d2100e01c5c400d803145010340000e807036540d0380d035003420424a90011200b00e02810382e1071140400f01000307a065444290498840c09640c012582c200b00c400100c08608a0388100300507404070100c0c0040205d00054442e10307005003041d41c14001c2100c080311000340070b50704583c010081c4420640d030043c1503039000035180e040030400e604401c07416101121100c9610855101e600b0402c48a06400520081103d010302e01c200901d440707058150f1958481152042d80141c01031100b040001200072481c1d44c0414a15001d9812507180d40e01d64000c107101fa44a0b0078208903280083c001d502c3c0c144a200e01001c9010002e1020001c080d1038035851380100c0d900104422040f11703011010f0744230b160440342014018118140c0721a5a403401500c01 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 20612353 1250 20611103 20611111
    0x30111040608240f0102010e010203040503090a0e061f0309021008010609050103050405060f06010c0501090b06010f020102031014040204030611040e0108060106080112020406050d11090915130c0807030308 90
    0x141c405003c80c803c4404050016000d01020001e180c1660301e4030280300c108a1102c2ea101e04566a501c3e0015510700d0070701c00385004070b00c43ca0286945001030000c1082e00b0030141c0101c0a01034400b0140089179440c40c1080302010208030600040540d000420350081c40e146001035003010480078083e6290380c7c00001c15050302c0d003640b126001a07407980d00441c204c480407078006180c3e900110201d0307041604c03180303010740c0701d0340500d020103001206a64035421350f44201d0088441c04505002d1046540c1c002c90f240540d005144001c504515121403180d034507001920540400c07a0150007110500e032940e80440380590741100d800c2c40700c0e0405d00802c1070150700c0b500ca9644044084070012501c0000070914904840701c1350b603100c140f40d0030130301c0c0040b009611030f00481e8801d5a4030400111f5465102c41e202400d8041c0a501d603a410400b020b10001940040203003205070401d4080444001c854400c07207801440c80f032844c0328034850314038000104003001d8102c1d00c4103100d002000820194420210307441 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 20613603 1250 20612353 20612357
    0x16032a17070207030f150207080c030702010f031103040b1008070f080c010905060f09010302070b0124030203100311030f010203010803190309030905040b0a05041803030b0904050d05070309050301110406 89
    0x106568a0300120780f1003002d4040100700c1002104042d0108143c0081c00c1c0c640000c3d1100146001c0700c1e80d503249210380c8206000c1a458001248080640d030300000b041e1424001820107015404021100e804d50f07200080009102c4280c4501180f150850aa8610041c0030100103c0300786075103401e241039001545200b0042140300700c04801042e075100c5c480300c000b107c0001e000d41f402c1c1404042d00105503040b000c4400c0c10968203101e0100030660401016009040c100324500054003000d00c98251901c0c1d1841c281c0c10300d4010010302090001c40801203046a400403181d400c11400040060b0801042c60803402c110340c001b10000c90849008001800000c560503170540c05510011403d509881c0b4a51000d0085901c4060810441c1400d401c00141c05800401403001340d0345990000b8100c07082000802c3d200300841580408058051040f4410140101d441d52060710b0180c0e07401e9a61440c0c080100b00300a40860301400309406903200b84007500d8024000d200c1244000005607980e0418810400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 20614853 1250 20613603 20613647
    0x60b0c0f010605060702010f080c070c090209011814060a120608060106020d0908100c020f1b040b180a020703110a0b040c06051804110d0911040509030316032a 70
    0x140c04d2074114110381550364182c40e848150310070b040c0103540c5003800901e08442400304111000003d000d03601c0d8070015040840300140c4880010000408008440c1c1071010201d80b15502031040103429102024811811108030fa542c0f440d43c001182d01c0340c07149030380c14000c900b0504041560440402c68906030f60300c039400c84010a1103010f085804d00943c4c0300302c403500d03041803120262194040d00710000740c2806004a8a0b2160180304c5a841d000c0c41c1600814000028640d80181d40740a0003140200c0700111895852020a0205800442c10242a40030340c1030b800254601014003451b1054104988403054455078a0301d81000a21100203c4044501d2840c2c2c0002099440c007620540e1201500b078402e03840480b1031401400001e120303410302c1202d40176003842203108103011405017a000c0f910400c90f01031010040c806010035a0805040740c403094006008000b0a038184021030707600d00080b03140105040074000c8a000d41d158812a107405081c00c49809000c281341c00511032418080000400c213 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 20616103 1250 20614853 20614859
    0x6090902030d08190507140c060906011203080a0b01031112011d01080c0f01031b030e0c01030207050d03090f02040f0902030c03010e0a030809030910020f06060301020319020a0201060b0c0f0106 85
    0x1100724804580b449000d01c601c510707451305003c240d800158000c4007401c200041c2c000703100c00010180c02440c4058940e42c032807400c11040b00400e1210b00d00400e20038105141d90982640d02070103210000340704a4405a690340908a1a171094100e8000880811529991141c25840c040711004e024003805040038214480b0382182c9030454066030403a01020081d050041160341080080084103e8583c1003540350700807808402c035003084184044105e42c5000559117510307034485081500540080b4141481408000049280420341500e01d42c02c5180000750511140303000e0b0344128140d07801a401500d0200c0500d100784840e400383d000c1c1d80c000c034100c6071411035490406090750600d150494250300507030010780000f40034083c6aa0807440f02002e0300e0826030608040340010040740c200d0001640804403400142c03406104858000f24190000d40c0345207070611000c6400681c1290f010005236000450f200094400e40c0f2110160401100c09661a5101409903544c1e54078a000d142007940b81034000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 20617353 1250 20616103 20616107
    0x3181703031b070803040b0a0b0604081f090327030602070308010302090f040c060c1e0b01030c15050a050a0c0b100513020c0a0b090a08030103051509061003111306090902030d 77
    0x2d190b0b074942c8107180d81d00e59071b1a07039600d03002a403000d0102c6480903240d2842c000141d2364400500040c10180c2c0043c18003520840c0d1016185100034291403280307252408401c0466480445443c10a20507850140d10b80000c1c04501c01ca1002c035031000c0e00c11840411648105940310035000e048030b000302c684500300c4e2100340810f02156420780700140004180e040c01c00009002d1465400c9450141c18920b00210b0711418010001001d103404031042440000184100000c02d4032000c003403c03001d50000400102c824024216104800741070382440400701e02c00c0c01c86403050344d60f010060ba001d2600715a07400c10366514a403403107540c000d1910605c185242c150a203407041c801d88007900050001405d003000789840783d00c0c40e4080036040707210034021042c80001041643c0003e42c02144a0402000c220069a00c00c03140d035900602844000e42020003030051245140800b031082e40d8000c408115842d280500003401c52070b082e520303415043c0c142180040d0000440d4840030080340260140c2c2c0c642c01e04801c007 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 20618603 1250 20617353 20617357
    0x40906090209030d080606040b03010f03170a090b1308100903020c0103021c09080c030a080906060913060515040f1401080303040b01120807020d080a03151203181703031b 75
    0x2d042d4056000b0424a02e007a4401d040c00b507000f050180c00c003440c254079a485c58141e68000d8009100b1354201d400c0400030232080c1c844040300741c1c1c9402d40301410300c100e40701c0003400f900d404c0c880c0c1c060001003c10000a1003c02d0000d0300002c01601044802c1c0c0800d461030341000d40510300081d00076000f1011a0b83d00c65020340200c2e407503840f444001d9140c103a485001c0700e00030041c1d01307019120180103110701400d5660410081c49166481c0d00c81d41e01c0c500d044180c10b450158000c126030b0181e50094203000c41c00320107550407034500780d102c840440c1542da01c20640800e0565100701d19030244c02c0000c104103c41d02035025032010084040d1050701030f84c030395064540c0ca200030b0350001c0105000000420130b9604041c140e000051240d50a285440b05580004090320014402034442840000d515038a2640500c01c0064280c1500d100c11a218070308444181000d843c58130140601000d2421703488400740b140b5417400980343c0540d03001a0f942c24402c03071680c3d94104585044900a11407441d00e803403d480d0b81 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 20619853 1250 20618603 20618617
    0x70e19050603040c0803030c031009150e070e0a06210b0d1407030209010b040e0708010308030a0b01020c100207080f0f1009020f0d0506090d080f0f040309080304030302030409060902 80
    0x88429406140c9418040140e100500980e0001c84007100490a00401c0c030040d400b80980340802a00d034200000611520801640515500c40c030b00050745104408100380001143c9028420780701aa450b110142d030a141031000269100b550f04001141542c1c02c0820f001c01c5018080a040c0060140322960f411141101521070b80a00c141c1007280c0000c1c0003031184e00c8040c0101c0c1c240c03400d29a1720f03400b1030f02c0c4000c03c0c0c22450030030801040c1171002480c03080007154840c10b1841c0c003500380d515603107a216035440041c1200205039214030101c0d01c00e034020440e0600200000e41003141000c01280300944a0810b40654181401903072000c0911000016080360703c0d1a8100142000741007110f00f40d03000b020303942c0c0d0880c1c0002c64030710b55000d1643d80103030100c20070340030b880500003a00d44079035180e0520004400791010301a5007000d01c0184140e50111523030000e105845c005d1140c48506043e200c50080e603101c101c4c1e9220000300842090341c0400078004a03101c0e100d00b84411600d8410f00b10aa000301e503 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 20621103 1250 20619853 20619889
    0xf05150603041b06050304061112010509060303070803040503030a150b0405010807090b030405010c08090a08041401020c030604060f060f031505060111100b03070608010e0106110c1206070e 83
    0x9105588a40340c24001550007920810801d09001c401c01804055100d041c1c1c00080441c0c004020070052191a0041c005c540c221850910715094070805441001e00703060046500801619000414540b420800c981181d44c100c0c9801e912403a10380340441d925802194100003503070600c030b04a0409080215040192408208400e040c607061800444810300d008103007000b003000703410340028500f040f180258021800f41001040c0480030f06009006164080e00c120640d902902d0802d000c42d614200346e17001d8415200e0030250346010500100c1c0340c8844196004d926000708024442040501d610000c1104210541804101d81e01c89035400d420440d84006005003d06140c00c894402195110aa0080c0f0504020f2002800c503407446180025541104900c42e5a480030b003940c5140801840c5c0080c0080d143c10f030055810301c244050342d8501880f03580180140d441e12a1610081072062031000580036128028080c00c6991555039040c2c26904c21010602d160420f411504041d1185000d001241d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 20622353 1250 20621103 20621131
    0x20a0801060308030a0207020102010605100c02100206060109140d0503040f030b010902030402060d020706200a080a062105032206030b1002072606091f0603020a0506030402040902180106030f05 85
    0x2103017100c000c1e622000049045568a180118641c0d50391140d090750f01d007160b030320048145064070500c0705160a500454095500290400166a034044a04016291305646010000510002040d41d41c0380e480710040c07440c0000302d00070806510350b5078804200c1c0d0241c900520f03640d03a2100c402d412440141c40203900400c080081c009140407640050001ea40b08040004142c46803111100030754207000ca20704c88001d03000590101103a0720000c800d812080d40748c41040001d14180d401420b800301c440c81515544a04400318003030200600030f07038401e1528042c0c103140f032a03010080e088424240c0e00031003001ca4640b8800c00361a0800070340f1a00c0f0400e0b6900200400e034280aa541c141e280000c1c007000206510005a03d0402d2080c014280606900c000900301c903986090000c0650603031000c0e65903440c0c940301c0d041003d680c501c8070000460354251078256a94950b4000704018100c6810f01030f4110a581d21202c1c000c3d0582034125040b10420703502040220314841d180c10540300d040e19a4403100e8a2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 20623603 1250 20622353 20622361
    0xf0d020f0c190b01050f031e030901020708070e060d0c0803070602040312020102030601121503020402070803010603050c0c0a0321150905070309050304031218060206070f0503091b150c0703020a080106030803 91
    0x10341b802007620782d00181100c0d0140010a1400c01c004c003068000c2c4803542002c1400c8090f9601045113202030f01c16840586101d42c20030200c14060b541c002c00081c803032a108400709060084401d0003101401d10041a02d5035003c0c07a040501c0694414402142e4160107c07003444005841882030304c0c0a09030580d1841c510b004012241d41c058404000400000031080b40c000005a9882c401003044501c90031456860750b24003032028040315001486207012a008020306292124081621041d140e41b60034550201059054820f241d07050341001e90310180d1900d0080300500c40ca110a05003210b0000006100b03503925013000b1000d0b2101e4603401001d0fa4010700091000603164a1740556541103450400024000c10705400418a1640d01c20340168009005000b1300551154449070518403604140d860340c01d1405c81281e80d80882d1000313449124500741c1044160751001020b03e54400e201c00709548510720b07000c00d0380e01d5807600c1c44100d208984210000540c0c8506000341030469400c5447d003070956503 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 20624853 1250 20623603 20623609
    0x10050c150f1302040b030304030308090d03020301030f03110a0b04060e01110405060a2102070804060305010b0f03060f0d0c06050903160e130309030803070302030105030606010306030c0b0f0d020f0c190b0105 91
    0xc141d030101d0b030003901c5d8950600c1c0f0707803400c03c0907000940c001d5540710060b0420301c175400d042030800d0305c00c001003600420040c03012400c04208400200e0345450701d006940150b600c0c103814080940d400401400880c1c0c1400300b4017407103401030500d080401d0002c01441c00701d103c14500b41d12481c03040d50b420400c24080b00c0c1010740540c40c03240c18a07044556242010b02c00820940403070b402810101c1d0908400300381400880d40c0b500c5a2405040712015042c50300c140b603400400203000040030240700340070103400a20b450b15060542110b940d4040501a011511000c020303005420000c8001d001344103402c04508404c03048000e007400c6650080d01201d05460b1103e66605900d110002038051250201d00000018242e000075071041a095500507100d505003401c01d0306000d4058080d0381010300b0601c003400440c08480d0044100c0307604090032175407920f88248004850061000066902d071010072505148048a8010034a5503442002d6903c1c034298254040c644940c0d202000e0310f02c402d00b00051010341 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 20626103 1250 20624853 20624881
    0x5150a0509060f16030e070905070c030f0201020f090607081207020309010e15030708060105070c060903020103060b03060f041a09041101080117070b030403090b0a020106140d030210020904090210050c150f 90
    0x840e22013502c1c5016108d9040c1020ba075000c0e140c41c000242c010062005066206031448000d842030710095151142400d245c1c07450f406074094903407040700b00144c90002c01c6824411203100c9a0801c1c0307040300c10b103050413004e512031300828025404a1001c03805c001c841d00c0d0903808202e107605428003440c03c58851807012602c0756002000c41d81030110811216002c50301c1c0088110040115a0b945103440d8150310004054810b2640110a815418018015656618210291202c50560300001d049107195020701381e141644019a800c10840007d110512503d1819048001c10a880e10b034003d0341d80f540500001c4810085060183c0c11801050000ba102c040065070098003a01c0e14080103600c42040010300c0c1d0180a025002d81e540784000c0040510703603800f42441150448501c000d4420307903140a9203510711030541035082c0780d0004200820360b4807a48414074268010f08444640e0842040142c403179071212180c83c00c0d40c882c203d00f075400c04100c01200c40c0f20b030403120844405a15010b520845107 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 20627353 1250 20626103 20626121
    0x4050d0b0a0b06030a02031006050306061615020d1a090405060406090c050604060807031a010207060503040c030507030305070302060f0115050306030a0611090f0406080c0d05150a0509060f1603 85
    0x164940210080e03942c0c8010296020b117081d48401039032424002504c800d0640564400414020140700300b00705a9250b03003e41301240c0721520304103107094161800d1105031300340c1c0702da40244a10220703483d20004010350041600c4000c000503d11200c80c1d8100300a011a01101c00a281e070b070220002900117452074100011981c400d00402c43c0450310340c40011000d0b00aa00b21800141000c000c11050395454081c1070804a0450304a10720100804d00003501d980a9008400070720800101007000c0100e400b603d40c00640e044000c0d10449a00c0740740080040d031022505800600c952004070b420b00c030320000d189040701d90707605010500746a541ca00791201e030401041d0903814000c06940740081020340c0103c890341e2180d10440359442d100b91040202520340f030315906010b5490720006102c451030006140444400444d031b100f0348801c2c03a05d00146415132000301c01351240d01d070341e0130700134002d6050b0800c2d405101c0c4402903c91681e9400c3e40066680380490791042d0300004920050b404c5c5010fa40703c0848 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 20628603 1250 20627353 20627371
    0x20a0314010b040c0e041401030b070e03030903120a020d080c07060506010c0b0103031115010e01090e0a080d0507030b0f0a060305060103090b090a0c15020a020f06040302041508010b010504050d0b 86
    0x2c03400e40c0800202110280303c20100811525038000090b49040d1246405207248010005069419911911800d550007410365003444202914044907640804c2554000000281100c001d103e000ca6155030039002419000090320802c046e60055502a140e40e0b846904105103c50505090343ca842d00035100281c045818003a03480710a801007605410076502940c020b07202c0342c0f540c600e071030800b038030302201c001c4040803004640005000c85e40d0b400c1410b13811192a40d00200343c0c4040901030500342404654010809440000e041c010868103400180c818680d948040080540030014000f41402c80c0707582c545e002c1e4241d1018007400f8040d50019070003000626002901100725502c54901c1101564159281d0b0301c10754003541000030a600c1d49000d001d50b0100448003600085000c0e55421590074024401c440940f0108134580b110015207004503002001030225042d0301641c0d0b51087d03110b01400100b5400c01135200c80d95400b43c000c54003114800307041d1200074440c644808502010207400048 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 20629853 1250 20628603 20628611
    0x20103090804031b030510020f04030204110909040302070f050d050c09040809060d0f0f020405100c0303090b0f07020d0206070c03181203180609060e12010605060a0302040302040b0d020a031401 85
    0xc210920403078104e04c0e50140b850010242941041443c0800c100745e10320086004004414200d03180c8400c0c3c5007102d81c103071000f00d0440b91120300920f640c05034041042e00001c0107000c010a041d40000c0c450100c451941d810802242c5580074881380032104140500154400020b1505034200b8a0610b0b60083c05000101d0a2290800002e80b0942c007040d20f80701c260742c4441c0e103030442c1105031013285c0410b510124210301e41450070f070214606541213030520050298480e89a018036000e604903091859000304c0b0400d41d4036020f02c104100c041e003603a2000041c801c43c800c068413171380005051405030509450710406c0d945270759001c8581c0f404030017000140b91844500042d04d08400813840104a02c03c0d04c60110001c0c1700c620f003480c14505688004104420f50303804000b0150808090400601b007a1090405145e0a859250141186500580d045034000a012081d582e0550151040e00d10859091040080400401206001c0088040c1d032103010b2240400000384034002e002068035400300081 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 20631103 1250 20629853 20629859
    0xd0f080901090305031b060604060e042303040e2205030319060911030f0c030105010503041203140103140d0e10050c16030f020a0b0a0c020f01020703020904050109030e0108040f020103090804 84
    0x1d09640082906d011960350080710440340c0e030300038000386a0000040d81c040050502d000141c3c0b9075040c0143c0050f000380482205074000b03048001d109001e0340c014a0883e43e6035580e45a0801c1d52840c119482a425502c1b030740c03001c1c40c01020400c0c108001c1d8020b001181507031140454111800b5801c03440755055952890001010592400ac1c0900078104010542e00c9192107814108091b4006204203a210420401402240e8200342900d400c0f035000b046045040c0d820a1041d4010710040410702c8039548100000010060301003202c608800300c8800341d40c1c000c07140407010fa642c000238800b541d074420000d400100e0558407070009004810080011125100905000340300c040100340c00503100c03041000c0b168020741c100340220300020014005060300d049005074004040201c83c183c024851010b824105e5803c0e0700c00c01c0014042d5400508010640c2001c2c68030600034201c002c8100e000c68049811000d4075801402080e20450300614071200580040d4011002004c1d41a030032100c1c0c00e020701001c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 20632353 1250 20631103 20631113
    0x111010905030d0c09081b06070206120601021c1704050109080d02040f0611030a080405031905030a0b040b0108010b0304081303060c020c030c01090b0c190c03110d0f0809010903 78
    0x1000c01070080019580d07402402c988003090756039880203002842100740e0304020090f000109000304008070090207006001000010b030041c41440c60195000d0303804188100410a030a000e903008680907000c5070004998003010800017030b00740301d10002050700100c58201d00004803a806a1180c4150000510303144107079203010240d0020001c10183e0390b40400c00b84586031080142c030014010900b401c44010340816403455980c0b00b140310400400c0651400704003040030820030f886030032070710044400b0a5020031400074121b400c01c9a110760b50b20308003003ca400c02d080a1040180441c0e0607501c070b0b8000d80c00c0040a0711150300c0a082180e01040030480c00d82007003030114000d00914462140031625144e01f8034003c4c60200c1c815415031094003c1c80d001c03482607800847c18401c070380c41d1030140e07501c030305403e1000b0303007084801c80c1c4510a030701d41d1920810400c4403d24042d010b69220355845603600e41b00d241844400805072034003c1c640d400040100000c204007401500700c503001403406416a946a036a4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 20633603 1250 20632353 20632361
    0x109020303120103031b08030115020106050901120b010b13151e0c0311010605030613030c020d060e06010f060804151d011508010e0304060807050409021603030f15050906011101 78
    0x80c0b0340c00d215500c014410580d0041c0b04c600c040500340c1100002c66443d8846030143e00c0184118812030ba07900c0342161010703000703402c00001044014840301196944807c84500b08401b02001c032140402c000010501112110540703001803004075401c800d145c1882100c1e0b10f180f1413000b4100078070407030301c008010300c500c12201001e0810361703555400304180c0300d0324000e4030304860003110300c41c01d9043c40d805000580300003e0b00ca0744550039403d0886842d50508007926171a580c075401035017210750181c00c41e00b070040350b030041d03c100a00310b0100c1d00e03140e99598092810f06050301401c070000302c1d01c101260100d03118140340550b407900f20400280b2840305200d0b42c03c05a0800d02000c00c16510356001510b440f4041c603501000b000084004e200c1e62040a958544030b2156000d52000e1204131408200958491029603010300540081159101000306100c0394440344a003048000904200c4170200041c018002c820400289045000003141000204182400000c0c440ca041010582201d15800c2003402 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 20634853 1250 20633603 20633617
    0x130522020a031a030105060306041104021b0c0315070206040b0c04050405040b070207060207050109050d11090a021c09150c050d020a08090c030a0b0f0c09040e100c03062102030109020303 82
    0x41c0000c10950240c101000f400712460b5880c4a03902d00410481141c4011491355485a40b00c3e54941c0e0110142c0005002801440b00d02c1c1da40198080d01104c01100018944100078001c40c12104c00009810300040c00c90001c80d400001a0404001b00740042c2440c148181c212400b845094242074450b008181120300440d01961140c0410060022079a014400700c005091140301070303e04c075424034001804102142c0700307050051070402824002d10034111009203003140c0040060035203080c0382c6003010103504800d50780025184021b1400140181c0d40c801e502c3e8071341c1e03c203e25070300e1100120f141000070403000b01901c040c03102c02c001c4840032180f00d02c001c0220f0812500c5207001400c0684442c1d03d23007603408079154081d0340800a0200481c200000e206d034000302105085000c0d50312030110300c0c614040c0e0100c007a00941846007640b01c658000c25844100304080104100d14208000124286c03000340c454040483d5400d000c440085d0b11514554050301e001174000300e03800b0b0171076011030700e07561102e5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 20636103 1250 20634853 20634857
    0x40c0902070f020f0a050a030209060a05040e030304061a010e012003030c070c0801020f070b070e0d0803010e10030c0902070c0e0f0f0906070206012106050f0a0b0303130522020a 78
    0x1030600021494130340100d04c10401c0c1510101c1c0201d08200200d050035040c0d00010f417140203001c0000e0210782c6c82003900d8005d0103010b4000d000003003205039225601d0b0400c0d90120354440c28030318880450724003a6204861000140e407224603001280006444c0b2040340004110036040300d41120b42c01d003000300015802003840c0d004050383c92105003001d15050321b03da004800980d004001c01071010030b03c0420360340e890ba00700024203201e0302d4550060b14800c64504441b504242c4c5c071050b41e03091184501c051412a18038021344461681c07a0708041c8604102c83c00014400c0e151018103100b22a0f4590183c405644140070041210f0b0303c1e03210082a80078201d5044200c1c5400341c080003155060818660b4021904c00002e00240c01c1c803180113503c51405010b4100c0c2030051290f440e01980100d0425808603410900400c03039400c5c40b11018403400e104503862703103405040460010b040e0038000700700c40b08248610130044415042404020a50000c0700c056900840c5800c4c006840c4103140c801002e40c1400c6d9 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 20637353 1250 20636103 20636123
    0x31112030a060602030304050a0201050c1509010507080601031b11011d07060216061b060b06030406090b091f0b04020403020307120201020c090613050606160302010501031a0c12040c090207 83
    0x14080040c02e44a8540080302190400e000b800001140000c0b0031001c6542402d01c1911641100145840c2588070b452801c140184001446840d40c03042d4001401451207130781c0d080c050341e210350054007540c481900034000c584c1c0094649109521030001c10000c2d40142e4008107080c0d44080307180550004c9501040d030141c10100b001c200c09a010400c03181c1c4035031054090844249805c0028002e40314a42c8030415212030400d1803410080340380d11103d0f169000a05054a0381003908281000b411466002c403480c64102003c2030304039100140011005000041c4035aa0300140f4000201400b400c44c2c034181c01540034000400140c5e0140201d038050142d0300c0201c50810114000207240c82c141120850185031041d09000c00c94491030403041045240c0000822140c65075004640188030742104e901c0029001e50000c0109541900702d24100d900a07008000032508150740800d0750384058810381d80c805000c22000d9210300b803441045a200380149900f4000c50341e00c0000400342c0c0c0c01142c040b9080148 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 20638603 1250 20637353 20637361
    0x4060f0801060f1206020c07090f02130807050f0409020f0307030b0f1609050603130c08010204061205090303070c051504030f0305071403061e03030c030406120903080106080403111203 81
    0x802d01c02d410081c1102c01c102c0000600d80342c004460b000981402420b403540001e645007805404025800082c10300410400ca03610540c40000c000f034010307941d00207960440b00c00008058500150000a484008221100d0369100d401000018141e2640880e00240200903138600c41d9000e01024008600030300722402c3c04d00e400c0b0f4020052800050a52044141c00c1c0380c1401003590085880007958025244d040e5079454011812051880b000c000502040c03000d5030106082d54190050002c4400706d80301c07a14541b1590301d15800341c0c0c00403500d01da501e07441440050306041c801c1c1401000540030304240d50200084400b4500300071022101900491401d0742c04200d86d5a00d80b05050b40a40d0300e03e091185035141c29081e510398800601401c0c4200708040800c4007400d111481c6c034038910001021265540c07110b101154580d00607105d0f543c08205c2c00071a1800071105409640c2a1560640e07d54203940e00703160083c1c0d80c1490140c0300b9000c00c40180c0c03120703100032001c0201d5500c5049a500762078407460 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 20639853 1250 20638603 20638619
    0x305060307060f020606060d14100f081207020f0a0902070620030603100203071206090b04060b1306030c0507080a1107120b0604230411040b0906010804020f0f04060f 73
    0x1145501040030403121409503030405130702240140c0c000d00202c0e1440e50712303020003801030041c100d0040081c0341c000001f02841590114410444100c0350356040c190b16a0359158101901e03850400b0022000303a00c00c01840d001487c2111707811a8100c0000d01c1c0111075611188044101d8202803801c42c1d80550322580c0e02460420480381854809e41c500540303180d4503114020907143c0d48a414001a800d4021000c18800b0740683d2040ca5001040041082030903610800500036100c000c107510f01541c60400013041040100301120000120811000f081a00d480011402040590b5441013000701c140803007030003d54020f0040688a1140c0c0d145010002444045030a01006a0091162032a0440d8040c00121524161503010340c0442d00002c08022040e0b800c92450401e075184207104e0110340c2048108001140ca1406541060b01e0410110000c9030621242c1c1c2000c0d503855010560600000d801880c200303000d805000f1026158600445a40010505482c450f812800d4500554801800525 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 20641103 1250 20639853 20639863
    0x1050307050d0503090d0303110f12010603060b0703110312090a11060a0f11030705060f07020c0a030312051e070203040614071a09030408030301060908010b010e030303150a080a0303050603 83
    0x400302c1c2c0390300c800d0240b9924070399244140384c8039502800c0d51324900003e150095204440300503c408166564a0600715941481c0d070000c003aa0400c010800004146580702e440341c1d90949500000c43c900d450303a1070b10183c984074254100b080c4d5511007084500c0d030b0350440000140c010f0000f80c000701914841882e15010780504042818040c05044c81001e09183d030084000c010030985041c810b00c00541b41e0314131070541c424050003411030721800080c80501d1000d90f00c0e184c46614141d094911124261040100d010501c4c0301c080c000484200d580440f42c080d560101b90040d52907108042e05891b42e8140d5511484d04541280141e040400c08020061308580b410300c82d4400d207000c880c90722000d507a0301004403e45030300e1980401c84031800a00c00803000c1003120050710421741141e840b50b1b954107004040d54120b0040310459400c03d0380d03551455010b009034480602000300954116900d000110784020321801c2881d07071101d8402c1d40000e0000051203981a1140030755000b04403450850305051602c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 20642353 1250 20641103 20641109
    0x30a1a0601031a04090206090d11010206100f140102030c0708030306100309021309080d150f0603021305040e0102090a09060906080a050c011b0203150402100504050604030f06022101050307 83
    0x41403c005078260124800711051180c0e00d81203800040300d034400d0000c44c41c42e00640300301e80e400507150680201031203007548000c09100c00983c201e030050fa9894451261002c601e02c1040c0d6480c020b100d00303100c940940c500032140704006104990400c2501a40c0925006182c0e024240b075800001c00c3c84024201400c643c2da141c034290400b800300e0f540b150b0104801c0c05400048100c0199118242020407010104991a0b429480001e003d02c0c886885c6016003c601c0c2d2054210a04141d200092810301074000c1d036107403080480c20300480d2480c110901c00075000150283d10195402c01481001c0d60b01d802200000e004100d00010700103041120800460381103402500a99002c3e284c404001400020168410350007807030194002c02c00c03c0704061000d0b010200007945805061031291001c22803c107801d2180d0300880e12900320030f0288000362124821801181e402520030041403021451450340d6a10312071086c0c00c01842d000003000310f1000d50058402c03c001540c10400100468a000c00ce12805 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 20643603 1250 20642353 20642357
    0x714010f0c14090105040b13050405070e0d030c0516060306050306070302070507030305090117092422021503070206100815150f0301020a0c030201050901110304021509030a1a0601 79
    0x100100369001a010201000b00c0c035251440000d9008500d0b40f058069030014480d800390360b500c030f00d584202014107a840d406500d01443c0340000082c4401e204222100c0d00e08c40207072501101c43e4064408884040d00903001381c8480c812031a02d01012100390080000500c507994000a1040c102000c1605050380a0000e9003058010f1110788003180740440c1d0002200e44c54142261b503681401c1c0143c1c2ca48074030081e012220b07a000c4040054210000c10700c04107032030005038203003903520400000071a4024103440d4492031441c203081171012004407141101125000600c820300780c0c0c100c4d01c08001d1a5004031507040040e0002d2092000301483d481024001d08240400f0701610102c60104002903a401002d0140041e085130011207942c4442c5c05072a29214060000d40d07440c101c03502c3c0035103180c078810000c6005619150024a001c4010310482c00e41c01e03038101410380380d61950b408010b100340302c5544020002da420480c202035075608204043c0d202e48a40d01050b110ba4040300d000d07a018400030040c1d41 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 20644853 1250 20643603 20643611
    0x200102070e0705030c180409030e031608032d18090903180402090111010608210403050703080a020f060906010f060f021c0201110715151401050904110714010f 70
    0x5120764105040d40e174400c1d448154141c039910065620b5004405841480760024906003485c8145a403200c04d81f14440026001c680c1c05507140e10415500101d030f4891010729800c18000a03204018540b030f04907500c131400002424003541a0030100c21680290f0f01c40318240e850349800380389828055040ca80c00485d000c0910308005480d03c00d6401440039035145445580d000404140d80d0b80182c02518486241000800450740c40340d0750f007940e641400b407480800c844c49250140750200840c0844041d240e2202c046e060315840d503565500300741c0080000c1e10130340c0111100c4c41c23003400d02003140500c201826801404254504103034030380c96011a81200c001c101b0040513207220305030000761240711049000c0c0d0008030321901e84000c900602c0c5e14003c900c400440020f1080238442c50190f03030542424082020000782c464171500340c035125054441c08440326178807089011598043c402410307182074003500c0803d02c01d401440c2140d1690084404840d01000098890005002403140c040050000d180800c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 20646103 1250 20644853 20644861
    0x30906070f0801090504020a08010f0c120207020a050402070206070b130213020c062e0905061c0f060e03041a030a050f06060913021207050d0e070b07120903200102070e 74
    0x200368290502401d0703041340e1070b800401c0440d12001080300003060740d0b00081101482c0d0305112006040038001441c001341c8079200305844ea07085407003181ca602d640184151481d600d03140c1408040d40011f0801d036400041403103200c0108481c2c0a00354460b0021809200603124180304001a00c418070700c455a10a105000000c13454000150030703600151004660b80a640c4110009100c210b41c0c601c1c0c4204843c0c0010001400101d00e0704600d0041600320b03221300c0c240c500c065400c640e0300c03440da0000e448070392144842c1d00414015807090010243c0c01041d61320f000d4984544401203102c800e0720410106001080200c542240d10a09800058110160002c0d0078804001f070201c0c0104e0717500300c0c4140d41e000c82c10038139802284d0454801501c030b10703040741c014a841840a403c40d0012949202002e040202840e0004030100b00d8005030f0300c91444503400d085a0780c580d454131481c0c2004042c140003044102002048142905540b18051426201c075100480c900080c01d00e001c0b54459285016040248 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 20647353 1250 20646103 20646107
    0x8010b120103030806040905160e0903030f010b0309160f06030e0c0a1a1204080901110d05040614120a020d140105030604030f0c0b1e01051009090203070c0611030906070f 75
    0x41e04407501403900c08650b85400c0001001000030b038500170001d00c5070344030f21038642140c001c00c901104e400c80c800300b40381d80da050380850b20b2748012110002d030b511f5036900500c503483d90403002c1e40e0400a10341c200c4100d40050704031a2030b000310310341010300faa01040c50104402980350080305a1706040340050031184c03404c4c03004540d501d05540520558060710511155404000c48141d44020144c01c00314202c41c14141000c415030fa000b480d5150001d1038250244000610000d501c081c43c00d040e50700eaa26181c5000e4081340c1c2c80d4820402d034103044408025058012032502c40060080048500050784d035510800b40304125054800315549440303450004010650b400b05141d0351140d0541050102c8a4a0300800ca41c1c0b681da400c0003c0440f1400410310401102d02031884da881740380c0d4080702c50541d1301c8804001e0401d07040c2010000003800008d0602100c00c5c607801854002906044c0102014002d640312002c1e10300301942515007186c04020440e400c0d004101580c1c201c0c40500f000110b0761510100 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 20648603 1250 20647353 20647387
    0x20d061a180919020d0c110d020606100c061515020705150705010b030a050a030906030501050603070c050712050a021302030c0403080a0c14060a06060509010507140a0212030a08010b 80
    0x1c180c1c4500b165100141115400340d1000a9040194800315614803141c6295001407080740c034600c00203009030818a400d403800050072095a00207800034074841d903c0000304940c06c80d8030381c003002c00c1003c009442c20004241c1e00410baa00b00104006400d09410201c8846a0b581104007900842d80310000400460b00d940c12180049111400300b02c0c0d442111b800c040d0702501101c058140c040c402c912540d4148000441e90075842c9229547d8403190995504045050390300030301516a2106041010078500c602071200d20b000c082c403904c117039451300d80d982021015000504405a50503000003103540110301c0e05400300c145da140c26240c00c5085040150b28964240030b903000003880100700113400c1203850700401a40c5202640b15a0012a90300d001c00307802c1d10f8680036203080c0031850800c10301007a02c5016000b44c803807148040c0d4a150800c07005849440f12049a0f111003100c9014a9501d02e01603190082c5551240205c40b00030f540c2e03551103113802000001d050384004640d040c18071810683c0490151 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 20649853 1250 20648603 20648647
    0x70e0103050402040204031205070b06150a08090a06050705040512060f060d08040f0303030b030c0a05030c060d091e05070f03030203090d05030d0609050108010f020708070201080c0d020d061a 84
    0x3030005038940d10303440840c000f4401c940000c2c01070180e80d90211401c40e4408028940039102e4000e80d1015200d0070248020f05010000c400a07104042c000e601a41e48034905440e480311152702103c00313003002d41d1980c00c1245c00c1922100002840007400f404181000e6150700400072a140c018185e519000403039145c2881c018245600c60001417448406016410341031703401038070340010300d106501d95030302c1c001d002081a0600c090181c0510914004146081046030b400c4840140180c42d00d072811104001d103a0b800080ca06050075035801e0010301298080e1035003e201003d172080d000c480c0340b05051642c5001c615510420b00b000030304005000195010050b948448415104401d0040c8540b4049045008103602100ca542c0f03801400100c1c0d12058001d00c2c122450540208400c4031800030050691185107006002c40d81704200caa801948500b80701390b809000c1924150a01c02900b440d8400c1ea8404080c44041c2074550350b045c040b44c40d1801091002410310101c080c03601020403912044031000c03036 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 20651103 1250 20649853 20649857
    0x307051008070507080307030c090e04020d0222050103060b01020601081f020a030219020106030201030606030b060301050d0303060812030105040b0a08210405030a03080405060105010e090c07080702060304050a0201080a0203070e01 101
    0x180c0841c00c1640100c054800715644451176a07242d2a10b03060040040c4241c5030f40600182c40340c040006c150080d003044a01443d005054001303040341940070b02144501d45001c10403080c0e0000d00400304c4a400d8800c1c10301851003940b010403101424000240b61030410b802c4088036401029040c1d8803003005651044d41d11702124030142e152071960f40c054009020301c0400c1012003152a000740f08003503040d4081c4003524400d882c01c1000c15200c010482c21104144200758000307808200500040c50f048103283c40492203860081242c035202c090017403d000100500d0380b05d50001000512561805000e01c4035022000c3c0c1c1c852140520b48034526940350454540780c500d110383e100500d00340f104c82c103049401038040603040b0350710b20600307203070051150504440c192150300401c4000304e00b41d8455102805280340007446142951609003030004594003442c422034213903c04001d03050050322031402861041d0300a0740508040300c940d0001402d17070040140744089280c4100304010100d038000701580c524060038 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 20652353 1250 20651103 20651117
    0x10020a030e0109030204060b03101a0f0c0c030d11010c080609060d020a0503030307020a0501060906030309060503130614010302180402030616050c0a0501020405130e06010501050703120c080a0b03070510 89
    0x1890060310100c81d2500017070b401a09100d000310b5048007510041d401040c1095850900d1941d0351404101c0c9441080d0b8805000300030402c0ca4108402807001c2c00882a1000544100b0f0450300002460142e19049100104503011084042080c01b0301c258500b02240d410203680b0340ca05400000d5070078a00a0120b44282c0c0c0340d070700721400e54481000d184080d040103002c403556400c18060107990b4020f6040115410b41c01c2c041d0101e8040c903d4000d2408813941519010a074a05014080e1420b401c0100301c0c3d02c40002c06903040e000b00c2c070706009080344415150481c29a070350450050000d2440c42c0324038201c45902c40828000141ca000400943c00045000700960005544404a0f03032882510b5203600e071486552810014410190300134421039400320380300b440030b1120140c58400d40d8104c001c0050f4941141c001042654082c0d00103000840c880e01e413501e1280d0307144840d08102c461041000c80007a10400411142c0d2606101d5a006048100c005202c4d25203424009a051103d10010f10704108030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 20653603 1250 20652353 20652377
    0x2090103021e030607020102090a050a0b04030303020c030f0d0b130213140a0503011104060305091c0311160309030506061905120102070b01090e0706090b1206060c010c021b10020a03 80
    0x20742e129014040c005007070300d400d410001c000901035040742c4d00311441096030800009040c0351500804003202c80d11904541081d01d59181078009410170300610015000405c001d2900d051800001d01f07a541c0b0101000505180503400d0003d68032070f400c450100d1781c0c410000100149240c038801c504640e0340c1200c0c0003d20600801250020a0b00d0b4400c64166007481d0070700000700048000b40042d02e040356010040355986005a1f990342000d070f10542150480c80350282941ca1282e0003a10820001c00705030341c40c0c00785089403d516000705101c01d44c00284158001e00800c10107002c80341e00818100d41800d401c7c01d4a038082c681c400024403401e441074404581c2d5443d0b4040a4040e50b00d0540c1001420149613500c0808001a254149150b03036640140301d00412201d018012040503207940700700c0c550400029460342002c14070042c100590040047c00080388a2070240140044034800e94050b003040c0d48a00015400c14806a9280c2d11480200e400403084907400903081c8101c0390075281040c01004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 20654853 1250 20653603 20653639
    0x7020a060e1609051617070806150d0e01050705130612060504021b0c01021204090902010c05060a0e120f070f0602090303030103060209090601020105070e0105070606080304300209010302 82
    0x200d4480d07101c0300c40740400340091422882c1e8002441000d101681c4421030030480c000311010550b8103048400b074002e00007c20030051003642d80f241c0c44207004d03000161115a408503209560403030300c1d0600c0d86c0c54503070b1901c4045010070b0213a00d821000504110f42081e030ba2824020700c0007101c2c000d02c401c100079131000b8060074425810080003400054030442d03640785002c25007111751a6040c044040b40c8598401c2d05800c0d4400141c562003860601c41860a044c00d000c2c04101408000009038100690f54004002250742840000d0180c0745122000034a91056500d490070f0512000302c400d03807483d041c4610407494945c4002c490300c0341d50042c45900c95003020728280000f8040c1050094051202000110421255500601280104407042c2401d642d030b50f00124240ca0b0219000c074005108480351107100c0d4010070240040901c0b40f2000b1034080c4d01c0d012050314542055000714020a6025150b01002c10080c100f0305900640e003000390005040e0750082100703a941888024000c290301d01c04610018 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 20656103 1250 20654853 20654863
    0x3060601021f0212010303051e03010b0d05061807020c1c050601060f0908010603050a021c02030c1c02060c1b010203130e040f0209070c0209060409151a0d050703150507020a060e 78
    0x260007941036413204c1d43c51b800d000302107400804400001b800f0318546480e00400070004e81b81204d4503058000c0c0b6003400100424041c2101401ea50707080b2480c481c00c0944250407043c818480c4600da4000c0c018600308604100e0f50142598815115424519040300441c0303012481c24190740090400c0c41c07a5084a02c02120082426031001d440740d4603021003c010402c0224a60340c0b058001c84081030030b01c00c2c040b0503250700340d40c0314002580355010034032401c401e041a800d8029064242d1041c0c0d0140c0506401154955004141444090300581e40388400403c2c0b00440000c01e0100384025401c0520064260700c0115940c0110100003084174009003c0010244d41044140d902800640c032a041404010f460f840c4606000c81c4111b9180002407030794200740c46002880c0b0b4011028005028806204000802408400034040c5c101440f401040762a16400500c0c030038495801009441e00d5404c084405641c401084090203013440c007400b40840e40056010341c403076004500082d080c02c080180c0c074079003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 20657353 1250 20656103 20656117
    0x70206030912030106020607020606120c04090203010b041107050708010507120905120415020c01180b03040f0c0f1404021303030810030606080a060b0a08031c020c06131103060601021f02 82
    0x4401c000004900a54040f0307c01c1e0007a90350b902143c2c010f45810b002c018025503070f819544620343c044039801110b8607240e045000c0d61400500009407801d00d50004c60107480080100c07840c1800002020010406c00700513103c01044480001c010504003a50010006210b01304030129160b1112a4041402418400a0080d08a020b52103076115034408010802c0c0300042c00c0b510150040c0c12a0044039400b606010318402030806074448802d08104140ea05608081c000307803150140d80e0b56420004c1c800800281c058036000c071840807950b1030b1074045007442004c0c8025a0065005010340b446641e031408496084e2a40f509104101e50703142d44100c5202c441903480540b889007040000114078502140e0309401a010305020300080c2c280c5410701261f09242d10664010303a0042100c1d004060a0144032507000e4400d00c40549041e030a00901d61030440d090711040810460320401500308042ca080300802440154007400c03942c82d0400010391941d60b15100030155151f10761b0403905d500e142c3d80c112181d07 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 20658603 1250 20657353 20657383
    0x311010906050601080f040b0711120d060f0f0302030601050103050603010905010f1b0512070513081b011707090605030a0b120d090b0c0d0c030309020402070317010603090201050702060309 83
    0x100e40141c2408000b506094924502045000b00420f003100201c00c110740c411508600c0030455074840c40421101e480148240b00c2d19401551901050b50032540024200000000703804200c0600388029101080d48541c40009007864440e02080181c84c0820241d0446600b4200000c1c647c0e561000700e03000d001d824500414a5113411140c400103045070307000b200e09810020700d005000c2c81d080c405551600c80c010b04101040250000620800d00c2038000f001038510115082c52001d40c2ea5090f1446c02da2000281aa601000c410101d0b0740d5922290404840324015403480c1641040c3c8400381001c080b80c0a017000300000000003485224554012010010380981400048120a04001d448072a80802a00010544400003a13850780701c1e010b546101141c0c5010f00480d048900701514102030408080381815105c41940c4d0144c1c2d1548040e111890103615881407024490030b5203100c50205800071000d03d440d00d020440540d901c403050300c0320598162a003d540f901c0d14162249001c1c0c0d01c80596807 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 20659853 1250 20658603 20658611
    0x1b080d060902130807050409020105030a09032304080105070507020f090421030204090e07030308010e060117010e07090b0a0c0821070507030201060f05060a030c030f150609080303071407031101 85
    0x3c01d0128050343d0030442d000407013943c8030035407039a040100707a8132422070290000e242072000c00d00d000b6003640280a918480c1c00e107507440ea50038506103100d0b244100780d15050010046010088040300f80102603110040e0305d8118039000c00e96002541d4005c4c00d0303025034061081200010200716010404090000001c904800315400c06d42005029501074046d61044504000e240089818000380200689606032103041203603081c601d03441d0081200511140c1009100440f1280a6000d4034501e800b8000d064902d65280c982410042d0803440b5070740c08816080c000b04032051034154402c54250b1025400080c855540800c054803007000284101d0440002d8820003e001c07a281d000b800a150a91181d00280f224503a01d0f4600d0441c1d000a00c1140d412050400440c40d01034406e5104040c000302a08000511080c4508404204c510704000300703065a0000b5000e11a02d6004000d081c024031688000394914a030040000300780840e4224049551407010414600b050b002c1c0c1c8000101e0104800204 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 20661103 1250 20659853 20659867
    0xf0618020406091a040902030a0201050c031908010509060d11060702010215070302040513020304080406140d0905250b0f070201020a150504060e0307030206040813180218011b080d060902 82
    0x20003240755000c1c00125045513420003030410703016a8014680040140404034800c2d0015900740e40030f030f80981841d000422640707600004440400c69500050b5403802501c1d03040c003084c02011580581400c0c4100207116503000000c512040c020b400800599507603440c0e8080d071005034504850320341c540111040d19000c20a43c1549680548211002241e0364800c026111103440d04a102c1550301422684041105110341c40c0188801c001c3c404681c60820726000304003020a0407038040c1182150307190003203d14030a083c5011460101f800d441004400301c494600480c0c40164070905401401a0001081c0701c1c0c00d5a000f8401d50b130886801001c41881c9483da0000d240083c082103034201c60f16454040304014580002050310b5450b40c2c9600100140d0f25117403609403c68001013207190194481213004a00200401c00c19680c10744954005621242c5003119501e07061070004047d410843c2c6c080c9890031003042414002607a5800603100c9a039041803461700300161209070008a40c0500002d054 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 20662353 1250 20661103 20661119
    0xf060c03090c010903050d031d06130201030f060e01050f03070b0301090c0210060303120914120c0601170616021005091e0d0909020c03160b01060f08040f0618020406 73
    0x45200301e4001e010b9804040c4048019240f1001ca80000f80041c0d00100c080000c60b8001d0384405003500b9247d420124241001c0d14141c58614100c1e00d10700b50648444002d01196058000c2140032030041c88144182810304030009000c03501441074038440c1c10380c049031421544051100201400301210341c0303560b035030b119408540600b8064103404014412042807500000c1d483c490300b0107982d81551541e610018040300c00c806882920f2047e00c0e000b01403002c0e000385500400043d264030581200441e01c0d12555600c840c10503205034065055448814000380f5a01800b04426500210071490f480800c02420812031804e02a030b80b80c0c1d240540b410060285040d000580600220ba640e4458030144c00c1510005440d20001c500100104140305070520100300940c02506501c1e6494044030b09141d040410642103844107030041d1030095075000184001944603d807204079001e1401e00c03814030304080c0c0d02c2c1d03580c0e040403400103020295114003c0e80b00100c0c00080440241c0c0003441030080c185c540f180 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 20663603 1250 20662353 20662357
    0xf0d0905060103050c06071106030901110a021506040603030912081608030103050d140a11030f040f050a090e0303161704030f120506031903090f0e06010f08041101030e0f060c 77
    0x180c46500c00c1c40b170b19181500d081c1c1e04071030300070764080c0c801202e0043e0b0009120180d00080c01113413003075480b01c3c44d0080740200d0801401008609500810745581102050010a14050090345c010760801c0020b02c00b103500070030201d04031207030060750211079040c9082a40443c003031004604845004e400c920b5045c440c070710740558103990240e03082e81c500c00325039007095408115003140c000c03011100b40201190301b4044c0ca5185804c2203202c00b941d02c2c00c4182c1841d90041d40c4075400205446c44a00000e1115013081d0340b03000f0241030300032002c0000081c0c480d02103969010090080b000c4020106000300114451800499141c1c2c5140095085003018036018043c03594903171701040000d0300c0007220303040c0801c139004450260764007034068041c100b0440c61014034080122801c1d8240001000300203005c44000c50600000d00325450341101c9400c107a400104444080444e02003040a0301c000d002c007054090310b91403040300b03090030001403409038038010b82c0c1415098250440140100d0301004000c40748500 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 20664853 1250 20663603 20663609
    0x3040309030f050106090b01020f061605130b04030614071d040612060c02010b010e0904140c10093204092904050c01050415210c02010c0201050708010b09060f0d09050601 75
    0x200500102c0c0c1f044004a9803068400070020a60b8040d10114401c00c00711076240038019200d213403061810005018a030703400041d50b400100c99443c0014108144aa00d11809440c1002c5042d5880f842c1801c1500402011020ba480d181499065103400903554440c1c2c4000010503d001c0403011380820381c10011700030b11400e0b040030055428002d18040340c0d8403c111100000c04024590300d4142c40f00e48541078030400620341c0c508144144984501e056861640d40345245c0702ca945c2e060942d509041c0d6060300f900012030401180c55104c00003085481d403042000c400c1d08010b44c1c0015602401c0c2c00e151018400c1204078050140700d51100c12103440c0b01080c000d2159000348121a450302c20f40004640c184a20f02c202c856004600410801c82480b0f050750080031008a03c00b403043c20f20307080000049548019100c00540c0d91000003e02054084c0103240d4081e45da8280040709601d061038080b260b00c540c1030390340c0c4201d0001903400c42032100340342900c5003000211001c0206507603d00e801613807030320f084c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 20666103 1250 20664853 20664869
    0x40504030210110f0d0908040503011b1404050609060d060e01230303040e160e06040e04060506040504210201021e0309060108030c0307110607050105090d0e0307051503040309030f050106 82
    0x108a6a443c0c240b404115495401c001c00740601e8494032880050080100400c12101d49030100b00005966409008444443c150204007601c0700c220210084c020602503444003805030030a0000300103d9035102e0030b0b00c0c880b103402d8817a40d40d9228001008401071240740c00903042c9890010000c2004144e128407110f245a48017540c1725580d00392000c0554070702492140c212640c40c1c81000680791000d00e0141c03102c40c0400d05100206004e120700044142e00103030408aa0060044108000d10980c0e01609070402c0007540c1c200190700303140d02c1c2d40c4111203110407118071240500e62a040e44034400d50480780c101e0010704003001d5040c04504800103c1d4001c1e01c40b42418468040003042501003c8100e9100e080c041c0011454004540c3e40d07588101d41ea000c07069403001003400f0940104400303009541c822180e26016005c0d407061181c0140c8075a0b04080c00d240280d102d40b10034025a100c5040f2100d4400704003240715200d540d549011a110381c1e031608001e1400424800d580208181500000e003a03500b00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 20667353 1250 20666103 20666111
    0x70512040602151003060216060203070512070f140309030408010612020901051e0d020612040c081b010801090f09020d03030203010503062203110c0604030b040b09030a0203040e06040209040504030210 88
    0x2c0d9105000c61040d80c14078903001c13080030100005400c6900604420711062410480c11082d519180100d030011130b20100030502c00104071911b11250080d960348039519040c9448021503604008000c020b094041e60030580000012400b60b0780b0070400e5500074104540280007030354440244219126000c40e040f8060200c100004c180b030f01d0820940d2405050380d001c40000540c015041101020003202d0690b0001810450104200b0b0f0811364103100e98003510000c00418075001d401882d04100034264901c071003039501128101c0e070780030b58030a045421276007000c00c8140807103c0c1c0c04010401741380b00943c000070b90080d050400d60903802030b604990b001c5080e92015518011100b41c000840d41140ea5440c0c0009419000240158600d507032103a50703001225084001035001c2810b5500640081e245136030301400704010000c05005059102102c240654140744071107070060354034000c81c098007800741070b000005a040d440740d5055810410008105001600b00f40c14040d403210341400380310f0580d90030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 20668603 1250 20667353 20667373
    0xd0507020415080307060b01030902060d0b100f020a061a03030307090905060102070605040902030a0b04050c1b030c0601121a0f25050901050901090f03030e120a0308040b040206070512040602 84
    0x742c0c1c44101128502c00180d072030404d60383e594000034280798250703605140d0340301e68000242e11440d0240040c0205110000755200c04030040121004500915900f044108981800300070f074089101c0c1001c030f0740428041074068a41c07007414841240402015010310010007000121540301c90886c0c11252110070410150719803c004907221078250103420003180d81000100100c01080d8000e543c4200800c500160f1207030a04001015038809a94500e62502d004c84d01080c0f02040350022012304060308010361070700071003d02c01610b68405210f6225070340d0303403610480c00303201a042c00411011550207040e8468035024031640c6d0700c0c0c0000d0b181c180051809c0e420104041c0010815014488540d49429042c40040c000440e8030b54002d4042c9810410343d10303400200f00300c41d0803c3c400514403d48030403806000400912240c00703480c2d20092250740c00118503102283d00041210f41042d0401d038019190783d01c5002040e1349209030500113050b8440c0340708680010611401410503074071654242c80442071 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 20669853 1250 20668603 20668631
    0x7020109090504050601030f08131701060504050f180a0602070813080f0604060c090b07060b0103050606070b010303050906090603070306030b010609062106030b0901020409050604060b03060d03030b030d05070204 93
    0x900f128018000e9000f5401800800d9210742440701d00362003212428a04017039103902000d80d030050b9003d24115401d8141d851040d100a010740e8010782416102000030f0326099849049141001e058a8110382d104001c03410400000e00490410329003005081d980d409491030025401d91260382809d4a4a0344013701003446000464051140344d400300c010400d948940d1255401405625030304801d104800400103000781500000e0000240507040001d0a185402700160603580c0061029210b02d8080003900002102c00d0483c40c15650945022501da6803000c012404501c541c54102d540004040b003040713225581a0050410380740300340d0b000007c603640c2d50015a645c420500484000c0341c0300c00c403a81124500c6201c1c00003e81e4454030045485560383d15284402e282c261243c00c8141d40004040c4015a01c82c021a81c0040080d03038200011854018a00b00c0c0b800080c100511170410b45080f04207161094004001c6818010140d91720040d00e07001c05400b079401564101d02a900700001110428 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 20671103 1250 20669853 20669861
    0x1090303080414070f030c08010f0b060706111b0309010306090e03070b1b0703050c07060906090902031503060a020c011802090c070305040305060726010614210406020702010909 78
    0x103641500c40700490b4807240c2d03030040900d04000700d00125202d0540d00080d6000100e000000440c09901c1d5868800d040030341175820b441e6100e2940c00c0e014240f15500f5440e80701c8008a840700b039048100020f0500d0106c1c101c00e0300348960b084414240104078040403003480048020007824400740c07010003034940e680d0102ca00b52103880d00f0304042508217010282c042070340c0c090340a0f80080b004040c074039076800e1480080000d800c8030300180c0c00150040342c1200208020001d00c409890603042190a45140c00001040006103000c1d500c400c0f9004004600c0d80621001d5407003503000010252003d610b80250400020b40040004088540c02c0100118007100801e120070301c41a006040c000031a0b031880c1c178104a550002c1012800c2140802c00000800c07010701c1102e006072041c2da104510030803110034000f0403544645a812003207030700000412103c0e03000700403400a403106090a580b542c9054030780c21403038030406181548a002c03101c100410000319500400c0703054401d0f00d80e42c0702640c54407040d00403a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 20672353 1250 20671103 20671109
    0xa0b01020114190b0609040c0302300414011506020c1005090303040603050402031c03150501111f0609020304051e060106090b03180d080a0f0c0905060901030e0304060c020406050109 80
    0x44000c2c0c0c1448030162490b03800480010501500b8141340800711b202240c12150410030140019501080b5192502100c00d0b0185494103401c242e000072800c41d00c0c1034102d150020300f004214050250012429001c02c0d045010362403490440860025500c04c0701a45548047d03108500c00c1001081100c00e540c0194159282541c019005600302814268150024417000e8001d83c0c3c9840740b0741c3c484800440681d1702c43c11048103581c001c22115080c1c2a40c2c50003e800340c000e141030000400c00344200030310002d00d243c9240c00d0305a2041c81c145185020328010329503600288401400041000240000001c00303140d4000da502580c802c0072005190b280e00d812080c06880b0010380340e01020042a61481d01850f00311200c10040a00040c1c07c201003072425111b01c04107008140c00204005070440140b207451408651003005016941007050001c0541340d40d400b501d44156008104c5407071f164403d5005074010910340301160341c1c2e15111749000e00302040010049100c0c90410748049100d51150040c1412 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 20673603 1250 20672353 20672371
    0x207060207030f0f08040b090411090303090907090f030605090c010504030203060c0307030f0c1d01020c010e06030901060b03010807031202120a20010501060c0c08160501120f050a0b01020114 84
    0x6041e0459441446400d0310283c15503004140130104c0020401c210010f000410300b040d4166603400041003888240e40500300d009401520900c4000c0142d00d010045a02c0702c00c7c116040709c0306580d0780d0400c0d140d013001030700210000e290701d074000710800585030b001c43e00960a11007114461180a801105c42d4825404002c1d0035800c03210104000c405140080d6400c00003a090200f400055200703c0800c60301400a0b09000881d01c280900d6200b00200b224484040c00384050192085450b00180002c01c0c0d4606040c05198004005141581e0a500500180854942c50703a07407540d4442074540e5600303840c002030352101d60602c103140031030380001003414013005078013855400c01d41010302c20b9508500703280703801e1a1111a5085000442028410f050182c8060b8a464001458900300b609070b8500a030030141450f804900d5000701e0107821482070003140c00c00d280c0100c07504101a044409009040174281d8880d042c0001c3c054804c031b072074202e001400001c0c0d008102d0f42c0c0700f0a8000307004038815560118 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 20674853 1250 20673603 20673613
    0x305011a0a050a030f02070609020f04050405070b09060903010e060402010210090b0105060c0c090901020a11030705030f0306060c0a21030c0807050a020106081207050606120303070e220c030c02070602 88
    0x5180b40910081d281c0703030005090004079500d80900001c240d0740204030482c0d02d81d580f0065a000c6140000000500600507102004540381c42c0d92043d548141c2c900401582d5640460b09a00366604c1c507040341d540350b01c090001d220318400071201e00d549a4003514128094090000d444a00300024030802090540000b40c1e4081a40307410103001c030551019100010038044ea1020100325280c0304c0f019401003410100040e40c820800da00140031100d45044501d054004019603804554004140c940381208400d040381e603510b54100207a43d0703214150031919a030042101140070300010b140125051249181ccc055040311000104030100c4501c2c00f1052301050060020405040c0310740007805486056000015a4989520b0001c0c038041c4c3d1202c08059203c0000340010800009000340c0c3e030050420746114084160744100d10b500e03404002d1544c002c024a800f1040c16607a60820540d11940216010304026440e68500c0302c050700344849020003003404c1c01b01d000426880081e8a00c101e40566010701 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 20676103 1250 20674853 20674867
    0xc03010608040809060307110706020309030334080405090705090306040f05070b0c0a020f010201020702010c060e03070c09050a151206050c0c0102030c0a020d0203040f030b04050f0105090703030305011a 89
    0x107503405902a205072114603080c05003600c00d480b410000c6018840b99102c1e51903403c0a090000c0c40c0420641101046400900840c0c5258400009542d0700305005e1180b0b034480381000e14002c4030348180018000492458003400c10030b001c040c1d4018000d40d08203036212401991020b40680e0035100d140542501a800100040c01182d240100d1b102090301c01d100303a038001c0d82d454056014a81011144010380d4009200c00411403034804400301d00000e00780002e504001007600082d0800d00c8008000d002030391941211030480f0014000c840000e50b00c0000d0385c450948030a19000102001c441a10b0004d14001c0c040782d50303040300407000045820460f03000c40c12100301c1d80c940004c0c1c01c020309030300e042500521200c604c0742800c1c00954842c400381403480f80c8800e4003000081c6850100310281c0c0540d081000144042d00074004d81c5020344c2d8008440c485a6180ca240c094604040c0360303840c159035440c1c00c0500951140101e241801c99001c0d683c20702c0aa62103008a86000d2018290340000031001c010071 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 20677353 1250 20676103 20676107
    0xc0702060307020109080406030c110609070501080702010b040c030507110a0209150d020901030813090525020a06050c030108010b030f030703030507020f101e0203101a0f04080106060e01080c030106 87
    0x5680c490424400455034517090f5403500f17600d0300160001404a600c0c3c4640004060788060b0808114144400810031401c05401c040c3e01da11040c0905810002031100007070f074160003500041107282c17015100708594405204c009000303001c19240138000481d003000021604100248442860341c00810701031007a2a034000c4265041d01c210252600b055a058449001d40c2c0c4001c0c15500a6004d11461540c4100815070200400b145410a5a01c54070740700520080b602400032070085a0140d00314001070744107504041c0d2602c000203400618080c00e14013040500060354024504803902d0714020b100a0414408054a480c00810361400c3c03076005010500100348a0740003140c210783e413801a141c1101c2d800c5216800c3c84d480b00e002c5981d298403050305118011407070040503c02203c40104605606141c1003041c80f6600342c1c41100c0c6403401c001c92050001d00b4210840d00949145200d85d5603d07691458824041c0880e4401c00c00070895860044142e9402414114820040d07070300e01c03918580c00c003902 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 20678603 1250 20677353 20677357
    0x2130803090f130b040609091e0308010303080a0e01020c0d030608210304020a050d03080402030c100f0309110604081612020904080c010603080c03090307050a12030e060903030f03041502030c070206 87
    0xf100540329220707160100340d500c41d03100d01805081c41e03800c0807c160319182482800c0a0032030a07110b140303c0c2002440c40100343d214141a040d81d41c07510700b00c040303902c82c002c425024004245804120754800140240000d000040c40300c1c840782652014859190b40b480740c551204451084400c2c2100c14108050b50000345400560384240300070300070005551564040703075205607450030880100d5807000a001c203500d0200710074802d800c01203c940a8222866900800c180206007441081c9500c640d245010050482c000c3e0b01c071500040e06041e281d580d43d181080d541c00700c01c260086031003440000840d1b00e0840c05034a000450700a00100c0c07164a4585c0c81800d95800b50750f100c102956105004000142050000c0c64005c2d0400001d60310b0309082410182000d000d07502084c03040d68440002c01003005180c04803025550542480c2002c803814602291061058006c080e03414080014a0700815848901a41c081c3c1d015161581120700c01c0e400001c102d100941e47d0001080e01404200d00601c0d102c40 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 20679853 1250 20678603 20678629
    0x504020109290c0a05030a0504061404140d05010e0d020a060510050a051207050402070c08010c02010b10030b030c0303030a050108060a090807080304030507060f0e010b0d080702040b012102130803090f 88
    0x300701e03184c0e41d00700e80b80ca6065400c070342195000034000003010000585c1c0104401c045000c070700d288a140518000701040b030041c0c801d1040340100c0e034140e169000d02c90298130030607403c104801601d0300c0300c0e400200291200d20000e401c0f10514901008580092580f2044009a9030046c1c411944c0324200020400c00d11100590103101d48105800411302d6151400a4881c10344901c80f20604182025140360941c1c800503049011a803614a01100b145e542c1014000d0006d480d040000e0420380c0080880e0600840c0d0b204150184400403d000e001201c1e54402e42c101c441e40001c0c0c2d04c02c0e49503500c99109441580c000540100400d03c070882c013081400b001550410700c0780c20031900e4080381d0390f0744c001036603440d1940ca600c03583c0d642c0c4aa5085803003030180344900c0c90100d0f0000c0a0340e00a40e11001940a00c410181c082e035034508030300e50b280c2d001c0d805101e141d20640c602034003d0354811140c1c3e40a5407100c4d40c013120f003080484000a0012002003541c0d00e210b4010300d129588800303401403200c0405076034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 20681103 1250 20679853 20679877
    0x10302060f0c070e04020406060807020a06020c01110c060a0c140702090717070201090506010801230601110a0b06040b01090501021f06051002030408011503150207050a0206030a050402010929 84
    0x425081c80412543c8020b00042c40c0300d9030103150500420044450036031140c2e060118000800c500241e011420008460b8020030050700c40512401d11030041481d83c0e50300c0d0003408000ba0640fa000d0000450b03607c20004c1c107209004014180004840040e4421307580007003403005112040c01071402101c0151310400d02d00c1c08240780e50300030410340034454050b2400001350355905614414000c2c1442680c1c00f4043c4040280b06591440d8060000c452070f08015200040d05200421180e81c4a42d01e0512010103500c1298070000040c2000c0c031501c00d059594a2007a80740c4100c960895003c1c6c814042120416001f8020901614150300740d01c00c00c034442510a280d690b240840c059031400c890002c90000c540c001d644039403c00c00903a084440c0e1401c903a0041111140400025032200500c1c1a01003a1403405030f181d003d5441c00d1445c1c280a040000d43c03100c008410020030414a82c061442103000740c3e03456034050b03624032131b801c40640381000d41300d42510104c48400002000e000140b24404800d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 20682353 1250 20681103 20681107
    0x11040303110313120605070203180607080904061806080c0d1202010603140106180504121b020405130203060a15060e0d0206030703060515040f090c05071a0105030d0201050f010302060f 81
    0x7442c60010000f403c0d00f2a00026040740c59203401c0c400f585c070555a001245000542c5000410f019600c1303030202000c0003500c41c1c200002c0610412902d04141c8030b890038041c0040c049551121417494005200c03a5246418524164000035030a000103500c0e000c0c0b42c40580000c038103416903266403184110761850002036640f502c10010008601c2d0381207413202284500005041c1d8140107159980000c0800484025402c05003400007140300720200d100340c0310083c1052005000c1c1c01111803020814518080d50043c40e0204012802c441002c0040e41144200c059817456076800020b1400c42c0e00e8010300d450b030b00000c4103050001c540229071210008400900c00e50160a2980c001005607004880d4200041d4032000c3c200705904220070f41d01c81c2000c8201040d800d0904046001c401d440341c510a0003080707521400320042e01c0c2c0c0181c040720149034001010700103040c0717100d4520700300060030301c42c8500a22503070b14001c04483c4184079543c05000030f03544907a0540d1031a000c0001e960040d13080b80701c440800b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 20683459 1106 20682353 20682367
    0xb010e07091205060c0c10060609150507030806040f0905060a0606021e030d0506010905030a050c01090b040b16050c03030301030c1503090812070908030f03061201110403031103 78
    0x10058180b51189846400035140010031609021f00502d02031001c2005948003070307201c0580701d020f00c03481941814018121414810040c001d8009500300d8040b9aa510701600914581c0442d0100815000416103442d0b040040545c0d4655a4607500c0304204041d54040c00040c500303021a8102024101d84021815182e12a8440ca04003a554840005855030302640c26007024050140469420005516003a503070340f41080e10403408203107842e500007200540340d011a0185c640032414203050003046410040341004140c0219114000d041e07408903140c07410030285000718007508540011a00d801044000400c4501190f001c050520005c0b5001c1030380704080740d17055200400340032055035404404852007440b940085d1164000054808030f1034226101071400790108840b44555800750342c1d00b181c221010140050400c81c03091004002003409004600c80300000e10381034900d8100 = true := by decide +kernel

theorem cover : BRFrame.Cov 20503603 20683459 := by
  have h0 := BRFrame.cov_init 20503603
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20503603 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 20503603 ≤ n) (h2 : n < 20683459) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
