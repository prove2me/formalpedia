-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3794
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:41:28.427201+00:00
-- url     : https://prove2.me/submissions/d3160103-f449-4b87-b24d-ad9c345508db

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 682194244 ≤ n < 682374100 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 682195494 1250 682194244 682194257
    0xc070210020f06060603100510080f060d0503070b09070e070c03020c010e0607020f0402091503091213030305220e0a050f01050d0803150d0308040b16050301051e03100c 74
    0x2000c0c0c500000c0d5a1100158040181c00c0e43e50b601030620200ba08020604c400c100300c50040020142c0350003009840468490f44d4445891070807004800707070181c0c09088640510440703281c41002c01d0000c02900c8070194013008480702502c6903010315240c41020b401c0702c890800c040e018469095048009407850750710035001e41d6101072040d001500c034050114a06904441e042210030018500000b0107140726400070700050134414030303c0208041c00124100616190800801d00052407820004110341300d080201d51441d01b021a00d40040400c00c5100003414440d011601e500d00481c0720000f0b0303001d441e0101342d000c1e04c142c0d900054000040c05644080c00303949000041110300d4042030701c8a0584202620030074003000c042d5290502070740000c0991801c0f00240a15601982c0c605000021040c065929503a55080ca03007000880210050070210501d4006400301c200607400005483c11220201c44001e100417001c0400f4400401c041c01080d41801400e01042000c1c6041c1d00c1014034014076500c0c003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 682196744 1250 682195494 682195519
    0xf0d09061d01091503110a090305011808070f14100507080a0606090b0a0e1f020f0a0b070305130c06030608070518060d151e0509030a0c02091e0c0702 66
    0x1081d401002030120760000d054002d0603c0404844404596481d20070b1900040d07052803098070b500700343c001c04482c5000409031441001405004d01484119042510b160b03903c0580c1e130764070303d00144580800200000079522542003408413003291110102c40c010240c4091102141d451002000211030b0000400c50010104911040d1441140285d07680364540b282d000d810080001c46541004500004102c5c0d0b080601c08285c490000c100e0103800002d084801c10703040484080d09164041c0e40300d03840c40d440501c3c18004500080200e03900915242400a042e846a111420000940100240c6500f0382c46400064184d81940040102d07110700d000e8681c0746480b0010843e0800d17800d4006031050b200180400c09510f400060200d5a030300c28084824407480324140ca00a68502c5185000035034804c108410340e109030b90081d546d2202034940a54a401000c1b030300684104c110400c041d004d943e04c54005100184e844a03c01c600e81d000e4108a2101d00e400460f402c0e442d80401030890148501c0c8801 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 682197994 1250 682196744 682196777
    0x91320120c0a0504021e0d020915031509040614090c011d03030d0203070201150906050a0f0524130f0f0801091a15090708040201110606031e0f0d0906 66
    0x120001c04024240b000c1c0701c0c607160402010f0341113400fa42d2006203260a030441d50044c042c0090400c1c2041c1e40700561078101507410004000070440079004210010420441d82c003d10800000010400b11481c615946540c200300c8001c0c460010100c00c681c1c0410103000d01c40c1c00014007550f5002003603844003840b021403444000d41142a45255406074401e100034102482150065980001130b4400020422075280910b08844071541c4129840c95a03510244040d007040d0000501070915105907182003480c00011403000d007001501c01400e0403000354041c9480c0301600495000c00c1441c0c1c0140e0700703c4c0e287e0350b03210000c0c103030303480750300ca4500d000d8031300144821060040c0e0003081d41005c04054000b1441c1c03060319101100034034030f1038404400307091051556142074205004201e10381d40c2020520780b80c40050042c2c4e103008003481d4160301080030046543d6000941600701c0351b0303103845001c0c008090840603141010084581c0028003421000d500c0156203c8000d00c219161941e90078182c03410a0342c07 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 682199244 1250 682197994 682198003
    0x81618180b04060b0708070f12090611070b0d050a060512030405280e0c0d0207081b0c130c090504050a0516030516050a0c150f1103100509132012 64
    0x1004066001404080b02180c0032201a0062a0040b2060a070400322a0389d8002d80c0c001a8910202040314034006110f01c5500507141c0c1c0388910701c0c10050003081d040c044004014003480c1c2c14400400c0d141c00003c2e0195200350401001403c000d842d03000c0c40040d0401051b01c9801c1409294000c5030394401416565485d43c81003050004031200c025003140c2849200c6000347e0006200804044040020040c0e00703079244010001280145240381d284d0008205d8004c1003000c002200c00c05500400d81c001c030f6555240c0069840319000640010700c250b603aa804e6070017440c1079020b1a4401d2406007004800350994200b24424800103000c40e60071a0382e880d064080b124181d800003003600d0350800003c00305000c0d000422400c46a82482c909800480d544c08649611482800c01c03c651606546110382480d4090402913007840080035095280c5450790b2011a4407510625108900d850080758041d514168111481508035544c0031004000c00340425030804038030145401404442c2c252881c1b61400329 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 682200494 1250 682199244 682199249
    0x316150315050d0c0e0405030d0518100e0c030a1a0105090f1302010c080a090e010501020a031b06062d0f060c03080408090307030309030b010e07081618180b0406 71
    0x700c0000038184000d005400ca0003140c00c440e100c82c11900400ca421040c603256104a200c2c030002c1d40c0c2e0313400701c0490405842020304140114240c803600740009140c00b0a1820400c440c1d481c0025210146000c0300c1e1606920070360080d09405030341503180070700103030302d00c41c0d050804000e1074400281d0f62401441038800003200c04101040500d00810950981501c02d80c1c00c55005144c4078880030010b840d180f841d580030491160103c0c0c01d18100f0405c00102c040b001d40141800d0016100d20a00f60700c025040300c1e00d007a8034114408101016608014a55100e100581421000003402843e650154121003180050010a40310000300002d640f103810003808040d01c039503039115056a50b0365501178483d90001350085405400900010060707031010441100158080d039920800e03285181020325144034180c004032060f040038010040c02e0341d0480001a00103241c4074590100c0c40c4440300c1110305092031400750040d4088901d0024946200c990344401741998180304024155007002040304880151 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 682201744 1250 682200494 682200521
    0x4020f270c0405100c05010f060806070206010e060105041a0723070b0721120c050a030f020c060c070c030614010512010e07050609030c030f06040b0708040312050a0b03161503 77
    0x802d1200c10003840303041400035242c400c6c400400c00b0401c069510040e600c00d5008002c0070f510980402595550400017280103140007001e014132814103d00007031252050303018460407140d2540e41a840b09410f403003107458854029a11404c3e0039005c0e1026580c00e81c07481800d504612820720042046101d2004881d812030b44034500c1c8201c5c1d80c00c24203001c8003503052008081402032106241800001a0040083d9145071340e07950340c0d4500000d000542207580342d510340d200c10707881804102c40c0000001449600660124030300c1d5141d0541e4645284081141e4000a204605088003403445045600c0018142d403411110300503400121481c0300e00300e8040a20101e8580d00200b003c110354241440105103140010303041d03825078134034600401d10b40101d03940b0001c2c140d40140100000e0140c1c0304c0582d60060817610340b00d0040d08041d11f00600b454400d82908511680d15804105165250b9229440c40c04026007696422040344514058840341c500c50b01c580c01154180d0b240c4114401e114000700005e18 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 682202994 1250 682201744 682201759
    0x1e0f100203030f2d0c070f060c021614060c25050f010302180613030c031109130803010509130614010807060e030703060e01060305030f19031103040b04020f270c0405 73
    0x1d400800c0601032005e040740100000402c54000800ea4001500080501440000c2485001c004001b4a020b2070081c290f013205503002c1050100d0b001860381a014040b00300c4406454820750424107050030b1071030840403081d20912107201c84460701c5100c020704560b4102c403440000900310005400b84d215460b00c1072418241803d049485113848005401d44666500005c14155147c3d9280540000c0540054031300d418142412011481d109884592090341c44c80308134807980310341c1e030381381802d00040c042d1034810f02844c0c3c00600074980540c0c2038444aa003100083c890004031815a1000e07070000c5c02000340c14001c0c044049849405070700c82d01c2c8120006401411030a01d5070712040018041210309a4055489800002c0440c6040010744811900381000f503503210303040c0081d000f00364400c000e0301c824541090005a00702408100b6260301c107811412440c800d54840c0700050750110b49105d1958441074420540f82a0342140f403a014444298005803021341d100c016403617035903024034803031158401003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 682204244 1250 682202994 682203061
    0x5040e1c110d03142503050a0b0a09020711060301061b061508070807050409030c0f050c0901060f0305090105130f140615030105060109051e0f100203030f 68
    0x86034580820500c540d8606900d1010305814254100040800c180c00029160700c031107541407a8511000c1c1c1c01403071640500b1440d40780c00380d00e1480c2595514400782415501d2000a660895a8001580446000b000200416210f8050740025004603030140e8030303900244e0441d0035504001c41201c6c10384200e6201d182000c000740b01c1e006200d0499881c111130264441c2c07105039405600c201180c0c041d000d08000351003460309040595190803001d0380918442e908000b940004a50004107040206410608810200382c0d0343c14074078646141486c51540150b508400000c40c1a800300304a058500c1d03d507400e000300d8440d1350b652800da40041d03c2d001056800301800390000780801114901e142d10034078100c03079040d181e4100c03d030a1010480e01c1c081e00701c80e0744031a070b001031070203101d0b0541c002e0007401e014001605080c04502e186c0c00420024900c034054004440703042c0d90380b400f050300004d07000b02044010912120025120303042030b5050140c0003010760100348510124150142c503c00d030128081603006 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 682205494 1250 682204244 682204273
    0xe060901080c1002161401020f060708160201090c09150e010509010905060d0c0608040326070302130801050c040801060803070b04030503040c1e0f060c02060f0a200105010f05040e 79
    0x1d0f680419070043d40309240d91207000381584080d0300020001c0d03603c10384c5584001000a420b0503125102c0f54581d8201400b0030660b5500641c40700c0c3c10000900d400030340c4d8010140c0c107900400040c0d07070141040405280024034954560400040540050322500c0006c2da9100b01c0e0b2038000081c06050391290011700140010400c079403000c0d9110030b00500c0030a180c0c00903110b041c03c600311034001000040618013040181074003c9001d84032012007401d800301d601000c0c407503080807607400380400d030806d500003402035402000240b501015003a08070003080b507410880b001e07659a41c040c0c811811f4950814100050302c0e00007005454100380c010b8110021130b941c9075002ca42c2c40d8130080045a100c11071200200f01c290710a41054003100740d10302c0d01d00d4040c2c01c0010420080d02c0c10781c01142000600c44010340140c4444d0301303881010007110403041c6c482401c1c90054074000d03402485a04024240c0005100301c80054110504072000652140c0e0b616803903c09000540707c107503103024801c1d40f004007000303490b0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 682206744 1250 682205494 682205509
    0x80c0a120b1b040821030103030c0b0c0f0a1d060715020304021c050a06200702120c100f1d09010b030714030c0a08100510140408160e060901080c 64
    0x58541c0316030000300b00c001c404201c40d07001074001e40b055500034100400005075181e044000e200130f0b00c403038600310341c5076690082007500e03804001003040e10b400c40810803003814401a0b9184519150b20951281000c4000901140d071414410704030768180000348006081c44403c0f90003481d00700310601100c08140400d07002a41c0050022604825800c500b881c0e20707c80e6000c064081442a000790485080d00e08000c07083c3c80000c52032444418150031444041d841032004c03100324940c16100541d01c01c40009296050800384044107800012040d4552060340c0e000600404070280c2c3e41340c1d152180c0601400384c0074000780080041c0c0280c40e500050002c25852806558400725514104411018a0009034070941082d19400034a180c0807480c000003603009030b80c25030b1000d01c62107441d04c0c5615000001f400840150215418844201c0c0f0000c0b0a21444040303401402d090021030744000c2c21511024107513041407284a11010300305002c40e64600c1c010706101d041b640300300b0050a61108800402c15036 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 682207994 1250 682206744 682206751
    0xc040623150f280503191e0b060c010c0e120102090f15091e040e011e0203090a0b07090e060306130201030203070306030c090e0105091f0c17090601080c0a120b 70
    0x9005a0741203c001041c040d291900d018a415600c064803801c0083d0149400740082c0c0015400b6406d0901042115600c0b071035800c000c1700a528045402d18803000407130b031244074282e1900c0321075080c00020049030707400120380118200c2c2070301ca808100d0b10003003a8908034000e251b07046900c40303001040e0f000d042c5481d101c4620b407440700016841c50600c0070070020303402c420000f0700440e20b043c10841190007840c140c4501c5c40d8201d240c2000341b1807005c0030101882e0640e90000105034499020007c998100000c205892400360f00101d04200380c00d040f84060901c8a1501ca01140786003c8400560340d400c02280440c026002c10926082107411580190042d4100030107050415954940c0000400d141040b04002030140726800600e41d13000c0c18170380d403e40d0401401888580e0140000c0d128107102c660340ca1000000d06200003420f2200001d0072076480da844005542031105001c240b04031160040340351030490315407004440380302786860184001e00d5094172070000c0d002802c601c0300d00410505805c5562 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 682209244 1250 682207994 682208017
    0xc030503090f09071b03140d05061311070f080c060103030513090c1e230705190c09020d0633020607050a1b08040b07120e210c040623150f 61
    0x241f00088001d8000d5a001449124034654076201813144900f014252262207a030f4440c0305000680000020318401e215074400102050301e800c2450090024203415908500100815141156541e040c020720541010140d80b0100c025520002650543d5100d8800c1000070741d260201e0403c005040d001c0c5c925250440e400c2403181100b403d454069500110301801d900144100382c464040d41010303071030018980650400d180c480314a02010880b940c162208a9030700c2207025a0781e0389010041c10141845d5440040501848403000c0d4010075402c40e040800801020668002540103130100da03941d10540d04480490f1042010884081c42140d5100720421000d1665048c0c2050342e58071080359020382c0c019644a0008a03800081007407080161000318151b02c0d10102c1020084001030702d00d011004090800400501024500403090083c104501c5004104000c1c9994600d06000050000d201400721682540c00d840001d1400900a0002200030f0341d0940c20006200103000311903000f507004c2c44 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 682210494 1250 682209244 682209257
    0x50a060518030d020d080907081903031401090204140a230d05071e0603020c070b09030c130204091d07030308061c0c09050106020a2402070c030503090f09071b03 71
    0x995602d0400070445050318030390040490f00b8848130020420031020300104ea05401050f400c10001d02e001540e02315070b140014503094141c955203010b03001030142c074420340c1c1002c0c280400054000c0300c40c5c1c0500125488000e02250080d0440108440d031a154001c1e0f60442e10f116140710564565864210001c0c10081c10b005040f4095480d854034000e5030780e110307145400b9001340700080e11258584840041c900c07400c007542000c0c29141400d440d450329004403a000000032528061a0737508002051580c0320141012164881a00c0310102a41c41405407400d42420201c80303c59042000c1007085074500d6000c003030021070b419075804441186026002030b40c4a000500c452101a83c0b003d01c9141c510310a20101d19a203160250031010303160141c0c0300c203007590044040f05012420b180c05020a5a002450301707400148600c140e42c009014181d8003500c0c402c84481d01108004002008007502c110480714940c003502510100041c0313880840b07014000076080a80d180c0f1920000310039000c401d10a0900d81d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 682211744 1250 682210494 682210537
    0x314090307030c030f2a0510200a060506010e0d0b10080f0604060c260601120606032301050607060902030a0f06051b0322020303040e04030503041704050a0605 70
    0x8201c039410790704243c17640d800110b614020032041e110250614001e4074401800c03940b0220422010390090310444d4000c41112101070b082c0c80c0b107000d03001c04aa261108607030f10038004e550081d640d000301c0c50044a01c18507050100b055913000d241036840c0e45200501e01842e440c2c207070b41c1d86990008007800b0a428190b90603408103d0040500828040c171f081c010081a06140c542442000c1e514801c007000c060013081840380e5401018045426003548943c2580d41240d03d60800485521000c105411070441c5440700c0490200d5160b000006405403000303500d8000350380003514030b82400083c401c0c550b000b10b0400c050340000c0c0b907603004680007a00003020b4459180c0c0075240c00704030352000c00c021607540d5668400c1207220300d802c1901c0c0241142e041c2030342d406c501c0c103c01c400801514004d0200e218842c0ca03103102c001c5580c10400c6802034010315001d452103040c41c0c6000342040e042a00c08a40d00e078101d092a00c0100312010070f0328100c0f1801441407900518068040d5440e80c4030100781401c2d60140c0051 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 682212994 1250 682211744 682211753
    0xb0c070807030321050411040b03070b0412060b040c0e01180b0f03091c0818210c0714060f07020d0210050a1103030103020f0105160c0b071707031409030703 69
    0x40d20096003e51a030210004124642c0f0303101482c0b600d019850b00e0b03d01020301001c034079901078186240030182c0d00000d001e1402c0c00040d10300f0030181d01c01c0803003100010b0007147e01d031100c20b6440c4c2410b00c640c1d411f000d14400e000401042d903845490036030004070b40d00203010315984100e61000d0000c401c08081800d003600c590f44400164803004038840c0e440d4002040c00017419007005450700b0900b02e4600c045c000e0301c407103100400c052070203884058000007404421440320303400d0000c0c0d0540c652180e00c0c0c5048840e040d202e1034031501301d00d6109406d409410310000b640300d005000d0304403402000b00403924040700003203040b4a54200e0202030740c200304e42000200040c0c4400011010b10001500c51585602c2599001800c249002040351025002800100010b0301e5408450100a030242400713a181d805000000a600b6480a0040e040b40282400018902c000714001d280b81e0b07001d032030703003100200700d5021031403080c803c90f0b41c010001060044001d462898090203060404401402e40e02e106503252207 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 682214244 1250 682212994 682213003
    0x31d01020a0f111902040209010908060a1505180403051804020a111b060f0705190c050310050f150102101103012402061311042a1103040b0c0708 64
    0x1184081620080b203042240c1e000320f44450484020300080500900c0200b80c0b501d6400188402800f80e500801c04901c00d03130080d0508809005940304480180c9004032401014224842c800c103070407042d40c0700c003103a2800e0030b208050a0515810740500a910703107990850341c1d5480741300b0502c00142d2394500240380e80d0321400103000303852450303488503203030002c1c010750b18104078007a00e81481c2d120a03060001900d032103801c203031500c804003400300f1a1140c009080c442d042040006201c0074022651410104000c0e1030b00415041d120160308840e006620b501801c4101c2e4028bc4682c0b5500c040503000400c82205030245d0b800407241031041d0744c2204000c0a400082d1024540d04020030720004c0014000c80c0c5405040c902c0b40144403e121004290082e006512003d000d84041c80c90308250000b41c050100d4a20a00316078003010b0820401c08420725086850f0701a0303038080309402081078401140c05031040d400c0b041005c190320091481d062520349041c0f10b951001c10f042c00c0a000303801c4c0005d5600e20500 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 682215494 1250 682214244 682214257
    0xf13241e02011b050d05010e090d030207060228030b060f0304061d010501060930020112390206160c030c0507060c05070603060b34060c02010e0606060a031d0102 71
    0xb1155521842c5881700780040c2c40050704121081c004060400c40524000610740300400d059003401660b40d001ea0418002038414100805480c0190700000c0b5140e00407010000803000c2a03580800411664008028043c8500c40c0c00310340655003400801c0c042411039000100005c10050596070461080301da880c21b40304268030040205030000f208225040c2c0501f44064000c5001c01070751340c946a0b11091003c0940c003140041e0400500c0d1202c03461403d0035078028820b074040b405054003680d1070005032000040c40202c0110a00c01d031591340006c8240000f801d18080d11801c2e24420142c0b645d81400c07507020420340d100750100a5040000380210b0014040c01002d0704183e51074101c06007603401c10320b01d0040300b684500101450b01c60704110700a03001c3c080d00c0440c42d05105001005882d00550100c8101049084c502d212b18032041c1070030020164000e00415240f600248080148196296242c4c43c007182e00c01d400c184c04018400710030348250710800d82982c0341c10304005000000c4849508980012 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 682216744 1250 682215494 682215497
    0xd050c040807060509030a03270308042d0611010906021b060105060f030a0b12010c02010506090108070e0f041b1202090c0a020a170f13241e02011b 65
    0x14140103100c014000d000c00f9200c0703401c0040c0307071107070740e0020a980700302c00e510140811445880c4a1011001000510200c80001c900c1d10882c1d46c9900340800703154040d20a01000d40303400c1100c10040281210358403441500441a140410302d0300605440003410f40110300025565010303043c0005805202030440160f40030191449021f01c0410b0340d1501d481070300442e120b120140145d00c030101a03041100c1d440111710304080f0314904201302007000102d07094903141c081d50070402130b9480c40c0c0e81580400d1043e40e04070f6a043e0b45076070380e8000a841e000340d4010542560500c500155100d00e40c100f00580042c0309000c81100c5804044000c4001e11480e008240342c685000862001e5180c80d80c285ca40202030045641c1c500000c894002e99146038072500241840e0041d610802040c0700101550380400b40741080d1550341000d14420480101c1c80d020b034921050140d01024409aa10401c4100410b12030710f07078030203090000ca03010308409410b180c8402190348491509882110001002c42546250f = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 682217994 1250 682216744 682216747
    0xf05131a120a02100e06070f02030a080d052a0901081806040309093606110a030c0215010311120c0d06020319110d09080c120a0212070803010302060903030d050c 71
    0x2580f04001350800900303c51400c100b044030f0400e070240d035030704226140301d84d001c20688202415032020a06005418a024140381c074003060034100c070049034200521400441c0c0d0b80c40091050620200c860700c60801c4100c10254061000e00c1040d4003a800d05500400003100d481c03540d103031046043d0f26140080f5030480010300200820040d00303225001d041c4110213803400000b007195180c4181d00300d501541110718070300500421054240302c150350000318141c140f6a1016039800340d041c00a4054402c1805102c014880c2c82c000444c5030f08400c2c00c09040c2e0754885422a14003d2100801c0100c0c0b4114143d814280150395007603c40399100442212074511960700507032030380340c100396015a0445503c04426944d0401c0e03103850303418100a04a600a00800324002248002410907504500501d40420348500c540c0420498284200000e0304d0149201d038203d980c1c240d08817142c221140545c00c030003000d040d400c1c00107000514102015201d60b00d0060110b90604204450340f0003902c0050346c0354086e0150 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 682219244 1250 682217994 682218013
    0x1609150510030b130603020f01141b0c030706030911091e16030e010912140408060f0f010b28050c010c0e040507030905060408070c081f060f05131a12 66
    0x1c4c00d814130f1003802c0e107001e41001311134610b40108031a40340c110443d0303040241c03151070503c02c8182c501c00d45000009803032036030381420080ca031070307682da414071484180c402e21951000003081d91007030050f00d0280e58402890a90409881c0500c03005040140c20030340c81c0e003c001d40a03100c2541880366948144a0b0071010301c000b822005003c1c044400c01c0001e08290b03410301c0c103043d0124501c0410110250791507c1c003c0000c4040ca0303420055402690000d580c1030194030140800c24000c14082801800444660039980e40c1e15004145a40303e451300c2c0f1980015614107120740d40010301040308454600f402d0580c80e148400c50110308440340e070440310020a801008802c0d050030648100340c0d0000c0342c0e0804105510031500c4a650380c6078000c00091040d10001410410407078200d03003c20081600380c1c1180d15510104004030309445402d200396042e80c3c604400001e00c80840940c00e000ca440203400a80c1d1407010100507000b401040e1030032101c00c0d0410458803250f86820364445e80e02c2d801d9170058242d428 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 682220494 1250 682219244 682219249
    0x503030a0515090601120f060e01051201020a23070c06080412020d1d04020705010204060215060108010302060d150f090213090207230f06071205091609150510030b 72
    0xa0024003042000c08512440c0115503c1e8011425040407003428400c040c0241b80b402c103806800c0d07800d8440b00d0305040c40790000311110380f00b50650590b034048807404031200e0f2100c551070803401100258800569801d0185061020380340e080300e006a55801e140703142400d96140c3e0b8210032283d50181b00014a140104010f204c0080002c20903000c451000d0049000072400091a90304000c0351800c1d920360554060704583d840d94115801e603540030009646580c0e0702c0001945601c13005500f8002010304500089841d8804c0e0318840c181d0398001c0c00325052901d00001c840080c01028841058200368540114855106542140040603190005030392030700d4940120000f401650701465586006200c1640024034401d2428101d0756500080c8000340604141c8501c0c01d10000329424032405444d0600118981c482e0041d150641c0040d814407081e1540e00c45241c0e0340328405122900240300513814002940750b40c01c6204640311403088100295107810000e4003164410500c07002080e41c540c0d2403042d50 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 682221744 1250 682220494 682220501
    0x405070c0302060a140114010504030b01030f020901081f05060f1f02100506030d0f1209200d0f380901060e04083907030501050108121e160503030a 65
    0x83e540b014490980502c80c00c4040c8175041c041c018070a41c40d042d15018991042055900840c0c00c08080c43d850359580c204020f01070040314099000b401c4120001c04d4060300014010704503415070320b03d6582c0c1c01c483d9140c40020b00300276001e5a845a030080e09601e860703980003c0131b02654600c10507a030109002c00c0c8080e10740b1400c201449240e074180402c009031540d0114010201c80000d041c503144100700c03a44100c1d40540d1607140f000a4500e81000001401841c15481c4851030382245000c0b10b50030071108110034441d89440c014004045102c5100c0015105e01c00130501d20324440b0b0352a82c0e04140c626612001001541201c4094400340030015034503000d0044800030540f01600c00600e081640390079104c0d2040c074504102440e100442c8102021014102c581100c208207000d4036a62807002103503444500745c1c48103071080d60070000080f0303650002041d00c0106845e001040b0340307811906550800c280116403c80d442d0b00a040c0415050306000d1500c0c04105481a406140e6a1403c0707a0110704070b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 682222994 1250 682221744 682221751
    0x3010e011b0e0108061311130302010306170309120709240e090a140c060301080c09072c0a030615090e0601060807030527101d070b070f020405070c030206 68
    0x10050200c00b29501c5907004114150006000da444009031040200000040c000622404452040004110f40a0080c1c510144140c80c400da03030903c80b040e40d90302c2508035081031460340340440d00304005060382c41c680f5281c801020481030040e680001e40d02c1c6507003c211400ba560000b91500092600d03128800758580c0340f030103026a05410011401e2000f641913541d800170070b004020781c00302d8030070a600c55070070802540d028600411443e41e968451184680316031014081c9400b8500c5030010135182401004008400c0283c1003124a502e62001404411446902c060a40000486001001080c0310340503a0000003107180b03d040d4810300d88004001129230b0502805500d400250050100c1070384080080c1d007205541c5400304803900c03a1031032002d40c61000c0381071041a0042e800152200b60300412200401c0c03500c5101004000c210310000c01c05030290752403608440d0440001800103441c01c20243c0b011078061403c04c5e42800081e400316080320000e58440021448034039012007015810000c8550 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 682224244 1250 682222994 682222997
    0x210305010b041a0309031201150f0f080a02070227010f091803031d06010f0609061d01080903070807080304061d0a0323181c0b040f0309030203010e011b 67
    0x20b410300c0c004120048840f04111110b000301e0000201d00b12804c04c00c16207190b8131a450005c00e1a50307486403c1e00c0801c00c012004404280048120b044503070040b4000c18540110740c446c02c3e030680e06c00e040d0744020350001900b02d9005041c803035110910300007500b01000700000049144030a504040300c140124139280d00212031035040000f4480d01103900c0d1810f507091549410003161041c150090007903002c1c1924401c854904c92240001044070014906804450042d100c2680050b100c00d001c40b45020000d45203000c0a54080d150034070703544200400c0b50300000c001c6c25a814902c2507600d414280e8840a030641d0b01020106c01d21043c8607140c8140c0700220880b1005038107001021114030b4443c0b42906000e0107100c542c81c4000b14101195050b05c9405100c200350b941d0f90400c004140d403181005100f89809040400301681720715484c0c10f03100103203540041c0c2c508020b0340c440c0e0f141490310403081012000c0250400000005031001d01815030815420000405c01d89030221800c510b81c02980c0c441e00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 682225494 1250 682224244 682224247
    0x503030315130f020a031e0e15070203360907121a1315080a05250504020403030e03010507051e0d110a080106090b0304030921210305010b 61
    0x403008185921080540020b41e031490103100c02080b010001c040ca03001000d01c040c000a0b5a05075154950300c114a0001c1d01c02c2c8601c14140d00c900c403a01102c071390100c0300040342d000c80c001c091407110f07009000c1da02002d03038070440f4070700302c407181030b4550703c03c1402c0c0741d41c0d220810388400d55862902898089094a42980d4904040c42c01080c01040400c408000302c4409984441104101e007003030610000c03a8802400c800c40e04802800707010000c000c0094100c1490480080200302400b001ca181c00f0903540100041c900072100841100e1450040101803100c80651a00015651558000b0b000114080d4440c51f010000400a15095440081140c42040001c01038118003528030954403000c1d40b040c0700000e44030260003511800402840483d46500303200440c95041d02da5008000c94143ea0041da82c800e040c035624924455280015a0000c011a580c001e0520002040450320740030f040f20030100440b440907580f140344010813980720060702c07070491528500969400d800b0b114010320b114100355 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 682226744 1250 682225494 682225501
    0x3061a0702060d0603020a060e090a23070c0b2409090d05070c120b07020d11030d2f040f0f1206020901090806071d0d050705150c03030c040f05030303 66
    0x545200d58400284544404540314185030f40d69030203040a507501406050803140c8805018000d00e1402800c40e20030710804e80040d883c680719000d148041551030305c840c940400005420343c041c1200401103020003a48812541c04141c48202c21402a02c5010420b84130954848000c00c41100c00f412942c0180306c0748042c480c0d10b1200003140f40c003205043c944561610700718903042d08201040c1d8010f4803c06480c00a9000b03001003040007a002d00b00326021208603200c4000300359080c501d141d0f8031080d5500144074296088038950000520100326940c41401c21048820113400c466280044402c2c4440204040c000380c40302d00000d03c05400d8216050303180380e240c80344d02400d050007440300a00890f002b240c0910300780d018441d898080e289000a4489a20b01043c006107440d0300f4bc0d0749940318918410307081c4050300340000038809907500200a8845581020144024207103c14980d4103600c4007040010b18110042c0301442c060070050440c40e9036a403401c500340400004035042588641c001b0800e0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 682227994 1250 682226744 682226789
    0x9040308010504021b0a05030901080619090506121b211b1c050d030b060f0a03110f04080601050321190c080307030f06090b0f0105030a06050409030207060306 70
    0x40a0450b20100c8000d691400f403829010041c262004660030b01c1e114a03040901040000b0014060081082e03035081c1d406e41e5450100a20510400003d0b003900a4000e014010504940c014a1384218080d000340701c15a00f040c0210f141401894a403049070350b03000816039251510310032480081f00c1c00341c0415801d140d40e140c0c0039210100c103e152200c114480354954040c2c2c03641071101c0c07061641c3f030348018000701d5241005505c42c1d804200110000e4501205285107242c003505450302c0058068409061065441041e001480600b1401d041c1c1c11080c41441c440c4030442006101401e000c5001e450305502d441c5c18980b411a11002e40c4c40a241400c0603059203201032810b8846110070445400c80504c0d00b11420b590b03072502c0103000f0340010790000800041d10341503040b0075021140c4c0001041140d540d80d01d17403400c55110302c01c1d00740d0214001604540d2584510050354009500d94400a0001e036074000140880da03031254211b016810550342000803035094455100101010380400d00e151684015 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 682229244 1250 682227994 682228007
    0x11041d16031a040b040e061314240615031315020313260417102a0e06070606051507020a050d081b012c06060f0607050d031406090403 59
    0xc40d180504e50380c0304010300741d0381c4a40181150501380010383d001402d00406491141900503015211a0b8003440441e11100b00054050b8500407008000041446541c1e4009891500641103d034440321007840075880d400c0c00c0c3c00a5000b60402c00004540f0907152521107580e00040c40c46100962060081252001081042652141d48007007081c0340403c03084034100c00207410f0170b41c42d0f28041010a021039880740010540e00c1c090100030803586008810038901060f2003034001c0b070302c0c4846240400c9080c10001d20b100c0007941d084505014943c02100b402142e001d40060b5030544405482e0712041005040108880b009505004800d42c5062080e40200314035061301c1c0714050040e070410b6146400d21583c2c1d81600c5480030450b41181d030404164410902038201c05800740d00201c000c07080e900a07400e000b003001402c554420050951a51b90790204141455403034251604140100030440c00640300780049007180100d620001502181d218150980040040446000d21903c6060001003600b107a03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 682230494 1250 682229244 682229291
    0x414010515033c15090c040e03161509141b060f03040b060d0602070309080f0d020606101e0f0806060a05071410150905071404030611041d1603 63
    0x4030302101404030040e00d5203040ca800e070640c520031910b4014801040400b1030055146d81c0d040324140640102841e00d41d850b4890b441c401d1020102c256031010008201c40d1001e1042e40724103000003132000391510b9020641c0308144a11b18503030885080c0d0251041c41c2403d1303a1300c01c0c0c0b094031560309200d8101e9101465100c0641b0140520b460800002c8480d030398010403806c1c503580020155114000746c6005410040c2c180600c0c1918002c4c00c803040d0a602c40041d00c40e0400b81c0c2d40c1c0c014a1192079410900c12100994110340040010300703900b141425280c0f440201428615503186100e50f001841e00070701e200b00241c0b02902c2078070200400700d802603001060316207458204a480111520012106103401145442c42a52a0620180c0c4980d0081c18041c0c8040302c0000900348415030310f900080b03540c1709404864507014a0300384006d1021540d45d90010701410302242c2d48030b1810351544182c140030141c600c8903104658156040080605200c010704140c00c8190030300380041d0304601b4249940101300e2 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 682231744 1250 682230494 682230583
    0x1150801081902031f020a08010e13021e0301090b180109080d2a031415090c2b0209040b040b0102030d0b040f050a020a1701030305040608041401051503 67
    0x1542002d0640d5010b108240e400025483c4000b9064400201440a500b040b0b480501040b45500001420f00c0c03172810892198400d01841ca80320201907003080030101018040e40e290f81d829101c0d490950303c0911076800c0e4140202a00d007207c1c981001046401c000c50f6a1613404d503410160034800203010442607c0b204440d4010110303100310741090800110003030a00080c242148000701c0e40030607030180d1003c402500091b64042c070130343d01c0804482a000302da80000340c002d44140002800314454001401c0e01521407402146030b1407036040e840c0805880104890b400c550700003008400717417426108030072114206035000e02a00c0c11120000c0d440340602d42e2001c60058580c0c465420340c1d90382d035200c0030201c5080f0384108528144ae80c1b0241c0203401c020384002c003082e0801c000008854000c10001e04880d40f503900c131481c0a00300326081346d4056024104590020a114030746d00c41d10b00c00c3c01410b100d4028401c0040d01040d280c0d0401d8075103ea030450001054001c0c07080e1039040b4042c480404916040c4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 682232994 1250 682231744 682231783
    0x1e07020d170c1e0106050a03020a0314030d14011809050606040203070302071b0f0f120f020604050913030207150e0409031704080c0111040510350115080108 69
    0x185003500709104078024142e42c0e01894600659020003404002212101c0f50f0007003010684540074880c00c41d40500019501c03a10800081002941c4202d100c0c403452802c00c20f0742d0618034000194400d0358400d40c4000140c840d003100503c01c1640c41c200910880c40342c07800c00d1140c1c10182d15200d85543c406440700303000e1600080051000d41c040d80448010b103600060380a00d560324950324040c040194001d004c200c0d0340310017000849403048010002275075040d014101d8000201e940d1200c880208040232a0064001e01000a032503881d070f0b48080c498038078031410410604062900a08080054021408212011200b41e22131980a1100545030070280c8001428101908044e00c0103950b075412615100c3c81c51041204000004016000c6d00e0f560100a02034600b03213144445c9640503a00031190415454160010542d101c0e06461540001107a1001241da60704000c0c018000500f007051291031031200010008400b0054042c8201e10081c500074601d54102102d854039400e5400b00314800001 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 682234244 1250 682232994 682233023
    0x403080609042402030f160906050a03090b1501111603031b060c052d030c0d06032a0f06090e04030509040603031e03051506070507090906021e07020d 66
    0x100c903003405103c200202e100360381c400128803c80c00039500849484081c440500049903000c0c410610103081d040351612404403c0c1d04150003100d0540003800b0b500105611800c507240400c1041494600400b00c0c01e11100c0caa0880d10000741c0100040c08c003982d103c0d804102c40b1000c11200c00c1e48007090b0307607051a282410ba248907001520101480c9000f901c1c1c2803620040000c040d40000003010800b508149550b03c0025807400210f20001d0040c3d422651901040014034580c49000103109000304003400190603a16a11203072850405031002a24400c0030041500245600185a00042c00c10f0400d10701303510b0400070010400503240c81000c84603004180828201340c013410a8800742075001e0400c010f4a99607040040884514040c081c2c491075461450405682c8217001c2c0a01c0b5041c01c0314a55104c110040c1440341603809802c00342c07168010038001140c80c5480d4062507800d1030240c20096181c0c9800c40c09032100702c0c003015000107107010401101c070040c0c803611450000d5942120f11140e4030070 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 682235494 1250 682234244 682234253
    0x303030b2b06020d060e01050a23010804082701090803040b04090b010504081b0109091a010e06130b03010503190f0305070c030b070801030611280513080a1208040308060904 76
    0x124003104038644c5c02c0075808a82c585001102c5c0e81280e408a80d86403003150b481d811001031560414100d104445400791210255001d201c030356400c5441100440d00d8000708900d005400282203680c0300c0801d0003115880035a41c0c0c00030840c4081c3c05003070050342c501841c8c9040c0301d031241729a200304d10040c1e4480c2001500d40e80030b401594010324501c819034129200c912802245a0304007514903000c200c140f980400c010080e841070b02032410401540c01d961080c9400155080320020800980c0181c003005115480300300900044014400000e1f80c5440b035040034205400c1040314158a103080b4a150801008513564100004106815003806c40c0e450402e41860340552140350000351000406c80144007000341c0c45080366040b01d01900041082c050310602c51603c511034043d0301030000d481841d24841d00d80404190031081e104608040386405502004003401241ca035002c804990450700700401440481070101d44100c0d480e1915050a1030170360b4001d0301c01e003809843c403400345408000240421 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 682236744 1250 682235494 682235497
    0xc02030d0c0e090901020301030b0c090d150f0606020102030a06150210051905130c060905101805091801061a03150a0302060d0c020c0306040f08180a0b040303030b2b0602 75
    0x80107800f9500c0ca24003041442d010b90b00030f2008858068111000a000140c0d0b030040da0460400180540b40e0785982e03448a8440c1e9403e83e00d503006180d56103140f4848201c040c4201d4008081076000583c4a141c0f8600f23890484003558050390300703255000a1900f210340d0100e030383e44045000c0e0b040014070f03440300c1091500081d00b007115071002c640343c44181315540451b03c0c200040d1234402d4400b080f001d0744032541159041024031a0707d07001100c60154806490203001c0001d102031048107802155a500d2000905221040e90700000110f040406604c04c0b807400c1c092480600304000e00a042c070308444104042ca0301c00203041000d020880d64104a43ea0384294407280215002020305d0745076542d01d10941d006025034088240544503440e2000345508000c100c080c4181e80060840116043c6625207081d039900000510f589100380b141a104150b4071034071804042c2c00c051000035151400c0d450041c04990811280341c3c03003180e14844046050980d4103082801c80104c0c020109420a18038000c40a03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 682237994 1250 682236744 682236767
    0xc280504030c03060b1f02100b012a05060c03070c0303020a0c120522030f0b040201020703050f06240a150c0c031b05010f020316080705060f011403010c02030d0c 71
    0xb80400481c008180480e640041d00c24003812540a420403002c2040c015400ca00c40c444e20026070004100c640d006001c99208030304900040c14080c11803c4c64840041c00c0311200405001e2440d1400682010b018040000a5010700b0700c601081c0b4501340124064020205404010b0030150001001071305180b00380b40f80b222513a030000d200300c600001d0200c007414a03000030128560254a613409507580105145004044907042086106982d0154455070700703030f003002082a0305511800c040040014400c0015541c41440d40b40604101e0030490883d800c010f40e00500d01c0e030203000c1800700003655601d00c03804d0350454801c12411085040c40401c142c40c54040c2210180040709070350400814400c007102c42c0b0640748014030002010790b40764401541c3c5190501d480301e005900521001c500d50305a010040710076801018502c0c280340042e80c0e000d1811070102c40e0101380441c42c800402c4241d84400300d405400c1030480090250000f046802980d900403000e14054079502d0307580348110301d40603000b5090b1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 682239244 1250 682237994 682238003
    0x118020408060f071103040f0b0702180108010e33090c04090c050306013312091406091c08100306062d140f04151502060c28050403 58
    0x710b261420f01c034601150304445840101d0300360300d4401d44001012044070150b420301854804643d04007000e8002641000a0890300139240383c880400703202c4d460792a14001e01c45840040b0340481425411401e203030205080c000000640c4480c0f0498058108221118202c15413076a840e65464882082c60007852502c02074009252901c2e650502c450800b003070303045c2c0d40c00354101d4140b41d81e60442044030300030000e5121540142e02c81959030700405036084821803d420300d4041503102c6800400c3d401c9a84400003107a0164240502008211081c084558091101b50152147c0140390350051200c00c60700000a0401c80140002032200c2901c1e0050405507420540c100406522010a020081016010040c40038642029900411403011048050764900082c030003501040700305200c90001d2a00529500c20303242c1070703410425110341c1841d02c01014420108180500d504001a0501c0d0001d890324000d1001044581001c40341941010b20180c0302102085202c19154401c03209400345400052 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 682240494 1250 682239244 682239253
    0x813020405100e010b0a050307050d0e19060f110306100c050d050a0909050103020d0303050601050d0504050106170109020f01081801020d021b030c0703150207080403060f05070c05060118020408 85
    0x80000400064641a6124080c1c04006642c99090b05c2c2c0c241d019025891002030003c100050b05c40340706034003034540011403890110341420540603183c02c00d1098040c4450840d940000142400001d024400001054070300410a0641710107000d1003920008125034019010b04140c2d0844074410640200595003200c20f0b117014501c0100700800030b5011054803000150564400305a0301c50a10a1504a90380149200b00044442c0c0d416409024010411414401c2c14000d401c5040f0650040f01c0c445c40c07041000140090500509000040500e82860a160300d008000300043e12181f052410204c02400c01082541e00d5882c3e03910b1020b010080841954004200c0708800c0f070060300989843c550790340007500b078030740d040c555241d40f80120003140701c0380e031700201c02040401c01da14426624150700e40400740c03812016890f040301540c00b0340e100301c8943e960b501404200030315a00c9403a0308001c1c0b904e070049002041c0d8550a0756214180600c0c4c0400c1c485008030602e110103941210002c1100409a5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 682241744 1250 682240494 682240501
    0x30b040f0201090f0806161b110a06020a0305030a020c0a1401020c01060605090d030e0102010213030c0518060312090f0d030c050f070b04291314060702010504060813020405 76
    0x248015a0444401c902086804202140800c1420f07100c03015200d0010007460b042e07442040c44061501c408a4a1003809603850100700d5603000700146280c0d850103800c496209008400901c240000568800350442d000424010006503000b000c403500b103002c02001688509002a440d0f041500d9844000c103d420000c4e03406801c4101900600400c3c26400020010b036035507064203850a00c5a00780385a840703030b2075284000001c0d004403050000d001041c4001824646c202083e0440e5075001c1d0410380340203000b02c100704820f280668580f61152301820314448075041500c082680d0302110f082d0004004000300d1a1800c0d0380700d001d1059089500107010708102d40d868100503003205011641a281d501409400c02803000e400074004044400a500d0b042ca4030346031409201c21006c044102480c1d01c0c20b030980b2400d000305c100e005001a268aa50b0191030340e03141180c0c600e04a01c51000450244805001000c0582e030004261003c90303a041c01c2c20310690343d4011940a01c80c03d9031900070350003031030030050 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 682242994 1250 682241744 682241753
    0x150c0f0d09170616110a080406051201080d0527061206040c110d031d0331030201050403150b04060e1f1a1c0e0a12030b0306150307030b04 61
    0x7a6821100b0056403240391940382686992140012074015012082c0c1141e160f841500c0b5150690203503c00e001074030007040f103a58448016501c5940403100081d4045071100d103807580780c4070b00c60040c15503200605120b41110000707491406150b203003440407142401c01c00666480d00102c800200300040086a40b140324908900701120700345c4580e4003981c940040510700f0340c020f0240c0b9002026900040c9001c603003660088004e0300c4802c2c100f059101d80c030610407040980400140c202c1034012440040c414a038801c20181d0181c03000000002c0741c40c075880030001f60341c126013220282c80e00200700c0102841c90010360005400034080d403d0304180703800000641e003510115094003921103c8070201003103011303000e030b805035860034041d007210003843c6500401c0b10044400146003020300e850310300500030786107185001165191000c0350070a401c03039406101081f180c0000c8251a0324141030410940c2440c0002c40c1e620f6000400401014441c2000082207680800c2180300039503000701c00d15101d02d0203150 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 682244244 1250 682242994 682243007
    0x170708071106091503070504030203120a020f0a0807120504031e02091e0c0c1c030c020606010306241b0c1403011b0503070c021c031409150c0f0d 64
    0x81030340e40703045030101d401c03491a0100c1110f00c0407030300030f01c0c2e0f901d010b0340f20070380f00400e51002d000c50085c020100000001a102400304d4501160784064894468030540c1c4041e04105c02c250228030550410101200083c0b0b15006031208941c0215000d91100c1741e540741641c242c455500081c010b800c1442c150340c1464405541a002d4520981d0f81030942c0d1103600c0d00c3d1103d00c881d49030200500c08810001502c00111030041c110881c50074044420400c0740708101c040e0302502010b040006038075050b040c0c04082d0100700c900e80100c002e2808010061030800405110300f50200741142d030194240e8100400c0d4422240040f4804c07071101c1c4002800f4946c5001001609180709400c2042c09141d14850076281c180704249000410309107a03004040c40344401c5485500041001044c48810004d010142c1ca4403180f000c60710390b41d080014884102810058841010182551403c60f010041501c068070b40344003040842d01ea05049075201d4030f000040c01d06144100c80001d485104c0d020768107090503433001307 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 682245494 1250 682244244 682244257
    0x813050703240b09010f090504230601140f10200106150909150e07120623120d18080610170f0604021c0605040302010c030c11100504170708 62
    0x103007001180c0f00701041c807180d44024440c1004003024020200322562090f04150380c814410410b103da41d5080300340d90b680245c582e030851069a0b1102d0018400d5070ba4a01d480400c42030101c1d02c90a85030740c1800001c0000c207440c5080d1041041c48000c5024003a00103010799a400c01c0d140090100ca0340b5420156000c0300040d805800182072003000084d100a184512000b643c0c0c00352003c46070764200f060441c900c0d540540182c007080489072100001000302c0c4240d10103480099a4581c0080000c6250020108200c0c1c0ca40d115503040500300c04507043c0060380140c10b40f502c2c10700400d0300c0072a004202400740640d1102405001d05020805040c0d0358010b9002952195078040505c44c4142603002d9540440302c8008034194001d402250240ca0184c0c4001418182c901c4032690ba400c4503038824050351025107013280981c0d1503200c50704280b50103000341107591071a031030040030100110010355682c1250030320300030420b980ca2000c10240440320798240001004244216074542240c0f82c01c81e01e660015 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 682246744 1250 682245494 682245563
    0x22d0a142706071e060c03151404020d1401030201110703080d0914010e1005090d0219030315030b06010210020a08160e1504180203070813050703 64
    0x38501400c85a500195403201c4295804804811200003140307007a11000d10320180c0c040d406000690005055030801c010180344002018102801850b191083e1034076602c01c407092600f845802444a00c05c01c00c50000c54581e4122640c0c0300302c0f9917001c01c00a00c203030a05c40e680d503414911000416003d110700c1c541207a01c01e0f40d66209180c00c0b0140719031580d41c140002030500d1002c0015242080d030641000c44250f001c1e6291441c0307003880c00380035070844009610500c07040d0843d00461803400424400c17558001006d10151502e04000c400003501e4004216030031001c500e000b929141450300c02c0d840301480107016003222103410b0300c82c2040e861083c01255901d00600c0f550780d14a074a0b031300034000d9884025603070b11219600e8032031074103c1c40b2400d24405468108103003504146120b07600c1007000c000c51408100910f03070350750406001904118420307101c0144e0078010010b1010559200340b1040e40000845071105503100646800d0f403e0080c1588040e000c010003e9018410b8030150407000800f00c1c4a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 682247994 1250 682246744 682246757
    0x200a12050a05190504090606020c0a0501030204080309040f0e0316050c0f01080402010813050303280903080601110f060c0c010c18053001060e01091806022d0a 70
    0x1810422640ca118003225180000c4040c803604244142000790000b01d0307030719414141d08043e101c00511080300d000781d200b507005074414040000c03039040a0345064050070003841c05510706820000096542c0c40f03001866800366942d4081410505820703804a0f1200c81000c0690ba91118204141903401007020010354160140c0b41d8998185d00d000580c0800300441a161303a1140d640340e030015034a24800500083c10341c0c100e420000d00040c0188001c510403014240300f030418404408520300341d15191140d01d0040c0c3e140c16680c50102e41c1081c8590343c044424600081c1605000c01014104000440c00b41801d218010500007241c0054001e00010088940200038003030711144100c2e0658003108101504103846402804a0b0030080700030b0b1102c01450111462402d10810b025000d00e032201003001040e5541c00e010321542c10403100050040c0110ba00502003042c400d0408210174004000c014a5580d00051507a20020040c1c0300c924081d19a2000031195450088106907951013540345d580003900 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 682249244 1250 682247994 682248023
    0x40609060306150804020f0406030605180f10180807030e09130c031b0807080706020d0206150409021305040b0a060b0a0c020f0406050909030a030c0903021f200a 71
    0x4280b0035082141d458600308001580a0042038425103005001030b40c020010000a41c101d889a0181a0080d441244009a289006143c030880f41c0c00b103181c0012690480ea4036502e0110000801d41100038191030009114596000110400e180c0c00c14000c21841002c0b8000042c10380080d140200c114095510302415580c81028114044449000034915001047c040c00841c14100c401c20300e1090700b60344401c40f9501d03540c0c241d1420b02da0b940304205641c4810341c1440240d6041c0012504106280020100d0b4106984015121104850540d0041c0d50322050310066696249001c04103014030901040309041ca4148038030311000490300c01e42d90508203800022007541144c21031b94480a00c0e510b042500701c0a500300036007810000c0c08542d0180d01d840000c98195101101540210b40c903000542c2c4e90891060082e00395000900f40c001440864902000541c903800c06061071800f07003102a00402100e11400d8034a242560650300d01039080c0d907660880d0280010f03181104071302400d4601040305 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 682250494 1250 682249244 682249247
    0x9010605010509130b1302040909050c0a1d130b0f250212031905010b030403020709060b07020904030314090705041103070c120210090c030201180302011413030c08010204060906 78
    0x42000303079244d000b8580d413007100d449002030740c00903d4030b5070000c00c2d104081c1c0c602ca4035803040c1d070029000a400d07a65904010803c01404002d03030301c80701d003054902c01c1145d841c006035019649407807007104a081351030100160800211880080c1c201d81d010480aa20341055211b22284100440388001042c15000c0300100b90142c011131200d80b2070342d0760300070030846900c2c0103243c180e030b04098061401079214000e00b9501031810b0140c00d002e8a459000070b0780b64030341820001d1a000c950b41c010a841840c0400510809403c0c07400c844c16035805130f03030300d074001c1c1c0f60b600d0220000d020000d1005408841e8609000ca041c201099400881d40200c0e0180701c41c90741e90001000512007920340c03802140c2d20403001000a036101000d4002800c50780155040580e8580c9941d05a070480441241c0c0300c1c00300c0380103008668214034042c1d001070100c041c00d10f40b282103a0010f002c106005c13941050b0004082a03410404210442000c06950f20172204203d0b50303681c04009010350028020714001c1a011070010407060f = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 682251744 1250 682250494 682250497
    0x414100905060705071502041508010e01050a050f011e1809050c0d0c05070c030b0115021b0f3105090a150c03020405040219020f010905060f06030a0b0906090106050105 74
    0xe03400402520003034488540075252540407000171102005a1407103010180071900c068030082496400d801c400082d0540d0040141c84141c2281d0181d801200060002d92900d41f40802038075400e5450440e13196032400161003042080c0b00300355a081450070181000c90b44074a42d00501980034620200c8a61100081011755408880c4c541c03542c94144002c02980b03c0c5070b0840c440c03451040c180360389440040d44506040c40d4a41c4c03c2170341e41c0912074004101c3e80c0e125100d40d500450851015000159241c030400c80c8208040d2a00c80c4a0395039042d00c20010303913481d88901c0c911004e10130900c01d11003100c0e000114443c00202d80307000c2c142ca4007000411a00021440c1140c56074000d03021032458001224100090594540c2c181c00c25a003408045080c1e1110320003049244808400303190f00c4030501c80001d1400036100c0a03030800b64180034001d800907800103100d542000300700180794030965455010a1038500d40d01c00242040129005020384184040b0312301c0d02a66514000b402003a8030740e00103588a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 682252994 1250 682251744 682251761
    0x100f0305062e09170106050f060a0f110313240206100902130b03071e02010b0a0306050c070615060807020a02010f0807030e10020c30030717041410 65
    0x810540e0075088040e010400619000034050030700b91800ca4444203002000c540700d103041030290b0354440003840645004105002314040071950345203080d45002008003c60390010040c4240401800b8200c60b00340d00f80141d070b0751803101c0d9040385129907494502e03202c2004102c090203503000304540804190780c0f000c1156842001c48191801d003441c03074801000003c1d405096560300c20f002e943c1c40450305042417001107000b8440c558840c50752404481400c0c8101e0082038400080da890003440b03030540c1e2200c4a0040c101c13500f03c13000154542c0e47c10309420301446184001884c1600d080e520000ba030480e0543d24094540300e50f5403403800d50310814281c1e954010368401a0110703030340605034410913210342c01c01a8407546600d0041100c2070203606151400381c1c070b07a00080d141a00881c01c45540d00e801c202c42139011400114441000191221443c0010300c14941c9032038613400000005c4c121400340794984a6000110342017440c620f410b0425451340c40c0f5100c04050240680c0b54a03003019a418010100b0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 682254244 1250 682252994 682253029
    0xb091306050f060901210605180d080f1b040308040b071401060b0304060504241b030227060708120f0708070905041a04020d05160513140d02100f030506 67
    0x443c1d090141a02c1202c54002e49109181820011b400005e0f1890040d41c0c0100304010710081400110031080f070600c3e2a00028008001c546010060415246210250480c004e80310100c1d040780e692a2003501c134865600050071a0100040024124503c1c100030301040d8040c121104241c0d1810344042e003a103026124081c8150401d00202d00400c5d020362150350022f12805c40b004d40c03c0e10b0714001c0b83c01900d084c0915000341e603444803050504032140c041420000000d103000c40c038104520204c422085029220401c9841446d8807040d0180c442d90211050150803022071611034000c441101c04000b400c81c0c404c0c45c50071075040855407040c000d0700f425000f0420f9032076041070350781404103000040840d00c0c142c80b0910300c0344810b15059165131006250f00e1040310b501040916040b0381100b4664001101c450411808000c00e12818907803e1000041e90300041044542d04000000640890300085010b5030251800f01e8000c400c5800030a4191051240d44050105a54100c00c01c01485c03030600c0c0205 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 682255494 1250 682254244 682254259
    0x7120801030f03200a060b0405100f0b1b07080109021305010b03190204090c020304050a1202010f12020f0c0c030d1d0904081b070311091006030209040b091306050f06 73
    0x200080c1c018012070700c0e03442c10088107400e13195081d2641458440c19180954032a50780b200780c080d03542401d00070707154040c0c02c0c00c85144000340783c503602850401840c4140088402c000c54421a10345004034564002c02c0c0850844202d40d1300c17210144e00030a02260201c3c424038030280f41c150b031100a0b000301d43c101d408894106045540e21210b03c1417414044e852844420b0b4204404a8028042c0c41010703491500755000f1501d032800c0c4401d1103200340c241e8008086881c2400d60a500503030b80490b8409004d00e503454152403e140601046000c0c1c020020006c40107000864800e00141c00091507012075a0f0840403221128036645056448042d00c2d403400640d074540c0409030040f0300700040c000e0b800c5841001114503248443c58080c41032040c00100703012680090004000b1f110042500307003034981084421000508140300d00200c0e80040d0712a48082c1600071441da000c558695100c1924420007803c0c403a0300346801042c0c0c003041c0801d4a01103840134034140210341e01210100d0f030144504006016003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 682256744 1250 682255494 682255523
    0x1805102706081b1e060a05120a2d151502010f091101050f041d1b090a050d1a01090c0212190e0a0b0c0706120c0e06030603010603060e030712080103 65
    0x200c2d0311008074000d07003100181c41800c0031380ca4550303400030242d41e41e183ea1203607111040c050b6140d400300b001904019a080c204106d4611494000280442500c1c5007514080901d0004002d5400f50401c510714001c00c00f109040050061039594400c0c540c00099802000b40c130307030f40c040040c0448120002c00b4010303c40b04418044a54040c0004041102071491024180307903035516000320307100341e1041408002d1280702c03d003c403400d405010100c00b40000d01d282414441e4030404108850814443c130741c03184010166a006002d50500e80d102060100f00c1441e60540e180e003d071101410150201c0300061042c886d0102c07440600703406407010303200c4000341c1c015101032641048417002e44400c2c40f264003210448000035540d0425004001100540020381945490500050400070610400c103000c00c2c00d103020301040f01d0388001d01c0103441200300d58842d1a030712242c0109005003e185c100401142c13070507440c2240d2200010152441511800d01e80c1402018214101e400240a1100070b00044100641 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 682257994 1250 682256744 682256749
    0x40b07050d0209030f03040807051819140f0601080601090305030d0e0f0a03110c0405091c201e0a120806010201090c09021209071805102706081b 64
    0xa00300307001e1494001d400d0911400009051013140b919026a9a00c009410815038070280200c1c802000110780c811101100007a0f141d42c9e0790001000080d00b1030720381c50b600701c4840090f40550300050300212010000e150115030038980d65400d4900602040503440010070030742c420708808085d41e900502560074562400500c1024112460344206240280c8101503000c220030030106072218060743c3c0381507826200c01c03401d505104290600f14021420181001640c21000548c000b1410340001c0020407101c4950048a100e0780d1101015400800340303a09600340c0d4000106522040458911188a41255060103551700201d5a0040c03041c4004d130042942580603440e841c0d4002d0041c0000b01c0c0d1040e165640c003440f1102c54010b0620950f02140c0d55190411440c1540d521030b901c0d00040007400e0414881100c041c60041089075010344920008441c0a070f00c0b1508002400d211135a90300e000c2850001034041a0f043c05c07a001524503181c00040d200400040001000c107160040b0508945103405 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 682259244 1250 682257994 682257997
    0xc0d02040e0a02120a0b100b09120709020301320d020d030219140d020a051921080402100206010302150d09051b24030a0b03070f0902070c0e040b0705 66
    0x42901c80c03405103100d2903000d611109022440b400f007000107415003103e2441e2030703400010047c0491a10707071107c071f505105030740c14201202c1941001700c400041480400842919121036a001420280c3c00400005000240b04080007002c00c55120080d107001c0030000301824105014a03030a50203102d020715071015090081315840000d0091041d00e500c1c480072900701d440309600d25412030300407000040c03130140034406004034004a0311900c0600104292a01d40c956141c2c24202500c981c10b40036004101004204480c000c1d8000076030b03981ea4003031501108098007007601201d060b4061400080d4a0703188600c0810494142c0b5030040281c0c805400020708031040303801055040d8911661088580b012540402244054003d1200f104201400c52418003259280c0c040c0e056151214403c60344d1450007141096030341c800008034000500840f82c130002482e024032544241107980c0c0301403005c9a0807805030000c10009010300596100c1030390360803444400e40d8007200e028004201010100315000d200702d0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 682260494 1250 682259244 682259261
    0xc0f0f0212032a0c0a0312030b0301060b040302030118150f020d0e0604021003140f070c0209040b01030215040b0306120322090f0b060406140d0f090b06030c0d0204 72
    0x505207091120000c620a00d1503100e03c0b6003510750a0900d0310744055103594030200141c0103100c000780018504001c0420340001841c000103005035004002c2c158294483c0e40100e5680d031b4014003d010392943c072000301000b030344540400c1c0c0c003035400c0110b1401c0c545c0b0b01c00d0611b18103642c8119442844105041600001c00740c40d54602c454a808100d0044040018040c00003d4a8020050300c0f082c140341c410048140540320102d0245818000c2200d03500300c007901150b42c03001e080403110303050382d44d00e034000c03944403503402c03402940103130240c0910092040d0061a541a2482554461900001c00f13800008900491082440342942000010b60504008003024020b04d0a103040760305200807034660b203039002d1061419103210400c2c0081040048824046d042030841b08040c100724403801a40421124400c03805628140600000380340d4010800d9070890721010912403003006881103c120140140c6411101665900c041c54085151440c006c00c500703a000000902051380850b080e802d01c006081543c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 682261744 1250 682260494 682260499
    0xc030c061103040b070314150d0c030b0106050a14040e01031b24140c071502070b0f09010e03010e21040506180a080607020d0309081303031d010c0f0f02 67
    0x8903021404250081d01540c0203900c00d2480c0c91440ca040b03d00102201c01c684950360244a11000340301c0c6c00010b0003009100040143e030300c4905450705003040075000060740d00040410b00320100000b601c590100203400c14629654038a100c0501d116140c8a46000b68000c4220a4180070010000107003601003401e070f40e04142c9140c11880d56100741e00c6460300b14109120030400046400b0140044d40030750440a0304402d41c40c0d85003040c000380300d00da607200300034090800d644034000021103142e40200f00d000020404403560b245d0f80c100400c500001e030342103030003594041514411007101914041c02588240d640c9003008180d24184034000c025100d405074030b40c0455000070000410251501001050408020403800001d11100402d02100c0d21340c6900a080c0b941040c07041c070001c03a82c04552400c0d201d80603c1d021440804070b08103074415100c0e041c1c0c08040003040c15000020950010045503c507004440c20f9100c400441b00155902010301c600189210800b80d0404000f0305070380c040c001040c1c0003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 682262994 1250 682261744 682261751
    0x1090b010f080601270e0304140d11041e0606170a140f0709050307080124080307112e0f030c05030a020a14030703020d11041401030f0b0d0c0314010204060c030c06 72
    0x14011005c048031044001141103030030029007801034001a0750745142d100350644d4441d00c05045030f01d824100680c224940d52045450340348818881050b0f0301c0700810725030691001c101c159a180e401500d0b02c0c2d244107102d140d09003414005034140a080c0f0910355000d03d2551700303648550b242408404109001440e240074440320420218450302c0422241001d030500c139000040e154829440b41070081160700c200c8949040d8a9001c5c071860710080141c502945d4401801c0b074641402c5400a0294090200c540e40e0519226048880d034200c2030074021000c40b001d445481810f04041800c4080c1c1303090403950b88c017003401000440c607595101c1d8028880e4400b1894900031410202d51100c20640c070540703c81002940105454008114912402c0c1d4030481c40e8010728900ba14118440b007081c0c1901e604203043c15038400000408540c5030700510080600186413040142a916104c0c01d0b4284c20300090b02c180c41e1190f9041002041482114251245e03070704c420a40c5d12003941d0488071608000303002c80d1002e46 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 682264244 1250 682262994 682263059
    0x30b0111010617060108210f09090a0c080c03070906082706100b0403030f180302060c0d09080105070503040f081314090601030b091b091201090b010f080601 69
    0xc00e1203148040c1c00942c80d442c00004034440302030b16022041c1c1010f4030f00d400404000c80d4441030341406151402c08142d18686840c5603809840c0507006020210b50062015002c005d40c0c1e07003441c0d2000c0801ca1494a402c0c11685235600c01c0c0d80d00d170108440355004a91305900034801e15000c3d100b0b042d40141d4100ca049c580b440780c8803000050800c454a011402d900042c283f00c60202001640c0000d08170341291a4200362840e00e0040c08040006d40550600851490303e0a0717003040c070504030000d190068581c0b07a444042a02c3c403550b55075543d040b04d0019404410100380700d98103001d0b1034094821079031000c0c21521651121086601c10b540104c0d02c82a003086030840045645589400810514401113103640824003804204400186510304051a008050101ea92209415500000301c1c2c2c43c811100c145841008485206419005034000c6490105002c2c0050540161007040e116484182c8603036640c005081150f18140290519500500c00600840d00c040c00c2e0341a2014848010910302c06 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 682265494 1250 682264244 682264277
    0x3050408031b0f0c0d081602030f0a05070203010603110411070c0603020912150103030f0503090703121101150f080a0b0a0f060509180601051203042c191a10030b01 72
    0x6200c214104a40c0d04803019217040c65402a103401c5e0b00c10300045018880d2517140c1002134582c41000c4603540c4010380406d480201c1c52051003612203840e1701400030410251242465201148030388192031145007024403004444140e4400c0d0340b82c15600c00c2103408401d0070f04100398080e401c01001c4603013040d402c56600a1307a80d010020960341c0101d1001d091078950440c2001030034112072103222000d01904209010f0110000509042202d4100030481504401207000b1140c5241852203c1829802e11005480c0000c0d15075501d412504002d0002001030b0351201d1546d00d03103003881c40252140340c1020000f18490010f41007403000904100c0001115030703c4600082c02480c007a200510229110041207045000c20099070740900012071f4034201c0f040700301000c99134a01c0b42d4011075410441c00d0360404003140400000c0450240d00342001c401524148120400d45480c800b401d00072a800e146200308403101c284480c0361350000140604580c02e4820f40e0035806426a40480c030304000643c01202002d2 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 682266744 1250 682265494 682265497
    0xc0f070c05030d050403031e03020d06091a19090b04060e070305060316050d1401020d050705120f06060423100e0a1a070b0a0e16051003050408031b0f 66
    0x521400d045101142440c0074145071680c2d6240c1c440c18404204414808244c018416200100041c58540495180e03090210064003030b585c64580b0141c20510041628000398010f140e4041080f80c400c090742800d030f020000350000c41c0d06a90f01d00c2800d64001e01c42035a1320342000d18440b01c09030000c1000c0382d5a1210f105c0e080d104980c184002603466040c0445032405002e05040b0b80744504501c02c001d42050f0008504d1002000000c00741d00392080c0302c481118080d01074a5800e0a004010040c6280000001e0000e03404240c881d20701c0030807900041c00c0264100b0003030380a008090150b03410903041100f0f1400c0300090f064032101c03403610614001840e585844080183c000b0703540c0c031042309131803000a00c250201c02ea00100c0d010300740600d00303e42c0e607070403a01030729007203600400d1880741d40c1c482d20700800c002c000300d9902d000b1a025205d01c20100c003180d240304030f007161026500e14409850150007181145c10a0714010710500c130820203d000705540c050384411961031391402c185405010920340c1c005 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 682267994 1250 682266744 682266757
    0xb090c040b0a2613031b02010f110f01050f0103020907030e0a0201031d06150a081b04240807180b10050a020115080a05070e040c060f170906010e2d0c0f 67
    0x4e0484010500742015404202010800c032048180603ea4800ea800a040c004440110404000390344040e060001b0b405c00520a00103100c000030081e40c10001341d03070414a00d0900060307005100e070b40c0115401a2007482081903040b8400c0207845007040550044000c0c0c88006840340c10111000200301c1011000d000c070307030701030710f01602c1d040d580403101c00a100b850b8000764480d400035004001c54034800301855201d4030515108441c00924500d5600705111880035010744101e40d0b42080340082200c41f000030300b40c400c1e14488820260018842084401134801d844080c035002402000820171460007a40a0309080807280000314990290b100c0400000d0130310742c0b1142e000d42c0040303d03402c10702405001c505c2c01382c80ba0100001d850302d41600c8407914020b641c8505010010b0034180e520115108850680c5400218468119107081040c14070f581e8040070300a000c0144160760204913001007100c0384c4000f6075801e0f29501550140c0b030540380c0c41c1c10b1004200d42c81d1103104012200c40c03010388400074008c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 682269244 1250 682267994 682268011
    0x60103050c060313150609061707051309170a3005070917030702090a0c050f0d0f0c0c0302061501020a061a030a0c09060e061e0301110d0b090c040b0a26 67
    0x10047e190000200584500d54081901098601048102d086000c00d00b041a5182a40c00d10005e4441205d0354008104001c4017412580304a203810303185140e080e0003018100045c0d5640d4964a02568141511400c6505122a501540c000c54840030605400899000880c2d04081d1030b0320b0350300c00e43e02900d0340340f41624900035040010880114a8088541604499102010000d4018151003d4094400c400b550807072518003103141c403a8030403103811031003a1445070030303040c403052002090150803544039040440c003502580300000c5914908030112070403810140e005041d4802039450b0711005000b0110518083c1c618192501060b4504010103120b0078030079007002a41c03502e414000c00444d8140e0f000a98000104024491030361f45070349085200070540c48801409450b128006801002c50a029498041021071800d1103110790f984a4070038010143c496003c00d55505019a045100d03601900d0120001484440074041c403c3d440c3c3c04000d1a9852080061194900804204001100e1801303 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 682270494 1250 682269244 682269251
    0xc0308010b2109151915050d14010f0f050603012d18050d0503010303081003022101020913060f140a06030c02120c03030a06060f0c1518050c12060103050c06031315 72
    0x425460f40c03207014903401c4002003140a40d03080800051004491203005440850010300c9c1d000c114000b035005480783c02d4910002c100b2a8a5001c0c0d510103810f0031240b281c81b95290041c0d0340e07891544161184404c881c00ea54808500c00880c111b24000c6c03103100e214549081500c0302e4000002d40800640e260582c03551903ea44940c954a401410400000c2094050000084042005031600c41c51219001c003000201410740c07112503a014021700030528000d0341b0a182901450082a040d40404241c0303500ca08510020398441162544040c41850455000303448064100503141c03095011810002d29072043e00c6590014009020b240d4000111440e0190000401d0121003600384c130807000100b0807420201c01200c05041c028115960000c0c0180c00f0b0101c0c104802c0d10241d869000044580e4140210001c0d80c109092030750303481c40716040c0c00e802020180042064101c00080c0141200e91100090242a0984080c400e07284c2002e031500f20001044220b45001800114034045c8010100d074002 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 682271744 1250 682270494 682270531
    0x90501020c1c0503190e031b010b03010c171302060a030b01031805030a0f02070b040602030c0105060a0e0c0a0e0603010801090b0a1a0103090503190c0308010b210915 73
    0x60b0510381425078201c500c0840c407403658030aa0700b00090301d0f40034030815001d0010001400108004d404108030380c0350103000000786855004480c803002a102000c2c0310003004051160000e150886481c10b40c03442c0403658180e80c280b002d048008040d40e000905030200820342c811940800c44c10340003110f00d40e011a0302c503034171108103503071610800b04010280d907003541004007207885e02912407041080b20380c1000340500718903881c0b034001c002c00d00041c050020402c0d51107a4a51000303407241c10403034462100d5400c001c00f0030070703924003c0c1341c5009641da00e424061858540144d0030f05181d021201e010144a8001c507001a29905d05025500030802d140c00851000280d14148070b4a01006080c00c50b0f051915a00005080211306003511408080c203001465281508103a491030181c42d000d480b914010b8020403280542c045c0040700500d10130744070482180d0321504014180d01900100b40800c005281c1944c4403000120641604450400c09075108001c80d10102c494174042100c0744210701604846a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 682272994 1250 682271744 682271767
    0x303120b0102010c12020306010c05030c030d15141314040b0103030806092e050607110a060203090102030304030309020f18070f1e0c021305090c120c0a17030d09050102 74
    0x50140080382403000b000512107a0201a045504042c40403000c02d60100025034a03074007a85440700e04036005411a502c9464040e24581d69601100da0300b0031442c10a01080380480b00316480509840c071405054005001c448140100141451008a101c645071200d10009804a446640c055030191b40a42e21941c107606003d018a1000342500340280200d100300700d0b9110f200113405ca103c0541030321881c0b0b50210390405132a22200b40d0086075020600040c518100300ca10300d016080b460040c2d5480c1003955031024145e8490003140050b07405030704100000390001e4440d03808001072a10003000c2030041010308000c42c3c01c0300030f0f015618866200c8802808100d41e0440c0040910415600e40f000b03a84101034050b00004905038041c0e01800032910318003046581d12400180b440c40c0100342040f8625140624554440f664200b241c040d40f10703800d02050000b4045910400c010001e0004049141341c45080001008094440c00e19800b00384059941d00c0024002e00000da40180300150302d680c6000d80 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 682274244 1250 682272994 682273001
    0x60a18061d091005090601201e0d0207061b0f03020729040e060d0506130213230a02041a0301030b0a02070b13060b0d14100c090b0903011401030312 65
    0x4a0a1040300e80b10100240e03038200040c240140c0300295501c10039519000c1c0162400118014a00e0351006080200210220f0000750041c40d900349220940082802000701c1d5113030040b800e490001604122001c2c000c031401102c0c40c02c06d80c4103011300360800c5c102c40d0b11002d41d9640c12003411070058100e03a20400045e50380e4012112002d50441c501040c020170764508103000d00c980e100d0340011034001c2001481e2541d801910710310709a00541075030841d103011844411140c1090404a100e0090100501003154151240c0c4c2c13030700348540c00030700d85100d905105401d640b5030003407016441c01e0f02040045240000b0004020614007441800741d03e139411442c048212400041104d0410351040c00f4140201e000403846c00e400601004041500001906141c8064143c2c011040d40004401151001704401019800a0324140c101901c04014402070484255141701141000103a9106018001080010700038000104002c00024500c0c40041c007102c9440003d074829004a40355840c50305a0182502 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 682275494 1250 682274244 682274297
    0x210c03241d1e04120822020111011d070609060203091c110a080f06150906190506030c09030607090302210106180204080706050a0f05031810020d0f090f02060a1806 72
    0x1144040c0082a0000206c0d980c5802e40181c104142c0740210701444400b940062024590507050f9400d60403403000d565614074051103110006000201e002a400340b02009030f0740d041c14014255807140405c56034241c3c00010000b42504c419510300c9040c10180d403039008040040003880c01038944c440c5100b290a003820f500511001100307080380c6451a0307960721011080ea0056046030402199141ca6050305410b0314207801140c1c11910020502a0707401114010b80b89941e030071021692940d840200455482ca41488002d4020000c1d4008110800c0d5205c0d541c9803003081c0e20000509036540341c407600319966488070200d02c0c8590004080c000c220303003031100102400c414180b0510b4561515802411001f0b0026038904103c00030000c071700c15911039840b0200002014084031700b4100300304924030081d030029058440c41440c1c02604a203a4804c1d000d494155a042008140301c09010317001e0104651211070780108100c009072040400482c00a401000742045e9030f01c22401c3e400a50f9400704514500 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 682276744 1250 682275494 682275511
    0x1207020c0312130b0a120c170606090a090b06071b030507080303010e060d0c090e07050109080d02120304080c0f060717060907210c03241d1e041208 65
    0x41001c400c10854001586040301c0810101030395407540084102d03411b01e95402e03402d101c0d90a040d4445e043d2a80006c1b04a020542900e583c0c100c1c0d01c400c02000000d104100381182c001c800ea080400c200c05032640308c00710001c009080c12f0310340307240395a8002500c2c072500b140780e122503d00f12051052280401c0204082c02e0360000462840d41800185101701400515803842170148813188010071911009210003030503401c10912003252418029034640c00a0300030329000400c0e20300000342d5408000350400c1068059005418610710741d01005001d54001031080d98245420800384603100d8041180900703003507502c00030301520706100100601d4a105020941184400d0300c05009003030390340510321500503051b418400303221021035019021030742244091006051910a100f0542c5800d0341151030306400c000a00d90520504000c8070702c10520358040d1000f01a0140c84c0c050600e8007851045801c070b10762180f141070403000081004020b190440f000c40306421810490b14007150811034090308800303203 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 682277994 1250 682276744 682276747
    0x4030212070c3f0503130311100302040b04030f02180c07060b04020a0806120703080c1e07083403031d0108090d0c0c1505090a09060e011203051207020c0312 69
    0x1030341c0d15000c441022400b21031480c01c2c40640340f0400c10100100e5045030009588840f10f01e56a051103950300f030a41400a008980304406000304c140320f4402c80702030316000c001342400c00d803d64440303040021805a04a03048110f80300b40c07601c84800076845910400c0718044003951500c01d460030310242d40c3c10110f180d016500520030a01500e1b00401e2950780302100351240f00d50300c40803880783c503c0e000c5181d0000d00161400982030311500004119805d410101071005080c194000d101c16076190602d1103030140d41c0d0801910300b201d03c2c0030040c101d82045c45002d1480c4a0348410034541c1300700c11003644110b0108065056003020844ca6620007400103009091440703903840c00f200081d8440004903c688200112003000340200112040410701815810004103070304000c00b10081c00c80d51151590fa441006100d1001640e1a07490141c10700740c814040b405451030b40307800186415012013507c200c080c00740a00062440f5428060054496035103a0f0013001030510000615050000011b12501d41000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 682279244 1250 682277994 682278059
    0x510060507110d06021c0b100809061321090e15030604060203070216352e1514010507030c1b081501061403060d060504030212070c 58
    0x746180b904480c1c0b007541d0100506040b4507004000f071080443c844807040610210351600e070000c1d4020501c8103002c0c0c0701c40022815800042e6080982291000d00315130110b000100e81800250000380501d208808012171240700103d01c44101044048400c00684800f8042268a102c82000794201c1c603808228401100c101001c252908001040544800e400101041000380b00b040000340a00140c021010100d0f110000b6815428110141e8100c0d400100d505000c0c42151040c280348690248004010b10b800c4954121040d0840019111460a4690700b900c4141041e015242400c002c122040340030030704200ca403182030250444075504008003403280000182c3c2150303030b407076032030780c0000326004420b128090b0601507840e180c2061485018001d11000c0e405d41540e1200c2c103031422a03c0d000d1003e0041c0171503030075a0108030307100e940c0684c107640200042450346d0700c00360300705000344184c40101010504200702584815070807504a90515010400c065211070a111012400031109885e543c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 682280494 1250 682279244 682279253
    0x3030f1a0904020d030917060615030105010206070c050a060f0203090d02030a090b0f04050a1205070503061501080403020c03060c1804180b09150408040e1003081902031b010510060507 81
    0x300000d01036803004e5000420300d40074002c0e00d00100f40002c41d09032165060150a5103900050316a1130168142051070500e07802c030300d03042d24141c13001a4014501c590702c038002101c044202c004e05407000c0c00360072031120110b2540c2c0600c05c0780a0030a1405a0340e070500751417052078810b40140c1101150002d2088801c083d6001810310100d581c410f400c0740c0c90781541d40b440005849039034030260f800b9140c1140001c09038500c51400310f50310300030401d03030700d1095941c814140c403601c0450b00710303040c0201117020401d01c1d070041000a81103070003441221602e2003141c010a02d043c4c02540c81c441484804550201c03590b0190041030a5183d09a03801d2110700040e80071141c456255000080c804100040003a817801d0b02000311041c2d218410f40809030f941054201844241d01500906462000c2280010540c01c040c1c8080d074112640003000c40e01c4c1910040e00c4100d003400e6281c180341180410400500400c10161514011800c0b00c0000941801c00c4040b80700c404841e54011814080144058030204 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 682281744 1250 682280494 682280509
    0xc1b170708190c110108090714010e090f010608011a04062115050328080705160b0909250503060a0f0b0a08010f03051b01050f03091506030109021c020117010303030f1a 74
    0x1e27200906200d40c800161340c010f0300d104101300e013440d402844540400400a41916545049802586445100e80d803200c821503054030300b4540701100d040040100b0010715104200fa0300e0f020404001400c0707210030800411003a6941000040b50842101206020790300e81803000005001045a8110040c2080003101a42c10259080580500b802240440601c14148040c1c001c904000d00d908940381d8540303201014076000200403a0060b840c0c4000201402c0d0340c070041541925031200d0104440340c0d120381c22030b0143d000612580d045600c540000070110210800d41000e08070001003c1e0301c03481c4c60780700280030400580c0415084011020200b002c03e4011608441e00c03880c00d400306801c0e45e04c000c0145c5039841030b24000e00500400004101c01c80b1800b0a08400c0000c0c40070030500d0a0320382b03004060903250441c10103540440384511040722490618010b4000f248103051280f084074000c0c00782c1d90700a00903802035004c241c4583c44051006441e210300c9035641444044510510003080115105 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 682282994 1250 682281744 682281749
    0x3070b0411030109051005070906030c0804260711030105131a090102091e0a08060c3009060406230f1f06030c1b170708190c1101080907 60
    0x480c1c490303481e140090700c080d00410021604681103a20401c0d4626158005280803103010000402414020512921901414070120072603562460b5039105c070340300d0014038401c12030b50041402c83c51b05c52144220b0030001401c0c0b001c0c001e02030800b83d04c40302424503081d100010055110125a210b801e03001940596446405464418440769590360740a41d8500a1242d0034841d40c1c01805000501e4140d80000c000d607404a07800c0d100b800e04a640c500312950342d00c6055800980044061085695810702d455242c0026000003064091108880e1901040c411058a262555410003020002401100d005118051864450041002c1254001030303003001c101401210900003100d02098080041c40382c0c900714850814508400956500405030041c400c0c00c44140104401202d40c0c000f46008001d003503c4160003401122403600462400202640403030411100410103202403d03e07250a4070460021030202e444109025159080000400034a0171030300707042019040c20804190004a401e004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 682284244 1250 682282994 682283003
    0x91e0308070b0405010608011409160b04050f180109020c0712210e2d0102060108190807060f020702010e1f0305070e0409120e1e01050315060309010504021203070b04 73
    0x86030f111031620300e01500d0a6400410158280034074800b01e031010078a614020503a02044904840e003461401c2844125440f54041c4600103100c10400c90070141c0f8028a088001000c2c40107e1440d5039001d8800003080c0c001e60081a404540d0074406c500070070010703002c7d0800c0e8281e41c0c10155282e644c0c0044206500e02603241420080d050b05906018215102a442c40140366140142e800701c0d01c10f1107003000d54400880c2a0f0901c2c9449803a50012130194161003441000c0c01c001084a0b5407281d40c810000401c443c5040100040008100f9600c54007070405c003c1540503942d04924000100700904c44450031b8422a203040c3c02c1480c140e000c658119113105a800c011502c0d1307452840907500c001165680942050a010070070080040707007501410282d001e80c644118032a20b801c00d00070100000c1e581c40d0b0380624125130741b03903c1d58020703809113074014440d49030800321014139400b00b0700701d40080d9110001e6a455106100c110f140403c00c00014a10450046081200d151200216808084e00c044c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 682285494 1250 682284244 682284263
    0x3080d0515060c0d21020304050d0e1002070302060c0c03120904110405011e02030405030d1101180305030a27151103060d0311010b120d300b1f091e030807 68
    0x140010305c0d5800402070415404086440b842d00d801d0098481350443c110000041240681e210785203000751040200d9143c0742c0c010700402c1e00b558244012580b10740240c0c520f5108544000035203a408210b402180e5000700d04007911103040c60140419121401010034402030b05120500040c0d038000201e91000306410304500850300030100503811885603410458250052403a86006150041242c580488900e0000c00c07100400740c076880c0110307040302c1c0001c00062003080400c4182000b5000042078540500355100030040e40007010302c001284020444030030380000e4030100011560700c41c114420b884241083d01e1840c00c00006800c0c040c00c0a401400e000610701000c411280c01d6009030082c1001401150318509000211a600d0300350328600790015140c00d01c84514015004400c02402c109410350304001801d924052010342070701150f1503008480c510940d0210348508042e81300c00e0182d6101c11060324103141a0700902c031a0f1035100c0003e010390b0701c0104001000030044401040d0003a681e40b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 682286744 1250 682285494 682285517
    0x1503060803130e0c070c0f030b07030501060e06090112020336030f0a03113c041e05060d0902030624010309050f0105040606140f150f0c030a020607030f051005060c010603080d0515060c0d 82
    0x5030f6040b580111a105c003548080104034990340180700d440e001c20f02c50b404280d6c044a00500101c1c0030388070300d510081d80360401d0080e600c0c0110760402800e4622140cac140440e2481c1c03051541803a54000e68014160303443c5d200101d20108030100d0400b400f0807420030040607401100f0030000800d11851144508044900c480a2000402e0f0300c143c20240600802403561260302c940300078042e0016007000da12074050b160114928010f0804201e00000920500a08003d00000154010801200199114040c5108200d440603080c49211312551180000007030315803c12529003c000740040a0700d00402c94039181e1801a510b00d85403010306800c000365076654035210990f50809001d2034500402e039220105500b8000354002c52400c0c802d00c0361303a0782000107413050004a0181d0300255814001ea0302407110601071407e00e1001040da4a403000e0021940907541c1d564101254040d082c181d092740d9a401c05d01c02016a440309811000c80c040385c00c5414841107080007900c584078445c555041c400001e82d01c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 682287994 1250 682286744 682286747
    0x9230d031b023d020a1715040f0e0109030314010b070302031815130513090f0f1707050a150c0819151503060803130e0c070c0f030b07030501060e060901 67
    0x403d8040e1000090030503d00075041e407030340c0c0690815010358022424003060400101380c4030b9200c9200d0b642c0181030340c09141040c010f0200400080900013456501c5442a05000c0824095111030038400e580004164440484040d10100181c04c01c1c46450380410102c4003099000090301c182c000d41148004491600c0000580c40151990045540c48000314a000c1e54102402c4a141100c005950414950040f00f403030004507419440c00510040184850002280d0380c2400d07442990701c40c840c2104090500c2e15502516000010209c0d8580d00c054200b00c10071040b520321510454002c5800d21040410380000f0304041002000b105156039449241c910350340094107c0385e03500110f41c009602058461901c5220f00b00013040c4500441c1c00c2c810b0000f003200b400021079041ca0762020f0702c1042241056000c4590340c501402c00600c2074070911003200441c400c103601d40300410000d03c41c5a0603501c0c500e02000e070010014000c0023030502c1d01c00100911a0092110b1320728500854440e952040c07207400 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 682289244 1250 682287994 682288063
    0x118050105032413051516020601060909050a11030c07022e0c03050f0409022709060607060b13050402031009110f0112050a0501061706030d0309230d031b02 69
    0xb81c200d22606c811003c510b08482e110b00d01038181850410701905d0055826641c415083c801c031f80000e408040d04010043c2c282e8083c98220a00d2a03001c20038501c1d40d0086031b800c0e041078030321076082c40e00010100110301e4566000280c5400c440304040c2446068810304080740305501034a8240201c0d10b4100040502c00e10032503042c2400b0000e060784580e140d2111000942280c5c04004000b0821a5a030341c01c400068514801400010034000040c0c3e112402d205841e002208100d0b809030b119440311001d85d0b035101e4024001c01e0144800034083ca010b004061400003110060030000d4a0410310201050304201140e12005080c0d41c414040c10740080103d032800c1881c81c00e640c04c0352801c0b06103c030b4880c858200314100d032800d984c2c803205208002c2c0100013103102692003651581c00401da01d080c0701d00a0300140307481805110b180c00405000400010b21048a4151621640155609010710b03501445034000041c3c8218112888140c04d4102944e500604d4207141080300440c00d500d00380c0c100c0c200 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 682290494 1250 682289244 682289281
    0x103110d080409020f1222150608011406100c0b0610051b0610270906110309030307120506060d093807180308070201140301180501050324 61
    0x3c008664403c00141000d48642103240c1900c0582c6d85c0740041441c111600c1514443c0c0080d0040000c01060031f9502c00080f160f070038103c1042c2c0ca0b21031b0000a5020030a10890b0400b510071000c8580c180ba16408002620407801d0300c3c00240540f80421f080811006040a548210103880d9121166001942075656000301c2d041031606000386640301e020560f0202d140c90040d220072080b103200580b5100c40c000280c0d100004c41d84601040c080c1004083d64070f4003d50071882c0911070000c2c1035070b0b401d0307145003183e8812134003003506600000c10300a0456010805404000030b0120401003030030080006601c603c03030a0b1000c6031850311a4944400d11011a28038181068180b82c12641e45140e086000700d0a140109101038044401002844c02c50080f003100b50500c41c0300c40c0d8504117505542c2d03244444d030401c690613070420690400c03003240c03003c1810095020f01000011144030708280b01a00d4260350058005d180260450f80d0f00d01d1004440b2040440080503910b514645651303402c91850b610710760388 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 682291744 1250 682290494 682290509
    0x321020705010c120e15060d060615021b060406270f090f0207050706260705030109181101050c01110f1306020d05031603200a170103110d0804 63
    0x50303000821205500410045030380d0340315200c480c183c43c0c6618007207503030b9415007000c0c1c0d8104111401007601c08019256201c48010144280c4400607200c4400b12030580c0c01c41c110a052040b8940042a01017118000c001c00c6862011458a54500424954011480764509104510444808162100452404415440d011104000ea0302d00000903070111601c210a151480c007410861400080d000302c0f101d864008005202d007a00c1d1405c125030084100401d88004240c0e801142245480d0001e420700505407503807503035187d504100d400f100300d800d080290a01a02e00c4124070000840d4a2074460f038486003401c015407241d11040486014001054120b180c0c07450000f841c141c04501c1c0c4000e030034a400d41400040c50951100d1040c0e82d40c5040030192004124180000707240c012010203103003410031452401107400444c00a6803000020803614502c0310310408660115501d03803185407128541105890307408554503503100e41a9045480311150b0203025050309074802d100d000c00c111001085078 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 682292994 1250 682291744 682291747
    0x2120d0b1914040212010e090a06140415050403120209031203100f050909151e0405070302030f1b0402070602071b030209060a06050313020a05030a03020a061b050403032102 76
    0x600c1c081482000d60069044010030181c0540380e5040c42c1c8252100ca440182d5503c60a07400d0146940d400c060003400d10100384a02c0000b00c0001d4051301402d251030348900e01c91744c2035042c10b160620f2054403007442d81e00740e00d16107000c000c0844d9021000985c1590100c01c010307035a5440b00d011a08000842001620b401000414001d400310b8400350385080ba1081020300e0511502c1e40c04004154500361858105a48039203610b510051300b204445c0d4000200c0c1e49100040c0302a000021810b80c41241c0a070b4440d04491000c2096007410710950141030184000391130b4403060f140d02240304010800955000710b07030105000c000c00403030340c0c11640b925400c80b1035205000408562305c2120003041c00100e0040080401150113814805290b130240c490903242c550942d9030b0329682d105001503149090ba403000d03a02c50700143e01d881c1800382001050196001d4003800d10385061a106490b5500700c4c0c041d1381d01c068080c100e00d0540c8001034400f9680e0501e001c80002c07000b0000341c104440441114600d1910 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 682294244 1250 682292994 682293019
    0x50d020406110c03070308040b2104030203070501141e060a03050f070906050402041401180510120605150715240303180308030c2802150c040602120d0b 67
    0x2000348507031607840114001c64034041603030f0301072588030b41103440002c044440500c0244101c090040292a40d8030602900040e100820546007002110a99094016030070000d522014024280a8110315554849a401c0a42040300c0c940700c00291400301c03042441000c0c40841d00c15030350b0300c880c68011b640100c2120744c11503e0110041d180c0d2080e106000c4424903111000403a82018001d40f011a035034803401404060448005440c0c40504882d444074200c07644c84045090399580c220304602d034000340d8600f00f2450406403000308441054111501c20703001854a0032084801004460b045503200790341c8040c0f40312100804010700b03a83d07003008120407215203911044503814007000c81103074065510040140f8842401200318841c600014100392001c00004822141c1c2c01300804d0410300a00c1d0360026034144100c080c5441170400610801038000045100b804100c01f00c410360464005003074103107450310b042d40c0a0740e030300400417810481d070f0300100c2d11a2003001198800b61107140e024281859451 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 682295494 1250 682294244 682294247
    0x4050316050a3c030f0c0501020d051f1d010303050f07120503101e03060e0c0402030a0b090105090f0601030507090e16120207110f04060b0f09030106050f010c12050d020406 76
    0x158101000f83d001000106019080c4140c4501041d05a1102020362041c140111040441001c00303840395034080000381c95900062040b00d00c1840c0511160808020001d200030300066240e0090071400c03034041c1d44020180002040b01c0c1100c1d41400d10a581c1c000f450031180c901e005608000c0c00c0035000c00c88404c4010b0f080b80003144228502c01c0206483c6446804500d510b00c030944411941d50010002400010310562002108564801c120b400c9498414006010b0340d0044903036a007031a03200c200c214101e051102d942c50141c901101c040c030840c030f0961209640110f0050080e810540c440000c243c0d054014490300008e4208540041e81c60301c2d03c10b4003110031800405042001490000e0144c01d030040601c2aa2412a8464080c100015100080107000c401c803114541c1d02c1542c031100001d00030701c040018050700404240a0340c6842480d8105400c503011540310034062003502c0500300450303911512462400d680310b0140b159802d00003200721224028000d100f1546880020003103580f5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 682296744 1250 682295494 682295543
    0xd0507060f080f070804171b0a15020913090f0602030f0414010b060d09082505011a0a1503140c0d110405010f0f051c020a08070804050316050a 63
    0x81c07900c0350311580d118002004510042220008001210a00800d0000d550181c85038002c048a9002070300705401d809900c103c0b2511050810030980c01200200c1c01c00030b01d0b2000901c0c001140008508041940022441c0005030307142c40401940c0e2425070404120307075a00064021500013808644a2034107100070001180182c5042d60b0017010054107400ca403c0c1400b40d00207464000d0081400c081d40e1102c2c0034040d212a1400701e410300001c3c0700c280e12441c010039440c8590b848404030840000c089042c02421902d21221040304078030000c180c1951515010341903000c81d08000d02c080080068040e04800402c050f5125a0b1115542414091650322100142039180342c0440b080180d42a045183c01c0288680e229950110b0f00302c101440b083c500842881200c9a002d04200340740019101000ca09070354036650508600d5404107807140000d07440300f9020361040c01824101c0e11402c05448035a03076401500106a400d103489400d0b40100f0806001003104282c0c0224032004401c50451650440c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 682297994 1250 682296744 682296767
    0x13080301170a0f1a15060d02071115091005120621060c040f050402030610050702120601081006050102010216060f02090a1706060904030f2d0f0f0e0603150d050706 72
    0x62003010000b040202c0d0048003481174888000b05140e02d400008031400020350030204d4195083d03243d81c0c4100c007150b240d600c081c0c07116090300c0c1c000315603540340340c410001c0c0303a140c241d405030070464148514842c4150403000c05400000895105280540d035203001d003210070401e5038043c0e840c05020140504520188050015511030041c0c50641381d80f41c0c000c0c04100c2c04100c034559801002c5030414142c2034040d00013040c2d1a4009003501d800360000145452501c0c000b0f030701803d5154001040c03111003841501c180300180000348001d5140c01c025203032201529100b49405080140c2e144107450048034503604882807400041c140946050b81d503c0e01c00000c0c0304d20a00020940940c0002424928080c000580700d940c0c1606c03458414442d4401c100c0341c03516030b240304500c1040c103c6504900414811101c21400d032980c1d8807110700e080d540360005c000b000d00c1e9640700c051240100c0c0c0350307440ea91b83c2000d0302d034804900c40d510b08422914400091410021000290503401098070103d00c0c581d100010101 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 682299244 1250 682297994 682298033
    0x30a02010f110c0703020d0807020d030e03190b0f091f060f080106030201050d0b0307120818030601080304140a0b2d130e15061305010813080301170a0f 67
    0x4074412142c410909201e00c3c12120705980044030148018a00700102880c041c0c052070130103040c14941d0b4045201d903d00540c0540105001802c450100d1408020404418000c00110381e800c1d0156038031841049005007205201c1842c401c000340f035500e4100400c000c020120080200c107030703900d0246100103108900440000d400c4000c03006c152a60140519021a58103a5510789800b8012461600500001c1003603a07050280700b400058080d9030b40c41400b0454040c11085907514100701910307070402503460506000303070445001001041c03800300c29241200c04117241d06001c0b40e01480090034890380da4000812200000c55590340c901401c00c0b5602c03000c081d01e84601c3e400391801c04078a1980c0104124500c85a1407480c0c10300494100d4080580c12091941c0092484011131001031800d402400460300e072803442d014100081d6030310900003030304005041c1118181400384d0b22459454401400741e0102a0521915900703141c0b0304000c2a5030301500f001003845081158601181842501003142d007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 682300494 1250 682299244 682299251
    0x306090506060a0c03090e0a0615090612090f1e052a040b060909161205040f0b07090b070503040e09030c060601140c01090f02011407030c0f02060705030a02010f 71
    0x621000500c100d5000e900d009141e01d043c0050b096040303e003500080b0f011400c00c815000002050709104851a01803001c9842c082401420940b00d41103814040042c4400c101500c00308100c0603800030040d1600c6426070303502050880250510420610706800000c0c1400428803440a55200104082c80110301c50426202c80b9803101d2080310f40071144080f01140381840700042c0b181442c1039480503d540402510b010f0800d5110800652122002c855140c0702144510b05003034a1a40420741d4020140b5124042119040a03190f541d1603d41c04000200600e81c400b000c240781d2405849140020140c072016259512800c0c070388217890390018407a00c40e0b0401c0405c0800d210fa40701106840d01400725000403c0784d50b490400449503480c4611949003840010880c860081500380202540c1c5070003880c2c850750300b10340c610005000c0550f640b0203181140080c4a90800207a025030101d0b81940c00000d1100c01e20b10500008400d03219082c0001d00c5c510001500d00a40c1d501900441c110300b03180c001c200f = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 682301744 1250 682300494 682300499
    0x103060e0709060c061811010e060a0c08070816030903212708031323030a06021c0f0b1302030907271817070c27110a0306 54
    0x2540002810384001c00410784580c018802d59201e03168a8040c24016000421944090f0f044031603408000c04064076031031030f00b084090465800501c0000003210a0b181c2602c0d14103009402060038503d50360051500d1000203081c4103007e85001661071850301c0d001d00040c0c1c0100c51034041d02d0305c10544800c175000f001e481142140c0a20071520100c07210749681360b441c40b861490350b24091281f10030507074520041c1c8e203050207d04c03100c042000d890f00380d60f904000380440703043c180d40700307250024100c41d040484207038482c07207415840224440d44261703072254015031580c1000c0e11001c820500d101d148010103181008244411160fa0001500f104054811103484114180e0300c41c1a44400ca81d52540385d880802c08100c0e4068100f081c60760700a40300d048591002c01a411b0a00391941d5440520b0755444104031a0180070078030051082c10a55400a24603001d040d074bc42c0048210144585001181d0310210140000466034540c8080d0280301c0d03080044500a2032158256000b0030800c2000a1401901 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 682302994 1250 682301744 682301759
    0x11060a05040206090f12030a03090302010f0e15130b0c0a0305090d0f1d04050903031b07030e01050307050c072c2502030c01050108010207060c0e01141803100506010306 74
    0xd5a0007140c001c1c102e24503001032041800104102015a00d03041210020303000208242440a000000220340d00032540c810a818028213546005c1c5251004c03a15204455841002c0000d010410b007850170240852990b941003001c060703100c585c90207450b444048007000b00d606030200040000a1b100c4e1010841502c0d030701c071500c0d50307418241d20900104a4504411081500a400c21011010804111491160480302060a48500340c4501c00d4680c800710504c00600d03c00d83d2180d61081d0031915641c200704503510001c0c01d00c070310003100034103101000021503c42c1d88150122400c110f010707011203241c155038108904038032078140d002d0404180b00b0340140200c1c0100d0b03106503008a807002c0c1901d8050400d0300342010902c1d05041d820040d07210802c84018001c20a028550007001c2c40000143c5a2006041400503210340048100800caa9481c00050680e040085c003d0410616418141c5032000010440c0120150741e0480e5407501c1582c0485100520941095109160aa0301802883c2e60340d902c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 682304244 1250 682302994 682303001
    0x605070f1d030a140c0a050303190302090d050a0f05060106141801030b1002010b030606060a02030d0b06090303040902040911090d030e060d0915060618060c140d11060a 74
    0x210680040e80420070445240310380811803008081c01001e5030003a4041c0d03681c80101010b0407080c02010303004402c1c01900c901c2e000e042d02c0d005207010740c0518a05a851058024060403480c03210f0145503000ca044503031600c81e01601da99003079010301183c3e01c00089051040301c002801c013044619108660001c16442c0c80303000030f41520303060001d80c039040a20040045100c1300c19914540d0415942d096005c2080e502d40510000c0100c443c3c00008224011b1814103041410051005018450401c070211200c2e60000440c1c1410000e500000f0b0380060441c00500588144c992169042c80049800b0901802e16801002111000c1c00c04118017010f02010610b03501844c01801d91118031680303440d000ca4018101d4510350100140002e280200700303015901100c1458000356507600600d4822180a049032061402605107400e046445030000003443e45400b080b4003400c000c125200c0308450030007400030488084101c180040c1d4401c08441980103005504142c0e0700c403020b00c00d0101141c0c10311500d00c07 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 682305494 1250 682304244 682304267
    0x50a061b0c06020309150c130b1602100c1401242904120f050d09032109030501142d07141225020f0304050d03090b0301080a060507 58
    0x100d07001401d05041d1a0000250402421010580103201d180884c1680580d161403142c40244503151b120b00524001442d07140842e004040910410401c03006140244102840c0c0d241c1d0455061124450710302e4110b41c00b07020810f006110408a43d000b585001c419007001006c4c0703103200c1112803584800216134810410358800c2881c01120302c1c0000c0c0c41c10080918040f25540303151100e5151540e90040340720480343d60320040d503403000c968041808200083c81003010402e050b2401d01d602a045840c0d407810f1308407418000031840303d03094503182414000d0302840020354018000300a80e240c00d030030a9041c0541100d15166020b02404e03461034001307000300301c5054500840200b5015075a8224103850700940b1503660340c010711003405408000c1544d000300c0c611920b500f0403840942400348540c00000050501081c0554204181012505000009450403a88125503d00920125007402e4071000800d40001001000c000004903c00000040045c1c420388074034010081581ca124040b100990000c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 682306744 1250 682305494 682305497
    0x20c0619180b0a0b010513120303050f0421030f2901020d021b1c03090519060503060603040602120f0124080612010f140105030d0905030a08180607050a061b 69
    0x30002c5140d60b03003564403001d03810300c06051587c40c02080074000340c0d00300c1242d400b07201d0104400d00c00c2030030154140110f40d0010031303241c0c01104a0501c0d9651010701584080000c040032030102183d0b003641d00c60741003440100c00e0310320108120000041c3e0701c4030350b0018090b85c0302d802c0e101006a240651000406240a40040e4040c11102c1d0381001c07008400204000c0070350b230050102c81c40ea031051a0410000a40620030780324400420b24080a100d562802c50300e04420100341c949082180540003030842c2d900c00300483e1042d944e9038032807a003000203004202d1a001344a41d0f101c01c1006010008440c05e050328032200c80c80001300211050103c644d104507202d203001542c510301040442c02d04c01c40350b41a039001d034400400e082c0304004440c03003120340103203a40074400c580c9001040581070502003103c01002070f2500304a00350030300c00802e96821600302d0052002c039000607001d40c590f031041c6c3c10045c8000c00038900350b82c0d16024140503507100c0b02c0810a94496182061000d0a080341074800c0c04040004d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 682307994 1250 682306744 682306763
    0x30421050304061803060e0312070302090d11150a0801030506061c02060c0f030c07050a09020c0d080c09061215100206010b1b07030c060f08060612040303020c061918 73
    0x1020021110134080100713100c50301000f0305001c0006059406905003546c6200000c54880c02d0a00032900c0c3d01c20050030000516104120120380e80e00c82c14a6070501e55004841e00302d01848803400f04000075529820202076850114105900e030391f0010000e1b0480340510120b90650701c500d001c001807181c801e004050400e10f804003690050070b009015198814461007500d41e80c102900d010390866001000d803000b85e400101040c0000e01d040d80e8400080d050101c81103040001103040c080c1d892540c4404041400441d10000f22a26034039400ca032010100504026141c41049212081e0160242c503448001524940c0181c5c01d41001184900c0303000c20b960052601d43d1802c546140b0b103a01070107407800e240a80f05a9840040c40401c00c4000a5109100300c8211030700d0719100605092030306103100304009074641440442d039a80e006442c414128914119500d450710300d8241c00901c1004010181d41c06900c0c100804851310080301d10300301444050500501030759140c12480310542d030900a246500 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 682309244 1250 682307994 682307999
    0x3020303190e06011a0d140108101401140a03081305180714030711011b02060f07090302100e030a060e0705060913020d0b0603010806010312090b0706050603010b040e030421050304 79
    0x3156540408035841e1009001d06e0b04c00c1d203646000c00d41f002d00941201080090f001000003800800c000d61a0602ca03038030404c200b00e103000c01a0ba41000c107214400740d0103c0041d0140481e503404040070700440d40803a00c030360340d641340780750b4484516a0f92081c1c3e40b080c0e105603001c400301841c1d00c86c0303203200745480d0b0703601c0900646100c01c065a50704040c05200410100d00480a070b16070b400d00c680e03a145d43c00341328951101800d00030024600b00e0020301001050700440c06000e001c5030049103110660380d04403201c1c1603d9281c0c0c10101c0f030000017540440e03414401d25a4440a00185600c4070102c017030f580d03094031600758039203060010b248110b009458006062440414402115501408002900c0d501c041003000b18200000c900380c200381c01081c240d400000c0104100700060b00d0725240b0341440c3c18003a0b111031514003991410700803000007034012a00d40001074126642035201d0895070b003000b00700b08819544810243c1d660b0300180200c0c0d200b2103200c010f40101500c0c00080c1d16149521900840c41d1a0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 682310494 1250 682309244 682309259
    0x304260105180c280803040503060601020a021e01050f03070f030e0102040506040b090409050f06070f140d0c0e04060902040825170109170a0f0c05060115051603020303190e0601 78
    0x80c4c50300d054003d0b040da41100408018285280703a070090a03540010f5444504181c10581807040c050100c50555112803201001a02c4d2510030a107002d100000a88124090400682c1c1c14815440c480341c1b00e2100200f04850107401c150580b4148240396020403030018030420341400c074840e5000b6150300c6201400100b0000000b10005c3c014810042d00104e0195240e5030780310700c0c0071100b0490981c40d4214508001da110350040352000c48089a140050700c00c404012203041c107120f40000a0161601c400c0a00201402030b550146d010001410802c0510343d900c2c1c5c0d01c0c00a4129018541460084400724114500c00a60300c0641424001c03203444040e10300310b050420301e0441040011f040d503e801000e00818001042c00b10b04298070101140e54581d02500280884c105d002c0c80000e000c0c264940304082140011494107540c1ca410241c215428046025210350143c802106807410140e9401d000b0142d02202450080d078090310704541440d85615940c0641e60f41c00001c001e20b40c0840c3c0100500c4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 682311744 1250 682310494 682310509
    0xc2105040803190914010917030f01060e04090c170706110316050a06090c03060b030303190e120318301608180909010e1e0304260105180c 61
    0x140804002101310140d61004070300d00501c001104181d40d1450360005220701c200d000c0e045041660507003448d45c0b0380600314004105041c000e403801c10101207980001b548a561208440365000008030f491a590741c0d4400d100380e40c0a080c0b443c0c00d030040910000d203031401040300400d00300c0c0d9000558141012003850031041903030060180c3e5180301c1c04440d40c021496900c034a4286074000c28162081c20309500b804015214000c4800d4001da0080040210407114482210b810448100340401d544a240302058604200e030b4079501c90615000081c00400045010000c0c030300d94001058940001408200f0010322028100a01c0c00c01c2505004240000707800300100800c50340d542c4119440c44454848100b190013240400040b041c0c0001030217201c0c40c05c0104640e0102501000b401070640d01104191101d105461005443c0c1d115410412009000e00540c1c1c09030a48031083c0740121144c00000c040100c007110000c0b525443c2c078011507181084a00b0040039049400d004000d14016041032200c0c0c03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 682312994 1250 682311744 682311781
    0xe041a062b05070207172d030a03050402090a0c0f030c05041a0c011a0105040e0a06091407030e030301031a0601111b0f0d0c0e190c2105040803 63
    0x500d000c00008034500000e100c001c5110040d8007500041c14500890003928202080d041a95800000440e814960000060b0090764400081700814603134002c3ca58a251905880d10b00b882d607000200d02c9002c501d03415880305104034001c940351030381502d41c040c003003040b01e003240c003540c1c00142c1c059440801c6a00a402c05403944401c0e2900da86420380d01c48039144004111b4000c51824000014a00848030090140e82980040c455409000ca0b29440011f8035034821885181c40352106100050501310840c0e004138010030340396805025820300a009030190010031074400e800301c1d160445041e500100001524180d81d4007a81c416164500ca000c407160f020801401203041050f415004000b811040c0145e40000c050514424503004076841003201c141700e031030750345c80c000c40780d1240660124807119400c03001c403829801c0c00201500d40d079104442100b910915010114106117400600c150711400c500d4510303503c00c002c0f01d00260043c0c180c6060341c0003903c0140c400351007440400c01551564048525 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 682314244 1250 682312994 682313017
    0xc1e03070e090403090815010609140301020d0c0801030506010b0406080406020304020301150605030901290f0d06020c0a0c090911010f020a06050f060f06040b030c03060402070f05010c0e041a06 85
    0x40c58601d0790005500190864044000464840d420007881204004584405844100c00c203119810000c2c0240312048510a60103074064801c0c1d0a40035403030039411100c0c41d240e5500148200001c8490140c5400340c20f100c00c480500c00c80000050301080d40c2d0556003601e485035178900701c2d42c41ea601d070b1401070740020700140da16541e24440302d004900031284520091049842d40c0e40c0f00d2800b200401e00b101d1828080e42c410f50318610200001c8686c030403039101c0200d400c85000455440075008945000c041d01c0d0000c2c480c51001400799101e1200041d595952440381810708001c81d1035104100948110070401011006440c1254099602a000d2000d080102e8412607196900d59190700d8140c9005070b030014031004049040c080242005103000001c0d45043d10110b1800e441d01419002d1032000401f0130716420000700110b121607407290120b442094004031900394074002030070110700a103020700c40803001c500035420f200c2040c1420b01400885080d05005a60140882c50a2041c980c0c4060065035 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 682315494 1250 682314244 682314257
    0x1113290d0219020a03020d03090f02040504050c130213050414161e03061401091503110f0c0c03070e0c1c09060509070e0615180109050a1202090c1e0307 67
    0x21040095402c2906000c4415070051403100082d00b8040e003801a4000d030281050301b003400310b4020500c1010100764180e816900021582d031a82402d030b003407040089480754880d000347d84c401400903040e0040e0003103016000c08940202e0b9600e007040211090a184000346039100c1c030002d017030195503000c01d03801800141000a440a440b0740380f4020b6030f08500c04440031940d58401880040c507080401140e4807800e01304907103c41e080071030000c80e902140f18404201030712842680c3d0000204402d0398444107042e0302c4c0c10b8944050482440d294840703003003542e0080c8900f0000181100c401c05101d0300400104942c10301d01341c070303100d203011210a5a1b82c00e8007100d52104e4402c07001881c2482480c0c4103d0800d00034050a80c1483c0d511688890040c000750720070704440c40002207030309400080701d03480f030189590980340f04940c000690307a00050350300080d8460227004000410808140c000303a03880748200c0e055041c40da920500d41196028003505400c10f940428a81092020040c00568102c0c0b070609128 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 682316744 1250 682315494 682315507
    0x1140c1203010f1e03170c15071e03050c1804140a050615031e1e040803060102070801020705031206011b080d0e03031b09040207061113290d02 63
    0x4030240d0003a40110f503102d4001c002007000c5120300114142c0c80c0c5041c0042d0b2480c074550b80310b26484809110802d18144400500c00c01c200e0400c2028641709801413031080356034903100744050807010303255881c01d02924002c00ba032800320b4880d224807071140c00c03801d000d982070107402d200c4440d14110902ca4075421540d20a0065031381d0580f0084148512a04030002c04c4034a010301c28003160348414140349012000a1086c4081078080d84401c00640c00f003d43c8040d4290780c1c40650341c0e000a03809500548070702008003440140102d150066126503000c0c0c0031500e40566900d5460700300e104004000d05141c20a01a480100d03803501c081d15009481490860308048038001440e0400c0a0480100ca40c000300244960455030729000708601c2c0424003007d1403e51420381c43e000e1700003100c0c020940784950000f03070303484a50390b442c2c0c11b48407110741140e410820f1120440b594071083d8800c54030f6802c03030055440001452501c03c1c0ba80d4071101e10115003036007850000e03c25601e06811070051070316195020b01c0340 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 682317994 1250 682316744 682316773
    0x901020f0c0a05070b03040f0b04060605040c0c0512040b0711041b0203030601020c0607050a0221011802090f0c04150c020d0317010e01060c1407090507090e0702070501140c 76
    0x1d80380da40165005000400010b151280c542140342c0e1004240c000103000304000304800000040c180344d0002c4d0180100d9896103030000c014581a00655480362030141d82015542e44203451b90f102c544110204d46111001002280c07141c00b8500c40c105a44808000941c0090340320261054600c10207000442d06081052108c903400d40384800950041c2d001104000003580d0400200500400548010703180c800c191b103030184c96555403e00680148217144036040c103005078005000322145140001c001b0a40c2d660380d8140440800072069200e101450003160410a26505c1280248030349607100d07283c13500c0e000c548003803042c0e0706056006011200d00315101685846000000f110300c00e68078140c010146940d20b01c81c0c040103130050032001d44038000611020750440300000301c017504045414516044050194685007240d0040c001039400c020920050030b401218036026500d400761641c0c0155900d100890b5600100e2044c3c40c00280e8203c4c2010348407800100030001c0350001015a29410002400c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 682319244 1250 682317994 682317997
    0xf0d05060112060c050901050d020a0c0c080a0203061b030412120f050a0516020d030b190602010c110a050d120e1609140112080306031005011d0711060f0901020f 71
    0x104070702c1c9000d500401410071916104901d4400303500c4c2001818070944600090580c0107020440d10001c0c3e00003800520b443c09444401b011030b80c00720409155580f03130000300342c407110000002c82c0244210404240d05250203035190302958201c503201d40c1990350f07a842d050a00c50014440d6414000744106440b464805405035403200d26034a0b070040ba2a040c1308100b0760440c4c00082c030034881c10007481d00c0c04680071380c007003030700e040c40301c003607c1d01007002a0041d0000b1032221005400e125284540c03000011803c0c1c0641080d4000c21030750300d6204242d404c0c00500c41d101e00b100703840141031350058180c045030107000320101d03e045002044d0026500d6000b8030304614001484005005496094108011020f298000e5a051510901903402103524180800c040146c4004c0c006024690200c009241510b041144008205030243c0030722a0f5655020b8081ca1103035200b81c43c00090f440c540c0095030540c02248c9000c11200404020003246d910017050fa0307a20a000b61204910355000c0211006d078092010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 682320494 1250 682319244 682319249
    0x10b0f13080109050303040b090f060a2c0a05060c070c05011b08130e10320d030e0f060426011508070e0106031503030507150518010b0103020301080307020f0d050601 73
    0x18000e694904040c180307a50407080040049e505540700b03021115084202045040c1c102c00b0301d01002c00ca66011801d4100908545401400000c0d41c0150f210404400000c9a0503240d001c1c60560714152030312203c11900c0d200380c1c0c0010300701006410b42040b065204035640811000b0b000c9240e88522004e80d10308080c0e40c0b2400d04051058007074034003845204201082c0d41d4009680b03000c8181d62915040110000901d084005604490300f800d1044501541102460040000800c50382414032503180103000b00e06600e0b10240200044020030b5141d08041040341e095031004145540c410000382d4503e17041698203001024607549511002003e201500c90a6010b0202000603000bca41072040019459405a1040e8100f6081c440300c80302030280c0c150044140c80d010b01d071095070340c242070601c466102d00b601390b0341003100c0c0790204020300503030903c1d4541c45140c030050083c00100090001142a0b00080c0620040c4d900100964001840c152881000307544028207010917041854452500780402603 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 682321744 1250 682320494 682320503
    0x18031b0e040f03090608070f111203070819140609070c0c1203110102160b0c0c15090c0a1a070213020d0b0310091e050f012f03010b0f13080109 63
    0x20340e03102e02015048500e420142c1210303d881009860720b408000c1c10b8406200c040024454524000c0040d000280104d01c8811040142075a42e418a028010301c0441d046078200701d842e8011410038510115400340006402e4510504805510b580c0304010f50180f01904002c1031142c00f04010001400c1c0404400090842c0011032a15020a003000390040c4520800c1040d40c0c2d10400c100e80454000341c4250b251a9041001d030140e50b62045054900707881280c1d8240b0071486483e242da10f000104100d00c0b0b2040d003425050760740045205042c440d03170081e0707801400145402450300302d000702c01c0701e006007107218001050703101c620204010190803a400200720b18041ea8480c5040326003400c0800c03190312007458a03c01003140c15a1912400d010705009102d071001708031203400c3e90041c081e0420103d07401540f014000c1104108400100b00c00d4940b000c13070440101400070000c4e45c1e60b0690025281203d2406121034075040e490100c20310143c3c04514081101c01040d18007040511007441401041c0703114 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 682322994 1250 682321744 682321763
    0x8061f032c010609020f030a0b060f040f060e010c050d03020c010204030b19060e0108030f0904060302031f0f02090102070902091f1d0406150c020a3318031b0e04 71
    0x41d401260035618103400207140140100a00c0d180c3c07400c054201d0354840301e07c4400160341c0825800044551194044e41a0821008a40414003141c40a0380d142102d00c80d444001c4000c08610044d5101a000300c400b5020390489034004400902130317002005100585070005241940b03941d01c1000c03403c0180d40c1072040940f1100c1180c050020303446041e0261410a940ca00150f01d0011116600d01c10303840074400c00c2001043d681c1c4252155000103024690050981e103010403840301c4044c40541805140f80003074240b42c03010f00328031800c2c821100c0400041c0d001e05003145c01d04680501941c00350480c00d80100400748241c07a003c3c00c0c4914031092404903980d22550810050912000d03000300095940724501e842000c00c01d0180029404035041000d0500b9010140280002800c250789540440340f2412007410240c807140311801c240c92990800781d0180c028850703421040700c074480940e41e01d8403004860a814004141c440c401044610007129107011440d441d010781c244041410746048500c1500d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 682324244 1250 682322994 682323071
    0x40506060c0d020f160b0a05130e0405010b090a0204080d141b060405010f0c0e090a0e03041d22200a03030e03061b0d090201020a0b100e0708061f03 65
    0xf085c4003d10171085c116803010001c6007040e95403200ea100760340c090002e00c480003e84202c0c031034100c0200c00007021a0180031180b0b140a04140740a0209610680e1150103403100113440c000d4507100b030714152604803004248074601204140c0d0040b4955256818151303080c05800c0c010050103007041c102e8030f103500185c581c83c1070074944035003074901040c0c0300c94400381001c64294200d40c0c41040b02c80140401c807001c504c075131610014040148a0803440e400680800030380032400b040d02040a03000349a18603034000d400d0f500c00c52150390211803504501c2c8050031800c6120046070400003156413019402a00e0b00d0b00011040026899140319402200880c6224841510794a02440266030048615400c000e01e2071050020514a110781d9a07a181c000b5581e88403041036910130420011250f5010385d84010900741603050315030340e81852285480000c07002e4009410603200b03440c014003c010142090051409100100040074088101d040c1050b6940c0c200c1e2100400503211050501d9103098440302890 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 682325494 1250 682324244 682324273
    0x11d120c010f03020f180402120c2d04030f05030c0706020c040c050309061603020405030a0b040507171207290f0c09010e0d0201020102090d0b060310050411040506060c0d02 76
    0x10040b054401454414003601500450031011120040762000301551040100c40009000f409160712100101404508202c240d1000c4002455a9540103041c03c001ca2031030603407540001d00c400e22010b401c44050004200184030391343c3c0c60405510450541c0d04080700c881509181100e15440180140e02c072612420307050909105030400071809152103465481d00f140074642e1080040c101044075640c0c00c421152843c0b00740d060300d010740001815600c001285041404400c00306481c1540c050240910014a0440e03402041c1480743c4114007a0400c00034012000300d0a400400041c0e8601d031742d40106040a948450b450055942d03440c12800050030074031030b9011045001040040d0486041014000c1030781c01c0005014120f5003210029242d1245100417130280c0101d440f0250401c09072803d0f8410070030516001d52240d00f00354100c0701d4034035602030744ca000d4410550b0080c2181260f5070895000341019000039038080c10141160b407604d0649180a8600f8100400c01001a045502940e03442c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 682326744 1250 682325494 682325507
    0x30515040e1b0420090907080f1906181b0302070507030f1a040f0c0522020d0b0a030f0302120702011202030621030703030b0312190c05070906140a14011d120c01 71
    0x5031403030319100c2c51600fa24a403151000140000282c000f0ac1c030310606500e00e250300150091b100074100044412040b40202c0c0c05010391a14081c0071514800248104900c07a10a5444141c4c0040c0200705071440c6840b410020910260192119101d60401442d03285403464000d000d01d1213a5540031083c0070f0307420315040012040d084036200e40c00340006c20780d00d10794241a0300301e00c00c0091001039a13946128465402000b1078981140c000c800640c0020038000c9290b241100b1500a03002d452203400401020784040c8148100280407a00d00d02c2ea8054201d49a4061640107402404540400000303844070701145c92800f2020107140c3c8002402c9040582c14007072a552028160018240c51620800d131401034010030070501c9484c40e498284100b100c0c4182e2400b003c0035003080c01c2d240c03c03940b40c05440001e0901030180d40318032030f91041251240d0a00050310760448550042145241b04080011540316452031110301244d540441b000d403844c0d9030a9618004c0700a200002d0081e24511400980078 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 682327994 1250 682326744 682326751
    0xc05130f020f09040e0c06030a02090109090608030c0f1606030c0e03150615090d020d1a10030b1503070501030b2725120921030515040e1b04200909 65
    0x442d001b401c3e829000c0d4407240240c4e07070003007403803400540ca904d900c1c40100c03800c0120390310070040349003800780008110f0404001003100f02c50040a507200c00210351180c5075954851111038642c006106010080d861095000c440f00a58610b0300204036170708003000918200d001000030300104111428441103141650302a5841ca00c805800c9041c81a0303503001505a03c0c00d150080c3c095072080b02880d08120050039107490b6140480300300c8200f42499030040c0d81c00b070321038003080b1591449103000c25920019000c041039464002002810342504000044001c0c11800c03250355084282d2202248020f80303c0395003c001e2406801300d0100724a0300750011074101a03a0a1143c4410303100c01d0704004a42e500c120710f9503800001000104504150381b5000146005101d441c50901c4505200702045a9154100c6030040c16040d0084454041140405c0101ca62503c100312156000241c0e414064030640480c0c0d040005c010b100260010b80c0007400105d00c030000f0300000c0c441900003000415881d140405580 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 682329244 1250 682327994 682328021
    0x21201080f0a03020606090903041208090109140d1716030507050105060f060403060c020a0b0a0e1c05040303030b120a030504150309080d1e020408010c09120c05130f020f0904 77
    0x44142d00c68402a444010107403400d4040c3c06003000140c03060400704215002040180813851051403a070411960b03d4128142a5000501340c1e100000d4920781c80d81c454090300001400f2031600c9220b0f50300c001c80d02c0c0c88607841c9825000c091101c1d84900091075601200f41d030182d11569230702c98640c6080c0d4210751004107010f110300f01080e89600280c507008151000d89034040d0002600d04545042645042202d0b100200f41c5070f0704a08201088500d600010f040c80415400c0320b11b20400340c94240034188804151500041c8140010000300e4440d4200c50507c0b68060002d0105104c10300e1600e091411900054012400000e820818020800707442c0070f5003000c600c0c04100c4481581e0350303010503105900f9500d00c440d403103804002a040c01d40241b0102d000c4c84220856a560361603000601a002441024002c102c1d410780c005452042d03c0300041925910041d1805092b0030401040380f1001c90801c100c4031140d0740d4040e0034812040d840100f2001d205200d0f1241c5480700042088140c070009181001c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 682330494 1250 682329244 682329253
    0x105180405090f07300f06480e18010303080702100b0a0b250c060e01140a0f020a050a0809121f020307030e100501260a1e06021201080f 60
    0x510b5417407030b031040d4540a040c500303c90061485828200540c0c207022a000d0721040c40d090610384049004554000d2504001a80f03190201e070340980d0000960380403890021042604044201741c61107540d5007030034983e0080c070302c0507020150f070a440c0303803184240c004070045021031050244082d010404030a18104c1e1102c1400036907040b10119007614000c4c800d0061044011a0040481c8800007041007039250320009100720a50070300300040b59824511400000c9003980c0b1a07059194403400d81c1c4820810485c41403440c003c00d09404842924064045c1400c40c003a103084c1a00085080c003500c0c00b864081d003811a201c0c00c0070303000c03c1018003009070b00c2207042e8000300403084100c00f01300e4074940d100307481540142c5940d45d02000b03034003030003280118002d01d014481c1e50702d401c060340307a10040c144d804941c2c184154540c80c0100484400041c800c0707003040e030b000300c07028000a00d0844000070725201c0d503038103c00d0084481d80e4007030582c0c1250f040c1c880700c1c034440c40052110b01c00c10001c81d03c03550340c00e40003803 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 682331744 1250 682330494 682330529
    0x151906051c12050c0d0e0109090c08060f150712090b0307020604060b0f030d0503041b0b0d050a09020d0b0910200c0109080a020d1205040803060105180405090f07 71
    0xd44104201481c0244060740e403140400c0101c0c01034040e680720300300420a40b03004036074061005086041e00c90a50f408618101c0340442d00000c2445009940b000903249c184a50b194403040041402482803119485026020103002c1e20003180050010300d48181c002c7c4020808010b00070301103120307980090b50385000a008024007164009203480d005600a1800074861031110041850380c03004502240c0c1600c902d80c24151500d9009005504c00c5002d210f45441c4030803d21081003c01e2700c85d109901a040040c40180300d0f403000361784404e400c224004d00c00030b076441007580860b8008140340821340d81e007039070307407003003100820050000c2134128050f12030400403440300c442d40d0001d5501240381e0201799000813032140301700c990940c800031149130040f503c1510f5000d000c00007942c032881e40440200180d40d0801c04030b43c0d00303418002c00313029a601c4542141582c1c2c0d50001102c140d00f24003240a00c00ca440624005e10740c8480c0700c1c0600440c8501c2c0507180c4100b01d01c0c07a55180100c0c0780d1200410100d8800c00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 682332994 1250 682331744 682331779
    0xd0506010c0f031206030206130f0f150f0c0f1208150a090b06040b0f0406260106080601031508011d0309030601030b10030602031f06020c0f040e15190605 68
    0xd0801e036505091100c64004e504003004020400368100940280000412500411425401c80100c40c03d010b803200740c0d04e48950302da03100da1b0802d2040805d401c140d00c181010081c01101002e05220251074114184a01a1500d03101c0403040603040d90003640104541440c5035121190603807001ca03601c0202120301504022a419841510400c110240d4400240509607540f004583c002c003101032071070b5251460240c0000d081e510610401c000318a0004400300b034040f40e4600502c0030034042c002e81d04540e28041c01503d40e00d070018102410035a4621042c90b0b810301401c4048060030004d000040c644c4585138805440b001e0032502d4180561003446803041c140e0380040c0c407030b05481e4000341c0d02c243c0b40c4900f0724880180d0040e801c000d09050000c0304002c0042124450741006058407050f01e0071460b81c4031010b9840740f00c0084041c0e004405502e0000d6a8103058000c071042c90b00d0207088400101c051700000c41c444c503040e40e94450f07c48106446a280a2650040b04083d00040310420403800040d0305 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 682334244 1250 682332994 682333013
    0xa1110180c05030607270302040504060608060f0c0f09040b04090c150507230c0306090a110909100902010e0607030306091a0306161b08030406050a0203010b09040f18080d0506010c 79
    0x104548080506c0c1c9600c1801c100880c0203900455020f032040c04142054500394002e04940d02030a00725201c3e03100040d40186402c013126000300c0c4018115441c010041c505001c171a88070003202d0390420780b035060000164a50340300744485240183e1110144c50b00345002c15440c5400d010304101004014010354010441940503400140c0643d0f42140205c80451111400c000d400780e80c8580c540120340030004462000b1842d00510751188214158028000c0108090010196102d0030315911043c4002c4140a01d035108080705030050404e0200240c1000014485a200c09000c40c0001c1d104c0c0c00c10440e062080c00b440300303e0702800101c41c40201c80d41004c2a62108010f00002e440320b031680407012118041e10034480c04081020054240e0a0141000101c69005550482e0514070385030010700e4103103041c8241c034160740a42c02c0a600d8443d0a80c104030250103107066000c0a240d81e80701da84595510704070b003000c8452007540c8440e110421005540202c940080000f070622824400080c0007404512 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 682335494 1250 682334244 682334267
    0x1c030c141c0c120e0a091a0402160506010506070309050d0510050a060f0f2103050f040b04150c32010c09030212010c080708130b0405031b120a1110180c05030607 71
    0x250001404d50485003000c80310f0707d0080c3c155400034800509400d1840189444180b943d004508480480e41d0310710078400c81e07126001000d0300040b4010030921461401c0d06105403014040c004a9001c01e8400940d20308890040c0e41c07604da550313600c54042081000c048040310062200103203043c045480d007085195140151500b1600e00e0400001600030035001d0420f5581b10500c0503451604c0d00d40f502c804a1243c0d000d4056012040306078240e840e000f5115000803041260f001d50908812149401300310340240340c2c00307440ea00e544841070802d0142d40d0240300d00155051180d8408070740c54958014054401010354041745a41d040030441801135800480c040c0d0810807600d0a04080d03134801c05000b42c07000084000078040d19036213080c0404d01a000001e003044200c0c58805003002c15550320015990031141c00300c0c82000d06d0500a1001c07070fa000f40c0221005828100540d444082c80944203401c880840c4c1c010114844800086802e00095040320405428194000d010505021030080d080c5034140 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 682336744 1250 682335494 682335509
    0x19060209011b0b0109060b091e0112141005010c030e090403051207020a02090a2d061a071b080316030e100804021c030c141c0c120e0a 59
    0x541203001e034810403540407480c1e0480c1142c81060214a0003000d0140d081c416012503600345000820074425280490b00d42c2c4000070010704240503044007803101510b542260a05012580301c5055968604d8060b641c10940003400741b8207a072800e000d24408200c0709402003030400071402d07102800640c221502e1807800d081290400b440c1d59072032404607480e114005003102c0d098010020f0014030741d00042c4054a003071088840710201e50360043c480080f03942c0d000201e2040008030240102c685064540142d00c0c98800c0701c0400c00a40344c2c0c0d00b00c50b410b200d8034205461828002050302c2031090034010320301c00c51040c40308049541e10303008805d80d4074080c0c04400c29184d00e010080b0001c16001ea0001c14000078041c0c801d44c500b0500b0b8801404100040360140e01403030000015800391280d0060310b00c9030b6581038075407185812280d150a10001290800fa0305580315003c54851480c0e50700b208036074104880e45c0c3c3d949171840f0902d0a2111443c000c0d4500040c00000207134800e8560b1410300c64401c0c0c0e40030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 682337994 1250 682336744 682336747
    0xf0606270a0f0204030b5506080312011e140d02190311060301150e01030f0c02012c1509070906030b0601020d0201050601050d0908091002071d04032f0111090102010e190602 76
    0x54540541c43d60000407070312547d07900d040310000b08400044040c0c03035140c55a84102c104c030303070340c1c1e800c4400d400e401510003030300404510310203000811107507500c58000380f400350000000e4950f0b540402d103c00083d0303d0710f51081d0f800400810800408034058a5a0001a40c9890455140400d0180d904003e6000d4105006d2000b41c4046244d00c89e9102e400030004001d0180507110041401038000e01005425003412400c0308076000c60003104070342002221003190300034090342d115000d01404192000d82468031601940900003a409000d00031213018600602006010307052400000e2720f04500d40500c0015a41030104018030340e0b03044000d580040641000c0440e040b00140b801981501c40e180c2803960101c1900c0201c290142d0018820040d03441d099451484003d6524440e1480c503812140100020140e612800d004421109100038070040d0784004008800d031403a6807429034100400322000c1c9400401c2590789980d0900442d4200e09003000600068050317450040d4904010711405001c0540 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 682339244 1250 682337994 682338121
    0x50c060a1802091006090e100e0405150106020705011715010e0303070b0c031e0c03070f120c0c020f06040b030f071b050f0606270a0f0204030b 63
    0xa14682401101d5000f00b80e0381461130042515207500a0714007900000441d82c010101c0c99129011580c0e014401d209159440e07517243c810121502c003002401200c080c0160240d6401402080c00c0c03807800707403215401801c0c200c0c0c1082d00040910703200e1108214960348010070702114020700403000466030401c0c0b83c064060340240c00400e15510604034010b03c08450310f8100495000a800514000e9803401c1c001610a05201f8613201c00c000e05840c0a0040e080400200712000c2c00b8860410303a194280c10105259100c1000c0300d0115004940c1a2000c05e90700c120500c214075101420415905048568508090400fa02000c0c2408002c100480050b4002e01003041a4092f43d2502c0f00309e07088584da9230b80307114146041500c540800414440500ca01e8001c83c541e850800c803160070400d03220035000c400812800811004210241803084402c1c0d48480811030241240010000b80d406202035540314180ba11462100274800c020341c4680f03031001c5810b0f480d03078200c261100013110f43c1e009e1040d4070b108 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 682340494 1250 682339244 682339271
    0x2040b03060d1118040b131a0a060b0414010306080d1218020603090a030e3c040c0c0c1d01030215090616030e01090e0c0d060f08070f06050c060a 64
    0x201082c64281e07220b0071100d4440c4000c2100000300e031017030748160070001c05900d030800e55a8068000000003032094078540d08007261b150b6031a80381ca51080b285000440c0781b41d511740b21400c4a91080c1c001c2844003804c9840e1300c0003075805000c2e0030001d04104c00107010122480c580202100e4240b80100031031a00d0b02601e80440409050092141c1d800511041d500e0600c1e03600750f9510030010078120302262456420911034a007040703114000d200c8484600c04080d0030051807018406010b20481c9002c00c84001104082d1100d1013551000303003247d01c480003440410706159900300c0240e400031002e59a019502c6156510001b102030469505552811021f1034040342d400c898010303202c40b1f9802c15000b09201012542e02600700303aa26000707448681c00e10680304011181551180a01007589017500045121000714100525051514010024010f40ca484100282c0f0089134071000147d0b02241040c40080341413585140100b00c00c1c2015450f110681c40c00c15100c443c000c00601b1403958503403400e643e10 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 682341744 1250 682340494 682340513
    0x606010908060112081b0102030709080d0903060b0d06050408040807230409080717070614093c030c1603030f050310030816050d140706150b0309010605010e0402040b03060d 76
    0x1001b4200202c07013150030341050900075001101d1140010754540c00020307000001151103000018250395051a59082d91070301e0010340800904150441c00d0b0f030b60110045030f13141c46024081c0f81310380b400594491400d0ba54919044603074010380741014000700c1184071019003079030719000c104045e5000700310b100d0030b400e19000501502101a1000b18040c4003100340d1030b0131900415505108480030045030b25107000350700d40c01d00c0c21110b12155500c04001e0710080d0604c680100400b40d0402410030000c9550302083c1038035800611172200342d40c00840c10050301e80c81449014210136242035040da0b81443c41c3c400034071a210b01544c2c8030a0050000c0400c40b8034038800c1c9503602568020003901d50358802c0003006140411106c40581d15401032000a03000c0750301c12188900c02c9001c4d203001909001c03064813004001c04940c1c0c2c0d1a107100220a900140e902c583c1c1d005544115035a00c0005486403070701001504131114218910300c01c910402c0103009402108040e01d410000c240c6040c9000c01301c51411140c83c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 682342994 1250 682341744 682341757
    0x3070e180f060a0609060b090904060b151c0606020d050d020c010b0d030f11071a0f070b0f01081506060406030c1116061202030903070201050304030e0d14060601090806011208 77
    0x4078002d0804011401216030414012120201c204010941da101c03030794003c40c060500350940c040d0858010401103802c98010081861000704012190f0b814a5050311240d400402003035146218880112510b035100d102d690001c101d980040c15030600c1d8618000d0503407140d034030203a644030383c0070441d10b00c132007800d50044d000f030400a085003418100c2e5003005002c060107190044001001c9103e04504070402080c2c6004849890303180e10243c0200c81003000e0941c201841039201c440c0b00380000f00204001202d40b0f070040b00000060889541401c911034240030320000303c9900700d040441401299260b84048504a0728189000501242400001c40b000d420759142e04040e03215509501da00207201c40051030454006880761048141c0921a2a0590100701c0d43d0040d160024808200594090401590300510a02e00120151030303c100096410016440a4528144941110740d0415007040510b410000908040060501d081c5445507100014040e40c2c4183c001e440c07a8008120040d81642c0300f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 682344244 1250 682342994 682343023
    0x90506180a0308031807050a18090602160209010609060f050903160825050a031202120408070e070302031915030501051603050c0412030305180a03030b090603070e18 73
    0x5110340e40e00f030001c0f00390401d50f54500d02000d0004015049480010480b08466001c2e00b4141c00310b103041d88800021700300404520480752034103403141c0028001d2009250203808000701180700c40c281e0050182c100701c16080302c03042c000b2018044c813207184c0040542d0415909441d1242c7e0f581c54240c0032a00748414428103112044180ca80030500000118030701da1404501d4001000c0400701403040d000030042485900d400a040d548148040f80c140d242c5804c4400d21401207070f400030030384459041580d20660204800e500008024800e0209140e101d17038214030240350960450500101c0c410340d01c040412110100f580e1862404000740c40240d84c4402960400c00822082c40c0010992443c1010180c0b03da0010f403401c4009894a80c48100b690305440c1c840c96810302c0012a40d4082c0c008020141100c03940b410040c041040408003005040602c601c2030ba0046071211a54060200000e00500360030322940005c582403103203019650792180c0c014002c280026003004690f000301e0030150003940c10392 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 682345494 1250 682344244 682344259
    0x81b010f05040b0a0c23040b0a0c12030c0e0f01120207030509091e01060f020c04060b07051005241c05072408010b0a0233010801020a09050618 63
    0x4194491aa00841c402c5016000e0040283e980c002c41c9001c88416004200c0481c59143c0400f480781180c0032000d14001a040001f0300d4a5190113601d2820f030886800c00001400f802c200314100130021103001004141811306200c41584840044d1140da261a0010f004110300c001c0c21501d6032054002040c40805800d0440d0b45043d41d007001840c662100201500800820012075462000030000d0761114240308481c0c1c060340d00300101104c10740302c4102c0da0001c51045090400c0165128030400c001404180d980356a40c825a00e4810b0500780341c0140301d10040d1403c0101301c020301c10901742e84e0581030305e0103d80c40601c8a02c80060355000c040f01c803c000c4045840103010800c4400204c2c00140c403142c0c0351401020004104c16100520308096200000c0c1026004210900f403041c044d0420742420300681c1c0c0f46a622a100c419002d1740819954049640c2c440c06170b5101e89031355801e41c00741c11244002e6103014507010015040549902c1094014903000501002060303aa50804096800003003121 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 682346744 1250 682345494 682345511
    0x916150f09030b0123030705030d050c01140708011d0405030a051c09062c032a060f0619050f0f060c01090b0f061c0210020a050106080d030c020f060103081b01 70
    0x1800c8000341509061021200b10400c88a2031900087e503900f1104000c008094186c081038040311641c003c480c2001d2250340b9001c50102c4030000c049181c0c400c02040c1d9903d0708540c0340425214021340010303c2609a4a02101480042080130048400d040307200e00780942d86000d4960000e0b106090b0001c0305064524189102d0100040c1d41c02c10701000410b0104207240480000004180301400b0700043d01561003040f00c002800445440e0043d000140c600101e408514552080c0c10010101c41059121080c24200b20251805003600c140c4a480311344d04540d86420709010650000000710701611407440441e6029042ea03c034021110302c00c00c00340c000c0c41040900e260030303131a500003503449002044a41d4005500c0382042401d4420020b09010a5140c040c0d00e60280100840500022000c5004516026001c80c0003401407000070070396000284030314004908000c04070703443e4002c4941150094070b550140c54900052983c15603030031211903546d4854440c40c0da01104100c40d6580e09550918214 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 682347994 1250 682346744 682346759
    0xf120f02070506060105040b1e04082508120d0509030c250509130f02030313030f0c0605040e1617130605060a08071223060916150f09030b01 62
    0x80e01e20184100100d96081d2200c1c001034486004078007a007840e036841481003482c0e00c000f84521408040e100a81d040c90302b511403260034200301d201400a10003030314880c0c842052000540c10040205100c0d0040c1181c0a1620782003a60ba02c103000c1282000358650001c071b0351040e018000c440301c9480d5101160903001851304005c2c0304600c01600c07074a038054000780000307407410a4906140f140080d50030a0008254580c0ea11301d500f40c14540076070b09444103105401003010324403410750185000d811131144044092802d00c40118460f00100100a024841000840e02040c030590b0044075201c3c1000704844070358401c4034a030b47d81c0b00da044a542040c80c140300b507001000c2c0c80c020303140c0c0c044d481c14402651070748180402001c0a1082d81510307031011100f0014030440210020140d4801c58204440390a058400400c0860340f0200c0c80a640001d414004011030030801d586100c4125071708a41c1151802c0641e2070301881c0b4403002014440c010003808516445a0544c2c8042c6500000400b49961602030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 682349244 1250 682347994 682347997
    0xc02190e010905090102030c0f03040507030615080f0c0307030b09151501020c0a030201080a020f0705010501090617010605090c09031e010b04200a0c1401020309100f05040f030f120f02 81
    0x54400e09620704404288050011b008480c400c020f01090203151074020070010a86900003001995a8042c0441c08000220180100903401c409030041800382810001100e090a00410448000303500694000d9a1605c01007141030032242c00202514140d0780710740c02c05040283c0c40c1c5480c0700ea1300d20070003003100b4039045540c942c4074000e0a0703080340d2064142000b400405445400040e02042080340001c8651100d07400030018000c2019034541040c1156960b1400d6070000c1e0003c40b40b458885c0c1c3c0502200c90110b038040b103898811002404900d142c200860142d245c094110303a4044000100348280781c03000c12010701c10204448048007039800c0501528004c001c40c50f90300d8032460410002ca0307803110030f4035407280e022003c000550745010440321064403204c2600008550b02c503420390745962111000e1010f14450720309403014008601d0b403012550304440c14001d210a80d035103070000380b10100705c2c202008043c882d803600b000c40c1034241d6440151031200150303500d003d0303043c00d00201a200c0c485c0c540 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 682350494 1250 682349244 682349249
    0x40f06020a1701050612010b0a1b05032d070303051803070308060918060c07060e060f010e130f02010c031b05101127040b1518060a0f0c02190e01 64
    0x8045102c0d6600e40b004c128040c4604a1903440186604006000403810200140a450054280207001e0061082e41800c28160b00b0300949464101150011039007101951944501d00c01011038031107a9814410b03a1058007600801030205555030000a1a2400c80380c01c1c1c8000c104e000c01281d85a41e12032500a04c40c1074221800e41c06590ad070b6000c80c4d5542c1d03072242105100042d0344040e0000d5901c204901c032640d0010740e8161107268440c040e0105055080c05100e00484071120079001d6903040015560411038081d104080d1024001c07024808a8107908000508690902e08424041c0a40c10100c804820394407054036640764216008081000014a8060b81a02c0107000c2c080c1d43c5031800e0000381d5004a0b04509036a4022200d0100390703041d00140550301080081c80040c0b04010200405c20420150f200010301881c001000560b0307050b0980200690031084440920b40702503490b000340000d01d1100c4480c140804810003e0441d9610f981c001e4103000554036000c0c0143d951245040d0380c0b042813 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 682351744 1250 682350494 682350527
    0x3050d0915060e061023030403050a021b010c021309140705120703020a0608130804060518030601031106160f0803070908010e1e0c040501180b0f09040b040f06020a 72
    0x4540058181d018071140c40c4905030041440d480c40c0c20303039142503806ca0030034609440b61304400200c07520f4030701c01c4802450180c1c0c007981d60350783c5880c1d6920000e89424441032040c41060000301c1200b030340b80c1c3d00080000a055040d95440c04c40088001c02802074912140001c0aa482d40c00a0701c8940c00d000422500f02d80d0120b465545050b107803482a40c4a030050700004c0e40000d038045045c42820300906a00380c2000c815803074008202844e88540c5041d40040e0031800c0002d000142e82c5016920040031903d01c0c50040300903080c194915507030004250301da955030358084c010104082500a14891050740c45a4008900783d481903118070b0030001c264411110140411a4800f0208182005114414441d00064000d01c0c0c00f240c0d641c07605034039041c515100003103840f03980070b083c00300e4451f400b85c28000d144408900d1800d5100b28581001d9651591945001d000c2c01460b04a041d80d4807101c0d1504170360400c5500c416030321079080420600c444c040004e842c0034000112241c0c8140d000e030783c4206d04040d2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 682352994 1250 682351744 682351751
    0xb10030b03191a07210501050a060206091509030d0608010c03150303080705090a05040e060f0a0b0904170f031305071202090f07180e1014060f0703050d0915 69
    0x9a0054110004034441e0141000c0b24810200c02d007140b08042e104d801c40c1d9181030154039200c40c0904101c060140000100195071144010001810200d403c08050111030001d095207140c0754640700d135190741c070f808082d11310144440414640071040c070480b0b84000d2103090600101d5203a940e1540606510361900000170324202d1840c1c11240c46104110a480c1d0560728480b46480305501200c3e01d40007050382c69840009000d001420f5034491240303546404900d000741480b4034001c405403404601c000c0a0b40c034400d0070400c00304080c1e5186007003d07620070392000c1d01c0030315a5403c0d0559015402102101842c020000092042c4404041c008111180c840d03c01c40d0328068540d5421440400001c9001b5080346050300483c4040c0080904150f2240e0140340150466003ea000e80180c0c40f059800a4031001400c424403004103d81036000d8060b02034407416680400c0f00e07101140171071140c0c2d46503c06018012490200301407043d0120740d440407214800303111101c0c541c14154114182185169001885d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 682354244 1250 682352994 682353013
    0x11060c0f061807060e0105090616021915050304080c06090a060c0912082101140a05030f070522020d0b01120c140903010f050906071b0213020a02010b10030b03 70
    0x2c003004081608020800381c20603514200c01500d0311443d1241c528140141800041c90316180c0d030380503056000042da1000c0c1c80203818014482c20703500d442d142d10b104400d0901d0520a8004900b00d15101014501d40942c0d0b81d5a0b80c1001d542a0090041c0d01855009980038014085000280140001c0c000c5004000b2100105001d880700740c140d00c9541000c03030700042c840010901e00c201400030482c03c40300c0d643c0180305440c1c0d0092514000d0304110100c00d0749405068090618044801c083c20b000c0d0f00402e42d1000f00c510380d955900031845124030540c841040da503810913039246117820501500d0703425901c404560032014003825206402034001100b2126540f40b0304014040d000c00391596440d182843c0b804021440d1283d0f014199440d010f6496a0f207007000d0310b01a10400c0e120b03400040240c00d41c3d04241038010002c488044182d403905841c104150050f03600c1c1c0030310000480c6170300401651050240c10590140c440c0140280c2d12542d140101c0441d00d4041c0c00292111b60100d098900014 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 682355494 1250 682354244 682354261
    0x60c0c030f0a2906090a02190323040f120c050105010b030a0f0c0806040c030603020915030c0102060151110a0512030703090f240203160c11060c0f06 66
    0x40c100000098141d414002c42d0085c145164803d4200ca0078680c0507240000742c030010b01c403442601007442e000aa0324054803501105100e41c00c0308141300781d542c4005905003900c49900344003a01c1e07409041411072030a80d05800f8050b000710107001e58090000c5c061581e4507040420303203400c00c5402080fa11700300044210300c4003507445105004007058039402903588441043c0301c006e101e501c5100c024140d0703030b40010007da5a124402c030b104541c8004506507201c1580240340c1007400d217103170241c19580300c1801484002502d86000303114404181c000301d12107854100007040803080d070f15003c031646d040300c514510400b40341010410003407568551110b4001c0c05c0301504c0d5204c81504002d00590061480707800c1c1d59614200a68001d041807501252031701c000e8564200450b031071842251042c2c003010380c02070300241400c0050410160b002c5e0450071407620180e0b41c003220b4001441c020400001a061604102420150a4111030f000c0c01003030322007024602d4207554a00c0c3c441e501d02c01348074040014081c1f4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 682356744 1250 682355494 682355543
    0x51f0b190e01080f041407080610050603010b03011e0513050a050105150901051305030601080703051606080408030901110d0b040506030a03090e07020f0a0809090601030b0f060c0c030f0a 82
    0x15030180c3d036180c000e64900342c0150720090080c000725030031100001005d09460040144d140135104420240401d420080031007020001c480e40414051001031004000d0143e00005580c1120100e140781d000c01c000c4e03100c1d00c00420007a500000c0e40421036000c04940040250700c802e04c10440c0000c200116600d4004000d107403c6052401e44841c42c1c1000441059403144d0003401003450070750030b0504800c3c1c4460000c6c0c103000d0260003000865015010400a00a00b00110344600c9440000000280d08040008020b400000d00190080780700001048a051007540540c4a0480e05240c2a80390b8140c40f00c1071010340680c0140921460078140811401c0c900414004e02007989612840d4142c4d1803c00e4007007a101e002001d00c429405240b800b42248079090200c1c040c00da1045041310ba54940040c100035101078050311003410035143c054041102d8a0700e001000d80d08034200e8881d61211011250300b85442d1280e9040c50700344c0180c00188281d01000510940c00342d10400d500880c0300b4640c075444040317 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 682357994 1250 682356744 682356767
    0xb0409020901210c120506011505040510021f1b030e060f091e1c0e0d14070f0e0403080106050f030a0b06040522061401020709051f0b19 60
    0x1210074900104038805040c0c104003070301125074096621494142d112049014080d03408600c8901d4440e00c24410008244601400351400180603d400c0300341d0313100104140164007800e40212070b80416050b06600812220f50f00744910a003440610b41c441c4420b4010782407101300118042d0316029030a1000340680107030102d98140350002d0080d40d403040c00011445801510103a211f0142d0949501c460710686581400028480014070840195124401c40c000c0413407030602c101311000d14500342c0b42da240182c01d03920540040504a07001ca4a40b201801c09441341d10a501c4c41c00034000008203004200b1425124a000e031711900704907a0b840e90241c4035481400c1044001100401c0050342e800480d500403240110f001d840b070703800d00c1d441b00045501c061240a078848541c03a0a0321824001825001e400d000d030032400c0c030760580000c2d41e0002070341d566180d01400181c3d5440340c0004100c2003070070340c141111011140e980b40c2056a40e001790303c1c0c0c0d03601110009000521911400310020700a00d0500326 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 682359244 1250 682357994 682357999
    0x1090302100b0f0303040b13120b190e0a0c0504050108064305120732090a0608101a16170c0f0c030601060e0105030c0705061501030b040902 62
    0x141c960903a56860060011001ea19885202a01d0303201e15030704e04202800240c1802640d880d42c03504e4070003003562000700982c030540c0c41c91a030009030380006903a06078042d04003440381904a010000807421002030880c1c001041442e108500c1c140c41031007940c01c00c050496405460810503070b6281c400382502d40e50308032202403c0c2929030300c11000148034159001c10a1034060004661a001040c81c142c048000b149043d00240002c229018184442c0800b0303600f10b1564203003009019224445010800310b42a1000c45407000281050580d800c00030072905060001000c001b2401d89510000c5d004007400c1d26030f40311040c0c00c00f00c0410318440b01901400d1109188401d24204081143e170241300606000044602041d202c40c140505005100940981100b440c00303426003030500c0803000e14141e42558140d2195000c8401085801e030851380c0b401c101e0a00386482640c0b0ba036238658034003d41c450103900030324500c5440104801c884400c2428500c2a00c240e800703010440010707080100f5690000d00207907 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 682360494 1250 682359244 682359253
    0x9090b0f0d06060807030303060302120c010e100c020603090d11010605010e0409050c1203031501050f0307030903020f0706080a2f0904090b09010203070e032406131802010f0201090302 81
    0x80c41864a609100015842054007261a5850f200d405041445030360046000c00e8842d9005d10851902180000340740450b640105140480100024682941c3d01d0703600d4090b000c004550340c000c6104070000102c56070040d0440d60343c0c0c14101046943c03801d1000000c030005400f5100705c03018003818040c4104031401650303151040c140d00f104100003090345690840c1d881c42201c3c0700cac000340c1d113560608000c0d200301880a59101d203006a00003a060031988422410442e0420a8108a43d1200c00b5250000d95034a03000682285915050345814840759046249201d032985c00a83c0031b0b440380403c0d21074050b00741c06101d52035030a40b4200180c02c00301c0103000e58610100b403c4000018080c040c00580200400111300d103031054540751140d2400341e88041d11a5000130803c400b1541103144010350200c258000c011480c0302d080c00102c10b07400e00d01c0001e00580601d000c24250b9441c40420701c000d1b40c240b85d0401c01650a110301d0a40b000c1c101a0490200d210790303036280280d50043c80340d404000d42603005032 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 682361744 1250 682360494 682360519
    0x501150c030503070504050316141c0602070c0b16030905060306011e030204090e030d14130803060301090204020a18300c0b04060c060e0d0507080304030c0605070c0309090b 76
    0x6a0301900f0051030f200070490140400201c1c7d99040080419101d0f02c2c1e03a16043e414101756a52a05c81c8c8003d90060044003030890f604070840003100d045212316006400142c4401aa14007042c43ca00c950b40104e0340e20b600400d14070010351010030403604180c0b1070345811030030039540d5052201c54081298050302207086c031202101c401c0c0d588903201284104038680140f03000d80f1000300c0780c1207500d28030010040d0384c004528000e0180d12407141400c0000c081e103e400301484c01c4038464081c592460b000409403640800031402e2034509402440f04580e004000350744070950514020b18001845041c8043c21901a0f00000d031007a541d400d4808181d4010071034050403092900c02d820005a0a40c1110440401d00002a10700c03680c0001d4005400c466480c014001010706062050b41c4400c25151078640240322140d071415089000c541c4800c0d03212800c141c44c0d58407414151107913034004001812031401c0c0300c1001810713903200180020351880794885c00e4400c3c0c0c4404001045038010310002d50041c29030940d0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 682362994 1250 682361744 682361747
    0x812100e0601200f150a0e0c01050c0705061206032b0e0d0b010308041a0f0405090a090c08010e3003100f080703030f020a02090f1909150501150c03 65
    0x210004114041254643c2c580003504501c2c0480c500414081c036004070641003688a40300d05019046a04002c0c03d210b8441e007540e0722501d1f6000c544500d4144080003400e0b02a20205000b00e200a0100400090303d0342c031900300e02042e02600b161400d1107801001d0640e8059003408154130380021491500c405620981c4400303840016108404960102181440c1000500306180b640e0295118000158032645000701560714800d40f4507030500404000c0c000810380425800a0310115101292518241d40390038018000400e80c012000c1d0003030b50201808124104150400520f841440d404c4464070022a020b60043d001d40d0100142c0c07410140850341c0c40c151061000e1500a284041e280203400c2d030341c141c82ea003c0700817523000c250180c0000700708106160308800030360210390a50024040a2140340e0010321003c01c02082006040003203404580c1c1402c10714040d041c0c80302d695904200400c1c007410a00000d2407000c1c0c0115016082800116180b03003840c3c206070b0400a01d880c1c0d04aa200c09680 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 682364244 1250 682362994 682363007
    0x105010c0309090c0314130501051b07150f09050d080c07111512010e060f06040e0f0712060602010b1306060906030b2b032a200d0812100e0601 63
    0x40a010191a01c00420040506d4000c950080d806080805903030740e21171038200d094070700040c000c21400031900d0540e52075070009022254141e9108090003c810700039240c0100504801551100103454200d0f032408000e000100581b1000f002c0e180c02d240703030360780c1081d284051103182002080000ac0100141c82c1c0e0030600c4100c10444580c0c9060b41c244940300f0352402d100d00099010041e102414002d0007114182240d8510362810300750f510314135103400c015985071200300142154004c0059940000d04a0b0300c42e00030f121100c03410b0041804117076541d00d0028041c0c041c0441b2244039071081024050362285030300c42d060846010361512080c00346014015070007000b81110090308403203031000800195096071201d204d0400382c4201021020401e0500802514100490116081100745000c1e050b107929140080002d500c0040c2c0c0d20544035810000042941d51401d154104407000341c00410030041c040500b0f050241440c4030841651070408003140c3d0b0103240310300142c110b403a8000c02c425520852 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 682365494 1250 682364244 682364261
    0x90102031c09290a0c1e020f071508151507080705070609140307030b130512030a0219050301030b010e1f03050309010314060a1509080303070909050105010c030909 72
    0x601110030b41c96890708590720300c20b004a1103041034101c401203502500343c42c1e0450808201000000150748005c0d00c607011445034903604850390540c40d4143c5108204250191080005a0719107039641d200b41c0174040720001c1684003103400e0728002107003016000318000311600024500403001d420801c0c4240030740c0c03090b00b00f43c2e00000c0403c030940208204200680080c00644d49054203145000200c070390794100d40305014400e030045c1e0020404214072075040da4001c03001e155841118071552401525188202811240c80c1c03402000304843c044596018120813440c0e0a0610700f01d101e020000c58052109000080441d02c800c0c00600406e910401c0300399121010021003d42030407807100488624a0310b52044cd00d503032000880b0302082d64180146811116003c00301c101c14280200081e030440c0b02400341070007400403401280e00d00b0b440f0340103000c010501ca6040d2030340d904203a40000c0a0312054007071009018100400061154441c00c00b40290075010b41d0b80241c4103061142c03203c043c1c9440d2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 682366744 1250 682365494 682365547
    0xc010509150c070902040e0403030b120d030f020d050a0902030d230d180b04020406050f01090b090406030b07090e160c020f12071d1003030203031504061d07031109010203 75
    0x42c40c0100d20044c0e584003c001801143c80344010501c0d003031900070143c8001d1100f850181c02e40f0165106c50580001c0d000c00107401c0c03400d0101d81c0ca03001c494520001c4c0034450034802d0003801c0100344400c0c062103622240600c0c0c0240e0a444548000d07103000e80c0c821300e24100a0061008a0b40104261170f0b64602811140c0c80401d00418031401542c3d0034400d5081400081d9201c1c0340d00c50610046103814450751004040070b941010412540000182c070343e07030f8540b08486043d0700000f103060041d940e0754400006154012841c80c2d181c200000020710f420814000c60550080d920082203076100c0944c0c00c02030000b03596441910b80d4005134240f2440d000c600200c0c075089500e10705d04000c0c0400601000b0f0141440319045280c07148031851160001c01c0282c0020504840d0040c1403002c20b0b07010048907448085c0509901100d1081d1000c1001840e50394404154000d55a0a01142d1240c4d00e0520740541c0181ea01031216124030200c40107540305290049000d41d104100d60030320504140d2480318543e01c0c1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 682367994 1250 682366744 682366753
    0xe07080429090f01050a0c090501030203041103010617010b0627040f020a030c090e060a060809030705010c031e060510031d0a080403121d09040f0210030c020c010509150c 75
    0xa0401c0c2401c0c02000e8400c0324481c0c1100030b003040c120900344030b05640800c220741d05000ba0f0300d0010b00500080b00300c0c0640c9040680000000f001d001d41d40c1c004010390315003c0d000300304440c1c0e2024441c0500110b403140340425403c0404205071494400c0036110111085011904038162103442c0800d01540da02070345821540350240b151403448544080d0600f03800a803004215260301c2100200420384d00c4e001a02c50001d004280030301c58035110619000d0f103115092241450300e0340d0000501c0d500031040c00074000d608010805048a601d03400103010043c043e1481400095060380741008e40d0014014160000b10085501541d548a5000720f41c00404201a190501c0c41c1c0b05561420590b44400c25285044001020010804a11706052980c1c1e103030b2800d100c450440d0742c81d0206020b107a040d51442140c03900c0114051204500d100f801c4154020070207580840c0c007080c094007030071795008118094010040340f081c5550040c81140c0b100d06000b0035400d40791015101441040d0000700021999109 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 682369244 1250 682367994 682368053
    0x708090d1407080f0d021b091015090f290307090503011104030201091a1813051008070503030c0a020d1a0f09120708090d151a0a0e070804 61
    0x10900070140582031410290000c1a01c08002c14504a1900d0401e0b08561041c203071841c090281c7c1d04896810a01160101d82e40c0c0c0301c20720320071504100c40d0004440e4201c00040740030080d40014100d82102c201500800003195680c00300790199000c0005400041030804032044800050002168403000702c2c1440da995607210390100c0c0c00c6030a5409580705800d0300050500542d80c2241c0c04100601c01c0c042e000d4643c40208001030224010904140d01128035022500d04603580e110400249140410b802c204034500381c610041464083d22503040c6030702601c400402c00303007004070843d0210030b03580c1700400d9420034560a1109602c0c80c22806d132034a002d0042c40120344003410403501c1c02216101e41107039240c20a6100c55003024030a4040c109242001c02600000a0002055031444207044680c107815520900b498900001c0b60447c000c1c0042c80c0000c1d0383d50300485000107040c400c00568900072650348801190101c0c03c1e080d1840c002140e454400640002c0340200344103150b80c1c0c403001070040310a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 682370494 1250 682369244 682369283
    0x30c0c080a3906050f102702030712150b12060a080102070f03020f1501050105030a060b0d0e010506090105150705070305010c030203011d010f180b1201020304050709020708090d 78
    0x220010044551403038075840c042e0078000e05004041e000404088001c0c030604018140ba081c1c1000d0340304e9000700120701c40c110b846400400817498080d08140c0c200b9581e03440e001e90300134013410711503414400c81883c0461702609001d03010070720400e5550310720155181078807000100c44036220041101b5401481d00b00081441c410030b00150440724030840e04c13248149424075010741048030661001e09a40d00501c00b4050480c54401c449044610a0815503600d07121407100101038802500721104200700012250b40d0800315510200400100030001c210940710703401000802e120a100c0d060307001c800c03c080c0c0f4000380e10710001058240d01c80c108842c5480d07580d6840d2400d6501d00701307094000c42d0303011004002d583c9400e00446094500105e42170081e604007039545242c00524040c0b8015100c00342e040000306c0c103290b4030464540f0300090408150000445545010f58011942150315015500001841000c00d00a07280c0c4075038071019071303820000e400080c0240905000c40549106400541409408 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 682371744 1250 682370494 682370567
    0x40b0604150309031101021c0207140f0c12030310030204020c070905070917190b150307030507171f180b0a0b0103061a0d110915030601030c0c080a 65
    0x641c055100494103241034140130b461040e8004038040d069004201e2941d440340e00c0c80003070030381c69081c040c0103071918007900384860010180100150369204070010400101c00000c0c4444103800101c1d004400c0203180d005640c3c481c0410384921181c06c4841c1d600740014039042e0054007a40c2803c03000c03a00d15950b80d255400545000355100c8000c03913400141030062040401c840380000031104000c00302c6002185652101400070003004e0281c3c802000402c070f00c2070b8150204180300400a0448000c02d4581c245683c640d4014402c9c00318403100d01c010004c055001203000000d07045000034280700604901c444c5406001590b039115445c41c011040d000c000340c90143d0407801035128020000e05250050009001c4a213580c000d0b400d9810050310303411030041d480040310400e0000c0d94001c144d08051092100341402500196580001403403034030098a48004059842401300340c0e018400085809000c0c0c90101445601031b00a10701040b11410081c001c98080c068810003c002c043c20200a8540f804003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 682372994 1250 682371744 682371779
    0x21c080a030b0f0904021c15020706150609290405120f0f0102031b0702150f0307270605130305010c1214060f01200105251409040b0604 60
    0x30990b1400381d000c1d6810014058040500150342050042c106500001e2041d00001007002d80e0000b4031000c2400c000310b9150304030b10a4104001903480c0d003054501100034104403169181150b0300c04c04001050780c1b1a078141c00072a0f0040c0c00b100003095441d0b003401c0c0300c1c2030300c2d01c1e1403029010100000500b54407010100c208002d01d4001405d041c804413101b060510400c444443c10f01ea005000384810080e6250a0f40c60201c036800c2a969070f07150500c0411180e00d0501d0814044950109404604c202c02100443c0710340319582e00c41c0580400f90b0034400442040c1080307495044103200707051248a0041e4018252281c60640201c81c06070349544090079200c4084400e8001403201e00170f10384025850040007a0389414000f00611458688013003200c601441c07140504000c9904a803a80000704548400300c8805148000c0c4520b260a1540c02e80000000814002100300351400304c2e01c407841030111504602d03851002c00d280c04281010403001e0100c50f290321b03070f010004000c0000c204404441841d0b2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 682374100 1106 682372994 682372997
    0xf051902101833111006060c020108090a0c08010222030f03050f040905090102040302180610030b0f03030d360f0f08031513020c0a021c080a 62
    0x204611500f0000c451aa9240081c43e0710307030061001c00c0710150f0b80221046900c0400144080ba001c0e4071440c0d001070383c82c071420001503100c2e820b406d401003200c0d011240c0c069070644401c90303a0141648070300a01e0f0350024044240c44030043d010051040c0f0707260005080d920b1a1103030782484401020003804c000700003d40780550380030001514090b140703040e020462460a030340c02074000c0d40030380001d070701c0385030000300c00307803440300900603051048030302401110b610204a5800d4001c0c0c000348808585c014603090a160f0a5141000030b0280640c01581c00f2a8106405502c06455250f00b80901c1c00c0c1d01e01741c00c4111500054040407103c103503000d0380f01540e5a0f2a401d054030702c01e84070000144020000030600503680e900c00d410882d095021a1806100c45440500c48200d00c1008050b201640044402402500d0146d0720301d1807043c40110108000001c40e5103100c03030f99004d503214a0 = true := by decide +kernel

theorem cover : BRFrame.Cov 682194244 682374100 := by
  have h0 := BRFrame.cov_init 682194244
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682194244 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 682194244 ≤ n) (h2 : n < 682374100) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
