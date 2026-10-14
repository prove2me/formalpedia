-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2553
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:03:04.08138+00:00
-- url     : https://prove2.me/submissions/ab884de7-3558-4e55-9d5c-0261110ddc49

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 458992805 ≤ n < 459172661 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 458994055 1250 458992805 458992811
    0x30409050103051507050703020a3f030b040207050601030f02011e050301091401030203061501030e01140411060c0a061e020c011e051603200a0f0905030a02010503040204050a092004 80
    0x9807801b4070840c2a902d440d42c0c50f074043d011002c40d580300c8159422000001091000c5c481b00d00010560300f0803008401020240c14081c000d4a07281c0028084910300b074601805540100301980c0010f0000c9146c9055a03480710107014519070321b0004803118401007050302c80001d21403189012007138100d409541200e800740c0082c0601084c00320410520718007848000c0d05a0700c6400845c0d1418491920540a00010700d4001203880000340d00314252071b14808903251004102050005018040581c0240090305650540c600225080182ea136440744a4015003003d9071481c44812030385071651081074080c1c54a00c15900e03411200303950ba00802180b01c00340d210b82700c01844605043c9050040c030740708000168100c429400010f1080c1c0c00340c448d80c140540c40c00070510110582f103c040c405082d804ca501d69441c1c0c0c11544500b00031b003400c0c0045d00810701c03a900c108285801030381e001007100d0340325505680205040c2c5071840c40c003014203000f1100420300d50504800070303160090700a0800000d17400304d03414 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 458995305 1250 458994055 458994061
    0x803031006030204180e0a060204060e0f09070503190e060a0501090f05010b0406110c09090d39020d05100203060a0e1e0601170c0417061e07020304090501030515 71
    0x42d8102c0c03241e44103042181aa50000c00100702c180d61107108492001401d03580b2020f01645d4082c00c90f80590031500100d0445005c045c07850408680c8007540040955044c400c5042c1140d01030308030f0100038061054025a00c29000011189401c1040c4035031310350084414500308002042c02800d0240a41c0741034a180c012250f40200c42c0d4000e041c1210181601140b4203070802104990f280440d00c0111010302c5078075503840d15500ca0328002d500c142e41003405080440004c41009100d0105c07503a100005690820011007a40803484582d00307071080700c500e6030502c0e10803407010070300d0140d02c004094103500600c2181100340c20150021817088404a60741084142c80b0b010f0006800015900708240c80a401c0c420000600c8004001d034005e03005050a02410f111800500114181100e0b000b189400c0484c040000d10750b143c0c2180c0c9a1109600075203034920300f201001e40c2d003202c402c11140070841c083d40801c04190003401221701a1803160000c1c030080d07850b0308000b55540302070180980c0340c0c0e65003400 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 458996555 1250 458995305 458995307
    0x10f06030c020114221a0a050c180d15020a08040302010b120a080f0c030d09020103200304020409080405040908220b04090203041509060b1e0130060803031006 70
    0x43d007400d0250307551501140741c850700313074000d2004001e09070604854040c01d40c1001083c05000c105117010f58806c610655442c1110840017620005060f002e1024000c0c003100c14481d90000128100d41e009481828141b00e01c1d003041c0c02c58010403015520001c1c40081d005104950052400b803007180a90024000c04180c502803041700680c50714007c0b1950061010310700060600001400d0301106400388074248013080c400720b07003564001450001e00310707524181d141c11941c1500408448240d07100002240c0707800c07011151407612000340001d200e243e8400c240410014000e054278060301c00540204110f8a0b0b070301d04108140e100c0102074a000c420010801888498421008150b42d80a12401d0400d40381c41e299030701a40015000711030000c006140841d150b070f564821030000a001d0302010440c07030021300c24003081e407410840002c110000d10340d038005503903000b11440051000352074181c04041071072507810203e02840f116000c16541800740020366150000083c60241000c1e80b85000c40365039981c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 458997805 1250 458996555 458996561
    0x103020f030403201216080904060602060a0b061801200610031704050a15020f03030f0f07110c010f0207030b0709060f020109020307030f030e04060b0a261303050f03010f06030c0201 80
    0x100034526240704011807040525041c10106d2483d01c51280c4030709041d01c83c0005016542203810200050f8010740400200544500500c15000801e80f00e043c034189004440003019881110024140072200c1e60168400044c40b5011181c803c2140a8035a5400c0c410020a51000315200c1603c0040c500c0320240402503030001120200c1c2da00410003008a03252007540d00d20303c41c40644400544c00b5035a00100310110504c020340c03060b100007600c1000c03031900203072501e50a140945200b08110088030301601200c80015610040b09007428010602d00160401700d18201c850380004200311100c1051000740c035040345806e8191101510703005940b01051100302d01300d8802400213903140d40200310400215010b5409803580c036000c0c1c80e11341510072110000c42e0564580740c0c40369039030840005c5d9640c0202e511880b5204035108200c003c941c8000b603074041c030042110140c8206030000b480030341d6400b010301401c00c41e40105003482e0300702d0f00ea60b0340303064200c40d013500762040340046030410541070180340c07040c8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 458999055 1250 458997805 458997823
    0x4060e0301140609090a0b13031b02010909021b07030515070c05030904020d060e0709051f050f0a0917010608071a120a06080a060b0a0b130905060103020f03040320 72
    0x1048540290350f100e0400c003140c20b000e080c00d8000d0186585250100e0181300c0709a12407401901301c50004035461070010280c400c203143ca0020091744c004100010f030307448004001140d811040140c0c032800d004003074080c1031415410f2021540314034071000080040100d201d0100031000d8403c2403150f41d5080081e01e18a054a000500a1f0420032035680c491800380c4c0504100c0501da440056050340741c190b082102c410139146d000110320110f00030086460008140604102048502c0c4566034036820050b006001310130b0082050070020170070b8004544241e240d00c00a0064060b4003d081081845550082040d0b00a02d03887d40188800820354202040c051404110f403420020710f44403440703903e080d00705000b0b020706004c541c541c3c04c00a11040d081014841d1640a82000642d07a201c407010064500e603680d1200300d405c0c40511000c4140ea0301d17034440c1d1003103e000d54404503040d03032246c004800900c1000345400d0b158001005000601d50b01014120f080001c845404150100290640c1d6451a2507 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 459000305 1250 458999055 458999081
    0xa090f08010209061c1814060a0b01050d09061107030504030c09020a0c02042d0e0f0a120f020c09010909020315061e0f0a0303050c0d11101a090c04060e0301 69
    0x10848442c100e10305c0083c0004515074030000251a05d0010705107000b802c909641929150b103203a8107005071200c01c1c04504d0b00500c102400304940410000068a20b0245201106055a0740c040c18814070040f83c00c8070952541c409412580c2c1e42240c640035010740c0180c04191510103220b000816071a2591080b507507002841d445003824030100354200800381066035011151410018000504640c95440e403403a0400c841030080380480f00400c050b881d03e072041d81b0264040d40f00503081300c0450600008202551507516040c484540780d0039091f80b810084402081d006596480001841e850580c42171011600c203c040d6841d03500c1e00d03d801034201206448655000510740600c1d8a5030f1482d40c0080702c214000380001001e410160002120341890b64407d40c0480d10006801c811941c0c140400c26a031800c60030070480151140902c15943c40ca039505074003074a80e841090780d40d110500c502d03400c1d50090040900301c003880c00689240440e0400d1050401041c6180c2c40700c6460300c1d041c0160451101c0d4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 459001555 1250 459000305 459000307
    0x3030301092706020901030b190b0304052a0f061e0306030a08030405070603060b070803041b0b0d0606020d030911041a0d060912050c030a080612030a090f0801020906 73
    0x30010050010503402c03a9400d0240704003401a800d05042c242d0780303010280502401a1208524800942034501c1404001e00c01d82c080f100c2411502c034407403256025500c03040303012902c0f541c131480d0440c9428103400070409518591041c05d04140825180000c041805030342d03102e00700e12034100b4810203002e594500106980ea00f040350507489011809150302c40b00c018221641c03c103182d1034009490303100342e030140c406030080241840700a8241c0540401009000b141514040383d41d220f03d5240d010241000300913041c02d040740e45080151094040c0900f5083c41c140c2d50302c3e0050500301c001000d10707100300c4000d802402603584d4907034040e00c14108450b410654018070401d6600c1000000d00e0840c040340300e124401c0c60b0b0642039440340d001100400b40b140a0010341c8020351b0500f041c510340303a600341c4420440708200c81002c22001105560060003681003500040d114180081d03800c229200c445030441c030000c524420440d50000c0f800c406c85414a0b8462600c035160603a00d42030b48203406600e608110 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 459002805 1250 459001555 459001559
    0x60103060608070509122107020f010206061503060d080423040606020d2109120806031903110c0316090b0a0602030f030c04030b07031d010603021c0309080f010e070b03040203030301 80
    0x3c014202c000502c14103c1500c030035070000c103801150341c03003100035800401c1f60200384082142803082e2044203007082400100b09500e02080000d1081c01e51028107040c2080103c00f0404ea500c800307000303180071580001d03d6910342d601c0d40803403041d61b105c0503030640f0f8a220340c0d0302c50006030500303210349426240194041c11401030512410703903400200d41d03402807001da501143d00a000c1d1451140d00300c840d105401c500c0c0c0490792200001d003008c40103005c0c1791094200e5a00301075410302e02401c07144c00c503038141050141465803240180c24420880e8845805004a01d415000c140c20a42c481e4142d41d8500410001310602070203100c1c412071036001700400340e4001c00c02035510340310540c06540c2c0040240e50845c5807507142c0d030b11501060800e40f0074034003003500c58920349100a0003c2c1226440c000e02c0000b00080fa285030009004002e0303401404c110541c10322200703418144510080b00107030030404211140700f584100a54001c1980d02044003081c0503680002c03034490a0102128007a1b50002e0056003164 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 459004055 1250 459002805 459002809
    0x10f03050c0307051309020a0306230a18240603060b0c0706030e0a050d080a0f1812021203090607080105060a020d051602030d0207050a150909110c15060103060608070509 75
    0x54045c4554600244c00580300203403450702c0d400104403100340c40d940403134800e2400741c10043c03d0010365005080d02541c02008021a102c2941400450b4119400c4c003000c0c12900005000400004400b000700d0009100300c0311040d8515031081c2d0859006540c1044400d0303403a03038161301d507000e152081c0046411408041110b148660803094022600c08240c0300e0340403035540c03160b00d400c00459101020811942c104015100d40c5c1c0b2800c01c440f200d15070b0031b0100000091101c2c42d00b10b081c20004258007030355401101c03103610820800000c00e0740c0001042e0740b402d050414030381c1c1d200100d0340c03100040d00001c0040b8990500e0400d440604080ba00109446103c41c0b00c20b50700e41d04990f031320181040b0070010b0035001d03960401240318881c5454028010240c10303d000e000c1c1001040d0003056900c000c462104501551142000d030032291080c1c3d00280d0b903915155800c2c3c880c4241c00c0c0411140c42000001c00c0c1142d900e1038094003d10098a007005929540c00e016a0b80701d81c111001c4010070030500905a030380c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 459005305 1250 459004055 459004057
    0x60f0920030603120c1b040203010305210f041403010614090a05040f0f120207080d020d180305031c051e07051308060a020417071214010f020d020702010f03050c030705 74
    0x90000c040e1240501d26200b0784940d608002c001c0005d42c0c0c05500b001c031505030644020280389800365810b5203558119200c5503540d50003210160b2000c40341251034203085c42c1c16003e541d080c0e890b0000032981d5a13600d21084003094242080c50303100317500e0b0000004144049808040000318090080060f41d41d80c40700ca1002440000c200303403005e0904400310800600b04030769840090f84030b4001c06030210030000009140c00710b00d07004030905600064414017526000176203030443c0121442c10505002d03d4000c99140f19950744c2c001003a5110120320b08140000b19058404000150b0074100003554841034092181c40d048040c640303a100040000c034800710b01c100020b0044408190808120596031191245007000c12a0326450b00d69010800340114820f211400c40c201800a00500006050041801070070294a40c010300348801d060300d502e1400c10a402245803a062303c6400c5403202c504031040406075100c102c1c01ca00080c4408a105031890103031140d1402000000c000c5070440d5204a0b0680345 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 459006555 1250 459005305 459005311
    0xa0201020d0b091003350c150f1803040314010603022404060c061404061e2a020a052424090601120e0a0b071713030905040906060f092003 61
    0x64180f03600c0c1d0680b034402403043e51b00c0745810500d4020742e1390364010b0103490811891282e800202c3c004101480030a281141c3c0150300300381040c200350702c2c452030059072620358411984010a20a440c50407411100710650088088034020754600c1c1408404015401400350f0044180706410303001c0c80180509445800640d402503c2844001a804088880c52442000c00c0303400b01d4416031900411280d41441010311800351414520900170903407500120768010080c01c07004022150005256a0428030801c12144000c0c0c1080c180da0304d14103040200b00442185c0f40403089030b12410000b242c07600c40c0b090038a40503220412049807146400038100121880068407250400ca1f0315418002010304510400c03915030f1031400200403403451460300480e1050010203000500210b018241c20f02129140760540c4041c1d1003001e4050204103103015101e13142030b42c110581043c80c001900080242c143e1054041e104005851182ca41e62800d0304000d8950700e4150781c504110300c941400860ba141400b03190 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 459007805 1250 459006555 459006593
    0x1205150402060f0c0a02030d17060411120c1801260a060b0c0604050d030c091205070b0d0e011118040b120d0513081c230a0201020d0b091003 62
    0x441e02400c0780301c4849136001080c180c4a15001900c0070f9045103010801114081281d0034140400301c41111552039488008110b1350041d504d820f450b10050085408541000b02c924407203415074280ba2a50031404e03003281d0080841034072203440400c00f43d8000c403540b882c2ea800c2040410103c0600e04250f02e045400507040078081a00e0307240100c4d1600c2410060801280404010102e601c1c080c10b11614040c8944141c0c410b16240007450080180d0180c2c0f60b01c151040d0303001ea4001101c45107400f503c1c001c010303402021280c0c030100350303a410901190408c404a4148400a008034194400700d07821350310a4030741e6003d81e18045200d1403040d0810b41c00c049503200000f4014581290b19944050410b4401c010360344c0003803400a03030011503240880c02400640b080030004d281e90040d1400495546803039410340d42c03d20510300200b4078000c4a03d03000982c2c14890090150301d035440004042c0c041c0d046149041801400c10740c0c50002d604011100521440e0204034074014645503840b100d010385030001d8041 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 459009055 1250 459007805 459007807
    0xe090117070801063b13051002070303140718120614040b250234030516081506010e0114040b070b06010512150a051203040f120515040206 61
    0x1d00d00d402880756500906040021011100305180170303035001001c0080c0e40000013440250b00301404d01c10070340a540908000c0080c048000c150504900e02001c1c804200103084c00000c0c3d4104056050300016610300d501401e441c5580c4990b04207031b442c02508100a065150080303401c11800c1c81e103034444405d0300c0c007440300000d522811000740482d01c0070440d000d96205921005000300546e611485840b24002681c0a85d0383c40410342c0000d4031001c0407032a8200498900c0c10400d03252219210003181c0e0201e040e40d6455003036917840d125445202240c0442c1d42d02c00028000103003603002052800c1c50360040b088070880c0d60744003030040d03030668007105405040110404d0b40c41300c4403420200800282c12030068064990a5a19084841c003000500e46070402c1003d1080d001501d80344001d50b42c01c5004010a00e55024944012802e8261181e105075440b1600d11071244048001100030400d0390502d002049a96481e002203046a14101c10f00800b0b0358403c05042502c070047041c14031038103e0700c014000c03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 459010305 1250 459009055 459009059
    0x605060607060207110a05060403110d060e0f010b10090812032d04110604050d020123280e0a06050c01020d0504030201150f1404020702030703050a080c0c010e09011707 74
    0x2c004076001108111404a14a013049000e86050f0125200400007181d150b46020709503030355984010480d800340b60151042420b60020030039a908480e1417070a1050072562030000c00d60015010b4502428158088d243c62150303050494420750103032055401b0f5100412680c002c1010342240c07a4030040071400b000d51001b0b0460002908200010400b80307280d0080310003414541441c105016010b0f0f100c501c6940d0411007003005459010302d82e0740950702420843c4020810000340e0015812611040c0c4503000002002521040310024404407030a0800401001060905054070f100002d994669070007079805200304400c51140006211030041c05002504059149031000b0590b4405da4040340903075164640201a83c5142c03002e40000c04184c0d80701003106203481c807841540f030b0070030400d2030185800003081f2041d51020000b000003140c1c0702d011246491440d05190003590003660603241c183c024010410443d600c2841c180d5080b620051156810343d02e8400b240c12008640b0b82d410100e40109000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 459011555 1250 459010305 459010313
    0x6090315011d07030603120c051005100e0105030703080412050c030a030e01170613230f0f090a0305031303110610091808040e040309090e15010e040f0605060607 71
    0x11560080440c0412201020001e0b1542110030400420600c10507107001d0f4104082880f064028035040214200005548030a082c42810803594101c4421014140014040d083e24003480450444240160441c032998850040540b40e070b0392484003401145c0e062005029500b40ca1002d040d4082c880c2d001c1701e00054180021078203002c07601c5010380111700302e044088420b50f080405030340b84803200c21000103946803080006001030050180c44102caa5103a140e800700300410b4864000c10800040c110029240010010b040b00f2781c107c5c0c402403201d074003030081801590300040ca034060544c9602c07618190f03640e4a0f8411000410308000340c1c100704900300e403164800c0302400403500950140c900444401d04101042e000d032031104bc2203007400880c00d0782d01004110950242c0e415a405e0806544494a49040888221301c02c3d400c41c0110620300f40c000d501c52000022803260300c2d001c034200490107a0380c80752100d1184c807040b42c0140c00340844007000000201c81c0e603c4203a0243c1d004158905168030361315 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 459012805 1250 459011555 459011593
    0x3150a090c170703050601020d080601170a050106020d020a031403100e0f060a080d020a020d03111209010f14090907140a0909050c03040201021e0106180207060515030705060903 78
    0x71080424030352035990300040030708440c0a07403100c00d80c1000d20031824103c0000355031b00030103044c4030b003040b940e00c0101e140d40c0c0c425921020002c81c0200358a00b2801d000740e898005000030300c03070340015104d0911044442400801c41000c100c0d051344038520903400558044015600060980041420040300810003c039421200f40c0285807595454007149412807e10411031925005040103500c14000f0600305640081d03c01c05255043c2d40310074106140740740c00e84020244034841403c901560460803410240c1e80301401e03680400740d07502c4015001c0d402050344d9400d00c0702e8111142e00d00810405043d420941a12034001c20320b0b14005103900511101501c0035089a450900020050b034010000c6803210300800d40c100c5440002203103581032030390020b551801c160510b030842584102c1e818100400039401040180300414082c104074080708090360095101d02e00407075200e8a090082410b2401c00d459032a601310001d170040c041d00d414413003005400d801c01d00030144d0510407100c80b001c14020380300e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 459014055 1250 459012805 459012821
    0x61f1b05010209090103050123060f27010636140109050303040906030b06100f0c0302150c0a032a180902071a0a0921050705010903050c0705031203150a09 68
    0x83e0000070f4039080218880340c0c07804800700c2c4e01e500410509c140051552141d01d0000000c1c01116170549640081d61601c0020342e40c4c000144c0c214000d103000045181c1c1210000306400c1c06482c0c648071030700d211a54180200f1070f00c018a013210f00100001d108840e8a07030040c1c0c40270281418205400c036901d8000a01e550311907007002c600581c0343c107801c108001d006c1003110b422990444100d510310200b41d07402054074115540d00c0b402c1014200f40c00381410f0082c0300d40700d1401503555407140b9030310301090207800d650700502410700040d2401208042001d0b81c800175030920f2b0080851800b11100f014407c03035450004000c0903542c0105854002001040c51004000700e40c45100b44840f0f80200100f2410134240042c00b149402d07007000003080010f0300c0e0000c00d400ca802c840c0b4150303080d105001c800711854014407170f00074015881c0a1f14a070a02d90440082c0410321058000c039010301c0e45070b50a168480c8007a07040d120802409002054120200e034806190f1010054442c0c1c500b00d0340c030036000f400e44541d0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 459015305 1250 459014055 459014063
    0x1506060f1309020a3b181626010e0c12040c03020f0a14101b0c030b0702031c0b010e060a030509010507080606090d0302011112061f1b05010209090103 66
    0x802c069a243c000864070450340782e11803043d45c50b0580c641810b044494103110343c14404030328403c0015036510288141a180140c2030314078018a8040c80f551600403110700228007040074003410005805180d140c030b80c0307460804100c0c51020303440c150014000c0c42001d020b507040921306008200c0021030824030148a0703070180b500c0d1090145540140b0001e2040320241500a0310119420301000d180e83d8000103140c1d90a40c0c2c0c40c0030700301041d00200c52101c0303100d207028a50800402d0301d07018041c030b40013142e0a07030f40982c641c8862500c0d50362090b42e0301d00c0707510040d040903048445440d403000c01950080040b0003060501c500d01900001c0010b040d41d00451220021035641c4051000c2400240300343e039400704007420f0209260400c3c1d0001500c5015030b41ca9984681c40e01e00d070900415101390000d9080c044110300740b580394507094207107034031021040790309a008401c18100444030a000075594207140e115503c5200f004103100340408035000e400002a0340c0c3d07640802041000b43c07034070845a4025405 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 459016555 1250 459015305 459015307
    0x300b0a0e010c092612071703180c04200702040e07060908150601090b0a030f05090d02060c03060604051c0c03060b0f04060302030319031b0806121506060f130902 71
    0x10200c0700e40440b09000503a410030381004c1140050700c00e00298054443d40840300894813022146048100d040c10901032900040e00402488000c00d41044c51030001c401d24000d503444c002000c3c5c24003007110a9028901641c0c840b24a075909125401c034010882d4a00140001c10341c003030f801000c50700d4110b2a510080000c0c6100c2801c121403c02403044814409007541c5499042c1800b8000070480b0f11030780036000c07010500140c0050001c0c0294000420480c20780070522036440c0c80104c640d110503c00c2d001c640035005200001d095141c01c070080702d12030f40c0010241070409040c901400403d000c0107040d080c0420a0780341d00000700c0d181c0000341c002540700e8075010801c03047d0f003400d0104030241341018a0103681030550510040c0c3d000300955016111940f0b03072240402196008030050032825005201c40075100340c2d440b8206601c4851148544019100c9002189150380081e40c2e030300900f02a0003550300071202090051802d24010100c40e42d282020394240142c40b15000d60f520016072152200c07543c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 459017805 1250 459016555 459016559
    0x180b010e06010f020d020c01050a030b030a2126060d050102031003030e0609010801141311040801050705070506061c06050708010303270905060604031b300b0a0e010c09 74
    0x3078400410f4501011a02c0540450b9000d034202135542c04903c0780b40b9050041c0415501d222a100743d0003920350342001000c8610a80080c20425045109115642c0308010001078000f0342d580a51501c0580070788030f25401d202070104a060403400d42c4042d1040e83e01c01e401c01c00d0800880c109001a40c05001002c020103415491403501404450104810502510b000d0000440c7d40c0c1c1c0150066044488424902c81030b0032480c0001222016004110030404e807400300050030188810b401f600640300c001c0000c12141d21024001c0d00e441c0a005401030090740410005142401c040d10401492081c0300101e2090100f00d030345800c01d13118202d80d044009080e08004000b8151302c007c02c1e106540c0c0300c000c0c103030b18000042c0350004000c6190041c4405241c448000c00d50716166001140c009540144100004e0410400c2c4205c3c80340291003844141c84c0c1c4030218501c0c03500307a00001d10001509000b00c031010941c1c0e80d90400148401043e000305244d44151402c0c0480080c0203405104041daa20031000034 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 459019055 1250 459017805 459017807
    0xb1e0304031106010f06080411040e070306050117060402031c090b0c031801050f07033510091b0305040c090c02070603110307140d020c0d0e210709180b010e0601 71
    0xf0340164010100c100045404000340e0760032180c156041504650b8803c100caaa1001241c06001d407080788042030310955a0000c18444103502c0981600c400000e0811654454034152b6078030302050b14041d62540020382202c034015442541e0824130882403e01c11106903841c0f01140142d0403c20190b0500e4200062404e4802810020b0085006007420141d050102c0100c24420318065a2402000c1c41105840c03504800072000d00c4c2c400c8001426240c05019641e020718246815065500c10f504086080b40810602d00c0350003002c1260506580082090103440f204801601c0090001d80710350a000101189041081c010460040c1c090307002000514a4804002c04840c4040d218541140061083c8008a54006400383c040100200560380760100307280c1c0d8000a10508a00301568490703c04200e14003500071300c400603035240443c4c0e0107940035080300c90b00500d8171178000c554417160007050301131100004d250300c603549040349001d01032a0800d6036a10001d03001c000380c0000c0c01031a81c06042042c95 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 459020305 1250 459019055 459019063
    0xc0405013c03032a0309170f0a0305070b25030507030f0e0105011d04051b12160f08030a0e010f0e030a08090405130b0604050a020c0607080106110102130b1e03040311 73
    0x1e40c2d0b1004440c1241c280ca5180100203002034042c00c80a900310424668984008010380c1040e900144162060500c271131901500c07c0d071100e00c08641802100c0006122071005c207000581d4000b481000c02c41d40703c2518401c40c01024014140014142e85181141031008a8031500900c00e5100e0000541c1c3e5040600c45404071005100c181d04001594081100003034002c910007035101d095181c680600e241d21070001750010004858100c03103200380f40c101d03041540c02440c004112000c0f1110380a540d80c466000d592244910003080f008541d2001d00075090794030810b25034654913000d1400d00b040340c96a07000282400709021059495032000320f078a44140c505032081c1604081c0da8a07145c490b00056980f4000c440100414091081e41c1d07c0e0009680c2e220310f60100c0d25400003443c195480c910348940c02616142e02801150006003925201d010000c1c014800c0b01e000312100c92019014a207000403c04080c1d1108180015502d001d0024020060348540698061480382d03c1741809109040352691034 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 459021555 1250 459020305 459020357
    0x3080316020f16032009040b10060302160b1b0a0504140d030903110d0f050d171e0a0f020a020714010306031a15030715020c0405013c0303 61
    0x3843d08402100c480003034040c03108104680d8010300c1151820307620956020000b80300c0d0480ea42009550b01040100082c100655100d00145500e2101c465180d0400300c1c201d0150640024102180c91034010104505450481d40015450407407008441d680c502e44007103800024040f00030441c04642408600d412900343c071a01c46041e103100e030900c0000d440041c04212a84005010050000440d42e030686515170f401d202c6640201c00345001000d9407502c16500d100d50b0b40c0c88030000d114000ca070541d802d00140e0300c82c025035003842f6002a2484083c510810018058080c0c69481d503a040c00f176008a60700e0010f04103805940d00940311241c41c10103419280040400003d04040c5013920610024800307840307040170403082c00c0c07000d00c0075039901c5034a03400712860790811941403040d49000629508941040802a002c039802c1e10305200840c1e0030f1105640080c0603150f45161014290030442d80c000e04120306810401d02d1002d031010001e4a8162a20b0072a002540090903101c03800088000c5100700201d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 459022805 1250 459021555 459021583
    0x40b0f120c04180323040b1201090f0504120e0d0510091202010920010c1a011e0b031303021009110a0e06030d03020f0d050a09110a2403060308031602 66
    0x104000b1658000c0c011140790045c2c070744c0c2d00c3c02d008601541803120b4058070054014a103c2139650500c102c03030021006001d00c5000c6c92035040c1054800d990440e405014000c6d41e0001590194185044c001d0742c1c0c500314848169000b041002c402c42c00f144040203411500449510000b407101907c0c2001003d9009c5403403070034150780c1410341c03103000900f0119505040700544007190341c030000d09400407944907044000c080c0240020305100260700070151100c504a40040505080b00c3d50256030ba0110b0403428806c040400300103200007000d00086054803904540f1a206484c2c0260f10210305508880d01d58005032480104203030762515909041c0404070103484000408506c5240110000c0c1d60b07041050a13080402d5000b15038400400300c0b440580328a4a0580d034140041d00e0705800c800010400c00c501030310600d00000c0004620b040000049040e107840340c1580c20b414207100c2e0341c03100c02240c4400c0b80040694650000000c181854040e42c091480746130401030000036a48002d1406488299401c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 459024055 1250 459022805 459022841
    0x2508030f0718030b10090e0105060a06020d170601031d0f0d030e0619020c010606081006030203012306070206180108150102250f0611060c031302040b0f120c04 70
    0x28501c0702e01e440220b08a0b58002400042c039a0b07507000c3c03960900a00c1e1301c02c030030036414846002900d90301900000d105007800d503540e071390709662048100d0380c902c40b0604c0c20f00402c1000e642e010003149006051a8800c2041c10f0114071100c920020102c03800c9813070891f810640040c202c00b4500b4505116100e0751042a10707042c0224202002459243c0c06d001d0900d02d19121040c542031030003207464064a40059442008000d003640e030340700c00f4010b610120f82e0144040e0ba4000e02144840c041c0c130070f03039040c2d07541c4801d19900301041074240c0400c41d4072351040503400744003404684016520000100070702ea21070b400640c42e501c0c4910001d400500f0150419215007400001040266400183d00c0c4800034410780031401009244590032101d5a00c0c0c222a400c82c1d86580080b0307150b50000001d240b071441e044202d4590350790740720100020f8041640e84a001300d0410f03049001626058001c1048080001c188103410010038001840c4030a1100c1601d410790000000590146060f01c00c0711032052201ca441 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 459025305 1250 459024055 459024077
    0x605030105090c09010c1e022d100201020408010516030b041a1e04090302060711031602010507020f030a06060504060b030606120405120f071401020c070501052508030f07 75
    0x507240180003000c55800000c0410181300580c4500ca040141c607401030411321030f084855607982d81c40e10706d910080c0e0140307242c09451076071115085c500c0301c220100c415108280c814154200b0412428030050740d82150740900000c15850428490240580c3c2000e05006148030030300b001074255840d4065082c4514a800071781c0c04030250780781440108020888030700c0840101184d51218140c4007001182e00146815800c00c201034001070010f0088105071546c4507404001c01c201130303a0b446803001840c8850340c507900083c0154000d1000d401e00310b00c014645880128080040380ca02080c0c0041662001d896110411403401c4ca4450640544240c0111919501d07000780450803038071910814403000101c410001d000d010080c0881005441005034607981c0b1041144484001e0b00705200035a0000811700b00c0321230f0107030305100300c0e68428100700140080c2450080103490941020381143c1040c5039406042c404002d02c2c0403c107107403903c901b0100b5140e0030144850001c225008200409104c200c42c88 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 459026555 1250 459025305 459025309
    0x108091c020d0e030f0c060d0e0316030e0d030f0c06020f180a0605211314100606110c10050f21060103050402180402040b150c0610050a0308090402040803041206060605030105 77
    0x1c2004454402d51f15541e503020204290001031280b0a1026214000426140f24444001500d01481402942c9040c601c401610420100710490304d001408500d0b0805d59031040360040d003800310b10602034200181440009910750300706a00282c01d00100320405507040c52589484110200a41450728020f070500d07c0141c09410300304000301183c040c01d180800029001003c210344c00c030b504c0340c0c000d04c44000f080703000c4400c03950740c2e03001c52200c82d0240c200342001c260349220300040510404480020490003440005200811a0000a4004200040210000110481000f0f1441c0f4030503992840c6001403140512401c1d48000d4031403410141014203200250750b5007180d0040920f10000d40314815207883c80010b006140c141000707038109030f0400d00359691441c800c02500c070766203681d01514110340c1c0b01c0d01103012800140c00f83d940e01c8090760605002044094010b00303980c0c01d0140c4010315140d1200422840d6807c00e03804400c100e015a59024204451400b0301c2d402400541071081c00c40d410080 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 459027805 1250 459026555 459026563
    0x2121c030e0703020301060305030d0e0111090f2b0615060c1202100c03090506060411031807030803011e0605030c040509070203090a030b06040c021204050108091c020d0e030f 77
    0x88420805444400802010006000c04001940e009008010581d501e00d442c03074582e000704214065842c9002c0d00e82855044c117000320324004000aa04c981383c2403500e0100302000103e441500e400c5070700e4842007015608107038041400c5271094800c1c43c0c0c02e4505443c1500c2036400c514010041369928640401c40141c0105078800032301e60019140c40c3d40c041e85c0104078600b0f0303598124541c20b5820811201d000315015400312002070b0040e001d4034000c0e1b40300018841a02c02c0c0d805c034003089000410010b101001c40b0120342c00322038014401e89580d03580d2901c51007000d400a8020724480e41e184000444220290107800004146509066095150241d003850060040d407103124001d460705400228071034824021204007040062200d0003243c0c59041c0140407080455034180200e10f40804c541d05140000f8018841d040c500045515150030203004541004001c0c1c0108903130300c2000d000420400455036034001800c069402030101d5019060010b2040d4808010b00b8017942010240c800c00200c042 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 459029055 1250 459027805 459027853
    0x30a030503040807060c050403031e120b0a03050f010b010e0306090a0201140c0102160203010f09150207080f0a232820070e010509060603070c030e0a060c0212 70
    0x10501079102ea40d50304218003988205600100141d00c0c280e1112040c541020203801528000d0f03480c4074041c3d04040d56200010141c1b040c0038007040003a04214011000d50700300d080201d6024029100180d40e1340c2e10a440d04401004881c07059440f52490146540c1c03048a054065008800600c410b0030080d800f982c803120385650107410000760100804142070080226200b5540410007156076041e0526609420740762284100d1095003040341030030440000c2c2c042c001c800c60b0400001c3d030301e041c10201c0b420700942c810f82c0122040401841402c620a40c40c01c044c015041250316141e070303030018504c01c40030030701d1400e1115040290305000040d480022881500b0303041440c0c0c0b0300340b1041700b400f03501030f1610240048003111144207001d00321510740c004941e07001101e4608071020032598886007001017030501161980d8001c0014030008502502c03840032058454000e003403e010501c00c06011404615840e0407081c0031800e03441f034080c11030414281d03000308803c0c40340c00360002044001c1d4481c0403c0c521 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 459030305 1250 459029055 459029057
    0x1c02011e06030f0f0c050a08150106030e070b0d0e01091407080307170d0e0613060509060106050f21010b07110f010906030c020c120d0f1704032006070519050405030a03 74
    0xc0f640c2c3c80d017004801e0a44078050100140b01d01d05250780c40001c036039500c0f401c000280115495600000360f441c064024000c201a402d005000c40c9814441101380541204500301403240d111224004402028032500702198024100c4024a0b00c4004101307180500c00c0e0b0044000e039204000010216094040120316120802c1e0810399514851200300d014000b1040e480046020785e0b424080842c550040350030340c40c0c2c410181030265075941e6000584540092040d100462002c01034840c511880200810203036080b5070300c140d00071480100918824000f60840c03180410b0000307100041c0101d1083c40d40c103414044030800201020000003c200c14900d01c100c200781a10f56412908040c002c7c0040c025140d00605503100078005c48200c07680c1d840d942e0380c00b070340450704c07403014031401c140300702c5080c0400444001040069100c07a90202c9849203421100151070250b0200003440c00d00c1805402d006d401da556440d40c481200020341d20b08500300507140410b001e01004100700c1e6407004a5040e541c107400d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 459031555 1250 459030305 459030323
    0x6030b0402070507080610060201092105040906080d170402182206020a0305012c0c0d0f06140d0b0402040e162702030915091c02011e06030f 62
    0x20a012401900500000820078001e0f0200480c0480000030301c1480750880352101680c00d50307594016822200c540c00040c0204524940f40250004c401041e01d00c02e030424a0036902e055030b00c0703100c0d030100c40c2d880d00079503099000080740d0160a58020000c034040307404640c01e056507060560000364400c030703050384000e4108840400207521030030f40d00d50030290140c22a040c014003000b92030110f00a40c844001c4601007803400001144d00c0320031103203a8032668a0300709041d11001c003182000703482c070000410480120f101005030202590040c01070412542000301e010400c4e90a10003007400001e001c40160303000700101a0000c004c64809145690056016217000526503581811141803a40d241c0500701840c800b070000048a01c98000114031f003219249000e140f0700500d0824030141e100646450701b60b5880210b91000050f640342c10250080c081608031150201c2551306041070520000c070003001b40c0d41d644400e005c0c20104c075031341d004000302604c0c041103094210780c0d9032208420124000f80203116 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 459032805 1250 459031555 459031571
    0x90e090a150c0e04110c010f0f06120b0a02070204110712110d02071403030f070c031a071d0f041a030f120712110601090504050d020a03020613051e030307270603 71
    0x383c4012104010a410001e0065072008c00c0c618018120b4440403403101890a8400150400d94481485009500030100300068880010b810f02a401046050b64031958444404503220000c070000c022492003901c0c40c17401e4462001e009400018503896804141c3c201000c01d00c1c6d029401b00d40d40003942c0e1040c1d451503e810b40384000c40d24600034200010301c40c02c030004a200c14040000c0d6041d085034810303418048503101000304440484025100c0c480070803641694070103402902c62440b4003c982c0a062000c0c01300e8401e00290503590072107192135004c2c488003510703203c5040c18008140f01040040060420513081040440345105045024028030038064a01640c1c1d84644c101c0e400c0004010120358007540c441ea6080001d1006440848203485800c0b1101c400c1070011a40780845900364000d0080d5074ce450301007a074150700c14403080314907000b4446803145030b41660846407007245101d0015078581c5040caa01400c032900c0750150503120020795280c00d004000030303644c4d04240c6030f02d440d010600340 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 459034055 1250 459032805 459032831
    0x30406120608031809070203160b0702010f0c03050a0e0718020306060c12031012050c060a141207020705060c030d0b0109030609051605180115090e090a150c0e04 71
    0x20601d038100301c1d124040054203c06a0f03480e004200d0202e003044a100740d094035030a905a1342c0f8030071321198070484184621098042901d041b0080d91220302400045100080c00074280102c8024071202008030395201c0502c11244540d110b11105803190b400101482c0381000f4903d40c00b6090341c0000416a500000044d605484600644805070170410459400b40038410b0300d9a000d8000300c85c03140d500f103941c500000d210f55440c40e000c098540c01101404500e0480fa040c0015076012100301c1d000d108a00f0320a0000d05950401042030f480c111560280c5810110700003800c1c204154031041c40b442c003e0107a4000c8540200c01c5901e6050007036800200c20200c600143c46070760243c0e00241402d07141a040605010380842e036060908003e50b065020f2946170780400c90b443e0362854001c0c1d1054024401805042a46100d1035120307403c0d8140400600d58071000f094400740221070100c034a41002d060101001042a107080c2d041c030348c054090140404e4824000d04101016000b03605c9240c540c04914046 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 459035305 1250 459034055 459034061
    0x6151b02010e0d0605091902060d0b0604051504170607021b1311090f0102160603050c04051507110f1e0d06020d060501170615031027140903040612 65
    0x281c03009803481d507010300039044c100c3c02032200311983c2000c0d004040380070910041c0103614a8101c1d074014092802c144613071417080002c2005092498008000f00000304240e42d502200d40103100a059115684504155854196002d500c503050255413040c0e05201c0580d03004100144a102ca28428400040c00e140c005251448961400d03d4428680803c0c1c001184542e80100700008007502d00e4100702c139000004980c3e0703400e441d03114180d04000b0401489100d200ea0030140d0444607002c80c8034102601c4400051a1102c0c6ca00500c41407640080c4120801807059206042c61b0411a01c008c1c104600c00d010540c0381d019920a000e0a503441060038403075a81d12035144d041103400140454a400c4515482d40041c0081d000e514007050421040f241005c07100414103200b000081c00e2400d46031091001618503400c003030140541d00341c44000c04a008480c000c4080041d81c3e0b00e40400049039490800d080c1240c004028400545c0c6d0000100440010000202e40481c0c0c03462910034050014510b1107402 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 459036555 1250 459035305 459035327
    0xb011b0507180603051b030601140f1005040e010f0b03011512090c0f05060310150504120b19140402010f12110d0c021f02090f030a140106151b0201 65
    0x80081000001050382d10140c0c00702058074450400c07140c0c00300d109101124154030706245594182e102d50014001480100056143e014001e8894246184650001204110400000030000d48040740400000d0b01c02032120b80108420702020b5065410991001001d10050184940241520001c80c080c21705c02d8440c9149102000000c02c0181c15600d448860182c04c0e00c038081ca074814084011a1a103070000440c2d000310206200c0104c10351814820740000e9104012803000d0150038000010492960981d001455100700000409890304418801c4a0b03031401030781d000a2072a00c03a04100c4240120030b41501b194090808141d0280b20080c100d0b0603000c1c1d080c1c03840c8114100f523848206242c86070064595190300c2181408002d8041c0d504998503e42461807408040c030000064880c1d4030389070f0040c01c00d0302d805841c2c0c5c13104003450004070385007103036503101211143d41206100c3c80c07004c420722518010b0300c8050140b200f24100104c3c01440401490b55144250280107940811a8007481300206 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 459037805 1250 459036555 459036569
    0x121a060a06020c06091507300203090409050703020904050102130f051012110c060405011d0a110103060e1501020d031505040e010e0105040f03120b0d06020309010f06091d010b011b0507 81
    0x350340d94192503c4425112030b1080401e1640071a8030030000d0010401c81c08c21202543d81c01142088000360401c400340c45c01100c01e82e000d01402c5804000342c0c807074000e9148618000c4d00050307600c14400310400c0d140c4440d03500105240c00b00000a004543d616030313240544024624001c100c20509030003880040c85da1070400324500e6000514445141c4000c03400903c901e006500030880e250b2a04100d0341003003070207005803ca64024460800000f41d442280c090709aa041c0b4000480c917403150103080d552070040c0c034001741801c20b0f0704002c10150b0341000190302d0084a40b03014000a0030080005500740e43e00e00070b052003280c03a456084d1180c20258055084044901e0080c0228281410001ca042c40c4142080d80003440d159074141d0041e401d805404817814000c0e1110300c1c45002c41d11100000e4202074084034065480fa00c8492004850380911400790a14020026800e4a80f401000c0302d0642071141078010707410881c90741e603c1d81e007080d144800c50f0716404400000d0801c91810600700041904920 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 459039055 1250 459037805 459037807
    0xd1803150608030a0c0605180a020d03020c0402030103110f151b0109080a0302031b040305060c03180106060504180b0f040908040b040303050301050a21140106121a060a06020c060915 80
    0x9a9105c0c0c1c0404034141c0a80114010001354807010703105d500251040c0240c0704160700c4851282d00504120844407001c034040d00c113603131007900103100040c1aa482070344140c920780d822a150b010340d89001c004101d039440301207a010303c01510325003c403a1940152811006030203410341803650912400c0d0030070507011764001909940c81c490264060001c0d001551038142c0154100451108402c2002c11503041c3d81d00b207030003031000740d880d28a0743c402a03000a1194007a085000a00040c1a0090180c10003403c40350310340325200e80c02c1030310040000245046c1c00030310509040d0070780300e0f9403102234100c40040420394006c10840c001e82130043e81449203901905440c0c0d0005800003d15030710030081d5040c5e4070210351847c2003039600c41c1d80b442481a16649a80c040b14014079007000101c20425a101d864040d000118490741d6880901030322038001031040d5503800404c0024003581c49403c244940c0510b0444400303046c1400d0950017503450007405400c6000d10000038540c4410390313485489101c2c0b00034403c00c0c1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 459040305 1250 459039055 459039067
    0x2e09020705010507181a0708090415140103141302040e0303070c0210050405100309020a081f05060316060810210c0603020a30090803090d180315060803 67
    0x24000c100032590800099900440351017094442200802100c400358180d0300c000c1320f00c140d90342107a8000501101d4070141000307841c8094030b850141c58101490301d54803110312031800c0700c1262006043c1c16213604141c541003003442e02c080c1c2064165003110440307218194112551000c68010103450028103460b01c8080108642e142e03000c002c520041d0310a4a90840390040f4400c01d41d041c0c0598001d850707018015040000c1014800d0b03020074800c0b0b0006060340a10307a62004440c2c18115503172681010b401c4c00e191100c0244485001c3c0326044107054005010310441aa051280c0300703124007440c0b0030850340d0404100008086072202010b00000108007400c1c0ca0340d189040800105a601150313140c2c0100c00025142d402071081c3e4aa00e0390540300d40300b05901d202441800d5a800d180c6540c0c002d840081032010011040c410344010740c2c815107103260359050400d207040c40c0c03483c0503281404009482c821030740140244c5c500c1d03c04a0f0340c48002c0640c0c1c014108084000341141e0f404c440e24503c0f000c00c2c4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 459041555 1250 459040305 459040313
    0x318060e160509010e0c030901060312180e06060403081803010c120f0b090c0c07030b010314060108010504080d0507110d02060709090603381006080f2e090207 70
    0x40c2511400707414403070148554402c02d10100e0102407180200380d000c5907002801614030800196805a0711500004140d07440b40c0e651b0a07001703490000d0400050300c031000a4840744100c04038802402c3d060f11034441e9407500c000015444c1c8210702000342041004100300c82c48c42c000058842c001280100284030050807800002c2c0075044180034041e040b030a008180c8400b42140c8107007030345244c000c0e064641640c1c50701d50100040d40800f440711014443d0480000c0842c3c40075000d540651300c107465012628419170001850480e06030410807581e4134200501000a180208840040100020100300341ea1000d005a881015141d008400d600484640d0754980d035011030303106e04c5036200d603c4080100c0d03210202c810440d5901c2c00024118503030200c0103840c000400009161b40101ca5902243c81c8202d207951118a5000b5118013106148004041c80026000021690301084000418409180c03031514060b812001c0d01c4000c101b41d990fa80d10121a011010030180501158003056503544001d00d0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 459042805 1250 459041555 459041563
    0xc03180902030708131214040e15100206090a0b18030d050402040f1103060909120f0a0f05070327080d0509030609030f07060b060415080402030c1f0318060e 69
    0x10310740c002a010320006803085819041a01d245e540000c0c55550402d651071064950300b1071403207800740b001c0050000150890510794002c1c0704450b00a64071282172500010302c24406014148042590403c40800c00215030004a0b01c400d2a003000a080c455294034628980400b50a09450000d003c0040e030414460650380000d80070754400c3d82d080100491074010391003100e488144a500e01881000401d01502c2c0c010801f94100c2d140506444140400d1181755016900c00e0b6851000701001103001c40003113401071110541c0c081030303040044c50488141d600405031b14860004c00c9164000c894510503134850440410013604d07051044541d00224800007501542040702e20501c01d1181500045043c0c10200940300104003c0420070b0900d81e0643e1150040d0051100260304034a0034000001c15207100814406c0715407180c5c03120116414180181401d066100c050030f40604007210100f0f10b8000218100100b401c101d04d40000d002603905c039000407004440d4005441ea03400d0021107060440c2c042 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 459044055 1250 459042805 459042811
    0x20f03070e010e0f010e0d060e01090507031502090a0303110a0215040305010f0212160228030f0c080a050903010b040905010e0f010b01050d05060d0c080d020d0c0f02010c0318090203 80
    0x10b210f865060260008000c0d100d080c0c81e04590004060b4030703000c0518181000c00c407001174412000860b13007c080950f500c4c212905803c00b590030398003d2200f08184261150030703104485004805518040c88031001c02d0000d207042c40005d00700401e205000c81c41e41010b01524002c141d0043c804041e040603940034105a41090109aa00c6c2d440c2c80440075850300c0f1031080742e541c240c85099178001c50b5074041200031101c0b1001c4015007940210842202c4c040c0400c008010320000d2515124142040b0342001010120107540c4403086c00881046000450a40801c0c0d0741c0780380003032904955641c402d201082c054503180811640250610560a0070400103401c80566071011b6800c940c80c600841c3c009a099410301208240031030400c11029401e500207411060f40080041c2c090081401150707524108600580d220752210b1304000d850101c06a81030141d0707982c0c6880ca151502000305240c454001c008881c0034001c2c140a070130b1424900700350046070034504907111894a855110765402ea810081c2d0302c22 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 459045305 1250 459044055 459044057
    0x21308070513060f0b1c021204110d031e110a0503190903080304060504030309150b01090b0a02071707030804150f2c0f060d0614030d05030a0f020f03070e01 69
    0x751030601e8002c02a40302c2e80d021202582040300c961860b01106030001c1d485090044804a10005030700c8000d1170b10300003002c01c0f054107850580305103418203020801c030b6100d490b03043c0309810094107035000c03e52000040c0c00f80c4000e40d04002800c08402010b60307140c1400340922240e402001c04aa0610030040050301803020101896103004170100000c0b5000c1a50707020040c0f540005002040100c2c00d507501083d0310500c01c0c18000391240c001d4684484110450092403259030300d4075600c040c00e5078010810b00007012140e03e010706003c012800070317480303204500485915030261b040c510300c1030781c1c108140c0c0c006507008103400b070b561a04e559a584441c5068a03184000c80d2200758a100c1551081d1048150005159100741030040c2c0e00a0903420243e4188441e980b110b160b4003043c10306c0d46d030f410003400002686500041e1051806400c044d1030820401c980c0d102c0d4010202446401d9004400c036913103c500308030001850079080c080c0724020f000f140d0440121141c04010424182e4002c800d844e881082 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 459046555 1250 459045305 459045319
    0x10501090b030d051804020d0222150302030901110304050a060b03032a2a0a1e06111606090503010e0106060207060507020a03050a2f0109030f02040213080705 70
    0x300d010300c0003500d000590064041e40801100d441c003074800c0c0044c0207810400440041c9120404001030266005120f9010703c80340c1c0050703e025030000d06002c5516101c801140c03003003614a0030310888280184004541c06040d0000001061402c080d4000c100511030130300959100d042c03e0403c02e9070340c540d005d801c64903d13246c50120310080c500041500c90011803510400e40d40b003c64030001072441d01404c00c0000a205c1c45008000100b1a150840703907042d0309081400c0c0c0044503804000354020240d10401d603009082d04001100307000905030f582900d00a040c08075003c9208003d9900d40710700003180380344030105904089050381d4030940482c21100304400900484039050145800c03901c03544100d1000d030348102000c100b4a070049014009c41800188010300099032620707410304000c03058030200c2d43c981c801904440701c1e4080904030030348110301140050840607002c00103003441200e0701014040207011031340b00003103542e0f42e011141000298034a81c2955995002160f07607030341c4240030302c51003002 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 459047805 1250 459046555 459046559
    0x6190905010b1b01140109020a0e0a08030c010b0f090a0e0307170a0e09100315060518040506010e01030b13080705010c17070c0b160201020c060702030a090e09060a15050d0b0603010501 81
    0x3c140140d10304031810090700700060340b0300350344403000b540446602c00c140040001091090798828204000921400c2c01559451000342a01030071a8020460544a40c001c200c2401079a1640c00f0855031100e203243e40010900c507a0715445141d4055218004c11815006180c2e108400c1d040d0064181d8210949842e0204242801041500b480481d020615080140403c0012440402c40078041c1c08010740006180d58569011502a0038035010307010060301150b0a001c20040100a114010020340142d03902c2c65065681d160518040680300c034501a8480080405000e620401c941d0140d0f0702c00b00030040c0382414000a4081103440c0c00c50a081181600005d807034500490300b040005034095010001c51350fa03540358100040024081c0011036500f4003048001035000c01500380101d620342c00960300c90641e600000e09a00d46904040025454030040c824440c5001032002d0304104050004240540d0000000f2442d10040c0e0010313a0103000340004400344140c010f603680c05500280c00030700941e1b03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 459049055 1250 459047805 459047857
    0x50712050f18190b12090c03030708031b04080f0d02160905090307230601060507170a0c021009091a09072d030b031903020606190905010b 61
    0x10045070300000d4050020002200c21000360310241c0d4114800908000c011101d8403450302c0042c003190040e24034580000382d104420007070380410a0344104203900421004d903400c000300e41c585c011a94018007841c00480420b614403600081e125040400100b219119903440b000707150783d01c82a096140d01030196080c403c401c00c0c804507000c5202c50444005581d03903442c1c0000140207007802040035110b40820700c0a140021601c001d070a140da80c8048144001c0c40740e05218905011041c0d00031010320604100600c0085ca0310040d92904002c0d0803591901c03007110f481c06030b070b80310300c0e406000b548a180340c0300d1500c601350031000d018242d94801c8010808054856200896200910701c0b4685c865140383c001998141304a20880e101c050312124410701e500a400b103441350441c851480c00100b5100c1c6150701c240e040402c0200100c0480803030803590300740d45841c080e48481019010500410040c403041c800380d0070305c610b54030040802c0c0000304415a9611460206c0c0d400040180c0c20034280f20303c42e01f640b0303 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 459050305 1250 459049055 459049057
    0x501050c011e0605040e01270507031202010501030519030f050a02010e070e1f0b0706020306120303070201090b06031501060f02010b031002041d0114010804021f08101d042d0305071205 81
    0xc0e12884440e2034a001080603900448036881e60449d8a44034110002c800640399218152001da2076400116a550451170a5402c0c8214528184e582240501505c0c1c0440d40c082245581c4540c03a003489950783c0d02580040780500302222010400c0d00c564000081c0030800207003007030720842d5820054008540001891540d0b08414441c2401100040c4400e0b404144298015900010001d10f81070349091018103042c11500f00f164010050703590381101c001401011501154061002c40180005e000810080e4002d840180a0f80c010401c0d030254425505000b54049a10010001c0072104480c488070780040c040d41c000c0c086c4400d1940001ca43c514289003801e4060305980c070541602d042040001d00448111303000500070f9a220142021410900c920700c20503030002003007035407200720f00c0c0f40400d4998104002c4c0c0c2e02c0006009020854448561081c90700349404c00d520540361207400c604030000401c50610805820080010700c01c1d007400b09500076000f490218400e0743c1d04d44202c41061030988072 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 459051555 1250 459050305 459050321
    0x605040204050609091e010e09010c050306090a0c0203090607210903030c240203090c040c09080c3d0f090b0405010c0c080607030b03070e04020a0501050c011e0605040e01 75
    0x28420300c0214418176020800c0e69019542002210100b030080d0031465421000f07900c0007005250042c207000b502c4c82c0138001c2e001e00d48428208203155060200200300404401040500ca10380d40b660f88401d01c6109108036050b860008000503242e0401d42040c10544540c2d0f13135030042043d80510145a03240c001d4410200300ea801d511250300400560302d420044488482d02c0030700010681d40f8800c00c3d401284040c5004500c410010b0002c0780e8800203100403201d8003030549081c0a5081d0017003108460001300680c0c0c02e64150b844c0d1010014100a8080a07024601003d4001d1050003402c6482d0310003010105018130580c0d5204004000003000b80c442ca24240240d41d0800010403003170105501070507095484d2486090302d01c04542e03866500b42e046c18002c6e1000c40009403200034034585460100540c001070300d00010f0080490416a00068004c0302c54403500303060080108180d81d45910a500c6070190300c050f00e203c100245400c040c40c0b00181141e00540e0301c074903e0f002c1d41840c00b1405110b0409 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 459052805 1250 459051555 459051559
    0x816030309060e030d1b080115020703021003060e0a05060a12080f07030c05160f0911070c090b18060a0501210903020a02211f06030206070c2907030c33060504020405 73
    0x1501d9027000c1c04084120600300c8642c0c00d62041c0700300080103842e0010094503992880c1d0300043c1e55400c1c001145e0180d00050a444143c2d82001d0a204042d50355100800444003003072010000403001e803a180407240540700320580d80001c0880c1c0c00041c1038000c028000114410001d031803143c01a012910150395076802101403410003036034141f20168580c1d006048000980203550304220b01665a410303401c0c1581c01250320faa80b240320b24080d44c00c01c2111200b00002d002e55a0540e03183c404046100401c503440750b14104801103011514408480c140310203080d40c1008103020031040f504003c6d5642d100c85404900450b01c4207155010022030112880e54a00b580001d8103c0d00e08406110b850444503d012884e800c2e0b4803100040180d035660024079400e07101e1103003ca40d9a191400c0ca0304006601610000300c1010b00c0540c0004d101500c04451101364542002c00e0410218206400310380201c00c4901005608000c4190480b2020550f1502d10040403a082c015941c5544c240010307030160340305242e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 459054055 1250 459052805 459052817
    0x501180b040308040213020a020c030c03010b130506040b0a0f051005250204061d040c08061605030c0d05072732041d06060603040816030309060e030d1b 67
    0x1c00103071250700c529030030074001000092680d9400c590707142280e000412030700c00359100484d02c6c80329003014800800d006d00200e000700805900c0e40c0108441c88408100083ca5a03034032000a00c1581e0f0300d50154010100c003820f0306035a00e40700c0c484c3c8454100913019052082004101b180e007405d00c19030442d103000491030442c2c1c20741c41840c501007003000c0c62a03000b02e0f406038903128041500c500d0b403507040303020030301043c00c003d41800d02e4204101c4031078041c0c10030340803900001d00704150303000401c0c03207154070211625000e44d480c2e481e030110030054002d0400c9416400c0c140800d0108155101c500d0b4040e501320000319004411101040700d1000005204008403280929508408031890001c048000d840d00000390170340d0f15901d4002000c980714007a8040424140f0302c0d4000c05288100301941c0c2c0000103503030052460070181c80340c1c03180b8000c0101c0c101368042d21100500c10548a03802420084d03612420a01203141106c84c000d8170394206007100084146844058090030580c1d8540c085401000e840d58 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 459055305 1250 459054055 459054061
    0x204090c05130905011d06030c09070309110406031716020603010323011506030903050d050103050706091a093304050f0402030c07030e01110f030307080106021b090603150c070501180b 81
    0x4401b0640000785420783c18058002c0340040c92b00c40800300b62080440384e80000c0c000c1600e18040003071140f401c2d055400b661032f100d41400018004045e4440c80e0307030b0815200d41c403039000e100480208041240001d4228070040700000401048040d64110501c0781458030702c0a00840380d0140c2210a4100300c0c107022108050708003d0305000303602913201c00f400f9190003442c2200b82c0c3c06100591b0001e903c1160550701c400810410b5603030103004103003e0210011000340758210324581e040207002e680c10440c411000d100b508a03000010b40b040414090fa08070302c030080b1840c152078002a035086803248a005c0c0030200c050501070716080c42200d20607a08191303050306200c01503c007150441c10124126050020800c0b0700303d1610030801c980b04910018400855580c40e00080c0140700501c1030b0300c4035041d03501003408080801017001152000420680304452107581d070800080c5405204514604a48541014030000355000e40044c80c00b68002c000a000d062800b00203010040006100648482c00344808 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 459056555 1250 459055305 459055349
    0x110909010e0c070204230736091b02120408100b04021201030b090d0c08030402090c0f210f010e0414032a060c0a02100509010204090c0513090501 64
    0x80c0d5008054282c22509190169000c80d04503580001107000019600d42580800c414030034142d0b60014151074200714000550b0444400800c05103c0c41c046600d000d47d15180501807800310300d000b004880c4082c0280d07000c80301344a1000011010560060080d5600b40750f401ca0440111402c03603c4100c02804000802a2000002c1c1810340325540e2042d020481000c00030001c120321806503018840c06061410003200403440c0600c031010940901c1070328802040803410002c1a6984103405440480c0743e80d03951040c0040c41e20984004220101001c00e40403112a05401c9050030702221092008650700c1c0e4090910701400244100980d0a0040380041d000402c0840d40748027a0040300216410060400000703c00700003844002c51001c032040c515100014001c000c1da0b6040304081c0600f03072401d100210b00031740f034421303d44106050585440100c0c2c41c00030250b04450041a014108002100701640d00401d5540403480d101001c0101c070700c000c2052012440b815040381c1550240c05164021861 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 459057805 1250 459056555 459056579
    0x6030519061422090b150306060f0d02041410031a0615070501060803040303120b011d04090c05060a110d08070f080903120118110c07050d140307060f11090901 70
    0x10410f041048401c0007104001d001e4020581c86910407a44410300b45040b107a8001c060440e0000c051095200c0801d002c41e07500c410040008080c1c045c0c4890202452600128014100c0124000480500f1408000312041e0327000c2c030801aa441550a141080e0781312494441e103000503243d075a807141119030005402c0f81c1d00c00041061364030030b20001c1030b0643d4403a441401e50300180e005801042c1811061101c000c2c41d4407a080c00c071030342402c0240c2d42070000b0711700c000c07c203442d200c1d420300441d80c41140b6010703c41000c2c010801000028031466845000c2d20008050311022017040625119546e15100128003c0b0240d030310544043d5070b466601840700008a403586005400f81c0120b0000700140740b141105244c049018024041a07803103c00d104400030011501c064226501440090043c140d41e400c0200d41c1e8412503070202c07641050f1104904006a1f201000d009040722407000184400811185800100340d1070341002c4100b18151401c00c100545100d80040d1981c0b208510005001c80c02ca091 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 459059055 1250 459057805 459057829
    0x5070f2603040b06010813060e100f1b0806030f0625082806051009050114040b03013f050615010f1d0a0b0706050c0408030a110313060305190614 64
    0x1205511f503244c99134807044100d490146502c11140c00500b001e060a202e9801403250441e0740e210104201010348455a81c087c1194070143d0410207104041002c960b010481100280c000c1000d440045c207028010740d502050b00c505d0300c20341a0303500d0a60090140201e114034403451400158000180c500c0070303c2041440350012054025940e000085115281c9108440900c40c09841c3d441c09a402d000c00506200d41042c40b8074a007a01c100300c107003c0304c50b00d001664115600258001100e150030100e03c642c41300040c0480c600500136028100440301c03040c401082d903a0060003621080d440c0c4003040056204a20302440c0426480785203407500c4c500c103140886040e000030b00b8003527020810750b0001d9941c162660081a8038032004c6075440078000c083c443c543d001282e21000d41d10701840e10070515203078050022920103119841183ea24000418021184480d0f02c1c80c42d000300c0c083d12581c001e40140802e90700543c4c0c441205084000300c424611985040c2e030b0842c1e245c0c0d08984003070010401051484 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 459060305 1250 459059055 459059071
    0x209010b0a180e0603060901050c07030e0621010312030504120e19060f12050103050705133c0902010816091203080f10060504060302030705070f2603040b060108 71
    0x1e00c2d812841500520b1620190030012655001d9040c010101807a001e005055840e040c0d140506006483d124002201c9100e03505081c180e841156060000301d16006003440742e02d00f4001c000070190201c0f038a88489060324031803403840c0031941000000710100c030001c076802062003044000082d82d0500400450f07071020002401038cd0381d074046518950071116581d00032800701e6582d0399184069608010308450004070404100107171340c5191038981e81ca99140c440d5034043e94001072540d90142e043d800400342c40000404070b004960500380f1100f089810128011000f4006050301c03114003c0c580508032142d50144c0d244090740d1510301c4003912100709103040005229420a0004049a4102d1801d4000340291102002440c246044000803000100030f200c003001007100501029401c10160390070b0741c14510780140c8a030b542201c245d1b89489525009801c5844c80c14001040205d1f1240d1658514100303201d568030b619440151f5030050200b80d400604c460b8003080081d070654400c100704d40c0c0c44085 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 459061555 1250 459060305 459060317
    0x1106160e130e011505030c090103020415120c0302010f021b0f040b04050c0a091502031821060a0b040e03030a020d02070c030b0f060603010617060406090f0204050a05030a0209010b0a 80
    0x840668402100c0c801502c0c4a1581d441e00700c98802401c401489500804040c1c0161010a0806001401c9240c05000081c8201d03650701454004500060484004d41520031462480c0c182e6410081380d0428284400c0b80003420048400040c184003048041c04800f2544100701c40942040401c1905402d0807001d0703410a41c2d03030001407403541d175074050207000d1040420219038480420100510481a54110200c681d00c0070384881c1b03041342d00100b02c61000605a1500c0101c5640c580081d4540318040000030740301030707503140c6000c070008049402401000d9000c810810700c1c1c2a40e007880103855041000740d400d50024000220480c034980c0042001c803035032004c0185403031070a07902c0f003e100c86c564206440030012030701040012000311103d80c0d0424021a042030441d8540310b001001c5200c0203102883d001098404211180c443d0b40125004e00361a072004c3c0901600300701940020341140c814039100c5c80581000007802d08000c40d40c2c071203194025080a1291f8203021140381c0c141d00c580720038403c01c41 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 459062805 1250 459061555 459061579
    0x40e010b03190c0501081b071a0406050702010e0c0609060c0709020412050105061c0f021306080309130c05030f130b040f0b181f060b12071106160e 65
    0x180c10300560401906440120100d00114100b12446400941205046c010000c003404940a84800300070542801070a005550b10b06034500412400d0100b507103103401c118000c042c0802c000550700018400d41c5564020014110940120707540d60242c01c414540000c020001802c8074140f070380040900d41410313000c0b01c072560f640382403820072a40560300100d6103a00311200d40c0704201007805007640000c0c007203405d01c101d030440c81410b034072071105030a00518000c0b440c4600c0085480e41c83c61102e0340102c040382000b2442c0e88201c1ca54903580406031551013145607090068820017184105100e00c111655181d085550303940c50b03850201e4021305820011000804404002180702c0340c1140f00301d2082c803848049d01c0d00c0349490003405102034882c18841c510b50f0b0b12101c81d100c000070012200a54901009548080f03007014500606c42c9410610404100182544070040c001140c00d0081031a540c0e04018626178125054039640240c840000c4511500d44c0f10034854030036000c4128103071b03000700303041e140d0700c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 459064055 1250 459062805 459062809
    0x5011e02150901063602090f03010c030c17010b0f0a02030c07090614011d100c050a060b03060c030412080a06050907020a0b0a0603020a0905090a05122d09040e010b 72
    0x600072100d40307030207a44a0005110385c0c500c141c5269510358131021400700341c108244007000e0a0b03800c11351410700c156012901d4a01070746c2c0d1a008840d6414050003c00098251030001806800740c109114045003003955403209030f4420810303a82c101d45210303180c2401c04140281c8001c2991051742500f00310302c02404242060441407103100000e084690700041c01904d0041c00c421814814100300c1d060100000e01c1c00080359500c071070080c603014102e64010901c5181141a290310049101c094810700c20310b03894508102403603002c1214418100c003210510b84c2c3d03201a0540c1031004440c01130880c20980036038003030359010f00145600040500300101c0c04c1c64072080414405601221200700507441940c065050110103500c081e0419044102404002d040d5000f040c0040020301c40c82c030075169a0340c00154406028006800d038554404181d440c0c5403c0c0d20400c0c41141c11031090040420001000c001844802801d0044024803440141d4144035581c03042000070650503900c1d00f074039500c03075005c2c120503 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 459065305 1250 459064055 459064093
    0x1050d021c14031c0c0302091e2704050c040b010f0305060a0e160909060b07300908010b010810260d111002070305030f090a050d030f1505011e02 64
    0x55945042c8202520040840300300540c3c0c02d611704e076818188100080740050f103c60740e201c04204031180000d080c060100002c50340407000007621800701e0103103070b00d004600c0e8505c081c2d1324000c2e07010b80211940459000b0400080b03030780c038141140c040341d503041076004c0c100e010f40c0003142c0c460001404081203a644a1008030250b60232034411210a00307245007600840e4010f02c211015001c1102c0c100011404c2043d4045144981480501020700d589840d1003280c10101c1218880b44007075540d85120880d040c4040c20181e1580074808141d4203103d1882169449100c1c00d601c03500d0242c14003007049140100000503d0980b003640c48903c5080c0f64031031810309080046812918071595200c03c4294902101c44c10407030460321907d0402e004020f030742c1c0840c1c0d00409490700101e10455a09103501c03545a40d0740f9102d051000180315000b451100305985800d07a010740001240100207001c4905102114139000c0030600a660100c2c2e00503901000303400d050781410698580c2401180d00706801c1703444590f48 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 459066555 1250 459065305 459065317
    0x40e03090d350912120409020f0c030a03060e0f16030e03130f06091706010b03061903050c040605040209010210050c07050604050705040c180605160605130b01050d021c1403 76
    0x1000300001480c0f80d81c4c0c00c0c8200580e003003407807950103820420491080340c051481984504080c0c2600895002d020340888801c0703400481408040740e540e8203101d03c024020301620b204100c1000d0380100000d81082840307200c2407290b250005100144800760f4030070b030010000c03e02511800d00c4280095000141d6400700a0003401d01b84000c108c566181601c0100310500e540c0126071004031440c0c640b140d4600000e0224103440903094450340340c5c1e40306004190000c020f5048848444d840e28400002c0c0b0201207890181c003041034409000482d00c1c0c10500c01644100e808071801680800151901c58206034007280d04030740d40d440c2d51440c01d10b40c0c0e07c0d0786250810940f41502d6980040b01e0070032051516208420040c0324905210000701500706800c07418844a21418040c040d001039004204450b03040c0907009958850010401818100103100401c031900c042241c01610303000000c03c040c41d04100b07450f00264001d00620190b09913585901c0300f8003030400115800b42801c00b403107800301818405000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 459067805 1250 459066555 459066653
    0x190203040f061d03120402010212040b030105030106050609130c230c0610051005031b04090c020f0105010b220e0106050a021605060901081f060905040e03090d 70
    0x101d034002800c0160880b043c0d01c1c0f803209000244540c00c2c840031008000d43e0400410248070062581d40d9000603802d1120b0fa004802e020b540019010441104440165060f180d0a030b0080100c29240c000380a070922030013010070351102e010111044662074642000c4484e041314503008104a219030317007080c03025800c0240d40400d44030104600c20b86440810a80f61301c10100c08401c9101485d00c3d000c07a6000702502030201c10450f002000400c2c003007991824010011464030010307541c5503a80e080300014001000308000501a464841d03610250501034141a640d01c0d213a5035141c90003800301107404201101f948580089420700000700a00b091210900900300c0f0344a4550340e883e1900001c1c201400c00007944c07105c20700b81c0401d0009440e03000c10f640c5054000e0074182902d407110340800c024a9001150503080501c2544007040c2c00d84d00c01d00e00011030300c080e1000e07c02c070501c04000c583c60740150303900990822840842c8002042c000e240100d803100c105c06041d000340000828048445e04c00440910f = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 459069055 1250 459067805 459067823
    0x41110080c2d0a0e040203010308030417160f11010c05100905010f0e06010e0c070c0303030c02010b09150a080304210c09380d060209010e0603010f0815040f03030519020304 76
    0x8a00b450b042030300c40081e004d04403001c514560459456580343d010180020340044010700d03003d10840e51600881c0c408440042c5800c1e0188070600d0150300d103088621088440404240109000d54052007028800c907901c10040d10b5942c2181900b0b2005182e40c01f010788940d03490721604844800948200300c4403440c0d910160100b9810034802900c104405494009480c20410840700800e01d8800b16000380c039030610f4041b0f051082081c0480c00b50040d600c992307038003210081c217110300c0e1070020500e40100102030f01c404881c03030b584124503034172400340d0303c01c00940c041b01101001103281003507000f0f04594843c07907609004545035200341045841c1c00c4511060060a0884600344640801c4c160001d8010408c8041041d604e800114981008005004000c26004242d00c03580d0381c00703001d11180c8000040d080689941e5110105010a030350782c802c4c2c11050280300d042d1840307903c202c00e110348155040640c0c0368591030165011001070000400c0c407009801c80794000490100580005d60140e07000740041 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 459070305 1250 459069055 459069067
    0x90307060e010509241609031203050106020606010f09211e1b08030702042a0e041515050a18090c020d02031806070c0905070206041110080c2d 63
    0x521702001c810b1404a001c2410f100040f0403281c0c48540c0340c2c40703154140c4112282042100581d054125500014600f0800c06080001283e06030311843c100c0e441942103803407540310400151103820719112100d0014810000c18880c07110107402121000030f0406031601c1420403a00c51000c0070824010441000719000e05450500c80c5100f1b9000d444941010b0591802c0d2401c1e000699a105821000f03000b140c48455800c100c140000d05108000d440c0c041d07100600110000040204d0220040540302c0d41c90310304201d0a01580b40034007020380300b1205042122070b4401d001581c45070002140441002014500c0510340142c1d809604000c4c0486070000c1882d8a8081000c3d043c0250141c0b0902158014880c00e40d2201000001201d00141030b5402c543c0d45069050591803002c294118945960a007030503c50724581c00554284600d004640071480c02c0c03000002c0110006680e010342c4000f4613a0404259000f082c00d00a101c035901840d08003540c510b00d80090303031020780350035900483c1803808116 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 459071555 1250 459070305 459070321
    0x3041e0515010b250311010507030c03060812070b0903161101110c01020d030e01020f04120b0109060e060f19060201020322080d020a18090f0b01170a05090307060e0105 74
    0x1510b01400d00c0c00080c9041c054022501403240d000300c000c0203600340301030b1081000d00d4050703040503819520010003070105140c5460094003034110311241100082c540000018901d0020a40021401944131040d280000948482c56290809810170200c2c2c001082001d4846000c0c499400b0071512a002400c440c81c100b4002624088480c2060390786900301d000340c034040b0b030380c007043e00e0300c00d80b81303a050004100b280e03046810f00900406801c0c41088100050202d906480c0c51408444e0500c115903400641c0c0e00d5050a10940c1c0306032292200d1921680c01080b05450810044243c171000a082d00d0000034600c1040740403030009500c0100541d6001041c450f039211022140c00c00144511101420800160703031300c8405100d0007121032903030b61380441c402001620400c921080321301840070810800d03480d940108010656180800007491030004c08001c1940904903a40d41c0d24915504150b04d0351301c400c80710000d00002059008117000420403140002c3c024400d1040c0c041d0f1040002800e440d04d000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 459072805 1250 459071555 459071593
    0x1b08010c0206010303171512010603050102120a0b0105070b19020702030102070b101a0d110405090a0c02060f0705070f02030f010c0c0204050105030a15020a1806030e070e060307060503041e05 84
    0xc11b2240c2c10140c00c20003141c40c44414062480500a490012011280210041c01844940c0004102c4c1d40005046551040942c00c681d000d0040800104504100b28005582621038840010151000800024101841603720b001c0600102c000945421650341c00242241e2011b03504075082c09582040c085502c100f500440c0c00f5013040304404c007441000204240b0769000d9003030168001074590300c211100d500d00b1002c0d1001440c0183c00449182054071600c005084010704c40700061003241c0028103841007074002036001e9005900d51078500034060701d8501009510640a0b6003611076000c020034200c40c2481810390f849030550315074000030b986104100a03600c1c103a10081c429031240840002040c0703540440c0d504134182c880300590f81c6e00715500c16620303560300d130403414000078482c180042c8450300340e0803012031000d42c07405403454070380c851210b928810790030f90309150980e0100d0020302c8810701801c021030b04280140050311250100285128546414000442d901c1e04582000c03c80c1c041d500c5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 459074055 1250 459072805 459072827
    0x1020a0314070c020909070306050106020708010c0f0c020105090301090c170c09041a130215040e0f0403090603020702040b04110418110a0c031e02010209031213031b08010c0206010303 81
    0x10410351000d0500b0349000300b5104941101a1140d0a840c001c54009881007040c90011a804981031015695594000e500e81c036840c8a0035a40b035081001a10b601b5114400c3d4142002880d01c0b428002390464004549580044401c0c90301503507141d04503400f240d40b00440c4001403204002202c2c2c1d4800c0c00070038a062641100d451401010b45800b40710020b40c1480e100303024010b25a0884403555102c1c060071440605000c0040e411040d0f038001b14a40b540880c000300152024045c2002c1261180502a101180300b240c0182c0010a80310044c007809200b03400601695000034004600d4951500c005022110560f0820b00c00d1a00018204054100312504034024410a101009484402004201c1e03a1082500c0e40c07041182d014070920030103005240c2c0122000c81d000384071026100802001c0e00039408441900d1091240001a1501c0700d424811115440b05540040804038034541e11141010002c015108003003547c0040030030243c000744900116403403d64001c10b110b5146050207094078400c4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 459075305 1250 459074055 459074081
    0x90b18010b0a0e0a15020c0a06020d0801090e0c03030301090c030506030304060e040f020c01180b010819120507051c080c04050904140f03120103020f04060303140919060201020a03 79
    0x1410040010080800070b0b1039102d0701a091400e6041d04090014a2000325908120400c00d900b1150050150340001d0711100180103a078071100450b100c0d0310907a551880078584c040024201700040c04880310076007014005440d55002c40c0c0f0b080c1c500303000017401d5030800d8004441d426550401c1c0410a6454010310b41c00c01d0050b4007851074103040c00d000804050b482e9100038011a11454010810f4803658100c0da2400e10410080000d0010b0324000c601c0d603c1c44070030a40e0315210400020400c00070114018055002280c0c9008166290759202d180021a1410b61001c2c40414422034020a07814403901012131038105000c070000005487c0902a410050043d40c1e80c51400d000a000d16219074054a400581001c489018500e41145d02844c0188003103021800780400701e0a4015499101034280c140c910840f40e50340c1500c0804144021103286100240c0010940049005140d004ca4000e145141024100a02000d00700c01000944100ea90260340140c3d40020500c414552501c40d80300000c60f1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 459076555 1250 459075305 459075349
    0x9040f020c0a0f080f0f130503010b010512040c15090602011406100c020f2701080a0b2a0a081807271824021306110102070507090b 58
    0x1c0d2000d55601c506020740142002045080c02d41804401c200b41c0b1008103441d2256035850240440802c000d41102c000000282200030b00801d003460107001e124102d01c0c06a58040c10034280c0e501040d054a409007040d0792201c1d5506000c5013584801151a4100103e03882e80d03131100340340001c02421640c242c0822000d12495500b404415038442c031b0903d10541280c03502c3c003201e11036400050702000000300ca19a1002c0e109546600700480c610040301865003500040d401680d840c4102078a03450520030040c140e40e02c400008036485411300140c01006190790010b01c0000381d1104503819507201c80c00d4600414200c3c0308002c241503902000200f0080301a0151528915207000d1250a6110811010080d00d1740781000174030080350f80c00b01120001c80030345c1140400d80c80c141814003d6000c0c2040540001240c8111801503a5000311010103030048000f1004c00e140000844000616410082c0700795020000a800b0035030170466500a0700500d1400035440e101001003001048401d01040c0700200 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 459077805 1250 459076555 459076567
    0x12060906121b03081e1902010b01030b0402041802160b040b010e1602120d0e010f06060e090f070e01030b030d0e0901090c020303060622081513240b041109040f02 71
    0x12070801556480085c0803054414200300e600540703110301a40ca10203203100210400e00740c45507415000001d020600b038a0800240c8030803010300c8180e100e14001c1c1003003da1040c4241015083e9940103110000805240c901800850343d55441e00c9801a1004d4420081841c0140080501c52000d503270001c1e4032002078403420204203000b940700c01120300344900141d404180d525000529810020340341e2081d10080194803201c070028802070100f4064500040c01704864032505003001100d03140164045100c01110f980c600c2c0003120001d01d40c071030050406071501d4080030b0320303182001060070340440b548448402140200900c209000140c0c0910409418001a5400c464000c8101c90f0045c205881c01903490ae4032a58030062001e401740180c3d50b48805280c0003e0070003020400d02c08040c904003200c031068540c0714210a00d10321440004e03021244864210144817684910080c2590b801c40c4e01013000741d01c40c000217080b1843c00b038014038001c81c00604801030745018410485081c10b00801141403c0d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 459079055 1250 459077805 459077813
    0x90105030a021201060b070804030501050702030906160201030908160204051b0d0e070f031a130804050d0312020a1d100e0904030311030c0a02100504080a12060906121b03 75
    0x12801c840290080c2d918000da2001540c00790440f0303004c1c044c580d4890341c0e500518580300000b544207202c161015441c3c80045190b1b00c2c80131044a449500003452541012942061a48006a044800c90515948205403400244100050300c0c0558901c1e072403454004a50040c0400c0c2c8030018800b0556400c010010b0020203541e00c1520401d808511001a80d0b940408800b8036161454100041454203080000200300d00c3c485003001d15418080d00c815540c07900c1d1044d038201520060b0007024113006210034001820b000701c403841864000c0c9083c2c8103040507000c0000890340803243e110001200030b404007460311012a61035100500c180c40c41a8a4101c1103070040800e030340980802c0c404c004003c0410145807090704091301c980c0700020000e40e03a06280f04111035550010030074070f01600500e00b18003210701c1e0901c201403040740c2180d03000d8601590100200c030015003d20780d008009030742e200c02260420107817140710084e000d000002c45480c880f41c24400034250640ca03801101d00d5045200b80001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 459080305 1250 459079055 459079063
    0x21b0f360c0904051f1203020a060207050303100f030b1501030f061e05090603060c030711010c02150a1e1d06101403070f05040b0f03061e070201110702150903060f090c09010503 78
    0x31560614081b01601c540d03d01241001100e220242c041400400c1e19400e004020004501801a041c056404165540752140b024039452001620820480c1c00141ca9071a01501090206c2030502d40001c0301c0030030340740c950102d41c80c0d42c201130004080304006d44682420309891038090842101c00c0b0a80389071440010390364000c01003040c1030100340800440d1020707000e981940c981d240300100a000b6201988002942c600b00c5411011000c0310210105070381003e00e00c94651506070071090140b80791b140c42c2d0003070060103a4220948400d5a0740c201c628000e201417110724000e0441c0146004560318080000703103100c400c6c04400744a604120030400003100313049000411644241c40c0030420f5031031a000103107440d60020b0110303018008c1d0b0080040100b15247c4a0300f088114410584407904d80c400d00f02d003214203000000c201000100f0486000d0315084003034165210403404800d151100320404a420414117031102410f904082d001d1200c00031040c80442079502c0c0c1070f900300740c07550300d0a40001c0d51 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 459081555 1250 459080305 459080309
    0x7030804050f0303090607050d02010506090f060f0a0f260d08130f0f0809040507090f0605030c0403050d02030a09080c060f0903070312021b0f360c0904051f 69
    0x30034401280c11524070f46041c0241e51080d4401811380e07403150810b051660f2160000612200107518100000c1c20320310b00708505a00130b0300c070507807503903895a0742000380103507100c09100496200c1e0010b880000c840ca4420502c002038800801000c2e0a081d444000a0783c0c1080101b4505c1c40e40c01510489858644c0805002d50042c10740304c6080481850b42005041c0c1c1a007070380040c0c48842d81042c0030003441060f9000b021811400c1c0d9041021340c0c1c80c801d04075140c01c0700780207030003800107030f100200300a520860103542c0082c00400c01a01d041d40d00d9035854506000c0c0d402c0400540c00100b10b4076002e42e08101c00c030f0010711424015203409104e50000030564030038880440c1c0d40320404104200780f03031410010388001e1070707020080c8a6180c00070480696030b48030100220801c0221b02c1d01040d0141401000780fa540000035040d0a000986d1603101500341150b080b81001c1541e41001c40c40740702007885a624003405040300050703a101c1c404424081601c10007000b0360099031b09911140701d4003a0700c4031341c441 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 459082805 1250 459081555 459081559
    0x509040b13081603081819050115060216060302040e010b0a051c151211060306030a1e2d15020d060e0f10080c061602090403030903110703080405 64
    0x403603038035007446000700032101d03401410110010603418401400414500d1156029032501080f60307403455400da4041034640340d0040a07812429060740da00407030325000800980314100110740040d64003105600d00e495544075600590101c140414602c10b03002d1110007a100619041d480c003407c3ca0901c0740c0c010010310824108400004e101035025220328260782c2110f10f4079000301e0182810f0380e001b038003408520004490300c10186800040c0e807400e04242c0702c201588541144040b00e1003c0070040641c01c028180e13909401011a2400024172a62001005804004404520344c98908001c611040d4098000b1118500003001046000f0840c1c501c0c0f50403130380a1031804140c5685585007000c3c2c01040480c1c1c074228100030000c0b864001e22801c00388510b10364600181d8644c0c032170b070300902017500300d12a0820307035005940d0f010720310304009004042c0c44040071514100303d101507001c52102a0b0403103045e800259907034001401c02d98070201004d10380b150200201059801c0d511220118851031003218 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 459084055 1250 459082805 459082823
    0xc050607050d1404180b04060803070519141002030a050f070c111302040801060503120901090e040618080901030e01051605030415091b08150408160206030c0706050c04050904 77
    0x90704400c5260120790152201040854010701c5c101c1610019240e01c07410a80b081d0f040101c007140641300002615240340d0004010600c1506c030300d01c0300b118072100c94010343e2a2114400300c080101e80400028040310031800b070041e500d140c0400a5001c0f95009001d00e84000f0041081c0000c031039102422042c441d030401c11a80107950700b90700007601c500b204442c40c4203890010074000340080066000c0c4044960070703811b545d40c490039201c4c00005d5210700d01d016404078101d078a042c061589640141c0d540310f442860001030074030f00001000360340300b42e40c00c04850810000078a82c45c02d580c54003c904681c58068021710240c142890303c6d107145240d982b00381d010400084005824440c28642e480c1070b07416411000c00c60041103052580c04011408254080d00516820002d02e003040040c0c1241012102c030043d80b4291513a6030b900c0820307484103000c003c400d540006000c0c00f50f503035040154024000650556a40c1440307207854003d441004000751641401480b0400068658106003548554070423040 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 459085305 1250 459084055 459084077
    0xa0c050412031d04180309080114070c0f1a010302010e0d030905010c02031006030f14030306030a0f0227090d03020408060621160e010504050405100b0f12010204030c050607050d 78
    0x504010f04561807540da20605081909206481c60812408281c3c060381e240081580c8511105098500c8141750708a80101074000600d00c5100d88410055544916208040f8a04588400401012040a08802c0d54012004000315a08400c500018030003e540c0d1a4005682c1c0d00c02070920044d92040c2414003030070801080455405100c80c2410b010050400c2080e99145d040140002070764000031510382c141910300d1491002c000040e40e2003100020010701d0a5003450341c0d942d009660340750089810200f04032000700207070300c2a450316481f43e006820541d0280b41c024052843c00100f48880d005040c4100018050b2040101e80e150380030100360b4400c1701b200026681101c0e0394950902604c2580554290100481d03001700d50003040758041410b00400f0303600c9104000485900351f03030003440c50b4480d17038190a03802226089550340f5000280585954080d60340410781040e100761030041c150350300050500405c05042c0d035104c0030304007d80f030650802c0c01030b0756020703601d000511020060203040c1e4a2 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 459086555 1250 459085305 459085337
    0xc0f090c0e010f0c140a0b06060304050604031b050102030901090c090b0312130e04060b040c2d1e030605030f0a331812081611030c070e0a0c05041203 66
    0x7101c1c120f07034401c00d5050b05c01c200c480b5068071074811a5007101d040448101040c11482c20105590060780c20802520590310b13140c0d8140d03059600847c0300f84c15000a03103042008640284081d5214207840344c0081389210341c03480d101c11a042c072500309000b41071604590890320307100081c01e804404941451180d0b10a01e40f4080c0305168410b92150310240c4d0043d08020400070942c000c007100480a0300c0a20009040c0101038800e80b0020030b100c0c030003101d290314035000502c0812680101c11014288000006404c55a64407100d03040c000343c0020a4079071804000c1c2d41402c00c0001140c01d07204015004a1103960359541a004085100d0040d50354a0f8105078440b000b54080b00e2184941c42c501001300c511040200c0394000c03114802075403010b080c1c64085600a014a101c507100340002c510450840c0201001a0740660003c0080d1101d44028403103010f2071034080003082c0183c107012001039040c2c40c00030304040030b965602c3e001c1c0c001c0181c01d0208100c1300011194007200150b2504101854201d1441 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 459087805 1250 459086555 459086567
    0x30f1305060408031e09060d020d140c0408061506030606210a140601090608130c0e0f09070602010606020d08041109010b0a030c08090316020105160c0f090c0e010f 72
    0x1590052001800140f210b90000060140c90601349094002c4980603031007101d503001e02400c03281c0040017040103e600c005264024070904096500002d100e90509085208210301180ca140d400c00f40040d042c032482a0802100ba07000c00340c00d064243e812505800b01d0018003015150314020100490190781500e000e2110402c1014050885034130b500d000d442040280446041411b016107405000c506654860910391080d00c02c40e031260303c01602e400c000074001c0f014406042d1003411029102041d08404501c2c007038011089410486800c0c00d18081850408400d0b501800c15a85801000c01070a0f4020070111005905400c001009940d00d043c009100c0d090004000c3d0b101000c1780010507031700602000782840c0c0d0919a000c1011541d4004240c2c0d88140655006000368018400c2e200b0307101049266030724103071041c9005418402c50280b500c09410110700c00701c07040b8071039540038001e03c02c641c0c0a00c0c0c01044200070a004205405201408040014030b400381000142e08501c0c0e07515000b42 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 459089055 1250 459087805 459087809
    0x51201060806030f2803230904061d010323030304080304030e030706090510030608010c030c030b010507150903021504060902010f0f0c0308062704050c1915030f060314060f09030f13 80
    0x81e60903010440c20703900140345642301052545c800c5103850000304010203030009520800f00c18590800387c40e400e545800c038101000c1030090240c08420038102c46505018005140583d00c01d031201610303401d262030050191900301c028940070780e006c080100120351784100720000b00c0b10301307803503806e6a000d00c0e42d000c5014007426040a182c540c2800034803840b0b103038154860381610340c050f03900b000044091030046429108081c400380410114418a40250815500000b18030703209004840c0e4100c00f0078409a2910402ca03003e40d40242d40321500800d41d60040d201180004080c5081d00b410040d082c8040d001402c206000350070030050700b0010342251114801c5041c3c60608402102c80a44c0070030151b00301031800c4504694030300844070071b044242041c0c0e04020041d010381681800300c1d805c01418804d945010f04002c410581c40707547c2880d07580c5651282d04003a5000c1c1101e50b20030034054900901e0540e020b4000d000000801040069a400200c181c40c0c6c000400d07054190b4403810001084202c009903 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 459090305 1250 459089055 459089087
    0x1b0102090915010908010c0e010e04060f2603030408030f06041d100b1504030b0705071b0806070e10031107150606110a02130507051201060806030f2803 67
    0x141e002d010055148021200700314409a0f039444401d921840340b40d0980c0c5800c015070000c07034650402c200042d07024080110a20354050b01c00101d40d07551f01030402c3c0031001503010803c0c5a4802925224010186603031502044ed058000c5145007130550382d12410f0702c80101b0a4081820300350109490741d0b03460304218803c0b410021000e180380b002000703164503481e20007045040c40f0314140407500c2c44d0601800312003250002e1190642028619150418a80700062280042080130860380d8000764900000d1032010884002c85070949062a000781d1521344007074800400e10450904800c01540c1d05032086000c02114600811518a96600c9100d24003503620020300801851100a24031850744e031001c42141c05690b1410045041420043d440700e41c0c81002a4204c87d40b51090b800421050708074a812814030b10740146004000c44030005881420780203000000c16440600c1018034003000118104000600a41400182da400702042038003040c1d0a019441d421038603140030305002d000c01014808032 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 459091555 1250 459090305 459090319
    0x18040e0f12030613060b04091d060c130e06090a021c14160c0503030103200d0302010f0501140a0306090f0209040302061e010602030306120c030f0606040f111b010209 73
    0x8400070414664204940c2c650040d04494201280c12000c0c1c003074501192016480945414200741d080c901819800400c10322041102c03c041720142c0080050030300c21880045030320b80340c140700d0154550f1644c40b58003a601802c010400d0225994485240d0b5030081d040c081c005954040680c1e00302e0791080030403805c01c005490711122925581c1b011405902c23840c0441d400c1450030109241c00d84245101c110090f007607500910042c40010701451014101a100e141000c1c20400907400080d102c030302e03084007100141d4443c0c042c0200112580102d41c05045401c28500c078a1240601050030a2078030300c400382c4003a4982c030070082032100408044030140e4016000301c03558902410003942d148030550f0503110718803030403d03118100310003c07440e01e041e40e03941e03805903245407038002c10820f400d181c540441242d8040c0440729031b102e0f41e08005543d4107040242c050314983c90500c0030002158042e01c86040700c4c0c0e0a103213032040c503900c0c1c030011a503842e00da0344c40466003140e50505060090080d902d002d900010 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 459092805 1250 459091555 459091573
    0x80106030c1b0512040303090311060a02120901031d030a08010e13030e150f03040302060c03070903231f0516020307030c03051c020c010c0e0109060c1b2918040e0f 72
    0x1601c168044180d030300ad030442240b20800e400070f02c41c0900c200c40d02040160003501214102c3d07038501c002003910507070514002c14002809810001910a441501d120702d5100280d582142900081c4d120b00410380c443c1c550210b072a01e000c42074aa81580300e0010100500303030340c840f8040ea8440c03170705580c50014038030100e4589031a222844e51940c0300b550158094032860001604203140c2d28202c1348108242d58038105100d207541e6070003c4c004005d034801103d10341e0101010a00000c00c100e2202d00b15140d00391000403030400c900d9101101c1010300a03089000010001104468001042ba6040e690510b01442540c02c2801d0840c2d0701d00483c06610302c1e080d00d540074012100900c0c1c014140001c9440d00030403040f2610724007611403001d02d00d07a882c0810004441001160b01030200c030b9203124064804058002d119640346514920240c100610304001c200c403c1000a83e14090388085102d1070030414607000169000d62402803d51020622036a210180700120440900c01991100e01e101c08441c0f03404 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 459094055 1250 459092805 459092807
    0x302010f020307090810020f07020603040f02090405060a0b090115111608060106031802090f07020f1005070906180915090906060612021213050a21080106030c1b0512040303 76
    0x15042c0c0c8035100040c030038904100d0f04294a4400c0711002c000c405521898400708ae801d2000d0740d00010805c1c1e07203d40020a4403c090380f50001c00703900c1a403180380504490301c0d0003c0d10b50101d03a000c80b082c82c0074030010001805250002c803440e003210050790426490020944c0482403804081c444140440c80071501d00250303020000450070b05a03101600c091080658003446107004810446000e5802040034000c00c851020b080078264012030b0340c0c41a241c98555100590f881c0032621101132030b0545d5248100107065511904207000f401c41440c080c2204508465083c440300c1e45405a002e4040d80d40c0c041100d200c4012020400400012900f48040d20071070a1280003802548291000705d00c1940c030048501c0c0301031007180d200c503600010000286e191011030000107800c050b011200d501c07418200d00c01080d40d400342100d500310074400b076820100c18620001d01e0b162040e40108141030801c000303c00c056412200132888285038114080c400d400c0e07410014940080780301c0d500642100020003201f45 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 459095305 1250 459094055 459094067
    0x140f0d1416022107090b011d1302040f030b010806040506040b3d0b0a050409111b061b1603050a031b030905010b0603040c0509100302040203010603020d0e0106030506130302010f020307 81
    0x707480d192041c4d60480c1d0f070311190300c0c0c1580c890005041c0050110400100300c11980d04c0c00c41824a40508a4107164150001043c103da1003a0000440c980400c0010420081090741031400b516180c4054006402c06580d910b40d5041e015100904092005c40010018508034404070014084900781c0703115a02040b1030035a8480b220300b44855101c00b44040898582808000c0750390414056444600e080c2c42d14980c00003e0425030400078038448100300304010105140e00481c6041d610700c010b0305181c1040c0101c008450111142c1e406040000e1003061f41e2500301804c89c4c40015014200140e0f03901111000324010101e0780480d0b24480400b070381e04070515a01d50701c042c4004e84540020008600c1030401c005540c0402c50b4010910340050b00c003442141460825190451120800390350394035203e81c0098207a0304241c1000000a501082204492403a405041d14002c9010001c00070749055480c1c268481c40010120f5008010184d40c0c0c2c0e081510075030141c10505c00d41d81c400c6490f030401036401044 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 459096555 1250 459095305 459095359
    0xd05010812250503130914040201140903030d06090209090709080a03140d1a0117103b071202070c0303050a0c0f1a07090e0103020d150504140f0d141602 67
    0x10240b1f4400d54203407032001e0b82d003a18000c540503124032000a600c480b00d030300d090340042c4415400d07000c00c1c4845403410580d0701a40024040441d00545c4a441c00d1007801480b0200030080300800110041c100304120022550445407601031800700b240300e84000940840e0712983c01000c084600d000d442c0322000c80300c1d45030444525000d984004040c481404c21b1100000161003902000418000422490781010010418101d000d4130300581480c00d81042c0710700c00c0282c41243c415000c11010816601d5010080f1803160310200d40440c01c0c130300d0135155013000030080d00004042c080005110340230903025a01d0307494100d51000c441e180d04500fa103000102c022488075103155421a06000c924154080c4003d801511034611490200303038a95000c2014908007041c0179202e4a240124000c01151503000d400d100307502070101102d540c0486045070780380a031215401c800f19001b00f07a890350a00d074050b15040419401074030154461104020790515100c041c00f0095114403001c1211b502111840b46d8440 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 459097805 1250 459096555 459096569
    0x206160b01140607080d1a19050310020a05070f170403050703060c050306010c080922020a09090c050403060b03010b040507020f0d090315050709080609030d0501081225050313 77
    0xd03181040b0380c02e021290160b0301000b0010074090058900c11a0a44d1003140c0f080710b0300740200f0b01888018089092041340030b54030342d494002c0481c148520700701001500020824042c0071440e111031101d00410601071301d10001c040c40f031105010070500150703541c92401c4855244200f5511a44c91500d1a951401ea1104880440c00c0c43c0a40079418040c2e41034911842041c3c50b80310480d002a56400d109502c03143c1c8699105507481400c041c0d03001e21418040c08200c00d80001a03461840039006442a10700707502400500341403501c88884241d0001c140c50840f503101c4030101e00842c5c17900c0020f001d06806a880d03a0400e2800d4204565182d00003070b11a5011070707500a031996480c894008561800e40782c0009890064038010003504000a50700055122400d841d00144041d11030740d40343e05006d81540d0780a0940e10106040708804803c0c86a0b81c01400004018903070b030070038008484018000d9049415001840c819038042100e500c0c00c0000c500303a41304098035668040701c422a800c59829000381d01c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 459099055 1250 459097805 459097829
    0x300c020307030e0607050309060d020d06060c11192601090b01060909090201020c0d0809030a150c05040f050649050915070201110c01020309190f0b040206160b01 71
    0x4043c0d03007071440480301080d4010010f1490812110140000359200000030503c2136420820284812914030848014002d1940c0e520340840c03080c01c00c2e108034040040315501c140c5074504e02540040701c04006400701c4401c00c0f6043e08003e40c1d40030f141400b003c01103020103154240708000081003e403011641c161440c5445000c50743c0d46481911044500b84980280540c0c400300d107070040c80c45c0940315a8440d600c9402d015103444484008a41058000d5000f210804a02c03003594151100320f0040d450781c21b40c140345c544e00f03091070030074450800c003842d22a09001c0d940010742c26a0548030f542002481c0c0d072054901c0c040b082c00382226618424544441c490743c0010350110305480c0300d030500549018031410001441110b41400c141059400f015114500f075660700e2003408500a084400b07022140c003248001601ea1a21512181c01c10f14035401100b11109020703a0600043e1215501c81189608520341d60180d54851010944603c9100b0072075030001106441d0350b04000981032503c1c1030700c200b6680d00b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 459100305 1250 459099055 459099077
    0x10f060602071703040e1b0703020f0c03030915131a04080111180f04020c0703052401030b01060804060b090c0702120d14160212030d05090d300c02030703 68
    0x20f030740c01d20f11202d40300416041008200000c24003441a42d80000c3c0c0c110983e0031202107450806000c0d40903440840241c0c01132102602800010300c0040542c88050300918900007000000500451241c0501603112401041500b0b454911000e800090310034058044462084105400f007540c01c00d203e030016030341c2400011005c0d514142c0c10b80c0c1001950801c01d180c101250010400d10941091540c0d4015500340f103189040d1a04216203401507000300c0140c48108200c58aa01c4880718101041822809031801080080d2a000b10b060449000e490320b00002d80b075034501480504041c50745e540d0b000c03e40400740403640d98000020500310b8400c480106010341d00e003840580328a00e403800e6402092042d20707521003264280006102030803000b4400304548000d030780010218012100a1350041d880402c0b45480d01c86a0312826402002440047c41c29140329031004007030105000070381015001c41641414080c81001c48861441c00010050200e0040844001e54a42003140c09800054420b003071 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 459101555 1250 459100305 459100319
    0x2090a2601021204122a0611031303030b060307020715021504080309010c08010503030316090b030406020910030b0d02010302090315010b0a23070609080d09120305010501050319150503010f06060207 87
    0x701000049880e0141c020103408103642807061800b0031030680b0001e84818206801d000028020345c40ac0d200300015110468680c00c00808903640800d07000c0c041e003400c10510889640000340c00044071015029030380034114081c012814480e4503c0613008070866001408200041480076511a542c42d4008220020702c0140481d5042001c0c0300c0c09405400400104542480e00d42590882841c2410002c4d401c1d980c44884c00051350007110281e840640c04940c0c90003500e81030442810381e850600d0240400c00b00f010000b1004018003100905141c0e0024a4001e9030b101404070400344012208140d4030b44d0307524245c24001e540010310280001d00b400c0b200e0b54000c042a5190141103000f0458241080c1455a4020041860840c10340b4801010b22040003441090f004143d0490301c584070014202050301750217010303118103801250501070140200802c51020102c0051030403a12600400c4429203030b9030b29034004040d500030329055424a032120810f070b40142c100604a4040b0b50803640310307075510f8003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 459102805 1250 459101555 459101567
    0x5010911061303020f0628030c0c050607050d0b120f01050106180e180d050403121704060902011b1a06060f030c0a090b070b09060a02090a260102120412 67
    0x5480c00c0d02c0c80e07815805002500b0b0401034121a9003000d800d16103050103824202003554040d0013a0340c80c0d2070700260404c040607450b01410800d21124144032200304031303650715071f40c5070391000b42100c0070090046000b03000d030445600a4111030388007802c01640c5441d01d8000305d456020500070b0801d15800c0000000d0028440c10b0400e000e4006a6400da84042c200b0705018185d84c8040c0c821014072544044041c8002c03c1480f049031340041c1900c90710703a142c3c517510340341d8125444466018280020080d00032420101903550320303842f5a0181000490858030700c0140c84001440c0c01c3c0092401135407011400b0803011040200c2010304180c2e8101e41c07a0340381820003546214000c076052440c141803011a0304000c002c2c01500066126013801841d02340c82d980c00980980000f0410364101400b00f00b840410741c418041c4503040065030b141136140c056440003285800080d8030402c1442c3c0311a54201c03d00001b81c00040d041d40e541d0400940d51341702c601d8000340c0024000d54080c0c079100540c00f00c200456000b41 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 459104055 1250 459102805 459102817
    0x9030702240a0c02061308030c070603021603030c0c05160512030c1203101d0a2906070206090a090203041e02180601020a050a140c06120604180606030501091106 71
    0x90407062400c0c0b4507100c2125001c0124204a03005042030104402c0c1c2501810007001034580c0388000c580724000c010b4003d241602641c41078080c54410801d403d03c0080000780c48e46810b80504003c582c420b00884100c40003c51040083c00354003440c1e9012001c4041c14854030222101264800c409800c00d105c07068481c03003009280c040c0c50384885c00c2d082c586000c0e0005035500200d000c00b080c034101c0d511401d054640d82022441d00c14144500200542001c0a04c40c2c840035000d003a000d400c490810700030032210ac41c518060b46100c1c1a01240030310865031801e045034090700025020a00c4950b403801158003940041e03904842e81c01c03c400c6010041d0b00801d01121078182c000f00030640003201310500700001e0a0291080b81140150300c280c0001c200d04004088040f8410310318a240d00c114079070102c0c1001202c1500c80d02c507410030801c810030010314145598000900300c1d40000c010803070800c0b9035181d2a00d803800400304c600300f10f4000180308040d402001d66501450140078000036a00c01c0100b00e00c650 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 459105305 1250 459104055 459104119
    0x60a06170c0d050f030a05030402270c13080a0c050301060e040b0105061e03090a0309050d0f06020f1605030a1d09070f030e01021201081519050403090e09030702 71
    0x1450140c1451a00882d5896001d0280c010f4030301c402c00c0907402c203045500c4102c0c000080b0310000144011820900c0e002d00e03003131545200001c6100e00b1074440c3d002030807018013050300c2c603400400c140c40e030081c91408010040c05400210f40840541d8a4004c00d040b11600c5868429481c2100000d56007038406070a038070580c3d0100000266a00380030810182e07030441a1603d406200314021342103950102e400440c010101600140148481c601d0010101d41050700998025251801483d0000f95250400c0c84070075445000503888040c84201041c56000e0005121301c143d40d1446444180030003c001006d19000aa45401c844c00444004000140b0410011030f0030007000b60005d500036204102420b0303107498929020440c1c048442c0002d00360380000040b80301250164004101d00c0a04000b0800d41c5404c52030354402500c4c201d10141c84540c10701c1d0520090546990000d400c00d0300c07a140780d0025020340500a1501c1c24000411540d07078000846c00c83c0541d0b04c030700c0c3c1c00d40c040d00e508100e6441c441c07503 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 459106555 1250 459105305 459105313
    0x3030b1f121a10410703020a02060706090203010f180b091606050703031505010e090a060906090b130e0c090712020f030906070c020f060d09151e09020108040f140d02060a0617 77
    0x1340d20860f000b26442944264118002d03c040c4200595491004110b55070103880e0128106142d40101400c48082030582158646130416075041c175480c849040070f4060b00310841c03000e144d1340c442249003006d24865800d10501d07050a008510950044068141c250107981d003003115040e80c00342074000c4052030040d5030208220641000c003500d895078806a08c9500000041200b607944d40140701a220755820440c03885442c4c10400000703003480c3c00224228032a00307100b030280710050845141c48100807080300780640908400201020300030b01d0b00d245140c840000455541d0f940c1c3c5400c2c01c80307400594a40c1c10794000c40c4003140b8010722410628010700c6e0002c00100c01403008004100b2590700c244158020b15488074014408521801c1c900070061110300d102003290040a6a541e284003c02c0784107a02a41c900744004d005070340e101d103580d0b5115030f026640c8003000c1c4507428140380404118500b40c100d0301c01d05034880034003075010402c14056070b440d45050084640703031469964684128140704281c0c0d44 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 459107805 1250 459106555 459106667
    0xf0801060c11041a0d050106081504020f10050715090309050f01080c0c0106051305060306060d0807061a090a06050a05030102041406090604080a03030b1f121a10 71
    0x50a9800710f03642c0051074241c540c4c804400d8010980202c0d01c2c020550b40c69642e0b00303040012030803d00a40300e40002001c1004a44d1500b41d00250300d008000c1904c50284402d80f807281c00d003038080c4085489840c0c00404003034508140f003500401500000d84202c000802c41000000c0c903060040002d4042d50050b150051190b840b03107103201807a085007000d114159210b00c4005680d4030750f18142c03c500380310084085000d10f01201854038008001e085a8042c41d100034ad004041108403003968852584280c010800100041c0400c400c1522607601560106040301405204d80c81548103c088420136542104525924402c02d4200d025a10402a10a02c100c0242526280840080c10f0070340004242500f0039494114035460050850701c22004039540f03140580c842d01d01200c00441c00c1d448407904120080d241e101c000d02a581080b10324181c0e54a8100020030141040e4001c0001301001c0c1c0900d00c2003c3d0704d8001802c52004420106841102c1b03002000002e0150501200300090050b2001d0512 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 459109055 1250 459107805 459107809
    0x5030603030a0f2006100e070c0b06032805070501030b030a060b1507031119030f051605010c0e090f01050102190c0b040e041a0f0106030207051c0f0801060c11 70
    0x890f401c0510104407000e5251000c901c1d54811880d029200c0500401180c03070032070221200c2100c150424180030441c10708009100d075229020f8020580e0107a040c0c4441d441705400f1900d808003410400740340d4010300c514034052181e40020208010302030000c0b01c080940e41d9005600322a40515a00e406411803441080440c01c95000185113a102902c0310409044004421b83c06070071007002200000d240440c528254141041680b16440e040c401c44280c04800342e070094a0700e0411881c0d41d00b401808515442c0620501d1a05883c05030484024405a015190014580e00e00c82c10501d10641034a4041a5906c0c810160241643d0041c0c0080180c103100518101c2400c000c644200c2c1e41c21304141001c542c124003c3d0240000704008488094070b8140342c6005601c5100c00d81c402c5402407080000c022012201c3c4041504450141c01c0050b80c5006a080060814801191480c1030724000b231050034074030b540310303602c814000c1296552055590300c2d41000c850b03c14244030041c10040c40420184114 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 459110305 1250 459109055 459109067
    0xb0c010b0109181d01020a171e040611090d08090307381b0106150513060518041509110708070303020a03020c1c111216021c0b090c0105030603030a 65
    0x400d62450350400c20a1300046a0aa900c01c081c1c040005100500d0380c00403c0102541d141c022002d0900c0c0d4088051f00f1403445020080104007804250b2507541c4e582c950201c4604a404048000d000c200400c98141854a03007075216980e99400391085240000c1d0f81c014040400701e8a00200c0c06255000d803031614001c0c44207114000280303101504204130700800d4100084180041c0c0c104002098403407600303600601c1c81d003408102e04140102042080340c01120b980e40f4409503846410941c0d21400c18081c10b0740d62843c031300300e1b403500145010305000a0040307003600d060440c2d044117400e000c0302c907a90910358100d0242942c001c11400c01072242e4000030313000390003511801358a8680103041c07403200c107032842c601500d400030b1041a40b080c480e00c130841d907800000c400035050400d0052403045203444844580744030305011590800c91850641d4119650900e0a00000c025164601c0c0b44804505003050104c00c16665461240706001e1204000d5020390242c03441140010082d5040502d01d800560716 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 459111555 1250 459110305 459110321
    0x1030b07050426030913140115051611040c110601060311070f0201030f1a0f01030c1706030a051608010b1005070f0f0b010b0a030e0c03030a11010b03070b0c010b010918 74
    0x140d40401e0081c450262242e8480300d2030b0417a03219000c29002002940d180247c001038000c101216010341c01108000d400c24101c45896000600090440815007000e4400485880a42d5032090800006142d0742e075004102c4100c40f01d4541c243c80c034607640c595056003250990f201042c20f01c0740c2440700c4c8c030100c0d10070320b6104206401810702246d0343c48d202c4c0580c000c50b405d550404a203c07030103111000c00e909000c46094030503102800d04000070714294001618007a4034040c400d2007421000300251403a2018000c40812903031102c1122800100035840110040050068016a61034545084680d1078125000c0c3d898000d035071107c0b0b19004580e00d514000742c542c0341c0184c803e01c0c0741e0640d000004141003a254020449686516114070220900500b654480c800c0b01159074004240c254040d5030100443e07032600740c14108005600783d0981c0305400f40c5100300080d40d02d4003524000280d500c5400000300510300020008000d10b968201c0152000c0e10341d4020032800b080403200c01d10580d0250307440851 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 459112805 1250 459111555 459111629
    0x11d0d14101503050c090103020906060a2607080703020a0905120f0a031d03010506061912090507090e0d0906030c030204090203041a06030a0314031e0f01030b070504 73
    0x8075400c0112000c0d9000107910304495500b0600420902c541070040380c9040004a521500315459a000070711030a401812240c400d540c0041d0003480580145152032140b018911440c0e0201308007030f01440d44003400c548a07000b0030031520014114621030b01c22100c03059400d84908240350305017400e1000701202d0722440900c2d8841c01558202c0203008014025816100342c4e41c100c6c4400c2407083c0d501808119082c080d00a0b0b0400c82030098683d1600e0503aa02c1d580840300c0b42110342a0110704641d9900e407540c0d900307103051410b01d1420038020041a508181d580318681489401c884c2c064013542c4040c0b58410b00c00003050398106000711407194000c15007841a030f03c1c0150401361181000c500300ea10503070f0220342e02c3c0d40407a041904d441c54410195803015080380500140328498070081c100581604010700002000000559000a0645d95074041c002c1c45800e0041403070202c4411304040401e0000742c0380c0c0806407000861231480f0380119001d6854680b0b010240760b0381c2d1070000601d040c554403903031 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 459114055 1250 459112805 459112813
    0x305012711040e0a1a0a030c1a0f03070801051503011d070201020d02040603050402120613080c190b04140705030c04020309010b090403020a0c080111030408030709081b011d0d14 78
    0x3410840d01ca10f00b9018801354000020041103020500301d944c3c00c840303c0180100052001000030400c1c0040030744c115491001c405107a1000c454011341148202055008410000b00a00c0030096003c0841410780c1c1c015244104000c0c5000501181800b0134820441001d20640240301c4c0c55a001c520690003200074000541005004100a01039070010b410041c0000d940300304020552074841002001c2808420181070325080505050320242c01400c2c0c00741081c80009400944d01d0010041d054114034075507505a51134105140801068070290780a0717454403015010010240340201e404402c4510040051003480d4240c2c0030700010390001851107000795079030821102c0c90380310700b689280b240303100350302825070710010b0300d80422030000a0300010f100f81e1614201d4095500305c1c0c4120303a04140c00c003070340d603460b0340d40d6100403a40c1c40c00075044005c2c240141c04003141480120415a00b03000703400d0721031980d02d051980b00300c401c0c0d00100e010b081e031241d0f6400461011404c1e2034040c0007504140e100395 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 459115305 1250 459114055 459114059
    0x10f05101101290a0b1e0f0c0d081503070e0105010e1f180602030f0313020301020d09032f1203040309030b0112140a02030a080d02210403030501271104 67
    0x19105180815a03072401c0c8400d03c0070686842d10000f40a001c010307460720700782010740e0b004003145070415a1b04080198000f4400000c003501800b0b44461030f000e08100d50020311100002001c603041581e801c290050b01c000035404a1601048400030b03034071016071003040350386844e00450344000c00d0648140c100208841c944680826188129031100d01502c0b03802030004100d04184410328168000d07021908103009038122500680f00712600403403807250070003c2140030b000190092113505800c169030b919081c144403c00d500030b4141e040c0e00c607135410b0314282c01642c04e01c003d01e50300c238409410225030811304400e03c40e610100b002c0c64216010346002c41c40d0342c0d100d030b03250307d4030880070380010885050b1164000100610050784507075040405001c5c02d0715034a140d01017650b4828407240180a02d02c00314910807814071a0f81a164660100c00550102c9034165000b10001001075038240d0000c0e0070240082031003502407000340c0d0070b001c50005808604d580c00c060200102030b1a044108224010040 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 459116555 1250 459115305 459115331
    0x102100c0504120503190c03021f24050a050a0e01170a0206072a1410020c040603060905010e0a0f0602030a020f0a0e042a0503090307060e1005010f05101101 69
    0x451003c0500c507000450f940c03807071403d0184030b003076889024100700080d08102d180000d40c04100140d280181041d19400380003814500e102400d200700d4541900c0001b0101c80b20048280204c0100302c44090754000d403010b86560510008480600803081d544c0429001041300c0143c100c12804c800c0000340507030f032505c485a80013031b805038003a0303006542c0c3c1c2d105015224840b182041090b15103801801100044901c0c112040d0030220421622511610202000c241c03d58003d001d060b0300c02c0e0000304208090741d288c0c9012401000350b130b8070a603078540c41c0a00e030040408000904d480000d8000d4002034a180055889001a50005080070b52441d000e1128100d100d500e80c02900003e15651615802c503224102400b01f00c503561564040c0c2608150346051000c59250024510221a03182c4540c3d85d075107074840d80f80755105000008101620b8500c2d0042e007072501040c60003030072681050074445a6039a1000c0d10510410740036141c0d100d072082210348001c2d4090700020322500c0741240045248a252a0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 459117805 1250 459116555 459116579
    0x60e04060b040b04140301020a0c03030b1201061205150105091315020301030303050103050f0606010813031e020a030f03021314010c020d0b1e04081b03130303050a1b020102100c0504 80
    0x4001415503c01040500c030080070385d05846006030080d0021414810307058002030601013405805000d0650303500d00c4140035118042e0060010200d00000d106040c0e48103038550188814240c01c2e4ad5030300070400c0f6a420020181c03003a034101d80f0000c0815200707440d80c4030000d0220a14003000c40340882d5181042c52411010300145000714003030384000070b0541c0741d800c0540c2024400001030f140d9410400c02c011707060707801a2070705800400d07403c500280c0c1080b9142c15aa201e00003540c1207051030b0703e20340a01401d6030007d805082c180c0710341e807510501060100f040d000ea0040c000c40c51b480040602c801e2000c0048505501c489490516100ca80c01d0f0b0720b5008101410403038032055883d800d90400b00300d0000b0140320040d820a80f1105480b217030303148c2501c0e40c4c400e50094120b01a403c402d00c03110444890b1081080c0d401000ba880116201a40e8a11b0302602e02c0d0301104e1000045841d51002c008551179503201c0e04074081d010f801503c943c803030701c5402c0401844504501000c3c08410300000c1540401e9130 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 459119055 1250 459117805 459117809
    0x31206100903060e03270102280c14010e0108090601060311090907030f05070912060504060204081605030d050f0307031e0e01060810050126031603030b0108090d09060e04060b04 78
    0x3019590b1015541c0c10007031098000e0304e08001c06c401c44050000300d41da0014219400282c02c026424603606407c210191100c0c00d00400341408403040408503000304c0400c4450a070140036218142010454401950046011a0000c40d5900304400400c4254040d4001c03101c0d821800c0340711381c03a00011400244010b0401c0d03d00300002581d411258003040c040e88074168000c0150305240307601600d0422203245010900200a06881c2c6441c04a0100051078050b5005440781d00196110299079421041d262803845c80b03058840e10460b003401502c1c1c2c2c000c2040390075031982400d20328a15a2000002d4000d0060920000d41209000803103060718605403107205000341c8458008140c403072800041e00c0c58250910030038504607150400420641410100d0500180048503418801c006900b00c5107040d03024000a0074101c0e080c068a40c030425505a000d13603400388090b25001c4050b1114201d05940758608050702d408903a558400b071003100e01a2400c044c400500034004210180c0300c1c29a118250003503 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 459120305 1250 459119055 459119081
    0xb0703050627180c03120c03040e01320d110117090a1a090a02010f0311041520030a0c020a090912080702030c1507030207050105091e03120610090306 66
    0x20304180049070310001c2c0c000ea40e000c0f800b401000101820380010b51210303100c9070f440c2002c4000103441502c45100340242c1d401012036510401340c40da900e802c2003142070104100c5000c0300b0042c641d00d0100703071172102290090b80000341400030600030f02d030b680701245456290400c0c18041d40354040720100030a441a02d02c076000c0c06016040e50006898911040f81c4a006410700c01012241040214032001544150340e5030240b90a660048030420240d0003007420341c0c025810050000b42c00320b045030324540b481c001c0c0100340e51000680030a004d01110300c0241c40107146c40c0d81e081002213000d001d00c155115407040b40008c02d00c8842e00c0e0349030300140072aa1502800c0310412a00d001407444160003240a0f0b07408a0580044c614103100315640c16103c2c0007500400300c2410001c80071410b8a84264180c0d0440c070340c4000200810708022811540e903c01e498001206440404c1e425094200d011080c0c840c0404070034070000301d40c0c68040410101d02000c646110420524400000100e071042c000e8107084a91 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 459121555 1250 459120305 459120379
    0x30e0409210e0102010b030c04021309060902040303171b030a020408030c0a1a132303120103020a2108030408072a0603020403080904051008011e050a05040b07030506 73
    0x1021401810340400942d01a042d6451310069815985010506141e001c8040b500141c0c0c41d0b400ca0302ca4808a006904103686180c58244041031540042d8001c0081d28041c0d103403880215096900108594011554007040410408040030350003001c402454018002081c05403d064948003410310b1a0803025082560b0350000019130240301248807004008511a0010034803440e001c034070b1490b02450001c00401086186100e0420810030001c106090006013055998600798040c00c4101d280013800113034031460201500080000b98000d100641820003d0403c40f13040041d11441ca4a0f000244103482040d4208000b400098540210001900050070708010507401c3e02c4101c0340381140ca82010003410320400050011825100070b44000350340c00c481c0441ea40c0d403032100038200000300f03500c118840d42c00c04081c00340112010048141102d12800204030381d40d519592072041e90070540b0068500380c02d2030702040c10300344a504540e03030200340940790110030110441c0300308070342d1650200108030040c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 459122805 1250 459121555 459121613
    0x1020706020d0c141207031506080a0e01020a0f030e07030c0e15010201090803040210090b03070302121e06011b020d0f0203060a06080712030315060201020c070e1003030e0409 77
    0x14501c01d40c145500c15140441406134600c0d502c4038184502074521103a6070401d000203005600c00c1c2c0124040e0744184212581d02d660301d00b00a49400010f031401e0006900700045507460900520170788903100c500d0754440600075290344003a802441101031320401806140c1c40440840c281000c840020410b40c640c031030f500e1600e010a00b25114903000501c4c11a410800f500011403080c00c190b82e0060b0b01100c4032503920401340403d4500036441e50286005101c00300400c041e1642650203084060300848420141340d0b40c00400d4100c07400701104d075140a0814001007060b552280303210100d40b0320b001405000101040e00018600c0101e078404484400c0750100c0d1208504050000c2500440210003d0004a0400080a0702c070050780c00790403801306031581940d00f80340c440d400858901d248280d462544a4403070704000d010758018154911144129100080e240d80700710146c510400e0030001d41e480c01030466504990070070713140c10b01c1ca40c82070b1121009030201d051200e1501002c0300400300c5820180c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 459124055 1250 459122805 459122827
    0x80703080a050705030630101d07090b240304020a09151701020f030109050603070506070305090f0409050d0e010801081b12011503120801090b13090809030102070602 73
    0x344010a5100824140400d1240d42600901583e4010744200c4a440b08001c200010a44031a0b042d40e40584550300425124030078040072407408641c1d85811000d2210350a400600b80c9200740501c258203459108000401544e8550340c059422424000d0801c61024a4600d140c0b00111f11035001004006002050004503d86094250000e01e44401c00303102d400b443c4510b601c50740c04588a02202e001441b0503001200c2d1080d8102c48410391920160350300c0f543c40b4010440148070807201103000e489129808102c1d85000015159117643c540c1d107861420303000105220040c600c1140c041e8000352640c1c40036000074014812071201c850556990303034a01000400052101d94180d10500c0d482c0c01c0004403004c414420224000b58400c140e07551440072480c0c241c00c50060003448507003501c0b855414808000c1040a0560818030000c81d5603040d0b080c0d072952004c00c115124045110783c45088176200f42461142900001150f50203001c0e95408c100c000c00c0820309a0b802440c04907000e540c0015252204 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 459125305 1250 459124055 459124067
    0x2d02090403110106061b0609020a052805030c030a061a090406020309010b0105130b1e072612060f2101060807090b010e0105030a0204030204020f281b081204080703 72
    0x4054611b840f054100c20f01506000b07107240040040c01030b41d16000404107548460901c14001d0502602545010040000d030984603407405006140d0703c540c0000000d458500090f0402030b800c001800b4202c03514150307030340301c00805202035450010710031000348080d95a1000c901510650046001694a10744000800d00315004141c4142c1840b03c01c0c4191001024000000c10035600300400d5140d50b241003c240803c0c581c446010300078448800a1002c04009008200c0005a103401942000002c04c20b400d84126000d50740d44d241843d41002e0002c0c049207001d04d90040500707000360000c007507030700c1800c9400080385040280e1038032031f91116401c01803c072042241a00130300e1405400c200c203a01d008002491140000301050402c14007002040090380c4540c116402076500400031940d900f06100070101a810050080300c14100154416070340c80701c80f040c1c0c03450303415083e13403042426841028042c0c3c1c0c50707401a50580d460f200074442141d2410740c0400c0c46000d24041e02841c0e13144c02c2ca034a401050703 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 459126555 1250 459125305 459125309
    0x9040b0109182705070518010e0a0f0e1c0e0d150504053c030a0c021005040f080f0601150e0f010c081b060604092d02090403110106 58
    0x400c4094a400c00280214680b558040301c410031010440040181c404814441500d1003c00d140c1010340c1030714100b00002400b081141c0c0190b031000204400c0003859a01c450f000d10580170179020480c00106c40d92800c2d448441c0c1040300e03044c005a50700c440038641c0e160803142c09c039100407411051001c1c100306402a840d250a0202218115184800ca43d210080034401082200719107460354007280070400300f4059102e1440b13100100da0807040c060102d803070240945982100c0f88410703807018900d031048040200c4914007515152a45c03174540c01c0c0d00703000498211013007030005c200d030030710000c502c01100f00a050010802c01c8010300c40411080442424481c0613403103800d41d20480c46c40700d1a1140c001d0448809600111101026201d0420044e00d00c500900c078014154100015805040c00400020070075100100040701e80390b90341c0c201480100ca0034150050700c1c0420014058241400e40014411072850080d8814940c01e200c1c0d008c0360039a40180c404a000ca0480741611620610034440c000c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 459127805 1250 459126555 459126557
    0x21050709231e1503071209050c0d1e080705010507111b0a090c03051609060c0b04020604030206030c03040b07090b09010804050c09090c03010e060609011818060209040b01 75
    0xa1904928684007900300074030002a80204034254031020620501034103029040005008010201c421040b03140c0554801c40b8014041541c110703080341e1540c0c0314801e42c088182e002006206c3d510042c01000041084200c040b07504940c030718283c103000456002d244c100144942c040347e481e0f1070741e882d1040c01d40e640140040304006020910300400c080015204030b07a03a480340c0329100220313200804600c220078107801000180b0f05041007001100e600d50b12031441440c0e0b00c0240000d00c80303111000c80d07450040344074800c0001c036500c20f003201041140101581041c030042440e4a4150340e9404100c10707400841e01d40c044d104004c01044107002030035441951100441c500100e601d400c00080b4201d5000f0860103904000c01c5c50009010046c04002d4841c0c21007000f004c03200286000b4404695403092904940d0007075003070001024100100141403030003958000d10325241030b800c0c40702d00301d180d41a0002650b80152541070100c100c03c0c22401c9400501e00805016954014440601042d140e90000042c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 459129055 1250 459127805 459127829
    0x60b060309150a0b0d03090e06040606020d050a0203070f052109010c0b0702010207051203010503070e06030705040b01091211330c120408250f030807020121050709 72
    0x200c4546004180030101e040b50001c0c03118207031104071022000f071646034006070f0011410000803080c540c010803110700b2203044032000461540d1340410700c02510414401d180260340300c0000c0160603030084010b0403c072a258412a8101005511143d00e000700e00702040c0d500b5044003000400d00a0340301c84985000b145c030710b15a454100362800090081c4a04400500440351840208041600c00e40440d110f982d00001120050b40040e91072051940c030070b108052092144e0007000035001c0d00f1550052040ca8000d0150204500c2d000a00000e00404800c0c2c40c100880103901040c03c1032000b042c008010300440100c0c8243c1c059805000d2407086070140c4011101c2c6960746021940144a550740f69550101121034588803001031403854815403036604c003480500410081041840003038805c2240c2044100c1880d1130520051604501c0d00070b0045190a01e003107641031010071002001003841610601d40010700780001125941451010b408404c002e85e1a10300340004590b03c6500300c8090072842c1210 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 459130305 1250 459129055 459129061
    0x1203040f030305090109030206030f06011808060f0a02280e0904120c06020f040b0d1b050a03020c07092a08100909080403080a080a0606092d090216060b0603 69
    0xa420390300441c0700090800400084d2540107920a94a800c0215800380a468890420729440c0c92164421189140014442d200c500600f0120590720822110004040c02c0d064071041d64005101c100101403002e899001c2000000e200504a03000c0d03c04c1e000b0b00030056010003610801031691400640c554483c4410b0700c20b0001241d00846400390024160610180c207010fa460400301a0040f403038045110040403c002401c03c003000c1c020284041c1c2000d080000c03c000156400e4042c80f004139010005209000181c0482d0080c0c0c014590704600004640025030347e80c0c00c10b02950b00307210100326600042642211541c591107049180c040c071030300701000549040f00041000c0c03c0c0520510340480c0d00c1e61a00c074188011541101d000e9900590346507590754440d2000f0300900c005031400c072a854a13154001448601ca030341540280d41c0c811200100080e60306405c901020780400002640d000c0c0325200080c140d9880c802052002d00203400c2068145481c140b80c001c0365003802405d13000705070801c20 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 459131555 1250 459130305 459130319
    0x2060108030712080403030b03030c01020d060504020703020607080c04210308071403220206073c0330150509190903050f0c070906170601050103050702120f0306120304 74
    0x3c10494440d2a02c2d215070700340e880c2d050172000350024880560f0540000100248088010b400070079160422240c14003015644505020072031258400150068005602080e4034911400000d074008641c400202d0404d91100e900c000052040800401d0591401c40000d04240e048003da0b40d00800c031781400c40c1c200c02d2200105080d480000c241010789140008065210130507c410215000c1d0041c0c110350300c485032454100b112012075040840350741845d0041a5030007250f030f56890703003102e203240807a1074201040c0c0e0140c2c2c9140750002200d1000d420f850645280312a00040109450000030000c0741a41d2001c1c80010f44031880d411842c000c00f000c0c810000640030115281c5441d00340d450002503002c03100d080403105406400007030401610001814010b9002c0003601e10240c03041c9031801c12201c0d80d24140d030b25141c120301c81143d031150004401000207600a5000c540d12280900641301a61583c1201d02c09075070081100940b509070100910447d803d2801c0c2c41c041e004101c0005500d000c1c20105 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 459132805 1250 459131555 459131573
    0x5060409050a170c19020a05151e07050d020d0306050301060f0b030405070e07030e010b06120a0e070b0d06032604140a091407030b012c040207081207020601080307 72
    0x40c050a00080403101040b0b0030b04120807101c40740c248000f176880400f0001289048901d8070305040c1d2041c1401003011403540303401c1e507029402007030452089151240c00e0103000800c28018080c0800c44509000020128106001d1000098100c1d030203400621441b11000d411581c4980045009070300d41030b030921a00c0b031802c0c00321040d10003080b520303505c80d950b078649503142a40c1c03508600404054441400030782509900310b00c1210102e80004e2151440030028000180a10010803a07820b02040200e5400d0710140d21119555040030701307541450340c0703c0c20603080030340c80181c00c0c2081307941d20f403420818480f0030f424101400e004641719070600801c4215010f01307030007a80100d03001180c10002080465850701d124000400100c1014001c01080700041000400101c031300070701090806074420642e611a900040ba081480c0c201c0b000c1c1d40d00c007140d000c14005c455031100d5410550070400d00021030f0512000c0c2041c2510507a24900610709610001d09200060344001c0296000740a03034000038510607 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 459134055 1250 459132805 459132823
    0xb0c072d15061203080a05071b02120c0a18050606030705090613030b010e1e04050343120c12080403020a0b1504270305070f0501020f0d0506040905 65
    0x8119000703000115100d0300800d200c0c1c0c040001c0c01a814898400c150300a4541c0380303e0700341950200708550fa03052050f1412100030080310f07299104040f4450052524014140c41c5d02820003c0350140071031413000c0350941c2d159410000712480034584100d041c610034064207130f0003c2c0c1a50460304505110801400d2030042c00c9110784a1070020500802006201001d60002d5800c4100e0101c0c0f035a60b4410071465001c15240140d40c00c1c404040558003484255519000f80e80c480001c601e00445000d415142c201044101c02c02240f982440c12143c0f1400b0704110f070402c5141c01c0b00b00d090300003450484000c1d03c441203124140a8181070100120b0b8a5114044059100307003004a010b40d541d00d800c909055032003000802080780078003031000e200302100204040e0703a0245d030100b2041c41c4031050502d6140603900c900611203242c91940700024810000303002c166220700c0304a101121241d5034103003682c10000f4903001c02900414501c694030850b01689030802c0003034400300400c5040392641c035180c81e040e03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 459135305 1250 459134055 459134063
    0x30d180e0402031006030803071e0f030c0306050d0c0f050306010f0509180f01090b0c46020a03090b090d0b07140c0609071a030a0e01090b0c072d 64
    0x140005095407818480780b01c0704c1d280404100724064691601c400702e1742055942c5000102c2842000c00748488920520301e40340c4032a15813003901014558114040c04c80c0700c50810416868010001e1952070f1214010002032140d040c2e0901c90b41042c1850281c50820742c44148291310400041291034140c440f12425075006641d041016650300c482001c9004424000301168440c000000b924084194080b0100038130940300c0c11820307110010781007080d0003812402c0060500305d0b41c0c03104c0801d0380c038254904100b10021042c40201269a08828107020250110b0056040503c0101c101a440521000540ac60504140c14060b1800c00700c1c00d03181200000500710503080c2c0c0410b01003030080d01c144522001403aa00340c0e5807840400100d0b21a41c040c1c460103881d10a9050115205007450308900703d4101509101313056a035842422000b0703104002940109541e102c0801020a41d07580c1314502c81c3e03500500840c1d95040c6072400c090846100c0a01e096400200d03003107841341c140030080c2c81c2c42c01c07500 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 459136555 1250 459135305 459135329
    0xa060b031602010207080a081b09130504050c0d14460219050405180a1704050a030303050105012304050409020109050a030f0b0f0402011b03120f0605030d18 69
    0x50706900760b00a2146500141c415600840c402880310341c4440120700c9410303da9030003400140d0540d40f00f4403500071500c4480d40302d51104950300040b80c1c141d100d0342c2c0c890300a100300c0750500900300208840c980805425216070700404040140d0841c200105140100c814840e40040341c0b803842146c0b860001d500c1c901c0800c03510480c8801a1f080c0a4030b59040310394009203241000484a010040307900840d100d80c5000e90b00340400914501c44061044038040218006040810000d5940d0340a082038440c0c100c4000505110116603034a449000401561090310005415418940050050400700106001d19044445940b06d1044c683c01520200d980699011070011510703c0161602541c4c1d800841d0032900c1e00300300005211001d51207500303160003845180310035220202c80c0c494441c0101d8020b400310700d00310209060002d0040144001c0b074045d01d001465948031900d01c034156110403100c6a2129103d043c10701c0f03d8034061160004044090070324844100b10380c0d0b0341d4110201c4510070243c04442d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 459137805 1250 459136555 459136591
    0x7120c03031d040507020102190302040b070b070c05161a03060109060f0c140307061112060d06020d090302010e0c06131e120c090f0203010e0604090204020408070e0402090a060b03 79
    0x82c1045042094000030300a01651800c040001d000350000c001083c441c82030500c0c0f45480f54064402c5509a90404036414981912915420583e0a01801180400411146520101d2010322003902c245a110f041c01c02072501d40f941030211034610b40c002d40700040042090202031ba0700141c201e0115501400c0001c0303401c3d00c11b10283c03562044e03814081e00d201d607100301b0008003100100041030440d20850b000c008442450782581c41d42e020fa004441143c200c0080410294500542080350044c27140c400580b03010b45d0f90380c01006449641c101240580e44030191680c00711030070b000c01c502d0301c002620a581040c080000140e0507035907d20a00c20881000b01102e800482800b000c00e020700580c803800004240d151400c4160f00b20305102c3c00e49014501b1106204800c06402160304a41c03a054485680da2140c8040200500041030100d0740306508010000d0000c0b802d0102d8001448010300d4664586050700500c0380c240340003080b0b0303d070342e51500740d040c130400805000341c85c1c00a2858100c10003482d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 459139055 1250 459137805 459137837
    0x6050a20010b0604030812010e01080a0b040203011d01090506010b093a0c062604060213050307080f010e03070b01030f151b0f0e03030d1e021b07120c0303 68
    0x200200c401c0f508078100180204c02e204400004107006483c0e802c038000d0682c1d82c0d00c00803102040030300440c0f1082e04040c0554010585064120740c1040c0010000900040081c520780222400e9243d46182c2da5114102074060201c18000c6500600b980d86400303180015072130005801c00f0700001c90307001c202c104103c2d0f24009814518071a03080c00e401c925003410000141802d500c0c548040c410400001d4056034040200044d103145100c100300c5110040d0582d840c0d580e500300207900105148144418214000140355a040001300700801003070002c0c102d40341c50844480d0a641d45261404400e60003041110005090031201d1030449400c0341c3c000503860395131300d00040b60401d05000301e280c00f42040f00502c03000303202d1500d41260281a84401905e01c0382c8000582d2181c00d50380510b03034075800034001c20a0135200c60b0041c4290009011b40c50000c0301e03880d07a84004982156440c4216540300030b894040c840810004a00a00782202003841c10b0106951b07120072464450000604202d0540c0446541c8 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 459140305 1250 459139055 459139061
    0x60e1009050d061b0f0503040809130606050a020c0402070c0909050f0f0105070801080f0d051c0509030d110310030303090201090e040f02032a1e18060a06050a2001 72
    0x1401c0c0040100007508050306040d406810106404182144a07440e0541124051804020381d02d0640e1655401d43d56191541c001e076400c502c5100380c20401042001c0444043c510400c009080c56450b159120080968002c1c50400344d9032005004500c1040250042015030403410100e420146020460402c58a04141000c0c402180c0c42854450a840d052081206401040c40b842c0c0c10754480b007141c0ea1300c85172507644010314120446141c0182100905180c801c8000b040c2c4c040e20040c000040c1030b5062018411281c00b100d80703c50503000421b25000200460251054002c4583d20840c15400d09480b416200540762000805144e0b1310031501017164010004800105442ca800010920305420a8407000c1d0f0060b00c100d109000300ba000007035007642c081c42d124960041c003854911040044082c0b001085a508110b20030849402150031955100c82d03040180c000380c040000e460b1b09059091060383e800503048041400000d000403059203900c951139401101505d0803141002072818880307801 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 459141555 1250 459140305 459140309
    0x20d0905100201060e0405060411010318020f0604080f030d0c09030b0118150e0712150501110f0d021f0207110904170309031c0e070e04051204060e011701060e1009 72
    0x1200c5c3c41d010441880030105105206901a400581d00c05114000440c2204c4880880ca408230045a039070304054207040301e81c0424207401601c0a4902900c03030004a1a003007101511020704d510000da01d44091905001da502d07121442d0428007803080c02c66848040d494014080c80304011005004000d0500d295000741d00260106c1c441d0500322520b882c40c102c012034040725018080340b00078400403030a500900c68903081810076442c10b144581040c00440d010485c1350074600c110700c0b80b4008005600313024880c101c5a204650002c2000c02100b90782141700b00140c41e42c0100c2e851060040802140c00c044070141c082e0b40440705440656207074502056002407240c08409505004030130440740c548004010310420ba2041030500b132185d00d000c2a081960300c0c40e8400c134280d8001002c1001904104001c490300140300300261900307241e404e01122580c1c2c0259211000103489029440038650304411803c00c8007e1102580c034141d81440005803e00da0f58000711401907030b04080104403e445806800c1c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 459142805 1250 459141555 459141569
    0x601142506060e070801050303180609060c1e07030c05090a090f0506010f09060b0901030b0621040204060801051303050906070204150806060a06140304020d1217010501020d090510020106 82
    0x806500e40341070410003803030030b8021010200d074000089480c040c00f900d0001e04844000300210315003e000060200058002c4030510b030020010304c840d81c0d96a4800300a840c80d140d4610040c0b10002096051031300c911280c0303c81e9542500600003c0c404900d00c0716003081940c00690b51030005444005e01c43d002440e41000c040c0c1407400e031000d081c08125000c200f10341241c84000d9600007150320b803583d41049540c01c1c410030311082010003481141754040c2c0c003c0030441c10010209418080d20b150707000d440001c400031500300303806c01404200442c5007502c6602d014007a0280200220320b4101c500c142983c1012178080d091100c042980e00c0c40d5560002180c01d2030b0b038007070810301800100100d04009082c4a000b0105180559000135000d400c0440002c411140c8035980d00701c0404031140d51010650000d0170a1344c010100d90541000708101c0200c04201c0f030044d503104a4040c504c030300ca21200b0401a003015045400103000d01c1400303540010560180d402c204c1e80c880d10301c8060035050b4010900d50388000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 459144055 1250 459142805 459142867
    0x1e08040314060106080108151501031103010f210b1906090608070f140a030f020a1a1207260a1503080c010b01080606180a05190617060114 61
    0x115000380402c04904807502d0b52504401030362610b100c681c07148070b5812a42e00e102c41c0307880020a04452500c10000c294018180040c484000c1e404410566109030441d0070400941c2200304030100705410100e4880e84155682410810345036661220742c4400b03000b260608a0b1044041600411640010010002e840040040711341d2000c0940e158a0f181c4201d100c1c41501000004030308084940c492500070009285002c1a4110340c1e55801405950400780c1c1c00854190003c15444080442d848001002c80541600c41c0e86101c81d894034140000c01403c20071407141c608444860034014102a039800b075074103510541d541e050842000f41859030100300c0d45410b0003400020700c1441c0c801400d140391040000d1000d401c011005490455042e5090758000c00e0400580707441400b415510410b0007002080840400d9030340d40029180340c0082c0f02c07013944041206040181c0c2d0b03000f44d003803500c840d02203400760050b1400d500007070110b51105502d103162810010322110188102d680f50340b0a080626660 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 459145305 1250 459144055 459144083
    0x21070b1b04090903080603030f0a0f0201110324040c020c101b031e03020a08070f0c0f0c0518060904111f0305070801051e060904020f030406050702070e041e080403 72
    0xa02e0182c90259401d8001c600000080340d071600b00802210310340f1450714201840d100081c001291443d5a030342112007195a1200e00301c0340b40754420007e41c0200310740d400034a001960004140800660501c91034840d600d000010700c800b031780100300ca2129490403648a84a400c20580a0703469192600e200d115a0109040001c201500043e40e00411122220310b40404211030100f5002c0307108a07040300d00811112400a5011031080280751407070150380c070b400303d891403080e5684408030081d450b0464a8641c0c03043c1c148800d0a1603000d201c1e411901100882107801d200c40401c1020202800c040c11203012101034020076100c0044001d54134a00d9001000d00900c23001b80200208020365028000a40400000403d480c200d803000350070407001803802401100403803c1201c1544802c191030381190302405080c040001800c0a10311440c060080842c0d54130b0580c80080c20100d080c2c01c00d2403602d2000e014400820030000b542c1020b4042c101017040c0303411040c10003030024040c1c2d910007031000d6102116 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 459146555 1250 459145305 459145319
    0x61109060313031416020d03090305060a0c0f030b0612041a0a0b03070e070f0f200c09060a0f0e060a030204020c010911220b060d0c1121070b1b04 64
    0x150b200351502076aa2650b01d001400000c07a41ca11400c0788141d68058642c906001500e0170280300e10aa520905003a10019502ea8400b42019411502c440f0041e580d00031801403260400c4c501c050030b00c0d09203010001d01d0740c81400980c1034040d200e940520f50044000003010040540400b410803510b484142440e4901041d85034054220141414060b000b403003030001c0e58601c9640b81d84d004400310780b01c0c603510840b802c108491030402041310004000c00769450003900c42064241100c1c04440e500a0701503c0d00380c0341440100030003d0200d03400780043d80010480d2401d1070100105079880807560f02040e8541100107180c640b9035800203548581b0018442d11003640540c011404540b060b90b075028240c4840c001c000e41495010540402850030101c002e14000b141d070302081e2142e800074031680c2000d101d8003210080b585521020404200d84040143c00a00f04002b04000c281d0002e04c00d16101e4140403a0145501580342d00038000601c80004c40c0040b842c584c011440420b4150465403921364a0302 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 459147805 1250 459146555 459146581
    0xb040806010603060506030403141c05091e07060c03050f09040624140307030f1b180b030420030c0411040611030c150c070c0b09090105040e0a0611090603 68
    0x41403101003403138644c0c00640e50612034190f80c41036406894860b11008402c44091282c1c2c0a20000c0c0303514910b464400380d04040501c100360040315603800501c0354008140c0c15903508241c81c200e05c0d0301070f4041213040003055400302d00424410f0f07040c1b510980351443c40750518024064005d1441e4403e00b481070206941818400c0c52a4130507071900c00c03503080c41445d0000d030303a881c1c0042e030180c00c200c5c0d0801c000b424003070081c2c00002084103a0b41001501e45490030400b42c160a8840000300091100c900d0304810000b068201c1c40900365182802e40f46051a6035006d28901c2c9034000d40d14080c081e600e08008586d401e0003402170288014005201d9a09034144c610b80c80e40c080d01900020920701911820240c0000065030303a42c01c40d460040c03403150050880d044280000500c15101110104030030380c0003401c0c0c81d660030000c1926003421911903554004010031000140c0005002c1ca18041c03c038105100000780307000d0700c80d8202d030380012a0f2a0040000242e4862131400c0350f00203200200740a00000944 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 459149055 1250 459147805 459147809
    0xf070e061807020601030b13081204021017040623070c12030902060906030c09271312030b04060f0609050405070302030f0c031905040f030806060406021908040b04080601 75
    0xa8007a45030180d0102001c0392100103594050059104100520000d0601c004581d00700f12000200490035802e90b0301c1d80110340c4180d1603501d41d5402c0e00180400c505004615003c01009405c00d41500c901c2085800c62415000348041c0403c1c3d101d6404451149100c2c10340d0364410600c0d00b103040302c0d2801a00280c1450803110044800001342450030b84914031901ca00500103a00910b102d00e40001c000803c07140380c01c0541a81d000721401c22441c2140e50b030f0711070551101c03046849003042c0110411044400100c0082c407460030300483c24015800140503081d010171040060900107840000c10020500528a6401440705046400c001290083e0000e24034401c980e421178013840f0680e110b131390440603400195401003221140350041014401d600e8041e641c40701c0c5800004c0071800410320f401c416503c0070b441c00d4070500d0b030307130031038501855800300baa99404074054074541d00c0c0600d0071800943d80c00c2d00c61f03e10a000801031800c0d908004e0319408039001083d03400d2100303403100d8450b00c0303c540360b00080c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 459150305 1250 459149055 459149059
    0xa0b131e02030f0f030a0c050f1f0e060601051c1b03020c06010512030703120b09040803010929120307080304050c0319030e040504080910050315010801080a0809030f070e06 76
    0x40d0481d088800004c1080b80c2081000186013001c0c801c2409a95100e814036048469000d05000c00c1c802610400250f035401c900207a0103d41c2c6410298071b07a0407a4a00c040720385080d0401000c20050b80d8110080b00c440d02400c1c1e2850a410455034000b1004001c5c81c04254a18210000c49003800d5500d6005020a034400d4001d650083c0d036200208202c03076030012400f420f160028060300b0b0100307020309030345c20385150400c4010810b0403003000000c0b4003142c200d0b803c03038203d2800300050100f00010301c26030203a0203c101c50843c41d14401c909140c0c15025021600380b282d05403002b030040d00034003402940c131500d9205580507103a0605140a588425214000a000e07203d01409141c003016181d4100b1103094054440407414a1260240000f80c507005000780e032541c10810850f405519403029101d0311003025078580c0d8890500001442c003283c0d54801c2c00303040004200040c8044500440e0440084d82e0040b070103a0b035028401d0101e400c0102c50345c03807140380b03000300100000d100e00130b020154840c99003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 459151555 1250 459150305 459150313
    0x3030513060207030c09021b060112060b0d111c02030a0f020906032103180f01061401110705040b120601060903170c0d11010f020d0209120606030a0b131e0203 70
    0xd6000407640e91116100180c17811002201c100044003440e40100150b5481301c2c1c210b03c0e03a04900054a10340380084e440b54102107540407810302030080900c0384400c131440480b209a8031541b180c4503070780065400c1d102c0a20070040036a11040c1c040d1140080c0e1061a40641580c40e1a80c69003401030a41024003026400351520300001b03060303440d010582040640c40c000c8040c1400303e0f5054209119040240400b0340c40204902484400034200118015503010070000306a00303017000009030f14114640201410700c807021a0f5028034040208211003038841c241da0000d5180742140c000351808068038100c500354084c2c100080f80780e580c4840c14100307030ba0042c500705100d50a20900d01e11540b00d824030200c0241c001e0b40d8140901c3c0e00c00c00803641c070300d0f00840020500140c0d4040110490784444443d6140950000700220f09050511500348440d900c0784c058620b40c40e00c1070202c2e4407100c1c4244010400c030041c00004500500404d18070a9840d044458070703100c1c0c3c01c49507110782d482449000aa2081c49 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 459152805 1250 459151555 459151559
    0xd05040e0a06060807110a0b091f020405010905040b0d08190807020d08040209060114180f0301060501020307080f0d0c05030604240522020c01060f080a03020a0f02130603030513 78
    0x70041c0035070812a40c266450b44031517650700b1001c88035901e0140d06030340b1038002d0707070a00004103a605500a000d4000d00300580b09032020724055441c010300b102d004500640c014841000310744c0c1c10101e42000c6810a460100e024480600043d90602c42400c0c010312040c000300f81c0c600440c000b6035103890718903820b84460846480b550000c0e41e0310700c00410a400091180b000240040c1480294103802c003030103050083d072042d464513040c1501c0c0c00103c58107806405000d005030041c5000c031640801e1541c26002004101d05001c0002c0d03d134819030101421051001698911225601c000c40d125001754840c1003003100341c4000c0050403a48107458980c03082d400c203018a0340c58800203a400c5031165044412810b12450001803001c1030b843d002201c500078020321052603000d07819000030f00180110400000e22641440c0c121030307128406401c1b00100ba40b00c01c540308002500040c0c3d00300810b030040007207200c104070f0344001610390400069034100207041c0b03103001007015080b00c041c000707500c80c900c820f04401e5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 459154055 1250 459152805 459152821
    0xe09011a040903030902130e21041e1203090e0f15011b0b01171c050f0306060d0c1d06070302060105130e0a050a2904060e010e0d05040e 60
    0xc80140c0015020324284200880d01d107403a0b40002c0d000d070300c641000715241d41a600013415481d51802e08168090701e0788040d041e0303168140809410362191600221658122604a60b9503000d603009074404220805034002c0401200304000000f00711518402c480c020007454000c04a03030b000e220300204030340d2000100d551407414812980c0f18620301d140c945456001d04c0c00458a0041c01b5a4910810718401d900b240881d0542010f140601600c66802d4954100002481d180c002c0c18414505001c04600e4001110341e4401c0454104c440780b4005191607845142c00900588235000c1000078081c5012003500e06540c00034a400e01001540611441d03000521041c03001d1840350480040c0180c00580060249251403004084405030b508400120799aa00286074a82001c144042d201a40102d00000c00c0150070402c0a0400c00b454100700310b48012580da0074185240504010984e81d2201da0440c0500000d622428070b262060701240c2120740300000191080d48503011300091220311a00241380c0f2 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 459155305 1250 459154055 459154061
    0x30702151e0c071e1113090203070605030c040e070504170c010e1e040914060103050f01050604020a0e011209080313021903020a030201110715170a0506030705121e03040e0901 77
    0xd941c2000900032504c10052110056010143c4203c0e010010300c0a882502d80302c803404040b103454901000206d08203d0b0042519161080d4009020090100100700e446213010b170654003120305050981416403a1744800703648502807034000300500c50781c58600d1071401600141c449910ba1003038a0b40303100000003e0500044091489030340c030141c102920450440d0403d40e01c040c181500800195041010740d10f0030909118080c1d10a84966001200c50802c03c1000e00c05c168011b401120308603d04201c90390041d0079507a21610050500071a0780e00c1c080d17180c000e608240d00703666100240c01c0e40d07850141070070750815003003110907401030280c0c3e41c0c1c1103800745a000d00c10095039001820a0003691442d40111100504000041c1950040100000301660102803001c0c84000c242c681e88400003c000d00400c9800000744205035940c140800d0000603103011400c501074500a4032980c03100c80b11300c1c20113494803002c0c1d902d42401000307510111b40032a03c044041d0054500307810405020380c40d400c0c0038a00b6 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 459156555 1250 459155305 459155317
    0x3110102033108250f05072d0504180c030309061101050108031e0f070303090308060303090a0b0f1303050706021e07060e0a1d2208030c030702151e0c 66
    0x15801c000d480081210000a10040e0503030110031411040300d0341d0b41145117529084225032076132000d0414401600c07800000c0451708540c188490305450700e104052180e4a00303100722405035030b0300d80810004014003205200640e40080024084683e80d20700105580c000340303d5000025400e41842034941c40601031507040341c503254000c500308018001c20224090522032000590748080025100c00c2c84000d002c0c18200340280c03030005001e10282400742818400501d0305201e60410482249256500f0000320b00391098074462030740710250140d51520610407078103103242005c00072000108000700026400b0955032241e0a07101d50400c040f940d01e10a544080352981d1381d8011020910a152140030580c0d80048002c0c9842111a6903074246450040c1c1d100c1c045481308603990403c0300800d00c2d0b040030840d00c00794201a00000b421911060b2040c00301810350b01c45800000081000240708201080420040301215115802c2401c19440d41e1052840d140c01c4000c20000004c483c42040400d40d030b1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 459157805 1250 459156555 459156563
    0x902011412090601050118032d061e0207080d0c0509060d0b1003060e130221011b050306030d0e0402190c1b120201080403090b03070201060f0e130f031101020331 71
    0x401c5066643d03040003a00d080c10270000d103092650241c60001c8d62403151071036090244400080d054401130031582000c681d2174030140418010000140002d06590454161240c0303004001100054944112020722404034481d03844000450705221980f01d40c1d01c5007a000d1001c848040401c0d644610690a40303803039106010b000440403000a0114106106e80f9141a03c014001c0160030404219503071041400e80c0c20b9078513070f990344801138141f442324a0740c08100d24203030400c01d08501c0d15400080c3e8070100c50f002041005800039140d07409488540640b071500507005400100b003001d2100003800002041d2060b074a25000c90031000c00e207401c4c0000e40382030320384244115035900f940750019100350300c01034030403020070111900000d8002202c00255001c0c075034136400403070320a1078200d0314154000b40c0d401080b0548007407024000605603905203801095400084040001a00d0070261000d450707810030100c0c40d500002c1002242c00211000314001500020b004004118680342c69800c8124000020 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 459159055 1250 459157805 459157847
    0xb0d08070206160b0406060501020f01050f0127020706021c020301060512060612040c05040c0935070e01050418150b030c06040807030c170a0609020114120906010501 73
    0xc0c000d41001c02c010038030a60325003001c011011503a6100071040c0000c6030140c480d0781d03840c1c01c180519a81840001c00c1c0e42460700c000e205034103204a00c5501020107110340850001e6604203840c800145600741c0d0902c00e40d0a0007151508058102a40a54440d02d0362103070341300c83c0540c00300300d442d214801e41f81039881694505042c61808116000c0c0c42c1006824550701003010300107070746c0c81c841030608580b007140306215400d1028640000c0c001900e20921881c030620041540c08d00a21055401110303480806100182c642d800f85110140e140081c06a24211400f85210204552104103d01d0b4122001030b141000368800543c0000e40c40b81c4c42580091a65454000001003c8415000316000d0507008041c0d035400880705001550301c0d0710940c803880c080d800c50346042043c000b2001065000b02002c41c04809900c128102c910307281c0d1899071000307004950b00c82c810415644942c0c030114004003100074941e5180362031030a0301d0004800f224000bc40340300c1c990000c01c0701d500c1002d8009114003031514103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 459160305 1250 459159055 459159067
    0x611030408070b34060f0603021806060f0d0207020a05121914010c0809010f0b090c13050a0303020a06060902090a0b1617030709083d0e030c010b0d08 66
    0x200b030a9032084030425144d03140e44406112000c06070301400502c1808104064942e95545408020f17980e0b2040103c140c030740381550810240c0c4491601c210140c648140d440480d980c1d1000050341401003e005800000000c038803446c00041540c020070040d4001c0700d912150750f56800802c10b21044280011542e90000303203d0340302c15603800c2010b51450348118030320448180240c804900311200e684490002442c4401800034040e802c0c45440e9428031501d4043c801162103001082c0704100240c103a180582c2c001030581d858504071070340513020f04401403003c145296281002942c0751480f940a81c0c00b40e01d4680c001a40b00c0303032442103900c0d20a02901100410307162030340850303503a0007a0743c014070300f40c050030103400c00100006075942d00154880902600c03400c4c490401030841c82981c01c0700c0c031141c0c0302e060243c412103245e900140109083c0d44050784a014000341c851840084222085101c90400081160502020024040c0c0d411801d000f0440441c3c0070003044841207100001920401e410414 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 459161555 1250 459160305 459160319
    0x60301020430120f12050402010c12050c06100e0f100909080d15080d0906020307060b030f0a0b0106030f0203060a030303200711040501060c051b030c19061103040807 73
    0xd0700070600c142210100e6480301580380c0e1489891008941e0000030001e640316203081c0d4000005c524482da01c9101040a4601a400a4251f106004000c3e01041030000030640040c403500845115050b1035082e68980c2c10075500380c4502503514000d14034001c4440700003945480e030820030503218a141056a01000e40303032107038540c008c0200c000c0c00c0d212220f042016601c4001240a80031007204041004819540f80c1111541805881440070301044040c52080060540c0003040d11246030f00500c0003d08002c0410000f8034101d1008142c0041d4002c2154241c140400c600e00741c2d040f12440c0d02c051007420703140b0075074500700e1004807202c07580211249014000310b03129601101107030044026003407000300d8004c2420095040060211040765036405149014200307401020b00410b014140340303400032517540c0e8440c0c6030030a0aa0800b04c403184a40d6200441d5400c01403030b07403c0300340500b4901d800100c01000382261080f900076040802d02189814038000070000844003215008806030604500b00a0703 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 459162805 1250 459161555 459161609
    0x50a1a0702060c1e040f0515070b01140f0405040605071b1e03030b0901140a090b18061f0305040218061f0c0206041203120e1f090503210603010204 65
    0x10b1362042d81200062032050004d4401000940f820201e140e40d001e10384010030100c030303024443c4229041411b001e0754000802c10803029040d111049042421140b2840114080c00d041e040a00d078014140781c20301003403103801c2e03010304e026555590b40d01c1c100150301c8140e1408103d15400090070854044003201c0034409604e01d544201b8428075010403440c2c00500003603001c440c00c0c1c00403440d40700b00c86890704692034000750050042c00340550621242403500d00007055540310000480c07840c810036000424580d1040000c2c0000e0017071030741045002010480080080004882c101d01403116421048060032103070f425544207420040c40c44420011084040c1902060f1410325000c8c041074034600c1c00140c2e030386c3c005403025015600e10210a5006410300a0101000c882c0000449140081c1c21324a090b0205104070b80001ea0004109000c0031008440003e0100e144090403502000c00c0d16007140d80001c3c4407071240c10310381c0e44400c40703501d40c001094200e124602c901c0e44102d8240f035038514035034032500d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 459164055 1250 459162805 459162817
    0x403060b130504030521010e04080912010204090e070506030c030c13150305090d080103050c01110a0b0a0c0f0518041a0406060e04060803040e010620030403050a1a0702060c 76
    0x3038549a06a010005280142da2055504030041030022030030341005041c084001c0008141d080b40e00d07140e549041c040e250041e501030f1014200c850000f541d1074694481081040c540c0d560300c0d000310350721a52142290000c0c05111002140c034007890400051a02e801c00942e401090100007440ca1600c1f40c803070802069003c84040010510340c484006800780e191040880e07008800d07100800c042c07800c1c10718541041c080c1300300442840031100041c401306200003462400e0440a0910f09008010901c050389070135560382c00102048443c0d404c200c25030724550003e02d131440c06501c5609210000050039136490103520002851110f4061804031545010f40013810340441c4c485011003200421000309041d60030a8201a0100c0d8520a0041060600d4403408005152101c095800c1500b0444403100056040c80fa050401003048010303010a072100c810450300303411a408403561144da914095840d040148425200f4005003810b190402c1e49040c00e05d4400d04095000d88002c0d81c49a4548406030002 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 459165305 1250 459164055 459164059
    0x1b03070314060a06060804030e041d03030a020a09060f0503040f15090605010e0606090607060b0102120c0a05060708190e011104090b0a090c1d060f0706090c050a0b0403060b 76
    0x211001010501040070786108894050250490380b07000c0c000c2500380d0341c1c5644818100a0084208004650702c40c25081c0140012a030100788110a480c40108042c05070301c99080d90700001040c005003c246034000d181c0e203001030300c48080003565910140c0d04070014103410300100d502000081c0000305003010104c0c202c0c0c4262140704503640d0b402008021070340ca220b0111113250752500140075a010030601140d200720100d645910b004c00c9500400c0c1c0ca4007403e0402016151202d800e401ea580c003e02c00e01c110f00581e4915903486940c1e00105036a20034003c40144d03000c1c0030f00d4000c2203086100c0c203a12481013000f0107200710601200f03041c50000700342117904c448083d5682c6420084919250f0002c20080c0b105140100b0801041c1e820050000174950001c07041c245005054030501da0040e0b07405c4040840146001d907410321190128040e44110002c13000041780001c2d42404015099100b800b941d0300400440c1e290546603000d0000d20152030041c0041d644040c001000020307007540040c0186240 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 459166555 1250 459165305 459165313
    0x60f03020f070317010e062101060e040c090c030522061517061608060d050a0209070f02010509010c02062212111605010e09130c06021b010804051b03 66
    0x5011000c2d00540011800108003400d450140b5042c088158007403e01000f0341103841c1004030000e810f540e4a004c004007611010603c81c40e1a980079030080340103050740400e280c0c1901c0c062511290090040c01740c18a42c610705100c0210480c8603128044c8900c1e8140c2644800000e010007a07a001003c20034201e4006403504804d54603440d40c2c1c0e5034140107102d030b203041c2c5c1c855490001203d0704100d0010980c0000d520544803122140e80e115038810b421603015540b0844410190510600340620540069000101607041c04521540214802c8e10035142d84d008100e1600c65820340b5007a1800c440f0700100591113480401d510f59070740d000088030045484142440d40b4101d54440f03664000b6200d000b80803c6000e000d08079041c50a2220701340441d021514001014103001c000f80500c1203010300f45000d041c403e4009100c040310242038550080d0040400e500d017903035a01000f5a200301c03051103801c440980b0131f41c0d2200c80d401002d0003400f030359011001c0d200680000ca5040001c1195148203541407107 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 459167805 1250 459166555 459166567
    0x6090a051003031409131505030c0f090403050f07050c100e0d12050c1603064a010f09030e03120d0b0303070c08030405090c0a050d050405030405220509011401060f0302 74
    0x5983c0c020552411b540860200c0c01481c41c010800d0341801070307480140650081c0e95034202aa0301d41300e80084030401103540f50a9601d95007802c1744c0700e000e5120540290140096104240035000500102c0c20004a403c071300e40000072003040701d181041c4003100385c01000728843c40b8002490890f5140d0400d4041ca401c0d810402c00f41d02c224074201c400c104000d01035002034004d00c24482a030280800924180e12406028080048842c10030080700810030480d240c12107010f0803d6a020080c0541d02060b88000d00c4441900c014010040c001c490049020400c10368038400181808150700000488000a6504200d618150324018200d6054030313652500040040230001140c3c00c00c074602800c0300380025034603281040148800310b40b0203001d8003c1d40009215036820b0580c001d04a400c8840c09000120301d588991400e04c0c136500441e04025440812a45410082000000c0b008541020403030240304a031a1042c0460803200b03000d2218004074001c00040c0880c3d030040e03085c286a954603250042c6804 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 459169055 1250 459167805 459167809
    0x1e03030b0d0305040f0902040b070605090a0212060f1605041a0d0c091a0906041e080d020c01080a060f03030f02030f130302030f0609060112170705010506090a051003031409 76
    0x981607080700491000704040c040094007841c80b0000c0d000000f411490715090500d8481240540e0a00801da56100c2d40000c10070082071003000080c95002d0070040c8086015421261584000c0710258803e03c686800104540a00c007400e50b15807130720307855031450207090864003842a040e0840701c11200408100c4407100e80c0c40c6206900c054a82c80d80c070943e12030300305100c100c0e206410700343d044513583c400d01c440708607a55042c00f01c03000c54a40f418210000c80c0b24503d00007607584a68003050703c074001c102107103601c51740200310140310090980e580c901d035517503141c40c020840e045400f4411200411010520001e0b029146088401c001f50040301c0c2080c05e40718001107c1c3d0700081d8030f0745003960380c2481041181410000e158034010b490011740300e80c2c0380007501582e5030b02c01440b0f084400411951110b00b03001400000d0198003460100160341d82c60b1030b0900e980070b0401501c030140580110343c0000c2108040340700f81c40c00b526104042e114044d01d952000c60360301c03d003e668120401c104000080c095 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 459170305 1250 459169055 459169069
    0x51302090618011d060a050a020a14010605011b1a0603100f2a1416020a1412061e071b030c1203152c0c03010f0b071e03030b 55
    0x2601840d5407502c6800c100d0400100300c82003840500040540350710000b2080d94800040e01c0c40d07205d141c40c000c0d807100d118120803031900d071039400041c3c01c8480807a041d015175401074103c202a10302c2a2100c400b044841c030308c5080a17180359800900501500c03018100945695040a238000c5001011a001c0d20000400f40d01216132081c54138592640d20381c2c1040152200720f5200700e8030307000074080c400c50305141403010305802801840d4010140340042e08000c1001340c0400d250200d80c001d00035101141c0c4407070b4010b151918800c80d992180c50000c2a00d07a010301c0c00200544240e20f2407966030700160500d400c0092428001c1d00c000d0a220002c0700306014100d021703002c07081042c0641d80c0e20765490340c0c0c0e041c40328203844151640010541401d81207101c2e4111010040300b210718840e85400310556050483c40140b040e001039003101040170050141c050394000156050324403100d15901080e980f10800c50482c8100c1400074000c4c2d00b803208480012440030700c0d0b111201c2c080d0601044500d408030008000f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 459171555 1250 459170305 459170317
    0x611091801060207060305070e0f030304081f0e01091212020d0504030e0108070807090e090a0b070c0c050f0a1e09021c0509010603050705090c090406030309030201030c0305100513020906 82
    0x90848114010800140c3c108980b100805490800b000b0600700150f0007095070004000050041070014440c280644041007154000d00c0400296004070f17003e07005607500d881005107500000360074083e003001079036010721906014940c01200c00d200001c103d0003e0700c110006100715030986a0a2154080c2204a03000b03092181e4400c0da02c031002c15002d0301c00941380d40001340900341003209150803c0485500700225900303540900c6024800f0366201140c91346000070304100200b1424600007402030542c1c0100c18007070741d02c0c8140e605ea803819442c0c00c1030228002c100b0101d1031740030b50010740030049400b620031401c1e6150414041984444e484140c4031050340d0203c00c80c2c0301c003228028802070349483e480c841e240d00003401c0e400030703c07038185107440300c1e580c0d103c50707024442c41107180710041101c0000c032404851b000c24002e4003e02c501d0b51341c2c1c10060070741c004510003a17020a091203040c001051091141c11b2183c1c0c400c0301390380390306414101841500203980c01d42c3c01c501a42000b1303042d01665408040c0c52 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 459172661 1106 459171555 459171589
    0x809030307110a120206160809060a0f091406100b0301080607050a12110a090e13120203070605131a040b040201030b0a05060309070305010c1407061109 67
    0x2040201c400f50041c0f4088001042c0c950b41c0f9004101584991800c4c80e42d82d40c804034a00007940e00c0003003100c080d000c0750802c80000f51403081c1039000c4414400c3c0003c0014100d4030310740e18001c400718040546d18803a0310640400601e40c04e002000c03401b070408051460b0455240481c041d0384d07800301506074803d000000c1007402e100c0e8426400c101c20b41200d0035050146039a00c040d132580d030350b00203c85540020780710840800c00c00403022a080c0900c2000040c410700d080d00d501d6074221040e001500c401140420840c41c40481d9441c01890301980214404ca0112005d81c9041c00c40358120555201d103a011010820010448252806178015020300700442e03400403000001c0c0d8410582d81020b1351101c0701206100544400042e41401d90744100000c102e0100903520650b640c50100340b0748264500f080248400248054003c2481c41030092a124146034003800040d13150640c00320150 = true := by decide +kernel

theorem cover : BRFrame.Cov 458992805 459172661 := by
  have h0 := BRFrame.cov_init 458992805
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458992805 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 458992805 ≤ n) (h2 : n < 459172661) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
