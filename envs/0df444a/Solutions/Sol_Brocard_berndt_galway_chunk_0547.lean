-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0547
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:22:44.059317+00:00
-- url     : https://prove2.me/submissions/ab5597a2-277c-404a-81c4-5c4b28624d1d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 98201438 ≤ n < 98381295 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 98202688 1250 98201438 98201447
    0x60e0708070e01020c0405150d0c090b060c0304060e010c0602030f150306060d0b090114130218010305070b090d150903030b15030f07030b0a080c0a0b09060304020d2103060e07 77
    0x250107003401a003010f1160512450306400c4184c114043c8401c001c04080058001640c1c464041c07821660105520810001074bc51031184441e00310066850340d20745044070204a40741e114078000c0105110b405100001943d115030b0f50038174440d0f404032046580f0f003805c085501c070440048a441300310b40c1051040780313414100400c0f018081c00d030180002d02c24919550390422200401003841c1c0071596125152401180a095107a0040c41011060b00c1c2a002c2801481606450780c0040c0892070385401c01000068400200c140480e0399180007242c8401910f40007900c07a00d418000640030703903c07010602003501c3ca19441501028800c0d103081180806400a00c55641440041d200d12a141130000031241d00c040c21100c0d90140341d525000404c1000310001600801d01b5400076100c81c0c4c403204d0342443e10704240d04140302070000e080c0c0c2d060924000b000061007500c03000740001c0c00758080c242d010702044a010444500f908092118400341c214085004005200798030808800403155400310321003a018 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 98203938 1250 98202688 98202707
    0x30609020301051b12190903080405060f1b030907030602040e102304020702030a1704080d02030f07020d0201020c0622150212071416090c0806030c01030c03060306060e070807 77
    0x603102c0d4282a10b904082c1445c000090017003c400041c011203071803000003480386107106c51190f101d103001d0f400d05092803403801800921384003200d032a21040c017002407100154100044c1400060035500d6035102c00391030034421a80e00c010901c0c4d001190100d0742e581c00d2011644a0f98602905022059407517141c071103100038021800d4190742c944180b100f050305080d0002c0035403500180c125403403000c203a9201203444a41c613001c1c0700b5501000c40c0500c0840b0051250340034520861004600b0310ad1601400d040500c11590000d120325403801081c0704690007408503a0310710000802a1352940032010ad004a03038080121400020799804001048488450070496181c480070740c014440007081008088140d0720090041e0341c035203001800c000d02e084080081e07100e2400f410005484203407406105200341c50343c00e5180000e02c04104100b01d0507072000101c036012a06d007440d000c0b50000f24044140c00504464101406182c102880411100301d00454603009105650322008603a6803194200d60550a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 98205188 1250 98203938 98203981
    0xd08071d010e0402070c030c260d020c061b012c06090a060209130513140d1e14070501020a02070608040b010302060a0509090412081302062d0403060902030105 70
    0x20760100020605050340a0b21220307204988046c0c10781c2e1240c450020a012682c02106001e00c0d40c84030380e0b21400301030558001200c0d540018901c800c845070000c0e40300c80c84a03180b07c1c068100440c1d0380c1c04002c80b0001c0c036190509072400810a4500e00b005628981c2e0314024101052208091455410180000c0b0300340318552075000740c034000c02c0c65a54400030b980200c2e602640881003508480722024144201340c02a4491f9025480c407039128500000030b1044200700b034845030000e441c02440c1a4001c1010080b440304121100d100b00502e042c15113500003c22002c2c100321801013250810440158000c200310070054003111242a07070b40b407085800c0c0d6000c50f0009c100401102c0100014240341010740b0040c4401d041841c1482004408a4040c210840d001c3d1080d4540b0b4510440c4103400c904280d4001c125803d00d142c0400482d0040392070703407043d0046000a01d060305110105080f02d456440c00403d40b0714120ba556590ba420107030064481c130308080c0c0c403c0d4a0b01001c100c00041d0640e9460503580f = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 98206438 1250 98205188 98205197
    0xf010f0e0603070203070b010602060105090a0501060509040e16031113110406050c010204030209070302120105091608090111030f090d020318060c0a15060305010b190e07050c0d08071d01 82
    0x140d20005004190700007030301e4401503200c10311040f80001d800d9642a8040d110a40c01002d5070340c585800c2100d8801c0240c452a07140f89400010b0190710340c018210307a0440700c203132070118084c0d0030000224a410400e01d4880c03c1d203181500c01104001c03091540d5101c0720000c55444c1540602a41807000b1626030056501c4084020001000450302410151550a0400c0001414181e032034010612075441280c0c0000001d07800901c1000400c100011507001d454242c03465101480d000681c003500501e4455101c0c144520030b0000f40f030301103007504401081c006100e04591282001001154070350020794002000c0d0003044048190b07688004140d543c1c840c42a024050051b02d840280030f4a80d001500c81401405002c8048012030b040000b01150040d80610002c2d8491131820300c00e00b101d42030000c441c414880110101c0007114826005c6041e1084090650555152058240e40510840c9421903141c05802c0340c5920302c070b41003a00d40d849465a5121400070040d281060311110680130074190204c2c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 98207688 1250 98206438 98206457
    0x1050618010e0c12100323030a12020f0a020a0507170601060c05011d0304150504050a0905070c0b0c03010510111e0a061805241902160b060f010f 64
    0x480d03500ba8580001e03060892910b0b0020300001001060b90448402d26001c014610800c03c1000c072160004066089045614440c81450301c40d545a01c107800b0b5203801c12854801d01030320300e251541203481074403100074a83d0386c802078404042d440f1600c0b200207480d10300450500040c00000300c009050401009405000700341e082007001d80b182c00c2954405c3d01c0640d40d582400030500440d203000c545400640c801191251f282c500043c06861540c910201040024003042007103481d400d60031000d8405c21840428181e0f16491b0840300c0c03000e0020040c2080d0510b805116012007410002c5040e07075400e80b2400d070120428401070b0b88201340010038140c1039120200031400400c050a100254402c2e00d0180c2c5c04001654827140d0a41d2551711550808030f0301c0e001c401081100801800c040403ca02d2a0f10a448440039103540d81c4140080c4040701c00d1301c607903410484800a590469a45000000850200b82d03c80d0070580305c8494101c3e4014068820101074540640c09070b600d000301e07490680e80c1c10415 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 98208938 1250 98207688 98207699
    0xe160311010905190b03040f0203160801050a02090303030408180a060c0b161d03010605030312010f061e0507081204110102070b030c070f080c010e0f12040f060f0c0b090c030105061801 81
    0x50351b0000300292094180b140b50400107940511800e07a4203d80804101e5049081c64500b60031110054543c007000c0b481040305101a0300c010003501c3c1d02980100143d615a40380c041900141104840343e20f40c400305d262004074000350450383d000c3c606405145840c8036a981d160121001c4482d031a40c02d400b00d075001c2c0101607a500450390220a0080217000400c0b030640d50000b181c5503410039040103160f180d07500e0042c0001e050115403003004000505c0c00e1011850941c0200040700ca40031700d048200040000d802090028802c00c030381d40f82380701c60b520070384034640b90604d80c954514600407540113006555001800c0484034040c0ca002e1180d400e0400d1800c403035661081d1190001c64002c5a8200d028408101d8201c02842503424940102018011002c01c1c078241a0400c01d0300c6d00120342c8018180010301198901414007000c1e5981170802034001d49081c3d40503224000c80c100010007a248040070042e280d07101240c410340c8000c0940003070016403079030307802c00644114840d80340c2030041d07194004014 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 98210188 1250 98208938 98208959
    0x60c0311090f1f0c02040f05070f110f030f04090c0c170c150a05011d0c030106120e0f071401030203090309091305010212070801080f060a0e16031101090519 69
    0x12100402002c8011120030343c08902d09645a81c1102180d003202c002010b600386070203605602000c5440c200000d24244201034600103132a407050082000c07203921407017100f0b010400d03030110b4840c52045a0b1038031000100d4429550140c0a0b01030321505000c00b1a8038603008a03815942c143d07100a03d4000d40c42400781602060300314003101e900920624070503c1d1910400d4a80078010381d02e88130049141d40c100084001040321b1030050095107521803040142c0088000d007501c1c1500c8841c50181c5942101080c0c1038050012100b40b0041400b8400c0078652900c0009003040c00c030f849034007000068109a0006608900048a820031180c000700444540351800c0c0c08015400090589540d20b001c000742c0b01c43c0d007207800c060412080303400307684248500e8940100c100d138010700ca40c1006240c65000d800d002c540700d80707007c1c240e095501e4480c01090811942402180514091441c412107140d40c1c9042456168001d0301243d8003080848001040600307101c41c40307a80c40a020029490a81c0c48c100340c155 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 98211438 1250 98210188 98210209
    0x131a040b0a090504110f1f030513080a0801140d11121204080102040302090a09080a1110020a0201020d050601030605061c0f020c0d02060901051014040905060c07060c031109 76
    0x95101c6880318010030441c0181c0b00e103a00942c0250340d17400c603403e140c01c1031200d0440441c0000340b151000d007500322003800250720b070341400091600d40440c507500d44268045540e00300c3c2000a0a001020403c0102d66501c50070042c104c0e07803a580550041c1c42c801041c004910035100b0050070981c0880340c009010b003000b094003e50311881504440d05a20b800d0300e41c16441d0040d400542541e50006401c00c203519210141d19040400c510081120403c940e4900203030b4414070182000b40b018a0452000c0544140201007000c5490071056613614181d05000b4000c0d8024098201e5603898040840c1882d4403910991050741c03c00b40c542440d019103050710f90445084003801c140360703d4840380700b007890680900103403d5900d14640100300503101d6603806820004001c142041e1a8034107020001804800c00c0c0200c101c2d08550f4140c1c49803a40a03000c01d01525400b030000d06076202c1c0101340409240004014001c460083c071007004101c1402d2803c80940c1d400981c1403007201030074040720b10039150900100e03 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 98212688 1250 98211438 98211461
    0x9050a030308100e01080a030e0303090d0609050f030a030605090f0702060f13050d0302070204200f0702060f19080106090f0603020901050c0d051804050606030a020903070f0305060105131a04 84
    0xf601551001da0741c81010090b00302907031039040306842c6820503030800e20b81e0380e02000840c080c504224010002c07805410604902030451500e1342120000e1000c02d10520458502403c20f496a0f0f164980015000c1c256621070036014818000c00581054030201c0c02da4000c0b81c45901602e80c1e40c481c01003040303508001400300307010303900d11104d003c000a078200209001940303191005600c914040c0104802c0700c81c0400300220403400842c0d06255294503c003100c44100a4039043e80e112813590020039200d004690b1030300c041071000951b42c0100700001d91260f003100019980c8403450380c0c0303074002111540407512500c0c0245a010700103121990003900900340001041c5003123824040036644040c589a20251000085400014449010010031a10384401c6006450130b00c01d0b41000004103040388030041054000b258045440c003141e94040c0505c00040c101490909022038580c10104e4841c20288206482030941c00c9100364110f000c0d01034080c000c2101406c0b0080c200c0784400340409071402d0b0546 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 98213938 1250 98212688 98212711
    0x3050a030c0c0b0a080a050f060a090c0c020a0806040203070501021506040515040911010f0314060906060f040f091d0c0d050f16080d0c02030a0611040e0a05060901050109050a030308 80
    0x3060302580080646084400c0356a00d0305d1508244584200302e0304013500c50780c1010001000c220b081d03264040405e04641d044100043c10040c6031108540400b01400d00a5218460381c01c00038207448001611402103008400303a649c460740d0b50700161780e29540c898840300f04031000000900c0070715050380400da21000800b034903138500300d01030001030444008050486c0e4007007110b9581015940c1c0440030120b0018513040400055902c1031076103183d14401040c20748100003500010b60701352100416190a8035034104540d440325101c89207808080c085005d0046082e15200c2100400c0300c0746c1400702c0003028410098030a0f42150700c140b16034170380549800d4130107115081003200503050802100c0842c80244001f0b2400a0410032811706014407004607501700501e182504016030f402050101480e580084000740900311400048114010340c0d0082440420700020058805242d0b08980d203c6c4a0844014080381e0300e4030015542020302d40621608115600310038070000340030310303c1c140e0000c0e580d450 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 98215188 1250 98213938 98213963
    0x102120114041b0302120c0a0c0611130605030403080705040b0703030203060409080a0c0302070512030f030901061d070e040e030a0e011b0c081e0309010f050c060103140f060103050a030c 82
    0x9a08803407003282c4400c030002071740c0010441c0b0b103c0c2007107035090341280c031170020075244c5290342c0717001040c0902042d0007502041d51505400410095a4103d03400400e00301d040c107101c190398070310140498008031030540c081580c003000100300074450002c45050b107090302c600ca814192503407400c80003904001c08030343e000740d179400c8410003286c000700c0a4403810181d0f64400d911150306140081c20600903912143c082c2006204400c40d01401205841103c0342c081c24082e100d944540d88507014000c0c9600650031891205c1000f03c41d2103a8803000d501c01d500c10340300c05c802d070390111007840115084040c2a080d81e810900c11820150f100f0807a050190005242074007000754446d04115205040d01030841e0310310400c000804c01800300380b0050140c40c0c11070124000d440d9040c011107450303210380c0f41081e04225040040e1906940188203850807a0000340480d10550b031a481c00b0410105480e148095030701c100784948110081c0043e5047c181c9520501070300e000c44540d40c00f9518402c030120119108810300d0f1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 98216438 1250 98215188 98215211
    0x6120b04050901020408010c030506090609040215070c060915080a0209150c0109020f010513060f030906051303031109010509040e0705030604050303040c06091203140903010e0304030c0503010212011404 89
    0xd0718024a0500001a940e0b443c10140300d003100c485851850030300d0b01701401c1005a5549c206d10660040046d06c040060b42ea81c0d20007c1c4055040101c0c203150381c100481d0303000500c0f2242880106503459500ca40001d1030301c58030440030210ba1002500c3c0080c40940008940e0020f0b81c0250807000c002518503100c04452521100e0144c0012200c414560366801040d400e524048814004000003070900780d2412040c14000c10441e040d602400052200038070421901c10311940c40a419580c005d003040002d424054850450408040e90582c000f80c204038910140407191070072103c85042c140c6601d882c0480c1c1d04140009400d00822104041c00742d0720001400381c038140300c00b910440c403400c00b5503a40e00d01490b00b4032041a00b90004000c01148181c02d100ca20104035418142c2c03905810306c40311061304042e4282152280400094155081c0400034481102c0000504280d92254100610841e25102814201c0c080c06490a9540c130100d8010045080304400c0e03003907000310160000c510565900d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 98217688 1250 98216438 98216441
    0xf020415030e0601170604120315060519090f030b060102120a1707050301180906020706050705040315060e18070503011d120c0a080d090609110414040221070302090a0207031b020a06120b04 83
    0xbd50028004c180b00050031211002c09440c8101c9030100c13400c02c006c1460030089103c5058045000c01800d081c844004140030f0380c000c00c100c0c925098034801c1107648403011440100086020690710411031140008034500794001c50541c5d042c1c40c0c000b040062960b09481d001c0000d00340e804d038180c9045a0030013138003010855074040c107032049030291503055859185180c81c840c072003000e9600c0c0320b031289070800c24480c00a454210a400c5012a03c210910740340e03003080c407402c003051030340099415881c1c40343e002403600f0900103c4c500031034000261a014200c2540304a04d5110f6908842081d8202354815800909940058800e01c0c5070384000140f8820a40d03100c204481a00303d060350995800003004107503280030700405a03254a03482d4003100740d0034581d001c64011481a10246403074110f02e42d480c55811b004000700d03c021034004000d0000c07828885101c10095005400a600294000200001081c0300751000d01000d40d014010219441c901141100c00c5a0264448080c60740c9078505140181d40350b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 98218938 1250 98217688 98217731
    0x604110d031701080105100803090d06020708090315160306030f03050a1206090f0b01020a051b0f06040e1515071514100e0a0c0e040f020415030e06011706041203 71
    0x1c4e03400000c0c45040454070601e003402075500c04074107070303104016030845a03e8000300c0d03524242d44842e015071038140b42c0c40c2140c41d5006901249070503100d1207040003400e0002903102c2e8010212a111408496101c031421410b4800303c1c08041e2224070030068040010340b2940040100e101d80340b51404104582d44001800e4580d19440840302e59280c3d8410702a81c07a46205840740424240010440f00c0e203255031302515040c20440c880fa0aa40c580d0700003520742ca0f4860a00460703140101280c0c2d40759140c40400001e40b43c2922404000d028840c41d0380e04a007080d01043d070140c803108500d14103008559503181c40c1d5810189182000c9500d80c0540315002d0041c00c0114001c0d040700d15540c4144d4102030030384a164000502e00d0b0406801d24940e4040741350415190003e6080039203011841c5076041003150007a11a551000e4000302050803d040d1207941644580200d1841d44151403042c0d907540300c130260200941c0102006a0041000f2500048051141885036581c0b0b0401003560300030ba001d400b103c00d41 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 98220188 1250 98218938 98218949
    0x1050721030b100f1e02060f0405030409020c100b060702030709021303240f1107030302070512120411011d12010b090a0204060305060901080304050909030d09060c0305090604110d031701 82
    0x2d0840c5000076054201d90030f040c00000520310117825461581c802580d841010f05018800d118000205050200500844000d880b030208250f554134503540e5055501c080f140e280d00c008625040c2d02492914007042224400c40e002001440c0d10340c1400b80390402944891403184101440b80700000000c0c3c600c1c1642036040d0200691407050844c5000c6240a9940c3c0e0403012a009103840d070700015104901c0103a500711905840c00685442107468901d14003084140200740b080e2000c50303901202d08002103918455171240b609010300f01254001981e080c005c03481501c919402260403c083c5040c03040c0511030b8082c2840010410202110100312101801c1d944042903d80008003440b11a0b0540075040c6c103c4800e82d5804a00d6140c44102502c80c0514001d41e031054410f0000310780514001c109503014070605501c2040100c1051034020000c0804074440c6003c01d08110000300d0240b4081000c82c80b0b0303900010915115040102004002c8140103012030500007500600a0742003540c2c1c00240c042d00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 98221438 1250 98220188 98220197
    0x20628030501030213050f15030129030f070608012709050d110708120703050408100209040e06040b010e07020a06140702070b190f09051909060501050721030b10 71
    0x5040d4018405070205c1c843c0d600320502d007404180040070241520643e44056074170022005d190002d40024094002070355440a58040305800040401e500b040e440440303d0201c0c111120f00c0c00340b411468a070041c40c41254041841100104034007690001150b0311400d0800d40204030848a1414000700c800303082c01a6080d5004980140605400aa0b081c210f0101d141c0100070b0b02d4500103005a85030600c0641159600c00405c02000309400707202502c000d0000c40c000c1d10101ea05201d40701000350020040b043c412170a008550070b01080204181d800b981d040301c0000056800d0030410401030002a10031800c51007070302c0c09100403a1891245840c00c40c43e4001c010f2036402d01c1d1a00926000f002d8011015001080207021a00600d00280c1da000041c10b082012000d000450262030b201e5580e0721403074028040345c002c0321054103985801415907a02510802c802e40d1550011a000d010f914070003410076858202100907803943c0c14007421020104c0c0b40114a0b840d4040100c2c1c080100d10300c034440480d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 98222688 1250 98221438 98221441
    0x60702010501030308100e0c0c16080a02030105010b030f04032102160b070201020c0d0e01090f0305060a0e010b0a0501050d0f0608031305010212030403081305030f1c0c0c0206280305 80
    0x613808141c21b80c0019a108080000608004d081d0b10303c842c0240100040c2807000540c0c0b07131040d100b17005400e44000b290240004007aa2864065200c80c90000c049102e54a010008203038040108140c0307006441c0034002894580e2641d4050314145600144070b412200540714661181d0568001070040407800701d0003500f900000e191034110b82602a0102c01035900502000411701b034000b9001040346010301c0d01c0e50395248001c0058a8051582d00040042c2208103008800e00000003807040c000d102c5140100030301404102020700f00d0b8850001c043c1d0019000e0010007040d072113940541000240743d0000110f40850340458011a00a9880042c082d0004203082d4006411a0310000080100303002034034001403032000c556414400144020140042240070540c5a0305280400b9500c541c0031084030343d80c031030200071300c10300780c101340810f5034011803507018004140703401c0c020512a82e0068075022201e4019900704101ca81145962000385088500d0040c4422400c02050450030b010741c400142e10f = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 98223938 1250 98222688 98222693
    0x8010903030e0f03090d14010c03020307080915061905030a03020a02010206010b070c0911090907020f070b1201060806030307050a060501090b04020705120a020f0618060601021f0f0e06070201050103 87
    0x3a00c1001107004003540210440f601e5030040030049072111202281c05a00b13840c00d926040d40303a401d013500c1b001d034198608081c0140e03454055008502589203070b22801442e0b56100c46850740c90342d03010081600208040041156801c249040a00100682410302003540e00c910103c1e20388003100c1c80640050b03024210100075560144800c5003d4440061568502030541c0c80c0e0031403134203007489160122a03454040c8440306442d60140e8100c01d00c020040700c0507081c00394000356241100b100d445080c0c01000030018000c0d91503003c940500c1c0814000c86003580c0f91581c01e81c0c500784000e01040d01404100005000200244000310780d40f031042c5c6d0002410350401244200311155858014001c0f441000b4090200e0380024031400b414007190703020f903030301c0020010407030400c005d031015414076200300d40c1440596484840c3d080d03191a04202141c13142c0da120b1004a030303a20201c4081d1601c0f035a038004000f4a9000c540c202c0c207283c1c4800440030035100c2550b042103182040c00c50310200180d42d2000113104 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 98225188 1250 98223938 98223941
    0xc0c05150105091e01050f0a1d0603010b01030614040e0f030301090501061b050a0b040302120d0509100507050d20030a020d0608030c0d03020d1b080403020d03091a0603070306060801090303 83
    0x1c004c000641c0400800a403151102c12444040c09154400d00403855551105d5840050040203045112092220301c8c02103400451150b03410350f0b10a10035400c01041300c01c40c0d41700f03110703401c00c443e030380040d03c0b200c3d24554080c0300c0106140d035914500c9000712040080c446d482080114002c144400340000c0a40c074240d13000f804000503032408079941008810071008640001030070090280c00ca5107034823407178a4900e820703460007000411070382c143c51002c2840c0404205551000c0c0c8030790000c9090f6860740c8007202011088179012a26000428400e01884913124a00e0380300c040791860140d040100342118807400e45603900100c0c0d400960b943c000460480300e000c3e601440005104000c01141054001e0203d00d48401c50f03038044804040c0d010031400e00d01c14103500650b84001800e06002c40340210340c40020a010f02c12641a8058414611001c24a41c400d1240f40b0b003d40d080900301a050300c03010031142d01c0d004080c0c000f03617241c802c9680c04800320320b0070310548000f02a001e000050303da80f107140c041c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 98226438 1250 98225188 98225191
    0x5040305071a0106171e0a09050106050603040c180209063609011703040302122d0705010e0609030601081f1109040203040c0b03090604060614010906030c0c0515010509 74
    0x1d40d42c50502d0010021240c01c1002d01080303043d8800304031540d07601d050050071203203c64002c4135004251501131242070142035111900c00d03409030b0000e00c841a121410301a1501c0107842c0140012112a42041200788520b801000032031040030142c138011054001820b00d400280d125884440c202050010039455850100d602030082d25200010012050004803903020500c25269a15600150420101800d1007110084c2d5070003000c60405245484061f43d941c1040c0040c14400b40061b09006c06980714008612024210b640007490401d040500454080c04802081d0350000001d00c6518090340d014452a0b02070f011110003045c260030400c014024503500a0445c10308289080303680546240d4801c1100c1803200256005603176603c85141c001179454040c2d000400e00320002c800c1c08020580441d00750f001da40501c030705001442c0c4425038418010118600d03203020032640304c820002d440c0650000840c204080c24581c100c0c40b00e079101e4504165164240b0400d0940081c0140080d00d041401a03 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 98227688 1250 98226438 98226473
    0x20708151806040f06050a060315020307080702030f16020d06020c0d0201050711060a05070c1704090f020c030d0c09080a0501060503010e03160b040f1a10080d020a030e03030d0504030507 82
    0x10501410300f9101d13202c0c46038825802a003c80e484200003040c10505800c100001d40d8001d62000c800d0080d0801d640080d001a03c80340c000800401c00b050300c50348000140c4908840703030801c0e246413480c3d07420646649030203c0012071b088140c1c58180000321340f251001d0800e140307420780544081007011a000b07003150300c002d24460034001c0094400711642400a42070741d00c12104080013a69403100c14066800f58107183e002032140c1c0c2c4144120f050b91481c1030160041725181d10090200d2041d80147d20241d010744451400150300c00c0c018030440307000b290000910003400c0e0605801d5240c90705c0d00c0c10b003072499a41d002c1c2c640e42e4440d00c04100a080911540040881c81006181402c1840000b50030ba04203055000d03008009000c040740500203080a13500980b07502c1040e090460717042510344440715008440001054106800010303602101041c00e203191031311030307018040008044d82c1c02d4694007924194540c0600c4140700024051149219043c0100d0003521842d455030030320728000000e0b40f0b900484 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 98228938 1250 98227688 98227693
    0xb07230d0c060b0d120504030c050f010507060c2003070c140a120302030904021207020f2b0e0612040c0b09060304020f040f05040b010501030614100f0207081518 71
    0x10300c000d9562040c011030155511000206418108a00003000014490302c040d0a0307030302c820f4030000200d4102c401001203074407462060200070390740d008029800305611449030100b2810004000001c0380399206075514601820030081400400c2c0a0f0041d6031091200014544d10020350701041c800c806400100408199202200040180e808582100010b202d601700004c60740128808050003030007558840c1070064000c64980f1001c5942c00307810241601c5110250150400c8801c0000d00032a0700750100a0700c10030309250764441600d01c01c00503c0700b4042010401c46c100418030640d580002072044030000c00c0c0454050070981801282094141e20003900814104400b420310344406054a174056011a80f0b1400c60702024049000740003940c2616900c20b00d860100000c020541341c1247c1a507100380c0e81007012a0b11107e043d194001c09034403181c0d0140d0b41129015840d407240b0022501181d4500c1944c0c0296a522140c2d0b2500368480d9203505600e04110401c00c0419001c2840150b00c03000900 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 98230188 1250 98228938 98228953
    0x1050907120c05040b010203160605040204050702010911151b01050f060607050c15070206070c03061505090103020f0a1a0a0e0607030e09060307080f1f0e031b070b0723 74
    0x4901e015644548079550080752034012405e9903030b0092090303440103404032a514140700a5441c1648c000d10080780c1c207e2045260101281003580305108800e0315541c13150080ea9150020f40030444508043e01283c003c40800300841c040041c9449807240c44400444008a06070920b09805550110000c003024007030441407110f00080384001680c1910307800280c4803a10420365540340782009220748440603400401c00110b05080084408400080b00c0c05541c04100c0c40c032501d104464014218410294040e03946001840035240c24020a50070b101c00070f00709540316548841003814440404c40d0340f1441c040110328425455001116800c00c00e008030340c4249080030300e03075000d0200150051018040e01342c2e0b03000a00300b5102040003e003c0d0210f001110402024002c400740c2da0049407003158100c2c040698412241c41060141500c0c60524601031030405150030a0f003048030829003090074035482501d800256803001c120091034a540a001c86550964080e82030301c3e81039032b40d440d940b070090788682c1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 98231438 1250 98230188 98230193
    0x70b091923101b02070e090a0b09010e010501030c0312032d09020603010b0d2915040504110c062505071a1e01090e06190e06090105090712 61
    0x7000c88035902061041c0da021619000a092414419602d4150300603d415601144446480c0809080c455582c1c200c401c01901c803051008880800d41d400001c581c04071811a001910b0300e4042907200c1510800000d280002e036442c1400d41e00c3c20f0b032050751000c800c641e0034024030511130b88010854005040902c0a2001c1440301280042e1072501c20400c05039070022824218400e0f0003c12440360000d003181c2d180d5840b554072000681c03080303038040f810324500310b00c2e501045108517111100003044800042302c5110710741031004120040151480700c4500b0400401c1c180d845100e400c0d105078440b020b064407001000a12840c10303101a00c0768102c0008003001c0311651a59a5000d00202d84602d012034450003c0d1400c4443c14154032000401011071000700b194001c460100c400d030f0064030241d000c1190742d030b13004500d084800406840019030003860000b100641008000880003000050010b1000d0011070480d0030614240d900d0040ea9440f80148030f01504200038240240610032003802c0300c00031a9 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 98232688 1250 98231438 98231453
    0x302030603031b10290d050a022205010306050402010e04090b0601051623011103010305060703050c09040518010c03110313060b0909010b0306070c0201082406070b0919 74
    0x150b96548600201c0381e016070350a410701101c11207400310001071240031920310034101002009291000c81200c5c404a1038282d00c0e000031002ea2a07a08480a031002c0d0f2203540900021400214800c503400320f200508515001d49480342600a40c0120b2000601c1c0c1000e10004101d405684100c500c25810401d42d140451159181180c00130424204603a41e400d00300c05868100c007002c04040c100c442011802421100031880d412851307043c4e1002080500d991b041c108070580001e00001c2c10540c4a5400a11014000c0d44045c1d045503000800906140d07030000041c00340c550440d03500784100d0046880100640d000d000300c0c0850140c070b003404d00402030300e0300c00c50482d8080100f0b514250a0020b500c2014404190300c040d0040074040c2003603c551500482a40c003030174008030f0440c001d128043c0010b038514829040f204c5599416540c000d101d40316120504030442c111101821050900c00f9440ca060b5030313001c02004414443c00340f80c40310f89000c6101c182000800c8843c20203098102c010600056840d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 98233938 1250 98232688 98232697
    0x7030f03170f01051f110f0616050a020601060311040e15040b090c09010804021206070f18050a05040209190611010b0303040e0c13030f0624080d03020f070c0e01080607030203060303 80
    0x4130406200d0300040c00301c21142002916581c40c8039005001f01c00d406804049000d501c905400d440902c0e45100031001260103128003401d0500580000c001800614400d800808110360b410a00310f003401d4950506480d2000195007a4403104100300d800c2e000381c24940030303903003c01804aa890129151100034117100d40f00755450981081a5040007504564480c480c42640040c810211441c40c0f07080380b800f5182e80500103181d004545a20030b03070882900442200b074140c8101500e1a2181407914045c44040d422080f1401d611114000842040c142610742210003440b60b42e45011040764554105801c58016001141c0a078204120600c030204070b440e411900903081c010410f580703560650600303101c0342e00c60f00000c1003804192120810311400f900090465075180743c0f01510301c14058540b03003171100248500351240d0004103008400600aa01038100102c1e0b9501640c58101a66203040d6890420b802040b1201813220040c811810104081644000c403030408502c1c505180f00000d40e207028 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 98235188 1250 98233938 98233969
    0x30302100c0311040605070201121b11031e0901090501030b0904020108060d08030f1905040f02040c02031e0d11130e0a06050409030207150513090c0207030f03170f0105 74
    0x1112400d40c1501840b81d441005105641105039407242d440d40e000511a920045080e80054040401201c1684081c814115030b04040d05000030710300c4a0000903568407401c450000c407580000e008001f845d83c03140c1c039291003c054100707580355510700b00c50025242c09100e401c404d04040c600840a25561103e140040d0050380901f4030050302e68604000603900c03044440010900c0c2c00103c207000001c1280121140169144182440015034140800c41110003c49020b006c07546001000c40260400703074080c0c00d807458a4416a031900c002e91040142c8140769190a6001c507030300113490a241c00d03091041419464400580a1400204010550841c5058011407050b02c4500d00415055141030b44200300400e03016100744289400d0b414065180c41041c17151084000c4075442c50741c2054407820845a04591007082416403604003440c0ea8010681c40c4080740540c46000408000f2a60b0011241c40d2a4400e982c1c000c1c4040000d0b10b40c6141200107800c01e1a00402c2100500003a9142d0130341030b05200 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 98236438 1250 98235188 98235191
    0x706050f0702032503020906040207020616020604120f0c0b0a08010312050d05041a0105030c03120c0a0209040818010c0305071202070b03010f080f030c0c09100f060e040f0603030210 80
    0x4a01e800000e0424415644404a603050200000d00b015260306400c01181c4c0215050825903076280c0a01c001c2e031255040080d4082810410607021040a1210b6940503001500792414075442e412404660384c4102010366030400c21130540380401c44440e2440700a40041d40625040c103021000140c007800040c04001c00c0005400ca11481e0148120141c5030014080e4030144020308090500c03004d43c091000300d00b0500c441c0c0308004100750400294958011602500030403019241c07045024240d0031400e40381c5464001e80c0da00300c015035143c1c110107001d24040c1c0b2303d80d90340e1302c5265101e0303403007400c2e6007144e905002c8000c8194001c2034001081c0c44005410181c503450760380c500c40e4103d0800030240c102c502035002c04400800c00c03c14003410350013a5544c40c0100d40c2440054034901d0303aa8080c0c9800040c0642c004d241c0b1018030305050504980011050605522403038440d40b0b00c10b00c01c406500010300040a01e008440b4070b117024013841e01c814904001c10401c06056480094444001081c03903484036 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 98237688 1250 98236438 98236447
    0x2060a02100203010f080f0105060a090216080307210e030301030602071e0818010305010f05040207020a1503020a080601081603020c03070f06090227011211030307060c09080706050f 80
    0x140203008031081e4203010003045680390386031803c100c0900254000c15a9512070003080303403001d40051041500031200203251b03114040c90150881e020303510088002c107600005c50080030024100c80081d600031030302502c0f04810390380c0e0340c40c5d10002c80c082d45d9200010303641032101844004101004590640e90826005640e440082c2441c640b03002d00041c50400a50003488e13020700740411100506502c00d101502412300c1e0500c50011400c0d240280100c02c000c42513414104401c2c6010350040007580c1c4083c0c540b0f40104d81c7d4086804000e28540154400709400040e0400b056500040c9150f000c002402c2044050401c080b012441c950f214203880309155000404513100c20b8100700351081d49900101c00d80003144545484000303001c07040008c07800390451540789200840c01c0211a15113860321960000668606042c40e00d400100c02c505030380f445060002146244c80500003858803a0149001060b40c005428009012900b594042d298a400c501c0701800100e03449012150104400c0d0b0350282c94 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 98238938 1250 98237688 98237707
    0x708040b0d0615080a0c090e060d020d02180604201b16081e010903020a030c06140108030306090105040b0a05190b0301080601060f0e01080a09030c0501020d0207051603020d0206 78
    0x10071003034100c0d100e4464210f10103068203a001540601c03a00541c48103000c0004030074015202c03803055010321201354420000182050a000910210315800100b00343c101d442c05401041560140308202008042e40004211aa042c80d00401e044020540c854505002e8103000e14491802003003003000005000c40c000c0341600004000210400c4100d104689001d5998101581d8521500050810029080d0f02c51410369106105800010390160082d142107022a50103c6900707100310030841d4655a25409d078200c4d807611061240c0a803800780010f56aa041000402c0b901d004164400c51107a0b040c0f41500d005603e4840508003110341c00c3d01c0f0a10f12a59400781c0038520038068201c0c1c4c46040022000080b00c060020326641200d00d19181d02038030f44c0044404958003900000a030380454819404a400e024803507104d0300f21035019140480304180250303030356400c0e64003003408020041d80100303209082c0101400b2070303075450300084d01828400345140c0c00324102c1511400003034170448022820301071 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 98240188 1250 98238938 98238941
    0x60b0708040e13020312090315040b13081303080903010f1a15041809030906020c011403060102012405100305010f0528121101080f190f0516140708040b0d 68
    0x10b140e40d0040942c0d01c1da2007011090b9035103800c810080381c424442c0289022720440d680e145140140d8104510040c9a55110802c03980588581022200101c00b000440364844051008201540c400d0f0601c81d6030704648001c141c2501d1170b04681c01c288034900181b1001c00104000d100868420540d142c0b882d80502c2082c422031401140d204802c84241014448868104c41d804840700620ac0d0b1070b40303000c0c82d8a41c0c0e001c030313500c4030031441c950b0103d50054084803403103e20b00065903010341e0510003c00c01103041d0b00b404010801c0d8200700300c81200c80c00c0c0140001d01e801510705000311102e1074100401c0d0b14000e59481042d0752441214045c08480d034517200703980c10b0b81c4180c810f05006415419012340c1d07144503803480c108030744000366036050320305411104540c89000d0782c40c0103003a0803d5410243d1942c82d210344004000010712b255242c1c1d10703007216100395080d00510f84a9083d031940341400085580b0041c040c80609011510703100400c0040b900001c5c043c4082e58290b504a41030300b80c888600d41044030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 98241438 1250 98240188 98240221
    0x3070906020c0307090f090f1110141c060b21090c031c050906071a0f06090601030507091d01081b060a030b01091a09120d0903030e031e03030703060b0708040e 70
    0x8c000b100f9655510b170512000540c5082411800c1d130380f1070304101d8213040490b9910000c898042000608000b000484913000c403401e801515400d80000b0314982e5100304503029404401d562500d0796426500210110001d501c25a003e421074002d40888505000000d840321820141e400c00e4013840c101080c161440751040d10901d440141030b4a90304d1020b0300301114105e511610142c07400010300001468814203640d024080d070700c040c1100758180c850b0310056026020051040041107001440007540d1010000b000f4408980e00c550310400d54140b02449003041d141350741c0c1c000d0103a21842c002006d52a00e03812180c044c0d85d9403074000781e0801c00000481d8005c01d07035400440c201503042e00020019200200a01c5141400c0307466011030300000345410780318800842da08010501200003000803a0003400d2540d0b000400405480b00e001e410b000404816020040c0000d490b4000310800205903003502c14840034102c040c80541c10f01ea4180d0f21003801d032044e4081e081030141c4520129100388803100824 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 98242688 1250 98241438 98241443
    0x31b0604291c1a0607080304150203070e030601050303070b011521020c2a1002010e07031a0c120712020c01050c1806040f14012303070906020c0307090f09 68
    0x5a407001000801c24842200700302411000b46800d4040d81000240b0349940c10510004d0462810600c2545540e0000d400c010b00640e900c00705c00e2034101e00d03842c4a100a61040d04a911801304004a503010b0500e0310f074050304003501940c01003100308003081040075090304444051420554840c2e040710105c40d45208404c40490f0780e44036030150907c00315284c000d05070f080511800c40300c0c282ea03818400d04000c1075040e01804143c1c4840800401e509102180c43c0c0d02d96081e00011641007080051540750030070725401650201051058004004500301c84140c02c9011500c4442c1048510201d9000000002d0700070000e0061000c5400208420354041d500c10300c040c40c00030081490100e00d1840d0030351042103204142440700d281c0c12500d01e05081600c081e510380742002c91105040660503620315100311101410321400e04801003540c016004404000d8601c0c03000c2c00d440c0e0520f4180a04800c1940d00054155040f521806101d92400103481c000c0303420810f404034100c0d00c01e00001c801444c081c2e001 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 98243938 1250 98242688 98242769
    0x150f0c07030216080a03080a0b010917030715020304030f0c030e0409020a0503060f060108070903030806040917030c04060f030605030a02090601180603050103140f0d110c09040f02031b0604 83
    0x80010f0f011802da0104c5e030003920ba9140c01c2c1d80302c0756088210f4000140d900d000c0303036080b8818040c1d180b510b803c610380080c050003200e203800f4550311078014550545680b440107580000412003011780c003000d6a0b180d24a941041ca0708840596006071100016441d624080c80d41c902c0680250750307440b001e00c8014500902540c1a909180262101c25a400c882040c0810000000301d0701843c031a581c40d00440707806568034030b0aa1220402c00024288203a400d443e87d108801c40300700101501401540650141c000480d660b61900402418206941980800741882e2400810407500c0114282440380e9044079110090740d190401a2403154100d21120218208840041840c1e50194042c0e81038074010300303c030740b142c0b508056800da40f902410140c101ca504030307907003410301c841c0a00413038541d0741504010344001600740300101d242114100c5041c0c03009102c4130b6001c01982000d1050a11110310488400c0c4142c040708041030640c4981d2007400015200104c0b0318401072441c0404043e03500d2080007 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 98245188 1250 98243938 98243983
    0x20f071403070b010807050d110a08030a05030106030606030b0d0b060d05100b0112050c0406080417030709090e0a03020d0e0103020d06140102120306030a02100e0a0303030e150f0c070302 82
    0x82503803600004000c0310705100c1e1800104544200282d86c0044801c0180088030180c407035580d00c506103074200d940c0380e00804a0328020402e02d0052024202c0740d40306a841030f440b5850208010142d40b41c5900c000c040c50b00d00304000b00075072508058850519000211128103403582004140060000301004d8071030700541c800e071f010300c0407580c001c0500c1c1c0200740c0c1c4620101201d8840001107540c103031100003a5190070801000114010070301e00f07910070300550480c01c00411141041d0311951040b02d0312000202c1104c0113020005251247c1c1e08040400700c007c02c02c0070010740c2c0c06551452035054130020302644c40101c8150360320a40496503244407018040c080c19550b05441101025402c00203400740c003800c400c0608400d889010349105400060040411040e981c003401680c01132007049804003c00442c144005485c0c10302014001d500c0b079500060030119500c662414902c0c0010115441c0311800705100c0c1044c440c07c609900540000412a603036003130ba1034241c0c9000100c002000c00c00d1501d00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 98246438 1250 98245188 98245223
    0x9060c03050d05090c0a0e060411120105010f020a05010c030203010e0c090a060e210a02150a0e060f0403081605010c090e060402030a0b0306040809030106060e060a201f0614090109020f07 82
    0x5223805208240c1c3d0600c40500fa0420300c41c2c135402036001102070144c603600104555880340303442d03000e00f40f0f40d4016901200d40035220741f82500d003001e04210119030000010424040c202e03d459510041c0082c50307904000b6580001600510302e071141c40104110780890b00c001e40d5904503404046203460098100072001e5500b025114800c621041c0e00c200386200600e03018194003811030700118410354030f0b9090596254100322854105068100d07140905000200000d1180c01c0241111707403d002600000c03440d00c3c90813500390b036180b0744400200304600c0403c04c62000c0d09131350560001e27812600035840381c1da50120400107003844007d1b180c0c50f10402c401d010901810070005c1c03181010a40084c80070940340c0c3c40680d090803070040ba10390091410003403060700601c1080c11050840081105e28000c050f0680c4882c60000c5c00034004645900500115004010511a22000300650507407503070804c000c0740c00140303444014414044e0385600000c04503e10b001640454420a600540b00c00081c580e01 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 98247688 1250 98246438 98246459
    0x807141209191415060d12020c1314090111090108041506060c0b010f060806040903020f01110901180e01061206050a091407140f0a02070b040b070309060c03050d05090c0a 75
    0x18941c2da015802401e10b41ca0607200c03160b000900c0b072007002e001c507406c044440c4d5a13032404582c8000c4050071402420340048030343d0345030390200c1d000d03d011620200781070181a4861040d00405009981382c2ea15050000746010130f220709880c6284001d09000da03540d07589081003800744406203404c5100301d02e03000010800980010b1152025030240c80c002c3c025a8131405150552506802800301141d080c900169a51405400c46036850744640b0581d004410804891400d6031aa4400080311100200d00c041c6103503800404800308420030354480884601e81500c074580b006040c040c1004002129000c0103261040d07410242c0141000750443c09816914450f850007000080c10130821440038a0110748500e12420f101c07102692203800091a000200c9002c0100e40d0142c0a41c1c001d502070740000060804d02040500b004015180320160b4a0080340ba000b4006a1180c002c2802d001e900010200401c0d4808151813090f807405c00c00050310b8071000307525403903d440401c480350f0040c007016022940b03d200 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 98248938 1250 98247688 98247713
    0x60c0102280315050f010302070b070819140708101a0403020a09020702090114040f050c0a020c01140703030903030b0316320d0602090d0c06080714120919 68
    0x790101c00380d8401d8000490983e55081c452041c000f0f45060203114501c2c0c06880604081e405040043c54414941e0381c5a01c8a40c3c00c035080c4000c2940c60080100d90880f10703042c41418142c2325070801010001c00300d06072207200f0203002c510400030854006041700c0d04451408010304650941c000340940034501c820004d034001c0c00128020050750304001402151070090701e1100703500900007803c3d41c0c245000d18030350010700012181e03c83d0b10342d44200d01c103030294030441d402013001c0c54100e0394034442000003900c4e04c542000c031941001603d01e0941d41221807802511b103080d07898a8045104407103400e08034080c11804441c10381c035014141680c4040a00381840308100c0c0d41e131128015640110003400c0c0604051200d040000124140c0d000903545041a50320342031034401d07030700142000803440108803151540c0c10b0803604088024414014581c001204a0b800708480c5440704400b4001594641980140e5016000c0e00903020b021031aa6042440341910b18025104070011980080c03d120402905 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 98250188 1250 98248938 98248987
    0x8030f09070e0103080a120b040906090b13020d0f0c090c0809071403032a0102030103032102030112020405060d1b031506050303040b0a0c0606031103010509010c1b02060c0102 77
    0x41e05000a04080418000ba04881e00040c1040c1000c29040083c0d559010404004608980c2d41a00800702d0782c1c0d070700c04c2e00c1c40103010381000591544a841c02d580000005040222280d480201c2400147d8455801c16040c1754000303001d03036100c05149031031110342a00b074000e0350900e82481e8100c480d1036400500c0901c40c84440040302c2403250f071000707a41c66980b03107501079a806400030400038141e0a01180c50390403108848400c000000c42c0201904d08a803c203030400c40002c4c640001741001a20103603031150300c00d60b40c04011483c2d035140024250345040082c00c000e02540e141c41c0010604c1e540c48101182c42d50300504840427418032694610b40340c403090f000840b0080409140310f90503800b14032545082e910060b00440c501414100d071107032540c0089d039645041055145030100001c5844c042d11000714810030990303030894207603401c01d42510401411100a03a2400e925050060340c45400136414042060411841d50454004505284201707846105c8541c00010404903100034618080351208 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 98251438 1250 98250188 98250193
    0x10f02071109010807061404090f02070212060f040303090515010602060711120702040e031b0109030f02010203150f01050721020f07080604150f0c0207210b0408030c0708030f09 78
    0x200707400801002600c00e020b100001e912940d0140400303401040c15030002c100c04480c07142480c1d540e90b00c03101030303d0b1806407607a11103802084403400c50504080d1101c10600c100c0240c003151403c0002400b01c4c10004001404040c1c0703d400d0401480010301041c5048a00c02ca80c050b801d603101d820195a50344161545400166907020007060030901285200602038086842864480c042d02000007600c42d01003032440a0100300643e58040598010030f07080300190100103c1d952a46060240c100c0c0b4241c0450303010359004101300320b907100204034003802d1350000b1141c0480d403240203401200e09024501e0300500ca20405100004550f0070008614508c4960b0f500f00e611303a21485540c1074481d241031050105651000001c14000b81c40148800380d051412a80007803d000000040300a6811055030140540c0004000740900e003c3e2007142e82e0070f0107d054014600b0340b55952020b0350280020720180c140240030000c60a001c2c489001c54000b01c0d08501c03415102e08110300e803060182e00940e600e22051 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 98252688 1250 98251438 98251463
    0xc130f1505010e03010207051002030405190b060112060501020607110106180203010e090a0f030806040b13051b03011a0c031224030c0a090b0102150118050a021905071103010f0207 79
    0x281360500843c1e04056000019181040070300b1001006500060b10440f014055403124614820640b03201c0301503640181c41800050500000140081c01080c40390075809040c5172090000b81d80000c0d9040e0054a646042812600c265000500504c5a40c1080c4004007070303002111070321061500034505940c0320100142e06a100c0034101c0c1d50b00d0415a00c01440c075403041d0744e9400801c0c01402a96030102000d0301c080342d030884100002d861051880c2c0c0c2e03040e0030760f074078818450b90581038002d00040400301d044880c55541845d03a03402645096000e2840c4d01c0d18006000311440304281705960307440c560341c40c0c06016410195203c0841c111140780343c642c0c040780005060842d1074001030403166404040d0030700d64141d0070f140d00007014100b51031000d419841180b1041d821168084003184c020505240300140080301d0601c408180c2e04040c3c490080c986c010312609181a40d912074404c03840c1143d0400c10340c0d13000185010300059a00c3c080055044d440d041055103225516001402018881c101c103140f103 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 98253938 1250 98252688 98252717
    0xc0a0b0114041d06060108091203130302060603060106055508010b090607021c0302030d110f19020f0109050313060c0b04060c05090a080106150801080c130f150501 72
    0x1030000d148a80c0d03d0781e009101099255000f0b503441900510701c001950340040300c880950f01c0560041d0745e5184c022041d03600d03032002d259052086a40000c0120050166549840750050541c040c800682507115100700c007401d00070011440c03441d01020032041c40c0c0b000100300209004030346903404500b50040200c42c00c0340760061140e41d440e416589040e8441d410500501c1c244251600301560498010034a290141c000e404607803881d1110ad4420b038002c5a0b18aa01c4410303e06882c035402182d1503801c1c00f408050401100a81502c0c03a40c526542d80088090200f50224540960300705c0720301c0c0319441c207841d0b101407040c048010320503456010301c803004c034075900c91741111090f0b01c108019103100b0114011a0010340950404503440c9010300e4103504050044000690b03c0900380c1c880d40540e0f48d212420011005c68502c00d00700030146082c80c010a62401d20142c0d00d41c80018445880b4a164818040e0302a03415440301c01481800182004417410144002c981001c045c024140401c00f446002d501 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 98255188 1250 98253938 98253971
    0x105070503091c030908031f090606020c0402180d0c030b0114030a0213110d020d0b04050402011b0807080a05120108030a0212090a03060c0504090c03020a0e060c0a0b011404 76
    0x641d000d6070043c644039018514810441c861640280105a00c850001c0c0c08210030302c019500a944400c15000c401d00c200060140b080d0b01c0b6403000040b58140202044203603004a945014610280e502603a1030070344100140035107007209030484e40a1900b8134020305000c0c908805c4000e8030300c18200558245d888081101c0c11412401c4020303031643c03014510380014101044c903688000c442d0382010800310f2400d5600030a6410034086c01c42d01e240d011078054041031190199959440003558204001d00305034000034020508030003074605e031240006100042022041c110790402e078005268507118803070110000c015070f0001c96000000d50031500007241569021086414400603a0020640300001d0082031080f038100e4030300160f1165150f84000701040d941c1c007407071000305010fa03503455546007400b0150048910b10001c40040520620890003030b2904a8601c00c1000c1d81200d80300d0b2502c00c4520400c0c0b410007907075001051808008000101718405034102a5140003c880c02d000c401e00c5600c2042 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 98256438 1250 98255188 98255191
    0x60f06040605180d0221100507050c1009020d120e090a02030402010f170714090406090203090706090e0105010c02030a0203010f051501020105040b0105040e07030503160c0803090a0905060a080601030c03050105070503 95
    0x21b600800742e1030300a950b00042d40c80303131105110700c400343d820080c480541c036421100120340110100343c0000d8a040c0200e018091a40e1059900608000c1e650305034021a60813510307554020403000d500c1003510b00c03041c0100c14900130400002d00d105190f2500d000540041c1d0025102240401d081c0e000c6091120b00503500524403855030f683c404043d0f6108803040b540816044104a4185400c2000c2c41061b01c0340e0103000b010b0701d0300e901d01503528141002014508412640704c0b00400c01018002d00600d40000d43c005d04588003482c004060008600009081190515000307615610f4007502c55501089a00401e1040d100d0f16401d1201c0501d00005900780c0d10308440041400400300014005c6243c143d0056200781001c2044070341c1c460b160703941c051541e44110088000c0040d060303003050400c0f8030084004003900705040511b0030001050046610880140111450a900c420004260383c0303441180c04014494541100e800d0350392401d140c2d074203400600007640c0307a5080c2000140414010811203 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 98257688 1250 98256438 98256443
    0x51023010c02010302090a050d08191103040303180e10050102071d0a050c0408060f16050f090d0204020c0d20010203040b0103122d09050909030f03060f06040605180d 73
    0x1d400c2401c1d0b070b004500960280501c07035442210351402040d81c2d29240480100d25102d00d07a1a940c0d00c04581c00a400e8404e9030f090802000880441075043c3c1c80c0c080281c404683d45030505680c05101041003000390f00b0f007a00252158417480b0b003040344000301c411182003101c0e020380aa62034030351180201903058509095004d8004901000705517581d4240d80540c1d480604460b42ca81410380b03071503c043c1840e0301039030142c00d855131500a110003007080301000c0c01c01c070000d401c1c09803030206241180000790142225035480340306a142c3da0019522a5011541030410b450180c03580041c0b50a40034003501c0300c131009221428000f0f5003182d45100b05201700da0080f82c20040342c08490b86550b071030a0a41000707411290070424152541c582e00d1007201038203a40c0401035030f000d8214071030603100103180054581c0040e2007542c4407000e007c0705076008030441d91a10300000c0303255a41d5072404085101d0500c00b15040b50800c0d4001400210207502c00c000d80420701010002c0c404107a8050100407041c481c40402 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 98258938 1250 98257688 98257697
    0xa1208070512090114040b0a060503060f0412030e01020415090e04080712021c030605090709030c0513020708030f0f0c07030e0405070e0406141003050f012705102301 73
    0x84503482c4184095150320081940000c10100c550443c4410003000a4504881c030b140e013401441031066a0307000e158080e000c15070003411586003d086030b440001000e0800b6245d8100c01d41c003240141d110707400408926074414025580d5a541e420801c591707110a505d0030001601d240000f0620a01029207140601c0c1c00c1170401e4205003841c1c503884e1010207000c030f00754150301c101454440003c0386024000704164480c1c0300000d41c1444c09017400040e0300024000b200b081442402800018803036508441550300a0340e0742540d00380c0340b0340c401d4024861014098245c1c08044104142042a652581d10540501c1c40c24001d0f0340302d44100c0c40c0350b40548071005000c00c0c03844e00c0101590800340d00c1198000140d1401c3c04800301c0300d40101e01265029002001c02415a00c100e240d82e0034007041c08584c590103407404100c545030012140042d0070040c0107400c40751007900340c0e03280ca503108041d180c81d240c2c80181082106041500c240c03080c4e0141481004502c0307d06030400b01c3d940040040d4202c6095042e1507 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 98260188 1250 98258938 98258947
    0x6070207080a0c090b1c052a0306070f05040305010603080c010b060705030a03020d02070f050604060c020705090c090d08030a06030309050111190507080f0a0203060907050a15050d09050a12080705 86
    0x1c44c28003a22011050741d802030380720105405410100008402d405003e1800390982581407888211081c0710045200814000100850754986002030542da000d450707858003180e0080c5003841201c86105640c0054290760806c1d070040180141d0b0001010722014020080240c0810702c000c2c040039004100303014015420074003947d4541402a0020a03007480300c2480140b501030366a44900c2c01256880e029104c41e480907040004100c21445043c0f40c030003103800105001483d080c0000d00302c0d40010800c0b0402c0720040b560055945824a031031024507031180c0d000c0c0d04c03480d00c4200f0a0041440e40b005400180a0180000303155010340611145d4104010150211036184d50b9810b000f41c041d51000c030391920810b00001074014003440021164800c60000d4071486860340101031800303001030701070840c2c0d4004050410036642c891041004580503603507091070400d2203400039641400b600b4121313440702d0b0800351490300b0030401052410358903100320704035548001d65800032620034000f247d0f0f902c0450002c00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 98261438 1250 98260188 98260199
    0x512030a05090a050d03080915060604060e040216030807022e0b0120071d010e040219030605040b040b0709060824030d030b0a090509030307051b070806070207080a0c 73
    0x700402d61142d0103001c003114581d8843c00f0460303217200c0c80820350000e0005001c0c01241c40003400006840c10070503200c46028200400000d5140c41903100391028040904004540740d29150140c0b0b032040c2031101c00c0040c01169003405866040200c4a44005004020802034400b40c25035030800d060380c2030007040710b44400050400c8000d10f817650312203050144040c8540c106400c10880f82e11125240390140005c10324114603c0b00b407a480c031a8403050001c0d0040140015010041d195600c281c0488180403841d00c800c1888124500c1c581000c2c0403681000b0400003400ba40901050080d403183d20b40b1160780c1d442c240111003443e16402580c0010340d050002c235202c2c0225901e55225039107184241c1078403071a0540000c0c80e1641111011001c030361500080d00c800d180100c0e0740e00041c45941d405021520b00722515070b80303c1c0301c0100a00c042c1b1101040091074010883c40c1c0c500c2c050341081c21505819292110030f40d60f15030440c0d8000c018420703000041102c0001080c817440290344511501ea1050500 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 98262688 1250 98261438 98261447
    0xf010e10150210050114131103040f1e030905090604051e0601090807120210050a090915090903030f0c0c0510020c0f0a030309110d03080a090303020c0a06020c070512030a 75
    0x2580c070700440c8035240b0645041c0c0c50380e210fa58000c010b40c52400b81110402010320070808000c4025490141c905a600030180d20a50101c80c3c0c816030040c83c0d001c02c9106890064000320008010b4004601c420604030100354008400100f6202c00301c031603055595941d03042000b170340c40c222120000200003402000110900c10803082e04450f0504207402c449403100d010030300e04440c1e40e1040e204019a0542e031015803c1980c01d0b00044802c0380b80451800004080c003070140c0070980b00d04040d040d55007000c0039a8075640a00e00300580300c0094140300030f955504004000d41100640803500a1411080c1c001560060290034906603014015019a0b0103c096401c001d400024511026000d030051103500c0e2903023805041c4034140720b6100007400d800c5500341007508209104c0d03924091402c1e60789000c0400d0f0000a0790f58420041500462890342ca403030101d0103405601c42d0182c1900c282581ca008200494029044000d403542c107c50207a030b910000c110303510155101400032600708010049489128 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 98263938 1250 98262688 98262719
    0x30c02030c1c0c050a0b0f0a051204030203031806160305040804050a03030c0302060f060105030c090a03080d1e110322020303030f04151505010c05010b060c060f010e10 74
    0x4054405960074400440c091910422503000c05082c80a1407000300910740c01c298000d400d045d07404e400e100d410224585802d12030b00d0101d080302100494404040340c17003001114000079082e070a52a09003401c0c600039581e500151141c4000007401a403070050418005081841200d810050b140d0a0460301e4064000708070250041e10400402c200c04a001c0e210600c046004601c40d9540c001d401c403031403e0017070400c075015011015a9806109000a40c0c1c2e010003030b60741100c09145199603400d40d600018410f0209640f00801120002c69002d042c1c04032513000c2102511115410794000251041900446000c01c81400041d401880403c001e01564121040c0034000d4440b41c60344d480382500020301e5038000320344401d6800054020032041201b4407441e0070102c42d201000307001040d060907522054000d00e014580c1000728840d590b8041c000c0c25080882407d0700501031036912045160f815031162812284514040c01e5032b000050315154200c000381c1b15420f0001d50b11540d90500c40d030801c45210 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 98265188 1250 98263938 98263943
    0xa09150b01090b070c0e0f010609030b190c09050103140108060a02030c0412080306040f0b030a12090b270d080301140a0e090a06110f0403060507051b070801050a0e0a030c 75
    0x200e018003c01e041200d04024002240102400010146008007480d046c182c01001c0300c0f610205100100844c54100714a01d040d603505c1140c3c2041a074424241c8202c001d2401d0740d8078001818000c0014915801152080c1036074000c2c2e8040c45500300154038040c24940a2048030101ea0000b0005441a840c80c0d0295400010fa0702d0064605036a88000309818081c08005031065100042800b540e07150038441d046407410511028462a041e0000007600e4041680002d030120a001081c2d24899200740400405414442e8100d070303c0314462007404a808081f565442c84e502100c41045140c0d24040d0010716489038000c01242c5180c2c00c162401802200e0b00034070541201e1402008650395240c065401d111b586040c0003060b40c00e08a08045003074a4803006600c40407801000a00a420324100403202a207400c4103000c5990b85a40c00200c034544621101c090300d0f4a59a50500e01c079680100314801141c1c0d00c400240301a45031501d84200b00d031100d000c0b0b4000342d8014512100024014481ca503607407030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 98266438 1250 98265188 98265197
    0x1e08060f040908030702010209010305010e0411100905030f030904060e010b0a030b030c0604060c0515090a080c0c0d1a0108070b16061d0307060614032a060d0509060a09150b01 77
    0x29665554010a410548030708006d80d4001c10850036650b4540302d100d00421301c035601e0a07074608160300c40f070081a000350101802225a01c00d40d00807240a51015001818050100d980103a09552001c0e140d40103580805d120310300380700002400f110032884c110b06a54482411a141880429040c0c009000c80341300c2a8040c06a02d000311499561303140540024000d40c0c40e44c1601041d1172510a040801d1040c4880b4281066410f0100350400002ca0b02e03100e03a806040c4039030fa16060040e80f0b1901c81140300f0660722807003030400034042003070003840701c0c0c0055002410015241d80f10b85080f41c1701c2c2881e001d02003290505008003200304070b006900340c0b60030780290340c0010a500702c10340300700c14615915103010241d807000814008000952044100612701d51080503800b0344030b800002e89401d121400f00c589042d40140649101d10500c101980c01c040080c5041c0c0d40340403290020380905000c48068060303006040000e12240594041c52081d154420b10035000207485480c034070024004a0b030000e0401 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 98267688 1250 98266438 98266451
    0x40303060801143301050c1905010b120712081c05070e01021b0a12031b0c05040b01020a12050f04030507090b040b0d210c0219061e08060f04 62
    0x251000c1c03042c01e6003041d81410366000c81c94158084040918000b1040110b000d00c1a03c2031380e4903d00043c1808040003d20f841075481c00300c101030600d04050104c0c0c82114840d100000020880305500c10034140c00161b501480c03240c0185195500c4021620a2180000610b0810000136114000804088420225003a40c00f498400200c0407a00200c40c041c002c5014800c20b4041980c042000b01030081d51012000c058405000102d80d000000b44100b000da001400d03d031204160081c240b20207000d103081581d426045079418a14980b01c41c92240744d025a00d40143d40685500c00315131074084a030000d01c40407001c035030003004889540c0150702e2071001e168244004400501c05001c0200102039000003c02d44080e00d2040008907001c180b0307418424041c17150f9244c0003130342410202e1520199070180c02d03881e200400060302d80300e0300140005d40c4104e00701165085100112680001c4d650569192000ea8a503c41110b04100c040709509021030720460019949190030400504008409000800c01 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 98268938 1250 98267688 98267699
    0x606051207050402070609061e051005011b0309120f0210030e0303130c0810020c06180a08070507180212010602010b1305100f1d0709140405070e090114090c070507050904030306 78
    0x101c27041e0203042d1410009603104100c2800071780c000c00e604040c41a07520b9940c10b01d8040060425407880048480c40d008245103141030600426450000304000191294102040d2401c0d031142168040c040340302c2e248805c03c4984461080c80791952590004004619544a211000c0390060500c1002c17500d2400040300820389400502150720240014613002d62600d840205960514100902c0440490302c0e101c100b03060702800040101e03507a504121225590351a030b0504034200192900210040740f4444070f21400034195034004c040728074250903046e41603604c1e11000c90a9485507001c0a0b8004400490041c0c0d4094a602c26034100031050501541c850b500e001200d0b088e8040d0f030089501d03ea40340b5901c000348404000955004040b450451300f4030742001c0c4000d03003020f0b001e0112402940d80300c0c00985440d01070002800c8100008090700219a503891102e2000b40c04451028058100b074408590300b02c411601f9510002d5000c0c012309406400e1078188881c402e4000d10940c01c050f00c80b140001d4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 98270188 1250 98268938 98268941
    0xa0c060f020409020d1a01050702010807020309040c0f1d060405060c010b1906020d02150109022208010507030f0203061c05190303050714070c060806240304060605120705040207060906 81
    0x1483c030b0900c003684070381ca0610510203c0f43c001400040403090042ca12005aa00004940b20f8030350900305203e881c0c440c000101c1c0b45000da0060350703405c41e107002c0010031b115802c158000c020400a66980c9102d070044480c98042e039204421094000c10b042c0400e01c000d01d0a0380281034190360190000441804200014602c1740c0c2c0b0b8010020203a071100720501c100d650501030031005203400e0000b807145000c0030041445407a014491110b00340d80c0442c00940d54001c02c0c208104540160391410354503901c800380e45009107030a072414808281f805c078030200c81d20281d0080d80d21610f0014082d08048120045040c8942c1d038642c411a414080d08500e1a4004906819842c066002c0c1e600020340c1c2c50502d20281103440c42d44007011541c01e042c020100043c200112620a4440d41d02e4546496110f130404959500702d00140d00ca107580401c41c140350500c9041c4041c0d44524029a014401d584d614410301918102e00c141084150300284020300a6003499001004003511480c400941c3c0055929001c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 98271438 1250 98270188 98270197
    0x1805010e0d0b01120b07080705030402060d09021f110a020607021002120d090c050607050303041b0b0406080910020909070305040312020a171819020307090213030c060804080a0c060f02 81
    0x10342d1019040c4c2e88060008546191394441a6421302200b1810502e40181007408020f000a1103080002051140b0380580d81003003144a9010f0000c9200e00d003c030650025401950103100c000503140307240c84d074425030006414400603030090728a0b07151002d81c7e0240112803261201400070340c400c11000c3e84c04048660300030601c6220950b0700041c8810249031194140720170b07600c014030a007018000200031510110031230390050791280c0040f103500802605500040501d6002c903c00e0f507008034000803503680102106104007040020b80b0300d036625110070380040780a00d1207903540140441e00001c00ca80d010350301c9107030090700904001d0440c1f00d5408070401682d01071000c204c000703000a481c4500401c0103031090741e000003c2401906585c0d102d0700c1259920b20444010050710368000c0100300640d02d042c0071180c042c142d02201550340d810510301032003070320001d44412144429240c0c000124284660080c6010301c1c0c1c40740744645800d5a02c107080f00d01e4004018151201903031a6108441841c6a10060 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 98272688 1250 98271438 98271449
    0x60b040b0a0305010501081b090d080c070303021203072313031505130b0a18050601030605040b070201060602030f21090106140a08100507020a05060c0310061805010e0d0b01 76
    0xd40c0d07108045002000c1c0c0300103902c101d041c030041000340308007000d19003901c1c1140c00c100c1040b0f640750103035040041c100560b20540038004120004540101d80e0010400805480c025001c403151b200ca212900c0c0b46510003114510001440d10080040c00b500300040b01d20780d0709200c14400c3c14090804004a84942c140d40100c41940b11500d0004080030f0342c0c05040d9000f004009070350340101c450f403a11580c1c844024904034a080d03685081c05400c03001b031510251895005000c95900390b0716850310f00010103050fa4165001206000000c42c0503105000301403d550660340514100743c00011007907959000540301c960001c1060089400c500c0314020350610030303030081d4000725045181c120410500e440ba10059070007110b5002040c80150000920000c1e407441580000030103130b4614808070304100c40c0c1c0000401d41e004810601050324080e801450054134581c0588080e15901c40082e62842100a20140c215605401c10800f560185060700c003c254003501d0a11558660395a8403d10b0009800c003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 98273938 1250 98272688 98272709
    0xa020f070e04060b010c150c03020d020d06030b0f091b13020a0e012703120c05031908070905030a11120d020a12020a0c09110702060f0a020d1d01030f060b04 69
    0x81006001480c021103a08031002c6c00d080200205e2034031040010301c0c114842c0c1080300d1300c81070346c0086035101c0c0d030403900c0800300c141046495404110401018100511060ba12a1014404515400100c2c00054000e8002d0303002000d08440c034580e03412403420300c905038640c270641e404e00d0890100e481d800101640c00c00703030307490350100c480d100005400e510000101c80d01e040300750071820341904901c601038002c0e01d4020180c403c1540d0400340c2118050703d103540017403041c000440d100301071070348a504551407511107440310f041d00d5a0ba180101c841c50014170900f945584240b07034005c007040341900a090112405050714401c0d00320002580d140142d010b0607a80180d102c0e00603882440f140b02c400e080e00c2070701c51025203400000d0392250007800340d85000780310026641d1030340c5141000c1001d04441c0c1c41341d030250141da150040c000e240103280e000840040c2c094029511b0b82e8008074880c88031a48864500d1000b00c003100c17110341c0110700a100340d603d1212210fa9884000c0780c0c0300c000e0b101034002095000388 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 98275188 1250 98273938 98273941
    0x901020d020c101b0602040602070e010504020f0319110301140a09060305070510020106030501180614040b13020406030b01080616090b0301051e09040c05100503040f03050a020f070e 80
    0x91400340081203220454102150200941e942e12069800c4a12a0b2420307034600180310000e28000c0c905104014152840003e00250454010400d0320032610354101c0b04d42c0a0ba640c100b03000580c45030300c0805e04d2804007040060009240d24030010522440c9910010321584041c0140105500c203811460a20181e0f400006d0603150a010b2070021703002540b000d0065070b245507542991140c8a003c0d89100369840120400c60500c01d500c400b00850300440203000004032146140d4034500340c4e00041c1c81c5542441840207401d169004014095584048041c0e61607448900b840308240c4030f031702d080342e0051700d580300000440c15164605020344034150140403d814001669107800303010140350700900041d84001c22040c5000000d50381140d106443c400d008130500d001d0f0080030212842e00d039900003004000d00041c40882c03510003060f12000c0c1ca62808100c0440010380c2c0c0b601007200c00510004000c540840080d1003070015103d0010140112149000b40c000c00d1410040700350082c00c1c8050702c0c83d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 98276438 1250 98275188 98275207
    0xf0706060f080c0409151e020406031b1106040201050a0e04050a0f140106090b0a05040305010e060405070506120a2705010b04140c070308100504091b0506040e150301140c 75
    0x8a42c0350303075408030380411045c2440ea9980c404040381c8030300290300554900c1b0100f910560311400f6420014602411907980d83c6a150280060000c84140c81901c400c07118660f50090141c0c94000190065074001c140c540e445074011034a951050003c5030030007612500201c4542c91702d00485024024030030012640c5081d0200c48030465000d0800400741c039443c030004001b121380250b51001902d1450351040d580340940b07041603510f446180d200602d150320701a000c03004c500d004243e050080703101d0302c282d4603495521801c0109174000c868030054002c8200001c03030740c40c03840c5030b0041004203902d0295040007040c804082030388480c0b280c01035070180d4480c0e102075050b14052080c0703a81803c507007060408a0a00004180b454082c0c5030004040c8400d030808140340070b034032a03600c10061070010030500001a9620f4002081c004102d0751030f8003820781881c081002d240400603141518000341c42c901c01c030355804039844800c410a8038129055540e502101704403200c2d8200542c4510b0300e1120059a4a0361765 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 98277688 1250 98276438 98276443
    0x60a0c05130602060f250c02030a02061204020f03031c021c240e01030c03060915110702010305090c1c0809030a140c0f010210020903010b0613030b07020c01090b0f0706060f08 77
    0x4040c01b0800e0307550f400c00d94000d402140814000704183c984040302c9203461002c2071800e00226006540040081400612041c41244007031085209580c0c91142c5082034003416602d01030034140e90280000380c500142180c1095005c0c12841c100c0322090a581c080601041089038080d40c4e038049901100800c07072081c085010600c80050400c506081800e6245454107660408a400000c00c00394450041d41c080c4070719441c0d800e031a0421b0302004c100c0090705405000c3d85a20148007240800e080c800050700c0382c0001700340d00300303000300c00b030100011401c1c6500c1d0038620010340b00c002c07910064240715094068404000d4550014425924840944200f1136404c0c9410801c0c000d00307108175072007000b4080c540d0b80490702c100f03070105840001d40c0b40e0041c1400030f03015010075600c803508150049800000107100e03100c0d83c070403203001d8140c0c0c0302c45480e0380000301e0700e4450b410105404641c81d04000c0100e00e04a00040100a010807081c509000c0d0a0384d4007019214a6400151005040c0340c080c440507406 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 98278938 1250 98277688 98277691
    0x7050406110a050606010f1e030209030d1d01050702010203040305030a0201020315040b01120b0307050607080a090f08030f03071209140c060a0c02060901030605030d0c03030b010503060102060a0c05130602060f 92
    0x5440080030607981d150f46059481100074601350410130504041c140300c07809200f101007012450780c2c101c0b0740c203000190002c0094000d02003040c401c1c41003104505219001710854101c2c03008192540b00419151401514954400d00040341184801c0000002180081c8007038400720600e580056034904101001c0403401d41162079240c4245c1c60111154484c0ea0003422525025103d030b400400d0751005003000030704000304c5500070b517048480003840c40c0c00c00a02d0001440840400e84a185aa41e224010040c0040c510b0161545a60003000384028196003500a943e1000041c5030100d00c0c40700c0c11800005031481954125a000d510f020511807128040c0114400c00406980c400c0c20048030b100000c024110120000c0e000d60701c000f6488a45034840c3d0402c1c400740c07901408460b11b0b148c0341c82004245081d00b503010340000e840e0801200303040d8444c03006c4130b00a0f60b0503401400541c0300c4690800050092801e10f4040c40f20030040070203102c1d520440030000741150b030040c22980c030b0241011440d4500 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 98280188 1250 98278938 98278967
    0x11203260604050403050d0204030f0218040c030624030f060c18060c080d11031806130201050c0106051003060e0901050106050f071b0f060e01080709050d0f020907050406 75
    0x444695804005000d005001d074480c0048602040c240c41310304007921207100e08031a5108181c0000740100900211403040e8140d24420364544c003d5603040031080d00854000c0e01e0080508540410400118155401105142d215500007401007110400d0881400c5007030340c0100c3e41c0120403108401801001c0c414040340b146641031010b4400c05404010012102501a62090100d60b0826a00b40410001030350243c212400c41001309503410b034810b80b1140c00071030315520050580c1e021b1184045002c1a0503004481c0d21110158500e800c4d401950650890003281e03095660310070002a6640d40c140042c0b40140384c07510001142410001c040300c00207401492543e0a81c1448010446650301008948002000c0c148080d00c94407540b40c1030840520035601149034144403d80425034842c440c02c0001213402d907031036264035109810700548000e14229036003004642c481c5000c00450409200b5040558840c16200d0040340031a0f00042a2240075227041d40010000f14081c491982c219140700000300 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 98281438 1250 98280188 98280227
    0x102060702071509030b0903031b0a050f0304050f0a0b060f090c0412081b03040f12020a0306050709120c0f2106110c1e0601050604050a090b0f0306011203 68
    0x50a040c0195440425115024541900c0c180a060451052152101070340e0b00c010f101a007420140c0410340d4940080d0307200d420040074035a503a0180200b101c2107510800b00b6455103410300411144003961600024815500c81c010001902d24443d0280300d00c0751428403032211051542031182c00e00c140c10040500c1e107401008080144502400c0c3c40058070202e6420400c032202980491800080a0027410060703050800c00341c06000e0300c0031011010700306580da41c40c0c1003034429030313180c0e60021031032212000079400c0130780d541041c030100d078440d0403150744031000e410420581e41e030300c8010880101514200b541c2c203c0c01e0b07a005008400c010700c2c041e401040c03aa84014007203846010901c20100041c0700080c0003c0e0f8980c0f20846240d882001c3d40c01900c5070000b07036608424003030718034610300c200504040a5401030b2000810940740260945c5c041d0781c00613183c15001410015440020100c1a00c00b90b40050380c03120554890750200211400f070045142c800310381e81d81c0c5140c094101060100e0700b10819 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 98282688 1250 98281438 98281441
    0x91e03030504260301030b060301060509010e040b07090b031501031e0b18090303070507060b090103140114070c06050603070e0103050f12031e13050d171f150509100e03010b010206 79
    0x1050036404d5a041d2900441d911185494200002e401424558081c0e60000102c00000480010f0030407114480c070b004500101c602d9882c01001ca0b960f43c07150150100d00c034400d02c0402c202c0030200c20314610030141070400086c084210000c17120208040031080c1e0440b91141d00402c01c40c240b004102481c12405600c002c03103801d0110000e612030100904070310400c140801c040d000d101141c0c10035858424050100c404650310307404c10004002003541134034040d40c00d1006241e0202011408503100d40c0840c0e6502006400e199500c0026150142c40c003030f4184075189006c94205004040c00380294401e2000381300892401012a04198010620514458040c02000003c032044101d4a41150001d20085100d41e942c06203040d01c640d143c0c10240851143d00c01c801211a0040c00000340408000d0312420182d441c498101d2441c02448002c801050304d2050410241d2000e80d400d083c0c2039001e007049410404420007240c02d0519840e14100007a010081c3d160b6941000e114881d20120300b071000d000d05 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 98283938 1250 98282688 98282753
    0x110106080604080d09020a031101110a0c1e08010c030207031101051306020309010f050a02030601020f0708120306060d020a0504030b0a051312020a1a061503070909091e03030504 78
    0x44410007007003d000000e000551041d404078650280f4221030b070090040c500310307403a420500d078541d10540105001c91800b00680c0c40c10200050700c059129408000c10f59880d003011300d4820074007808a040000c403501c00a010801e00d07420b00600c1c102e08140e6800584920950900801040b0140d1031041c49074501000c2c4420900c440c403540d03071000d8210340050b0356502c403110014010407040c074852800303502d4641481880102900110700401c0c1c26802c03541201c0004101c65101c0803e0f01c920b5003c8d40c4060b084803042d806410141d030f40300030010182e030705001c2000024000e90f4404480f0500084000400b4800c0104e141c0703c2541221548401300218075007551449088444a50b01030500d000d94030450303110034401c00240f2030803544290701c80007481c044800c8540306a420303034010381f2490441c1d40b0380d003c010300001502c2c403070503850b6164614a07290840b420010601842d0070b075181060902d035441e001d50b500d03400c00e81003407096600040528046c00c0465040080c3c60143e030800000301065042d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 98285188 1250 98283938 98283943
    0xd021210110c0703080f0c01050f01080c06040e0f0a0b030706120f0902100c0203071d0402090601050304020108071b0210050a140c031c022104030f0302070209010303050d060305030c010204030311010608 89
    0x40e00e40c0710542965425801c4001c034805d0168405542c10748d0700b03000400915130075464500d03040702d0b80c0c3e41c1207170903403e480c800304078060145014045010039980b000984d40e641c1c6e0755000d60456003401000801050074400300341000110b81141010500803110741c42d802ca05482800380b02181c1840820500e002640000c0c4505074118100d01009003c2c1034007019503605001c00401052101d1610b1441c01c941111080c402c402210300307922581c410400251294040c6045a1080368140d50303604007981da250003a1017502d80b0ba0072201e0003002c0402590010f0315003a0182500340902e0301d42503220108240000c0c60390644800f02c00c0c0012040c0100b14a01f03100000b42c40360340411a02c0c0c0390107840d0740c00b100c1c0001c1c0125584450360300301078950202c0007040315215600450180d0744981030484000d2040d42030344200c2800940001d800401000400c2c40740001d007031b00d40c105940c08526250b803600e40b60701e140c00c8000c1003a5583d600080400c10940c12008204010220000a1040700e10303000c0b07030301c0c6c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 98286438 1250 98285188 98285203
    0xb1903060e071d130e060c0a140f07020411090405060a0315020901030905011a030618070e04030c0b0a1b0c0c060f091a030106030f0b0a03020105090d021210110c 71
    0x10284641e80e48103030a5141c2040303c0718502c58002c0c11860865140160300009090081d100030700e1402180b020078100b0900c8400c0700c80d6403842ea02d0769240d800451480c290f1591110400b249142800d02c0030000503034542c010149412084840e968490b0003003401c0000312140540520300c1600002c20800c0000d28042d00183c1c0070b400c0c4600141c039000b480300140d01806001d84010a55440e01c0855400324a2036400710789012825000c4910b40e980b40c2416800e4940c000c041c0e5402548112409c0008540e4651740c140d00a200c1c1c501012000500d90b10700c0c05003074041d10964086601c0c0c03561b0702a1801c030b54440d4035000c10b0500c0c01c810021815114010801c409004403420010f1484007504c13514002c000038002804051a1440000e40301c10242400360020300501e00003d0a000d600c6595901c0341c0500412900b000781441c2e8000e00d10740c01543d10760301070082150041d00940c0f1850142e0f0382c4c00110444c60307080a01411a60500f02c080d40101e40701c0450000c2c4a00091016409481d0005083d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 98287688 1250 98286438 98286451
    0x18020a1212080a060e090f0705010906270314060601020c04020a0c020f0d02030604030905010e0a0b19030f02070302030304110306040c0e0a090c060e01030609180b0a0b06040b1903060e 81
    0x2c0340241c4411203e40060b11442e00003407803030f09400c3c003417180007900001c502450050304015250315030b40b24401118070280c1c52080e9000102e8080807075005010400000d150441d41c1e1030450562a941d03a942402e40c101800f0801042d0000f604200700c951301484040341c1c190007220114607100040300041d005140d00c3c00041c0c068a0060120219516504404e0b040107070018100d404521341482c1c001c1030020180542400180301040e01002d0341417048040e411385071140011818401d00304407403000350116072460806c16403104001185071420344000c000b0540203902440d520b01c0c0a0400c1400007000804c0d4034000d901040811020980240e81601540c880c200308204540f0740b480c1c500064089004064040c0044031400a29290801d0144684100a880a002c06640e6000d40c0c03040780c0c408550f9030402c8031000490000280355132038155001d180b5560000755500007030f011840030b8100d600001c4501380c001514403456500e441c2c2804152103140f6040c4000e078104144a110740c2d01c09800f4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 98288938 1250 98287688 98287697
    0x40f0311030c0612100602160b0310090c0309110909030301060516020a120209061516020301021e09010908010c050901050706020c011e06080c091302011218020a1212 73
    0x1a40035550742846400ba209400a00881e10703900828442c0300d021609032013040c110040300c4800281240046980f60079400c06000076820f076460003880783c8940e48000d1640701000700e59880484c03407903d144035403802c60041c2e035800070308214103151814901c44420035151044101c1001c118406c40000102d074107445140c508503407280c1803c100c2c1c101c03075201c20200a5103c00182e10201d44c9505984134942c1c2103000311245285503d901c018400b101040e9140c078890b600c010040003010484203035062007a1403000c4c000628140c05800d00096060b4600c50400801c0000511010690b9010154402401c8564002c1081c030208041c00791007407040309001814050082004024080a039041d2008013882100a01004a40c861460035513801c028500b90540d290840218400710002110340203030801500b8900503071214026280d0062081c9802c0b0b04010303941c40643c012902501440740f4510f80c1503c0c900d072a104920402c942c006807600107102580c0002c1c3c0c064041000555001e0460995080 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 98290188 1250 98288938 98288963
    0x1502130e0c1b1009110405180c09090a02030109110f0109060203120a090f1a160806060318031303200303071b0b0c0f0c091006030c02100c0e03070902040f03 69
    0x5643d05106025060f0082c07245070198607000d000c80800d02d0460310004440400055588021400c400c0803074101c98400340e030240c50314040e1070804a601e21341041070341003150b40000040e0b000a0039914600d038121010780000036581d45038140011005940785003403c00f11101820603000039603078000c00c40b407a210707a8000c102156114050b64001c0904940000100603090441c0c10070f5104030300720012034080d548d03da00004024140e8040c0b001c0403030346e0703d946020b2070703860b100300b0001c19800150001178605200001007040c82e4080004154070307101c400e400902c4510b0350030a002902504c0b040310081000c10014404240e401004035603410364002c4d41e1120324000201945146c0e09550060311740d0350f0780001c0200e402c42000810440102d103401c1114404542c1c0700134401c0305441038a40800980c405401405114000d40099400f001c0701d20454503001d42c07449e051410b585845951001007400600c881c4410f05040c0700603c0500340c404000d5107041d20b00302d01c03803008182c507100281c1540301000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 98291438 1250 98290188 98290237
    0x603160c02060703020a0b060609030d0309061104030309080f03030f070f0e1002010b09010b0f0906070503090a06050d0c0905030c0f01030209030d1806110a080306010c1502130e0c 79
    0x52035001259000307480103407036208610f00070750780da500340341c0135550381004030001101447c1c8001200c40031040680075000c901800740055000c0e20441e00110354564441c02e0072864480158050001503020f903030b410b002d10b468400c1545c02d10206d013640b010039410800820071095040d2514541060652070020b209a04500080f01c01242d600035040c1e000c91943c01241c0440c2e030540107009000e000700c3c1c29800c1a41e807520104601d2040c0d0004c1c0c0580303171060002c10b00300d240c810041e2400724001d6094a2a050840300042e6003403149801100100710702040d070f404415002e1007154108030442c00c00ca0491400e003400240d841001e2a02e09120314100d941000c0c0a900c20f130142e801c203402c040c08807045201a02d90281008000c1359203030980c2100c42100045841c031032203a880070514203601800741d180c55030311032810300d0f80000e0032035043c03040c8001d5442c0060060f00342150a86030201d00140c0313420f00d1000000f840d8040341c1c0f000d00903a60010902213482c0714107040b10b003a0300c01e04100e09175249114 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 98292688 1250 98291438 98291447
    0x70b040b07051c020307390c030c0305031c0c020c10050c100c020f060408160c17060709060e01081819051f0204033f180501020c060316 60
    0x200020281810b003c4030790103900c507180c02950080900c0d461301c7d020240c03810100000341900c449143c462140f409050315540e02099550580c4a00500c0801d0207181c03a61100c80d40074003d64400c46035030b030000591150707070480c0031110710f60240c0704402444001700641c0300a640d075528699162113044503041c40035400b805101140d07420100c1c0c00c19a40c261044000c16401001007034004030150147c0d4410852060740480c176184943da01c90002c0d07041500310440000e403d1903c0b2000c4596414100012600d09210319031841d10210030300c003d02c120f2411031001404c0c9040f50b4005014000c9040d0342e0380403680c0040c034503030340b0203c1c00e8604450f4035000480d040c644811640500000e000d96944c0340144007021903441c1c08500d410b000035141012000740041240702d544005000f86085d0018007805d040d0051420900c540c1e0f401c582860088040300e00d43c0e000102842c1c480c0815958000341912504040000008000034006400038801c41008243c040c440101003600520030b96402100280c0213 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 98293938 1250 98292688 98292697
    0x40506060d060f050f060310180612120e0a1409041a04030503070201140f0105010e0a0b1c0501120203062d0103030518040618090f0218100b070b040b0705 68
    0x103841c2404080d40d28010910001028060705008001c403080191103070a00000300e80c01801307069011006185080c2901582c1d50355070803148010703034a0f090700103103800c2d944542c034400d40d001c1c03003000030f012000da07a0140074031050380b810900502080c0340c2006412180b002c0e4501101050f603112409945034034000c0c0480e003021003282028501c0c2c9040c0018150700c080554480d5245030002c01c019403100c80800d10412086405c420181e0b11300005100c25407103004824481d80c0041d103000350b000e4030f48408144c590002040541c00c2c8442c500307251400d500501455005200504421043c07080d25004a80c407040028450480c00b040c189618640c1d42001e03003003402c0e003d405100c2d021380d540c403072400038242c0e8016240c02c81c42c0d48841c101302686150512a8404407110090000d400c0c1055000e090090807a0840a981c20703421078006e140941c444503103185940000d03140c06141e520701f00795411148070b5190000400303c0e40512214001a007402d40301500103401604189441e03071082001c40c2c00f40b04 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 98295188 1250 98293938 98293957
    0x60e010204121202150103020d05100c0e0a050d110613080d03022a07030b0702010e030301170d02190209040204020d090f020109080f07032d03020601030507060504080c04050606 78
    0x800500040c48551810b0708500103846031094034026588600b040303035a80320345052a007065204800410043c50224155194103200300c0540d4a64204604140d0443d1000b070580c0022a8000c1d1800b0a20b1030101c11540240008603141c0b40715a19949a14100c840d00e010b855000e40d8000444000103810000c8e00001001c90000b111044c010441000b03000c0d41001880d44000c40c4000700600c40d1107850b10380849001c203605c000f000d0b998616146c04445c02d9014101c0d5055550f074081040e500e80c1c0c140001d501034280c2210800b6840d8541d4409481c3c01c0041c5280002c64000c4010340460400000074100d8107a01201c46201c5500d0b1400013800a01c6030100d0b0124542c90030a888040103d40541c071105c0a001740c1700d500109564503400d644500380514000010f070032164042c00013644203440c0c2c45c240141404200c2c1001c40240003000c4028404200b5000360344194010030030420308103c42c10213803002d40b034071078201854a00559a1307145010f0800d480f40361a103001036155105e0394280c642104 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 98296438 1250 98295188 98295191
    0x70b0408070606140102060411010306090c05030f1e040f060b040606080a060e010605090d0c0308040803040f080a0201050412060f05010b07030201110a0503040201200102030c03220b060409060e01 86
    0x2018984000a80d0202508403012402c0c0314000542d103400100c030302448041a00601030a035103903030703a00700c08416a042d168140b598450010407462043e2007010b01d85045611020703503a052620382841881001000d10800f4401221442d4680d0702540b140d940003070340722030101c907407011a24002028058110000390001c0c600301c00001c109500403041401508c9001081283c90344900300f00c064140240030300c0000c107008028407415810000265507080e4011180b40183c16125a1107008591065201070300c150b20218083c0302c9104412035002c001c2c07800900501004405038000781c468012440340303c480b0f42d0060458000e00480e908103048810710100e0400c91981c4404401c0c20036080760328103500540c0f900b103006441c4041c0d80129a01143d0070f44070513007181e8079a40112888105075081c14201307180d424001c610414240007a60054065501c12038481c0f030103440d100c081d60f403421989407041075105122400304040c0e0280c00e40100007038074041407810f030031308111016211901c2c1410596 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 98297688 1250 98296438 98296441
    0x304030203040e0c18091b0c0a0b01030302060601120c080612010e0f161a0d0e100c080a0c021501230a03050105010504051e0c09120a1a060111070b030402010203070b 73
    0x151300c0b5002001c510001120440310130091300280300c52003a04440364880d4110b0300d403417000240010009044080320f81c1c000c0718800b400554402801440a0b401140940e0003941400003030760704070080c005c0c0b0b00041c003410002442130420007441c400014001070b02602c0b041d5840e5900e500e0030340003440c50302000c204803400000d0590b0000d40e10000c0060b401200c0c46500004640800003440c4207903c594280012402c0c100140c030107100410000201100070303c50580d0807440c0e00c0d40b601424a10400c6a1968134a03460400d800e0b2060b581d8400d07020045411801c012410551815005819503441c03030b00604a1000100c8015072040f10b80294990040c0c00607400410003005400650694030150f800f4403840e04c50002c095070340302c410b0128031f000c3d0184c0d00000700b001c46c000028042e4901c0041101c2c0e01041e41000f41070510301002400d4401d4001c0750241d03002603c4100c4c04da07401c41e6082c43e1803a4180ca260f40042d031122030900a00402050000111b02568030804c1510415a04054400da2a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 98298938 1250 98297688 98297701
    0xc1504060f1401090c020c010c02040c02010e1f0b0f1c230a05101e09020d02061b0c031207110d0516080616050409021c0c030614040216080304030203040e 68
    0x7103200c01d04c90034504500f0920b103036030a5031020600550085040e1503040d00342540f07a00308030107042c003448400c04641d40d5401400c90200204a020007402c15083d80f00e1081251000800c1234904581c04140036041d20001e10425444000c9410555540f41e08182076164691520000801d031003c4c0ca5554040f00707510043e64000c02040d03e80c4c03600d226104542000350b031190300700d06032105a030807006240074060000690600703640010004610080118507445032580c0021866001083c0c90756000301750b01880c1c1c0d4190002c0005d0712142e0012001001144d800301e185c26010b200e01c0c400140701510700c1074000c802d1340f900c0c0401108a03078072000351518501c5107003422502c22014441c1c0c108038803400020814080120517082103407425961201d18060800c10f000c00650304c17804825861544020a840c02d00c0340600c61003003140c006d40d4000c10b042d4903180d440d10350345100e44080780c0705510400c00c0c207a09510080e034901c1c3e1194000322054a983d2141820390560259510180e910b56070784080081 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 98300188 1250 98298938 98298971
    0x30b04140702011a0306040c060807030b090406090b0a0921020f0a050303060a06090b03012106090b0a0f0614091305070609170a0b061509060414090c0c1504060f 71
    0xfa2803000140e800c4071402e44c6010156648425500a42104103100c0c090200900c2030a2a0354080c5481c103000c40c1c02543d003030119502080880701a0f5405544040f44020004810240c54010407120000d1008030a1390302c603552400101c070240d501898a01c860380a0395402842010141e101c01c1064550102c582e0401a40340d901c01c07220741c1d204241c4c0400205219005201101c00c0c0c1d030343c5031902401c50b820502800004400d81140c034541180d0720b42c508000400d28007400c1030841c80ba4031545641c3c01c0401d412816a02c02c00300d100c44440c2484014420a007100090494110080360710183c60345403602650702c0e030226010090000d010300c42c0e02251854010700250b00711040d095014081030b820b40f403490f4079242144802043d00e40c070800441d00b286090200c0c085d03038000104080c0d01c0d0070016000140103500541c0a031130076068000403607441d8981004540d500c44c0b02d03508070500e4201c1c00c1c0441500c0c0d001d1b40000d000a020b5003008134090084942c000b0f408090300d003404000702c2003145810746 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 98301438 1250 98300188 98300201
    0xf050d0b15030405010606080c0a05031b070507030506130213050703270209060d0308040b100503010207030905030601090603030801120305070c0b0306030607020c331614010204060906030b0414070201 88
    0x84c0d1641c241000042c00e24414503c1c54032030f501c005942ca0601e251107004481c41d0b84090a4000e88a018954000c2c0c500c01c40c1b00149413030b41c0f01e03030b00a05c40180340d468102d081910040104580c590707076080038009a1940c4068101d6600f001700000340d199030384441600103105d001c0c00700724000000c80807251520310001d0182c421900886528071503a40c7c0f04108a07401e40444001800900e20601080000c0c1c1c0312070406800c02d100750608414280c440c000300c3c0c2240c1080c8404d40000d010310404000a060a02c03a02c0d0142c54595414011b160841d280501103030010710480d403941d0fa65000040a052069060700d00c0c041c0d000a01c01a190340d1000010386903001540c02c18440e0013000c001c030313070303160b000142c814001c0d0005401c110810850b41c0603020f0340381d490324591006504d41c1c0e0064451981410082000c056a00c084140c00320042c10000c4600e1425041c880303150313104100a104540d00944190b0840301c5c02e103400305007001d1060120300a0020161907083c00c203c0d140900116903010341045 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 98302688 1250 98301438 98301443
    0x1180f080a05070b180d050106090e0304030b06030a050d050f0409020d0603030e01030504120c02031504030201061a0c0304090c030b0d05010c11120a05070317090604120206070f050d0b150304 84
    0x22103c064072441340d000c61384030f508000090106054840d010905024580c6c031003485c01000000b0380f09a8523048441603e49034108600940c10024081c000c200110718000e4025205030020491001c1d40c4e660180c2c0e90b20b00c0140c1c4401e2200104400c10303004032940031039003d002c5501042d512410b03a0601c5602401240c0811000310721900d017040c40551292142503c560313040860403640d14040c2c0015038003654080000d1740c150040d41ea1281c04017a1508504d80914820b078000202107240c04001500003c42200030b901d5050304009460002c04008103071070030f42d42c5e200740015800030314500640081c00400a442d41208460b800c0c04240701c010b6016010301546070312021078040e29601440d4452024920f480303420315041c460051045d2150000d402c40c240f190526078001108007400c0006c224003250399a046902c0102013002304010503104444401c4140000c1000e4184941302400118540c1805010060701240144072092560480d180d1910b0140c0042d0002204580030316250340122003d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 98303938 1250 98302688 98302693
    0xe0c1c1b06030c030c0c030c030e0d08031302100c0503030708180609100f02040303090e0a020f030f09241315020d0f0b09040507140d0602030c1305031b01180f080a05 73
    0x1284545002e8911b101c429a8142d80740740102d041590141e03803040c540d1082d141c0141c0c181c82d8803030024044800540c01002c50100c2122902c00d40c0c410803018403150700c079600030442c140c44100d002400c00401c1e680c01c20428182078495030f03110340206070100c21002d43c030f81c0c040c407030f06003800541c800c0400d944070700b40000241401103180c42094041644124800200090101c000c10458092075486036604250300703c07405480e20b0400c0948500030303001501c03810341e0000100305003d10103c080000d40220b8a48549500f008000d20050b20400c110042c58203071841400c0e0484401c01c220315818250300c502e08802103442d1142641e03030000402d03007030078000081464040c121001d86010400c1601c2540d02c10010714445041a4542540610641c4d003140c00050328541000040c0c807030700107140300e41c00e40c0510a80b15095022107a6000a255200300d0081e00300d00c03a043c041502200803000c40c080c00b0708041c544100740c40c0d00c0c88080b482c698032400458580c81404980141c003c644049118019000c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 98305188 1250 98303938 98303951
    0xe09310f0501050f16030e0f030f030f010f03170c0f010c030b0901051917120301060807080a0b01050d0c05090a032406080a060902061c06090e0c1c1b06030c03 70
    0x480c03000c003100517680a104004168804800b0318425003100000441d050250350b147c5a043d1401855600550b040e400180c03808000c2045c14403014081a0042c072440c1050300d00d003861500c9452041c0c111000d5145510302c00547e0b511251401c0000c41940300c0410020000b894022500400030024070502e10710071a001000003a2528001800850804a10300e01c07040c0e040ca080180f6004000c0c11a41d581c090080034801c29010409001840c0201181d44409080d85845c00c0010300d0080000c19800140340b600785208590390b4050141d50075181200c41c00a1020701141003650603004006e10258440c64104d4084100003049800c08000208011004030b03003400032070782070140e5410f0300801260340d04c4940d40360049201078101c52045400030b06034614100c84410441c07035144124105a440d185c4a0000b04580140c0e486000800071852014000034801000000ca49144102c40308034000d0743d1051020a005804d40080000340c81c10300103031410350b034801c0064003a045400826001c01d20b401d0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 98306438 1250 98305188 98305201
    0x807060207121515030605041101030606030c080f070c060f1a060301060c030509040908030702010e0f07030308040f050c0d0609031706060d0c03020408010614030d0e09310f050105 79
    0xb581e031803800da802044601c420400c403010744000c002e11407050280c0c04010b44000301090017031003000d0050f409840301480640540c00054103071a025401002018039000407150099030000c070720740e0444941c541042041d10703881401c07242209080005000c651401a2a440700c0115030b108200134040810b4207160300034900d003081601e000c02d00c40c035404240140340d800c0010388140028118400010000070303902c03504c3d4681403000e0b001141e8241c0982c0d0744803200c5498120800040010901900042c040c45085d60740090540300047c1009064407001001d50003044424441d000000b0406401840707009918103281001d0038040c8029000b040b0811710084440c01d016503941d201d41800b80c0a20b02c3c101981180d64002c108820022080541c01c0c400030401541c20701034000100f40341024484d481c0e141104040c1403980b030391064000e00440741907100740354803140405548078081b01d61103400803940c03e158400c2c0d88042d031620140310300c01e558003130200143c2f81190030015006100030807030340d610b00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 98307688 1250 98306438 98306459
    0xf070e0a090c06050702130e01200a09050111100c02070e13020108150a08070810050f060306060d060b0405280501031e0c051507051204050a031e020a0807060207 71
    0xc88050007502d04590240801c074001d000a0401910240a48001202031040e5a0407510400409400e51351540081b0000315540001c10030340c071001004891070281e000b04040d118051794401c0905000c20342c200c094100c4c00a000b69004441e240130140300c0d900f00d4020080d182c0d01c441c01080305544507071002c41c03d40004203216000051313040c1c6070700c0c3c030b6070706c542c04000d0240300f0384172504c1ea00144144c0040b5480200b444500b0007003100e1002040e94910803407450040d15001041220404901000c2020340d650004082e601b05030156890140c2e901241003090103001040b41d40f0780c00c0313410301c414048190081d581440d44a04d4034940480350a405010020076a0000c2c03001510340c001201d02c4484400380a144209400e224075030383d07600140d942c4046100c054080340075440c0d0600c0400d04100313211003405a40001c11501c94841e01e81801e100004403062000c0c0009402d4041c41c0c014458000e8480b601010000e030000d1544126036601d40c1000e07a20086402541c0043c05500c40c00180032006 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 98308938 1250 98307688 98307701
    0xa1421040623070210022107020d03050702120d0815121209120a080304030806030a0321020c01020705010c0e060f12060409021005040602060708040803070809030405030f070e0a 78
    0x440da40c812114004000307000030281c8900c1c400c4420b503010004500166210360003d06144000d40240a4502110000782c10000700102d6000041d00c04205010060303039110301e0720f030307540c0e034141000c948546c42400840c8196400158051052003005c0340c2a4403150004811031140d4152a02140c2c00c0c0601400c1c0050700642c482e001c0a00d50000c1c50344c400c0c2e0b01c901d0014201e80e841c00b6101d0342c0b040c001d07180458908400c50101f9608403070000301b40018144d01c89140c55001105500170000411036a0b00107004040300303100301e0300c4002592041d085036201c90b01190031940520009541f41c6c242403c0081c000c0c4a080414001301b00002c11000243c01d0110645504030044406503040a0000000d500c125500074542603200b03a03030b900d6980050740c3e295002188da1010781c1c0d509480d58103001000e0f2410038080c2103802444402403c000004200c0c208503584030040d441d000a054441c220140d155014903007056030f06008001c08d0303c0c602940055050308581c10000040c46a4a0300300c00360084642 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 98310188 1250 98308938 98308949
    0xf220e16140313020402090a0f1403030a0f030c030216050c03011a0f01030209060c06010f0906080601031101030e0c030304060527011e021213060806011716020a142104 74
    0x9000245603181c0c0f40c15440b8500d80064800761030100700d400003400300e00c0c0c59080500d20601c0560188000d09200d01211560f18080d801946412100d62010700509080710a1408254071804d40d0106107110317405940d2001404554914a640e03146819031b181d10410680e203009610300600090350b10402c40c60b090524030080e2284006506c00c50044000c1d500103c681d580001c0c2c2040b034041c0b104020001c0b04e0090518110084100f4101000f00062382d04a62290700c6a038021001440482c02501080d0200704d07003400d001501504d440040c07418a040840d0140e8103000c003050001ea040d8105c0020100d9000b03104030100742031403002508a0080b802001540058a180051002015004110b1039950105c0c012030b45140c1c07070041d100303d03254403030040c10f4a030544550041002c207030018401c68000200342400116000c08240440c030901c0c0c010060300607540591030b04495a4020700a541401d0340200240b001c480421071010358412807140c0100c0902650b041031840c0f0310201c0b054a05444 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 98311438 1250 98310188 98310227
    0x921020c011e270f051002010b1c0f0b0106020c01090f0e060103110f071a1515030c0c06040c0f0e010803070303110927010609030203030f220e16 64
    0x41d04070310443d00c0380c02e688095002409400008400c0d0011410300310000c02c3d2a80c80041d00505007402d010308001013050403003d580c1040d2212040b9540c44010101001c0146614900142c003406c0844c00d94aa500c07014080d0320801001060507980072860741d0300c1c420281c886580980d9200840503815005104140f00171007000702040d9550310a401000342d40320611542c07420005008003d910310340c88018121120b544103c820011401c019000d698898059000c40d01707641890000b103808905418407070958011f00000103940400c60f00c2c1980e290008200440e0000d02d420b24000144d07404500030b4085407405a130300024000c0d1a070b50f04c10f05075080b5001071400c1602c2a5403c2c2c2c041e16600701c3d42002c001e000c0c041d4401640300e2110048401d400e0403020034200c072120310b4404242c10181c0000c4108520a1010b00150b20000201c0d00042ca00c1c085c0036941d118001203c03040300c02c0310810080201719244001480c0c4070a10542809105a00d0354025110594101910030701002d003036460181 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 98312688 1250 98311438 98311487
    0x201060e090f070504050c070c1404050121030c0c081603050705030105040f080717070305070b1807030305030406200307090602150115020a02060d0e070f0501170403030921020c01 79
    0x141800c0d00706d00e8000c0411003100741401d860703649070281d155081d003014660303913500b403d003010b076203814081d190042c16140c1e038003410704204130a0012084802c0c980607050064048242c0104501d441400c0c0c000c161110581c1c1245101544950440b001840180e0703245c454090f0118403480d04cc8140c500550f40003500002581c0f40e642d03422501d810205003a12402c0d031b42208458220698401007210903c03075690103031f4981d144d29015100d64006444c00d80351440d1824000c2d10404001100800e076505802c1054480d581e503d800c4024244440b2902d2410240c035030709520b209902e1028501407034494461001c00c6468800490f40c0340782d013205402c114004800100014056407480b0306c0e0181040c030660b0003046154000c04c04581c0a1410f8a200c1c40d03032140c502c00e0000091008034013805480304507140d03481c0b412000070b054043d81e0904403000c3c4400800704040602a40c000e03641250b001c1811100741503d80f854200c08140d01c079051000d4024403901d000c00390310584820781800c80c100c4481c0c3d5031 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 98313938 1250 98312688 98312699
    0x714010f080a09020604030f030305090106080c1504080a081e070803010e070e04090818010e060703031d0a0b06010f0509130b0102010e0f060103050f0303090705040506010c120201060e090f07 84
    0x80500142094404603629000e03c1c0141c0c841a0050001d58012440084d42c0c1940b0f160041c00c65500401d240901e9143c00d005100307020010406640d443d00880708010210b81c071480f110524840c2c0c2c0e0000d00c281c41504459010864240050802540b05283c081102d084c0401250494403070500300a01c01c640c104014071517030b10094100f40e0400c1c018540707030569000f620082001c65440386000d079044003000c50118100001161025032a203406e103845070000c030f09100404c0e42805241e20040078907407510340500c00e01c1c00030030140c150340201d44100c1e0544400303400c01d0310303d4035002d403000c500080302003a009441c14040c8003140c000130700c00303400048000c0b54451000020045004400d0440d500d40390303020048582081601100202c060140001e9459032a00034175040711005109540e40007031080001448010815404559058070040307465598240100c941070f003d010000d21003041945403a903110f81c150303c0403050b946560b8140c07116407a0141120b5460111000e20311165000c0ca105000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 98315188 1250 98313938 98313947
    0x80105041d030706060801060504020715090515101a0f07030c05030f0d0203100512070611030f030f07121a0105131703120c040e01030b0907090606110714010f 70
    0x807403a50742280a04218003082100c0d06507400a00c1c2079880c0c0e511000d00344100e16003882000e000b070408483c2185004229620400c08200c0070700e468850070f56608105060040a01842404400903c40344a961811022460031201d060061600d42140650100c6420100500b03d40c400d862100211b41400161f941c1210080c1c88280100c65a02062011900d0172500c900680705001c0400700140e01c0e807502c1100b040081d41154400d034803944000695000c2020003203071000a41d42c0310b143ca1518800901c3d8034510798400c4c0241400130043c004100203c1c1c519001546000d174003980c0e10b25a551a0118040c8141d402c00301050071400d403484400601c83d800346008000d4070366410344c804c8000d075882690080c54540024028010b4000150300d036969050004000d500c0700319145c0d41400c10307007010b907072120000d0305000003071200c1010804207110b0042000310100502c090b4001b0301c801510b41e400100f030904100d180710035a204115001c2462210710f800b000300c48206a4440d920f01600090846 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 98316438 1250 98315188 98315201
    0x30106030308360106030203101808070c12030c05010c0f090b220e04051e060604091e0c0f06050414041d1209011403101505090a0807081c08010504 65
    0x80c86583c510034000803007a801c450500e1010a8000100e55107940189428541c1c08040d41d41c5030303464070300c1148213280c01c5640c61080941004506868000601d880c2d5105209c40e007081200c0920f89411400301a444030b0300707007909071141c0001e00c680e00c00520700f62040300064000c40c012070983c46043c4420881d0340040c000c0c4074080224900248800300840301310f1801500003c001c0d088950030801800402c0004201101010a4007803c51080511164503080003030b01c01da05c12074440580d00c00340a0150284240d42402d1003e1010b159074918004540b00d607075104090300098140000a015402401070700d044072041140c407031056000504100050200f0284006840345681200398190000c210b12201d1180406040f07642d142c400f4000b6104203503c29204011840401c204072080151030310090444052810310b0703004440460301900c1038014080d2642d000010403000289900e80014203004860b445010f941c00c0741c6001107a40c1001401d006c0101c04030f030100c0010440341c02e09a003c0f1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 98317688 1250 98316438 98316481
    0x201020c040203090106121202060718050d0309091404030f1107050405040311100e070b070201301404020f01020309090f04020102010f0e0d0e09240d171305030106030308 75
    0x11b50192244450b03d65210b0149003560b0888404000702d9031a6010401d894010b102c605203a92103c01d8241701410f0704516000e06401900c100824a003054081d1480074003410451500740910141c3c04640c1f03002c400102c0e010b6000502001015034114081e402919800c11079a01401001e4201000d00000c0c0c14007400440c200107071420b08105085040c404111002074952004c140c49845160345403400726103403c01107a0100800240005030b0f041b00c0307a21981b0303a88059072420f58844104d0703940304001d44069500e10a040140804000d500e041d0280d103d035208485040a0303012041c0121b90301e01440511940101400001c0342852a0605100394410710510010440362850a1041c090340d2160b01281c06c0c9034001c5003100807d9030008038941403d1415035454225107002c1c1c00d16443d014443c0420b50201c42c0031840b260441e1284880e581180f034022250020107001201302034030541c0228050b8100d5555240c0124491406020380c000322505552800c915446540344070200490941c0d45 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 98318938 1250 98317688 98317691
    0x20d08091215010803030c03010e090f031b01110c0a020d081306030605030c0d08090103020d090f11010809070e16020a0507060203091809120c0f060f01090b04090201020c0402030901 80
    0x201081035032078005503166460035102801c00200141c845209032241a0010010341d0402d100f081605000b142c00e0b241101c541403220381454484000540c2840f022044400e25400000341e6421080078108500e003004619030004c0241c100300f2107014100d03000f00440580e16820081d800c0c00503182400451100358090a0302074941240100c1c4800740c0d03010f40d030001000c281c9602d401c0280b8031b420b2200034106903050754031030070503051580d42c1c0300c00d4800c55001134103040d4046214581e603032480c0d1006090036400300b11a219a0910b003015841c002030398807514002100c680018101000c04125070044031280400c51441d612007404503d490a5031031148003c6211342544240403880030400000104141e4010b183e640c41c001c418826015022100d440c6240704035002d008180780d00181402c081000c0b1002942c072414104091030920204081185817031003883e05104400100b02100c03412a030f01c2d440104520000b01003400160307520580c0190158212060b12403407030030190020b50780700005000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 98320188 1250 98318938 98318947
    0x30c040b01090905091501080c010804120e092e0b071113051305010e010b1806030f10050601091a09010818030a05031006080108100905070f0b180108010f03020d08 72
    0x10343c501140c10031608801d684e0b0003580694070b000151100c4d207025000301c001600a01e104070001920070140a44010041c0c0c80d81200641a107204581402800400821040d0030b401c1481000c0304030b0115010607031403a0046c203500d201075180040802c0803541403074500c6060100036181c4030100c001c2a4a8141c0100d4440e0746010f00389414800d91f48150800c2c08061070400290400ea0708407016658484190ba1404460074041c1d9107280070b400524407000d500310440d60303c2802181c200040590480b5003841041b01405040c0c2c41904441d102d03020070782e110040c0b1580c0724980301c004850706640000d21142046001425403041a9156002e41d072250740008043c800c2100d2407441d030040c4051700025501006011030dca410b0801a0018411460448046e50611212603228420720044200b8155900125410031030144008002042e078010080e42056840d20040c259500c07a0302c00a10034a90854000306540c0a000d0305030685d54441d840f0140e881c21642804040d4038540401d5820f80c03420300 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 98321438 1250 98320188 98320199
    0x30b0301020d090f060b010e0a030807152d02040e060108040f0507060e0f04090503040b0307031b0908010e060907060f050408010203070c020306090a050d030506012001021804020306030c040b0109 86
    0x142c03d1002e80300781552140f00321a41001800c94848007241410405070390140600b0790f81d01440c4e8010390b90842d020fa640c52002d440c0200c0816a220b40c000d8407942404c407100880e100e4400390303074407406841309500e00c0c2c05a034011034007c030300c924080d10001b0503a03140440d1441d442860083d901510070100e180280342c00d62642e600c3c01c000d60f80488009960540340ba42a82003c1244840f50042600c0500c000c02d200c0e942d681e03e038003850142031410100400014102d0303101e50007024228061115000300e0709003042000f0b00382c03055801040165800c014550414040006205201d2042103016025050404004580c214084403081007000341c18031010035082030a10044d4000c602680f1400003540725403051505000c2c00a110505030341105040e50040f802c042819110a1014500040c0c29500e8800503200c1e401c04004101c8034510340c84100306c212105600400b01000c09101428269400324100030a81c4006c503003094058006001040850030160461108203405040000700d241c0c170390 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 98322688 1250 98321438 98321441
    0x31a0d060608010c0e0a030f170301080c0f1c030509040207140303010302010e12031e070609031715030304050603100e0a0c0f0c0320070803070318080d0f030b0301020d 74
    0x1220261000e03603403001d040202d00300034030620703146624074184102c9024a81002a4000004d0b01c000341c085038680240104000e100328411075040b1280000c00e450f540c40d0812940c4e521025031601c2e004034100482c03200903242528408519410b158540301042c105139404a8081d00031406440c2c000d5000d000340303c00184c4400d0301d0001c81480200864582d031450000600184404000c01e01a6401044000343d9030320200c22a1820030212644060380b684400000b540d034451007602411441c82c01001004050340000100c1d50180700501d4040c1030b0300c0d0b9032000c40409501c248210b42c151310030802040142452409180e106040c40764041170150703603021529116504482c0712000c1c6070b42d0404d210007039402403002644204c40d0303c3d100c421510300d41d5000d0254100000c08001c40c400201c45038040490400c8804003a20070754040d2501c0da0310318500030300f001e40c045100d9036950340c0e4500301080020000400b007640900310354030100011172949c03041d0020070440ca02030350555003c1000000f40d882c04e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 98323938 1250 98322688 98322709
    0x902040e010e06190510120201021002030109091b0807050f0612090303040b0a0605060403030302130305010f02070b01080607210603020616060c321309021207030b0a0303031a 77
    0x40e070b0003a1200d403404207501942c41c0003601262801901e400140600c40c807401d02260142c8500001c0c4580103002400140d00d024136251981307641c40c1c0000000300b04212650080300d4020311811100c062002822118410042c0790700410b00180c1c4107800070403451401503c08903020001a01c0c0d41e1510020403040a2103184c201c501246550001040c00b04000c41d07c079895511040c1e002d420401c507810800011283c1c8242d10010301016008901b0206440d01609100000c6921000800510f00f910b90380c68065042180103480360340d80a00002500400070994030300c00d90481d0388111500d403c900d0425100c0701a4156060032958800d130120040c2c490300000c241c04d0412400d00701464800e4a0f00784142c4440a044070100501480960600c03e01038184a8840308420ac0062154a00f0b104d0800e00d070040c516090030303050540c680040c040b42e0315401400c282401304600c0346240d5690000b94150746109040c0c0c2d03007207182103004002081c46940103a00000500c8424451112100c0000700c10050 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 98325188 1250 98323938 98323961
    0xc031a030c012f01140f01080a020105030a14010f210206090904051906020910020a0f0308150d06020a020c100c170424020c15030a021308030403120909021c0902040e01 74
    0x655000c40d060500402100607880040d000169030f1548c1855089500d40780b000700000d05005011012507810340c0160001c0030048241c00200c0380719070f5144581500021a0311a10088840701000f400200304001c0c03890003030301d4000e00300c149010110320510600b441d00404c15035050080b40a500d0480419881c0420a14000e243c0540c840038a1f108110b0705441512011080d54000d103602c3c800107180d4440304032900d8044c28505a030b59612103082c04140c0e41010901d50041d40540c6032000c0200c01d60241440402941c200d40c5400c01c0101840100104880c481c2e02241544140e1000290101c2c44200c00c1135040105900b005d40d50f512226640031b410811001d4012940d84250754650704206540500000f1640d517031508907a4070b100750480c40043d01074080142c00080c00811459a5000907001f0a1000100c4c0c0d030312981c4e07040c2440e40d0300c1a0140c0e60f000134003402d030004003c1181c0c02030320882d11030b07114007880505e0610807001c01400158005c0b40c009803560400d0b8034441c82841803d50805 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 98326438 1250 98325188 98325191
    0xf0c070b0409050f011202040b0402211e25030b1507020916170603010608030a090905090604080405060c07090f0204030b0f09030306240d0c031a030c012f01 69
    0x6050404502c242e0320000d00c60002113201900400100c0c40035990b0010047c0c040e0760010300e20f9030004c0413034068407418002c4c40d0013607103000e0305070302400035005020701c120599034020344008200d01180c118501c06841a8007041018015407800d42800441f80e00070003003034240040c0868441c6c011643c056035207080500d007081c012800c8829800c01c8102030390b1000343c0703100f11201011540c0c00640b005c072091700300d26078000e040400240c5640b825402140605440d0f012a500c4003d04400180b6201e04d40c0100c4d5482410280440e07608a400208180565071010025042c941050b062010b19005441c0c50401481340810000f9041c20601c9440c4000c0078001d0f0142c2e580d411030414144102025240f120006058410012002004400d90744c00143c102c0d18400d640640d80810300e4902e600c1c2d0550707517000f14000b810034070075815a808043c02d240d241e107041c0f1200f000c08000070a00007101e03000c6501500070511950245d031003a1a0742070180041c11425540b80c0442c031030103030b540002e024001141d0303 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 98327688 1250 98326438 98326447
    0x10e1914012402011b0c050304230a060e010504030f030201020d050106090807080604020a0519150909110304020d1502070f050709110309030406050f071203090c0801020c0606060f0c070b 82
    0x91000301c0c48003102c503509000138016018000603204c84601001c102d102044800d514440c1000410b0040f500108a5100002c0f40d0200c600c00d2103280981448d204c80c07080488507000034801d070080800250311641610b0360350605146441b0313802c107080741820460071550708000f10168441c10f4800c050281c6441d41c1ca84410500b0400710300c3c540340301c6030000e50a03a803110080000603035880001d9416244240c03800750528443c041403070400034590700440203241c025080740c1c0304198800c0e00001203071800c004c1406414124514a0720700e110070f4402035088044001c54a004c1010b0b00c4e03089805046220006241211a031034414040701c0e405000c454503001440300700961078180c012040e103100104c004510b90f0516813481e5549106070f02c540700130300901050380c14000c03021006030b030b80e44c03604000000f0318080b030744074014000e002803002195082c0c00300d0317404030321654144256030b4118004001060641c40d02010081d454000c400c84000e034030000c0251102039842070240138000d00da402401c50700e8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 98328938 1250 98327688 98327729
    0x4030b040309090e03040b07020f1c14070e070806090424020706060905070c03080907030206030109020901021b010c030e0f0a0806070e0103090308130c05030609030a1106010e191401 80
    0x140c0301c280b83c13581c001d03500506c404e201c2e00c22031404590800e641121a00856507400c00454a000b040998001107004403510060078040075400741003c00d61080c040c2c48040340c68107820b0500260075904080081e0b081c0001a985003882a441d580081c0100c021201c4695104c88096800d180c1c4049111055004111207040101c9c9005000140c0702c0c02c00140014600719034010200300c1380d200c010303041001c15408101840800c0c4210405143c000d042e65030b1341d41c3c6170500d40c406075000d512054010f1080e04070200032030660f0b82942e081c2003c160765041d094101510b0488046458089840d4450750700301c52031600303660350304400d8010f10014000e440c007440c0190016041241c5840c000f81450304190801d00025404400e03c1d520040e51040d0203440101410311030307400f464541100b0b815109100c00d00c003800c0c0e0000081d161074641980c420058002d00110551110130a01c15200410343c1e50022910081c44000207081030711000200240c81030055806060746082a40600184a50288600c41 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 98330188 1250 98328938 98328941
    0x315051e03060105030a170a0905131d1204051201020f070605040203060c04030308070f0c12030203011e0b0708030403110304030b0106090503030a0f110708011b1b08030103080306040204030b04030909 88
    0x1404110702801b0001120f4495420384040c225000d00c004000041c9040c603c0c0c040d015580281c140070b0400c0c00348411940e4100028803040041070b6400d02002d0703803441c00348000a10100c88802614016050a11380800d0080e80502801c0224840d5024021404140c1c2c07664081c00b81c59000b850041181d0074140141420300708050000740342c41008100c2030002c242c1110101e0f400c507003140b5055180241c590811145211040d000400190707002c4030701013840d035240d00075506a50079401c60440b1140d961000f6151806a4810740c020300000f070050b580800c2011000c0d66100c4d0190828801d6204040c10050851303009030012a4844040001801059400061000504801c4d030007107103407011460001d4586419200c48808205035103002070268002445160300034061203000740040e85c81082e4a410030034910396410b000070036255030258940b401c031507402e2a0f550080f5443d4516401d50715052107641c40102001e4010350204000400602c1010031a031003680a80e03501c0195074109503003e030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 98331438 1250 98330188 98330191
    0x20d0b03060c0313060e0307050a050d020a030e0906180a1a010e01020c0d02030309060c010f050a0603020a0e0a02070f05030912070828080a050a030f05010b0a0315051e0306 76
    0x900980c0040d0801110b05540707000c5a0700071007015414115405145803900c0541040540201c0d80d010225901c81080070024158078060321403000e640148503203800c12643d54071148809000a101410365101d0341c28842617507504000082e0081580d0a103891103030031010020f0719010030b00c59886160011a4106140b0381d600a4024a0428002d141c0000000c1d48d980d0344075407052244010800306011960f04008a03030480700050329040e00d5600e100390141c020030503041c681c82c01c242040c0000b40310b440306114460a4a07402085049554140140700c4d1007110024200700410758200000b10105030000203205006c6d02c1070700250342e102d55220520007840c11080540540d030744240d400780302005010582e81d415054038030b0040b1420111200000d03a861091030040c00408001801c1c1050303503031180084c140180300351024403c3c2000804000d044940c244540c8240c5403060081010381482500b2030011800c00c00e166014041d11807001560440c1084908100a0101d80c02c03c1c086050900c03003036 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 98332688 1250 98331438 98331461
    0x120702210f0f0d020c0f120a0605070c0303050c04030206220801142406040b0a1202030406050115170106030b04020d0f05191a060310030c27020a09090209010306050d06020d 76
    0x20810003840101280006c40d0404140f8030546414600d003c5081c401c2082400880c0c002d0f00c24800e50400090241041000200c2600042d00301030000383e81841203c200c0c1d04499018150030314100300c40048500c0c4001204000c0b24989540b40001201802402142d00d155034942d1000c00d2814581050362469a44285004070400c0d0040b902c0410f80d101c0c02075800300e61140c4501030703450903824000c680001102441400b1284040280702c14402035a1106040c1c0356400f9680c1c5110075491800d590600c11901144450341c00200140b00d02c40c401d400004a03210040d10150404021035400d40a607144c01c41c400d0b0285036954100447c04950347c9400708500381c01c220400c8418000356042c02c918035a07841d035900a42c0c000021a6800c030040200300c0c001e68000211444c000e80310942c0503110044481451600300b02c25240004030300031442140c54481c841d440c2c0c854141c2c0b91442c0b00c4041e4002d5110b56051603528400041c0d6a2a41d40035080024811003005a0b10300008015100b10b55191251 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 98333938 1250 98332688 98332693
    0x170a0504141f0806030c120106080105070503040c090b012f0601060507030e0618060d053103080402010201112b050402060a0804020a0306090807030f02120702210f0f0d02 75
    0x6141c00c40340b050540d911a504545045030081d81d070301d40800d10740541e40c0d81042d040010101d800b0034078001940000141d40102700240040d88070780404440c3c90100741c6024202d41c26500c010450440140d000350001207040c1821680407600100e2203800a001d865000040322821120032600941409041e02403c200e003400c0e03041c4181134600900c0895880c10441c0140700028600200403e81e080210341e050b1b00030071541e0b9072002c030040710016100a0750b06007200d03d242c502c90110303503e103400210702c100301840010008602070748044444081c040e105a055542c0c1705082e64000d40b0000c01015402c040d03541410741e54444c0b5079546d450292184400700d03890301d044248001640c44004031050102c040c40e00c2d070b60b5910785000103507280e079007940700a0040e0b160000180820101c0710141540600949555000b007041c200d06a0306c0ba5030030031140280c2c640400ca54801494822b60302e02d001d241000440303000542048450b458617506014400069004501291100100704600801540c09101 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 98335188 1250 98333938 98333959
    0x60105061e1803010606020a11040b18040f0204051f050306041106030a060b040311040509010501050609060a030b03010e0a20030c010f020c10030204090f1116170a050414 75
    0x21003080ea6030400c107030324210820000b400b5550082d2006210028a0014000c1000c1541c03034001940e07070200d420089940503280520002107117040d10038400800c0001d001000d8614400c0d250403500d143c0200115032007901115804090380317662084520a03600782400281c02200141e03454200c1c2401c0d4060f5100354003200402c8005102c2400b120b041c580300395001e031303120340307a51071100c0180c616030700484500440801c0000500406000c59400301809a9013005540c54441c142b6003a94803d0082d03d42015082003100c2807030815000801c41d80149140c0040c04801c030b03600103402c1d103400803006003517640f00004000502a00c1c403d200c04e0308408222f600e144080d54800300361148131301254503040c44040c144005209000384004107540340000c140364410800904054029000345c007810102030718106c1c0c0c3d60000030503032142000c6100281a83c90800b01c06084090409466003c11030f0301c6000f07580880f01400441e005000c0c000c481ea12780c19219814040e15605040400e007000e441041d1900 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 98336438 1250 98335188 98335207
    0x8160c050111010203100306090201020a05010509010b01140702031b04110d1d19080f0c010203090115060c030503010302090408040b0c010203090d0c08030a0c110a150c020304030314030702070905090c0306010506 93
    0x1510301041f207501200210340e403413840c00143e00b485000300014000313500f400c00304500110107501281e045002600c5504401581c200c101c0801c1c0241c40000750560301c50540000070712181042941042001400442c50b4041d0096010980d0000d105842d2040e07103130744000002c00c6810001802c41c00840707004003241103113120100801c0118400c00f0b0075992001501105101c00501101d6801d001507000790342d0303414101c0500e4003d103103480360003008040060b00440c82130303ca4001038800a82681d83c2e0303070650b401c5800b0040d0303000d00500f00300d84c810010400090004250009050b1180628000685a1034010705540c10007540020090801c200d1088060005614500340c076000482d1a01c0001c404410b0441a51a105c000c0c550b01d0091080304006400c0103040307410081101c8040c0002c0c050942c42e1042a0790300e01032800001c010418030403143c80800b0412000e95444007881c41241e2040c1e645501203003c5070800d03684446141c220420341022810100b1840c0d004240c2174804919090350344 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 98337688 1250 98336438 98336461
    0x19080706020a0e0a030f11190e062701091b08010e070903020301150302011707021c0212070818010903020306060607140d090e010e01050f06030408160c050111010203 73
    0x860004100c0c81d4085107550030b4903c00c403008107480308050507058180f07841e03061500d46803010381c0c03080f034010781e10380078064840c01e1180c4c84201c03964148070398101150500013640d2401d140100100d42040d10b0b80090440d000014401c402c0000e280541c44510303504010085084d142220b011401290501070401d90013503003c0003080c1115248900304a05480300c0710308850300180e9601c065030540c209914442d19100145030034044920076211a03c0c414100818030a42c110100ca03241d000d600900c0700d003180002982140d0548030400d106039500d040e1460031b80c64007504100001d558000d800721f9091152011038680f000c2940c024249520034520750740c0020f0341ca0754010b041502548000c1007480402c4040d2111072180408501610321009680c0401807213003a041c411170148050060000440701000d8540506032540642110f4580003010203200c1558405841140c48070000c0010400c10f0703400070340d00c4000c04c2c451007021044e00d04c2d100c001403841003e04401c00040e4410001d000110404 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 98338938 1250 98337688 98337697
    0xf0f0507030c0209150306040506072012131a04050f030105040b19020c0303010806040201020606010c0b07030c141306030507020706090515121e0c04030f15060506120103051908 78
    0x103c8408130242c0d208130080c8a2901c116444a4141c0b24a07010311013005008100988211056900d07040c2c065170480380c281210040b4a24909280c10888012811080650091040c241c5802c4c100706466503500241400d250f440259110100300801d06000750b207800b07080c400081e001203000f4003980c105516803203c980c4014001c1c5c404900c1c440c0202c43d5166064060302d19401110b8140c80e180d603500d0311940e03240d503000c0b14220f0050145100150b4198050b2130480c4046800042c10881c0384d4603100b00340c0080926030791720024400d080d05103803542a5440010325006500c05050306100e0300e0b00c0d4018054840242440f81990400300d428400540d01024901c1115801c942c00b070191120b005a00d40c83c3d1056690400d200c070200d00800c1800e075000d80402c0e200c4500003002101c1c1d90f541400c80b901c1030280e40001400407001c0c8850501041c060b20240d041d50071080c05c000b60a0781d841c0c000402c5640450806918110804010001d101040c000038040c0e90390883e0f0405011190780c2c80040c688078 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 98340188 1250 98338938 98338943
    0x80118110306120c031906050609040807060b0a093e0f0f0d1103010e010801021c0c090e071808010501122d0f0210030c09091d030301060f0f0507030c 66
    0x450400050101404c00581c0692000a030a98601070200c004141102c003c2940c00c0d5031140c14030000c61010304024445600c00d90b08001d50900301102c55031102c01030401001d01a80c8116a07000110302941c0c01c3c801d002900c9408401e61080f203803860f0001e01c5018a50300e6405c00d001030a1041010f88600c0c000322001001194002583c0b1181e500840d11135003c0c0b0704041602504d00040500c00c40ca40e94001c5040e24840346416419aa03955030880c207074402c4545008003100803150300c149440c2590040043d0088a040c14000035488001c1e00d03903188000ca42c241c001070f045001c0484452090101c140181c00078000031702030f641c1003210300400620b070843c00038480302044019440d05043c50a84c50781d50306c4ca0400c1c40403100b034107041c504402110b903201030381702d1164900f820340c20301e000b44281000201280c541c040d089140002c00030040140d043c0804444040881401c0c108000307100441c041c0c87c040c1c0f1101c00d0343c80480401480c42c1340d5000741030180482005800c01007034101c102401c0340c99 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 98341438 1250 98340188 98340199
    0x109050d020103020d0507030b12030c0a06021b010504150b0f0616032a0b06010302074205070215090718020c0a11090c090a170c06040303080118110306 67
    0x41510040f0001c2c824802c4500110b8034210030310814580c1a00501c2e81d61900729042c1282400c0007042c603881e8411032400e94041d80c00440790000003601900501444104035180b064000c603c50143d5003550000ca80c2211070800c020540d079082c088901c00c081d1a03200647d400d000d40380007600401d00a1180b05804406042d0709419034040600c070302c5c0f40110b1001c88a1078600703004000d0000b07040110104100712480180100010180c3d4400d2080e9031940c0d402104411002d001103601400044510b540c543c40286000700c20290140c080c2c000c40c41811826200040614002100074100021240c0d604488406070b014402d02490014100058031040d2564078a0440e2000210000f0b101e603040703000c0326025000c00107040c050ba4a40181c1503100036940480d007981c0b180350420b8988919030900d9408540b4881c00d10050b004408881c0d444450941110070910030342001400c00c0d0400c4e801100003489150043c0400b8211000d82910165012410300030703007510805140481c04000d2406c1d0080 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 98342688 1250 98341438 98341459
    0x80109092901050a090b210c04110d0507020607050304061a090a020307020706020708070608100e01080a0606050301090812340809030c060103170913020d0b090105010905 75
    0x4040c810740407481c040d290054403141210360500c1034102092081c00d00c903201100001076800094050b00c0d9460b50004d01c00000c8142500d250407c0c02c10404c243c4281c0d00c160b00048040c0d40301c5200b14072500c510840d40b07030344600c100d00941e429988020242402c54100e58240b1861a80100c2920340041d8081008510803001e843d008540c1c001010000ea40984c2e49030034459030f10071540c01140541e080354240e40380c031a11340206a0780c4544500c5980c509038060003007000424400ca01041e045503190b400162040c2d0b513800070f8030310722200384c11a2116800421403042000598425140280b4096009100600b410340381c2c501140203031008100c0320308800340003e801074074040100e090562604245002a000c806010341551465454100884c0310540070440c440c2d80041070307031420380135a80204040e03800c654640320346a1001d21031240ca40014028200c4a0340c1e060080f01c024102541c006844401508000c02511078030300146004a10a01c0140000c1e64061469404e0f07a0b000e2300c4820391f0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 98343938 1250 98342688 98342693
    0xc040f08162303010207030e01080907060807050d060b07080c0f1605040c0203070203010c0518090126120a05030f06010507020a05281401080105150406030c0c0b070206060a0b090108010909 83
    0x282482c0b0300031982e155100103441c4c0200740d004520410322110a0f81d84070310baa0346250015540d0350103809000c0200303100d8030004a90510980003092070320b50008021030368569481010600d03800580c000c86140a01080c407107901481088131300398649440005081481455103030b800308001c1ea010302801a0741300d9107101130303641c02001101c00a6034003400811a0442c05070004049400500001750008090b690440f840d150120915050b03503000c9804948001c000e1001c03c0d0318005010120303c440c01030008100a140c1104050f14070132140f07071500c6039245071560f455500620010641d50611205006030405038540c8140d12041d99010b0b41c265411144114500e074075007000c040f10507081c0340030078030102e1030b030301c0304030015100341020b80f110010390f42c803042041a140d0f01d241030314020328000c3c0020440f00c3d10a03005891604a141011107407005951200d89060004541190150b4415010b01040d800c100000030024811000c0e800c0c00e03c4080800240300c8607041c0705107903481e074443c0c00d844107 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 98345188 1250 98343938 98343989
    0x61103010e061011030a210c080a0c0908061602070515070b060102010605040608030c2404060b01140301140901082103042904061103012402150c040f0816 68
    0x541c1c151381c000c0340e803180091840104901000c012605c40070752005104003001070540526400b0707000540b941542a61842d90880080050540300780c20090000703000980d44205004081c0954603109690001031810040a85449080d0740928001c3d4800300e5030252103014201540d440581c405072100c11510f603500103e014201d0303904000d62143c5088000030f459000003006010078444041510074812501d0724900a82500d41c020b0307d030383d49240d800078000031090ba2041030340c2081410300c07401100803204c2c4d4040a8100b600720300c00c2074101700340300105481c04000c505d004020002c020310314800300c48054140c2d284a410600315120020000c0380030032084408074080300c029100540c6514006104a922229017a030303060f54a170707151562301d1110014030b504690503601104401c4207100000484406003000440d072500450080382190b090248081e107081d401250700b00310b200d4860b4204090f00714041e000341d001000c10343c09504124114141c046091b03080f201141184261621400d00014 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 98346438 1250 98345188 98345207
    0x80703030e0c03061e15010503190204030b0705031e040507061d0d0302160b04080c2701150f02010905070605070326010306050606030f190204080a0b04061103010e0610 74
    0x80d8140106010031904841401c1d00c0718520380078104075501a11b0702612000c0449504000c039000450400c001607110144915940405400200c010310340b9a890701c1e07688107807200741c801500144001007440030112051040755105050701d03c5504040c1010750b82c1c665213841e0383c400c1005100d001e041e25250098100c9590018002c050583c0d5900071003450003c0d144c0d1008440c8203c00b8425200100f601003d06003900c1c10754403100c0c020078402e00c8200c00c001c03040b00e50303000c07002911001c800c90785481c00500c403a0754028a11410740041d00008604054030719031f4110320b41130442e850726509001150700094010b0403030703c407400c1455540321a130a04031a805203d503810802c203c80001c2e0281d01c2f0520144080c1246d01542c07041101e038450305d0801002d03110650710050f000700340b4004255810611700b124031a01070a0740d00107143c1659454080e0800d00024400d83d030380b0505100f0881848214090038052024452500c0e00d150305007900f070140d19101516040c050080c1e48000100280185800c4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 98347688 1250 98346438 98346463
    0x1b1b12110601030501050106110307030e0f040216060b030f01091509020303040b0c0d0801060c030f08060a0909030903060506060705070e0901150e07120b2209080304050a0b060904080703030e 84
    0x540740ca684030304003c1c1c082c040030302c0380c40c0c00030358005001008040d020080d240b4182e8140c7d00c20910783c0c103070010010f910074518041036105c5d074200544486080c00c0320030082e02501c55040494548010801c16080015500c40c0241d180d061407000c0c0e0024441001300c411403045504002030712892400460319500441c0c1000798500e100103909a074a11000400c0320a0340c500f40d84001c82c07a03072280000c42c1d040380d01480081c041481e075126980380034003881c0c0082e8800000b400f10340c00c0390740d9420582c096030707010582600400c0c5030101c140207004140c0696039000ca429102146040c285958807039946a561003001d0140c40e65070301240850a080d001072080550f5124011201612224000002001960b908000c908082d441c410018058002c00200b034200400c01c4d0703000001171402c0042c4643c41e1403990156030351002c05a00158045010b1401280200014406090540b6181c11151005030806129541c0d6808100015641c00100c07080213030f25190101e48800f080211524004610303000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 98348938 1250 98347688 98347693
    0xd0602070c080115030c0b090109031e02040c030c08060a030f1205070206070b0919080f0702060702030105040309030212030405090703092306060a0e0c0304030e0616061b1b1211 78
    0x2081152051100085d20701034070f202e103421983c480815500740315142c4031310f02090381c0c60020404681910011900400c1c901e4030700041005590026040b44d6000a90b440429900d0360505565540184140c0d8002c1054840c5940c0d035045403510300452030070714401041034900c0300700303c0c0c0214400c0c01955192035014007505d4550f4420314044091000440d400c002c14820601400b04040d070a245007540641c2100c0c1003407400e5145541c3d202c1c00d40c0100c10603604223800304103500058500348956489030f80256540910380f400c600c10810007110810410740c5070351040c84140b12513502c07459800e800c60080c0c100041d28640341c1ca0158080d80345400e01003807114a0300c000603d2250082906c510409044401c1380641d5200c00c5200030740300b0f064425105080d014000100024010320200480083c010212800c280c001d001c203076008400315604640030307504c50010600400210040f070362114900c1c105002580c41603411030442c00031208002c0c0018000424009089003c3d90402c0c08120040c5d00707 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 98350188 1250 98348938 98348951
    0x30409090c060e0910060806060408070803030a06050a18050601090b03150924090403020a0506010b0c070509090634020606130606021905010f051806070801050d0602070c0801 77
    0x3407800c1d00030303014400d1802240310401c1c0e210a41c83c002843c140300c1c4c0c4241c404001c04c5410160110b0345000020f00051300013908110104240c0010400b95004040c0381c001141c1c1c0746441081d40081e02e160b0b5000f20b01071421800d0600c050032250070301004110070ba00001800f9030700c00004803002030707441d44520700b40080042406005900314540f5100d000d002c6d2000f4180d51944108800c408104407021050f10070f18080300b40031454921440c0360461302a1045605220441c0c5a00e41001d40a901c00c40f10061b0000d0000100c1500384119002404101d03003c429500d000b00060740c0b2250b008189906001c0c021445904a00c0c032001b01c00305441500720260340d11200600b000e5a40c90341070340c40398400c0d00304907040c50001d825805480103640c820760203803a0200411002c40c1d181d842655040b2115500d03503118400c030040600c42c981c482e40c0c3e00285050320344030320941541000030203020202002526401840700d62075070624452069800180140e1743c1d102c0782000c0c46140c2003a0481000f079400e106 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 98351438 1250 98350188 98350193
    0x5090a050d0f05070609050a050405041104060807080c0105040317031905190f020403080702010804080717030106120e0303180c030601121415040b090a0b09010222050d1403040909 79
    0x8840d0380b030440c4280122070241d40c0314801550040014071405910010502c0c040c0254101504074540182c03142138025180014100003805445c1690020015540b20356810856950100300b02031417044203003081c9240074116110f0300021070440c5155030703800c40d001000c52041b4140d008074450040001d0300c02c220a0401c40d4080c07120021410107010f0583c103102d01c11800b20290f20841e0126640040c0760743c0780010b0765005440c0c0304c4006000b40e4034250244130080104071180c07888200c0c074070004500c554039810600080c005c020412441c080d418a400211880684000308072908900049080b8400441d024031407440d0402c008150781c1c1500414000150000c01742503d03481d101d10030020444010151650b0720380d143d20101c0509400d5100308089004281c0396080c20b5000080e0401351514265907485803101c03840b0135200c107449d0703a500058180401016201003800c4284c214581d0315003d2900e4001202507081d00c0020700050500d00031000c40240401c1100c004041000052001f201c450 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 98352688 1250 98351438 98351453
    0x30210060305060a0e240c0403060501120312140711030f0c0a06060b0309030d0b0402210a0f0e060615160305070501060605030c160c0506070c231005090a050d 70
    0x2514001303c0c01d4245198220801c40100e20905001c05c84521900340e8002110034820300040a011850318410070080030001c94018000d01d4068103440d058207100c01100d15009001180001e52096400e29020b600d007402c003101c00d0f400c0c0e0840464500000341c22009401030341988944844d007180d401c0c000034000007480000c5001d003680350140b0010000240d5500c504503141c4400c5a002c04640c00030814011068610f901c032a1106001500050510b62501840b00f940e00c50a41d0600b40704200100b005141e00490241c0240b1090504040c004c4400741c00c41c903030b0707210304c040e00c42c0d803045800e40140e00106c480b52040d030709165181481d51500c0341c01d81c18007070b0451340415020344040d420100d011591721b0003901201c1c000c4c905c00754614038210901003015052051000300700c0d002070803e5000038842d916140a4410b69003e41d8104400500c0c04802050b151046114210341300d00011007854644d84003400064410703114181142e41d5000b9600050711032100350000c90740f0940042c600000d02140 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 98353938 1250 98352688 98352691
    0x207050606220c0306140102120d020c10090308180d1409030c0301091a0c0f070807050c13020c0f010b060313380a110412020a03080301080c01022e050403021006030506 74
    0x644040646d51035098004913180c5840c2c0012145560381000680c1641e45148c1c02085003d110a040e40c40000f18000790310240d030b0f03110b0360581c00241e0280921466008084003e0076030444240100a10b14111138081c182c40721995200f40b0400b004120201a40c07020f11907116681c100a008101910461408502c140800e9400ca6842001400000c0034003203513400b110341050307016410b1360400c400313a540c0f10510392002d0f03000c484c1e0b40112150800786445d5074003c1d08020345502c8000d0707215880e5003101c42c50205004030420b61617041c0202d41c0701c03d03203649040741c3e0404111210001a46054100003a07803030028000075240c154014018070b01000c6c010040108410b611020401d241c4a075103840065800135807200059400400c000c0104c0b42904282164940c409080581803a6607a05c4041c0c00c0d8009078440d074015007100d2400101581c0c1400015560307400c7c2102400b4410444510002e14410782030700c42d1120f651a400720382454000c0102060303a40b241e181c18040c41d600c0c1d1901c0c9032203000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 98355188 1250 98353938 98353949
    0x71a22080a120f140c01090501050a0b010e01090312030504021206070305060405010503060603070603021b0703080904050606040b030a18150617150c0a0903020a090c0f030207050606220c0306 84
    0x7503000759014010311998000c0d11840e919944c0404071001c0818102d440d60110440d07541070341d41c032145540024000c1c080c40d031041e882ca01e40000c2041c480070000d024107a200310180c0c10486005411301c0090364290300c0c2c40c4c103c522032600045d00c2ea25440440c0b8100c00d03008403800c080c4103600400035450751503003040384110b07401d5400b40190703662041415950305083c3e4000754990000302c0e0520965110368090b0203a40700140d91a512415010318160400c0b041e600183c988800c005540000c90030240201030b0062401e4643e58945481e01c01056050702001d00811a403a40f80c4519041d002420750305502019040070000282da1600816800140841e00c100d425400001c2c03081c003c0303400003145c03440200364022210380180d0b4920b1300c20f4403035600003d071500c20300030250400700140e140e41040c90040c0080f0200000d20621000307010300340056981b0100c041500400600c0006400800d010340c101d0b40036585080032100401c4d0042c0040c0f1615090b02c0907520300007500d0001541600540300325103 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 98356438 1250 98355188 98355203
    0x140708040b191214180c040c05120c0f070602090f040f05040b01080d050d1d030a02060a050c03070c030f020106031403091c0803070f05040503010c0e030f071a22080a 73
    0x70302c0f04040c0644000071030342002c0c0c02e80d00000505007460140d074840d903800010f082c2c410307a24613038000408075101582c903100020070128107040c400c0c00402e400b58110244085142c1001c21a0344000a00d210364040140a160081255265901c0b49a4000c12200c0e00600500041004000090041004039001e84003954504000035080070041101500c4a1050361498640b8441c0c1d85590058403400c800a191089128542c4880480034005800400f0f055409000c44e0306003952101c1c260368024000c0801c041c820400c2c0104c0c250440b038080b6000d0b038103042c1288298031014041c0d00500150b44084d01d614980030780a0f40c2c42320040020507030f9a0040315007498115040d1100c110070000a00d00402c1c1d00780030004202000d00031820703410404070314a0f0403441c054550b0080781c00c0d24000710b2801c000c0343c0400300c18107141c0340078410450881d16040084c07042c0c1b840c010a0344120354540840c8a101e04000640140242101c0c40301403800d0a1f68860b5a03038150350b88401a62120489029610f04 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 98357688 1250 98356438 98356457
    0x5070c060c1b030201090501050702150c0322060c0215161b0603050c0405040209030715020a11060c0d0e041d030c0d110703021003090f03080f060103020703140708040b19 75
    0xc8000b03281d10b90a40350183e40d03210700e840c10070006480e00d42c48002d0903030b440720180e94005000d02c1c1c60742c0101011100640616203440c0c1c1480844a130018034505850403910260003170115070f900901e8400001e030115102401114913400d4032039503109502030381d842145c0d565248000d0280c19003009094161150030780001654410702107044400940b1551954103040204121515042d006032610090041c02e4481403983c40a2030710f6a50417190310304c80960090301c0e13500103001a51000001840054940c6031a210000d0320558482c2845807603d07081c0031010120b0056911694440700d000020030300c204208000080102d40c0e290005c4140c0358145c8141d4041c091194070a003402d001b0b5440d048020240e140c203581c204051000b17002080e604041d9144e1104022556022982083c10f0103a211342c2820f0410300d018031340b101c7e0300610311814540100150000254821201044881c6540d419070b1079240e075140c44203403132196a00440f41c140001c07541c030b40408042888003a4044c495143d88454 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 98358938 1250 98357688 98357723
    0x507020a0209090c0109120201031103070e041406010f0305072f01050106020703170a02031e0304030f020d1b1106040602060708010801140f040c050a060215130c0302010f05070c060c 80
    0x1315500004418000f4103024010005000e00c02000d0305214414140800c4030007003000101c0990300100c2d0030800240c0c01091030301c068142440b520441d0846540380d00d40501e880300c00641404541c04407401015981c800140c140344c03281e020305030700041c02e922114585108402c03140302e0b44d040c01d880000e0382d46094000140b4a000160017000c0381c0c0e01803c200b40160300c034145520184c210746441c1040d40400c000c46104420845048040341e4a421406c9840c0d00305414002d001c00d000000300402d55204016824a1079007218119412601d40a015038070b03580320386072100f00c0b0031402c0444d54000308042004500d80b40c012070901d00c11242c554510b07001da0b903074800c40d0b070907500e07117074581000540201c0104484840c0e07400503a600c14003684a1a941650343d2011900182156015400580010070300d4490304106142c6039400507031a20900c03489803240c0d110b04c0060f801d43c0c4030003070602500211100000d40078a0544a21035003107502035150700c1c1e680b030300500003a440040c2100c3c0b804101000084 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 98360188 1250 98358938 98358943
    0x100e030f0607020c22060f031509080f0d0f0216050f0303010e18011e020d0c0c120f0c05070e16020a030e0103050709080102030408120c03010b030a050c0408010507020a020909 77
    0x314074600d50051101020410a001c103034011171100c481905450111803541101d03a02480700185100d500307400c0700a285050201401c2d0107126007142440c100780c020008141e8407410b6403031000030f030507182d0360b81c00781030111500400140c800c42009900100319421034104000ca051001401041900ca04001d4554119140d100900940e40460031100c0880e0002c040c2d450101516102d10000003501c40c2903c0e1100300912a203588184900d400103403140c48030131103000d102102140c6081071003851000b90399182d5140040343c0c0d00c40401501303201e034010130b40c4200714100045811805032601d194699074104080b1004444030a100e0030f0070740c4080ea550344000f0305000c65a40598805455071003a80c01103000d001c000d08541d0070820b4024000c141d0a03004c0c40214000c42c4161811507681604242110505074024110540078106100420841d13212404030b03903001c070703071319000040c01da0394901e0480a60096070041e003032541c03a01c1c04105429400280101e8039030b000b210b841003160380c2e1041056 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 98361438 1250 98360188 98360191
    0x2210d05040e0406020a0e09091b010302090303070b0618090c03010515091f09020f090307150203040311011b05030315040c09120203010f05070906030c03060605030123100e030f06 79
    0x841100c0540003d4042003243d4060a502d401c0791402580d020054000102d25200950b0310070000e40100852440b03a00d8848200d8119100030b00b0706509148a4000003a1039029802d00a401c4504050000d40c995540405d8421040802001c094484c1009100c1a65440e198a6440c7c001c0d840c11000c1000000342200c1035448080007440d00c83c02d039076a2180d2407035102d210406054035941c80013011640788814000313015114184000203813a82c22007020149031091a034480707120007041902c4120025408002c40d01986d42100140050a2411004840144c9100a940340c040d0001003000d082000201c000c6016103420500b2010340d1b00789500f00000c652405840c400820300e14003003003003014891082c042500780002c00020320913030710710717503501c1a103404079104400104d40300001c2c0555501403191522142ca98901040480c0c03c110003e4140c0c4410302a0500007980003400100c40c0c800c091101e510303002c000d405250b039821216005400d00b041c2d525114030030b02441c0c25280407500700080c400d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 98362688 1250 98361438 98361449
    0x3020a030204021b100c080c030603061b0c07060c0201020d171803270a1502030a120b030703051e03070210050c0f01060f03060f180201031802210d0504 67
    0x2144024955402c000084d80515000c0071141c010700c0f00883c8008050004291000d5242130229824036680c10041100e40c0041400e1910141401401034540b40004d481e64402c20400c1c1600d000c81c41c001141c10140074a0400490074400c00d42d000c41c0c070941c01a44074202c1c034402e1b004c440d4403400c0f22200341c403000440c0004200a0180000148840480c4101c0c1c500b4484603c0a480c50640c2400e03080c0442c00d0100c0b0b81c002e0b22641c00025052038100404040000c00d8007080784808903c0848009480f841141c2d042420400300c804154400c500c6540008100070000b011a41815541d02e041c513240ca885120b0500c210104203d550f070110b00c044101c6078600c0e030041c0703080c00d041c1c50800700340c4490b04140c0040b80188542c4c01060b894070400d01c10000582400002c1082c0d90f89140340c1041900c05c01400b2404003414178440c4a5407815682d90802e00c00d80c242004603882a0b10f0744903581c4003038101006036103c504158424a00d90008220101c0c0c0c0c079054096800090000c40c068401d13206a1062 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 98363938 1250 98362688 98362699
    0x306030a0222020301031208130c09050606040b030907080717071a040e010605030f06010309120e0102030c0304090203060f01020c100302070f0605090d0801060306120311010f02070305130501090302 87
    0x500040c0b5121030500e90444141c202c2118585081e4180003c0340c000340c00403100100b20035608420f90360440c0714294006000102008078690365a5002d81070040d501c2003910b11601c1c2c4011518541d42d03081074030054002c11900507224a0010b15080c0e484489100310401030180c0a4040cd040100d0582140744900303500c01458081d01e0800e044880591450720b110b40c03a44280b001040e0b1481081c5058004e01075903071030f80d440303040965090754519405001d16060500d03043da00030024801007980784000c103e44c00d24022628207000141e0640c07140401c43d1246000c00580454503d9095000d50b010b404151211505421400010790380e07004046a06540084005204940c0e1482500203050b50351080009a000401ca56501c1040d03070401d03200240c40383c1010200d50400d40d8011172403401000c16240c20b200f091300c1c00c1285100144601009000c10841c502d00c01003042094000c5081c111007603500315035503a128140100309404c10700242e11b500c44101c500103417640c85500b11106a81e0010706 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 98365188 1250 98363938 98363953
    0x1e0204060e1b0c01091b060206100f090c1710080609010203042301020403020a030c1419090c051201030b04020a0602211c0c0306142d03070b040b0406030c0302030603 73
    0x2c600c0141e0085180c520702907403504000300005004444404809201e21200c0284071b042c0403000e41416401804c402d10000440340c02c02c1418603041000b01264400704001800381c081100403150012100300065a284c40f540c248003c482465000c542110000415150282c861100190a0303110944000e0004540205405249604000c40e40480d1003100001440c0a9490340815560111580189e4040c2c0d007a180c2049034004900d00d22102086c126040e59489040c42e484c14203416041c0a28002c095596010f090b4907400f48007241e000d4007005111607455a0342c0d01d045071700302c002164200c0c01805100d40000300e16000003040f155409a1000811407903845075226113031600891041da2203074a804c484117800070a0361280c83d540e81a103070f8010481e1401c0a201600740d00d054500c241c002e10810110f07030017074070340c108000c6c4e980c4201c090742d045844030b14400285001100c0e00410802940010000341103c000b0f0028800c036045604d00b803281e40300e0714a0641c101d020444096400d0f410821 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 98366438 1250 98365188 98365231
    0xc0c0d1208060109090f0506040b240d060302061303060c0206091c0c080d090611130b0d0608060f040213060b0901080711030c0a060509060402011b0503071e0204060e 73
    0x50110b9110006141041c030740381e80c502581d0f064840d1900d0341950a956102808424101030103a00c5120700260f440e030400b03184058502c5c080f0b0181e207245180040700410b0804400c01b494012900550f0000e240ca074a424038419000d500d4491840200c2e206850300f040c44d1412400450485e03c1158441e024051601e17025229454948400e145071080110360b419903400240c6075006406098840d04c400184120140f420500301c95004060401e005020b01c0900c01c85002031a82c4820744100005d00c0c2e031103454000855021f02200d070440420fa029100800c6620307030019600c548203a0084a07881c1c0c4801c484101a01120f0ba14043c202d804002040b40d001254024088590403c2c128504801020001160711741140c0005010310440d4000c1209a41800300c180a90b5410907100c070090080750034640d00181055001b842c00304000c180e640041070501c8024410340b881e180d0480700200c0b894010b05040e02084503111404c0b031150385403540118044440e000160710507045010420403414210307 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 98367688 1250 98366438 98366447
    0xb070602070203030909090d020f030426010b270a051003080304020f03071203091a0405150405300d08180c1206010f06020607050702040f0b0909030c0c0d12 69
    0xa103410b036050711041103102580c1d191400729501c00c0725940c3c040c100c40c442e044002420060a01f0015443d54000e001c00d209404030903104000c4420340792a090b40c0c0b040e8903c1e05078007409040c4241ea80c80700b0210500f0343c046004481c1088038501c4d070344100d8107641ea0303005540120b4005850556007000c0c500d9040c4000740c4a40001c6401500003005d010901c0c0280002a14003007140c0c01c0001d44001e201c040e10101a08071041d2000781c101c1c11604910b0011600d20038016010d58804e240c89460610030400103c00b020b82242d010701805071201c04c05907200c406821640d40d040c1e0805816a0507030000040210010a601c00300d00c5031640c0300341c0c5a803130320012181038200c1d14215041d2401816182c0f031441e6204075010b101885c180000d070002c0c0d85800148111000160702c14415900002c0070031464943c00000c07910141c1d8103c0e00025040100c02c60701004145c0801480c0e00980384005205034540f000020b00350110880c4100e07420422001e0a00030b1003030700b4000090960034458142101603008 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 98368938 1250 98367688 98367697
    0x120b04020d0201170412021203061513030533070801090203150409060b010f14040b0f04052106091203010504020901140708030402012010050a060b0c0102030604060608010b070602 79
    0x1450048050540c4c4488881614815a011607088a01c24280c0380b10340d806221590600700131907035803815850650007140d9003449408520002810000c0e4003156400354100c0c50001d136810400702d400100c12254145074040780301c4a8208003c04030170083c041ca91702c0b5075806200c0d0703106689808184c0d01c1c0201c40c01c040d41003e4040c2c0404180f003504141c02d40c40314451580b80324001c2d140482c6545c61a00050260381c00e16403003004104002091a098a01e540c003101d049a0661780869030780c01840c031140300540556007013103030700194140c030714000502011180c070804000e62066403034a0310342041690f5180e10026020801d020700740010042c62802d64043c0440303010606141c40741052001c040c03a169031041104032a00d00000c001d000075560f006c400d02002105a19511405001c0200d051343c0c1c89102c8000088080c1d210b60005400441a0300030b80020000040101e0300c8094041c8924040d40088441a0207149400740c0050b01510602c22181207030100340c4c00b945850b1440d11050060f602 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 98370188 1250 98368938 98368943
    0x1050a060f121d0703060e0a050d12140c0702040c020c0307050103021605010603140c0603011a0a030605060c0f120906040605031509010308040501020c010f050a030c0912060204080601120b04020d 86
    0x2503c3c10700302d4500782c0e01c0203030160001114028144407400c1d49003a504903044040786880c146d03c1a0402d43c0052000a04032030311103000e0404200c00c00030010b00401814000031007000c42180c20f001e02c01c0c000503410240406d58400c46003409040020302049980b4020f18840300d50681c00740d4030030821540a5802042c1d51106a200340420b00341e69190203007501c206034011504446030401d804801101130107044200b000c2155042e245524025045000030350480d0b0300050007800169440c10a03000303511190042c0750140401c4c0e02e50207285080e9031202c9800082180c42d01802240140c0d56008008580d924600140a1800c0506103a002c581e29000205842d9030700d82288600c111aa80c0c0100d180e008611903c455039903070741000002030404404031402e030306110520301000680e58002040e15080d84251400040254007100102d0784003000768004140340d018072000324180149074000744207a030380a1040710f60380e0366503d4120a2002d000346018100e00d0864001c9001864503079120b458050 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 98371438 1250 98370188 98370191
    0xc0b0115050d0501060503041e08030c03091903030b011805100c050f0109120e0409020112050604020d020705010203040201180f0e07050702030f15010605040305060a051b040e04030801050a060f12 86
    0xe0b108071118111a000c1e0001d40214901004002c2041210b81409106604800c44e15aa20541380d448040c18080a0500e442c0200d0100004401ca10100143c0070303080080c841c0c018003c07800b41005002098403408081c001402d20401001540c5643e00d450210703580603100600070712485400320341d1001e4240003290780d0f014000113050750b01e009004030840c00340a5030b44c07000e86a84580c0003a0071a05034000440c0070700d0500240b00007507070b08400603400c6500358000100301a903502001800a20845c5088598107101281a07410f100341503000d588528400e881d02c0e601030f0248107074080c481d603542c429540250200501803107010591454903400501c103042c41410305c0c0d030b06c0d4006800c01c12242d085554561101443d01c81050a101c0602e00400260400514013401d50702c60b90348502005000641031500d440109444c04a4440c841020009140840d070b03e076070721000c020441c82001d560560000381c0040c00450b01b490a00340000884049460b1804c112182c218296003025103400c8542405 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 98372688 1250 98371438 98371447
    0x405060402190f031406010c060b0f03030d0501140306061e01090f0603020c0c06131e09090503120603150103020d21020f060c040302101b0606090c08070c0b011505 72
    0x700102850381141d07582c903200c58104100200d0010122040a014680200503030002d000303859800103c44d00605030802400704421400c1c0b0085100c241203400070a0700f41c8000564440e9030a250390010303051b103000780d080d50202c43c0c51808050399001c003503940c6035000841d1b411680842c140100080c07030001c01030411365600365481e418013503510030942c40340000c6500011001c80550051002d6a00c1c0b810032103015090520316004000c46403154021b0f0f07500c04080380d0a00780721141c0e1084450040c43c150304140b160100a140054583d04158081410070041f64045079140c039001c42e1101c800300741e061a0042136807840d000c100c48042815015220409255800da01c500100c0c2c04543d1002da80c0e0b00100b044c01080e0386400e1a001e40101040139a000901c001d2005a403101403440c854038451401411791201000307107408521420a00401c82c40c905400019448840d401148804085850b2180150f0f18064246d80c02003420f10300500401481e00184480284603007020701c1c2007810f16207135060 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 98373938 1250 98372688 98372707
    0xf0a09020402040909120207181508030d090506070201110d090809030609070f05010509030709020306210c01120e060109050a0905031201050a05060c03030118020d020703091802090604050405060402 87
    0x103c0c1c0c400e8002c000803680325081242480310414131481c808900d44010800586000722031030310b02040d04100080592200b03415046078109440c0c840c0a848080706a035030f503007aa2601c00006008a00046900b4000d6400240b081d600622540134042c40c000380752841c5c0844142164000e25101d001250351005c244044051518108200361080d60346900500d4064202008510881d40b41d0f88500c0c1000340401c8042c2094a0100f4450100c5491000140e181d4980000154a082444810415440640500341b114150025100d01001401c1e00e400c0c000800c81408041591309400c02544c2a03030200d401042511842e81c0f01f586d010440305000207107040b19036101800e590000f07114180b040d40030310045c842c0385042d03641000181012540a0328101c04132211a4076400140310b154404036094808003c504015012148140750b80407007150368140740c1c90058940f088134000c0708201d001146250381901203a00c2140c101d40001000681441d280004020140000504180d0025004d1081508 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 98375188 1250 98373938 98373941
    0x6100903120903020306130503070b0a20120708060120120409020405040f0903021c02070b0309011e0204210204021312060b0405070e060a020703140c03010605100203030f0a090204 79
    0x900c412180e54102c080c03480d40c01010b140c44c0018182c40003102007c003540d000254004112a0200d9101021000310b680398081000246080d0103c0d8031040d041710700b240d46562040e4018480206801d00a02203910350b024111080b042c1120542d010034121402005e0204011151640c481d24580c100c8800c0c810301006035440c2e0304194000000d0680101d0144005d18150240500e5070035541002c0005000741d8400940d03401c104603503040099070311401e560384a07100340001c0b000780c10503110302552070808828143c002c2c800f000e00d078034032003200811620203070f0018001ca40c200c80e00c540380c0300e031640384080b54000036800a0404a0340182c0c200010101841c0080101005110740d0446c501c24003a07038100107040c0d0b00701000d441e1156150004204030740342c015011000e071402c10350300c6a4079501c406006914109903900080c0ca22071071340301034400c0d040001031194031141c0c0c103a000f071103525601c0f130a01c109000503001400150f00184005000c3c611680c18051f070280345010003081901090b00800e0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 98376438 1250 98375188 98375213
    0x110d05100615020f01112a06040b061206160f030b12010c02060c1204150b0a0f0503070e0405070b070309090f090b060f031b06090405180d021506100903 67
    0x241c450905a041103505501031100400c0f02011400038046d5600041d0020111304c2041400d03814885569104ca90b16100c00b01942c1e0620075100865038241458100007a01080440e4020721848081c902520031401c003080d0075015100c20744021130345c3c0190074030940d104400c5003101c0c42090740c0c031540d079190740c3d54041c001000d48000b50000104825003070030003030170600002c06104614504110f0012200480c0001c10b0740640c01c403000041a1990720540c2025103c40c180a44c0d12103034898000c0b0300e040c110541e0324119103048044520b22a0b0754460100c0c1703940116405040e40c1c00c03062040000c00c668070014480c16109240c0b40003010b890f0070440d0112490212200b202941d110014008c0002d2032a4103504080103c8140420040c40000a42d4900d0385102091b80c07400040503000c01611000c3c10343d50759101c020000d1042c2d203003500c1d02d04054100100115114480d0058203c1100e00214020018203164071140034a80e035000c040c0030702286054010010407115013400408100d4021004 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 98377688 1250 98376438 98376449
    0x151c0c0309020d0b1e0c0702040902010509040f050106030c020d020c10090308040b0315060f030a0c0e03030a05090405180d050f070803090318040c09090b040207020607050d030c030504110d051006 86
    0x816052148a005c52101140c1c140320307610344070401740041400f00405841803d41d0480c1c0c0480c140340c0c41e20049a60b4004c211004d0b0f0070a080211104150303580e0b401a60507600e09503401c200c41406c10204a039034800071707850700d000350700304440b0046e00341014900c0e0a071030308550800c614120354075580e840c4c0590003a40080000c46002c01030011840751081485040d210840d921030900380e0907601c0303000c00d00c000b41c400000b103030f955042011214010403511250700002000c0d01c1e1074400030500034000368800300d0b60714030480c58000080e0380091043c0206084100c6140100321036070013102c09640503400f50f401254407100a1100100040115005501c03c5a4080245842c6c00b8004172038940040700c48400e903c202e05000d1034004460340300c800142144d0201030b000c80c0b03110070100864020310131018003039042080090407900744040040d001c610188140e0b401c002c1001128400c4085410a1750002c2c0303900c0501d040006a0b241640781c802100f801076044c1ca103428540803034007040f903425a005 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 98378938 1250 98377688 98377703
    0x2060f0a02010c0903080a030b040f1125080f0708070b100305060a06080309010e0d0602030a15080a1101111e061806010f05190e070e151c0c0309020d 66
    0x100c0911903080c01a00c0760300400e82824940b06080d80c0d2000c44a00540f0711039420141e41e2490840565a140c0000c5803013010301904219a0021885003511580404c191080d80d0340e884042489900c0d00141c2098001e412040c22410504c41007503000e0351394001d5505440e012010300502012401c58142e050180d00c011044c041e4082c84c505d0312505101c0014483c200359440c28004001c11440482120b00452003440d14802070520351000415800c0f5601020b01002d00c040700304035000342d15034030004000030103070b041c40700c5545c3ea40c0d810f40d520b410445c40200542680c06000003030354000c1040d0301400f4005019190091010a910020398608000c8413030503900c0f10040c001124602e510003060383c0e681d0300c0a481c3c9981040b02d45040c01e112803080c20700580f2044d41900c4290550b45e110b01c007410000c55004100e06160b44028080c0b0003400041d071149107100c00b142c4021000c481118100070320041303618409a05815040020201e1902d1501403503118016100140e0341d1300707450180070744107415 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 98380188 1250 98378938 98378947
    0x130f0512041221090303030b0a1a04090b0607050304030204090c1e050909160b09061b01020c0106050a0510080c04080718060e010b030c0f0d050103050f0c0613030f05070302060f 78
    0x24078205105400c400000343c180c03001004100039a000e40e60f007003641d4250074041990340c804808030350250303003c0d4081c0549062502c96580340003d5000184221001d0b120f0900c01804c0311030411103184103202c030040081c0c0c001c00007000142000d400c001d00b12400341c05003619071035441c0307100711a10000300d00368000185122000d01151500e81085a041b040100c001c00a202d054122744005028030700541201c0b2401003481000b0707540d501c084583d0f46601c11601100000d0881c0828040c3d0014280407025509001000c519030070402d91510032500700400c0c1c800d00f030f60108010769182c1406403d00328491000c020100300c50400b00800300003052140d402d02d404c40c10228804040f5a226000800140414401000103001d404103481e00301c06440006603039400c2c0c1e180030824034411008071074042c07402c110000090000201b140c1c4403e503e4134068403000700110081006a10841d139814040e82c84c0a1070610219054050260845100f04205c0300c1860b00d9400090032a0044070040400500020703 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 98381295 1107 98380188 98380193
    0x1e1a0f0d08090a1502070911030a09030e03010e2107170d02040801140a0507020d0813020102010e0a0b0117010b090402060a0c0f2603130f05120412 65
    0x1045803100390f6980c10180301c0c2407030a104c2400980503c0d000051100010300607821082d458903001469584d031840d50b0300c001c00038070781d0907010480502c8115140c2d803024460000410494001011b1704010a20001c95a01c00d000f4001c441040c248180400240034601047040180b5803080e86440300162914a00240902c1d80081c100d0341c242a07403240581200c01011380180d01982c0d044c4444e40e901001070740d41c2c0f200c035981720001902e00380c0003d50b101d1081000041c9a0f205100109019070540d55a52401c0e038145011794030300000000401c10701820a55101d00150381c000240030341c506003c0040c801800c0100043c1c002c40c40010000ca0b0284150305110310254448500396074100503082005401c1400c0f0400c0d100041e03440601524191010150307882460b2890058240346c01e556505404140c441c00e045034588101d11011601a0700c140182000e0401d0b0380070700442d5031090 = true := by decide +kernel

theorem cover : BRFrame.Cov 98201438 98381295 := by
  have h0 := BRFrame.cov_init 98201438
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98201438 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 98201438 ≤ n) (h2 : n < 98381295) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
