-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0844
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:07:30.537442+00:00
-- url     : https://prove2.me/submissions/38d27d7b-918c-46bb-a4a6-7f15ba03ca88

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 151618705 ≤ n < 151798561 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 151619955 1250 151618705 151618717
    0x60e060606041e0302030a030f090503120d090302150a061811120a0e060f070206100b0409020a020316060b03070f0302210f010f0b030c0a0b2b090807020f06 69
    0x440741c0d080c0b00c10701c001074441030400038083c00c2c00c1d06001074503900c0c1c0101c3c2c200700b03010005030000360718280c01071000c58000000760300910b015401004a5a1225420080b0f4003490404a50080d22a07244606140c0b00300328451142c0c0070007403106840c1c209084048024a5103201c2c11608864803880c070480c80d410b5209800c14031894164403490281d000100c680f0801008004000342a607a4220048190080100d44c0c171a4070400f50091203400c0412001c0d14001c401400410055500e031018081d05003404140c50480301d0002000d41c5600180c4006e90444c0a4070510709907441d070341c02c01c071414070145030000c0144175010740a4555054a030014000c00c13820350302020350800031040703032010000c001800519070914282c1c10340d21007074903074080142912503c1d042261312584618019103e4501801808400c030302c1150b1000d10075180c248402285c2c01094032684c1c001d151041c0300040b170a98481c07604507102020b002004a4250f520f44003825411610f8241d0152030402092130580c24802c0841306 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 151621205 1250 151619955 151619959
    0xe01020f0405061b03030c091813020f0103140c030a0e0609150c0d090506060109060309030e0907230d05070306050102101104080102040602010504171204030c020303120703020304060e0606 83
    0x1c601414042400596848015060070041450001c0d0b11880c8040c40a18002c0c140407604c1c96456201c18104016100d4902000c02045800e5040c0541c407000d05003500c50b015030540304188045041c000582c0142101301d00c3c50b141026140402c604403804600a6224030750882d420006801e0b6070750115540d10040301e80340781581c4045503400308032500e00b110325485100d26981c0c92030100035050350000e440f28044115590384c407400c14421550303040310020300500f41c40c0c40c0400820203a5100180180702c0d02c1007003800b60700710b0008551041c2c401d42e00d01c080114048000b00c0c1b1800100803004140c3e00104501940391303d04808a0015442402644100c41c0164010501d944403816440002c1013000910801e011080000090140302030001c0c000401c450780002400386440c3c2008152000e54090341002008104088540c810602200e1740c1c00c0764051400f19010a91440800d02d1742c4101340340c0c90000342d4403500704000c05601da001903200321302c1114240208a04403010175a11141030f1f1350a5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 151622455 1250 151621205 151621207
    0xb130b010801092007120f020d090504020723030304030807090f0905101a09092212110304030f140d02060604090606030206030112170301060909090f060c0f030e01020f 74
    0x840b204158000413140c55140300f4155801a41039005102548400000c80d0f505c0c0140009524990304a207904035540100d00141c1001e50802c44020884078040c0a000e21a56000c07800c03105100c10f882e0959010500751110313400c0d83d1081001c4c20f0f6203402c212811400100c040e800034103064030a041c040111040102140d51060038000000090b0100030055201440044d0000a480d48940007800c22598651030701c0e40d451080206201c00000003c0641e41c103400d5a4228038801511030101000c00e5820042d04410441d60341001c40307032003008403881d110301d220100d40801130018000300c00781002e1081102d0140481000c4440303444a40242442001da0003120024000b030400e44c0100d18064420704e4001811a01c07603000640700e0700b081c0c015401ca9040265008100038080700f20000001609106a0466143c00d10040c401411b034001c11290301e0710781c0750090800040c0c100c43d016542d48214203000c40c02c0711400051400084800700000642001c500100c1180c1c107100320751020901070001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 151623705 1250 151622455 151622459
    0x90706050f07020d0323040602010b010804020d02010f1403041b080105070c1209030c1509080f0604060c0903050a0f030807030b011409010203041d0402041a0906040e030d0f0b130b010801 82
    0x3112144001138268113208422095403100c50808000c6040ba10000150176252420100001c0c21154041d0070107050158601c18000980c0e610441040801e50910f068841c802d42d0800031a4001a60402441ca100e00030040c002040b203c0c459215084a00c03a00e5030030019942e0094a09841d007d584100114800702c0f11035000c19504410101501000d06024070300301e50782d50303503034505050b070342e20070780c40e01c08044d68512203160320080c0000100000c4008040b403000c0c0300318440d1101405840240039554469210050074014802d000c015600101520358241c22400c0804001c0e414041c200d0015217443d00060641d8000e2048100098060392850300700141540b03140403c1d800b00211a040d48002c4c880050402d0f4444040840e00c41c408040d00111b04017032051005640048102240075001c00141c40c10b00d132100050b090b032060046031701042c1b11010030101801d44c451803012912050801042c1c2000c80900d0700f05005a810503038100c1606404151600200e6402ea403020b80050462801 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 151624955 1250 151623705 151623709
    0x708120414031206030115081203060d02041410050114070b04060f0501081f0525032909090102120c0304080d15090e06010807120309050a0608090706050f0702 70
    0x810340c05032003441c1d100c070145100004680741d40c0040181d4003040d0081010018142000c6c02903255580000900260b01410302800760f80f40c0400800d54405042c01000140c0c1c035985901c802d668203600608101715050f45003280c891845011602d040006426000c0029107500c1074074645a40f0032001c49142c1029000d5540c44c09102021708140c81c0603480d0400d003c4503a860f44501402400343e9401019400d81c1e03507403025000e885003000000300c1b6192400b001844c41d004002c184c5541361030800e100102c80e80610580c01000c500c3c043d00c20407038cc1070a0a0003601d0000030386190002c2c0448108a1590300c3c01000350a0f4450b5564041522241401240c0084002c1c0d0107185c01621502100781801000d006500032034508a01c0d2a5411280280400a80d125807140800c0701e010300010340025810241e000390355242c81e06c52010320302074040d140d03c241440f80f81d910f000703000000c00714401d281d84c810008100160507200002d250048d088000b501900803001c41c0c103004540e603580780c203103a40750702 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 151626205 1250 151624955 151624987
    0xc08041707081b0105040b150a05010804031803081b0a150209012114090c0109030311010f11070c0b040e0601030b0d050f06040c061103030103020409050705060c010603060c050708 79
    0x90840b80d044040c0000341501000342c0f050750703425500c0d00c00010285030608180b0f1550f5030282c00c0c00b4072000024030b464407a49520a43e007056840c00e00340090310f51641d00d002c550181050760341d90b03607080178241c002c0104003410700108010b0f1070307641103612654540a080d90700c0303000103403004280181c860244070303001150741c010341b60185050400c0300c28055070a41c1c90310313a603c003c07141e4003903660343c4e480e14000e61810240c110f4004010340001e00e0000c0d07032000040c3c0654001d01010b414000c1400d094955600b0940080f42c19001001081c406003c5490340321550303400120040301d540c0e007001001718440703050780143ca040314004035120034991180c90041d0000e114949400e6000010308141501180c4c04000b1f001d81c2181110040a83c0d181038284240850041c1d003002040006c2c0c0f1054601c1c00200109890650b5011100010006840e2604528000081e484645c014901042e5403c01110640c0400c040b81d0203884240200090304a089610f0b10500c0d400600c041c10602800c030414184032 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 151627455 1250 151626205 151626217
    0x815030a1719090303021506060904050901020903010c0305092407050903010b061602010806040e07031407030516030303140609070c0c08011104170d050a08100b1209010c080417 78
    0x18980c0c98501e582101c1d50740781e0020789040001c03c807210340410405904001d1800750709003000d01a43d85040841c0004c030b20307206000480e48100c0c3c44c0c40128001e02e400790304443c04110b008000f005a94020324014001d030800f00c581504501401c01000c190a00b03400f100880364005546d8180c00780e4130403000341c40b01e411401c0c4135501136690740040201621400002d10304500c001d90462100c2c60b05100042140c00001e085038004c80c10544000d10b1203100040400507603900c011019140307031014a14901e0600c4650000e8039501c40c0d40b420988402d0f0f41500c403003e6034040c1d5001d000918107100784903042c01059070020b40240e00940020122485410380c0300300c452044041210342940d40c0d04290948100c3c070b14aa62001c00040c0800480c42030328407054400101c640036102c070801044014080d800b440890341c060096040000b6044001080b1010140c070002210035141c02d404c04011705000c1d030445084559601c0e00a0035081d40c1c2c0151100c07403081c2d42c0080700e10f4003400302c1e0880c40040e400c24 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 151628705 1250 151627455 151627493
    0x10507021c0204090b060f04061a0703170a06051504050f100c05010e1e070506030604020f040e010b07031b0c0b0d020c06041433220f02010815030a 65
    0x105510401030307586010740400940a00414607041c00e06c0010090040340503481d19100c0c078a032240030010754129021003100c0c002840401a111000d07800c0c2940c40e080c00c03688000d5180c00303404c100f200c08022030b8040c20a50380305071090f18450060764801c0d951172080e4015103501c0380e00440c000300300e451701036074104000c0c0441c0781c05e50001030305607101030945090003805007154004051103820310021000000e005113000000b001440e03c0c0030003041c0a403001401c0316000b030742c002486141e0706a540084600818251310411440e41c3c0d5030071850850f4202c80003c0340000c1800400340149980c1070300d44100d581d000440c1d0a985441c010503208240e018980744285a6001e0082c0c054228042c81010b10903400b40810480501c04118100d0a007030080c01154000f400c200c0c1502a520702202445900c844002e00c1c2070b10944440446d120903a0b00da0302c151541110301e108001c10440050132041c110340c07007a00c4041007070712001c100e550312005520030507403d03520101c0030b8400301d542c0c0c4c2480c141900d40b03 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 151629955 1250 151628705 151628749
    0x1106040b041a1b060601020c060406090b03181623010512060f0d15050a02030c0304031d0a12121e0503100f030b0103030e03012d140a0c11010b01050702 67
    0x1c1d1450000d092004100030b030b0190012002c00178196018003a852291008441c90307440c103400c101014100134204d0150500d010001720016469495008283e184000d03090126103048000d0140d0185107415809050352061210f44020700001c10a0f16140320850140c43e803034141500c074144030301c4c0d0201c0284040e6110400100155150702e842c0a2440100d019202c5658181110000304059a402410742900b06104108000700c443d480f00949400580c540b828000c402504400d26050300001c8030455401500b4442c0000c441401d14658450140316001c0804144c030004010742c7c4005240d01300e078454841100410886910460045900c01c240000120350552034405040b0600081d4108407a1424401c0050081c103070002c3d000960381e01c04400074801c070520030341c0c01c08594a81d602449003116400303000c1c190880054020420904500509030301c94509038a41740d019001c0b802074400860070f6020649426081802003140d607000684985184c00c185500b403040b644150b00c0026001a0703 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 151631205 1250 151629955 151629967
    0x81603061a040e060303070201020a080c0102040e01090f0b030105091b0d14060f0f01031e0317040305040f061b1e0b07080a050c0a09150c0510091106040b041a 70
    0x700d22080511240008a4807a215400d007606180d40da00083c0c5040d1003035009008040050b070340040c00c3c2c0d00265200c2c007150745030b41c0540d18041c060301503500580784500820300041025019076121b604411743c082c000b400302e5180c00c03007071608889040c4c0c1c0503800b036004100e81051400f45c4004a21181c0d80190001125039195140c000035402e00f14403000c06031b0005802d1201c1540700c6542560450610b090800b66035245641c0c20091075250050301c0d0361040c1c00181c0c0c600b494041d80708101004880201948c862600d443c001f4440d078024025081d00d10300200c80440c56621078200c102400c5241c120746a04058292640302c040034512a13540540320350105a100042c240040340f900901254441c00341e10b05004103108140c2c0d200501c2c202c030007603090107069209580040d43c84101c4030803a00c000c100350f00c0e840e001c43d50b050084101a09510528000c40f020450951014646c680110b081d460010481010004d6604c25441100b44034641803000340b2450845c0122030310600341350410751346040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 151632455 1250 151631205 151631219
    0x60a1107030501020304020f032e0b120a050d09060507020d06090c0608100e0402011d01091d0420060d020d0618150603050c0a110712051006060f08160306 68
    0x1944541040312a0f94003c414807046007060b00075901c850000f00c000e03000e00445045010b8072017080140c007100c16107a001201c80c40c6480b13540b0140d40c5070f40281581344440101d9045942e6940b480c50101c850703106011940c0803852146150200b41c80042d501e040c5888219020071400746450142555030554904204002800b409482401404961900c00d403503c0c0c290408442600d041c0d0042c001ca03042e0004010050b80c1c0a0303810302c902d1320324101c9600d80f40b08002c0100c030781103001d8101c034844a070b00c18000b0148000414500748118807031119454507000005d4260841000140e806401c100280449003201c880c039000ba00e034881d11030500180040e82e601901c2c00f61415491080e101301d0b42c40d550700a46070389050881d0301800d09070409006608000300e040c0c0350f92051b5000842041102d00340c49400520074005200285508005210304207450304109461300362184416000c00d142980024540b03009400d2402c048069071246221542e4000340002000110000d2000b0945e030381202080c03103 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 151633705 1250 151632455 151632463
    0xc03080a0e06070f09050301060609050909012d05060a06021e1f020a032d11090d050c030609070e160509120f0d080609040602160605010303021501060f0806060a11 72
    0x3e00b800da441045048554201600690458200310f010742d040020500c1030039005903031202103030010346101d1540d558856000e4014940e0304d0700e1070400ca0382980d1050b48498202005104480082020845a21403030100300651f2401c0c030a42000d80c00c0780030004414204039114546da00000416202400c50451540411440f1544050400c590120300790f042d2680c5840303a103000c665020142918200c411010500d0b101860b100c1e400403546400b0000400c00c0e196040d165a01c00c003920034480051180b0b800c4da10740085081960080c860140020a1003400290090883d80041c0c030800103615115044c21007506400785040620200f040b0310f1134291a1410340c0e0114040b417802a00307101d41030000c030b0f500380400c1664100420105c1814005565544516203420980c406001652502c00035880000031864000280800c0d18000000040c1034000c50f040303401c20981c2c040c21181d070389c03076100c01e613200d012071a4070f84001015080010120700305080200b20021003030519801d00341c102101c6c1490 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 151634955 1250 151633705 151633711
    0x40806010b0a03050108030a02120a0207030b0411041104150c02010905030312010603180c05090601140c0106080105011706060415080109110f03030c19020f10021e0105070c03080a0e06 81
    0x41c100300142c42401e41ea4180300d8240940109805989000c441a1000f940c450550554007000b04000503407031300542c0200007900042d5804014007402d49001d0801c1c80c0102d01281c45c13140070794285020b55040c00c04641c22142074070804c01d4099114003100c102158441d07940c07902203050092a18011400c3d07034041024040c40c111110b03c01c0010760410a0060590b0a20700c9015072a844088005001608505c030400c280c420170380300d4462603981d480c01294140546107101c2036401000501041d0903c06400182c15210444028030450740d0b41c00741c40c000c13650f0008c00308001d07800138000300310303103181070f8100030400342c03a081102c207640361980c1c040c50849540c603104a034081e00c501e15030025030420704510645100110080c504201b000c2c05656250f600007405ca0a0701441000180115030341c0340d54405001c60b0107040600c07203443e90480659200c10150050b00014a183d010081c4942d050240034815031465482e40e0b01c1d08402d030b4090300c1c0303410041d21152f0000e40354050908070040400200d44 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 151636205 1250 151634955 151634969
    0x402040e0103050d0320040b1c06060207060f0c0b0103060b03010b03010e0106051509010c23030d050702010f1a0607150507230c07050d0303020c010e10060909050601170304080601 79
    0x14044480600c003608440d400c02c516044200070031804504040104262400c541d403001020f6900c1091105916a040c0040c0781c2c0e24a4030700d85400440c0300359000413100152000c2c1d83f100ca001880301c01c030a0302e0319401004001e01040660f001440007070810340111038100e601500104280d26200000303425110418083c81c8143c1d940c0710304004516000c0032006070211080c800515048119000038a01c1030940d10161520601e20744003c0d0842000840360360305d841100590f51540d110910b124007801040d64281c0042d0309010401d0200040b902c9091204e02c42c1ca02201c95001d02c003400c1c07040d0350b00030714002d0b5084070001d50404031440c40360044c1d03403048070b16a44121a03401e07542800d0500700070104020070a950140b001221170400000d45030150741080f5003060803030a03949000c40291042c4040b91f560355003007c6116060810004400395a031400c0340041c410702c1c1e255444a42100d12580025020358000c0c80100415014285501c0c2501511070580307140c80d2300c4413030a910748032081e48955 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 151637455 1250 151636205 151636213
    0x90c130b030a0c030321020f160f0f0c03120f02100c140309070509010e0f010608190e1005090d0c15090c03030e090c0c1b120d030209040b0102030a090b090402040e010305 75
    0x500781600c61007034906c803a100b10304504050841314004298018056642403124103086c1110501c01d1111603000280d503c494121080d08051500f03001020322807101b00c81c04075003010b00421030b501032480000200580c0d4018519080c00a54050140031360002e511305114203a1461590507181000840c03181d290080101b89440ca407100740310300c1c03030300590042851710104411310004048081d01384d070440352a0320340392110307440d414070315108410610300e4840702070301c1c010740c5500401d004100b00a40450b107580400c00c569544c040300761100d286080c10000600c0000d15400041c0000c1000048074400e600001100c2800d50b41e0403440710401d400580104105ca01ca6115a14100310351680c08600740e0074460600c0f06199850380e60703154109940128083d000c1c0c1014482e1594840e510890324050308031000410b0060014000b0740c01000f655000764100040c020140d40000100d80c1c0c80d0082d40d40b401911458007080c112981c22046160380c1c019020480086c044d2075a10046000e9030281c0098 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 151638705 1250 151637455 151637477
    0x905010e0c06030f01092a0c0203011d0a0303020d1107080d0f0b0907110c0a0f06080109060b0a080405030d0f14130b0106051803010c0905010206090c130b030a0c0303 73
    0x140d2401e240d80e88020302c642010001c02a0b1000001a2541142c0d0210070114084502c1400703103d114a200c030426200403004c00b81080c201c4e500c609042c5100e0700a0307000f000702195100740c60b04c011030841d40c0210341c0d911900002d000a48603600400302e8000da514000759044514141c02080c0d070240b4400d55000070b0100d024104c44001c1e104002c80849904402c00041d60040042100007500400c80020f01041010403110307903205000310500d02c0002044e00824a4031440100140140d0340944800660914000700344180c2c4c5120700380c2a44d080c90540f034101541e0f20800c54803404014011644d9010a2000c0d040041640c000c903421940e100c1c10106104000307101c9005c0d4484005c00340103481c01c445452a0101c3c600030401419101e0034981590344201d4600c210041140080b18141c141d86405009185603610210500685074240e00703544554a0345c00c00540d8550110050550001c000040441400d1480c0d2100341400406400d48410707441544503200c08a01c0d40e403054010401c08050 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 151639955 1250 151638705 151638731
    0x102030108061503070b0c1e011508010b09010302040e0f030a020105220b0f130804081b060a0816031e0501050a060f09050904050c0901030f0b0f070c0b0415090501 72
    0x1400c3c0d03100c0d40341021010020082d00c000391340d0700301e1441003110213800040d010840d0300040c406005003602050003c03002107101002c6a008003c052208503d5a0381170340041010b08040c042c1e0842c0e031340001e1540381181d00315000c01c00102a0a0070159051244010690f8415824009408007030700b903400000c2c9070300d000310360745003c411000000c1103640e10486820f400101400d8032590005692004484507a03152031044100b121315900c050900080440c1c001903004000034154524150340984450503c3d00400f44182401550700031404241d0502c0041c40f0400d100041c04111f0506241c007051001da048003003041804c40c8a0601d0155031110300520507800c10000e01d500410342c620b4101c203c485090b02c001d111084074001c291080c041c03140414140b240401c6400c070b9007080201140001e595078038200100c2c111048084400c400103800140c20308280c0d0a6091050380207440d9155840c41c182c0d01c8220840000304100c40a0352656171110002d0741c3d81c811040218070070070002450b040f031000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 151641205 1250 151639955 151639963
    0x50a030b280b100516060c090506160507120c12060906050a09140601081005190606090608090303010f12020d1209170105060d02060a0504080a06050f06010201090305160c030c06020102030108 84
    0x2000c5800d22104001c100c00c080d8a8000e05c01c6190f402c900e00280c10300708040125860074a60b40684c1d0300010100e1102c0000003a6107190301000d10130030490f052146c0c0d03034074130460766110100050105540004200075000d00700820b458000e110b090001441e0102c1c2c4c1d5284c00310b540a0f10901d490340d56403012a070801814281d49084582c0200c0200360301d40c5088206035035100304250004500d61107074080f458200c00546070f5610355022344014003007641ca5010051581710710344900c0e000918120701254280c6000700c2200e060b03072041e1500c0c3d10811704003191880d000c540200100e81101c69081030001281d0010006030301c5054968640030390a25120500c1034030800e00d013003c00180d14241c02d01a10781e840344028442141e0545016842d0744c488a0161218001c5a200390814020340382030204101d6941c0c401485058a031403007010f40d40742e0034012400c880c0038220050107d0001c0091f5418140007000c5080c56602c5442c19070b100c80d449950b000c4810100380d0000d00940c0d0040018091840180 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 151642455 1250 151641205 151641229
    0x50f0d0b0405190f050c041a0c0708010507022103011a0d060308031f05030c0d020a03140325030c020103020c010609020c06090d021506090c1207020a02090105030106050a030b280b 79
    0x70b01c04c1c4078904206ca000603145c0b243d8401c8034031100d00079503400c2d6010300700c00a0b10a80310140f4242c4164694407520b144c040c0c201103904e00014010304068200c1810900020141344180503540c5065a00b4003521104e460010750f42c42100c2c18080c44001c18403001402200051841100f41c00d4a900f008038400035012407145162140d0180000280200c2d10002440a050300048600c5101950382d0b0012400c2d005442d0800340507181e44072480442144000010700140150b8044940d070b4603180750311000701d15400c407001070000d00c400f504132016610035005003030303140010000011007554850400080345d004030840121600800c007008034142e810300000c2410a014005401d03c00c01034400c07006480c000a120301e00c2102c214000c00d82d542001e005440410841b150210000e00b0061030103503540030f14001c100c5c81100303180d00204a45c10180100070849001034005200c070340c2180c2c1c0d05001d0302c05c014410785d03800200c0e03401313400591040c22100d90070400072140042c840440c042804581500380b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 151643705 1250 151642455 151642481
    0x60f030a0f0c170307020402070f050d0207081603050c09060a0f060c061109010909050a0f060b1b010e0d030b04020c060c0408010506010504030803040b0601020a020303030a02041d0403050f0d0b040519 88
    0xf00c44666035000407040790405070341141c00507510540391030040d8032119050000fa001d032255031400f034809a000183e41e81541c00303003400c4584c203510b040c1c890344c501d208602006140741c108150904107410107202460b00308200410f0010842c4e11070300101d00181081c0d10210000c4c03912000740003404207904c28010540008070015207407480b1540068040246032141003400f580c0c6000080f42e4800c20340c0845000c00701080184101559603004e45c1c9590442601d42c11818a86501d1040182c41442071110010000001c0c2c10101780c020010360007400c5005210ba005a02085003840c510000d2003158031074480040d00e40e0301c2d507040c441c05c6405c540e002006181402401c1009002080180043e0707a0b129602141592240c2d580d840101d052031100070000b0b4240c400070003804150301032900540255a810344655403101080f508041040f04103881c0500415010009410211907410080a4003040c03584003180f011020004030303088404c100d0308010140741809000d041740409006d034a0398415a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 151644955 1250 151643705 151643729
    0xf0d080a090c031509080f070302060f0123010215010f0303020d050313020d02060910030b100804020607120203040b0a020114060306071e1103160303061d040308060f030a0f0c 77
    0x580e40d40541e00e00b181e0001624004820f58100100811034000844103076100010940301e050341038400e0515041a601100540508400954180d0315004c58604840000e0441c1c058085d41515001ea1200b00c00d071500e0445c0500c0c58001e694088080c091070003403140c02454440f0a10311706000b41403101d03002401c81081003c101780124007841009942c10681c04840d050380b030030360910000b242441582c40903500103041132a007012940d00356100ca0300d403140540c1c046540d1140c42c40300700c40581080760000d600000900804c2c1c04116542800c079120072450040343e10f17244d00c40400c5c04840d0001c000c00300c0183e44445140b0b050411285c486d54002000340d00800d140c1c00c01d80405003405080340f000045007203041034a200010f10802040c4003008800b0180d03941c03451010305148102001305800c0e40881d007030900025205080345a0100a45551054049107495a5400f26103028018026980c070034522040003031155001d00c0400001c52050b010344072001c84510f08040900420b9000c0e10b1500c04e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 151646205 1250 151644955 151644971
    0x703020d02030f090d050304120e180411040506030c0109090f06080f030913060e060d110402040e06030d020303071709211b0303060d030311130b04060905040b0a090507020703050f0d080a 82
    0x8503000c0c5110400828103002c2c0320ac1000d6400300300000301180120200c00201c00502c01403081c1218501d009120940b0b0602803951180181070b47d0b107100b51501800500d554108200c0500c0d03aa0001e03001c2c000480002c05e62680e1509100c3c5449141c1c601051300d6000000c152a440c6802000b644020150440a000c02407500290b1603040304011f12143c000c40110000400300040203035540302d4018000e00c210346450325142c1d0032030340d008111407a41c001d108041501b5280303400002901c3c0b2440042d40c3c0c803182c031a900001c450014070050566010341c0304414031003040e040b84810500081600700f540c941c480300c2c511401a4112408800039007203400030800d00c2219158001c40803855034150a004c5180910110180c1c3ca0b0b20400c1c4600c0c103080040c4402042940c01e00d4000d00c101c50b003030343d1292505034a80c0100b10488004501030365010341c0303c070800c02541000740c106551040484c019144056603e441311820720595284083e50754000740c0d9626140e54000c4c4095801c020518010003000c1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 151647455 1250 151646205 151646213
    0x120d17040b060907030912020708011104030809060f04080a030e04050601320d110a08100e0103060e0f060403080612070e280609020301050a1d0a02030703020d02030f090d050304 78
    0x6a40680454020903d29000505680c042d80004000a91003002c114040d80500002034030740003d409120025400c00309181503440c9080c003602c041d03035009858140750181603400c10406a100d002c00003a1800d0920000402074418042d03d071103903000e07403a54001189550300b0442203c10043c6113906011044000030384c120741d148000e01428541207607104200401080e410003d018401e034000010303040844100c84010b41d83d001c1c0c21074512544803808151907180000020004900842c940c030092a001000030070301541107105c010800d0000c6e20702c071401d41074800e4207103001150240c0100310700c0790034011182813030401a0300910180014100382402c140d0309604003640541100d003402e40d298503a2000d034074182c416040c07880d80b20208008180e0344030f8001001c0c1d002407284070b2041018200000b0b0202a0030380d604075412164104940e0350341c1d0786000d0002904080c00e00d03c100740c0e0070b0240d80c1a41c406840154000c0d00d6444000b0a9407401d00d01403072034100d02041600c208482441400005 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 151648705 1250 151647455 151647473
    0x60306050a0e0606040b2404050111061b1e270303040501051c0e0303010f080d0509030c010305040309050d0c14010f020a0f051c030c1e020a020904060902120d1704 72
    0x46401080b06c0743d2000000e6030380007168038a400c8060031681c410819201180092048a40c2a2a901c0c0c82c080d41d26040ea44030701003102c09004071803200708003641e140600801040360340d140300040c2c140443c9038041150b40741c2101d4401602c156100b983c094151110007440c880c4058120000c41c034003410200002c1c40c600034804200e1103648114105d08480940d5004605444011811aa106e42e560411007a01515520031b6103803d0182c2180c1d85903035885041210301c0d0440103001007400c3c081d45001180100002007080d0100706101c40041340b076a41d040c400c114824091010700303401500b04685241001c4003c540c2c1c1b418090f401c004a50140d0700428410451904034902018075101800d120341060702c4607282c0212181d03800012820990103a00002411280340c2d52241c0414101c0c0060101c03031084007805016a0060170600010324000541d00d41c007501c0341e44080b58194040d8041140ea0159080d0700c0d81d02e400c29860700c40d103542c1c440d00000e1215200d0784496641e090030340341c51801c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 151649955 1250 151648705 151648711
    0xa0b0f04090b0a05030d081617010501080405120c010e1204031a0414101a12100f110708120c04120f031701090c1b0b06040b01120c03060306050a0e06 66
    0xa01da00da52100d050356850070320741001480c001c0c0617a55000e01c918001000c0041c1180e0903500024801282480706218000341e8811a5805454032116400e00d001510a07a90050045440740b06045844051000c46006011990f595030000b14104a205003000d0900203841c0805110103c03c4c0420000b0850301c030740c1104e025944103180401030300c41c0d00b400303400c40c8030500c0201c02c50701c11411000e08a40345030303205e5098140301c1c080c184640714410b02000002680d03100c0f0b4991650108041d9201c408050b40820640383c1290f40014290004059141d520f8005100035185000041421100b00700440e40b2140d000f46400c5c2a48d2030641040c60350614441000c901030107010314624580101130042000b144501044c00722042c8640e03442065102801325031400100180b08040400e000092034049c5000c025849800035825030b40d04003d02c001080302d01c401604000e80342e4a4118400c02520458468403800d40c0d002c622142107017044415070310081c0003510703260f142024042020b1400304100303030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 151651205 1250 151649955 151649969
    0x80c0906040905100204030b010518070c020405090a05100e0105010b07050a0b070509040504060f0f0c0503040f02150403030203090102010b0f300d03060503060a0507090303050c0a140102090a0b0f04 87
    0x8550200d030402e44d150000d14400c180c032031071000401000780506400800c1c100e0704111a00c4000d03d1030101c51031660745044d01d98802203178074482080014613090b0842544150414115180641343d03440766440e040102105003a52591403040b0b00d2260402e001d1a400760222100071440c0400c00d60f1030755030313031000007a015161070342c007d01145180d0b00c034804a031380c1690002c02c02d100c00d003018180100101503090000b1059484d19080d60707181401d40c01580124a003036213481d41580e45a840d1015000042036013281e0222252a400401295901c0a48007840c00ba42c021038481c041c01002908444909070000d208001c0c608401c64103540d680555a80c0340d89a0342c540550320040100260510305090a0f908103010b08281d80e0245d42c1d26a01150031944220112222600c40540c81c1c1c3c2220025100400000c0f8013420a00110b070207900281401d500840840b080d00580381ca074001d05c3c8580d24141b43c1c450350005804902441d0815010000d01004501d0130314010b0020355100b91403255119410f = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 151652455 1250 151651205 151651211
    0xd051f2103120c050c0d020c0f1507050d17060f060a0e030708030c010231030308040807210e031501060c1406100f0b0702030a030c080d09080306030106080c090604 72
    0xd0109485090201c1c444480b4580030f2180d004101c00141050b0400301c03400f00c01c0d12030303160400310301440003440340c070b120720003070100c3c0c681c2483d80c02440140c112054042564690401c91100014410403c2d5100d08007607035114040c80d00c180341030105d00368010706000e2140c0300c0c50400b1003160359284229203c1c6082c504040070400614000310b03081c4030841e4030507040c5010100d4603070200031040d0014880c001c48800343d81e40611414200f0710b0044649200c0245083c5c1481341400001d002c0c14200b0340085c0a401850300f04085950f52440c00c400000401c940380708161000b40e00c031038026410501c0e59400314043d01d2020218046482034007030502c90308042100241102c41482201c405c50108030104005451040c0780c00b01c40c00c0286006072280c40c1d03080700707030400025405060105941c00c00e0b50060150407802e81d03540f0101e54080446000741d6418104001075000c0050034460f00b07401d1881040c109440c1d00c0d043d803c02d400c55140e64000007a41d004100d1040c0d60b556800f207a00d07845130040ba000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 151653705 1250 151652455 151652519
    0xb0f0f0f01050f060d090f06150f0f05040e0a060509010f0f090b062404031209050102120d0504060605060a020a1b0305061803040b03010b04030c2c06150d051f 70
    0x20707108a14014021001e101d0014048c08200c3e003003213034001400050a2000c0750784511801046000d4031804520601c1c06006108038600f94016410b000c0d00402241c0d00010a9214002180e0003544c0080c0560f540d500c0d82d20100543d0b000341c3e413000c400c4960070083c1040e2900c680e1200100104031920417041107102030f1841c0000380c803440503903d50b100c43c0c0d62115100d11308408220342800700d05000c1403401c40c000520758400541000d2203015190090b0500b80c4d82e008a01c05070001a104031440c1d500d40d403003c50a921500003030306800159170b0080c56001c41604041403406211400003080c08403800b4140041040041c1c00c2c0e8100a220a00c12031000b000b294031429409217810505060740c0000000698007909400342c01507070b0040c3c00c1a0b030110790310340c1141440d2031341c4c013144102d05508072210001480071208450380048080c0c0445000c40704e0381c801c4407055000100e411011607459091011450901200208080f609020600e0341c508044140240300005180c00032006010350007 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 151654955 1250 151653705 151653727
    0x60a0218040914010c0e0312090102100c0e13090611040b0405011d0a0e01030317042d050d0306061803050601050904050a0f0807150c0807050a0c0b0f0f0f01050f06 72
    0x200f900210100710007040203003d0301d903004062204081c001486403082000410403101108212800010305030000c0100d9807010610070041c00d5407020100601125500d500c0b0540c59120169154541b030280001e403850f000e01c0c15004603a5561000c58406c0802d020600221880e0821142a1042400e02c82d0401038000c10003050460000c0d0810740240200900103003114003d20210f040e41c0c8030740c982581040b4019400320344c0103401c94018014010f8207007030580d01e0b00800c80c104c0250600440001d450600c076103c1a2034425075241c05d8000942d2030208000540e4800d868212224012812113121071842d15000c0e5900010300510348108100b82c0840d080200401c50030103125400392400d144e200742810b1604098010a100fa9030401510f43c403140c850400d4403880c0020307203003a2501051031710360031000c5405170000c200e000103004101c40c81001091101c1500d9200f01d0074030b40101010b140084080004130070140032001da0344920030044c41107030b0300c040000015400a50318103403a0005005 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 151656205 1250 151654955 151654973
    0x21315050a030506040b0702030c0705010f0e030f030a0207080c1f09170618010203130b09210702150f0d2a0c05071703030a020a020c030d030608060a02180409 70
    0x4401503000741100000420058081200e921560081200d08025501e848081e600d034454403a00356000d40160100744565805411508407810f85494803404080590012910b440550158a401c541c40030482040d90b0794100810006041804098070f0700c44000008500c1c403a507031030501102d001c025810100003c0c4a0914007008210310b0512004480c1c0c107281d401c3e1a02c1c4244d4100654044042c000300344030740d0500899008841000101c090b6202c107440304954604090b03c0c2100c5801181e90740031528521107001254038104065059036110903104201d03c0405901a00b141520140301a80c0aa000001519490303444582d020403400040c9030b0800c558074044680098500c00340b40031128503648040340c079407210710030400c9403041d07619000c0f141842c0c0090056403102e54410000100030714019005040c1c603031602d0044490f449450340010381040e0b101840b00000960724407040041910800c46950408122601180b03000800f400881410f0410040540243d440d1b0b0600300400010340 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 151657455 1250 151656205 151656209
    0x2904080d150906030201020d0309050a030c08191d0405010602100f020f030412030e160612060e010b0705010f27020a09150f0503030f0306010f090e01030c030b070309021315 76
    0x4001401241c50b200c00d4002401c2c0c41c082070340180310301c04a150b4130320f0281c1304124200d5040780c0144040c1c1c0d0b882ea011514645400411120b030f400611550b20401c4020058060700c40c81c03a00c5d074000841d80005040c0d20308200403107040c8202d040c000100302d201e4000c81c2001c00030381c640d0400b0691144150868002e8850ba9609555103100041000180003240c845030a10001560702442007000707801100356104101e9070049000384007403a08212150283c0e41c0700019a01800700426020b03624001e0320140c410903403003840046c00003d00300040150038031400c0d018076421501080101c00228009028046c850070080c6510300e00012401959104100300000b0321000005012081700da1292004035036607880741d0301d1620b84050010450b4640441600d8201c8494071a050450ba00e0000458802070443c50704014080014404200913070f03000c10b9940a10b00585044040c18038500e401503003860014582402c02d403400c03403070300016a03c800341c520050a07500340205181c4102e0303a85a8480b030040e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 151658705 1250 151657455 151657481
    0x7051303060e01050a0608070b0a120501060305010e09061302013e07141309140f0c010905010309121103090319020315041502070809100306032904080d 67
    0x84400000c115081d0020085031a07808024082d507100c450480058544030f0040300c3c159001440e0a02c00c81030000b016004090503460115400384c8034425a8003110300030303001000000e44900051020460621807030350040e10310001030031146440524151001c10b5130000a04000c6001e04180049030901c0704040740110a6001d80c03c01007031518400c40c0ca0010398468150390103840c6002860304203410345400c00c010040d00c804802444032200e031004080020701125072040303c1c20b031901424010003051000c0f529002c01032182800000c00902a0821584000d0403d03040000000010b03001c01ca020508420509061115548030107015046002e01007101d6054460380c10044030050384d004070704000d1802074040e104903286412035490b98540072600903144e070401c995000c000c9121980184000f50003136200a040c0050040003980e2010a09184030000303898000070720921512004006c0007952814920950016002960305203440c000e0002e0440c2c1c0303000c00c0440c083c00c41e03a0416468401c107 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 151659955 1250 151658705 151658737
    0x111071226070c03080601090303021504080f03150406050405090307060c120c05030a150b04060c020102010219080603010b0f150903070b04030305040e01140a090207050a0c150311210705 82
    0x6008020300e2103120500071340010f4110390201d480d550180d801c6800341c2c0d4055010305851108036001c0071820b1809081100d0400302004180055880c10029500a0407841c504003036203100041080141da80c107420040c416031511060100068000084480c0c903540f20201046400c0c88810640b000e16414038840525810200307117441e0998001d00861080800110410124070400d44014510025002d0020348000c04c000a0124502500c81080c840d88148000740c40e00b00e40344c1250f007412124501c1100841c15807030074800d00303240a0054045000041e5104000b496001e00001c84610203416081707400e420018600100e07440c240480405040d00006407039039036959140080c8540d01510880200d2840000007060383d680c09481040c1004000340b006c903a060900002000a500c000f6007282c0c64820401c00c00b00041c0d90010305402050414610b40f102c41003407001405951845041c441c01c01410029a0b082803445c43e600c214180345080e201d1020366405400361820b201d01c10703c080d80909 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 151661205 1250 151659955 151659961
    0x180206040801270c0501080c070813060f020604020a05010c02030c03010501060203120a0603030f050d0f1e0f1401140315090313060503061503130f0c06020111071226 73
    0x1205401c40d0100050100b484406003c1c0c2150000c1d541c0700c04080148109905401084030750b110b8981c042c1c0140d540c407601c0340f4040b41d40d070b28014554469041c40725901811582041850703003007040c1c0032042d0484c0c0042d2280f45056800120346000340d0181c581405003546084082d500c00304240c00342503901074002c112a50719084041d5a03604520094181002c5140003d020415140500c05c01c4941c180c550009042c648601915284c00041b400d0a41c00d60b66840c1724008441c034001c00c08140c03050200d0b6081c901030742142034159445804404034860070800c001181082c503000241c1103030104408020800348900010341031030400d04003416641c0c01c0c0c00902c608180d0100041681e40c0d00c03003036850b8545540b00c1040d1514002110041d40c802d1065084800d1400720300000d5600c544119081194200d095540710307580002c1d001c094400d950403a13418000c03650240301c1e040482240100c8141040e066590700c11b07140d148501d48004021803000541c0c403012241e80b034501504070840620940d45 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 151662455 1250 151661205 151661219
    0x3091506220c1107141512071b05011b0809030414060702010207080601030c320f010e0a121a040807060b0118031121151305010c0203190201150918020604 68
    0x401c40c280581c4100245000c560802201c2c0c42141d400400c01c429005081d88d5024040d200c0d079000d004520600d180d8802c000d000202d080c13141c41a40d00006071070030400452444d006100000091580c2d4941d88100001e000045040034000d0424000300c1e1090b59609080c40100c1c2004038940c441e0300948581c10000c41008020208442520010001003186500c0100b28498542103070300c4900305282050041001030800507807082c0000018101002080c1c2a20040351072502154010400c40c1d4840c0512010464038035000d59075800003e00c4155141040e45441205208070b813400ad200983d038240b00501d590003495800c0c6192900c480d4060b5140d80c038100f0b034102d6031a800c5910321919008580c0680401c8040c000512220b1601c000c0c84424070500ca81a60814007401e00341c440c509002c55000050030900030395103c400304d54007450316811800c0192044e141e8181c410350a6905000b0b80c0fa2414900c055a001150701d01c60300400c8101c40000e48555112102c2e5001c0c0d0081c0e0005400b003880 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 151663705 1250 151662455 151662479
    0x9060a08030f0a02010e060606091e03061e060906010f080a060f180b0406140402070204020712020102040f08030c060406051915180204030203031207050f03091506220c1107 76
    0x10b213030002c6c840814045945030700c030306003181c000340e02c207006105052640c203200d0001c001034080c804e0300b43c010090050019140840c2115400c000c2c1142e1003001d01c40c001c407405c1c1150071041c150f56241041c10b1807000648141d2580300c10004000c0303900c0001e1040c14440e040b0800421448d188401c01e5502d4012104000c024410b129803000d040c18081c442608052241c0ca0464180d406a0301310700b0404000c00019600c0b11209907401070f02032284001003041c29005044405c0030740c000581d61450b1507201c20315103019030700c00032450300240001c0740408404284030740d02690205001405503a030720485906803171110711030142036103001080d0381542220450b0740151348000c0024480380a5640c144410303440785000094241d0818841d00325400c0844034025004a21070410301d080115025040c12140c0080781c401129034445034050085c24081c0000b00c2c2c0081d41502c5902c0300895244c40c001c11030480f07803030850800e5965011076600030b01c02c08a282841034404240d03000c0554807030f5141c00d1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 151664955 1250 151663705 151663717
    0x4060809030c100e01060e010905060a060f02030901031512060c1128030903140105010513090305180307051801051005160f0f020604030602120c0c070509060a08030f 73
    0x108011001049010100100b82d40280030801c000b0700b103080702203600c0c1d4003801e00100030004641d00d40e18003058043c040200b0742d002c2e2600d0390700054140380c0401000070510322940a00f040c0103007070001c40a4281d0110481d1001c05007801d0114040c1c0c5521000c8011240c03951045076170144200f101010000507800042900308165517003181010810a15034591719406044840b1241100c0c1c042620b9107010580c00303015000c0d0a004003401d5481e00d8506220483d07070b080c0f03c0503075524401440a031800c0f4020b901c5180c00b46004004050755558050140d205452001c0b50340d448902e45500c07140d41c200b0507000036080c0a0320500c0100c4410440c580159002c0c01110700c11681010020082d42c03191301604c01103c038458140002c041d060301e4442000a1008041d40e00720170041e00980541c4030940140000c51240c41d006903a00a894000e5001103405400400048820004123408840000e21081958000c8030104015192714000482c401030701d034010819800003080080c440740546001c0c081c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 151666205 1250 151664955 151664957
    0xc01090501060e0705040608040c08250b070812060d15090204051302180907050402040b09100e0a0501031d01060303020c0a0f0617131a01090b030f1002210c0406 71
    0x212584941c04586043c1c0300700c42000015200340000c0041d144194805900b0034092450780403966152000030b03080c25071441901030124003841c4841c009072046a010002021140c59440c140441c50782c8001c09445007030041903030800d0380e40205201e0365800c102120069842002120100030460000300900a402d1050717100e2351820b000030720384001e00790f03c07480e060782d0042c060b2804544200c00d02896560141c80d6582a1107008008241d42d115480200080c2c491020b4030b0391250311a8003046a11940314024400700034500520001075110706120700151903090031302050386020340c103030b2003980c882441c3d042d4115820600008240754000c1010000b00340b06544101c0d006464003161000d820745031044000280078041c807000c0b4049100002a0010054030448407065039640b9140c0002c200c4640b2043d500c0c80362001085101c030640301c0c0044164043d40949991a0014002c0740c0f56501e0021047c1c0325500002c0b14070803807541d0075507a0001e43d0901c52240b05802c0100100758260040d018840c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 151667455 1250 151666205 151666211
    0x1502370b16030e060a05270a3305090102090d1109010803070b13020f04090605150109050303070f03050903060a0504030e0d1e02042c0c0103090b010306020913020c01090501 76
    0x8072401e0300c0b900500400450642c0140043d45a0000d004020b04000f0300f5402140510b4946c400e50040c1e40c0040340b182803606006142d4400541441c0b840003c074000c1c005c5a00c1498501401c20310000311003600c50300740c003a0300004c0664035500103501a1068806231903000071191510400c000c80c5041c145e203884000d4402c1c0705144c1e2605001c40c0d90748503554024207500f10902c002000651180c1059808074400741442c0b15a1101034042000d80398540001c860070381c3c543c41002031a010108151098450919000d940c8a20345800b1980300e200d202005000c0d02141d00d1000149070260007280d011040240480e201440c00f80315100c0101000d44040340001d20701da40d00c1907140350074003207038034425085a03500420040c4850410f1a50524807130498105484910029020343c6914101191151002c00340483e01d00c0903000a0130003408000c054103152411500a022404c1e41d0610b505603540008010f13503c51180d00018148134001c484504070b90f0000034140c41c4843c0640012881134443d000038 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 151668705 1250 151667455 151667491
    0x903220305060f13060c0c02100c0b0702061317250506010f0b120612010c0905090603070f051201060902070c090b0904170d0e010e03090a1502370b 65
    0x50f4074104001c0d5650105070b40d482030488049061503100301d00f0b0058908200c90303a015030381d001c01c0b031484035a4031040c00b041c4800c404006222490f81095486135940c80a0701d100c0c58605441d02da030305034588014001c0d003804001310f242101134100710b071484880d5043c450740000d11411032903003403410048111402e0003580c0001440c006c03080e6981040d030348900031041c00c1286940d0340d8240040c0040c1000d501840e03010882e01602000c1c454111500c0d500e50710314069a05000c103010484101420550013940505010000c10752011208025540704450103141c1c0c1b5041002207005d00781d1500001e52071072000074440c0800c0316011148044035100b800030700c038031000c80080024410040758050220950341500b00352510401c401015100341d019400210051107400590840c0d40007059400d096000081c1c099562034403058100081543d0000702c8165100c2003002516186880030742c1c00e4595144070490900e404515070461484a4600c40c01403c000798180010441c1082e0b5816480c0000c09201c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 151669955 1250 151668705 151668721
    0xd09080309060901120209040f0b0a0803030c30091c030b0901060e040f09080d05130f12120f0501090b0a05011722030e03060105180f090322030506 65
    0x1580c8030760074020800c2c0d0a143c203d00044d9104a600411074074416400c1185a26543c0c0358816024260404d0000290720003d080c18490500315540006030582c3c010b000300003444045004640d083c400e01000480703d00c22040028500300d003540b412490754011403081107903c0600180b9038800c080f0fa490b11700c04001040300c0c103408840c01c00d02c030290005491401482658040c0280c0888d070407014200203001d42c0c2070a00c0390129010340c4000c4695a50010b40344a41004078081d2681010740c0d040603003501c002e203907144240d1a01c1100000e15080c0074001c0f02c0f61990040d110f00c0303c40154144148800200d50745541d004101c24041c00019600d04840005a820810407040c1680c0068451144068a815001c203003604e0041001e10f142200309450f0f603080d062070100b294858801e44903800144040e4040504042c0160001d90044507914030b22541c0540b0426090380140020808401c1e5841e0021004c0c02e6108080100c20881c02102c001c9000510020403101181d0240d410799442d91100c01c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 151671205 1250 151669955 151669957
    0x70b0304212c0102070b040b030f0c120a0f02190c14161a090a0806040b251d031f0609110a120207050607030204030b07020d0518030c0306090d090803 66
    0x92540e5142c68000c0c1c0440c1c20b6104044007040103076050048034561a91210110310701c3d4416046521011008070621020800000d081030704100d2055900b030408045045880071110010046020a5200d0f09414107441c1c459044030071026100703e51401003203100c1006061044035400403207010103042e038000c1c0000c0b408284c04a4114543c2c003a448410702e0040c02507290000d003100691550030400941e03907a550b41100502c000c08000300a4602031800e414803040007200108031122585c1c000035040d24612454a002440b803000e400c07c540c180c0c0d809a0f00d0300f4410f021250564040c455207034a88039401e072040b10001101842c210904c10591100300307060640341c12210402401e88140840000103000b1030491480b001210401410300886450b40c070b00c0c081c825a60080820390000b014010302400083c0c4a82c0f100075400141100d40c0c05041c000c1003445810700400c1c0721a84154441425139080c025040101b40080468415040c03240d085130311646a041c402c03001c907500d80f10010745604080 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 151672455 1250 151671205 151671227
    0x902040e0f0c0301150e0607210c080405010305070e040509060a0e0f0c010c0f06021603200d0302031008030309010c11070b03041b0503011a030c0a030b0c0a02070b030421 75
    0x184280e0960346000400c920704046915583e046c03040242e400040ba884220140001c2030292a00c0c0e02c800e45010b4400e2200d20300c454580e070407c9229181da4001c80d06102c1106d0460b0401c0ca000a820703070310000111800604500b1503640030f030a041c28481707082000100f02c2d00414019404100814900002d10740e903115280000145030404440d400840d03000b8003201405900410706039036050056643e000403640030035440340601d074140c00d00300141603001c0c5101e002e50204c40000755120031040c4815981e03035600da000b0820140c00100182c0a01e400403000e00041c01e10108494413401c10078589800703005e4508018000901c1c142d50f41c0101500090000d0403208896136081c9103480e151180b503a280310514058070f00b0718600d2030009140d1000d205445581c1c0301031a8400500700e505c010941003c101d07482161050b920b5101c18004118059010345c3c01116031080c05a440b4040cc80c01da007440802c5d8040003588002004002c10700a4251460b074442d844042c03e4001c0402002059401c1e402003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 151673705 1250 151672455 151672471
    0x20d020c0d0b01050d11060a020a0507050405010b1804020c070602010204090b0906091303031413060507050a050406030f240305060c1602010c020a260106080607022112010902040e0f 80
    0x250010132003420030f41c0b080c8100c2c90145001c02072107031841d40415419801455000d0059025550800511900380200f8010f498200c4060001e54544008400c3c0342c0121100b0414850381610800100d80d21036045941000b0b0010907210010742c0c0e100064000c0d0030034410640141d060043c8070243d882e01e000a0380c400d05004114684a884000040880311900d0b00d0440a040d922283c00551400e02c0084034440e142132242c03c00c040c4103034038184080da00e020308a44188501808078542c0c0c15007040035103042c0c4056180006400d02e0f0614400b000e000030890040d0001150035141c40c1c2c1d022a48040d106581c0200120364a0303481c1da20540340d1900c1a00cac004661a42e14007280c000543c800d0319001481070004200c83c450b5500c621081c1c0c01c00040080ca491030122a1044100100c000e0150100a150402c0a0000703490b00740c4000c1c0d02d54856039044008010002400c7ea03051540805a54950b002000124106e40c0c680401c1c00003980180298a106400f1000040040d000148154800ca2107 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 151674955 1250 151673705 151673723
    0x302030a0b0c0705010f050603010c020c010206011202131b020f0a030806130b090f070f03110a050f0c0105010807030311010504020d080a09030212010c030507091a0901120c020d020c0d 81
    0x584072142000400b80648035800800c0001c071000c2602402001c0d14140781100000311030412000701400c43c2d0341090054295001003826102d241e030041442411940348105003103001000b4800203051603003104101141c640381101c644c01d1241c08007421540003210b5001c881050305124001f642e00c1e841c0c1c40d0f0040c000303214907000694904000c2505080d0380d10080c008103807a5a102c00244d1644001c40d05000081d54040402c072582d940014030013001000c500b420800c4030129403181e05c0364803030040c00a040c000b0005030400f4503a46001142c4c902d500000007005596195081d09403950154130090b80020442c101c45079540d00d040c46420300441d401003980c101c7c10060340ea800e140790890f40e4514240701032400e0000141c0ca412003003c1104c1701e00c03400011404912807014044880192a0104100010b00144400b646203407112143c5a0412401030310380fa20700c001241c0c041600c0d50f05160040c20000d481803280c1c1c000030032455042c040c0e025100000c0c0d0410901a0030241e0743d13006805d13445 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 151676205 1250 151674955 151674973
    0x1020303010f091808030a0f18080d0c0e15040306110f0304030309020f0307060801031a061804231b0609010203070201080916030b0906070c02010801030605060109030c0b090910030203 81
    0x503540107200d002525414000d6207103854172101c2c41c64000f16401c00304c0948405101c15010018481c01e1802d40c0700c29811514010607480341031050080742801190150740b0102c0f03041e010300581510520341d40c0101020141d040d1490b0400994229100407a4614100500984541c1c9060f003601c482d500501406c038207660b15520118003030a128102a40c200d01020f504881c1742d1824002e010142440f5218403900e03514510307048091110078415843c4170f0340f0f01d5040c010140c1d19030325240c185500d8401c2c44501600d030f81c2492000104a000b100b044e10140b416140007410b0082000e59000b1402511012240030030000c0c49101d03c25881c4080c01a00100b001c2d200540c050841160042d5190044410400024900b400a960b0036002134581200380020800d450400f080913640c094400c0c6048400703118950300103043c0344011b02009048985420020721942d10030444000110740180811185c2030b5550b5041140350321a400190140b008180001c03001c0b08003e1041041ba5405001409055 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 151677455 1250 151676205 151676219
    0x1511012702040e01050c0c0708070506070f050c040203040b040b0702060903031803130617073209100305090c0f1e011404061206060329010e03060405060103020a0501020303010f 78
    0x5640000c100d902955640c900710508009215841c4120b01c01c040301c69035402050b4856107044030f150b01000c4140d000d16014401500c0f140f099400f0207912030241e02500c4401c0c6040c13401e020000d03070f4440e002840802000148130b001100640240d010386e528000c25102c21104984440d0210368080d046d50041002c034004160640300002c542811106980c180b01200381d9880c5035800640c414400180c0110030845506568450590807002c2400c21402e101218091121407600b0205015201c0804080b80d50308512124101e0b00311800003440032540300f0082c4000f800500080c0e031a24524440c2c0000c0410b1400c000174031642d10240100801e1040c00c1c020024200001402102c0d17041000820000b1060412240a0405000c0d02e803681755000180824a100700c07407550f806130f0109802c1c8500d0800c118082c04004002c51011410417524a0401c4016030f5410800200b00c3d80500c141420030003488000302d04035040e01c1c42118504002c50380c2c0c0703004907a240000e01904e0722041c040c0f28100104 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 151678705 1250 151677455 151677521
    0x90b041101091a03100f0f0302040c090e071e02030711060706231f050105160303060f0807080f01021c05090c0a0803280f0302071704151101 62
    0xc208149401d003005500c41c0ca031180969404000c2000302c0d440401404480000f540701c14002c1e242d41c0d117494148900e48014500f100d1098800139000c1ca81d120481541ca40c03054121802410b035013205140d030b50400d050300800c1c0425011000c0d210308c1d800c805a004003440441202c9a03a9041314140786030f0035482042101e19800b20000325609503903445206a0403100078644000d8504500101c2c0603407503d100242d0321074061002401c42c2d15008442030140e0382c0c0180954041c1c0c0604012501443c1d0b2a19050300281602d8112105040030340710000740b07030358000510b40161360300c22040e142071034155201c4030700340e00942a1504009078082d10084100c000c0d90320071503000301880704032500e4121501c085000480c5a4018141d075400c00100e4200002c01029081341007080d00009044054280c4001441c0c0c81003090036a08150f0002010303000d00201c1e24000c2d04010500c458955910307a40d0061030150001d12486101180314840a0035500c07006105800800d825000b6030000b02840c44050400 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 151679955 1250 151678705 151678733
    0x240f290a080a03110606010810090c021002030109092108162c1009030b0109020c0a061b020607050903070308090d06141504020408070b0306150711090604090b04 71
    0x11403440600000c1c40380040051000e054042e03190030201180582685080680c028401810300c0070720300503c1071030741c0500541c000701c07428003000069801400c00c01328207000d00000f101c040180044000300d1010140e0f80b085480600c100c0504100034056240100402d80001c121004502944005a2018814900621611910714107a420840f59a40d50f0680c0f65003602803502444400c2501045810100100030b501422424018005890f5a1b90780900f0081400340c10b000d10340106030201e000c502040001000c643c4903005000385034004e051000501030b030610f00340c0148920b4020031500b50180085482414018000c1d00550f810350322000c2842e40301c1400140c0244104980700d000c0f0b111480b91640c0f16500ba40701007410308202804003504900a00702c20300c6584104420085404d000036100200c0d20740301741c01501da03516600007030410003449100c8500310340009028400c10a160007050a0000d04a0310041551103500500040310321045c00100700761184d002040108141c83e070202c076 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 151681205 1250 151679955 151679959
    0x1d01050915010216030809040c0302090f040f060803030a0e010c0c0f02091302090f04030e01170a0504050c060408010b090a02041508040611070308060405070302091503090307240f29 80
    0x20413101c403480c440e024582c0f0b5209403203400000c1119501860039018204968100740340c15814925620001441180b900917150310859854810080200041e0490802072540c0d10549480e03203445c08606001c0c121308141c9001d254641810400c940b801078000040f06174000c402004e51481c25030174044d040c20007078010744544c200e903c400c01c01a980c030840b070380c80781e03c0c2800304106606142c83c014240e60001200c09040c042030540401203126801c00266024415600101c0c02d5240c0d4140700d41449250b400440c2c10240c0021b011680b03800c150800400b54a041e240701c610756990780c942c90124015400780100100e004000114503d00c82c00312143c011f8021300d400903525000790502643c580c03080f641207011420306410401075190500c2966804074032130a0640c688202c11001a910111001c50392015042c0440415840c0c8020401d58045a0788204141404204000a881751640b20500585c1c000e0074180c5901130b1030270301d01464007a8101c0c5046000c14010507030f640f00b5a80011701001d9 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 151682455 1250 151681205 151681213
    0x10060206012c01030809010e030d0c020f06040504020f030f01140a060806032a13020702060307050a0309120c0b1303121a0d080a1e02060a09050a0606030c1d010509150102 75
    0x110b801228400038020751140031483d65460125001411200b00f00510750310036000b1062801641d0b800811540030350754120344407a4060344010004000780a190001500288045010444004228010341c05101040340030000340e0390b05d0f45054140f1a5500655400012001c005c20a080c000c80c1216044040203080d2006001e201481c051701003c01c42c4a8808115080203040d19410040050180101031031000e510b0b181c5170740c020400c6440b016044070304110002910107042c922a910004516903c0034016030310102c1c654004200f00c4003680c0036281d001c942c00110b00050b0540d102590030a078035458907841c8220001d417903001440e03003554a075040c0000c030f642c0410720790ba10003c806409202e10801511801c1c0b0250007454031948103000120407802d4040000501d8000544a50007041c0140100d10440309140c654240410564014442c03410060040100320040a08030141d55004190802c4100354840c0c07240600000c0c4286070b00401c01c1408918071180c1015450701030303a03041c0119 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 151683705 1250 151682455 151682519
    0x1030b090c1b070f0303050306151309050f04020a050f0d2103051006080a050703060323010c180302060918010f030201021509030a180f03030c0204051006020601 71
    0x4226109001c55180c4803144000030710010032540b440012800ca1030220042c590a41400c91220750300f400c0380805800c0c0070b0007000041c0c5966492102c90034001c2d9401c400c580300c240c5030114041c4c81d00d03c0d000c0c0380006070820001640c1d4070020861300344602c0d0010072036000c4901e01414080183d510320280741d0044070082544001c290440e20040144100c45c0c480c00701e20b01d50500050032503130054449050900051000c0000650250b02c25401100000d000152500e840c4419001005280d0005002d00d202c88605100a00d900072075040b082441c00080c402c2c00020343c8200d88400e02e44640240c2d212450105101604215002d04488000a40010244c00601010482d1554240d1040d500d61036003403018000c550b0305116140f40034428a0030040a070601c4c000140e1203002e42d02c4d980d0100050024440d001860f040c0c100002049109416603966440b4100105182420602a030187d803c1c00041000646900e0540e0700711400c984c013034030003a400c000602d1040d11140710a294112010030b94 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 151684955 1250 151683705 151683709
    0x30816030b060703050d0605030c060f03070216140a060e03100e0309090907060e0603010605030609040501110d0b09060603010308273105060907030207030c0803130c0b071101080601030b 82
    0x400f003030340c080e0b140c1d19284c0f03454400b904151043c54010300d000350031207240c11810341c58603000e0f1150300d9100e0944503140d41c0c81908c103d14201c2c0000485c00c20310034828000481031038400c80c480c10f03000103480068005485a80c160b81c4a0802001c150309944048405146000346600100031500c803001540c0ca8903c951000a218440035101f14a003600404010002540c00c0342c105203581e40c01b038400e54115031402c2d0019255001c0201500c0c060f0142500240400c44203521403280305001200c1c982e01c421007011400020103261200300d00544020010408900e00042907a048039400403105e4503110024070071010880098015031008003c0c4459046141e13038400c103041d620400c501e0032400000b11004502040c1e00c0515889000d00d1804081c032105841c0c0042c900d41c0204a800d0240c1d4903021403408648a21703841c1005060707250044180288080c4910829000c075025191050b800d60301c5444114a5124450008103140241708008402d0350241030706d140d1000e01414005154045000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 151686205 1250 151684955 151684957
    0x2090d08040308130614030a0c2601080705010908030d02090607060507030504060b0108070f050a05210105180f0f0402040e0d020c100f0c0f08090d05010f18030816030b06 75
    0xc2150b81100120305040015001003840c1300030500f5242801a820071a0001025440003500024002d0749501322001d200d03005000000000052038440e07540d01801ca10381d06201c1130700b03010304040b0340507141c0001040c1d0310135908002601d121102131803819503691183c50003907101541040d0084d20500c00100416550301c2200d10650b403588004c251380c503040c034043c402c60340e001344081c0c180040c00040c4050954049003000e01282641041d683c0e07021408416138160182845a50304c4248648241c0100f86041e29000e040328410f503128440501e0314401c504401c007007150080c412407038403000103507408003a480c180e42003400a8400641c0503c0c800b40541040000a050809680040b00d803c050f4244100341d10140c05480c5003c180f03404209900410051322940701800b11514040c5c0c0310280f046400884222003c0100381c203ca030009460300501925075100c6415807503261030445402c29030070009240d0a903034141c0d41c2039459621803c852107a880d00c41850000c040d5140d070340c0c20264035400 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 151687455 1250 151686205 151686209
    0x414042c010501050405090d120f15030c090207080d02030403091502060619080a110f0904031701140d080a020a080409062117071103070609031e0507050402090d0804 73
    0x18000c0c0340d80010300088509454040e4040d0340694030342400c002003000045112030401403907150540032700c001071111030094030b48450312042440c90981401c103565006124203007280d201e02c1c04042a5581c40d4000d000f00d002c1c0704000b502a00b403c0007880d114106680c011079000344079085c0303c1c021545030495082120148210000564421018882d0034580600c00c03070a01c0c0041d071031241003207080840c1c40341c41d60130030f80700101403201103a4821029030300c080c00082c030440701405140c01c0c0d25040c00c005001103040c04218094585807400032441100c5a0a21848081c000c2c0644850301132940d1804103a07803103800c1303c5c2c04500500d00140d0000c0c002d07a0060006000c10080440c0b0542891501b0b14840081444a44040215490440014801048044850a01041a6101c6078541000805000400760b0a54180200c58001c01d1140d04041183d050703038099004401010343c2ca420000032003003aa41c015000380c0c0015400c03c403d20305a001404500c00192041c0040d000035038605c0c0b5036400039 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 151688705 1250 151687455 151687511
    0x18070c05120307030b030f191a040804030b180606120f01050a020910080613021b07080a1208280605030a050f01050601020a0f0807110d11040c1103041404 68
    0x20038010480e0341030003645c40442089000c0c110030194880200d40d117642030040c400366192039450b0541031055120084240b10100c220700d0b5440d150620300166168002c1c0001c41c6c1c02e540c0300c00031510001780c02c10804190043c00d0020310141c0c543c18204101e5000c1e401003a41548912940380f07086020a005140c000c0a03400720141c0c807005124104280c0312410300c0403408100140c01040660f9a552040701d007000003403100180e503080001544a01c4444010805e0301c0c62203006800503460000240200d9218042c903c114032038a00c8100444074042e0540389900300c5442d511250401c0c1f40da845403500590341445000841c1a03440000c01c1c141307c045da8060342c054004c1d003020cc150203001e014483e400902440076210340320aa035144400d440c460080507182c03100100e0003104100b4003c8144044600c01441c0340c41e090b240707103054031000308403c8500f4007c1d03041c403412650041c040c03a922110741405601a500b400c1c1444820080220016161a132003921940303904480d101e60b00004240802c4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 151689955 1250 151688705 151688707
    0x70f060504120309051221040f1e0b0703050603010f0603030c150b09070518090411040f05060f0d0219060207090e0303070c0b0a060b0f070215030618070c0512 70
    0x2050070000d00c169802d116040c2458200403074900081c60203e003c010072194100c200381c6418200c20040d814111401c02100c10450f130b482070005020600c070303036100068031906c080015101c20b0b4468005c804e02011340181301c03d08110201e11858080c1d0841c0f0341c07004c1c014000040301d0744401526801d4414035801038021904003160030302480b4030182c540008a02100c010300c10740400340c001c1145a60002c001804104001c20130114668001c0c0c009034101d400103140e4440b6042606240403410042a0301d17510552428825030030030141400790314410200105000c413143c50702401d2040311079070018201d80c0288030800800c001c0302c01c030942001602e5241d000f403c03602d0078003da1008032044a50300c044030340d105004020617158001071070603403d07a220000105a4840c81e00b90300103030076940c010310044200414050711203904100a007540074003c4400207000360420506009a20080e01c4580e007005c45403030088034002c00004020340181d2103240c948504d4407507444280c01c08005800041c40040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 151691205 1250 151689955 151689961
    0x506040e06060d0e01051e09070e040b04080c07060f0e030105070207090b0301020d020a0315060305060310020c100e010b0f0f09010b0c150a050708060907091802040b1605073008070f0605 82
    0x507100c5203039038023a41d10001098490300317280480c031032481e00078030060002825000040c20480c07180c050319241ca00190840b1800e5880b101c0160500c0700944070840050301103c48110741e49014000c83d806000c01d500604040750801c401007001e000c14821181e0190340030031004401c0f80c901c1c401020351200690380052801d07881c5240b42c0070b0403a241d0260040500745001d2184a50700428510525402c1c4500180e448030384031901d03401c00d800150b420645901e004916150240d040d00314881c007100840341800010380000070403800328010700210fa045000c200042c0b14440450b401410950844411103680440d220700e6070340c16070012180c03251402d8540c804c0c400426041103076160040001c913440385191a05203002403002e0024490b01c0e690028a003016100200a80d0440700a4040d551400350b95001883c2d1a0701040d1018008507a148241c00780060010044001540501d80c48860003084440400d00003034000300ea98030946502108000c17500000d03a04441e0301d0780c0c0500c2080c02060031710b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 151692455 1250 151691205 151691251
    0x806010e04061a070c051e091504090b100f060504090c0c20030105060d1208070e060c0102031501050f070f02060d18140f0307140c030d12060506040e06060d0e0105 72
    0x180f5980400d000d050301030100e2000114081481e1810b447c15503030b03640d6a0780e6000400c00ca40c1203c5105507041b40c034003240b03103080c000308031105449525080801c0360601da5032140d10688103424860000010300a02c801c0c0070700880340d00119504160351070b00c14000921390701c0d00303892090b1700f0f8050b8180350941450182c00e414280205544913804035082403e07606180c446610354841054001c081059150000300001c0c091080c2d1003641030050419900c0700250075945001394025205800e07182c129080c03001d810340c0300d20215643c0810960702c0500b084500c0e6101c03129030035203960803607104c10180607000c1c40102034418002e03680b91034091811800c02c41c1c1824000c1c84805001100d01c0d420010500e01f00307104c000115140140e100000003c04481011158101505a00160340c14010818403101c05648214480360102d048081040340ea030f500e40410480d80310354414240c5190036000010b980389051405032041e1410702d0008139241052003100c46c21036104850f8050301c2541c5d030381544002 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 151693705 1250 151692455 151692473
    0x50d0e19060b0105031003080306030703210206090c030c090a0b060f04030210030902011e03140c07020109060c020120031902010e070e041505060312030a1b020d0806010e04061a07 79
    0x2400302130803c00d1450609100045002440303000103411580000003040c03080d14100005001150884050040c10b255940c1781c034000150100114010320890000c1a50078074042480709941e200100140820710b984e00038003000090040c444002560b48140d007106a441d45030080040429a0b411180c1d903900318410014051038240500c400c251a007031752240181d0704007038a00c82c8507218a040c2e03c035240d400001207018061250f40c921a03043d100043c030013613112850107814a0340c800d80714400d40c151507040440d05290758620203030005c0c00340d80c40481000e551001070303596041104150b9207845500304447c408101d10070940300050303548030007244004200303202840207488544018081030034540c072030f507090510750007400d11342039580c1007c140d6907a0200f1030f040750400000301e02074407450a1400d44000b0109c0b011110741c0344060500f229400d40c4080741400c00710b0b0700d5460b100140d440746001194104004c0c4101900242d0350b01c008601180c01c2c00c68140d1009107001002e40d139612920f000c1c608 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 151694955 1250 151693705 151693721
    0x121011120c0c0a08090a0506130510020d0c062705070614071106130f120303140c0a0c081606050105031905060408090f0604091d0c0f01050d0e1906 65
    0x54606000b420000400819001c442c281c20484107a114046600050018115540516442440001e415801c041c642c6058402ca40040341c001c0c10b050b9205c8000d984071100e01407032200107042d09140342c2c0051100c4d8403030a120354007200824107800001804801d8081d40207400d03034603030b440a2410003010358403c00003000d882101c043c0a04001940d070707404c4100e110101640e4410340d004940c0442d0004554400790040a040c54903111490740c94214850425640c00c09400190420108010040c00c8013a92409035100e512810705d00384104104981c4480c070340b4002c8401d800c0811040900500308010302003001d000300c000003921b5250804141c94030f441d8202190705c0004511221340822030120b00154030a41050905a031030946e400042c507140d49060b940307640400b0204000c00d00203030760b80c4a02c2032042c642412881500400f5001c075030b600c4008a50540c0188201e10f0104194401c5020b40350240800602240124495211074100a0070100c08071104000d0706d02681449203e0003000700c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 151696205 1250 151694955 151694971
    0x405040303142203081503010624031a06130504050a0228050327070303091412060a020a11150f01090603030504141201060b0307140301050f12101112 66
    0x192000c0720054a10310f828020160500c2059400580361041d94405601994001402040004d845004a00c40e418151510717000180305001e60303000c002d001e4403401d0300d401c05c2c0401800344411108204501c640c42800c1c0500080d240540008840d100c5004083c040e003204000943c440e05d42c00c500d800c1c1d41480e00e502000c0140c2c2001c83d030102507084000c494000c140100d90f44580c0e40b18510040140c00d4822010303e051041d072900009141e4040441d009603588220480002d60403142041041c4040000105640e00140c0104051514075801494070b64110300b8242c0d8869102030806040c281646007060211030400100506007420240040c0503003142c1204026503800c588006000d0701480c01011000b21403441c103c6c0107642c840500c5c0c1481c00604c4004d01105803a400c00f041242c01c2991010003043c0782d807220790703450f081c0d9100f0390341642e4006c0d100b08102500d2108110244200d0b4002110314000d20301800c10544942c012500c1d138848000c2c02d241c3d00c419141c088484001e008207d04 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 151697455 1250 151696205 151696231
    0x9080c0904020f06131502030a080a0207030915170405070303030e03070302030406140f0307020c0112020f0712111203090c010c0b0402011103040b0a0e100f0203030106050d020702040504030314 85
    0x200503903035469110360050080d02d0450305c0c1c40c10241000ea281555810030540c241041403034802c400d07400030003011807240d240d45210540e25100301c03c9003030b8014000001c011030b60a500522800300341020b1040d82c0d07825440c180c414003016015404002c58192010745103900004414424035400d40100c2e503601c040314005600e44400d6440003901c07030040c0d01a100c00c2140e0b00c080178800c5a500001d441e0804480c41d11241da0781030005e400780d030b98000010140d020501b00901011030340d42c9442510f29204c002041c1500e800440d544288082046091040501c038140b082174450f807800f000042d058070380a00ca281e07900e003042d1601034607126928000c58104800c050726680011840340056421035070a080c0040c030a01034016941c11030240e6000307180310020100340d00c041154003810400e0b4403001601d451452218007003080319a0342182c0c180c0e0300542e204000400860b4072034801400070341e11301e5100504203000c070380c0014156501a0340030b1703002a07240d0202005d8000104801e03900b00035030341c511f1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 151698705 1250 151697455 151697461
    0x1e130e07080a0804290a050d0e06100303050c010e070611010501141c020f09070903020a1e05011209020a0b0405120a11011214010e100608061e180709080c09 69
    0x64030b41d105a004070380f94116465100e404001700d001c50b000d4182e0444070310b10346400340c0c00e800038210340240000140d179604044c007400031242c001c16640d0003944a001320f19802804d42c0c90955a65000e04a841440d43d80c03070740c988040010500242c00544455900c503061902e4002c003030750a556060300402140d4a032102d8040c2c0a80d03421008241d90210b88041060300400784c00058440d0402d445256046440030003089074030b5030700140000c1035901c00c44485030034984ad85005800666200401b83d41e20348800014030103580101760b03118041d4421417010904085660100310381d08040e6112000544003c035090241d450b00361084807028203040000c001c17040003501c03007100500c8007003c40341c144224110384213a403a21641024501c00d40c0c00982640303c0d40d44116040103a80100e9480c2c510800c000c4d40070508522400c24503000b00d9000300164a0081d082c90100031010951301c0442e0b010107088041650700400303501903880380f032050b00d41c00903103071501c00d0641c28009151425032051400c4810 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 151699955 1250 151698705 151698713
    0x103210e010f030b0303071416120f0209090f010905100b030d08011401090302031203040501290907030e06070f031d0a0f020301090c03120f0309111e130e07080a 71
    0x21000301c82d0760325000c038003481c0c0c841c0440e0540c800c0038000b8040c502c2000004060600004642c94030120104c1e403102080c0d580d50006001c41d00014008046000c030340011000752822088480c1c0190707a020036284413032840c090b92130859002c000111101d0b0440000640b81e80305610900303000c502c0680c061700660003a40f4000b805200c0500400290301807490a540907a407003044180040e41c5d01400710795505030908481e0b200e642085034100c51039800c04040c544008035801d200021400d0407071040c5003032582101003061050000341000d0030103a42c1c0403000c2000710104809801780c0c1984c2c440e02652044e40308000d080e181d00760340354503681c02d00401c0d0b406904c200244401c035881d00f040340c1e03801821301032002901411030090050002e4602c1d01022040c88407207110000d0f0403003c0c0e186e09a41098030a8258283c0d0400540541454082100e9444608010300c002071b12030008001d440141902500041c892010b40c08106005913403080003003401d600800c00c500c00f401c01d400080001040030b6031 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 151701205 1250 151699955 151699967
    0x8030706063006110904020c03090f040603020d06050702010b060706050402010207090e1e0a0c0e0106180e04032111220e06060c01141302090604050c0a050c0a0503030103210e01 78
    0x340241659920094044c891001d14159080c0040080003035580d440010031580c0d036500541c034101d1180005a00e06001407800388211030449a0141c00c6104131843c5459000082c44000e100c00155526400e4801300b6540303500060400707911507080007070f42e41014000245400303207079008402d01502d442003501011100003114038280400d4048107090f20210042982003800d0100000d06802125001184210310702c1d0740107041e00c00569401c0396520716a08008905201441410034031140c3c0800f00d00841d1180320300380e9034080c0300911403c0c00c4d44407a001400301c03150030020f4003451401040768421510002e0100f142019100c1403036604504140b48000101e9016040030b1107064001038005903440c080d00701c3c1001c83c06041192042e85005506000450001d650803842212040001000e9203014441c0502840c0380c0310100d8140100100181c8140e800317440614958450301503c5070029800300015030103940b040702180111440324a1407080f18030744504040a1200c0481c001c606a64000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 151702455 1250 151701205 151701299
    0x905060a141e030a1d120433030e1b06030109090816050c03010e060603060c030711010216061b080712020403020901080a0c06080c0901140d0c0306051509061e040803070606 76
    0x20a041121882561102d039008010b0304e5110403d15150400e40b01c2982c05500165501c1409010b5440304948000c152001c0d100505043354462014070062090303030b800782e0041000324450b088140c9402900482d0ba104071900104c12100e541c05a0b8801d03c1e035080a01a000d523082008004003a603040620002e92034070802000203290303141c048005121a4030a0303660488240c1490300841d51211603030b03482501211800402e640300c1b03042c444045840000c1c02005010b00300580c2c0e6444460726014006c0312004607003480d40798126020310000c070143c0e41c0c0d401494020241d03c130080030b00400914240002880960080342401b1a9404006100f05507604841c0e07019024038100300740c3c542030180810240221400203203510b01d4403248144854040d40090150780302141e00300f09840f114548990a48100c042d201d40108040c07010040143c83d102c010000c10320050013035410903455040303c601e175401c0008140daa458591808000c040c65a580d05014580b82c40c8203400d284e032a0344a840d0841c0c1200b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 151703705 1250 151702455 151702469
    0x140a05040c020127020a15020d0e030705031002040504060b030603030415091a0a0201050a0c0c0807060209030307150b0a0e060108090a12050403030905060a141e030a1d1204 76
    0xa292440c14140c0300b903200001d580b44e09001009658803810981c4161001280c0072401a00310b10800304244003941c0383c080d8203814580c0180031840380e8050855805011203512a0548248000030030103607014031485221100070f58005848501c1c150401041d1000c9910840c1015002c0040c40b000b61408030854055590103100b1402090540754100c800c60340310340c4601590105103e0302001410310000030092007019070f0007030050743c4400d0000710403169071100314004141480862400078110398081c095040c0200c400500344042800031a00310340c000e010403211044144443c590f401c0c494482c40c0910001540c080a82c0360030085aa011204080c1106050044120014000074020004583c1c40c0c1e500c00905c8404960381000034181b50000e001c22030102c0c8c044000401d09090800c29075441c0c10f042d6451480e281010030181c8995801103001441c000100c0310750050114aa8000b035000328003010000680155100003514186034049140a2641013008904120883c2c17030181c1c1c0c251202 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 151704955 1250 151703705 151703711
    0xc080a09020114071b090c02010534110105010b09030709060605030708090109060606080a0c030e0a0b100f0b1207020318120102040306050a061412030304080901031d0f07140a0504 79
    0x24207100045844441c51504c685c0c612007070114000446800c20444214507800074840d64541c40800101d80034a009008081b06641d0900070b15802c41414080d201447c0703003131001c803100000c24541c2c00d58000340c2101c1d1030011b00182c00ca5413030408100c0f5200604807602d0803c98181403c40041c500e10020300755070100411640420072080f002e5101c004d81c240d024400308051a500d140203405124101c90442050b4500315070005c0e920f000b40590b0711140a80c502420842042e0fa56051018402420ba05051000100c0100348003407594004000380c10304491090720f60552041f42052050003c11401c2103400600507500f100c510032800400303840c412540190050358040e1094024015580b004d4003c50400c3c1c02d00000c60307610744c40742c3c0075682003801168410645d2024000b0f02403929032581d00d00da00c20000100410b440c0d201501c0140c905142c0030525409001185c410002046103810140d0085101240c0e4024100300c80c40050035501c0f6100121088840084ca1081e02c6110322405552 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 151706205 1250 151704955 151704967
    0x206060d020a081504021302040303020705100203040e0c031611060601030b01020c0d0b040b010609032103090221060115020d030b03030f041706060316260607030c080a09020114 78
    0x2490600300c41c090300804048400703002e00f1110f081384000050320164080c00c14036940103000141c0f80211415070f42c060300101074892410040c40b01d04845d40c3c1a031421400140400705c0c0500605503101c5c0203210b0100210f4513404c081e2440480b00001556601c1400400d00c851a2012400709220b030b4415402d00f000182d641070f100041c1c3c28042c410309903950003041d50b16904200312650b042c4074041c238040c070001621680c072400c1c01c0d104030b4410301000d003040764640c903441000701c280240031140503403e19001c10f098555602140c01100600c5140311000e6145440355050f1030b041000b41d0040c665010780580003066018065154030781e800c100720801d42c6400d900b00980c0c800300210740c00340c055481081d50715543c8a00502e08042c841001002c1d9000f1800400c4a518000030703060a0382041d24040c03210507141c0030400b1a4807800d0301d00300302d141c1022404181a4ad005224551103110b003510082040000d07800001c140ca400207010780c0e541c40c0f41c086181c0140c2d81c031407031403da0400b408644c0e903544c0c4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 151707455 1250 151706205 151706209
    0x4050a05060309010e0d02070303120608070315020c0111091008060109150509030f0c011e0e10020c030604110f03070e01091503050d051e03090d030f0b04051e070f0206060d02 77
    0x212070040c402141d8410400c14a02d0151f001401d4030403039010313550b460060240c0c000d10704183c0c1c08901c84c590550b4071015003403001c120314401202c580c8850000061404a40038109403d58805550174040c3c0b0002003031101c81c0d404c0ca409a65030740da00e1840c210185240800c0040c00d00301490042c0050b044d200b0030451274082c001d200b10340409030014103c0e81c00882203655207590b1b000000e202400640c05150524810100e00f00403105514280c44412490780d01000344500b440100310b4100031031160b00c640201c6034031b050240307602950040d01e07558503455000b41442201e00c00c24404a01a9118003010401d411186031954151403800d040407844a030200001118014203400140a901078542228443d542010040408a0301e4040c0340c103820382c0742c540e01c0c049800111000c0715030740c1201c410720301910301c070343e01c800084588407e0021305540c0141c0414102c1d50100c0d404c1d50100c26688200090704100b000150740100549440104200d071004025101c4a01910290244078480504070841d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 151708705 1250 151707455 151707461
    0x16020106080105150307230d0602040905040b090f1516110601170c0a03030c0209191802030f0307080421020904150e16030f0f0f080403060b010504050a0506030901 72
    0x5000100c003d2089040c4a8040341c81341521340020b51217440b07504000101c0b48400d82d00300c43c400ca0300104002d801d006481c00c2c0242c45c15005422980e0503800c2101140d80c4111744660303806540682c1100c0c1403840d011000d28604980200155255404a682c1505071400394108a0380495440080d000e0074900e000305a407002080c0c8079007000c90203000004201d0b50070503107034050903400e04e10031101169025402c4c458042c1140c000030b000038a26400c4c11026040c0310700303c20b8015100c045100d1009804801e85011640c0004005051502c80c04070801546410811208180c1c060350285191800c0b581d01c580c91481144070349003e02c9400c492100078008038010001e18250041c2c01c8500c0c500e40f9107814101d040405809100f0103140c241d099200040c001845079051410703200c030500450a540300c0e0110580382103011909485042d1008000880e8050f4018030341d4854206940c0395411440c0a100b40c81c4030480c1c5904119040c017080102c1d81d03980f00c4500460f03206603150381d52501c88403022409 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 151709955 1250 151708705 151708709
    0x5070c0b0c060916060e042d020901030e011104030f11091617010506031b0f0a1106011409011401030212100501090506031b0a051c050709170616020106 67
    0x102040411400724048010842602c1004010141c030803413400701d4907101c4100050b010b090b00040404858004a0030325900801e03240840304070180c40744803c00b8030112441d0700362001c6801130b500800d42910550301800b515250400b80b60090041c0e03409074040e00c2d10350043d4480508044800d080400502518180c0c0f070107404c0c0003504800d024542442c625803c101501d003034100248000c240104400d120800543c182c840040c1058a15240c902d60042c1110607100b015101c450100900e824444640d0002c003441e100c00c0e140c5540e021001c030401412b1020583c0b00c4130a8201c005401022591380d9440c25055410003d03007501c02c0981c1d000100d00900a05101c0c130b6500098800340a111480d51465201300c450990742c07000303001d4480091080c80d0209a848074501c00a200080c4441c14040c400340580c201e5526010b828030091a00c050507603a000d80d15011030703d42e00c00521140c0d035403182c0340310042c0c00d18603c641c1103022080300c17440e6100e50040120741c08502e0590420104c510030b400000c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 151711205 1250 151709955 151709969
    0xb03041b030812150f01080a05060109080f07080d1d040906060905040f020a0506090303030a05090a050709150902040302030a030e040f09050102030609090c09010e040c0b0a0c0c060203180105070c 86
    0x103190b82c2c3ca007050b00a8124141c0b04000c4c50505a64540f245180050352040c0024044c0c1d640d030340c0ca40741c0610642c0070b000081c00407810b100c55554042000350041240f0303107102030401700804686181000b110b00304482280d80c0307400c200120401000c868411450154003600070f60380002c02100500740400104030940000b800181807405100522880f00c4103c801c0d54000ca5100300c00030703524410001c55200300d001d1584c058206000003130500c52070b03500c126480310a5400782c40b00b07401550f4599003800943c1e00001d42c6140e40310340b4421548451424480600703c185070441c9858299000645ea070003451500504124210030740450a480b5130300011080060000240003543d030618005002c1c0d0001c60b021401103a8403070004100070b01c0010360707040046018042001d142d08080c05408200001030040d0f6030000840b10014140058000900000d11141e891142410003450309182c1d140d240e45c84001194010301c8460a402e012100c0550019802d0800c3d5030364503402c0c0b4196034500b01c82c0e40b090f2 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 151712455 1250 151711205 151711207
    0x160c030314160906051602061b03070308010e010b090d06050a1b090812070f020105030a091a0f0f040819090302060a0e0111030408060705090f040c09050114040b03041b0308 76
    0x11000054030401c40ca900b007100e8443c1801952034036800c480a0091604041c02c80d02c6503403d003000b5082c0380c2c00401040c03c05000f000e240000d480f01c043e1441e84240f0b001c40c0001c44250040242440c1c11241da03014100820000d0304d009507090024810070151030000d01003d541d040864010303405a40000c2c2802410440000118590783d00035029000520528141d802100d01000912012404880d503096004e038548484103065001141c0540000301501c3e00d060307955146001007410054503841c10b1450611071011450000c40b89840303044042d001e4074103d0703000740a0000040d442d20075114000c44890303240c280040c14400440700c41180d5400a03402000000301140420341c404007440b0b440070280c032044a520382c0316400c5a078070701c130300d21844200f81c01c0880400c901c0e500c120001c2856507801019101c2e003141020000f030845141254a03804194000c0040025581010b1075811140000d1946030800c1e1420b1003102e5184001403005062501206113007a40f205040c00c06405903400039405 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 151713705 1250 151712455 151712461
    0x60c0b0606160218180703081e040308031510020316020103050903040b030a06091803020d1d131b09050901031209171605060405030309090c0f0d14010806160c030314 73
    0x60780c04510641700c00080d0a03640c805c0d0b0351a03aa000840760201da030b110055610b4125003448200d1108110088035003c00000c000000120340c1a4008e140030319111034021268090010400c1820040a8886c8080d90424400826a9410585004503868080c00c000c40c01c0e51300d1125840c20340c031664201e03288001c0e01000740070303900e90582d01c00d00a4400e1001d042003a0350010182c1c00403803000c0c0c0720040041e803020982001d05481171800c004010080d010819400d103054001540c920443c0511141c1039564564401092604010407010612903041801000d801e101c0030a26850f81408080c0030b410b0030300b212500e1188500d82c048020501c0d80c2610307542c6810f488081ba1141050032884100d01d02100300400c00f882c1c140216000c81380010700662411128100380000d040d00117041000303000f81413003a03842c040060001400c14000e040c500041c0140075804012a10700103030403401d403681c0f0880070001c072042d044c050002244818241840300301c071186002c034042c2c200381071200d00311094079041c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 151714955 1250 151713705 151713739
    0x5010608160e100504080d02030301180e0309130b01020601050616080f130e07080f190c12061206110a0207031b0801090312230606070c0815060307060c0b06061602 72
    0x41e205441c86c1c041034400d0410000700480c0e50707000a021f920440420710750b148101c21041d40c0a0542d000e07411041d2400c01c0b10b00400655140070480300500b00586511112000c0c0d03a050003445d01504044901e641020000740500c105401c5a5900508a180000306020424040000d03a8095101c2c10710180d03440b0788880d04e0b840104000e84481c404180e40c8408500380b888503400c0316229a58580b0000d02140220012b400a04900c2d014002800408010359076089050700515014001221110403203e600f0f141810031110708200410840c1c41c01c1c4500c5404950129000c5d0442e90005609044464004842c003000300b07907076000c03070502c0d86080601c40805400513201c1108445c41c03603040008404042400c000380c0140015640010b0030800003c0712450038070090b0101a004901d20a074168a54107001d20b006000010034944a4150302003004614080024401902e803600c0c0030000c00000d0b5581d0480e411340a4039040c454003000c40c0c0d58a01e0008100b01102c4e01d6001442c1d101304410800c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 151716205 1250 151714955 151714957
    0x213060914010e090d030b0607150506010f0c02030307020906120a0c0603110a020c10200102040f15091211130b030106050f010c14070b0c03190305010608160e1005 72
    0x41d03200d20103140000a1071255a980d00b880341031108040c1803501d40c0c0c0e03c8210003e000c0084003540c8044184814000310780c0c00100090502196080002d160800e04009051650800c0c1075404000421182c4001a20048195901242e041e18400308035124180005d500007480c00101115105030f000d0041484988411841114101c1e2070802040403a40e614103d984541c0c0c81c400050303400315003201c1840c109182c04882c0e207105441c01c0420417428242a1003030503008550000301d60340229007030050100c1c400c8140b0003800700481210f90300c412410085d02111503885070001c04c00c0c0004140c1e092200300c0d452000c900340010b00c80320794082039400c2c003c01000c1c1c1460940c0030b5032038010041203e040c942c42e4600185d00507156042c04030041c1d0b452504010340c5182845090060510014105101744003134624000200040d54030765a0301401444c0c82c041031384282c000c141c244001003000d650090b08490708034035038950484000110160a8400f0811601c185411899080b00c450690b94000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 151717455 1250 151716205 151716221
    0x1091205031b0903030909061302070c080c06040e01060c030c08041806090b030a020409110a030506040b0f0c0a0507030c0203070f030b10050f011209020924030609120702130609 78
    0x141004100240324045640b581c064120701a406078010081d4410310f18051b002d155110800a15201000700004800b0007030780c10a100850701d03a804010b090104ca402445051165681034402c241803a203040c3c8080700701e900c180725100c2030007041c10940c402e0602c1220300b00401134020911954895a9481407102400d1100052503203d00e02007021511240c540201060008010000c00c0144410307001c104c001e00820310202d071500c400d136103400065220450800011405034026007103d281c00e040640d0314000007481010709501c1c0100300222001140184c816184041c502140c441c0454581239070454000480650b06102e40e08001030032090002d48403054078452128240a40c0b90300307a0680d88480d0314061f0562181080c811004107500c1841e01442e054260761b404542d0700c030b554021580607a02914016014000040f41900400115840010308c110a800810725440c20104075070701c990707410350b40200550001500b0b1055645071424958414550340d000c0000d01d03910260200207013028 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 151718705 1250 151717455 151717471
    0x10031e230d0f02250503070305030304051002070c121b170c0303090901031b0f0e0f01060f090b0a020309030105091501120305090f01120c02010b01110a030c080c0109120503 76
    0x2900e2803955104410480c6804003980082c49003001d22210041139000400101c0c00d00010200b00007059503082025000440c05180519540e051a08203507042c010200401d10b0650300400c410f500243c3e605041908495051401d4221002145404402c3c0140a03c141c440c909400070045059100700d25581c1a8603200c104a6111085a1080c1070300c90107540704060784000d0100041010400c0c401c10708101c000c03c4018141c40c1912240120480d103201d42243d01492100410801400c081060060150a15050901080c0b00e0b00c84c8c0204400394600501201500208130102180d000300250b0301803d00c0100244040d152074014160f0b290b02c2445d4801c5c1c13003d102000085c00080c0074100d808030682554401d440c00040c001405900440b1180b6141044068030904445041c10722640411500d19400405d899101000050007804c69907031406e5682c0003600000000781d0003919a0020300e1703000f802161180a10350104e8010640c080c0c001d054000384100c0c1d80d00c92036100005510900403 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 151719955 1250 151718705 151718713
    0x5070e060111031b030705191b180b1f18090203101707090f020309010c09080d080405010e060f070216060905040f151e090510031e23 59
    0x5080c01150014400541000a500104901080010300b4102c0159100c2e054003181d1525443d80d80b21481c041081542580d00b9084103e140308100c02107005407542d85695a5100c400b500300400002003003180703015840750640d05d448604158544100b02054407001d003440700d036194001400548403001212442c0c0e03800c042014081085c805d02d2090307d0250035600c200d0f904060030800d408135042d5100817251050720032548005881100c9000755001001b450300c01507202d062032180c9030f0031748680c0d036290130600c001d0803424404004000392880c1a08038614000100751070310b0402e24014061280c0e40c000601031801000701424000d1440d42c06400d19500b269070800e8020301c1c181040c000b600590001812480f001c10031468507402044420250480005107060341c8410b45629600b140c1c40212003140c001e100844000c20030040702d00a14950105102c02d2816000c100072418245c00014030494800c0c03040182c2045881403007100d19406065900418503480c0401c5540e00354020041107441 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 151721205 1250 151719955 151719961
    0x110a120509061501080702100c0518011128020a15110105010503060105060d140106020d0f030902060702091e10090e0a051e03091804060b0118030b06120a05070e 71
    0xc800180306203e031001102c083e1000340b00c94011a80c1c1e11018002504500c198160302020000c54403440001d00140d40ba140e03603a14000100c4000514900481e07818442e071345481d8174041e40f020a6000050400b0307907080c0f500944c04120030b01e00e0001c40d04060340201c4000c41c045283da07100c107602e650b4520270307855690001c601040200c1c02e9800900407160907800a50041255061100252132101442e1002041d0311009024108090401364400401a44400c1010300c2c159084a140130700f98105107400e200940864011602c030b84556103009006203040300c0011f0b0303044980c99051240c2591100e005809042140c0c04007140b083c2d9019080626140c0480c000c1c1071080040e0381000c6a070301c00040c00a00141910100c0d55460361598464a40000c10500b030555642446004901901ea0040034290a2505080048a43d0741780800c1c14004124550741e10300022824010480c0e50000744c20b1100c1d69000302040e06000030f00030040c0c40b44180e02c40e940c1003090209600d41603c40f44c21740280241c1e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 151722455 1250 151721205 151721221
    0x1005010b03010f060c080405030a03020c0a150903120908071202030607080603060414010b0a030606090f0e031b03040f091d0c130b06130608012301051c110a1205 71
    0x31000f8031420301000350f0b04204201241c00b41038500d03035130f9000d03009035400c0507540e802082c02d0801007139044005800c1001040d20502c2c1800d00d00303020b01084801d00d091000c0e00000a09600741c03130300000e420800c52120f802c5805101e4503426002c6c26124080d11b031000da4481c0c4000241d601210224824090b00000928079440380d82c460344a070200900910f2103441e01d4585462000c1c601d00021115500c403568020580c880e906480e00961040030b000411620384005d07101118168083c0c204124148900e03545082c0c00041a500081d080d81d840e41c180090003c421f0346544281c0e882000140381d802c40009d2044481d13070120701d0000624840d00c0c41850700429540d203801075139402c0c66120070180c2d6074006d208416880050191009130500e4134140080003803401c680e8166020a0014003100014065860356806911020000480503a0170302105000a0441c1c00f9800d4807203882c680314a1b0741141e0007103d4111007084034111801540c1d490b0a00c500400204030301441000e001d0400010038001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 151723705 1250 151722455 151722457
    0x30403110d0c110f030303090a02130506060406260a0903180e150409051504051c02030f0f0d0c09080c01080417071403040909110607050d030e0f0601081005010b 71
    0x5070785503072001486895540c404128000d400b0140750014030070100000141c0b01000118002c2007100c00034080c40c0340520410040c0a150341c01002450300703120911010303071190303400ea50607206903061600a900071140680c80080000144810500202042c0300142500e50b10045109000340c3d00c2c0d40101c012200a5401840d06106a1030032105800000d05644240030441d0000c031130007000499109481c1d280c552901030154130014100540303e0611080000400110010562813a4201440100b0302030280d200c2c040c1b2520804013040000d41c0c005201e502c04121440207a5410301000058680c2000410101031401031903174a00c2000028101580640c00e03d078829540141d030001e610001105200c000c1d001003804803001c0c1d82c0b40214100001090000d00050035048500050300d14250070260302441040d40e03017600584041007a8408500d0108407141e501c1042d00b004649464141c140c1c03480c006e91040300710380a000c1c0313800100c4c07c0c000c04034004017400c0c1c214a09029a98a5500e10306203 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 151724955 1250 151723705 151723723
    0x509010905090a0213140a05090d1409010804020406030203030a120605010201090203030f0d02070209010915050d030f0f140408030301153906180611180114040807060503040311 78
    0x41d800388040c200185800c5c492820f204c240b40c00040f4450b009810070300070003403065a003440d90a88480421100c043c0400488181090510b008122040c01002800c280d210301030031b81d0304015000c80010b040d900d550b00660000c42c0c0c09000c4070303650b1030740500c010049002d0a0020b640c490a00a00003041c1d8414010a060f80740c00038061458156001010000c5a100000781c0040070b1f000d0182c00d001d65640b1481a0003080c41881c082103039801800c54004411050b04420300c1210010342900c04264001c101024451b298103202c0c0c0004c0056800350f034155903091419502c104005070100314054080b018504a0303c0703072210411060800302d0b0582d07010840c807019000402641222840c019482015441c80c240c1886032400540c00903201c0c481502e460310354070b540b0700348000c2c1d10200f040a80d01c038040d10b1175062100c1e9800d0071740f212948094100203401c03540c1044800c00f10100130700140000c0310001c00e40715048559141e55010007800a4002301c9054000c200c1d10413061400c03600101c0c4d2845 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 151726205 1250 151724955 151724971
    0x606010201050105100f03090615030804030606080105011202060c0a05030d02090a0b280c06060605030402030c04050f0105040b1302030103030804050607050414120a0c06200f030702010305091606090509010905 92
    0x81c030a03241201f140204000c01042c0c0f42551640107010f21041e1501140d400345014040c0d5540d12802e6040c407406460b1558401c2940b603140c840100034580c0300200701e1001e15811a0b2041d41c68004518407840c1c00f0003044050400c0c007001488050a000950081c146000155034900354199241c5210b405d41c021005d40c0086800390303c032848284d120040807110401801e080030140b074a0030707455030401c4403219000140420b40010604c4154030f8100912196150211740901051030326100c055204403042c0b103106c0c0510f40b2010380111590f103d0420003103001203054115129a50b03428001c040f0102600c4c155418058800401c001ca403064003182c05481d84034428a059641000512130000c114001e4103009000e8084400c1c000303038407404041e00603d0582c0c0e40c4110311120001c80b040b0309850b00c442c070780c9560050414860f0090040242c50803a40c09082c00950307513880a841b06c2c1015052081c046400000010100b40290000304040130764800b0359981e45540e803100300c9041150b8007640c0c06c3c6 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 151727455 1250 151726205 151726217
    0x20414060f1c03031508030c06010e130c090c020102040915060917070e041502071101080901060e0408090a120b071b0203061b041805090f030708220f08060601020105010510 76
    0x240464080d8006005d0f0b00821110000710655894002d411a04803640b540142c1e000403004014035141d401006400503202c030030000340d445060392080c01c0c060751445071081c643e48901d51031000a0013941524001c1c417048005002e10a030700c203500b1181ea82203009540100d00c0800010601010b66513079500001c0c0f45030010009141003410040031031030020021a44030600e500e1516007544240040c3c0703400352040720f0402806c0d00d0074002501da00c40040c020156030385031074001c102c1801c20840d0307540c1082e0401d1145a48010030400f0aa12241a801110712031840c0004001040090541c40d0310900040c0e86154080c05680305405074030a401002940c90f074061004100c40c4508220800c074280c01804103180340c1566900003584034400d10600c0c6040c142d50714100705000c181445175181091034240503501e849113980d200f40c0c0e03034041e80c0311346800460301d00982c0e80c11a01420690b40907001c11030b00c01311250303038800f14250748100c103c58850055007018000285801c003001440c0140c119920b41c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 151728705 1250 151727455 151727509
    0x911030109050402040b1c060606140f130f080303100b0f0f030702010e010507020c03070509091c0e04023603030405010f0302091008010f060f0c03030207020409020414060f 76
    0x100001d80b0300a4003d030b9100d655949500c0030b80d540c0d80344100381c6810049000765600e00c141007a0b0100c3d10154402c1050000c1c04a03600840c0031300b11f00b2100345c400401082170b143e881c12503109041500c541c105107003449840c1004201c0040000141d03104181207001c00f0715954648982880714011650682e11a080a00c1006080d0040c5405140c0c080f24503c0005074164508244900b900e100b5100c100168000d0a032015250406002900151005a944041a09007000d1880e030f04c2d4080254007010b0151005800c0c00c0700d00c01e51071098404001041035445511044940340150b0609000301e01c411107004d080350792450600b80702c040e5294001c6c00795013000d14200041d00c074401543c1e51031007056402c0041012540e20300c801800481c1c43c66132685400c0d81000148000d1803e1500b205044c40442c0456149043d400340f0307481003640c1c1c18035025864040701d20108001e07110510009500030f0a2100f0008500094071680744224001c07a03907256007901c20070600507035900e070300620880d400f045100 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 151729955 1250 151728705 151728719
    0xb0708131202060d11280e01020a200d050604060b09150f01030b04090f0501060509060a0e1f08010518011b080612030f030a09020a05101e020106080703030e03060109110301 76
    0x12405c1d01d448074081600e02100306007640f0024909846408411201662a248207640a070891841074401e0008100d102d5840c1c81e0f0802480c9542d0800c00c8020340e858242e4016215220501382550b0700004850540c10700e03240040240c90b1030140203000380c203298009183d0304002100c4c245840c501804071141c10302d42400440c09000c100c540c05030031075102d919800000b11032444240415000c2c81c0009089401d241c2000030980d0302402c1c00c2c1c03150004190601c208a078145a29411055001d0800c5004401c050703d541c400300b45070300101e500e520313082c100070712311013034502e058444510306008211101e01c560380000e50744400281d100004034450001740c03060410202d003c03003032001d480841e0304040c0119030054455204580350302041c1d889a00d84011403d1620410380544400c440c0907071100c0401d4401040034140100640c1001c00340200e04940c036000394404070103025824156916942c40c3d00300600011198180c09000e07100c2c0c50000103024000c1d21440580000200f00246141d1074220 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 151731205 1250 151729955 151729961
    0xb04030809070815150d170d0f0606030507090501052d07120c0303140f0705090a05090907081209091b190e09060111030307030906060b0708131202060d 67
    0xc40c2112034490000d010030b1603202004031007114071491071190300520300000c2c0500c00f03541001446000c6c2c040040a01c001404896600001040520085858143c20402d140c0540f8403146c8207216070b4681440865a0365054200701e03c41c0b102616400800759851004403128498070744801c1c44403c02d51103000c0c800c40e4070b8400d110011a200700c00b0341041c00903118034000f01d11054800d0041001c1c41c3c0307408c0401d03801d03028105d0f4183d00c41174030345802c0c80c002a806110200080c0400d00f00200010720401a42e21700c3c50300c0c4080c11000d4503260580c03030604d036003da80c1c240c02d00a88003684106404107140750403110888021542c05400f480b6243c80324000040c1c44020014005454030040c413612130b800600028903640c5041d940d582000c000c1510b810320a001901410301410032070350215200700c40301c00000701e07600711401d807800081c030400c0c5003040002490700da000b801c01644000b5588043c090142e000c2c210940108450b0300d9010399920b01c81c0ea000382c078440001d4020100740804104114594 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 151732455 1250 151731205 151731211
    0x11a010e1005041a09030f0106060207120204140a02041d01080c0f01210c1205150603090f030304060906050702070806010902031918050c03010c0e1002011413060c09030b040308 78
    0x10034220304180d190b84c0070b1078403d1000310750842e00640c04a6a40d50a190030084a0188030481008000a41c2010303002503d89505014480c1481c2da52481e4400b1500e907a4000a000c2613801c02c0e130815070803c001c03044040d45c000e208410300040080410002c140d03145888034101ca15042c01420300815100078422254000c0110b00d0501a59141b0009c4034513240d10081e00c0300d85d80c40e4002404030214600505400c0c51036001c00c082c43d14060401103485100c8a50a202500480d001a00c0e55240b54680345010918142d446140c00003109010070003440da00b004412500c50601803006655103c0103e90320300d528880d500c4980c1c00b050040017060902da004641080d00c06030303910040202c07905c0b0354041c2c54019011640c4440d03220704e040203000d0248494144480d0840080c400c1e00c51211000f00000108101c16106205c0c8000b605481070007544031414000c05049009454503100c0c21100181c00400e000740c68540c1444601c0d680700e88201000000c0d2940109284010b846949040b190f400000f = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 151733705 1250 151732455 151732457
    0x10501171009030e09011e0b070812040203070f030605010e0105090405150405030d0c02030a020f0c061803030702030123010503070e070815090a0c02011104030203070314010207020603010f030203011a010e10 91
    0x24070f18900740385c0b5001d00756030181440640c0c1e030040e00c09071141103d9442c07540c0e10080c1d0103c2d050045d000003540d0758003100c0066a5680e00c03070ba116140c42c0006420002a6400501c980219103c00001c0080d56000b6038100e4201d0746206066a90310014427003040c408503001080c581041d02034100d07c0384000c0d0a142c10a01400c00c4034103210901d48980d044800c40703400040581c1c00407030455582541000f10407406d42040780544905565130011600502800603030900d041140c14150502c2c0d103080041d1285a070b0000c00034027100580020f0340326070b200381e041e200340c01422078000400c0b1402d00107803e40407620b81840b0049c00381d80f10750085815200180c100700101400c0c0100341c0c0d960381d40f0b914440c01003600500000351040301c444082c7c01c40c0c141090000300311509100400150740d0205a81048070303004080691111030710081c881c020301c90352070025070254010002141d020245240181540c2c0f0990003080042c80e00a0b924032100010008035002420002c00d22140d0b0500c0c030344d021001c0c142 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 151734955 1250 151733705 151733717
    0x31d060609070e210c010207061407151817031b1803071806080703050604020d1502030c070303050708040c0306020f07080c0c01080c0f0409020f04081504020301050117100903 77
    0x607036000a044034010782c040400c194807510740040007110178010f00380b0a1009000070b190b80d500e030031006071009562000c000c01410f0302185000502c81c40090003000e04c4031313075002000700400c4603a0034080211900c1e070075a04105500d54800308854940d080724058400c0000e100301c00a0240102c45e4240d0184c4020100e001c03259624070b040d81c5040007000050440318400c40b141c0e0b050800050229052680100100c4d480840e00f04081140811003d070007030b0301a249142c00d81000d0030b014180444007110300e10301a100008000403540c480000d011441d11995081c881d03a216100100d0b441d040554000c2c01981c5078203400c00004909500034880b94900068031810300402d07494141e1702d80c0190000c402c503038020041000843d82d0020889901061840106d418424070b04101d05042c01030b4020074441c507600248003419030200400750303001010ac0604449000b0382442403005036010a407030880c003943c2131000206214611035000c9802e0785d142d10091904040d1340744000041d001d008001d41c1440700e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 151736205 1250 151734955 151734977
    0x3170301030c120f02063103080906090d210f09060e010327060203090115120b04060b0603041202070906051e150f03040c0b39010203070906031d06060907 68
    0x100c81b005441d1442001c0d007202d08035040d81c1446410001203201b181110910903a05000061450081d514908826074203503407510030781000f00b0992100104003600085401441c00040c1040c40391440004c6030b19918240100f0030b20385c00380c0301840c5c1801000007080180d00c801300d240d44690300224494100580b40c05101081d03da003a12042d205520a03561950000300b0000e1661003405040600b031140284490481c2c98468800500202c004000780030540180c045070a0100e00d800040100f103009041c0c42d5241000e117030002007440d000403118054081c504001401641500c1600d0882d00d003c6d203418000c0f10362900000b010000e02c13502c80d500440080250f02802004030117040209001109950f0368203142c14517030100d183d9684504070100080002840344c4004071001040d04c189060f29a15040c040d20b03020905002e10000481950700c0031041041ca43d5200c407400342142c0f041c0e14208444114081f0300742200501c1c5041317400560010022074594188809000d0b40200b083c600034103100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 151737455 1250 151736205 151736209
    0xe030111160c08060c09060726120a050601092d06020307021e01120f020c0a08030a0614150906041a0301030c1d04172203170301030c120f02 62
    0x50001241410000d181000c90381c100008002c0440c06400100c004205520384100194864800c2c1344c8a42d01941c000304042080080407968552140c03003480c3e41070000030350040c1158607078100143c140c40c041c0d40e0001186c10b003040e03446400d0140a069440416240c10812490808458034400c3d004c1d401c4601c3c81e5004c1083c1510448010300030b603a001e55684c12607401004890200d0301c56a4a0018881d40803140700d03a003006500306002803000c40031507001d0f24007003904000d0045c441c0c42d15079405511915001c00442c2c8000358803403405d05000f04070550b1105140d034000350030030080b960040f9041501c0600300c820300e0083c1c00003400003804036250030744420b203076100d882150013441040301010006004102c007103040314001e4240002c5c56244512100000902c07144081c20217010401d44412040c2403240440480e4040402824142c101050411015200760014070041d103c038510728851018011651085078122501b085500c0c4000d42040007100d03600030003400032584440d0445c40c01e0700507 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 151738705 1250 151737455 151737457
    0x822080f0d06030c0501140316032a11100605030307140c1f030b0603060d030309021918050901020304020d0b100314030901080601051c0b1318030e1903030e030111 72
    0x3e14441c02070b8480051800001402030751180300400d102803018030800600c8411480c6544003403141d1700c0c01182e01000d44912010064038000e40f41c150b200540d91110000d5089118143e0301d40815040b40d0340d0003e50b699001c1112210b00400d075158000b0408040402c0d80c070340d100d600300d130500801d8072079143c013810020300310403841d0106049520f00c404841410356014890360700c43e0a403e54803d49586824070000380d0400000c000241810342e1200c6240954807268040290b80c00525180301d00951070705041d03040c4444400c103019090b8103040000d1400041802541e015035409402007034000d1051760741d0003030004001c3c004462000138401c004081f44813800360501403d6580003840e1381c0e054030400105000704c014000c5050110810030380c03000015910007203215903a5002d0001d0114041400618049200c026544059041820401d0112000348040300d202c1c1c030a0301c542240d5076080091001e01d40d5400c010340a902035000c010000300c0e01403404050403c500a000040210440220f1042 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 151739955 1250 151738705 151738709
    0x209180d0c120c0f0f060b12010e0115050a0b0a050708070311160e0a0e010e030c0105010513060302100305070513030309050307090228140a0503070822080f0d06 71
    0x34070100c0340d0341c14000c00040c107a0300c01d071151618080800d0710351180180000345440040100440c49a8001880403907070201c10080360003000f49a501050300400c4c0d010380340491840d002546440c1c84011007032403e405c140d00b1248050080028685001f582c5420313a00706006450a11200304402d00005000c60024400e00f0b1080d11081c041e0001d100f0304500d80404000e01c981c600300304040501204921019503540310b82d007400e011400010f040c1180380035200c01483e22441e84000307c0e0707410401006400443c140d075415950401c00c5609040890190340c02440080c1d00308411008920045101e5007145a102900f4240189062021180d01081c1d4519030300c150005440c1800602082c03070705114440082c920b112041d820120750440c03200c0c01e20034181500701c42041c4a010740e81c886d80a051003000103c1c4e85070015454044001c8042d1040e0b004480700070021781f800b4000f030041000e0141c030001d094a0820083d180c48529036a5802c0740e03004610014110303105000380c500c60300c194091040 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 151741205 1250 151739955 151739957
    0x30f0a030614100c060b041107050a1109040c0303080709030218010305010b060f27031203010509100602152e05150a1b021306090207110405010b070209180d 69
    0x1540d54a8502c54241426805038124450000918940035480c0c0c410514100940c000b040000c208040758000b400812044240311a03200d40455403006001d070114105044500851403140c2c0c41c0c00c0c441c00c0206a4000312001025010923850a0003c00e105902071070744100d603800c2c20010303541c403500014603010058036a280410b40010042c401c0100038007848807003000135142c1300e0610190284a100794000e14030050080304030741440403110761202c1c66010001c00d01406880000000d08003440d102e41c4240951402060000086200c4e10034003040d40046409640c090840c1940e0b20b030004448400203840c0c4c0504e40c21a10f41140c2280220424403e80c1d901c00200b1580a46800244030700c41c0e0780d958180c46510014441204038581258141d442001300c070360364000070440c1d8400031701613085a0788440f103400d00d049000f00c1c0c005043c0c1e008121850140306806610036440d010401518001d00441c0040c3c10180700b24001800c20102041d04400c0c4020104401030540750340510300f10341101c3c804 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 151742455 1250 151741205 151741211
    0x705151303020709050c0702040908120f0411010c17030a0e010c0905010212040b19030e010204090614040c050a120912020a03080a020a0f08040f02090906100803040e04020111030f0a03 81
    0xc01c06030100503ca008080b401320074407280c80c00b1071902c100c5025640000c3e01640d210141c03a810011414100c5080106102450496041002c1c211a1078442200c00300c1d0b1801038150414400e40c000c4c041c0b0324040b540462545201c1c10f040030007541c0c5800203401004042e0300c40d40791207070f1143c01380545001071082d03642707901c2918a4140020300d860500d040c000d4880701d0800007400040004421039002403281856070803103c10350202100140340d440100d40041d440403070041070098041c3c00c003000312a4440607002e0140044020401110b00e110075600124100300f1070303001024050031404184805407280003c2c04021078a81080c030b07410b244010401038120401900401d9040380050780c01803441c41085003013604244001e801c0c42c400240c010140124807000400b045554400d6078140e80d4080c0101c8024200f83d4102940c070fa105484500161000002c081031042d8000b01340c604484200391501041d407550340064416843d00040d5000700d00041081c0441c10349102e0051031a80c81641d000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 151743705 1250 151742455 151742491
    0xd02010203151203040e0408120406291008270601060306170307150603081603080603011a0628020f10050f0402041a040c050903010509060103050601030305070515 72
    0x9110100000400503c10a01c072006030b4506180002500d0507510000d00c245aa0b48950400c0c0505005507886808110782e01401c100402007a07401c00124540782c00540d081003120002030205c12408a8101900a4928603000503060310803285550403454400ea1034480c2406080300212f01c907049010041198061b100400500394140b10341c00040540180c10f02d01008079800131a203d200c0c40d00c014090040e200c400da0041216a8068401103502c401c0311603a42c8844c074410008650000003d40c0031400c200700080c5c0324141800b440c084a140c62003030961040011081080c0d68200c1c0c1841a030003403031180c1c0100c0e12408601412183c04417600100400c032007184101d031510640c110032024039810305040c0311851000e4070001e03400c154101c0e00800c0100500e10410840c02144603002c1c0d1150410151f440303244d81190007400c0b54101a0000c0c04150fa4228049542d0082880300a00d15840f5500420100384100c010744085031090055aa46802103000428100c1040d138100310601404000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 151744955 1250 151743705 151743721
    0x170403120c0c0c06090510080705040f06030e1b030a06020304060207120206160f0503070509040f0606050a1e020c0d14060c0c010c020f300403060504140102270f030d02010203 77
    0x40d0400400d001d252172511581400c02242083c0b000344061024014500086240a40140306640c09000c000312070b03c080d07583d41d0f10020040c01020901459a00510002e15520400b62240c051898000b0b0000c0c4030b9085142d5900009601c01001952030b540d09000040c0020001d404484100300a40d00030300c414100000e0040c1d6a481c8410782c4024848003805489900c3e030401e041d6540140700b03041498541c8440000f0402420801c4034404480340340200105000e60000003400c00d031016650740075400781c40000e820005100c00e100c20070160303001c210079150324a070140d04c2085907407041d0b44c00d49218107006c0c1028a015000e584841a080020880c0e48071070000f446030f0329002c410752008110481c40000026201e641c1c01843d004640210844180303c0c80140e00c00211a007181c0303108aa80e19524101100100015982150702e00460780e154540c02c507050080d60200e498420103a4142d042080303143d002900c0010019070032402080100080796800d010191000e1210340000d039407450f181030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 151746205 1250 151744955 151744973
    0x3030f130e0702010207020916110d050309070902040b03040b070507060501080102040302130c0f08330411190c0f060207061a03120f0705070503071d01060503010303170403120c0c 79
    0x2000b40110380c81032000101590303409074616000106150008020541030900721022000c0305c2100000d44034041c03000e1602540300000b50310442a0809030b0b0381258582c001c11040c1c0c0300d44d125070f164201003070000c100403501a0750045d070005000d0074802c0c500642c55686505580099200b14141d943c0403d0800650604840041d55801e0344035082080054001005d808500001d0080c410054110000b601c00032446c151600321040b81c025400104040b49010348000c0c2000441501460030b001ca070044035450750303045d940042d204034071108101c2d4a0f50030484420f040400203071420b02c152000b171804501140300903d8070602031400406c16546c50481d10030f6240011500340e0203907002d10052011200368502340c40030368006010070343e0388a80c1c03410424505a46a00200c0d418002c1030300003d02c440d00c1780320464461040cd250120660307078400c02612240000d1002401056104100c0017044681d102031650252207400c101c0c02c4039101d064400d00311540160420049045150f106080c031200c0c170 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 151747455 1250 151746205 151746211
    0x6030f050118050402120a0f020a090905030f09030a06140604050603070501140c010603020a0b0d05070e011409150a0c020901090903050f18090f1f0f05060903030f130e 74
    0x888144581d52404488011488400500c0a45156030b04040380440d92007030344280403212070104031443c165190810700c240b524000f004034071445101c0ca0025280c51540103581302c45070410055814410b0034040c09070150b0042c0d040c00e44c1030180750b10410000340c0902c540d01088800b1201b503441c034a0810244422a07001a100a02c20b0744650300c05c0205a90008146172040f9048070b510b0b4862036000300c45800742034581c10080d400800504049042403481018082d010403820781407009468000094414509403a1160300140c1b80e10880c40104520304000e01d45000090908040c03034200c440300860540081c9801400108aa01142c040d85850300c032032805403d49044c10885041079aa024000b07201f50720b881c1c04545c0c004290382c5083c181c040215440c018010304002c81030329000b082942e80650403101e451640800e035201004103164085d41c8001c1d170f01d1540c18a80c130581414100106c0d0303002900413a80c10711080010020310301d0110003500c090300030362003002c80140c28250f41621103c401 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 151748705 1250 151747455 151747481
    0x608090613120e0a150203030402091005181f06030c020c06120103030e0303070c06020109020414130204021c060f05010f020a0818060f0a080f06012303060105220603 73
    0x603040c00414607081c0404920b40c90303801c0140d20001e002001c6180404580e00c600101318000581030701281d00840114800c510850b0300442950301c0c02810311412000b8020781e5000050f0808584800001140c000c1d0050002410300315500307207680c0d682c061a071035508140002900c462140c0c810503010000220005c408450650a2050700000c000c22400141700103020081d15201d1403649031000d1085500180c0c000550041c12512504c000c1c0c0a0311018400b24022840c2c6010840f001c0c216030402c0e4001d925000c0c015034088500d8007003002a4003e500011812a2403c0d1402901134007845100300400ca01105002000d1800c400035100c162000720403400d64200400c580e0004144e80c049800040d840d10035400c08900301c001080d81405650030410030110b0001d1150640c035007100d0514400d81880345009d20958903040110740c0c1c0341c2d040c207040700b034a280d040b00b502c00c1381000405158002018545242016081001040c00f0f03060b801c0d54441441046800740541941030140036584103103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 151749955 1250 151748705 151748731
    0x9030708091815240d0504020a120b01050910051e030f070e19050601120c050715090c09020a050f03130f14010b01090315090f0602190e1002030901111606080906 71
    0x1034038984c1c11041c8240a654020b142c2d9490001d01103640c0d0b038000c000580a01c0200440e81c3c201c0d032a00b100c4160080c01003070f2059403400300250a4a0000b9940c105899000c0c6c410220703612130f0031305207442d080250180750303060241c0400982c0940d001c2042c90000c1000070880f03e041e0030411041e5204a41c502841c49449051000704a010b0360850404075803141ea80400040c0b24030403c42c200c0d03060240c4a030081641c0c51502e08007840d125142c10140c1603a0084964164003a66a21200200d110f002400740c0851000c2c0514107610701c07500080c40e40840c066003401882513042d55551441c0142c00c004841d0810042d007440e44140c030901c21419403000a080480082e070554039191420581c0c224101d000d40d1b100c3c5203010420800540d80000c06d0780c00007042d9105c106204030700503183c0322885044001a2600021f0f12185030440d580c006400d5075030040c624021801004403211002d0004200452085841d08082041d1820030a030051404d0344c0c480d881c40c103050002600301800034040c0d42021030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 151751205 1250 151749955 151750009
    0x4150e091306181a0403020a0b070e03010b09041104020c0705040204060f09080d080c0c150106050a02010e01060e01090902031e0607080105030a0209010b22170705010809030708091815 81
    0x40608030303061111304211034040b080e98551400701d00e848503003100100061a10000c4c01542d6402204e00b1a402030101d009101b000c1d164000e00a40d408221005003000815120108141c10990300604108a00100b641c020342d40f140b0104013643e01079481500000c0d10382c1c1031400e6566200d4110703030203040300201070500e00c4a0020001c05846000d0b201c503001c4040040d5209540e181080b4041c0c00c0a00a042e83d000c56940f0302010f01141c101c00c0001e00507500b001d00d0f9140048040c0b00d080b0580380c245900c0f590f181d0800d02448010f104240040703030540315141d8034034482c10100582c02d900072551001424031340f0301100b00900103641a409140268400c528450050742c6460709207040d80d1052180c2500c030507201c441043c441b4407124402040c0001180c0120b800c000250001101c910218219440c0c15a148011109404100d0f0710410300c2d0420f001c1c44c0d0005a150006142c81c0784010100e0451b0010103201b4058401c003a030302c0085a88001d03001680e1400d000352a601c200c6207139440540c07460 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 151752455 1250 151751205 151751213
    0x3060106020d030c12050910050702161406120f06040c0503161d0d03020f0c1909051003080d0e060708101403030d09030909061a04150e09130618 64
    0x40c005030303040c0c180b6440c4d50140520358824980250401e1401405106034100088800d0319415040042d140c07550134040024045400014414a0148590010800107190421003c0c006120303440c0568000030070042c0104e04942d1030300550190000f40707544511828003008000445654545030018400b05108203b01151402814240c002590030201e801108510261524041c6400080c0d480708281049006042d03000803441204c03240d01040300c064803556000c11034244a55610805200c2c00100b05100a01661f002981c0100240301c00000c51a100d51301c0b4101c6801c80200001c00c03580e106044200110308020490700098942001625420800c0794024540c03418010f84d0050351401c42d1021150300e0400442c2d904400c596030403c80941c452600800400b051702c2038004045c01c000c40450b4440704194589140c801d220001481c162800e9000e00c11503e07403212010502c89074048002e40750316503240c070620907080a0700000d508800e42c6406800c07241c42e208219005031208801400107 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 151753705 1250 151752455 151752463
    0x4030c0f14010c02062502090a02120a06030b180102041a1c0605010522050d031e020304061d0f030a05070f0b040305030f1b0318090a0203090d030213030614070e0306010602 76
    0x3882c20b0001610f07410a8030f01b1460703440c5000b08000c0d00011250100408011168003078198500c0104069809843c0d80480900352495800050318042d030200100d1281c1e0340c00300c15521486903c00025003415a2109000510555160100000340d400150341d1304580c4007480b640b00d0050381060801105041c0b0000a02a000e6940941c018004442ca448070384209002078400a0100801002c00107050b8600100b000d4941101101d0303826940e07080e0f4100a0010003a94150b800a5a41814421b403e41001c40495803d100f850707000140314110340002d031420320403100c115000e8001400c40928120210f0070343e000e10740c40a40d0441c3c00384424000a1808030071100360030100e42c0c0843d110400d91024148224038140d08481c141300001740450491508041600c07200e508540302109541d50130100d000b680303c220781c8144160803242000305400d0290303029203400011101c40c2c4c1d90701034590741c42070219502070802e0b40300301e00076004103c11307140d00880103400c662040d4081d21995140400103595 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 151754955 1250 151753705 151753717
    0x1031a0f2503060909080c0105160c03080703090203161404090f08071e050706030f0c0804032d02070509070e01021203060d021809010f15030b0c04030c0f14010c0206 73
    0x21a000d000c1c8414080e00c80d4215802400c0c10700c2c010804070310b4500c0c01c2040c2d5030046800c80041e50a000000711001d4803051400302819483c0c403020a40841c03075a0807070b610030000f0182c81c01c2c1940d82c00100c003d80c03810092485100800075001d5442814009070100800514030707842d10a504000014002030800e00c00c140c61180c1c0006c00340c5c0c481c0320914005001212540080d41205181519201800000103449003119030544082081441c050101400c0d075514425900108902e1000304000034403555290780300c40e0400300701c02c2c240584142c0030031034023080c1c5401a006910841092180c0c0c41d18081c0982c0050b03050a1011140107c1e800107500c2d900790b260421800203001c80000c0e0552104800d0341c10507503004181d050359802e00030b4400030080040d103148000b586088403585086040344101d1100359944030f0710076030031455665100840031006011000c0c0c004107100000000c1d401c4940d071409010020f035403511850908154059070341003411240d042000200c0701da4096107449085600e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 151756205 1250 151754955 151755001
    0x1b06020a081b010528060605090f130203070c1a06100f02070305010906020a0305070e130e0c0303031006120606050f0d0e0a05210c06060409050a050601031a0f 70
    0x62915400354050b0b00742501035046540d55400c0904224080700d00f03c248214183e0066008001901e4000503c0210b412600030000416010040792001e4684032030310908600e002001403020340e03010500c81040c1e030415103402c0082151401101c0800c010214074000007056404400389070303e000000181c8642c00d0f002c6460500030007643c50003007240700780f00c404095074201000b8800c000c82031406e00001e5001c2400030001074541404184081e00c80c425110074602e00500181c054811080508010f00c8401694945440303580a404803684040c805103124404244d585074146260140240c965821030715403a00303aa24146023800516080701c02d50300e00130010310702562034855203c404002818000140386044c4035191580040000005030a120155044484460081848964942805404402d03d40354026000050481c00c1540c0f00003422401801110010191500e40304d007403100a80040e01e03629260f00440903000d05180c040c5400034440102021989008a40000c1010145181c61 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 151757455 1250 151756205 151756207
    0x20d03050c070807150905030d0207030201050d0b150c06010e09060720031804060602010603030e190b03070c0506060a0806040222060e01090b030a0b070305311b06020a08 75
    0x198410100b045940058030014084074030058440c09000c5802c2d9130f1015510029a8038940400c580c1400701c2c0c2d42c80300b10a950010501103040d5030064510750042c10300400030035920484440140e03641c3d03c0c0300920105030060643d4036041c003c1032034105401600b00f280c200306030a050001c0c541300006c031164010300d9480c0c648003021b0300c20041e03080c25000a81030440c0d1321000c20310a20389501c0680c0e04425003030882c1c082003059038483c42607099810912000c2c000c030707015010700d0301e0904140c3d0f00342c8520720440603071403519034942849404030340007a102c0d000051190004441002400c004042c2c00030070031200561001e181003a60342d903a96005000070300400303212002c42d8541d086480306414201c010303082400480d444428400d46a8024132590901606003401b030070450a0201c0c2408041c0c1e048012a00c1d10740d00e2403029005400060a40c0e980314080022003106010505003000e001aa0060346104581083c10201562021003000a80c6801008804c11010b40c000403400d00e6164440416 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 151758705 1250 151757455 151757467
    0x130b030406020415050306030d11070b09060c030f041a120601050715230a02030411010810090c0302040603150806220203152d0109020c03070218160c020d0305 70
    0x10041e019944c45078801902220110003100d400c0005103108040940845105008080044403c095403500c0f019050700700800500c081220b840040140700f0025112504d018001814240b455012503039585404401203810703c02440202011825555000d0740f00c1d08002c4e0303100020b0030380308010f4040c034144500054610304006a003e800c01c6880c0301c14500704140001090701d07001126802400220700c2e0008800951103460a00c2503a00440d000880525100c1c0e03060010740742c0082c09444103500440001c0001600c0c0d0b4540a0341140b403525940240c0c440e40741040c042c054406800301c10708400d54101c0248000d88002982c035501c00c41c1c0840b08452000d03220320040c4c1d00e441d0900083d406014030480c107070200040c502c580b030041001402145044060000c0b201908030b00d01c00507640140d941004004004480c0c02400780c2e600b410703003038a14022850703000a140030080d0810002c8011a40200004504540c51891080344141020010790000e51f00280740c1c40301308440281403010218603 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 151759955 1250 151758705 151758713
    0x80604050d0c38101a12130c090603051006080a02100e01090f080f0f0321040311031303030e01052b09200a05101b050f0313050406050402130b0304 65
    0x1100581860014000040342001e04c0244110000ca005000c6a00560041415400c0650084500c000e0304061002c829480713190b280361800c0d10a81080e90341c2c0c04200804600301c00c00384a40e00c01540b10344010002540803a44800c19a510360b40044110b8102c2007210740546c030380090701c1c1a9128203243c0a842d00e80340b0801681c1d1066240c0102e220001001d00200711101c0009445580843c120100c1c0c0d1480c03801c2040e2035a034410541c04224200c40484615100c100e40402243c01521904020001d014000001d42c5150003c1808400e289142441002415008040044e04003c00c0c07034000d02d8a03003013220000d146c4101c958407446c01c3d6142004403401600700d41c0140f100c1e03a800481d2103140c500c809802148800d10300492807085840391000589482c00c602c000c90401e056032202004c0c1600e188201d1018402100e0558050040010202082030b007400241240f14015900004031814002400304039400b0350082c50203a0320400812401740c80070240c800886601c120b800781d070703aa25498 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 151761205 1250 151759955 151760033
    0x503060f09010204173a0e0607140a0b060301050114130608030a020709061d060405060a0305070602070f0806131401090f1505060405151c020604080604050d0c 70
    0x2115814900d00945c81018110020805000c40101a40f603441d41c0600d140b0b6018001648000c101000b40b00298010070032800744d1554002200024220350812005031140c1604002074014510290009403a10042011215036039030400800c0c0c4c000c1000c0e604042011050420840f2a944a00c03104180c3c120564000d4001d00094a6014180c0f030b01c506200704043d680b081c0c540100e5075480c0c10007001088c0401c0100601e120300354028003001ca0b0b504c0e000f003071000400d8042c100c01e4200c0c1213100c1c0440807940410890740203103030560041242510b0301c0c0f82409c000c20340740c000c01c4c540d4203e44248640b100807105449a03154101403224a440807204499005005251008040300004503220b024030071004815804644d4140090010365034900c100801c40b01e0480d525050b220405e044507145061000d2501407102015045040e4040c00e50005400b681259110501e154081c90030401040401d010070304003104141055004803010b9a55400010303806140120500b60941115003103030001c00f = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 151762455 1250 151761205 151761209
    0x60901061407020d0b010f0b251a01060f030e010203060f150d050c03010504111c02030604020903060901050a20162d030e06040e1506070203100203040201080c040503060f09010204 79
    0x42134420381154500c0c28a285003824032039502c146044102c0050391010030822151121200c2c0d0162800c9100718a00b160141b54140c2c042e02c00c1c04540b0700315640141420700e464040c00141e01d0300102ca8104410040c00d4400e030726000410b50340180103005803500c0c0d450035800c141000710b03804110b508002d80110080e001c1c010800306050300f88001e018890682e94002d50580b44140e5003400681e403100142c0c4554800c4214001541003803100f242282207903613028640050004101520b426890030000303192403001e40381180103075076400902c035145105116100140c404540f07100b003810025000040d850080700c024400426111000c130040080003500b540c60000c0801c20211490036040e08030307104030340e1468110007003100c41d1104410380c82d03c0781c107480844411014007111075880420740103103c001d0701c2c1516040302d03041c011040182e40900114113040c00050340183c480c9000e000041003410081d001c450340d0001000300f03004645000c40c0e202c1c1d00c480d414204644545610714030300d0083c0310b10303 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 151763705 1250 151762455 151762459
    0x12030905060708070f090b160302030d06060801050a05030105060d0308100909290105030307020105071505012702090105090d0230060c160f030c06060b2106090106140702 75
    0x1901c2001441ca4001180d0740c001d88051752001000c10042000359603000d15402050808402440740150000c445c81800400504c07a105a9040168400204040d80d03500d0f004400499030102c014441c0c1c3c10080040c00051000b02d0003405141000c40115450008104c0050100428413002480c0941900000b00050811420401010300c0900705074004240120510229191410880c440d400258500c1c0341a240c0080c0038516005499006584662200d0822125460040d41c3c081c070502032445042e0090065a40710301c083d0fa44601500045084410304800107881484a81e8582c0d0740b0209071034480106480c02e87e1000b041c0c8c00019130620a01810005401000d10701656183d0415402020540d0180403036070203407200714250405010382031076200706100046107400450042043c0354416802030400440038105130320307a401030b074409411040f850780380000c0b550030140350140340280080760f050408030703203080031000940d2440041c46070b0f80800240100030442c10b984c1e24201d42140d030740 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 151764955 1250 151763705 151763713
    0x21005090307061e030c0207050105070507030b01170d05040305030a030e031306051305010e0321040909081908040c0e06040b040906050915040309030b0a0603080d0b2103040312030905 81
    0xe101002041c5480c40d0303940b1807001510035883d41314103009014004042c052074000c0c0a0642c14030004540d240c012050a4400748505200000852090348906001c1c0210011202000c01100651031802e68685d490404125080000700042280442900c6420681d0300c0d02081030200419620301d1801440b140c01d4100100110003c0c44940050051005c8100c84e1000c5542035514001543c5100307400460503055000f904034126000b00c0e0b0000c250040703042020403402e194641540c481181c803000d80c1201c40710b0b000200404210092415464205010320304951036140559415900b46120703c0340c81140b48502c40828110341d81e40e081604940000703481084100c9d19814100054502612701c0c0165000e21050b02002c80803507007030349100c2c84d050b484811003d881d42d41d5007074008000601d8032460340e56440010000600d41401000c41c005102800b148004540003081180a4404030907000001005040b808288001c01581c3c01c598018420010030011204298083c01d840762004101d809 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 151766205 1250 151764955 151764959
    0x120b0a09020604180902090a11031302010504030b090d080121020f0301060504090c03061a03150601020c15120c03070f0c0f060e0610050d02011b05070b0c01020c06061c021005090307 80
    0x100c562018645c1e40c02100d00d50340546034030807074508481c000d00800c01c00302c1080001605040d114074080302c0061042c909145003603540c0e11482d0800d442a21a0840b540203043c07004001e5510581e02c4d0301501034001400c82e860302211008118074030301d00d00240242c0282104401136a0300b07600c1a0010300020f0014000400c0701d01d45198901140c1c0001c0f62101d2506c94689461000725110209407200500140f5152501c40410f9018400050141e411449802d169812a44400034404007052100082c40d4850442c00c40160030b4070340051580300641b01c20f000300022036502c00b000d9614542c880c10151450740c903504201c6041e6400680251600c0c3c00c1107064250050005407803840355250792103420031242c41d1420030014807000c032406400100200e101c41020307442200c440013002d1050b411035403c01e94070403c0a41582055920b19016507022600b03003030311002030140943c0030f03100315482c09410f090901a03948451090780007900422107800c0f41d41046004600312840f800000341110b851507 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 151767455 1250 151766205 151766249
    0x2040803070204151d04061e0e19050304271505090c03010e1602100911040c0905030703170c100614010305091e2b0207120b0a09020604 60
    0x3900c80306040340143d24040b84013080c1ca0300c02040c00309980c0704581c4141402d44000034044e91362009402551116034404078182c1e0b0341801204001160340500020500007011401d05042510703104450304a580c0c030103401c45c001032000c805c8900341c0f100c0110340d5200717001040f05c1c42c61103180f10001c00045460b00300c07071181e03020031000c00707004031181114240c0c0b061356a40300d4000750f0f000a106030190100304c400400c0c4507612140701010514941c1c411100e283c00b500004c5004c0e204c4410003690350083d41003042e036050506016039040c80540e800c000c40c8051a05010980d104050300c4003074041452024454a401100000c56640d1001c0300e08a41e5910300c2008048003c00b0385104024943c018030f94102c200394001c2c022180300700c0644020f0800c0c1c020718240c07801910340d10740c0b01110a0048098142008040c442101e954000c0d006064401d040c002c0c50113071400c00d850b000300a0b80c3c4a451280790015026183c00c3e40d03c01c2d249080400c0341d258a1002c60f0440c0916040201d6500c0b214200d03001c90 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 151768705 1250 151767455 151767457
    0x81603080a200a2a030809060d05070c0204050603010e030304060e070e070203130501141219090501020306100c0c0303210501170d14180607020303130e1501210e0102040803 76
    0x6203000d0300481010804143c00200445508204280000b04c1d00400704040746103032000e40718209025200f07502d45224030300300c0412608201c0307410011071b04c032030307646001d5060601c00d20b03600c1102a0001c00c21043d440000c5503990200803c0104034940b02d10316a05513007030604c0700100601c1060010b81d5079050290f0043d4898008071400021135002c09400541c1d5131250001c50946070a50807090301c2d01054aa1600c6014002400d540c0507400505c010251140c0c20f116440d1098082d500040e100c1c10184108203c0151412010003081a00291680460f080098030002c580d458242101d41800e00042d90300c4000300c0e02510700030103180a00001e000c94aa0310690510220b000543e0081d0024041c107507034a14015040143c1c80344248142c1903908524410412140001001241070200c180e0009141d903200c0545105000300d568010000c1046115420750003408100e03410b404a0702020000745031019001e00b1000300a410513042e80025070540c0103030503169200d0020356641e51101c91055036 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 151769955 1250 151768705 151768723
    0x5061816030c03091502030411210c04151701060819031112031f0504020703030603020112020421060f0e0f121206040b061201120c081603080a20 64
    0x100b03080091a568242c8030348554110103501c02c0f580c01c0c0305c61191040000039000100115441d40b40b2046404059507500c20340403809600000c00b107164101c40c15120b04204000110030300440c20036810f2400400446414000d603107682c0704080000780e92030b0f6074a02601c1280d01808041c090b86450855a00101c40d503440410b0207920b032030000482c0303480031aa903001201403001c00610300340085000074021540e902000001544201803264844000604982c0844001c5002c070b03580c0d14040046582040c4c0701d100700b0103080c00441c1880d15003100c0107040d45000100700005000030311120704101c0326501580340204254410403100d1710403401c05a84043c00c6120314420b214800040c145c4031071000440302d1420b442100e100298a5100c10301014101c18802d49504c0a418030480c4070300c80c80340071403500825490740f409080c6201800c01215a1203140c0204e00544c0164002c0501c00348480d00c408100c90740a810305580d80340101084034140b003040e43e240d0004c2c80c026101c3c40d00c40300004141d08 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 151771205 1250 151769955 151769957
    0x5030604051503120901090e09060a05060108190207080706020d0f1a010905120a02100f080703020403020108041101050408070806041a01080a11130c0f020106090203060307030605061816 82
    0x216152000400d090140041802c0d5040d0300c2503075407030b440402c9000a00702c0e99006040070300c86941c889550344803100007100e01001c4d5611610402c03020340e085024981d041002800e0520746800c2401c074082c0e515004803d25401c02c0e07000191a0100a1040c0c115a00350341c01c06000c64941024820b000041c10b607042000b503000741046440c0c401760360070368110320f101007050312108040c40c6081c003806501b036200b03074602d140d82c0202a42c500143e00c40780140e0b901c04c2880d55490304160310007000a408420094014010584180b0040c40142d802c000710b00c0e0032503000601e1040d114504001211541310b0b58100803541c0c05462070000d2000c0c00085d24038080c920582c1400c10440440c002004c2e5080e0074403071009030f80d1110120101181d616021101d00ca6005000c1c0300c4032034400344001003a21560100c1d5000907049403001c032601030782032080e140500100d00040d4a903042c1180000e0791400c042c00050059652032000c112203665041d1608480300c0724004800c0c040c41d054010840d01c10350400b04070 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 151772455 1250 151771205 151771211
    0x10020307020f061501052d13080d020d050301060813060609021206040207080912160f030209090706020c10020f07030c03030801080606030d0804050f010624030b0f0402070510090305030604 83
    0xa001d158030304d8038058905506945190900c8850000e10100044074a02000380c842d58005000b417540d0000010071202d18410728004a80d0b2410900c1807409944082071403c40d041804c4113528542c0c02012a41122082d18068100d500c4104440034480754a5400400c030f00e140210000307201900d03802610003080307041828181079640101f404142c0c41503a07002440302d0020481c0d0149440d00ca0401500b082510007103500118014003801d41005140e081010340c2124514100300314035103c5d4080387e220709820b024050040c6401d01c00383d40c820390000950710a1050000c98012540308000c1c041482580d141102c044680d281000e0180e1801030209a00054602c800407030306260010307913940034590240040050160081d4111503442028100f02c4882c007038089030344101070003402100090088203000714102c45808120403a040d03c003110203028075041c21281002c1d540d89200d4503c103050155005039441c21146404d40c00c00c02540714403450186060441c4040c9a44803000e141300704016a410 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 151773705 1250 151772455 151772461
    0x90b0a1d061f2709080d0509061504090b180c1f080c0a05070312090203060405070e0a0c0207050f0409051603060f050903070f23010203100501090312030c0210020307020f06 76
    0x6a0784152000714070341c10082c000d070340c608205520f5a201c041541d004403249810120302c0d240c00e40940c1c0302610000348a034040d00c1030009c010b001403480400d4030310456080004160350740c2c480040d402d00074056409244185c0b040102044217101032a400040103001e0700f241b003600e00507014001040054240001c11100c0080d140740040411943c02603002c0e01d89a090070030643e02294145d10009030201e9a5448111160050b2000c0062500551003040580010707810035440440108008181c03c0c102c504080c031401b00c2940115101c001d8a1064070603040f40d11000010070301800e8100401062403080d040c01c52050580d0600034403d5a02c034040c00e10156010f551101c05840c402c0c0d400c0720342a0002c1107004c0006031904c2048140307910901c240d4010681031041c030501d100c1c01e81c1341c12180c0c5c2d4001040058911210700300700003510090038a00401804c60700c030a01000400100c0009040e69035951003622030003002290b2250000c070905554925200728001d4450024110441441c46a4804 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 151774955 1250 151773705 151773719
    0x1c05060d020105071202010209040204080303160503010f0b0304050a12170c0708160c030c0609050a05040e0d0c06020c061501030507030b030c01032409020403020a0801090b0a1d061f 80
    0x4000903040d0140e5505042c048280c86400d01a40e807201410b041d5075003000f0601042d03d480c00036100a246490185441e490702100b01d008440380412140c1c10408100010300062003940309900a581c0c5032403c2039100e0f039407841c009150040c2102e0140c03107906013006003d440c81d40544070010700c04040e02c43c08030b59203c81541080138000d102008200d00f10074425003040701c2c080d984488040d0b0080034403800182c0e4a44415003004515004103002843d0381405100a0030115680e0001f05400d079010401c02c0140606151104201e07191070080000c400c500009024842e0142d41c00740a424040d60070a00b4400f1040c2c0800c4c66074017405020904060000f0038080c028882d40268120180140c000300e0000710044005025803440794048005444010040b050088020f10181c00508401660f0740d046004010207580b140d402002c0130303130501000400080640344010342181000320003150005a650700c8010b01c4031a00c5016000d4818002001031036400310102d80e00e040c0c60000c0c2e002606840f000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 151776205 1250 151774955 151774969
    0xa050f0403060204031a0907061103120c1e07120509060c0f0a1505100e0c041806140a03120804080d0906051501020c1f030608030703030c0207050108150f0105040b1c0506 75
    0x6648020b0347c001d6101000064054403c448a04ac0036a0550340380c8031080c140381072041010303141e16412000124241c2e5000c0d0380c0510700071440c1304020b4440e046c00c1c40c41d034a01703401400360480c503000c01901185083c00d5403500000c0d144401c026100341c0313030ce442184030900c3d1744007480e031419200d1880929014440300c2180c0301d0103004440c0711040a0300f86040c20503100c001d00c4d0103014603140d01401c01002900410850115550f0040000f000c0b4a07240f400c4d040c140d21010704011203204507440041040041c0d50403000c120525180d08040c1642d503076909206c90b45010300120861114100001d000800500e035100510901d00020b0004600034084012652120710381c00f016004200310b01420382c035120624003080d45450600d0080f0b4400d03103411046046411040c0c1c02c40200c0e8440088000c515010301080003d00403e1800901601e4400b0b01e0984501c0e40040141c0902d41000000c6016442141102d01034160496050343e81c2c001540c1501c0304514120600f000f035490800412901d2620300 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 151777455 1250 151776205 151776211
    0x21806070f030c021201020d05040b010503030a02030a080a06090903020a020a0e0c12040f020a0b070606080d0c03030e0a0b0106090e01050d05030a2007090c0305160f050a050f0403060204031a 84
    0x1c0307161401494981d40655501c00b000c0f000380c0e40704034451407950804109000400c02201112004219404c0c01d14010342c07020f0060b002103101c1e401c1072000b040e48540c00015200413615614000d42643c491103412001040c658100700c0c0301600300403160046c143c00081e8800f0140c801d40e20320b0034259680380c01c948042c5003038501811041003040ba1400d8089081d0003d90000d0241c001c1440780111a4009100c10100c2e500c898040c050200c3e0400611231244a440001d0204801500c11a8580d220050030f841d0624001814180d41d642800300c0800108400e450700795018040b006a541c41e403401904855641c403400030b55080800001c0759506001c035607650744980c408011400c0c2440c2c8801545d880f000048115480240b450000e41030010401100005012080c00020030044030b860050944030010302d4011880d580d0240802026444400200304901d54a03210f038a40b003840e042242c252180440c400b00c50a00814080148406030303009100700c900c10308182d442d60915070b801480b81c00c022 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 151778705 1250 151777455 151777463
    0x3051f050123091e18070816050705060a050910020c0615030f0a0b0415051009020a0302040f0801020d060f0e0c0703120504050706030c020304030215090d0f050102180607 75
    0x1d804200c0603554a0301030101401d282140503420011400c01203201c60442c0f13400807003003c04049035240642050a50503031500c003040c4101480d1324001001408455000c0d003000d8441c103101d999508568400c000361901d441e8054261150313800c0c032031200009000700b41e41c220317030b14061502c00410402461088400d102400409400381e50ba95403850402c06100c1040c041d05801500d04c0d4107040c0d8000d0040d100241d10403210804d071402d0500745003181010340c40440124502e05401e000e8042032514000040381c40b00080541c2e10004010210f002c1d000d942e0000020903041d540c04908820b064002d0005100c3c015010840f0a0b0765044802544110b803040c4541c40d110318001c14a89403404006006041c00303410429102c0c140c040e0b1800845104076400d40b442e0700803110900860794940a0000d08041034030056080c03d04580028000ca43d4104152703082807000100754180b40c07240101c251915800101c4031000355024200307a4040e50000303101518405a10010450307070300d0288140e501c11600 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 151779955 1250 151778705 151778717
    0xa080705040e010b191d060f090402040e07081515151303170d0f0c020c0f0a0519060806040c0c020f03120c0a0203060105460603051f0501 61
    0x2500d01400020103212403690030654a408103440c00d40c5070b100c4520f150b0007034440d1603060240b402d010b4000c0c4400c04100034250360040000c4c00166030b26110321280c4024111417610300c03501d0f43d01c00140102803850f002066070007481d100141c000c00229480e88050600080c002e81070351172800b141c107e034110f08541c0c0d500c10b00c1c0c1000200880d180078040c0c5200c034600b4409450181c0c07651904c0d1000e9201d400c13a40f424040c0020a036020414500940301ca0420071002403220001d0808040e40780c0c140341882d075008074a0383c1004c44040d607820043c4030061102078900a0700b0f100c01c010240c61841e80c3d00600c00410010004108281018031600e443c9000b603640e10030200000c0c0d420440000011065507606100e40d00d011038484080000070a01000400010a5480e11501c107060502ca8140c1c4054401c40040e000c16007100600480221000b8203c0f4010010f40d01301d05400c00210380125100b040000325000110703009416070301c5103000300c4003200c1c004102c410f65280320381031200b140203076030020b00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 151781205 1250 151779955 151779959
    0x507120608070e06042f040602060c071a0a021216120903090513140c0a081b0313240c090909020603060409051516030501150c0618080715050c030c0708030408071a10050a0807 77
    0x71a00dc40641c01c141c0701c00d8090f1400c402020241d130310581c10780d601c202d030300c2076020400380081e085204a111f03652800d00a020b80c00c0c2c1d5490280102103588103190180343d04000041c0102c0b41b59120040d1501c80b140c1d02c1c5a01d00b80f44481c5041900304004171800308200ea400300f60f007140a2090b115000d01800809481c40d41c0e41a598407580d138141100f00c800301030040c1c01e0391003110007284a000d240c0c0c00d4203002486580d00707000180180ca0307592040e0030561412184801503194070040f03d903c040155400304400c0300c185003203840c1c13190380381c0c10003035104001041c851100f0b8100004240010260390a000c56602c0c0e0b100c210601100c002e07103070082080001e0040c0015120342104070511a42407020070044c01689070841f05600005044803000d68082103010004030501c5040d40000303440c3c00d41401d610f8141000002031140f1140074018210120004041101460456030b1141d80600d0b0080055226407010701042015a82c040c8001d46c999404501802d090062800301c8100500600b000c83c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 151782455 1250 151781205 151781243
    0xf0403090f0b0a2a03020604030207140904081806040f080709020f0304032307140f12040303050304050109140c010908030c2107060507120608070e06042f040602060c07 74
    0x40800c0900300c80004c1546560480c0d0b0310507150400700d40a5000b0304814609850020300b03151198000035245450080b14000d1501c4a501c07155000e540a03c0c129038640600000090480f416210320b54062000200400c03400403450428048426000c1114556a02c903c2e034a426800f840c40c40c0310304240284001004248650010b944c4040305800c1d200041290104802d4264410740043d1070071080461401765692040009118000340900034041c1c0420b06030440da914456071001504228002c804102440760a500c036031030003503020000002c00140411890789541c20b04080d1804201803110008401c0408811102c0c2400c0b01c078042c1c010955001540c40468200c810810b00c024030a000000c00180c2900c03c440c0100b0454032481c04030b0310100e40708826207060340c010008035002032104100b5404812051a00002c003140c01140072001ca080030188100e080014036108006904451186a22080107005440140d420b550440d61001c0a185151107140801810a100102040041 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 151783705 1250 151782455 151782467
    0x291909031424190606030207030206010e0103023d0e0102011a0a05060a02150a200f040608090f12040501021006030c05120a0606091a0405040302060f090102040e0f0403090f0b0a 78
    0xb200020500e01c1c01071903c0062982241c406410130000700754001450000e142e01003003c180104420310706d504880d07040da40402d803520010351603446000040c1902c03480c40102d40725803440aa215034248000d40d40e03a010000c0c1407056401d50b041c090f51809850201815101c0f07441c40c80c41c0005071080c0e0440b0315102c144090b0340e0103641c01c40218010118040700c4681f6400340349006000943c0d001c540c1d1080b00e1400c44420780c078512510f4a003001080401a080c002030140c400b00e624500b000f0305580d940c80140c80c18800c4c0040d00c445103015614031402d07c141600054820351744280e0840c1d008000c090204000c0301d075540000341c40007950042c01c0100e0f1170070306000c0c580021003000383c0f001085182e947c0b5084e104070f500080426511505200680c0401c410140342c00d0300112000e205c00d00701754030065100e01c5d0182c0803c4410034a000003401840e0250102d4008050020302c2054600e4440e540d181c802d001560100d0014880003400a0016100483c690a42318000000c1e8941180d1034016142 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 151784955 1250 151783705 151783711
    0xa0206011703090a18060f0311131d070e07030915021303140303250f0c1e0302030c070807030c0e0a060f0305010f0f020301291909031424 61
    0x70030721081200109903107580e0782c03140c002c181e50640324003600010708180040d54015084210b00c003602042c2000440c240c28485c2c207e44d40103590469030400d4464001c00a0851000c0400d00c1c410104c0421000820008401c012501e0180214072144c44016048056980200000c0d08232110783d41160001c00b03865004000e100d2400d07500010b100c0d03880d51404c518900c0b01540303000b180c00200800c50042184282401000720440e10030156105041001d0040b100030f42020040001e1f220b2028204034418001d011007805040c0082c00031409494020354a1303005081c60f04a9004107040020300c0c40001840b41d042d80d030302448140409091084a815002c0b00500d0303150915143c100004016900d4221240598020340011a00b003501c003851009940e6000c00400314144108010020601c8035040c9580003134110745807102d40f03481c030400c81e4414020110707461421114074444286054002d04a58200c038070039990b100c0350050900009894001c00864002800c0300104009c041102904138158 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 151786205 1250 151784955 151784999
    0xe0301200c010b040c02070f12030804061d03030a06030201090819080d02090612010e0612100b0d0b01080610060314060607050109060f1a060c070905060d0b04030504090606050a020601 81
    0x80c4043ca2000041c05507907812040201503040070405000342c8007a026034030050a001041d08904141ca40d0700200416001040a003c6645c0c405418061881d1210701404011f00001200d44a0601600b038500600e40c52008034013180c43c0300000250f01c000811441c140403001c100a141104250b00d410500342c0c8107802c5000016420400f005840d42d03000c014015080721203142c10803560524040b404a05009402d051007800280103641001c200000c2c02001d00c082d0f49004102c1c1b484480228207003141188000b01a080c100001081840300041ca0701e12902030549984001d43d035414041d41110110854080c800810764001485424150001c0030500d201c0c5000160422650f140c9808858074105a20491034541860300100c03040160400745803c012291075241903001026180c0d5244240708000245445000103442961000e00134a0780c2600300d81c02c000320346000d18004015510600a10208a24050021500b03601c103a0030b0752079a240075002028982d007054401c0000282a961882c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 151787455 1250 151786205 151786211
    0x30d0503041707031211031006050901020a020409060209030d0c0804090902010908010e0615010e03210c030403030e1306030308040b04020411040e060a0b0a1b080d050c0304030e0301200c01 83
    0xe03482c14000030003480c0302806555495040c002005020040e80c09030400310b03071405028000e0185164205052074221952410304c547e445c00010b006074200306050700082d50240c90300c01800180502d6070018001d8641c21415250140c031400e40c19180400717401c0000c0c00e8541e061101307000000150303002d1500305005041908100b41d64803801030940707884807104000d40d044801404000c400000c0d4114200100742841a040754120700480e94400c07108020565072940f0009880c800082581203c00e145041419603541d10f4407400e0283c810920400c0481c0110f1002544080a0850303209540c2620b5040c3d89464003a2580e4031900295140603005076403056a4a115402c242c0c0824010001002481c0402000349000b00800100f98080e601c00b003e4210100501c409256101c42c0d292408007090f0304010544081d800c0583c000d0044600d0202d20a103400288140c045a6101a500c00d501c25503940505e210f14000381030030f882d41c1c103c40c40c0d180344020328848615180c07240176103030920070f81c0000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 151788705 1250 151787455 151787483
    0x50109150c080a05071e0e04060522180c0803030f0a0513030815040f14060303030405031902010b03030f0418060311041109090403081f0b031302190303030f0b010e030d050304 77
    0xc070210350741a00300d00d03010407400341812602d4209401441c00800e01120040da002f59104d030710300d171800d202c0f400c6800b204d90303281c0c5403010b052486100341180c1c41e0494003030f04115849603201340d5030354010380798060348420780800658401480c0c0540751141340400240240081d40d60780940d042c06d000b4001c2200c110251071261001d8031140b113140e4038203030349440220348c0d840c03002080038545901418030f074085e030010010407010a80000494814005840c21010113503041c90080f401082c001020680c1400005072442411100c50003400030f4600b50400608078100480011003299140d2000500318414207940002c180342c1a4005612040500c41d0545060400d100145c51101c04031030480c00720302600c052103a03501040041c90702c103005d40d07005068110b0038945107002c1e0703000082071a210121100a2001191241f403c042102c0c1c00402d4210000c60300e07854090701500842e40351080b520301d8652989200d40c492410744052030030203009001d1620b032005003200c1d554001041903801c10020312507 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 151789955 1250 151788705 151788737
    0x1b06040f0f030e04090819180311030a080c0d0311071203050a0608010509030c0f0a1a0402060c010e060402190303090b090411040b090102150105101d030a050109150c080a0507 77
    0x1400c602184a05200340c0c1d07c00b00f101601c0320950368000840104519010082c0d541001481d15805480d04260000719a003c00800070345002800704000b0080707400410600c4040f04000307081c42c81103500d520140050a45205461054041c01c4d40141644503000b9041c8030480c020780c000794000040e00c0001c5041030322070b4140d80c20343d04141c45082c0903030b1000451584140c814007a00b407542407100d001e881844000d48801714040080048680d0003c01240800c0c110b41d0340800b12980800180300a02030254074100881e22a00304440690107102e982000010781e04412861320260395054a44500460800340710300c40542140c4206034006a54040541100483c940a4030041c1200108156108200ba00090800501e43ca0001c00c101c200801404560f1b038900601e995500c1c03a1400c40e90401e29806201d082100c2c9200391505402080c3d8101e0500030107401c0744c1450384c00f894041104580c108101000c907684102103000107a040d501080d2070f0380329034001541201c000d1928880031500007035 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 151791205 1250 151789955 151789961
    0x1060b03280b0312070209010b03060306040303020c1501060c05060105010201230a02041208041e03020f19050405070504060314010e011a0f04090203040218010b0d0b01030612081b06040f0f030e04 86
    0x15004070740c1c0f44c0402c00c9011864900e80850160114050150841c280680400d59586018000600381a004120840da82d503003004800070042d885e0810041d656981c44e4082e00c0c4410500040d205405040004565540140290444201d1850354180c1c030b14100c100240742d9900c06002104419002c00c0000f0742c0543c62241c1286c800d000b60121581c1d64a00400901c0c1e4110a05010741c01c03158044c0308002694030451106100314041c2c8921618000304550021000050303046507901c41d1621b820f1040069205000c3c20aa400c952000c2001c140880f00100c601d640911603d401d03d80480c0040c803c0c07002000710880d079504210b100909210700c0e1040b1820940264200d9906194080300300425840c007011941d00441c01c100190419504040c0352201c2482440d890044580d295030b61145039900c29840000100500c81440c0f017000340d10b01d0504200e601907400c41c021000761603c450007a400120f21580125840710401802161a554581c1e02c1c0040080a0b000e12180040c2c82c803054a80340 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 151792455 1250 151791205 151791223
    0x11a0f0307080d0e030d020705030307080304150507051c1a21030c0a02181509060a0803070f0b0708010b0d11040801020c07080d1803060f020403050a06090501060b03280b03 76
    0x510340e180030130340300f506151801e0441c01e011001c660081d002040303103807008412108942e4010030b0103a41d0369140e0610103214445070100042c60352404082201c00c0340e02c8005801550480c0c1c1c40d2407100d8000000450a50380c3c00707010390f00c1c406030140c084010b81c0360888442100e0740810320100500d40d08603ca031401d40e004090040296000111580308615006039501840c030304507008201d681c10659900c2d41e984001841c0c45008a01c0329011904da591001050001020083d048070b603074403a10314029101c802d805038100e4070a0440130114040c03500402c030040c1a5a8070b02a9a81480c00c0c0303226120207400310b80440d0b003281004000c0440c910b00280024900f9003081001840c0386403402491516020400ca410000c102100c0c2c2d070306640d1000c1d5107071401207135004607020606500884010000348215030000305540314541c5140d0401000e9040303607100394001d80003000000d550700c40a00c2680f10458a105c4032403800781601c100c0b400100080180140148400a4001030b400046454080c0b00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 151793705 1250 151792455 151792457
    0x11120c07051204080a0201300e030c01060306021803070308070f020a1706040b010b1606020f0f0703170106020622050c0303040b071124030705070f0c08010c02011a0f0307080d 77
    0x10300174030829940c0086216481c51840008080151040f4500c200c43c8801c3e4580c880c4155202ca50010881c081001911031958142c40204456560703460041c0c0203502049401d0310545030000350703841078075001c82e90360300700c070f81150b0f2481c0303000341c240c0d03c190190400000480e070100300c0c035501040e410150850107410035a103200070705080c01c060800d4bc085c24030591040c0491042080240d06140d1a80c1110080704e034410409611404403020007400c9000b204442140040d020500c4402c1c90341c05250419480380ba180c0e485a641d8948400300d844410850b006104c20160242008000884400078002d2500a20035100c040031801c1c0000d0a561040d0300443e88034101040250911007032898a07042000e00b2240d0a503005004442a108000030701c518081d08507011000540c801d000d00308036140254040b8004480004900d0b120051039230601410000d50720f0065102f03203540c014401d000040c009400d640840c407031000108101094881c840c0c94150149000019002104000070031880040d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 151794955 1250 151793705 151793713
    0x9010f0512040317060a0503120903100e1c05040e0103030e120604030f021902090106030c02070b04031209050d150e0312090102030103060c0c0c140409080c060403020111120c0705120408 82
    0x40304c6403603580d291010301003e21070b0400f01001c001c0c1d80e0b000156000c1e0500c40e504466101d1065070002402c002d41e4207441c0301c1950610031000c080020204000d5640e9112910488000e1041d5404440798040e501030050760b1030b010801800440d00a911045174408020010540c0340d19040c0360508001c01074800b1800b1500402251400940502c0041c620991054000c140d01450350005031101206104540525641c0c0c501542c105100307200360300c06880f180241c65980d035a01d2030300740030352019000e1410015045050208241c540744000340c401c0c82d0002080b00410021b9812100181081400e00440f07100400905002c4a01e02e0001c0d0320803170380701000580f2589141480416664105410020818a05504000210320941800030307030b000c41e48142d2001103103001203801080c1d00f4034003034400040461611a1041c1c00a40d040c8580d102e54020b000902a0310b500344002c1c001c803400d00c00075004060004101c60820320151031498001e100b100d41c01600300703060042907840381e0005000340d00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 151796205 1250 151794955 151794977
    0x50d1e05010f0b120408071b06080405120f0d0b0a1805180109080d0903020705090c180f010c060f060308030c03011d070807030b0f060f0a0e040e0309010f05120403 72
    0x1502d00e01500100080741c3c81900d40811403c4e000b4504000601c014141e0030003254a400703102c078181070038559401400d1503603007003522413101902c14007044800325810300c5601520407407904810f0550300f2079018100410b0410081100701000380061042080d0421041c11001031264400f202c0d0b062603000401d000115401e1942e20301030b8002c56101082e2260f0306282c4201c0c00200900200c41c07483c80150310005411700300d45401c03402c220450b4000342d48940c4580900840e084100010882c0c401d0703540640c64400c2e003003400c0c082a412250019400b01d058001c0540220340b69400000c21a00080400035845450780c0d6540b000750002da645040d5180044014803441c1c1c441640308003042e0b401c1c180003804d450961001490901c0042c100ca0815840e071014820720f440b506080407940c02c00501280d141c442d02403003030310f03503803c4101003400044418201d801c140c00c251240842d6504403d0203586404034070001590344815010221042060801071907440074581e03a41c0d580564480d64808039044 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 151797455 1250 151796205 151796219
    0x61215011e180b04060905060c070302040c0e0102060a0603050304091a0301090f140118060f0b090f150a080604080c0a12020304031101030e060615120a1b140307050d1e0501 76
    0x202d07042d040b180d0f507040c0c100014444250040d9480301220707021542195200e145002a50a20312a940000e410600303101e603035008150080c000c0094004280d01312903060747c0350800903054500f207200c060580d400c2000280940605908406009240030008072800c00d41c85011a0031181007803001e031007004409440c64104071807840b050350303000c0140c0000d00041c11081c0e200070310200d88040040c0417aa0307a2191140c104583e420000c4900401004884945424010100140740c220707202c1c407015a171400350030045d1a100710080252000480140059030b20b40d80c6418160b4400c0800f00000e2241e65401800555010200700c1149020750165403994914901001d0060300030380c0c414145410800210b041d108001402e07584020201c0b0030800d400b02040d10f5115500c204820101c080c1e40308030800818024030380003101600100b01811254030408007003129108608810400261070810106200358130580203801c00c0e04132503000180c0380091444a1148503184444d203003807503445100404c0f17a0703 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 151798561 1106 151797455 151797497
    0x5370e01021309200f030402030703050a0f060b090106051603030209120c0a06030905030301060c0c090504060b040c02031813020f04030f11061215011e 67
    0xa0180c501a1070300300303145400b0b1840c500e403e10407922018071300040042c0c0b515050700348003070401031508220f4403e50700162090741d051140c1440440070440c2400190b1500d80b18640c205064145890b00c034007691402c0e4034061203480e102004000013130300311084540007044600001c0d00f80b0807a1030240c0c000e001b003803149a00128940d92028981c070300003075481c5c001501100c18038401179480e0412400d680c1074000c001c240303400910042040e1030007245008030441c4500788011350740380c4800581013180d504980680d000c6441e05031a00d03c83c1814461031300000990b00c0a149081c0e2480c00004844c034622907454021903a48100c20107450f03140d0306803583c0c41441e0341140d5945940e410312000180a000d03060b11440c4a400141c4034500e0070318111000c0c0004144132003000e40c0c60f054a43c902c1c0014459040c14015100b441003031040c0b02c0e60903901c40c28843e4407802200b400c600c10711405 = true := by decide +kernel

theorem cover : BRFrame.Cov 151618705 151798561 := by
  have h0 := BRFrame.cov_init 151618705
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151618705 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 151618705 ≤ n) (h2 : n < 151798561) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
