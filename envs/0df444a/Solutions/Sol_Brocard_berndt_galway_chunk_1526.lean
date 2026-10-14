-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1526
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:24:43.011878+00:00
-- url     : https://prove2.me/submissions/7d49a723-d462-49e6-95e7-0a7be160ead7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 274280575 ≤ n < 274460431 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 274281825 1250 274280575 274280609
    0x17060f0f130501060e06130e041703090109060c0507020a0e040206090a06030209090a06051309050712030905030d030c080f0403090308031f270f0626150105090a020c0a020a0807 78
    0x5c0320a40c41403844100301005e4400342001000e8501c6c100589c0070740130b441d5890040c0c9113491044100d50050301c4481d0207070744524103c820312441d0302c070700b41004a450030040d03c0d1042540c0800c0105c0040d1155005010b41d060004055484031411241003580060400c452242c640310060003c3d04610b9a00d40217800c84000600700c4045842110180c4d00020803482480e2004100c01d0090408c600c0c04803400e01a030080054032681c415024101c052003502c0722041135042c5000d0600c0c100d46401307010201401c0035505044550440c3c04a504400c5100c21140541d545080644048a907a800148400b4000007002005500040d0b814002c0400c0c074402030906681d000313810f6902d501c0400249800303150411f039001100250740100d00102110602080696461500c0004621180840c02441074102032a040200081c0012809241e900618401e994105008030354460b400401440c84564006140b2012100c2000511a05c90340140345084040c2c90798400e0b510b0b41c0c0756101d240e240d001042c0b99 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 274283075 1250 274281825 274281829
    0x108150606070b010315201b0606150a0e1305090c0a0e13060e060c03090d020303010303050f0d0b0d1202190b060103050417210717060f0f130501060e 66
    0x12a00d68540200345000c10381d00790b4841700000d0703500604e01b810099481650348001110075611050b81009854810303180c0c0007030b241200c0d0300c0c0d4070b49100901d01e801150402060707654054540780d0f14078409554a45a40142a040c2e40c05804641d56640c44440210281540d40290b04014411003020007591139070b41c643c006029089001d8003070400140c0c102000154144d6071240440c0d4800e01030701000c03441c00c40c526400350601600b980d448040020000801205e031400b080f40b1000c184440c4002c44c50756156403030080c9603000f04610500c03c01c40000b154a080750040d0000300c2401d10041c1204200645441c0444038039400c0700c030305005801058100c56080c100941c1484400d0381190030201e240d83c07010011802040004c000715049181290380d00001c28640019004550f600b4501c3c20684041030b0000814000080c030030350030000940d035130345104080704503411740010003038400010018203500007c61440c41010b170690040b1a80c00c500080007070039044541266129210307651301c1110502 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 274284325 1250 274283075 274283077
    0x303060a0b0309011d0109030e0a06090302010c080d0c090e070504030803010b07031b030302030105040b121e0709090606090609090c06110a0b0a09050f010539030108150606 76
    0x124240d200c004400c042189032402001950301120741c10002401644240009804041100500d1010f81d903400b00d100801d5000507140c0070700e640443e14100c0c0b0510b4080e004124800d1400000d0401001c000c0c028100174000d020b94400c001d0550080c00b841d8a0018014040d200d94400c4040d08800703040850306043c065000ca0b000e890300000d15a26581c24003030042829844100300700c003041082c01c0d8a074800c8008801d0340080c10311a980c0940da0307502d48010801601c2022041c03902c0b03070000b009840f1800c4e0000401c00980b900c0c00d441a221995404101401c0c00c0e042d80c8039840c00c0b03090603030381d004109a03075102200b80e8681074401c0250a48804c0d641d802c0780c100700c0c0000c1030028075020a014860040c00c1c003005045a02d0100c60000f540c5a60b034000c1c03240155440e40085490700b103a41e003001003d00030b01c45039401110080155203010351092054008442d0031080e916015a8102c0069118200812040745600c5d1180c0c0d4035650740220340e0365101b520a401c001c00d84a0310100b4a2890444 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 274285575 1250 274284325 274284331
    0xc151403060a05060714070b0408060604050c1204210f0215010b120c07060f0209040f050606190e060304260c06070806010c020306070302030106020d0e1e060f0310060906020303 78
    0x5000c01d003500b403c11041c000030758810041501d5107035004113950400a41000880701500307182040c16120751802840c6842c0141c040d182500c02d50900c420084c2000540f02134981c0030b42040c20400450b217450510311610381c2840c0c0d2506d09813407904100c8440540010501c2910b1a05508440000c4500c540040c070b805000c7c011283d5414080000d0b222440703030035000300d400c0031005100c3c0d0301d810074a0707458804680100d0031002d03419402080c0c442041c9041d00c510010722280100501c2207107844030000300d01e84200901e60740c4000a0510610802c0e1264261107800c51028000c99941d0519080c045203000c6061000010288500301302018001181c064510768540003000b001d550f21401d0041e5601d010040ca0745041180142c08800503a504001c01809280c40da24016074a506245000b400c0071075502c1c0900034000b45c0c40300400c250700c8a84c2d64100740c411503010340c0f82d446e04040000b07801e44a91042030f22507034008002d0040d000c103488100012200c4680312100000d80d6500c0507070301c0313000803 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 274286825 1250 274285575 274285579
    0x803090a09051b0f0c030d0609050c0721020705120c0301180c030803130f1214070b0105060304021801080d0215010605030a09050f03041202040506030a120c0f0c15140306 75
    0x2120407032000b103c10700c02408074120500072003418010140c1c56540345810510071064143e48034a410042c1110314820b154218083c200128030f40f80190715900501d00c000e0b5214880344c07e402e00060800361090225901821005100703608090302d02005030796980070200341a110b035183c85252403a80b94440b00003424a680000000005c07840c40c1c44104541e0002402417100c18480707109100000c2c504819841028880e411524800d041682c00403c82041c5540a04400ca020010b680c086001e2620031411034104603180c03031b66552140702007042d070383c403840d00c2d54083d100e52400811440c80102d1034905200c0075508a4003031074010b6440107500e403420712841c00450000c0002c280d0301c440b90f810145560780140121145040f40140300340c510b50203988049014254000f00e03500314a005d000d0150088021001411152142d8035005000742c10b01c0f1004040c07207001e132500c10800030301080c1101c2d400d03081500400201d0761513080c146911b68485203440040e00f03a0a4900c40e0402d881d0a8902031080 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 274288075 1250 274286825 274286851
    0x4140402100c1a0714160c0621180206040e18010903120c0c0206210903040b030c130503010f020403020405130b060d05030f16120318060b0d0605010803090a0905 71
    0x5600d08203462800301070001c4042103400a0041c0e0740d011014002d0900c440b1402e0041403408160070301064141da1f9810036000c100403010000c0040781010081080c4050f100030024840d40c150540d030321400490540250048800b2800042035070652000501c11050689030174807156041c43c8450880b004014010027041031107484449101a40c2e004030710903175150500181c0340d01c0c1c503000102c2d940c02003176004403245009002d80c1281a40da0103255002401e0000550601f42410341021040c00020008120000c02003503044081070002c00100080501a00170000501055240006580726020690040b41003c0c04508410075040d1091001030b000346907401151925404c0100382040c0c01f409444a01c070620400010a031f02038002e00356036008601d090f4001000e890005030411844c07010b40b040c185000c056030600c101560380517414a034440c0d40019540064000200ca1446900b4007500e00c85c90704002003440e00d400801005460022100c01d00b00c41d641c1d6040e80c0507100216030740040106 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 274289325 1250 274288075 274288103
    0x1020d090518060105090409050717210a02071e030605060108040f021c061a03060906090712060e0f011d030f04030b060102010e1902010306090c050a0c0203010b04140402100c 77
    0x400560701e1908002c0505d00706140203000300000c0e06a6802c00030950359600045c3c41048854000d10b851803400241c0c2010b020528640502e105820000686422003414006150403e00740700340480009051410380c840a12103c0103d000c8a5034000c2c00111046c0b0f04d801c0100d90b10b0360080051038815913000380350759040ca000b40d00b03010304000b9414060241c44d00348038800002031440e004400020261052000d11000510101841c0440280c00840706070408414045c0003070001c07851030152808000e215015112504e4000001e0042400c00c0901e8003900380032020400040d0480384814070ba240d02e105000702600c0e292500c9108001d60a0843c907001c0008000041400244d030398000c105000020b145241d043c40d203800d06000c401c0980358501c600d0860700441d07070548544c00107802031800c208480d01907510b0103403480c4550002c1c1c0342030000d1501c1805c210360b025040f07100c1201020304107000241040c0500145000203a608030b200380307611103000c00c1c03183c8940c84090000d80c002e0100c01401d8 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 274290575 1250 274289325 274289359
    0x1503100f060e131e0f05041e0b041205040b030103050312010b0901020a0209040c0803040b1c0b0d140109150c030b030f0c090a0608030a110f01061a0f1306090501020d0905 75
    0xc3e0b00710070134540744c078001c1ca2031800951803003200d5030b0208600b4085080d2500b0b16090303a0b50007002400210300c600742c0b80d80c00c001c04c0540c0841a4415409404900f142d81c0903402074405000f1350744000203040002001000304000403000d0810900c111104450603600c4101d8034000703010740c11100b03005034002c2101c4400361400104841d0014025001c508215880d006921300716405608042504240007400280f400c080030b4059401002c400e00c10403041c120100013a9981107039010282c4078041b0020000b04864083d44060810b50b44800c1c404d0756904401e5070300d0041c1c02030300c12200c0881c5c03420031501914200840c0e400c4890b100c010107015014000d0f4200b16030321001800d0b803c00e80d69212004102e10000f0001030074111303e1074440201012601c1c105518002404442880c240d043c00004c100c03040340641d68006500600b100c56403541055189003006002ea40300f218000021007a0000c1e5141c0c10010340c000f51142a0300352003480e145160240d80c40c280074482e070b80d0060443d80200d20f44d0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 274291825 1250 274290575 274290581
    0xc05041b1d04060503030a05030105010207061d040506010302090307030309140604031a090316050a0611070f021318080a0306060f0e040218090a05010e13030804111503100f060e13 79
    0x7040020b0000405940702e80c0801e203560030a48a04c404210000300510643d0307010403c00c0c00401e80340c90721280030151020080003030986046000c5c003458460b808944280e000750155015a000582101d24040e49c90800030070458280c41450a907a031000109601ca08015007200c1c207498010703030301442c010615001340c08180002801e0031070f240003d0000700c0c1e00511021030329810600a200034400c105d000c0c100403088460f4040740184049041051000060b82c00c0e00506180e80c0407500d05103681110940030307001d0711072164601c6a00c042c42c8002d0041050300c0010304404051580c00300807480d200c0b441034464804203842100803541035080c1050742d2505400070490440901054001c3d5003501e404140701420950307040d804c07951181c006100e000c4007010001d50010f01125554045e00345900c02a0000f640a8070180a100e04401c0841240e2101081000348030b0200310226920701d4124140c1081c0006800b811800550003c8000352061182000840e8064020800c80e04d1140312a901001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 274293075 1250 274291825 274291877
    0x10e04031803050309092508100801090c180209010207030f0c03170d0c08060a0302010e032e060608150105030a0e010c050403020102060109050f18010e0a0c05041b 72
    0x8100d20035109020080c900d4900790015481000195160b0303850000304125060024007006000d118030350107503901c1000817541040605c032400c103110b4548604644081d44501d680103000d180d802c0001348001c000100b804001221800c07d5010000c40f0200042010391040e207910a0060344100300a1020801844808411034031414400319441d0392035842d00110100303d01c0c0b2911004012a0f000c08811150040d1245171072a8541300c1107511b00b40b400070701c1c007203824000a03040200001003020350f520300300030000d06500c4180380000e401c1e1800c81079080c0810000c09040102e41031081c00140c80f800394a205015801c6130541c3c52041203828011107031500300800e1055041c1e1034502040a04030288240d9200903020f0b500c2e15034490031800003a28000040c0e103c402d85501e45801c2290741020342074001d80091801288010510940da0b02c1c6014020300e1242150754040c080e181410807200300c0019040b00c01c169010303c81c0200c200d500040011071000305101040051140d05500d000034070103918 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 274294325 1250 274293075 274293077
    0xf010315090c090e1006030302030307050c0307060e030703090f0b03010510030227240a11120a1e020307020d020f0a1d15090108100209060706050a0b01111203010e0403 74
    0x500051940750107284445683c4198100d544d95a29100400801d00a201076144440c1080c0005481c6a40003962488028612010031030003045201c1c014809004442e03c2d180c000005000b000c01421b0000c1c0c5a0b80444012070102d00c20303400010380842400400003c649420000d2401e50f840c0c0b605110741c0c01100180042010ba0030016440710321065a0001c0480d16001e140b41d100945010600c2140c5801001c03684010003100038030b40c0040141c800701c418001d120314007041c0c44190f150f0258907001c502d94650440754404510f8040255204801c005009030030300c8070001d0050182c46c1030380c903407182800180d080b900c0901100090f040c0900c3c5001c116102400c3c5c03165581d52061080301e000320005d09101c0d80f180c0c01d010700c142c0211000309001188004c031480815549401d00941c4c0d107030100e03107142501d280c010070342c50710b941c1d580d41c03d894200380c2114040c811031400b40d89880051040c8201c1501140e4038001ca9100c0500003e0030301c4901c004061080d01e540d080c450814501d5000030401c030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 274295575 1250 274294325 274294331
    0x2120916140406030b0703290307031112100903020c0402030c07020f130906021b1501151403072d0c080304020301061706100519060503360c090f010315 67
    0x4c001115420303028420318a0f60384c0062000d110031078940d0040b41141e81c0c1c41c2c0803078141c0060420f580e008101001100d0344030301550403100c0160049400d01000040c440054002c1c00388807104504d203030b0441002c5510076820743d071117a01050108803c0340403c1d82d240c5040b01c2c00703000b600e0040c1000c00168106a400400c201c1410b04080c04110075924a004211440d64000c10015211898a41c106454504200c0078002e4081c071188107005000c0148a03410840101c02090005540940e22855620301e800241c0c69882c586600040e200d100000c10114803100011214442da5002480c4c07200d51101640e20031680342c446865100b00741d0805041a0303030655817500d0000d13004501c070b1054025440d048000d0412407400e40c130801e03076081160740680c2c000c0c001c03400d07440c680f036442840303c5041e6040c0742002c0f07440b41c607909400340da490300555144031404018040c00145079103600d03c1c003102c0001c813401c50f040058104203107c046102030b110301d030b409020b0301c00600c0010022610b803410714140e0a000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 274296825 1250 274295575 274295579
    0x150b010c060f241a031f1706090c0f040b1503010e060a090209030604030c050f0f0102041809120807021002070b010f0e0609011a0c030d02120916140406 67
    0x6004450306104849505a40c42030000000c4503500f40c0074005031070344041c8055062501121004100741d2000615581ca000030000f41901d43d01c0017007a208414507205515032075102d140002d69070000c0300c85120719100310f00000380c54100000e4400400c07000a06501001c071140c200744409800303c2040e20b64002842d0b1205035484035810701450007001440c13403600060a2010034480400c01c150005145680100001d103916100001c0e050f4215a0610b080c00300c90340e0383d082660811036240d024141030b02445400c1e02d5264015009032082c0e62590710701031012402c00780d549007204c003400c00003005440c2503906a03900da03000300e0a050f4401445c3c016154609280201c070402c0b68406142240c3c480d038028010702840690364014005040035a8807134440b401d10031300190060805100e40c040100c2c0071216001c0c0c8400d450103640445c100e0710304883d110440d001c0d00d003011f90040341c00c0310b4443c10b00707900080c032038400041c0f0175a1008800c001c1100290405031503000116480c100660070039114140 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 274298075 1250 274296825 274296833
    0x60d12180801110a1407050a03140d090303090b0601020c0307090507021608030a09120f060506030f0f06010312080c1207090302120c2d010c0510020412050c040207150b010c 76
    0x94003c08260060003184e84040c440e02c09052142c502c0020810480300740302070300004500207000e0b2501e43d00b504010600b6014800c01c440e0a10035800c418910b2800c00f0f41c000c04058058112010b150301c682045001030f035808004a959001441859134194400f10003013082c0c4400e540120f81242c007a1040d2141e09815801260342c230b005652000d8400d9100207004c24041e80c0c00006d00c005041505401240d242e45078464903040c88150101030700c6079a0355800305009950401403205410401d03004d0b141914ac01500503515000d0920040c0c441030384903c0c1c075900262103400d09520482510b001c4908101c00003074208001500140000248480f289021015079602421041c036604c281008202c2e41d10380740180803540402002d614034500040354000040003882442d51030100c000e10f00b0700600111401e00358a841d80460800003c9440000d02040c5458001c1c0101b145c24013079011101ca20b001c03001804200d03c81c0e000d001d402c1c03c0f065274440f00c0300032058002528480052400003803240150321 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 274299325 1250 274298075 274298081
    0xd090c030f1202120a050f0c011401140a050301020f03130f0206030a0606020f0c0109050402070312050906070825030b0d140102131a030604150b16020108060d12180801 74
    0x402d80ea0300000141c9004810360410654444010a9140d1380c00e2040c0b0b848007615502800ba0001038152020034100c40131002540074101240c1103120884041d650303000e4001070310400032402030180100e0380b008955070505008540401e03035002840b62650350b81501c0328052601032135044808000d80182140941d4401000c2d6005908101e00002d9161400c84007a260071a44a044012500041043c03072080e80c014140c503089460a460143e52010145000c4903c403240c0480000050324000074041c115500203800340c0b02d0f078041d883e00c801c15100e4240c1040924100c008444122095040420042d0300c00d42003030f046c201010b0000401c1054983d25899501b910184440301c80e0341c0890716424130402d0720030800090581a0344410154241c0d0080e50261000801050090791903503084021140104c07107000c02085108801d6480d44078007941c1c1c480c80c426400c400d034000340482e40070803003c3c0350940988200b598004200c400e820502103040ea00040801040c40c80340082140018080100380 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 274300575 1250 274299325 274299353
    0x2c010e03211b07080d140f0402041d0106090f0e161215020a080907050d0807120207080a0f02091b0d110904020c160b0a02150406110706020904110f0d090c03 69
    0x200002d44616003045d0501c11219070640740400d039030f0428203004003200c0d000122904140c0641f00461101c0b00b00c3c0e9814640030340e40340001030561806100050441c020b600401c84000e0981040c8500c1c081c031044550f1f14180d0f480503200720307102283d04005281a225485800c6841011082c00c030103c414803941c12a003104240030080742a59041010b911800d104803c0500811070741c0183c420038a48903003c10340904c5800901611140e44415190703402080383c40010480314044030301200007403810164500100070124003c60800000c10400b25905441025201c040d030706c02070420503001104005001c16115101c5142420040d24940e5220b034001403041d4110f00700101803103a841c0046017180711540d405000329503401c0c411602000e030701081c1c00c04485850800c44d21b1035151170070001c000344201400c06454044c002500420807009401800724500304480c01c100310005c00000c1c4200d44134640450030707102c508120503140101260700c200407160041144489154403941c0d2001d02040803 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 274301825 1250 274300575 274300583
    0x903021810230d03120501090c0c0b040f050f100509190b1504050a0204050913030503040321091101080702010c0503130827031b01170a2c010e03211b07 67
    0x5d82c60141800068001d050060034220010407050080000003014020020001006040c80c00080344c14000b11603140494183c0050a44250ad42400002c85c0e440c0c28181c1006a00d50900700000c2c5002c60101d401c00e62440403c41c3c000703503041c2651302d810b0150001800103031513803807101800b1941e8032903210350342c440d840c0301100503a52404d0004101000c6401400740d40e410710308410440000354040156a042685820490058242c103c030300c89400801d40d051010561a00c038404086c810002246141420280c031045141d40740c00740704030300b85d500801d0f0030f901141c0100301280c56034211040ca001018050340ca0350f03040c812031040942001505015602c2c3c00c0548196040640c6810b01180c82c0c2e40d40c224404034004000c550001e40a61000200822070565000005407480c0f00e03034000060005030390149000907400d8140132000f06903907025602e099842d0680018208000004842e4090000c00c1030702984503810150b40d488100080c03c6400c0c4c0410204035000c6060b81c6d1000d490541d1017 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 274303075 1250 274301825 274301837
    0x50403051c0e12130b07020a050f0105120403090f060203030f1602010209060c010605010906110d080a0f090f030e0303040605121b0c0303040308130210030902040e0d0903021810230d03 81
    0x54611412442e1200f42c0250748505c3c801c000050041e95081098000c42d44181e8a0b0003c2c2400c0d000180c50707070301904100304900307074001c0308200415a0000384682a1048900607e84290b1121005c03a0703a4001140c40b100b40d0f2214802140403421551242641d6500300d200240c82c00d0004004114140c102042c1941c55a448117402e1100e580c028111001400f040e20b0003134821000e65981e650b0703070088000601c042c4040030000c200b203801c44d9000b07500101900f03102031110081f03503d0000007081c43e0100950001e0340036201c1d0125031402004807812074000b81c3d07845080030340c1e02c00f15101e03800014003800d1441c0003052030100c0c03140b40b10b030181a800545602542d1249004e0034042c1a24200170000358003076103d080318100503542c0d81640303a9a1300d900e203000201040544085401030101201c2e60280d4411550041075495002c415842640e10903142442c1d01401912442c540e44410ba440c01c60220290909218041064000030000c000301d002240440380500302040c5080141d40c0d0980008031 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 274304325 1250 274303075 274303087
    0xc0604060801180506280e0414010501060305090c1504030c0303020709060605120a020a03060b0c07050103110a02121e28020604200604080f011509050403051c0e12 72
    0x3540b9091030180f80c10003c0180540e181c207a0004618007982d502c0b1034088900ea1408002d0300c464081a1005090f403144101c400e4102800c110300641c1d8021107188441d0b0030403001082c80b078440c1c00742d0f80c09200400300400c1d0102d00b6104102e4484e40304882e0302500c007814030002021a031186604c03401540290007419a003401d011300301e0700340c0704030b030300108180f2030100318003425002e8001c0e521350300a030302a10040c0c503900c0d0711001f1005803120f40e00c8400ca003480440c20103200341c07000c20744a0444000b624100b00708080b1100300c040310b000380b00022015030081c0001c0c80214024500030440d00b035014220348079545403c900800d0315005908070f50b64000c1340340b0a50030b03140d42080070a80714150364001031000340750580d5201d0f07885401007440103110700840402000c5865480640f405422650141d501e03140000180500800c00d1403044004821070040000c0c40002d0351250601035601542c5a030b141880c24690b02409514003006c160341e880d1768100c0c42c038003081e0a11034080514100400c25580e90 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 274305575 1250 274304325 274304339
    0xa0f0c2f01021606060f080316060506030f010f0204050a0608091002030c0d0c0c0b0702150114030312010311040b0a0303020d0810081504051b010206042010030207120903080a030902030c0604060801 87
    0x80c6e40d079008009941d108212052411004601007940190b00040105042d6202004a810501d00140c40c0d0307510340c01d00c641d025610400b40c020f4015650f040d512501800c1d0750700d0044032908003d483e04880b581004411041c415600e400540d4011036202c109490014020201c80480d030340d51b03800400040618035030f041003103000096507400416610040030036000d41c040407200c80c401845400700046180030100030945041c81950f078030346801940d00000b50303134074148181d0f42504610924840d80c640aa5001c0c40d10302103900700c0c140c98140d0f0007821503403890764094403c072501901e9069810f96002c800211200b08003d801d01c90f0707800740b032001910304081c80c0007850f000f0300d541940344032090320912900c40d903800108958800c4e041030749000343d00c0c0c0c0c41090125603142e407288541c1045c0307141014100c1a4141e0020480d0340c3c810192000800440c9c2400c0700d1001c1d00380001000f0444c2000b10581e00e82c482d8108000d9540001c0a0342d0000110030005a403a038000d0384517901040042c401001a1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 274306825 1250 274305575 274305599
    0x70801050c03041a071b060b0a05041401060503060406260f01020a0f05070819110705090f01030204020c0c061605060a05160c05150a0f0c2f0102160606 67
    0x20144110b4110f0501c0c1d600c24501e608001050219280300400207500c0c1032003040700701204038085820f0300720083c00d41820401f620141015502030000900c0000b814141b81c454108400742c0348a50300c1c11a42040d104441c55400600b205030722a894075800b05a0351414000c0381081c4070440074003002c070818403a00c0c034146030a0060f009074a92051010894058008031b1140800b019860b00d0355580c030f045d15000c0201c1c040c1140d00b480c00d40000441c014401c1e000030120070100040c100320361485980e2420812005000c441004801042c5c2e03004100504140c0c01801101c04a10142c6410010321000701e103a03034010906000c20b1002054086050003428000c03c0c2d04098007010030301171032406a61160042624050140800040d140e014040c084180482c00d052a940e104150807824141400300107001d062910240180c613291540124a00501c04071103861080d4501081e10381c02e10b0385858403603880c10024000e81d50204484803d94045000484485100d00800101c3e01d041c415001a0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 274308075 1250 274306825 274306831
    0x9080d020d0b01080103080301061407050607170928060f0c021e15060d02010c0506010b0a090806060306011a040e040f1106030106022a0d050106090506030d05160f0c0807080105 78
    0x5204d00c40006102081001c411a810358205051040500685241c104014822648094441e020b5171050105669202c20300200741c180d01e41c0c403100725840f4046901c1d154003940c04072641b65081c0d41010f100b48020301c098590f03024003c0a000656034801202c0ca403c0d5101c1001c2e504c01030300013005104c0c2031180c0042005980850200404d0580455100c00c180418098469840b132010890b854046a02c11850644440e5104083d01c505594808017181a504081044408624101c02c0410764880c0064014440c200050080c078083c1d00e030602c0000d524003400c1c0b03403001c0300c00304010100307040e10b10020b200e0003507121f82c0c40c06c00c5d1842a800c01d0858000302d00d2820b0301c1038104000400145a00192442040201c42c0304400c0c0f04882129111204010701c061a410446100845041c40701c194842c03801c40349001c0b4240115500e0f0000c154442d2440d02011020400a100084081c040300c4035400005204901420f440b00c607a844400c0710328072503803003c886503000c00390a000c148001e0245c150 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 274309325 1250 274308075 274308077
    0x15130c0206070c150f0b0d0302060a0f09030f2001060f030203072c0c04050d140609121204060b041b0e03070f0b0333010e03060601020307080d09080d020d0b01 70
    0x80b619640c0d61814110641001c54500e9561034920500e01515103601c0b028071b01d58002c10b00007880001d4500a5141d5004882816489240015260080c07595016104031558103945120000440b440e00f03940c52000d42e11001c800c22040c041903003e03400300740728101c041c20000750ba400e8a5840c0d481010702d808101d400c48103030100040c60340c5202c0c402005c0c1081c00c03a06c183ca035070303811940c91140d460203134003866200c5607202824060f02d80501c1078540b00c01400050324029100b80e41d90f811703999699412451040380c40032904011200d044c4c5004500713990013501c04c91010460705000300000702603402d21400c001a21703440c0b07003200c00010780101a000a604041c1c000e00201c3d4542036810030510310364800c2d149446000400240c120a568021840d087c03140351312002d0002021aa2140800036080040e0114983c0000c421807481c00041c0700c0d105c0c1030b050f4001c502e449601d90b9204a943c000b030240064458540c9803107400155407601401c4a10302202c40180c03920303003200c060402d0703d031031088141c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 274310575 1250 274309325 274309337
    0x901140903180d0503090907030203040b13081c060e15030f0f0a03120207020a060306051503090604060c0c0b0106180b070c05010503070c170703030606021b0915130c020607 76
    0x2205112001d50480d4450b01101d641090041d182440b90a51182c6589140e1016181d01044005a050381c0918001c41c001c80404001c0d65074080076001e04480702102400c0e4420511070b0cd01c2c9141001e0110b110002403c10101d589907903520b100b40440c50035907003100702c43d002c40c000c5042c07410200038000f441d51700c0341c2c010142003201c42103003034884501a8002d0200410026149500040d87c0c0403030303801a60140c16042c840d540c03582d00400030507107409120701c901e01d9040741c010b81420410940380215228000f0b0004d644441da9464010100c0c040da000a001400b244200483c4601460b43d00810315615011142410070001107464011034210a21005060002e40701042d0f0543e42c002c01d4910a0800a42d2911600b500359084008010b00404101368152412440d5281e175000c0c1054900c43d85041c071030035446250136601c58240d40d9a02d146881c1c20410301c403042c5015031035560044103240184074400030220107d400704d000c0001c000600354681500c0001981d04114255201400d85044 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 274311825 1250 274310575 274310587
    0x70f1a0717040b06060c0f010b0406050631080a03050d0c0906051914070809041521030e04020a0201021b12040623040e07022b05031503060901140903 66
    0x100c0c540d1003000e03101503c4140c22400282154403280111001c14420004984c640800050541d02a044030166940941d051080c0015070342040000c0c3c4074081841c95400040c080050504501012140074000e201100800006000807051000740302441c0650f68641d5900c066180800a03180501c0c0c83e0340400c01e503200d0400180d0b90000a03a82150f085806401e001c28280e90101e41c0e00049110250508000003990410800140001c040d0713071400350b40910000ca8082011003414603a44600411084000c031001c100c91000e01c0e81010051181c18841408000200420200c0e005a11a50003503940001c0184007202c0d100b10110420030100010044402c03440c0304078a03240501d105020074002c810142c8103600f0250355040074122000b0300c0381038450b6501c48440002000070b4030190090301501d00203242c410f07032040002c42e4000c010303050740e80700003050f00d4215802c0e40001c00d1908120f042502d26a0710f907a0500400307002d03031605000071800c0742e13212000000407280030f070207011030303501c10404 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 274313075 1250 274311825 274311857
    0x8010f0f0b0703050703030f0e0c031203070207051002120d05010503010e070b090409060608030c0d0801080d0504170307060609020316050903070519170d03052a03070302070f1a07 79
    0x80366002c030b03403601c1c080741ca68410f864143e0141856403075001c8200d040418202a0010029a92603425030031021990805d41520511030940b100795034500042c1c110303201c14411800c00641c0d03007500f0080380c41224503a0b04440917070701e15504400c1d481106d040e1204010003c500e024013503100f086401e42c0c054810540303090800d0701c0900c24008980c0c0074a072505108000d0019a5000c04010310402c01520b030b6540c2c03d8080d0b01d856040381e00b4602c0202d0b94540c004154000c000540c03d410548648845103040d0134582c400c0c0c911180d0300208007141c0300800c100c00c000391050192400800101c3e101685074107207480850001081d000721502000b000340403402d4280e40004151040318001c0d1101d044d0b0845452401082c180795410041d00c100b085041e130200c6450004c0d40300b40d44d40300341e80d0801c00740e2141e00b1005c0c8031006804003010100f02841c148845808660011500902c41d820014a4000c16a0f54030404080914056407010aa92659800c10100e40e070640d1f807005191812019045da4800 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 274314325 1250 274313075 274313077
    0x9080613030e0a0e010801150e0f010303051806160b0106020d09090908190801150903080703031d0a06060504060614030c03040302012a172404140708010f0f0b 70
    0x290160420484168800c2c6a03110380c221075000e00b5103502c0d4458a580c480f246e02e4003a1000c80c90b02000d407038096900041b454040c40806010740003107101d0107400d0b481c644040b2480d0300072003009003455100703031080f900990b60603000380030540070100d80c0c02c5810100e062068100750142d1004080d03401104d0003101d003903402210101030780c9501d00c002480240c07074100032503580903500103039040f4402a2010700b0103541045405040701c44c584d008450000107a43d049513030800c14440181f4044080c07000e840042c5c020340245010ba0a6518050140d0460041103442e01185a400f0b590513940d6000907c25030415011b18001340006080c13810000d1005a019149440000d1030940c41080206c04030302014403e41141d0a20240e4030340400144180c86510a900010050082d0120300911075010402d1650308a892103443e00c0e6590403041424450f982074074225004045d90f2003a91121207110550301e100019004440c01e680d820007030340c1040c1c05d982c010b180c150824030040d1807100b8200701e4418010 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 274315575 1250 274314325 274314361
    0x12a0207090216081e040b07290f070c0c1e120c1712030c0c0d08070e1c0501091101120209060f1c05041202010b060403051903050d060602030901090806 67
    0x40a001d548141c000075942007101c1034030207117900c1c190000f40080c0141150020744011402000807a120480303100b46800f010701d8014a9540b80d406410006401c1c2c900c43c0b00040c4d10a8460800303495003020f60b9603000c2c0d000070740c0e0404071000d68000a0300700c02c42e40b40b0107040040d049049841120030815111110903601074404c0d4800700e2003c0c20f81d9000c14200703002c1154102a100740060f140d0030500d11b42c0e800d640140034130b20300a114941498100d90f208a6440d802403655494002d80102c890b0248400d101200e041d0b000040c04810362903001403401d2081103078075030080b000140071080410004103c4185800020000c5005000c1003c20766680d000710703050100c80e00a015910b10500190005c0f4600d0b204030000002c1c82e140c10882032001d003044d082e442c400654002c014844ca8401000101d00441c000a07025074070050f100060000ca1040303440c0568041d06009040c01349810000d400d496245d004840103810204038043d45580145040c0c0141420001070301c102c0c03400384a03c0d4032580c1d00c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 274316825 1250 274315575 274315583
    0x91d011806230103060911011b0209090705120109051204060f0e0f030d0201060602070b1303080a02010902270a14070305040c1a120c130902030603012a0207090216 72
    0x10301c1c1d03080b0208680c22031510070241c042c4880c1d501507959007400780040400b803a00b07503000c21012021f41000c0d0b02c100e40e00040b0064004500c0800312840c0c017400b44d848801810724200d84140b41c800308480e0307120650740c1300110102d40041002d203554540b203400c1c016003030701080a01c0750600062100f0764000740d0115203642503103455079545244e40d001961b0080300c002c0ca0b80e050b001e02c1122024007503041d00f00d001a1036940e000c50f0603440d6a8005006c3e28401d82000e492000102d0905100095411008000052441c030020880b0041a00010451030400e00390314556070f00c400903005140d01440304c283e4000c0f5408030030041c2420b01c9407902c0c01c2100c0180802c04042e40c1d880042d08020203104204050403d002c00b442c2446e0b124450401d1030762003c40403040301d001d020005401c081c4600100c50000740f505444114484c68082241c000c0e40011f00000d60554a43e030120380ca0f089410500d07903200248880a07001d00d41e1486020b8100704003500001490303401040076015014640410f80b00349030348 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 274318075 1250 274316825 274316831
    0x60402100c0c0e010b0d050105060412030804020d06050c030a06080a0b1305070b030109020c060603070f2601021c141b0d0204170307050f0316080d021201091d011806 73
    0x2861420320703400c1c500b035006402034124110003c80c4140080d005050840d41c1301ca02000285d803500b003080345600540c03203a54603a00d03030072030090000b0748140ca09542203840a80b05030707050b0510b66a03400a076141100c101c00c20090100030480c8104403800703020018060384000c2c0c41c1e4801c440c3c5542d40030b24030042c128158100d00c00200010444100500c10050540c0c000240e00e030b507100c51051001e5445825046000d100c5c03080420301e64900030681504681d0000e801103ca1403a000c0e41c9402d041c103040000e10107248400191000ca5401c0c0004c21401417025460076501d035005503564200c1d0f103501c480103801e0740004108004103800e41240407810b501c04107180d484840c000e203102c2c007038881c903040102400b00700c11071008084800000303490687c0c850401c0c0c0e1a544500d48a0350391301d0080150380355204000403209404108050020403095101c800c0262400c1150004101892020b03405100700c5541e0341d10a03241d68900b40114100030903024024000640545c068030519643d46100bd050166 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 274319325 1250 274318075 274318097
    0xd050c0705030604210302072d0f120908070b0301031202030c0f01050105010906030e06010b0912030739050603071403040b0601080a0b0108060906010c0b0108030a031a061903180b0402100206040210 87
    0x40d6915180790503070f000b80328071300c2b49503145800c0c2d000c0340990020780042501c5202c041441a80804c030107041d2002d416015082d6881e548400e401d0b100d04080307480c2980010010921203600500c4440e1102c40b0f4180003250075458034000402d000400c1e8414402c00d4540384500e480014045034107030454208036581510b54000c880040c43c3c900503e0304d441d803d403000003100700130410042e1441880c26450002610000d0055110701108041d541e12040b0401c4840b0060210340b81040140d42c100c0903501c0c00d40800405003007021640d03801558203450301d521060401c1259a0b010b042281d0140c440350301880164002c10011342019006020709202e40740790000545103134818046071900301d8008a4800055075120406500ca60011100300c000a041c0200c03182172103960790308500700d0000070b8166440c1015014042810b05030411060080540303400b28000c2002224550a001d03601410101200d424a4030401107411100c1c840001950005801c020140e40c2e40440302078038076101c0c242030711801 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 274320575 1250 274319325 274319393
    0xa030506060f070b010e0f06060d09030c0804060509041d0c060711030a0c03110603010f03121103130504151a0c011b030225050d050c070503060421030207 68
    0x20052040c0320420785004140d090500c0014150507048a00b04c4d4281b071583c0d150714401c842d031035100310b0b5103030b41000c010000d10294031015440f61114034000d103400d641d003031043c0d40c4410310b0741d203e070f44010009540419101c4161400d0300c034646d00b0520b03c400100a84103003400749a102c084004030188680c80215491042c04025869038880a500606440b000841840d141c0300c7c0c3c401c0760000313030b4801d00c01c800442d00078209901100e06a415030002e8904640c038540e1024210300c03081c080312041004c6006071400f250700800180440314420004a0403d6050400340320803129600c1c101c122400c1c1941c001c001140c02a4503021400106044440c1d549104502240c0907108488a070303e100c04102070720b801c0b03081e490f5020308921940c441d04080d8840858640d44100514104054881e80003101705c1d6a005026400420408000d0f006407442540e4641c0001c0c01c210080710b00741c50168940480d2a540084068001c10320103003410304505090840d110381e014850075844070070440c404003a12500307403 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 274321825 1250 274320575 274320577
    0xa0605031b010305070c031d0409080a030519060f15031b1d06030c03070f02072d1403100c030902040509030a08010e10031104060302090a1509020702030a230601080706140f0a03050606 81
    0x82a003012f11640d480392803030070080c0242001c0f105500d041c4c01c4852000027210140c0200001c403410307016040481c2c0d052003041100e2602550698007455903809411b91070780c04804003040180745a480c0c040796031504100e09101c410940141d948900300070010042111090b8040c0d0f40c1206452401858400c0010001d0340b91076002c0e04030203011204d004011800e5240c011501403265400c1c448241e81c41c1d540d1141b00c00728880d1181c16075068000c5078802c1220480759100144d044107602d000700b00c01c3e1140d000f250460300b05071441310303040e00001900502e01d42c111008500501f43d189180aa03482c090310300e42d02d07030211404000c00403e00c2c3c6117040303107694440e0088000b44d90002e0040d50769080503c20440201510002c00070000c03480d00c0300207030048144c400e42d20300e150081c01400c2980400d5035120781100e601c074030500f00545034a10100315804100401c03806082c008005002c001c1c107028010b4441c501600e0300318a0f04904006814040c0300400035103001901d10304002c00e094a49100080341 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 274323075 1250 274321825 274321841
    0x18010203040503100b040b010e03030a0806042009091602070b03270a050d020706120203060307030f0b15041a0d051011091203130e0a0605031b010305070c031d04 71
    0x40f41c80781511021030842c280c1e01010700305104950400024601c1c2005452000150b030711140c5c143c005120a4903103d010711001503100c00010000100103400040113078415030743c2c403220408640049982c4042d410600c0440d5048894018000100d102d0548000e6480d48030740100801c0c00310103c0030461144414619030039041c0108900803d0140490303400b5038440c0b03061000d0302c543c82034089000740d00d400450008180c58a41c0e44a488400d09a0703a0400a98006480c440c3c05124002000000c01c0d05c41c41c9281e055885010707800c4160614150501c812208210098492490510340c3c50740b10a9030090601071010a4405901c1c0128506126080c03884070f0384103002140c04c218000103096606002850b200100b00c0d04224140c48101080303a0b24007410407010b10346074a01b503044c85201e946500380b56201401c0704005c11060f480b00d000c603040c030b010741c0741c0e00b8065201e65074840c07050368060240310790044a0b4035040c0b1700030440d0b0320020a02e050041c80130b60b00c1c604034110081143c480e0b07081084 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 274324325 1250 274323075 274323079
    0x506090604062601061d0108010e01290a0309032003071e0b0c0301050a2304110f0a03021b031c020309010e0313141c030f0c060911090a0c0203180102030405 69
    0x2c00c0c2d80d40d017101a00d095405540680811100f40640341d00d98020601c060589401c80c0107000300d80e0900300c0440d01c0d0443d0f080071811006000e1f0041c44c45601c03240042206000070740d00440c0da82198503010b013564107101d0310a84440080588031035400d01c00400c0d1180d81c0d4002ca01203120b80300b48926400751451a010107018100d000e0104110314001400541c121001641c07688801940c0300c5079440c801810b050040340b4104412028000c1d4580340d081690000440420710b468261554a080015400740c0040300100b43c004c99405091403450b241041e528040c940035524040507030490301601c1864024860490341d020010400e03c0c2700c25800700a020142c20212690b550300c1c9540740108041520509981019031910859603040802196820204110440c08040d506a6081d910041c0c80c070064810130100c00049804500305000b4044501d02a84082c0240c0c20f5035414450000c5000f0b20f440c0f83c00741040c01100100d540007044036100c54805012a00180300200100d045204a80c0207035 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 274325575 1250 274324325 274324397
    0xf0f05220815040b0702030403050c09060a0f080a060605040c021905071d06040b030a1205072409020f0f061b0a05160801050609060108040b19020f13050609060406 72
    0x894030030070b441160350040380180c500c1811a40e5540c42260b80c0e21503030000400f1900076604100e0b0b01d003080b692144d0403c02c0180643c3c503043d21241e01d0201080e07640d001c0e1180341d0002440100f13128492050001504080c0c0301407160780e0003c40040d50764403004030000c10403a001010003080c0b03e030600c00e0704040c007020000d544031050095000b9244074810349809104628002155080345000100140840c0d0b01110440e119486035109580b503401001050f281c50a0f1461003409207400100b425540c12a41c01000950b900b440c014071107020a000305150291040d0184441d09598220a8230114104080b080741c030841400300303050800710002001030080c45907000b42e05082040c80b0840042e0b40c0b400c1c3c001c01c003a5885000b0080c440e042551700a0200340d5140105000c40e84100c003241d480200c5d2246200b42585040005040343c0c0310081c10880d82002054003b00e01c202c0003504001004c0448050b0705010010700040e500313203c3d511800d003e000001a04076a0025080e0040b000c448140302c1d00c0d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 274326825 1250 274325575 274325593
    0x301090b04260412140712060608030a2316080703030e010605010210020d09020d06021209070b07020103020c1609020c0d0221071502031302090c1306030b030f010504120f0f052208 79
    0x12003d07d40201110301e03a0400c840865000d07000800e40380c0c00411580c5206132010707490508a100c2e01c054500c10040d2030300b04000017a0085d0403c440160502c210f4480d80d0f110f0490800800301e403890b248281c01030741015400c21950b039000170f2140c01c00b0014000180c0d200c152480c40402040741840094002c04580b078040c0038413105034054101182050903041880d911a030041351644414081c2020001080c0240300241d4465406040c03240319181c200e800c007140c464a82c0f516082c5a600a8a26540000b0300c91603045084c019000d12081500040052070148030000c01089600300c8008801e104c0441c00800f484500d1103000d0701c142d1001001c55690424200d440030103002c44009074020044100421003495150085501c524042c001c00a500360a001d4104c0c068952a40100c0d4035102e240980004800d083c8205809207104080d84c24010310442c1d0003402d180212050001031040109202003025000411900d00040c1654a2030110306000e5000408150942018486d403081c5158 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 274328075 1250 274326825 274326839
    0xa030f0c051b010e090f040303020f07060e16090c0801090e1c030f06150806090c0903030f04050306010b070213050907150c030e060301050d0201050f090301090b042604121407 77
    0x800d100d00ca8082c0d1325441520fa0302e00074072865001c2600e440080441180c0094003184c0700764042c20442112440301c918150441d112002610130005441466801a00031400741014140c159402000440010300c19a40a101d001c0c1845074148110303900d00352211007034032500b007044c020303820315120f41c40b02040c40200742400100244401d0303202510342854107102103041e1851004800c0704030555a1101055a2102c0034404401070152061a042e5410b010351100c6580030300240000d405034440c01c81d1594a03000401d85400b0041e403120f003081c141000381401588036003079207044a01030600046400c0c0c0303030f50306028a010442c0d444075035801d0201030dd2058569000100400c2c00b0b001780c1c0c81e17100703281168003044060300c402e10460b54010002d80101c2c00550268000e0011006100c400500344520704010a0070b42d00784403000c8880f103602c0b1003040300300070201300031041c203c031003100c1c3c0382c4c1244502440c010b02d413150f4014400c07601d1745400c2200c20454481d020106160f03504054403e45076031000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 274329325 1250 274328075 274328113
    0x6101110110d0c02010b0d0201050711130e1903020303041b05090106030f0b09060f01120b0603092a0603061203070203010e16080312010603020a090306020307020a03140c0a030f0c05 80
    0x1a4081000d0401e600c00c260f142c41409055841140106032140700304403030b8019505684603e80c12180341c03604030003410040d51000c1240113801c2e480d01020a201705803594040c140b41201c070300d40c0100c1000208150101e0340c0001604d82c02a4411403600784600740317445404a5403480c0c0c0c08160700003129000800c1c0e082d415000038100e810008024880c3d07800b40e00030050740440c11940c8070b800c02071481c0d002d50698810200710a0301c841d21840080c02e4180d00000c20110f500840c0c1c254216801320040002d51040710b0452000c2d00800e1500082540d00c1c0c1f40043c40500c4051b007102d10900c100c00034082c41c40424003c80f040d00303500800070803425401e00d01c89030321001083c1c000e10340c00044207000105140040308561901124089240c03ca03801c1900c00c0d0000d4200c0040f001c01c0081c042004000191144000c50040c00c0c41d400910341d000851800070710072120036154030340720101071020345c02c09900054603012041d41070a021003041024001141c02c200e80c103c0281c0141b18407007400ca48400102 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 274330575 1250 274329325 274329337
    0x240c2f0913020f01050a03020913020a08010617010902130e0f1609180f0204150302180423060102030c03160b0105010309150504030203211e0610111011 67
    0x20311205095601c00d980c81c0c40a10001a01941198040a21007810b41c49074005141c1110241001401d00003010040740e90b2078a81c0c103418007001e60000f10680d842d500801c0090041000340740c01301d820101090065545401071040180458020840d4130007841c03259183c1c4050700031408681e1440c94002c0340c010400c441603d140d420410340d100f141560520071200f00c03094680604104154901d4000c41e40d00410507401c50100180d030078800481d0448842c0d002e1030107106e1686d000750300c49624010320f503142010003260b00c0c451458040c00f80c800e24004c5040015000340000140c000790b0310741d0700603415403046041100090200148680f00c0444074000008624080e02c04061941e8844005504481214002402d07031541c1d10100304503050030f034204030b600522070300c192810070351111007860000d5614600307031201a10300c10401c000d84415480185481d11074461103840e0f42420004075581c415521b40d11010081c418040700e4103900c04000c1858442e840f03130010080c0880341600d4992503042a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 274331825 1250 274330575 274330579
    0xc031605010f23010e010b07020d050a0f080406020d1806080613050109020a030f0b030331090c110d14070303020c15010815090c010e040e060f060109240c2f 69
    0x9070004100942d170050395034140c0340d050745064078003000d45d000c100403204401c504682d580314118030540051400d41070849080e10403050341ea100c604142000e424081000c1c640c1d82044070b2080412030030096041008100c0722203080c0a0000d03107a0002040b02843c100441031406d6003030400008808003903030300a1044003482ea8041064090102c0d00c9019503e102405030342c154014050042030201c1080119041d0898584070341003101c111458200c84582540129006645ea142c02a2030a03001a424540021218040c1c0011810054081c00390321520307200032903645021403c00c00300750103a4112200c011065007161802c80c003811074004140c2c030034000c91180340600d040614581001594036401900c000002c3c0019503890801192008a01da40c55640542c0f102550703c844c0c1401e000441c003414880b8024030107482c1110000d071500b00160702c00700400c0d00b4402c1e03061800300010740c030410002c858600042c5480c01411302d0801105104e0b19500e00070082484030a1504104000c40059001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 274333075 1250 274331825 274331891
    0x150b0a0b090312040b030103080c1507090905130c06050d0902040e0109050c06040e0a050a090f0506010f051509061b0d09031a07020a112b06050c0c031605010f 70
    0xf103c285800c940107522a68000750010f00c010b0000908040c007509040c18040b04950140303015019240e0300c0c50b41a41c2e85c3e400700f5a400d200b44003002072406125406040d0143c21440141c1c03a1762601081105071050008000010542404420740da400c80440284c0082c0300340328410b00d20403142e0082080c100c085030385101e0545002d0550400e00240c2d41190301c290300e45515a51084200c001904c8010302504c0034560380e140010006143c40062030300103000e100200303010760400080203c5424030703400c0305100c1c03c0e00e1000c0c1d1441d0300b800ca0407281982c0056800649403001c3c040d05c0c003494070070354040e52021300500005150269004010400b101d004910b46007050b800a002006844005c1d2002001038115660200100e910041603c001000240a444060901c0c0d03012440304080e040c2d01400d40060340b4523400c24441ea900034250010340e07801c00c0919000d4601d0340da5580344206041c0e1101c2501d42158441440030a50050002420001c400c0c006604007284030140c240004541c01003200c1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 274334325 1250 274333075 274333093
    0x30d0c0e21060603070501120507180b090f040b060405190b0c030c0c0a0e0115170702100b0f1023030106050406020d020f0607140d0204090c0f080f04150b0a0b0903 72
    0x2e0001780200841c0c1e01a102c1c200c0804201400c40060000200782909004038000d02200e1510451441c41c0100f04100344542c80307600c0c10f800c00c02048902a0b8940c4070310305040c0c0c03c40c1d4641d00c1c001254101da404980482d00440b0100d5144004801d90780510341101c0d000c59140c0c1c051402100030410310f1000000e55401c3c049000401070385071264000c14284959000c010b001803090304038155110003c0b810b107105000d118080b100c00b42c3c10103c94410050704040c2c0c0301e209000490007601101c041c00c60f01c2c03a1010329100003003105034807003800d81000c00201c460141c080d4240807803507084094008507440c0e0b036903844010151a96000b44540030041c0309001c84490750ba1320104a0508000821028081d01d84441c4011500e0030500c0c000460030441c10400401d000c1480d200620013025103c0c800b1901800c0d81078040d0000509042030410310102c807041054421040100b00d0f84140d120a160360154051050640144440c9807001c0e00021a51000700d0281442c00141101a00403021100e00e01 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 274335575 1250 274334325 274334329
    0xa11090108031201091113090606022b0c0f0516030c091401090209041503050c181603050a1b080108010606020f03030a02070204020705060103110a17030d0c0e210606 73
    0x11140120800c06503110f200107000f0003840340c0040169880070080603041201e404406000d07018158400100580d554400b002890b406100d10a030004030714600c41c40d110000a1346441d110740d024600382c01c00080c4061401006140c04140c9070041d0000101c41e050010406070030f00d546011302098403070040790040018548107a0040180342c00c807103642080307140d180c03054110180d084042c1d140d0344a601d4035000c0000b40fa0100d610700046025100901c0c490300074001380280500480c0d498218510740204200000c1d80d226080841030007031380380008035a620000241c00500c2e5070711035290410a9074844444040d40000410b069911940003000040e0382c0784426655503595290300aa141c0091000444008541d40501a0a800030b000585080066510203041400c00d80040b141c9420b12400c840d0b150414000701006010b01a188001050000043d0303a134078083d000c059034500342c46070043c90b40f551051145182c10b40000d0b01003906100d10050a40240c11010140b9149104400000d10744d4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 274336825 1250 274335575 274335577
    0x50c030c0906010f080c0405060c07051302070803010e100504050c1b0309030a03050702030708061f05030c0603010330050d1a0a05010804080c07170606030a031e020106080a1109010803 81
    0x1c2c40140c4600041200c1031205940030311000342655031204e01403000107516190f140051104418410207403150a040008210f03403604400032041c0c54a00c10b01c00040014610f10459064600014910005950340362240c81d45070301d280c0141f038009003070038184607080700c68102620013040c0c240150401034401c180d21540e603005444109501d03a02c5802142c0200e40260005e011881c00501030b50304881e10340402600c0d20001b52500300c0b1380d0020b803030600b000c0240d005440c0d0203014100c014042c8150f18100003425400107000c050012603c0c0100185051485100759680c0e100c0000d440869950154014020342c010521a00417223081c01d070700c0110313060b41e03aa04110416004040000e0b00d801d080c011505404001d00440e1054420003004044400c1004100f005100794014004081ca2812400e401c01002822190003070b03001021410000780c0201074003070300200c01c100b200c514180c80c0504034050500e41e0710029941c0180c1d03c00b80140400030680e03841481040d00c2090881e40c0ea800082d40d2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 274338075 1250 274336825 274336831
    0x90a0819080a090507091a100c17030702060601030b0f030f030a0e06070b040b2a091201020c07030303180c14090601020d0f12090803070c05011d0307110d0c03050c030c09 75
    0xb00b034000d508240440c821a90105552858420b0b0905d007c2c003010002c218a81000400240422004e24005081011200c1510f944625100542c1e0a605003108080c0d80c580010304680d0601d40c603a12104c1d036984811800340202c620040403180b03003070310140340e2948941c021142813000031020f550040a034223080c41101e075819804903074038900340d0399919000c0610740c000c0e244410141100800c403d280350700c1d185003550242d0300000959154031010030070203856a00e2503520351700e03401801601003501c0089851021a6010308012804900061800c0600741d05144014004115490702040c0f58001808420380e4000a980c1c4e031209031146401a661107044092080004600c00351130b402c0a4841c8107409800c6106040c003290154130390f512085607401c01c81c1c401d40007811481c00c200601100340220700c00002c20f07070700e40c09890101058031610307807140180103002000442800442900e80541061b4003682041140703030300c162203242c1682c0b035404d000340041c031a102d00d48060416290101d04d0b240 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 274339325 1250 274338075 274338083
    0x105030705060a140901090506071113060e1314010f0e0d08060d0303090f1a04020103051b0a11070504091a0c0f040e0604060329011203080f090a0819080a09 69
    0x40c032520b648444041c07581c0f100c0d45180c1041290000051a270b202c1030090022544243d0046003a2007410302070200040d20442a04500c41c14000200400a203200249400c02100028007001c0c64007420504103803000840e0441d0650b20740103088119150b80e60040e50031302881010344050f120350f134104940b04c110030303105964042914802d40c0b002038000e80c40110428411200321807491402d4558090202c05040f40c8140f20a200040108540e0b01d882a55842030b1800429840b21540c5070300d1000500800c0904c80900c17081c1e2503015a420820000341004003030043c400d0005500b180341038400c100320480e1b00c06819002c440892824451801074491690142151904103031400c20400c40000700508030395042559024040045030010306800c0c0c400070000c0440071a051540321030f192186050780544040c6e00300d6441c180000f40c1c800e0b0400c0e0010700c7c3c0001c031080e54560f420700904145112400401d0b4900004038408000004800d0b401c1190f26615000e100380d80340e0750030505a91103650700070 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 274340575 1250 274339325 274339337
    0xa0e240f0a0306030c0605031f030c060c050304090507210b06250f03030e190f110109120f1202010207031e0504030c080304090b01051804090f12080105030705060a 72
    0x400c012030040a03100052252502207a016501e0f1141840c00d00c0319000740c0d002610000820440b80c0c0410046100070a4202000440c1842e5480b451038207500e07806030401300440d2958550500c402041a50094001c0440800c060b0411280140c0400d690802204c1056084031042d40c0300e00745841174140311003005c1c181d02e00c2c01d8210910460b2800641c203c1c2d15030101c18400e4440400c0428203503040440c441c2e01e002030354078421016680783c00f1003030520002d6405034903000070009488500801c0c2095020348041d021317190705070058850070102d070030084200443c803104a0a020f00d000c244110700d4001c3e50350010001d030100049003071780304044015010a00f002c510040842c8820300d186119800e070314110341050b40b2550740607007140d4980d05c587c07c07650001c501440345030000c0c841e41484001c2400c0c0756143c02c0c000340300419505141c5d4440387c81035688003010302c02e00440c282e2010b00164003443c4003e00220b603070809003820380f00b8000c1501901ca071703030300c0407459041c03440803910b0119168440c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 274341825 1250 274340575 274340587
    0x1605010c08070e150d0f0c1202130306020d02091002032109150703020d150801050a060e04200d2303030702071e08070602030c0c0a0b0a230a0e24 64
    0x4c4128041450401044640e0030407058000000381d02ca000306440c1c2c0050301044900c01c45c00300403c1402030304049000d41d0303c10032442121401c0030000c0e0045a0b4072040145c1c0390401880c2d048024060080c2c20780c2c1084e00f20a03450765859000c0020159400012240d603000c103041044245060030880d03959070341e03600130700f1103580d824904c085541c0d1020b40c0b07150251800da04c03082c154050741d0b84c00d00d04039510b103140b00b02404051428080c859002c2c8070302404210302c516110110b20000c2e0046c20140041498000d0501c080b14001c03d1600c801c2c0001d820f54500c045c81e0300d000c583c9240e5404582e41d030140004801074286d1404800c883c003894650703000f480b082d81005211107819451400042c18003d114800040c40081803108800400e0175401a50301d5a51244145041111050010788104404034040c01b002000c50305540400c0c10764039110381074007c00b44900301c45a122551010501d440802e013524905d50100601034a80c1c42070312007006045c00355000100e05080403400d40d0303500a06000b4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 274343075 1250 274341825 274341829
    0xd021609060608011e050a080a061406010c0201050a03020d050114040f0902030d1b14011d01060605120415090b06030111070c0306090302070e0114210703030e151605010c08070e 78
    0x100d65240540005c5142d186607640d0001040c02c415988103c3c0d5940200c02d80030184040c6104031040400101e124051515040000900030040740d14000d05002c0c020034007292070f0740b184d810340d04640f8442c281005203586501341d10303d1158944070442d208a00b00707641440102c085001d00c0c00700c03540c041d000f060801005401912452130150b50001258060a4441c01260300615500701048040300005017252441c04002c40119150010b0328650303042c044100215944101100c1c1d0141c05601c205030f05403114a0040d8484200c425241c1c1c40d0383c2000b444805011078203860358055001107008201440c004828030605010303d050150051000e00c0042000c148607802102c0c545101c2d105480741c098540303030114104082078102031600d05203482024082d044c4030411126650303042d10345040c601840d0908035610101da000050801500c0f8401d2544c907211050f03055641002c0c000c3c1c850321541040c3c5d020840c3e0f184290190360302d40c2450040440c0500030005a8044d1225a880840c0c520705e46007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 274344325 1250 274343075 274343099
    0x10504020306240310150509060d110c0c1c03050304080d02070f0c05030607170a0b0f040207050102030603011a0a27020301090e10060807140d02030d02160906060801 73
    0x420340340c000c150f20980b094042c86a5004003000c40120540d42e4a900f0300c21003040b80701d14141c11900100d400e0309122107415410130162210035404542e410b0f901c00c40f840019024002c175580d0401184004552494083c1000c100d5144080044e10000b550b104104181c181c4c0d094440c2e00540030a03020404a07004c0f42c0541c2c01060650341c4010b001d840d00303480da03907203245526a00b41c040c0c0360300540000c02d11092a0611115400c00c00919024120201c0400b031103005d208042c10f410b007181d40d00c00e0300841e20b48039038a100d284410300400854450b0f285040130342c040c1d4030480c0d056100b5441d01214021400310a0140c0c155200007820b01003078035003003085902044480e01d070411021803610f084500c85001d00d000a6020b40150301c00400d03c44002c0d002c0390b180c0384600c048010388508010041c0541c1900141d02e000b01c411240345540d000d100f2201182c2007060340c4002942500401c0303613040c20b40340c0000d8012080c50948800c810704580e1800e02c2c10454031103000380c20005500200401509480f0341c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 274345575 1250 274344325 274344331
    0xb1629010b1902161e03080703090311030616121416030f05040f080309160902040e070206070e0f060904140907091a010e01120f0506120712020108070903050601080102041403150105040203 83
    0x2810300751a0340301c7c2c641140300d402401c0118006041010180f08203c24400105507103001900140711a040c055241d0340da000307115139600c04000303081480c0001110260843d032075543d9004800c1e0030130304005200307000d510001d04e201c1e408241080000241c1c1c2c5034901c6481d2113aa00280151070004e40344c0e641d80d13001d0f0310103440009144103862840245800c2411041c00030409481c0060783c8070f150000b00f8018201c000c00b100c0554000030300300001580c01c42d01141c8034079821609410b607401080000749d65406070140d41500985401d802c244410404d109050245210504982c0c0847d62181c8031010364100c1ea01c0303549041c00d1040c00000a50050f003206102010505140b840b81c20001e010408685135200701d404140d8407003080c030445082982c4040081d0800034040e12005041031415030b200040c4000c003d04100f103040000d01c00610035202d06c40610303400401d4460308d5968540b124083c5d0805d002c0d80c0d18000a0000112841c5000114020003459521803c00340d070f1310301402c00000350001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 274346825 1250 274345575 274345619
    0x1c0206040e0c25120206060f04021b01050c0d0e0706141b0a0f0c050d02060304021005070b01060c0309050109080607030b0301020f0a0201020409060b1629010b190216 73
    0x50082c01c1e01c3c01e0700782c4030000b49458411403018040e034490410b988020880030003002990081000c2c4034258546a10782d01172600141c2d40543e4074901c12256000003500c04610070540c0d40303000c0610441c08281c40092440e452610420301020318444401d545440c003611504022615040c0308461501c003010180c6410101c07455480c82800c0c110303c0c82810100320b01d2040f01d4107003444250808001c401e500d00d00203000190355600700700b40246e000c61700c1c9200c0603201a01c0350480a594110003071281040b20382c00c1da0700074803420300340d6550712014009000d480d00490104158000104071540300344039000c01c488000000f07103069290400306130001c003905524190195001c000c040c114840703d4004061014556000590300e6191820030000c42d84650004608500d040054a56140170041609800c542105524901c1e0303032048260907072080700070744503900d00e680e240000456041c110050411085950100000c0010380102280c5a408801000169112900301800500c1075180041d101c0b05c20 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 274348075 1250 274346825 274346827
    0xc0a0b041502042102220203090105100b0d02030a11120a0f11030a05070c0c060905010206130309051512190c110615030a1502091f0203300106020c1c0206040e0c 71
    0x1b030383d01403124501d4880842c0358000e80000034050010001d1107403d0348080721401c0b0340d000a042090304c425034032821012aa0b115008408182110314a40c400c81a1028500d42c039580d0b00903613501d035540904104da03003003500351074205e440c401c48041e40200554507081c0b0b80c1140c91591028050030051070017620130390800c55041c454a000403030ba00400d0018000c00c4d1100306909141c44002854400010300c03010103201242004000a6080400d8400703581c0111074020f01000140d0400021380120301c1c50400c0304900409104084642a07541c0b07005421030310040c400402c0d4a0000d80b2001c540000800e00359020701c00043c1070503041c0c40c00102c002c00080948200c2015600c403a405402d40d6113218a42c07a41c005840107540c0b61500d580c043c18030040441008800c01200c01a407280612001c040c8058501d06d0307411f00700030b000d401c41c240710004540b6000c0c2c5541c48007402549ea922100081e405281c130b840341e401c0070160b03082107181182d50007001036142c5410001c407403000b0b5034042d14051010700 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 274349325 1250 274348075 274348099
    0x307050c010507030e0d091a09060f0a0c03031d070e09030f12010518010b19090503010e010f050903090307030f050c03070617010b121b0c0a0b041502042102 69
    0x800303000d039030300400c0d0f00d50f800304203500b095010609240403041745009103c2040010020161003503100201ca00201400948444c50800800c0640c07107042c003c80c00c0c101c40052144d6489810400c01c0e402540240e8041012464040306203542c40765610409032198013840d03040145014510f2280c0e400300c0103030280c038100f401303181d80d0f40c1d4281c100c1c0e0408100307641e4a070010f00044c01c0010030341c148180050710104055151181001040c07050060000c07401071201d0280c401c0900074045000109005002000203420030f0070610700800307000b0607600005e410880400c11303094000083c0c80f540f00000300944400e40c0785a9503100100e00d6140308680b180509941105240da05100d4440101000d440e81440305410001e80d15004005030805040014180000000481c1c1c0a480b5940490343c901010402081c40c8030140c018002d15280c105184104681d00041100c0d504c802c0c2c2c026445441111148441d1501302000e0b07001d2409001401c031206020310310300c244528204203d032800a0700000980d4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 274350575 1250 274349325 274349347
    0x305070f05190809091605180604050907050a120605130518010504030f02060a09420603140105010821120109021b070602031b0f06070f0906030b060301030602030705 73
    0x203607000c2d8181e4044802140c0d0720039906100034540e5015114085c1c905108004160141860058000e414090080010491115126a411500585001010030f003a0345404a4010481c2c0e104005040004903c00b081405c0946240640c1d0103a500081c1300e03208008905202c0401444020584000c5c0c3c04040058100080c0a1068601690007540c50100e8103040d103a0280c40e0020207031420349254506000034010403000402100c00e0083c902ea0030201d100b034400c495103644880140014504200a124841d52003182c0c840000c582c440d0248900c3c10007060356007801c0b55024451704001d07410003d02d00420712091030040e06120a440e03007042c1001d0882e5501d24504509070450145c10340d0004130745005408500310f0507000045c8600821105003025802034903800703011080e064070798018609282d0303a1b80c14481e09407985401022a0310a1816007001002500d40da2802c2021440c00200440c0c0c0c0b511034000d20038102170141c000c62946c0d19643c1d4020096000400c40b40403c0f0302484841c0b404 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 274351825 1250 274350575 274350613
    0x3010216030207052103120402030c040606030b011404030b01120c03080403062a390f02010915020303060607030516060603060c1706060904060512060a14040305070f05 74
    0x4a4082c2d40108540c500b00014070941906a50240000e03c0c05a100402c0c1440000110352800400d00c01035640340d200c500c00f0915080c078800803550b0007030505001103681e66241d070095100310b10903610140302c29007040e00750703c00d4469400050082c5c0c400c60018045140c0d9000c041c0b2245200b031002c02602e40c1d0b05e880c2c00001c5d41060304201e40082c3c84e1000e440e0744540c580c2600e0818081498020864034070b000c806032803107079848000c142c1c4066200c03038408010350007008204a24a4120441d240c1829450070380e00b044d190810803408039a41e100046031140747c0341d04410103a44550000e51a40c3c032007004020071034000400803070400804200301910000d120114018452060b04085803090940c9062000d946c1c40c00c0b680c0d403c100712030300824500a00b452003d500301e9404c1d50019500c130800c03000328024080031b411994004414080d04121078030002000c6200d803441203403c11042603110b00b82250018141d41c0513002550600603840891000d0b00c44404052090b0708555212205484140307807 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 274353075 1250 274351825 274351867
    0x31b051c08070305060a08060f04030509060d0605031005160509061b010f0c081009180c030803070306050d0f0b071205090a110616120c02032a0a03150209030102 71
    0x10749100c00e000103075426008898101c00110b600600b49404c1c00c0d401641d0300802004810041100c0e8003046c02d16000f10125008288040d114503910b00b846130300c2c3c501030a60351003503078041c0c46903800e8150540c40d944222070040058090440301e40d110b44008031119004140f60350f501250401541c0c039904112044c2c000051111000802c020700712003008800ca508890347c0e842407000144c10440459400d20105090350900ea20001d85a0f04140c1400c20b45050b00b0f50043c00300450b500c0c084240209403010710301c1034680769070921140740c40c1e1042c024444681140208080d403080e202c10002040c1c49541e544c0510345141c83c24490704c1965107070f0181e6000356000b55003604006000003d000081d8174030040c9802c16242030b440c1c9174204030000c000c00001000a08112404982540e1840c821a6a00100c9030000e0480c0c02c0c401501d92030b001070708140c0c284c1d26411440c041203015181481c011103400c1781d40104d400e101c0d1410385440c0d0000303035008010143c0c0c955420091803555404552091b84 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 274354325 1250 274353075 274353077
    0x12050a050906070206040c0b0a02100501030f0b090304050108010e04080d09140d1e031119051902010902181317070606050d0507060507020402280f0c031b051c 70
    0x10035081400c002800c0a00c041c154100710b4100000700408244050100021070b0a80c1d960155240c091103412800d003052004900d00990812000100b40400d1076080620706029030914686a2124154140e6030b101c0d5110302400304030507200400080c0e4011180035805805055468039040d0441290070403030341c0180c0201c2c0d800044444551201d0020404007142c1c2d00346040c6007045211703010703e140a204001030803004040d03d51000861080200c41605e501d40d1012600709491080b43e000504690482081c01c1d2444458005a40029105000354114150082d00400507150074920003140c1480c020040b10302482020b0010000403160347c500c1060b5212001101d031500494a400c0c2c0941d000c5510144c400c801c1c6400381c034003240c0c0c046440011901e02d070911654845032417000c100640600b02000d41410b21100d00981140194074140c1c8110318179a4072241d410000420a43e40102c0141015001907400407405480e081883c010a91050044040300c0718213071201031450240c040c0b00a040 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 274355575 1250 274354325 274354331
    0xc080712020115031a09010608150601020c010807050703030e07120609050c03060c16061404080702040606031a041107050604080c1612110406033509100c0312050a 72
    0x9108680d0a110b03070880203030f405640c5101e00c0d182d0b03103807001c84208500158403043c80800204c3e0004c0c0095121200604082c1d007500c0c0444214403250000180c21110203015000b20066500d0541c8036001203481074200391600c3d4104ad44980b4110700400f160940d8030360074400c3d540b020840341003200d05401c1040c030403e4049451039040c5401810303c0119265140a0341c080814008032400c4001651451007040b18110303030700029410800060840850800c640e04042e4050105000081c00101740c0302e4002d550034401144c3e5410114221090051094020381e4107080343c0069103002c0c3c1200e00b080000070030450508071681c461504207441501e00310303510740000458811100c01030181811440c4124003001189251052050807103403400801805240100791071440d43e652580084095604010070b08a04c0c9407a100b1418070b80d966088400c92000500e44c0042c05e4a04601252001c4101400c01c0400c8044c03108140c031030041c403040480c10303c05454810700080c1c10511800b8801e0901e08004 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 274356825 1250 274355575 274355603
    0x30f2f0304090b0d050307031404030b040309081e0705040c050c16030506090309012a0b1609080303060616021309060203040215160b1f0e100506120c0304030c0807 72
    0x301e81210b0103d6035035401043c2d4100280d011403004420b4844c41609401d0008031900c1e0011540101e200d283c000400c1d0901d5542400f0505070301c81028025178003441d089a0503210f20240140e1825444121074180b503100070300c1842036041542140350346111a050903400c09925080301030500e0300d00d80701c1c07001d0000e81351030400c103100d000c02805403c5000c000107941303092410341c0020130f80141541006080360361900001c0c010425a1604030780300b034100322165040e0030240c16580c411010044414002201c0c1c500124100d40003004403130140c00001d156a00e4400c40300161402455503140036039000c1c06d01c090700d0b1118869806000d50082c0301d440c0c010781e2483c3c05d10400000320b50a0340712200100040c0f15408030541901e40d58042550080007001031903031361014058006042d40d80780c0340141c00060000940210381035140e07004507404501c500a0640780d205102c103501441102030408001c1c500843c6140c1c0c0107000030b50b0000d000e468480c4141c40c81d40c4072400d282d407007072100f1510a40101c000e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 274358075 1250 274356825 274356839
    0x81e030c071101050301061d0a0b030405010c020601140d0b1b0c160905070c06150b0c16060206040203030307050a051b0a0204050106080c0f1c0603051e0703030f2f0304 74
    0x900000b640c400d0030701504550400c100101a400620808003070382c0d400322030501c0c03183d440ca03140368002d00c0d41c1304005540746094a022406480c3e10349409016100b69000800e0016042184c1480035070050020b45c08400c16840d00c01d0b1200000d8042c0c00c424043c0230200d06040d941e00c001b0040c1d035007200300501ca070842003284114045150351240d01510315000500c01000d51098000000340d41003000401d052400e80d60342d2454021550000415581c0050205e51451000c545c0050611030042140407442d9100710030790b1205002c440081d4950070803c00a42130500800c05064041c60728580907040c600c140500344d01a160101d90129a544988120011480c0070300425001d8001c9140c15229030410401048090141ca80c81c022120b002003103180443e055201962200d01030a4018440d8503584d0410b5910b1b48600145445407580200300f0030760744100025000100c0e030f4941da8035003a00c05907000494040d4821040c1031201c4048402412a00c00301004504104001e0005540d6407444c08103 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 274359325 1250 274358075 274358093
    0x180f08090901060f11210c0c0301021803070e010b03130311070902030118201804051e0a02090f01030513020415050a06030902150a12090317060f0904081e030c07 71
    0x205ca107149511555650822100c0c1210400c4d6800410300c0c0c4030345444151941504144844524a41540c808203040d1195441950429203900c4141c00390303000552a009200741440c0c00f4014111030701c0b400c001050100d4010740300250811700900d00b01003a454008109410300b55140c0c00301490740e40200040c84110804034801101d10000d610030801d022020200403c1040040d031201445500482c0f0407005000a10310b201039828018403c01c01850466400c280b5031b980583c3c0aa4440d0314100001d02c0e640452080701c00c50000108189003031b94101c40118040c0c040100071180c1309140380071103401a1540d0107102d100c110701c000c840d0091405d000501c41d40313650304e038440004c050070540c8100143e21014801d400303420b510180c0c1c0d551034040200c196948001560014020351805420b60181a40b1440c00038090300e02031200002c80d182c03c0100000c40000c0d50043d03900048100200780021004002050b5003904034221080c413450040304000c15810444648010180000b1007004108140c1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 274360575 1250 274359325 274359347
    0xe0612010e150d120f030204090f0603050c090c03151302070f03263907030206060105030f0a05040228080c150d02030c040b04090b010e0301180f08090901060f 70
    0x1451a2035580f90545412401004c8110300d8000d00030b8001c0b00a0030244280c0450300544900c410a008072589911080c0c010b00061200342c1b2240111800c501c5245032110100340034074481d2030070600b140c44a401d03d1215103030021801c0c0d8050710b41121400c0606160024168080c01011a41444401ea00300508518828000d41102202c00c0084864022403800d501c2e40000a860400400d02c15180c41c40305681c00281d4410741600c42c89400e45800202600200300a920070b9095940940311f1400654807400f0641d00e4070003031a018070004400c00242d5011781c0d4024001000340e80c003c0d403281c03203000040071481001d6021084c100c02c14410908100701500c41c141c42900d609005516000c040541e601a10042900194001002c10007003c000f80554000d80350124a80f592295074826a074010301154640c10b000c03076403a44520041340b6041c8a560f001d515402d50803c0031402c6e50352500d80714069600c0c1140d210300148818122503c80208885c0a0222502c5070600c0d500840e1015010281d16 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 274361825 1250 274360575 274360579
    0x712020d2d0b01050a2a0516090902130e12030c0409240e13080a170601030903020c0d080d050403030617010207051e1005101401050711010e0612010e15 67
    0xb44201d16541da02c07038111a10345940346004580c00c0202070780b880785d0b50514002e0100142c10242084280000864400c0140f0100d014087c003035503444040a05031542d41102941c058810301200c40c40364601d800120846000c4400e80b00d50254103003c0c0c44543d00183c1e0940c03607584001c201030100004510607a0702c0720710007108034081262501c4030680b211769203000b5902e040440c24049040412000c4007050400d9100445a0329142c04100007412190038004c4e404000c1512000724607079500900c41e04000d95095805081001420750610a1004080c1da046490003010492031034003802da07202c2e182c001c40c0300c3d680100c0c900d494403d0b080080303403480f5000c0800380d00c1085120009500000c00f031040500000004c0c07032030b24400c1216400c122040003640e48883c189010058400055a0b08a00792412200d05800300c5800c0d80045540340180d1400416a03000d666901d007456008909820200100130b08961404040c403404215070351003a4401c0103c000b0b0701041c0507030b044c0340c3c91000c50302d0041 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 274363075 1250 274361825 274361831
    0x150e0703020a14011b0302010c03050106080f22021e3d030e24010603090b0a0504110307090906051e07030e011803020a050f0c03060712020d2d 63
    0x464001900c115064860b08403960002c3c0d41d80c40349640103041c40950724091282da64040e103203070709010340a80907110b20303c000030b4900400441c44600a0800350f01a44410310407140c181da071090480c0c4c41e2800030b60080b401c0a410101e0340c0042c2d0319101d0b01c00c1d024507064400d0a03910081418004501e00185141035001720b44144148402854900700301c1d0800220051500c142c1d505c4003e500070700351840010b94900a2a8030340c1c1c0b10910064201e942d108114486140c942c4e40e4030801c40480780d4802004101d00d84038000f0810400b0650042c581007401070440030b134048212000645000381950100c400c5946510310711050041c54402e0350342c0158501d0343c918140224280e132040d1002d0080ca25010b02d40e0740e840c0c0300c000340401d601c11040c0a10444015a0248aa09010750741c0c070f071404004c5809118034409114801000f0039240008040540208003030748880c24281c848a48603d007500e44154240303c5040803030458054282500d9241240d900b03d50000c03848146c10340c0c585640c3c03102c2242 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 274364325 1250 274363075 274363079
    0x304140603070507030f03061805040c0b0a05090f0a090203090709110708030601230313050f070509010e0403230910111b0613031101020609060f07080c0d09150e07 72
    0x14010f0104c2da03a03907038540341ca9000d84403170703400070380c001d04450b04031401c1a84000d40c00100405241e02107400b0340e0040030802c40c2d05030780d481e048902d8805c103c194030002d00103001c002c140c0e0a1040540301002402040180d52945466451007260400c9541e104d0710f900118003005180c106110b0302641c0c0365410b049501d01300c01034541e90017511000d00b016042044403075101d00ba104054921045000c100c15485949082203001080c0040c0c4030141500c00f03009960004041020004a000490300d02030104e801030303860b102060300d54080040007641030210a0b004400000c0c01c1c101c06100c0a030411090a80310b5035204103200d00c4059800812041c40082c618030720342c4040006e540c0a45265042020b000c4a0040e80402c0981c081c981c1c00d440c0b84c1c00c1c801404020080d03e0850708481c44000c5c1e0807902150303500000340396961401c0d1100b228030741942010594082c89016001c0d4004081810146050719040700003003101da031880240d640d000c7e001c0c000080c0c040039000d108a201085001440800c0c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 274365575 1250 274364325 274364327
    0xa020303010f0f08060712200306010e1c030509031c02070f090c120203070e0d0506010e130314160203062703042706080d0918060602030a08090717030414060307 71
    0x2240949094144211f103200d1044a0b00c01d5008007142d2042d4511411100c03003540d000943d15002914200e010800c0c65800c40d03c2030504412000d80314856265180c40107905d0749007910140e00c1903511135054094104100d0030121405c0d14150040410341c000c01105260514880c0f103509a5080941320504103a040c00846500030b141040c50440c902006a4a03255508291000c0400403090390708200641c002c08140807010030818101c078465040320140e5500c015680000c5e0031240c038002d010410700381813103010031208006841c0411504030b11400180054000078030b02081100c50022030309160000081074044042c100c0501c598070382c011400c0a04102452210303c01d000c0f40ca000b41864501c5001c0e02da009500800014103d82081d02ca04c07941644004144202500079000304034030081818403045181d20a81049071504c0c3c0c00303182081c8800d0b000301e502e1400601502d00621a0341c001142c0020400318007800421844021035482d403a02c200902c11445a03081c59228200c1407082026103 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 274366825 1250 274365575 274365583
    0x513030c060c0e0301061d0a0b180411120d02010c0f0f0e0303250c0807060909090203120c1b030105010b030c0f0d06030f05011a2101110a020303010f0f08 68
    0xd692150010a550841c610100c50000e520740e0030720b905609003d400104e841d051003401c45203141c3c03086050f00d56514501c0d800c040d1070715515055080300381040d250001007500c200a40d04030348100304241c00058048002000790a0709140b0030303072540003440c0c0d040215409204800c0d000f04103080c40c00034034114010140514045160103400c2c001c0c00c202041481d9414401c0f540001400e130008500401d061003040e05038020a0400c0310001c1c000b040100e001c0d10001050021102213a035800701950401228101030a03000700201d07054443c2c004445454020340f0040c22241648900402c0303402081101610078480000d030860007a4500380050095a4101040b25801501e040c403080e5a01525070304880c49229810307580c0d141c6490321902104000c907003e0002d280d540500024001c040040f4000220342e04480021a80010174206413024a0441130030000e52104c9500002007441928081c00c0032544020103590058100200610800c0158010b1002400030075004001c024201038050380e80d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 274368075 1250 274366825 274366847
    0x90320042f0d0e1501050a0b030405100e010f060803030615040506030402060702010c12262802040302190e330a031209090b1c06020a0201150f0302010201051303 71
    0x203220740018409a1404142d08240b00c1c000741c0348121500c80d4544905052607003801c0c020184220101d07100001d080f03003c8030560340519042000780c40c0ca16201c411920081148880c49220b5549031707030401050504038880c1070020901c4400ad150303a49041070421a103452103801c4200e0800007071109002c02d48411060341d0740540d054810507921002c80c0011380d031000320b46800030105c0014840c6540c00b51b60100c608a0f034196105a044c56040100325240780c0c04404450460758a859641503500030802036100d030744d40d903c0c041c07001841c080e00e80c0c0105801d007028505000c140c0f450080300b0880c2e000c01a03030250340500b071100e16404480c443d800c46002a60548503900403540462403058243d07440308810310065610450380c490b40e24006001800b881454840c0e511190726100e0100d110382040800314145005030702080e5041107440da034042c000e400c4009030070215903850100a11501e0400c01d000003a040704a09204132906c0d51000900f9a0310090407400144a075240d00390000b9040044000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 274369325 1250 274368075 274368161
    0x1505070503090906040b061305040c0e010e0f190b0301150f02060103080d02040b03070c061b0c081803072405040308070b04060908030c0a0201050f0105180709032004 73
    0x10360f6486a0380000c0c081e1100c00d0855030300030800075800e0b11f00c42d4200b4001c02200c3d800c2d2030034004c403d4210b8042d034000d05c07176013841c1d408102d00d14000d416601d40550001c41c9010000c0001d0a04007151018101c2c2039015007110054078800401032161400c901d4000320220040d01e051a03010846017030094560a041c03100408150000c51360b190f09030700c0e03901601c014280d03092010751030b032030401c500400d403900814041da5584d01d00340382043c0512440c0a1400c0d09040b60300c0c0c21034010000e0741d90700c041d580100d00d84810210b01500c103000700c3c7c1c0d09100001c01002e84142c19140364011039900910180c680d01500180326040100300001144001911045604a681ea40306d41e40c55051020180245003401031281500000300101000d440c0c000d810a415554000c001e40d0340d41544940705940f0130700907594400c40030a0001c00c0c4040510b10f10750b02903202d207003030b0380f07034030742d41c2d56a600568018055005008180b141041c8607080070301c84c10342d611981081c00030810f034044403403481c25840201d10350 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 274370575 1250 274369325 274369339
    0x7171507051204060c0e120304051309060c0e0901080304050d032105010b03180f1005041b06021506060703170c161101090e070905101e02010501150507050309 70
    0x18200a0280040e03802c04100311500c48000c1c0b0742460581c00030040da5080b0000301d24480080c06080c145402c0440440100100440c03500b418501007000410418075840d5400da19603c050000401d58090040091001d0300d43d8040805248200302070342c60160010040342e071051104100e540c0d1003031034040c8056010b04009205e00c8408549002198000100d0082c4505240000820030210001584280240e010244948400d00e624680324a030907010626180d00000782d50a50070714a61000360024404c6d848810041d038004845103120f0f00341d610400c0540c003c40611b120003e004850b0a900500482d411b038076055a568014140007415420203209415400002d40b00e040102c04445145240c00031304030040319a854404102d42da034646050006640510000d00205080c0450303000c2d00003500d4a1003e03d0a00d01031010403103032450600200180282031400c180100c1414000600d026800420a5030600102c50072075a1001c800804010040002202065002c0b0559140704801c031450 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 274371825 1250 274370575 274370581
    0x21806250201030207060e060402100f020c04020d090c180c110d14040b0f091003020702011d01090905070c050c03121804020c01140f06010509100c0215180102071715 73
    0x128000e002c2d1040003000b152030200e2040c120b85000234072030322491080b100000d200410500480e10344076440c40c8080541d0042c296041645050703005050b4440011000113104a040c0c1ca80384444c40b05948104031610a552504030000100e0050360019030490400c1e1485010204141d5034903d03c9048150030401c0103401c400003803030a44102c2e0001d0410f1042640c1b034404040001b44181e107e46501c0d8800d032005000e1280440c0070340203503000a50140c54020f409620301508000c5140c00e102c01604000c442040410b04d07806070b210b1035008150a40d2081084d043d9454858a016071109140d4842d0780510703c1c2e605a100008202c40f9698858209401e0302070203c00030801a000f0608035100a50a040c001c92004000041300c6114031800300c040e150907107540005403603038422410801d4205802d15081480b86000b086900105480a049103000c000c06450390031031900310494920100b03660b0424800c1d1507a04201c500050242c1017036074501b0303840105103907589640701c01003250032403880400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 274373075 1250 274371825 274371827
    0x71218020108131425080d110709050c0306030105060102012009030f03040602060403080a05041104020f0706060e090d08190504080c0604060c030c0509030c0f0a03020301020d021806250201 83
    0x80e6426580c1c4503032039807400e001210324540c46148088032410720388002c0c1c002a84000c1e01c007210408a41c4414050b000d2900c1008023241c000c03921804408440c4900e00c00005da440d51842130510910403001016280c2c20b0106c00c250079a8006000705045a041c064903e42400616000c2d035101400440e40b55550303001040480e00301404c2203a4a2030758080440c1c0012030741c0c3c010901601c5070303201c0e54418040d0b0303a805410100311241580c000d803d00150344015007403824103500611060005400d0503050107505d680c2c07102590701c2500801414082e001c01c3c841c01a50401c14400a080030381000301d450b10700301e58065210a0006601001c1c26111404101400b040a04070f0344800c1d4020151030036882d20707081c40d274040e000c05d0080d00000792501d0014501035218409407403956034010050b00c03646d4500c0007000a81018002200e52056a0650000059409100038618040300784800341e03c80b0055a0004001289011014000c44c003c0101041c0003416840510030a000341d94a0001c070b180c1400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 274374325 1250 274373075 274373101
    0x30207020a090f090f11010201061a0a03111605070609050d021c0f0b0a1a01110307110102011e050a0c05030609041e0209070201050609100f0b0f090402040e071218020108 75
    0x1001802200d60050100140806c0b650b12150364003082c0c000780211591150703010000200300c8600c0207809030a11044401c2442504010180f272507101d4031900f0042c6035402c550080c84e2100c8111055030081c04200922504040345d44002c001c00c46440981e400e194010418070038028401c20f18454980b5500c10404c8019012000d400303800c4244172195180c0821008014401805900c54110a2000fa00c5066118218040d6228041c80165051444943d0381500310800320030306078155500c8040303c01c2d50841c17000480030034207404a004202400c0001a180884080c86a03030010000c0820820229071a100406500b20b070b800b1030119a000440c90100340d00c80040e00c0000d50100c0700b88113208490f541500010300800d01150f0185454503001644811007901e88540440f10640c61820080c05520802030308a40b004810041d14102c04a00003d089a0042e00424030b0740801905100e882c507031280785901c0140e200c0304c00700724085584010254851007150001e040150020004030781c070304844 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 274375575 1250 274374325 274374341
    0x60507150f06031a090102070201120513051f0b0301090201321b0606090402031c050906040e0118020f0301091109040e1f020304021804030c210e01030207020a090f 72
    0x42180c60340720f140151302d0181140b00c01d0250365801000c290000c81c10300c2241c0320706a05841f4102012540e11000014140003008547c0520352040584045442400841c0e44c7c21000400c5d16140c071a2401540d0441d02c1684103240240e2504400c600180d0300103850180d445d104000303580029003900745911b0300204440140304c1c030a10101d02109610701042c0c11300c0a1095003801c0d1500780e65540180140d0100403a0040d6040c1c2c40450820f802c245c4009a00003a840035281280c51302201c203020070302c079034825401009090124401000f000e040300e80798040d040360b00d0b40b0551401c0d0320b5842c1400c460006000300ea007500c0e0b82d0041041501000c0c0708030349684a01400c01d2082c400354503550760310748103104ca041030002c038a110780c807c4002440c42201c0c0303d654002c00060140a100410110141c0020030803000e0140d981500c6011820035802d01c05100440e11448025400500005107404548000c032414503006100304c000594504c20342e80107480003000c5c006040d40387c80c540305014003610 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 274376825 1250 274375575 274375601
    0x601110709020a02150c070c0302061c05180c0603160e0f04140103061a030a1707050316020109060801063906240308190302120f070908060106050715 66
    0xb483c403030a03075004940d04d00741a0012000034140d543d0007440901c1442080b1004040c042110820b000501e001d101800170100402400b542803080180b03003108444056400d580e080741c8414500101041c10860012084015a101030035030811107400300e40c003248009100c050210a012a000c04d40720001c1068603000300910034003a4114801015181c010280401d0707507a14189040310740c00b200c220030f48281181000e00144400c0303c081d11134903914541c840c2d02150b20181040000301042003000600324109600140d0308103202a4400504501203991210040c401c0c0c00c001002074507009141071a00e2004010010f25a104180010340309a12803084c04110b903401c054010f00740071a44e4010440100c8002484407056061a103505010030603200062540300100301441d5241010320f50f56040c2c10460801500b031031040704140c84006c02c00c88100042d070540c88200154180d105a804008002210140030030354180907006000d4411424080c2c2400c00ba0150b50624125962005048400b1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 274378075 1250 274376825 274376827
    0x12130203010923060703060f060309020d06110d0e01110d0e12210606071e0c05060d0b0315042102120a020723030a06090204090210050c01061d060111070902 69
    0x100040d00103290804003818901813041800041500340244540025116440c0491401e0780c54048200c0103400c0c400b008031b0304a484401d1084c009019070007020369030321001d10503545421000746200d084030814002d070480d60303062502d0220b641e14444200c0300c5010100d1000b142c401a43ea8141e450b0050880c507a00788540e0005007000c1800e00c0d900100861100e104c0610b1168881804000e0b2602030000c0140110b01001d00d4400c411148074000111a882941602c0c00c0d9541e920008507260001440d034011691102d210030341900e0240540010000c01d40ca101440d4141a2200c01d13499105130351045080780200a064a041d008111074012060650f175156922540c82070025103e190612426518010022116200e0301c400024031181c0e11006d40281001410364480343c0c003401070310790103980060b9100410310150f1140c41414a9684980d00c0d400d548a440c0424542100d0066101844114201d49603011001c0b00d100340a40150303091800a124040000c006420035000d50301c200c0003e48 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 274379325 1250 274378075 274378103
    0x182d050114030c2a0d0e06042105010603202211120411030705030a11150405090708010e010906061b08040e01030b0406060b040b090d0305040f060c0b060105121302030109 75
    0x1800241c8681c08a4000d0070f50b118207180301c109072000840c0e00b042c47d0303010100b0b000074042c2d9640035220380c440800c2c0e05080c00382c41030790380c0701c1500b180c1041d00103407005112011210700120b0802c0c1c1c45da46920081d250030042c81210380c44080441e0f1900d00101055403030b41c2141e50728000002c103403008400f071005405c51074100b902d00b140c85031801001c0b1a001c0d016848002070742e0310380801c24060356178200740609c04c0180e2000070468512010842e0090000c0c0500002c60161910b40380e95220366030301d03203501d80d20794104410f04001d014168000c3c056a410b204040c0600c5034402c0d000f035004400351149803000b20581c074101c0345502581d00185d800541160001051000a00e2264016802004104441da8880e0b5113410940300300d026030faa1003101085064064180004034001d07090080c60000d083c152110520360341c90550b0f5000b0000514481e514a00b0702c2000103010390402402d0030131603e841184602201514001024800540c00d01e4100c0d9041d51000c0d044000c1581e80031000c80d090380c5d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 274380575 1250 274379325 274379377
    0x100815060c0c03060618010e0403020a060e0d030b0a080307020402090f040908030a0b06040f0303050d0f0c0e0a0f0303080106110a05062502010605030705060a182d050114030c 77
    0x6050742d40303164030078400c140200c4d901d400e14842e4203c3d220140000640d040e82001510008002c02610490440c420658000d000c102e00d03100314025090210090300c0e00c926a00c070300030705480b005c82d8018440c2d031b02d42c14201f15040d0300000300c3d0000e59040c1c81c0540c684500c000081e024494070000c00380c00a041191441c2045032250040d0b1140e80620000c00448010f1414411180114000d10001e43c0c0902800d00110740500090166a1501000403641c280c0504000e82550341c000e0380c15002c25101c1717040c080649401e03d0010058040b44a50007802c5280d510004d0010906100300d105000d80e081d40340c10848020f21203082001d81040031201242801201031000741401024450f00c4200d41c2440001d5138818041d8904891000300200545802e000400030250300c0000c564040c401903811560f40410801e0240005040c4038268101c2d07900c3c624000e240e002c012620944070b814200c0c0b428810b9a8001619460358100001119180c0d135600c40e03208001e00c0340c40799a000302540365006c01c5801c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 274381825 1250 274380575 274380583
    0x42090301022b0207020d0b0402061c05060f010203030c030a09031803200909070902031807080604050105090d020a110604050603240a1d15090f10060e100815060c 71
    0x1240b10031411000c005104501c4004a0045200c02036200301481c8001010411800e503058000f4002012685042e2005604000480c4088010624184c942003000101c1c13800c5448049416028006549945043c10030300c0c0700303848000e001490322981c6580c2c2c0303030615101e8101c070060454221550030744a0780746c0c1091202d4821848091500d1000540540f0140c2001180e035801881000001c0881e00d0034032a400c40a900010f00f0f4101c04100d216030100625070801c10385c00200b01e03002c0500442d0034281041e03403d40302d0040c0401030a0348a102d840c40b107a6400102000c2d442e8100d084000d00c102c012000814522596102d0f40d800700c030110a2064080e80315003011a41000840c1ca906903241c01d0041c0156401c0078422440d414002842d908e44070f400407c622a4004c202c2201c1840b50b0b000c102c00600f000d1020f80d51488618084020030600380354124005c80503100034241120241c0d0010300152401e54400e00340420000c014000c500846451201c2d1410004002e1610341c840782202030701966 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 274383075 1250 274381825 274381867
    0x212070c0e06120624041419020306011e03060306110a020115050d0b0a150305030c071d061009050307080a05011109011b170d06054209030102 63
    0x1820324140081102d514040209010b841102400703005583e55a48409400c207054150024501d0a0700301081201e503140d115204034003c25035842007a40c03c2400481d102020103070f00c1480707850310400502aa6070380140c80f60070b2480d2005920b00100503241000c40c094051130740011300241c10f0011641a82c40c119024240e50700c0150700030000c1415000c001d04543c203141c0700b00e5406c140803040000c045029581c4903035100040100208400a101c1302c205200001c82e032003924242c01c0800c26240c00304050100000a10070110411000da900d04080105404013600c2140306210069036040c01c0f900880041c001401c2c002e0030f44540d181e80360052900c900401d841185c140d4a4201003079003c1c0d16034001c1d02c031504030607901c440000a07017881190700d440c10106d0640301070000b00d04e0003181080350b0000380b260026410000c1070181c900010320010281202c010347c0c1c1014070764040d0700c1248001c0c0440d04190950501c003201d881c03101c0b40442c828456011016059400010f0580b4054607220002c0d507 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 274384325 1250 274383075 274383089
    0x703030c080708070e0d03180305031b0105160e030a0f05030409060e01080a110109080604080d0f020703020a0246060513090c1419020606030c0a150212070c 69
    0x316a903203a0100c441c50000c664a402091410500d9411400c00b40074020007240307c6e080410308504692882e038202d030002e0b442200c05610008804d00c1108511088444100700070000740160305100001018990703d01604c2c004201d0703410705600c05507400700000c19180d03030007081060542c969410302c0c0b612a481800340c0d00c034a03414200c0020b01d5029641c20345040f00d04920160401d12555612a550711340b00d50060f40c100401c1160106074034009004c1c2c82c0c0504d00c07412030a030b52156a04c4024054840d040318002c625481844090f0109401044070900c080e0b0449081103041c15240320481c44844501004130100d61800d06841c0031314000d02e45906c15106501c0424100b96241c0003107816114422129600b980141e10402c00142d050b080230400803136030308210305444c0d95800e101400740c01c00c440f0032038107038a0b0346902c06550350140413254026000340d014004228410b000b0401003800c6115100d4602107598001d40c0c114828030038103005e003110340b1a05690b02005d0408441d16402801140 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 274385575 1250 274384325 274384337
    0xc060510061d0d080a031e05190603050309040e01020c01140402120c030d08070e060304050a0b061c08030c040e07020714060a0c11130c030903080a0905120d0e01020703030c 76
    0x10068a100d01c40600700e0320b5000f0a41020080d041d510f00e071940e00700141260a0540f65501071506942020200718102060000010b16181202400102140004d003200c851440c6c41e034280702244000c42150113080b010365011441003100c1c807880d4028071500d400200c940d440c000c00c4808050702c851800340110300803030b08034000300288110240c80c0c1d20b1070711215034180e0000f000c496000703000391320f92984103d59041030b840e4201803034045441648100c0d0b044506422025140c4c00f00314412090b40c0c1c1000c42075510b5402d40e0b19442100648012520000c1d00450001c80081e5180d061141250080d01101d00340e4800c90034600c1d00030303550301203602034590801c803880030b881014242072040e60b8094516a82e102114101c41e182d00001840c1e0780c0706560064501c09a8a042c40e40501581e121ba9505507070020340c50a0301e050051444001510284c00d460809071104042800003410101320000804004c1d40c038105070017030100030301070b2107008880c650021491400b07050701540301503c2c0c40740e607468007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 274386825 1250 274385575 274385597
    0x70306030c17030a0c060e010504030905100f120e070302040f02092d010e0d02030a03020609010e0a0206040b090d06050a0506010e030a0308010608090703080309030a0318110f010c06051006 83
    0x4010386950440030320075294400e003c1c0070641886680c0d174616403400744100141555846d1609070945100300c40660110318210000c020791304007104810041d46080c94054820502c40d8002022030007540d40000001d034861061300240c5200344030702402190300400402620b00f001e4400d6000c4e411401c645ca22034100101c0e06107a00a00300c0850424401d96000c024034074071410015142e59102d0000c01d9086800c1029200c016201041103416a0340a50010032191803c030200d207080d40d4001041c21020b03040542c2e07003401038403140e050742c080d6200b0040c440e44907603689000c80c0d0b6030700520801800c950b06050a00c4800802e40e80102e025074400c4c1d0b104002c0002060500d41d964488040040c005100100104641d912a4800700e8006100b0700c04d65455595035201c0400039041603038441c2c00c035000021011030032030301485140604000000921188030043e00da90740074841a6100a0183c0c0340c0204072191684145402c0801c42d900420820080c106007107600071120081c0180008141c078102c4c4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 274388075 1250 274386825 274386839
    0x4032102132301020d050f07060b090a0e071d011712070c0e011a2208030d05010e010e010e010303050a0909061401020111090303040303140706060305150a02070803071115070306030c 80
    0x52040001c9a61100761509a0b038040b40c0b021603010300d809440c621350303230104104142d40b04002c150040c1100e0710085004071503000c453b070408a4540c0856500244c002c110040c40014601a904413151207845030100800f0006140c1080303042d180100103242d00264040c1048241e03041041616405120400c00e80e03203030400000d0700ba48111120340c42000500940e40500c8a40c0340d400b6030102c001c8020103900d0760710544146141c00440c64411904d071550014022000d00030380c0140100194000906513502d41121030b01c5900042c00b000d000c1044c0040e006040ca80281301080c0140050b8200300b05442e600d94030a0340742c47d0f080507414010350030215440c90510036041510b581806c000e020b580f078035203956025510f07450465200308040c2001d20a4801048061003020300850240c00909140705404000c100c406800600c50b8040c6032051001c07002140100094a600402d1070421803100e103012101c103482e0072000d42441d840308050108001640d6070540040c422a0f00c03c4a4840700c1540b03540c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 274389325 1250 274388075 274388083
    0x31b0303080703050f04060c0306030203060a09020f030613081e0a0c060c0c051c0207031b030c0e091c0c060504060c0f02010b060a0c080f04150e06030403210213230102 74
    0x90a211740d40c00010205011454507844024201018200062915621782c08a4204401100d2480c501943d0b0800d41d810340c107168801116140084000e010985418502030448034501c1d40e01600c92200401c1d0054150702c42c0d03a500e080c000c09440d10b5038031280d00c450300030004400410119141e600300169030003400d008500c6925521341c000080c0840380c0b0303041c0c0540758101c002d54101c070441c4506030300000440c0911081000b45c90142803440515411800c0002c01e000f020b03445410a028104c04203c0000c0d004200540d82424000f464610801c90f01011a64441480c0000e0401403411092000b0452a80e00c20f40e03042800744c86801c0e0800040c102a4200d44c184c0c5100f580220b0200110100d15225201c101040342c85403c100c0e0501280c44d603281c40c5600290000300c8044402d58024041a4001c0f01401045170100c4810f86985030545c0c00070032003204689034450303400c446030034000c51441507010780358400e1403420400c1c0d000340d40c1e0030744100c1046280000b140e0024414404280b0394030101e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 274390575 1250 274389325 274389331
    0x4120f0201090b0a050903040b0c15070906051207030605040c02010b0405060f010c060b04090804172a0d050c03030d15050301060e13081c02071505090d080a0204031b030308070305 79
    0x4076903083c55a501e40640301a203401440d180c0c060008010104142130024003419030180d41030010025650b1283e101500048080d085c0e40c144136041404001c190f62003000c03640c2008440c10300c408a81c07102c03113094010707008680020b42c0c030030b0a03c4070071b151040d415440030301d07410b1003100e0900c131a40321001409030403c581421140061480c200745d1b4003040d401e80100040c400094000075034000c16484418240e001500f01030142c0600e4020400315020400101d038200c0300aa11124030341d0003005000c00300704d140200c1380340580d80100110050100500c035205120700d001d07091b01c0d910750031000258014000d000300660380c0c800e00c800c0401c1c0340c241442044161980c11b03941c0c00c042c0d10340c0114007041c0220381104440510081001584448201c0c0c8240b1100244038001f5844008610705007100403014210440740524100030440150310000380c1c211078841d1410511b41588840f14114040e2003280c0000e0111103c0c40a81005030407000300789801c99020366240740164031062411030a8940507 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 274391825 1250 274390575 274390583
    0x70f0203100e0a02040b0d0b0f100501030c1704170c030903060c090a170307020a03080307120b0108010603021806070308061c030c02210607110d020102160b0606040e04120f020109 79
    0x4400050510794004010f100b00240700c2d039a11f07074455a90b249914400c480c041c0f6035108000600c00282c640042d9940944407d080501541d08008401080b030340c844a5103c80350f01910780070030184050440d0400300d1108410001d642c4481402c0040e075a40c3c84601c030a80a80f05050011f0040c95200c3c0039100c4a060080414030518070700480c96507003a003e044000d00c0307404200300100040ea60040304600a51294102503240c1ca40040c0c081d010188c41f45007600010305103515001c7d9681d1100880e41034070140e0a0040e118010f00108200c401c1c600030140760081800210002410381009215220350011a80c07059081800200311184d21201c002c01004103594039040c2005144c01131340400f22002c010041141b1841c030742c0e041ca181100030fa0b9000046001244c80407a14a01840803c084c01c9090009503c0c16001c0000410302d060000740142840300313014085101e6607154422100240a0056544900d0a0500f8248801d0150a50440108160300407204c0154018010012a1600 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 274393075 1250 274391825 274391833
    0xe1008010b030610050d14010314030c150c0904090f020f01110307060f2a261306090b040501060e011a0d0e100608100609060e0c0c12070f0203100e 65
    0x1420342400720798a04c240e03100050003011300c540303030300c1071600d201e040c4101e109021508403551450508404036055214242c1c11034008014840400790300086002441c1401e901d034809543e01c01c0d690766064000c10035015840360505001205008455142100c4079000300c4001d0303901e0941c040103650f65102c240e0070748002c0d0401d101d00f001103107450780001c481050724200480e0a40004400000d03203a241d80b040072001c25010036501d08141c0c022000710ba10340030a10040c00024000c0c6c100240d0007001001c001441000031071a00402160380c002c0c00342c25601c46820700d51428140ba159020b00881d005101c1800700c000d00005e401c1c000c41850b4000080890050351500050b2584840078202d011030300210741c45201c1840740401a01c1c0b2907400100901390141850219600c2d03030805892442e8010b411060904000348200049468650340000010b80307031940c0c0c4c17602448403d003410500700c1e4141c0003020114038101480f02c0190b40e130a1551084003605ca41801c08201c527002ca0301c03160b00300f203100d502c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 274394325 1250 274393075 274393081
    0x507180b010f110c18040c06050a0e1903050304080d0807021b0402210c0c0c06091c050f01062c090606061806030c21040b0417090a060e1008010b03 65
    0x70283d8600c0422281810545110340408030100701144042c1c0016003e490000c01000144000550386c1c60250105103002468440f246000501e034060746220540f16241c004420300c0301c0c400d91013403000116408029a0380f10340d91100da0603124242c070071650000c80c40c03500c0060b180510100e61007501000d080d4045401201ca4004d101c025000400d20003106a009041108541c0d5030352041440391640000c40d603600c3c82c0c0550000c1c140003810804500401c024400b21405a641041010102c0103001e51444101c0c000c0c14071924002507026003e80e0382d4642030010070b1100c0c2030440b40c403503180c803044138203410540c0d510002c00c0c1d903904903442002a0040382c01325405141ca140148034003180c4008041c80004943d0000d0116401910124164500001c20064103441004040c0002c4c07034480c4d007059945040d8484072543d440044c802050048403101b140c40c1010f0b03000076110000b41c042d0416200d0b5840e04c0700036144148140c7c1c0c4c144a0004100c1c098103091090340814140e4800001c441e046072 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 274395575 1250 274394325 274394327
    0x5070507330509010e070e090106090509060103030f020a0804060315080d090b0c0705090906010f0f080a02040c12090f150b010c06020d0204030503131e0305030702090405070f030507180b010f 84
    0x3040c0074050200035503d425800d049001704000c100003030050884001d0030390815403805400c444a03540050b440d9030400c801c0041da0013010440314110b0740c0508204607010385552040b800c0002035a801000888003180c003040c29945640b010381d040043c00b6030b42c40b01540342c03280555601180d11004000515a003018091818140c003c5c20f1310b00c0c400030460300c0458031040081c003488000c4611000b40d50040c801041035442250016009226640e8900442418641c415841d2001501c0286c0100d40b10400300b02440d100d000f4820304800000340c1000103100030310309014600c0d204001520481c200194400075100c9500c2400c51400050f1180701408845a07070704000303500800c000130b0400c0d909210010100720700b80024003900f824245820b80f228100140501510307410810b40c2c020140070711007400064000011901440e0b01110071085940d140d15100785000310b541c00c0980001c0009400000700640000e480041d5030441400e07800b081c444c0b00080044550a01c1c10500180500320420195 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 274396825 1250 274395575 274395581
    0x30b060f0315060910030b040c050406091a070602180906121e010e0f0d0f0801030309060e03070312030911030105060a1217030c04050f04060b0405040f09060507050733 74
    0x1c01003c0c06503802c01d0901e070001101c0800020069000c29240d00301d9114520301840784410003007490400c0b500303060508d036004214005900034080c0f45030902103100303c41c611503001e513030382c1079400001595030b840c43c00e12404980070561200b43c060811000031890710300e000140601074035500002000441002007403210103009481040d4070310f568800003a0004042400701c441020200c0c0020400200740c450001c151103040480030081107000001880081d5024906100f2a0030754900941500b06140000c3d00781015640300801c0c0748060481442d45541640081c4a00d500138880200c03120601301c00e150a0790350403101d4552080c403200c03090141da03108815910540d40510450041e80c16506000141507000380c803c0e490060b80400e00b0002417520000758410044162001c0c03008514243e1400524010360280604c1a40c4600031000d40f01d4107544480c1801341c00107130a01050a00e8a40901185d100c510240c2c3d88500d100d020000d41d9036103000845d00480740f108954550044e02642c5001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 274398075 1250 274396825 274396861
    0x80a0615050f0d0f05010302010215040507050d0602091e0a080102090307050913060e15150a090f090807060501051504080a060b01090b0a0206162a020418080901030b060f03 76
    0xb03101c00c02d00110a00e45000d20403107602c0e04000780e000525504600019103442c2d2160034088901845008010000300042019402c9a0301500d0003244001ca0b441c00c0c101034020010100e4015001c40a41481000e95080030708031280300b5580308460944541c411420b034418050b4598269101410400550a125401e00e50041f00e030990150401c20342c0d5241c50a40d490440c0e8444560700101d85107106607203540650390012241c07905802404800b4000c900f03030222074861382d050942d441141030030301c0180b41c0112005076444264a6510401440c10000500d0203021300c034088c80c2e00d0105178049119610032030307040c0c4110070000c0410103405d9807100f0141030b00280c3e140c100105070340e000689152500c040c4c200d1071481c0c0c004d40230a140070002c103010b0003c40050101040030703490711643c3d0031034010f4440c8000e003d10038101210001a00119001e03049010181d420301c201c00f440c03c0b0a1001010242203440e0b402d0703800740b003d41b511400300702240c01180404200c3c0c0320208049241c041120414040d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 274399325 1250 274398075 274398097
    0x7030f110109180218102304080f0601090f0207021320030412020d2307140607051b15010e060d0b0c18100f050a050403170a080a061505 60
    0x21010740f58070086074400304404401e0380e078640114101c2c10b800c000400300321070b1070010340300b00103943c034201c900900003400e00c60f1902c520704840004800e415034503030844002d4101e603001c80341b0754445540d0306550b82c0300910409003443e1404010020100d494000c50740c070720b60018002103452103000d100800604a4030262070b0014050128030506980b0000a07501c69406820241046500304030080d00740702c1c140c03518008111004245054042e0f4240b026452519521505034884d1894503103998002212107000c80c0c0d910442040180c2540c0c4200100307030420205640304107030210003a01c9551007140768203e00a01e00044010f001306002202d6003540131b0401003041c0300e000300ca5101d002d8200d40c01d80312410740c040002003c1070980c40202000c100500700790384440030521103210040c2140004401641040f0002807000f0503940714005032005550800d404a11000311146540305c1d0394490070078a0040b8400100081c259520391050004603200401c0e006110000301c0001c03160381d0300444c0504 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 274400575 1250 274399325 274399337
    0x70e0108070207120b19060303120b0409020d0b070906050f030a0e15010308091014030a02091212120601030203130201030e010f020f040611060408040905070c1a06011107030f1101 79
    0x11200380b0b242c440d413034881c007450b00032001c0d00b403000c1e83d00025036110241909142c2004020000a6030026440883d05c649440018910081c90001400341403086000307076000720701101a50500030100c00860007095a5100d440c0410b0740c0384425115030040e6216928591024400240c2400203a00159040802041a1513a031000411f05400e8020207030415074010034042440500e605152070901100c50882c00d000c0c102086181c600320309844002e01040e010354003c03654480c5a190030914284840945054850000e03040071411021740000c4000801c00c2a0800420480d500a10840e8050814a08528035000780707a001503018190308110031403a590794402d20000c450952010780320351440b0b055803d940710f1038180f0040c8195850340403001075801a02c1444001841501100d04460300300e0b801060701d996284080d248614051405403644052143c80e04506040b18401441880e090300d41100007071221305902da580e85103010061410398540e864801141c030794130b900c05032140c0c140740103 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 274401825 1250 274400575 274400579
    0xd0f0b0c07050f10290d0807050a03080402040c0c11040908042117091e060d020c03190801050303071104110406050d14100501050319020309150c03070e0108070207 72
    0x1e0340c50f00400440c07803105500f0003041400a151076010355500b00c01ea0b04d41803019000f910b0226003031044407140061088580c815410304000380801500c182c1c03038002c416110703802d610b414007074480501103404034070852401c16001c1c0e600e80034156050219411529120ba04100301c000d0100912800d42d0950f19070005010014480250508207201800c0301510f084200e00d280c5003016044c64290102c0503114000d008102e550303110360000c0a218403680440d088190f034a00041362140c071405003510790690000441c04001d010001c02440d9103064151000040d034641d407001c4509110030b001e800c0c1c2c103810401441d8041007044000e51403403040140001803044050409820550260380804045100824039140b2025580303d400710008402089107294603120151810300d80903802020705100010000c10b10500d600003034002900d506000465690a0601840d599005030b600c0c2444450300c8c840014203c00f8010003030360302076003140c0c80f842c04c120700751801992603401c010503030011031158140c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 274403075 1250 274401825 274401833
    0xb04060c020a050d0e0102060901050c0307050a0e0405040804142b2103091406060604030204020d14010b0d0e010207150b01051201030602030a0c0e010e04020f1606060608060d0f0b0c07 81
    0x1140020306503501c07045d020580031000a400c10000400d008003a9240004201040c1c4043e01143d40c0417807185013190b61025080c0003522080010240c01d030f0060f00e00810042008041c02c014802d55065903068000c0110b07081c1000209500c1c0700502c41108150001606618403a4036062070380c0c2d104a40e59480400180242605600c0000040f80003a8641100000740641100b0542414021101a2400e440d06102050301c0c0c0c819480001d01442e0b00007003101602071554044030304a4408864003000e96034440c102d8000da0445078041c8001854074182c0400300070705100301c894440c1d0086021750201c20290004000f00140004541405002c000303540404075052001170185114000058880c20000c503480105d4034a2004981408041175502c480c03a03810460664403100111009a5143d0911404510310700403c1c001207580c00304010f91a013000707920340062095545540c1d40c40c4060303031140b08001d80800c0c030308005000f4030248e80e206004100f955903082e0340414031800042c038080346a55 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 274404325 1250 274403075 274403083
    0x102070915030803040b0f01080601080a080310090c0c0203010b0402040513021b030307030504050705060405181b2107050708070b04080f07240204060219061b1206050a030b04060c020a05 82
    0x170301240d034185040d04221046001c1c220007405001940d008000a40c18801031036070760001c80c580907083c504040001400303011210240e102501c2004800c1c820114803e1000d442c58154090481c400c6d400d0003130744111070400c4e100360303800c6520003030003003e03170b000d08000400081d440703007404010014038050f2840c0000000c000460003800d03156400500d514103418424103003e50380d003146100d07000c200000c102039501c035541a01c40b20361a01d09030b00c40b43c0f182c3c5500412a058109004224103001c109144001c2034814030303440c04034a604591083e6641c0c104111107900c40d00100410716070080c404400442c1403003013000ea1251091f500c0b41d2804005c0c108440c403d0f08005422603400c02c9200201081080d050191103404181500c01e60600b41400d201948a4405401404a0211030080a01404000e81050411303a10300f510003616500b400400900c9103124850303d008032414a440014103007454807800045a420564172600341d1036a80d030380009043c01a2540c811449914010004194240 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 274405575 1250 274404325 274404331
    0x312010b13060c021522080d1e030615020703060b03160303050c0309131a010c02030303060d0f0602030108030901140a0e01210e03041d090c06090109080118020414060102070915030803 81
    0x10320020b403d2079418086c420403082a401c0f4504a4211040840200750001d13007040280d2112030b40040c149440d0342080740200000d50017008002c0e10b210340c0c91340d101c0c0c000c030300071055a004040922546028800740356580c071a02461401850355460300f007001c13910039005004110807020940c1c0c40d200044002034400303560078090480496550451899480e9012340e541403250382800c00d2400006103800080d113038000245610f0291202003404410482022041c5150550000c821522543c641c0912542e90b005407102c1c50100311107560310701d0905000010758010031001c0c1c1d10410004800b000458036813403901da010556802480010002c14010300809400c290315400440e100d40c6002c107050b080c4070039205400c1c0481107004c20310800c8100403440e0b5461920aa4002c6e0361030204000407206149103501050055103440c854810001001415064460085809000c8500700700340b0140c1ca0101070764030a0251b40a1030007006802002d401c104540f803080000800310720341d2912100140c2c0e00803 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 274406825 1250 274405575 274405597
    0xc0303010801060906061b02090c09060c0105090118051f0e01020705150705091309020f0915100815010f09150509120606180603030d0603050312010b13060c0215 71
    0x20882485140e213948550001005903282517400175400c1401101c241041c0d050103800754803000d0024546205540898441e0307640501520707131310810040850300820083d1400d0744036500300000159612480d03070039007005980007000303084101802c54050450410070302c0d880041c1500c80d59841480403003032002e00f801500400c05045000010003026602450007080075060040501061800e601c40d00750008140307499600000c5c8039811400001d1244031050b400d640d11014103000c1107030319407003100d09101d8401705071200500448a044244c50084044840e4010045d03128514001c40d0b105a222a00e9008079042c040da402c0d0b25904045449e21300382c180c40000c11000203505213a42813041d11907140c5904400604003e09203d800108007a000d20b0b04400420824404143c5c1580c050003201ca10781c200c0c04080240540d24030b0180d81700c0e0170821811281c00082e0b000002c80c401420115442141021403000307600c1e04280042d80c2e160368040083e030300110b5000d00c8a07103500604004000c0c3c1400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 274408075 1250 274406825 274406831
    0x403030302130603060815040f0206071401050c0a080601081f0602151f1208041d060f040606020c060c03071a0103051c02100504020f090f07030f05010302030703170c0303010801 78
    0x2c2e00c0c041d010003945501c80d00406180640800c41d0070800300301c1c019060409407540b40709031107a0506600c036810300c440280d440100000e51408000d00140040910035003040240042c0e0340300d004c00c1c00303c2e00400e26080d0100f90100e0004074250300c14088140e10024030240c040a28500d49406191035070310740c100030b01680c021142c580a12202080c00c660041c0c235030700c1c0d03112501c1d100207526424415500c5403aa20804094050f0700300003600c001c0e24040c10345254003440c000c40b00381030781007540c0d03082d190a401801003054070410342c1040e01403407081d61142d800500048601c20241300095110261829141c002070111000060518005032015020011040300550560610f03504000c0900083e4015280c00702c0f41c61003d0360081101c4c1b000e0342e0114000201036a42d030021035454002c0d10045c550114160040003450700140c4041ca00039203103641d01300724401660088104139078080c00042c1d416032081c0010400107140c99005503030350171418600340c2080b18010003a442c5800a811000b45651 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 274409325 1250 274408075 274408087
    0x702011e11151021120507051902040605040515061c02070c060f26130506100306240b180d0b16050a051c0e070308030108061506190903080403030302 66
    0x5030945181001d030120115074401800d81d00b104614a4413004001015030103084071500040b80540241e0b50000c1e0800151030300002c0d565102110150b007050224880c80c0b4116000c01c09007054400c0a12a10741240806542e040c400c0804c500b80e00b028251000f90381005414002400150000c1c0000d01d105409081c030b220308081c00039142904046c801c0e010000356034202018070070340044030380c000410341c0304903005a00d40122030201100d8440700580581710f03041c00d1022020b914a924000c4034080d15041102020041c1c0c83d0301240c1c95100240295207804100f030103103040d8400209880501c110a0140d140b01c254040f440350000ba5500360341b40c0e200e01e070030041d0081e6030b1800394001280c5454010705d0499000320240050155100c201130168030745400c002020042c0d44004040780c07070030040b900119524500056a5842405250024092070001c64400004a40c0c200e44c5030000a181c035080070f410f00c1520b880485449040d20820030754120000104e54964024009940a82d4000d0303a248 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 274410575 1250 274409325 274409341
    0x5070609150603080426060a15050621060102010605010e090604020d0e0f010c0c0f03050304022107030c090b090106050c0102070209040f02010201051b040909051002040906030b0106050702011e1115 87
    0x8014110702803c482d1b8001001000707160115250380d00107075000780002c48407a601125091003d070781d0400b94100500145454039100708070740a0418031a4200980c6031a5030701710049090b1030300c0b48078050104000000d558698a02007800381e0740180301a000605000c4048a2076094405540c0790360203680008588400e101c00030302508245902c030342051103541c840783d038840742095607080d0003400704200031000c5001c55030340182010842040d8441c0804003003c80d40c180f40c03201c240d403100b140c14505a020010701d034583c41c003d801c10900c0042480101380e10b02002621aa0f01540344204503560070044000145d0303400300c2040c003c0d0b0013210213049140d0309100180c21904050f101181c0c1d00e0f0f803000c00741c146240c80001c46043c2d6007018000301e207403c06440d00c00d1900554a0790010014000302c5e021a0004245d4084400c50b8090080c00d000707640e80b0541913a162290b1803002e030000e80c41100031125800d001003a003130003000d285002e680280103003c0d03079400c00900d120100c2d03c16043c001808480 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 274411825 1250 274410575 274410599
    0x110a1b0614030403110a050706080105101805040b060d060e01050406230f0f041a040c05030907140f190512010b0303030610020c090c07031b03050706091506030804 72
    0x505000c0c00c10305034050241107000c1450200500040030000d0039a2215003562042c0007920350954031404031161180c480720080c002c48000d0040703500403e18621600300c0d480c403540a502804c0f0801c05088040c600f44020b00c409001c00000d0b0582103401003240400f407c813280b140c08000c01d06036011030340f103504020401043d182d0603440380802c0000c1882a42040f1800d08000c452804122411220440000042491300100742c0460303a1040c903140c0b06030000c1002168019804004460030001070326590029142404192142b5400381c2c00300300301f0301c01d0341c0103120000c14101d801080349642074981c8001542c08080b10800c412410f08500003080541050040d5482c002c650780d009110402c1ca001c00b0075683d0000500726445024000ea0090b0001d0081c0104180150090100d0300d03a0300d400c0018403a954408002100040c2e43d44483c800c80322090306811100d41d6041d40e41e1460701599403291070251110034015154102c0e0190b176015048038522641c0002c5200c2d03990360b900e136450318600e2805 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 274413075 1250 274411825 274411829
    0xa05130507091a0901030f06090618050f01030f03050307170109021b0304050d03030f0b0307030b04050c01030c05030105060309070e011811040501200106150e030c150d020a110a1b 79
    0x2e055203884000c0c00c10803032030180c8200680a00e000a0415054200f52022380302d25440b50300c0d95817810a02007070303c0289010030042503e8101c0e090045481c5da0ba50107029401c00d1201800003484007940100280c400c0300150b030402850310301000d1007000340e9940700f42c0714002ea1021100c203500180380b04446c090110510414000c0c1005941003500d40004110000d641d00ba00504242e5111900c0d00b402c810717640489448071010301142d28654a0345011900400251016242d5120316542c1d0b003559071082c00343d2406140135a441506507441c1c50180015508080d00b00880c5002d200f4011078502c81c83c0d003a10b8000c220541004400744112603404044a68007a500407814000f04428001a6003010388030540f07100000002e0080c08441201d140103049503081001c6046070908500103940c2e00034405174000d0320031002d07601d40c03ca80e00d00b041a10556916a0009503400707100850100722503601030300d06480c0d50b04084841106402c1e400d0f003884181d000490b14108000320f1040d8030840d003000440 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 274414325 1250 274413075 274413089
    0x705360702010b041d211b0106030c09140a09030c020402090402090405090706140306030c120304030605040c03020907021c110a050304260d020a0f11120604051b06030f060a0513050709 81
    0x4400322001d03554000340300e440380d0307d5520760b00100002c0311080e00b54000801190014401052592907005d4880501f0000c0b030000454040d01010800c2c2d80031900c91840103540c16241c800c4102090343c2880040e402607089158000c0c0c1c240180340740c0c0d4440c1d0217003502c156000009000040d05180f0302030031780351201800f4620b00d2028401c00c4a5901c0014075403440c2601280c0342c0441c440413030b19191a620550300001e04140c240401d01c0104548000800e0981e40308650415a541d92000203c2e42c0c1c126481110703500808a05072424854081c141d44402d01d522100dd0703940c40b100e82d4551602e1940035a00c290603c00029404407440d1140003d5068800382100181000000f0503400039950196034038068000c44010980c481000180221301043c10b0024100a841d1408441d0f0320740c03519000c035801c0c0c41e50b0160b95450240c429140c00c2c22806200e00505060440d15055585030154000030481500001d6080011400b56034104c900c60741420103d8000c20700e807030702c079400070010407a50740011 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 274415575 1250 274414325 274414363
    0x30d0201090f0813080304060216060f0206150a09020711030c0a0602030a050309150c0d0f05070903080c07120506040c08060708010b090f040204080705360702010b041d 74
    0x101c000303800e02e0442050707540c10100b0305482e44100300f04a5844500c6a00000444c8400600011074a4001c52a00b8030b540c89101c088074400c0da9071000f0b8540a041005c03d00c0142c00080000d88942902c0d81c0240752200c006e0405140c91b520791031020100c1e404040706464050f40003442d2052450108103045101c041990440a0546000800303903880c050080c1c650144140400010a454000c00c1400c844040d0340d1400c202d10b00b40110a008940c0c08400b04400d0035040540e034200041c443c0c050640500322603511405038600d540c54420580e0854406a081d0340a650b0000469004c41001d64042c5801a030140466080034544401d0780d04455005c1281c5410030020498141e42104513681183c040100309541c0e0702d0b2007800202c100c3c03160040309900c94404140400e040038001600d409462080d11444c03c481c6507800c080c1040007581407003090040501d103481d5580109121003d800c010580000b05584071280c00080030341d08001e4218088403907404002d01d01d001c003040000c1d804800c40b10b01c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 274416825 1250 274415575 274415591
    0x1150911031306020c0a0311010e120409020c010b091015090e0c030717090318030610050d0f06021909050108131b050d05070603200d0f02070b15030d0201 68
    0xe03059800010b000522031218081c40d041403100c00d4040781c44140740101902c0b004031107883d02401c103425241c01d00780c0c0f80d07180c107038000002c0e0b0740052224140e80311144201d051524117402c500c080d52019040c0c0c4115500c80c200d4101c141c40d83e525040c003403841103d4443c0c0f00c41c206101b540d08804054102400c00480a10400102011880d5940c1046500000300c0d0b495540c00d00a07500c05603001c010a11410090082206000e0080b0140410b11510881e00000005a00c1019690081911102c0b19036903011004c0001d4980020010f00c110302c00d06101c032100a040d11034200b01d03000041c481580701c002240210b405584034540d50003904003401c10540901300001000000ca0121500404040e41c0d1030b05a10a540790f800b1520040100070701d64100480741d0f190080e02c1d0032280c4284008203050086290f04001c41c01d02c0d16820207841002c45040c0001c0c10708100203000d940741d05140701c0d5030030813501005c039004a003014480d1000301c41c81605032500c0d806140ca000780a0354481d0442e4900305103 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 274418075 1250 274416825 274416851
    0x20c0a030b0106080c090d0b042906120114040c03060c08071b06020d0f0906050105090702030d0c091d0f060609150d1b09030c08121c060512011509 65
    0x25054450614001050345d5801035464070610502214a50049080e00b5600400c003003488007912961041c804100720040b840701510110042d0080d10050743d560300006410750030542c40a0034100031074000402c2c40c0214540b0540c40181c2586d060f14800121035090052000b0b5010300c401641007450040107525019500030900c0d6603620983e4413078904039030705d84c0601c60ba81d01980d51285408008202e040c0081140000a0084160445005060130b000003000e140c80003481d8400c0450703401030362034032242542540042a030701c0034500502c076000d00c000c1030030001008410004034590300b602e02c4e6818003401044c56000d00404803031060508000b500556101c00a00c030801c401030040594035020031407421009040200c140705245044074440582c040d5020226a0440340244045848aa00e51404070f886110002034103541007001c0000700e00b0040c9601c0c0e00403400010150004117103071280d00042002c203404000ca100c503910f03840c40c4440152100440c00003031811000030050b0400302c100d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 274419325 1250 274418075 274418093
    0x150e0d03051021020d020a0b120612030f2206110f0708100903050906030c120a0203090604110d0b07020d0909150311010c061107140d0e09100e1501020c0a03 69
    0x2852080030503c050201d045444000e07080c0341040c1c1c000c0410a1144d114004407400d45c10000580b412149882e02007003681c1402030102d0322445d0075034043c5261050b54801c030003940c0d11000002d803501138001210614039030304482d150301400c3ca954400c01d050a44116580c0380060340c0707c00b450160840d400c02c0001d552b0015070a58442c1e410100440c0000380f03410166241e0190701a140d070812000010480340c00001001080304c0942068100950b84407030004204038003049825800d00d1380000045008103400900000001e80020302c02e1340400030b00d684100c841c0c6029a08617000d6800a0034000c0c900d50003410980181060036410404008030410b1021380d80c4003440046c00c0e04492010000b11b50344280c0205031540c0d0046010b09c035069003c006e80d58581c5c0700e00303000d0700c840091450030101d150010035a03a42100c455074401844000400808c20100805000103042198440c800640d140925010038031806903421042100d8450100283c1400c10028407a40719001c0074106000141e0b11003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 274420575 1250 274419325 274419359
    0xc0909050a060509011409070f0804020405040c03021306060905100c1103160e01030303110c0d0f1b1b12030f11010204090603120e0405010f0b07150e0d030510 70
    0x40000c1a80c0d229400528010502508519040b80d1448008107411035641e028075106a03082c0ca05030708940d01c500041342c051a1900d1340a001560100111b0054030709508850307040f9010b2200403244a540e5800602040e00509403030010036100c030003c00440340c10046890003003405840e00e0b1000916010001c08003261100000c2a16100403d10398041d1030410620100300052035001185507260000e50503440000d1004600090400c0c400710185d4844030256244001604010410746940060945000e40c0340c48560040008030000c1130b01c4035044e83c4244504900440c2500c0101400003e1014a00480d03003020094040824540000a5015020449034101c1e0f2500c40601000d0721042d90291085c0c1d440005101d04004000c000c2c0103480f149005005000c0d12151312518a010902095410034460400e082c17168540400c1a004003034020100d4034483d841d202004000f0101d0700d0300f1680c00320300d040c03090744c440800039603030755014800c05070405400d085070304c0d170740346800c08102c0350700380c42 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 274421825 1250 274420575 274420589
    0xa05040605130f060f0323030403080a08090a1e03030b0d03050910050403051501051c05100b0d0803010f030b070905030a0f05101a10030204080a0201050705031b0109060e010c09 78
    0xd89240420f0a401e5000d1000380a0011504919a0b80c90a0481301065a00d01032050440c0003450383c03403420400800c0341c0c12242c1c0304c00c3c103e0800c1401c410039200320304000c10480703050007070400c0c50f0300003142141104039116405400604d80c4501c0d080081c11612141e461900a0078402a40307008250044241e03440c40d401266800b03d50302c003d10f4222440c0c00750b940028000e128030065011030b409a800054140c400030340d90602c00d51503413000c0c010341d0142c0034009050341d08100c461030b24503d550707001100581c601a040e0b2016003425954412a40e10903400325006501514051040000d040180d582048242c0b900076451401c0100082d1034154290b00242003022002c0c1c46020084c0030f009601c00c80060704030030801c01c0000d1040440500c20600464406d001c0c1e40d1255103558082d00c252002d07114440004c11407980b20b94010344031540b255134203840038482400740c21201481800810320001c5035100201c0c0002e04c2c0e14000c0b065a83e59001c04400341d04241a42010311341c4086810300f20340340 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 274423075 1250 274421825 274421831
    0x908010c171b28080618010b0f0412080a0206011710051306050403031d120301120206070b040c050a12080316050408010e0c10030b010507030507020406050904110a0504060513 77
    0xc442d0310b00c0c03003807182c0107000301090100e201c0300c0b0000000c4441c140030044251145216983c0e80402c12001c043c802c041220091440001800071445e420064901260846d0300c0030318058540548605106104038122400b401c0010302d003c0c13542e8140003031801405401840a056005052301c140c64003422100c4800550380d48000034030010740203482c3c0003c61f0300300404005a040c80c1c10300401504400d84422580c90101403015012640018405007103100741313504500310b900b00000c1c1143d540e4001c0d000d991002d41803040784042000510344502462007005a140400c1c41c050510904c0c034100e5001c5400c03141034410f0030001c10005405c81c0d60144106840b03011400484006983c18011500111140e61070b049a00103e104001020042280c046909455154280c031084050352903400c1d41c24005902403004900090041d17020704080e910080c40402c04a880d40007284421304211000e5402e4110022003c2035402d15440f048046c110036207003071020310300b42008034000708594058602c400b07076 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 274424325 1250 274423075 274423111
    0x70506041505041707230a0605060102030c0d0c0804080d120b03030a050702090a0623010e0a0f060807090e070509281403120a050a02060a090b01090e0c100908010c17 73
    0x1101b40d11000340c06120182940000032088202541c0300c40741c4204039a2603240001040d010341c0000182c0c1c85541c01c000c010255400c40c1407007181d9880c2c000d076040f41c24420502c800320f190300f01400a0390001849c1e0352610240410703c40e00c00c0554000c0c54000c0e002c1d402c10009030710107a034031004407030340c4940544090ac1162580c403081c0001b031001d54801040300e541e40c034040e07441d4010800c600500c40d1090303880f840d14418840c10841303030390b01034442c81c1c200300c41c907402c10800e05014010695002405041038451940c2d81d10508409444c2102c001000030000582c42c5990700d031841c00f8040d02c150399842002142007854090f01807458dd030107401c1c40d03120b000c041141d01e0f03034041040d81e2440c204c0100c0103494046e5500054540c0d00b24024100140c0202e00000302c030140d140c0708090040d5000586099540d2030240c600300104100c062610072405882d40c0e664042c1c0b0f4501d040240365a8541e0303030034801413400c2407842c03c51b0303092110403040000140980114500800c42160000d20314440f14400c2c00e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 274425575 1250 274424325 274424333
    0x702060403110a0f1104060e100509130c060309030f020105150103020d02130f03210c110406051f080c0a0503271911040b0d14070506070506041505041707 68
    0x46003090f0001c101c103000c5070a480400031030400220310b4001c1034400340030700390703c9502400c030354182103849880d41c0c0c4104004002518100440c0340d0441d141c04440031101d030030340d200d92200080a80008010940b07070894034040591044840e031401c3d60a2000304041d003003100c4800010f01c9030300b110324105a00400c0f14807500e403041c2e04444038025810702000100d9034982312103540d07042030312096820000740322030380800740038540b5003401200240e0b076100141c0c40d680d510350144c0d210103c2e02070340044d80e5034000300d91038580b24076201c4c5002d26401c9440c10001d8950004000003001096412140030034004001c42641040076242c00c035525001e44210f06401149100c2c030b090203108d03400414495001003e160b2803000b4041c8444c2405001d003a68598900c01c1408259000d45070042d400000040468010445103410300c0543d1700c03480d003610180e96175240000d0035500b08400c1134a403074015a090104002c01c158120700340c090703250414411403419843d0051410544c0041a205001c0014042c00300 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 274426825 1250 274425575 274425583
    0x804140402030606160c08100e060a0c090603050c04150e100207150c0f0b0f0109110a0906030506040e0d0f020c0d02010504050918120c1b150702030a080a0323070206040311 76
    0x180901f40c0c00c45452a0f4a042e20501806a00d120f1864501a6001150a89a085c02103800f148400e0310381b210000c1c0f6000c400c6004080042060040910511010620041000c005d49080c502e95a9010100d0014002c010340700c1e0705030505d54213540c0804001c114002c41c1c04c207800e2a03042e460a002c1d20704280b50601d202c80d101c414400900c04200e4a041000740551904254141d502541c41044140f90350110003083d88907000307095007c190f841c0c80c02c0008911a4011590003600680042100d1080240403854240b182101e1030210748030000c0181e1041c2e0402c0241b0394203008440e03904e51750205800107011032003217008a40c09898003074001400040742e155004030380345102040310022942c4d141121141c0e00858507031500c500940c030b0262081c6002003420b24415200819131041001c1c1c1308800c01d420b50026504a0b0140200c0403528007041003907020b440014010303140880c036290f64030fa020f1804c820302c0684040b10346501c42446911a400102907a02a9050410818940c6021301003490 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 274428075 1250 274426825 274426829
    0x302030d0c0203190f03090801021e160203011a1302030105060301090203250c0201110d02060c0a0905060409050105030105060a08100c0e100906030b010f140f0708070804140402030606160c 83
    0xa400d004c060f400c01c66030005070915140682e5414074515140c4440300e0a030700c605507450700740c540c1c010280000300400d5401840da222140500320951290b41d0701190071344844544401c0403105603850b800450421011440e16510120011869981060005683c5001c10300807441c6039a4044009403041c01d8860303620410300360820780100f401d07140d04402000e5106c1071400700d00184100c0c001460544001881e150a601740e6000703029565941680260f041d000350701c81c501049000c0c7e800284070346074500104041c0101c05d10101f0f0b5503040c0402d0500303603800a41614040c00c103000003082401800724080c10754251004020540c1c1c0c840310005c4422070508085507a111040707060b40c0f0385440d0400b500a0840781c55803828030507000440015250001105030040206e40012540074040581100a040390520180400d040c8001a05c0ea0052a000440100e030740c048001030620095069140702e660b480000c442c190f00d103141440c0480d10900410301c0109034200c05000c0e10081000148110340 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 274429325 1250 274428075 274428103
    0x6030f26030103050304080d0309020f0108071814030c030a03020a06090f0b0f09160b0f030a06151715010e04020d0608010515120c01020303181c08010312090302030d0c0203 76
    0x81c49585034180316440c3d034420b114124192080b0860390009900a0003800d00343e9400801e4242c5001e048001503401d07400086c4001c01f000682e5203510b081c000843c00c03690107040315a41e402c50043ea000141450040b680d40a98070076440f00d4012070000707070f0002d41e090140368003007404181c80c0c0c81d91615040c001503100c0020041180c5804011096140101c032500c103031801002c40b001d00c42101c0396807503c1c1d034890048943e228010071841080011002c01140c000512582c0003842c243d0b00c0c10941c0c0b40d4000c044d58100082d6409410140b00c0f805207201541210f0100c08941604540d280060107800304140380502490300072540d002d0049050f4084002080008024410b6141c034481007281d0301d441c035000d1341c4640400b0703031074200e00c80000440307002045068004500d5901d81c41d94004001e0400907a50341c280c4612658002202c42c000050030500000e0389032244107506501c0e203440c841200720840010010300b00000c00150381c0c00a40d0303c0314444c2c1803c0035a0703034205a0001c0390034050140240e02c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 274430575 1250 274429325 274429327
    0x3151017040609031704020603180c04150501020706030e0715021603151406090a090507030819110a0510021c0e150f040309051507021008010f050406030f26 69
    0xc0140079068100340d000c58420b603504d41e08825002c103e40c0004200386d40113900b0400030320001e240ea80d03102500a050750800c4003100c203d10746070b00c0050240c030901c00062480d00f405020801c52941c040180700c0152000341814000032074840308890f0303503440d02d00c18070302c949000d0313805804000e0080c401d50746000d000051110013591681404854040694561b041e4a4548641c415042e0101403145000d0480103020300b800d91284040a400b404da052000d0310140074a0f080040007900a070300502643c00340c02c1c0c140e4108540540040c1c400282140001440d40044000d80f0009c0c0c004214814802001c0c42c0058071500d469000c0c02c1520301c42d01c44002c05c50300d814044581d10314002240d0708243c90b4100f07070442555603000011124641a1001004140d2012040c00380745080b449a002000040f85554140700c1c0307a400140312181e07094000e00c04503000c40d00502c804014a464a03029140641d01805080c4c91981c50010082c607083c00039140340307400000003500503c4406101194641c400c0b01c6 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 274431825 1250 274430575 274430581
    0x90a090509061f080a021504080d120b042307020c03010222050105090a0306021e0a0806040507110a0303021b01091202100b100c1506060f080c03151017 67
    0x1055440100b5180c02407a90981001d0f8580415076003168421360301c400010385280c41040d0b00307000044a40303903901c405032981408082075a1008100042c005030f866540c2c4000000c0c0300790348004032181024610301890400c40003240c001005503141441c00c1c45c0c0390090116580d00d4034101d0800d904085619415400043c015075481000c90003c9014031200c0c42e5001c0755561303072005480d00e2046035030320354100014000030808a4a10780c06058441048801010441040d01d02480150300c40c0d0f000d0b1002c100044140011400d10b8810180e102200b8107090200d000110009661411080001010181c0005910b5031031100410b0031802c0710803820007488031011a252000201e000460090010301c034000601500880d0381c061600410b8024007408500e090240003102d004030b6481c025102d12012401004649610744a2040200140d17600e12519011130000200081409410707500c10000138400d10408200c125000c51141d03508030344000c60399400c01c8054135810006520180c82410300020 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 274433075 1250 274431825 274431841
    0x209040201171305010609140402150405100503180703031d01090803160506130c0510030b090a06060e041b210204061d060a020d030209040204030f08180321090a0905 73
    0x20390f00003d20038802401042c0d191101c04048a80b4002d030300c0443e03d06500803030b0150922a0b00440308c0b010003c2c5003403400c1d03101c10210302c900800000a0000540000c1003040c25624003412840001c0f1000c0944601d500cfc41d2401000020400c40a5501c070402c2c00341341c42168000c40740d903c01001d4401c26640c9904035100b4082180d94000000e850f940900d000041c414120040d4111480e5400b52200c58080c0c100401c2c4855010300c1c25450341416a1540d405000780c3e101030f5058451840e840d00801d07068245a002090260340ca60002e015900742200304011089040c14104135807110300d007030746041424402c9240e50b0001100c0041703d04d0f00c001000306819611070717240080010362603080300b24803081c8414080b5030700c152140380740140c210744c0400f26058070036001071540720030050000d410079841c0d440f21100641400b400700c841110000d603403280700c209020201d400903000c4025181c6950001c4c00c0c1040100000031247e5415030001e0707070503042c4d41d91000c0880681040f02d0100402e00d42868 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 274434325 1250 274433075 274433101
    0x21605010c1b051911090901150503031e03040602071a010515072a091e0c03060b25150518031c11300901060f03020904020117 56
    0x600354002445184440c524050b041c07541901c240d41c04402001005001c000003071003e400410102c5c1c500701c003002502660340c2c0300c042503800f4000d26000040c52402080b0b80c100010f0044d40014007a070010b02078050104140c162031491840c80d440030039a2941c641c40c0420084c8102403000b01119210804400354103a40b5040e00d040e1182a10030800d5401610140f05c50340c024403000801442c203e084110844800040c007003802820004241e01c015100c92100d025110383c10300d404407008030243c40c405d120003180030709030484940b03050400c2880d0412060602d40d200b05011940301c9060f01920014a01071400100449034201000c20480d0301003504520103804142d4444406070988400b04008480100c11140020f80042c80ca07003403a404240d1800140c43d1840204032008410b00003038484400e0552045a0200380031402c40c203500c02082100c4043c040601203d40e281c2c5440014400b216204451b402540c0e01110aa0103a41e40c13880104c1b50103800d0024400c00c3c08213a414400f8120300340c0c0d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 274435575 1250 274434325 274434341
    0xd0209030709054204020a02010b0a090c03050112021f0207120b092e09020f0406080c03061005012102130303030c020d08060a0524121801050613050a02160501 70
    0xc0014045142d450011140e4070405010b215500c1315400d050140515190740104507079020381c00046100002400010740302030480e40000780040d01c540720703510119403520415014001070250784140401c5a004204d66030804075002d0400e010f00c80b00a107619000700200d070700400d0300003142a03500c05145044804003400f91003c04903449503199044886c030022103542c02503002c000720070005903034a00340c15014119205090380c006104d00d5a141d410340b41ca01030304003d020148002e0600750802002e140c5040d42c000c080401840700180144101da81c07001105075a16000e00640248458240a85d002440741c9c041400c0c90719070f2560000704040e0103411110310b600c8a90250380301e04d141c2e540d0a448182088881076401034000304207110303d117000a17820341c1c88004075070102903000008042100707541c0441c0300d440761003002c0381c2040792030380462040c0b0310300c1e5100100a0000d8240307c0046202d0040e010380c0308800d41c0d11040061038904c900e40c185c4452034014200c0901c030710a64100503008003108 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 274436825 1250 274435575 274435621
    0x1203020c1206150f0f04020c0604020a0b04060906030b0103020910021c17010e09120a03150f03151d01091520030f040302070302041109031608030d020903070905 71
    0xc0500c0c00301075030340401c100d4810140342020101c0c03034040c0d4040001150074086026481355802440040d1600c940c07016001412645004041c01d091030300400c40c4044044e840304068080410090211a502406040880d0381070304010039041c0400d00141d010380100513080b500001928001c00b140c560005020203030103406903d031409040d40100441d4145406002e060340c1010040041005280440c50542c0c044088025205024401c0c1d402041c180d0005280c540041d4503640c54080b410b1040015200030721141481c58504c2c3e16560310f0325841c10764413210380c1100c0d0740d80141d084414110300c0040c105e0400c040003005034452a00d4028035200811150a10440c03400320841410104190b03403006102d038500e40c041c159912030700c4881049400800c1182140500380000005850b140691504561115555510b40103003100b410315041d0120400340d04510550420840303400084201d400320403103074001580d80d40124020900d0004542d00040c80c40e03103028100400110000c2d4603031100c00c01 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 274438075 1250 274436825 274436839
    0xb07050318011506110c040203090604050606010c03090303210e07060201050112020924030709020a0e10080718030c121214030a0b0d060c0305060301150803030a05101203020c 77
    0x2041c4506822500340c2d141c0c0d030510300d070f94080078032015018001c8018801078000c21601010740302c0c1e0204081e40c1054810442603404841440104101070019550000c400e1809500000e0b55480041c41c245c00da200140601c128104c1c6009101c4209000c0f4070301d100000400d0014407a0124001d60700c803801e00c5010010b510f4400041021001d91005120742c0360024024070850700d8551928051024404070020003000c40f03000e0749015101848900d00074000d44c08016120409000d015021b1420341c0c0f1414803a00c10a6101e0340312941102c00142c00100610740320300c515500c0c01c940d0518190356040580f40d11028000025480045011030040f144180c0510310425501d220545080600b1a150404030ac0b040c0009004d0901c1584158aa204000c1c640c2034032a035152200002c4460b4200380d840002e40760810042d40313060074021050684030104e0300c1c0c00c3c4a480c2440c00c54036330201030f00c15031b200364851010460544000d18114041d00040007526420401c03031030065960442c0301007183c05148 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 274439325 1250 274438075 274438111
    0x2010f170f040f020d1214091509220507090b092b05070e090c030601140114040b0a030b04180b011208040e070f0f050405010c170c1509070801091509020d0b070503 72
    0x1098000345c0c0c1c032602002d0701d20141d00703540c0489d028264100b81d52264100c241486c0161900400401d4501d890f80351110014403070410080040043c02e6a800500191008000c0307880e49894104c11403620003198408800185051030305490b0310001c3c0b2401034290300c1451004141c100c000421180984038050480d47e12110304420706440745024411032420b000b04012000e41940201031050103c440c0c208080c0c03401762500d60380030254024041c15000245d6030ba03088550340c10301f445040380c0001d100000c09020a0195541d2110f000b05006804085401d400040d0800204400b6a0301030856142d03090300c94174090f54010300385442480200001411084030000c590302410845003034900603560744241c0081c54481c103d0202441400d88403150042283c4601e8032400c0c0309c82c17034a1640e20520380001c1c2c200b004165261040c1600840c46592602000304000790407880b01d058002d4002c440810701d2045800042c8018003161400b0307107104990010461303821703070000055205610342c1d141100824 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 274440575 1250 274439325 274439357
    0x20d0c020c0604090c02070f14012307031b02041d0c0604050901120c0f09020409060e0f04020910030506040602030a0f0902061c0204080a050a02010f170f040f020d12 73
    0x424072041030300400200414030072035401d50850f0100240c0340c01112511562402a50400c88081c1d00032090141c8110180c1c07003035030f4055080184050317102c002841456081ca064121071150540040c20301102950922915031444800b201050f00200200694007903502d400850455460b40c90300c2c54000c05030031019078540070082c1c800380d82d030150640455170b09103811280c1c4d40c607022400341c400c2c1c0b86040002480c00350141c4880041c0c400c1d030b5409600d40385449400c20a840780d41d005200000d01210822626004104850754410340442d1641119140c07117200c29100b20031034001801e0303806064104002c1c040707140c00444c010083c24400b040211124058441242e461b010000d60105c010072549070503082e1148407240000441c640140341569030300d115490030032100d004480340d401501c0540d06543c0c0041408580e1079590400d800e4965101c0c0c419a10311900a108a6080303904802107403e00110381240540d159010346490701d0106a401d1004040710304002107400140d0b0115400d90807 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 274441825 1250 274440575 274440583
    0x4080c1311120c0d1d0706090810091509030509010818060a0e3c032b0219030b0a05040608060a05090c0d03050307080c04120b06030c040f020d0c02 65
    0x1100001d00380d402d00c86803071a103210342c65000d40701d41c02e182402d20521034502c125204e080c400003461541003039480400c850403810055154020806d01000a000700f2001e913020903089213040501c003001481122910b0305c0400c802c0040d900c8070f501860b001a150070141c100009080f2300209807a20301e0349644106c00001c4990682d10400d82d603401590104003400c0ca10741110f20b040f0700307a1003a41e00d055002844121101c2040c0a40203000c111000c103203160030038000d0800d88a4a112028518106610f84d038090045c0a41114424907000b52008a41a901c42e5040e036114100f03009040d000c40c07c50b148020060031aa00c06c06d07100307050b4084000361071700e03051080e0070484072a0809001c0325510684510020980142424907a01800c1050040da0743c2c0c02d8081d5001c0c5110b40c55207512030030002002040680010450b15080504000910400c01001390141c0110f030300c4500d0501903030343c4002181c00c0c0031051107a50781240c1452085003640340640c019104208225030100444132030603008a0361 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 274443075 1250 274441825 274441841
    0x10207090912030c0516080301180516050f0d020409050a141303120b030d080703050a05060a05130605060c0c090c12010e070306030512070201170f0a0b030a050304080c13 75
    0x740c202d07039882d01030114082c0d00010304000c005d0a15504200702d262100d1070311011200200c44100300000140b00c91600107030350314003a1103844804c10a03443c0c20b07030407002d10107010780c03200c1c01348070004c210382c10b040c40320104079a423200d181c000542d120b030b41d60300d02000685000d940c0c1300c05017030800b05042d02c030889840b00e0354881c07440002124441c0c4d80320b48080d14844507410a1800b059190310741c2030401c2c2c804100f1000110710ba40c1d5405040c0c500050000c08444024014880041c03e0005001c085e50b40d00141d41c0c15101c1c120341d03a00c41703500c90711051001442d242d400306400440100301410390120108803000141420b5880300c100b9913400b03c078201984251024440070000d803d0040c0301c500441d0340035a0707001d0140d0400050140d12925000d103810700320032100004ca00005900011564844514031440c0c002229544690030070b41000c01514200600303030ba8000ba46d419480c0601e60301085441034030380d040301c19a40d8941d114942103484124045041740121071250b00700e251190304d4451905 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 274444325 1250 274443075 274443083
    0x2211030624060f09060a0923090106030209010507050109080a020d2109050703051902040b04180201030509011d07082820130c120c08130f0c03110102070909 69
    0x2040080440c1000065082041980300f9000248049126a1203210007001d00020716150312822500c0c00e0303000d265601e21105010000350303c40c0684010303500e07010000ca05440c001e060142e110a04200122943d0282140191441d800c03c150181440b15107401090b180080781c2c01e0341c50001e1442020394400303450660400401c400c80e010611404995402007007001e1140080c1e6141656903103500d46007001280c2200000d0140c04015030451520f441404014a0180c031f042c030443d00f80c01c0800003440c601c11b5020b81071544940015040c0d0400307611a10507844501e8001c810781081202c0780780c0c2c580144c001e101040c85891140b410740c40c450009180340b4203c0007003070300c4816000d42d180c01040e040c00e00444002c0000e1403501c11035594840401103d5034146400207075108544500411342407062003141101842d005135400140c4d8040b01c1a0390000c0111150400010f90b4500345000e010131400c0606004040d40d404002c01c030300020300c0692032800b41d00300e4902c42d8071060583c00b102c0b003001c070081c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 274445575 1250 274444325 274444381
    0x11070806010e0414152703071506080a11030c01020613080d0f06080d02060708010623070204020c0607030b030613030e040615031e05090d0822110306 66
    0x40711169445059010b8403034030411509140090006141185c00001071508844030720801840c2c14051090303418000f008201c54800550503240241c80303125441c00589a003200e52010a80d914254204000810700742e0102c844801182c2401c010700c2c1051040c643c070a01070b89140c1d40c2158400900d190060002246038100e031011541c0700102c9500c010000d02c1c40c80d840c0c502c011840ca40318481e038030040040001800d00b03544d01c010003d05009000f020541800309030001408000c1d8000c020280c1d0300700100c032504600480c245180303510301070304070025401400000c1820b5002404200103008091980b0240040c1c5001005c15441d1101150654125030031029204003181c85409030041e000310180000901395102d2292411000c2c4003600400400d0b1100300f070314030440300d4032a20700034541c2c551070411a07410301c440181c2c0c0300d219419881080009c4840401c008a013920084050f414100000d61000030f840d283c0b03003c40100001095110740a420b00180c07160028504101345007208814070 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 274446825 1250 274445575 274445579
    0x6030a0c0b07060e1c270b0d0f091b0602010605010819141006140f1b0321040b0109021201090c09030215030907050102030c0606010c17070606061107080601 69
    0x201800d40201800740d40041d1104540884910180302500205071160305d0340903004000e003c051720320748100900240391910710340070001c8018550301d90f209507a42000e05580c0c07a00d05a4076440030303094090007401103a151414000410000351f40e28903002c0b080184404805a03510000e03401ca440c503200d12400300e1380e07540002c4d00c051505e6540340c20041c0d81c1d11001a4410300880f1403040070104680403850f45404001c20b00c4550b810450843c0c0719600c01210922300f80f602c02840311540a4039807160031040c4640328071452210140103035820138200702009010040d05125650084105440940b508884040007107070300200c5000715203030110000070003190359181951160040024410384000c0051049000c40181d4400ca00841c50b1781652500503203d04017001d2490030400aa48101d041d9403042103c0000b816021500c0e640c070840900f031011540015042040c95419000100c0181d04000541035040007a250301075001d0b1810303580c400420b50303806208250760b007030140542d0b01503901c030b030b001 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 274448075 1250 274446825 274446839
    0xe0f0f0408040306050403210e030d0e0c120304140f0105070b0c16050304030c081609050916180501060302040f05090a09050706081b0304080a0c0201020a020603090c040506030a0c 79
    0x1450300300344203400c40352809599807103074400c807502074074100c0009134400398468205100000703119001c488420104403c0d008903503002e98134481c40c0e0103a81c00350303141d0400b038001a1003400445600107001c0c00c0c2c0314412401c5071040d5282c0e070003401245040100d490005025042000c0b030b0f200c2c4c89506849442c94040329454040f101c090081c5820032251042043d41c1d00b02401a179100c4c210b500c03450003143c5490451500e098596465041140d00b07034003220010525039064403a1601f111900800018280c0b501e0f030a89017851045503400100381c0c02e2040001c0c50740794540180000da80314213170411042c2d894100c1102a4844d504ca003220034100708105120b5460440c2140380c000700345040000d200340465641c58100310245d0701c00008121160100098480d40e001d06418984e9034070309162642c60140d0b56014a4000d5145140403c201c1c50524030469008200c45c112140c3c00600c0152240340400a040e9200035a0008900460502010501030308000520b0240d00780c1c031102c1c504180d402c02e40 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 274449325 1250 274448075 274448101
    0xe06091906081009020f0319031b0221060f0411010e01030207060504060b030601170a0f1a0103050102040f05030c1005030c0f070309030b060616030e01030603080d02030406060e0f 79
    0x20111280c964520300056069003c1242006680c0c900401046041c032600401217042994002c17140290081860002d06010304000750740420f80c54106030480804c84010709115160810000707400c03c2c5810003543c0601d94400c224140d640015040714082d549402c07003440301d8038042d100145107920b2a0f0000c4181d602a103042c1340741150614005080c426540ca800096030015103082d42c1040e92203d20304c2c502e04040c449203016150b900d1800120b00320301c3d42815510100c0d101c014014660601080c1d0800c0348490b601c583e9013501c4c000c031610301d5840381040350003580148103412610215180c001f90f06c3c140800c066580500040c064002c040da1140260341581c401400c1000c0200201b21100e22540c9a2000d4036802d4003c1d41c0c2d1a03685400d501c2d081c0c00d066130140c0014403802040c49045d69000b02000344100d61a814608024417000306001030f001b40c012034000070300180000c40c1000311360009502440c8511300030a410b1083c9942c0781d0300c886c12a00d0036134441103040c01c000000307011700d41042 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 274450575 1250 274449325 274449361
    0xc0f0806091503010f02070c15140901030e010905011506020d02070918021008090c0f0904030e0102030d020c0a0c06090b2b05070c030801090506101407050d02160e0609 74
    0x2d03600300400300000380000c2c216041d082d0b4150740c2503408a10981482000c0c4203e2025001c252942a00e20400e10000740040714203071010f80040c040011050703040c0c0d00c01d0700408000da030504002d0041c0c891518106018080c03044e800c644014070910001203007440015280315400540d0090803442d800d1400280140203103038a25082c074211304200e200140c482d40c00d00a400e002c03e69519840b82040c1d00d030b00d41072005803000706c0c0c4214013601c03140446603201051140c010380d05042c206000d82a07200140e0075030003112650310b0030500c0803e50107045100401d018054602ca1380e030180300715403500016148100607000300350480c0d41c240801c0d00c182c24880e0404050b5000c0c20507000019010301e11003000e079032080360302000080c401c3c80d00c5410150013843d000d001d056560402c0c055071601c900400c0d01440d0314415841040010f9406020701340354042100e0200c0d170400c0a13141142070b01c29000e035480540c5c5124001d4085d900000042600340e24128074001d0074001d00814030341d181c0541c00f8000d050b0807 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 274451825 1250 274450575 274450591
    0x7020f0301060308070308010905010522240f0611060405061b07060c031a040c23070b18100b01020a11060c060a0b030106050f06040b1b06010801050a0c0f080609 71
    0xa582c011010038441000303002c4041c0309036142e509079810054654107841c0107034002401080840140c50000c030400780118800c0742030140008810b0071007040380a070100101282d0141c0440c200020600118003900d180984801e44c0301c40704448050710180759200b20495025019400c04804111840805030382031013160780900440e4204000b948030036040b0b403120220240440d0355580b2502400340040c0804070301e0103040340c0401007240340c0e05020b0b003500711801c0704132110031505402c032262654140030390b10500d800503502c0c0071030b14080d000b80c41e01078141e0020030f03410b100b0002070b0b1401c0035103030040c0c00c0100c60684c040c101c1c1140c0307507803000703400c2e03440c0c11140764031007002d102000e16490204805c0b81325600e028800b08400c00150203140c2104c4990300094040c0d01d81000c200450b1f10b8000894007103481c5448581d98035060b403c00c051040001d03500c4a02305020341c40001540c490150449800341c0036241c0100200c454038001602c880d08241106c1020400aa0019070b181c80d0205a159002001d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 274453075 1250 274451825 274451831
    0x22205060d0b011e09141c080a02101508070506030108030a0e1c1a13030e0f0604030f030c020f0406080c09040309050a030f05010c050901021e120a0305181207020f0301 74
    0x80d0452540440c546503210000350803000100240010801000c1082c44247c41c0340366200014510814840c2d00700a0141040c1000603e01001300d20070800c18004250954007048007140604813036000407041d01c0343e0b803950310842c40c01080034a44502100c1c100c44462000314a0b01c0c400c00e0040d21200444c0107055448040601000b04144102102041031845890400104a0340c0790003078550034030207401c154240024880c4170380020303001075401b42c0c4c100086440041014195001440c41d10640d04001c0007000380380a100304241d000303800d16012a2084401c2840010b81e801403108031180ca100349e884a60240d6009201c50504c00d6034180c0140c020b2400c0e44501b5120004145000c00780e81c4211100c4010a502a05029080c442c500001c805840c205e80f03400c00d800c00007540c84903400f4000e6041c041c50b00d044110007100700071041c140381452000c140c030f425100e24041c0081c0021202c012600b00d00b01e40a44c09054042800d94620000710742c05820b203284e039024400300c050100f01d076a03010b6507 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 274454325 1250 274453075 274453097
    0x30c02030a180308070b0714090f09090c0a170c01021906050a060b0309030a021b030c060f070b070e011707020303070e03010b0901030b04230304030303020703030b1003022205060d0b01 81
    0x1002d4001741401800b419400d00c1d103040440c8004c0051080c291a6419007006000700840b5507511107183c42d040c58211220703c0107807140521181400f140345455540082c05010004881e65612007809140c41c5002c20f440c0c0d00c110000040e40c0f00c5036410f10a00c03012003800181c800042d03003603000f103402030390860b0005801e40c3c6070340c0000703455402500e44100b903900c04170350480025030401c2440150341d8404d0401685c0e500c8040801d58030600d40046511800000ca1809040c0c0328120903518041e400c88070008103030a02110140100208108090010b03015207441003071154000c084a000b15541ea00851655031040e001b00c8a403640d050010381e05540756400b07003a8998034101064080d5024200907492403c003441c0000d01c189000c0c800e90140d9070300c0082d60520100200559040325014200907980e2401807504078000d050301c20761039910010701c102907150746515901908800350340140480c040c501c201c040d01ca00340b54900c51581c3c056820441c0790b000380e801d43c200249010301030400c110420 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 274455575 1250 274454325 274454333
    0x141807060809100c02030c190b060909100c030606080105041e0e0703060609140f0c070305130302090f040b0c04050303030a0c030e030a050711010309020d020108060f10020a0b07030c02030a1803 85
    0x2131000c075001801680046006900b0104c103224242044482080800340680d8a5641c9100c03210000c05842c03240c40420002a0040e100f400314202080c80c5100c02c2120340c4880c00c0141c0100b0302409030308002061800007240030b00b024441c0710312000908045a0b40c000d03070062104041c10702c2905168490103620030000c00200316000f110047c01c2d40b25000320740000c0800d0326210456009000142c0240d04034180180c000000084444440e094a03055598014002c0428407001c49030780000d4200c0381c180100b151811840f0b11080c0070b14801e032815100d43e00c030041030701d00c14000c90107101da00da0010008505859003580c000d02107144181408201110100b02807411600070310010000319100080e0b80b401c104010004005181003401e04021748003ca03000b003883c2c01c000e4000281808080301c08540c0030758601031000205500100101442490440000d446004031002200c000c0f207800042480313980640545840100282e008504111244100326403107134003580700210846480e10080081 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 274456825 1250 274455575 274455581
    0x60105162303030109050615031f03080a080604050a02090f13092f061603050c0f0715090e0708060120030315031c051b011404030314180706080910 65
    0xd03107650005540c0329894181c03030030152600105038600c640d490751042d17010100d596042d290001a46500c0c00721928520500705d190b07008640001c2c00002d404a0182c52056203c07520760710400c0151400c0c002d6495100b20041a07008000708564082d8003800d140c4046d00f00800750071711240602c40003007000d90054403410a04040301441c0d0b401006d00840038681c481b10601c10441402080c0c550625017110545a00c180c07450445000b0204030000912051821080110080e80751440064406c099642c0d01d0140d000044044100f020521000e000074080307851b82c0e0114800d031625181e8603c1680c0d000011104600140061091a405001003204d21b003000c03c041c5100f480c1c0350350f49880300a124070405103000d617601101f91352480381ea02e07034455813503000d0140c1c1d5070000408211882000301e20720f840d002d04444204403a01c180c0300c0e0100014140e2640050101c18100030283c141c64454010241896a4845400c08540d2220404204003441f4020407503010301004141d401105e41c409000f401c1e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 274458075 1250 274456825 274456883
    0x5010207020a090e060c04031104050703020c010f0213140a12050f010614010306090b240d020d0605120607081311090403020d03050702010605030c06160209010806100e06010516 78
    0x4a6540c44c030030989003e904000c034982241c240d1154604040c03031a13a65278240e42d0340c50780c2140103540307580104145a0003501a24001710600f40284110f1481001d940001d42104000903065240c0c040002030114607241020705d060700260844000b00d08008114072560a403500440c0c0900c984800c0c182031400031710854000c2d00f409079141a00154200c00101070750216042049401d241601c00c0007155141ca81c10100010b954440c0711078519402c403401c6482c0240c00d402540039000041002c07840529600c16000d69404490a00403600c2e0f4411040c0d8540c01256031402207202c91000c101400d1026602400d0503104a68110520449501060b43c3c0c03101a5012005a0b01c04840000000e405000d01544804548000c0060354940000251b03111159a0750902800c40050448810503c5413108510b26801400760001035039500302a541d40d11040b00d40303410074000844040340b0004402c08017406408140d413414200b00d02844907001d1050034080031515030b4070490050103901c52400217038103 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 274459325 1250 274458075 274458089
    0xa03060c09080f0d1d01020604030e030313060305091b010c080702150f030709081b1e1c0614070e060313170c0714090c0a0c0510020403031d06030604020705010207020a 74
    0x4490850325001405801040b46011180709610440843c5c07a42e0020310180d109405140c44036541418001007411449031110f0a07104044a0301d0200b0202c1d0950000c0d4000c90035042110951b400154000d052034002c22000c41c00125103c10750300120b0001380c007030601140000e24141c41035102c610001e840303900981d501e0304004800710403c03001682010103540141003c2028042042c0e901094040c07042c1a40c164910a0600a00340341c0400407507807000c07190400151040c0c881d85000c18180301030a814a500b1030380c041c10b080c0c0d1000d4000f030b6100c80314040c03201a02c0b1010089000c104000c010381004224409841c1d07114013030341c00708000140d81d00300c4405030003200d42d4540002c002c9501700171803074100886990304920f02007065100c02000720ba015640410711a00d400b60803504407040c10751102c02802510035800c903109902102e074024011a071103925924034030a07031440c40014a42c00c41c02c10581c040c00500000e16503007019001003942521031000140740c4009503000607003200b2a500655 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 274460431 1106 274459325 274459333
    0x130501290a0513170609120a09171c0306170a0f020105031e010801150602010b0315060312070501060302040c110607030903090e180105150a03060c09080f 68
    0x1005003e0420101d401e464040340c2640d50b40320300f920800d481e40200d18010311f0010b0780404840c0c603486e198981c03c048030700c0c04110300b06141298031640518081c0740c81280544200e5500800a50302c143c0340041c03040d0030301141202000009101c40c01f103621100c2d10b400072480c48200c0c818407650900c0c10756a0380e512039103261020307210103039101009000031001181d03000c0103400c410390000c405200360440d00d903220800c81c01d88009203c4960150000502c40381e10030302d00707405c0310751018028088400a1280c1c24406910381e12602044c3c0b1180d42d01e1205004510b000c1c01070030001c003414540aa0105441c0a40c2740d00d07207001600460a040e6100c4107103081500a1055000821307500c0d0500c8070a140c40161700310008441e45001d0002c3d440e1600103000200c030348419461860380038201400180c20b507501c0e100201100d000340b00600000d440005015542040001103240e1200701030 = true := by decide +kernel

theorem cover : BRFrame.Cov 274280575 274460431 := by
  have h0 := BRFrame.cov_init 274280575
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 274280575 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 274280575 ≤ n) (h2 : n < 274460431) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
