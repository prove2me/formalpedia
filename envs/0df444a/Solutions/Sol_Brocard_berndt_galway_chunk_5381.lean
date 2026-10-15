-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5381
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:41:13.096432+00:00
-- url     : https://prove2.me/submissions/399b1da1-8f2a-4097-a02c-6f43864d6d82

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 967625899 ≤ n < 967805755 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 967627149 1250 967625899 967625903
    0x6090b0a0e0a080a020f040204050d0b04060e0d0314070804030203031504060305121e09011d130e031e090a1a0403060c0509090a0903020a15110c01061706070c060f0207 74
    0x7a2040200d00e0103c046035049410703209030b8000c0d00c2420440104000e900690280c5600180803a4500001ca8103030741e4099041806020002081d1034406400c50038a401140604003094a9882d60300c0501554014541c1c070500b9480c0144842c18980c0e4001c0d01c911009d003050310b05040d001044581039407151f100720000c3d680001101c0c80029240f5401c0c00c150440e10314910301c070000085240316040e4410448580317a40507500c809007825900c5c61855034030170303008014ae00500c03002c424600250719441000030146040000350340310b07410b031108411900c44071501030340100014452044603844480c010810789280070a040c181031000d6264041c580196880580b1203420704002650b1103411070005c0109940503240d00c20030b1b54403600c845098401d40034000740140e00c0556000003283ca107100039581098001d001040c0d59a0030300041c40780d80c01055100390341765501d02c0c1c108445805001076140c451100f4010f0b141030b2405900107004501700d00006041507803141707940c4160b4010f40d4100c4081075 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 967628399 1250 967627149 967627159
    0x30b060a0b03090709050c0412030804170c011e2c12040e07031104030f11032d0c04140a09300206060a0b07080d111209070f06090b0a0e 60
    0x490900241031351100070744540e5401c2032502d4040349216152408841c20749180440c04440711400d13642c203c0c2c15420003001681c00d00403028460740b2060015009042043c5101c0010074001904851000b5002c0b8203d07852100515000303030004d441c807504200d4503941d00b89044401c003590102c0b08107410140c0d6044001003c050005004c0f61034000c204030607000f461141e0301040200006280010244214040030708034032907480d0301c080018400d810010146102500703444000034000030111003203103c04901c100da080049804a075040080150185107a012102030000d590f00c14400ca060500c0039101c41c24940d00e810043d03082c0082111490703a00400c903002d0094071b255400d00c803240482d0398006640180200c1c800300d0340e01d1404101000a80d14101c01c0b691401150343d40e140816404144d01604039a190902c03a071145000700702a004e044a400500111403400039050340c02c11501c1e402440e00f4201d855014848150f11501013010b56160640c52540c030708c03540701e06440201c4000c980c26400 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 967629649 1250 967628399 967628401
    0x50309030904021908060907051c0b040c0201140a0504210e030d0806011d0901060c050a080f040806100e0a02030403020a24181104020a05070b161205070207030b060a0b03 75
    0x880030003e10800c0d10344c1c4039035880c14075413a0700d801c21026032400e8a414002131020b0080d9019440d54440c41c85444480e02c000007115500c0c000802c045e1000e2168580151350765a0035041516a14800190b1041d1400000c0015181039542c4014040020032814440604400e90404185c007030a02030201641c02812160020000c0700000c0c60392408a820500040b464144400d03440c0c00182d0340c076900b00c0010403203100c503030a00400700c400506143c070030b0340c0610400303880c0c41c0442d64050090215140c903d01c0981d5550600000d10300d055070180081e000d2180c420740400114200e410015000f0100071000341e580c5d1100d0408a20301510201c0103030626921707800031103140c0ca00513502c1d00c100043c0c503010b0000140c1d120038200d0006a040000d0011a0410701c21980352525900814550b4018144142410515202c5400d42c1c0da086400304100c8010300b45016055400099040d52480d50402c03e000703601e06100000e4440d00e4510004000d99001404500160b80d1041d9400c0600b0341a96041d890b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 967630899 1250 967629649 967629667
    0x30c090308072306060a0303050d020f030f0108010606091a18040e0f0105010603060f05060a03060807032a0b1215040c092d060f050d0c17220305030903090402 70
    0x80f00e00e20120f500202c1d800225054100002143c141d20410f001808942040d1a6450640d966404140416001c0e41d00b0480c06041c1444140a1805403030042600aa10341c1440c010b40d085901680110081c0207a0b60410460044403d8280406c034610154043d2503920401a6800d016200e080d015481030420607641e200110003c0c4040404030210024401641c1c0e80b80241e040725242c0c003a860048000c00802d01c0b09040c618020300b4010002d280000c0d145aa4409117410f00403103030001c5030200520340c0d030380e5901045080041c0582e820070543d420200c0c44c4c910b0060040c41190800311620100c40d0004244c0c900e201010107095002030000c2c00940750420005012544c1c5000f00198484582e8101c201c1079045010400b40c0758601e180340e1807450a01005441c03140d02211b201042007020004001c00074010301a840e0200e0350b079240d070303c08541c0d0303c08801210480240820300001c03034400350302c0d40c1d61030107000e04240c941c040c101541d807615100d00f400c0c02e51081c1e61025400c81d000140c2800 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 967632149 1250 967630899 967630913
    0x2100204030f20031509030c0703050d03060f0e0402040b030f0102030a0e070e070819090206040f08060f160c0201020312010311030d030513140a0c080f0d05070f03030c09030807 78
    0x12003600c11034000c2c18442c0c41c141c60f041c1c00407512980c20380603400304452207001001c8051094100712408112410201c03103201652408060390130480e49034009611280324242c246c003a0344041c00c6150004074035103003010b410340b030381c139200610291213540c544088004944050190850021085001b5036491409403100c5e8050300f6100c030501103034800c4100000b0318440050010380076000c59540c900c0e0680350440001c0784e084c03c5500030850596110528001a9610001440107040102c2c1e904c00407480c0005942c20034a009000c685655015010003064001013000c0d00700950081c202041418010b000403845e40c091511400040c520b000c002009205259142c25801e04080381102d00c903511482c000c5003a2a02524401c890800c443d80c200001207010b150060f03112814412a03000f03e2458840701030b882060f620140140d045103208802100080c0000c507400c40c810300780203161928540c1e8100002103c540d010f420141e4540c83c2080b040d2262444100035a0400c019603251152030510740 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 967633399 1250 967632149 967632173
    0xc021509090c0a05190e1518190e040b0628060f11060c0705010606090b190e0d1211031303140102070c090212011a0a0806030316031709030f18010210020403 69
    0x50b00c1000040012800e50320180c0444559a038062000b505000480302400100b01c27504180314144000c1c0400410340d540001c2c02c10303200754003800d0130803c0c03801e012080c419042e0080c0307001742c04501200e030b00140b004604014141100c1d000d18244108a10303c2c002201c104c004803002e104507000340414440b0310400f680c0030b002c40d50300460007040469a5084265903451a51044190142c3c05000c0000b15460101900c0d0b400c40440c2049003465620200286441c80661400c8801c10a902018041294041007034600071941e0700040d0300e480360041140f000b01c6c24904c8010b1503c0100307500c01005082c20f4068800c101d90010a40822540f00c440e03a8001e90403000c40518808910400001d540400a03035101841c940319100526015030903004403404035009201a070540310030810940c0e100f1880c84102003407130283c0d450348001d0725241000c80c2c04c26400b9010340c6203940207000b00540301282000701d41040d004583c02c82000203610f80141d061151400c042c00800d44003107000000c7c0481c01c0000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 967634649 1250 967633399 967633427
    0x307230307080f0d050a032007110405060609062a24150f0406052205010b0c060609040c0803071109070306030b150a080d0c021509090c0a0519 63
    0x40d40510751146480c41d034941194102040300d9120241c25101382e40140001d00440c9001d140c04a241781310000c030590301d01800544001d4035000061498248101440d140c2e00c01e81381120144020b0400c0000140a800344264142c441e07400000d00c04d484031040c03442001c85100c45000c0b03002148610303424a442c0c09664030510030040351020103808074804494614481d00d03020311144c0d0802c2d41c101c00e1001c0030364a004010b030003950b0354901140a0f07540d1807941400321084000c020729025460300700383c02da641c180d06c290400b5a091080e655000e030003217080d0381c2c069000c0e1052403940e543c608200c0070161641e4009001800000f070308100f400b8598055080c0c040c01034410821a4030b4261044044800520002c0c140000c16070104071a061004640845048018201d81805455415450614150300d840c1004104c1ca0742580d801c604101e07542013204000841c10600f4500c03801d01141d034400e00104030f15501880000c2040700e03140581c0c2030f01c030001c2440800c0b02a0820302d9030042c5c15058400c0301 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 967635899 1250 967634649 967634653
    0x629190e090703050c030703020a030e011d010606020a08120709090507050301090c081e070e03030c0307020301061a070b06010309080705010b0f2209050316151112130203072303 78
    0x41c00c014028058540a640d80d50b05c4d003440c59480c660f0440081d084010903404250311044030554918090007506101023240440b81d440b0741441c9200c41c01c640b499404142550480c5d81c03803401050071007096881c8035a2401c1361200c03a0fa2140001c644010454220fa03198600e802c081c014100e51003c040d5060314401e0380c04204000c11400c00b03075823000c41140e26181541072030403400b25282e401d8120582111940c1001c00c02000c8150001c0d00f1900900c0c149803490740085407100a5181c00d015000c010728070090484c075810320340d55007400f0718445c500010300038000b440041903c991299000101003038018410b1174035090140b52083c064991808610301c01c8040300c8402500d8680b203240a11a990701c00341c615900c402e8140e01c07034060803400b4810307242e0b80803d215502502101004c203440302c0d072142c140c80441c031f941c0c0050502224242d01c000c500c1007006010707135010034000c10f030b1054002404581c5c0c0d41201e50740c0e10009203000c0503a0007103100004032201c41c1c4000c1108844400b204042102 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 967637149 1250 967635899 967635901
    0x70905040c06050403081603020c2e0f052b050f1006030506100c08040902130611032704061802092803121107270629190e09 55
    0xf112a03028900010388000c8040040c154282d10b1641080000d511a0060321803030b08031040014841802c91808480c884450505040152036440e2203170780800c401d042c948400b045040c002401c5000350300c0ea1a4254074a21810032500102c08507501400300350345d0060000d8940b090300c1d2001050b0540721010041e00c450804550036010b8099a44200005050711040904800c4100c861f034000070f41c140c0b06580c1c10840440d15200d140014040824140a942d41091600d64000c00030303100c45602005d260000d03c54100040c2440342110940c00500a032a02208040d42c0000c00821680e8400300b02c2c46000400a030b81400580c02030440c038182242c55281c0e8010b0444104094448110000200223010f4014070000e0799002d000e00214141386420801ea95002110500d01285608100d0482c0007020061264114108d0f480c0521402c0000034460b1610b40442e2500304444080d10f020021304841111542d54040b005480103001500701460b20051075240107010040003004050003088004 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 967638399 1250 967637149 967637159
    0xf0519080a24051b1309050f010602160f031202010f141906030b0f090f0d1706011110020a14030a0501090e0d0f0509120a0b061e0d150905070905040c 66
    0x71050b1031161800050b20080d21442c0c0c40044e84907445500030b11030040b81e0250201d86c5074454410300d481114000400601c030750405502a1030111a6811240100001681030215140c0e001313851046a41c0141d17168100071b11a1400d034050421840c21414062401d0542ca002d1207200110a000d402550482d40c4003985081103541900e29500002c4d0011303403008041560000444d84031580607440d4400d55044000440c51581801907005040340000d200010794003a03000d48040070b1340c000009003480e081820402121b01c1d2203030803006990000550100d90300c40304a004107402c00d1440e01d50740d0784a50341d00d040b500c3c44000300340a00070040c0e100d142c400b0b4201a004001454021003100b0703201c0a00c084201d01c805c035166401040710982221012048011155040080740c1354288102c80d5080c0604d000c000380034a484240c01d03410031002682d00d01d520380d51200310300040d9103034001603081c41d1940e504c076061000c0e21191704020001d00c1002c0300000e0340611703a40035034002c9100d14101407002c0c1c1c0e10 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 967639649 1250 967638399 967638401
    0x901261311010e1e04090c0e01030c240804170f0c06150d200a09140f060a1206021201060c110d02060414030a02030f0d020114010f0519080a24 63
    0x1043e01c0c640c00c0072040150716a0b40191500d070800c013040080020030608507035906c402c1d25002983c01000c00c454114018410860803030001c40140207500314081440d90800300480b884101d04900005200c840d0000c10180700e100c2c0d06880b002c030705006090795940346072105a00145c0c408020100344e40500c0021551100b00355440b5409540300410f4644d880c80c0603242c10030440380c94a061000b100000403501079544500c851038009080204d40001c0d0000c0e600304c000500e6000a01c00440081030104026203a03640e14034a80c20344140010f044280c070b0302032820340028803605041c0c2c0c1014014000000c1e00b0380c1d204c0602030400b4452040e68041c400100c0510000b2404030740001d501c00001e1200b481001da00c4011f01e4501c1400030112404414290086810420044035039562030304054080c484c5690240140b140c9080343c0600c0c2042c035850075905c48114400f074000d0500c254402107050340050701e00310b9580040d0401e02c094410001451030036200d49500e824806007402c5542c6045a034201c11 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 967640899 1250 967639649 967639667
    0x12110a0e03031201260a030e040b0f060307050f13080a12020303010812030903090a0f050411070c060c140106080a031103090904021002031c020903061308090126131101 74
    0x504010803d00e07400c2003070000400354034428900b001201482485a0b0010402503e540703640079840d071070aa038a2100501050303c00441d4020700400005403c10707040e8403a80212075000245241083e12031541ca001b01a83d4030800300c503a480d03002904004a0181008292040070750322403d046110449501826030b1203010074419550180c02c000040f0b003c0c054035200a644c070002c0342003500d14050f203010008014803181d401c200103a4240c61018811814680f040700e0100c007104284078107011603551060a0a5654041c8801300700c0001d1843d8200803d0440400b82e030281940203020309529055088d50790b081c061815030001d910082c00c500421008011034488d030401420180059895409121014040b84540411484100405e443c1807049190011048000000250fa01c0c1180320403d440c0450282c688510301d41030049110000d40c0d4802200c0031044203003051a0405d2800d400000300c0c907002e600729880316119130f0400500840071011070b03042d648031380000c3c241000a10011544850703 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 967642149 1250 967640899 967640917
    0x714120604060608040b0a0911040e0c0301180b040f060209060a03020715060303020d0f11010e240601020d030f0b100305040515061507151b02071e051012110a0e0303 73
    0x86d1200880c40004d500e0700801c485a000307429030380003046000007080448508044001c4a50451900c07180b040c0707802e0080c0200d120a1085020340101e49844610402c5800b400081403ca1100b04030400c0012503010342e031365114010406500c8000240c8040c0181d07000794003c4480c803080c42220b44030003003540304110550b03415600816265844140a0350114504c0400e0070902c85005610b100c40c14007402540701c0c00301068054110b103030401e6003188024250f0786004801c0c131581030400425036400101440c40c40000d140100b80c0c50340b0171202c00d00416161a02c690002c0140850301d04d0740d40c25812160041e4402c1089a86500f80f0400181890200740d032050ba0100b040320501840402d11005403503c3c034010401c134a0021314488290703040390392540c03046100aa1001d840d1036a81c0d014000c0701c008002c42480c4820300b81308400c00303140003020390207010706c601d034124019100140301d1b581420360983c00140800004040e5040c203c150342002246000145200781020703130604004c0152000c0003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 967643399 1250 967642149 967642163
    0x90809010e0f04020a110c0619140927090c130e0f1507080c0a050a030207030e300316140a17030403080c0306010c0605071412060406060804 62
    0x20190401141c420380c0100116070301209008002225507a5440100304020607612400e000c80b2041d60ba16080c0b04028a20500ca454140011460000d4a90344050a5015440c000c0011542900220510b0180c0d030041500400c05546d40014250016000c00c008004150200c010380c0ea11880c00da50384d20700080c0582c0188801001c02400c40c0aa0020510300c184042980c0c0540500340b210781c64480c480a0810300b0f030340200d003400200e50f00400d446402c8502406c10034686000a51f0192052040203451070405900207400c4060610840345900000b0000348905040b007442710180d02e407124660a2603244954a0715801202d20001007125000c41619000314540f40f080e0300c9000c4040c0812003038020703d0085940b4907000aa14640c52010780705a0140c2c40e4503401c1c9402c006101c044000e15041414030100240030081e0303001014051000e0740403030003080955501500b00c41d40c0b5140f070a940c1c0304d003901007800d182403914205450302c80e82085d00c040015a0356042c0407200c04800b690080c00030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 967644649 1250 967643399 967643407
    0x901020a171504020c010b011704050c0f1807020115060c0b0a05090a0b01032f180702030405150d11270402072f0a080d08091c18090908 60
    0x401c000c1485540d1103000480703607141041019000c0350584e4420521801980d40d136021851466070410282d55503070560103c880c2c044c1c40d007075a540d40e4900b28038108600c181411200190b059989495540780c40011000c40086030906002c080e0281c07140280000640440310404a1140c0c0b080b08003451042e0010780710000394840f20800030003400042c05404139030045034903c0000c1400c60002da8000e501c1001410b031099191740da4200310000380700d405422043c00401c055242d40c2c400030802c1d10100c100340b0341140c64035040401da140d44102d038402c680006c4c1c50300a1260400085014003c0d035110800c00303008146500c4440680c44c49843e0100e07084008120204520228448184512050103040103203803030002d4651962442945010320303501034001000b203600c3c18140115205074030050710005241424141e1441c0c591078200400c10130004c036034000034005e91003000280034180a032410010085480ba800404100002c90302801c40c140c19100014407040340c0c8100d080e1240c22204280c20 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 967645899 1250 967644649 967644677
    0x90609070e090415060e0f1b071212050c07030206180703030c0510140a0b030a11040c090b04080703140d02030403060e150a020913150e0402060418140901020a 70
    0x4404030103001034a100c1510600c01d2044c840d144100307009001000381c51000c51400107140180d01c0c20080091262106d00e080640222020a090300c034907643c081c107a010081a0010100c03080c0754161005025103042905001d14103076000d0041100d64000d5083e00c0d4a5a100140d94a0580e6034071035034031055001c100c040000c03903c03c04840f80524820700c140e6009444010510341551041480e0141480c580c800b8000d64000394890180c4032181030b006800c034130b09030b80c45200c0054030030120390307001d151902280d00016104201d1100174059245401d074503039481c1d034140b503912501400101d403000055122024a6500081e842c10b40d0b0000750300552502e800c40da039002c00b030302103042580303c244128900645120782445c070251045843c0803005032101060402c0001d010882d100610100e40b4188032528000305006622080e9440f8075035054840d29070b480403541c80e11540e400608607030280d00c03403008120100c0d00b11101151550340740840503101e485001d800c0307206040c40c00012941d00010001 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 967647149 1250 967645899 967645909
    0x1903020301080f061611150f0114040e07060806040b092d010b160618060c120b060702100c02090a0b01090512033f0402100504080601031e0609060b090609070e 70
    0x10900301c07540280d546e2062541046503907070701c7c29201c0055426000d401032003c0010350140c940c2c0d4000899080c0980302c0500744060311100180608820884510001002c54507107401880100d07001400007410381c41e00c0c0703001100c90111104c2805106030014003021143c5000801c0364142d81c28401c50b54a82205031f1100d40f00c11000747c000301c031455154a0982d21003101c40078141c482a00a0801050361000740c940107100401c0303443d1807442249005040299a01c80e003096447c40d5070b05803068008030034402d109580d0440e052000a60061941d010030454000540160308408003e07240c006010361904200a80d50450341810425503109000034041c8207050091406180e200048c02c1000740280e005070344030003201310071694000d90100148000c500384080095130125041c50301c1c9040c541400078294642c13070103110140c41200070b82821002041d0b4440e040f0300a5622144c01c01c1205802e20704000030b0f1110025052044001d480011001c1c10905c1c0040d1040101d0795900407190500f41c1040 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 967648399 1250 967647149 967647167
    0x3060c030a090c06110d09060f11010b151e03060108061c02060309010207050c0a0f05060d02040e010e0105031009120c11090405010b1c0f11061903020301080f0616 72
    0x19512648071264000481e012450743d1010380b10a80c0c4103042281e83c2854145800c8445461070100310a418003004541d502c510805255000d51400c016402001c00c0c046000d400e8207001903034400e000c5c81103e2160082c0714000d2072080000b0240407802d003025000d807061804115501c5010801c842c0001d880b038500307600000c02031a1054600c0701001d80e26000b01710181c00442d43c0c0c00032130394000340b03140600100308200140500d0844044083c00d082c2819030410031550701c16180146001302d404840210190180d50161520003c060310560751070040760b1501c4000c0c03003030358081d00410307005034450646130107181b451581010a800380d180324110102c41110061405641c9070401c40f4241c1007a80d180411603014500540010580da641c403010401d0110581346088050100e94825800085071903101407426a0414110120100060003084c02031042c00513007104200d00318034801030141c0540c040c6040e12401001c5032010007814510743d0303644405a0300d16040d03108100d403400400c0d100b44920 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 967649649 1250 967648399 967648411
    0x230604061e32010308090d0c0810060e0718230904050c1c0c0303031505190609122004150e0402010f031b030b030f030705071e0503060c03 61
    0x124210300009190001103503200e0400c001c040060366607244081c81601c11005024205080031840b0f5403441d40e83c4030f1a0712481c0304050040c500450b0200900c034404409030003c3c01141d040d0350900c5001c64130507008280d17a00400b0107440f02c240203c0c000c035218a261152924050b191100d443d404d00700411403040c81c904290710b000388000040c003455203034406010b01440c0300c0e0000309460f07002d420401240440302490858046400d252142c04514140f13840d00460f034240c10005819203607811428802d4020b5004590001c4191002d50114001c030190007044410742d0380d440c4402038860504201111740110007034085807583c8000c1c01030048200d418207080c10300038000507413543c0000e5900001c00a96000d031103a2b00d1030900704000d558001d60740c420146154074042103d164a8a03101c254800c103035040e40100360340d400d188000c1da18108210010464010101e0b0f858603080d00d00260348105d18068800402485c451003100c280700000c0e45401d5441c014080e2400b551010b01c20030546d0002009 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 967650899 1250 967649649 967649681
    0x20f03011b03020c01050c03070f030905070308072906060f0904060323060c030f043f030b040209030c1003020405041401061e02120a11010606050723060406 69
    0x1204a540c0741e4045026114015440140e00e40d80000d2015085800041c094100c0e81410410006003a0b0b00c8583c040f48007246080015600c01a814514500b641940000f40305440c001101d00501032541d4048604021b80c99030244684031030040541080390aa03983d40d0004400e00110142119a001810b114140a013001504035a2500e8421140da54404030a4120703189a450440441e018040c2c1c644c016840303903401d80756050a604c1008130010091002d011000310705010300c02d00d101e14906503140c3e456294401410400e4036070302004000076600010200e40380402400c21410140242d40c1030328002009000c10f608280c061103040300b100401c60040580c20032000c030300c582e02d9210340506511000b02c1026658142000a40702050100840c100c0c100c000e81340c1c9003907603400515100440c000707405094641070032810544001e03c60000c03528540d402e000020580030b5000b0040c1c407009000380d61002034111203401c1c3d50704210711550014504d4001c100001c02054442d006850070f4428400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 967652149 1250 967650899 967650911
    0x106121b0504030b0a1107061a100306090614090c0c070315090312050906041509020909060601180f06081b07031d030106230307170a02010f031404020f0301 69
    0x5140380014154444000700d40301050502c2400351020320303550b2103401e40c1010007040d80c2e03d260203075003809080c0004104a441c0c0180d1b200c1d20020307400c10f003400e100c0500305141002d54010094090202c0740204daa4003841c0c00342c0090400d4156410700000d01c0082c246200340d031580d1602695580c0120a0814544100140040040c001000310105840c1c2160002000460351030000c04c1e1592055894051071b041000380400d4110100302240c0059021581004130030001d2040400f03458403880c0a90300036034020810000490110f4410b1040c00b00b42c2c1c8131000c5006003403000702d00341081d0041031801700040c1c01c2031007484e009189807030300900381002c105180e03500542d04500662120f2003c0b800205501005d0140c485224000300c2008400c8009000c42410100b032185c050320300c0c140705202041c100b603a000c20741d281403210384098141c0810b4003c0d081d4446008030f80c0c3d20310340f0004074000340356a403500141e40d110f48216541100e0040e0740900640320f9808100010698075002d80e815560b800d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 967653399 1250 967652149 967652171
    0x30c03030408010501061b0210210f05040203281209171e0d02030906072306180316031815020714030d0507232406040b010503010612 59
    0x40030700014640d41002062030360400100401d0300c030254240c010760706148900c12006a60300300042083c00c0b940d1400b00e00522840310a003461442c5040c0041100785029000c9100c8403054110030310460080c0c0450709842282d0402c51404a40031008014031190100030500142e03060f44040241d000a15001018a49986201d01d04400c0200190102e41c0042614442c0c10740d44060f04020600c035802500c840b80f01464040e4583c4039205411740b00b00310014008040020203040c3c020780c903085007240340c0c1c6060315910f01c13035444105454050050501102608040d100002103031101040c0d03d0003800d01001681d01030701c400300484140503c4202141d4082081081ca41c2c4c8443d2600c140da0081c05e820380b4000860700640b03c56441c86029401c2420212105500441283c1a0551000c0041c81d0540d541d008c0c982204141030b000020b0340100c0410700c4200342e203942003041c421498003040b642511040100720031174017004000341c01700d0800d20041100c0d601a100c0d9a0000e040107001055070f01c489 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 967654649 1250 967653399 967653403
    0xd0b07120f02090f0a0b0d020d0617060f0a050412111c0f090506030c0405100c06020c1005280f06081609110a05040306091e061e020f0d0209030c03 65
    0x400321510710700d07408940c201c010718145034896078000094406465050034100d102c0514400c142402d00c025400151420800c8029071000004180d200210f0007051041020301d03072543c505841007546100c54401181943c1030504c6141e0285610071017040903580180e006840140300b031f0a00b2411800382c07050340c04990752070308001240603031540d440d070f503c1c00e1111101500c1c180c61908942d00965040c002c114245512004030340076a40110b40800400d0240300f4100c0d6005906100140760b18000b154810b40048001801840f45008070424496540c0302100ea411502e40c28440d0882188100c0201003480117642c0724071003249807042c0109400f51110a501c4c5040d10139503980c0e18642881b641041081d00321300c00c00c6420110310007503d10304010031500600f54012070102400066540d1100e104200381c0455083c40d0501008049a4040d40750505800518112031100200b01030b8a034210058042e51080328540c0e5203046a550512801a81080c000c1d00490882038252041028440659400b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 967655899 1250 967654649 967654661
    0xf06060c37230123090307050709050f01120305090d020f0406060503010806130308070f230d110412080f04080f0f0f0d0e060307030f181b050d0b0712 66
    0xa406100301040b14103071103504120781d520004181d0745415080060f82482007a2400a59406000110300e030311100d040c1819441045001045841115800110800250001840b945100c048000c04e60390301c2c0d0200d1100040040002c00041c1c00b00700105039490104204140d03640050aa1200c2a034081c01150403241c180e080703000404d001000400c4103c0701040203c0d441490001d4411001c900e40c1e4018140381d1f00900a8818841c80250f401c1c541031203021105e26428401ca11034644028100101d21103030712000b00e00e01c115082200010121030848125012030f0006400851174540c680c81b201100c2d0061001018044400c2000041a150802c054000541051302a00421103194203103498180545c40c0e108081d003200303a0700c1e24143d410008030492040b0544a0641d07a40d1084411402004200303042e46805141075940160440c0c1d290700c5072400c40c481d40c40100030382941d60781e43d210301c6950f20400c0c2e40514980e1500340016240380080d900095076041c00c17400307403081920080a66803 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 967657149 1250 967655899 967655903
    0x30602030a0908040b0909011208040303050d24060206060102070321020c0a0303020114090a03141c0c0f0f030e070504021b061e0a180201081b030a02030f06060c37 72
    0x11010441c2e061915101f80c455004042601198107040c41366503d841f40e5020301c1c4000745c14060046020246240f050300041c1024511b00d5038540c00c0389131550800801d0095015290062141c0400600ca0754000078404041e2904540003142000483d000a0004031040e1a039004601035031150035001d40f520f90021024510940000c902554400d14a80481d0303001491b5030502d034441020310001c40d40106105502180e4409101e588164688401c10030200320309107071180b10715003100d184080764072000100703400000360b8a0180d0710013921001c80076900542c4403c4216007040c2010401444d169005041400c0111100500c140034027080c5824450300700e07114410420010a6480229032503908580d0060112604000b03425409080010300703041c0140003418000c1400c041001c2070302988111a00095100c00c0a03601e29020007010040d400688080c240d150990002c41d00301e10b0040251007802181800400142454484030640b0b803260349000183d091001c034058000b44810b03924422954 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 967658399 1250 967657149 967657169
    0xe0f0604050607020c1005181c050604060f0e060115020f070b041505161502190c0c08012f090402070809090916090b1503040b1519030602030a090804 66
    0x200e8110f40203400c0038071039480705104900e01c0b810b015030700307400205650121454004140c20020440040b855060400114010107a9420000010810f0002c0c0c8540714920941c024402c4071200c12140f010746202000300b82440d0400c000500401002a5204034201e4081c41111a180031010078103003899029000896540c4001801340400c1c8503185020010035807510b000792903c18421009842a01c0b1660001e154000c80400300511260607016100a02c500c0b000207100e020341d00c0006015058800c800321390a1007400c40000303403001c042c401c0500d00d6038110030515108580d0401251240e500d4032030484400340a109061458503244045c21860f88030301d1217030750365078025000c100c07090600420511055226800f80f42070001543c5d03481d012540f800380c0c0070854545920000f20309003144046203110b8100802040180700b180c03a9990700884100c12003442c0040c050b8244a80d405e004c0481300302039020070404100080450b030003141d011a85600004c0c0c900d0455840420390ba0083e88071880c40 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 967659649 1250 967658399 967658401
    0xc08070207050d03080a050718080c0108130305030606130801050403110114060105040506130b0304061b0903020d200901170115050a030f1b0806010f050103020903100e0f06040506 79
    0x8150100015005084100c2d0044540030300e07135400038401030005003402d00054607480803940b2280586564610507601501d0041e0090f160181c0300c1d1b03103151808019002843c408049004020300423400d01c03140f81c066541c60b2071642c0e090144450342e0300a181180c8488040c2000055a800a2145030b000303c0c8280c0d510868079043c0c03c0100d081d40d5003950b112240b40901000d014141c0c0c0c0040450f4100c2c4c4099a001c1e490b207004605441078210305900000109800104020802000b91b12582001c00900729543c125050034200320b4500205010080d048880300f4490070104e001d00440d1031007070044004001c0030110b440d0204010f16401c0c4d0108440c003c0a24210700013840a0185110800c06991744e68102403400700010aa808541f1003d0b004001e8a1001c0003402501c40e81c41d8809000b54400b04d89050345d603201c65139a58824411021881e0f80450b000c280356110340220307500c629008005103040c03240c00300507400038002094070b9080381c812621482403500e014089107115034041c501901c82 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 967660899 1250 967659649 967659661
    0x30408030c1c200a080613090c0b0705070b040303050702040b13020703030b0a080d020a02040905011b0c020f0f0d1101020c030d03060f050907090b03092b030c0306050d0b06130c08 79
    0x9075070f80381410000800a01022005643c0242d082d80d021100310b8515643c7c40c070500112008054100300900b03c031000245c0895100a508018000581710f00100c5101954800001ca81401240001400500100402c2d00586403941100c40b104500411180409080010000c2240e2081c44124080781d21040701501030b00d0300460b803400401584019041003410981c00a40f0b40c01d83c480c00a01c216569031410092100950000c00380c4018102c00b07182000c00b0b400043c1072080b548030101c0c402d0000e5200740c07499080140340040c400001401c030300902103055441e100c03400500c0c04070754118495001d81c0c400b0f9980c01c1001041030411501c000400908101031114000616044a40201401400d001d542e0782e02000c01405c660322100300603142c2c3c440c0164030b030402d400341c48291003841008103540500304144250f0038800e55a038508100c0c2c001081f40030340c242c44042c17140f164001c0707050300d0400102c0d2a40c00f1a50b40080e0082401e04c03b003583c40b40704403c03140080506c0c0000340c100c004002c8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 967662149 1250 967660899 967660931
    0x30507021207170334020c040e010204080d112404031214010b040504050a0203010303052a030f04140906010e130b0d060501050a06050903060406110c010c0519090b030408030c1c 78
    0x30f0b000200c9130a517032000307070a250301035500c0744140e01c00350049a0750104803000f46400e505580107040d0107400e0f00c0250403c0300009105500180a800c1c0500901030308080c000031003000d81d1440d072041c807420f80c104c0c5d607161016a4103901c0700c994100599103648442540c81001e548040c0a0301005030300549490404060100b2a100280b900020610402c014030100740c0210546007405240303403c255408410341c2081b402c80494940e00e02c258407001c1080e2803131120000250090f039070742c0400141c00742d124000304104500283c80040c0420804c040303072001410b02300e408110318481d0b81000709812a00070003040d012040e0750029101c040d5200f0042c061307850080d6421000303001c0e900c2c00c181007101a0000a1b100d010217440140319070f1b960044240030211010a4460f42c0c410400200070b00c7d03c05607c064a240e00150524142c181c0d0107041060042c0244079020540b40b040084500316650340e0f958480c0c551000d0203210810109000d0b040307981814010090208407040c4011610003e40e021040c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 967663399 1250 967662149 967662211
    0x5160b0a0f0c02010e070b09180702030d18020f060c1509010b0909120f03152101060b0c0a0602160f03030c1d3a0f120305070212071703 60
    0x404690408002a4030b0605c00101d07481558032100c0c046503111100c8001400b0601c08030411440401998100034000390040040c0c0030200d11158244004482000c200d5841031011400950141d0900704031480740c1014005018071403600d0f01190070324100d0043c070f1400403c0448540c2c3c45030391924481c01003414030540094110b10202e000700131080b4800c058442d6801004900d140007100070000510b661f400c202e042d11a040054408a0100787c0440b1948143c01700150785240756080802c001031503001d00c021a80c0141280016140280342039580390301035413005441d26280040800c001000c210b10004a42160340309807000210005c10000203416001d208071402e21000d0f0840003501d20ba110490308854428000050050301c012512900703240c4d00304801c0011807580204100c5040000321400b040d90140680101e0310030903180a0308030152003049070100c3c01600300100c4540803038516001b801c1d1243c8034142c030105510746604818100d170800c88103081d8990681461100c0030084807030103 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 967664649 1250 967663399 967663421
    0x8120c0d1121071b0507030b0a09020a050f030d0c0c0e0117070e061806011202040f03032a0b040f0b0c040603050934051e0319030e0105160b0a0f 64
    0x401440e10320009441c0000703003401c00f41c20100c03810304c01040003010b002d15406103a000d0030542540c200b24803444010000d45500320f0045500300c05c0440d0614182a83c004001001402041a2802940221825011018100c0e80054a02008561000303a0102c0c1400b82104541c81c0c4400417900e0f07007051070306403168801e598051150050040c2910350b100780c80181300c40e52046889039140e40d40100c4140082407c1c401c2ca03a480414046002d070781402508c0101c03030184c1c5c1c5a15000a13051046081007101700b50700390b01d070350600d500300002940b0340e05210703031041c000c240d0071650100b10f4568940640701111000592000000c06010064143c07251b036801c000401e005022401d030a01101215500e0310504800c041858500b1a00f00240301d0329100103480040d09400c030410101c0c00e5040d4114148980c284640603181d10f0501031541d45c2c051082290b0940d54581030307240103a0055413035a018030f04100d07413444400000300101d002862418041d680400c00002c4000818041000b1030700c0d41c80e05 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 967665899 1250 967664649 967664707
    0x30e07060305090601050907050909160201060b040f17030d0507081b03090d140c0f0607090608040803012306210a2c190b012108120c0d11 61
    0x9006411030005502e41c1903e1b810389500015072141041500c007800742c40000d9911086480400c000c80b0803034025880240019002400040e031100310b0b21410340560b0088400d0070315504030403c070003000318050740c88010142050f213180803021075a0b20b0540c7c030700311890008120301c101401340203005070444494074003040010a00b035041c90030560351a0124070400408014100e0640071503001410102c900c584144800c40d281001150001c1da10389c04100c4e0020701051151400040e41c83c000c100075840340d1b0303000245601d5613007412154000c6143da469080000030441c0c01039689178076090014039030303007062060701660365000d003080e1208410b0007043c0002c1d00f410f1000c1401c1405007520740c4645484620380d02d110306030010340041d1800c101a403450018111240001091011980119060301c0f01601c020004039205110728514803c001070040052804001c41003807440103042ca990458040c8480c2460410200c1c0c00c0b00a9800c2880c000b40941400141110b455031407170300c2c8605a000c1110 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 967667149 1250 967665899 967665901
    0x20406050702190f0f03120207030807031d0402070b0f0c0a051b1203100f09061401031802060c0309091515030915270c03030f07020a030c06030e07060305 68
    0x8008029015181009005880c3d09402d0500c0090411101025111058400c100b00e5550680341c1e007840e00a2100ba103100145100c0508014404101c031019641c00c6001e90386070007090782d4100c030b1904120101c0c40c01c0003e2480d802c0503981e2240010702c0658017550503441e19044c1102c6486000101904201260788100070040402d6013107c00e4900248841c503140110600e014152400c16501020300e00340184000100030f0031120211341750083d203c07012032010b00c83da02e40354545c0890f0482c0c0a5841020010b40417170340d041d0300c05d803c07181c80700c1d1a0f00a052800110f6502244582e04414510804d940010030b80369800e041040e5007507880000f44060800940320f480105448940344807003d040c0382d40000c00505802c2013040004990001c501000740b440c80c090f610843e5481000114548100401e00c0b4416281000280541602da004024501e0411004405000c561000404076007202100c1c1000001c80d803030078101001400c01da2004126040240290ba0038503505811090034189000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 967668399 1250 967667149 967667159
    0x910050702010e0a030c0b07140d03020406180e0a05130f0c092d050c0715061401050711090907050303030109020315090f15010509041503060e0111070206070204060b040e0f0a0204 79
    0x146c00d00444004448160755001c043c140040881101130355041a0310810ba080d02613554168020f1003150f0700c07503039031081d001010010000707402d00610584100400c0c0002040031907a0b1944100d811200d42590401c50b1200d954900040e02c5043e101600c0d03a2059080421034407046025090030316682c48144442c800800c118010703c20700394a807030340030280d48000007a880a8208215400f01da0800100b80f04803410070301e0381c80640041e000d400100010885d0398031642d40114162101598400600504051000180201c0c1e8000912000441c410110b0009494400340000d601a192800303015a49e8902014020340084060f2242c43c087c5070740e0002c02160303c400c40e410b20b0f04425a006819044010540100c4030740c05940d002d640d0144c9402480d000c6151b41c80c5050b801c43e44540300510012000707941e41c81c03c960078864000b0f400340e0f04029860052400d00003c208003807000703000080c030603140c1c0d0b5110301c25003158010702d0740080c07080103020b003184954485a0b072000f1074143c03d5141c02e00700 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 967669649 1250 967668399 967668413
    0x50a110d031b050a09140109030816021806030c0d03140406021006050114120a0906060e24011b020a0905010f03150c050a030902210d030b09010f060f050910050702010e0a03 76
    0x41c8140c6c6440d24012094102e641c1c850441c2500464014500540355581a401d6904201c8580c070201d210340940300d40c401c041e1003032044580c49000c00030007410305108454144009207051090803801c02c040114070031447c46214010700701900c078903401400b20304852a0920111215904818140b15906407150030b102c806504480541c5100390303135449161621041980980621140140050304089010500340c0002c0c0216201e166250003450141380003100034800d100c0d5064100340060001000c0300d1803d51141c100c622007901c040c00413080d00b651010b1050442d85e00303802c0702508901040003002801000a501199a2a00701c020805100b040c07001038400e201e4180701006058446001c00107654500c0240190f03603856030401803205400958240d220304a500d480c402081c901030902505040490201307058410209010b00300c10305202040e81c0075070300c10401d03100300072081201c0d05807510340c0405051800615140c0355160340007440098040504000154090111035000700045182 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 967670899 1250 967669649 967669667
    0x310611090a180608010609050403030c091a07110d14160803030109092a0513020705070e220804180506150f07051506030c010504060e01050a110d031b050a 68
    0xc05a58411140702090000001d0300f210303805038100354a041400980420180c0009114038401d80d81003220700c0e0040401e030f400310380d5801200e00841c251a004100d54468100a123089801141c1052650b01160300054450003d60011203e18000b0851418810b008000070703107550060a81d030105103401d0400a0341c0e40c0c0030511440100c10303103c0115000340113110400720421024110b020003407043c4c948d2507005100041c441c29026a030101325aa6004046100340d442595110024240c51881e1a00c1c00040742c4018082029543c0201c2c460201d06007500013015202e4800d005081d25103180c4618030070120369000007035003020700f00380030001203980303083c0c0d13141c20201c03102109602c1e110003881d940414094554010000d20030107c6030501481014142d52040000702d0840d10542c0341d09004541e140a0351140c0c0e03011070103040300000958002e90250145d03110034500081d41c10000144140380848071041c01c40400e649184480c01c000da900c0c0e800076145082d050180c90002107007001011411 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 967672149 1250 967670899 967670909
    0x140307140307170a0c0b070c0f0b0f010503010905030906030a02220e0606030f04030f020313090516032304020d060c0806040c0801152a0c0e090c18310611090a 70
    0x5a1000100e46902940300523018580080c40340c105030340c181c5811122200240c414680d0780c1c2c00c40303000003124030341401041c0c0349952003409542498015402c1c0401500080c0403800016020300c5070228030750103a0321061a0316080e002040703d1910740b03000f400509030040d201d0f074040d1740c041040100585869621581242d894500002d0000d2403410490560040c0aa1981d0401c4002000540384109400060050401e071225600090005500b41c040f1481c50310755a2021a00600801d0350316111820660320900180c101212489940c3d102d0044410404a4a0110780300005000c3e1034142441000c0d40205541400003655052442e1403a00d9480c5143e442c0c10030144161620082c0254240d81350041c8036a1500511a03007d442c106030302c0c10546c007035042c5220441d000100b41080000b04401002c1e0007030444682d80b5100c2d00c0b0481c03412001082c141131040100e0b40105040003c590010321140501b24203562600c6500d00300d002e0b0b031a82149000b01403000d000003005551f0703400540003102c2c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 967673399 1250 967672149 967672163
    0x9070f0609030b0651190e190602061806060105030406060b0703200106080316060f060e04170f040501050a0201090b1503010c0504140409020d051014010504020304030903140307140307170a0c 84
    0x100d0071800b01c5000e0300c00e03a00300d03404c00c4542d071600008036580d10541f400c1e09c1c003907001d4032940da8034007600c10400102c1000c0030745241c0c4200089030301c1e5400740b401140c220b400750a000c6030381a1a80101c0d1101e6214078411000140d00c00445243c3d4003401c14154002c01c1260005d12003035280a030078550b240a01c403400ca510031b1914000c0c1c01041001ea00030070b9040d03d490028006c0e00c0d0744401110941c4400c80b0b007a24100b80c1290741c04294204003040325a0868940340050030f107818140110b03600e0300081d410100359982c5040410104a090300030910401c02500006c1581150000340340c207591070030062501780401803201384138410702c607100380143c814103580016000c0440c6c00001c942200414014000d40a0f640480104050390b80042c400810840c0304418580d0b6610306010492004960241c0064403220003480007540b01c5040200e0000e64008036803c04606403102e602e400a007440e4100240e1000400c02d08014101614400c2d541d8004040e60604803401c40c003401c800c842c034000501d15 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 967674649 1250 967673399 967673437
    0x8061e01211103070e18010b1303051e07150c022704080304030e12030d0e250f050a051f05040e0403050309070f0609030b0651 56
    0x1100c4241500c415190380c964103120070201540032502d594029203558000039045035001081e8100088040e00046058501400e80d80ca04000184107070480c6802a01c4110450000004280c080100000040b0045143e400000003402440e07c0c080d40ca502c42d6490b8400000507400c00360b00407408110b1960142c404900d0300d03040d20f0260a680c110340c0086c1c250080d0325424401407205c100007451256102e505c42c0203154040d1070401c811190a03400d0501650b0041011030440340ca50f40128181510060448144030803808101c094403403011a0f80082c101801c4041080102e00103001000300702c00d942044001c0d0034000882c492070f5041c00d80d41200c03460322829441c070700d20a9044034000c042450250125040034600109194020f813440d030994403d242000c551200150140811100035803200441e15242d5910111070341c40c01030109a0080303407200300101c01c015003c030030076043c90f119001309180d00c1440010540840d0318404682c0100300c103407408105900100855024a40200c102404 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 967675899 1250 967674649 967674677
    0xf08100f140906040303050a06050a03060b041415030105150d020d030c12170f3903040302010e190201200a02041416080621120307020d08061e01 64
    0x9003900600d04124220403004100c510b10000c210140141c0c03190307030148019111403c0c41c40503200c090061581c8113420580c02c00005500c1d91240555140107800454415042100300840510458110031154065040c103ca2460b082c46140d5100b18640c4201000143c40c2011420208203200d00038050a071001c200e5083c58002c04209401c0d0303501c030694081407140208020441c40002e181c200010742c030b01001c2a20380b205484d50610441900007001c83d002c0120303d51074110015005080540000b403c0e44050380700a00005520544c003c0c0c0010645034051241c0e24a031108800003842c1c524044440c08006030383c0540303000c000d24a051115031070f20640407410f40c100f00301a94001d502520704418000e100703888802c4036204c1c04024440a203000700e1800203070744011003107078915440700328804410010307000e03030100b5050f181d4100101c801c510020340c80e4050590055640c200581d01011a120160358449001607100206a40b00780d246001200d2151a402070420480d05000c810685968 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 967677149 1250 967675899 967675901
    0x140c070f0c060e041a030a02010305100503010912080108241509130507080312010308070602040b07050a120e010807143a181412070506060a0f08100f 66
    0x190003078200e01e04440c0296680c0c4081c010760b10000c2c62600032420300e42041307807612035259011804000900506400045c943c01180108002002c09012032200e82c00070490b5202441082d00c164820205c8003c1040e01200c00360941005a11920056021800740086901c0d402e00c04d05c0c00340d68140c0000b80c1e50300c848448403804030b4428085604084007c0c00c001ca110310a03114082400e000d201501c03076607526604059100c0c81001100d020181080004000280c8000001d04019004003401420b198030781480c40907540c02898152a1540109400014890804c031110310418080c24036005800e40c2500107080360100800324014892100202161200018200e41000040503403950041c88011200c524200c24480c21140d03c450701c0c080e00d2500640d07403027120f100c3d03816082c54204107445a030f65025490082c5846203c40e025600701d50b09122810703400341800b50300c99030160a140c40c20744140151848158072030a00800901c2d4200450319000c24407081292500310042840030110300400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 967678399 1250 967677149 967677173
    0x30d090303032f0a3b030109060c080103060e011a130e160f0503011503080307020a0b0f0f0a0b0901140a1a030709080d0e101b140f01140c07 62
    0x5007100c0c503110540300d65a00d80f0402442d0084543d103811070380300100840c0004a141d80d00a500744003501c242c0b000d21683c0c0311103140c030313000c0002000841d00340000d03540c00c0c0c1a00c448441a0f8089a00c0600510400c00e00e4000c4801400a1701c00800150400c861040ba41d141c0480c0403901806a502300d94003c00c84580203800650000003c5401c00a5545c01c1040c3c841e503035100700b4000005100020510303140602800200c003004401d62086a403c40e294100c49500180c000c2d010345c4a0728540800288641c004503101e1203840c84500001c0c131300f0001d80c051a80c8020010b0241070319001100b03442d6500ca08029054600003011520b201d550b00002c28110b02d00c90f00310210018420465244024184005603c1005960b88000c0495503500109a45900550b22080887c1071151100c1442c205155a0401c01c4070b503203810b0122400c01e4940ca0110f00100303009484441c2c10800e078482c0704d1400c102c2059800b03801002007216081c0c13030290300c0245001078104004910005001d80c02c0c442c45e01151 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 967679649 1250 967678399 967678451
    0x6040506030c090c0901090905150103240f0e070323100513060302100206091515060a0e040c0509060412031701170706080705090d060204080709050105040b030d09030303 75
    0x40789040c10720004c840882c1d0018200070b40007600703060300454140707030314001d02c0d000c5c040020b01418175210b010015400b400488501c14455481c804004040c03001d001ca4400c005c00c00b500900300b020f07042c151805050b040042036881890308009030744003010202e5505502040000c010102c3c2c60315103101d14500741d40f00d5070215074050a2400c000d0326aa8003070340443d040300e00c00c86660100e00c11051040c1d80701c210803240b0b1504c1e500400f070055a0002c19080d4039901c07404031107503210003400590005819822090b850030000700e140b004400641824031911070300580f24240b1609110400c1d0005440344640c0c01500d40d802503220544040500412801031498a81c100304001507855000843c82d60030449000000c0c5e221f450f0000421a020341d46007401000b039a9156450502c100c0184508190a81c0c8125000da600b000005a1068140250303c0a4501468046529450041000180d40e40c15010718441e4002080f14812142c000000e039085076031600b0003003908143c070314014035051107075541 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 967680899 1250 967679649 967679659
    0x50a1407210212060307050a030b0703020903070f06120b0103020301050a120611070b0f010e0402060307111006080114010512151302040203010b1909030c330c020a080a0b06040506030c 81
    0x5031040305407050f00842d00c0340c8010b80c02c80303015554513001c008050000b44800342c0038070014400f090900d031080e0020800f040000e01203c110f103544044208289006501501c00100c403031a140030114500e01585210b201c0c24a0294115414a0005004900c2c1445084ea0342000c22400c5810001950050741d01d030308904540d1920f411050803c03026690717080321750541c0d244850002160803c0b54011032801250007a000f0f07406c40d6100311094641c0a942401515180b00d00b80200c01c20b81010f0050b84040c200d01c10001c52a4440300040b040c0545041c2c014901c60b5480c0e40905c0380d8030f4000101d10103c010030710780722421520390510002c030001400c500039420500000c008254100f440c030013001b80140108aa884a2000c20003c17100b00171680002041140c03107210400804100807201c6d40001d030441460792800600c0d0020381a007641d40303a8240d0200b902d00c2c48084c29490406560700c0144402c001405040c481a0359510300204007d1007144102c0c0d0764804958903440400882402ea000500 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 967682149 1250 967680899 967680907
    0xf0a170708010504110109081207020405070e130c0e090105180c0c0304060804020a090902090f07200109032d3504060f2003130b04080409050a14072102 67
    0x408a245e80104500b040c0418610703000040c00c2d807000280c042c9501032401d001130410746241c0c00c10024200151200040042040c0e2540950707941408802c0c44d014441c20011320580100c1300506003400d50ba40c09407040c0d44500040266880c4d010909091042414400d4029a1111101c4589003d0050b280c03040e8400860003084483d005400e060141e0700849080d4500d55580300d0a03400c2c0e4003007000c000d4008020750049100f07030818881180c2c2000850900110000d91045421023440c121071405599a46400760081410f4001c0d066041e015461503038100e1120072051044403400900c51b0150401000c410080d0301d503c280003507820304c003004151428601d40741c400e07038200301c1a060300e041c0c81141ca030840141110f1f05500c03c0c0314154020050030764980000f488440caa41c1c20040c8841300714034490404500142a40044501c2035210f81c110f00d0b2100c4c1094107060440d90010414265a441c00c2150700b0000400758025500000c00e00d000d1982e40e00091101c0414842c000319031613170300e002103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 967683399 1250 967682149 967682153
    0x1080a0c02070e01030b09011d030702010c150e03030406060b0c03071e0c06031e18020f0a0b0c0a0302010509071a07020a0b040602010207030e091e100e0f150f0a170708010504 77
    0x511070166801f078009100c5810500d154403044044001180000d40c420403002c80194041d4190010382406003181d4809110310038803038002d4803a84200c4010580001040204002880c41400040c046d285207041c2003402520b002c3e5503911581c0c1e0302424444400e80d941c809130345080304d96040d8907482010503480b140e480c1d030068064003601e00041c12200322085001350401c80351280c0d4140820403084000031a8260f0207111400344078030180d80c2c00c020840c901180721122000240000c0204000900c411565410300038210b800c003034807510b074907000300c0d08c100036004011624000c022200ca00c1c1e2643c030039083c4002508407820b54000802c00c180070030009001c036010b50103448414000c2c1c5500d002007003c18108801d81a0440d6424010b001001000900910315800c1c07692240e20741d40340c0f4010301c0d207524010301000d00407103024032202c10560802c002d8511111384a1500c0105448401000e030b59480015000304d001c4c0a14040e01d5a1a00b100c015260200505001000807600800050400b4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 967684649 1250 967683399 967683413
    0xa050f010903093b0f060f0a14060706060807030c060305040206041403150a1b08091b130608061b09150c07030f0b09060c0313020f01110d08090c0102010b01080a0c02070e0103 77
    0x2c4803200c110f0024107001403581d06114100000082c3d0081441c96101c0c10142c4062a01da91001118ac102c030301444203100162943c07003074070b000d000c0c0e404c014003401c0e256107071007071001402d60003c804140c02d0500344401600d0711003c0d2030641d01c103003000c1411400000e020a00d00800c1900c1c080341d103014279060000b01c03034413070b44417a04950311884041440001d01d04107a4041c082540c1069980d80003110b07039200b000000341111a0b0445c0103003006955032002c0d550303909441c540c0c0c1051800f034001000340002c4005401500b400c1002c08a6614280040500084c41800d42120040c0024100142c0841c1680090000304051035201b42c6c44c205100341c50400001c0341074200c480c04110300c03400740492a003440d22002d80344a01d655480141800c01c8941c01d02040249508515051003080014429100f0060002c8007240c4003071b40d03c80c580382c175080c0c00480c540350592035600d06591410040424999100c0d51243e07001e8030040b0080f0344100d801604070b2400e90340c0d50229051a03850720020040042c2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 967685899 1250 967684649 967684651
    0xb12030711301b0915010e0307030c0602010c0c03050a0c11060a1d0603060a060509042306040f0c0921060e10050702120403030305150901080a050f010903093b 70
    0x601c800c070f42c4a0724a8401d8801421a1800010340c844c5a16000951540044000c280000c034103141420070800c104011916140080d0411541031744900000d1001c030781d0922a81a000d4214580b00e4510700b56a00c010b4090310032001c0030b001b081000c00c02c04080c0400801300c1401840050b05107662000324074001090702e80140082e4080d03140041c00701c4154a425002d503030061100a003040304444ca0038500350b485a10030070149030059200c01141e0400da403205090024201c003032902c01d50910342801000202c8980e201d149070220303d1b01c0e80381c04503d680b054011003600c105542e52580305224611200750446a40402410796040c5075200301c00140c0030400205412401d070003031140740c807940401c0c7c1c0c40300519603806620030300500003000440e101350030140d0005080c56070040000044070100d0513500007604080030513402100781e501006006c02921a0460f90003000b002914110341d0014800510740c410394800310b02c462540c450044a1a40c030240e10754174007030744220442c041c06240e400450 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 967687149 1250 967685899 967685989
    0x403171602151809060a05271302010e0406060f050c010b0a120c0e090c13090c0609060f05040e060120060a0614010507050d030f1814010b12030711 65
    0x100307007064000d407070500c420300354040d0794010400c0b40007a0407c414011020909103081c0e41d0100e861091300007070310000313040c03a0280d1060710741659102c100f800050200341d540d403040e40c016031900404010455111a8260308181c003403a1059a501c14505c0f0a80034000c0507810070390103c0d8001d80080d000ca040c051041405114182c86030740b8039519800004d10340c3d0216460203498010f503015903124580602ca540e560951580c0001e9032002e252140040d42c0742c80d070001c2c804942d07903d0060001c03c0d00f00c0d402942c4034040d8640f181c5001d0500020b01d00b00400900410306011000341180c26100d25a6151070036030510108071641e6180400b003800c0580168800c03100004100010000366500c07500440e400035400c00000d0641c01d51281c1c0c224010018000002c01081ea03903044000381546081500ca8814040c0000410749500b4100c0c8500b12801070720a90300c64564600c2e0744554100101c10b0303401158000403064880c48502000c14130905c95941c4540400300305440b0100440614115270301c00300 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 967688399 1250 967687149 967687177
    0x6010807091e14010912020f0418110f06041d06060c060c0403030f09060c03182102270a09032102120708070c1506050405040302031905040317160215 66
    0x15443da005403030880c09401907410800582d0030782009420708980d11075420102500002d8032152004c4a440e4824114408840d241c403420b1401189190064841ca00464125400c0f460b05142c0b900c60020120000c24003030301c1c0069500000d01507138400741a51000084101610301c1450304046e80c00f41c60303100340411408103da05814a149520600e4114251181c1da02c450b0701c45040c5490503510007031410000000a2821000840c42c00e0300c880b00151003118418000c403021005204004100688180482c8660443d0681c4400c156848041c15046001044005103044c001e040482e0310183d528285250700c035a044198111000c568001c00109244072890141a1a94541140e0180c0180d6000c80080c404a5106011031691408524481c4032510001003850f690b001280981d882140c0030b0b000b42e000410300d074039051050302c04003268003964605145810305540c0c591116540011708407100d0b21010130780c8641103403585401d480480d0014054141582d00282c035a880b07034480700c0807201d80c1d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 967689649 1250 967688399 967688429
    0x2c01140d0212340b040f0b280306030b0901020c06071202190509031b220e010606050417031219090c03150b041104140a27050601080f06010807091e 65
    0x404040400c0e45c0984004000c3d8800c1c55180400940c20343c2c10681d0500d18110304080c1c504030016050007041102031040e200410240d186040002400100400f82c0000e640100402d60311100d02140b013a510100e141403e1140a844000ca003000703010b030703030390f136140e030b0300408212801468000300a4850018100d04545164072030084d03801035070050410716900701102c0840491107185000400f0034201040c0780018507103041e2065603007907401c950b11142c04624002000d0100b0034003102441411583c08009601d041c108084008000000501c0d950380d00400d078120818500246e0403c40c0c8980c0c12480300c1400d1303a00e03420052080608408020120761400c00b5003030003030505c2c1c040c801d485100680c14900300762800a12000d50801c001c8035a42c090340d01d42c1e02040c503060602c4a1810300c040c00ca506c0070b0b18503040180301c0454801600d0341d41403001e60820007540c400e0088001d0b60020003840c1020007a1107004080e20300d407507103400c0b0310200003542030018145440c41581300304441c407a281d2035241c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 967690899 1250 967689649 967689659
    0x22031205061804080307030e06010905090d020a0302030d02030a09050105070f09150e0402030a0b031b011d0f10030f0c0215060904030804060c0203042c01140d021234 73
    0x11800402c41a40c00b210500d50004010511007005190b102031a414007151000c0600b01e118181202600803258217070303840c001d10501c075004000d00700c2c100f0481c0c001810b0840850718007940d01e0013201e4000e814541c0010014000b002903401c1550841e6004009110074100700b04081c04800800c1201c0000807412000000c03041504901c44d400c4803030548810f07021201c49802d00000e58001407105803240c0c1c480e409500715480810250f001d500d5000e40c00040d804000000401203032003450800300b81000c000c8200032030380e61001d40220219045a0020481d8428081580074003030988020351130914000c20000072540104a07138040d42c1c0c103e807050b00c0340c3e9101030410800003002d4074045d00040340c450015001130921340c1f01501041c0e80e40122800d01c0e031798400d204800c8040200c140c0406a02403c502003004d000c00c600c6003d0081d2012951240241e4804156040c0900e040a4850007580d4413005034030b1401d200c1c1000c2103d9402002012442007191a42c81865006080d03054020b07540c00010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 967692149 1250 967690899 967690909
    0x60a1d211b0319020405041a070c0308070212090105180a260f030306060a1e03020403050c030105221b0f0f0b0a0207171903030501052b0201082203120506 68
    0x10142d0030f40301d601c81401c0034a409100081000030700440d407500d4001054034014503401e1a41d4450741090b80c03000306504c6245002841c81b640075041009543c805620030700c070f9070424801d0340c83d821070038a420398403550342c107840907600e040302028183c1002c810b54002c01c40c0c0c42055800711601085403550183c00c0000003a0580e6540e2501842c11799410910104840c1c3c07902d02c0003080c04010f170b490300c0c2c2c1c61000d40c0b00781407903495007000b12a40480d0340000c0403c00c00c1000e01c458040f14030110000c004130701d800d21814a04000c403481c109505440241c00a0401c030960780e081810b84048100c0012054450440350348030700442c06501d50104400400041c4000c40d0011200520015030281180c1da16000408002c024451803c040c03500801d008000e028600c8111040381038080d58021829501d0308003408030009409807450b8800c100c1c215003c000c1c0e5041c0c1d0490001960a28148030103503140107041c4850f819102d034000141102021070028190702003600303c410404032030304101a49681003000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 967693399 1250 967692149 967692163
    0x70806030c1917030f030106050702010e01022e06080a051e0d0e0f04060504051306050106180b0c0313030302010e010b010516032007030c080c060a1d211b03 69
    0x480d00005032030b400d1208803011101c4084a0300c61a040701d040038000c1c12a9240ea03082600514000b98011900600355a80000c014514410a00140c00041404031f00360096800c61001016203640340c1012402050050b402003000f0034134402580e00003800752820030303151001026071820101c104540201c07503410201d440011108135407182c501c5071000c9024401700300840119640d001e941e9a000241c141c0b1140580c034030484040180c41c031504d83c82e180070011244107820000400c06100384275014100d80003074001c1038441601035580c80304c004800803881c52103403440303c20500d009460f00000b0580c05401041c079080d0607600a000090022004451f18010710600d240308001b00d80840700424021f4000108600d4030b95010300031454850a140d10301081c1d540308841907001c3d0301041050803000d00420349041d4080317a04c80c3c940040c0e040c2c02020b07410607864110025403000070007100c683d00c000703140c0034801c52150081c07030219580f0300c142e860341c0701682c00f04405104071128480510b808140c1c1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 967694649 1250 967693399 967693429
    0x6050a050a0c0f0206030109020c0d030c021f0e1603050c010810050d1a01080f061602250302031006060f0201060312050a0905031501060f05043b070806030c 69
    0x1d04048045030202c402400b01002a43c10183c0d58a4480158035080011030181404c0c290241c0e5900508900a2a024000f8400b0381051314100f00c4a843c958080340354484841000c00005140c1d140305864001000c50040204251043c1080140c8840020f01c40e01d0450780580c059910311204140103451528080310304001c2009281c00c20b0185180c5401c42000ca00e005640ca940701c04291001c0780711002c3e007a00600020341c8a2598014207000c00c0004d2035106056001401240c0101000a944c0f03400200d0800030042400b03848030720403032407034400c2d00045800a08840301404103080d018020145802004002044003100c011ba4900500642044036846040d00581480c84542240c0b6a00082404002c12515502c0007440b84c0d4100502016552800100b0720b0340c1d4036180025202e00c1d48480d980c0103211041c8010050022a00d2500320702c03100307491040c882080300d1131000c0426920100340c00208000c0314240b01ca136951200400348948021360486442d03140000030400c80700d400e1a84 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 967695899 1250 967694649 967694657
    0x1e0b0118050d080705010e0a140106080a0c0b0a1e03091406041211010906020403060f0501050d2409080310030b01060c051b01020a0506040f060b0a030503070b060319051606050a 78
    0x1c00000307074110b001000c200e17002d040001441c4019295450030a107029005a8100301c044102c01c03150802842460001e1044d01c004015100040e0f84031641107000707114446106202003410110340b40a6002c42441e44600194040c0e10200c2060140040034045815610f515440c00c2c042c00c581e40000d0315a0207907401141c3c1d508810b148050448180300304011010041d5226250301001451074009400510701c60800810a007080d01c07a1001101c80580c00688650b961405003400718082c0c600c0014080c2d5403403a80d010020680c1049000762500b990f00500003000041001200072044070f04c402a2441814481c5d1140d82e29001111404041e60014050343c01206e03c40d400921010070f02e402d10300c410b005881c00d02c50b42d0340301c007810030f03204407010388a181d4004064410440c0900c256255420101c40703070200f103825525020343d64001e00b40f00900c1490b19a0124034586e83c10041020000c040d8481080c2c410100d24205807200c240d28004641c80300e41590210b0414062415101407102603a0703 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 967697149 1250 967695899 967695919
    0x6040e1b09280b161202030f0d05060103060b03160908030c030421050a1505061504030206031302040c0e030c09061005030c0c0102030a0902030c09070906030f1e0b011805 75
    0x10005200301511100e200b0000010001048a00b00300a04100c0034181010048503089003041d810340c0c507103c84030200719041004000c1403030b055901924440301c3c44e00c800042956a040045c1c000700f03103d412641840b280030080090040d0300c0000403010000542d03890360740903a102101c0c0c2d5039000e65030501029400a01050000d44480c06824802c081015103080b941c503040d444150604c0030b1a002699039600003004801c100d4102d019140d0009000d0b86c0401540f058001004901d00490200a210f0200000410b020416507402c4154035500200100491036003408060100c051000c0090301034001c1e1804001c091900781d0f5550f00c00c442c013600303507124520402c4040b50070b980020441360f00690140200100d00a00f4400765103d1170791100000307246035050041601d440c0001c010a8441d20411042020103a84045501c0c22030f81c003400c002c030781a01c14420341e001900f50300c1c09000f072014040d068011403001d160400d16250000781c03145503140301d502d421070301850307801d0154680080f0854 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 967698399 1250 967697149 967697179
    0x503010f0f0c0305071d010e150310060801060801031101030e010e300d020318011a15070c051207080604110103200f03070c02041503060515030a140c06040e1b09 71
    0x10108010243c4140b6000c00c2355007007000002c05200945182102010300441041203d0b07081c04005009000141822045980b4101005105800500004011051411400045900a8120151400f00440288481c0c0102c0b60b4843d55484014504002113558440c018221184440c02022507a074000003a0f142482d140d20f404007039800074182c2c1303811700013401780100200400e01c0340d0302c1e409044454810448401030104040740d00c0f07644611621840c00c001d54400240c4070a62441261000da0740c1c800c4402c407400c00d8a080c40a00d41c030030040750080078104010071038424000004c0340f009803020400711081c1d01205845600c214540c42d800030003041140e0b000380c0520302860f0b00100e40e141c0482030b0140396010501f40d80c184c090703079160703d180080c01303000300711950181c00c1d0300200c1010000441185a40000e50304d82011401a041c1c1d0241101d14440400620454bc0e0185024000654880e640c015806400404645403040e100e40c03080d48a40b4071305e0380070444611040c01003e0038040705000d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 967699649 1250 967698399 967698437
    0x50a1202030a0221060a050f070c02061909050907030c020d180512010b0f040203070903021302040b0a0f0221031503070807060203071406011a0309070503010f0f0c030507 75
    0x102050340e05120381070300380005a480d46124000c1a11032200018800020303002c852030500064962a566402e0804202d990651506c01a80c410341902d03000c2c00b00501c0c1d00109811f4407030700d06918510402034441800d2550014020812900c0030354116680c1e68450008604484150000c180103800006140740c80910541c03010303150b00c001900a18030150782c2c5000408401404203440d05994481c02143c000f4a80800a00140346013981c00b94a1840d20f2040180002020b0000034407506c108030100c424040b0590654000e40350407200b2541d142c03c0c3c103402404070000d484e4403c0c0144690350350300c000001d141e2602c410003008802444c0c1103842e2411803080f1155124480c86c0c0520410328001900c0303000300450f400518058000c1d540d40c41840c104814501c4002d07403890180e03400200108032025000c00d102c0315075118196415101d894043d2a1800c2c69071541c4042d60640c00e05588100c00c04180e8400c0d58a80c2020f141003001e1904000140d050f0f40c4201d40304d101064406040110032441c2d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 967700899 1250 967699649 967699679
    0x9120305071721070f0e09011511060414060109060b030a1e0f0209010914030a080313051f051f060e010203210f090f03070f0606170a1b050a 62
    0xc1c0070b580e903052a401c001540f14520b490040c064820818206004440f60848108200b1103024580502da070031203600483c1149034113206034070824215045910070f80340b16005150f9031940440075614582058203040511a503d05100080c90040760000640001d5501c6a0340403116440c01c218119aa594010302c000d0422001c04040480e00d0344034401c400000d1304c46d502510400d100016181c808200005020843d1a001401148513810b501e42c2265000107107000c58540c03020050356282d0b96200428103a07115100014858400c0d20800c003401424030104c100020314600041210f40d40f01c5d81180d0100c4007041d00348603d807401c5003050040c140300d00500c06002c80e060040b42d1a0284030004400e090b4060742c04600c2c031402d14402c0c080e4070004c0071400e0350023210000051501c404010881031f2244103840300106000415242c140421609420550040c040204c5600091410151140e1220300041023100e0207814810092000766940141200342c07003010303040310b4800d800c11190303110142d2 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 967702149 1250 967700899 967700933
    0x2061f0e100306020310090510030506060906060702030d02010f11041508060312041403010c1430090a03020705031b01030e070e010305030c070801090f06050709081009030912030507 80
    0x606000100114020380025801b4094604407600344d10310b4481030008898000e40030744002400c2c800104003150300054166000102141d0b00c10f9540c80c0e00000900350f02c035800009403d0301490302541c01064042d4032101080070f1100f003c0c070041040c1d2141e0003951166014950805403c103500c1c0300c625101700c5540d0360101002d4220341030b22201440c40c0301160420b500058201d00b005030341d008070381028083c03035400d0140c5003040019200140350480960081801c02507414003420741c5104014040d407948640b60151411002c1a0f0034001c10710358403420300950950151040b0030300040c0034280007c079000c008a1250000030741c403a1000045014000000c100c40c0b0328422407801045680f006680c682c001c510620082d40d84c0d1490610300350519000c3d5201c100907034500301001022603100300d040c4081941c4680000b0301a40c0ba040142c40344034845c0c00c4461030380f085500000c1c14040961103001c07014042d071680113802d699078005540440007000020001001404490005481c000500c20048 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 967703399 1250 967702149 967702171
    0x31f0b090103024903021903090605030406110a0801170604030e01050a05070204230a060f12140106090f0b06071e1a0f040c0b1305010516060f05010602061f0e 70
    0x6080340f0024502c000d0116503a500c0f1540f2413a0402c1016010800150310400501c0704c010648080e440150014080d482005c0c140500000020308203e0030354480b6040c0c104900350552a0340c05074500401200303003400343e440212103d4441c91098040011014402c80c0d16550300c0030940103030801107460380c00c050031b00001c1c804203101a00040e0754a009070580d80b100b030a04450b580e0f0801801c02c504040240013030822611300401804504030101c00b18040e94078000b003190000c0d5003031605001d0308090420941565103041d03401314460b1480e4028142c4111290070504c0306203040d404006983c45001002406078400d904500c14076205c0c0e034000b200c40c5004848a11008801c800c09804607601180e051002001c17610230030041110341c0600c81d01800c5400c40703203410482e81c0f0920003404143d0f40685410300c41c0100b440c4501c03071280e5564030180c0f944403000b44a0800c2c5171118071301401080c0600d00150103184002460311000701750b082010090075018a44040c0b030714510162201e400780c00c00c3e07445 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 967704649 1250 967703399 967703479
    0x3043209070e120106081c1b03050f070b090706090501020106181802030604050a020307090614010c080f040b09090901020f03011701110309060402031519020904020405031f0b09010302 81
    0x70100c05e128150051041002070301c1003800449164078141d8040340f00a0a00640482264080061a20300c000d0785606040550707803100846580700303c074000c1850007030135920800f0400404800c0030a2000445802d0384841c440a41c40e200168241d59040c0036a22045035022181032403054181c20608620214880c0700700846025001f00b41131610484094550361b1003010a4021030904108c0a401080c101908121442c00c0921a10b02c290b00b46141d54104240903481c041400700c0300742210380105d58800c800f5a11940c03080f2852003074220710126485500880300203440503c06000300c513218050a51301501e160f0030321030280041c040140c80d5807807540d6105626081650311600850040c1030000040c0298074003841003600d06034002c6a800c22543d581e00a10400e60003981c011020001c0c0c0c1240540c403105494003107402030199500140e4148911a070700d03c40e65584040180e603503140b8400510020f200e9905011423041d0a10000b034100d428103407000070303091180f24100c840801c030300b17400150 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 967705899 1250 967704649 967704679
    0x60803220312020d0e031506040f0f060f03210807050f0909040605012103050901051806030109020c0f0307030c15200c07091e0507050c03043209070e 66
    0x1c2c01c12a5058802580c4848030351aa1a0780046280c0c080d40022002040507587c03025401140240c058000342c0141e403241190101840203030491041c01901070001c1100075950300c1d8401d00c0b500d0130b1200ba00e170b05d040c000012002131a0400b241c400c002c1d86480c0c0c032989441c0c6410884980e03028401030810b4240038440030100740d807010002ca010310300981c3c011440354141050848054031820f0103400490203200c0310000290400240d0340500c03402d082058a5103003950340039081c08003885116a01c48000000410103100a038050110307804008101d80c2110500c444e4595244906000980803c4080010100141c14290080c0c00e45c281150049141c0650509003614094040e071160f406407801308000b07070302e05400c101840040c0300d00306080c03200b0b507400c03014103150f10008040701440d182c5880c0010280d034094011141d40f40d0702442101e680d0b5564582d01c4c401c18203a05555124068801da2004075402c80c0b101030400340f00002c0081c00c03540c50700207069801e000302c0881c858000d9804400c40030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 967707149 1250 967705899 967705913
    0x140705070605031005010f171b1605010b1e060a1103130305060903040b030c03060a03050a030e15030903030a1a0d030201020903250e2203020d120608032203 69
    0x20041c81140c481c280c0300d0414490b810350f82d0655801c840d0402c444540352801295100700d03090f01c8011400440c2c3c0c8540c030781100303068100785403840d54035221074002011070100e0858900340c525540600000c11070320303014001304804000070340c0303507841080314a1120001520304400140a2407225017043c030304c2d4220a601c0710f4116004400082480d0480460400c01d000e014002142c1c041c4001c00650b14050428490990b60b00020b03004020400340800040c01e15180c0d0b4882e5030166030007900319203000109180c02030001c0403420706240140f82450030018200c4920055a02400409001c1c0d4215500d2480040003410784d080c48054000202121540031346580d14410040c60007a8000f5170b0b9103680d841414a000300007007056421100200007411540380308407011f0251010218045180d484034104a503889000d404150010b00b400c0300c0040c105a00003c806a0500cbe051711400341860801007903d0031076107a4800e4905540007001074010340012f50080c00222400800307005a016100d441d160 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 967708399 1250 967707149 967707163
    0x90b0a09030b0915010b2b06030204020304080d0b09040f031101090210200705031504082502010e030a0b13020102150109060501020628020f070f030207061106040c0501140705 77
    0x6400215014202c004104c004a0140520b11041450051400d6000d121042c404100181111f41c01208001d03010b0260031010081d500108199124201424800b64a82c0090020710303009190182c08002d40c1491080288181d03009100440f42c55007a46040e12415400741e41000d242d540d504000e001a910a036080520216561f00e44110551101c610049800000c0c05d003049a809284c0400c207541e800034030410700540c030304c03060b8036562070741c0c9060319041c040d00c00d03512849521400e02540a85600c8a581850b034000d03a102c0600154007130034551110a20007000e02034058920004203003508d03020009028a01c1841214200b075241c580140d010302081e0005607540391194010003d540e4100720254001e1082c51440d6911030301c52200c040d010710400703400c10301d45401186084851048400759030180b134100d020303403181d422140f81c02034540500c0d020b0700000ca6525200201c03c818000784880c4503d52001d4150310042c24080107456046c0142d41881011101308900c0c030000714117100302c6c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 967709649 1250 967708399 967708411
    0x5130f060b10030603021003200406051234090504150e25120204081501060206010603090c050904020d0f050d0e060703080609220302060421090b0a09030b 68
    0x208007a0180c2080510382501c54560109401e00d2070500259541100310043e510440c1400284506450391401c0e807006501d450041c242030200d00002d1075500140101941550344640009941e900041d00d4800c0d680c0281c102d0640481e5210fa121000c030302d518140500300c050800c00c18035030b6210002000c4c0c0704000d040d8405500b03400b100700250300c18492215001801c0710b6140c248041d0b0100784054a141305800c003820082100300c550198102c40e0b04840190486000b034a401261081082150800a20034040107100751400003a50394404d12a0201060380310b100d50301c06074504403c1201070700024205a9114159041e040009002d484458a550303214601030500c0c80041000984400c02c13491409002d50000c02030710b40000d40c80400d8940c084401c442e41d16458071000034400c1e100c40000c0038024000c25610a28050540002c1c68600c124860030031300d5030006926400c0c00414803c40400408500c0d000814800050781c4070103045110414902004415600d0b120121840425611 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 967710899 1250 967709649 967709651
    0xf091e08010f020f0703180e0406200309191a0f01062a120e040c05040810200a12020f071208091e07090e061905060307060305130f06 59
    0x1081048800c0c0205281c02c0c01881046082640a5100c1c540c0b0b803146410060411400710000141081007141c0d0300e026084c50092103455141510b40310f80101128022a00103100500140f40c1030160b403400c5034810003807400904042010441484140c401c0740c80c2c1281e0035002000c400402251070141c503446a80e64507003100c6103525090000e0034181020024003502c402420404111606406010800c95880b824015075118a03010032904c0c1e0304041e600359800303800c00c4042c1401356070240160041ea40c09005882521000e604120102c507003500c8480c0c4000205203d6401503032003400a08490b01150400401d540a01e48030b0740103d82c4200420900c0d040c011035080248240650030b003103140c00382c0c2056201030415507051030b40c030721552030707880003610000500d03010f442d90522902c0c00800494100b40700c561540d000796900d403a021180c01e814044010201c01201c0100d00400d402040050086e110305800d00e4000c6020b0300d0300806604105042904c0c000008000c4c06501b08500d0107558 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 967712149 1250 967710899 967710959
    0x6020d0921080f0621060f070e06031e090f03120a0b010809060109020904090c1d06011706011b1b170f0c12070f06180605030106020a030f09 62
    0x141c4415400800300c9120204a04101002a4a151803d10303540050080b5100c5640c0c1c02c8000c4c02004014420945203054003c500030f00603002e160700103941c000c0707010340c440c1d42031081c1400500031079000440711514010400c0b0041841d01c0f1264646640101030507041d1040c0d8150302c042c06241d644142c1c50303480c48882c144200300b007c2219226007000748809103000c00712800d0040a485d9030794818000e405800d40d00140d61103480c1e0b41c1e680204c5c560769000b100c2d05200c941c0c0380c20b1820024010251880100305c1c4d8400515035600c50840a2031100840c0000f8407151100801100e1010b005030582580003609001c0d000482d201c034000c0b8140c2c612010f42210418184403002c0b00001c11300e90702e40c1c480e40c801d901ea040030010120300c10303180c54816100d5210100504502c5d42c6441803a03840300b91652207454010958590041e07070111001c00e00400a1034680c4d1300c0008503600c4c4424460711005070080141000040e200d400200c0c0140780e10314114100640365401c04052800407840c0b1802c0010710a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 967713399 1250 967712149 967712183
    0x30507031401180201121509060b090f0402121620010c09090b010905011d040216051b090f180d030209011103190c142a0904080904020706020d09 64
    0x10007040c03c0c108204414180715803c1d0750028107540080c40b1a501d2150310b9158001c8048802d04510b0014804d03c0420300900d5a1164895459404a0600750148080542d802128201802182c48d0b180110759010065980e0f46010a10103040c6034041c030400100501c0038100d45d142032020343c6c0507101d00c000024030114840000e01008001c1d0310074103059007411001d80c040ea0b08800042c086400030b08101d0052402010600115240760300070326402403000c02e91a6608502c0401140701e01c0c071030021580042584d48061141d00d000004a9500c440c282d800680c42d00d4002842c075822541d40804407207242c420500c1e80c0e040c520000d407500c0000e68041000b03034081d80c0c8910b44400e412844c1001d18a450b0000e90300e98240015a11800d080c0100c2420910403c956410101088070341e40c4180d41d2a03512100050700054810541c18102c1d030341410031031080d85403030040d550040d503114030014580b40e01d00061001035004208240c0340d4075800d2026960f841c9070390142d2503805205004144400a0380 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 967714649 1250 967713399 967713401
    0x10230d150b0f0102060106030c0318030206040312050f01060c1410051e190b0303040b0c0d1707080411040921020f0304060813021f1e0234030507031401 67
    0x103440c450301c9102e0700b00c01c003a01031360046442c0381034400c14035010568001640341a80a09140100075403640c140c00007440030316501103000b60080b44a542c2e107507010100d864050040d03039400c1d549900c00180a100400060b0700480e0009105849020b4280303d5000d40c0320944c0c00c00c016201440c01840d1602c0c1006260b1011058555402c1c12030144040181046d0300c4400d42980c0e5010700021880d92000301038015541002130360020058000c07941d03034a019101d01b903522420070042c51000301f2560078a2441800040b01e885118000c59920016503988036260007a500350326100668009070b0780c101110104110300d814241c0b02c084c40080e1203418000b484024a0000311000780c1c2c0e00f6400510060040da035200110300d4000745c090108503c001040d00000c0c0804900d02c1011880c04068210301c15a01c0c3c01a5102590714051a401c4140030390b070700400c2e83c48440c07107515891400c0240d08503585003816840d509040c5a4500c00075070107103490740d4800f8903280668000382c1d19841c40c0740e8000e10700002 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 967715899 1250 967714649 967714661
    0xc0e2211040e01020a170709030f0809130608150414070b04030506060d03081b0f040e0a0c020102130b0c0304030501020c150a0b06091201112703030310230d15 70
    0x401008500d070064000000300448109800c0303840c8951b019001c40d40651007044002c01a640040d000c0345103c8141c507004500c0e900c46103546014003141c500d40c2c2030041007172042d4002c9404500141c1100106c0e0300c052420741000a00482d14280d044407103003a000c1d0200300e000050320030006219521405d45c20f125151980017480144111180a424800207500c101c92540040003180c481d9681201030b130b10b81800d8081c04011620504002c030380058800e0884807420701426030154100040410306004070709074072a0075071554901e07048010400040c016003008017115204542079034140b44c0c4940d155400d903440001040c0f9183d200d0003540802e40c0d03200030090f4001c0048202005521354040c0425141d02440205910500b5a03600003810881c2c00c0d0007080c00a10391140302035035103800e42c69196801980c0c140182966080400c03d100a017400801c0302e0103582e0740c01000900500e8041c98039083c154011440038110124104401c55865000c5c0014030940b00324070460518076043c1c2c4120807611 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 967717149 1250 967715899 967715921
    0x60f031220120903060f090c010815040f060e07080403021e01061809020111070302031b01030e0604031e0e0a0510120f09151419090206040b0408060903070c0e221104 73
    0x43d040140020031f000081e006032060130a0810544550319030084c6070004d26031201407070304641441c03030604ca5201d40354402e4054404544ca651202d0320303a80801c8450f0402214024096409907425284200d81d446419400b114424004071700c1a40740d50885829060360400c4000842c2c4817024141150b0300503400c0090440650001c0500d05d26580000341d444c480c00c0038440300800b101c1d001d0540b9034880d8015240e82d803100c5086030314509051070010301c7da41802c411900b14407403241c000c55255100320a101c0040c000280484003c5040c80c3c10850101606c4500c1c00602040c3e20107403044c2c1c00700b80a40d02004607200c40c00209001c4a041160704c14030ac40340c01c508100e00d4145078110740c0100c20401c4da0840c00e849450314450007040280b0000708405000039521031408100010a411035100a1050315002c1041e1201603c1d0600000c1e501c2c0140d0034002c203000e480d0181802804030003403007241c4c00041c0f055241c00c840c64a02c0c00f002001c0740b04d442034510013003d1110300c500d03040c540075003031800c4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 967718399 1250 967717149 967717171
    0x30b060c010e0f1e070302010507020a0503010513030e0a0e010b0c0721030f0804051b030c030109080d06060801080d11011b030209090f06150f070b10060201060f03122012090306 78
    0x355000e07244c079840d440c0d940802414800e01090050554a40b008040046e01d4054001c004505211a05500310003c0c40c6003203001038004982d00d54075040007000081120120304180ea426400c009545e455038100030b4928035103104030800000d80027140c40c00f0001c45c50b04a1154419070b0244d041c01002d0411000d481c42c1444460310602c4005070f000a850080140200c200381800000341c1c0000b403c003408a19242da1540c03c007800c8900380b11501000707000c86908920100f01c29a034030407060355106400d2056014940258414907080d600920594421080440002030300001c01c2440e040102c803a510903000181d804504440f80703040003541140c02643e44c40c1c1c141414507010001541c040c801034500c002144020407144616501035090780d10a41c2d0001e0b02d0b911515240c545415902214842c0a0066003060800121400725407410400d59802c030410101e1110096402d5070b60300b0b50040d551807540303c0700b901c1c400c16110a0060a640040101c0200da660044508040c500400035028402c02 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 967719649 1250 967718399 967718443
    0x271106041e08120316031d101b23040f12141b011107091107021005030106050703050a1b120e090108031806040f0f0906150f030b060c010e0f 62
    0x1803051001344c07944100b241d20181180c2e60781036421006030020040500810400e00c41224107403401103034010465128031340c02c00400e48c003122401e2401012582c1c00340800e1091050b803030f10710422141e0086203825080c82c1e80ca050746c2c406080100102c2940201194902e441059041003203181410140300011310040c195a40c4c89004500445c3c072030144641401200e05228502100901c000c0c2b00500740844208003181c40d10301000450b034400c0340204d11400c0c1d4a44030b04403041c001c00c01d032810395007165a01420300810f640e080c2e030f09500c0390581800780100c00402e01110342000c0c1c040740080384202d5005a800c840d082c1c02400d0030415404d054451703012040140049817002082d11106845850703004a40500c107800300d83d940c421500440c030a4211201c02040385042c01d0400c0301240c0c070304001006441c1e5142c0100220b5400300798a0000034400300350000802d4400e804c0348440450041c54145030010b610300a500b144d21410000e043e030340255201c451300410a11007d440c2d1261002c0782045 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 967720899 1250 967719649 967719673
    0x180f05070614031042030606020304060909050c0405040509010b130c14030411060304030914060a0806151b07050f030616120b0612060f04271106041e08 67
    0x1055541d80100f021883d110f1018101c4250040900ca4006441e100021110f42803103c074a180c40c0703402c91505c3c01280c200240000c1543c030001c200c030125071140d071700c00768000d0030551480f000d41b601400d4404206420300006c0341d66900c0384034560240100c000001070401c510b005011a00b5071000c4a0325009240c403c005d04030a4210740780d90995040c9040c103d691b03035030340e19100303189200b280103e0b078011001100300010140c00107803440940c0c014841ca130040b00c0702a404c100042c0300380104400003038406008941c03141171541031407800101c4564141d040002c0e24240b00d0001c01e00d0315040459502000080200d418403020340407024106030041c0129187c05264120703c17281000d20782080080d40c460424046140ea400305445d8000103011968131003a420100b03c281c0015900b440c49900092100481c0e441c040c0b140c03031810030051b040d403c00300c240350310441180044404255505083c2c081000d08542c4e5290040000c0c050b5100c04002100144800c83c41000c07454111000d030754000800d11768 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 967722149 1250 967720899 967720921
    0x90c0507031412041a010e19020706110f090406051c0b07020a0f03030606110a051b0307090603061508010504080d110c07060915051804180f0507061403 67
    0x44907509410118110b12010310048640d00c503201c4072094050036401480200014003a0b507114034009100c070a020b81c2d889801e18540c1c00416a1524070100307610045043c19000c0342c004e800664055500000c7e41a84c00540d00d04980c810b189001c2060000144035525280c54490310700508415078132a003510b4a04e824840000d18114800303070003d1000000201c2051080000f82d03000d580c4000f14071b6858501d440c002d0081d0a2070f01134480402e0341d0001d2010090400a02c004003560403d0040040900002003400344540520415030140034864001ca40c2d4003880c0210001144100c4000403650301c0f112480c481f20400f0f8000c2560369040c003052101260600042c0d5050540c004000604181c2c28464500f09215940500b845030160780b9001862a070407404400c02c03207000800344454110a01f10485061040685400c0c5070701c003410358500c81d824a9030024144102c1041030348045503054540014003042208200d4003944050424043c041c0e0014009d91200300c41c104039401c500b0102d607144 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 967723399 1250 967722149 967722157
    0xe040c0914151902150a0507140a0909050426031e0a0615020a02010201180203030d020a020f0a14010b01090803070201030906020906041e06050307050d09050703081210090c05 77
    0x184221035a0410b98012100e14040303d0480490142200d207003a600040a51103c1031a03080e1520003420b0000501858414080e280c4100f4040d0b41d40038203201c0c2e40c482001540c001c01641001c011140d46d000c6000c0c4110300c10240124001e043c0003001d000c21403080b126201e003003201d082443c40c0c1401848000e03401c124014080700c81f00f10900085aa489041c10010001031348851800b0141c22000c0080c039030007243c00380d031403030003a4003e01c40200d402c05100220509828002d40540c01040000342e0ba61040d03000d09196166841a110b101c460b00f48480e00c2c00110020a9414952103101204204030900c208480c0c0b079001e00303003c1c090074500303240d2039207034080d0b83e030301078181a02c2d49440c0d0300700302203541140d0b0301000081c10191201e49500440c41e0320b05004548008a00612101040c100d0142c416a8442e18803507031590310f420702651401c40509a2402e085076584244c403030101c00240040050500c1a0050309840e01b43e10f400782d044040208103070300c06988646003c030010b0446a0080c225 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 967724649 1250 967723399 967723439
    0x2070807090b01030f06060e090c160303090501060b072a03030e040923150f040209040327151b020604091104030503040929030d0e01021005070e040c09 67
    0x2400c4040b8000603000303800c1c0481c4143c1c40300c0c58034101103691500501e98024140d000d442c0c07103000303503210090700d2007074411f00240c1400d2100484000000911942200062901c101d0011614507a140310420f440d401c220421201c1c15207144c10300b060804240b001280356454101501411445c545000c0c0080c0354060059020f0741c0c032001c80c54180100706500e041c5601030a101c103040c8040300c82c0ca0549441c03000f50b000c0702c1388004d80003007100030016410560040b0380041018105489035901a2084200c84081451292100c0340d624051182d60f0480300081c1401d00304903184845480000b084171000100805941d5444140140943c44640517201030314841c1c08000ba40001e14030a15095000b281d00050044c0300000f80490000352a4004158201c40441ca00c100016200780fa083c0300003041100c02c1c1c1541c89083c22742c5a0f41d108403a007030040320f01801605c50f01082c0f408a08280c0d00100c40c02004111058035618803070400c3c2c412102d0702a80c918025145904125145140c04802030035 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 967725899 1250 967724649 967724651
    0xf2601060b041815090c0906031a0405071106041a1806010b0a050702130f150b070609080c0a050c130207051009020604182301060e0d1b140a060207080709 68
    0x30a02405409500c8002071400006100b00055900c0883c0000342080c145401b0015a044100154003402809941f504072101c2c08100c0d00c0000c0c0000740001081b0081109042000742c0700e10f0f2504000030322200c1d01890107880c1c84d4007501d00102d10b1004050020744880310a1381e01c0d036130310611400045009415a61102c451560383c031029a011125400f43d040040d40c02100484c1c0c508005646912000000d888880c00780a91800203808001c082e1a40c82041c10080080250000007501c650180e1840c0d4442c200389801c219851021601e00745081c0300c01c80b11588064106e038203e00c2c2c02c48160807600c451020a42c5012003d13030301c160f2204101c0401410740b545840c002ca04540d11036080d2806800c03500f00c020060320400c079060700a4040500e401000051080040c0402c045001e00103050b60b203207858451040000e8414850a08450702082d506213121034040c8868207800f40f074a1006005142c14070491260250821000d0103031270780000103650040c001004a4200403500504a41210710 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 967727149 1250 967725899 967725929
    0x803070e0102120406050418020f070305030c070b0a140a150e060d02060307200d1e18060f110f06070c0c03060203071e32040f2601060b04 61
    0x50f4a00402c0005000a840000c0341c08520b003540314002d0001c44034070b01c90300ba2038940b24a40c507034100d00c0790200c45075240704104100f0f00030900a03002150010000040249000d81d16102c10625480c01c2c0e846040d00c64441c0d20100310000351041c015044900b0034070800c14401c03e504981d40c460003610a84042c003050000161040e0783d1901c413000000d8002e44070b55601e150509000780a00b80c403500070030444450845041c0b61301400203451002600c1d944500343e059420010910382c4030142c42d5a80208403111001181c0c01c280d101c20a00145800d44800303104807580a0083d1208480e41c00942c0142d000140c0c1542c2040300050b15900307c0241d00341401c100e009410115411040c5800181a103400001842000ca0b48031020b031103108003c0584c905088200b107000c03075041142102e04007600c0000c00300c04040b0981c0e807200d14204c42c00e030141c0720700c0e10390b49100340100c0c1038090b4488503054411914408401400c12075401040e004c1600802140c0d0034421030b100039000e18025685c212007408 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 967728399 1250 967727149 967727177
    0xf0f0d05071d040201080c0a020a060b040209040603060c1b0809090405030705160608090a11010f0c0b0408030411090f0c090d060e0a0219080a02060d15141c080307 72
    0x4000c440107070000120440510b80d025455003014030301903074120b000400d058009000390744140706403501c4411942c06860440503d880b098042c24a00f410b041e441a420445080265030b10b11804000f10f00c00c060108400c0e00030300c1d01800c802c41e0381500d84483c0d20788146034000a01e0b030b10308035000c01ca000c03140d0024580311420a9842c501034500010082e01c80c07a07415051805070040e00004482c40c941c1d4104c9142c0d241d0003401d031110318a18006003810000304c8207000960003209084909181d514190545900c16103c0085540040e41c042d18200300000601040c00840e20100f11240b0041d60040020b082611076841007100052840c081d80d00d0106001300141e0701e80315981d000750380040c0140709000700702441d01c0e100d842d6900224414025107440950481e2141400d804441405014000300034040d002d2000350f50103054410281503560309804050840c2c10500c1001c2c20046044c074008100b440305200c13010f4081100000b280e1040d807105c400142582088075440242c2d803428280f640004 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 967729649 1250 967728399 967728403
    0x6120f0a0921050909040c05040b040c0804060c050c01241406030103060b13140717090c061e0a02030409062715050a140a1a04062a0305180f0f0d05 65
    0x84d0b001c0980c01000308003408240000c0d40041e806640e011039040000300007143c100001c4400c42100200440c000c0c4000901180c820307442120b14404034101075103403589003071740d0500f100c8107011180904002c03000242258041c5400410152905085003c0805001400200700f400f051100600254980c521802c581e00d50460484000f101c87d50144800030003ea407000b040c01d811114140010b42544c0c411004aa0f21041140902000c40207007190740355010910041e54042d4815155101107041f0208260400380010140c8030499070207152205d04000024054030341c9907200c003054000385910400341903026038940785900a030f1040001d8100d00440031031101c0c3c00720b500059010a82c80400550006032800f1000d20420440301c1d40700040d11000c0c08105000d9131a000d205e05241030000340403a9005103603e100416007500d0701d00040c0d90103441701e0740135140880d0440000b440424400034081a03802040b0802c0e4080f100401d03c4500f820105220900d03032120750f80306488407003600d0148101 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 967730899 1250 967729649 967729657
    0x6010b070f0b0c072906011e140705191a150f010e1009090e0f0a030e0a030f030f0305160c020f040e0a081803070303021c0e06120f0a092105 62
    0x20141441d28820301040c079a81d0a05a118210904409102c0001b5110362207042d403480792008032036044a2203031450401b11a418504115651416800c1165402140d0300700042081855100c0710380f0030040c070134035114081440c84540c504020031804180500419100c0d00c4041d40e100c10380e100a0a030140750012074401c48076001003600040d11869441788158060304480503078200320820300201d200110529070f44c0304c40014400aa801c1318500c100002d124500030100c03194001e1560000035140d41340e065271201c20748802c40100740200c60024503690140a0513601550340f200040ea8200b16101c058070911211000910031441c0300004207682c2d0301d590000700000b00d2042203d860000c540b0f8100d13030302e0348400d4100215403141054805185070000d1004207499156001c0c0c41010f003140e010041c1c81210744407080c1400001c5441c10801d8a515024007440c01040d4462135481c203001c90341c100504405802042001d041c06401400b04a6642500350203c02041400b407608140c80c000310303060f0107 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 967732149 1250 967730899 967730903
    0x103200d140610080a2909010f0b01173607030203010b0306040c060c050a080c0d0e040c0516050c121c0302070b0103020906030c2106010b070f0b0c07 66
    0x850096005000341d00c50100014041c0004840d4582c4601286645199080c421080b0650049500c040000c1e9101d5450701d0490218480c950307441100c0380211100c9a0440c2c000d0841d0703544030380c0e5010300d814034080c0388aa000213081c0000180800400d030594003100401146142c40324404060081c03800110600384d160843c5941104410712841d203503203074040b910090b8825820710814090521340451400d008030350000201d00c20381d242000c00e1380c86c1da00011040e10076001e0000528041414071005018030f40200d00500824000c454024020104d11030010740514644075180c1d20f07031608082161000086c00700d81101e4486146421460458801080d90b00f01e4020031112044040000780b40c41c00c0604582c0d00c99001460080803801c03809010805826002010300400c05800c2c4400b4551304040040c00341ca10a0342044c1c08500022078060500c4090302c00d010007299603072400e00c149400350907403104540c9405819141d03128031800705038020745110b41010110ba00d035480342d011941915 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 967733399 1250 967732149 967732159
    0x3130510020c0d020c03010203070f0f17040602250203120912150103150b131a2124070305101536090b0a0e10031106030f010320 57
    0x1801a903034070f8254221000d405031044402c000003030729040c026288118040e070303140d82c0091600071086500d511a00080805e01c94040521000005001c0c20244180c0c0921400340e60b030050308490031419800054052001c0420089a40c01a640411900444031444403450b840d10032000014a00a407540f0740d29400c0d11820b00198505e030341600d2000c0c105c0e8000d581c0e104e000c40e0821340b00021341b9411000c080e400400d1881d0300d0328855069100800408241102a441906800200d048001501000100460034841600040c442000304100120f0b2040340c120302c50f400031002e00021000640752001b41621a0b00141c100c81304c80b1112001045000d8070400e28800003800a410b031903480c030b827400e03a054900c1303c1c103041d540170380c0b0700d018001c00d206814000091911920304000c02c180c000040c2d200041c00d00000381c1002051131940548041c07012816290328602d041d844618142d04680d0060b00c05000b000340b0b1100802c001c83c1180e4018448084241030310f0400e8803285804030070f041d804 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 967734649 1250 967733399 967733407
    0x608010c14570c030703211412161d09090c03060f060a050906030c090a02040801090302030d060608010e010e0a060323060702031c15030203070b1804110313051002 72
    0x256104900c81d15054054078107a600d401051030a06860f01c1c1035000240c019000215000c5009290841f807d980524601e01481d4038038810407e10701c3c03540203400540101c8100c81c10b02c2410440349061841081150615000700d4584441501e2020300706082c49106899090018103501c00c14031001024501c000c0c1600c00c10303e005101459a01c00580d440b902400c030f80c410208250070300d08950b40c01104010001c20048610908200003828000d241c5226240c0078030000440c81400d001e61481d0382e01c20f8024548654110060f0b00898669038010400c1040c0007004005105e1107440c00c83c1503c8036130003140090755410705600040d142540c401403d000205586000356898052110411224001601c0329034581e46c0c8100da0741c1c02030039946c502c0041d120700b00e0007010703440707911800c1a492100a4405c41e00c2e92a000282002907986c031a070800000022000d08451402d4200410410304880800020000302c9400a19000050208885010610b4440c05110f410042c1900265104900f1340da6 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 967735899 1250 967734649 967734787
    0x601030b01030605060409030915020f16030302062202010c111005210103051002160b0108060702070902031509070c0c090e10020c0c01031805010608010c14 69
    0x9001402d02c0242c80c4103140074042419881d160051181041e0195107407030103a0304110011581d1940800f140c1d09500c9910340f500315034803013841022280400302e64407056240ca51304002e41440c5000b0300c11391000e0806001e10758030f4031042070032108140e02841c03e22010201441c0240000900f0160140e125016040b0b0102c05c0f0390000081c0251641ea00c991400398814808406600000380001051341d00b00010000d10b12107a580600390680ca007840701d40400c8941d4542c02d000000070780020070346801c0041048092501001154000c00c5196021451031034551445501c52844843d90751280300d22101107600e40e0703c9030b040f030a2a41c0e044000e1044070350f41c445d00c0304010000394192681600030b405810740780c00d00620940d20340400300ba0107002c0310040100110003d00c08030700030b8210301ca0f81402c80c0002c07803000d00c118000f0304840000090101068000507084840b40b0807040513400c401c00c10249481540c3c110b01d6821001d5400000031091091034081e082203154901402c5030000c1444080 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 967737149 1250 967735899 967735913
    0x130c0f0906030c060206040302060604020d09080711040c0f0503062103030a060e0702010b01050d021b100203091c050a0807020c19031502270d0803240103020309070e1305060103 78
    0x100c903c5254018a00c55456900340d8039802c00b150050096002800000c0450619800500800035109000500c9004036580d900c01070b003061400760f448030981021540a41428495044560a903041c1040d9144440d50001c007203100003401107004035664107140c40c001c240c100320445842c00c11000d99890745806c21400b0001c01032489255803840010000c1080b55006100703004050038181e44440c580308900b224100691f000d0408206250b150100300c444460b800c1c007481c003040386c900d00b001d80e40e07040890034140303800700da180d0f054015a00062a071440941200442c2e070085001c0c188001c081c0c0c0c0320703075007641407001514050350450101d4a81c0700440320345c500b000c42070780e10600d03200c05070340013041d0f03d602240154122991140c0d1091a2000c0ba500035440042803818014100d902082956444010a400550b020046030f0001814403007482540400e40403414002e190440c00c44c64021103180e0f50780d6030740c464a41c051540700d001c181381200203090313410000d81202c111031841d40e40b031030448 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 967738399 1250 967737149 967737161
    0x70e01020a02100c0201140306030c04090c090c08040b010609060503040b060a0e1e0f010b07200a0308091003050708150d020312090112020702100503070c0f0605060324130c0f09 78
    0x34005a2400507258072600d03031f00290703030180001400400c884d00b8000d06100041502e031106072035036088203c0000303c1540902a811290045503200711490a052a01c03006c8540d068000d0310600140f01003c1c0b150950005c1030785e50143e00a059410503840c0c160100340c00b44c200703400080141c0d0b20710341000320707400000013107901514095545414030340daa166000103401c400e000b15803030b000007040800c010440e1890030041d814401e10f20b0220302074034440007a1000565034001c0340c0a05010907003403820724160140c80101002802c0901980c617065100812643e0300411400f419541000d903450292141681082c0b919070140469400220701e0915108a07041941c446000458960b148600c5034440d00944205a5004d01030f0f9030319885064054425400082a1000704000c502c40300c00840d600d4582c8000d0240076000006a90600005141c00d117038040e4185d03041c051448800300c17010b110b840b001035844068a0b1500250384201d00d4503595171500d59000031080e0079503004c042a0290182c1c800 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 967739649 1250 967738399 967738403
    0x708040f0b24010201200708040f09151d16030207060207110328032016080c240d0b1002011416051c061206021b0f0303070e01020a02100c 61
    0x2441d42100a80049081c0c41c0990400541d103c0000510100303444d1403005070000038230078000b607410b00f901c42503480c103460803d0b0301c45900c05485517a90003c070001c0f12840b00c05082540c50760903221100e6175070442c0a0380090b020b203082850f00d1403903000d864441d07410303291a20340c000400d555620107810012400e45080c46098407034001d030714681900711082160500e52a0f05660781d40801c04d138070344040d030300c103480c1005040544165440c0c0c5d2070802c0050181000c40f00140d252044401d042440151408006125060140c00603140075601810540028044246008075490744c504943e41084050003080f50312541000d2164020030400da010742014040030b04558014559035502118084000080c0d40c0d10000314400b08132511890703c0c103e031030145111008002141d155560340c460f04034810a600706480f580d601150000e2500181d1281024601449000340341c050280841a5100c1c84007400d160244041d0701d01c0001a64000d10840f20150f8000b80040d00002c01004042e095654409013 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 967740899 1250 967739649 967739701
    0xa090906050106210504030e0a0306150510050405060309010f09050a050d03021c0c090e010816080d27080115030605070216261c11060f0708040f0b 65
    0x440c2d40e07881001402d2a800e0540070341082142c0200700d440041030046c00035810002c11000f6000291070300e103a014000c40c4148400904030181100882c0c103003016400c450f1080d0320b58582e203002306070300134150b50980e0821150302c1e65948411222a00620500c01030000312400e043d07105081c0240030601d008018050000c4d90031144903a00d0031422407003121460161015200c0c810240c0d20490790180c0b44555882c01e02c00600c0f0707150044510450001d903c540c000307610844161445da060a2442001850680001d254003030700400007034040504403102180e102160303900034052044146000d00108a5103008001300743d104840030942030041e00060300d6290820003c80c0c1118800940300c00b400300005009000c0e00e090004036140b03850414080ca0a81c02c90003d910840031003840041c103249c40c0c0c00d124082c1505004d1010342509041c0d04140c4c1950400410440c1500030b4000c0c440c1c1c400d0031031802a210b0b9039141303400c50340401e42c40005091500300c1e004000d484c0015420360080d8401c0300039 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 967742149 1250 967740899 967740901
    0xd1d030a081006091202030f1e0c061c021e040306140c090a031e0503121617070309030c06020d0504060515061c0209031c0305072c010e0a09090605 65
    0x81c0b060b400c1e4100c1c442c0100003180d951080100f41025040c0b01e80b41c9200505a1325000c80f50500c3d84e240c0103010206d00f4200c0190011501e05070001c0012003402038098940c18104200c50400b03a02c08480040c14034040c03500051040142103070340d0782c01e000038042c020f00d09850304c1c0c0349d0402d1070040030303280345003152100860302103141c0401507002c0d100d90110080440040310f0660f5244e00400085040802101c40e954809070006034040c00a40404e00f09034290301c100c0e00d06200310001d5010344414020910098880c01c00c200780c0c0500540364440030900b0003041002030f0b40740032130394805d079000080c1002d40b0215071034590031125084103000d42c2c0101401c0c0980d0300c4825054401440201c119035100c0d1040001c48014500594008040c21611134018103000300070021034184520083c000d01ca0003c401801c0100c59018440e09401620501d4503084440e13103001290706007012200841c0112500c01c1941e16035030301c551407038451410050702d08285c3c0c5555042c1e1101528010400301c0b055800c0c40 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 967743399 1250 967742149 967742161
    0x306130905150a0515030a02010309020303130b070b01050108101a0f030a050a0e0319080a02040302220e070302010912240c1d09041401090b01151101050105150d1d030a08 75
    0x603003010030b901004010701a40d1f145030b80150010101c4400413030f0113004c20f2060120005444102900515844118658800c4240b801440c0454142c1025051080035010302c2034100a40754040140c03810104120712000d91410200302900401034044809480001003000d01c003a40d4000c00c0c081c4501c82c0c0f0504c2450369000700d1613201d0003403400d0f6881e00b01c042c0700040300070351041031710070b4005800d50780040c9000c4d1250082810f44454a00c9510340c40311000701051503120f14442c0c2104844014040e09102c3d00b0742d0f000030526080392091a0100c11440044800e210507003600d10581d080503143c038604030000140c0c560142c0804a0000b0200d604440501090740380c2c08100d0251807401010410507544075600d0004000c403841c0525901e44d0f0310560304001800c111000760290000e0b821015800c401c1100c01000410b02c040700ca0030300e0b41030200400c080e4445000c180c1d00b40d040890442d8592a03044070000c010140041a860500045501c042c2071490110051500d54456507800304247d80340d07 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 967744649 1250 967743399 967743421
    0x90c080105090a05060c09210303041208010f05060a0e120d0e010207030b060105071506030c050f0609030c0108150406180507110a080a030204180e10060b0306130905150a05 76
    0x310348007904c80e030045400941d102c82041d00903d10703140002c000d5180c24070540b126403652009040d11403007580c4000240018801c140882d6903e48a0382d1501384869810000d0b113508400c150f1090502442011a10400b00c6018074003132000400c0150408e111a4001003019583d0150203c2c030300b01182140d40a020749500c00300c0d502c0181e90f0003884100140e00c4520044415501142043d070388821000c0c640030b00d030344141c011030b8003c5009910f290700040c00c003401c000303200c1528142c9511500042201c074041d40c0b004103036041e60081c2400c013102c066840071440a01d00d070f64120a5076000b4903002001c81d00f0b0840e00401c2400c1c28100c101002543e9135000260b80303c07140c50300540305940c46003002400151a500040c07004c41c0755488e0250415581d01000c0b00c408041502060007a9220300d884a01d540bc1088a1090064125000d200c03140c603062100341d41e0f1201804490150303540d03910001c3c1c000503503000b00502c6688041140d507001400d00200341c4085040ea05503540d0b604200110b124001a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 967745899 1250 967744649 967744663
    0xc0a031e1704080405060a0206060a0609060f0e010905220f0c020a0b04050a080307020109021201020a050a050c011407110f0c22060504050c0403060609060e010e090c04090c08010509 80
    0x325161440404107228012007a030200074030840f0754400410001c900c2e038480c8070140c405007046070014541800d15004010041c030003608480100700c1880760405c04903504c0000c255810702941884812000c42000403240356a190300065042600c0d04070805411100540c61244004c0c0c07880200b107001c0b07502010406640355200c0050045c0d00c0902d962011884280406401501c40c10465003000526958420b15800480e03494000d40d544401c00c0003541000070302da15051b00170030000c40c40c01c4401100640203028400100007080004102040d034690b09502040d504030500309014003926010340001c180030440c03844c82c010760003540750389441d5110011710003c1d0480018502a502001514244070103581a040d40c0546900e403040061552500c0c800c2c1070144907203469180e03550381581080303c103440c80d81e800f0b0fa01181c600740c0100800c021000296054070718030500550941ca403094000d1401e0309280b502948940740c90480010402503060020444520780001c0c455aa135503140c031511848 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 967747149 1250 967745899 967745957
    0x6011703030415090f06050103050c010206160f090b2a0304060903060905160e100b0c060103080913050f01090b0906152a0d020c0a060f030c0c080c0a03 67
    0x11041c004100020070a80c110301c602100e440c400211084103441d421028020a60240c0305c050341c0c0c600600c18030506101c140c0f0443c0080c0010681418540c0c9401c1c01145800011000c20810600c0340880b184034401c08401480c080c3c0584e510ba81203501c000c10004241030000d40703014048484c02030151408015a0101c40b541c0e1101d0340f1052030360f218100034010386041140d0602030400782a4400801e410f444000c4c00241356010080e190220b441c072018003840d040030540311410310040e40c40302000240c3c40d0649500500440d00c4400c0301020454051a41c9041074030030382080f040044024400080604851624100303004114039102848041c01d002d071141a00500707015404210034548000509036580220310141c017104055030400c4000703084004401040c2c0100344450006a0304001d407104443c0101c8820007860320300500940092300194103101415229004a070403580103c404041c10f54100c40c01035550389500c1d00842e10f81026100481c0032460b081e07014680011122070001903a8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 967748399 1250 967747149 967747153
    0x203270f0d080a1d03060405010b101128050601060201020901020c0103020c0a06090213020703020133090906140c0d05010b0423030304051c0b1e07050a020a080f0a02060117 76
    0x14100c0d0104c4407449041103010507940801c1c034404894808004c81032040340500d00000f20a9090010000c00340500c1c03440c0ba00300607032061080d001e4440803078004c0d19245115030f0380c0c84904900c14200407100b904d040140ca20701840c400000d00359010740081c281076030309034240e50b030714080400154120300a000c030b03940c0345034041240301e4001115a40003003207050005004400c2a4208000c110683e0301150080b40141d443d20521007000106615880034001d44699075100c200c0340f880c0502811059100d901d242503221200002405080d03440300131461000e0400000614202130038414a60160071210a024030301400001c40c036044009407400e96588000c1d43c1e6400001002200459682d006206d50600040100241e950344520505040d103c40900080c401180d0342000500036100418060011801d0030507000040141c02c9001d9018040703061198899442c00c0c0100d2910804010050030300e40c0000304c0c1c840c02c00640d4060304079403001c2e07402c40b046a07880340c6400b03c1110030400554815 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 967749649 1250 967748399 967748407
    0x10110c1009060f020c03030412060501050306330d0803181f02071a010608010e0702060601020606040948030206070308061903060903120b010e010f0203270f0d08 71
    0x16846a5a8000c000300c440c13044408460074140080c0c190f52140d4070610540c1d800848100400c170203030190900404044000c0e004500d4916a11040c04821000310728102c0c00e56800c000d0056820388039458080c030080c0c103a410214861408418540c415224000c0000e00d0038441200301c000007900b010381c054000242e641c070042420400300039400200048400c40c4804051181d002a0448080d0082842e61f8415046516088500300145d41c090400400c54104c0e104102e502d0f600043c540340c000b070017640c1c005007401850600c40c0c2640301700700f07904550a8100103c118800c0c07150010740001c606110905141001c6849024018007032444002c0d0004802d0140c3d00100f402100b00380c0d0f0004016280901d01054070194011100543d0401c8982c40d03941d07540c0406040d800710b446d003082e8010360404c000040c0c001c1c1c0060007840800e40842d04002d504450404000d00c00c2c802d407400340844040c0c0a1182c40000a04200d25809a0009006002c2500da0b002640b0b411160042d00c035401407155403070 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 967750899 1250 967749649 967749659
    0x105010b1c050709361d1c14040302040c020f0d0c0c030609030203040e1006030b04060b070b0402032505090606030408030a32070306060503010f050d060b10110c1009 73
    0x61003c4034000b0502e05a0707850030024909070485002850044000500380c1030310019183c1c0b00031b580c0401c2c0c02c117030300164684480c0020307805203107003219460604900d84104071410810b90300c220780000390041d007410048440685c0000f010300b9449a10f200f42c441c903162800003142c8003c41c484000c3e00c08210100c080000c524903610002c01c5900900c1528585501c0b811900e48a03c41940e98140c0f07880c100000b003040c5ca5052046a08218040b0340c180800742c94480c89440718014101e0241c605800c00010038110341d0100419140794850180c40c45a419070640045100c003c0391040030f0040d1461400680d040c41c2650403031784610341c404016411906c611003c84021b0000c1208803985180e1401c5101c2d50081d07444420340c0c00e02a14500700d08a1810f241c0c001c00b40c954503480481402000e0005201c907014515945c1e080c1e40c001c5e10081104181c504240c4040c2041c49aa15001410100b1040d02107501445241c41c00718010104d8201c1c14214042c40011580c110401c000991004405d011f = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 967752149 1250 967750899 967750919
    0x4031e0c0f0f0c03080d15050f010e030c0406090605091003170703112b0305091b0d0822060f120e1011040501020c030f0a030e0d050105010b1c050709 66
    0xc5a1409040d8510481000f42c1d69020071002542080c0e92081c000b0441402040240c02034801240350100d0181d1840e1801e80802c0d00c444249a8150510446000b20362064400300140042c03200d00610034050180e445070102c0060865004a030300540082e000110003190b0302e240c41c011079500c4840c0305516048140083d011350000e001c12400c01400e805690003580040002c2210594200302e508034500e100c4882800a803040b22408043c14145010001091000308094003c207202c6004004400011000030303901250700003000341500e07000700307203416900f001c281c8542d00659507640301c50200c0c1c2c0740e00c3c0503295041c150801c000040c3d141e441c0040720300100d80294250b5100c90003181c1000310540c101c481134070000c7c50003448100010404020725030f17042004c14000f503820340142503000c60301442c00781c5502503860081c0600442000007039079a110701aa007031140d9004402000a0750b154603400e621a40914941d404503d91641100809000f40c81040d006205913100d000b012490004192 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 967753399 1250 967752149 967752173
    0xe070501021609051812030a05060d1104021b030f0403020103110319150314010c0f141b071208040315060e0708060402130306050603240a0b0301110a020604031e0c 72
    0x4191440c803400c1d244003000c10458886c007000003481441d1285003105020084907401418240304030600480c04010500c520180085e40390180c07805680d8040360103088808000c180c0e288002440001a00351541e0301d08000740c41503e100341ea06204208030002d40800301c1c0010307078099000c048402541500041c159006011103402c01101c105a69900e40361001c21981400e0b002a069440744441c4950607445041c5513400501070030401440c000320881040d9501038401e101904001c40000240132080810104008146022007083c02c4c0040e8504540a500301d44400c40e80265903040078402001e42d13001c0c0000361015415160325039900c610080b1a1400302a00f0160415401c208102c0c0041c409100600618001c24010a950030a5001e25141600060a42d220000e900101049040007440499041116040f01141c0c0d0942d060002b4014542070014030503000d00080d420344115000300301544124000d032101940701c03140707441807079000204221650009401c40d01d880f0015105440c40 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 967754649 1250 967753399 967753411
    0x30c0901031524021c030902030f072402120a0810030b0a0b15030408160c0f151d090a090f0812010510050705150403050c100e07050102160905 63
    0x8180b102c084201e40034610400d80001c1d02c80071081e0706001c444860078200ea600c12440348014092610290714449001500c0d180c038804054984001e03201f5560b04000349207540c600c001c10398403070036070310405030302e403030030441d20010312451184080080580049001d905500c001c0561601c0c01401050884080c0c100a0075040b84641621010021903008841c00d84180588d540c00605032501d201003210610f1018101e8030144010010000025074840a80b80c42841000c60352902c02420315080e042401da0790001e00000e060160002442e030000c0e00d2252001c403240d00d803020010a1a0030324050720290f00d8400760400c14200204443c0d60050f40803580302c07401100c00c2c040b2884940c0e9980b9041d8482011810040140790042c0800e00d810050413914280c03a0402c1460842c45540d910380352449101540c0d05407065400143c14180100111844554108180e030300312141c0440c280020708800c8460101403050400104031540000381025040244010703c2e00018a02040c15000d04001030013 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 967755899 1250 967754649 967754651
    0x1002030c070621150302060c1504060204050405060f180903090a0f08150f06240d0903020616020303150406050a03060b040b040b0f041d0f0604051c05030c090103 71
    0x110301540da50500c40c400203001c59903038003140b4090484004440300c001814510700e4030301c0d00b852181e00310008000141240d5060300c105888840441e041800c0c001c0c0005508100b0b04100e04010030480700e680108156141160200550349a100a10414540540740d40c1d8000d4070011003003d00802c107036440d030703803000b80617084034a482c0041012815003611540040f00203d41e000041c0440101404030410110740b403041041c91b46000392104007400d0000d040b06000b4203000c1000c031600c44609400480c2c1410441100c2d0351840c0301c440b036200507d0410b0040c0c005000d01004185454001001c407810031540354000c500350344030460902e2003c540825810b074030076601c0c40d000406031105001c3c580218020350340003920300c100e2014042504d51914000b03104500d01256544d00e90b440042c081011a015280080e0400b00003a048543d610303000d030516114803603980d1003081c5e250006a4103228921402c00c0d00c60303c1141204103001ca41e042c40301500410800c1c800148440c0b0780c1400741900323080c1450 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 967757149 1250 967755899 967755907
    0x90703150503100e120313060209010302090925080603150613090804180c1407020a031e02010e060304030e0907050403060609050106020d0e03030f0c030d0c020c09010801090c0302100203 82
    0x181ca000c025020f2100760b2a22012a2043c8920910106419005a40f501891031800a0041c040d14000c480000e10700b950100d40ca00859200354195070361480050001083d0342401c00c001c100281c81d0510b02c0a01069000285c4c2e10103202d4000d041c01000d02030010302007a88841c7d011307815608010015900a203030a482c01c002c00b40c41d8090341e100a4081e051250f5a030f814025500c043e80ca8910314900b426003410218904c80d540030b0340d0720f4000e5162103040c0d5214038461000521262036544040d00080ca1204000b42030114003005920350b0707100741c80300760b030100341601805030034001103401502090140e003075070302c030740c03c082c10380b90340c0451945003c6203820f449548101c00c8484035009814401d03a904018004240c0400002c85941a60304240d10b1800100340020340d01e200d41c01b800e00030b00f00045422001010100305950010b402b040c3c0601c030012031003030001c0d03071004451042403050420320000a1402010702c01c0e22401500189081c40960864080c4030384012641810802c40c44100 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 967758399 1250 967757149 967757159
    0x207030c230d020309030a0308090a050115051e060f0703021e280b1603020d020c0303070324030201440c0c0318011b060902090109050609070315 64
    0x701419024182210390298044220030551401000e46468000e5610420410001c5d50780020606485540361428400640e904024603040080500d0000e26039070800d03d20348220810f0120312410b5031002d0f204682c0d00c4c604505d0703910080c3c2d40c2c070114a812090070440d001c1c8001403e0300078030015010b80111390001d02e042030b1050f4600700407507c03042581c0090402c0c2d01404c070030300d20b10141c4141d1031810b541d1401e5103031035000c0d40c038101a0075008072001b910700141d0441c3c02034060f00d11303080600000319101c00904255a07140d6008030313800710021345048035400554402e410f80c1d80c801c80d1140187c1042c2403e40d401903d400d1080c0480140d650341095012401c0d0f11008604454040881e891100401c0b21401c1c13103041080c007410120030390f802440100f0345c1120000641d0403a803500100c48888040980050f40c01c03061004480cc0b0107129041d068062040a42100f100c0c00c1c0b09483e0951586e036244650030813a5810740300395038800b4860f00801c6103036100b9048030310042a24040a84130300e41c1c030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 967759649 1250 967758399 967758413
    0x3050601030c051204081c02030a060512150912040b0405030f07030f06051509010b181e13110408031c2912191a01050303091014030406020c160e0a0207030c 69
    0x80b682d0f9407c3c8540000c20070507164514065031008010644010341c410b0034041001e916800c8070008581c6501900d4000740c1c09070780802414202c22008400141ea1741e4070b42041740050791103401503d009102d0301242d1400000c000524000303e0350025094811200e040d40c400000d40009040c00d141001820b07410704003590b4440300b0300d008003809000d032a0781345421490f03c0051030303c1100951143c00e05074101c00424010b0151400c6440c1704655580b001401960600018000f2a43d018080580450042400700e4000000c00c1c01414404814140b2603032108643d0a80e1010032040f101d0000404981d50307800040018040b501100a0242c000b00001c1005145000c0d2407032500036200c001c0c03084942c2444605244032441ca0f0010461280039811706010039a40c0c400c4091407805808080f2201010b00c3c80b80e2041c8400401d0241115a2801c00e410500040d400c4995509141c1c0961000e008002c0c0400c1602c10441765400c4104a060786c4116444000703401c86501075082c8040c0c080c0120019104d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 967760899 1250 967759649 967759687
    0x62107090302060a0e2110020f070503220b040f050d06020d0f0203100f0302090708072c012604020f1311040f0b03040302061501110d020d03050601030c05120408 71
    0x49681791141c414550f410005401400c000400f405884000700080107240455820048080e6040159039149540309400e8107101e645000b900500010030b613800b0000d0050b8104000c58036504444110175103c5003410102d101e60711910f11842c00c0710300200030504090468240c0140113541c01400c02044000c084103581000010f40c140c540c0c00420031000384850440c840143c000707035041c590494110381c040355048030060280d41c10701030b41000140f1224400c0d070381c40c0000c6655aa64820b989600c82c440c60000c1c10440740c0c103000c1074101071141345103800042058064048000c12040740d0f2079503003e1000d490400b022180e0002c80324406c42090040743e016405260982d0a000356580707250900030b0305c0a58207500310090a0108106100104e6400a1100e0700982620f080c658228101c00c01030322408083d82d0700785042e0041d0b0748422210703500800c0c20700030300b032141d241030045542d800c0c0114100c170041441c5001081c42400266005401000115406440f4261061410010030f103c0d902d0504 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 967762149 1250 967760899 967760917
    0x3080a020d120605060418150305100c0f0e12010e07080606040b04020306010207090b0609100302181504271e06051507141e010903030b06210709030206 67
    0x220403007815603101d510450381c81c092000b00310208180d9080500007002c0e4800e501c10f8103104075080e04103000da80b03455417050001140e20b50341c080c08142d8a1909680b900ba86040b405146454a000c402142d401420240002505543c6150400c051541082100504600362086640d621000000316013020006c03e006004000d008100340d203006030411003551b82c2009858003035030040c0f0900071541d1300050f1a80545900d094003264081042e40481c04501a400380e0310f0340001800380000350300740c0540c000e0682941c642c0d0a036209807010001d1040c0e8aa503070103603c03107901040108021103522584e8000c3c02185c5000642d008000b416005411313900d14040c80b811880303520035003141d1000c40c0d00c100c4000348000d5900c00c041407080e070010f451a002d074280c090710306560200361804481051201402e0a403446141d070179140f0700c44100c3d0f402040880021408a4501215030301f0f0344c5042400d6030032086068000f100c0d440f0210781d000303071070120192200341400001000400103035a100060400e00c2 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 967763399 1250 967762149 967762153
    0x90a0609090f05100905180f07031b030b130816060204180908030718080a2901050102100c0c240c030207120f020a0b04032c0a2c04080a020111030c070f0c03080a02 72
    0x5825401c3c00d02f0381c070100c0820f1000c84007803640100001035080c0b00c0103900a03800140f200d4844460b041611292003901c480e0107103004aa05841c0070401e00e54058029100741814090860312847c10513002c0720a401405894618140006414135204030740401c0f0890205440c1c3d458203a80b40c01240c0340001a400881c1c542070542441e420003814600c00103c048084508124a54503141c0080c0d2100341e030809100c40c4544034000040b0541c003039120300c012107502280303560a810000d602035041c8101742d16150742040c10301c140120128800e0080e552002d40245c44103028811a1000391043c9039020f600000390300030070298801083ca00740701144624007030748452044500c16084407500303001c0004100d0341065819480411030301c41d99030341d4040d104940680c0200700c541f101103010205c134040f40b8410108464082004000740b01e009001e212640303030000e0002c1902c8080580250000300c9080f0040360082c42843e000c5035a011480155900510300c1015080d200e4481c0070b403550100c0c0d0400050703 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 967764649 1250 967763399 967763413
    0xb0901080106090c181406040312021b06090105040e0a0e0303010905040308010e130303110d06080c0a062c130e030702012a03050f090a0609090f05100905180f 70
    0x106410700450301c04813814a030080640324002c4c0c0f42c0e0100b00190042007110001301c01220b00310f403181001c4030041c51300078540041c0300c0160030f070096030752080810701c0c841e01c000040307600554108034050340d0b04104140c4525060a06140310340c011000c0c0205200f900070b03100e0b003091092030303000c0c0000c5008c0c044c000004100d40c41c080c18054215603042e4048449041d03000c0400030001c864400c0c11180e5949860040354050050309807038604d0060010348102d00d0300d04800001c0030040000d20500d0458140c1d4444401540c45a040e202c0150807581001c0c1154000c000ca18070f02204d4030113031251040182069480c0e83c03008003104c100c1e4440c296507506a4000282032096681021000d0505404603c241300444152101029040403079040102445401b043c1e004044e101038066841140f0090648440b203599000018180c4129204104040b0315202000c03418440500400b44100c0e00f62aa88443d1894444040000c0000a15130500129010119800b0034401d00407a40c1401140c0c00900784 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 967765899 1250 967764649 967764659
    0x70912061812031506050301030b060a35061501110f01060b0421170901020703050312010303080f1003030c02010302091203040f05180f1009050a050f010801090b060f040b0901080106 80
    0x4075013003013281181140050340c0401c040ea81c040d0440b4190b82e80f1034804030b03480d111031000c10444c0c501c41d0802400c804c1d41c03d0b49400c0b40800511040b141280d00c00001c01240b4107840819100c0300103803481c3d010700c60070280d007258070b5005840d50391808500204654008414010440c03c60b085500441310100d00040c04200203610200c19607500c01541c0011154001607548096041030b00b265061461503011654200685c028008030006640110a607980c07801d160781d541c092110b0034001140801c0d024070108290b01e40b2200c03814400d4124a040b68220350468400342c40850001c10100d04041d020008a1002c1e11000c4083c03034041180c00003940c5540c281002e100c400d0425400050203241f50f6900010b02e0341e56240e81e15000311044d0307054010b544810840e0804400d15070018002141803200388143c403103ea40c0841d1103200c02f003211402c140d807100720960981d500c0000262000600303001140540c079083c100410020001030000035141109070102d0008002684841a581d54072041004 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 967767149 1250 967765899 967765901
    0x813080102040312050a02070608270303161b031d1c0605060f0f090606040e04030f02060f0402090a113106112a090f060307060807091206181203 64
    0x1104c0090b42441c50a2000d07a40c0002d582d029140700ea801042400c001080145042e810501100d0410f10310343c05002d54804200c40c0d8036801599045984500700318403101051260400d0311003004d40c215228003c030301d40e807002c44124208070a01d06070308040840c050401c0d6162405014a00185010b900f9000e442d42094002c5450040041d40a504c08054902250343c07100c00012244808644126894072240081051030040d0f030485d50358007441074140300074140c010503000e5000b46d2075421520141e440e07903604102000b042d14020f402c0b2600303601142c501001e9820028445c030340e49039003d0400284041c18103004d43c81e8081505265aa100180d440c02020003081d805081a0b04001aa451440e10440c1c2d40320740e0080040490f0100c6008440d408418488030021420024184040c506082d00d0782100f5000c1a24107034400e02c90040c00040c668011400c80d44981590388954000c0e034603060b890305841c0d424000031500c80c1c0e651015030b2007010341144e4040d445401510b00c030a2440c24480054 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 967768399 1250 967767149 967767173
    0x405090a02040627091104060f1a490e190206071205090d0b0a050609091e071d070206010b0711041107060609051f1a0708130801020403 60
    0x255041c0526200f03545154100e01c1c50320321452941138001665810b07030070040c014050100c41142c0c003a01f41440056541640c0442000396036019640c2800040381c0d9040c82054030852540d0071854450518051030352082c81001d0003c0c10507182182088450a00041c0601090030707041026640c0c0d0b880100e00724001004000f4030300c001340d1202c008030007581c0c00144450291840080580c03403281d03c0040b00d244100d054681051000d4101c5030460743c00e00d454018007408586008c5131900d4240042c40e50302d40601d900d401400300c1030107401d21181c0c072001c0d049041c1c0c03920115200340c41411000145c1c03014588140c080d40f05ca090071040030f4241860002e09221069125002d000790074482100070540d0516480c58030b03171089800082c071040c1c0da511000c0902a0480c064880c900d0710100094115541e00114410f07032020b00f00d1100201080e444c00d4000e8054001c1c040c0b1103007480c10001c04200018000d0100368003864049040c0904040340a158002d00c0c2c0000111ba50046001c1080201400c1d842e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 967769649 1250 967768399 967768409
    0x60603020c0d11060103081c06140f04090309090b24030106031104030507180e010212010503061803091003110d200307020606041113080615030309100c060b0405090a020406 76
    0xc0ca445000c3c100950f0307030302c060601000d024010000750055544d5914079420340880f8141c00c01f40f100a59503002d80d511441d01e4848580200c0c1461090311844c9841d02c180854654162160030600d82080041c01c01000c076442100d8003c0c95005a81c20303004036030301440100c2c1c6101c0c41074640d07030343c10050001d06585170b185149034181d1052105000168011034148159916039200d1840b400c42e40c41508003a019040c0c810034594070014064500d94140a041416228103500f29030060b2507a00e030800b04804c2440d660f079000d80040c0309024581c641001085000c000510f130119a440e804918800c455110201b42c0602d65596184103c2440c1c45280030440c04040101e018210b281803080a501d850b0b009000310711541c0c0d5401108101003c4500303545a20074441c0c2104521a10340080340da035501c094880d005412031440e48444e0700e00e0b00008590141c40c0240110000e068000029103c0031000745048540540701c51111289441e1881014440e440c03c10061900803500d00600c41202c5a079000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 967770899 1250 967769649 967769657
    0x200315061207060c2d03020607030c0503100306020c0c040e0d02010b01051809100308030115021e15073b0103050f060f192d1a0705030706060603020c0d 67
    0x108210141c4c00c200010001070b00401189400c0d00c07903800700351901c079880b040c81040c24803140c03141091507800100c5501c51091034400b000203950199003603407280402c43ea000c42e031404c500010b20004445030041c010b40c0c8101d0048544d2010030030002000d03101c11050310b5100303138000b094080500e0341c2405500c1000c1420b0920528000c0d03091400320540003201c444c04c0c09050042e0101c0c0b0100e680102d103000460304400300c140c50b0350b101c0d007603000e1041e03112481c1b80051041120701442152844c2c0c010b05002d000034010192791401c10745481c44500c0082010062002845109101181c51001042c0040b4110340f03007941a075105c04030148009421408034101460b250412651601d1480f140b5044501112900c084d0098038000415406400704010a03004041070001040343d04107000c4181401c046440d4650b410b07074400454202e5200340710309810541403561454030090300b4401001c101c0c0c020002e8920781001da40360300007070311040c0d4084000282e0000e003070a400481401410344490322880c1c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 967772149 1250 967770899 967770913
    0x915100f09050310090b0a15030b22140c060903030a031812050d06141005030a0207021206010509010803030c0901030203042901060801080c130c1e080f0c03132003150612 75
    0x4808440d40790700009214ad841140824a2071940c4403249040380700071032411340d40072598640b0349400805001d94070040d2081c8500074034140f0b4940140e66000e02e018008500b4034092031130442c094080c0d019500e68600300921200041100940107440c10030b0191a016600c20345d464904003200d10300d81c040700ea02c0f00002c0c11419295501032000102c02c00d545003168880c2c032040b0b1050002d21a00380000d50020110030b400c000790901060032030403544111211a01a0380e11490343d034887c07008984032014450100001e10080d8041d5001c1c0d80c02c9070151030408010541803903402d0034104103449510324141d00760010031809612801003805403c061018121888900001c500081c0c902c134031b00041d00e41c0318200301107094400e880c4960120010751001c500207100000c054850042030340c0c911080141d40300000c0314a21040110b1380983d1a58003030440004041c3c49a07001000400003015600742b000c403401c50203075400c005522801c400412080180d040040400001082e034070403032495504414 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 967773399 1250 967772149 967772171
    0x11041107060b0f0a03150509060402060a110c04050403050d0e0f191e030c030f0203041a0c070f0b0c1009050303070c0804230915100f09050310090b0a 66
    0x1825281403030741c0140c010409094450008110070400d0303920035080502c4002c0001400581c050300c40001ea2100c50030407039a1101000d131501c6000c1107401940240081050700380041c031982404100505d00415a440e50303501400180076150306840c1507000075400300b014200388100f481a0161800c219008200c049031600d00917840f0003400015030340070780b84824240c0512800d0151002d0428180c81c0d580b81110713491401900030740d0005010380c000784401d0f03150b001c4c441c0004229010b5500e00d0001c020301501400c20303494294055110101c10340100c0000082422200c8030030006401d2800059440b0102e08454625002440394000145410540c0541c0031840110485c0d0f0022580d140c444003400c2641422005480790340d00c890b100031000019052901507c5124a0000d0f108803000c55030354560000201140144205055121000b421202c11240c0a0740c2e0480401c00d0358201440c000c0e550320b00080c14203042006800020342c41d032400604001c0340c02c8280740d001d0700d480d1081010074003030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 967774649 1250 967773399 967773431
    0x200918150d03030b040534050706061d1509061201240501020c010801150804290601140c0d05090301060e0906011712030103110a0306020703030605120109110405040303090b0c071104 80
    0x8500484881d20703600503600034440c0b088d8210b4080d181c10000c2440543d40d0f9036102940a140303d00c1e410740031620f03007000c50403607201c190403102c802400078901c20075a01d44d10100006045c41c800d0145096603200a4031039500032840c1c104c00b40200001540140529010001e4201207802c550281001607150040c000034403081054101c0380d0b01071801105903a03c61a010192240f03508194000041103800400f01601c103500703062040c0d6083ea5140c0d04a41035501c129018060172660350015040652807521041c0303d00d0141c01c0304000107002142c0341e03548104a0070070350310135107100c4c0440c1c1048006002c0040000b81c20300c04100030324018042c0740400100d81c1d030b1901040c0001440d000301c4410f075034426565041407001640e004078045607144040d1030050000c0c42070f80305990181d00c0a10030070030150703c1885078020441d00202c0254410790001c0c1000020b0070010411000d1658901200000c200e50110b0944036140d14201c06075604164101049558285480c0030712807400c00518514031011 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 967775899 1250 967774649 967774711
    0xb01020a0f03020a150f0b0d02130c0e130603060b120d050f1207050c070e060d081e041d1b040308030405010b040f200918150d03030b0405 61
    0x30918019014640d40380890030130101c000068120383c0c0c00c00c2408460030311940b03c07031901d80d80144200003880f651000d00c07802495404000c3d5004603541d00d021030340c0015802c0185040c100e454040c0800300703000005100d90103030309408066160b03926400c0c4100011807040c001a800d00310396074584044244c44042e03a4483c000d21110800501268555842c00d64109030b0710f40d100c503440360aa241c504080d005100303821801d03140c0d1851041c2c2900050044d100c0c0c030114010b1002801400c04079440752204201d80c1d2006a17040740411608101003d0980b9050181c406000c001141181444c980640110400c002420711121800c45541641074161210304075802c9075030021120b03889035114203002c4d0043c1101c2c6035054000d814030b01c0b0f0040048041e80700c00c14528801c4030b205500c40c3c044140d6030480c09a41d0b035040d0050360200141e0604034446004590244071408542015802880451050f110184040300403980710b242c1220185424040d0079403102c12000171203d190f03903d103a2142030583c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 967777149 1250 967775899 967775903
    0x1e0601050c0309040f0e0d08040302030a05071a0a1d0c0604060c030c020307031b08010b03030301090b1c0b0411060702010f1107031a0907170a02040f02041e09050a0b01020a 76
    0x350000304801040030500a403000c0b000300070300410145844400074400360a14107131884690242101c0882954010100705002d540c1540c0250306107029400c0a8845a018035029107152104d0400381e02002d80001840d84654040700300807a4241c10401c0e0301101d40090a6138020582140c0d078440303042d84404054a04039042d61802040700b01c09400d094841e0761001c0c001039010f0207010004410b01103065072050482c00e01c8270f03d0300045595600c606088a012804840e4585c01c00c00c01008821000e030400c4c070706420020b100034442ca002e000270064074030103414211100c8818404000074085020420191510151056498038817036500003002c0d020b404996109001b1941d45001c16040104599005554041c0441c04002aa19800015200d04492410180c400d00c4c0002c9204011021804503001054006101142c1d1940c200805080e41c00842c980455080c04005441101141002038001c403010807030380c00d541000d8244042c0e4100500b02038019061184641950b40c2c0000c1e625217140d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 967778399 1250 967777149 967777157
    0x1504081c030c0507080915040b1204052517120a020601060905040902060318100c020f0d0207120803070219030f021506010c02060c010605040203040803150f1305270d081e0601 77
    0x540ca000705800500941e00805c0c9c80b014042120481d030401040c00c00d0103180940e0856842000d200d4000b84040c082580882045082c00703030401131654100c1225050210280589201000903641801c081d0441648500164005001001019000f0007110003400040d2000c0c8407448058012070100c0c030014011035102690801e061205600c2404086052a202030301030000c1310b45420000c1d0303103009120100d8a14060300100a500d10b00000c0c2c580102e600d60342204a03400c4040d254050b46400052001055024070006841c9107140745054441c0c01e13101c1c1d1641e2202d0041c0100003842c010500c2d0040d9000d000305c82c203100260f0b8109041d640c10b2541240c000e80e4a00524401c1405090141e105540283c008400d100801580c600a0f5101d0140200d2002515844400700001d84c055084c0c1381303411107025060416420095000107030320026004038500d03208403650b104840c801c0200800c078010380000740100c0c940340e40940100c0c1c00c124000700c3e03803e08002150200840c5100504894140 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 967779649 1250 967778399 967778419
    0x32a0301061e1107090605041104290c01060e04060507022b05120a02040302030d02012a020f060709150311040608060d08030a05040b06010305151504081c030c05070809 74
    0x3c0c03040c04a880340c00c8402d0291031445503140b00000c041d1600b80151031083c1d041076140c00340400d2400544040320300c0204003000c5400410680129110241811116403004004401c590b907024006c44004042c00b5030046214601410100101c581c050040e404640000c2000b01912408030924080c617044100d00c6000e1207900349003525544951402d02000800e50b200308000d40c0301c41c0c1d024000710b038020750649503107031543d1004a0132116020701d40d107404000d0b40328203400001c80d010408a5044607004036180b03402c51042c414604881107075040c00007001d0700014064002060314042194445d82018080c17440402c140760058000c6024400422000c4800948a82d403481e40b020070981c0c01030407507640d03418542c017001d0181c002140c0548104c0c18001c0426490f503c64491503100c0d0500540807000d446001d001c11445803100c008035421540e05100c04034024409211410605070030491514003030b085c4040c090161b440c0003001e001800028017000021400ca075049030a000b200712103050503 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 967780899 1250 967779649 967779707
    0x203090307210501060e0402010f080709030308060a180905010c09031a070221130b0708030612120c060f15030709150308040303050d29120c0402032a030106 69
    0x90002c10a400f0f400d03036081000024041009a031100c0c0104d0003039a509109030b07000354050303d840341c0030b440c200c0029a86074010408a0711a0940c640c0140005101c988110354039071f0003007801502e0300e040707444141d42c4000c1c4004208003446520010001814000744592035616040d1000540027613a1040c441d418001480c2c4034404e02c0001040808072941c41051400300d5603002d900e410488150309429105100802c08005a00a840c01c00ba405880380d4619500e0505000c0b802132103400a280520498400d0113201041c500a0b01c01d00301e50100801442c42c101c0c40320659541d020786800e808040051540c0b80c1c9860105400041d14071010000c1003000c0492034910b80007000d680050050900400c01100301540140202607128130040c1c20710106040c0c0c004410036040b40c0300741140103504281308090500f400f0f02002c440e4100741d0240d4513618240d00109003130740d00031100e1303d1401e0022111050b4102d0910441d880d000c0ca07000501d4110340c1000320141050700108070304c1c1c00015050401d114 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 967782149 1250 967780899 967780949
    0x806040b04050f0703141306360203071d0c03250504091a01450815090d0e06070615090b040e03030c091507030914010203090307 57
    0x95064805070040007a450402d8490903801c40985a40b400241001e501310910350b00c0343c0009000b40c00500d40d42c80d01141a90310f0340c5c000d100030300c00c00c00000004801542400d280e42d102e0300901c0c074011001d5590030384500c1014144007268010342410300700e45903054911239001344450fa00c51480d0190a90382e4440e80750f00c9020200919480e282e05520038204551a54014041d000300c440c000d1060081703800403207810007482c0c42d856101d0300140740c801180307410350b02401ca502241088000e128034862042042145005003465001c0c81c00c07000e00000b0840c243e42085403c4175508840d44403809030900c0503a0b5601c84c600c14441d44100141e98a0042c000e9840000300d5440d03c0d0300c080b0410005e1400104050105514490380210a03c0d0a01c0092a0b0800d8014008580c8841c1c0c091895a51110313203503000d64000101c1130b900025140e01c0e956181c0c800e0350003400154042d445602d00146415824014282c02d28113150454000340001a040e0310300040307c03825102d2400c0c4c1d502c484a40f480d1f26003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 967783399 1250 967782149 967782161
    0xc01171f09020309030a09080109210909090c031205070b0103150b04020313060b01020d02071e08030705010911060c03030f0a0b0a120c151d0105070206031f081c080604 74
    0x70080ca4400030600801c1c03a4004000c21b41d41d40da945800c008540d0351030310282252854400a04414190810110810420003260070b078014103060507140d1b0b545460080c8100c41300544103d400d000c10081c00d200f80321002c117000000c0d90552528034906462903035404900101807000602c1e504c0100000c0b0710401d426040507881074800340045480c0d180c5004460b00354510136006680301c918022062885500c0070030700c80880f01c1340c0e4004008441c034003110140c90085089102d0728000b040040401d0b911010702c01842058025400402c0307051071424031210a1200d60200351103000701b0800d69a024002100b03803540250b00281c210304558070b080c000c40103401901503e5a000180c90404203072108044c04042c00c07a13000b030000c0380d9859142c0c03030307400316142404d076a440105d86240b144000d041c0040388100c204000600d00329081207502c1c4d010032205c5d0025114001d15201d04202000b4101c0302c200e030000103050400c0103043c0701032000c101262007641d84400710200250480001c03c0c1d0f4a881d00301d6 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 967784649 1250 967783399 967783409
    0x906040b030415110a140904090b010803070506070306060e011110050c070b0114010516080408101b0c083114271323030c0c01171f 58
    0x903a0340e10700303490980780b4408600c240d80c140914150040050000d1310041d2902444103890f903101e01504003120003680d4111410f241d034000d07225542d42e40041e00d80800b1900900700c00d00255120f440c83d141c03030740c21300d400104600c04140c40c0c00020042d05501c01d8500c0b1510000f828004091210704650038100100312450314a540d06003c1848001c1801070000e183d42400344030000400d98880d040c020000c100c4400c2107002444c01e002002139405102c00040c10784e44240c0c50341e890b0590350350440d414004540654042d056940e542110b03410099060216900130324500340c000341d103d55444d52198042c900303c140f08129045444d0800c04072101d1582030b854002d440403030f9407558407101d20095180c4889054001e44024040c50301d40350300d10705200317400405080b00c0c000300e9903840800c061141d91032034295003241d0401602155901c14100c2000c503031290b06c014503524816201d0003494400c03401c138464100724070b403002802907100e0960340c1c507000540d400b0500f100c0e03410709201c0e4003504403a03041 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 967785899 1250 967784649 967784669
    0x105030c0304081306120c05090a030b10031704090b01210b0109050d08091009290904050702010504030809160b0f09030f01090c0b07150902120d090302031b011202090604 75
    0x1001c070324130750000300d071001c81b82d02403070b0900c41c1891b41e060403522400f076481403940201018a041c40041d0450003110fa11000000c136110130f85640e92143d2071940d1000760f45940030000007405002c041850f01035822220740c2030805001008a9003102500c0003100090801e489550f81001d044aa00c20300a400050500070302e0701c41c0c083e00c1410300140300e0f8042022280b2601c440300b0f541c0c052501030003035402203890f40d4042503014401600301241c118803007061400002d20800c40340710340790394911815000307040550002940d441c003850007401c480b0000c0d0150410380e01c000342d2800d0a2700c02c034406200780e4040d0035a645e2180b4020140a807607004400031140d060040c0307501c80c002445c4c154810380c40540207011460065540300e0710301c01c040c8101c00c0c000d041548500c1c3ea204c080b00c80c540140c0002071020307120651185100002c241030210301c1d050500016613250042040d49410403088840504400c03140403009070b00d4001034424544032904118107900821004402d640300130a81d0010544440 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 967787149 1250 967785899 967785937
    0x150506070b10060c0c06050c01090206030f04060506031b1e090f070e010c020603010603021305060a02010f05091603020112022106190515090d150209010807030b0105030c030408 78
    0x2070070441c0c0450480b056141140a40800038805124400036a40d5942180301009800c0c1440c03000c4940340c3c0031019800b0259202c0b00038100580360740d4021882851003491141036400c243c5414003d0303604c003803c290300c079500603103044d1410f1034900d102040f1521308481d038100c5444004200c0b044020500e0030b0075840b10382c1c5010414900030000701c1e584101800d5941c44d580d0400d1400546d841210076201070b40044080c0014814540641d0007041d1103042562040b80d103d944100207020b60384012034102c0140d445884800c4280c405008441d00403401a01525401c0445050100300e020b1901c406070400418a040701e10050142e412078042e04035071125400c2501880b201d1001050042e07648900904c41c070000c10301c0301a011094101561001071400c40405522814080660000c0000c40e034030408083c1d0b0030002500c03800248112850491000d6140c050000001d0200d0500800e5241858140741c0b08014582e4094200c0c0d500c00c1c8a209020b480742c0762410720344014010200752140300c001c0c2e01 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 967788399 1250 967787149 967787153
    0x5040c02070510110607020601030b010306021c15062c211606090602060910050702010209040e010501091503032307120210200301150c02032a120a020415050607 71
    0x311150741000d1a030000c65200c6d403901d0004a9440100340b00c0507050441c460010300c0003450a80080c90320700c0380c5009032503140480c04040c00880d03030201c1103502a541d025408020031500701c5802c00c44140b0b43d80c1c9079488a08410400c2541101d800d48040c4103110141014691a121481d041910f91700e00e400c554030101c00e0f014100300320595004110100b80007020010302d0f11b00c0000c400e841124400040c0800ca44548002c1000e03210251410080d07540a102c01106a2540c1c49800f4207000804004921549000c01c580308680b505144143e184800c0d020610100350032001180c00c81c924400344100e2030840c4009140b0900070850020070401c0150346900001da4001540002149404000c101400b00e07121000001d44802000300d0780c42e03600388010003081441e05007081c030500c2c0d81d00b40484034035003c2d40060300340f03005c0c0c3d003a080321400c0c0081281c5c040a0f809140b070010a0003582c0b0f4090030503295111555400f0403100c0240700d591100c0d40d9110030300d8601702400003050f0280c0410380303800c118 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 967789649 1250 967788399 967788407
    0xc03050d0206010b03070c0b180d08010e01090c0c0b040f0c030b040209090c0a050607080d11180d0f0609022d1207030f03050c0c0307090902012705040c02070510 71
    0x4000260042c4500d20000c101c0200840849015849640307802010401a40e00d42240c5da000801140364110302443c0906e0100c000d10032407030203030ba06590b601e40340e60506d17a601c03010707003010b030031a081991521842d01402500094608002c941154202c112982d0300d00d004955140c50600040041002200000410144418060150b4800c45402409a8074110b1160341e0384c0146000c3c5500940819080005003403000007007c425010395a6646080c0c0345111b141d00b41c0c1d80c42c00c0b16a11000c00010030030f0070302c402e00300081182c8404a41d0f0003c041c04d183c841c0c0307220a13010303000546120741d00e003000d10441d6210f000408900b810070444018072085071b03490000c00c003800d00c025400349403080c1d41d800c8070030400304501b400e0700e40c07000c4040c503c0349080e20111440e4000a032054800e1040d89682c54144c1d40070404800140100c08021a240400d8400100042c04080d0030f003102c4018034602d200380d680c4a0038100183c800030780e000143e40c112810202c2c07600406501094010a03041c0300c00c0c06c4103900c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 967790899 1250 967789649 967789663
    0x1b180b10230a0c020306010e010303020d030507020d0f0309050604030807110703050d080702070905010311010906080906060f0a050616120c030215060114030916090603110d02010c0c0305 82
    0x44580110344840040162a00000c6407400d0010840d032800000380651000003801c5112410f18241581d0300c21940401e19003502a0031820b20448114010010140d040040510005062400b44072a041c280b00c060b40e00c44911800c10140410408603485441c445d52188000075040380842d52142080e0501815501083d1440000908003c806045080d000514541126880700041c45510011802101c1100340a0304034811030054140c001020311840c002c950203940140041040400d0032000909800040e90201003880040c00c04c1091a20010919643c0410261040c01400301035000281c6455003c2e080258451701c040390080c44500700240155006201e40b4000645265810099620352000d000060041e8003511448000340f810381c1c2e2042d0884810b05001d00320450b13080c00d008880c1c1003240c600010703503c0110103d408025107802d507001001d1100c01003145500315103502d140344c52400000e90241a065541e4000c59209a20840e04942c2215441800d641c1324a032072600c400c4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 967792149 1250 967790899 967790921
    0xa3c09050112060807030b04300e0d020f150f0c01150512030d020d11030c031f05030309091e18060106090b09040c090e1e0f01080304031b18 62
    0x4200c05061060100c82c3c8254010b407040030300100a02c51450f5201e542500000b4400c07181d407450f60301444034070f5400d403001d031210100d41e40303144101ea100700100403e009e07040540c440c40b82503500f64200250701c0d460242041d0400540d00406141001c06006859100f0310711860300c214000665025114010360240303003480c11343c1c00b1181c0210740c0e5001b046286141c100510509400c1003204855024440d03005108002c000d40c004a0305980d01078020301250001c489c0d1100040000080158a80b8074140c8010042400a2902480c0742864007003a5280a829104c600840400307010845068121003c40001980d107810403940d454903146014a081c58103e0b052076500c41e141c008568035014070340102c26520000300407403c103101d03401000007400440e6511001e101d003416002c140d04c0e00c0c1403c964450300710b984800800c500c0780e01000c007c009004182a20125030032005010848011044038100ca800c1080c0c15500c0c02d21a00c1c00d0ba00601d507602c41d02800440c10900c01145607181c110b01c0c02e0b49 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 967793399 1250 967792149 967792157
    0x20a1217010f08151302060d0606120c09140301021204120206090c0d0f210e030717101512050105011a1806030c07290c0a3c090501 58
    0x1c0d03680ea44840610302ca50150000a81042200000905031072800c20741c0911111404103200c0f5031a00803c18a51182d001740c020326482c0d07202400003e800056404000d541090208001c01c81424014509a06c902912a1455401c82071012958094042d60600b6140c0e103003240c0036003001d20304006801500f03400c2c20090f0103100002404c0c4080030540141248002d0180c8100c1c0001c0d40d42c1440c0300c100304000300e40720b4600c04541c4156104600b81c0d46040c1e100b07611b66580009404007014a04502a2302c40300c5070b81c1e5034a40500348800040b407501420740280b0808600740c8050040090381104c0c3d90048080d103a400d241c500c0c103200d4150007285c100c800e020300040081d0180001000c2c10320850054400395401d0444490490a000c0029070b4014138030340400d814030141e1380c3c0d041c2c1074810482171501c00c0c0440c054010380e400e046c18070580d0840c01141009280030603114025100b058580c440d601190109203244018003141500604043e00c0c1807090000b03280d44840142049190f4001e1038002 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 967794649 1250 967793399 967793401
    0x30901060603050705030714280221070c0902130b12061801050120010e160e0c040315111b030a03050903040810020d060503030a02060f1509010312020a1217 69
    0x4c103015074200e900603203090b44e4170a41d8003060804070006911641001100d0207940c84000441c1c25101e4040d5101e40007680030b00003142414014aa01c1c590080d45071040c00070801c401c0c000200c601e10180210b0744030800168807010121107031940f5006580c014102460000340103282283c024814521030141195564114460b50f40b1041c1c56180900805001c00d03483e5481e62804080c0c404050142111071001240035403801a016040510280d205405002551003e000885881c1081980402a0820103007041d1458803003503140100075411124050f80d4104440310500c0044c03c841d0101f0200640000345a14400d1841d644e9006032007920002c2d180001041400300c001c8122001c40314460000c04000d08103982c0303040254040c0e0348842c01c06588010000c3e02d910203102a140542c600e0300600307441d1801031304411031058000c2c1a11000302038000c110001d40d545c41c40345419250030401e4244848402d03001a45440305c01d900252020741d80c515a0004994000240710824034031038980001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 967795899 1250 967794649 967794661
    0x608010801020324030f16090f1103061e0307170c010c020f0135010f06030603050a03050d1d0105060f011b02121f0f05010b1611010c0803090106060305 67
    0x200e0100ba2842d044101e40f0700b044d0510950f80382e480c0109010010162010200c01c075964600e0504814000400801d946008004600301c9114220000c2442c0c4d1b000d001a000c1c10711464890300c0010502486105d00142c03603005c102d05404c1c0d0904100e00a0111590b041c0c840d07014455540010115015900c180c01161056510495030340d1a070035406448400c550b8941e20065800742d0203c90405921130045010486166821850180c00218081c40c00540d5040484c2e40410040036002002490700b0400108005100080c100c43e81c2509440c000740c840f040411200043c000030220001005600307044e101400781c040d44441d00400c021148684850070030001581c00000d10044100040c07403094480015003003034049000c1d06a400390a071401c1c0764031600c06602c030f1403a4030402a4030035525800075035000c07a03034840e150151000c121183d041201c1e0b021104034400a42000800100c8024401e01c1d50f64011101203400c6640150520b4407481c207000e86500808041c03084100107401d00012601c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 967797149 1250 967795899 967795901
    0xf180903020a0201030b131107060506010c0c0b0d0f0c0207090c030c120e07050d0c090b1f1d27060108061806010215130b06012105180a0c0608010801 66
    0x455a03254001c0c0403425165001500184004042950400e140056428a131070451007034843c1e0760108050542c441d135081c280744040311401840d2906020480800764003141d00b094001c41140c00c03009280e65105840c8010002070103000d907102e01e005080c1404440103039004900c15050380c055510800540e0100c480403019580c4020140d00410886506801c001f0b00541025054000e22812100703410f94801c041002c00e03d07001015184154061000c0c08200f156000341056a00c01321480603282006520310a01341c000e0f00c0c000703014030100d403011106041403584616640d0380010200c9140248071560402c4030704101151401001c0c0780c030000784080d030088000380d000c3d400140012414000713036082201405400f414103410340c0324103c0f201020308011301c41107100d00842c150203c0091030710b241010802c800609a9130502418048210001813000003003459100c0c0c0000100311a00c8401d1a40030801c07030780b17041103101c0c0035441529060002d000b01d0340d4100e41403562058030756a0382d40342040c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 967798399 1250 967797149 967797161
    0xf0a0801030b092d031e310b0903190c08010606090e150117070507031407051c030f020f07050c03150a0c050c010e0606090a0e0a02090a020d0504111003050103020d030c140303010f18 80
    0x2080780c9847e05000d0041d000d003d0060041d8000160443c1c1c1130031b8148040341608075410504403465440800e062207510703005e01400c0c00820380d508111500e6070800c04845201d480041444441000180f0366285507071241030403107620780c07401c0d64200d01d500307100b80000c003680e1050b041500400c140407034001d50750300c1d684c0803101416041805031070704490301d5030300310301c100d039030b9110b140400d500d884010446103168402085001600a810b555840d07651900509100390000c00c103100fa0480040c11414121200c4200d80c09400300000098501d82041d094490340554440114650b29003807080703c01007000100c06003d03c1c4200e5202d03000d0380d00d00d11000199000c0b030600d68035075041980740e41c00505205c1e10094101d041e04070050308119029034980120785040320141da15801003104d11009041c406841510250720340b906012542c1190041407203003c1c00b800040c20002296101f5042c80a0702540c226851003a5041d2907407540d6452000100c1007542c029150801d59140c8000c1243c0e41c5403045c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 967799649 1250 967798399 967798477
    0xe030306010e030c090703050421030f0612020a03080d020418090507080616180909030c0303150b0304020f0316031416080c10050f0a0801030b092d031e 67
    0x904040e60300e144040b0050040076004070ae648182554044070203c1043d0204c0507103070640e03000200182a010004d095600d1036201d402c20041c100c809102503221242c88100f40c9401050071540e9405001000c40280b150ba4010100908241e04180400d01c03160416000c0e1030040301100c0d0401d4070382001e81e469002c155030b07000c5c0c003038000006100264040c52088104100c500341c1086069541e805880c00d0b1810780d50102c0010b00d201c11201c0c200754051003044d451186040e5410815814006120070780e100c06000a403140044000b160865034003003010500320406814900540c0d5178070316103454030444407031042e02c00340140c820000c0881d00361a0704108490011008000d00d00b0144140301088010410340d6040080401101010203180002800031045030740c0d46209942c50360424824102000d0b01003491500040020035412000d000d0303001c5010f2513050f00a5904101c1070b4214034610503401c91001a00080e682c21905130140c00c00380000c01004040a6121881e4044500940d50180b6103 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 967800899 1250 967799649 967799659
    0xf01020c06030a151706070305070203030601170603032209061e060c030c0506090f1b0d121704030309051014071107030b010b0a020d020a03020a11060d0e030306010e030c 75
    0x80c0700b80f051500200303694944240c0f859982c54842e6074620720a1000c03071985545500c40030030300400b1981403041a5004d0b0745407014609505001e40000d251002c40300010000040c1000072032040e40e010f10803034680210f074003001041503c031403000380c80100c41d40c4030300f030006407a00d4800079814242c00e0200710040c101d00c042007031190508405a48001034a00180c04120015640a0004808000150040d40c000b4000c1a48407207070040d00d0b142044800075003510b07442489040e50503407994540c00384d0f40f6a20103125510310307141101c100c1d0082c00010340483c5007959031040c0418141c00d54808004203020340c040c4c44032882d103d0000d206035850000d02800d889407080014110030300c5621100c0e0070351070080c25038000039907985442c228400c1c282c000c071092036000510b95000580400c4011940601400034000108658401a440321008000030f8882080103408400a41d00c41049441e02925840c0401c450003c52200b20707035035007080320043d01240700120b003c0428900003409040415000b40 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 967802149 1250 967800899 967800901
    0x10e06040c032a090513050d09090b010903021e15070b06040c0c020a18150e101203170a0207020301050a060f0b0403080f07141506040615020309010c030203041d060f01020c0603 78
    0x44c0d01c00a0400801c0b0744015072403907010b00c00068091200540b484419524100700c6820b01408100b115617a9000c1410301803a031908200584507020400080007008080240103036800000c51200122ba46010700011000101c01c41009030a400c040d0107900140d604000031408007200b90381c1d10360a6507000c1c2d4040440c5c0001c20203e41d552a100306c0d10460400301190611903058a0502076500d6001001d40c00016002c02040ca4040701030718001b00314503485015107010305d0314050304592100b00c0c02100c0e0031035100000c014000c550101c4081d9070b4050000c210f00c1c40c05220358001040640602c40040700a05070002d60031151070203071415139402c2903020740f509521182c450ba240d48010001c40300d032a48122145800501444440c010744241c00b50710b05545010020032040381d607190481e0441d01c02d0456140046540081030f2a9698000c0c240f16800408509040c0c1c03441c02035078061401001009252940b81e004000c096010701000e540070701005403100016612100240c0019801c0301d8140 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 967803399 1250 967802149 967802159
    0x3120305070806011115060a051206010302040c020a03080708060d021203090906040204140105070204090f050f0c040903090b1b0706091a0711010c0c0911030403081e010512010e06040c032a 83
    0x2406d030381c0285005203d1000f1a076554041010304160400340f07071540d08540010800c3d030a041c0030340c2010922501c0603000d80401380c2d0b009011001c01420752400c000d200d400003006038840040d4078001d02d40041002c5050001308404a035641e10025a40d030240d440000404d4140c01c0c14000c2d1420340b9603c0c9803240c000c40b00c1400441d0b00f1380101c03806a0303106484480030f41c0484c400c484400b03891b80c0180041e0045403142d20309a4640049203140e50301591501c01d0001c040b9500080b224150340092580341d50751000d0a04208981d1140000c800d81c1d0b00824000181607900320b8400c0040301e02c000000704c0484d189462000c114020480e010f850101c848000c16255031240308401c00c624810f00c040d0003410f8542c14400121040080006c0000d18000144018103810401e201e034000c030700030381e03035440d590101442022560701803060501521184840a0740e1507420342056641450782d004881d01071510317007041001400385101c2520484849c2040700707000c900c0c500d0440e6444081841c0041018509 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 967804649 1250 967803399 967803433
    0x1611070605030a020c0304170607090b07021e0d05010c030e120f030106031e02070305030f010801020723150405150c1318090b131106180402070606031203050708060111 74
    0x41049903151b000401000c5500440c00c0920f1804c08441d0000704260f1900c81c4001d00710103041c1d042b03002c1d002414440040140e4880301015421080a9400182c41d12190041900396441c00380081465007401049600305525034881c0000e03101c803004032510011050302c0302030107103d00c1e9031050b12628100011f0011501030b4000003041c6018080700424038101c1a03049080ba0421001100000d10020600c00208041c40d085409400283c008603c0c184482d5950710348070b00790074801c00d002180e4008118070ba050a0000c64401d4a055118000c1e03480e040c0350043e01c0d040300d00c0c9078143c83e41d000c2000c42c0014034541c0a95100c0326001a4010b000c0741084000c000e0302d250150031001e03040d100c0764000001044050706501915201d00c91005003c418078201d88048001480c1c0c1c0d0044206009009841014282451020f10291401030759540745091010280000f50070240c5401ca000c1c0081160b00d0b07256100610448190791a8001c1d40c642d2001110801000c4041307010f5507000c201140f5906180b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 967805755 1106 967804649 967804657
    0x22051308040b0c2107061d07320d1104020f1b0f01020906074110050601050301180615020705040605030114010b0a050d051611070605030a02 62
    0x400c3c600d10441c0505c0750040d0a4a8817a80700740b0103451110b2003031000d1a01203050707603802c170f823100f2400480c081220032082191107012180110fa03007000042c100d961000402c03282d80c1100503200c0820744c1080609007603000740c0c20007020318602e4403500204030880e00700b0f454841244000d400740741042000c1e140400f45034010003c00001ea0340ea00c00311416075500110b00d4560144921610f000590000824046528104800304510007807041d504c03110755040c000c4501c010b018803182d00a580080e242d040c00b041d400c0c001400420180b0f184945020700c41400003590981d1449a01c400c02100151040940c200e40c0d02070165040c0341c001e14016001c154024060300711000480c03c08000140304000b0a51004103420801c2407041040354244003941100b0702090411450356001c007810340802d134021960010044200d110007140680840704180c445030f080d55240200310000e544 = true := by decide +kernel

theorem cover : BRFrame.Cov 967625899 967805755 := by
  have h0 := BRFrame.cov_init 967625899
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967625899 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 967625899 ≤ n) (h2 : n < 967805755) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
