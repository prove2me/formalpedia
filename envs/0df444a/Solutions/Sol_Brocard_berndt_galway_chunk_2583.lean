-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2583
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:08:37.302317+00:00
-- url     : https://prove2.me/submissions/abbf0e3a-d01d-41e8-ac34-fa048b1b5a9d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 464388489 ≤ n < 464568345 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 464389739 1250 464388489 464388499
    0xc040e07030e011d010e06011512051b0f071a010b0a0305041a1f0b1e090a030c060e03190807021003063303060f05101701170f060402 59
    0xc520031900a0340075072651210760b4004500304070419054804c0000d942c112402e0b40c1d448182d00200410300340401805040e04001c616007201003c940184aa4500305413294815680d85c04503000000d5800640f403080700c0550003c0c2e5403502a05582102c1c1c020042c226290210819002d201d0480000320b64181e400200166081c9410b800040f405040e000d4001d50b0710021981c43c24850003401d01940d031252042041000040c0035071a112a045031aa90002580318020300ca02290020309010600403e10408201030700d880301034001234041c90180d44028184551158001050fa40207801d000248008070250b070001030f0100c07030084512191300303c02401c40d10108020401443c0c091100c0c12513500ca8030700021801d4407095000d02400000d049542c01422140008001a400c2240a0003a41e210300c1c0a110061400b44401152001800303803034411040311060f0b6a0b5240700d000000380152881c0210f1080c8d5a441c0000401c00aa41c0003c0d135450244503030501d001e11001544900880d80a04 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 464390989 1250 464389739 464389741
    0x62802010b01080a0c0c0b01120b180604080a1115072d0819050103050a0b07020a030c080a03020904050103080c21040e07050405030f060601110d05040e220605040b0c040e 75
    0x320603004100b404000780a000706d90400d0030200e5020500d540c044c1484451300801c103403481c1000e601d01c000c02405002c48181000075969800ca02050064000e58414440c54031204a20410b566990810070060450b2084000344007440428012482c0141e9050721051000245c050756031019441d02140c4040400d81c84000b012500d00c14110282d00c4100503d0f0f007406054000ba0a10541d442a8015201c96020880440c00e001460b14070503001342c1140000d01d041d000380e50303028100400440f0003604a06000c14007504250280e0110781c0a0000104104840d60b1a4940fa0140c4d41002c03041050500c07603c5129003440c00d0a03015044400c8800b00c2080c03d107031070f0500840c81507a00910042c1001f0301400001481d44082017502c941c51583d40151400d880c000000601c1e817584030010f0305140d4040c410406103150440112015a01b83e41401c00d010340d10342c01130704070114054500300c03008080c5400711300500c00540d000500580c030907c2c40300c0307464964039010007960190380210618002044 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 464392239 1250 464390989 464391001
    0xe040c080f13080a08012111090414010c09030c06090501021009030201060506180f01091206020c010624020c060a20011d070626010302100e062802010b0108 69
    0x1901c581d0307200481d5199800200d105aa07414a9504155101004500c00100601600407152401c81a0342ca00282035403407080c05072208000302044010f50341c0156111070204062020400c201050309074141d0007803040e02c03035200f0010012074007440140c442442040000c58014410301c1c0800840d0f030142c1c0240740c03001d00c4c10b111000510100100314155176a0f20000181e03920760001030300a031a41c098003420f41c0d400080600098102c0070802c2810003503559001d12070102d0008030040c0e502c0d00014016114a0220784050041070f15400001e0310301400c520601c201e050f0503c41d542002583d50a95036110a1a0240a00e9001d994200c002040c142032481d507100c2e19155920f2010f00400b00041480a90209184400032400007202d459402c6081d0902c16150080302110440210a882c40140042c40d0140e040311007040c08024880c000403900005864070034880c010f000d017001000e107955960050880001d070000b5030b070051310030b0030000b89030703a100750045c170034104001e42c10785030440340366500 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 464393489 1250 464392239 464392261
    0x10203091c0c060510031401110301120f02090408031909020607030324321302030712050702100b120a0b09030c01060b0405090c16020907110d030c0e040c08 69
    0x901e201c20041c0c00d5520401040d401c2c01218000c44d404042a01c4070340c00c5081001b1121148048404141c0c14940720140a500d1407007140c1c111112210200c1422406142001c010098084087c0d8002024030503c014400c4840085002c0c4120103002140000114007002c02d8507002e0001030b502003010711100c1c021a019030041a1880f4134005020040e12240740a00145121a003040c0300300e620320018240101030038000c5e0151881e461051303502c4200b0315400505065410030007955640d401002140720f5038020400241c40e4041104107000501d8400802582d8940140149210700e050401942e12401c00707d0f0780c400c07003aa00e00058201c061158940190189000c0c00c00542c40c4410081c0040c652800e103c0d45000d481560213144e40c42d8502410400c01400c054050400b442c010420700c020031a46204106000b98180e55244080d500d0680c2501c08000c040004500760203001606000e0691590143c2d01054030354a47c80ca4481ea02c03024003080f20384505003034020402401c046071450600c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 464394739 1250 464393489 464393533
    0xf030f03051b0a0203011a090103150605030a03030905061303020d0e0109080312040501050117100504080d1a030f0c01090302010c020f04090503040f080a0213021b030414040e01020309 81
    0xa04240b0700d09060b520a0800d40d240d003410303a04080c0c01281c000801c6107000e001d24000604040da1441c24507090b800024288201803100074500a02d660060111031125005940200300050641b01540e600b400e01401619440104541c1401000300040440b003225118080c10b0740c01d80e000700200e400440f01a503000c0c40f81800c440c140450441c0000300d04a08000924207101a01d039506140d05141c50480d00b0740e40103810910b51442a4910302d542d01d80c000420b51000c0b400098080746a8032203052184092046011140400f4245100402060305002d5034a40e558425021207102090444401d03445468800307800d0300140040e102040075622545081c0d201038002003111500c60390020020b01181c8007c0f5040f24250000309082214640a4605030002d107501805400515121360002c1c03051403140300d2528071940d0100745c03c032500814070b40c0100f5000740403048a07030391921502038002c000c5110066511403410b02d2404848402d0600035079000d05000002041e003441010070752050644 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 464395989 1250 464394739 464394743
    0x705030609090a0c12031214040f03031e0903120501061b0302030f130510020a05060c0a030e070f09150302090105040e0a05060a0501030b060118060806060906310f030f 74
    0x410b0880f00780128a04962000062200810303004a01c950382c0340c0a02018060a440031005241002000b580d564a00705994455409070142400801e5864280c004001d0540e008801842089001c2c0ca01d0313030580d0280f184180640c03a03050043c0d5030010550103680c0d09019071b100052401e5490b0030490740c441c0e8001b11546c8680140d0f070400303104240d092080d8000b00b081c3e0840070324071300d010030003400c00703a150310000480c80c40609600d00312515041d07030728a4040c10210390700100007071607060644642d05c844826aa030100396180c087d07aa22500c14000311b603000d2a0303041444c207a16400e62413400030000d01101d034060061038550f840c0104110041821404d0040b0364001e01140000190303090203a1445645034076400140d0f5411420010303100c210092900e418070010404a4007400300c44c40b00c4104499052600227100c1c4d8544000c0340b003034000c1849190300482c2c04210607540b400d4401c2800000c2000501403c80c074442c0030058801c030242485480d43c1c0c0340f51410b0600100d07000e22107044a142c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 464397239 1250 464395989 464395993
    0xe15122e15380304020a0501022406011e1706271003020607080304060c140711120a03050c0d0c0f08090103230a051602152d010609080303070503060909 67
    0x4001c000a42e0710716010041a400e80042000210702d0203080983c0905420b100500441280c900311080048248540c1101030814a00091081c3c1c42001102e40103184020f8200010700041c4d00a05a01040510110b8101c0c0c0800001d2043c14030030819414004041c0752800030304401c500d1108031400c00303458840e0240c3c1e442d0001c030150f1640c1d001840030340d2142000701d9492600d4104041228038041c1c0ca002040480c00d42d0080c28500c00c81a5005150030140c3c19440b0f95190b0f0001d08082000b900400a50048100b40411b043e00103003d054518000000d880440c0403200e401c448864040368010300c80404400d8031400706103104040d1a428406042c00180f64000030400c1c180391421405c00706440d51028100410000e40740122504428241e104102e0441417013000f9403a00240e044400b403000090b00054044144d541100082c912030030b040894020746a00e03020700d02802409040d01042502ca4005508000041124032804041e5243d50941e1503078400c102e09410003425010f924 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 464398489 1250 464397239 464397299
    0x708120403020d140a0305040608092109040621030206090309030d1101022a01180b060f0607080403030305040b0c130e0a0b040c02070501180e15122e15 67
    0xc00800c1140300c5c00e160007510340c075481710f03c0c2400082240f1401042e891a54220144007010006200c188441e000180740d01d064650b03014001040c0140010f501201d1300181001c1c450f420200b0000c016071405019609469075541d17141c050035030f6071046040c06038055000d01d1004000038420030100182246000000d4600107220590400040000a8000010402800302c0d00510300074030940560180d84621034800c505503440721220180001c0240b40581e06a68031a8855a1340c90211500180c0c01a1940c1d1a6910303410300400500381110100c5012001d000814075281c80e640c00d0741d200001d400d040610300c9081170241d89a5075009040c3c10201034858043c801d55985a000398900d1130304c542d00030241c981c5030000045c400e6803c420400a0028464000c0c02a007584400f400da000451201d12101c0404020104051b058465681c241d5802020031032503c3c03100403100c8030103018090280c0e5107002e24000f1618200d403600d800c02d81c248116014100145000b80b94100b2440c20184a51a10 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 464399739 1250 464398489 464398523
    0x7060c0c0812070306060309021f17150108180a02040c050f0d0509010b0d05060c0f040308030f090606040209030d0c08040f260307020a031b0f090c020708120403020d 73
    0xe5080161680304000d82c4208014550b0750612911004100704c2c90140081d400903000702c1d03c100d00c0c03441041801c88104040d004a1400703050401030002c0701107031074015460a8000310408190503a01e2600083c81030000c11030352500c05030303d05140350000000e0040c5038a46d40c200001003001c50010700c24480c0030300400c091040140003400d04000007600220742440c01d0841942190075107000300b4820b00707a00c5c12890204900007812a4042844803865961b9000303000c03d202035010325031000341501c1b0000108450401b40d812014019403106080724120703200c00302000241d0088094140d050390100d0703100888144100c9841c0361340303401030041c0d40c40d080d15980104a511040d400c151030030118144821000c04071003070600301d1603612001940c144030031580020b83c050303040d1001401210003501000b6081c4c501c3c1c4a20001002c0005290341081d54070390a1601900c44422590050b0082040028050b0786c0494056682810784003210300d4541141d080040c00c0010380c0c016901c0f544840e01c1250 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 464400989 1250 464399739 464399753
    0x201083105010e03070b0f090c060d020c2e18120507030905040504170a17131133040e0106080114150a050a020703140330010605070809090c040914010b07060c0c 71
    0x10800c1b000300c50150355505041400c030b00d030221201c4d20000181700c006500082100c054455030ec4144503510100380300590f60342002c06601400c07000340580602400640c982c80d046002400d600d03100e500c03075501d15a84c1c0c20400040f540111800340c0b01c1c03904254503403202e400c3c880040c0707031000d0703581450440d130300e41024103250065080f5041010800b01020030000d00055200c00f4140c50011075024522a071180350703885035544040e12050701d00300321203901c1c0b401140c10403e0f10042c0010440c02d00c925a9102c2004260450038800d0020310400b82c604603e01d13080106001b0b0000500142c26031400c61030840031101d0350b0045000900318021060080005140007200907095800f0300001d50300c4090040c0000c020105503c95000d02c3e6904400012140107140c00702411149a41065501e4110908002d0114460031281f40da004030b03844200144c00a41d800944180e0700054810403035411620300d0007240031030a000e90100701a040c002d038030018000390810302c04c1d0b01aa150540104a41d5a00c1c54 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 464402239 1250 464400989 464400997
    0x207060e01050114151608071a060112230604020c0f070611030a0c080706020403051c02010b0607020a030609020411040303030b100e010c0201083105010e03070b0f090c06 75
    0x351140c0d456800400c050f00010714001c0418000329109041d007031840a610409104104048040c0c44001c1c58110612035213030207454070346030000e034501c4458a01c200d8000c0440400c0702d140e40498820031190700250350911540500745d4846121640b01403020003500c60713000c0010300e001d03800354013040f01180314803050010460f551008801086224102400039180d401c800c40030340c25583c01848820340c0b035a404150041c0440c0c000a03019620709250038404003038480c2c0e80010700709104281882c0c3c5d0020390140b203501c006170346034006c200c4005c490082207090310401d43c029610070758075501070000c01c19962080038141c2c401080010780461004c070101080d0000d40c81900400e5894400c9003007420070514a010004540c40c11b04000100d807000600034598940c8040d0400c51908001440d014402d482c1c02c41c0d440028034511061081c1001d840420908003204503115405c1148003200f141c0004251418aa440311034403c02e51f0318001071035482c420041104401d40300c0c14850700ea040d02c603a0028 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 464403489 1250 464402239 464402261
    0x24181d030705070302040b06090a0312030902060403120801060302040f210b0106081005100c061a0a0b0409110405033301030305041d06030c0f040b03060f04030801060e01021009020301020706 84
    0x40d0400c0c3d403560042000b1a04000c2441d030080d002000031402075680c4280b8401078940c002d107040c2802a5a2008030014460020b00a4014000141c08024410000030801d400501955134245030b030380320841202a40030b1803240036880c102da00340034080220440078841c0d01c00c14251764141e20b03503401e84a01001d0307070342130f8031450118071650184141d0741c20200580c2d0241c50251202d15003c00881d100500080c0c05400203401a565102c006a18030130300c079080c04090f60006c000b0642c8075101c0f04580201d41c401d100c3d003010385180050718200080f902003518203c40e8024040c02d0300500c00030500c80144144d05d042100e5100710810b003080314246215803400b840c0280e6030706890318103015051000d60300408410520b007030030200704509070341c000409402c0b00400365410500c0d4400d400c0824094200440300c56070600600d01085090702c2c190080500c114080d0380c804806076643d1100741c0740103114482d1140140c000d09031903a0090450b4004c80d024038130240c001460308106881c0c250440b03002c4240 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 464404739 1250 464403489 464403493
    0x102030d1a1f0c0209041401050405060a0b1c0b09030d020a021c030203100519052706010804050a0206031b030a0605011112180a03080d24181d030705 66
    0x11002160904590044552000000c4030b810018107800c09040702c0c2d52158001d104060400c0007a0420030300c4024069600401402031110741003624040da00c9840480721403001a15000b02070b146494446150310000310004080c1c951125140c6175050100750092a114652104108036440110307148010400c400f2541c1c060303c0410703d83c01080c844003080035415400c05005100384202c101d003e0500320121001200c0c46d10581610340c2d03c0091202e1035910042d0701c03014000021020007a813800c100c007144c40d0b504d60611980d960703900650712000185c0c3c014003e9031003644400e0040c1010340c0156000400b058900b5800210360030841c810340c0c030440c0c400010b82d403203103410011960005d510020114110003d000341da00000448009402509c1041d01c500a0002003498a9110b0200b901d01550f00112000d0345d5045481d001c0c4040e00641e81c641450900c4003120810395203118441ca015582080c800403454204404c4941c05020010f1031190207901c01c699500b40190200000d0500c1841000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 464405989 1250 464404739 464404781
    0x14061c1e02060c1c0f0f08070e040b040606020106210308150f1203090102010501170325050d051305150f07170406020d080105030f070302090405071a0301030519080a0e0102030d 78
    0x1c0020295401c05141005106071000101078047d04118030310740c041380516001081254036400070700681044080150003038a807041c081001036040d0051029164940c0104004800c0000e800460403014100a80069440070210701c006c406a41522000b400040c50344620343c0d030990019480c1c0e0048400544264000151010b4a580a002d01401032001c940700b0600d840911605c01d0b2248200602d942080100c40d02c0c80306154100340c20665456003050444049808090003d421680003074111180c0c0540c9400004592414100c0c5006040380c0d10607d9041c40c861550b00308a83d00003035070444150000601c02c45170350380c940d00030f440208895802403208074065800506503880603000280683c00000d80e148411000282c01e100b103a5058410014513540c0782401420403507160000603003c07101e1031044040c0200c050146040c1ca010f00261030780e003486951010111a44900002c11354082031104c400b10318090900440c0d0a4018015a803428000383d441c2c00840f0060741c00d02141d016816 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 464407239 1250 464405989 464406043
    0x80304061116030b01060e19121e0512090310050a0c12060302030d050c0f0604080712030b0f060f040302040e010204081c02030d051005030114061c1e02060c 69
    0x245030300e2400e68403264080340f4156201c44401c1c0320140036440501a05808031742068171800c60903074403d10320360407450f00c2c1500e500300c800e0365000030744060702c10409a01e5070b096202d82c80203c03220b10f5036000c00140319160905d8140c1d182030300700e510402d615000f1810b0002150b107950081704c0c070418601d400001c60780c2007008080d1100283c10317244038005282180920068400084070901200d46082241c2c464210f040c00318540100c0141d807200c01d00650701808204142c00b005407980030702c41c02e10031800500480d812012545082d036200d038004100001c9010710f00b0031900402d000b0000308002460181c0b25004141a05d0350041c0c1064903030360024007005600e205102851416151070049441481d410000a42c0d078000ca01d010483c0556a5020560800c40c207000d601c001c01015000340310726031032001450191103003150214011460100705620758403e0103010745410754400c0410007900007280c00c0708002140074070202d8006108111070944038108114411255404a0814500382041 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 464408489 1250 464407239 464407243
    0x71e060e03090303120a06050a15080f0708131403071b122406180203070e010504060c060504020d0204110703141908060a0e0709050306150919060803040611 69
    0xc208046141d041400180e08998010044448052204e44008280c1c0c41d8400c1d1300c8024205075100c9580000192800903d4840c0700080a4211030b190300e0700a0b0303682d200034080d03e00c0c030411a0034000103890200001d82220200c0307200351003680500d460246000074240401d10710341c0f1886081c0c800c905443c6105100054038085c503005401c0400c0e069080080c40d41e16250b507054009802c00003070b10484c003c290007004c103034001001000c901c00761016090248074214020345c0107458040000300c188002d050194000d8049608686066583c9050303006903442d140d00904003c1d00481c0d12007a10500b02015030f0740d501030410141b41b0092050b03544c590794600a000407c416424511180301804150300007441c10641e60441000b42c00c00c420f42e6641ca6001800704031454014200030503009040c0a14240d00c00e41d1503095410503000c0320f4a5484803c200140c15450303201c0180c0c890fa444001810103110300c18982070300f0007100c202107109038442a030711741150469088440001c3d03078080062072a20b01 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 464409739 1250 464408489 464408501
    0x60c040f050303210a090b01090207020f04050601020c100512010f1d10030209090a12080921070602090307030c061d04140a020c12070605040308090609061308071e06 73
    0x302c2c0214030348944c0c0f091a200c180366041414150f0f540c000001126880207401c0340340000d0344210840d40135a1104540303c000d41040308160b002d8101512501d00c076040510442d4090007058008000c071b14248400c002c020031410140701e04018003441a8a0242e142001d8203003c2c128501e5a0304032030b400c0c000703040c1624100f03900343d602050401050000070002904801c042d00e070166555a440d41c0c807010f03024540384e041203008190341c121110005540381e1084a40c2d000b941498291a901d100d454503224480d0390010540404c000100b00c0703400000d0031940103100401d23002d01a6901d059898071076580c02000c0785c1c006800302d450103104075401c0110f01d00e0140c0340d20b07003185e0402507681202c41010101e080200445034007540080e45100407041003005a4100c00158055580d5540510308030020700340584040300807491500108c0c000c8000890307098410b040e40d42c0140131642d5003001e018401d803054542a901c2d400d08100260205003403000c9806230040108907411000c0d82c40c030f41182102c034 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 464410989 1250 464409739 464409749
    0x406050c160303020f190309150606050910020f1905100c0e041505270c090d0b1e0c03090f01110414040204171b04020405090c0706060305060c040f 65
    0x108200300212185400320015079181c051400584403480316100703403400d1003a0708a56900b042c0b40009890515810341041600c1441080300ba000c41c0c83c0c85844200b0340b6864010480401c0050102480304c0c03e0030329514034130014a10407544603602009209080401e036050140c80d41d1550f4202c2c44c01c1c080100168104072000d143d0800050389080c0000b0455194050b049201d5600c1c0c500070307480000d060a103500a04001007a902602c64082c1c088001d1003c1440e040030020800340010342c00225070416241c6011010340483c841d070030540d075014510140140039820301c00c149034000315003a001d00005481001408501c0340d4900385800780c0b03480c0c610803203901c0e2003603818914145601c68201e025103086070140c008044c000c0720204000f0700680110b82205803814a00f04000340d480300b000074071000e0b0030303d12039810080414480500041e81300c0c2d8012182c01c10403000104003d4142c0800414202c0c0c0030707910000780b058403a503d5604090341900e00c81850000410113001d03240b48203456038001c203 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 464412239 1250 464410989 464411011
    0x613060f02240a050910110a090e0601091502030d0f0e0c19060e030c04020d0203041502030c09060a0c05012a0305010f17102903240a0f090803040605 66
    0x409007541e030300319007038000c0090603d581c8500202c2c0f102c8204001c1c1c0c0d01c5072903071200d003031020300c200030070340c2a1940080040c540002c288510016900441321402805401c06a55107038076907041c140040c4680d0300005015046100030440c1005040f650301c121400040c280401046410071072540038640301d80c4403900c600c28a100c00d0308400b000b00e040c400d8403c03285141441001d0300c4428001a040c10b4034104030b1504180005030141210389694010b510440c441e5110140390741404402000728081243d04005000301040211601e1910303a010f40004445803400849070801a682c080c2903606505d40b09039060314034442090030140780380035038000303110300d1604101c558036040305010307204d0107841003101409101c050180308072000d005141182254180c1440050660b01100d04419000c00d10b0024201803440c074040e491a01040e9401d0300502d040048001001c100301d010020728001e02101c1c0d032140d40d9600a04004810f000324002d40d030042080e15201c0c034250800300c09070395000b0500000c013 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 464413489 1250 464412239 464412283
    0x2210103111f0f03050a0924060f0b0d02070609150902040c0507080d0e0f061008060a0e2515020c040c020312150a091113080c03100b0613060f02 64
    0x2d0350041d5a186122000c1c07034081290b8440c4141880104103c802c060300b12210002005122940031900d07072440108030200f0800142c0e18445030032044180d00411400408c2040744402c501d01c2a0050b000240c081e000005114100e50ba40a00c1d0f2141d030103a61416507281c800e44003c0d4a42803103110403007030311414040d10b00b0f14070381d640d810350344038410391407081d5aa80c12495244000c00c1005030b1294110074210384c1103041070070318024003054501c11402c0d5032003a9000039101c03580d0381c01a42150b140300b0f402418001401e0504110402c42d0304000d4104080501d800101410702c903084100d000b5198014040800390b42d0148015501c2d070507880401d41d80100324801c4189010a4056408031038420301c42440200ba40009507426140d62140d8840e5003031003001d0060301548401000d18030101c140001d8529a505009500c03200000d21b099416084001c1c0582c400c3c0b0a5004084114001801e05182040c0340c1c018148501c0380307410a0000030901d6042d6280d050301003251070300d207040d680301c06004 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 464414739 1250 464413489 464413549
    0x20f0609010c2001110309030301090501051c1211030f0a1b0c030803041106211f06030c11010c200a0b07051803151f05090a0221010311 60
    0x250741c103000b4641100c8500e840403e82d03024003e41c0669903160344061401e99074101070074480d85d0394000780200c08040745880c1c00000c2c940b401242c0e401e600019000c3c10803061a803503c1d200711452180c02200284100c1c1c01c031311452040244024680c0405400b16607840d5102c9a000601e0b900050701c070120002d00703104180d004220060243e008480d03020306155529500c03032a1840146852221994100c07501041c121036150690b584550000381ca000070043c40d60718645c09000b0500c6503001c42e62140003020382444018400d4001c001c001c1000d0804c00074050f00d040d6481d0848420248240014032443d8403587c610f41c0950010110340080c500510842e01543c8819400c05400f0703169000f4080b00140c0701d054a04211405103050f10001d040e10b050068548100302d10030700c1200d24801c075601d030424000c0d81e02e60b00c0e070080050b5480a403910b01d079035840300103020007548100390b00c41c111140e400000b64824083c4007641e002c0c600c00c2d00306929020b8600c0520000b100000124102415030005500c1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 464415989 1250 464414739 464414747
    0xa09080303130803130b10030210050a0905010f0c0510020c070b07031202210f040b060109030309180914070501091d131407030b04050f070b03040803070e0d03020f0609010c 76
    0x929070341040d4615569181d880701d440442200317030b60062508910070708100c00036480119150469000341c0750b0b19104010604100c446100ba4911134020402d120003e0141d94880c4500b00580501810b01803030200083d00d40714904682e440315040780640020710b1a00e43d1383d003400035900520103115407071305140301654040c00a5005540d24440194007041d0340d034155003510803510800000d004000310301e08090404c10114002180e050341c00205482c0072031455481201080100c94060399004440d40c206820947c040c10042c0043c80320359160200b900100d9040180c0c81807500d010f8004203441440d01c400940150782c2d40c2e00c041d0b10041c80003241ca007083c500d00303215070f03205171001c0e06200030204600e810786225035001c482c0e40881c8108000031041061150045004034080d000f1554210400c5901c265100114003604040500c244080f03000241e42c4400395801490605110510003441c0d8045010340409a400f0350050b8402110500102d0051201c83e4004070700300c2c000d00810455001c090 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 464417239 1250 464415989 464416021
    0xa110d0203070b0a0903020a0b0705070b04080d0c050c06030106110705030105041505130b0a0b090a060f0315060e190e060c0a120225120207080c09090c030703080a09080303 76
    0x8502c0c020010b603504c00310344a0746001028560041c40b0250298507045403d02682240800b16034174400e410380894400d4056040e601200c1c000310042100a0080e0000c03920070841403000c4502c1e101d40c201101081d5a1038010352b02030440b03a0f81700d0004400c5602030b14500300d400c0c1c0c085406a40b4110a02020a031800d0f000c2403401b0005d400400c42e43c0351a007144060383d00c080400fa12000c451030521481991030341041040d40c030b0403a4840c9068451020900c12a0b03681d1144941c102d0040794104000356583e40c030060301b2040801d00007095681e403000000040400c41c0c0120703980e00c0aa4611010000511400410070840c00041c500c40c602142c1110381480745842180c24403105a04e8840240c4254044995618202511044000051107580e00c4a503480c007040791050b40201000001a10018821045030320b48002016a825003030700748840008060711030550b50027000e41e81d52260310100b10703c100a502c194102543da014004000301090880d420005164204005201c81409410210 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 464418489 1250 464417239 464417249
    0x1c0b16050a200106060905011202090f0904021314042108060609210f15040b040f020d0602270d020f040e0f0703060b100c03051803100e0a110d020307 66
    0x2d0204003280c84980d02580d1072105900459609000020490607403100808084174400c0e04c2d107075034850034820303007100fa4050401c03107580081c0c1c181241f00741031400c0c90406800c240083d00704004803180804000c143c4240300c4072107007100e1203801032104100c512902c04500240c1c481c48401c4c010f026810080c00c80c40701500161240c080451030100345e94802510150308021050018609041c11011a45440d841c010703501190049904815000d0707a680d2038944540c0c6e000040c0f11059071640ea50401904c21184141d800100000c0081d002400a200074141210702070041c00413804880e40500f0420302080f101401102540d050500685540700a00b0480c1ca00700d4000c14501a900101481c0070896904141248529200041400132035407004042d680c060750700b000c5610320014203442041c00c2c0304c1d004001450400030380805117080e0408e000032100003403d2320310b110000c29941003551b00190910005411400c00300082141e551028010740a003602d00311600b1840d9000a920b90742c2034850 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 464419739 1250 464418489 464418497
    0x3050a03020a020312091008060111010c030b21070603150e070e04060b0a09030602032511070e0610201e0114060d030c050c0a0e150306010b0a05090406051c0b16050a 73
    0x30270f150340e006003a0340400c0078508008129041c8a00f01c0180688401d20415008801b0a4880d028140111106001d039446071802004181d00d082000c83c0140010030100c290b440810f8804940036004401650280800e80c3c0c1c2c1d80714505c40030040100715296940400d290b013504118024140d078022031a0011203401003401030f00c968070b041c806000111040303500c403e41d0488051035843e05411240090b800c58a40044956243d101d0915081d468010b42c0d91650040c0d5203a4942e034500e114121007840300314070301000302c140c01511082d185000c4a01d14000c5d9002c240d401205000b15092144004011401d4085419420b0072404a110004107580c0034080221040e042c009001d800c00000034010f0000d00380c03915042e40d420a200c1420000e842600030f030a8030b22016a401e01d00051a18185e4150481486c9403030919241503800391700150305c0a80046d01d40d030740080c3ca50381d0606c91400586217840851240c800e185003202c91001c0080240040410aaa908541692000c00c2da1040811814 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 464420989 1250 464419739 464419741
    0x6080601060509220c0809060103050a0b130b0f070e0a0e0609040804030803013210050a02011103040507090507050f030412030f0203100801060f080318040603050a03020a020312091008 81
    0x2021071421450f50081c49001c100484c4030914041d070300da0140c04542c076156140112034035958445611094288005819507001d903080c100442d020402040e045190011980e802c0c903070a50701c84440100440c2c5452a118416040103120364001c08610340150045940300989400d201041c490920041d08450240b0840400501000400012103000c0c603080f032035030b0f80c03650b0351541c2e100143c00c184115a03200821505510103001481d2148400c0c07034000524800301b030801c080c0203e800e81c00441602c0110340d00d036004041910301210045004034025000341c24014140440c1509a610150041302002000c00081001036410001d494000b94481800c96030a00303a41d500302d01412200d0f148100c0c00b44004248100d4500042445017100c0400c402481015031394131000001804521070010b0a4000f003040c0010f400d82d030403440003218001000050015241d417510362610110700c9048002d603001070003d0b4150328080180125401210250b07a207801188004607040d03000c0310400d02d081c091040 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 464422239 1250 464420989 464421007
    0x50315010201020f0f04031509151a04060b0904050906060901230901060e030c01050f070201180b04081b030c0f24210604020a170714040306020a080a060806010605 72
    0x90111000e00790481c2040340c40348113480e2609410340c0075200480e5000480230b40007507801c0090098000f030300c0c0c00c5400810300801c444d210b403010341603a5007080448464801440300aa0f074a02c5000060400003041baa103a18441003030100b1904c4c0a08a18920750100d010000f644d520b52400a06450705200035107005c1100154001080007040320f5582d110342910004502d07950b01000b000c1102004400307d4000c400313440e0064500740704c0c00500542030b00f420000704000d5401182d081007245c5d2004500c800745a82d448080f031700da401503044450b20b0740048107502192400c2010550070700360114054003140c0b0300d4030009420104000043c5000e403004588601d0543c0402c611001021400c06030180e43d0310388054000c00820200768030350040001c401c003140c42400c143c4283da880c110103864201c60101168480c0c250100002c0c901002c0191220a030b9036006a04805000214401d5174090303180d00004501415289009001c0280c613880c1040406c036600001030100e04450490514070b989078191 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 464423489 1250 464422239 464422241
    0x50c091c03090305030a050705010c0315052404080d20060106031113030c150201022118150601030e060907090b010203090d050307110105031006050d021c090309090c050315010201 79
    0x83e82c00500a400081101c0f06415003240003051030798031a1000300b080e040005815002c131290448208140041e81c3c00901c00b41c02e003500700360b0486000e00134a46ca41c450010403a03142d0b500c0394119a01e0740c0c200509000150340c100c006060b009072a00c078840584507089a249554074014400c2808054447d0780500485c0c4107a8121106488403001032180e094603801e12200601d140c3c441c083c010b540c2000801c0c245481882510035003000611268018160b0740014030000102514082510219141e21030380020100241840c100c804031440141d881c18500160841e5401481e03d003043e0003100030081100004035410054640c1324400144403003203400100e01d1805402044c82d040704c66450101d06202d00000a4410b03144500d00c4210394000c190011601360000ba5540101e80303102480902c003540c014400740140f001c1c52240181040010b00e10000421807410b20070f940103a9690b804000d241d4403800b6203025000d00340042c410030705031180c0145644002000059100f007440861141d40c0e1003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 464424739 1250 464423489 464423507
    0xe01150f030b041406120114241e0a051203221511010b060c0d0c06022503030b06210c070204060f06030605041815110d02040801050c091c03 62
    0x8050810400c004c5000354803202c0040580f01644100c4184980450340e80741400342c002405106515000281c80f610031144080200e40401e071013031541103000007000d450b001201e01e481e51402d000d81c20740d8481c07442031018002ca590442402500f808900500101d400411180c01c100c800040802405010310104040415a0041454000c0003510800c0306c6034401064030204076500000c0026006041c1001842e100b8400e0302100e13504a04469060301d801402c4011460340500760252034204c50b510340c0e0390000ac002204402404882c5c90380e03002d00d42c0c03510030546003a40c1560250304d04842c500d40c502c4803d4506e0821120b1620301c100007044c00625001341e0300342d00c0c0c0c06171041c8041d6444070303003c003082d900a00800c0300081c680440000d151801d4000d51103d00f4241380000d0340d507090307a1200441209506241410329898800c8540032703840031801041081050480140c5681c244017409003910800b915034108441c0c00d000d408131035640c00c0e101c08400b04220309110907442c020314003070f114010 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 464425989 1250 464424739 464424761
    0x3010902040c020a06050f012106060b0d02120906101a040302040504050c090907060504140303071a0a0c0504080c040203070219030207050109080f060105010807020a051b0405010e01150f03 83
    0x30910b0003051000743c00040348015a0721541c0f00b03003c1a91000741d02403031490b091150310305002c0580b104030780140e03c1c8104100305c01d00030000440c0303c40e2030b02c0c460903480d03101001c121281170f40010f1710313450300782000c44041e0031560704006024182440407003030141400078007940e0101d5800703d9008141207950811200290303030103481480146454242180c54201c8140264019000407000440014011907000c041e61699243c8500b803504042100c07002c2c04c501c0848507058403081102e0303004514003c0023040386181c0b00209900710303e011940007050f240c7c0d1035110410b010041c0400c2c01004000318904542050a41b0016100d81e0380d40400c034a41a000016407995081c004104414158003252a03004e030756017030300c8149501d03940d52902661446000c100d61910341001d00140195032142950300c0e04902e0610454400300030503190142410803800d039800d9041c86c00e54074000c83e0700785802103600509071007100c0c00042d032400344004103a4400200040812070103401d81203249010f030340718824142d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 464427239 1250 464425989 464425991
    0x3010204030501060e2d040318030b0f01090e0a02150a0512040f051506100c021f091a0a08040303023702010e1b0d1502030c03041403070308070e0301090204 69
    0x4d40c0c5e074440a00c4848003641c11840d0404000c0742d00044800d40322485c180c0c0d500b116801c1c0002c2e03031542c03001c950300c1410340c1c80d4103420584040004003060f0000100d03400352104407042d0314103500d0199100d0482c1e5a80a8000d40e60301300c03480410160313840d21568803009560440071913840d10300a804076824419150083c62401c103040a000074800003040c076081e5580304100301c50a1f4445500c00c03c4c4240002c80301a40e10a00a000080c07000d48146400c0001c40d1001d007518070280c14424221440104c5c1d80310120018501120400c40054810004200b410941c24054a4000801e07802000380b44020005001c0c1500068804207011003044180050607107030b816600e180005080401d9040410145100190700b80705081002c184040f55034201c0a0340e13000d401841c1406c51080c041c901012031020b6501d80240000340740300a40b00e0008610030444000d0707041d520710349840c0100c8410400d003200056640f0501c00c2c08000380c0c01c0042c1d2070300040c440c140202011003d40000303000d041400e400035046 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 464428489 1250 464427239 464427251
    0x901060902030106091503050c07081602030d0e011403040b1f0b0f0d05151e011115100602060705091309170406122003070908070b13090c080109020903010204030501 73
    0x200c5d60003007142d030544043d042c1c140409003548000b1130075508107031040b8921079420131074000004c1c034000082803260302c3c01101e50014030b0160000307030810b0311400c1c0c8007020400d00000100f1a69200c03810164030382c2c01c0c40306030741181170039115001140341c010a800300e9181c0c1c0c01c10440d2102c0502c4c0c00c5100038003d104406607503808072009410240c00c110000c502c17031410700012411078981c2030240038544802a01c201191010420810804641c84035414180104c3e1490050505e4061090f42084948a1040c802a00f4078901100041d0b40c039501100440d0407140a00421a60040860b58901e004580380704070881c070306030b140000b00074000000303007a010801c00030070481807201301400850b202902d41e102c416048110140944034501a03c4910306045884011a43c4444001d150070460030714000141070b4440324001d00d000c080c0d070010308904c2000314801e45840d40c05040000070380540321041c4480058000040c080705418017411a004e6000314203034070b06480c00d40c1514001d5400000038814 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 464429739 1250 464428489 464428499
    0x100e0106020d0e030c010e0402220b0c0c150403230124090603050304120f020d080705010c0507050c0d0204110d0204030c080c030604110a090c02010b03100513020909010609020301 79
    0x140d00540e44503200030030f0241d42e01e00540d10300480e1026040c032041e1511304818034002c0402000354009250344810880d18866900d840300103100081c0500031260b0000d50307400002c02031a15004e0030305d040c98454160f60a8110f40741c4d481009840450754400402008110000890789015081000c00c04c0035618003400c00300070303402540d001d03940d07140c810b10050220754440c41007005a4009000c081c1c4254801c00003049611010605c81411300d0180d880014030040a60004030740020700403042d40c0d402c6020441c6014040300b0b100d858880885403c21601d0149541d42d032070746880c0c1303510010b8821240001c54034195102e90700035040d0030030002e02059550100800050003504140425601e4103030f00034004c145441c0c006071034112950010001d050301d90b80c5039148814091000050340d00030310444400100307090203000e00c1010681d180c0005c904a0768050600d4900301900764031082c01400d10003440780001d501809c8080c07151301039a224043e0750740c620190b4050000c0b6402040201d10000000403 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 464430989 1250 464429739 464429743
    0x1e1806140402041103011223030f0a090905010509010306091103030a0f17101a040513021c0c09120501090209150a0602010e030a05071e080c0c030a0f0803100e010602 73
    0x84a2482150304001016070f0724138000d50f43c042401241c0110314040c0c41c41c0c0c086048030b2650030907080c0010000741601c0010a089045030000e00c06241920804644801900d4011110034050680d11500300495803403e4001080400180300c003400c0c0c0c681c0e40c0e203203c090007064034000000d05805412207503191051100201100c03045807084000504050081e5400c020350540240141c2500c22500c1c01e076420a089800861070304a0100103240c070030040040c05444040031148201c003c03100041c2c0783c4071001030300b168841403142d40c8407159180c400c604001c90b4000c1c2a03070003940d20001c50305490412500c0d20364014910098040c0d4044010010410501c240c03415044c0c800e00181e58002c4060f6485805030300f030f103d081c01c3c04a0301e50010300800200921801c007911380180141841901e400ca0044022648800c030700b01590b00031000075442408040402c0301d0300090700141d000342141a1561211400900203410041280c0e030000301090b42c0d000c0000003c1c0142c4400f1300388500e1540e40d5030004e9 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 464432239 1250 464430989 464430991
    0x80c0d06170f2b02030c010608070f050d12050904090204050c0307020d020f150402010c0b0a0b150a0219020d05030c030304061404050309040509010f020c07050901091e180614 77
    0xe5452144a9100c84102004035000790402d05100c0b5015800d540c4902550030b02c000c4030125000c600c17060040c0b0b154a40f09000741e01c024020b02d00030f41446403c3c56500c0599a000b030300068000c600d50345074100051340c00e44a00c103051502e858502c0d2542d0072207000a01819143c90085d41c040c0c05d11040c00003104020006500415007a02124942030041d44244e03100e001884e041401900103074143c00480d00082e403800d42c460b1051420030042d50065540303a150342415100d401c011541c0741310424140c24410014841116580038842c200100131000035900c240f01e1101070425088a4803040454413040d1803241c0065000042c2da03182d8003100c05040da00c0e00f0440e010b070350741d90400310016a11480d010641c0d00840c1c000c0c024618100d04002404094230016022031455943c501130b001c010040340c4013400300310311120040e02e481c1785010704000541d00180c00c20b05c45030303141c0511100040020380900c2400d0b0985100480c0c9200b01424a420421502c103000d400207081c640301044100082d1000303 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 464433489 1250 464432239 464432279
    0x90f061e0e040e0a4205060f0d030201090b0c0310210503040e040606050a0506030609060f03011b12050f1308120109050906071e121e0e0d020d02030a080c0d06 70
    0x250503443c0490030304075649101800705040004c01e0351440c20345c206508901e03804603000d0005031002ca015030100d81a19120390003900140d5480d50703800c041050000c10307941c10800002d1214214240071304000382000c014460448001580103a02860302001c1e03800d4008242c210040e01d07107d85e03907000010302d13115040700c040721001d1810001003003c0c41e02c40c00d19001c1c2d640181000781166281030078003103c030b003003e004142d02c0113080307207203860bc1e647c2401181e0b5482000a04036100e001100006003041c0049840c0314100740c1400704006481082503d40c951200f000242080034600d2401c20721510711500d502d0252204d400e40020643c52003640105000340281801c5803021765418008442c4515003120114960241101100c00703644104144901410107890018032602410044020001040c140c0d8010035241c2e910540110001d100408040400f070000d400c1401845100940320311a005c0110305011000010a902e003602c02e042c2e908400114804100e400d844203070400c1c002c4540c01c2a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 464434739 1250 464433489 464433533
    0x90204030b250c03031d0a0503091c051c0c050303010801151401120f06050d0f050f0a15050c09100201090203120a0903080a050f0a090f061e0e040e0a 66
    0x202c0d2442100c19415940090704540e00c903902c0025507030f412006850403c035950340700c143d00c02c00001900c2040c40009040d600c9400110b43c6d070004e240500000764502012640414407090380800442c60105e440c0741c880d5a02d01c0c0405070708116000c282c46961102c03001422a06c0301100100b8845015885401d8082c046408003441981d00e0f585172440b0f0703506c0e0039003a00083e0840040300c501d0640d50050082c000300d1200c0462966103a41c0403030051000c415044d40e0b2500c15401500034044113000c03100d00c40601038007900ca4000305171a500780d40c0820201001505640b100028118101e01c03050b1814804010640c414180340941c0080c060845d0f810280c1c0b007402000c00c20b4840842680031610381c01515100c1c012568a151a51041600250003c01c103000c01005800080d407410001010300030a03035220b0889036410282d81d0320402e4002d8200205108a812903030304c41d0b2400142c0c000100c0a00c1c0b40420211000c4c0c004140500442042c40116214040014042064481800302c10303c990f121 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 464435989 1250 464434739 464434771
    0x803010306051b07081207050c0d05070c080f1f14150a1e0506070f05060103240902011e020c0619021c0c0b100308041401200304120309090204030b 65
    0x3104983d144116000141001e5007007240d4000413100c1d0801175809141030403c2070421742490034250801003c08074000c005032001601c94104400c9040311070140014034000c0c541c4c800303103011305551070a031540d400884c0d216003101018002d2560304002402a0055108105401c0105c40f110881c101c902110b80700d080c0925000c101117207941440031480352485040661145407409011140e40802d0060764000800306101010500030001140214441e210b10045c503039145400d000450341708003106425900300781d1041c0143c7e80c0034401e0260800d460b00d94041421108100ba071805075841c4400ba00803c000c1540391000b14200d64100a075411a0240d50304094001d15441983c008143c024000c10f100c4d011040c08a5006120154400c8030400b00706003490326511003a0068002d40e20032041490701b006002c2c80fa5a21650000e4100c500c0c00d42c2d100300e4002ca40d051510ba0103035015a507603600c400c83c4018185031107120103600030f101d40001103540b19141e08007018040800c55042035040303e01d070 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 464437239 1250 464435989 464436031
    0x10031b03051506071a18070608090a11190905070e0a08211b0c0103140f0105060c010f020c0102040801270b070509030f0705040b0f0612090a080301030605 68
    0x7005082c840c071855503004050040c180704103c541e40100d4001d03201c482102c10800c0302c00310039102c028000c2c4a5500004003048841d0419454101c260304130004203d0741c201809040c0500103052210746d03502100c1e100307080c4070034404242c00d0014501038441102d010300001030084a5680140e0060949139144080d60b04440123202c1000c200b44191125903010000c3c010000072031010b22140103900402c820300c0c00e0444e81c101c000503480160b508401c0d40100014940d00c0d0781500c600c0c4401c09007990041800d280ca04d14861004034144582402208001283c1084080a60080f042407280c020110348070b1550f100d5a50003500306004a0440f986483d00c1680041000071081c030f0341d0344e50102003954500441c0d641d034407103030301c0549808240303e410b0080700300c160307000e02c150f0340108200c400030409070b0315040801c001d840d010070303119006d03852110040100c1c1e02c64a04950780c0c141e1300d0303001c0c84181d205c810700c0929105140d800509200000b10002c0200241e9801c00c9001e143c5070a8a46500156a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 464438489 1250 464437239 464437241
    0x90207080f030a060329061509121f0605090402010c030509060f04031203060b0307050703091701020703031a130b130203040515060103270f02060f0901030f0209010f1d10031b03 78
    0x303280e06c60041a4001c00942c981ca00540344800192010414504200c64900895921040d002649020f03400c000400c0100842c0784903030940d0300001c440c05010441c98000070905110b40070b400a41009064540700303003810f000301c0444603080300c040d010959404c50030755018215005800121901d0101c9040031030030501c079004e00f2080c1c811100c20f180c6143c480d481d041d0703100c0d400424103c0c01d0104048000802c1c03c41c80b0404125102044000350b9615003e260007400c858a0407110801c1e50540c1008041c5925044030403101212580c1000801c2440c04000501e10762008034900d1034240008200001c210700458803042e9151a044180c0d003e440e20300040d8107031402c0c0b003641d0900c8895010a29031448041070b8400b8410b014014811590485802050103503003c0c04081083d1207000603020050750f490311510b4012080007408500780061031000900307030070070540e94004204000c001907154007503404400182c020000c00800007103034029009009006d080c10802242c14800c0c080c0301c211402 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 464439739 1250 464438489 464438543
    0x1c0306031109060330070f030e0109080706050d150b040e09060f22050d0806030c0108011203030c02101401051509181803030103050109020906030d09090207080f030a0603 75
    0x80c050102c420840c05c1017505c0c2800a0301d00043c1c0b502c41081c0144800f0000300800e000e50154903204000c200303d013006044032608200d52410803103248802c00c10a200450444160b42e03080c604036945a1001e1441400342141c01ca100d5444c40c2c4800f80010000b1445001f8402c03592010021091580e9081840d034892800300c48044641100c0d030b00007100b282981140740401c0c500100c4403460000543c89040c589004071410502045091041c4111464200000c041c880001d1074180859130400441c00011000d241008080c940c46610710081603000303200d014046203d0040c1001541181e00e114101c9803400c0c0320f1a80a0810f1404103903601400070b003111034000e8060003000c024804842424070004c40103016004a071158460341c2903581090008500950180001050900403070040000c0c020b0003800d1a4440c2e4802201c861140790407030243c1d011142044401a1102c0190400d00174510558400002a0100000301314581d103859004600b80d03030050310720f501d0100030080007903404a4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 464440989 1250 464439739 464439751
    0x50c0a08090109080d030f050a0c0e0603040c0e10090f0e0a12021f05011410090306050912070b15030c0105040e040204150609032f0d051c0306031109 66
    0x102006280214150000405103680c061600c20b0541e59039182003070a080c00040c10000203900c03600c01502080d214060310790058140f02c4100100115070b6006132160b01464a581c1c0900d80220009041c0810890144000c044d40f1013606214a083c1d03a001101c00640d008a18101e8640320000d003004101d40b04a0a0070342d0300038000c04a0700d20607151942c85205120340b40707085100d0030780c8460b04981c1e07949241c1c8807800181d101040c6541002c2c41c5040078588003c065000b6202d281e5110030240e1701c86010f0040306c1e0020b40000782c6032140f90103141400060f228280781d005002036590100b01c05150898410500d9603042944c0710608010107403260b10800d0704d203001440601040c0001484144481c0d01b240c40140f00103946608a10b5001050041d03602c0507001c11a01e0301c040043c050281e818101d00c0d00039041442025181100e10030220f42034812482c0986201c2d03001c1e0381001000c001c0b1680951640081c0f2040c280c81c1007005001d0720303540c082203850349078101520b81ea90510484644c001c40e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 464442239 1250 464440989 464440993
    0x150203280902280902040906080c0301020f0f07061404030807020d08010e160e040e03030f0a020903060a0f020919060e151602130c080402011103070213020a180b0702030d050c 77
    0x41c419840c1d070040088401a2032681c00f4a0030002407104500d10041000703007032013680030844a16040c0c0c00c500b0a00100340150003640100f1410080c034410388101c0b140800103c1260b516641a81020401401c401c94815038800340d190074031050540014006224101a600721501c0c0c0411303540407038940f0307002c0c407d86003500100c9001c100800e0101034000303442070503458038801c04104c600000d010350f0350300000c1c0f5075990030010500c03d04141c000200b590225001c80c0039490b003446000800d03681c80c0020155107000340e95480602002d111501101c40800008010801c3c45458a0841c0f480d00c28030300c286070102d01100c801c0c038101d040050884000c04a400012401d00409844c3c100e29080014030032030740a0601031b1081600c2e0918414002050925a950406490184009007e0340c040411a1040742d07c14003a03840107959610300c0c0d0f01a076010003000350700e44685080a49000b00e86100c2c1c54400b100342e410124900c00558050403409000300d00f260044501d00009440c14810400c070240c8907 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 464443489 1250 464442239 464442259
    0x40201030506030a05070f0914040302190c12060e0715020703060c0507080307030b0f1f0e0f0406030605060306060906090c0a141b15130f150203280902 67
    0x59030003540030315032000c009404e07102c0c07040c3e241d40c803607081905a4101741a030140840f01030040c0b110a108075000e1503070810904c155810240c0340a0f54030380701c0c0b000103880724103002d90a00410580010000c010459050703880310100892504001905004100c080140b0a10100003180c031641c014402040180381c01810304641952130f00030250400c1384c011800e024080040c3d4001401a60003144200150794001a42000c50002c10140340300404d5007501c1640106502240000c2036444000340807000e06000303004c80c42000c04902d241d07141c01031656006142803400000e101d00c58100502c81e0504806a8034a40d403100100031750400159201a0004a030000003240c001414004009515003810040900800c1c242c1c03451040e44808180640b17281507014155100f0b00800410214200c01c010002440c9442c04124082200780c400c0034150004032080d1900b80070003811044044680a18155a42c2c905080b5594101c01302c919a942594900ca2140001450030300c00d040312150300506d10014 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 464444739 1250 464443489 464443493
    0xa021c2f070f06091410050f1b09010e1012060504020f040e130606030627030509010f0e03060109050711030301120f062c012a20151501050a0804 64
    0x12982c0c641411281c1e56507030456100442c08100e90500c00c1c8500740c0c001d20340000d081d4140029a40050103180c1040e440c0710510140c0ea4112005021107e91000c030651910440030048a00e4081424180e030030071030351540b2001c0e0643c007070405040008081c3c0107001c030319690004e00c0100d114240340c030b4090a400b40414030082122a0446402c003074501c0018040700c8480c1c55540c1101c56641c801c030703143c03550303488007148240c012083c0d07045610002100203981180e40d1000781840c441c41c82014100140d0700380300c24000e030050381d038003030291005000c6414a41c0c580740c011004002c01d441c0c60700411a440c003075440c0050000100c9050b501d10807541d620f00c42503036440364881c8100030b10480c0c03a951503040c00c0e8020b01119102407000c980b8421034458840b050302c0c030142100c0320450201114040540500e4041540000004240310640303411051a15003d2101c104095401001d5405000c1c0c0f1100110a10a10800f80c2c042c4104603404510342403244015601c0f88194403001010801d0400041c4c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 464445989 1250 464444739 464444753
    0x5030c0111150c1306020c06300c091003020702090a1503201f0905130605031c030b0307292b110a1b140d0201050a05061203070b0a021c2f07 62
    0x504c43c03203611600d270800e1480391f9600800d00401c42d49030200c0305000c01c0c034140c607182034001c020407034000c0c1c01c086281080300d80104080240082c2800180c64076401c1c2006c1c0592000c110100858010180c0550311940a40121041600000c0e5500ca140d400c030b540d25540e82001c004442e1304050361100b4001c68541003d003c2051017860f03004410303554450001031284c6051040c150005414018a004e5051526002e401c071402c1026079401b90f03200e03079010300c4695641c0748000c0501c06109000414640c203070038145941d05c0f80841105400d903201d00c2260b040794443e00500400c908240f814490601e00c100d803c0307042c2c002c1c60f40103c0010a160700e1140341e50001d010690040b8081c4480b0000a111500c1c410710305a940351154006070b42d40d004120440310a4071809400c0101202c003989095102c042090343c9001e03e010180001c45400085141c0501036411900d003800321030b41c68480001100340e54070007001c000180040c0040125022080403440c101c8410a9803240f407107441c204082c1e034031015 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 464447239 1250 464445989 464446027
    0x50603010627030606080f01060905100e0402061306090303020c01031b0c05070306020310030c08160501050d02120408030601080f070206010b07060e01020d020316030605030c0111150c1306020c06 86
    0x1911998040ba010000c2500d40c02171070003401440000303046150086658600b100d1003a445014020300d00300c103000c0e4041a0700c1c441002c030741320410b1160045e10349000141d0a48180c001c07a41c0c0c0c2c00b14802c0c00140042e080000c00c1e003200d0081c0c080d07949007410100150240ca400d8021001c0e0419200c40c4044614090b004401c0114050021111103a40301d6503a0022130b1310030f88040f188420b80a00800401c0509507025000d803100c080505007043e81640100e01540c0c180c0203090601401150050b00228294146c1d10310f0341881488686a040a0620000680c016901980010301c0100010300788070055510318016105079005000c260b2230540c1c4045650804070b0200e0781c068417190000c10b040c00900150400c00d00c4064016a00e0030f04003e0903040405070340e031034402d241c20407008000c0341d54003081d80d480c004802e0030f10b5202020701801041c28403502015130604400e003242407100304030031100907000001300507007080c4110f038440c00144e0340e81039001c07421980020100034904220000d09020 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 464448489 1250 464447239 464447297
    0x20d05010f0b0c2812030510050111030f22060e100503060d080c0a0c09060918030203030c09040e06040f02042412050f0a050f120a1d151209070506030106 68
    0xd0055132916541d030180d100041c1508200090702c0b80288100f00d441c0f42c0b1400014013003401c1a00c0040751808080d40c0b6800361b6048001c00040100d40c0510054915200ca8595410554501822502e82001900411600c901240241180981005414020000c59000703200c010301c400c00d100d02d241d640d141c488d802128242c8950044001000c0081c07100c3e070700b50028040c2070502145041c2401d5003201101c1900c621030b0b090684c006d14420200c2c1c1c012003102e801a20300c0768825035035440c80703012074090700000b21038000c5885404200814099154250400c0d248201c0381400310144a114070014107400100d544882802c01c87e003009202505034034a40c0c3c003441034043c0c403150604401100d00f4181d070301100740d40d0340c0c000440700202c410302403000007024070700e08114506040500500070a011080d000c25181c50106070300c401c3e80741d40da2500b0440f260340c240115a5599010002c001402042660410854030412201141d6464804c0640e8143e40381a981c101162507048a407400c450140060 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 464449739 1250 464448489 464448553
    0x40c0911120903090a0f150206010f211203020714010b0105090d11040504080337021b0304061d040908070b040c0317040e0702060433020d05010f0b0c 66
    0x141612903250341000313034011700c0f92031b030f050401c0c0b4a0035540c1042c07004c1542011045410500050004034540d04206042d56818003640d2400c6121030300f023a0b010240d0400c00703000e81400304c004d01406603254004002141c800d80c0b6449062440e10801c5080e034050106103408180240a070702c0960400c4854602c031a401801540c04c3c01200740d0104041716401d0b03074140c0d04460004200420303002d4500c0701e2600304140188074a0f04440480c403120961600e03200d006581c980001c1c0b8030b07104080c0303a143c0d14503000250040c0c0e42e6580e500c803c0984000c0118a04150250368903004018520742171250300c5031244c101c03144030702c0c10320030384d490300c3c0c52100080007211800036041c8003002003030500d101391034004001c4100d01c0d039039400c00500240161005124108551151003000b002030303480c0100c544a8640502d0200c2c1a152007000c148915040c05010f14a06102040840003040b45400c42e5041719151040301d001c0c0d9866030030f403110510588078004060340c0141210180a480e02c041303035190240c0194 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 464450989 1250 464449739 464449747
    0x10e0d0305160602040302011b0c03030e01021608070f09061401111908030601080609060307032d121418060d1d0f06060d0510150302030d0503040c0911120903 70
    0x20354060031150307884151072865010501b4011075800458040341140074561108989c3c0c516900c3c0b850b05802ca020040801c0582d16140301c3c20f9000700040c010080300081040303419074403850b900d80d0720f140c01d109048009403900c5001409280d80e10034001614041b01101004041c2e082c0151f6902001c2c0c40303034441910444090041d60480304080492041c4900303155a070300c0c184200010320740e03030002d803000303104540170000e0007070341d07a000140c04080380c0d80700c007100b52024200202c000d110110126048904003c00c080401000301d102c5500314034803044c2c2c840e01e0307400c0c042c8600014240600e140c0140d200e4464021024589046d2001e001c264051310008200058024261000c0c0b445208001d10741ea032010641c40307145071061007038503030042c41035924800120380d5840d10b6a484115004507035a40f503442030405100e1944800702c0c00515009422103000915a182c0208107600459054484600090b000b048050060080440c49050700a22600340711801900e0a0010780c0134004400900c4100 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 464452239 1250 464450989 464451007
    0x8030415050715050f1803091207050301230f1b18061b0c060a0f08100e10030c15050a0e040609050c0703120c020a0b10120606140a05010e0d0305 64
    0x71010740f244500780705020406003810309980200b400003500b950744007010340c03149000f440c400100352000050100e030751f8501c06d00c0200605081214036049039416508000c00c80e035201041e201c0890008010b60001034250743e0f48441070075140c2e019541010503116905a00c54032040c10806000360004001500d00500720030700001e4181d070301c08017140c0a00c90160714002900d1006102d00710401c002922860300e80310f00301e0401086120041c10b5541030081141c04140d82038580c0034802c01901040c0b0000c203040c1802000035179030044501c800c0321100f1044101007004401c1211100b00811217441e940e082802130201a1000040c00100740d4029030382c0c2100098500c15401039601490762a00900d5a52a440c02c008007103025240031900d9903418401c0d20307000642d0005141c0d816980041098900c1c4d285c100c4001c00e10032140d4407002490320100b0300c2a090102941c4031404480304406d600004641500910120100031300c2074a01185000c460750b034031030400a00d50b0095074840d01c0c180d45418000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 464453489 1250 464452239 464452253
    0x5030d0c080415121503051905010207050601081e0d050406080a0b0a1403010b06070804090b0a0801050f1005121002030921090f011b030507020f0d05010b100504080304150507 77
    0x1400c103070018450300c0f84c00d456050588210148203e01d840ca040a003800c40c2c4650b80e40e2182c403c2d00c002c0d080d0100308004180301303082d8141c0700841d60050a8680301d503518056559141801d150020030031300c180d940846454400070300c02601c1e601980310075082c40c5c034110094921040050038000c0700c0e0744038000d409480c0d0301c0e01e03001806002054044402004124181401c441e000c1c00028041c090030080d600c00308041005540440b1803031800425071444010104400c0f00f03d40d40004555800c2805000f141c00c00d03661000c1c811003180b281c10031916541c4003002004803503405000c0251300254550010303240180c00a56000c95105c00304c498058041980d00d01c45014101c3c548003010000c2030b4541c40d0f1400101e00c400040d401d1030508009640c2d004030040140141d5402418040c00044103021500d030901c1c09031160300002c02da000c40c0c2c040d900302180600803d00005126545440c1000d44984c01581901c0030b842c0300c0c9008604107824072090b01012020301642c1824000c013070144000140e00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 464454739 1250 464453489 464453519
    0x170a08131203020f160501020604020f03030f180f0616020906040b18010f0803030408040b070c0f080105040203010e030a0e0108040812010303170a110f130816080f0705030d0c0804 79
    0x219500510500e0300548030f05085c102011900d01c5140c000c02e004003c980e81c0044d81340c1e041030f0100c410a4000d40600000303032440c031826180b07040314400407c5c0008509070100e41c1005042040d110b00c2ea000052204000d0b02e80320700b080700110400640c207010050b0038030040c855442180940000340e069040c90000e031107508121005c4640603031400040c03101e289507040030f034000d004960055095041c03d40d90b1550300c0c0524002c0039031042020a548050050785016140207240404589001c0c640f80c4007010f01810b011901039009608040d8224003080e00042200c11100882d0b403055440300000c00112402c8030060011b440f103110501604046c04c050507191740c001c5210347c86054001c0c0f1455204800c540c4000c1254062510b13100780700803000455000c840000003003410782950395454030120584210542c1060381240b24024101c0b000d018410b00c84000e952080c0e04807000b04822040c0151b49082d28001c107030f01034000141e0640114040c00981261034810303070005050644941d0080d100c800 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 464455989 1250 464454739 464454743
    0x3080a060b04091a150405120102040b0a03020703030e12031302130c0c05071a070602091f0f0207140d0611070503070303140c0c070b18090a0213170a081312 69
    0x5600c0032010042c00e11590342c001c8109080d100085d802907000032040060180b0712880b4001e0b04044c041c41d09118082d41100c1c0600700003103000b61a030b007501e003000b8000d42004c501140801c0c545001d8180c000800204503040d02552105c070f514503035490503a4440070740c2c4040100d801008172242d00000c0318a50107072190b146159940d07410070042d10705000340f401d501a4003560380105000000d81e0388404807411940c4160300001c0c0940e88288000c041100c052040c2c02010300c441004154044980d8406550390020040b942112180c03621030001d9110424020301c01070303101c40b200d400c1100085140c1c01003001d0040aa94140c1400e0160316518159401088100c2c0080d6580410005112048800503040070664400c0f034140340030701c0146980c41c2054014407500020106038900d500c584011425146e410141a201103418a0038034000a03400030452259140b103a40e1010401d40c24070104c162034590060002e01141c6040d880c2e1b00307100c0e480070340010000d07a141d02c6e003c00c41e40e030a030000d44400f80c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 464457239 1250 464455989 464455991
    0xf11030a0b100f0503060103051017070806070504050f0409230105061003090f0f020f100503060406060f02070b0d090c0311030c01031a09090f010e0a060c0212030403080a060b0409 79
    0xd9003000401a10403003640b00c01041c089900500fa40c083d500206883d0b21500a013400906038070341c0400b040b4001034550108004140980401020180109038003003129000d03812903a181d2540c2d40140ea96014034040c080c0c1201c403000ca80ea04503c2d01c0c0e044100c1c0e00380204c4044140e038460155940d81003174000d800010981d100c0041c010b20b82071408a1048182851a007000b0381080e983d200180b070a00c03884040c0000b0040e5442005541d5901d59003001d545000f0841c0100d5000d002010300710360021240f5511941c90030f90002001e42c000c507825001c03841142d000d4070b12903007440d40060480d005045006a140c0e647c40001e0002905c280c031030f01c0034500032080031104140100816140042c1c40e900141018200820758072102a10456144442c1c41205c00410340d903590090340345002102e414000c0d0641c00c103000303845541e0010807015a450700580040c84a5881780c0000c1e0781da011403018104600f07030b08000060201e80703d1440343d5041710441c6000300b26156100c5003070301690481d4000b03403581 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 464458489 1250 464457239 464457251
    0x2105010605131505040e061f020c12030910111006090506041a0a05010e0303190806191401030b060d0603060203181f1104030b010b090a090209030c01030f11030a 71
    0x41040104014000c043c1541c103040d0804003903070f00501d030f4040d0348a8a0709103091400402c0c2150b54091800b20508046010f0513041011104001e6680064000c20fa003e9218603805441c207110103c00c81d8072000000e002d1410000c248441288c1d000b034441958421070107208040603041c0c1003070050800900e0550008501c609095003000f0484606910010003c003180318160711035243c2c012020704681e4242000d14440c01d0b07007004a0700350b120b030541c0b500d003503032a000c1142c000640207001c080c06080e003907591200310342c040060b0395040062801441e001034400c2c5110140703036109410030306d00d01c1c82c060701950401c10b6003a0601e0549a86030800c0f14070540100400400b00718103a88420a014900010000f8507000c542c00c1d404ca80e60b041c140b10341d590315403154210b0642130070211070045900c01114003456a44407062840b135044240f03a240700c0d21ba201c000050307081260080e1500c5060040c007500c0000c0340d01c0019001020786000d07100e0b40c25200c0c1c0c0c0350030701d41c0d40e42c0e00954459045070b0008166 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 464459739 1250 464458489 464458507
    0xc010f02070b130320031b0a05062d030f01050d03091e080f070e040b0a0605100305070806060316080405073209090303131b14090a18032105010605 65
    0x3417421140c0c5444404980560030401ca9800240810196003a10710000c03107080800040b854000041d04500d800c030f43e001502101c50044659500a03440d900c0800b20090790012103408400d03c010746484e42001c45510041c08903150599108001500c40d05105400a98812074040c00c0380e026035500701c001c40c5413007081012980502c06c21840700c1c020000782411a0030030000754003108028001408040308840059070841455200d0300250100508194034440740c007400801610046810500084070500850350504010095034041e00e40c002c014111400c2c400c00454034a00002c3c41034a4a214420000a000c2603d421480075105003c2200c102c440b003440c0c502c0f0030600f0000c542e03802140e1410401000103404015039410071006c0030061150411424001da00b0040c0150011307182c0c03a03175180050168524089160f00740b100741c402182ca40e55044940048420780e920030000212030749002c400291089011280020f8000c80c403034103a40403205083c2c11101d098000d0340c0840c1c40040e00c825 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 464460989 1250 464459739 464459753
    0x1305060a05010e13020c030f0c06070e0f0d020f150d0e1e0705010f030908030a0501051c080a0f12050f04031403100b16410c010f02070b1303 62
    0x20140c0400c2c00d00f0312a5510140100d02e5142164010074002540401c07180c134821014001ca42d040c00390401615124185460801d860381015262800881d030b4030245d281c1c040c00c10400c0c5400d0028001c12985000d49290240f00196079126041c030f078419920020007c440c9200000340094480000e00055485078036004c07186481c0703003002d90201150f01c12020300000b41000030001d064582c2840e100100c00103001003030340030f8603440c00000d09c0a1004010002828410745c4024101da404803602405c4424001c02808039908201d005080300e80100041002140181000388101c481842c1041c0b40e450003610640445500360748000490041400740f000f1302d40d2103071902c2068911042080d103581428591400056110300c12800392701c90125062405c407064007440030741c0c42c0e0031160800720009036070280710440441b80341100ba01e0b1034030b60406640e41c00c44d1500c1984042800c004201c441103a40040d00d0410541e41e5880452184036030202d4800305000141803004520700c0d200c90501e09616001c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 464462239 1250 464460989 464461009
    0xb0a060e041418010e0c130908041802090a050d03120506010e120a06110301060c1101140a0c030216030f080304020d0507030f0c0603110a080c0c0a08040905090102040506030c18130506 81
    0x700301d542c4165106c0314617542d80000c0c4c0039010440c810000e1408a20700d44240c050055a000603020809200b04624001954000302018501165000066510f660030801e03940f1070400b003e40040e94608001c3c00120980d03010940100b01410550103a100100c0000d031404405814400700360001001041044201e01618107403503640d10601307040d581426001032404c00000c0780a000c50340c400240e909140d008507251000e41200d40b541030b80c1c4105d0aa400392003400c5061085006210303034400801c4a03030b505130f005c0c0300b587c0d84142c480820004940341e5040a42001e042aa4001408004000010820000f210003907219042d10003c410250400f004400c2c0300b42d11101c281070806120014190b04d500495a6510103130400b001c090315000c81c03004550103012405007041c460080b4200c24011100041d200311454490288034039510b8a4143d800c1c0d01451141c0b942094007070000c504504d02c1c0c200500400503602d003048903100761005c00100b45c1351f440c500e030f09107043d5a001808014200b40b8101 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 464463489 1250 464462239 464462261
    0x9090f02040f02030412030c050d05090c03060105010228060605040e070e090a0b0402130605091806011d010611031207050309010b090402090601181701060f090b0a060e04141801 78
    0x440c114501171b145e4410381d1410050000c201aa10301c05140d409001c0c0c010344026200e10f40e002c0025240090919a40d401c2d44609980b00b032041c3c7c00001055803000800b40758068000c082c0c88003095901085080c01014071070203c030401d403541c40218091b161841820207012682c00100000b500d440d012b2102070340d015000c60381d1038001c1c010110101e880e641b00c8503001075040da0b0700c10601222140da0f50042544c2d0300302c25442818030b0240008541d5280394000c00d925100c0645619999803c00d5600c0000324010241d4418603c17801006014042c81c40c01641050340b1090328500604846180720883d0708a0b520b4003ca200072003400300103082481741070030807201610200a1030a03d40c00054007210024001790420004544450700520902c1c1c0030340042009420760044504182800d602030701c041c0c02002c0081608400014509419010700150810081c0401503140d0801c8802c0740e000300c44549840c1c2264642d140b11003100e0144001c0e1707202d2000240901e40b049542c1405c40d0a54143c0014 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 464464739 1250 464463489 464463491
    0x15090c1502030a080717240409050f2401050111030f130f080d0c080903030c060f150a0609030303091406090d092c060f13090507050105030c0d1509090f02040f 70
    0x2001c800810351b590305c190085d1a042c9807514244040100030b8400c856003114075007081c200102c00d820840001002d5400b50ba003881554070064140186444e19540c10315001e0b0764030a241e004010650062180a40c484080d10a50385002c8000d403090a0300d038489108040c80d08500401007290320b005030400e00c05412000c0141c18000054200241500700c05c0700d020b08031040003d00e009140da4104219800c9190140549945180082078107070304810440e5404500340034100715551500e40348090307405641c03c68407044141400c5440c110001c007241e05080f101203045c402d8004e80640c2c100291485030040c10300070144180e9400005005e18042d500002c000c405005c1d50742603030b100e64103800c0320f0881c00800c503401030381d12038000900c4c0014509403503810a444004000c18281540c0ac004640c500a800f102c1c151a525001103c07584002c9510749101d000521210350740213015000f104004031076404400001c1e44a5404c0380845e41c1d0003200b00c1c1c10100500d180c0046081038009c0c11800c969402d0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 464465989 1250 464464739 464464757
    0x13020a020616020c0307030506100e0f0f040f0204090807020321090d081204080c06062205070c021f1205040201050702010c0f08040e0105030105060d15090c1502030a0807 75
    0x540a5511a005480c03100c00ca080c040c0b400001e00d10800120641540c002c1c222901103540f400c0280d01d0b050141c1d14903020841241c0041140d5654004042c05800040b5030008146d50f0a07440d50071002001d4405c9419150210580000d640e6034060300a00a0003a040d007642c69800e441050300e003a40b00c08407070300410b0040903880e40c40ca0119003a202c4101c001d0f01c9910030402c107840e2008007482a00c2d101d1b00340710f5100041c00140201400034110002c1c5240403607809403559000c000c0720080300c2401144190b42c200f48001c003c03095411035508a551070500c100c1b007000075400104140c00001c042130002100520b1300398080d5103c011000103801c60441000141084d0f00000c00c944103c0c00081d040c041650407403403c2100441300c00171015001080b0948458540e12480d0703041e00280f08983c480c0d0b0804001c2155881c09141e840c12150b07103c1d841c210842c090756035060203403440c0307142a00c03a5107441900040d40085584500030b842c2282c2d02450b621954900040c00340c243c040c082c2c0f820000000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 464467239 1250 464465989 464466007
    0x30f1b061e060a2412060b1b0105040b07031a10051305011b0f05150a09150b011e0215100305010e030c21090303070303050108010f111e0c03181302 65
    0x8074030b10800c903121841441c0c2c00040f074000e50b0400c0b81d0000c000105e41c5414400a0080244c40181c0b0510702c00070340180c009800c01288a080e10307800d0300d000e001003c400c0080f4501a00039441319001116141d0400700d82d807104000190446d0402e2102000300304c00085c40e01000311781d95a944090b0009091103036204002c0244080741d09895107000b0084c0c0c1604c03c101003031007002c10988400304140090290a4070b804524803000e0300841504a8450903001141203840d5010300030006503000c10383d01d0020b507008151002e0040343c49042d01e00290301481004100c24040c0b139010501c2003803e800385000c01490752401d2401c41d90f100000c0d1903d0341041c404114000404038603600c103546680b946400079208000e25229521444400c0303903262000280e0f1000300341d0035400441c12220314000801114a9034540c0600380d400f00d60120f84404002c2080380f1124902c1c5840420280d0070a40850508522076807103881d60303000f1880c0190844c0c1c05a0310305010700e000000d0300c0100c03048000540c1000441 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 464468489 1250 464467239 464467259
    0x1b0c06060504020403050c0d030c0b0106020705090c03150f0406050402070f02030d020d050a0503060414090105040302060702070605090405150a0305030705070b0a1205070e0919050117030f1b061e060a 88
    0x407c040c0f10383c072100c2d44182498415855841010f8220911840c156501c09020755503080d42d125181c000d0700c02e070707001030742c605112800d51340704002001803610390080100412504d1080d05611300d0344143c1c4c5840128950300c40e0f1024212070b0b407003a620711400114500401d480c2180f4000000d0455128480e0201c01c2c580c42400d852120103503040c034135240c0c0c64660014010308691403136040300c0c228610410080b0b5005412282c000d5009801340d40d0103498008080780c40d681e00303000e20320104400b04000c3c13440d8186079203e29401054161040e400400000026109966903803065501c0e50000c11072006100082c02214014003d00c8140c52404000b4070000d0076641806944aa2142d59100001d100601440c01c0c0c02000300c0c01019101585440c000340b11000320143c060400052518001250548040f1080c1000d44190002142490200d078241d1100f0782c808803180b05200b5075140f85071040501004058010b482d011031400c283c4043c12880214001d00401451161000003001c100310014 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 464469739 1250 464468489 464468503
    0x30c140f04231c0210020f060c1e160b01150801030b0403020f0a1b052403090f03070c0e0f04120f020f0609060106020c150a030c031b0c0606050402040305 68
    0x4082d5000300d1050022810002e0409000c2c10705800c041c1500441001401988185610744c3c421144101c42251001c0100e988490b400c072045039641c0040041190032485801529a002c0071100040c141c206550300d403015900035a4502401840c12441d1104100c954074646001d8901004000000704400000801d4a07406110280404280070040707003d040c424007400b440303c04110101d60b0350324000d00d03003070301c51a4070402416241201700c10007107200e2810014038504080490741e003018070b011009045105a0024000090324407030b000318074443c440d050000d000c10324051801c990f05e8030b02e040040000d20900406c0042c40d00b4000c0d040000017046410041501282482c0c14602154045416441c00042059070585441140100b01c1c20000000e0018141c2c0d0041c0e0035240e00300c40d00020b2003c104031141c82c640410300709010f20030810340300380d100105444052a020540c0222124003241e01c074203030030300300d00055440e04c412428000c03107004070401007005135011454117165803941511844 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 464470989 1250 464469739 464469749
    0x30305070606050315040c27051503070b0414060306012102040b040e010302040615050304030f050708041508180705061308011103010e10050a18090b07030c140f04 72
    0x4042501010711036290b001c81c0141002030b0454035081c032041a55010100c04460488501b4964400821020040b400a031b04c11131031414055a0b41d03080d1750317151001d0180105820220454001e051140b0f03582002a40020210501c400fa605c0d800c05e40150007070000240110300400341003041c441540d0b40198050f14213210340b8200d2242d9800040380c94003900c603d601c1080058030104002c0750001309000c90354102c1c1e00c00c8400704145036545824546504046840101181d810f000084c0440d014996101c699041850904d02d0100d566445040b90342140e0041040b0821140002c5282034105480d1608422184111400394855100403580c6691034000d890040783c0201d503e100700c499042e036900c081c204150003030108051007001c150464200b4880c00c0841149480400e40685620040c0c04c02c2c1c50000e081d04035513030704203406010390002a49225500c160744104030004a0503203c0158001c01c400e40e400300c2e42480d1064010403103a0400007090400204005080c1c42c40321080c00c80d01164 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 464472239 1250 464470989 464470997
    0x30f0506010e040804030204051503070914090a0308040b04030c0501050a0507030b09060303030c0c0304051003240b03040821091c09152007060e09130f11030309030a050c0423010303 80
    0x90b8600702903012000b00703c2c2440d50944141000410020395a3b00100c1c1d04443c02c3c0300c81956035890352a09595082c04070310181c0410b01440208000c129415007403a403190103030030054001200b40d41c03420708461080b01d10003413050fa00c1c0d00344441c1d5640350103020081c0314211240e24040c00c01c031002039240d10000d0884542d0301d1000440d00c90701181402900d0042038014400c000c2c807000c440c00500a42150079001080038003803041d002040c281504000c0a48002104440c1141d649030b9440c9807036403090a000f000502d5000742e41d0031243c90a01b085105030605800b038002074140c40514020301d0702d821905010321a40300e90500c0362803142414a01d001c4040d20300003280d500d0046803000d038034181805681c039074003a07541c000c5405030704400c11503426001500c40880507602c04072001c40c06546500d00400b448507100c1103c0200d000c2c0661142c80d5800182a02d14003000340001910b0050880d10031141a00070424090403403402d44607400001d007401261169176100100310f402a5001404010240 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 464473489 1250 464472239 464472241
    0x10e0f040b0414181203010803040312030908130e010501050f2d0304050d0f0c241b0314070207060f050f0d060e0406060803130b0d020705030301030f0506010e04080403020405 77
    0x2541c0d454110f41440c1e0300d000500002c505040b0a0404e544604500212a503c00c0110344543c0103ca00c003240d0488030080003031410107041d0f81c0c6580075440c020107030108158a4180c01000b140d00f8130000c040354440040c1e01d00d0207524010106404110590015061050a1010000c66049002120719411440c07000605000c150aa0580d08600b501c5c6004039445012040100700000092030b90044402d43d12602e60446000000321522842264010712100410603080320f41d07044011948140c4084030300104a002c05d40c0300000c40720702c01ca11490300103501e40e913007178481da246909540e40000e03440c8084d210707240c188200581a1510407241004104001036590740e2801100706403046910f0f0a0320902540ba0349560451004030701b0b0320b09540c900d00d004800120358200004541c2604141c1c002210110b00d4024105165045095410510b5408001d48000520b062008501070342c45005000154039080c1441843d10205030441001d50b240d003014000402d80c0b07601900c0c11268100c43c04599 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 464474739 1250 464473489 464473511
    0x3201050402040b1b10090b0a060b0304030507030f020f01020c0307020f060306060306100c051e0f15060409062004060801120201080a0c0c140d030f0203010b03160908160311010e0f04 80
    0x40c3c40917051000030360f03034030f0b0850206c200f0043c0341895000d071124500902015403580310110103403000740d45c0200441c0c0c0401c9207600090164407805040b81050040e034403881041d4040900360381c89180440000c1d0000164002140740620180c0204d80c0c0950f001400c40ca8a6004070340e0a10000d4046c9200c0d0040c0c0864400702c0307105140541085038004162419000158a171410603c170900c0318018501401c0610b100f203c9002440549103008195945d2484d2111810300c4003c0449110236207030385444240c040204900c1d030031000003204061a2250b5101e14065000307114680607041448a6800020414090b03a4421403041e00300110380000103020a43d600f0588ad1914000401000c10800003122280501c011032030b04101a910707141440804170b00d5403980101c0c03000340940b81e00204140041018480c2103440301c10a4182810801d508507103a0840034a40110180c54040d000f840303400500800444070800c2c11440400c0c04c02604080d4500c000864101d4180d40d4107000d03903584e40040f64 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 464475989 1250 464474739 464474743
    0xf0506070f080f04060e1c02090601090515090f01090e0a0c092412020a1b08040e160e0d030518060d022107020d02060103060f3201050402040b1b 64
    0x124076907014152680e564080c0201e80c001da00030344505004910b040b001c1861038240101569101c440343e8019412085840c3c1c02c101016402800e600d042064110b00451541c43d091000344e1031800f13500794151a06070680c1000403008414000d181003003101c0784200b1804c5840140b00b9003150000f4404a209154100c045a221300c10380e0001c401300e03018510504261203008c0401c8080602a910480d981d4044503010040e40725124405001a0b1440003850f017090601006051540c031990885142c5943c4521450740d503803041c2d4007081803d070381c1000710411b590002900c040c25207080d1801110704165403009041e5000b42020401c144502184000ca81d580d42400c940326412001c10454032103030061404c42c070414204446100b01107510010030a0b850002030201441c040c2c59008010700d03030850383c13440c01400c0b07400908944a51224101040100f810030300c9110008071503968885003141424500051006030700c140d005910420060003903159000440310b04081d101c00c0307403071590000c031400c0e4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 464477239 1250 464475989 464476013
    0x2091207120624120309050a080a02130b03061f0906030b0708040c05040e010b010e0306010503030307180e1e07110712030504030b1302030601081c111504120f090f050607 75
    0x34030200420102040500c051440384d007100d0300076980c00101c50b80310340c00c0c03141d1081240038011159102d034182c00014901005140010801071070041030f0318002c4400b080c42c1c42c80986200c401d69100c5103403882544002c0000500400d6006030074400c1500d9034803072040306e8501400b10400c0001c190002014002481c9182c001400040c000b040000d40081d1158002c1c540b076803403680000c030003a90059480c600062507505032100140590302c0c41c0c4030172005032500038900040380c014481d60440055400080501607105102400a00729001300e140765994007140000c0001c014091254000c001001e0000354102c00d5400342c10621800f42c1e420b00307088d0750f40d004941c801082e0a42880403c04200f01d50492804000d20903001c0b40c01d141d0f00c5401480d21224503240300301c1d04610b0401d041c500580301d50300901110140c0c4040d00d900c00c107248454498401c080310180e401e000c10410310517015030301401006180c180b9150401e10f05052400051072540c1c81d10406121b00b40108030a000d00c40844024 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 464478489 1250 464477239 464477291
    0x103020409030e1509030106061d0108060d0501090302060621060705030a06081009170f031f15030506130c0503062e02070608061e04091e0501020912071206 69
    0x4000000344c06001c12000d40c4c8040d00080c029420100d00040090241e03249501e031541551172131403403001d01d50044542510082c078841d4000c40304440e40b0045502841340030340ca14043d07409440300f0710307120003407103c041c6200e29000c00c5050001c80c4a41c1404010699903084040c900d840c0e6500d1326400300c124054155600100442c0c00340c5100b282c09212a40e003c07002d001c3c454940c22005030406003c0c8281d42c014210780a1000380304000003001041c000c00d85510400750440402d0030310707441e121140c202c500d8070142800426502d80030320403186404a950010360503022014488181c4613400100300d4040541304900407050072203d00d400c0000d6800340101030030805d03403070220203400c400d001396640c465103d15008180300001007142c82c100415202020102d000070550103100d6002440002d050046c4207884c610709911f0b000b0051443d01d15030b558143c0c0914000b507150041403003000440380305410040b4240d80f06c0e400c104044e11483c0c405c00851500318200003030724070310380803000c41c0301103c1058 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 464479739 1250 464478489 464478499
    0x201140c01290102160b0904180609020915240706090b0117070f0b090a1e05040f23040f020a0314010e0c28030c09140f06090103020409030e 62
    0x1082c030706690310804082200380b01c45841c400d244480160b85481e0462a40407520f108801d05004400010f40180020344024100140042902049200144035480e04940d100d80303910300c3d04190700d0450b42c0e0541214450402000035a44880002e41c0c40b07010902401d45201c40e07242440183c00e0340002e40f0841508801c0600140803a480c01e8100100b0034080d40007007464280e0a401d131458009002410b036406008a55003840c1008a00c0c202c03500a8554154000450f030380c040341007165081049a04440800e1486005050100704019600785110180350285401100c40d0b03a820600d100f1852441400481c410b10348542c1440d100408002d64081c1d0081c001c034000008100510000008a9090b14000c00c0b5540003100056100c83c10345200b15445a00c001e0340c0407005000a8804c030204030183e0180011a5403548d40141c2100740d548a2211035075a000d10300302400c4886d80241d03000a0f40c124001c558601000024500388042c000a070003580d9403100700c000c1500800003083e4240000309 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 464480989 1250 464479739 464479751
    0xb03032709012d12080c100c1214040203060612070e0c03070f020a111302090910030b0105031207080307050f280c030818030f0403150507080c070201140c01 69
    0x14524594041c4190700c0c03420901030043d80100c0c002c86290380c0381030701c20031003548980c4001615202656040781894000c1130064020009100b10b0b540b06007071040610341c0f40d00c0c91500f600a80041140c2c3d0560b2243d010750420420000140c7d004200030b68000412541c00802451030b074011490985141c024001c80466001405542c0d00b5420255104140c0d555810700c140715210000c80e103a0f007241c0e500500308202c0c0090a25140303810b04203251102081540181094484800a420050199144145840e002e0b6083c018012450b185602400f0300f50010100c201e08518807003074030303ca01840984055408004282082d11038000c58900e1900420710607192100c02d001c00c0c51884581101510b003084183d003000c1484d009483e02258a41c00d87c468840c40e44d0b0380d812894811540c00b074603503014001000005c032055014800360018501070120407500900d4070701c04404681001e0300344401d000300302c810010001d89810441d6034050b23083ca056911042508143e1541d4024014181965400d0130 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 464482239 1250 464480989 464480999
    0xd200c09181203010302190308090d0615241e030c02070f0603051602060106050901080907030c0303020f15040c1e0924050915120c18010611010b0303270901 69
    0x2005541a68000c0702d0944080f08003000b0401c0100b1f4512004002440c18000c031002803410719804100d0500030603002c2601070900014007094405030704410180314405520088000c0e071000011212012800e200300e5040180e89240d0940356080345a82c1015120884100003500c00d0244034010400340410001d0f2589484000e4094401180d03034031021030000004a000c81e00c00a2450304807103c903114280f4081c0b003040115040d41d0010400070040c4940440080040c0c158081c0400460280d40507180c0b14011100c41030400044113040c4041c010040144808100c2d04a00c1004440414080020812142194001407d41984035410051070002c41c40341a10003082102c8690603070302001042c01d41c456080088564080e9015a0b03071612448400c461070401811a400642209003100c80418000d0005800c0c03140390800c0080402c0500d00401081c0d80bc4130034401c0100401c0b009200d00041107001c2039481c003030310214450b19003c00c0da40c0041c1000d45002c0c1c1c6480080071f0201c90003581c5403 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 464483489 1250 464482239 464482273
    0x61615020a0216062001060b04060507050f06060310020d0e0f0d030f05010e01120f21030605060a0f0e19080601030b18030901030b060f0c0d200c0918 66
    0xc0c29000c0940140303201e00c1c001c8030a00c00003c0944116803252131107510584601c0203402e00d00038802c4001d41d42c9201c0441d000040101a000524241e41d0315a6101000c0c82e0540c1020405100c2c1e8005500001c14000c3c944e501080e141c0b62004070b080016101e0f1007990415000e0021070702080307528064091030001c00003011038a03030a910050b4606104070110340d156981210005d2080700d4070201b0a00050144c240d1481491440318040d114100500810740c40d0720a82d111806c1c10552800c05090701d4203c00d075014000c10004000c1124000d00309106c1c0301d0702814884001e0011400c211090204180541e101d184441003510b001500c030b54582e03241c80505030747d24428082961000e000724001004032545d03030380100080e25050091820018000010b4010b004264407080d400311050000003000e007040700140c107410b9410002481014000c80d0003034401c8000f9800e00d4000743d41e50b01815005580090600102002590400e06950360526003482e0707a019502d07050789900941144098107280 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 464484739 1250 464483489 464483497
    0x1805090f090d0e131a150304110103050903030412180902030f010f050109031b050402070609060c111518060709150e011d19062312040206161502 64
    0x1035035045410b10a15410203440b40c88021115590110f01059103031141c010b69002011400090345d1803425240041000a200c1d00c002c0442100c1b12201100b0001071042d680001d003400c5400313003030401c0f481c02e19039041c94a0b44001400544944000e545030800d143c404c110f8401882040f0f503043c844681c0300da02e000c010351300c00d507440d40340403044c03100101c3c0e8098040c041004580058490b904590319564420000f0b024442d510405091f101900013610b0b1550f000405c0028030039100000c00c0e4000d440d000046036005032849041010000200c44030020001d40701c205041c0000300d04e11703143d4400c0140302d8000c4070003803e400d0f54003505040c08001a003100c80c2c03030299068011000344079500800c0403980c02c10301c00c0f0701c540020b030225007811801d42080c82c101e12482c0003800fa44009038800c011403194150582c401000241c41642600c0b015030403841080c00f51030410400b51a254102d40c2c40c3d810701c00040e202a200f4040040d00320000c1821300c4507200d820341d00c0041e420702400c0c03140a407402500 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 464485989 1250 464484739 464484751
    0xf2208030711040605090609070203040905070e1306050112020f0403080c0105010f1203080708061201111c050411090601111b010f020a05061f050910030c0e0c0a1805090f 75
    0x480300702c04811070300d0b01e8042c0c1c60944030041c00c641c05940d101e104200340b6820240c416420350200700b00121b034800c13550042c00d100d503402e5107801207262052001e000d40075030900f080c04180340c0ba2110a210580e8060380c4d00d500c1c032501c1e1401503181e10800245010511a0340c1c0700804440000481141250041d000b80d07040f203010b07112005003550b550000d4a0303050b404d004001c0004403080c000410050240d050590000400340c03054144c1c1550049841c2111451444913a825401040388504060004a10704582e81e482009020b181020b65545410008042503d807140d081036000840c240d01c1054000032190303888007120072540d010100c80360243d520000042c001000f0900f4414194000a420030449a00800505280d6591100c0c00c44e280550400001492106100000d01e56518840075004070040394000e10550303d1403030a1482c00070154840024130309210200f003441000c3c8425a10070201d0360400149200510300c1400501d165904500d0340400c82c00d090003100d110580006104103 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 464487239 1250 464485989 464486003
    0xe01030c0602031e0a1b20030a05070504090201141306020d0804030813150606020c03010b15030115031805010218040213031e1410150b0f22080307 65
    0x5a2a110200d80fa0300c60306401c101208400c03940514034600c03500080c03007401c2e1189006d08050407082d55030020210341c08001c2e1404a140302250000303020014050520000441c028000e0305090f50f0b5050311211244030301845103540b55003001c29a4000d0001e5541c181001c10141c1e81d8000385200c10403610700c5402050018410741c50804800b1f401501b419020f00d400d612a0409a0f46400038140b0303005050f02c0c22a19584003440034484c8102c18001c01000d000a07401a020520380c400a02d421210448003617885522003c84520791540d91100700c9043d40c002c92416080380d21503801c02d03000b40614134000a80f201d23111a290b001c0c418194042c1440040e001a54608014801d082005034007606a01c0d0480b0803e072202000050a0940c00b950400e071030b01d01d411043c0c221901c0341c04c001140c54807201102c1c0c012241e0700307020100c1480386082c29000d03c0c05040300c0c1420700203408218012480c00b80e10300940002c0c948a5010110300442c0f844000401e5028000d446080d483e0322a082208103e03418 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 464488489 1250 464487239 464487263
    0x30a1b090c0c0501180b16020709050705070b0c09151e13031e0503091c060c110d02060103030215040204020d0509160503060919020d060c020c130b0907030c02070e010e0103 76
    0x3003800700078070b550000e4100c4100070030347c1c40c0c41004070101c0c00c0250200c0305601c102c00380094009280c1c06050b120310354030348466131a400c05082025000000810101803000100a04205650394814608a5030344211a45031540348600c4d1100f100324401011404000e408506400c04610402e00b21007503030f204003e1514040140c0c0310ba1810400410b00c014240e0b0024440358800e0309064042c43d4064512135001001070300e00743c0381e490442d8100345c900c100084043c02c101c850080104100155006244000c0401d589513481c0203403500983c0b204120706180c80d43c0480e0555540d0707010346680c203000c800e040095040c0003003070703503940d021004440f007140c048550005468500412400c1c8a80d5444d000351038042e210444244002039034401c202d9022054892080c04900544110041c5d947c040e001485009020000c001d26100b11942107030a440c205014001c603911480d034100c1c1c12061600300441c806000c000305a007811419004841703450505400003034142c078005c0d00f50b4100c07405a0515521 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 464489739 1250 464488489 464488511
    0x70e0a021e03070906120b12010203070e100e19030b07030c020c0f030a0609022409041803211e060510080c1b0a02060c0606040f0b030a1b090c0c0501 66
    0x501003190380c0d401050088008001060240340c0780170004050200c001f4141e004400020100300c841880002c0e0341c0c0d030120800c15041e42007424281750060440d078284800c900c01000404804a138130300140504038180d40400490f522003a1000a15441a42d5403414079100f0340c020b00804040c00460700612400803107078003d0410914400b900240500941705000d1240c1320b05016021410040780c0040c1c0c5258801c45014100c011802c0c0398031041c041c10354900b04541040140e6013011030b0b02e16001c40340d03800b40300041d07004040c082050500c6860b00c1c880340050441c000c000c1000520040c00b500b9105d4104402a0041d0b00c0350003030f03e90803a40500450042c45003200c0200e000c079003020208400b0040c03140b2110388411241c03112103107041110103040095000c1840750300100b580b5100e82e4003070014031070185050300502c8400b02c0744580030045121564006a82c2e4940311130007074104468080f510f16203240d0a030240029102c44842800302d0250720340000c2c24900b41201c1501c81d540782c5040101 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 464490989 1250 464489739 464489797
    0x9140c011d030a0b060312040303080a0c0516140f032a0105091908040b07030c02040b101e03021201060c031707050f0a020a200a0f0810090302070e0a02 67
    0x3103505030150043c2404122580c50140d0260701130310300c0b6414840c0c407032508040c801000c0140050741c0702c1c1c0e441a0b840d0401082c1030064844134100d6000b40841032101581d2800d10b07015401905810444088110044118141c1844034030a030500040c0400920f216000a07000a4102d07148002c2d079010304036002d40081c071800c0328400c0d40d40e450590004000740c000e410415051013800d070301a514031840c00740c1c2d4090b80700c500e82c8102c50450101d40403c000009600d041d124401c84542c0c04d07180020102211034000745496818603100c2650180800842f140910a0381036408160801140c00055615050060020701030700c0001c40000340000c100d400100030051015008040c191660340c285900c0c21035945d980d07000300c80b21008500c81d0f01c9010300843d4100301102046040984203505001e02d440c240507440f425500300c83c844000d01d5004000c10040050522201882c284002659400920f8100e0510540741c2c441e0070140414800d20408100c0c5a0007450705035000c0341c1f15540a400c2c410500b03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 464492239 1250 464490989 464491037
    0x6090706140405040c110604060609110a0f120f180b06032803210c031a03030d02130510050a080703090201080403080406060b07031112040e0406020c0109140c01 71
    0x407100070000e120402007404d0075003080000c0c1c091814402c0c1554103a4201500c1c1c0001100c0907601903481d1007080001126034801d032071501c400c00d8407042c03910340d80150240c45100303c04200d40410428449050851410791b00070074410140c3d00080c0503c2d0b007000f89030f040c00130009006a801a05141c040351503442c00180011074100c002945c251003041a048004055040e881c0680c280841e400c0034001c10030403451390408011200e4000100494040301c003e0840d01d6001182901c0e500d202461711003075400000799182884004805681c3d4030320030082460713000580d13202c0c40d000030f2805ca17500d001c1d64004001d480d8460b40e583c4d4a6205995030b49003101910a45030b4080c0c00700e103448001c03801003407141130403e501c24003a03103000c2245561000380e103942d40e1181c101580000e0f1501c0c40110710303190a004002c01c024084800324102402c0400034440f81501410040582ea40003813015940304081d000050015040110a4120026940701603180c5910700b0516000801105407000103a00c880401 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 464493489 1250 464492239 464492267
    0x27040b0c03011d0c0d0504050d12020a020705040f0b0406081506061813090c060203121f0b0c0f0709141e150312040303020717010c020c0108040204090b0906090706 72
    0x40d0302c0343c0502a0820f16100603052084000c410171610480c901c59004003401944190300070b00c0c0c0013000c003e00034420340e90542200f10103401081141c0c02190700040410544504403000a107154580c0002002041d8004549800c94140760380042c4854008c1400c80a40840346809040e5a54940030424a44201d000e0f15042800308955007010b810943c1c8140c402190f0402c0004050609469864410b0342caa0f02290050f400050700c2d1000b01000c408090700813000010464a51203083c42c8035401a0f401e000d41d0007002e002040d85104401d04000c02e0840e03050703040a41d4032041d01c502c4108080c000803183c10000c01c9803103011414120000a030f542046040810030400758030741d034001c800b11041a9601aa051040d007001c08aa1000c00e13009200442c400d800030440549411200711480180000e80200c9914001c1081010f50700403454030780c0400309180c1584150749610000707005040d40c081c0038040f481c0038020070455140026981d80141000c1d001c42c1e6015603914011241c1400c01485 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 464494739 1250 464493489 464493509
    0x50f010c051621020a031e0611090f1206010b2818140d0b150405190c02071401050d0e0303040c06030605031f02090f0d0f06050f061e27040b0c0301 65
    0x420100d548500550001605100b0440d1200b1f0107440308801d6801c4000c0c0a00503400000b6240564a0070200440e241e2000340c0f4246184003003807960585400c0148911411004009005207030107050840d4584070000301034010440d102c100030700910b589030b01200c00d10b07580219100465000c010b00e425100004d4000d00005140e03400703035204000340c2c0c4090300e10380b40301c0b00c40c00117030300c481d81c0d01d00895102d110902c4421102c0b004806035481a178030381c10102015500040c0e820300140d42881c1411a81030300a0034020368400f02c0300481c4000b402e2000382d481d150b00000c01400100148215201e045074200d540c01d000351600c42040640711002c1035184402ea150507100306080c9101c6030050030340300c1d00050101c1030380c404450210318a45180a0201d907085110202074040040503c03550303400040c42e004940181c03405c40d000c17070040700084111a9905502c0d10b6401c20981c0d511461440c50303520302d15800446407000c055a1680c5000303583c11900d00c40d0840c00543c903602501e09072030481c0d1000c46 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 464495989 1250 464494739 464494759
    0x100509180c0f040e03070503071106030601230d090b161817012004090f0903080402010818031309110c0a1b0515190c0c050f010c05162102 61
    0x401401c000384403240c680241d16241e1001040c403060006e8140b071400f6401460f50741450740780c0402400014000b161183c2e1080c0706019590f640000580a0ba4800c000b0480c11492480c0d04848280100040c40222505011800d0204541000524090051516185044000034500342c508064a180c11003c23440c090344100100044150101c0c0e10b0901a80005004803201c0b45032072682c1c120b003d10740240000020204903503111440340300c56078103003904100098216a503000704503103400b80000e810000180c012803480c103190048202d400d544482245d0340ca10100300481c2413084540705502442d450710800a403000f0560049403000c0c00d0354006480307242120345d1031045c48600300e4030000710898590404101522244a04002c4100c400e42e03a03a1903c030242c40d00c0310300c203a070354102200300300c200301c6a900000c6800c004030003075130300803925144a0508040100c0d03801818850280c668450130b600b87c40001c0050240c1c10941d69410070304034013014000c0d03030300c20036a0421200a400400944c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 464497239 1250 464495989 464496013
    0x507051b012f030a1808010903021e0c0d05062a030703051b0c1b041a090a0207060203040b0735070302070609031107050a23010c020910050918 63
    0x70080488440c0103209a4101c2c801c0d0051664001c0d540030004201280703203030100c1c6211000814001c0481000078008031441e0742c0c0080d11900342520740300700c03420b0514080b0020030060041c8504800c025106c1811140d42e800c00698861041d00c95510060520400300422040d00403040714031f1041850786481d43d03c40d10011001002c004200404410700c40c803107690341c0c15400d40105001402040102050500c40010354004401c0e601600c0c410352400303e01c031902d05070f0b5004035012108100d8184080355600c1c100440a4824a280288011310000812003000640c0b0102c50003603a0301d075254414104550038401941c0300c80030904004440103600a1904c002500a040c2c1c4400c540ca03000d0b05010041d9142001e40e11803490072000308255401a5500c3c44040200e00c0c01060203d8a69225625042140c000b500f994000180c2000080700038104031f0340146000003486030f020703042c0895441c202400703d03031513102c500900d4482d54082001c50800840441110903081502d009084072180d40 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 464498489 1250 464497239 464497277
    0x1009020a0503130201110d09030c210303090204180c030b070503190209030a0b01081b030c1003050a090f0b0405120a0914011103040603150b04120308040f0f030507051b01 75
    0x30760300132030400584031960020046c0900500c0c01001c0b040e241d042046085203010040102950803001025000c111140c02400556881111042d050305001900f5502c03800803d0107000901e0384901500e050740d215204000100e07038804122801008143d20a031034100d02160684800d99140c134541c2c0c10040001c2111070194000c24aa8000400b11003815035166601c1c1d2045c8400d07030091000c4c2e088a2030f5081040715170500c4041d000002c0703000c1c0910082c2100040c1c0e524000b801c0300c008060384c0b0300008034014015402001c0f1706410610340c0d140301845243c000c0b1484c104a600315060b006404a070741e0b90760440b0f4150380e01c40030240c0791010614107000d4130400c1ca5102003411810408040b601d40c0b0186800e00042c40075011682d404a950120358802c400e40700500d521000c00300b4400c00c0100062030398001a1280c0c00e40c540b0b44141c503625142071040f4000381c7d20f40d01070490f98440004a003050340000045c21110710410030f440005501c07a010440c0c69901405082c08510a140903003001652 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 464499739 1250 464498489 464498521
    0x1b02030307140c0a0803160305010605030c0703030605090a1e0b0130090c051002070506030f0c040b0414014d01060906050f060a05040b070201140c061009020a0503 72
    0x6180325031401d1240180e0740d14038000c4c00d810140da21100000a00c00e060004180c04282801130f420217124a514110700241a44002001180402c1e408035850781091300ca80c000307500800004240a21604010103020018800d484501c003801d880e4148030260074078980500e40460005840d0525941c090016222524201104200501d85500d040c2220348040c0d218051656000c1c2240e04e00282c00c207400c1c030500012034070810301550701140040289079a00021694421845022000c07292505071200c21180281d4100ea04800317408140400e105060304220f1007004400d982e503032400e079a803a01107030420912044a100075189204050b96600001282a9558299004200c802c01281d94241c0c21540c140d0801810786443c0c5c04100181c2c030744000401841001128901d2610030401c801400030311031031196a801c42c0f00440c0000c00e681c05808503001031b0420040469440c0a01685640c039540102e8040603048114140450846002c0c829102c1c04101901c5862558644282040c18030b80 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 464500989 1250 464499739 464499767
    0xe10081f021614120f031503010605030d030903120504050d111e0a02090c03100303081b0d0e060c040506091306080a0b07080a14070c05100612061b02030307 69
    0x780030420040510b01c4000e00394109801040140e1111020008003414200e5a038540d11124000f0f001510007010341004898100c6c11103850a201180b840011a003d00800d40c8002c0c0d0500402d008501440d0b0550440c407021440f903540c007000010309440c0901158415140580b20703902200320350010501400314400c02e40309020440c0c003401600c0464444508080c411800c1e83d400c045582411418100a03003600240001c0c031860451402c48240c0d04030460900c4050208850440821900d0200c0c00e45940c0d410781100f016640d4018503007004001d000012014080307881424000b410f1071100710142d500b51800241a98581b00800013040703289110061410426030380d0b4040043c030031004001c100b04180c41040d801180b442c1620303002d422b4800041165842d9410180300207480e17242507106030340c000c0daa0304001032005042d0520310300d401e0003a5075140c12a407801e40c3c041030300c1c4240141c2480c1c05100b8001406515a141a82d0040c403820b0381c1304002681c41440800d418900424210024603 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 464502239 1250 464500989 464500991
    0xa0c020105160f1809020406080108060c220e0f04260f0d020408010903020d0807050f1b03070f0c15030e03250b0118051f03230111040e10081f 63
    0x404c002441300105a59440b0118a07503000800300b0030160420340850043c10701c0070140c849441d01c1f2030001c009206554030440c0382c500d03002c06180c030b81d00c0750800030740034000000034078800c0e14007401000441d03002a41c003a02c00c074000c200301d2885084000d0070640011890000e8070f0920701d0401c1c064030f543c0c00480d10907055a030240004a40c04100340700b4150881e019a0041400074035003180a013985034003504580c1044000c02000c0c50b0000403604a5030441140c1e0964070640c0660b1805600b1030007611001480e00c1407603a040000d21080c03038400c0c0c0a40d1044440b410100c600c0070019030880310000c108190716001032100750162804420503510300780c401200109400c8180c4d603084e000f09401d0b00030400710070030b05202c80d54038031991041960140703c8007045041602c0301c0840041aa905200c0284040015070b50f10903104040c001d0084290100c80080c400d1188003400d07110982c00c42d001e10741207441058000b5031070211011070041218812000f400940d030340d824400130600d0300c214a0721b17070203 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 464503489 1250 464502239 464502257
    0x18050601020a032a06020d060b0301030314030a0f0203040b0f01062f0a0c03031101150e0615130906051002070f0605031b030c0304110f03030a12060515030a0c020105160f 75
    0x4d84078503800f894103034401c00006030344004641030701c8202c941540010381140030a20051000a40295118050115051131a501e0350b54070038044001d466404201e21180340040309100c00c12446800300d42c090782500062044582e2a400125050140f0204080940c0c20310008024141c80079840300b030418070040c0a031000e103e001d49460b2244001c0ea407089000984401640c0c1407075600380702d02d008401020300041c104070b161050181c0c00782005452907102e040c0c11400605c1c040c8045040b206220b0b4005040906150764104400090125201c0c0d2070085404400c480308961002c5828020350705001e2594503c2403c1440450303554200400e884503440c0c0e01d00c22204d000030000c0c0510b101710390b0b03a070100340d03649801e2500c414128603914020b801848119030f810429079000c400e42d4011404c40ca0315424a50b03c00c01140e001d0300d01e603070007603402c4900c00b001050301320710240c0103500c2020480018070a500310424102d00703da4080b2580d0301000d55100c401a2140c0c4100c0000ba0140d0343c0346003803218 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 464504739 1250 464503489 464503547
    0x130503030f0309060907240210060b0a030510030c120303090f110f04060312111c08012d0e041b150323040311030c03030c0418050601020a03 62
    0x6150300c510400c0c80300c0c000100030003c0054013000013a60041c0c01a002d0854903181005a617224412414a500801e40070121211041e2003000711951300b1070a2002402580d54605103111554458203003a40001c2c01c280015210316480c40100c1c088940c0721000400451902131881d144842120040b020942c5645802c008122039402035000e4601030791141d00030b20210f0040180f40210f650016000d10b00f0700c1c500700007042d015007042ca8240d4180c00d140028242c03000145003803540b00154480d074008042c0e4003035040c030f50001040d8160b441070b862000203001c000d1042100c403216440da2900c0502d0400c8240031481200090940152181c0c45940c074604001c241f810074411103400417500d40f4803010360f0740c17030140d4103010b4031024014010705241001580741c0e0003040c001006202800780700900c1c0c0a400105802c01c101e580c81c40f81d50040e2602d0741001c0c414000c0561091041d001c204065414078151000e10380b10340745c01003405030000c0c80b2201d01e96400381c81850b951001c411001008420100d0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 464505989 1250 464504739 464504743
    0x105040f0305010218010c05250f0803121311040b04020705031206011209020307030f080c0d03020903070f0608150f060c1f05101e0b1b060906150402130503 69
    0x18610510004d82c681e010392161071280041014180e04000030411448041040410864018001100c3c800c4c0304042640b529880a192540801d41d1010f038000c1c00900b0180100142011806c19a0451101e440300340e9420b511600c4000b01801c9540301c07665044080c94282d105603841d06001c3c20240c1000415102d041c00c2d60410300d818602445404104801c2d036910886074407040003031a8007041000e28a17000b09581c1e08113800000d0004223415804001e011703500040c0c40c00041d28070101c0d1068501c0b000010065004540171501a218aa10100340421540060003d88a16560300005070341d900000c1c1d0075545601030b8480d04108045c1c42d0200c6500d800008040b031017258001000208040c2180b000c0e484a51441d01900c145400144502c0c289d204460b00300325030b00c216074406400441c280d003008144d42540b10b0303500f00d040090605050000c9008130500007803400c00b542c0d0076980b80140c2c25200e1404880303001040d5030244950289103000d0f030150880901801e005104191258007080c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 464507239 1250 464505989 464506019
    0x9050a0f090809032e111b1c2d0306050405010f0513020301030c12150c080a0f0501140d060e0601030b16050a02032a0703030f14160809010504 63
    0x60740007034000440058505007000030540d0030030b0409000104010f10500d01c0c6007808440135030081c0300d88542202111801c9a0140c81c03006800684291124040d505e1f4255980100740c50101c180d5981103401803031500950200c410744810611201c00b11208a034084110402560a202410350f900001b040d10b4456210340380c080c01c1802e603180d449904000030030940303024207002c618800d401040140002400c03980d0000c00c651303c40030105c20511480c5071200f441620311340c4090b0981d10744685280e51035480003865008410f011005c02451466403210340660310240602d4200b5039859040c0c03840c40c1001045a010300e4007400c03000410658000314641019070a901c20758014013482c0c04d2081428400443d40e80844076414440c0c80c10041101c0a5200d014400c811513005014036070880d402c500d14804079462120001c107031000c2d40d07160b01d03002d04903000703040044c00025000040c21620102c84401c403100e22440c1c40140307402c0300b116900c2440541c0b11080c0ba0341000b4003440000354a5070000018 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 464508489 1250 464507239 464507243
    0xe0313030308150406031707021203030a020403060e0d0c0209060d0b1501030b030d08060d0f02040903120c090f030f05160803071109070e0d11060a090e01050109030b0109050a0f09 79
    0x8002d0801c0c40b03d8049094581101520541c030742002080002c0061407811b062040303405c1c5a035110400350000820301203410040c03001c20b0000104012152002d503004009491050804226482c0d507001442d6480395154040303c00302d610464104090300d0140a02a485a401400120100d04550315083d0b1010141c070480e100c00001681c1d4000c942c0c040c041e008040000b0f070000c1c50740d103507100d100402d1280c0192159000344c43c402044014009804445040150003501c10302401c8960302c0c00500b5a01d480040050162078804e0700501107101d00e81e400100c0f4036000300080c0850071a21707506041301c00040c0480f01480380000807244183c400902c0c0d00200480405503440d18010700b030601103907080400c4584100126400c05c0f40a64020351030305181401a10038a41a000e207141c000e07800441030382c0855000402051740e0040030b500c12103103030503290410903030708103641d84400649004642d404028030788205080144003020060b03000b107901c64640403000c10801c6600810304110b42c0c0c0110f007 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 464509739 1250 464508489 464508497
    0x71406120405100c17070503190203040203070b0711310b0301020702091602060906070504060f0c1b0329060112060b13030605280207020a1809050d020d02100e03130303 74
    0x100c0f8017110201e0510f41c02203081c01d00528500c2e000003020918038415880303c1441e5408008582551030403c54900038050301034005598448906100981490360250540b0510040c40f00d82c01c00541c0404240c00c000c4020260121070b880081d144028110381d05040b034056500f0300c604005a0f8071859814006c404408518000c0c1100340802414a071000b054003410342e011000344000b0070303480f4044a04840107840d00002491101ba4101d074445a5148050304a9200c480d070300704030003149005241104e00c00c8540785281099804a19500c0c3c0c60459070392100c4202c080018250750043c00308902403ca1104e0024007d6200c5819110f56003011290301510704c00d11400303104101c1140306140c0c01c00604540310b0043da4100345d80c03280c00780c00d00d40c403040519000f08001017152613816140d0090001c00c03404142d114400c20005000780400d4106884a1213a5000e00d01d0460010480000039003060380681040d407440f800d060f014040189058850744820881e10b0a072801c09400309000e18800d940d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 464510989 1250 464509739 464509757
    0x109180c24050903120a05070506070302090f0102061b0306030a05010606030203041e0f321011030705090d0311010906050403110c0105070b062808071406120405100c 73
    0x2418a440744084003a031003030001c00c00403c0341550f4002406540b210707010713602660711050608101c442e8050814014818427940d0140049683c064000e04070241d0159007406036002f103c401286c0c0d032030003510440c0c40000c04c0b0114010710301904000b154001b10181c100d8042041c6955440e08403011980040d0000e0743c003106120420030b07520350b40c162402d9010300d1048a1209600e40c4185003000200c01000781001901d50341582d8100c0001421030b09001c0441c900b8000001ca04503190300c1c00c01150568949005106001b82a001c0f0589008140a40c1d500341081844002d0103424000000f050782448581c80b20171603c800240113410031a4418800482c01d404d062401414000c0c0c0785a00902e075070007549410348540d9100f010b50ba14184c21241c0c0f210942c540102042110a00ca40b08000f42c806802c0d04114103240980036408803522030701120b401503030360181d0502e180e10020941c2d0303010038100040a81c1d684484410f68009019000381d805c00c0b2a0030144500701c9103d10684070208442030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 464512239 1250 464510989 464511029
    0x103020406050f06120a2301091401060903030309051002040914091902041a0612191a010f02012406020606180105010807110a2a030201080109180c 65
    0x10040c036006182c291a00c4000700007200000f8483d00801c1000500045407130b000a241604035041500704139100e0021411628082800001e44002401050001400c2a04858110501d50381d050304880780e80d56000c0c0014155074044000d000e07245825545071048901d02201c61815100800050044040000d40c84101c242c41010b5000001c2c03208006401104d202c40c12000c01f01c0400f64030b26411100000c004101da8543e1100b03800e04070b48240c01c940f0126441794503104c0c1c030410b01e004024910003c081880d410035030b00c003514001c2046442194000d8202469940108421600d40083e400041402d404614541e02d042c1100c4000314424501d010040100319014824a03801030341c196840602001917010001d40904184102410010584001040184a0040060b11804c00320a82d10021024207000042c00c401c8103460004a8860391102200f001490419007260f0341a1120507460380f07094404c01c0240b00c0324a1000c04103642158000004040c0720680d00a031282d840254600c103891 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 464513489 1250 464512239 464512241
    0x1140d090b0a0618050105060f0f0d020304050307021201050402030c090414010f062102061b0708030d0603060506030613120c080f0301090b011d0603060f12010606022401170109020303070b01030204 87
    0x4c1007003116281c540001408180c80300380c00c9819031700106031310a6961317805072010007080c85025070034184988003200384020080080001c01406008890700216030400d554201d08a03402030b500254160320441d40e0241034100008540c0e441402401818101121821614203580d0300000e0354060300d607507030424040d529000b10116200c4020a509040300e02c09035011030001c0c81140114140c89600c00c034003502039201080000c024080c0042601e4417031407610b42c100060302050200711001d604040c0092503d0800084a6105103040c2050a646030b01548074443d40e1788202d005d50080141540100d0040784811000b080001c113a003c42d103990b036140c203441d4002c640d581d20b0740d141080b5503107850014500f0760140382c0d003130f0301c000b1140a9034070746407400000c02e404081e05c0016001070b40e200100701100010351040c41141c0b46902a51107001c0001d0240c4150042560080701205d1400d0061240c0110100c4808c0340c843e80ad0000100348046400080c69600701500444541c43e00100501c218201 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 464514739 1250 464513489 464513519
    0x203190b15060304060b030a020d03030b13020a08070e01021908030103052503080a030609140f160504030b041a1006020f0c010905010c020109180e0c0a030201140d090b0a06 76
    0x41c0349810000492690002034039440040c0001d04030586451400300716940903c10f04540c254006d1020302100854039015000e44500c041540c4160350f0540300c010032803014003c0301e0070491990790760f605540d54588140d55503040d01c0380250441c0b0030100401c4044001c20801c2c00018001c01c9516141d40c59403524a01c0c03e9001d41c5440840e201d4003036032107940003181ea0b01100b6668041601034503011200d00c120002c2c882c640c40500d070390341005c070048840c0005483d2680900c680801820069a82c01801138040c0640030240f0000b6004110400110300000c0c51281c00510600500d204800a00c190440c1c1050075590000c0703c082c1d94008104e003640402c000e40c031b000002000340074407800301c50001c0c15045040c812141440002e1000900b1a031090b002d200c003a080c044104052000d60310032000050540d550400000d00c100503082c8400c1c54110040411640d0507074445943e00c025421641464010320100c0003c5506ea504d00e10004220044080c030030a1031b410700150a03440d084804900e102 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 464515989 1250 464514739 464514751
    0x21c020d0911040b180a0209090a0621110d0c08010213080d020f030a03020d0b03010e160b0c0a022b050a0c0530070906080c041103010602061f030203190b 68
    0x202c3c00313070701c001d4544800705540d440b081c90081c4210b0b15030b10361407081c019100301d80d99903034009811404c0006541d840e0b4003900603202503c407270f81c500691078009001e441d411444068046000506c101d0400d00c0e00c0b01c10406864452415801216500c0038440d003603800c04901c1d8031282012403c1031003010000c10000001450354402082c4100c00c800040e074591090812060815800007102106201d490304200741107000a4000c0011000000703c00d500c0b02d00031145001027091495001640308083d109440b440d42d09213000d083e0304403036942007019088804200d40040ca03a6031b403081031100400c04040b9100d80c00746010344125401ca1404d820489480e411540c4683c20345d4002420740304900c0c5120300d02c01003170b28542c11952000000030b071a101566010162160070110007080400b030100d21806401000d503820310004c016460144c0880c00240210f2005070306c80310024000c0c2141156102c03685400401000340562030381c000c40e0401009442c0c0c0303c8040040344820041000c86030b00389900c00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 464517239 1250 464515989 464515991
    0x100f02120906010e06040b2205100602030406050f0a030b0a030b01030227070e150d0212070314071209020402030c1c020a1b06061e0305010c0306140103021c020d091104 74
    0x58141a5503084c1c3c014060300c0c040c000c030350380d00402d0741c00c0c2c9030101003004407225400b12080341c03250000d51790301400d4204d4038804600061a400501c0d0307400041682c007610351a403141070614074802201c40040d0495000f201c1050313280c2030202c40f11b03200d0403d0000954040c82e0300d01195815801840404e43c0414403907002d00c55800c500e031801100013580650005410319003813410800c2200024150b0001010341c0140d1540000c0040301500c0c568002c00c00c0c01d0001681400c16920050160308a810f0110404142d00304c50000ad99604c0c0706821140129044c8200065a50704070b4001c1412a041102e10405800000507461084101c045555690951050042d0b107000d054000042c620004034010101c810000c00408040100b5500094060842c076003030009125000c0003c40b4501403180310569855107090400d614082c8240900e0342500d0040d1540049011300400440096000b21107034210003510745048501c0b26640d000070441c2c2100c0b94400729958000f4100b41024400d4200c0d0180300d2 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 464518489 1250 464517239 464517241
    0xc070f150801090b01200f011b02030a050d091e031b111002010e06100f0914060d1103060a02250209130302190302070e07020c0a17100f02120906 64
    0x3660000341c0310306540c030074100410400303902c00050704c00082c4400031030b9500541c0e0b0300c120189070700060300c0919044100021300140c2c2e00b00a240744402c20110b034070801600304009002c5d40500520080101010704100081d440b641ca44680340c4c04119a030241d42910f0f2009180b03070905a00116a5a2110382503d640d69000259900d045280044100340c03401001e030510a5100c45000b17601662044c800030040d6807135403428001001031240713580034940f4512180d060200317008000d4812400003030a8034440740f400b61111004c01003034000740d0508032140303200140d15940648050003218040e064808016031501c403008825190004d6135105400f80044206207071000d80c0e00d810f2515000000740940e40d0178170340d090800303c0c28040c500c01c208052104001000081641c0000c0060031158051007108142c0c807040000c1361601200c5580e5036110030030700c200340098140324018076600c6046c802207517080c0c0408000c040507141005002a41540d000c1361101e80c641c0c07040d248a52101c0010050015 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 464519739 1250 464518489 464518529
    0x122303042003071503021b030d060b0a050d0b28060f05070201050301090203060103020c0304120605060d020d11040608070b0903010608060105102a0803060f0a05330c070f 75
    0x52205540b1484104960a1202d0400140668111f4603203004140241d440c9113940390035030303036658010182000c1d55483c0031000980d860140041e1500801c0907070710300b481c211440001c1d00c05044c20100c595800807107081001c0001b4030702403503400340e10710019036240d101e80391040c054444010141c1400c2400010801c07900140e0317110f412241595441c1a0041e226103c10004800034058407581c6490b511000a005c40e58007444488256032521641040c45281d50394401d0140c088420032000b50061640c05035080010002c610a144038803000d0000208256100403141c50801036038040200600c000500c00f030326082c2802607201400c5880b0003448594076040101d038a40d00341c80c1880c41040702e019000701003181c40031f0325035812000071100c5000500e02410b01842a038425a10544100c0ea1300604c038601e820b1810741c45088500003000744020800000070354603404040c840450034607110b160b410040e00100320140c044610014024640341c1e00700780303915a2614030768004145027105500c0f8405 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 464520989 1250 464519739 464519743
    0xe0c06040e0a0608030403050307050105010902040509040b0711100608190809090c12010605090103180b360a1403091f0c0507230103020301030807122303042003 71
    0xc4848000701c480d00750742da01c20307000014116600034200b03d0100040010505c00004044d10205005d8070003000940d0b40c405a0030100d02c5640316594006e070b02580020040b40200c02421b40c010340608140b6000303c4100340b1076041000c40a00e00c00351070740e82e10090102e072404100804d800e818180380c000740351a0b6900c82420f24028240003a00c1121010009080f540c0c0f124140c40480440c00c103410115615600068056004048498000391030189268800f0451034161960b9a03003201030850903845840003911002e45a10b002c1c85902000304003119141c01014201e6042c0c0e4180d8080e2007200b085281925403200202d8001072640c0c020b0000380d001c1c0d41c5002c0021040c0c1120490038446a54071041581c0780d0100d2000030f003880c0503c45c000540c3c030000c5071040d00741c10102c1d4810b11400b0140780c01502240800c0c04094500c050a1000d0760018010302080c441035080340c20086902b55070b01c114490340301d00b51100d17000f4140f0301005000c1003090020741d1824459150351041010790b244404a9 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 464522239 1250 464520989 464520997
    0x90906070e0d1e0201120207150e0d1d060405032a01090f1e320301150504050a060308031602150105010f0c0618060b1512160e12010c030e0c06 63
    0x245030940f5045004045a00445004040001401c0f042d9210790090500403205032070123007030b01c0001d030503c540145e0b0100c0104994100030581c2d00c4d0451601c0640020240301100a400320703801c01810040420f281e542004600714640702d80a0031400d09201c01c1656114007600c0740b08506202007184240080044080e101041e510111b48100315070250400d01c1010402580c405081ca4400f007540c1d40b0781c2e83c0a1076400d1682805007042c05400007100c014103081324541d410840341b00040a6041c881c91900742c00c41c42d0015221030010800540321b840c0c000803a80103a6103070080c2040c0c0121082c1c03141d01448030103c540b800040040043d0315041c006000f0200c62950203007000b01d000c1d003a00c1003107025800343e04498460580305482c2d101034500003005100e510074013032152061724240045800148100c1c2c02e51006152841025103d115041818084048289050000aa0384d41c01d02c3d031110010803c0b0661180001f02e03840e001110040d085484809011806800017500300702c00b916280129 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 464523489 1250 464522239 464522273
    0x80c04060309020114070b06011413050f030a0b10030308010f0b0412230c0315160c060b030d050409050601082203021c170f04030f030902030309090906070e0d 70
    0x49100b10303561004071071400303069030703042126500407420009010074009031a00c2100283c940d4a0f50030100341c0c150713484e40a010401925441d81800c00d1049042c408110100458041c04131032048160742d65150500384203d40b06a0f0640304c00d80104107040d8000c070501c4c0182810030000501504007802c0381c07100c1c4030380d000703070501d025004654408100c1c0d00c200c41c022030300c208105000e030050790600040e181d98070041e1030ba100e44201c200303820603110b2103158a8080c00c0544054500c0001401301921301164011090f01c0041d80e0348a454420b032000c2c40012544c984030742d00c0c256164200741307030038080702c03009041a810403002c1c104000315800e1644081c100c0383c43d000d651354500303013061034200c0c03510304101e8444035014110390101640030740061403019544103804814600b9a03a28110f138403d4282140e0290020700401c0c05544924080c0c0c0c055503100d8005401c0c1c80c54403e000d4080b8542000590303400d035142d802242046440d076070010060369540000c0710700d0003022259480302c4100040030110 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 464524739 1250 464523489 464523491
    0x6070306080d14070501050f07021b0315060307090c0f121a1903050703080c0c030a08120a06080a03211a1504180203040c060804120e03030f1b0706080c040603 70
    0x3800c0f20112002e401d80c3c0155074800024000c034076082180f8010084151500ca02600c40c254416605840c0154042d18801c4c028000300410541c11840e0f4003022009411241c0500401801080b0a022409801b107140021b031603101000b9a0200010424100c81c44002c0d405841c140d180700c00e04401c400524030b00380d021111281811001c0c1c039218040103039a88014401d10640000000300100c0501606000c1c402c0c10603945451022014942c454880800c0106030300301c2000112070018000f41c01c80e800020803000002c2e81170f06c8038940ca2a11034200d4041c0e0100e041c11902d03070082c0b2004000e90788000c0c02c0000501074040ca860006124800201c1420b215051030410428a8001c4805942c010400c044400ca410b44088013814020360080c0c400703662402204002080c0310340035031081c41c001d03940484510002c0003201c808582884810010f030768035000400c02c2d4080216520050000b038400301c6040c14005180910580ca0102c95a0102051000b440200481900b40d80151801c545450130 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 464525989 1250 464524739 464524757
    0xf0c051504022704060510030213090c03020a031505071409010e060c0a140d1409091e0a021215101b0b130317090d030c090e040503030906070306080d 66
    0x1000032000c148081d1641d00312043c901c4921072802403d0142030103103015010421031500c5d000d40b501801650350201070341050b42c0e074410f40310010301580050841342c05042106140b5450ba40003448001c0c0d5503005480c0c00e5400402d02900d40e1042c800c00d5006101030501d1200b0141c0621400c1c2580a040491418011000c01d20714603620b0707180842d840d40d10304000707403280c0c41078524182111040d043c0744041d440c845d9180d40507040c3d000744211007141d51400060380c10001e05004001c00400014040001510b00f1b052000c800003010000c0381c0900390040c2d0150b1294080c202c03045220300020f00ca022020820352081d03403142c5505008031442d11b040d00d0007080e40007030701030503100c4a068060004d1030040032500704021214102814241d0603c42e9131030100440207500301500c1070400b074942840b0754100100030140280a07502c00602590b5030305002c22401da43d10a15804c48104842c141c842d0340000041200300102400420350260042c00e08000960a00c21140d030343d04802c038805003d00200b41 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 464527239 1250 464525989 464525993
    0x3020306010513060807081c050703050301050904110d0809121504030309080c0715030608011e02160203030706050108070e0408030114041e0902031b03030d05041b0303020606010f0c051504 83
    0x1d046213000d0051070044811490742d4105c1140d507541c0245000c0c403910882c008058010b40301c4c074212880c3eaa015501c83c0d0a41e400c010402800b410054000c443e01e400e90000c5800d5a01d46041c03080c4003501800310541c940ca8100700340440ba160300310301001c007508a1040c4007484071080c1f6149030001d8043c034000984103803519060805115204506210744510800040d41c0e406481825002038482d0b5024000725079105030103800c1c0d80010324138411214134074004e00346021645d030103000504205e9150f90b200301240d4000c01c0c02d40e4001d60043e18040d44170740040c01503550410200008040d8100e00c640b6a24040e1900540e0740418054540310076910031076a012a9207075003058000f84501201080c0511008078504024594101c0480c060302807001240301204040080b0b5141c6080600998a002c01284080e0001e24004208a8140000050380c2a8840448a880000d1807180d0024099810504005030007044cc0c0b2070000b0801072034522300c80001d140400c0d9010b03000e101e11a29a4551124 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 464528489 1250 464527239 464527241
    0x31d01020a0f06021e0301150f0c0321020d0e0f0703050a03081005090a0c0e01051e0327060702010b0f012a02103c120b1302210103020306010513 64
    0x40c0200c001d17200900302c1c58000142c49840214103c6d11092400d60160703e070f0800607180c07213001005036404281d011403007a000c40d0090f01045000c915070301e04103010001c5842c2d92003c1780c000c6180320076180d81d80c1030a05110030003000760444148890008001c401d00d10f030f645e250380b41c1400c02e004040003041004250502102582c00002d884001e2803e40103103403980c10340f402400410714450004243e0003522034994090300448089504506c0aa11056284e0074400c01c1607101400210021046201e46924000680c01c0c0c110792001c00320140c80c203420025002800e481c1300340d070385500ca000c1204143c400e6130b800ca003c1e0340d2040c0344c1e5111441142030001c04c03151042038600740a0b400003803243c00c071100c00307510607240c5998000400e411411080358071184025000c130306000e08840c220111580410b903000e03c004240912036071202091b1121050082035038903d06040d200710654000c1f800511090440c8040040d007082c06610050a61441c2c0000e41e4608041c0300c1c2d203001d540c0451032103500c9145 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 464529739 1250 464528489 464528497
    0x7090c1202090a0b070c150509010e012d14040602010b03070801020306060313050c040c0201060603141e130c060c0213090b180a0b0f0103050c1512061305070309031d01020a0f0602 79
    0x520000c05510700c1c100c200500aa400300000500148491030914030541c0110300760100715101804107e00b001c20f00f84402100c580455141b814810340d1540c0414ec03584000062001c0c08003980042020103070341d8141440d00710180c011104990051042115640301c0c84260b030750007591103440d0310b541c00c00f605016041003000004a42c0043c1464110400c8640541044049807610b0b601007042d00340d2003410450070301041d100c001c003461105513035a89001c1d03035491044c0c0014044044d5000506141e69036807143e0104c0e0f0001004c00c04601400c02036190540440d5010b00d6000400c0c00101c44a0360380303000f9a0801072084071000096821441900004c1002150103039110b005800a410a0b440345060210248000c4070f1038030581c0504140e6080103548c2c5010a55507c13545810001681c05004a2401c0202080e8019000c810000c0000308540605401069541c400069285190400070300c00e07402c8040091500c1c0c6c40480d0018985d0b400101c400e9040c0e003003070301100325040070300d0110041e00c9 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 464530989 1250 464529739 464529749
    0x20d0f080a0b0d0602280507050a080a030b090f0906060a03051507120e0c15121308160303150801180314070230060f040b0403020f07090c1202090a0b070c 68
    0xc800b00d001e02c0b00714001c484042824003603040149881c11120340440361072044800040986e0003440342b000c0014901c0d00608a401481d08001c01c040c012603000c01e6a0322000c54081081006c17510601101e61400d00019404c503d054840b40740050944d10740c41d40d130380f40c05d00c1c400c20300010305c00005143c184076001112110303140c82c2c01401303501184581641e5510255051034801c010045149802c00c2d1180115050052007025244095880529149140c1c13400c03001544e2002d01088000e4041d43d10030680382c1300b64840c0d10300003060307140314008043c1140340350041c52090b850031900081c581c591030041140030f54103240080025103880f9050246003e1640002c0d00706c414103c00651081c0000c840d4072554038003d00e0a40106c001c04132142ea5218155900c8410304040e4004c1004110b0380d030111a032107070184c01128541c0c00054407652a00503d5482203403225511400f03042c900350b00900480c1d0108039001e055091000c50400102d04010900c203803005490300003584020804041d0030000108 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 464532239 1250 464530989 464530991
    0x501150f1107091104030b130f021e040258061a121e0c0919081605180f060a0305030703020109150e0c04020d18050d020d0f080a0b0d06 60
    0x103c01c010380ca00f8640142c00101c078400801c0000031003c405c260125407045400090308004410580c090081841585807010a094040d02840005807a0b5000400d4560b00781400540d03002c041420101c4100b41c41e250410350240c1d0061140340085044ed120758154901d114500300c20906d142880c001001e007980000c0710765502c803072810710501911018150100715074200c0380309170350382d0704d000710b102c200b240b100c2105180c5200110790300b09910800382c4803100c0c0140c150070f90201c05400100813002150b002c00e0b40c1d035100303070446500001c001805400500b030554243c640e01170700925111800800921b00f03024009018002003c903136484a49400440e084000d59940b20490b0400070f0190016600c166102e9101840159075007e051145407400034061000d801c10703070006410400a5440b481c5c02040c11034581c280130007200d0184d4105060b01d407142000300440700da030703800290801c0300a000031014031000100c2c0f1134506d0740000049500016500d00010418010f100049100d00c0900300a004c103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 464533489 1250 464532239 464532251
    0xa09020d0b01060f0519180909060b01020c0f0d020f031623060f09100e15070b0a02040f0b0304030203122805090a02060306060d0509100501150f110709 67
    0x1c0855012441d042e100c4964070040111001d00b800d440302e00c9140c20f002171207260040c480510074810300c14170040300f202d124924143d5a441c044041503940c10b40c03060340c0c000da588500e40741035a010010080d80140035203003d18400301080008128101081010740584000d034248a11590140245c2c6140c6401e907003011040c54480c900c3c0c601c4103c039055000f10b5051120040500c601d011001c5c0c84080980b042043d107408082d0303043c003518a06250b9000180983d40c10900b40c41d070b64056030480c89030400c0e500e141d220070680c20301c40d07003028010307200e40000c0344100f0090041c0c1c3d06c5000003400751030180c00034903580d86172454102c0c503500c43d00c00d00500c0b2440740e00a1000f051507200b040301848850400c08400e065100255800711101501e00307124035417021403080014146803001d554440c50003000039007801c582da020001540d80c1281c07502180c0c1c01c0104082c0062103544a114094040200301d0800000e0003000907041d8001c0300303211814080745441140400d10708011100151002c60828004 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 464534739 1250 464533489 464533493
    0x51905040f0b100c05010506010519030b2e0806180408071a0f040b0f0c0301060311040b030a06050112090b06130b040e0c121501091d0d080a050610170a09020d 70
    0xc1d1313401c412080f1501d50801001c640c9643c810010b403070001c09140c5803050465503c51058006100038044140c01a0801c40000e00346052120704e281c103128805101e01090880c1d20009140e414014200b904c101e03015050450703007610303100c0110740c00f1794840400ca0740c403119424a6880203004403207001d45201400d0411070810316000c0502c0c0168401e07016001b160b16492840300c0020821600026000d10600041000720310030b4010080b003103a003030b0300c0c1403500c0e4448004044992048841c2108503889050400695138001490594000c090104000d807403050f540d0b01c001e4000180400f84601c10304642100b10003880e40c00540b101800500c200b120300900703101151603045000060b0b00c13540c5c0303010f1138070505440407400d0130a400d024403d028260303007000000d500520300e400c40c01c500c200826a04c2d1281001c00c01050b83e05900301d485408a03868440495015140000d001c207004940441030380040d6038000c101c0c00c1d9460900090103a10b0760b104101035006140004020390702042c1d500b40302c81 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 464535989 1250 464534739 464534747
    0x809150108010617010b01020a11130204030615060f090306020912010207030306090b2b17031510171801181406010501020d020303130303022a07051905040f0b10 71
    0x842e03132442903441400a145008a0807030345080300050250700301d072051400068203000401001500200001040c2290031505003c90700950000c407141d50b92050480c010180c103100040060580345040500440b03901401481080c0d14800100a190041000b000c10380c4c8865400606d0702490008544491072818001c1c043c2045d4890344440c0f920380208109141000440198588003805180b0400304143c82149101c0f0b038012015180e0503480840d144c1404500c00003940541401d504440484030881c0c204448503101c00d109500340302c503d0b014405920180048075600a054452051640e0f0581c26800d001d0071005e81180340d2003645907494002c003e0300018108080a192040710802d0303803184016680c80d11181820005644140001203251122115010265110789400344c00c2001c00035160122000e01d07a489800788000703600d615581d480c02c0043d44010902160111840841680c1451186079103014050049489149661419042c0e4208205905001c0e100466403080414001c0c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 464537239 1250 464535989 464536001
    0x809220b04050711070303080a0e063d05010815150a1704050a021201270203150f0c160f030e09010b070317070c050d020139080915010801 61
    0x207106628007404692814400c0c0d400000c44090f44008101e0a0305503102526454402043d00002a480b0001c403681d40f4002d010031801618055001d40c0c1700801c01c0b040020000303144540107580010940c3d10749225801c00001403c484080c03c200c0030648138040c0c45461401000000c58004400701d040e826015250001840d1070012a50756803071061074070030144107420082c1d50150080d8000d55280c0094600791030145011180900000b40030301004c003217018190b4404244060340d4000c40e00b040154242407008000c0c1c080e50707984000070380c545520b20000000d0050144410b0610202d040310046003555100c040b415004450710b2001c105a00e8000c1a169009442d0781c0192000400007405410960943d95820381c1503e6900c00d1044062804011007401044541000350803080d0070045101809540b11922055001050f5a103607065680d6400c001a43c180c101c803510f4415408070750780c0500c402a010700881c5009483c0d40c8607291491f24002240003101c0220071880000100751405600c11 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 464538489 1250 464537239 464537261
    0x120c0a0914030705062a030a030f0c020a0b06060408030c0c0a0609030f08070218091507020d080f151003020705010b0a030b060409020102100e03130806090307080922 73
    0x10910007512084244150007154000d150141e200100500007442e181020306280104d40c030342d00083c403810030020140300c031070100110195003000510130b100d60f9150180240c0c1c5402200203010a81480800a666004c14500034050000d2078010522680d10002120010040038046a8403000c088034465150314002d0400f038491094480c0000d00240a0700d10001100c1d04840761040c11b00c21521098000c0c2d1001c04101d074883e0240c401c0b000e0f400c45d052040c60280800d04001d040d43d140c060230032002d4400251103c1d0a55004128803017010b580b20216651003002512941c00d2031301d5101d101b402c0750180704030751540021103107916003005074940c1c06040d00304e015900a004c8500c600c81800a51790b40c500019003007205500000d52903003001c2c1c00c4000c0c1148103204450140499204044c211908041c0216442e080051108080d080d0400a90301420700704c1e020b88030a0401e40081030f039038030401030000c0c48410045550045651148029031458410416002c009214035030100c0090010040c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 464539739 1250 464538489 464538497
    0xc0201050114010f0518041508031c02090f040e071508040c0e01180b120d1d06120f0a1e0e0d0903110613050604170d0203120a11120c0a 60
    0x200d041e50b41c850038403801a113000c0c0c1c0b58035103044010261003c00c1442e02c004a6001a280d9010020712480556040028040a00619101d482070140c0035130802100d8040f107040e50061001003440e6540b100301d8002c4a20403180007600581d80d801700c1303003000500e030b01400d094034840f1001051340790040201807203140b1604211024507200c16250300711220a00880b13505d480002c1d003001240c442035100300071401c0700502100d06407409031515898203000c092903000003904901c0312040784481040301d00315020112a80350500070401034001140000500381d400740c01002000c41c90b061070356804829410000000110f10540c42c00344100906060111218107104480103488000c3c0314014103000d0b258028220182008810200442e50b0010050009480c002000020f02ea82e0740c0d0700144021b142c0000d15080c0030054803140384c00c0402d01d51007038055410420882440321301074034080b540070b0044480002c83d00340343c1a100c212030040d42c288440d01c2a4090600600700e01c1d00024010700b001c1c1d952 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 464540989 1250 464539739 464539769
    0x40f02042903090a080a0c0c060306210503030604091b0b09010e030604050d050d02090405161b24020d0c020f06132d02030a0c0501120603050a060b030c040c02010501 73
    0x400c520907444112240c40603908070705540c0c4006517000380204507400c65807401c030784804581c0e200c05040362002e034040c50111740d0340c0700101b206420b8041d60301910892103200a002071aa500c8032034032488010a0b20b0b02ca85d55030f075049020442c1c2c10741c50b1207901303652440c50f0001944507141960682c1c4000812404910461200c80c01d92800290181c41541e002005e03049048800030245c400e1382006804989143d02806500305030384a0740b141d140304492030b2a091540c031131200009001080c9054a0501c948802c10505010618803100301c6050f0f2038410b041c20f02da40b24031a440c0020b029041c5400d00789801c04111099807680011110a01580a003c1e20f0745500e8643e84e02c4500c0203a1240205064010041042100b00c0400c0d00202c1402c2c16091003000d0039540e00207400c0503403410301100d100c044a1001e02c03003540e0241042d0040a007200b4204059421601c8040d5201c0071000014612515105050007a844c140030802c030000c4090014000c0304a2014064080c003000d00480164078900c1c5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 464542239 1250 464540989 464541059
    0xb04062f06240603190507260105041a1f030f11120108030405031f18050d090e04170705070506030a0207200604030b18060411041820040f0204 63
    0x9044a002d145240c61084117003451035612030140500811410501c002d00711603425008846043c0c000b001003088041800d5814441000112010740e903146400458000c81030700962141c40c420080e244070916800f18107140c24104601818076030034910a95400c0814194164100700041d1101c580c0685070325074242e803100802940c80c052481050340c954810028802548c4c0c08110086000e20445400b08000e42e00610a003031000c8204411107146d4000e210b03146621f9031010745980900000200d0551a0620303446660342a020070f1600d0521031400150642000b10070000c5000611010340856207034505000a28025000214150341d0f4000994103e102c1d662410b501000301903008040509280c25502c9060010713a008141400f900314041d03150032040301c1041080e2281d8030401452509440760710922040c3e0300c06450280c255030f00c0c07a100a0000d610710344200030140300e0341d4400c2210859600080c01030300b080c11101c20080e100240204504984211198041c1c00c580c4500328110008 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 464543489 1250 464542239 464542249
    0x512100f09030f140306120f0f061f050a0501030f2a1b02090a020c030403080f0301141f03112709010e01030b0408071103030c070503070b04062f0624 66
    0x8444410020b140c01c01c00900700740340000c002c46145004000f110075805aa05850f8508074802c07000b041d27503030302c054101300c843c00c184410b0001034030756600c0314218140703800040ba40e00002400381c1810715454aa1642c003100b50f640c82501800480171101e541e52180940014803280161004800241c41c8809188514a030400200e0190741c00707048140140e0302e03440490025044400c2140890204000003c0800c24480241620350080400e0703541c0ea5150410110b181900c0f220581d0240b00b6075650012400100110800c0d100300302e0402051030780c1c22820b01c410760b03c1003128001503039405841850014502d4052201e0000c0c055030041d03050b98888003c4a078403502480021f000d03a508100050025104101500c80b0520a9914803004505100085c0c2150000c00c0c040303032164003000b001c110601e0100040e600070808a05030b40c0c509800c0c03000c0281032500c60300910f00e00380303400404110558021003403e441c1c801c000c4292a0036040ca100c0382e0118440301d03840da003821010440345898a14003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 464544739 1250 464543489 464543507
    0x706020c0d020f0406081209041a0d06051b07150e0307050a1518060f1d07060e0f030d080703151203080604090501020d060306180c0512100f09030f 65
    0x40100000c0307a5401d82e5080014918404004980040c0c85000001c0c3c03410081100d15100b02c407400032952a015000c0a00044840790307000444442001c030906c614540b1400060021607400100100303c07541c50300903008145140450301c1c85800b50006289043c851005d0909051804401040c888401c0d1401c01c2980d9020b0316802615a03040040944005144d0360400b10501d0000d407404030b04400c03403070f0400c02d106400b0354050314031036101d048500308811148501409210210300e680c2400000c1400d00c1e55070030803030042109001005404049668641144242c0d20500508864003160010b030b00500e81c7d841a0313071940200f8200780390101054288054481540d075062084425141c1c5610210b0320040003400554001d84d982c20004003007a0300b80000c180c0045084408201640b8500d004800c80f00100c00d444545413698920344000b461440100c4221032080342e0208594690401190800340404142ca41d21880c00c103d0505100d980e40201d0f1029000703440c0c43d9a1141c1c00c60082d290090 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 464545989 1250 464544739 464544763
    0x9010b130507020c090a0b0d140d0f050414040f05040305071b0b0d02030a0b0d11010210020c06070507051009050a1101051c0c0302120f15031b0405040807020d0f0203070602 76
    0x400c0704c00c22a0030a0320365150301c03000c180d1020500a05103004640c061901002c1a604061201000c44801000308a003900c01340032403900601c41880c2001c010864022030280c1d442c54030542c030300030060303a642da0803600b041c0c03402000802c00ca080c185400307480d5510102c000c07204050f41400401c0c080503c1e0401c00c0c01c80b0a030b144501d28014681480074003e52008222001d0590b43c0c01100c40075449102000180c2e40c426818000c1d616080c1002900d841c01b4100d034043ca85004210301000031801240442d0440000c0c105151203004031303e41141070144219548030b00c986040c1c29803090000001d40c2c400c4490103030000c0069160101c00440c0c5500c500d0814009491500410118100055020450341c020520f070044c14103010280200642c10161b4000c4400414081805075500c011103842070140c000b10028a01d1107580c010707121aa0043e00e074503500c2160fa030400102841b809108884240c0c3d802008210302c3c0e1117a280c106007500034490282d02910032900701049803400002c40749000c0e0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 464547239 1250 464545989 464545993
    0xf06050a0b03070f03090201111618110702040506010e1201020405010f050a020c0121090b090f070e041b0b0f030f182d030307090812161509080309010b13050702 71
    0x2103200d064020f0040c64000302d04002c2104044050408140158ad00340511403001201041c0740484040c1803404800d009644145000c0e607459600c91b101084814150341a01d0104284d580c490060b1084c0580c10201ca81000c0f070403081266038a0107500800c1070f40c0c13003600c2d8600a4141000c0c01c030349602a03040082d026030302400d00e100c3c5a600445044d07403280708100255641da400001c5c44019074164000460303500d01d2180502101c4003051114030460305c0c40200928649280090000304d440b8003034130280240704040d001120310541c0e5504e0b200a089100e2034256680810003001c0003545c41140c031042079500c8540803909030400c02030340317400071034040e4010b01810500584000399225040440740b603204800f540440002e8050000e944140a030b41c894080d80361130a902242403601902c85010010000c01502507400e1884003002941504280c02c0d800c200381c11120040141611800600802000700400041c0c1005400c43d09075040103554442200b113007001000183d44041d10380c40b0143e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 464548489 1250 464547239 464547257
    0x90f0819110a0312050403020901120804150e03071403010f062402010e10140c1c09020f0a030b01060e0a120b1f030c050103110307020705120a060f06050a0b0307 71
    0x8607010a0140e04010001030040c0c2d010b554940d84c14004008424481c07000c82c01c00b080c00c10561900040440c01080c03500c510319410308455072108030600c180e019403800241000000c43c685881030b01c80e84d0f20a2400340482769981c1e00d0303038004048800f64180c00e6200e0b43c2402c83c0010182c00758041c0c10304507005480d014284003010380000b00628806079400d01199039900155150fa03104000000d101c080d018000141e821321080c031012202d40040c4540d10840d4100094100080d1164140081c4018400e0003e00f0b001a440007500034014070401c00d078000c4a0300004028004e840300c92504030b41c81d03529814009140740b41800a40541445a03c5205803c500ca50b4041003840c22000c0d808031200110310390481c510030f4200701288180d0000d50b000f07014403400340f1240d605449020b001001d5002c41900390314002e00000d50341c3c0e00601910340034603640a0f40c0110308404100c1c40c030945a20200c14401030305441002801400144222403003801c11120010f004c01e03150040341e000f071255070359a100c5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 464549739 1250 464548489 464548493
    0xa0e0709020f0d05010b03090f0610030f0309121a07021902060918010305030408010b09090c0d031206120606051507080f0f1801031415010c0c05090106090f0819 71
    0x940202c107189966442c03c0295001407101031284502920b03002518036200e04111f4941480e20200c9104504a0b130f02040601a420500031280310032640d10482c1c0b405441200e240890700074010341e020020001d4000301460030810114020001d500c00581d1070012a42d80503000c90b511006080240b002c1d00f00e40703880382c0260425900804401d04054007031351940003601801c04003040c00340c1c42078880b03400101d81030014a1080c000e503440c4803400c44985042d810034501e0580c45d100d080130442c1c800d80501000700101400b50511a14a0003003e8041000781c2c2d80328050240ca0300313000421585c0a00d8000041040c4c5001c1010f40002c80080458900744241c035a00c1d00c46550240003e4480048144504102050690b00400150203641c54030f0a140017507034000740130307516285d100c04000c1c1c07044020001d01c0101644074440c0c02030709113044c101c1ca00007420b01d00c0602c0701503088250413050300341c00410042e07005103190044a02401c0c2d0f514415540d5034440c0c0e2034203086183e031400010303c0d490740c2d00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 464550989 1250 464549739 464549741
    0x2010e010e0d06050606071b0e0a09020a090b010c080a090303080901050702033c1803210906120408040e07020f0601151b061b02070302030d0309230303040b0a0e0709 73
    0x30340584041e001c80e10f002815100c2942c5002300c041207200740d0400c0001800b031600d4000703105810011034001800380c2071803503000661003030260007460026592000001e105a00c110700610040d60890b01151346c5030740594008085101500040d0040384a0f400450030910b0305100e09840b591150b805981011010b0410000724007001c1c00d007052a100c4044c0250070131880e2000c004002c0071070703040a56504c0c002d4041d089245400b0840610a42201000c0d0902038444400c9460502490380200e644907070b80030015045000c0d6400d401c0c1803d070301c10200b00800c10650010400e883c06040d01d49620386e40e5006c1203076900301d44800101c051704403200410466078040c00710b4000440d24100600f01c0080071141084030303850440144e40d481e07110240309044071504a043d04100001c2d1024003c482d0840d004250381d444460f14050826607a20491014800340314512064060740101d080b1503000580031107641c940080c1d8060340c980c030703181003c0b81d0b4ac140b25106003050904048080d041030352500c1c3c0024 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 464552239 1250 464550989 464550991
    0x1c060510110606212b0f0e090a060305030d050901051008073c060f0219080c0102040305030a0206070306091416020705060d0f0c0306060903380402010e010e0d0605 72
    0x400d001038100600c0200300b0303041c051194202c13248103407488a81c3c846142d04080c040898645001d010320a992540d50a6104020103c540800d90f018070b00b50300c0c9c0b00700c000003c014079400940140808102d1020b0182150400b9000e40340039402400207440319540c8070f9044982d0f108404040e4490081040b8140c0c1802009019030800b00c9050b06074401e020030780307544090100c102088170245070401e00507070740c10000400440741684001d11f201c443e00740c0c0c01184806001c101400f9500e020840020614007501124051a880700c00d407074691241a034080d5a0300e1007503130005c0120781000c00c04268a5000c1c8554140c0c05031040200d10140c481c0f0040c1c0c2090040f40d806481140581d10b80881d040d11154018030026504035000507040060031140c030211243d041e541420907040000400400b5400740202d0282d9820001a45141503c0f0304200e004804030200c48892404185d20b1420b010000001d0b103100d14001e0725154507404810b80111040d03852140c406a01c511844482d41c04141141d00003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 464553489 1250 464552239 464552269
    0xc0a05150d240306050405060c0a020309010806040603050d2309010525050f1014010803091005040f030c140a05030d0c0609170a02190f060e031c060510110606 70
    0x80400d8401c030700010b540300c082da00140c0350702e40c035503051104002040112561181800404a09010869a001b9180e110741c02c1e0080c100444070012075110b1b81c499107c1c200865026003121198010600003501c101c1c0c3d00ca150203c5031407030000902800080c2400c42d0078101c01659803d2030302d509414441c2d44203a9660f4459450a40084680000b802c2040292046c441580082107030f0155040b03440c0581e210300c400520704c01549401045410030000541b61444c3c001c5445841da01c200640c11941402594000c8c40650065000001481564403211041e920900b4070001c01054000a00c4910250342c400c80350103521281220348054400d201e10810307240300b8840400d0780140ea480c0c03030801c0b0080614801001d00006003502d8079607010403d03008648000c0d520a40340c960036464900090380e165001901c00c079110410740744110b80502c115101100c07101d6150030929081d07080311300103000074011240616100112141010f0180f000314070590003000090200b07070340300790610803c000d083c101 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 464554739 1250 464553489 464553521
    0xa060f021006140d262703061b0c03030a05011703090d06020c1006030501022a030904090c08012a091a13030206070b15010903030512060a090c020c0a05150d 69
    0x1d201c00724070114000180391504039400d40310b48a04103408143c20040496080e41e2141c00500c011503203002c40e49581c0542203250311484600000f64031601c2b80705090007009603020000400000115a602c0349050b104d0140040d50703900c50034a150780d038a110300042d09070301000d400b9040c4000380c61a00100131102c0e0700001c1d588604503a12040054074038a07041200c10785d4001c00d180c40c210b10728991100e0300400c1071004820321910240700c03136140c0c803600152074011515002c4950900040302c5503034000f03214401c003c1003001c00d18011540e1000003d9078a84da03400d00764202c10a62881900c0960940e50106030003d0b001200c1000405560301050701c0c049001ca2840000025940d104080d1801d917001e01a1180300e407a090310301040b592a0400c405041c466070440910101e64000255030030750284841d104490b860300350006040c0c4035168045600141043c0c002080c0c185d001c21039503107003002900c1394601c0d04c1c3c58800b044a50201803110031003000040c0303c511034011780c1d900014029020710407 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 464555989 1250 464554739 464554763
    0x40207052e0603060504110402070b0711031b0d08010e061e0a08011e0c0512070e03151806060907051603171003030215040b1f050a060f021006140d 65
    0x9807040c240e4080394401d4039105d45e910100400c2c0051542001c19100c0c08440840c0351600b00c0d9580c03c941140900030104002221690125111040085a4809450702080c00c1035a1031f500c800c5598402c4600340c0b40029001c603000056140c0409a21070241c0801010010302d4491408644c80760400c0e188416445000c100000403034403001c1c4148201c40f4184010212554004910074003600c000750802c0c82040020019100700c4000d0510058200701b65183c030b039414a01d1100000c3c0303020a008010303441c084588003406060f6510010003000c12504405075811603440b0010045078200844004000c6501000300d40c113001a002d01c000045413007070510034942c0c0b01e400d0800e404801c0032904c0b12b420000c80c25003442410f030104589001c0c03604d010744801d414a015035031403d07050000703440d6290407119240003005058400e85103c000d000301824030500250303140d01c000d00003822491301e0000342c081c0344c100401502a03401218151403001d141d0403400900c11042c420348000c101c0d010b8a80b443c0003c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 464557239 1250 464555989 464556073
    0xb030f0a121b0b090102041508100501111f02030a0c08040b0a09030203040e0103030e090906060a150c060f0b01030b09011a0a030209040f09030f0c0506011203050c0f06011404020705 80
    0x71010130300800d500c0000580750307420810041c4021425400d01000d0120702020058189a051109415228207281140c0c803498260501807070300a0401c00c0c1c840d00ca104040c40c0480c10300b15170145101c1c0342c41f9013061062800c4036809480d0300302d040d64090001d50820f400500320360381c9900b04420311442071040300d1501c3d0740d51710001111882a04218001000e00310745000c1031a106c00b21a4208400101810042c240b440019a014600d480350300800c00190174580d00301800307840c1284840c1e40114040c8500a11410398000402500d0651800f2a141184400003070801043d0107061b070ba00101620701520000f40d00d85929000070080c00c0801da02007040710080c2e281c602451442022464001c26907110516024100c40c0e000150341e820004c5001c0c500c00882d6001403264111200e01e59075072100c0045003402c641522804107105118820300501e110034042c0000c2c4541265180e4080205400714041000140e100e91000a400e0b42d0066030041000c4a1025052b580b80651080e15141c0700004 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 464558489 1250 464557239 464557253
    0x2090307030b070e090c0408030702040902042304200922140d2a150f0204150210110d0509070e09010e0f070f1206090b04060b030f0a121b 61
    0x103d070248001000c440080c2031034141007440c2500f20080c1c6202c103040a0138695280c2d41d82c0602c2c0d2001c0e104546600c2e6940c15515164000c440d07000c401c5442d00181c0d851500d07a441002402c4c0c504030344820048148a03a2070808180c81e003821000100f0000c05074840390098444641c90303a00e0780d40c520b1054105000041c1c851041c1051300d1032400c001d40b64074100400042c24050b0b0151170005000d00c20a40070814a00e1711207070006c0c7c2d0394040d1445c0504210314001000030010480748411092000502041c110461400d1050064141d0f00b01d40c0903800070106001130f0b1f0702c0c9018034240b0b40030610441c0b400340c10f103800c043e900c1554402200c402955507004411540303401d961541c3c10765901c101d644442207060124004c800e5101000301281440c00102090b0034405116508202c55a49940420403495400001402c2d821400c20307112801d003810003200409101107164443d03c18600c2c6101040408941003000c40d4015980442a81e0760390000e81d0b031880c400d0101e450170315a4030b070300c100081e040f = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 464559739 1250 464558489 464558491
    0x30307090b1e070b0f070212031b0d0203010f1707060507021c02030d080a1508070e0c0d0c0f0906170408090f030a060b03070b030121021c03080a11070503040902090307030b 76
    0x28144003060340c00c0c4405c91043c048000b8004408540008a055144800c0d440c120381d0000780d80460a40b01841f0303a07900e1145401029040494180000000103416010301548403d03108102c0455040141422195580300b0380c510405000c60004d114210141c03a089081030f058801c441c4908080003941d82c000784c240200c614209011078003440600a03000f03168820420080f003d81d14100d2202e04181c10140d032100e07a4441c14242d0101240080c1c0041800c0040d03c0f000401c040e418000c6141c2840003800f41500344820100166102e200010260b00c00c52240100d113a0030b00d410510b944560322006590b07030010707100e00d4002280490311403203070318104194040c1d0340c05100002030b44075287c0205030038000103030b100012881050005010990b012240c0500c550151074a00700240748500c04242c005030702c102141001e6807980d2111092540044015106040303d050800c40001000b061200d5400b17410000f900c0c9a200f44020301c1100d0483e401046207450040840d00c030710340e0b41d580b0342e810124 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 464560989 1250 464559739 464559743
    0x121511120a110406050706050a060807080a110d200f1309151422060905030a08010b0c070509040c05040606120e010b0d0b130c060e12030307090b1e07 66
    0x31a18100454818503110741054188032081440c500b6213070007001441c60080c10009002e03181d42d94040742400d134556211030001c1c5100b205503800d031923a07641419100c4c1c20142080d1100000c06280081914028194082c00e40c2d000c4000c0c1d84c0e09070b000c0340c9911005084901141c00c541c10a44c4a48169120383c1b115040c000c0c40a000715a9007001c0c034001e5124a203031512440345900380040c2a144a185039071181c0c0c00301c40701042e0050a15400c00000700b25068480107002949026000002e000e408401454106c00c1920741000c1a41d880070850300c14845c1f1002c0041c5030f00301040030300c2245000b8042c10b0b04140a04988103025441e080010115500c40d030201c004100c0200d2808440e101c6800b075140c004c82c0802c02040440e41100c003041009406010082c01c074181c820005044569100304188204c0c3c00c11000c445003500d98001800e41590b11511030711a20500c086400441c01c00000c5900c1a142a0b031040c0ca185e1500703802000e660020210030701e0700f0500c0c140c1102c0c400c1c07c0e5409050118 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 464562239 1250 464560989 464561017
    0xb03090c0109120b010308070c0504050a0902041b02030d0e0708010e0601060f18090b0d0c06021e1b010f0903061103040b010e0403090b130f08210301121511 69
    0x890200140030140580e1100d28885410f400c900c000c00d000c0072482e41100d40080c6415520a000c0c6426190202c07260010742e406450f0a0600c064012154070581c800340c420341c2c2c10051014545c4518a0021003680c1c0307440180c0c42000041d809103801e4100e030050a034800d0071140aa5280c9012900307481d900030024490340d00c041c6c0108190380d40074602e101c8151076407c100c0402c129040da50716242409000b10a0440d440c0c4507106119204c0b4084016801e4202c2c80c014001500c4603002501e40e800c2902c0d4144080d41801e40c281e2040307020910145d40600c1c41d08800024040f000152184040b4400c50f4052090202001004c1140350042c0c0441e084100c8041c0e98918240c9404949d906068200c0544610010100400241c002c01d00b00d06550b10b291040351a011212401e10191000303422200b030702520124005614a0002031001517841000c4a4040c9000501da03901e800e408240714042c003100c6410741d0700d008aa103a815a403214102c490700414100c207031001840e0f044e40650801c007210 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 464563489 1250 464562239 464562253
    0x70803070311180613051c0201020c0114160c030b0f070306060306080a060b04110c06090c100f0807020709052805060604061b1403120603120403080c070b0309 70
    0x305915100d1540d0100c40b03030300414100000c65282511031607400d0307070160080340e000803440e1825016038081d10003014010400c528100c3c022222180c0d1007a1040100d000d4411280c80c80b5466014443c1e00c03604603030400d070580c06c161700003810802c07684940500756442c1c0f002101c0800400d88003208103100d440d03012024100c90410f280700900710340303d41c1e010b0b0040529240092101c1c21021610030705d01504100045a0035100b900054004c1c00d102c4002400c4607030000708020b03444404150b01c2d1003030340304c43d003914001c003002800e00c240c00e0100410000001c2180e400070b040c142c018000380d908500d20b841120300242e142d10002c000c0310300c195200c40100a0740441e42030f8000c0c048012140d83e00c5440c1c018029400c18001081043c0100e000301428003261004080007640e80103105191640c0210700d91480d0044600d000c0c1d11b1354000003547c0900000b00e00001c415003000502e080100900c82895482c05186d5107404d0815044140d4590103406244000107080007030300055805031415002804007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 464564739 1250 464563489 464563501
    0x91c0f0807031403010302060406120b0604140109120b06060d140a1b02011b0f020f070929011d0d02040606092607050d050715080411060c062703070803 67
    0x6070140f00c0209001810820040c001a100e41007600c00b10351050401111600c8418040c2010349a04210183c003c80c000c10006502552889624248807003a01c8000e41c5a807603114030030030003210401c0a000395038808046000d504180c40101200e6045402c009141201540303200700360700054810407580c9480d00000d11b00f800040b4800d41090781e00380000c001c000c440401004000610300c1c40d03c402e00003541c1000c26254024022551003c2c401e1068070945515490b5080c0100072146074503140031202d06141d24010050340c0620701044050b102c80c0c5a20303841000c0a000a10500c4885800030102c0e048a40161164014440503014a440f42c111071414800300152034a90859007070b080103c071102000081d8000300703903e0b043c3d603001d039203112040c56030b41050b501d4028560700c504000c901394480131860b158080203503070089100e2071541100900400400181b4025079a40b400d15401c003201213000800111900801010040002010300b4600d12019085401c4450141e0f0106800410014 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 464565989 1250 464564739 464564747
    0xf13180c0603020306030703060b010c050a15050603030703050d020a0c0b04210201060303090e07020f030a03061508190905010e01060603150509010b160302032503080702060c091c0f080703 83
    0x2000d0715041c5011811894000002544d54400c1d1001515241d55208901070320392003984e0f0703400d22070707000300440314400071a20b001d880d00640683c03010b030f03d146450003185051402201711403a00341c05a81d010b0400b07140040c100025400342c4010700501501c41c54086c00a000056894856405041d4107100340307581c5142c00144145800e440c80c2164503000b401e00001e07420122071000e0345c1ca84001070034559a07040702a4546400c9030b80148480c400400ea80d6103659060f0000e0060f120048000844d460354150182c0304460142c560b408124441c880c40030001c0e0040e8084405540140c1c00845e0203880841161b00310340c00c40c3c0040001031f89681c680c556520000a8000080c8800d0f40c0141c480d40c50000100c10070701a40c0d030207000340100202241c1c2498400c0040d21440c0d0500481c00326401d0000000c102c015583c036504401007580351000998290010580c03d01c01c0e200300d02d40754507042890341002148008500040104128002e401c80881e0701c00042442441c4900b038501c5d0344441c1c906020b0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 464567239 1250 464565989 464566013
    0x7120308070210050c0d0203130606080a120306061e0c080a050904181e060e01060b070210020105060a06050a09030c0f030b0c09100c051e011506020c0a050f1318 71
    0x4503c443c00c080c24002d4241418046a6040040040c0140c40e6115102c1406034280c0246000d0301da0f5040040c0418140d0011030315911281c894010280101c1007004250103a842c40e00c01ca0012405001110031104d910050005803000c0c2850035124102e00c0703688003402d07504203814440000790049181c60550074140b00d601c142402500307031106108407594030440107013080081c05a040d20280724030340c104141d1703402107034656440000078800d00d52034040c214003d400052041c1d00c5600d10283d051401070042c411140a44005000050381c036090100030758607944031000030810810940c3d000400308001c9202d1401a0800002d1040342e0340c0765003003411441c4c60180001e051034104000c0c46071559100801e801701050141000c0741e9188440c00c040c0c0c2084181d588000d030212112000d100072940c198030161040c1d002180c14200c44c0c2c1c071480200ea580205410303040c1c00c101011418006443c04d0b030842008a07100500e0040305070413502c030480a94000c544049101d00d50f82c50701000300404150703c2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 464568345 1106 464567239 464567263
    0x7030e06070c080a020f180c0c3903030c03041a1204030201050403120e03030606071b0602070f050d0f150e120408070e13030809071203080702 63
    0x99115464444c04900c00e003c039a030f80900030700c0d18200c102071044082540004a6a4074222526140d0041c110b003a182d10500184813800f224010006140074958200900990701c002e522030380210608101c00d10a070424010700b12411000802d480407201e46061700000b80d203902106820a1007400340d400c0c3c11484990401041c5a01504291700680c0f1a80d01c0100c4403190540300070481d48154460001d1750000c001143c17003490311901500049000f2448083e42c41d8400e185644c0c049040d07840840581c02903001040010a54ec014000403c400d0322600e5150080b991030b075262609404000302148201e608500c640c0f44a507114040514134402120040001882414007540140c400c41c10540b081170b82c0810044c5403512214058280d000340101711420315902500c0118000302004024440e040c40010110f10b02a041040d85000751250b040342d08041030001d09103240c159203 = true := by decide +kernel

theorem cover : BRFrame.Cov 464388489 464568345 := by
  have h0 := BRFrame.cov_init 464388489
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464388489 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 464388489 ≤ n) (h2 : n < 464568345) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
