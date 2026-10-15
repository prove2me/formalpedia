-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4987
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:22:42.843846+00:00
-- url     : https://prove2.me/submissions/4a50d7ae-a63b-4a41-903d-22c37eb32e53

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 896762589 ≤ n < 896942446 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 896763839 1250 896762589 896762641
    0xa06050906060109030f171c05090c0d020f0a121a0f010f35030a031136060307050901200c040209011107080f190f032105 54
    0x40c88145009894039002d5500038009140d10b0400d2001c10410341000301031a20030b10b6a2510012044522070603030700030405215800c0070713101c5492941a020700490354446040e001800c1d01c00c0c6140006a8510000603010b80100500603901c0904c1e00c2d02d161000240139020a0000008000d1418001080c00303d020900c00a042c5000724043c0030100e04018103882c01e04c02c4195003e400c24048020740c4844060100c0c200350500e441c00715800781419410b04440c1030340b01a45d030301d0850100150548140341c0c2030b680450020000b21b0400b81080f407040380105801c0c00f5080c403410642100724044001c03015407951110300001407100b81608000241002c0c4400c0e210900c107000c004180012411070003000740515003000c44c1c120310901c2c0c1540280822041410703e41c111004003210585041066000b00e4499400500003001c0c821080108200c0e801c401860036140c0c030741690307803941000c80e00380005080c46040d60914004440340c404c0703000000340c0b0100070002898942e41401c00700034103000d406102c0d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 896765089 1250 896763839 896763841
    0x2100c0510020705161a2710090f0f0b042c070822050d0806040e10020a02070b4f05151206090402011b06090c0906060c030309031803050a0605 63
    0x100c4402500307404540780202e81c186883c9603203041f0b40d03038000c003504440c41d03070201050203060f690756075103844651440e52002401800c1106c14904110190414891855050000c0100307020050860341621204905110000d800030f20b4070310341c50382c11f080c444a10344644003008040740d80700503950311a03007480d035109100345007001e00c0f117584c890901c80180c41c90f00300c94031710600103008000180e04804040c20001c3c03000b48280d5100d0404120030000d0701c03041c0d00002e9114405034108541c20141414040c154640500040240d051207900201142031000d400307103090003200c0c0802c2e0000d0309440000d44400144c00016440d140c90414060031384030f000700e5901c50308007004403403c3d5519140103a001e42442d440766002c0124180f0002c100301d04002c0120300703043c0140c00c0b10610807485c5100e0b40c0c1c00310303c4480c80c4c1b510f0103066031590400e50307405262160030803400d80e12060341c444aa416081c0040c00c0320b070300d041c12259440d000301002e5000d40e0a0300000200140040d080d04400e000740410006 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 896766339 1250 896765089 896765099
    0x2090901060f0806010c051c05030907060810141309080903010f0203100e04050c0409050d1238090c040602010b0405160f09091b020c090402100c051002070516 70
    0x1060044082c40c00003a0300d81000403125400b030040c0d02080341c004c1d8102e41d204400b00030311900140070000e0001c00104d01205028443d10100070040203007080d1b04200200d440e10300084422861548a03844000c0c1315503180081e01d0325102c4001000d240c41e200d060040041d18100340803181c2c802840a8080d41c070304882c06206001c24826a4002e014800151001c0e45c079040c40b80b0011407026000381d42e80c0c003c0454106107a95184071b851540e5200300c000d4a014804800c000c7e1840c034694100351403260800c0c0f601907580c0c2801c40c5e010040c00707018402100105d6030410b40c80100241843c4142c000c0328901c240700200328404e001d40200d0328158000e10100c40041d00b071100b40ca4054925031014802040343d07a01382c5000f1010205002140c0c502110740907510b1403040190350116500891009141c0209000d00349d0500c54040700440c241c0e900496410030b5808500324005072481c1c00c003041044020901009010300c182d0801038444131041d034aa03503490410545604c801050018500d000c4640054 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 896767589 1250 896766339 896766347
    0x106140316031e06062102010212030621030c010c02070812040506030c0702150d0c170708011a040909050c18130821090705090907080606120319030209090106 70
    0x2030b00d6100c0200d03411683ca04070030800c00e02c03100b1000c90707480d92038801c04100b00a280d0440c5003410101c0b02e000194011700d000190400c03040070b509260302c440810800500c0c0d226019080ea019489001501c48105200d61250643c00340050300101542001d200e20f200c59400074644098440c000240d40c803801d0704a0001002e4440c500c107442c1c20003000d1000070380c00003600020b400010b00143c10039000825011000c0550390118210f44851030307560203403040580c2d00c03907040c3d00d090441d81c14803661800c01c400041c3c040c0c11305115072070000500c03001c044044140001035800a0a8900080c070103542645083d94031845240203070350050145601c5110340e8004810500d005541400500010b8142c40d11465407a0313000b0200aa01e61014282040a00c5140e00d252449142484c0c007428a9500308000c10150075070140c007501c52603000c200103001a02e004681c10b42c0242089618264000ca560895811070140040c0482d02007c01d941007100990960003c110a2004851707100c400c1e80c0707d04040d1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 896768839 1250 896767589 896767633
    0x109060b0412060c0203040f030f2001021e07320312252f0108011a0706140c0403030e18010e1806090d080a0908090603150301061403 59
    0x64003102c89240907004100c481c0c0c0001c40c40c0c000340c41580c1c030342512006e0f1000380c4c040f140d00c04c072082604446041c06010f04103603980e404159034040300c5801d602c42c0c00003e40d90748074096503802000d0307140c03d4400080000c010b00c40040c01c94541010b44640c1c2e00741c3c0810746411040b107800c40b181c0175160f500170034540403410313031b50140d412b444c03560424203e1a07030025401109200ba07040201003002d51307404514403038011600381e082c9120130702c40d03041ca0400c1e54408403488880e507070502861380010710a10f00c5c02140702107081c0d1001c0209842c0d41613818084041c000320700c00000640b00c4a02440f406001039401082904c5c006d854200030303690a00148900380d404801500724050544005101c0c91851140141d000f40c2410961041e0003004564036083c90b5080c2c8244605038083c50481030f1040d0400c90880c0c1c805420740303082044c0e0861b03480e00c0801d44220140244148000800518810011182d43c1d0700e10001900030410662109030b101c29400c1c140d03c14a200e88070b0b0052000f59044d822080c6 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 896770089 1250 896768839 896768849
    0x5030a0e0a120329030d18080a061a090108030a0c03050f03090a0b070c0302070501050a1107061808011415030703051f0e011a040b010507061104050a0605030702060c0a03110c060109060b04 83
    0x50120156600c0b08840200c1e550b04d001550400348440028032408c02c001214525004440000e201210030741c064100d1209040924010102d41e0300400285401105840f0890340500700152090018a02280d030b5100303040c444440700c5808002e000e11321000003a10303a10240305c0d4045c10200c1e103881c1d009031611360000c500100140d010000600465109402400c0e40301d00a040c1025440440307404c1900380b502c943c0004001a40c02d081c0002c50040d4a0642c00041c2000c1000f00003405990307003680c0c12654010022080c1203181e00300107030603840030444200155002000e0382c468024103018076040a6580961001c0300c1d080400030107003420188540d0101c0c03070404000c0894402c1840504c80a080196a030354180041488910007041d0180138080f60601ca1100c1c040d901e5080c0410419091003941021042090900c00c1140c0b06400046042d044828174040c030762100403440b01100501142000540c454030041401c02d002c40d4002012410303a4421a81405000e4427682c21100e0b601031403140d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 896771339 1250 896770089 896770093
    0x20c06030f1b09040c0f09090603050a0224040311090c09030615011107120507090c08010e040501021303060b0405180706050c0726060f0705030a0e0a12032903 70
    0x100c1c0020b04099203158401540480c0941084034a9001030219510a2a01c40216104030702c1050503c0d40020060041d281c841810011f0500316115250b446002490003401070034a000d02d01c410b000244a404420310b0150b21865a0b2a26468080303c1b00303102681803401104d030303040030451180c1d4a005444603807a006d030041c04243c3d00c2e04240340e5595240301c00c05041c8901c07076040419086041c415035000c1d111118602050b103a541c50245d24100643d4001c800722464800c042d00903640c007a000c0ca0456000d21620601c03070f120f60410900910911740c440b000721195580000401a45801c9010004411902001155110100b94060341c10116120840341c01c1070b08180004d0303010308040e01d040e200081c11600c1540c2c40391858444010000d20740e60a000d80c000044010440c00c01c01151322510380202e040a40c24405030240c0725020203440f0a1400e40c4842c00184004001c000a8504d80d801503901c0c00d041011600c090000c00301c1094861484100407030303a43c10782c0300001541e100347c030700900 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 896772589 1250 896771339 896771341
    0x21c08010b121f150206010f0b03061210051303030f0c02070506130504050937060b121e010c090b0702040b0a1701021b0c010f180b030115020c06030f 66
    0xd000202d5a0b402081e4914400148458000b0f00b000c0300400c00c080c00b0407260040990000e4036002c1d2074580142d00c608155607007180d0510800402206407500404143c070700d0130882c000d1145003400d01040c004d2184e00c0502e041c0800c00058003140c0c3e22401c280c081c2c0c400b04456007540319000240c800342040740b00542c1c003a100c100494200390780104950070840c081c0c1b0803000d440e030001509a58081c1c5041c1525409042d4902d0f039a401121030a482214803a41c100c1c00749420072100c0c201e03007103040b0701030b2400c0e695201c00c0b100d980760700c0c003c040d01c40701e0030040d20100c030501404505412250b840c40c148641c40c0c41645214580110402c505461107800b15500f0b0108560030440030300384c56042c1036040400d080002980040e4450b10350018a4060009601c410003140d0b10b4404410411101030a98015a0b03c00c0403640c00814422041e8501d1400c10100d90041030450425041c91340b00510300e440c008000140101d25074107000c9500700079402d40d000010340400700441400181c8901c0140c0d000c0c40 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 896773839 1250 896772589 896772607
    0x30a0f0203072415080109060c091514040b0a0305010f122006040b0d0506130603020d060c020705120319020703080315040b060a0305040b0c0a0c11040609020406021c08010b 76
    0x600080181403100c0f4080395010f855080c00c60362990070b6102e40c085a441d003020343c04101050188030260b010600e410b00000b460504007160030b82c00c0d02c4814050110b41c41c22036041440b1401110041e10448890540d40c04050740001e000742000d1180c1c1814599182c004103100c0301c6150f1203409581c003d40b104101100d207880ca604819042d01101d0b030302c00b5081000180320345044001e4110300c00f0200c400206440c1520600140100280010b82d159140040034030043c0e80d60b01d0a000c0541d0429000143d00901c1041a854141250081c81d48112282e40e00102c1c8074001000304080d07030030031141e201c420340403040c241e98490050000034045c07081440002c80501486121002483c001171000c40c051004101040702e99001c00406000291a41d0802c401e01c03c00000e2290040103405189107003040490004102480c40b44004281584262402400b40c0c0c40c2c1d00100040c1110200855170b86135aa07102a556100303104a43d6140c40d181c0c000360f00010700510300c0504840c0c0fa000c89504e411400c0c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 896775089 1250 896773839 896773883
    0x702190f23120c0118240c0903060504020a030c120302151b0f0409051801050915070f020c0a0905100b04030807021c140c0f04050c070209040507090905030a0f020307 73
    0x140c040d01030716650b500908000c100d0240701c8140d50318081e4028030800300d1b841030181420740048800c0d0313400d1030601500c4000c055110700503108aa4008c140058180c8851002a500c55296030003c0c1180c0c40841010408503400500200c03054425021100b0074200192500e000682c221403030340321080c0755545d000d11101c40e80300804105909142032403030a03884544100490340140d8903540c0303418910403a9005000e0921549800400e81030081c8140d00c604004040318610003403141003004070010090f90024000c004100128030000c2c050307404661121725100042104454840305550003002c0012480410070864041d84d80001c20b9030314000703aa03024070058400b010b205c521559180f0b00e09102003010700782150811a0400050300390301c0c51180c100030318200f40554441c41503103040c040c0081d0030101d800315074956a051300d01d0905a601c1e4103003035044c1906584a02905420902d0410030000040002c2641024035110f904816075090304c100da0360300511100030803ca4a600d4030521003285 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 896776339 1250 896775089 896775097
    0x1707110114090c061309110703030f050f0106031a0916020c101e11060915060a05130e1c02010f0507211109040903050403050d11060a050702190f2312 66
    0x1c104444105d0907983c440c40c008a03011900c03a01d2a142c408101c040806905008903803040c080b01c0e90500490404070f0f00c82d0350008040c803a030020b050307427a0b0010b03071600b0040d10384280488008000c12114035149030645803800d10014281c00502030090704000628100743c603180000003c0d03413100341500301c80e0340640c07032034021585682c203200c40000070394242c080421947d0b1041d11010060024910b4502080c40b01d10406000d0b18403800388540107216030384640c00040e901c079402020208407680c1541da900e041400003400c0c4a04410004041c03404140c054201400c5504000c004100d81d54940034101ca55501c490900c24a4222006c0340036403801403500141044a007000c41d0034944081d040006d41142c0700c0c0e0504402141022600b0000c1c0802031049940d21106802d04a0203400c107600e0054807084010f246c950041d50342c00105071514400c000c2c42189003454441000e007450781d4100154032101c0744000302d40c202c1860b27070154126408200040c0040700600d0082801541072050703a186608 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 896777589 1250 896776339 896776357
    0x3130b041b06020f010f0e0a02060906071e2d0602030a1401081b0a0303020a150902181909120e0310150602060901060506070209071707110114090c06 66
    0x3107800c51040034001c0c00360403440101000e40090081c060307203054650964196072001c100c4a494040008004000452034444047e412a08030f555010345d80b0000e166409007a0000c0c020203480d6600c05101c409044002e04801e004100626940c1240740803022040c0000c040b44840122900c80380c0c1c001211a009550032040c5402c01003100c02d10401030900845090b840000c1541c0290f11074001c1d4600040081a202000c0d902c0171120342c01d40c3c80c040d55402b00b1440003004607140c2503241710704a8060340058403041d8000d0042c850020240b81007481810183c900e01003803c3c43c1c296400c0c4a800d5032140c00314855000810295640080300c0039141c101c90303280881d82501461680c458640c940d8421102075000c0e03451240d8007a0b041100c024a09240140046440e078540308041c00140d8502d026102c030654101c480c04010356500104442114038007011104045014061020341600400c804600c0c4d11600020403e10307200c0d80c50710414800942d5049210740090780d2038081c40c20305100821003d4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 896778839 1250 896777589 896777603
    0x30403020a0e041230020a09060809071208120118060506070c05130603020409080705010b0303030c040b0a1407060608580f080109020301030320120d090606050603130b04 75
    0xc1444030130017481103440d03000d041c442c1c0c1c0002e0341c1c12825000000600500102e240c680034514098042075500c030103034040c5084501d04642c4240c01c0044240840b0f0451402c041c0900d601d503503030303241084c0040509818062441c00c180c00422a4280102034038221390308288030038100d038a01814032002d6100c44c1c45801a007074440f440880541c40f02d019401400340b01d0300314566180c1182c14811301715400c45109070f1203608100140f040341814003045d60250360000c2405940c4d2a51030304140c2c0c0e690b808035030445018002003212402e00800d40d10500490b9101415100320155141410001244040c80c4c1e1004c0d244801c00e20440f41d5001c0102c001940b941c0001c11040d40e01c141e800e5110400c80010f80b0001440c10001c00a06588040d4140c01803007490404c1d4203650441c1d8001d4459141c0120403040740410b0300e025007044800308100d140e603041c480011a9104040c0c80d840300a051202c409803804c0b402e080c1c0002d02030500c00101c91141e0f4a200c1c000c07a415400d030359078500d2210003030000c0e02c003d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 896780089 1250 896778839 896778887
    0x3010644030f0304051002091f17010b0310360f060e100806040209241e09090c06161b06080a0506030d0806011107080f030403020a0e0412 61
    0x5508000400440b480300100c5070b1030349084c0c50510b161100198a0441450050090f0301c00b50300d803112520340480032118504511802c92500700c1d241c0f030083c610004a0b0400f50300014404c1c03010300084d80115101d0000c41142d2352140408010100b00724041c80382c000102c0392034201034940013281002c0484285012803076548a501f40f00c151010340c5c00c0206100c4008040c4261100c40400840c01000b54034003030319462401d40c000990304400100404e44400543c28040505d42d2644421408032074014000300200f042400071f4140482d02d01013290141e80a640891880d102c001254160380b0001000b882c50036022000d140b030580c031415400c54a4280c0c06e40102107580e49208190003a0145a50f02301c0980342940c404004e032100a03240c1806600200d521403c4545d209601540c000707002e0900c5036035100c80d8840b1b1468401c50b54868006801600f204030300c0d4080210050040b05d000301d6050140644600d55540d07044c00aa074010440440d400d101c0490a00800c0c1c107092030711030b070022440b00b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 896781339 1250 896780089 896780219
    0x60f06011106010308040501120209150901170c07081612090503010e030304050604261c11090a030204020a050c011503030f080709050907030608030c0a230303040f061b0806030106 79
    0x103030100310103065011500dc41ca120301940e010040700420044604c00c911541042c660032842071007010005029207100080303940c1507894900c00d42080c1e07a41f1644020320400c0800006000c1092402124070a500300a2003c039a00c00005c180c034011034101000c1c200300c1d111941c541c1441203821510b00300c00fa01244000a40c9004400603054400401103419044910b80d90494101c5130005a00145d1000c280f246004075251010b5040c15a641902c005030394a8148005840780e000f16003e203042503080146000403111032075408001c50703100c0e841c4e40c0c6040d59880e84c1a200f02800b00c0d14000040c1c3d000300d04128628240000740d41003c21350500194880d103030f8120314110b61103114100003c2e4404210001041030301520748203085151000c0b0504045a050025240d200150014060301e030326000103020301c15180c0c09441000c0c5402d110500760503d00307501810b129003c459540c881d510384603000504821580014100c0c203901480000304240204566041e80c05e2030078074a28840c080151661 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 896782589 1250 896781339 896781349
    0x421021c0c0f060501030501060501030603110906010315120c050f0603130f0b0f060906030f0c01030906140403211a0d0311060a0f0612020918010e060f06011106010308040501120209 80
    0x440b06002d00c1c40443d196042d41840381c00d582d50b5912050406103801400c10120b840210550310a030422149140d054843c40300403005132104031850005000c0c15580080c0002501b40c0c038400c650b100300206925599180100410503030312102882e004442000010640b10310041701101c000c0c45108000003504a030b8850a400700c80c2210032a08100402d01808018030f03041c00c0c0c0c1039010b001100180500b0348180c0074152640c01290105041c0345c1c1f01c05c43e410030441e06400880510181d5101104145400c2c10b004080ca8640000750340801d44000225040800038001c141c003214401c541450b980f08248140325003015000b01c00d404105000c402e880d03009100b4080300f0300600c110700c1d003c0b031608210440c1d4011606035900c00740109807410b483c100180c40b01e4007401c0d805601105051200f50340707a000c031405411000c0f010788481c010102081120414606030b0380c080c090a0360381b02c22003809103510070794410f000c0c0005828100103110404c640e40c80360340004080b103544040507040c42c0b50680421 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 896783839 1250 896782589 896782613
    0x1506040209060f13080615042004170a05010207031701060305101503150e0108120316030203090a080a050304110607050604021201061a0a080702030a05030c0a050705150421021c0c 79
    0x4007e0696a0310588140c3c0361a0055066001079a15410341e1401068500c20580c03140380300342000380b6aa41340021100d42c0c00d100d101701c81604400255903610710b5180040554036a041d08441340c2d0140700012035464844e1207654420070821030200915401d0138941000c0b64003c07105c1900301b549442662040d1040b401c0680c0080c41a002c0c409159410072040314280307403c80d03a0032803124400b80f0810109142491080029001d1402c00613900d1301c0c0c1c0c8042c14189400c5803805450010700203001d208480c1c0c8940254400c5014144031103400c034008041000c94401d0220140507030b8400c0001c1405480e24905120078000044000900d45540d004d4588020b800605410303d440340c04100c0300c0500f81c110780560b9001815102440c0b5207254440e0150050001030003440081c180030803a130f122503000d402101c0030281c100049919100940c0210052100100e50841e00130700841800144c0c041030428640b4098201c0d0007405240ca00142040c4003100c000400d5401c0182102610b400714040704611 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 896785089 1250 896783839 896783851
    0x20313150f0e150609061504061e110318060c0f0106030b06010c03091802280f05040b3001080a110306060109060f030f0203091506040209060f130806 66
    0x401e07120350198441d4121440300b1522410750300000800a02455035a060300d6003c042110114800d03220280402d040001aa41030085520000307004901550070400303a01500717041c168040c00b080040b40c001ca8040700c0d03203031208d00e1b254814084900440d034100c113810900306000d4021802d000410102038500301c4800080c0304580d654200900921240e12a9194014070a0030009840021641c0081c2071103054482c284041801400407603490015804849840041c204042440542c8242da18101403520a4610200b5101840b16465500560035a411039030841b55407424092a000001c0c00f086066a01100340303800f10341c041c42406862280180030348080001802104d202c0c3c9403d1101d4010880c800e4800c3c2c1c811010444030f40e80c000500020385800d80342c601c0c0b11524400c815000350a404181d41c11050000c0100f2503090030000f10941ca021050490041d25110007042c48200d21030960460b070404c07402c100713280001f03155030010251004243c0c24194016590401281000703810303544 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 896786339 1250 896785089 896785091
    0x21f0c15020a020c040506060a11010905030a1707090b181c06060f090b030d0e061b160b121f08070308090a0506032815082503120302031315 62
    0x6582c40b0341d0402c00519410010340d0108018100745001801a004141c5c40703800304801c000840c0c2101c1400c0d0000e0b640b60b0b504c0030032240c40384256103020340103807060300c10710119000d100c0004010700c0c0300704285000ca896880c8035910700101c10300d41031035118150a17425040b00c1411490100400c00c040442e59807402604c0c006002410000300d40652486580556000d03810319200c090302c0e58000c507086184044038100148c4000a14001c02d085010b006103501d9125000307560908020030115800c241452115010b110702520740e1045052800791540510802a03043c00140c00b0000104140254400c49050300c0e0181ea610005240b41500c590001c880b004408100500e031820080300f83d8001c0c2c10704031078650441c5030040c6200c0d0700444c1d01b15268a62154000030300014141940100d14501003900d104114603168100315a0b2003040e20030302201c072807402c00c0180c094403002e050a015070f40d2001e13041c000000071303003c110302a410103030506000c0c2000d4000c07400010b82e40e0b01c5c40540d8000e403401c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 896787589 1250 896786339 896786347
    0x90b04061503051e0d1e12090803150411130b0c0a0c0902130e0f0a0f11040618050906100315120f06050901021e0309031608040e060d021f0c1502 64
    0x307080b0705008110341d001d005d016100b0800c5070f46c1c46110120709140000c0e0314026102c40345006040015210401c805080d0b9440001400a188140020004020b00c151402d0081c0501408002e10b2485800d509006d1046c0401f0140507103400500104100b684000071034440035456102c040124201d54068050726500007804030710a194112440000c10070352495030254500446d1215140c8401890000c0d83e81c0c2d951001100c2c000c00e030341300e00124450f07004c087e07442e1a03c80c2d2016140382c003249a43d48070130a41c4200040c0c2c0c4d16165880501c140c0002d0000030542e101c0407000d0f0054807620b000c0422080e541c910124100400300d411030400340c040e82603928a0100c509060048960181250016074010440020039200b0112050f070f00007416800d0595903510504554114000c042800546210420041c01400035860150060710070131130201082c1d071240e42c10800c50402904000303411020a036440a00c6a80c1e8619a01f52a803139030812146441060303903450303015520b030b84094261301e6000c1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 896788839 1250 896787589 896787643
    0x1103090a05070501020a03120b031c09030201141e0a0c1a07030c110c010e01090504181209060c1e0f14190f061104030c08060712090b0406150305 64
    0x803082c0144028009040706080544004008450509180c505076071117100110f001d440030810344a403c4a40c56103101407803001000100780d17109134072003a170010740302c0c0340754400c9820504221004614102d4900380014011711170101c0c2600f0205000090014030300ca84d0003c512255031500451528060100d000c0c9030210015084440a212500400003c1d0303c01a6000d41c002502a000c0746003402c0000c041c2d101c901c01200e21515603000f86411030b041070700042e4006042840f80c080d0511810501c070f005c2012034811501c034001403182e0780024000400c82c1000c6221000c00c5034540c01c50303400207880038a26444004640501c950708132400300c0403c00c0b49212010a0041d205403403a141c45481200313195445403030122007480380141c425562050030000140840c402c880040d40d2109102e900503540e84509500c410044a041000c0388080400303003503a000310300c5040940d42e841800d500c541c0c0c8541e102c1d5401000d41c2d1512403250000f4a1010011501c00c00a0421421907203560030ba10304402 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 896790089 1250 896788839 896788843
    0x7110621071101050702060411040e030d09050c060f070f060906021606051305060606030a06180605030705090f0420061b010c0f0f05030a06240e1e12011103090a05 72
    0x81240b0741c03940d01d05014000388a42c046074154019400070400545201c6150001c2c00401c01504c2086441c030000a2000302d0031403d800c80118a401442542c0d1031880803001d0045611900318403051a0b2000c100c400001101c14034182d400700c0c041c90000400405540ea0304040ba80400c010700700011002c00d508040200314001c1e00d90001c400d0402e901e041440b0360360180d5400b0050201481544044006003900459501c1a0b004000044008500030200b0b260314005100341d0044034000e0060f44c0001c5014180003048500038600065540300c540d890362540741d940c4500c0000290044003031070280c401580d6600141030b00d4100000e110054004103c001e600312062142c00e0b20078400c5200c1210b040540007078180340700344c0d003c1c105580d803940c910a0880060205406c98610844101c440c80d051080e2070403003885d0018640c80300c1c02409081020444443c22100a0541050b03110001201509055459a6103008000700204545040c0c413413103002904111082041903024080c914148441 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 896791339 1250 896790089 896790107
    0xf050a080a0c06230f0318121812060103140105011505030114150a09051c020904020d1707031218020307120807020a08010b0307090c120c05120903090a0801020405060711062107 78
    0x181f0700040c030800120424072100c80c090907a40b20300b00d038600034030364801c4e0b112807404140007071840f0152040d0f0342c3c680ca04010580303904504141650319040000c54505241d841e01005040c49445070b9041da0310304008101000d1034240d0b0750303420810421500c1030418034400903010840c5141c49100d50f00381060103100c40c800c10b20350f02c1064078018041c008056118034441d10b4102e0b070150307080c070448a202e040103c2c6007051130315031117801200003035404281030744450100c00c0b11902c070a0500090707103a9141141020841040070354140c01c013542c10000c4146161001019901c41d0307014900b08501c40c1c0014520100303a038000290ba9460700845071a0745028412103028041a600400c84440c4880006002c0070f030300a03c0c0851342d175983c40e0400020380a1030940b0703801100115822a18600300d500b00d62260041c00e03451b4007511a015004c28900d606009a405640c4090402424040140c4404a41903001c40c1415007102082240f104950000c9061069107056481003001c039007000c5400410760300c2 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 896792589 1250 896791339 896791381
    0x1090c0e15090409081216081303021c0e0a0b0a09051008190e0a05010c020601060504061d011e050309060a2903030f040f050a080a0c06230f03 63
    0x10314003152101d2405110582d41c80042c2564000390344403603031410030114410003083c80d0319007070400c4c200308507c2c403640d9a10011075995950307400c840e1215226800741701d1440c10024090b8202041d50444040080c0510380550034178035114000380c08000200340a081c1c1c0e078000e1810b0620000c0c000c108141c00007410ba006080584010700d001200090007000d90601601c200281d41940101020340391864101a484135004419103410010900d4070900030310a030f07004103000d8004d031800000e0590092003981d088036800d440c0d048a200c12254502400c505403000703207050240490f2070084480700007502002259441e2204c07a6a8108010170034588600240485074071414180400451809031200c140c2e11181024110f070351818007030002c3e04602948142d401d1203070000c54001103041e42d13a59001c045810940f9110003071515003400031b8440e54400805004544104000c1003020310980d88241da45010810300c0f0b40e014020003180c5543e9100c21090a1440c0001c400c3c0404500c101c0c0b035510340f01c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 896793839 1250 896792589 896792599
    0x2060a08151c1b0b0313050a020418060b010e030c01030e01111209010e0309060a030b010320300610051e2a0601060c06110703210209030c0603061801090c0e 69
    0x50300d8203d800b0034902c0003c06410341b000240803220b04215041000a4100e64020b10034003649030826809405044800010f4400c641000c5185145500a1224401090028024003050050302005401412221907070441c02e40da03942c0c038008041d0f1404058134011020300c0d00c1c8141c0d03080500800f801e45011101040e05908200030741d041680d00c101c200c41e030101b200d050105032031203064016801080403d9800c0c0c90910004107090050071010014401100c0d840c42442450380d5103c14811007540100f4685141d01500c000f0071290b02d028200b6842e4410145401858042c00b10b101e14000303446e000a640081c50040b50004410544206040070403481c882c3d51040342d84400307030181e034910041c03250304d05009114000c04144040742d040411065444034085654902e13600c0d004000c1d000303051600806062114071000c0d09031050081314400780d030003402000c40c10314140400c00b066101a1856512488034040303803600320080500036000f4032100c1e80c0000d2840001001a05038208060346600c1342c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 896795089 1250 896793839 896793893
    0x72409020901090c020715050d0c020718051b1b0d030b04110702031e030409060b0d0c140f1c050403030e19240905070f1404050402060a08151c 63
    0x305a0005001b42180e150800402040b00b2103038040d00d0601c120030000d110315090200c41c0c01a9900082c03074074112100c4800040c1c031110302040c00811a80107640c25560039040c2c2d030a6080003650003020304620310049a5281c132102285403018a0100e01c2a05840400c0d00d6200035401c83c42c00e4480c0c22204124130540611f0721007658002601da16a80c5102c0b480c00028462245e0701c401e0420070345004c0c2158581c1080107035103512401b482c540054002c00b4800d030400800e81c04c9240b06d42172001180b201c00300410b0130000b40b00307064021504a25200c480703820881021000250311030003028000e500a4500203111890b1302901c50602d400c11802980305034101d21070200091198482c01d540030311804441c15980a03101a203005884000c2c030103030003845904004a0b01216215210048460071540d40d070000c2c01500505c001c0d01c00071103010354401d030203004031045180135155942d801001c0d0b001003110070417000c00140c01d00202c50f84240071050400006810414500c0041440341c20303000e000012 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 896796339 1250 896795089 896795111
    0x801030c0b090d0f03110a06020d0f0e0304030b07210b030d0f091205031209060a06120201090e070e121b0402030405060112050a0c0e22020307060507240902090109 72
    0x80c8164058004d00010790031001c04c0038144a496002c81191121059500404081c182030f0b010750403a5421000302840c01e0b80c42c101250042c440c036142c46014601850809285481e0b411403228020414403d10115201401c0101c2c010070350560303d01d001a000080d00c01c02d07103040c107250a448119107800e210500844846094106000320700f00d4000f24000c1a003d00103203032181c1980903031419030011007045c000b8800058000301e0901c0c4030b0500010200a03055440d400c010079818008000303400f00b10b550070180320b0900007541c4181d02c03418a0130142c45003d64a4040f822400100e0b02e030580c0c030b8005908050240e0090344903100010012103080d030a45c2460745031070303450f28018440d50103c110301c6842c00c4104102408020122a04140d60b0658265144a411064442204c5d00360b11800c849ca880002d0f807440c80c3c00381185a8001c0c0007070070b00d43c6c20240f00742c1b1250f111f12001c0d20000ca490081481c42140c2c201c070035002c20310f078030000320f80c0701110302c14040250410303040100003508101030042 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 896797589 1250 896796339 896796349
    0x51012172b050c0d1503080f0a170f0a0f02070c1e052b0302100221070c051b0612131406090309090c0702030105040507170c01020703110a05030604030801030c0b09 72
    0x114000703500b14001580501045d0310024001c46500c01049600302280e2071241c440e40c6000b8140e940020703210101d050803440c20f14807054108555810518541201180d0b00e100c19500400b0031030604400145000016110508110586c0e840110b9808202201c0c940c480300000011004200942d028030f84400a031101801150202072400d098108014400c0245403082000300801d054003841107550301c018008090340d0b84214242511818440404151007034410071424005a030070802030103840c0c3c02180603000c04d030f1100c0d03029a80304000f40080e440a42001800e5405010107080c0a40c26959510348081007035051510010160440d1080044030341c1c0100845403608021034415119590358807030325509000e00100a9055031030310003000204440042c4444c140c441c0089805c2c0b49070420910240c0d00d811031030200740160441c20003000000c1c070030041a81c5c8000000d10015650ba22a40070900d014070490b412b5001443d1000104144504000030318054403c1c9050189402c0781d41000c14 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 896798839 1250 896797589 896797597
    0x608010b0319020402090604120f021507082d0c060115090506250c06030b1302182709210304080304020f030f0f011509051012172b050c 60
    0x1e03002d90740006106e2030303a40c0c1d80401c8901511466440c07009640711402d01c211810200c010490107a200c1c0100840901e000c8000d40c0e15542c0e201a14516010480d06944003148800050302d00ca0141913482d0324600032444040c02c0b640398101d008268943c5013610010618100d03e154405008994a0512040e2156000c4400e42155001d00700ba50f0350460204082101c40c20300b0144c000340c1804000700c2e401313916411605280307404441003094035407903141c007204074031807000040325000ca81000710480d42400681c001492229102120320481503003038050301d425041b18000105e810914600700a03819044080044603010380c0e0550442c075060340c038280a0321014202034421141940506400d6500f0400c5032075000c0c0300d405840c003448040d030f5a213018000600d09101d040001d000c02282e40e2030781c5c0c41000e1194082074010a0514641a604811f410b02c2c036006544a00c00400000301c1090454000c00080c1d00380110401d07584e09500460114541c1c03030720201d6003d82010b040c00110500b5600f91 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 896800089 1250 896798839 896798843
    0x31c020d05031b1323090a0f091a040c0602010c14030405010209040f06060917061b07060510050916091e051c0506010e0106050d0b010905130608010b0319 68
    0x81d550381e40b56540d10342c09209030b51602442201000032103612494901034000e084500300d031007840d28644003042d9007100108481074550001e0050380061000c101d0f5400022a048095000040c0c4140c4c070f480b0680c02009410042019140c12001e1008001280399101c0013001c441c8000c004e0044c0140c0000c2c0b00c60000380341d0b6402004040081024040b00390f04a480994000b4010803c4a01540710000a04583d00c5098046001e40d0000103140d29000c48114040e152440a00f0096030303503030100c140440301040c900d0343d005010310800c03000540e103126040c0a1903078400b080e035483d07103080200000705000030400d030111081d480c101500c4a401c188440c040e140e0480d110544010141d49800070140994009a808901d001d9403050314643c3c0e2054800044c022000c1d245030341c1e256101000d07130038400c2c483c95000400401c8880802c980940c000790040c0c41c140340c000d0301076940d000001d8400501c550541e440070b80d1101c3c02c0080120034800c2507041c0c201503014100309203145400c00c0c0c4042d861080 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 896801339 1250 896800089 896800097
    0x12060103061104082a010c0308190213032001170402090702030c030d0207110604030c140406031401050f0703060f090f060801020316020c030601030c1e03020915031c020d 75
    0x10003502c00e61180c0940340603061035400c43c0c005416515034041140308040f4003003444075038040d8802a952203080107042c065059180c58481d41c80d0100b604450040d082400d1250070387c02c0c003990b10041c08001c03181004500413a0100c000c45c103c5094904908041840d00b414002102d071403164209240101660007501201ea55200e6036440b081682544640004c0d0141c0c2c0c00b00042140d0090301c0b6901a00416010300110ba22040f2444180101c0c0c0c4640d02002d051800d10940030401c90250612410104102400119609681c1d680d4100b460b241445003c2c01a510344041115082c4400090ba9100c201d9140c180241481d00400038820f0600c1d0180300201500e8006401c0b200d005a0040b100070b0010000855076032410745220403002c4070340a80100140102c2245142d40c0c90002500340c166030f002540c0715200b074503007001401c1300c640801483c4040c064480b40000541d50300207180d449180e000380400080d62103541003500703001d800207098900c0e200c02020189015800101800200100c0c20 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 896802589 1250 896801339 896801351
    0x31505060120010e0c0402120c070f0609060c0e04150501110102160c030c140901090207060b0a09060f0501170f071404030614090606181005090c0a09051206010306 72
    0x1200d180c40340039000403401c0c0704901c000300c0d42c480541c00b91300380203585002c0d40ca2540c8600d0070803003030303102e08600300d1550402c280115558901c010020000e2510a225000c202c07040f503501c10040d0b0703d50b0300c02034030150395401c10142d21a41060000c20b520380300322010401d08280040c03c9800f5a481c1c01541d041082d00055504296425811504040035071004918032420b00c1c903180e2a907460600045032040c0d8003481c0003d110300110400100d40c2001407140c885a0b08020340c8900942101800703a8080d5210707501c145882d2100107040010b020440d60201c0d80900348007818607082401d620140c100700d90b0030103280300b0003a240e02031034000a152842c00316a4031440d00c00c4922001c540410031041900040c00020004168040c409181071b10403078100d240d403020401038591804a4840350401000000021503190401040ba40b29801e110700c20115601c607070106040580440740248500300000e01d8000350741d00140c03140020001207840541e50384540c007559403901c0040c4070042541d9102c81d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 896803839 1250 896802589 896802601
    0x15100f030f021b0d080106023c060a06050d021e0303071203020d06062a05072102120c1c060f020703020a0b0115210609060b04080d0504031505 63
    0x24101040081e81c0c00429510b0707201010440c090562801d500152500c80d9249071105a80510310030342c100d40d03190700902913505024014500849440084003007888440580b001c210f010b124010714600482401060585800702103807048591a400c40e80c480c20702070140310011b96074407440c068a2000c010728540074200b680c0210380b450244120090843c0300c0005103007d9941e0544c003900c206894208203119040c0d550406031915052000e43e46800c5914494980141564015241c8118411000ca48044d030343d030310441d00040307046180d24024500310388981055191021000f80ba444502011302140c1c031001e0f0001e452201024903001940784c24840310300c203008583e0300060124a29540540d40c580d0203140094460b40e00d00801c4405540101c000b2071400b4072042040361440454603005035420716590581040c0b10fa0766100751501d92198000300c0d0f000803034020f440082c48800542a01c1da400c0008450811016080708000c010041c0030400c086a81103003110705000458400049a032614 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 896805089 1250 896803839 896803841
    0xc0607060603140d0311040e0103020603061f0207171c0f020c030a11030f0105072111040308040f0819060b0102031201081e03090d060b011b030203040e15100f03 71
    0x80e074009841c02600340700241010380042244c04482c41659004c02182c0a10026515540500d02401800c45072240040c401400c0c450b00031a0000e02c02800b40324291400069440c00d4420100070400503004a04200119655082d90120501903400035203a17480c500d24a00c000405200305e000308000f11820030025441c001e0050281d0700e1005010355000300c984d410305040b03052220380d2040c003070700c0b4a580d08070740c6590602c504ac2c00b4091a1b510b09076a649140d03a06c1c880c0522600395140340d41e80e035162125415110000030700003107216200300b41d15180b03000d41c46a104103842d8807656107500454000f503c203030720002c3c060030525402980001c1c21038213100101e1550056508a903500c070080c000200e071700d0078002a414410700d5501200c1c120040385c0d0300200d440f800781441c19074002d251007100500145164000030024070061400751410500800030b0000340c0315013034050f800360b000040c00780034044104841992000455004c0c1c07140ca10b1040100e002c000040941008001140000d000e0161103 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 896806339 1250 896805089 896805101
    0x4140910090e0303060f100c1709030a05010b09090708060106120f0c020a05070504060609051002150403090501080f0f181c080a0f05130807020402131401200c060706 73
    0x1c2990400a4108042c0d1840e40c030760055454510a02016003240c04174a02082e45078044030300b03076035660702550f1981c0d40c0604043c0180d042503c1104280f003a43d1958a080110080e0180a0740021500d00c14403410300c60440030180026059401580c0140400310000400d5130444102d031500b0034064206890000091100c540c2c08132485042101e00c40c140c2e640017408194550140044e100016a24010402110b4841c4141400319000601c10446807905a60340b25040d4100d0055807140c4000b4018800c6100084900302d011030b801070814041341d64001c03d21580141c070286000c5003070070302c2c1d0403440038620018030781980116010030842d0680307010702c040050982c074844100c0e4800d02c80700000d4801c44c4125051050b45203014045408203101d406080d000da282070544080240321500c42802e564000881071b60095020061f0300e1080381e2070500300380104084c145801b10b003007541c0001032080d1000302c40d406000b41840103100c1c06100c04038410201b03040480c0d065644010610700711b800707062 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 896807589 1250 896806339 896806349
    0x5130803010e040302010b153402150c030313050d091229090f010b030309010c12090b0304080405040506010c020109050f0114030c0318070614070f3504140910 70
    0x20002301c00560300c40c8000500310313440b003541c000c10440724004003090500c1421131040400c1d4110386864005400e107412030740d880703203545165146403905503044a840c0d98820380d07440019000620010301480000e1050004044851805241141c640b0303849005446164401034084d040484040003c0705900d00060301601082d49024483e1503e50907407901d8082c1c1d03606040c025424a140b4011925011040354100071050b111000c0750740c0c0382d0b00c480b0010307401860a441030041110000c605001d201d0013540c881c038441e01e1a1560b59003803c2c2444151180500400c0c140200113100c0f0700140c0e00003910350252842580c0c0e030b52101c0001c000403a0010401c0001001074500001400241c0b04190001c40c8100c140514980000b050795906540d17a0b8064401c8100103031f110f452000301d040029000f0070324580901d400c001481d01c540c80394038035010311440e0740c0d8004410301c00002c0b282c2c0883e2400b1076580c0300d4640031360415143c5090a0407501300c007109540326120440000742600501059640649 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 896808839 1250 896807589 896807599
    0x100f0206010614070218100e0915100e09010f110306011205100b07140c0102030403030f20030c0f010c3905030c071409160c0305210a05130803010e040302010b 70
    0x20710341c980842510388080d214005030405c851f0011500e02004001c16015590610052042588401c403510444001034002000706002040c002070340c1032240c1c44180214400307000000c00e0154024190b00719034a221640c94008818410860140c0c0c00c8503256480b009015800310309030340d0b0750650030803110060b0031a85502001041e003000f0300203440040d120349800081110100f480e6031005a941e4096844003c00090b0500c42c400c8a16105103036015049517401e850103050030250441c4ea0035500440e04210450340301c003400a00c0c0400034043c2298a071014108900c8485000701c10f4061020501c091074051061b1060881a021144550740b180503040801d403034a83c00001d814a45554440c07081c80c148091020a0316002d01d01440141e01900c0e5031144410388500030340040d40c2e100804a8150b0910405204480d82e0300705003072094901300c01c565042042440d20400b64400c80b4800303030100044054010341140091007a40c00c0320f041d1007010f0a04c08980c0c1e076070b181c202d0240543d00c20b1503403c4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 896810089 1250 896808839 896808859
    0x5030c01060303030203090f0601030f03180b0403060c020115080c0906131e0c05090f040513020a090e07091a191d0702060a0c140c03070606080c100f02060106140702 73
    0x1c0f5515a01541c0250400015214401c10200e0300d41da940d2000e003c05054401c5803014040001d01500c2c900c945940840300d0410410350b02c40180038140c1203640255005030300c51141c0a4403507428460f034403071283c040c0c00c1c908509062a0b0700c2940c0d0440800484e0152640340f001c01d42070345d540404480030380c80e4400182302e800c5064201c10061641004403d40c01414403001c0300d2100d00401c01d59214113005041040d007142414104800f51a018241d1140800708008540258a40200d850040c2c15030a8001c1010f110300b03140c2a141c0302d050b038002010f0b1458117104a075481f151003940c1483d82405c980440d207841190070f440c00f850409901640c03066008082e902c4103901d1440880b84108515000d9404641d075034240403055030403a823281c0c400121040b2502030741e000c046004c0d005014a50b81140d042804958440045440a8002080d5070340084444030251901c0c80310008182d0003460090310b86151198041d680c2c80043c02031100340070200e407100e8801240c070001c0e00c4103544c00512920b01 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 896811339 1250 896810089 896810093
    0x10b0a11070609030515191a1005041706060607081e040f05100809060f07140301170f0a0c0e06010c0821010906030c0e040203010608070e090601240c05030c010603 72
    0x1c0b505075110403103050250038076610250141e14162481380344404210081101c0401c4a080103000344a08e581050040c0400480c207038640c280f420172441c095440f00380e95541130001d000b10002880c9a1200aa80040d080280a880e2242a103002c00d0744411240d0301c2e00040044030501c1200b20345959441c0380e01142c0050707100302c6040400b04a560a0301d840350b002c42606401ca80d90342c002c90b00c0e110f050f840340d4003041e01d50b9001c52045600454138540b050088100f5000100030703604c01c2c0e0000c14010341c004d00040701a43c0078056240f0003200341004201c00100d541d40e40c0b002580c140b00340c055180c110300020b281079008190801203e80d00c4428540d641d1000003055210820351801c58600f0a000000801c130001e95204500c1500d030000028858a8500901950244402407080303030555280c0d500060250001c200003006003115022081407072812036a00b5140c120164841039200d0800c1c00c3c43c14111071251003024607030303c452801c01591142070806619600ca42d62b07101045600e42480042 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 896812589 1250 896811339 896811347
    0x150206010e0a0203011412070914220203280f062c03090d0f17040305010b1906321305060a020309060c0a0807060b0910030308010b0a110706 62
    0x816904840c0c07031a5103940701c09410500302d0000740036002540401454680c9986020403d514624100404940c5096120a148415582c1c0021035544010344803041c000d4804103812003e403042044043c80b80c000b0040e4002950381c000e1408034038189040f00a1022a01030002e031a000f81c85d4002c403003030b0b0b00201646040740041c86901b18200c14401880091a02c0054a42d00c041030740540310000c6040030318050801034114141d41303048403403510318199180010310802c3d0007091803041d030341c485450780c8c9581001429202160011032042d2a000c10f500d42035020242c0c400150342052030284000c002c07035034111021031040c0060140c2480c0d0039401142544110004028400740707a0480707880c0c1680c0e82d0601aa074020b0036082e034090713003080c03000a4040c10044007800010014000f2201d0301e2074140c036502541d50045030262200b5460b20481c0c81c203428244101d44c0c112a400b100c41d120507103107450041c90140c0c1030203200c41925000a0780c585252088480703048040004040e81d080c04e07030303420001d4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 896813839 1250 896812589 896812591
    0x3090d0f020f0315190f0c0503011802030c040603020c010b0d11030c03011109010309021f050301060e0d11040e030904050c030a200f0a0c0b070903051006080307060e07150206 77
    0x902c90400d41c1c01d00c02c21800c002c07500b0841012090000c01c81c40d16029414091405104400f55445075244001c800d0040355006060b407104194495503a0380d410010350242e04941003540da800540100705100903030742404111400c6550b5894016101c0481d0501e9502400128901c02d90009030221003900784120a4469829901c0840455144050304001d00d800d952060703401c0500d0150600c0802a10b500030340000c00b45901c01401a003820310042002c0701d500203003e52200c005103010005100c1c0b00c1d004501440c2c5024119801002d802d03c1c0d07594000400f420220b0f030342c010f6850300c604140d13452040040d2228140c00403c18001458484854070268004503041c000050400403600d40040d46490300541c89080c01842e03a180501080409201e03920600300002088032034161580410320042040e405000d07550788200e5218510b0414610313240340180907041003454084200850b15001080f1401c1c5540040f012408041684c006810074401da03102c0d0203003400045412115990105140d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 896815089 1250 896813839 896813843
    0x51204150b03010b09130305090909060f0105010c05030a1d030307030507052401060503100306060b1305120d03361e0210110c0a0f050909011503080c03090d0f 70
    0x7003250310304203002c02d42680c03600210300341c00a009402003200002c0100520320380764060b0401c01e00c2c0c035a204000c251a03400492b102c0c0002d40054003800300405078015103500404092030151603840d8903460b030b15224452801d056041c03048003c001c00510a08071711198180708000e054a440799928100030f00786901001d81100d541c042c0fa0110340184241036000c01d466030a8215545c1c2d585e081035010355481e40040d0600c00303d0b002510000000511302c0c028040038003404203506071615641c002581003424aa00440c0c46103001040e131545441000500365826402454085410120349007520051802d24614145640c500803400311007030001c00e00c09801d070784181148070000038036010506100d8100132009600c10020303d4000e062503c82d48003561140e40c00300036250340c00c40c6c4200003010b001c00c1c3d41c0281c4024606000801892400d02c01c40b035401114100244a40b100b01000e42140446902008103505404511003803030b150308006176403000b10f0140400055180d10304003002810441241 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 896816339 1250 896815089 896815091
    0x30c0c420405061611010f09120f2a02031b15040f030209070201150e1e01050d02060703140403030e0a0501170c03090a08040b07050609060415020a05120415 69
    0x99405480c0c24884551155401c10080c207143e8039040407071000f010300140c0c490200320b0f001c50409602d490a1140840c00d03540d944000481c6c4a091400c04082c014010300c4c0c0381400700c1034a054a01a400040c91001820007000b0030780c1160091100c1c50040c40f036a0000782d098800c00e07000b02a000e1042240c0403031610f040700c6c0382c00ca140900c0c0074410940300f14000c010802149010810040c14030392011a045400c038000404d8150341a15829030703040c034a6009030a9058080140031400040d106001460307400c50311100c100c0c0d814803000c540e001540001c028010b450008042c1c0c240340c422504c136a500c4000482d00b9644a599040040041c045002c0f0f140c0b0032075020100141542c0280c5500000c0801c500541ca42c50741da100d01e54900d50401005040d8600a000b03030301d00081c0d1400010009010038002075a25002c15050161401c140100b108009520243c2031002103080210203020b000078841015a6819030b464003140e0754000e0b1030107600c841840034180000c0020010545504400c2c10300 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 896817589 1250 896816339 896816443
    0x4110102160b2511060a030204081504120c020315060d05190c2304050a0b10080f070305011d0405070f0602030c0616123b0d020304030206030c0c 64
    0xf098a12640005800070014920b0300c0c4680c10f242084009083e0304015400c0050405603284811414000600c249040c204d10900403c020880c100008031032400681c0f4100c00402402d9011035070f52504010f980300f105011400060725079032510043c0c8542070340035042d507400041c59030040140b240300d80c1003101c0d4501c00c90f1022600d582401415114a2140b60403c0301114102c0c0903c001014081c01c80303c2d2141c0c9030922018281c40341501007202d40d07401d5960254a06e0b00c8000b0302440580504090101814680100f0800507100c00203103902c0600c48260b036050701c40c3d25040746000746640c82945a1101d48500080b0160003001900c04400508195115540c80401a0240c510103040302c80104603201d800c0c076512000e40c0c1c800c1e2601c030029058191300c482c1d018120011000305d203401000c610004501ca501c4444240302610f00500280003c5051505590006a5601000b402c1d4207143d00040f80700d042425003001902000343c0320061401e8408100008010405180070a44000a0920f1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 896818839 1250 896817589 896817637
    0x92e0f0207090c0f0804030e030102031303200705360f181c030b090c031603060b0706020c15010801022106060412020604181a060702010804110102160b 67
    0x2010b6408020142e5640005a64070540b0a6845e07a5000d0010307020480c44808100141c4c03000d00c0258010000d90440f14160440c070b02c0d0090200c1c0c224005032520310322104240c4031100000510000362001240c207000403510705040c198120040d41440c10f075038003443d0f108060014480700310a020310460240388103281c0d104101801045001e10340f64206610524400303859001080d0b10f0198103100e440c012900400c2c80c800203100260075205116142c5000083c0307d0a00e005082402c024811820300b413201d0b61034000b234072840780101903007c1d00164001a002900b48024041d00d0380110000002400d07035611681c21034005c0d0040b0842c003200300040c41c0d0722469220700301c221030b00c43d031001011246007508040240700410300c0c0b034100b00d0f044007050001203049407000c18001c100c641032000001d036101c24460096050b140e4000701d64080d040070004500580d038090042c1e41d110303401c111600c10001035131004030b20307040303185814120000300381d0300c04126142001c0c002c020f000b00320191000d0003405c2c8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 896820089 1250 896818839 896818841
    0x1c0203191a09040803130b0a0507021501140603040804030b1e06010903111003110c0c03100603020d0f03020f03070f200105041e05040603060203100b030c092e0f020709 74
    0x55641030342e01c402041c00240014042e500151741c02101024080c00d5070140baa500040790f5400e07148103a18545400c2000755045e0304004640c1e035000250300480c0e45515082464541c10442d540f0300d4010341000000be07041c84182001c03207004641c40b1a1a030b880d450003580c900d0102c20f14156090906001a0110b0555071040e01e1070000d80750012411075401c4040da041104002c61a5900c00505840d0540c0c000f010300c04802401c041e80000b401703050000705c03c101305814075619941120145192840c1480907031201403244103540da00a885a401000500b0240d02d07000142d5108010b61000143d080d00300004011440501842034807520190000c0403148503500144440c0107001604c14403003004030b006405407101c1d000c810040d9200300035841c0c0002c20140e5446400c151400354000040c08030f95404d08200100070480300c1415410750410b0705a0256074850f02da0110321071424408080200052110710030055400501b40b82200004a98050245030071b42c040c1d44054012800001140451 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 896821339 1250 896820089 896820131
    0xe130b06040e030a0c2a06020d030c0f030207031e0306080c0625060905060403080117060c18010509042c0d05040522050a20040302090c1c020319 64
    0x101e402550800a0601d022503660514078010b50703000454060300021225500c000c050303564546c1c2c540700217443c00d200010f440d0074041035510007018a0f1400102906a0100d5a4005c441c905c0ca00541e407640c507400c080360f030428209514212461441240c04145425621886c101c580c40020b8804504404081200c203000302d201d5050808108a2401240e4402d105540c5249206074400614800d180d203542d481c24004640c01c4000c98242d10041c0b00b9142d4550003662058201307801011039203454448020b0601a20045500800c0d01310412512a8042c1c1c007521618440500100b00180c01803003091455011880e404610003801400300b210b494010a0a2074440038a4031003a01e494030340001d02400d2100c40d50f000c16140c06044003000341c10041c0c000c19000fa40807650100300c0540ca0360413032040e19a01c540202d0404001c200410068841014659104001c5000c10380c803a080381d6001c0408080030040c02000c5403001007003160681840040c1208000740d503100300480030a44a440c0100d0350 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 896822589 1250 896821339 896821361
    0x10203010b030609180106031104051503251a0a0f081506070f080d06060f09060207090e0a0f0c140604050f0f01180305071a03071704030302040e130b0604 68
    0x10400190a42406559540c00c18131061741c00c101008948151821902e4681085510400c003c0c400c00c0c162400d030151640000c11039a0113141e0b0310303d040001e5500c44481140c0000ba1007105910f860080038408080e00400d407000d43d00b02e03540d01c40f0000407071782d81c800d030002c201249400c4a500c1415210340740b25031040504444004008620000308003281d0480e2004540c83c0203041078010005403c40042c1003004541c04012900e00d00300007000d05148028040c03081040b4500000304641c544c00600d6004844881600044104402c14103500b4400c05640150100702c003400444e04005004040c041182c14450f0354480222038901041f105100303504c18151b002d038002c01018080d142c000c5080526100c14107141c0e200c00501385440c48542d5583e48250750326041540c0400161415140441d404002c4c0c0a40302c4c51031800303290141c00c18071845142101ca561600000d02054001e5044034040c0c2046109961140303404480e070101a04400340840c5c41900600100301c0e1410103005800c08a8 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 896823839 1250 896822589 896822609
    0xa080f03091f050304062a11010605011b0b101505120a05240102010b090c070506010e10061b0203030d020901031505030c0f2101050702061305062805090102040501090801020301 78
    0x40c503292074543c040c211022418100b0300c18090301c400303201e4040007c0d00d130304000f42d142c1410b0345401c111560f003100c909a02c00c0e818402c0c048000301168114100342603074160f11440c0f00003140c6a2038042d080c0f460090304001c1d0201c416400381c507801608030317001d0980001070600404082d60b4056944003916015a00b2405090580300c4040b081c0e6030400075016810b4040c03000150348001c0c000001c5d0402c1c1d0542d203004070868000b0b0031000b40f200c2840031178054032007249202c0440c02c084a4480704103d107482544c0130041c1d83e01030046032040340386644e28540e4004003103a80b00d50540d00154000c3d0300c10b14019002c40d181c551081040481400c0100031503c005024000d660a41e90900503080c0c01500c01a40c0f11228118a54160120146c20300080c202540000360510740090701a1030010003818100c1d6086440c0780c40c0e0001900001d0142e0b10585004c01c3c0310401101341e60042000800d02c1e0700f444240d00300700c100082810154091b104860302641c4190070705540d040c119080b0310082c0500c080755 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 896825089 1250 896823839 896823841
    0xc2d060528021e1c09151b0f03090b030a02030a051609090b03011503060b031603120e12060a151508011415070302010605010e0907080f060a080f03091f0503 69
    0x7041e02440e0035228500c01c442924107071100d890401c50b44c904541c10003400b140403074205000445d0b82c500400318000f8a03060208203404060186286880071001c001c180c410300ca0703c3e00c130406d0303c140b40b60f4000b807441c044880d4036400d11251080c00fa400448001d40b03410700c1e000008001d19141061840b100321140ca440c40321500b4004d103d4090182c420b03480e50190348a01e81f07900b069020305004401107002c1c1500240417403042c01003509088105d040d10b00b601000d04810300201d01190068030031094603051007610203101740d0110784200d0b89415040614058041000308400403034214000b00340c0701039511040e40e51140110000c0c00855404000007442d4900140f01c0080e1060741801007400041640c91100419101c0044950003080d0450060351680c0b410401544c002c0c1001e940900e088a40311818500f0460003058420020650746000b4007400111b980f58a80102c03460180241409440c030000300c00c0d0382650b82c0c0d0310111245009a50310702e60b12400010524411030300c82010f40d00c1901d5 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 896826339 1250 896825089 896825113
    0xf090319031b020a0f0e152b033c020303090309010804050f0f0d031b050703030c031401060c170406080601081b0a0c02010216030c2d06052802 63
    0x182d00002c0d107040781c0000041d000814034800901000c0010410500c0308081c1d450001c038000260b10000300005c2c0249903881d1a01c190014034a820440104400c030f001e0344854240c20300b151007200c0c10190550f007060301006020f5442c3d002400040500d42000391103241906180308030703660b100446641482c0d42040c0405205584144000313500f1901030030481d00340c511200402410584c4052294250f64000061920b2264041c001c524143c41c03980b4102000e002c0d000009000ea00c10b00d04c00070b04059680c085507455a0203544011610354007488004d040d9030b1074800183c0a28070302001075070352820400320104444524800c480a40c1c110750f0321041c0d2511110700540d03200c1d402030710f0794400d07006000c48039008207038440c0030302880b800950f00c8008210950001a0800c2c2140982400820182030107102051000d00003008a0f5803041b50b002c4a046919090f050002038480041021018810000b46259011016280801000c40b00050180000c210b0441e00e04403001808090303085010701d081 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 896827589 1250 896826339 896826377
    0x4150f0e0f01050904140f091c080c160602040f050607210c120f080f0f0c091207030f060b0603160305070306030219080d0201020901051801030e030f09031903 70
    0x101e03203041c100079007040040030010301583e01e480b0f9600415526003041001685112284a0308007149074060054208400100b05096210706c04007000c0c0000d174400708840d085058216100e45e071203581040c1c54104e080c03915902035802072085015014181c180890f1360b140880480b2444d0f41e100302c85040038142e05e2500784c411006c1c0380d03600b0103005c3d0600802c004904a1340015031010695528001345404c45080980340e0500035040c2450300214504003d10207010294564209500d0355401d40c0300c2104a00141801c40940d0301d007603050246807000020817620100c24a40548100c07010b1082d01603440601440f40822a0080182d2003441242e1500038001d41c00b09801c01ca082ca00410f0071926500400c411028100300c28041400c00e041c10030000c8030a0145400c0941c083c4000e615042c0344400003401c5000e80c403021042003d1a90b10f032101603000f503100e04103105910042d070b61a20040201084150003007850030f4083e0248640842c5111440da2a8801ba558551503a03c80e202c10740d1024a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 896828839 1250 896827589 896827609
    0x1c060f062304060506040b04080607050a0f140c100501091d12130f170d09051e271006020705010804030818030c0115120b190f02070804150f0e 63
    0x1d900a42e0351035000c503043d2521402800548224441e0a64541c904a034440c5808401003518040010074005d0200e10380d0301840419500b10303941307030003004409681d12070309140c420941c500215204402108101e2503894101c24100c40100900300060b020300d00c1c0c180803040302403070344081d00d4000086510f0f10310700e00c00103080c41d4074101e0a0b4200198584d000851481c4080c1c224615081d01000c1086070318004103c5111590001e160a0b01064501030100d414028210340c4e030115084090194000e80d11342c4025a01a0608101ca15020309000c0b6000c180c40300b030a4a064003119580c640114500b400020b40c00c0c22500180c2d64000d2075a1103490882c0c40c42c6000c0c0111200c11f8440c020710b401c1c03030000c0025001c00e840b407000000d4184082c141d03451040d0b8035a40030200c24003951451601107001e15003540d0f8000350120946034041b0728906014010560710401c0791010784081000c10034001001c02070001d95626105030035142c1d80c02002a5401102003804100040f001300103100c0300c0c04c00c00c04c56 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 896830089 1250 896828839 896828909
    0xf0f0e031e03100807031103101e180507031b0803070507170a020405070f03150305030a030e0a140303190203060a05061b030409090b160c020108060d021c060f06 71
    0x3d0095103440e42e04007428041d0aa20a444118001d03100418600d010301c102a03d944082c0b0040103294590404206a80719007008055120354601c0b11400800c0311000000d1034a91000644411980301d203856032100312450b1414924114405004c80c00c0c81c0d000048441c015003100081850910b080d0180c0b030924000d01c800342e11401200c142c40010f89880c081d46004601ca5180e5440380381c091100142280c088012544850a61000407c04134401004440701550103190225540c010800a03074541400b10000800c0007040e031f00190725190010003e140965070072411410040c48100246059002c161141c1d0b510480c0041d04101c1b61900d40010f140c040c40319032480a224440c1e8810505542107540320000c1a92650650003c100c4000400c80c7d00c030085107800e911000344010010034030520f00c0c03402410b010300c09000c1003c030381c0d40d8240d031520290700808569011803204070b80c1f40000c0844500312101400d10425540b03100140c0190000c0e15500036150665012131508220405104088 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 896831339 1250 896830089 896830111
    0x1b04090c030605040b0402130e27010b130b030606131d01020d0b0d030f0e0402040e0c0703173c011d060f01170907090f0f0e031e03 58
    0x5442510380541280d1a0903a180000c0341450401440141c40040c13a0701031095104010088415589030031040950301440e121a5030b42e43c031030200c45214040c143d002150200780250844180405400501c003005090720741d002d40800c802d0004040c0e840945917030b0f6040d00a000000d0407810162029041e0308120380b0701181d400100c001a25150303040d17608800081e500001c052041c1c412600413800c85680540310701031200d00a450003403910401c0000c4c2020400c16028580e0a542c0b0340d015240600303581c840000d05810301f40c4240c4025488035008038041044452885218540480124416a000381c220105000c8500c2c80c04404510315a10890003020210421807403513114504902814601a0083e4050f2241030102c2120a0040c0b1044c8641400341c2c4100842e640040450440c02c1c460a5401c503d071111074800e41003103800d800080c1c2035440c20030700344108c001c0c03500402c10102d60748a0411126103980d010a44a11692400701d045003d1000d1040442d80302000440d800209502 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 896832589 1250 896831339 896831347
    0x501240e0405130314030103050c011b0203060115180b190201150e01081b0a050d051c081006030504020d080c070e04030210060b090f060d0209040207050f0c06121b 72
    0x7904481060f150035880d5258400d05408254218107402840c1d0f0917450381c10300707540c91640d039107507a29124000f080c10051415044000c0d4000c1040d0786a01d00c0e8002d055440568460008084030304c180303030401c07000408010b216890300302c180d00003506594520411602e040d41904034109200f520104070030031590703550f00d041a56180c11010749c010f4207010707070400207a501d009151450000305440742e205560101580001c903a0310343c0d081a0841d04252012180300d4030500317260f4100340300b05800c00b5a0034480d01180d24000e9001000900c10031100514204035619001c0c11012100c003154000c1d049072001a0080c0802c60550240c0a001c52005c2100d0655403600035600c001002541c1c00c50250340860100900040680200000f400812170b00c00d01300706034040052041910b43c0c1c82036000311000110412a19400d4045a0348281c0107402999140320b90300c1d165954801d040102c010500411090320442d1404000b00c03410407060300542c6e280d5803030325007103100208412983e1032880c1c80100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 896833839 1250 896832589 896832617
    0x4050c0405130f0e1527151b090603040206181e0a140609010f18062d0804060f0f14071106270309030102040b0d0609050124 55
    0x90500404041c82d0340441d448545100750b02c02e842c0a98030810043d0429250303890000c4100510550100ba1410303540040194044558040300b4060540c64a42c0a42000030800f160500010b9000d61505500c0f040303c001c81002890a034018041800d0b8001400c02c041000b40c07500c500a005010f601a44450032035200d8030001d10320049001c140d0003000320925480c800c901d000c0c01050010703c0c1c08140307000d92480e00c00015209104800c184d80c10312129141d0010410701c00d130050300c6100b801e0801e49510755150072018004100c005e240000481090b030700104003601e00100035540400c50340f94100e080e122139480c11301078010b690307003800362035501c0c2d0003201003401c10b00801002d504407190341c09282c02c00000051a013989001507a840341e0100d030034001589030000507207002c0c0782d0300000c0343c0444564104441c110701c00e10320026415030002c174001c904091044000d0540801c00c20041004c40c1e0355101e0305003070b50030900c2180b682062800c0b1440701850ba00ca800000d00b0b04500d13220540140b46 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 896835089 1250 896833839 896833849
    0x5041a07140f060a0e03030610030f0b04060f050a08120a3b12011a01180506120115110d03020a022a030d0c0b070309030903050106030605100506070c030204050c0405 73
    0x11999140b19a4000400d0061081381c0c1d1261701d034a0220500954514508440444c030b92840030f9282808041c0d44032404078101c0380780d41c040385040000400a20806984080c090b000110600500e407168904523000030303c40400068140050001c021003506007811540d0580c4d2160911009150b804040115491411180e901103c0d0070710782501042c00c210f0754003051000c41c1905040b90405032385003e05405003d2404031182c0c445032401d03c1c0080b82004c52040e0145000c002c0d81c80039800c0000410b6001c508482c03503034900e050310b8040041e0801140c3c804012900700c01c0910f2182040e40101802c200818404d4004196072034440c01101c044602c1d40d042e0136400518031b018801e12944404603002c0c0c80c83c0902c1b2200c504401c81c41c1900f00403003a51181e034041d040190044040c141d64840c4041058003400c0b41300000c44c0c00000030014150b8908000010307240c2250a00300c510700610300492513142c01c4099403001504082c60410203811a82800014400604443c0b03040400f03200002c0d00350b0b14 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 896836339 1250 896835089 896835103
    0x20c0a1e170303070e030c031e1f0504030e03061018061e0906090b1302030601090e0906061011030304060e2d07050609030d0e010e131b05041a0714 65
    0x800d070085a42e8a0054001080c1342c1c003151003603100740c11070004200c1079036000940e00009041103c14400000044400302d241024146070095070301030f40181004404026400340d403169019480740c411000b43d4804061311180221181c50130644901024451030a0240c02075009070800341e0001452900d40007d00002151071a0100746011400b205001424140c0500c00040c007010809011010f10000041d0200d01c90950014600ba40440010130980c4070f01d01100042484500c2c1c030845003070001d2541e49030310045030b0050240006004411103244110321104032064920007071800c43e165952900301425105918507070b14400c07c03d0b08c44662001145913010b080b03401d0415900c10003040c205a0500c00c00d0750096100c0c82c0180315000058030045400021103070307149041c210000b04580140c4400309004203403038008a503100c0d0030b04c0381c02c0300b17621403000c00260b244483c2031141d0b4004100e52510490184802c00c0110180400300032541802400c03049200700c88600c401b240d031402803441c24032 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 896837589 1250 896836339 896836379
    0xc060209040e031e030709060c110a060809121e0304050715021006050f0f090a1103010b0403053c0f010504050c120c101202130e07030c020c0a1e 64
    0x80000c0c01004c0341205102442d1a0b842c050746242145800319020300100b09511a40041c40042111041041808041f40f045410010421860f2540b510001400c12104441104551196064101703c00d07c1382c1040e16002481442c000031802c0c0918082d502d580c2000c3c1c0202c41030b12814401207001c07510b0050345295131070941e0041031569040e14100301687c00ba6408180120790311100e200d096254920031541141e02640e0360304458035088000001444411250745040b403000c00085507102007200200704980c020000c443d0301a50700f480d0011910f1070415079569441103c9150300c5642252501e070f0521160500c15241e04a010001c102c1c20750320111404c44036500a2400322a0358038049049004056254000b4502444c0c04408160345c00700e04040c1c10148042d01403c1c3c13103c0400c41e011520000c03101d0051000103640d500003003501c581c05a4000000c03034201100c49000030300c0083e014510b084010240307070f0418903007044c81141a10400b1990b5000944000100d42c080d441041180780d14 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 896838839 1250 896837589 896837593
    0x3090219030311071e120812070207180203070801090c03090615030b0c04060914220e061f0b0d2301030210140a031d010c170109090c060c060209040e 66
    0x10003001c0013400c0142d40d402c14443c5420312007001005c3c1c4103480c1e860341610603061308032507a5205814511070764018a41c40b4885000b0b40c05c200b00000d9030225001040b0307540c1e2121103881001c54402c4070164041103c0000000f204c200040003060011b40004c1031884642c10700081050641d202c102c140c411002c005591304c0c001c1c1e0f20030001c000b04480002da20550b08001c03d4101420410018500d4407a03120740b4028400f1501003014035a1620000340007046160562200f40d0039031404480940401480c9403d00d005150011b80840c2800d00c040340319008541d2280310150a2040345109900a00581e05038143d40e1000459200d802648518401841c03440452056244d807042102e42c2c402c4004100400c500c28041c4010000d00e54103403044640142000701e0105404c1701002c011040d031501c100d0242d824031689101c035913006500e44c02e08444ca44000d045580c1c96410003070a90328488001480710000c00020864548502000d10034280703d44009494080c0100000d1f040c1c0303092850490030381e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 896840089 1250 896838839 896838857
    0x303411010f0501150207080d0302070203011407182c0903120f040c0b12160c20040b030313060c0807240c030509060c220902030108120301050d03030902190303 70
    0x8404062151318012503817009102040c10000c030307140c543d9501c010107424541c0114070700046603020740042e1401d04402c00c44856514103002c00a14a81d0002205036865001c000c000c00d04030800262501c0303085110400c801400c1102c5100303404c0110090014120f408144103607044101110003090213410000080d03410b500b400d0805240e1400941e1041811020802c01c05800d070a11252103540f0440141081c080c90300503c81c15168942606002800c00c114525001001c044204807103011010a4808201d18840d001c1456964071079140050910050003a040003514030034071503140704034410740c95581004465030b12a00301250340000903070400d0500c0c0c05c041c5102c0c0d540c4036454039491546410f02c100e08042050544504001d000721800480001c2c0e102c050314500e000305142d407001030f1082d407407a6a4803a00c1400a410038007841c0360324000c0401d070401c107480007025079059a800400c04c060a8810355800e030300400581b00e00300e8000c4010020104c5590005505800850003511503c0320 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 896841339 1250 896840089 896840099
    0x6050a09080a12020f0c0913020103020903100204140d1505070c0c0b303c090d08100e0a111c150f120602303411010f0501 54
    0x44c1440c20045c0203a40c4d101128818855a4014074075070000d01f0725007000524121800120083e1066110f4143c041c1300d01d4031205230358030455005208072080c41302d112481292450400c20507161001020742482080c14101658a52550250760800c029081880c1402e109503614950702605520030383c4a60302c0030071f88520a0f954981003115070307541c0031000f440f580f0116007150400c1d240030300780e5a48009002064003044480c0021224500170300c807a180c103501505003d00700c4100c0c00b1620080c0034000c040c1c4110507140558032281c090b06061203200200c86c140080400c0460f4018440f80c40c140e240d8456652201c60321005106a001d00500030020440c02c2405c441501d448511162110717a03084020460f0b1030003c0c141c401903030469010040c940015041c038030041e0149940c050242411901026224910481015000c08100405558940e5110612420692000c4861001c810034040700c1e80e120032110b02007690f041e00e60400c0ba55108402c00c0b290b0845250305183c0e202c003030382d42006001c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 896842589 1250 896841339 896841343
    0x15010e01060306080312060a05120303040c140112050402030307200111030a0c0602070f0602040f0303080901060e0609060a0801180201020c100e0904080f030c0d0e070f06050a09080a1202 82
    0x405031455080502080c0c4c40d04101a40d070703201d85040010f8405c0c8010100c0c41c00d03a200d103c600c00406000b000c1c8600c2c6a001d4407441c1d00c075402520200c50b40000c203040026200001005800e60030f070161900c220808600f16143c0c00f80030010401c0342e240c0003c010040029900c11111442409044485815008500009884040c00001d2182d0f00e50003849452031590340107000c8600664080800f50300c903802031510000300056a000200128008900802c02091403502c03c0122401f981d185100c60303d03040b010324202d441601480c40501000c9000510074100019015080303035016103c0130309039a0f182480c41c02c49041840e0789050034261601369007903690401c11460034110441d405d50004042410140c0000642c0901c28000c10710741c00014284400704056070201446110451b13920326002c2020090781e40840320818445280481c450502240058807005540785209142c002c1d42c1801d2003958540c01c100841401c000c242c00d0041050003007480400d0005201701281e400520b45c94401034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 896843839 1250 896842589 896842591
    0x6232d030607050a020c3003070501060b0a0801090504110d030c02180106020c0109080c090907080303070305042d200d050c12030f04060309020f0d0308091c0e091815010e 75
    0x41d00c10915000f200100c51454a00b104040c802c0360308140502d42c40c51147c5066000f07000020708554601940050b0800c0034900408003003051b940c3d4401142c1e00c40c1150001c840080da07000e0308038480c0d07074542e03074107400c100000340080c5000c1d0030132101e0b80722a6400140408200c58001d181000c0d5000108941038040010101402e401d0038400c10b1a130400c0c030503a03a101655540c00340708599000108220b0403080c4900b20182151000780c80e80ea140141011300985401c0e1412601603400000c500c0d6181030b10080c5807222850428122480c0c101c54a501051145203464007411003200b003032681b010350b5042d8803407403502e00c02c8001e0010703c800d203401c000150b29018000c1031140c0040001040002c3c60a08440603146c00341000030318002c8500215411000185031b20340c1100000c8014014140c110322850f1003444042c044032603460b14802d09064810075003003c00049101c0c105200503602e8101001c0b03030310208040030444007594814400b403070130002e4444103485401e014010301102c000c00c8200c17 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 896845089 1250 896843839 896843863
    0xc0106060e030c010c060b010c080d0b19030f03080402040f020d0b031501030f140109060f0f0c030204050d03080411090c03070306120f0206030a061806232d030607050a02 75
    0x90110964983c0c00600348035010000109030343d84d51103035a04241e005035586c49510340c215104c60303150a504000d100003040c03048100c5110f91150301942480710b1407402c080d8162075014844e80f01c003002541c0c0550b80610090700c12603000e034682c0c1640700c0501252014002d007160303007440400d0900042c0240b600f040020300b100c4159900780001400400c40c0000130400d210790041005421440f210600c60042c070014100401c0182040d1541242103455003025141d17984c0094100604515058141c049104502c64160448001400c1ca40030034010f04501b98854090b0b50b00341030003400e84002404800044490744a4502c020062100040d41446040060300ca2114101c5e00c50308552111b40c40380702ca055000340724550010001d074010500b40c000400402030b038480d2160380c0040b4000c41002d000540100c440e0850040e4401c1034818103c2090100103c3c013609100d5424601c2420a101820390004130342580c0820f00c0b40c0560392020000240718904950b04c054036801d03c0302000b401d081501440c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 896846339 1250 896845089 896845093
    0x1090308360c09070c050f0703030f05091206041a0115121a030f03090112060b071101141c06171c0207030b04140c01140a050f0d020c0106060e03 64
    0x101a01d94400c80140c0100c62281070740c000c42055500961521a00700a070b50b8010741440c0a0000d0190003186903100d0f28811400e0760110b0480b6004d555440382c403031001030f000510111008080718000c20003000011400382c00c25040900c8640c409103009070036141296242901189042c0c0300640c0000c05025158402034070075a106407406c02010301204100c001c1c8882c0d550b030111a10801d02002c007210410001e02a1200b800b5a4402540c4a81100d5552404074864200b03141c9242124802c0710203440ca00d0800504040c0541c9030415101c00701c2c0c4070309051244000c0c0241e09030b04143c0c06849841c400b224884a100c50340044403094134070561100e031110710300078000010751101007401a0391050030101111a600308520032850303c8601d62018229000405c2444213000091031200b44000310b81080340e0580600800448880020f008a40094401480f800c00100e00c01c0d00109280b12071490082d0400c6110340c2000d003283c0c030840000320603039910901004150b070041d420481c0b0000c00c40c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 896847589 1250 896846339 896846371
    0x1006050c0715030b1206090c0409170307050408030d020702011d010219020307182412030f020304050913060c051303080918100303080c19050307030b1201090308 71
    0xc500e54403440750090120690200c002465070511030781c090010008014180541401030340801601c5036025903680c0d08501664605901c07900b01790003042d0440d9132100e030a0301d9100102250070000d070030162900c01040800c100c0003441150400203400d00940200005a031000f5130310000d40f191509070b411381424904100680c0b500c1c0e07000b040d00744d20704a1304034010420103200c0c0700107400d01030f40e60000024240095841040511140d1000c2c20300600b502408070000c0c0d0815032000f60400b01c0c490505c603001c10800c5500001d110b8543d2800503107240c0116070902d0348480c005180032500300d88000c582c644030550b00043c02024001c5401300703061418058500b121038880c48040c103103c1d00014061a2000a00d1003581e1126072a020003c43c000f080c030b001c41d0800c60000094060035210942c00a1a42404106507003140300c00c9170041c01e0501410035100141d427a01f07440e150070042000f4241981d80c02c0303480854a42c1507030044c0030b612410000a209000e4070700a00400c1014000c0c0a40c204901c0c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 896848839 1250 896847589 896847607
    0x718060b03011e030803010807031b080c150409061202090f060303030106110c0a06050c060c030c03070e010201090507060201050106030c050301050f0d1502070b061e0a0504050c120f100605 83
    0x4080320705481d0680c2e05030300348104a074410f0700380f440a640024820340c800000007070300160108222050fa441031144400031000f5040c2c03401c28070b0544c0100c014541120344003001515040404000c0d5100b900d8043d0708003071f0f0350076121045070220740c00302c1498000303110a8404c520340405541c3c1d00141600154000c0d09024010a0b0789000c140211000c0c82004024111030f000c0030400203e05540040c0107010098460000030301c2c0f50000c0c4110405072040c000450b1112080c581582c0c0f15950302080d00741960f40e070f524112440c228003040241555620070400300450b809009840140c0792640010449505d4803500500b140c0b42d183c0010f041000603c014480380e500d60000d1031100108817040d504600e10340c1001c0020154040d9174042c0c25100042c03200030009a110301d20b01c5014203c880659407600b5644075001980180e064079400381d05d400e4180072500d4a40e01260300840c0036000b0b01e080007010079451249400c2981c00140d1941135500308825844505184000780c04035103007581c10724440c2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 896850089 1250 896848839 896848859
    0x5071715131503140a0b150a060f05030604090632130305041505160f03080105090402240f070f02040b1c15020f1204030305060405091506190305071806 67
    0xa400f005000e02d000403c0701d69070041c20403802c2003942c5c01410b0303601507082010551090304007105195002e46c00780d07403000030036501a070950b241c00d140e9a12000e00e199203000401c001010059011035105603240744161601480542c3c1c1d80f50a100b0030140c0c4641d44050001003010400101803401c89804090b0010000343d00c0015582100c10058000d8024058030340d094555000b6044290b0b032216403503490a0900072442c4030144c800d03000340c07180d401e1790343c840307060261b030703d00494020750002010360a40d02000130a00f0b010051380300c1c3e44006400d00011200d0b452240c0d00206041d103480350b10b070659500f585042d100745200a8411903200505d401039a100c40041c0000b004081d20071004640c0d01a1101e110350100d804180014200d00d036a407054640041c0300c100213482c03e40000c0d203080000f8809040c244a1140100d108000901364410320382c4031a003060344024082a0081c0b404050704a88404817000d050103144200082d0030320901b402c42400300d001c070f0000401d100c2418a02d04110035400 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 896851339 1250 896850089 896850131
    0x6090a050106141b15010306140106080c0c2d0c060a081602070b030a060303110a0305040506090402070204050a0501030b0705030c0712271503060b04090507171513 72
    0x10f540742064a407032201c041c1c4440109864204421409001c2c8203c03241c0c8050021070f8103036841800e00f004006140c058080031440d09020b040081802c4502141d0f5040041d0003510503d0f200398101e0b440c0b4402d0074104810300c0c0310b207180301502e03c3e00c500c04040010024042000c1c88802a161641401042d00b0000c2450f84003405100c99808034802c0c4001c2d00c1c0c801e101c000041c201c0307400425600c2c10501034000c002c011500c003d038005040b0001c078810a0801160805210741c06030b982d1070606042008003d40c903030121841c5a400780d402c02924006888900a00e48500350120000401c0d6155040000d03046600400460070003100b0410003007042c014606544860350005500c0d1420490f1390303030640e20f03110ba0303660039407600884031020b1403804a018000025100b4004c40d4900241800c00142c0c183c038560302030054403010901c028407400042e80d0045a001c0041d01d410440c1c0a6040c0c05240c0e0543c0030350f107407001c480060400170441d003440c8003500d2218100321400c0000503207810140700d041d05 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 896852589 1250 896851339 896851367
    0x5041211030d0c020c100201090c0302040e150103050f0601050307240309140a210507120201110d02040905060a050306040308060103151415250f0c080606090a050106 73
    0x44203a00400c51003820800e50b00c1401c490300041001c00c10028002e50f4805001084900ca203100c841d03d40e001a106004000b10582d00c0305d29589200d055a08200291211804442c2140310304000308006102d8400d005000310b0003000509651508080b01c2d900b0403505070002ca003c0c0d03204d00e4040040314544c06901c003200c42100920741c07404c0d02000044001d014030741c2000c0c0c90b00c00c0c2940b22501c480c1d4049440200300b442081e18400b030701c0f4000c0c070030345440b034440300c0001c08550144202e40115007282407070760654182d44000107213006541b0013a0300b01e8200966030f04099a002c84c09220000151140c05c3e0400300c03c6404101d40c514150001c1d680d5070000300000e0030403c0b104040b4600741d00a402c071000012480f8649907c41b52100c555241681219482c0f910074400000c503005081d40d014202e1741d40481c017032072511440b040da07803d0035406800468103c91200000346010b02042c502041c1901602500d8007800f0242440b608001c83c1110280141c4901c502d04801084625008a01c00d16803e07 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 896853839 1250 896852589 896852597
    0xc06010b090f040228090828020913060e06190f1509020a081b1603120507030204080f070e070e01180b1c0203040f11030f01060602060105040b04050412 67
    0xd0100c001003000c0025150031940c0003400070942e03610030348070a05d2940480f600d00fa40b995010145031801c0f10038000c01d12030300c2c074103403c000c40c2601c26018182190140c100070817195084c0c03001c0d590210b050000308031503001149000300d541c0020404203000d00850b4003000b1009142038146500011461810070000c50081d6940c0c0050640081454001c002c1c808400c0c17515440c2260b88814a801030350080c5000c1740020501d10009103155400c00c00100c01c100f41c101001e04045400f000010140c0700040150184a8903c3c1882072451040c024140b00f940160b40168442c0d20309580c00b884c0845520551140d07400022060040c1101c103450298000220302c0e001c4e160340d0500740141d03861190800000c5007035500050114100c846440203264460aa888100d031440110030000202c0c0000da900400c0f0300290600b42c00842c00d110900803001000a00f42c035102d440d003000850840e600b60b1f00440241c2c1080c40100800e1500b840791184d04d00c0140c41c01e200600d0582d84264903e00211116401d00c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 896855089 1250 896853839 896853847
    0x70303052d1207021606020d121e09140318040b030a240b120c0108010b0747010512030705060610020106031205030a0f020414130e160f0b0c06010b 65
    0x243d0304c04c212440b00b503d040f002c200c1c09181c8455000b921011101e69102c0400c2105840303201c018024480c0482d41d00007401034040d906601070802e170160041001c181c3e035540044aa07600b000700103000404038440404040c03415210148107000c05d944d0340b480072521036004400b0030008903464030700c0a4491072408032010408402e90035440c0060049001d01600036144481c00c1000503000180c058803403c3c01d17201c11400d42e03610030b9003a1071482003207001800c454200d100d01c6028025610300f81c001c90510703e54000744c42c5a403001c166a2008040c803841c4050350880040000742804d880d6601400d5029000d10f1414083c1d456455892402801242c06a0492440b5602540c400c1d441a40550b82c80100044480002100200250020744441c0290b901d4018415849582407003120115100c0061613250346020008100148204140904015490f0b10340d030000720b403040c0b0a01d1010304405030406002c0d81005022480b80416811003045a141000082d5003001c0016076a4112a0440d20032662 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 896856339 1250 896855089 896855101
    0x63103150f110d1a091909081e091302090d020d0203070b0a050301060807090302011e1e0c0318080715050c030d050603100b0a05060d0e070303052d12 66
    0x20700d110480040200b60106448091040070380020307402072420584501094810010030220880a5907801d50344451150844030080490f04542c5070315000d8485541040001c9081e4110012000f50b645030340b002c0020561960304e01410022894103a80804504010307021000c43d000c16a107120192244102d420441e04560b000c01c01e50340500b103004031464540c600140042e169400a008075800b10304043c000600d03ca115410305402c40c0e40583d60b008a55a03180c5001b1350700d0310403800900130131884094081c0003a4041020001c0e03200c21b5910051816880e00b80140b90800d107042e8039a1105102e401004404400135400d416280c071640412008142408190b80302c3c0704081c4020752130b001c0480c000c00744120700e61247d0b02c41d1809505464500020f02420000c8409800a070799000c075a8440030300c40741c14414040c0c00e600d00d0100c00040d0111900d000b1130f1a1128540c0100c00080d00000c0f0210042484403404000b15001640030101c05071224640c90b0b24060b48500d1031135003464900041ea = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 896857589 1250 896856339 896856341
    0x1050f040b130f0f030c0209280218120d0e06030c040317130905060f1014090a091104030201090b0c0a0803190e07090501060203181e063103150f 64
    0xc3c0300da400180d0201d207100030320780609642100b510980c030030610b06c0c00044034000340c1506004203c0c244416030b00024010765142c002904101e11000c08d80d40b00391001a1540c56114140014018000040c80c000c0c9400c48014032140840c2c100500a000500900004410701015142038030741c42029100582210710004d0411302848502c104003c010840001c0c4000403584102c0c042d540c01e4500c4d070015a00c1505201714030308035600c4140007820341d42ea44102081204060402480014514448650340d0301030902522030440ba85800c00c00001001c0045607080041d000041064102140c1003106000b1000c0c0c40b042405406094500c0001c00038600c0c030031401c40e031244042640700400501541c3c2c0c0c2c205a981259001da4500d6a00e00000898418000815500300c01d8401d905400e1050000040c072903500f49010050034200102c04846a0030b95401c400f800d001c03018a422085003102036400c90807801e0054a40d0442c01e0141403040c03001c2001c244583c045000314640c007044035805007140c50 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 896858839 1250 896857589 896857613
    0x1e050d0224030f01050109210f02011103040618090606050304060c1704050309100e24120708040515011d15120a11150418150b07030201050f040b13 65
    0x1071a0305800002c00050380390541859058407000c0e41d480c1c8080d81c440480c20800070200d84044006020390341c543c000114100c1e4400611403042c540070031800001c034109442e6421513040304000c40d5419401c000710b164998040801003040d00390030312903140340200140c018070000d080501130540300c00d190030070580240010844c2e50306242d04205203161a00b440c07900d0350800e548442c4101084010441e1040c40741c1d840d100003420044c0b04448403145100d0399240c004e03200743c6515101c03409010590020713990761480c0d4487c40c0b40b030301c0380951407403c2e142039810001111460348501c254880140030307060048054509242d5512810601e540b26148010750240c112039050741e10481c14500500480c4000c2008018140301d14010012025007100f08113100c4a05266003181c030b0400d000403c00105c90a030350035100d6500798400940103100c03084100700152940c2100351030100003d041030815909100700ca80c88424001407010703608040d51602002c09000d01003402c40c5204040036414080c01003108 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 896860089 1250 896858839 896858899
    0x7140a020c03160311090c090f010201090812040b0c07170309150115030b040216020d1e030503070906050a080118020d0f0b180f131103030c071e050d02 67
    0xaa01e1030402a03803c2c01c01c0d0f00306000c00c81d8103049280c0110039500b40081000c2c0105448240c05040030040402d03c01078104251034181150348603210300001c01c18500080881c802c0d00d0720b9070703080c030724081c02c00200f280c01c090510b500b00d10040007c103010070185504049800c1407601100d039641c0f148600945880384142c50484250192000061100212804050030a1003900c0501600341c2d008200002c03401030840103a0f01c0c04451101c0401882c3c01d1318041c0ba514440e030310703030642c080ea00303401166009145841240403034400811702c45441c0c0c1140084004002e03510349941f400d03071503505c000e00f9400c06205031003000311054160701140a00303805982c4008201324041100460541040001d031041d00310103401200c2810402807442700014541d8030492400000c0d0fa5a03450b030340042e20740f100030f200b001d440c00402e17482500f0b00c0e580c00307100408080100700020110241820152184c8503004082d034801e030007071040c0400c4240c40d107113480c0f405590121403054032480102900001003280c1074031 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 896861339 1250 896860089 896860093
    0xa0609031e02060a0b06040f03060f0608060705091306031a09030f180f0402030705030103081e0a081501020d0e0111070504090f0b0a0c120c02070512070306050c0307140a020c03 78
    0x903040c0d0154001501032003084844c0d81030000c45c6608041c0103041c401e5014038a50094442400d00200343c09410100407208414000038500366658842814000182c0c4c01c0e000280c000281940145003c20a41e1a10804110200130003441d60b91481d40b04003104ac141c4099551030f0000404c141018000d881008407252407207542c40d1598a0422805652510f605104494021480840d03003068405c0da403007005e6646441d840e42c0d0031521040d009402902e9440003001524103889040680d04010b0440c440080e143d0101c00c2c101400306001d580229118541158031903e4a880a180c1c00078036007400900a0a001d003101120508075420720b00b058201e55041070905d203114040043e5544248900e0f4008d00300701c0d0351602c41542c240c09039500c0d80780d440002200780255924541c160b40c021080d5940341c1c011031341410350352000314808154504c8612001d0304603000410900000c0c3c02160760203c00405454034510b4060b002401d00c06200380e4050041002080c0607203018002c20480c030b40c042c40102 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 896862589 1250 896861339 896861387
    0x1e2102060a17010b0705031b030408010603060606030e0a020a05060702041503080306030d020712020f0409050610080d050c03030c030912030408070c0501111b0103020d0203090a0308070807020a060903 88
    0x405030041c40121980002107082d0400001c80540c90400d82d01125070081c05189450558550411401c600d440e1843c0741c2d01041100180e503038806d1040070001c501c00c0d1408141d0b185041c502030704540c1c41c0301c0c0c105025041012800e006a85901700001070360811a1000d880b80c0d070740c0c00803400a002c41100c0c81e0368001590404024072034200007662040004a040700c0003404182c1d41242c0311001403264440840310600d00c40014600504844061000078000040e0264035840301c9180000036200620065900c00051005003018000320385070b503d603414007916100035900c150342c1d0791100801d0301194030b00210200d802500240200010070018136411b503103134101404c01d07440d2a44102c5044501e440842d000040d5175000d440014010b40302c102c041d203107011003c0901a0f0309004000c50707e041690070070074002c400c280d0340b000d11f0080d00010024600c0440c07518016010003c040d2038481401b460004201e61a6800540612031036440807000c01c044407545026903000e50a01030943c05500744072 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 896863839 1250 896862589 896862607
    0x141305240f0d050c0c06041106070b07121107020d020f04060f0306020903060604050403121a031608210301230607031d06040602070621180b011e210206 67
    0xe000342c000c40c032a8840400c4144c07a041d0340354540388261402c55496030880d40014001c200500c4d40381400c2000907181d285484490341e50503030f04900841d800c2000c1420b01500c04000744e4244076521201031080e80e900d241000d1500000c1c01c00303101200007481165600c0109400e038070765410a400034a14448180040c6460381382c8400650405408a8041e01c200f80000d80c2c0c9103494003e15000380c1d01511f89100641c111142040540900c00070500546010052036403280c41c00c01c14a05821031641c8940500c0e800c1c2207030203080c02144040d18403413600d5080529120003001c7e080342c0c11aa4615000800b8009410100c00504071541d0150b0340318101084800901d6048072508044005c03120546545030207510801c40c01c0e0080d070090b100184d0000e402400828019009255a0080b80d0500c140c074420a105502c10382d01c0021140c20b2400320180a5400c0012102e41d0740d0140c468208503529066042071183e10a8800388500c100010075148501104000e02241c2c0c481c03a40c003d80025900e0f0019 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 896865089 1250 896863839 896863867
    0xb090d15110d0f0912051327050f01060504050111010f110c0f0109080a0e01022d060c0421020414180d05070b0402010309080c150714130524 62
    0x90714a0b504a5080204201c01c101c0c862241c40031641e0f10040304050182002400c44850700502d51107034a06542c4140494450710600341c95810200b00138280c035241304000f18607419100058002e101c0c04d21218018010a50484140c0307013503410a20784001d404508030440303030162200d6501014114500301c1000c1304007400c04001d240440100701101d41e150b415160712801c94050820107400c40e0001c0c02070002c20703480b41c0340304c1080d00030500c11030305804000c42c40e40c070541002040001d05004001008a04110240001584180d60144241c201343c60290798001071840f100d041c3d0401c004c0032007988115034913036010345180070100650100d5441c10071065151200d242d408851031380702e02c0558101640c4918220b4400d079600c15064003041d2655401580940302ea050201e41000d01400504078260702003003c14124201014207050905103401d002d050341d5150085044842030411051340c80001050804089810540c0d0b01c070340496030003025094400c3c6a4820041100c40010400c048001c1c1c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 896866339 1250 896865089 896865097
    0xf1b050906130b190f1403130507080c0a120804030201180803220801200310050916080f010518071e08011a030103021309080918070801060206010b090d1511 69
    0x4001d2501c4d911494420b80d6000550743c0100c001420350412160865102c002540e00300304820704210501b401c1c0e903602801c0440b942c00c104410380c0a80500c10039407030003110300c0300104a034140e01c207501103003610303100210b04c40c0c0d02020341888103030100380480d8070351130902400601c0c00c00c00340c0b5100c048415102e20322481c0c1d0440101c080148a102180310b0b0010320a2030481e4000ca0701e058007460203103031503030381e2a00700401c54600756003840c200180c036884000d075491094280d00c00502000700100400790000c1d0000c0e02000003100420010f1003503840e55030103030346074019124046c41c05075034601c0f0444003280100080c03560050790269824107550031601d254165402c41144011070003581202840074002480044d6106200e0810241c1074503171035000c02110790040c00c0b8203142c18220b0000c980c00032401c0c44001c50011a84040002d050b50184440b80500031910280c41103514040b008a014024003800512420340400c0e50300130080c0c0300303100240380642030300309225084101c2c0400e111a00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 896867589 1250 896866339 896866357
    0xa12051f0b0a03050919020d0c050d0803010905071b080706110f041706070c0b0c07021806011e09140307120308190b060d0b040f0608010f0f1b050906130b 68
    0x2c2000040b4007036a60114070b400741001b044404c0c409200c201d408014451540d030800340c032242c44081d40404c0c10707200c3e1000b29584a002c0c07500e2950342e5151880200480307200403d010704018803044a40020417601c00b030035050b1504044050f80b6100d060030440010000512000465003001855400300070000e8050b108070740d00301c0307800c0f071707107450641c01d01030711260100c13030400c000b817590349a0b240064826419660420642d0782c0160611a8503030100d500020b84190319494003881a042100f02d6030b00c95100c1c944500003422802c0300c25074003034004d01100b1f410b004a110041c1d201c44144441d440801500005004035080c070130340b00c2c2d450308010313200d160250f612040500642c2d26280c9a140c6901820080680280ca42403400399820b0070f1500918400744056841511050000c901c0301d03960003140041c00118000040f154500b0000d84100d42e01000307000303074003414080100d12402078682e00c1c1c44800d01c1030500a565502d40e0001450310712400c0301d007910000d21408040361070070310a805020030903 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 896868839 1250 896867589 896867591
    0xe060a06050d111017150934051c05090d02060103050304090b0f030d120518060103020402090d020907020d170f070320070303200a12051f0b0a03 64
    0x54541040c420071102d01000900041c0c6050300a01c0b013414003151180d8490024070b00f010f03101e0515070300d0034030041c8156010b43c90030361103440c0c20076545050700038980c110345161600840b1880340c0000d05102207048049035103020225002d050400d028a007102c0c41e6501900003e203c1c61041c0c000040289000d85100d4103610444010910950002400c0d50580e40c00c20015410145403001c4040a005403603a030300e0b0400d40001d48601d40c0e880c01c101441191000351682c6c2c0d085d4280040e41c00440340000d2051a03140460f2000310407484020510606503034040e100541c1d01c1e00c821021138496002e01d10b0094211100c1c1d010416413030360204034500c2481d41581d039222500c1206284144000050b91801045801341c004980c00900039842079000c03d0019000d401802000303410100d550b0821803042c0d011a4075859549000d01518491412140c241c0c1c40560810054013001000210419864100302d03503607801085080a14060141d0071180502c403002a5540302e80003900c0c0c1e0340003044c5a0b004a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 896870089 1250 896868839 896868851
    0xc022a1c0506161e0318060207031205060d0b0604140117061506030a09031e0306090518070b1608181002010e060c07030302040b0a0207080712020f120c040e060a 71
    0x481e10b03208500061420390707440c100000180c0c45440404950013243c807040c19a42c41d51021000d00d01018040268050000141c544010341005000e52807843c0c4c00e0364005103010100406561900c0441540942021400c082030b0b0312480400e0052112074140c42d15242e401000007200400510010313452400c11043c0d801d15203422810104080e041011980c0c004018030018902c02929400340c25175a0007483c0440e00c5c204170307062a030840c0003241000d40003e51150001d00000045004585d0050311a888501002c00c540c90700948450b050f006080d000080020000b00080290f0590350040380c010304100d513141c0003002809400103900500900406460725262540f50041c0b1a01c01410401005015181e0b03885080c405141d014290407014154280400302c2c041107160050072914040e500186003090810042c949454416442040082070012108006888100303600711464010303a108480c1c1010401400c0c00e080680309416040362911801aa80da02e00184107805508d00007010425 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 896871339 1250 896870089 896870101
    0x70602070603021e07020d0614101703041403120d06050a140a1701110d1a0603070504050112060302060a090608130503041205031e040e0a0c022a1c0506 67
    0x83e4002e242c00d804501c00702880b1110006802c10040081c10300c001c10581d8824030a03503940302100e0182000d9014500c000c0700b000b01c80321455484201070501b040960040c0e06d0901c07245a03880c461030207214034228081c0303610700a5031400c0148400813600c8602c01034507410740c007945c14000e00c5944030b150b2140180b408001076100003044941d240d00300107428400d40c40d090000041d6480c89040d0964001d40d80e4415030000607086030003070005440e20f182c0100c3c40a1860300c40100780300d04015414030407503040007031004c0603401000b240c4c101c0d1003e0034020740c05404080030b40014845071307101940041c000103031a075016a02603c180c042d07a500e5100c00f440d0b9112070505041000b00c520b401481984108002d101001c0c0f40304201e81d04d5481441181d190002a40f4010310040040040300c69004000c1000c4c4403a40b030324241e00c1d901594500c010460421007800081d540c5520050451a0070740051003025104607401d05420845c5c0090910a1000c0c000e041807480c6100144082d01c8900501000c100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 896872589 1250 896871339 896871341
    0xd030219050a0f030e03130e0604050c090315100504110a03110c0a260a09080c09150f0a091d15060904020603090304080105010308191416050c12070602070603 70
    0x4040308160f0740b500d804420905040d00100280c01d050746007840248511132111138145441e20141802c07000e40d082d2400c0610074801511006400d4060640b802c2c070841c0041e81b40050035048020b80061030a01a80b181c01102045942e83e030419a0440e05001c001c410400b50600207000031303401550108480c203112100d689041c00785842d0500e031b91300111100404a0440801901e002402c46442c40035120000d4a9120a921004102c0701040b48004108040ca41c1032160f058607041c15129240d082c44e001802c007500100429095204900481c0c11040c99120384d00004050498040304105146200c10000d9692080001c200c41a104000843c1d02d410843c420303840c000c16014001e0105910345608000c03840c3c0006101002d00e20060200003907114003401164002c50158440c9942d0300c404d1300c12a020304c490b4084400900c05c000803018200c149031030032900d605d41c102c00d000002100b546403643c14100000502c540c045c1501c945c0702c14140c0085224070444405800f00c031300c540d5540f44103070 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 896873839 1250 896872589 896872597
    0x70b130210080c0409020f1b0c0306070e03060f070210060303030b0f0102010e0c010f02150c13270b0105090a08070e18030307050d090b0406050405010510140d02010309050d03021905 80
    0x2c121004e020410540040d034003d800e6490310041c040707040003007090b80d600d072107030f85003043d500f40f0383c481c0300d42c00d0040c18103114183e0083c11529002e590f602010b030100742d0b03c08020341901040740c184400101c406100340021b00750001390000901890340d0342c0c10000c000d400501d40f210721030311a21520411941c0144510803149124501404034088500015600469424007010550042d00d0352221300e03440c00000c8c54414804c5414080d10344540c0346210f2900301e800e800c0784000c07460607c10300d003403012102121400c55100207008241c010303003040121054050f0102ca03e03009000b42c50701140358a00440c2e6041540c5100352046455030351018000c1c204031300d4040c40200c03a0010800f2640c024801c0000b400090381190010403040e001c2da0301e89050701011282a5078a683d10818041002004e0144640103078600d0304000c8200c0c10000040b11a03a10085814891000da110b01011640a41c04c2200c925400c141074403642c40707000d100900a5402610015000200c400d82c1008103401030702a1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 896875089 1250 896873839 896873851
    0x140603060d0605240f0d1e1208090118051b06090409030302072a2903090607021501081f0b1507060b1503010608073006050607030806060a05070b13021008 68
    0x7211701b003c9440711017021001c2490640000c0c0007100c61008500042a10180c440c8540c0d6040781070f1a140d1240d50031600c030684c1a0880c0305411445801041d00017400ca80155030340c10300b010740c0200c0070002580a110308000745400c40d0810400741e0a260b01035001e4641c613401041d41454000f855450b03000728440c505404008124620010310641d0142c895401d61824100d4002a00c00c01d03160b00d81c3c5103074000f15518410750b84800d0812500580c103015103101c4100c03400d0041d1955040915003074542c50300c0c2c00700344101d05180c00d40303400040c2960010100e09502401d4213480c440d5075183c40c10658003415058514a0070442e0304030380c500780103403521208040c2d0031045003540d0901038101c2e903012005c0d00700d030108041d050403038030202c182d0086040c0b59060294020414070441d10804162641a030000303101e24014004a00820b03007001e44245d210004840c243d81e15041540250349500902c0c201408060100c000c10505202345007519074624021201c9900442c01403d013181e51020440b42 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 896876339 1250 896875089 896875099
    0x60c0b0c07170a0c0b011203022505120109140d1106060d060506130509100c050405030714130c0c0c0918061821030510140603060d0605240f 62
    0x1c00c0b030541e05118040c0219404503d411003500805403a50415628287c0062095551078500401010740401001a8601c00003282c0c03501d00e00b050500ca410041c2d81c2c0315860140f4110b041074141040d00703511a40905a01c4450820744030200304540b40d883c4080b075550740214075820540454007600054403882070304002c141f414101c0c0341e0750341d080250202401c001d030040d1070100b00002208450103440e1260500344028190110b81c20407020540c0d182030168030522404101c1440951030116018007510000244c0300d401e00c00c000d010a00c50424550340c901c0451800094441311648103003c0b0116034051007580281d030341c590744c001c0122689540e000c505035440401c903500241e010781128410200001c2285c0103000951220b06010780c0c0444091101c0d0102060980c25903014030800d90420500039400c4141418503006880a51117000341070b2142c0d0f00400051030035030b0303800340c0501c1c802d81c46601800305003060348515540c210004081c1c4180c00e101c84170008a410b0007020f95142d0100188 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 896877589 1250 896876339 896876363
    0x60b2a0c010e1c050c1302070b04020913080d020904061403061503011d06060306070c02010507031103040f0303050d1424041107030909060b160308060f0a060c0b0c07 73
    0x20054508080b0444125000b02d4050840407002c00c0c045081d00c1060301400103041840321090422035441c0f0104441c0800b148140312850110700b070040701e191301c941d0644030a00c1c1922951103403100000e0000e0000c1580708000780144140003290003500c10340c0d5065900344840c81c0c440c4c8100a22003032107046990542d00c10b000041400445001002400501030300000316201c042d50050381e031000c0d2080380c5030a503210400344501820200085527015410789015030f007030b040503400209140b01d03000000c1c0801c400c182d070000e9803940a1040710f00030840300c00c440380241d9603450041d100c0d4204031602e0017102c3c50700000c00100901d411045214960704d0607041c0741d8884a002c00c10b901c408001e0010380007039941c154140c11a01d05070041072030344e000e500d070b00880b607140c4014403003503e4403500b24405408050050a003060000d54800c020389a140c24141c004e6602c441c0414413411281b52050781c82100218000384460b00441d2071030005002d0360843d02c2d1a501ca440c1e401452081950040003414440c0d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 896878839 1250 896877589 896877613
    0x302070801021c020702041b0504030c080142032414010603020a0c020301051f060e1008281a03240702160803041d070e010e0a050301060b2a 62
    0x1130700a1682c2880148009909801c983d0460791884c05000c4040120700d00090074000d018100116100810b501c00c001d0044169038410810f6003454948003001024081d42038168503142c1513540e81559902c04002884190f480c20300f90020403182403e00a07140c80400c4803529003000b402820f541d09a01000356034642d1070700e0001c40083d449242e80f281002122070143c0c0040c0d40a01038207009942c07064402c24161886c056404950016034400d501b40301c9100d0b000643d80d2038081140c00c10132607605000442d55141c4110000c9001518000a00315580b48060502c41c404e5501c005001c1c6080354140310040700441c00e040d40d038450081c036403512180c042c8a8000584940950700d07445062881030310483c280c0d050905440016a400183d020380011805000758168080010085803130460144900d0511843c09407606904881050400c40090402c200c582c544a41d421700030308000d0020080c40b60340d0420908160840d6114000d0388814880c50191418a0352900e044840b9000c040d02c0b07030410203 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 896880089 1250 896878839 896878841
    0x801050105031905131101050c0613060603120305160f09050d0611070807050127060903020102041a040e061807050c0a30090f060804050a020603070c0302070801021c 73
    0x401d100c202c2001c00001c0f6030740d4500750140303034011244000d070480c41c503250f850400034004841c00100e04103c02800b60300200c90001425540040590340a1551050740e403d280e00a003030a5000680f2028080c500c944500b641a80035600c0f03101b459050048503081c2200c11501c451020160700002035400109201628100c5c42c01c000d514481e81000804000d060b040c0750454000703520680d0080800708102d420300100380100d0300000c104000141c285c14000d100e90414025803040544410340e1400180100742c004d40c1103a0207001c0940075150303100096054143e05500c24001c00300c103098041e001c24072a061820700000030394521951718609989200c01240c0380e1308106070030700807845400540e60105c0c20035105a0454220031000c0008250000d500c0700a01040442a03410401040001c03c000859800100c05460091514545548945c01c089180c0300000d1000381d07220400005000e580e41d0042c281d500f03118440c8d001d031181d4aa48d54422030807402100080d03104000c4094403c441b60030302d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 896881339 1250 896880089 896880091
    0x120b060f03090102191e1e0c140105011202030c0a030201020c0105071712040b0702070305120f071505160224070c0b09100b151207050408030d05160f080105010503 72
    0x541c40005043c44452000d818261805e10340350030200e801d402032400e240d03840040d100c03507900180c00c06131041d283e0740307490310f00d03c10140080c04108044d840e480320410032101410503074010010002c2c000b5585580fa4281103241089003203103c0d2050103802c041038100f403d1000c4c1240d8058003d001e8910104005407013a500c0004125038200300b02060a00e1026458050000b00302c100c0f044070514039041c40d08140ca601c000c1c0a02c01594840281040041ea002a61164980c0c0199005444044001c0c2c3e182950182000003410918804e20904e50100c981d4021441800c9032030b042d442a00d8008010390300d8180300070380c0500000c00900742d064141e456101a50300410b07246402c064000c01c5440704960b03040141c1d1480503c0d0415103900603010100c0c0500384201008407445c00d04d421806c80140e49612500e507418941c0c040400020303034220f002d0029070340100005000d8955540c201e0040900418003151524104031484052118152081d820b90322244000c1e1102d081590034540156000c1d00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 896882589 1250 896881339 896881351
    0x40f06020a050709200307050304152c071a07050c0a0b040b03060f030f0d030c1815110d0e0a0b070206090d110418140303091507020a08040e0601120b060f03 69
    0x100300440c411460714017030000d621850107a92034940760f04140c5441030841550070b01c0d00d0241420000004403026014400e403040e4083c00d21152102802c400300b80781083c543c0e62014440070302d910b024045030709185001f010b56038400c80555042d80d001c50708009550030240a21004660144405c3c00200b64410041d030304a0300c024004107411400e0b200192600e09c0710851451035401202c0020001500760054140842d06030600c40d518294030401c41e0545000c6d4810502c51084c080c40c03c3c503405018600000003c04004140d03505468200005403103054400642402200c01c2e21000800140040a40740615402064140380c07440d030208022102c41511020783d0484030004024a4a6849206601148000f0a00318031b403c151030801c001d03414450800343e2465041002040841c880100f14400405a012038108068540e40c00491074445180300c01044c8580004020030003503411004607126800c2640d505181e04000480041524101a0502c0d00000b050000310143e4202c0e9002c0d40e4044 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 896883839 1250 896882589 896882621
    0x50903010906021803070911090d0c030b07050a022527021b0f01150614090301090b160c02100c080c190308090c0d0227070302040f06020a050709 64
    0x20007640350701c0c041364490348980141202c03007592100d003403c1c02d029241c01840100c501b003112030204c1885441c1440394041c118070900759200303000300b0040d070281c50002454200c000c6641c60f26100c00058000e512155814025120700700398003049030007407014481c00f0340e640360480500c0392030412654549483e01c1d00304980e21408582c80030310f6004600c0502440082040c03100303180041808036500341002d0b040b035032a80b07034104245220440486800201250818505110500e12030b03225942e00c1c0c00b90300c0407070f41d01d5420024000140200543d0513400703041c4042a00c54084044c5500707a903c0702903000300a4100c0003441c0c2c0902c540740580d400c0e0480e10300506070b0310310385002d0314420b505001e00c07018840107101c80d420142c0245940100010380c45000040141800c0c0710003400a2072040181c40000d11a941c2c2100000a4022225000e07401c06225485030107a41481103014000c1d41180c02924040d482d40e000000d005440010900a0700d03410001078104d06081c2030b80c81005d80558985041c100d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 896885089 1250 896883839 896883851
    0xb04050f060901063210020a0f0803040317250504030606090204151b150b040207051f11091201020708030f071b0206090f130903080103210c0305090301 67
    0x1904107200e6948990800000015107031304104500380c4058030005003140582e40410658031014070600f500f450b81c0d030300302c4550740b0f400e100810403403a018503144001c041440140b01790041001c41400385000c0c0d442622200041c503048003001400b032804844005507002c510304105a00040c0e8066140c858002d80b904924140e12a02e0b100c044d00c1045d0320270715103c1d90000c1c041081204c80621810308481500c1c0211112121035083c80c880242520003800700c074169500011010100c0c1d024464080c0b0282c001c0d5241d1103203050003902c501d05081c41000b0608103001c00485003015101c0c6246207940148068100103102041c0110112070b080440e0b21594204030420104698102440c400e203045140d4017601d01d4000401003186514083e2501050200d0070600c006a03910340c10390b2072001056400c402422011400100c180548800c0d00c1142480c0003026414940d20802003416240500c030700d00c0f503024960340b108003090383c03032060200002d110102c120f0010303100d94000c0030320700e000900106074 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 896886339 1250 896885089 896885113
    0x1410141914040e1609050117060609090414060604150e10030602040308042d090f29030c0d1112011116060c0206070e060c01060f060f09080f0a0b0405 66
    0x90303902c40d4108100c00f11514042100303c6942c41c0300300ca9012294600f0814a61902002030088a511006020410010000034440d500c510b401d41c0e143c0c0b800104070907c1e90074a800c100425006c1075000e4100c03806200005110f43c145401498000d40c0550002c5079507500d00355000420702006000781d424183d4442e00040814641e0020340044c60180c000c895840c1d1500030316070103081c0402c0300340d080c522005144607442281001000b046504110002c071720443c3d28542c20009198809c201505111940001000d4000480b00c0080e1803505408480110494004001c000207164100420451082216030a2410884021402c00c0714a01c0081940d5805012020080e004080392480c6400100445003e10250380164800c50380c29002401c62420001c600900303620408800a02440001411904440095009000070200030a441c042261610401081002a4655100000d2102002003509000450040305150035000106000042540c0d005468100200b080e0b600d4040d440d40d81e41 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 896887589 1250 896886339 896886377
    0xf09020123190207150206010806010e01060525060c0f0f0534060609150512071a0d020708071103032b06120309050102010507230706090c14101419 65
    0x80034001764025080c10340c10130500601d481030581c000710001d80140010041290030200b1110840d148010000d884807218003000c1000c0e456000060455140500608101742d00c84a082c80201595580468140680104903000d00904110b03007078640221a820003255003007080c01c99003619403010008a00ca071503c0310011245540d1001040701c3c1c4410031840b9011000071000041c013000c440012014600c05000da50311052805080002260b40101e5060a14000155082d15200038020741d9100c0a510b8001940d400410f4200c80404528041645514012040e1445200c1120208040c1c608070f1600320400c0d440b54600f40000741d075580340400c00341071600320440f46030301945034a010340745008002400c440b8020031200c01c0060244110704074090341c1800750f1541c82840f50968031510300c1e0402400030401640024420799031000001020425104682066a411103100c0c0e0300300031192064401c4081c400c0718100802c010404032181c010403211055a50900c0c2c6040e4810120a040c01c071 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 896888839 1250 896887589 896887619
    0x1219090e0109061d04031b032304080c060a0c030f0504051c0b0906010f030230100b0303030c040902161502071b08032a010f09020123190207 62
    0x86401e440d80b800340007013080c5441c034904829181c08650130f94a41a100208451410302d200346a806012040c60240340c410300150301c9000400e04a0302814141c1c030b048101d04d9006d40b00c2c1c02c0c5a0700890144c00e58502d4404281c8902444640326407254524640c0c044854100400d554011320200b40804503558441e0031204c1d0141c008070b04c14525001160a01c000d0103500102102d1440d480900140506100800c4c14003c40b641540c0804444a58691001d0700742030341d00541390079440529406000031000606008021504402086403940320000d0648902c8100e8202d000c41804100401040400354028014401100180715210ba00ca944180120034402e050021694010824405028000c5d4691340030080999407406118940142c00b510b078001c00c00303600040d8070036543e13000c0c50711a80d0141168070010b0000030011482018100f000410040009900042003444440840b022000010800d07610381c54050781005c4001003050015241c001402045000f0000d0005417491488066 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 896890089 1250 896888839 896888849
    0xd1202040801091118043201050f011508090c090c090d030513050913140f0105130b010b090a03151121060105070b1f08030a0f111219090e01 62
    0x600e0b04d0031003034030421042e0f50a002030981d41640a070144000520082c1400115451041403001c0842d0702014440a050310080304140c15400d1404100505603401d04440c1601c16000780148069000c0c0401c8031440b00440f10515584d01030404140a03203441c0d01100e070b21510107500140b61124003c08034460100c01c1d00d0450100d5004160355002d4900315050801500c000e03186001f00c0d2900c002d648218011400d8090140807040c00390b60010901480051500881c510007030050b41850a568100544031b4a8191800b030030140c00411036030f82c41e408031424544000c150a1000303041d80c403400761400d4500c40e001c2455948004223100b031900c500182901481800c102690420a06001e40b5400da008020304e0400c0402c101290004441000c200d03000840300040703000c10003516142c68440c601c17a41006800f0f100c04602141c40550042d4110341c2c2c4112580c0d80010790270f1000c000c0e0741e24812890941040030b4103011240c564200704000a03440440303482d100761003641d250001d80d000c10083c1c0003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 896891339 1250 896890089 896890103
    0x7020928050f0601020c010806090a06030503032406030906070e01091703090406140303160c0e010b0931110f040305071e050112020c010608120c06090f0d120204080109 74
    0x100b1014280105040d54030901c00e001424060040c0400200580801051a44103012010210311001c281e98410806168803101f00c980c0c0e800c09034103c22142210010b117101d812004003040d5914108036082c1c034005c94030310000b40085d0b00e90f1001550901d000002040c100028500000f4621150028428200b85001c02035940c2d40d2083d414481078a403030303401441c00c1e080640b08145681d240007007250300210751000f400b00c60054916140180c1422640300820340001c050000c51412442d000620b40c1c4002150100b00c10070f0b04103001c4070403c2282c1160810b185103200c00c1c6580e00070350b03002000d03010a0b07071410625042001e10100c2003038019400542d81c43e4040f180622020900c032844c0c240034800d2480d00d007005407a06000903c046211041010f8143d000f040c613100104c8250003040107001500196450104204c10207240c2d500503030f0054003c0d2042e0408188000008600a600418454003600d8201031a44d01550380003030750441184216401c06c40001c0028003845503100140c4a011 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 896892589 1250 896891339 896891341
    0x30c060204120c05040218011103041d150f030c040c020a02030d2c090c0702030f0a03110d0305010b0304060c0c0b0703060311011b03080916080309041803050702092805 74
    0x420848603201d0350480d40c0200e06c104114417040802510718038842d00c09282c0b0fa030054079400082ea00b18051940810f00004c2a100940111420400d80c0e80c0701c0d140100400400700c24000400c0342a111211407203401d83c000303441480080c00d040c1c110310312854860044403ca40520341c00311386040d248040400c0020038040e801d030103000380c1940100c40d0405500842509255500001d42c06540c00750200890307100004114085440c20701188031132a081c00c0580d804a1200c2c03c0c0a00703840c10070a0384040178081c6081d8400c3c3d090092044038161140612200c0c110b07640d0b0394a00c03004180741c08820b0203000003050520001039043c60024815181580c012685030324515084403100c00711a58203050003400070003030000002c80b0703a80c611120b406141c01c40c0d017519078103c4103040a00c0c1d10f2030940c4003800c165021851400000040c44034100981d010840700c0c035103218141da0051042c6005002881c100404000740c5800c00800d504038003c50034204520740041c031006086041a4042221346480344 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 896893839 1250 896892589 896892593
    0x140403080702090c040608070c0c030b0a0c030b1503012108030a2c1903051624141522090302010608070513050c0942030112030c06020412 61
    0x440f2500900283e906600302030030000c01a200c000700074001d50420200b1000c0500f4001110103d100a42e000200b200203400c002d481c45c006011072100600210307091034003880160404042c450b40d00101d8035940360a503424003108190300034000e0f48101e84141c1e003003d4040840c24410003940107040c05840041c0b001c00b402c1c0c0021029030f410403010000078a60081c1da111107004a4410403000341c4c40f1b05044011480e24043d52103020b0505210280d01005000a041103c55401280700d8421a03200d07225501170071000c00c2c261449a0040d44184402c200070070750328030f00011100c0b00031100900040e80100840032000300f2114880503611101e8803100300b84117240c0c082c81000043c0c045d480c0034040f040e06101c081380c994804d101c030504071a40d503100042c2c00c030a510300c00d80762005001000800720030025841400e000702c5881e101200283c024100048030f0280c201088660425424460b003181c0c84e08064212140b8801b00a80500a1452107000024011310080c40a0700030700d50041c4c000d02440c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 896895089 1250 896893839 896893849
    0x60402040321080a0c09210501051008070f0f0501120e120706140408180d0b0901020406180501021902040b0406090225052112090c13090b0105040c140403080702 71
    0x240091401a01d083e4140c98595800024072003a81c0100c40d107842074941d400100d0405007d002405822940f9020900010742a490100740480d6003400c2251041c58848035001e03c080b60f80d00c90400c60007000364080050794040c4d0340609809515840c009128418aa0402e0920f00f0107880350324420000104e01c020085035102d44003c561654001d1142403800f903403904e0940c81f41d480c2000d200894014035141c25600c1600884059a000140202500b81039843c1c90203900240180004100c03114090461b070441c051400049503016030080c40d030040a03001030940603c0d107450590300640c4801b45511182c44601903540149100400160781d00c460103400188140807100a0b00300512030b6049101194000642c0a800790f0041c00c810742241094145e00760758881c24031401d4920014004000c3c0d46c40001c604018020b0342600d282544401e541c101400b1200345a10003806030000340014001d905007540030310301c0c1c00d048d82030032900881c03980c10700044c0b604141c3c0208c0b05807500280071021410a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 896896339 1250 896895089 896895091
    0xf18060f0f0c03080123180a0605010f020d0f0e04020a020c0312091e010314040303091e0f03030c02030408010908091c1a04080d090302010b0f01020304180506040204032108 76
    0x1842c03529458844040e64020801036040c481d040c00003040185020b46014030741d070003030a131102c010090810b2840140304045100b0088030385580b8507180510014103540503031015010000e140c0c0c05803600c05c0d60410700b0703240c02424807504020003454101d1078074143c81d244020051400d4a40041055040c004105858420070f00207614144d082403040c14801d40318008021007500140c98005410380321400124024510070071088001c18100041c001410340551007010b0141c0210660403800c00f0f4a4484d240c000c04040700102440d01c0306111802081c4268040c1c85088120310540f45442da0f43c0040c00d0945441c6801990031001c000f604a2692a2050071002010500c90a2510b40b0049480d00e03000740e201500101e003000c00c10700000c1d08002c1e0450840e80b410489044c100810846820028000e206202c11540181d0f40c00091207402d40c000000d81e0b0840c0d400403003880007804c4880240c0040d101c082c0c00d813604160203003c04400550130041c4400c44070948140f4107081c0702070550007000518 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 896897589 1250 896896339 896896367
    0xe0c040c110c0d111005070b0108070e061c020604150909050603190602090a090507080a05240f06030f0702070603060e04030c080d050c0d0b09060d030f18060f 70
    0x107251504900a4010444802912085900080c1c8003024241400b08070f00b000398241d03100741240d200703252454101c406040c00c2030003007100a24580e20f500c081551800307036010b8441200032500000b80d25103800011000701180030103662000400d554041031140e00607130840a41300c0c0d01041c400d41d14903446104c00c0020300a451082c46581464004a5152a00c003e490f4a01d40501c1540c4014007030b00341c0450701002070141c00340491642d0b40300312000814007540c142001400741c401041c1c11701c10b14041d0300c4c040d440312450032426034440e200004401c0c0e03420615176004001c01003100455901c03a0080d6100722000409603201c1c0c9002c000003401c10000c0d030032400c00d06103002010b0008548030342d102607001340c2c142080032440c1228281104240a4000700400c032600340402c2024081402000d44a100b400d00d40521104180004001079003c0880f4855081100310300c005000c24416000c1c0d66854200d41041700544a40da040300042c001103030003a4022807900040d03c400306620118400c034403a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 896898839 1250 896897589 896897597
    0xa020313020d0b090f070506031b040e0103050c04110703170711011b08010f03080a0f0c02061611061c0507050c10140109111605070801020703020c09060307050a1a0403060e0c040c 79
    0x1420304c000123000b4000030f040101224140c026400780512107804460151050114140296940340f6001d41c1e58542c041c0c1d014000d500702040842810317401c405440c0c020358540c499071000d0f1143c880400328000024421410481000140711034500300b071003656007005030500a61020940c80300060200c0c0c00603805040f20f0b4042910400c04940540b082d20042212403400d807400782a0481c08035007045007290040d61190001070012000e1001c031109146140c4100c001c1100c0901507020881f0500814100104655540c140c23041c480a01c0e0b0700c01c6070301104a0415900f0001d5140801c0e1401c1040404101455541c9542550016488081e0386c01001c1100c02400021082c5070240e500d801405440c095041101d0200401c00c01c0500484014122000c000c5454012b1800e001b5a5840b210322801e0084110401081c500c4c24003103080c00c103070f038406000c0c140c41904c1c04080400405140b101c1c0403100c4428000400054814022400241038481c02815240414000c000480c0c076028902420701c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 896900089 1250 896898839 896898853
    0x504050d08040f080f150709031533060503090106030b0f011a0a09090b0102101104090b0307030b01150c06140a0f0c0f110111040e04140f060a020313020d0b090f 71
    0x16400031b030b45840301c219005107104e2a1994441a03501c00c1c42c0e50002082c4a142080e0000848065404121200055040e07040003140407004000d280400200b00840001c9103142802034600501c0210f8210555800008015990762240910100141d9040c02c10b000c90f20010800f2610442d442031400c0c00b00e96030689000c91264000d404542da034802c1442c415140d146100d480da00904c528004200e61580070702901e24220000349403139010b0300580701d0702886c002e42c012446c01c1c0060401c081d030740e10400c96090b590802400200582c1c10b40008002c00203586610000607209005079112006640f400b00d50b142408081c40e01541d40d44a09503110502d0000e511444030b5110032038040b801003504142010301d2180c00c03064050003076108000000640024005003c007910701916200d04d00902c501410a04509900d40e26a0300002c0f1246059100c10b020484015090340110b4001841621030030401c0000d90200d0010f0210048c165915440300c0200b0200607800e00140c0140c550071320203070481d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 896901339 1250 896900089 896900113
    0x28090207151a0d0807140105071403091e16060507030912021e040b0a030b04140303010e0105010516050d02060f0903040f141c120212030f040609030504050d08040f08 73
    0x52a4403264520a41c4041c3c1198140451a401ca84002d80c102902030307603d082e92142c1c81d000e440d0603030741070000540c15001c2488400e5201c056130f0289460101402c407401410481d10104650a9898615805808403955101c019226000d0040400307840c0c464403100103003006040c2c0f401580c05800f401c0f0010300340c24010f070341351307509440481844170302c440791941410003280003022291a46a0080c1d81101c1c080103000e40400201d00c100d20030300c40740040b41c03400c20090382c80380020701c240d28510340b910005000940c0110090440c90720720300c2c0080928404c030b4032400c5c90301d4007184a40b03016800078014000402c843c2c5c4543d90b8455900c1d0000c61500b0328140b8102100b41c298419903400c03e008000c4401b0541d224440041409a075030200800342c181414040702000d65650580c016116649507400c030701e00140c0650f84245040c1180458654590302c42ca00940f20b0080c00b2000c0080c100b10208441d41c0d4012050302e820300400409807114248800100c424036260890701050780801c400d860 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 896902589 1250 896901339 896901371
    0xf01180809010f09051504080607050703020706030e030706051810020a050a210608060718030308040f05070b0c0a0218060622090203040809091806062809020715 71
    0x100c81c81007032900c41080b5540c05012600d400300741d000a9884004021140311245004010703005495050040d210f07241c40b1800180d500d40b203210300c000c025801c200010021280241c3c40703a40c485405100740c0f450807102e41da5200c1201c030122078280e2007082d0340101d5943e5040401540030041e511007000c600e4082c4a002c003429034001e10303a5034010840c260004c42d58071140400b1003441d4810000080c0403454a8100fa00d884400444890000a40540c100d03404d003001d48441000300c94050b2281c0f503c548540d2a6015102c007881001d036201d101d660b2000807000006c000a10300610140c001e4241404184104100401c01004035a4050308030810b01001c2e584041c22a800c001480400c42ca0f40c441202540d40300f241d00d54080c0201c541301104200a2280e0368008000601003101c00700c1942d658107110b00c01c54111103281100700d906c841d0015240382850400480d0b0034004d0911b0b80b01504002050300070100168004501c22a004140c04040010744141c1200d8800300040a215001d03030b80107080 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 896903839 1250 896902589 896902597
    0x20a0314060307140d060c0c02180c0a0e0105070b04030801050f1504090203100320090c0307210e1b2106132918011802040914030a020f011808 63
    0x841c54444c080c1003100c5654a820402c81025886079040c0075605003800040c00c29aa0070500b80d0088812a103101112120180d079184180c118492060900c888607500301c81800c034000300103041c08010000c10002c0f82e01401914801c41c401e64883d80258106400c0c0300090034201700d0740e0f004007101055a01040340390016102542d6012500586075a624400e004814105a2002e002c02800c400850000d06c00c81050040382c0070259140d0315980c58040201e0094442203c01c4e000042d1130a00440001d210004105000c9800d00b00215000030b420351032900300034602c111009507001c605011922424022092100381c0c00d140440d41408428207422912032600406c22140d401c58051a0410003880020303038060482e4140030420203606280f40003084120a450380e0003a00d0082c418404503203814002c402003420403185003291020079030300b4003002c3c1401c008212080c011040ea20701080101b0005021207000e01d5005018030714140e0211401c40e103582c2c0b03c00900912510704800401c155404031 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 896905089 1250 896903839 896903849
    0x80a0807120c0c060206070207140102030712030209040606050702040c090e070503040606030c0612110a0c0605150436030c080a02010e06160306142206080102030406020a0314060307 80
    0x250510606400700d801d0b144624008203403084103032011603129030029a9a00c20582030302202c0541e5159410000600c10005103c0d005a00412449000502a050b5464840c00c1428050f09001240e000102911401e03007103e0009540403d6a60941c90030b03019285900860f41400c00c0ca503802c04000c1c00c001840104400c06020700000864200502c0c1d07800400259080b10b006d4803810b0301d0715030090100500c0e480c0074003490304141c110700e02c11200b80c04940305051507440c0d00d1501c1401c0e030303a09005007100400044401c409804003015944660268080b400d00c41084202c1101c00080381c141c404807500e0031500d400b001001c030344000a401400e800100303034021207a942c841b52160b8049016081020418003e4005c403402e10002c14845d03407a4110710070554805201d516282d46004110554201c41181d2104003024007d040801c2c0c40d07a100d000054407000800e480340c071450f0f95800e84e881600c0c00c4882d20740c0041d00001c229070601c288002403500309816001800e0040000e982c80f02d4501817 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 896906339 1250 896905089 896905103
    0x5040b07050f0913090b1e06010f0509090106020d120c09030b04081303030f11010b0907030b0303040801020a09170c0915010e0307121211070308030408040e09010b0406080a0807 78
    0x1896501999801943c032550001400300f40b5840310350361144c2c094642d411003210a90b0128010401356400c00c1b00c2c080c07200340d50700340c4009036030303150b02c0115600c0104460b250140f003010043c1660035162800c04c1c6000c1c000d11b0b0010503107038042e001c0c001c200741d051030701d240e0589141500720b80d8a00e0380031840340e00700c0360012481c1c80252511704101c000c52180300b1260010180b03d6100208240d008800d00c400c1800b0340d05c504981c80f50070140e550a0b9542840c500b50b200d9442000180134502aa01c0030105013405000c0340e04054403811510b0899212074040004030308401020001c100006010302e400c40d1400c400790529480c2c41d40420072142e00640918207070381da4000180501e9200d20031181190000170115598555542120f09141d450001d064076411004080b03804043d01401d0b500b05610400300c020b00d0083e14640703072582030f44c101400444075154100400685030250304002402108080000907062984101300022941070b68040304182d00008011008220403038142d800498001e00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 896907589 1250 896906339 896906347
    0xb0403051b060d021303030f050c0606060304081c021e09011b140a0609050c03060702070308030910020a032a09050d060e01050915091f1a03030c0a0605010905040b0705 74
    0x1000540c54000c2c03c0c0d4161005101040d003184900740560f11400322030180d110704103811008901100c0c40e1250310050304a0341e118401092140c24242d005540c8a4060300030141040d410940c00080740143c505c003101080d40100e00d0f8071131102959405603480282028061030004c5010001c0d0940720024600440e81c0c034858503260503c0112821200120086010b980c0c0d01400d61509000500300c501c425111449415480a000d0034001480e07070003511180c0080011518655500c00c607544018090700480c0604407600c401c82c501d5001404240c01c850703c0200d8070a01c0340c44000200c0c85448001c286410036440500c4049401c0281201a91400d441480c1582c1032070925402919002d0383c54182c56280104100a035180401c1c240d0140303204d0082c03000c9030740300c6150311981c408003a40001100024000b45032070030200769008010000541098441e520341d58800641103802500f9a4282c80d001310f1104410032465204c0c0501600d0710042c10012803c1036242d850440000a00c8607081c020001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 896908839 1250 896907589 896907643
    0xa090302010f020c0709060b0703091206090203071706070e0109090b12150402130504080307051b0f0d02160810051f030813060e130b12030c01060e010b040305 70
    0x904542242c805402066503982c1e64100480d5480d40300348966800e40745403490104030f581120f8220b610094140d61852106c50900040809c181c51604040742c5555070340860500684081c03041600411910381050311615116141504108000f0240c800308004212020401e071f03044441c06081c0d0f9107001c1d000400c03001841c0032940083d9284418803103803290f8010a000008294041032140b48295103403004070840701d10041c142d540590740240000d000380006a400351207800600340000c00f61000b0324810343c4154840d03007810841c089000740c0307411a000c0030000c19010015028411418650b01c880e561501c52441d4031840c08a20080c540c545440100704100c000c60041001d000c80411282469613480c500100260302440ca400984218260b0000307003d4020032502c1314045015009007a2003100101c424010300c40d1000c4164040001c1c800c80e40381a00c108040c100341142c10000180301400c0c14049038142d00164801042c80340204414400100007041a000940c0000f1524a5034113504c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 896910089 1250 896908839 896908841
    0x919091a0612070308040e04211116060c0219080f030d110301050f0d0203030d09060f0b0d0515090102040b12070807030e12090301241503140a09030201 67
    0x80280c111904140002030316140c121040d40500c5085408442100d0400c0720591180c003503120240030103c082c0300c108010100780c0c0310301d98800e22460080e201c19034160b07070074030311103940070b003e8000031780c914101c000e585008200650b031000340d8503030041c1c5561604070700030540300100200030b02500c01c40500c02c045140d05140d6070b000d0700821080e00c4034213110200700c0c0d035aa00025a4000214141300321010b580e492034080b68144d40015014056800c13055040c402d01942032030089070507100801c0341079180001480344690142c45000f01164802c0a41c86040c250359031220024443e9407486001800a40300044c1c1e0000d03209003282031800350740e030140c2c20b80c020b018075406840c10100003d01d511b5403036611a5220302c13540c00c0b62a140704a03154003408034100d0381c10440fa00000d0340500c02c2213140d00d185901a0607035000003000441c2e00032000245c01c5580c4000c9074240f000014403032301400074009000e8800f03050355840c034040051301e440d11604010ba102c080c107552840c0ba9540e41010601d40b00f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 896911339 1250 896910089 896910101
    0x10612110a0e09210415180e010e0a09050a17040f0b030f0f04140607171005061803120d0b030d0309020d03030b0105070f0813170705100908010f290919 67
    0x111b075401c2502140c01c107020701035020a02103074900000e40c41010031480301d4214224140c50301d03881780d400c080c4d0f601481d03080200b600780020740b4140f152002044c00503103410a48039100300181c1d80a520303140f4058a0076545080c3c0c0c0c021403d803840500800880081c1c580242c3d5200050003691041916030782003200d03201602c0c10281e00c29003e800204800c903600103112819413065400d4150060f51264200760010303007240183e43c2d01000400c2190110100440b007190401c10080c255440340e05040712049003075001a010100ea42d848080420f010701d0240401403035961503090a00c040140d41c1c0c00160160f0340d8010050a15a440444040f0342c2d01ca4429035040039400101da10300400039003804d10b0503070001030750390811250401c070102d08110340c0701d00b402c1c10845a50040068608041c10801c045041038089000c114034000700190b160802d0007403812140d010200041c5441c8901d643c60340000b81102d01510000c1c02c16014030b0705860f90095a680004080001c8050a020204030700240003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 896912589 1250 896911339 896911349
    0x40206120a090c150c08030c090405010f09050f01030b01150e030d020f06090703081e0f0a0503060a0506210712090b10090c080a020a02010612110a0e092104 69
    0x20aa0100105059a42d00c0554641d000f980e40b990314581c3c41c0300362040202e01051200008402d0402000021000c1d07000d0b640001ca8000381600b015140e1003c01e003141c200340d0060794542d2030008200120141842034a03004040f0b40d19643c1d8542c1075444114415006100d280340300056a601c9841407403050075045503048004040d50030108450100039034031002e070b00b074814803801603030b010502506001841d030040b20340c450b41490070055085443e083c0e8202c4a01607074205c9034100a020748403000200140701440007522029124200704040c0f103494850b603044903009101c108040340d00084503090300301006600440d602e41d10380e1202c03000c540c0c19031014030b421490b508000c0640e04000f02c03c403045110317140511480240311f45e200400e200340d60898401c1004100c003032012805850480c0c004141080140c0004150325686501008200400712001c0d514040320b10030741c20042c40c01a1004000302104c5428004605280d80c4064507102d42c211a000e26040001c0012043c9002400b5a00100 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 896913839 1250 896912589 896912617
    0xe03041a071407050d26031f0b092d0603010f0618030201050d0903140c0a020f04090b0105012a03120e21070c0f0b09100323070c150204080721020603040206 69
    0x3050045140d01c4028248c5401a16061302000100390860070406443e00108010010070f9030300d03030741c925583c000f1055200350550400f005564000079101c4100540c005c107652003c0305032182c5403080007064400300442180c090b80c4074090400c003507a405410340704119000074001a8a40d41807800f65a8400c411100a60703580c001304d50140e0080d00892644902402039882803000c2e0802ca0400084440c2c0e480c0c01000c80010000502c002e52298001c0c42c0e040c1510702111001e64035400441801c0100901e040b030005020400c42001468280a08041d00d5104401414254800440c0c41940e01214201142c3c458000c0f03282c0003401000c0490074018240c002480c003c05850f030200c0b0703c2540c45200c000340150200144015520b109102e0041d2002d035a4000b06640d80c01114291071002c030184c003081c208024034003401c0108a5020610910442c52600142d580349400c01840c02e01d0602c0c3d000e80301040c80300300f11100c481041414000705550455006950f680c1e54800100a03001c3c4c5038034500c1d01 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 896915089 1250 896913839 896913841
    0x609010b093706091104120f020102030f120a06330302040515030a050f100603050c071509020a090e030d0c02030c060a060609050f060d0e03041a071407050d2603 71
    0x1100d0b60040f01039800054051120324002c0c00f00c40320b14803c61081c1d40814030a010101d000c12552152110020302c144140c918008000d80a500c03107030003007282e6210102a0301c0c00d10002c9400ca11401c0d00425407282c034031003624611001d814600e28840d10450452880e07440b17007030240380710764104c038040c01c0018040c1c401c03132038040f0099926804c1199403414962500e804110200442c103500c13445528402e42241c46241020011000740c13601034801a0600c1080c054440001e9a42180c034000031207500000640551030300410003001550751041464034684990a19801c202004641e490000e90501107134022010604030b20310b125100c2c100036203001d01070910204840d80e421603000c82c0d400c0da4075145e500d9102c400300b0074101821650740b54400002c2108800912590704001000c4018000b5030307092941d00c0000914842c44040054840703030000500b0070400801745140030041c0d1a1000034a080c0b418031000c1400219031490141c884d20101d049480780f4669006600024904010400d4407 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 896916339 1250 896915089 896915191
    0x22030305040b1803040603020a0509040f020705151302010e0612010f06020d031a13060b03130303110406210f0c0801090e0f250306020408030c0609010b09 68
    0x20002901c044481d0b0500714042441141c80c215005a4810040041c5140c01c0c50300c00d0030380080d40700f0800a01400800e00401040b69618030a1109029801d0400f50366610546403460800030030501a08007218503a090016030b03508040c900b182c6690a00702240001410b1000031010b014000e8240682c070030a90010031584418030421007150295000c03242c140401030420750540c1c541d0742e00e022108561100309403551a2010380036405042203080095091b4070b44403008010384c001c03600c0001c0c1c01160700e615400c041d814410444003050868200341410b0508000a04080e01e40780284815030111003424202c16040c2d011044503000b0010030400b00401c00e10242107031070244a00d05c08245400140d4425030000711f80213550b4010000a0b0442d11880020b60410100c1c0311401d2910b500005400b0001a9103880240701070000d600045450b02090f014a502d0b051006061211990506441e0700c0c144d21882d52054205c1185801d01c4007007085212906200380d03510750020140c041000e09110 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 896917589 1250 896916339 896916341
    0x3030d09060c090b0306060a0e060918071709210c030a0206060109050d0b0c03090106081002030414070b07030e06070f03080a0e0118020f0609060d05010806070c1505220303 76
    0x1080856035241c0c035048030f079101c0e04d00d400b5020407a0038a4006208000c00c3d54180d108130451841444010303c103604092814000c0b0300511103c034503801a4200320001d100c9200d41104100c0051100821140d1a9103802940d03284c0b00c0440030b10110707981900714040107901c188202a61030103440001140d4490b02085002903507284244d54031404a00003840118507803c05041d250314098001c00c140d02c9680344d41c40c50100c56030004024a0241d50380b0003000c51001800d01c81e210a08000120142e224213150421905c104905042d000050b8003407a8208920000300c0103607040e407601030510016029405011400900c90303260300900500c02d04500c5020960481e043d00d000d1009003d04000c5802b603600c800f42251880d10844c0c040030101154080146050301c0e1035402c1420283c1201c0c1000c408501103a200e030000c15485840a44503c0140a401800c010280d882170591070104a440c5050321480820114601d0030030041d40c46400241018003c03040c40406d070040800384541c08511410010 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 896918839 1250 896917589 896917601
    0xd091502152802071e110a0305011413020d0807080904061d1f03020d06021b070603151a03090f10020d0e160b0d06150c03020c0102061b0903030d0906 66
    0x515911008510b00c4212070588281c6036a0707540100c4071910740b42c400003203c043d80d43d070a40417a4051650000301d595074071401c00460082d489100086103402a9220180b0455070042c485041d2081503180f50001d42e5031101c95049054114024a5850005080a00c124882c1e0b00240383c00a085c00d80c0042c005c5840d0941c2900c10a0305580e0741482c2c1c590b000038003215400342001c02c2c1c07804a00c4c001400589058101841c010703110300801842c14142c0c03182100045203034208400c5640011401b00b2160b9014000c14824900d56000c00c2c031540d052008080410039007911400615a020001540b00d00040188600305281c0108480300100710140c0b02002e540050456045c0504103261903004a100040c103034000c015420303030484038508150280c04107130030860a038819a52550350000362204140034061204000e940c501c140035046040c042c0c54140003500705411580a44d00300b15284040b01c103588002140102d40607a907100100002e4034501565003000c101600d080f5000007003001ba98810 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 896920089 1250 896918839 896918881
    0xa06051008012c0105040e011d0109150c090902030601020c0904050c1804020303040902070330141005060a090f0b0d15180902040e0a0b09010e0d09150215 68
    0x10450f901c007a000e680c040c00ba0b00c2e032100c1d045050040148524035281e0000c80221018100003c2c420000360382802e0407240396846103200340d43d03800955062008003000b00300300d9180b12030309100099400c1c8005040c50301c20f205400d0301c2035011003c100345030b00c00c4c007141c545884d00034800c1d0f5085c185420301503182c101784a001407040c0400803090183c0318442c40e00d103110340d400a01460500e864000301ea406940158411401c214080360a410042a1040d2400036a0200e0803040c440d90200400d080450341160801c120a800b81c0381006580390b800f1000c2c601341c4009491481d00ca4040550a60b40c0b580c50b03803c19241c1d210f04400104500c0103000182c0f05019031054181711004010007650304200301030088412540800f441050342041d50303081100d20501c00307040050248a01010319040121001c0111840e110003020f12907142801d01818402540940291461450174180903182001c540b0800388251412090412503600903c100302c0c50b0758004000c03500394a0b100c0c210040c01a092040 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 896921339 1250 896920089 896920109
    0x180807060b1c03051c090b011203170103121103130e040204180f0803130b0108060702060f010b1b100207030c060c020d05090f0a091803080609040c0e0a0605100801 72
    0x40041c0c2d8604099540d4030342c0b80c060311807910305402c5140011326407910901d0400c01c80c0e11404400f0024107241c1c2c03218000e080c001c04504c00386600e4030700244803190540000d20300503c00c80c0144007103210484440b8a04e2a103003440850810707041202030460154480342e4600d140005ca0014031000010030440c41a8800c0300d003080030b100c0c1003641280da4031000c000a06800c8000c0803000000302540000d68010301d1600d082d81c854500d0340d48040307040109070401d000c4c541040c03092003403180d010032030f81c4e40203403c841c803d172040c0d814824154620300a003145d0364072402251444441e192410301011107071084c0e20209643d60001c909014040820542049403614500303c8080c019520200d208080c0e1442079461a2600400e5410001140007074482030364072081c40a03000480c100e462140c0050a480d1404d00003441c1e2183c10094142d002c01440e403070203540300720104070004081e80140000c0e0381c0d842d5080101074980c001250024030050b04203d0700908142d02e60b104e0103030000040c504881d00951 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 896922589 1250 896921339 896921359
    0x1c0207080a030207050d14010504080904050f071b020d02190302090703020921031c0e0106060e09060913080705011d0319050309030d090807021002030319180807060b 73
    0x800e05659152416020340180c220040922041c540300d050010201d000b05880310b01e64080c441503500b110b800351011250300340c001403017401c9810b1900540d41c1c4011491080e4080703103480f44002d03061504c82420802c2c02280e40c2c080008668607081c90a41ca02d4002e08204159446602680201000e90005038499407509000540c12031090080b0707500794001504803058030030b582c00800c404481044030501640000e01c0000d034410280c0c071a942002407240c0300410b10280d40b1180d07908450064004508004070262416441e1b2289204150030071800e40e00c645542d9619544101c800703914000061811500203624001e100054000c0013500000e1340200181040c50501166070303100d40d01404007000243d021810b03180c6e000e40080c4d135200c0c508000703480c60721005034060411102d4503a0f080355200d1012484100b5800c244405c866545c101e80003e600d1403c02c070f03039144a8541d621103d01d14403503c2d0b02c401c01e03001d00c4a10030071045c140d0024030f05071505540d00d042c0c406880d0b69410300d80900d01c180 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 896923839 1250 896922589 896922599
    0x102103030b0a060f0c061d0601050a0515030c160b0c030403020c12150a060f06030213091e020f04091a120d1d0f1008090c04110f1b1c0207 61
    0xc4000011140a0b031036071054481105800d446240c04841c061b00c6590b03507214103100d640704954080e0b1a01c2d54910103080d0944c140410814604101e170009070080c0c69000148030030483d854122500700b010f41c041261941500855a110040050402001c0c54110424803607400d00c0c14025500a504c00e4003900c01145054003070103164441d407920307082d02c0e50100f12501070044090010641048829802040c0c3d00c0e120300f046000c4015503800345000a0b40000c500c080321700118541c0d005071030318150501c5404241c240f580ea4441e1140b0251141c0c0c0ea001070b0700300005000704102c600420ba504014055844c03c0c002d1001c00381203925015004902d000400b20f02040d010481181800c0c0315100c105514005105502042500d141d98980002800314110320655511001e80500381040e5145041480c1051299040c25401d01d030481c091804c0000002c286280b0509446a0100c400d90b45603c0340001380d245201c0e5108030072000300c54094040741d0408804960080d0a0145143d021244c21542d42c1c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 896925089 1250 896923839 896923849
    0x80307152714010e07140a1401020a031101020d0507030b0f04060602120901031d0a050f0c150a121e0b0303030c030411030313080d14070b01030209102103030b 70
    0x14403111858035144000841c000303805528045402010300b00009082e85845013154a054010b07008540e0917184d00c09607404a140202c1c90001a00f1000c5642e08801c100c040040d58a02c9010070050a022400c410145000000d506403510f07034040290600140c14062400390041070707035110780380c011450550307502954205400f40e03000700d440742d90003031070502201c0081d034005801c0448024109902e80d0b91010b442440070600c02000c1c000100900f01d8900701c2d1811524100c40c1d010780c6403c507001817005004960302e0f01501c48001c08500605682c8030205002110300401110380c000d100c1c2d2500c171185200149038a044002170703181607010480a241803003050707601e000495074140014010000900000c041c155911007440000d07003102e06085150314240e03075007025a0450412a03010301840301c01198001002403190704180402850150a6110080320140c1400041c1c003d0300402e022880c10038103210090014884a02d0b042e00246015148000c10b0503110b0040d00001d0611b400b540319482c01d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 896926339 1250 896925089 896925131
    0x3060d1e1406060f2403041101020723010305041e050c0312040b18033f0a020a03030e070f060504030c050a0f0e040611031f0e0c041a0408030715 64
    0x34881c182c4050305070104181e00000000c0e030143c1200384403010b68205ea80c08065170099110301d0014003682e109500082c40c0040300e502012080440030301d00040700c0072110000f4602a82880c01184030703500c0341031024a0110f6000340401010602d80c00c2c2007400301c0801c0819204000724240d134040c1078100d03d014410300807405600e0000c8400c2000410402540b10341c8003103040050207490021405014040c80019041402c040c800e030116400002e10204410790b60840b00303040e0f00c00c1c0c1031604c0d1050081d980c0c44450802024160390302021080d0100400c41c80005061f6014652016626440010402e07081848100c504072186103010031140351806041c170a40c0c1440c5c03603440010b840d00400c030080060240058038116920030352200f800c85210300940c03240b58504c8012881010b0306100907401c11903a41301d095003086043c1401042c4413a941181c00b01c1d015980062408a40c0a0075990144144d030b11015062000141c0030042000b00c0075446004644584100485544660642c40540c5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 896927589 1250 896926339 896926351
    0x60d170a021501230d05060103031d012118170a080901020403030e01080709030c2411060109090c3c080a121205040506180c090c03060d1e1406 63
    0x5250705214030407040041d031240c082c013002440d0741d0807102c040e203903e828041c0170b030010790016510015400703044084001036050aa401c2c40e11440214400a1119840880e1f0b4a65000652200520754070f01561150300420507030002594885401080400010b07903200c9205440494129000503c1c200d5043c0b00fa2412a0342544800c003075800c5140046542a00c010000d01c01d0004901022011940840606010b4042c80b06c130501131550650910047c2e1500c69900c9041112a003400352a5400108200f411a0905140410003515034903141e040c0380c4141d0880380740685880c900312501c2020f026400040514500340002d010440c1112288050351401140e0080d8002803c1c00001030b00d03010610980c44061404980790f5a0416081c4160707403060310166002e0740300d501407000030312100003400b0b0640c00300c400401c143c07142d00001ca242c011004112b0250848007100207400b546941c40a07060b000e07440540b5400010601e2581020000151810750b0340b02000c00103208401c4000800d0781c000e030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 896928839 1250 896927589 896927609
    0x30705030a080901270f030b220b10030b1504061a04030b0a111602010f05070c03020d0503190215070c2003120406020601051207060f0305060d170a021501 68
    0x403c5401035a29040300e4408031018014400c9101400400103040c2000d05440749568408600e913051207a04110301814001d00041d10705614100e404c103c4490744580d80c0e00109002c100c0d80d44080c882c0c0003c01e161b20241102c0301420800010305110b00b003540400c1c0c001c603030400845442d20a40c10310a03580000284a101082005101140b041c109644d8822075a010208601c40388a540400b1500145803580038166800703111011076801403a034440b107410b10310b0400e0030880c0e651505001c10b00a4880a80102d02801612052140900403151aa801d402c800310441d059640025036620408603440f10356545000440c0d01d503403090701c42d4050700380c0062160440307241c0301c845000294414590315505105501c0302c8846915500080d1004040ba500900780f0b96240c03005025000c0412846901c84e034002a4090208503003201c52000c106440c2e290014ce01e80c1c0f1080400c460b6001d0a0020b0881c90701c41c5106450a01c04400500c400c403240d600b03640303c208030410702d0365551f4030a01920104c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 896930089 1250 896928839 896928847
    0xf03030503150307050d1202070501050307091404020403140a1514061c12170a02070519141b100906081305010603120f140906070201030b03011e0b030705030a08 71
    0x30071480c01070100050000301522184d607a1540025409100700300c00f210800c03c40501c0e13910142e01401944000d00382805d040303241d881c041000034806402070103010807900c918446242aa200c0c1d90554000e160700c180f600c0d00c0c0c100d802d4480d0b9901c4103001340444280c81e545280f041460b040340140d03440c515800c814840c0783c0c1c6420b400c2010050a54441d407101c614291000c0c40400d01d4403000300d008007070649036a0107440445a03a03001d0301600820550f207aa004102e0140021030000300c605d21005040c41d035911410742d0f1f1500e0503074044158481c0e0480e1013142c0400401407100c516825442e10100c580501b00c0b11785050685213002d452003000007080020700040c0c5551095075485828922640002070302c00d0716079841d03004142c0440e0500e80001c40d00003111003565040b5994003408800b4241c1d190800c0f04440c0060300604c600f0760000e0400d500c3c0c80810042d40c0742500003880f135032440100d0843d19180c40407800d0041c4256001c0511070b10502c6400101428042200d01000da003242e219864 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 896931339 1250 896930089 896930101
    0x10c14011a03071512020a0e15030108190b0f100305100f0c0305240f13140c040b030a0b130e011a04090f020f060415081f05030303070e0f03070f0504060f03030503 72
    0x80d00b140b07409606201c01004007002941c1c812800d03250050709c809403241c50b941040086440e240c0201c8204203541480204800410303d0740c3d04042e0721191750340219815950b4030f880b140d041240c1d94001051485810511040350f045500f002c01e81e20782c1018200031540450408809807401580c110b0289103548028000c800c46004020000d10000390042e541e076000b0401042e029034081042c00e041a5858904518074881c81c8111074000310040c0040d801c290415804161510014229601c1c60b640c4a01e40710306a120700d1880c900b004512242040340200021000d0f000e003000500ca180400304080250341c0610b001d124605416420032114009840c0036801e11810b00c00c6454440d44c270030400d01c4002408090100202c5a1140d10f5407864140e08065070480c0c90b1494104444030075441c500d40900090300d00200340c0c0d40c010460311f441c0c0070508981021860382400d058400c1c0e0140174008010030350241000d403580c1269010b0740c0411080365a03400440f000c0703080d400300a0006404002140c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 896932589 1250 896931339 896931341
    0xa12110703082a07020f01050c10050601021203180d1823190305240705030a1103010b0702121605010809010f020a0c0317010311010c14011a03071512 66
    0xc0d10050b0040955807845001c40f03608144429880010081c08000980c4030450030308070319000d1102000c5c00e1050801c00302e007120544441410704090100c999500002e1a1a80708010100c446c41c40c4000b0741d5640e091000c46000900c500c40780c2043c1030300c14424038a040c01d200b201189030035016807031089109030501d84c4a4042d0460400000e81c042c600680c0e042d49590341c0c03400c90142c210308020600c4500d00d03525001d8101640c031f5540b050245488042c007001d1000181856510034960310b40940c3d2641c0d9501c0b080c004003400694440c00d07240100020074031450501c01070602d1802128911a5040080c0308903643c1c4010202001080a00d040200890350207651182d81280c054000481c00d0260707014248120b070000980305000841c810400410f064002c038102d113454040d034542502d15130540d182c040c461113414a00c54100200c0696210903c90742c007001e104c5a01c0044000c2c0502c006c0d20074440144984080060311030701840000080341c5540172800c03a800d07103064480e4002d41c101c4200081c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 896933839 1250 896932589 896932591
    0xf060d080a20010c0e0a23061b0d030e070803030c04210b0702100e0c0f0114070c120c0e0906061309150f05060d021f030b060408030a1211070308 64
    0xd0b80499000325103080d00200b8001d142c1110980e82d507558103030415004200c46151160300c14035a00949802010310811002a0103403140025a50640e80e14201520003440c10602044080140104031410f641c480d45500074406c25540c1d030b070881e0410398171207090b0360302e03444140c0d0700c100301d0340f0200001c01030441000ca8902c42081d9034804c2c0c1701c0c5101a07883d60b4a55840c100d1b50080144c00c5100d03060a003071094490f100c00081440000c040c0020180d001c550145100342185040c0002940b02d006560440400c694405610407034000106075140c182003140140380c00229000c05121380042241c0261911071407141100e80300401080d11b8038028005207882007055840e20b962540c01c0c100209204442020329a015480000340d091400002d81044450190045220307804207601000981d40e203000d01480d842610f11140542c20255000741c0050081c0d50240d0b40007100481d001581000200281c4940c42c0d803915040482c02a41034440c00b1511f0710303904d500303441106109400100384149402 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 896935089 1250 896933839 896933867
    0x6060f020712110604060f030f020a0804110a091a120a0c12020a1a0304060b03030a14030606070c17060a200d0f180c050f0a12050c13050f060d080a 65
    0x41000725156001305480750f110f500202c0100750908404217825034503204488150551000031070406943c02801400440041c00c05019000c14032a00b1205c0c1d540c2030402c0c002080f0310300d41000b202d0b184100c0400001c0c1c440341294418104a07100340c0380c8050205440220320740c00030401d484c540c2482c82500b07106000c1481641c1242e0710080228a08004040b4251410092003c40da101e03c1c01d0329241d000c1d070705180300c0715004c0c2e0024042099120f400c06180140340218049140e141d5641202045060041030401307441c00540e502c000511118003002d01c0e07012044442510300350369800c200801656180300076a0000800c4459118490400c40068500700c950180c000c0781421181000d4001d0f544200b044144c01c40200c0c80413810003c8400e04017005200c2914400980f1117200c000402d07498180c4035200b88550300c0203a94041200c240196031201b40c0c0207112482c00741c403070403404000340400c50b01d9940005100c40440c0c220714084410900003940038068900d4100180c0c811030b0310020241e0f035 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 896936339 1250 896935089 896935103
    0x60e180d1409090109062d060c020103020d0c0306061d180402010c0f1211010b0303031609030f06060f0501031406040c141b060f0702070905060a051e010306060f020712 74
    0x34440300c3d03a6202926802040c1410002c9411820302c12009241c442c42541400c0b5002c095219011a1500c0c1c0302d0202192841e00300a07070308135528001038010744200d507400e282d02c1d450084080701580d00b50388001c040c0c910903940d490886d40048078407031541c50505150365001c0726110302c09954044c44038240380d10910625207510200107a0750380210304c0129520445030021035100f5524603e07030020828640c180c403600207002c2181c074100800d40324031016040340d40000d184140300400600400c001030040d83d00010804c0e03550b125062440041a0324043d1190103014510b0000362503100c2c3c0104400c40301c42500e65659074503008100700007081c0300800b11007800300e02c0b15030710b04e40f070703035000152400200030400e0144400c59114840c1c1003a0000701280c2c507902e2124144508541d00066600035a032004900003403d03100c0030b001407a04035203903200c03590001c0140008841600402d034180c1c92244203803400d01000e43c51301d50694141c650343e100a001a071015004201c1c403c07910500b00c03100750213200c0d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 896937589 1250 896936339 896936347
    0xc0304020a030501020a11010b060a0e09040302031c0b15033607080604020a05040603080415140c010207030906140d02071e030203181c0330060e180d14 67
    0xf8409080e80c00c21851140420207509403103074840b20030b002c2c5002d81841214180c2c0341160b4414003420b0f110040748210b0103041003000103001c06000300b0459180d841d18000041c844511059400003400c81040114001c45011851501181d6042c06a81c00350700803c000c00301c800310010100d15120f032801a06d014091101e50135000303442d8144051000b410b0303800003420b004d18007030052001c140c1c1c0c2e80c0c4c005401245000c10800100c2c954600b07030b42c16101d25407460f0543c405000702c1240c070380c803044101d1010740100003010018004150300520318544241c5038001150341c1d4076402e6819419600039001c01c403004102d05034156001e0f900500e1014800e00a40301e07602c800c1c1c003444841400d801000c8000d6400041c1180c4141b500030200c500d506401c441c6014004071010010741300d1080d0403002800e0241024900c40050b0305240481d804460a208040b402078006020b10040c100d280b1a07100045402da000c6040108200c40000c5001e0007500209610703500d07407008803054041c08003030405001081c4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 896938839 1250 896937589 896937593
    0x3030c0a260108030406200a030f0314070f0206090c0a05010f14070c0503150c091c140706030e0703120503040c0e1608010506070b06040c020a0501090b0f18060c0304020a03 76
    0x382e000e0807140000b56111400c0c100c0240a00f56115821980c00c40c802c0c41404107250f00003158840c2c1e540c589000050b501350520140c0c068510007200241c0403100c0020411001d80c08840030588651590031210551503801003142c4841040003119040079402030700340015406102d0040c002051842e00c0302180c201c3da10b410106810494080390018940c0c90200814a410400c1344000b05200405030554105031100c8a01403040c0700b0304a01810141c482590030450700344440d402150881c4504c1e40c068000308440784ca581c102d001c0d0f2070100349000040e4101d00c00002c0c000066a0740710002105c6040005c1d000ea40035040200115422100340c80041200360025036464022101800741402075011924040d0000344141c000354001c200c18808031000c40c0e1109484c507084642a90b00040280088074202d00381006500060101d42c20940f120040150315225148149081c81c01001140c698002e07901003256034084204543d440a40451806081c000086410620060900c10035699036 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 896940089 1250 896938839 896938907
    0x504050c10170f010f060216090b0f06161202010e03120a0e03191d0d30020f060f010501083105060f010603051306110d0510030c060203030c0a 63
    0xc680f00204030ba40034004000034040b502040001e0940c41c00038000050b01d03100902a134842922405c42c65645440402d6215110102081c00c4140c000d84500c0e900c0c013a11851a140b051500001c4031604042110707070390100e1040c0728654070810311001075031618802d00941d40301840c015100c00c407059991402d90708090030030030062403048010304003203800a081e805e01800c401c031841d0301d1001c1d00703605420101c0942c0c2c078040503e159940c04424800303401081c420355031a84074401d03074200c1000c41d641d0300503840580001d5050b20100a8004551443d80c1d41442607400c1c000030f01c10307640410003d0010607400b05034940c4501070001400c64103400c08030707007140a0740860460300058800c1d401c0701081c07210951452007064007500c0c4a08040c0401d041803114101d4445682d00b003d04a90f0b80c1d012240c410008505c11909030098100f014412401c00386480791000540d840103c41c1114028030004030b081c004801d407407054036004620750030416480800c0e1203025001024515402c5000000001c0c1a08 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 896941339 1250 896940089 896940091
    0xc01060816060f0e040906060503190b0a09050c09090a0b07050301150305010819020a031406101d010317120405010b040c03151a0f04140906040504050c1017 69
    0x10000040c40312003019180c42a4403070740ca800c50420000d03003510308a0071035000f42140304010310980e0006005d51090500c0700080c64960000d0b0350501680c081c2e1022606018120401c0a000e0103030b1051f01d446810000c4200d8660317540c01080e41d00280c0d042c501c51f161105600e03510060301001c2c0c03100685241c0d1242c46013442255030f8000300704c002c80180401d031501e24140b8076a6400c2c0c20200710715410402181c0d0303541e020241070b08480c02005140e108540718856000000d5501866840080381300781c5040f0b84401c011900c12503141c52604e000100003614110061062405403540b20307841c0d0a549404c0d18203000d04031007e0042c0d0302040304008609041c4001442517000d4000018200c0940c0c041009440350401030340101410720104000a00002d0030007021a00003c02c0420070300d940408420042c014070303620742c0b41c81401203000034050a242d020314912400c21030708142d80da900d6108000c11200300f034030301400c207510808001a01e4201955098007440701403d15a1400803054a8000c503440 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 896942446 1107 896941339 896941349
    0x15050301090c151818050906010f1a090904060c03060b1215030c03100902190e0402010c150f061532090406031a0a020903031e0c0106 59
    0x74043e1031580300d03400d580c0201c4c0f51907580d606840218464001c02c44a6928181b000007145000c0c0410030a0584000217414a03405051002030401a406002c0140e0022020403541c211561121403080c03160f440b40c00003250501002d0b034014180c408a5000d141c0342d00d018031040424032850480203602c4136094008807110b4040d03400003803402821524080e0076000d003800c202121001ca80043ca145d40c001d0712900e601c40c070520f051601000709446903001f1000c0520101340107610a640401b07401d4050714408528494402d5508100c80c0c203182801c00a95454004000d40a0305041001d071101c81818003215014104100d40c0700e50b00c1c524034600c600c0c3d031800d4840c0c106941d68000d60342402400380081201646903d80103c4200001e64135001c82c044003400108401014000c03201c818501a01450514008241140181d501d02d400d4142803a8188540c85180101740b0644000300 = true := by decide +kernel

theorem cover : BRFrame.Cov 896762589 896942446 := by
  have h0 := BRFrame.cov_init 896762589
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896762589 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 896762589 ≤ n) (h2 : n < 896942446) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
