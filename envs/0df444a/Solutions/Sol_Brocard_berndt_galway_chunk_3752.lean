-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3752
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:34:32.087396+00:00
-- url     : https://prove2.me/submissions/ad24c6c7-6852-4ffa-bf2d-581bce131ba1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 674640287 ≤ n < 674820143 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 674641537 1250 674640287 674640289
    0x1103010c0c0b0c0403050a03030f050609010b0901180504020c0703111c11010c08070f051501150810050301141f05060f0903100e0d023711040609050a0e0a02 69
    0x10701d44604010b0a645030400010f200459104101c40143d41c00c54219107c510091030b004003d40801c0461410321400c0901007080303800c0c100c110303505955003101140e0600c07a42000440d5540e070201858904d052101c90000f0705629544001e04011a4141c0500351050a40c03c100d4101103280341d5550050358008880103d4401c4090440160340d800101032a1128078440101d0303d0401c4501e0280001c000080c072642000001030250030058401c800f601d01c0294a4110322600c81400d00c00d071842181c8240d503680d50700d880760b88001e50040482c403610315040e0322600407034216001e030403500b61074204450a000341c0144180f9500d80007950005040507450074480030501c039000b00d80700c510440303002141210f815074050140c1d5010f080000c104006100050140b9503642c03040c0101c00001d402220700d44014580c2c10348007030541440c55482c5003845d80d20003851600d041c0d801c41040d940f50051003032004d85907889004202c000c210300380300070445061070301c4500110381c4071301300c100f0f0b8039442844d0300401 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 674642787 1250 674641537 674641547
    0x151808030f040b070c181a090603061302010309150c14030705091c0f0803060f030f070510050c1b011b050c011d0604150e0303160b070c1505041103010c 67
    0x40d0303044501c0c116201d031303040d140850100029400019280211050f0003001541e980c0c08004008000303408040d00310340c94020300800450a90b02d140d016082130002540900300e40b022401068811b1500003001400c40c2c403039080740000034080d0b5403030640700c0c2070050b181c940c40340780c580110b6a4074a00707a05d141002c260151003031041e102060701580350179000c2905c944d201d01444000341e81040441803c4502c600d00500d040d4011500701e4415607100c0311041d4103003400948215040250402032030003504220400c4031343c10108200340c00300407003003005c0c200468041c09048201f0440114400d040002c490000d40f1600200b2403400d07060300e210100d400814800640884040c40c2820640d1510030030307031008032224941240c01d64200400081c0040c10032100102d58861a001c1c0c0d032401c0c0d0003510082010f031a403003a52200c0d00c014030002c40400100d04034081040d00600c00782440540b982050342c504909004403401203036080e13910005c10080c4182100c1006c1000c800b280204101100c01c200030340 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 674644037 1250 674642787 674642789
    0x723070320060414012d02090f060a081501142a031b0607050301081b0d0f050a0b0a0c020d030209040603021f11060609010e04020406151808030f04 65
    0x8001c03024800d210110000d03010110040201010b40704103141504000e51503800e64100d030b2401d90b1902050b56101400a103515290f54600a22010f40c6058154041e000c3d41012110a40c80710741c9040d042c04c1c2c1d6035440f0007003c00e4a0710f038590038464500036050124124140341c0c0d250500a8180c3c032062448980e01c12104000446400c0b1510341d4000c9100c41911800c0310b02d4090640301c0002d61120081d40440503101140d0684215100d965913580c00303d5060000b0300c18108154006022007503104803195a0700c030508006095000d0041c099200d024241e003914205689540020820606001821f0345090344006209400c2c040340803410802596500414107c804055022611035001c3e918ce0304124000d54008000154202107080d82c046e40c0b000c52401c030808a144542e81e6241030307601250040c82084024043c4046070f180c981a0000444024400c076406075503038201041c0301290040b004110740791a550b50070380b4400d040e940132480c40a0341040400da40107000c0ca011100c60001110 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 674645287 1250 674644037 674644043
    0xa080f060a06050a120605212109100e041103040302010c0807200a0206030406050f16020715030f0509060718030b1315020c0309040f091104020c030c0a0605072307 72
    0x24821002c05d20154000c014075004507502c803039045025105556011403c5403120026000d0f1001c84001c1c04088003010f468144102c1a41001e20000200786010a8821200e0209003000000000ca0300c0009044440d006850448103101000f44400d040d424403c100c0040d8840c140705095040c459409051b2420710070f49001182001d200180845030240300c05440755a001e0040c50f100d003481d1030144098141100d50070180b021290004030140c4007030342d40980310399a58000d0181e0324144035200440050f0014060306251325a0b1042090196078401e551068014601070705050500036002012050019040999600004001c1c0f022801041903690040008180d020071440340e490301c44c100d0964440b01030a0310384045141206a0002300c000c00c45000d048408000e0305d000e2140c1b030300440c3d0007120081e201000e5544200d609090a60044c40301c4070b003030011203003400c644603075407854207600000480344140c61706c013400071040c1c2190420001d205040f084c11305d01a810300c42c2c640c242c02a2103001d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 674646537 1250 674645287 674645297
    0x90204081606020d1d012105040b22061503020303070302011a1212030601140d090c270504060f0c030f06090c020319091a070218070c02012001020a080f060a06050a 72
    0x2480e2640e00030300145140011030341652905a11f040140c0f4003c05080340c040c1c070072000040000d89032910b041104040100281540042c040c09034031400c005080315064072088494000c80840980c2d01000a04540c0f03100b50b0003c02c1c9501d00607030b149030703410030030407124000d00c04100d2660280c1c001244508961100c01e2076203442e69a8600126007000c034402d8030f4006000b000415440d124000c0e041045180e00420702103e580c1d5480c4115507000b0340540039210a80e442c0d1000c036078081d000c0d404c80c54015001e414003141c038600c080441008c07a205040c8440120f0381d1500100703149881c5020700c9006294445040203940c1d480700d4003944030710411003109030001c42280420340c0d450154082c070004c0e0005029002a00484480c1b00000341d00a01050f40310f80000c88028001d04004020180700d8a881d958141080000d0350055664200740c81c0c902c115880c0045482d002004244060491221550340c1c0c912141003610404c60402d9018141901070904a2001d10000c2c3d00b010407208082101e00c0c0c4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 674647787 1250 674646537 674646587
    0xa0e0402090312031801050903070210080403090527150603011503091a040201110d0905120102042301110c0d11040e151f0e010915090204081606020d 66
    0xe04103c1a2407000c20780350404810700009141e40078119000304041c60081200c1e8070380d142410768a00440100a50008148891000f581e00c59000c0c0c3c0d400c14420f09140d44030680b26000250010080c040b24903082e56039290103840c8900c55604142c1040020a51050240031032001c07860a01c014040d403500010100c4004810714441c2d800100ca594101c070004a9203a17030495552032000054401741e0026100d900c2540c0c036501c0228140541c807000b51902c1403580d19101c140990000d00300c00d58403040d50709110002d482d080a10701c02014945041d02444c13403003080800541440520340d4181c03003991140340460041e40341c00b0135800300950012004810300342c800000a0150502c02016509402009940c107070303042d204a4010300038502c00084e1200100f14601d64281b00c20345200d0340c006c2a10300e0004006180541e0301c44c1440034114405072032600d03120511442a0391060b07201d2640390b4420740e4100c004a40300f44650018000c90700c00342c01d01652a00700103240b44c0b1420122000c141c00ca0f20 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 674649037 1250 674647787 674647789
    0xb01020307080f04061202030609181e0c030d0503040506061909090b0106030b0f03070909051c020706031104080a060b04060801110301051c0308040809031905010e0709020a0e040209 80
    0x800e035810740b58040308850f03690750f405034181041c0d041440340e803020071003498000f6000ca02c2c1c0d000b0b0b24856100940081000d64454540c030100640d0b1280d809818010318065007402c4d03075050995511b500405000b0070b00421035105040c9080ba0160741c0c1070800030144203100005401094107500a40301700c54082941d4000c0b103921042c0c400300c2d840040120701d0721901000304611190300d1812940b807030700c0401c0240118010b2040f201041d2052075850381011006224512280d8400400d5034000c80031036003014114442c2d00101020203202d00c2c0581c3c02103108000307c40d1316002c4c502c3c034010480c440a040ca458040d4a923500c14603040010403003601c485003401b0507180c0781e2049004104400080c000d20102c10080ca242e40d1080c050580a03c0046004a06424046000c00321706507040e950403007d6616030b2600c00720341d0410482d455242c002c500c01d07054182d115100d038030083c40c0900000a8400c6140b084507140c803000da03000398841e50050001c000c00a820500c01e0f40c40c0e520a95004d40d032203402c10 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 674650287 1250 674649037 674649043
    0x6070f1112060703050108010e030a1d10020319022407021609090c05030105070c15090b150301050a0506130c020f0a031e030204030c23130e1501030b0a0b0102 70
    0x803080e9088000040a03151960001404501a40b6507403000c00440e620380e43d400f03081c0c03041c0408014042d8410440311030014400c08407944600b694a1901c071904444000007040344040101d10001a4400320340544100301c04402d00740b00c1e08460004010311480ba4244214210b885010f80c0c0c000002d07040040c4486009001001001480e00a4010807546403040300c0010321f0005010740f041c2c050401301107460b00303051003980d004281a80340e60b1840c0e409580c1e240342c0c07210231f00b40018040b6254503981002070041c880c1c1c03600030400e10003094580e10100050608598004141e00146424001400317090f4540364000d00505420030004504030f6404001603140c031700005c1a4041d02c1c45021448014142c3c40029035020b008084404543d0040c0303001d00320240e01841c040178025403d00131003003041c203400b01080a480a90100b4403880c11007200c00154950560124034201c0c181c40d4001d21000344018488044005a01c0119030701e15411900d03600080c0d10b0040c106503c16a031131031400a070303a00030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 674651537 1250 674650287 674650313
    0x103020903010c0201150f081b150408060a180b07050307020c0913020a060f0504091503080d0e1e0c120a0b041401150503100903050d060803040e0606030606070f 71
    0x94020b100f140c0700e0f000000d0080c9950344020a0681c407000001c180820380d42c0480e800c88040300020600e441d41d0384450b500d40d00444d100568132041c0303281d40c0d01d4406c1c1000041c100400d02c8101408075442c144044209480d1070054041d0f2400640300c500d8005412802083d80000c06803400380d482e82c4e10b15506901e881115140d4a0380702e4109420010004084004400f00c9807003513800200050b030f11002a00c2d035145501c561008520140000e102075041603000c60810400d03241a000036698036154019290300c191040705c1c4150715850481da000008002e04908110040003040c90b18014000c41a1254800d4180c1e80c81820700300d0a9440d031000400c841002503820075200c15943c182490541a105900b403043d10540d420100f444c8100503c000d80340003140c0011340034013900322040100900604014408074203101c0c1c14000309032270050a120344800f6156a0b002940c1d2503080c0b030588901400001c0000e4860385c4104100031132900c030312041c0c4201c1c6600c40da01200c80442c1c2d10f00840f8903194 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 674652787 1250 674651537 674651539
    0x10b010e011b240e1203010501020d05070f080412260403021201060b0c0609010605040c090b0c1015170c0105161e060f05160f0e0a09110702010906082401030209 71
    0x800c1010005001013944034010504d04501220f072404d01120340001107000922400d809a049221250310090265000340900c0d13201e000503022403041903503040e0f41900b1641007003001d01030410b0b01e0810001c0410304080c4415032060300c100d072603003402080300c050700c104d000080c0030b00740401d000e0030080001d401c40d10103403140f501101d44130910b5000b01590b03001c0031910001030b5800d02d00000340c0d81c2401d10558694840e11390300e01d550281401304010040d40629903098051048441411761007160b80310707200900c2036503d17030f540e000d0b450030031201000c0c0030003105200d007500300382d01d0a03140e07a8200040320308603d44003a07584107502160510f00c80d581c400850b5141030360916840303070042080d140d00c030f10072031000900304200782c1c1ca90903c4130340300e64095840700004ca92002e008180043c000d184118489200402d4000e045444c0d000c0001600c01d4092240303e103203004186c0301304560300312200f28007400203132400416a107414161001150129a508084101e00d40031001150b40320390100c0b444110 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 674654037 1250 674652787 674652833
    0x80c0d090804091407170c030a180b0702160906080615010c050d0e0a061b03080a09080408010606023003060d02182202241603030e010b010e011b 64
    0x72a042a8244d440f4110f50300c070006502003500001d4140101c681500901c1d5000e0700c3c1d4119035030300080c1401000c01c03c0c0c03a1001c24542400400c0050001e280b142d02c0303034800d80e0281003510110a20f8070300e502d0050300072142c424140001403111a800040c400d62041c00010240114203000780181d51810340c00c034000c1d18501544100c03414058000102130005001518031502803503540b0011590542070100c20400c50000310603010201c4c2c0b0030036445400440301c010000f40e000903541c03a002503a010768403480303842c1d444a0040050344c0d010b00a1300c40c152040d6042004884404000b984040801c2c18640c40523080403010400c2905da4100d03103980c03558040c200c503c04040342d0030f00010241c41210030704000d610250961410280016403500303600e6001e000448000390070b83c0d0080c2a030040368000101c5641c240483d0541a2850800e144864001e46001441c0c2c52010329850070348922942050500146e040b4403041a68011a2304482c42844442007141c01428075020340840804100113038842 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 674655287 1250 674654037 674654051
    0xe0f040603080d0b010e0411090409080c0703060b0f01030506090a020309030930030432030a1b0605070b15010c020406090c0e180105090a140412080601080c0d09080409 74
    0x300e0103501c1115140006d803038001c0407401c000d082009403058946d2440721001c05005940803400c02c3c3d001440021b101c1d130259820003030796540071881c2c100180d0081e100c1c16150701e142490750622a00d2404c00d8078082c40c00744140d1902c0b00108440e030b0f4024004540f180d41c0000000c040000610076590302c8980100814200b0443d2466011004d20040c3c11190600207a440700c1090307800042101c1c01c80b181314540007105043c1e1160f0b4550f180c000c161040e40b28244040d112a5541d00317001000380c592094035608210640da0491031901c0c0c1143e0401c0050000c104410404181c10541e007a622000f0380410015001004004070b5459206000094001d4100302010800504a4000c840c495015070f48100050740200300300420402200c0d682c2c46110895001031025003040c0030038a13401054040082201260201d07541e60302c207170403107050350030906000c40000c03440e0f07002030144c2d001602480e108115040c02c03804000544510810b0160155646d8940c804200041080d94010501340004200070 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 674656537 1250 674655287 674655307
    0x1060905030d230904020f04091b0207050f04020c0c0928052203050418060302041d0705221a011e0806010c060b060c07030212010c0e0f04060308 64
    0x114095014a5109000e00c0210751030710352180e0078103280e40700ca40440380121600e1803900300f8560302ca0703009684c01507000c010041440c901c0e48020b000800100b140041c00035042c0c044c035401c0d00b80b20030078441190031419082241e90f03205a030a4408a508640069450f9401646c0514248402c030006070050242c504008003031010100180341581020203000b4074181d83e00b104e1080300c10841e0000103a0382185010021880d01ca038061030300b00c0c400e0819503d066140c16050b010b2140c6000c600100580302d40050003103003446d001d501031840f207251403051a444949201c0361504c01c3d50003000d0050304500161a1050b00d01c0340ca140d071641c2664010010040750a111004034240c1003a040d010a920030601c2e02d242c0181c0001090500069980107803d80315000111b4401c5c07455071041d1100d0b82c43e1700c00b00701c150760303000010413052250310000d0a400d071952046c04641d0b80d06440e04892070349405044492a80c2012195400820407591141031a040e04001001046140c00c0a481c03d10086000005 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 674657787 1250 674656537 674656547
    0x9070c020a170330040c140409080d0e031909090c020a05100f110a1d0906030c120a0501060305071a28031410030c1e2c0106 55
    0x154500036110212500c1d110074465040e11010a94000c080d8010040c601c80d4070f4581412422286101c00104140d04d02c02031003601d00b24040e2000c0e0f03150140c841c0f0420119001880d15220040300b0b40d014050000c8a4449107114000d40614800103502e0f43c440c205204001c4c0100c4600821031200714109a00000f0b00a002c1d0a4502030140ca45180c0318a09521500020b12030110540c0403004001408010701d60001a00021070703c805017944807a100f00400c01032401400360081e4070ba441c1c03543d96400d240b0342001e24030707000d4486000b05608400d0000541700416500340038030f02682c8079400703600301900b0b00e0b103009081d01d405821540380c00c0000c0108900421180c085500100540300b5284500304184854481d113050b1181c00c03000c1c01d21003008511620161140030202d42400684c3c0000686800401d64080303e1146845c04031820a2080140040710301000e4607021805200d84541071844a2000149004000d8000c400f10600340a880f11980200740300303841100140b080756980e00b40509 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 674659037 1250 674657787 674657807
    0x60c0a30081305150c0c010609060b0703050a11031b1507020304140d020a0801020c0d110325050d0503100801020f04050d0f080c01050a0b090f0f07030213170f0706020c1c020907 78
    0x194550800c1d0f00012609c1260190a042d00e0101900c0303071500f1a1980d003501d440c2e100041140c14000030b101c3e24108401d007813000d0416100c80140302d100503000c000700c00c3d040950681650f0700600c0303450140198583d000040d1801e442412140880320101c180000304c4e0f00c1c0c1490070007580035400d4000420500c0064002e03203070003152807041700d102c00e00503007080c0e030480a039032002d200a900500140c104400000c020000701c801c4810040b0b4510708503165181030801030448a404144000140107501c1c42d041010300003044184c00860a240c0c5902030300895201c0c0340300361880b400c9010070800500903090756402d403113030780050015590040e80700480d02a003000c89448035500c1c5409030100349400c14940c2c1921442048800504603076610038500c1d50f480d400381540c0304040c3d00f80026003070240c0c080c02e480040c2016070f50001048040b40c80380c51a0000c9203a24035001d400400c001c0012075000598408002002c6904451302104810f00c500720703406448010754003214100601c083c40d0340000f85c0700c1d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 674660287 1250 674659037 674659057
    0x171608161b0c0602062212050d0f15080703030504152006010305070b040510030e0c0a080604020f0d080a030506010e040207030807110105070f03050402060c0a30081305150c 76
    0x40d1041d0340704210703945000d685024542040b410a00c0c4440001e205003124900e0104909040b41000d8181270010211901c0c0305072146495500c0f4825003c0c0040b44070b00a00a1030044002c020442c11954001c14078010342c4a511060901100228507542c09035540c160340716454900070344050842414607540e0002803009981ca0301a0f200c01188103000c8400f1101030702c03005045281100807202e0114020684640a03640b24003800340501d440d9a140c102c1a80100b1000009052600f80750040002c2200100f24561103a0030844058000554980c00c0c0d034041082030a0011305907854070b0060340d03000680101d41d40d0140c80014100209504100402d0142d04541e4849044200c400700b21401c03907106540403404a20841003a4020501c20707080246e000b48064041e60815960381180c3d844c00c0c83d480000c6030040010300b00c81003480a10700d1040d000302d100c2002c425803420240301c007400c001c0014000d00b0301807841d20801001c3c4072040026006c01581030360003400f07500e005101c401c03458004554031 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 674661537 1250 674660287 674660293
    0x1003050f03031801050714130302120a0201390c0506040f060305070e091f090203010803031609060e010c05010e0f010c020d0e03031b0708010c171608161b0c0602 71
    0x11000d10007052040030b1060340e880d02c034070074403010003128901e454002800b23100c2100d022010220060711003411041c07002005200600745001d00d880050841c0246803100014092101549036107103a2680f00c103841c92688480302541c900e158200003189544035045141c0140e40018000b90900c16180c403602150004e030b48c00c1203da2030b00070080300d61551501c105640f0803940c0c0081071501100b10a946140c4d0490110f00782c18507581c1100304c007aa08241d1110b0041d40001c020003190180342c0405100c80f4403986040c9640c0c03030905001821070195411418104415683c42004000095200b0810b0022080c22101410200d44050340a0084001c1038401401180d103102c10440c010501c40214020080c040c60400c51406060313a410310300b00b81c008450b4404c0d0741340002c0c054803e10491603151041d9031001120140440c1039201d855001d4060b81030141c0701c00050b1b0625900641c20354100034146141e0404410f10300003116004020111118601351220100e0100300c2d007038002a0803981c0c0c6400ba = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 674662787 1250 674661537 674661571
    0xc1712060105070203100e21090301150b0301034d030a05060a0f0603020901030506060a0527040819051207020f1902031f15090c0203121003050f0303 66
    0x111103034020000300a4055120b241d0a003006c4419801803544402507004841e03080103400b980c016090740d00b164188181c60b001500c2041810280a8080d5444541c2c000010a82ca081f002c0c004034030052002a002c03c14241c50b000403c85200c2d1020700d100c440c0c02012211014048000c5981c80d06003c0b60486050680c80280e69801c021525403034040d0001b003e040b9940d40c8841401c058070f00b00c412110301c03a03520f070404001699040e114502950041005000ea450014180082058a90001441085000c03864191071160703410211000314140076802291702c0701c1c40c200c5403500503900c1e8104151031480620b0079a6512101038103440000400c2a0030540701e2220903038407140f08420350f828039001401c0701c03d00c9007403600391003078034620180494902ea5500403001c515205500e8041d18419115241c101c590002684210041c05000004111180350107501030758900c29841c182a11180420014030450000d07802c0300011a0800143c03a01e042989604036107942c0102c8401961400c4885 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 674664037 1250 674662787 674662789
    0x81612090501020c0315060d0b04140f01021213060b040221060603040c260106090f0e0d211404050303180a030806011409100f090e040c0311010c171206 67
    0x2e41482d00030018015040402c206c0c58810010a0024000390700404a980c800703001841da884850b209d140280450611018002002404e000d840305134044242e00501c14aa842501244115040b60345492026803403043d914040024107003240d0143e60103803010a0301540050141d80003800ca554400c42e490f6540c0e240c0041040501042c0c5028000c481c1032402031006c1104408081c120b04005441d02100c1074002040600f5150580c10109030a07880c0c02c8000600003c0f405220f401c0001c58014044607911540001d02d6461109400e1189015021400d045260903900584082c1c031003608c14000d40c079090600f5941c2398000d0f40d000300e03c40c9141c41ca903144c0d0701c8046440c13501e5a43c10750702c643c0c00c0c1d00d4071401121504200307000902c3d001c90411862420382e96500c1d04210806440e11440d85180c080c00000c0d246440d00d91065082441d03007400c11000411014894055951107441032003100c2c4440d004035044146040020308411200c0300c40810158864042d0034941e6880341c44407160b9403060 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 674665287 1250 674664037 674664043
    0x80a0f1d0123010b030c13030309030c050618190902041203170c0a1d030f0d03060609060504050409081e030901150b0714010b06130f3008161209050102 67
    0x30b001c4445461201c0014802003140300002d40d000070804000c40d081c40c00c0500b50b01011600d80e88220081200030300308000300004a0540320003440100d40c0341d03046c4200325442c400d21080c0c52106a201c1c04004504050b10b01c1003485c1c80703001c0d102c3d084045481d5600d600401c20f0217a0084c0c03040d40440d840000f03c4406a4a05160310b00c038200f20602d060401207900000d4038010030703070146440b0881090351484460384003000000e2a43d00520001d1191914480001d0102c0310190010820000901c106114844d000710448003140d1080d070f8001f442c9016402c00040f035009034529800030900244840c0a10701044000d140242140402085041d102100d64400980f5070320440d009203c0501c44034004c41c40507070711040c01c030a00000114200c010700380028241e41c8461041a00d8551000e001e21044404144040103414400300358182d001c00408842100720000124103500700b46101583c0c20849090161040c00d56028a0585014401c0c1742188c660304001d145103001441389040080c06606c00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 674666537 1250 674665287 674665331
    0x11040506040e0714010e04140f0c0c0a140a0b130c080114010302060319020307020307030e09070c02090405010209040501030309090f141801020705030a080115020d0f080a0f1d01 78
    0x12030014000705280000b289200013030302d0000c9041c46074031010000e540c1c665014030464140c0300185854681b0f001c00c8025524070000c1c0000301c3d01d100900012289460000310b8800e040d41141280342d50b492070182c010f1501440060007000480f1440c02e110701c410039048128502c80c81002040704185d114040b46007296040c1703825404412907000100b0141c2880740c011604981c004880071081103c4502c00c0c0d0683e841602c5c1030005a00004500c020705510604d214050354046130303510f115041c0728000500f640d0b904080030344626606000718003000403d504480300804090001e0009603902d0401401c1d4103610312411803040c0c104640c1c00c880c100984104608151003050000c12a1180d807040f00b40e0000c56040c007d10b9641c204490380115004202601c1c0919103962201115030500440f000600c4a08540ca420365001d801c110314101e03003210b007046200c04c19141403036965440d8940b1030301400f40704542c0c080082c54840c044414603284000e903240502500024000308211030340310b0180e0600 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 674667787 1250 674666537 674666561
    0x19030b01081e0601050c03090d080d24151106010e01171614010201110313063c0605090712050601020c0a1a09091302090f040b1315091104050604 64
    0x150b80021a41d6018801030102c6641c10303000c40b42814101000b0960154200c0c02c140c1c2c000601280c04903c410541c014060210310b5071320403800c0540100c10b16000005d050144403c5480030040408000c2c1c0300e002130031210f140950031a0209d5030744024a42ca5030000380600b100015464480102007540081c25911010b0051442c00aa900e000d01084020a144030054110754a40703411142096241c1c4c05180a5803100004820141300d91400008542940074101070003549641c404461078101c8480901903094a88400d1880042401e207030010440c94021907444100da0050029445d40314940d4a250281484104103586540d030043e41e0328004034003901c1d0300041050007445602c0c1c001200900c041015500c0030b0a04984000080381a03e040320f614011242d070603007010561400300b100390b40000300749000c00014106034450a41c8244000d10400a103007029030103c003003040c0c10243c0000020300c0c0c001002039194a1903d000c0346c10f140054203215505107404555a482c04e03105840544072 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 674669037 1250 674667787 674667841
    0x525030e061e1303120e01050a201204060f0513030e0405090d140d0603051c050a0e040515031002090910050904030f0908070b1903060f170319030b0108 67
    0x515402c0512001807510f9044007085a48604441002c90600450203080020800840c091408884000884455040c506030380340340070540040c071541000464a01060300c0381c0d001c0c415074a03130030325402800c0041c2c005624a17203440304102c0c0c00070000c0e15118601d03200780e8071200c02c40318100030403064030780aa8148196402a414a14800380154403040e845480011440c0c1060b56140882c0104e03070b030591041d42c20741c1004243c0704008264040107010440c442c20300c00c1c24000d14110040c400c034404501c850050703680e140400d24594103490034685d000001021110404808a82280603411100f80203015503498008500c41040d10741020090b500c014002c521641c2e01d43d101140c0c40c0c0311401e2500c013404500071020038032600901c2114054210491050f981c0e1842034036400303000703004100d4407003058903110080c003a00b80100c0c82c0e00f0480c5c9410f403601000b503a0000105043d0320a0310908a581c020541c4103440c0c1c2034158104440310b01c0c090321410000c0e85d44005400c0c6003c007050a01ca4801 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 674670287 1250 674669037 674669041
    0xb060426061006110f0706020c1801080307080702130f0b10020601080d0e1503040c0608180706080a06090e0c030c330702090403021b06040e0a0525030e061e 69
    0x2c0e00c92264204c00345203100840e10074013030050b121401d203c00c0c1d0b004000182c10410102001d410400c480b50032441440c81c9107035240d85064420f5031070b40201c030002401d590700045c540c2d0a6546038094031113654024002005034a16020f05207008186c6903a041c1d018040561000b0320351800480e1142c100d171524030140c402c0300d048010899040e101da95045501c8000c80e0309500b40500c15002451042c0c0c45070681110a03410702901910860006100c00300059000d802c0800d03514020900c0d004a130964200035619894458459000d00704541140590526040820158145c006081400c90809806503590400000240804100c5011087c585c2d10120080030581d01010540700c8021042704540034106246a800100380100640702903005901c601c0391003c551420007500325846401310780c098a0145008188640c800004240343e103c551390340300207200802c91011440d007260030340b100384140b1190554007070002c05400404c0d080700d2060b80000b40c0302d60300c90700f251101116410030010302ea0b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 674671537 1250 674670287 674670299
    0xf261003052e0b15030c0913050103020f12011805010f0b101b23100c1b030305060f270106090302060702120f072c070e10030b0604260610 61
    0x141c0f40c00307214180c0001a4007041e44030751072204007650003000340e29066959241c45104011440c444000000c441c2860140100010f1380c4401c001803600105446840001d2001c8801c107004041e1040001c080440010a2604104040d401000001030b103da0400504003144113224402819840103808541c0c80100c50030180c82d04101604d00510500002162403d13051416003c428090128012070303010504a02c003480d0940540c54400c00c05280000b4026907445482007040510300d805420b01d90f40b0400700b4925220042d0000c0120b1000d0b0035100c0e241118410030243d00042105078910404020000c20058802c40721003044030f400034505814030f400c40c3c01f00000401d13401402d1809200304c440c28480f0100c284000e400811081c100040446103440745001c08513003140380c2c41c4a4000d820104400c01d504000c8104148100361022086d500c0040c2050307009003218040b0550001e00454001240d01c031000038549290003c661420b2120b1207003840c90707507682060350300300001c001985041c088 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 674672787 1250 674671537 674671541
    0x13140705031e0a0f1502130810090228080303090a03080a050603280f05011508010504020306220506010e160e01020a030f09050607050a030305160f261003052e 70
    0x1341c03038005d800713070318055400c190840d0403070780020980502d00e100369104201c0784000740004000e00c21010740500c00d111a41c5d0005000c142084562180d20f0b2070713100c501e042c040c094a060809000721a048030313a80d0a10408955890070845400c4001400b050005a5003c1d000c0c010340703024800180c014065008040500220581754403440d0400350080d80c0f64002003449030b4400a955405800000740c0754412841e000b4000c07010707801c0604141c1c140014030005840000303116074411400c50002c00040000100c550760092612400b9000d4411440049051406941d10500810410140075108802014140c58001c0600c0e038850158010f040b000e40030900440902c00c10b0f041924001c81c0050710303080007440c150801141a03603281c5c4128408010150588645600680003080c4c02c444420440b4005103c440c04079900d0003081201381c80102d40800c50084406203880c0c02d19608440e2030845001e003884001f500c0b056820740306003003030900030010b2025901182101e6001c3c0001c1042410001c0c40 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 674674037 1250 674672787 674672813
    0x200706021b0708120a030f0221011d130f0f050102041401090312140d18020913170d0902090420010f020304090513080f0a08090615040513140705031e0a 67
    0x205151f2a950f8800a2192600c02421801c07104400b02c00c45401c040411111088143c101c907038080203001030145d10381400c1c029142c0c030034952540c0290304100c1d80380440d0b40300f01441c001040d40074540001c2c41040070640280050b140b40ca8070001800589400448200c00306100c00b418900910742d041c40020310810300802401300302c0028626101c001c2040305c0483e024142da082d00032100d91148011071030101402074000c1c0c180180203200240381d032502141b4000c1041d020104075000901d422030070394207401102c18143c00405111003031400707003003042403010307213260320076040300d42144e0001590300400306001d0b5000954001d50401e414040f0310f00c010321001d002c01d80c241c010302c0d0110000500d20f034020030038402c044682c103403540c200300c82c05003490001411034269a0400c50400c003c40f20341d03644501c02000d00304d030b010405465081801701010350603000076107260032440300c40119410008403071040303074002e03400c4968074074440081e84411511070100001642118181a001c9059012151 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 674675287 1250 674674037 674674057
    0x30a0e011802040c200106182d09200906033d020409150b0406120f090b01080f1e0607111c0f030b030a0203070504200706021b070812 59
    0x290b4000d9410743d08601085203004100c40c60380d10307030000780300d00c48103202e60500d448844101402748200c0010341c4081044000850541b084204114906207522500440002500909103685000701c0741000d03184e00c0e42c02109103006540781000309105040c0021040680d00b0402e003c00182c00612103a1820803108140c91303800700a40041c81102140c1c248002c1004000000c0c0c00604801902c1007181071401c10f61100300c0c100000c0c0f00802055070040b44e180019103c0d188009070644d0481a5107008001c84403002c0d110400d00c00001c01d013030f500084c41b003141e00155022500c0d840c120b03440034000e190546541c1906130b004000070076686401b60b01c4c101c1c00c582c0054140c8030050495110011a8290410b102c00010101c1e038401c0f00c01071f01441000d4000301c00303a001c1d0512054a4000c25070303a107124810303140691f85d0f411021100400c4000300200e600c019a40b4035a403520300c2d081400180d0441d0030384100b0700440485821903060006983c50844201c03601414041c0a20360110900d6080800c0705 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 674676537 1250 674675287 674675297
    0xf091403030c03121e09060a0c110f0f100605031c0c051915060602300d021c0501030b01060f030212040b070f050a051608070512030a0e011802040c 65
    0x200c02d280d010b00152010340d255895106251130401c840582d05001503000484c580aa1414003440b40d001180c450340c4450000c1d00490b40d0041004110f0780001d00e132100b40c115000f0000700403107403400400c40c1e01041030000126500014020840da00301c60052040036070580c40406059007000713100260800b0b00c50b584c00d0015500042c1d45840e0f0900010284041003e0a444601d200f040070070350f04d681051515043c00c121203810490081e54034044800d201d522818180410b021025400b18911100c000c0b070031225413034901058020010303400080014604100c4051000800305003403040d0f504807074003c662001035900e4648103480c591141c407401c00c02c140d001c02050700c40400c1c0100448c011407060038034103414034003a00000c041300649088107007088410030416110980c0141903900769000d0b241c903110300d15542c0c50b000025101e0b200b001002c9020b0400d8400b90ba10031117001d0740c03003940c0c0050280090302c1000000c5080364146c50410300d501c03000f41c0c01040942825801b40211a0301d1b8105 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 674677787 1250 674676537 674676547
    0x1a190c0c110a0e040803092802011121091201020703170c0d0614010e0a031101112515140f07060f061401030c140f0322050a0c060f09140303 62
    0x50f100d02008850036131303070301d6000000d10100902c00c0112138020502036400031403c0300c1124407204035942d00c40c0d01904015a68000c0c0d03060035400c0c05030803200c8004064048450400c0284402903800c1011100c1c0f003403065048408034002d06000712441e040d41036a940300800c26040c0351142d0201c0181908404000c140501c0031003410074855440a032084203041d001c171707031000302c001800f50f0700150006015554030316040000801641d520507002d602402c0c10b920300d841c18041c1a14140f500d04508003580d41459140c81310320001c8450071300740d4003202c410702c811186091042d81c078030054540f03040240c0300420058012109040c098500248034100102d0403014554022059030100d821202c40e5000d01c04e1010b20a68251080c081e445156041107000c0c004c2182008000b400342d10510f9111400000c0003c0c800307e10034058034103031161040103544034813840c1081c9540e600141c4044511a0303101001158960180fa06500318040d0703562002c44483c1400b000406060100f0103140e0035100a01c4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 674679037 1250 674677787 674677799
    0x7060c0210050a20062d0105060901030b181008300706051509060a0807050d0201110f030706050a02041203030c030b0a06030509060a0203270a1a190c0c110a 69
    0x10041c400300c03074200e00178452410041802030035140010b06100c1300c070b00c00d1340b000c41c480000c3c4810b50741103030404c071030309a11404894010703006060311502059006e49044031001e00c00302c0324480d02c0d0003598440e440c2c0504946a031000c960b0354041e5000304210880902da003100c440105010030300c0c19121243c64604090403545c2e00780548a00b035940401240e008103581d0b00a0911200c40340e401903003190707400e908070b141019071900c8103c50b001c0e883c016088142114296401a044402060b0405003284c03c4085e0f514130b09a100d40190004450141c245070215000716498000d99082e00c048040b40c1d14448150364080c1c004011045070700c1c0605071a4071151420755580180407000f40b441382c0b40440d551410115041c100304004000d103280c54414010b121001c0f059500c0c82c080d405100c00400301c0c1c031110002d168517103d0300c82c01c000e04c0744010448480d01a100c00361104d0155034401a4101d054600d08140c5054411482c1c500d0005072a0001070004543c1c46002c200403d00d0180c441e026441d1250 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 674680287 1250 674679037 674679077
    0xd0c020304181b0201061d060d08040b070b1006090e040510060906060210050408091e1005070b090a1104020f091302040512030723010f091407060c0210050a 69
    0x840207440c0940c0c546410740740040f660300b20b030081c0c6000e20080003201c0c20000c1d801c040c281c08076101c0c4500d015020000d151615002d03640410710b60049405d603180d80da0f504503c0190703417007007404407202015900801d660f81c40b0050070109030b48194945c941010305101c0c1f51608000f0081055886214110004685c08034a10549028204510012401030f0800c040a49002804120301095500d0101040701194078601964210601254000c1958520066081740b880003820715a0380406030341c0500004641240040c088944101c0c60341c601d594a0100a03501c0d10070307400c40504080042d140300801c078909030b401444d1020b03468030348600304034106010a5407105150030103040d00c0c3d8001780c03d1140b46406190b05641c42d00040042d441c0103195941d20000c4000c40307030085000c1c2d06021881d1112002900208041258000104210455800d00503514031040203a160300380a54800420664480da808850300c07074020707095140c052210081202c031580320303444140030402403034032182000d10340c8 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 674681537 1250 674680287 674680319
    0x509091c20070f06050306030304090c02060a180201020a03080a0906050103050d03050f011404090804031b031101020f15060109030f060c120218040f020d020c0303090c0102030c030d0c020304 84
    0x19a0710700c610300801415811045506192201c001e9029040030415101640c801406407595450001d0b140c1c1ca8400120745903001d0343e0071072084581401445c0300d40b20780c00201d00340b148018032018020340300c150100500803100720300040c0c0160444911240424054080a600401c90881c0020034410715281e04040702c4081c0c02c100e07000c1d0000c00d812a03541e41d040c099290849844c000c1c00c1c0c01035140c00221140c20700c401004c280030325203d50340c4105100016058030000c60f04418034094040741241e0340550080b00f80401c8034246146203a6058079403001403020b031441b03010320003401004040b0f24501c3c5d00440c002c00840c104000e00d84040005204040140d0b2581d10610b00440c0d101c1c4203241c0a0304400315000c6c01c5241e544107101c0c102541ca5080030920206009542c002640c65504200308040e208411b0444141e500005680c82401800801944203074841c4003500c03e0300c00b9003401262a80306040c92100291300c01d00103039011944aa20402c5584014011a0300c0d29940d8400c1030841211 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 674682787 1250 674681537 674681593
    0x81807030b010510030c1b02060f030901020901031d03090409020f12031207080609013c05011710051302070b070e04140106021b03010b06070c08150c04050909 70
    0x78400400890500c2c0c0d4409000d0540f600303043c00b00c2030304910010410600c503c40c10066034101401d10080d5111842240ea0041c0320b11011a030304e150140082e07020750701c03003085513000a203000e14246c0508281d0305109143d24508010750301d4005e0f264100f101a008615082c3d9100c5c0420b0400d980541d200100f10502c0400400a56101e110171004801c0c40301000b07046106000000c0b0401800c1c1d5120360f0843c0c1901c2049002802e104803440750b284145034000c4080c20350f081d5100d400c80c0c1809160707042c14219002640c4911010351a00c1101028240941d80b0480c80041500e0030700052a14084010302035208100050034518162180709805100b51114004920341403005140c03801c2c1809044000051800c2da82c02651403c0b00003540c80c440652032220901c040459100070356030a4100300b81e90a8014103058aa0f11036085c4100040c902c0c1c800d404082c45803041f040200d500b224a6544180e4110084908051070401232002d0624020a069501c0c0948200303a00d207010420002400403072 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 674684037 1250 674682787 674682803
    0xa0b060d171602190b1e070501050705032a1801050c01020315180f16110610062a0b07090b0c010903020601050301090206310e0a0606050f090108180703 67
    0x1441c018046080550000c43c041001088000c5c09000c8983c0c04441c07181901c0c1903000d580f0f0840e0404c1080034001c2420080c4207500301000c0c8001c1c560b00201441c05195000e40c0283c2c000b1100d41d90051290b038400003420844030620082805c0d00c07200400040302c60060402501d0100ca01140508a81c803c9440b501030b10112440d03040c40d42069000d90360007010203a00208031341094800030010fa030000b4503481800801ca9150100385210740444c0c004202014210740e105c0c18002c051420840f0f0314050b0000040d0810288581c0820485c224070780000110035210304030700180c40d01c0c4a4800010100402d00590000000d0204440001007101f8041d0900009410b009850024103200069000e03e100b6814007000c80c0141e600c1004071100c5e0b420f07241c135083e1300241580040b8036401000b00c11650040d012840050b03034655aa01c43ca216044501d810440c994031241c0540b0ba5000d10300014090b02014001501154090550990072140c0481c1e101d164103801046140340160070381049880351 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 674685287 1250 674684037 674684077
    0x9010c030b040203040b1515120405060f13060c0e0a0602011523120109290c031b0c10020a12110f071707060903030b010e01020a0b060d17 61
    0x190303051040105680341202c0030740c83d50034652584244000c000e40ba200181c0c8450100440c5650b407080b50911030848440c0f0b083d1242c6007841e04616802c02181c2c29542400303250001070108054406440c81110344169a01c40b10314940c031031200500704c205c0903606001c46c01e00ea2131825912584044e0003001035900204d402616540d1040e8500242d034040d4504031020b80e02420088043d1030780c0c0d00241c6040c0c0d00d02c6800c0d15009070150140482c04030203401d040c0900154190211401034aa111440c50200701041792170300c0144c00483e100454440904110003080c002c2c0341600d40d0010040c0443d120101c030003076a00000c07210100d901031380c90070001c00c0c1e02c200022018202405564401550035a40d18100f9110f0841c01d1900d1140280080650480c50414a94000350f030007079074006500f062003040380c0c2c03a442c98050020522140450302081072109081055840016201030b00da40c0091045100d07200d101c1032010000203210f01711044134910614521103000e50700600f84070031100418000b40 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 674686537 1250 674685287 674685311
    0x30601120302012003061c0b1f081b040914060a020d0e12070f05030d020c011d064803010e060a0e06010f0c050d03140a060f031103150901 61
    0x541204d079011480034a8034009040329441002600e034460710a8480b0003121480389010b908144441000420003034021050119070300454881032001424102d00d01d1405407680780c0c45544080045480440e0288030300082c1c0942003030740081791494496088803241c501080c81d254140b042c2200ca500300c0d543d01207100d030f1100505000c1d2003138507015440a8207039044102c916001c42e101e880c1014143c450350b44542e10030041704108440003c41e0800d0115120403412000c54080c1141c11400302081c07451000b054410035012030400e016003c260400283c0c0b1080750361100059520381e0740414102200308900848241d05c0500c1c0d00e500780352404280d03a84d810004611042040640154020320032a20f0900c14201d038004010b801c06800d0a20206140c600034040392291030900c0700805078091806514445038144e080f0a5000d4001e140c1881a55200003640d0200c80711031141038a00480c0b40003c10100717096103030301883c0a102400b55003001c14a1440039502000644402140380e644d07501e41014 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 674687787 1250 674686537 674686541
    0x31a031e0c0d0506060613051306080705010509061c061203271a030c16140601060302130b0c0c1206070207090504110909161d060406030206070b0408070203060112030201 75
    0x100c07420884500d42d01c1101a140c0a554480040546010782c10000308912105240001134004001c0200308406410b8801e0340403011340618440c032540c2d0300c95484045410742c00b4000355802c5040243c241030900702c5074030b43c00f401d480f210302d003450415648000109003031289800c0c0d0080f141c082c6d10b511303016400d01e8560205190a1405683e0107200c180b400340104840e089a00e01040c0d445110a41c803511801400601d038031861907040400c40489c0c2020003040303c1a5003200e00002084140c85603130b0b9894906900380e101e40e14142c00034042e030420900030304e00b040002d4040b602110044500300410540403604880d07048248072002d034003c00400c44100e5040040b84060850f0010038026801c007030b902c941c2010b0500743e01d41e00c40d1103220001001c1c1c410400003140c444030075003204664559902003c04102480450219510303100c0c40015040c1d00781801070320226503000d0032142c5000070780d840302c0000300006002101c91080c10411078015035001c00109000c0c00540c0042840ba0981e442e000c0d003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 674689037 1250 674687787 674687803
    0x10e151909060806090c061c0e1911010810060f0210050c07150b0d02040b031504030e01110f0a0605040201050c071d16080402060a050c100207060e031306031a031e 72
    0x41103910002c5c1301c5c034141c5c580d40240c941440d55403041230901c41011182c08050300040401101c0d612805c503410741620344900350128940d0080302c10700380382904a0700460703d0800480314000c1c404074800c010049144030300c00210b02d80c0c104e803065900014046640c0c405031601903071880028030300032540c0030512445080c0c003440d14405403420081d4100359000b01b81000c51803080648110760b10041981e554a003402000d20b403a44034114181c0c540350034038000c1c1c0454058207107540050441a070800d154200003030001e5280c1c00c41c01c01028000d12540c0c41402520f0300620482c10031078184070400c1403031420070012000e0043c1c2403542500c800600d150740b103d044000c0514281c0600c421030504201d07044282a500690150341c81d9544012a00c02500c41d44030352043c00e0154840c2e85818907040d201980a08a034a109210a0100d0030401010f44e0383d0f8020341c00140201d9014050800c2002e0013584180c3d00003640c110401d5007034103440e001a00709249000e24405410003000845102501400007075 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 674690287 1250 674689037 674689051
    0x103031d0a0305250608040f0f02090907090c020c061c0e0d0f0e010e10030b0402250c0b0a02121c2309010c091404062606070503010e151909060806 65
    0x815130030710f0300c0340003031084070041c00180c202c42617409079100f0b000600c1c0d000d00c082c1d034000d80059000d041030042140d50340002c0c070400400b18a040c05c41460b003031010030b00c1d405a40c0018460f07030401c0c1000d03042d0600807260440d01005155130320251071146200f401900102c007140c0c0c40d294024403240001030030004402e840a81040b800c051211603c0d40c4000e10914060210310340000c404c41080301140c002d109100420352101004107a02590401d24810300c00203501c00c0c4509100140e07181c0c0b950b0400d0055806d9040540c108183c046040c0c0b00c04000350803425100e8541701d40280c00118468201c48080c1d10f45054400f540c1035039046540d01c0f16405401413446402004600c0340000014007a030010b004599107950b0320168105180d030782c3e402120207480340303a651507040703615488801700c2e442024000040d1805000000b070b5032103015a00f600e04076954460b5860407aa030f001c4035130701c07076000701220355503c2078030003100c0404260b0203492040503100c000800603000d810308030a98070f05140101b100e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 674691537 1250 674690287 674690353
    0x303090803190e1908010903120b0604170703020604090c081608071803061103041a01140d1406090c0316030c030201050c2b030606020f060103031d0a0305 68
    0x8860140e07040d035078009801c500d480003402c0301100008000e500d16440903500e0807511080442c000d071703040d4002403455200780c958502611017120040c7c1580d03050448964050820700c801c20918203c02d05400c81082c030b820590f200c441d22580003500c1c540198004058007907030740c090142c6940e040b920498006880500526000400c160020514400100360904200709800d00c0040740310303211040c0014603444030050000c40401c001e94400c2e900b044030107031a0781a8507100b20300041174042c422070503511340701424840401d1000030701469003406801102c1c080050300b100c1103841d606000040c0101c1c0902c014050701c030358020402d0b14024402580043c40b6440d0042000002d051110400840e81d080c2403c82c2c032030320242d03400390400e0042e80321031003007504031006803911035045050116200d9240d101040240e4803803008a984030007011701031082c2e500c00c01c018404a03001c4d2514a62443c1124041e8a012100d5804108108802d034812109a8000d0841968070540c2c11f40e000e10512190100e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 674692787 1250 674691537 674691547
    0x20307030b031f0b0f060c0a0209061f0e060c25080f15070201021314090a1a150c0a0803240d03030207080d020301120507080c010c080c010b190303090803 68
    0x2003d1040d4a590600031256075070303402c0c0f001c4c15218009075401902005041e01e40b40da9110000c5611020440b00c100d109071240000039500e45050f0820740c1d031720820f800c3c3d0690743d940e01c2c24043e80c0195190300f400e9400101031008944045040014608490300721440d001c0b030500850750010032061581040e07049130015503600100010004042c401080c0341e42d5044070a86070302109900a20944101501061200b100400c04006030f440c000c540100907540106a555155042001c4410703d0001003030042030110014628a0301d00c2e0800c1c0c1076440c0d400154604a40a032149142881101381107800c040003008000003103540143c1115419014090a0145603019002032480016441c00034149a4007003070100510680c402074400191401c0007c540c1e95846244d005145040d00c4000c460a2084090100d82443c010a2028112038180c4072400314030342c240c0d80c4580703d07000303820000f09030365a83c031050655641d100049500c003007507164065003d03420340c00e0003070010340710303801080050f803013000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 674694037 1250 674692787 674692813
    0x8090301060e13030c170f03160903150207060f0f06050102010e07150f2c030c0103060b0f09060f041d100b0405130b130c02010c082a0c010c0201020307030b03 70
    0x5902e403100f541c5443d14440c102e40a182643c401500301802000c1c0083c0815112074081d0f0820045015803401c0f160031100c4882d0b51811281c080c0d040c00001d00c04501502005502d0015401400c03130f09100d243c000c220096003e0302042140c150030f10750ba0030b0701d072200400c01c240e58081c8030303020082c1b0520014200a43c20030808007220303070003510814104500b80034404d5280d4850160b010129203212311900250b100e00407044004001d6410451082c09958200c030724075800707445110215210720702e629013016083e51251400e03420182c03800d6000700040003030207179540c0d8200051000c0c01e0b010001c0c0d4000003051448084410000307080740c1520201400c14000c0318015401d5034110f400807282000b2103284010744102078003614280d26000001501074010582c0750390484410070110b42e0003048040c905076030888034600182e60861420902ca0a4105041c6400c2c46e2204880741d162081480c1c01e02502c0f8080c21200042e07170f000c006075400b00034803004590600400490710f100314000c0c000c0b100710709 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 674695287 1250 674694037 674694061
    0x80703240608060310020c0105041403070b01090506030a0204050f2a0313080403060c0906020607031406041d0709140a140f090c030d0909060603020a090e070c020d08090301060e 78
    0x4010a001d100390400018036070744d03003000700710007a0036201030035034449160812030780c041c00d0103943c1199a41c40c10380a51140d241d002066a81c21038000c009060145d2030000144000e00d0b0240c405038241c05500c0140700561100d016590080180c82441c81c2030340b40000e80594484400c205148440002c0c0031907000f0782e60800c1c1540d0b000b4000104040003802e49103007060580c4a00e60000b401c8500b002c6251051a40040ea42d20440d40c550302510000d03900d90030200c0c205d907221030f05183d001c846100452400d0034940c4c0301c0c001081c09818011110102040e07828500310041d0f0200d0710070343d100d403254074103100071000c40d5801009221007440515242c0c1c11003000300f140184848580c1c0d081500082442100300400f500002d0054240d8583c50210301c0000e05100c844e01842813020b0070140002400f52091003141c00c01481660343e10f05050410f02c03880c5690f80b000e03014504008045402d00003598403542c420a00b1707849090b0340d56440300c0c00d206041c203440700c0d43d01400002000ac010407090041d21 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 674696537 1250 674695287 674695289
    0x20304080d0e09040308060103060905190c081308070c0b04240816111222050d030c03051321050f0607050405191a0310080a030c03050d09021008070324 67
    0x1d42400406c9030340780e000480040c05298040044c0c10700303020910010450500303003100340f0784600d90140100001c0050a0340d020100b621a4a4252035461070070b000729210030701070050300f07203e0a0171000301656a2854099034102d5040941201d1414400c0c0d409010405061a0005e6450909059515040c8d5601c0d105001141d250b43c1440050072040d9030032482072114280782d049060050707850381310000502641c03240211901d0298011100e000c1001e00d402003022003c6589603a4000b400b03035056608845503041280405d40519080c6800b14100707410081c401da038403001d02d01c40009604a03003011840c00602143c5007100382c00c000244030805500c07100300d4096440c2603a060070b07001c082c91045030040040c0d030b0000a00c00c0b500405044580d00941c011809941440d000034081511442010b0303ea505240c001000701d00462001c3c000207009401801e00c24401560003d03034052581c0101d00c0700d004072009030380010707444420002025050300c18104c44000008000d802100d6011254045900c1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 674697787 1250 674696537 674696543
    0x301090605130c0807080403051204120909050405121312030206060a0e06011e0c0b0a09021807120c030608060712110403030e091003020d0807022d10140a020304080d0e0904 76
    0x140b030002414903010707002b150310303142d03009141441c1860141080111000c84c071628000040d400480051081c040d4020580034580082c0130f040900703221803c500040d80911803015104800d83c3c0300080902c04044240e050601980140845107401c1d020010749901c281c20150b1100014814001e060742c0c8001492207035080b0f02e242480020030301d403050302e14171140742c3c1c002c25421102c000c20030424117580204d038505100755541106d40b0200704105560580c00c84c1c882002442c05803038566034440b581c000a0240c8101c0c1400101da603100c599190800d042120400080b803140d5640040c4451944110300c3e041800e81c40640c00c01d810340c0c0d801080da008004100c1e119442c50b502299280742e1a03040c00004607401048000c9403607030b42c80c1c2145ea0340c2200a040c3e20038217078039240c85012005100d403527042c2e03076466400e2100d860440041010f032000031020542000500c452414402d40020011310f11074009800540d261440c000c2000d103040c020f18030150800c0103010046140f40c42e0898015040f5038 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 674699037 1250 674697787 674697797
    0x1506080f060105310801091203091b0303020105040302060105031204170c19090f0c050702090405011e09020a0b04050315070201090f0602030f06040509100903050903030301090605130c0807 83
    0x1503040048071a40a200307440f030413031804000e84c4d81d10820241204c00480060f1583c08190350754413194a0300322603c2c40c10281808000703100550712640700e6484203090501c605d080c070420032038100403c11a061107810880140c0c1d940c100f40001d045d01040828010b0000300d00a000301801c0d151715000034006d0b0320807030b401c081c09151019403a440c140701c0307801c40010190125480280b03242c0710308508a081d100e561103003442c1841180c6604a1402510174451803502c0705441d06e0714582c28446030020042041d15655038419042c5500301a000d402008406c02000100d4100e03550300400a801c44603500254804500300001c001940b0003140e49160039903990000c0660f0780d6080003d80c09090055401007101c101144503030100840c03079002c2c500a50032810601110b5440c0d405010444130156500c40483d4442030746500c01c0a150707040b0742d0300148245040d0f410304401101003481e5030000e03002041c10700d403a0b56082c06581840c3c03a0180c00200c84100a00c103034500800040c0c203004024120b8002c000c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 674700287 1250 674699037 674699041
    0x3070f05040218282111040e010510180509122b0603060f1808090604120f02030d140301030b0408090d1a070914090709080609030c011506080f 63
    0x3c00c0c00420604280024000c0d541d07455104402c2c00300441d851031140140c41010b48086881c00c0c1046007030110b450004c401341982e800c0d907240d01407001c0320441141d910a4a5813140c0000d05000c3c0980e90152405408621036542094000000c1d04170301c0b101c182c402d034030313200400181030720015240c0c00c0c2d10510403440395101010b0f240c485130701d060810f214010204510008001c41e1456003d8000c0f00d0144008102c0b498020100758280c500c681d01d404603040880354018040b4201400034140002c3c010a15454140c3c0c44c42048001e000100082d2140704c81c40800c1425401e061082903400d21452400103030b1140d03d00305031390f1070740410300010f480030b1802030000d010880110300302c40c8410300c0204240c04905140c0f4015410690044040b40248003120124400d0790150045070141c801c00401d15250300503d001744004242e001382910100071142c0740010f0b11880a0100c90b02403454500956a03c6280b80112400d5540e40e0f0030f40e14942d2000c100821441e5070240340c0c40c0e0091143c1c2806d210f0350f = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 674701537 1250 674700287 674700307
    0x1428090603200f04030f030806040b041803030507020118060e0d02060705120405190605271b0406030602040824220501110c0f06010e01081e01060f0b0702090603070f050402 76
    0x84c0c011600010000196960528207040c1c101032654800d032002c03036061100c000300c1c100b82f2064951494200c42e41250034080300f00000d0080e04031550250312440006010030404100c030403401e041800990390b140d5a00c00284c200d003002c0c0000b1085e02250b000814803403c218400030030a02c9942052281410102c01107020800107212070305a4810038021b040c20b42d801030509400400c01540c5100c0782d1442c1c800d2058940340401c1c02e00301c0581000c8060180300c45d620405110450015444582c010707541c1401000084072840500301415100008211524030000c40d040901c052800b0f44c0e40d044418020080740003508201c410b00e0801d5510814070107aa549030442c00751465041c00c0f5007181c0701003204500303c80d0000d1140070444402003210760340d0740e0790411040c01320428024010b068002c0c00000c11040c0c2c1007002900c0b10880b80000150603a6100020203c414440d00700143e940d00c00542c0c40d05501c0e107a00c0c03644c1c03c24002c401416010340381c02c0c5021a402e69a20031a4080d580124401c902 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 674702787 1250 674701537 674701567
    0x4060513090c050c0c010f02060a0f15083901030f20191b06110403050a03020618031804051308030a050105041d0c01142809060320 58
    0xa140140060040400340e03040a0590f81003400c0044251240d114598283d601c690342c47d40c1c1014140e0003400240d00c485284401900d5284240c052480e03c038076a500c110984010454020121319000e40840c600e020040e0700e00b0101301c070401806032540441c052041070420a10595100242000240b190000c08154003400c0c2803505c000704005420340414a00c9104401071414401c9100d15191030101c801c0156050804400c040791710800320402384000a0565000c0b41c10100843c00003800c2503501e030743c0e00d444d2000110b411801a00868180442d1180c2e4010b5008bd002090014504003114442038007886035000110600c640d403140d0118003488440800e842031681c104104aa0740d141a41c01140546820310640c3c0c0038914006126407030400030095980e039400c0b0003001e00558041e02c0011036416001e88113110703090104101c02e01c078030000c02041c5110041141d000d0124400c500401412202e02540808145402d082e640c4041049003905c03140c80e410440d2400d512010601c4000744 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 674704037 1250 674702787 674702789
    0x90d05070c0e100603050105012f070b030702010c1701030302030711040f021605060f0c03011a0f03130507300507080712110402090a06030504021818060a02090604060513 75
    0x80351060181c00d024212940d0210032064131210346040c407269a8500044940407901003066124003c030340b000740300c07400004ad50582181c800404458581d515001c003620580c0c4283e41c46c0340541e5480c086080c0c03031500101c03442c60102c1d00300020303000d039891a20302139200e11910300014080082c00500208940e60b59108048400d501c85003152240f10300d039003061588046083c1961035214400018501a00c1c080c0b05520480c4800c1e190b50850f4600b5a00400e04c59135455100401281803240c40700e44805003000d94498041d01c01da40d8a04021400c02c1400d182c01600f06009d403608088070a10b00c1c1c01e03c2a124482c070b55456415003a450036504100f4101501504109074034000c07010300041c405445a00e101400e030250b5a0603a018192000300000c900ca1040b0168100e060300c0720800c41980641d01c0316603c640060449011940e0b00f1400c9803400c2002c407134262b5212a03000100061584c1000794950084203690114030705910540002d00c0f07402107106080c00c00400040c800c0d00301d952080050 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 674705287 1250 674704037 674704049
    0xd1113440f0f061b0a0c0c03022205070e010e12250503070f08060705030712090b0702010b04050f04080304020d0c2309060f0405090c150306010f0206090d05070c 71
    0x80701d24030309207949525581c10074401d4280388183d4000c20507141000b10502012078543c0980c40c5460b60030003042d5a0102420b4040c0c502008400d00040540c41c0e0300d078591440c48480a40568451007903102d00c0859202828020400c145400c4003200d99822505994400104864201c0a02d80c0e144010f1703e80441c407801703600c0701c80c124100d464510f1034650320242526011001c3d90742094446a031034290700c40d80d1081d00559400340740844ca10318041c1008640001040c40c10507481c440c404032100649845600c1218105071090802c030700e00d0360a02c101a07070400111070600141c1090005200e2080010344003a000100c0000841d0444d6200c800404526900440303482c40e50f6581d02d016050301c4040c03208146c95002c00d1000c81242e203849510131344a50f42c0101407159190129042c48000c1c0740040000710284075559071003003541d80c2d0003020600c40b600b440c50b1540d24600580014124001c0c42803400c203540c0080203102d14070300c001c200500d40e8080c07071820b031341c4031082820800c8030110f50358060 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 674706537 1250 674705287 674705293
    0x80a0b010c06270f0501110304081c0b030d0810050604032111240f0c0a120e1b0a0503010e0a06050702071d0601230f07080d111344 58
    0x80000c21040c07a00220b58180605d000b004400901d0000002c60710046a00804050041041c600040820401210501c2d0351803c0024120b0310071020900d1f200d004805000400c000c1420070411400c580940c2c2d011300303000d03980d09050130b00e1940c2d03070410801c0074105582d80442d942015003015100c2c21540000f030590300c04440d80d406907000310020805080c2c2001500c0c10141e0006141d511185011500070a600210301c1d26014520100b11404c120302000b0648440d02d81c4c56007024100e08210300c00200171948036150400e0400000c00c0918000717030f40168045d03418103159000301c10300850a00003450b000f0201103095622281c04a0a06005412040c8100751100c2855256193303540481e01c6000c080c2ca5000802c03903580101511000303c0840e54400002c20007185c80314141002c00f45c6061445035100c1c606040041300f070f180c191461001c1d4507640800100c1c05134481040f12003814002c190f200e46402c00590701010404003081101495070301010381c590342600c400324030f08070910612450001c1d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 674707787 1250 674706537 674706611
    0xd02030a0327120206090109020d020d05070b0f0a030515030604030c0f0c1518030b1306060803031510050c0d0e0f12011505030616031d03040303030c080a0b010c06 72
    0x203d00400d0045090360018801c020015100e600148141c210868004100d440440c1080d800c10400c480e14074001c5810b80a0600300140c1110b007040a403414401c034500c59525a20b103000004e00702c0d0b00081c121414011030310000c1c905500c0129803d90000e4151400c00543d103800c1c00d0804001a2000c40100300b190045400a5031035401602c4005080c0a580c07128071442929203856074400d2107010281401e44a100401c5042d07089046d4103c8240c03140304045501c075a0f038800f81d411500100c40c020303424001088065854940014241400d1619041250034204010a4070b9642c204080b190410304c11500d0703c4000079524040e0407004100e005007150815100180c55031701070f04030aa0031400034003440d03402007590714001c20b60910500c4e42c0000502600217010045028000320b2522101000d1290000c401182061000707001a60082d20042100c0c1c0ca1b5a02c000d20503a030003060b90003a02e00d08000410b580c0e910240c41c00f011a0492804075002c0c258040d103583c0311041302c1e030750f107108000451 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 674709037 1250 674707787 674707793
    0x1a090319032c0906010e0d1a1e0f010608150d240b01120f021e1c0204060c021e0d0b0906130f1b05060409090c080d02030a0327 56
    0x103256804600031401a041502d6114107074200d41d0002c0b07502c2da01070640800078070554803c80362051110001003003292154155180e40c91020f03907409880108040880c00c000748490840048906282030749030a0020345041c040c991030922040c041e00b0100200b1002040101c10420b11005226100038800341000d0720916008100114a000c0a1354403174030171a03d14480c610a20803900c2039041038440080459017440180010310420110100c015801e10070319085030260503070032080a00c4c0f23641135030751703020203a80315400c3c0c4100076100c54080740108028040c507940031800c01c0300680d058501e2801015450500c1f0584600c010b070030703a0810500c1c1c0d100c0c028841d6a081940c02020b689003541d50588070421040c03000450110060150306406403440f000070a00000d840300e043c5000040c00d405a220800030b003080e8419840701c0141511070420380144118401c0717002c0180220001004803007804140692240105407001c0306040d0b8852000c00394141c0e0038030401c0751f200000d032210554a0340c1e203 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 674710287 1250 674709037 674709047
    0x907210b070f120c020c040f0e0610090b09100b070c08030a020321012105100903030507020c040606090b0a09050301090501090510090c03080c030c060702010f0b030303011a09031903 80
    0x500c00300700141c0c80c5848000e4150403031013000100303401503014003010500242400098040c90600061680d581c14001800c120180441806500c20f200003640140c54001d0500540d03103072200303592141d41c0480500941008889501c030455408c1c0201e00d840c0d0030281804e034012006580840082c0c040022410b030200c1e400701c000c00398015250348074441c4210020f15400100030034007034070000c07100c0a003681145100400702c0d80c60b203900c20004c5030400d0030031000801c180c0320220000c0b0f0119840d00c080c40b14041d0180160138242d04203940c10840385144ca840100018000d200300d0315a24030000d100e1401c2d501c035849803c0902000340003070060030102e24082c0d0090181a900355503502400c11103111421141c0a0203640369001700390560102e003981c485061951108404452500c002c0010f040d9964040c00410f00c02c0740c094000080116100c1005000e8481e0861018860380040006028002d15003940b050030580510640b0380f1421480301080c0f84c440404c480603105111b40c0203181c100765200c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 674711537 1250 674710287 674710307
    0x12060d1119060912050d030518030406020c15030601120e01060905011e0f080705151903090b06041e09030e150c0705220902040f0204030c0e0105090907210b07 70
    0x1603803003c119a60b19400e0603811000804010000d0300861513010042d07109810540d040485604c81142c1520401125407031039015034801c1c8050b0300099120030207803405503000620324005002441c69440d000b0300007040302900e03082103a12644e40e0003102c400fa540c254031501c090721014904102030750f124170441c00192680440920300021004010401181008080089446139401040b807075080504003d80c2542056402c04421002d1003508081c1000b4890201f0200080d10000b03010380c2e03039080c45081c07008000d24645c01141400c2c002e400120b4814105a0703a280a1000064038510900d800c80c1c000307201659103940f14403c02c150812240114000f440344501c180c0445070980da803001803101c03202c900d401010b00d02d0342c2140c1109074a80142c011200d120310003000000d4401c11502002e00b01e070401c0c0c00c16107034000f00440c1400908c00d01040e45000d4101200c00170420719010718001e50b078004e01e021384000c4400310080e1090b4150350314a13221aa40c0d121804040c0c0b4030342008010002008 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 674712787 1250 674711537 674711549
    0x30601081503070305032a070608061f030203070e0a050a06140d0903020615040b01080f0415110903060c031302060a050f030f06042301170705060a0e01090b12060d1119 74
    0x40d200c4080342e000b620310840c1f6040d944100500010391401809403405103000b4403d580108100046c0c100d541d40b00c001108410300281c07801622418030800013822a0340c2c5071005801015402c2c4c080c0150342d2074050329422200e551800c0020a00c403600d500c8568002e617000004042d0a20004034101b540101da403034400d00c0c0c03d01021404000710310401c0305441204103010f01040840e008200000000c0742c010364043c3c0588045003000c201800c518049506c148060202e039000821921440e20b07052050300d810105421080c0d0039820b1100d88100c020700c034020300030b2107280c0001e0702c07200c1180502d06803020f480b08503c520b83c42c1d1502160251121100b00c0f4001e114920340152642c6010300740c950110b04c440725000b00743c00caa080000003c104120446201d196210b00000001e15035640002058009420b685102c01c0550b50320014010f501e00780c0011311405024003001440c2192000465070200045404900c5100c40d4140510720156030140182c024001c4410201d0200050301d5520407110 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 674714037 1250 674712787 674712817
    0x30708070303140310030b0402041409100e06091002070c0b0f07061803021509010b060c1c081603021c29040207080d090c050a090c0e0109060503060108150307030503 73
    0x8043c80c89401c1072000320350317043d0351501064050000c104d140e0061680207201402c000780789518081d90254441044620421035030016840110f010078038065042041c20304001028a030030455207454a07801c50103414400b8550108464045c408861140f00090501361201691139800c03400c0e6032090b6201d44003c0d1703929810701c20503806c0c0341031a01c5803945258059018140d40c10f100c240120500c500500300c401c0a44d00d0b001d09960700d0399076800901030000401c0040c10319118124528020116090445c01881005020400078800105803171350a150315250042e0b481503214110590317148d426204045681c50324400740189421007c00981481d5108401c1084860620400040e40f02e80c0c54000c0541d1000e0080b200da10100f5000076083c5885201104e8089483d0000708088000d031343d1003010580d8843c8948000320b504100c0c01026401d003032809041850605001030107034400038001d681000000381c0015001440c0040d55401e00341c0090580703d1003646c074149990749402c0f040002d050b4007 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 674715287 1250 674714037 674714057
    0x120a14030c1e121f05060c060405010c03090c270e0d110118140106030203150f09070605031f0906060c06060b07050a0f05120328063002030708070303 66
    0x4880802540c010040d9101c00341c1c0f443e07807040544201c580a4805441d03403183e403181c0100f000e54900c80581010581d02e001010b0b41d140c242000b509640c0c0d5808204281031905e41d480001c104414840401c1c0c030030101000b1078043d030510ba900f1140e0b00c96001c0341141881e0400031f80b4150700129500307030701050300d41d9001c40c20721141120b075080300c0c1c002d240100380b0204030b0414800107a900c400d0009041c050f000001c4c41554a40101e810580241c10f24450084032104001400d1010400f050300300401500401626041a102401a03c4007404150301d02088141088000441071841c2028000c40392060088954984010f000c0718030034641202c119051540100d101060601542c5e2107580000080a00d559180c903124522000b6100c29101d9004d0910060840ca001d203004500451204620310b148e04000000c09136900b4030341d40fa04401508012040004890b4a188000707480050800d40c88000aa007030000f4a542841ca4000c1d094017584e000001c0800c408a510011680030f625010188 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 674716537 1250 674715287 674715337
    0x1e011e111b210601090e10141f120206180d03021e01090507050f010207030b130308091504060b0a0e1005031c050f0a12020c100f090203120a14030c 65
    0x5003038028260301c410791204004001c0170f142d40d0054045182c4072000c0d10b60070ba50034400001a588800c80c0c02108540e03c5082c071801d601c0d00c1080107180c09000010610369420070544602c9614a408080d1007414045402c401d150521828036408a100424151201079280b0f000381d00e50310364041d48501250034001c801c1002c14180581e82055605c0700c0a4405142040c04004080d440c2101c01e904510840c0c6001c40060102d0b030001c0d0254052400c101ea01e0303045031500804154005240d519140c0042d64980505175042d428503400c1940040d001c2054109200414603c584540c0301000c0da0806400b4001070510101c0769a059440c254140e0340c1c010302c4880401d12001c207141407200001c1c4204040c1403907901c3c3c5d0001c5e1002d07107136520341041c0090510041c80c05903000f003d074041580c1c11100650440c01028480c41072003240c0d1807010b204000d1203400107034651082c6641c8100e550400940c820a40d442045254120b00c400c0f44900d4980c1840200d000f400c2e0814003403003a016201142e000f00d8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 674717787 1250 674716537 674716579
    0x2010f020106030b0c0307021903030204050a0b04260c1c050118022b21200703020d061401080f0c01020a0c090207020d0512091e011e111b 61
    0x60381e820100740b004c0c545403d10580c0381588000c144404501408000c4070341c1e148001c81e000c3c0d01d41e0080e41c0268842d0308200c10880a150180c1c41001614010032040140288004203040000004c400c4c2401c090360000c11203082030014200d99074440c00c4000aa000056603150b0441c55038050030003040302e00c0c40036100140d60011004080c2d4131a501403d410300c0c01d5200d05000114038180c500f101b00b4001c083d540d04030044a0075020540c1c80500303c604d003050b40d5021a40349421034640c1180300c660006015041e440701c50501000c1e002d40d031054034503018401c80da0000700c1c41c10840e803031606c0650794038401e180c0c440b4600c6940395200d0088483d1440c0a61000428190003070f00640254106458602c04000079401340b0422a040400280c4070f0010800c01d0000c0c540a68016500d983c2c0c80d6041c508000060301c0240a20030615440c8030840011790b40925140c3c80e80300306c01d132441d170344240c0c510b415030324941640e00a02c6c2034800d180d0010300da0000c00301100c1c0d0794801540ca5103981c108030740707501138 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 674719037 1250 674717787 674717789
    0xd020d1d06220b04031110091113020909041b120201020304050d11190f0503010603081e0d02040f05010f0305131b0308030a051012050705040506060d0c080402010f020106 75
    0x80d48100c0110b41110240702c044501c00e010310700440c4620000359148860f030384003103400ba000b03d50444800c00313142106010403c041e207003040c0e0800c000c4460340e8683c4e84078100800b03000d002e0480800d03541100f200a50403104c2c0e030f00009003460003518051030314104c02000c84208103600c050591001034510b60700120f001c10207605030007039814582480188400300c80104815106050103510045041e103c000080010103242c4410880c0c6a05004c11054040745d40c1e40103a009a2403c4401c0010820f0007040d2600c40d0709904281ca80c0508441c02d00d0414081c1d41c69801005200050015500b80141d0580303080b19821b0700c8200d140b00c074000e8150102c6008407011250504001410301c0001c12185042c070054408200c03034107840751240c491070240e4000301e80b049c10301642c07813040c04245059043c00340d005084c9640303c0713402d4400176511a92164490b00c00e042c006c6842d000407560303c0e80d8002c243d5848913180c2008001b0510038050003041c11506540681c08500f00354441d003005481801108 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 674720287 1250 674719037 674719091
    0x1091a090402030408040302180a0606090e040b1f0b0304021005040806040311030d2415021b01120e0109030801050f03030a210915051f0306020c01090203030d020d 72
    0x38101409482804065440200101d818117001c210120050380c0d841e8030840402c00c207504940892800e40c1e02c01088071520340010080c0041c1e200f08011886604484680c09070341704010454907141c00c02c0324849000c0c01d400d00e40301c11aa00c040880c0c2d20f1083d401035803246000f110b2840c1a940c44080a0703a06210764021402141c1080c00041c0109018580c040c2d2018031110840b450603038444143ca044a0009080c0920440718140e220325006241c802c0c1409002c01083c840b43d41c00007000080c1d5120080281a1910f811511040c8103980c010503000c0c031001200032040c0460250241214001c051146086011071881000898a03040910303a04545070070103001145810754a9100b80e44504012400c5807000a40c203200711b90111450095000341c610541c014403c12807001a2103040d50300080c061400d601210384089030032212165645c04481e0044170069a80311001e6005025104011010703426100002e80c2c0040d208440d4010b104182c54038108020a520305c4a40180032010000c1c11 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 674721537 1250 674720287 674720339
    0x5060f0403030e0f0616050f03030907150e04060f06080a1e02070f050304080706080c090d030f050c0d0e01021e102d0b0418020a0312022a0109 63
    0x60001a00606105015800c000d052244e40140e0300e00082c2a60310800d1412a502401100001000010003004d4083c820000241d41035140c043c41095440310688603040141c0ba445070030710311481c0510158990080c0c05003082c00310380e480f01c0e0600078015261180300c1c001288280010100c00c3e9520580c0241d082c3c04d0a1410014003051200c006500310f1035054414094401c03000c400104100010401010544040d12040d1b241c180090a60359004000c0044401c041000028550b1a5a4030102c1194541008481071000982c00c90315401500d180807a03900c00d2454191100b82c1105044c02d081c0400da0813138400321362260000040300d2082d1841142544405c0b00c0e03100340a404c0c1c124107005d5600507006c0820703100c14200003d024080311b00054200d039440914003000d0403c2e0080c021034072402414413840701c005074040b600710a00c0b8071000d8030342411000d00640e018800e00c4415445540c52002e8803400c4020240589000c441191542c003103103044600003000369114001c200308c40001004 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 674722787 1250 674721537 674721539
    0x3070903080d290a0f080d05031806090a0506090f0714060702061305040b121507180e0613110307030f2d05070e0f01030b04060e011e05060f04 63
    0x5052156041111254460360312418010f4501e800c28443c04811010810a24040000c400074000d42d035081c0d412810303843d8822081484a5900040c030351040714498070301160780c5d5031000810440202e101001d2030142c041d030030038070608807400121500c250b03024100b51005600d030b5031040c3e583c0d481005151111900b20140400c542540040052a80380703001e4012131612001d80c2c00981680e212400d17040c06d805481a040c0321a0410f846101c22220040d034010001c182504242a9030381010345006d8050018000000d591510030340c1c101700203110411114943d81e4480d0460ba104940443d007082c000c02c1ca19040101d405503500405d2103450525103641d1554840903002c40c05032a1326140e48000d1600c1d1050a004180b03038811841c1c200341d000340c601008602d00d070104000c2e104094a11270410110003c0c00036642c0d102584241b08020034200010212601400b1801401895100703440304c6003400000203096480408048221140400a40c82540c6840802030507004880b2511852441844 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 674724037 1250 674722787 674722793
    0x503090c090414030a1110020f0f09011806050408160e0103081b0607080402030c041e0f0b100201050708090a03080604020a050c060114010e030a080d0203060d0b0a091703070903 78
    0x8003540c215000310540003c045440e0501c62a591001c90008001400e10f4419103511400740700c00c90b00980040001c0d4506521072030100281d0040380d0b80c803400c04c90006181100d07030780604d0190034101048022121496032b10030000d4070a81142c458400c45004441c20102c51003504a400d00507105200e900340c0345a4210303210309145030417805600030070161456090075410030401c003061041100741d03942e007003d150501c103260a04103461076690259003090301240f060604070f0b403070030030b003001080000030f0036466281010094101c8600d130680004580b01038100580e030641002d8400c00c0103448048203520b501540e15940e154103e03001c0c00150640c4042200b902d09130b00281010800b038a0700500344200d14103410700b00707002030384030f81200c0580d41d03d84009560001134468545004030041d03c2c80c11200e88070340305940301e042c0718040c44076030000000b4030941d6125140c2c0041608000c0b0780b0501d1504c0ca02210040101c0101a18080d80d44907400d034007002d02c003044900c16040381d0350303507078140e480c41d0703 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 674725287 1250 674724037 674724049
    0x30501060f1a07230f011a030d08160311032406210a02070210120606020102090d080a09030b07120b120d0305180a0c0f0603020c1203150409050102190503090c 70
    0xb070080c0710044401910306884400c00601c4c480001c2140002240109042055100e00f038100040b030103078000924440c00275401c141c140d0b601001034803290002880041c0f00310018100c40c00c01540c4043c1c04000e024082c2c00f42da400061398105001c0b5000302c00c481c5000c1000e14043c0c84e0030b1044610b145010031032000e400c02d210b96003000d0007001c0507044c0780c002c0e4000750344800320b88440703400100ea02072403206400030707800740700000c0c4403900085190030220008031b040d01e018404040c00b02213000880c140780d5842900805c004541140c410b003214102807000800c203000d0078207186809802c1c0103680c2c241e403030f0809101400340c07021401400700c0300c000f800a4010340001813006504540800140d02c0d0785e1800d019407100e10340b140c036505103030038204042000301d208142c003c14200341c8140013030206007400046103524500100201522596541c000a00c0100c102d802c182d0824100000c41d820440150040c001a21481404d12200c41e00345100f100e6900044400c10225404003404842c10f0801d6 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 674726537 1250 674725287 674725313
    0x2060304030c0218040807020910050109030308060d170301151403040b100b040b120a142a0406201b0409210804031b030203070305180a030501060f1a07 67
    0x1500d0084c01000c10400e081500c581110306807619400000d614086181c45040142d000250807002e4400505080000b03140143d907000c01400d1003400004142c03141c0e0b0324820b129145a2003a00503861561074041060503400070303c580e032610016484034051040c05400442400307448070081c0350075503940c1c1e202d4070a03d500c040d011140c40b04c0100004200c0c03101410090025001c0000d0566407080f45c1d41611a1281d001812004114505131040e2205100c1b240c0054109040410b1003080100c10300f07101d40a43d043c4030744010031450005000443d16002014080c03e0707030400c5600810105422411600c51864500c082000c0d041c20004030181d15041d802080c00354010110499a1154181e03004200000715404601148a040401c070806510010600c060050582d03a254110040e0340c019507a4003030020000d09201010601840350307181c03801c3c4c0020282000703198182c031950b02c1c2003183c028031640c02890900316885001181c06c3c01d0b0707282c91a0044203003900045c40c201164a03854a41100 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 674727787 1250 674726537 674726539
    0x308120c0d0f2c060c1b0118021201051519050616230c01030230010602190228030209040510050a1109010305071b060608071202060304030c02 63
    0x90044400d529414481d180b8038096502000803540c10105070030715284010301440340700200d201107504100b03d010407200e401441c0c442d0344035251407902031a05ca031442000c00107070066103403c880d0794826811101b800c0f07585001791801c5100c060401607103426900b04903180d11201040c68054441420145a49a400076800500c9440c0c191500c000840ca0350294550b5990904081d205200780805c015811050384041c074800545401c0d040c040c00d4076200c1c0c403800e803070515601281c0740428030b80c001c142c1045907511218000f00b1f070007150900e80f6440020b0007004018400c202d0010016a98896001c02140c1c00801919295814502d6040c60407402003080400748010040000107889244c0340b0742c044c4d441039010300381145402c2c07450000c43c4c00c01829486624240200302510380e0f540b008555605a0031b1030042130b0780c4d079022810342d810800340340400e845043e03a08494040c44225405181038401c0348090340d4141c0d42d641a0014040c1c00204080d41c424410030224001074011202c00300b03060b00c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 674729037 1250 674727787 674727811
    0xb0f0403050d020f04090605030606012a06050c0309010b090907030f060608010e0307121b060207020a1502031209060708190e07030c05040507030509070b0936090106030812 76
    0x1035542c40e94016a0003d0707042074104039001c1000d02140d0000e00a01c0c020701010780c0107110601d8145d00003410320041d184150800c80c41c10030410390100085814180154121100740150f041c040101c0d0041e6101316036011040d480c1000004030fa191100005000d03502400061040308e0942d1223268088122603402c07104103070f0303a100009001100b030059940b5081d814000d191a48910304020000c0c8a90300103100400c407482c000c103840a5100d8243d06809a003003480103071200050b1000c90184030303258014040ca1a59546030303950007503000008004c80f4070b8401300d21066482c0c640c045555414103681d00c0d004142201d0000c0e0700441c00107100001c40c0b0420101160060182e41003504191161f001030f44d00341e0b5402418801811701d40582174100f8141d10f0208514945559070503140e01d03850003440310807a0005010280c0390390b007455800c40c0c00840202c1a104544610360040c07564800d494a0000200300400541140418401c440c11641c00c144c4841c40c11702240080b0042140040a8a501c15 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 674730287 1250 674729037 674729047
    0x120405041812050301030c090501050d06020a180f08010c0302121f0b031603060e1b031b040801020c120313331a0a0f180e0615040b01030501030b0f040305 68
    0x50b0990a81440400a6100d03550b0780c2d4110b081034800500b60f41c0210040900745401001275480c0c95030a0301505401ca403006888015013442181c0e07000301000e010b603252290040c0464110801094601110408002000080303441ba43c260168001c00f448400121103050003c4c3c40900080000072a002d0342901601c011f80d110540b1100e02d8005a070b068002e1441040076201c855003600c2140d01030000e000940c5020725094041c840380703142c0b402e071409011101002050042804809030089103004418441e280c0da15084800d000350080b9500c0307042e6100740c004800c805181142241c2c05404200f0450b203c0354580d0722590310400c04a540003941045c880b06284003590400b0616120105903a0045030840785800951040d4410141c101d1154061000c1005581284da9030b650442e00c00b01110081010911505802800c001009009502450082061071510408044482442110104507042c0d0403001101150f009010081000e174a90010903420171f48840642e074001d01c42d00d0326074604 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 674731537 1250 674730287 674730293
    0x4050604140f01210c0504090c020f060c130e070e04020c010207020901050f101803060608102003040221011b020c06130e0a0b0a0b1b1204050418 64
    0x1a80030380e001e0030141c9901e03960750189103000302c01e0160035602444e02d0070401c21002c41100c2c102c0180c02e0101e03c4c1c16542c80b000c40e00c1c1da0052042d14000c100038541088001c2244001071344a00c000035640b05240242c00000c1c48001c401000d0342d5129522600c0b0886480c200140d00400e0100074107034000344002034000404a669600040082820301c000158881c9150b00c1440800310040e00010f1042c41d005442c1892601d0740c002d0003248100c0352400300e64043da407001d80380107141d02c0d400141c961800d00f540410b000782c0010702184407141603102009400750740704c030502c071142481069291076001007001c10050f00d0020b56240c520720108004590150191034a1400c580c0c040b403141c0f6070045162401103102c0e4061008170950034058074501e16210400203209a190458082c820b4842000b002107803200d02d02c3d41c401d1820206c0a080c0240c442e48494484c41240c001ca00c42c0390320202510500151010003064111800c0410340c1c503242064200810400680074900e47d4200d040040d0b01c0071404 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 674732787 1250 674731537 674731549
    0x2102040b0702120c060316110303040609030f08160323010f06110312061009090c090e151807120906090b061206010b091f02010e0f0c13020705030405 66
    0x1445001141507031202544140121525a6000115030f40c0180c3e071030798415213440c001c6903030007102c1d500100d0f0a410705403001c1d140068000340343c0117644804020082040002c1d440b582100c0d000382c0302c078170302100807002c00c0381e040740101d503648200720f005543c0c0c8644038003a8001c0681500c1c1c0e113007002201d031070413500c10035112401d07407043d04206071040c4100a0741d0340000c103000c91681401d011f5460001b43daa8802d02104000d00014020144e01c402e0b52004c910810715400940038055051029502c10000100004014068075aa17503c0c0e020100b170a81c20080714074a90307800040d1490102c508030006108011600800c0781081c04412821845130980a115040310746100d2680010080d00904041c003119100800b4180035211141d680700d0040d03000642241101d09038641c0c160b99407410700104040c84031000665620000e541e151501594047d000301152042140c1160303800403500c0c032541d684244090741e036608800034461450141c1d54903001059400c0c0604112850700c0e54502c08540 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 674734037 1250 674732787 674732789
    0x4090504060b13270b060f0301110a0305070f111c090b07050703060b090912030601030b090103141005070e06180307031a090307020f10030b030616260601210204 71
    0x555540d490035210005940c4421021113002006a107040300140c2d40e2020000800382400d442041c040c42e032070007187e40c01d401c0480810450601c5036150140f100000e400340800361501c002107403251616138a094415000c0440c0c008209004009160000804085841c101840c0d28100412420701003208004078004200f03041c8508014084c140c550b061030021201c501c95040c0c401e40888080c801e41800004da8904480c0d5281c0030950b0f07a84440d40168000c120764005a80c002c510240000306202000350072002d844032810661300c5c0c1d03686000f420300880c4c0088803d4004641c88203199502401d108015001c20021068000301240107200020301e0030183c1c1c0e00407104081915004201a0041e8040c580c0140f10003000310304124081d40082d814021620101e4041c042d0485e0061209101790490792074140090151500e90405951010704c0000400150740451017030703c4038039250755a03a4140421600040030031207141c0c0b5800700450303000e506507401034014440100d80040381c084d1440100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 674735287 1250 674734037 674734069
    0xc061606091e03020105010e1303081906030f05060604090c1a0c0f0624010e0d0807020d0305270a0b1e0412020f0910060e060c1b041503030504090504060b 68
    0x21a98100ba803600900b0741d40160450006034901d5030a001c00b4001c1d00c1e210100d81a40360400302619a02d040c424408003022488500445091400000603c041c1d0050f115000e40541c0c1500d80d90b41d203040a00066a0042c0e100418100e80504100102b4030721b01c8000c521188464846403500c2400041140b408107840d0701e60703105800810501c00301c201c25000102e000c1403001c2c14092030303044130300003c4c22410007108918065551804030f003042212480407070b2110780e402000e6921140351810001c265030070407000c4990681c030304c4000c83c4038017403154510300c08090000d110303070349c4070741850040c02c8141c0140e90401c144002403c03040d4192003004000c0d10103000403d9441d007c00c1054010003c0780070f0301080c0703580913001041c140100c0c150104e407406c09823409400c0c91109003d510f00840c01ca07202d0000d0300c030314034015200c0c1502880e411190b40d120b0840c0c22a42031000001a10540764400d4403840001c0c08100708000c2000010032903080b590f80680216800114451a4000f050030290000510 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 674736537 1250 674735287 674735333
    0x213080a11010207050a0e070f050c0318100e1e04150e27061305162309060a150c0209040807020301060f0506040504020d0e011e05090c06160609 64
    0x15007519681044000001c00d42100d04007030311480d00c90b04810122000d0456400c000b00c010300003540d41d00a00c100d804412001c03080341e540300c85d030001ea004a101d408414600c1500b5803440010340a1283c544003048080041400018448150881d5400c803506000c16400c06c1e15400da81c00030384980b030390081c01000152011502c91a00d4800e001011010440c3d1921000021400da20141400100d185c0c2c024008451100740420a081c22131a02d15298020b80c01003054072004105861a03004d4042c502c03880c0c1c581c2610700d640010800098400c111100303038200c0410346041100c2e40d40c032171019000160504210b4214440303600402e5a00760101d505440c1403c00040c102c085040034410a002492a403aa5060040c1000c2c000f40a13445288540d61283d80c0205da112101d1510303501100092001c00b000b01b010640d0b100d120034030801c00300361040020b8503090020307210f04408602504640d0005005074076000642c81025101149140c081d15101c0c0e440c80f03620009459030300c0c9005000402148 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 674737787 1250 674736537 674736563
    0x61306080304080d170a0902030703060501081b1e1c062901020f1b0303130909050d0906090308030a0e0105041518020a1512020307030902121f0213080a 67
    0x1a1030301e010301c6070328100100030171845a011203124a071042d43d000b0b05651000308100007107000107480c15140341c1002d400c5900c1c2c5400010031b035000145e0020701603401407403010010090380c10804801902d24442049841c00161659035250048200042c1c01241c00401581003064a4250450762106c241104140d008145908001260321940e0500c032001d03c0101500310f41c440d03000d5212181d01c0c1d22640340c5140403c26103da0354043c407d0310038210080141686150792030900c40b029106c003190603503190203145a0206400e100304400781c00e030b68160b00c41d18103107480c1d07980300c0307465600061000b036005a542e200051514401e0003981d02403800303608800000031b00300400b901110114040b00e0941110f0104031401070b00d41ca01480115114820305130000d200302c03a0103039500b01a298440300307014400010030260b642c050384640c05075802031303407501d01d4000440d4000c4d59801d0fa03851550310301c6100a00780001e0303c85c0f0f43c000f00340c41c01c1110b0504082e1035541384800e140102c4881c0441c0c1803890010 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 674739037 1250 674737787 674737799
    0x806011703040f031a0a020c150903121e09030f09010806011412011a18090618040f1b0e04060b0112060e0a050c07030507030c050c1201020703020106091112061306080304 75
    0x92504031000146c114070301100c4104c503558418000702820075000d070f6500003541003031041c0250781a203401c08904106a16285056460b00a0380c020352507080c1d10340d0b00c081340781c4800000c1501d43d08803100c90a0751400010500640346054024a03880c10403410780030740c4d2a5440502c2c09004804071301c031a13080855041030008180e01c1840c030740d041180c0c40300303200c00c0d602108890741c2400a020103960300c071519218000482d202500c1d0703c0f164040d22840100340001c000280a41005c41d50180c902400603602c02c949500002810f485290025500c10000c0b401141042e03001e50784034901414401180307540303001c56500756021503010842c046609410480c20103854050b0942c40b484c5003508a284c40075590f000b034028020201c015041042d15618001009000c008428402c900106000400103525030350038080d501c9140c3c214019420102c000403a16014043c50300013200108090f401c00e08860090b540b0160000c100c0740d0300c042e200c00f1400448190380b281d5000341103000059a03a69081c02 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 674740287 1250 674739037 674739083
    0xc03020a420b0103020a09031e0501020408070918231507050406110604030203220302040513020f09090c01030207030e15040e1f03200301110c010c02070806011703040f03 75
    0x22840c1413500400600814030b0340250140103895010100c480c400040383c5505100e101142d000802542c800180491400e03000620a01203036400c081c18003003010645401380c2c0707a40103048024014105d00d4804c8500440d0900001070340050001210f003902c590114540c0c1080d000d507070740400f188000030248080f6a0105540c071940c4400c00042c0410704082e42c0003940d91140e8966004c1d2004004d60f81c0d0300100c82205000011500284140107a0900b01204d10481300d0050040f0700c100d0031010b50b0300181c1001c1c0b1006118a00b460081c1c45400c01840054000e5405104218104014071560300b1725559003008040030304a0350002103440705d041154a01c0d8006024100c01f038520100c9541c9044001d40b00d000304c090ba80d0003200c0179900c4080d050350055408820016642c1542040b81e44100615014041c2c5200454030f00240301c030003841c6000340e842d0140360103000c2a40e080316005011904510b003140c032840c0c0d88901120302d03003591031450b00d45000c00c54100306d40700d1044c02120301c030315a051 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 674741537 1250 674740287 674740301
    0x2c030d0f150906030c05011808072c24030c04060f0503061b0f0a0c2901140303030a02160b0702010e1507021905070909061b0c03020a42 60
    0x10b40410001c590450b00c40051030000ca12585040280400c200c0720583e0345401030800410040c1c0846207945d413243d903144007680e4118a1182020795140c10202d40d4200352501c64002c41d03c0440e01c0075113100f00010401c0711709003440f0b025014480e9500042c1e0944a507c1010000d209907100440e54501300003c042c10400b01510a2400c05c10408401c2c9075200c0e610200c400250b2110205903854800c5107040d2120040d0b41400350035071000407403e0161020000300404030500d03503861440560b8990000014a250300700d1980d405500c144001116481d0590080000080e601241d0f08100181d40d81c0d0403056800b2558000142d4440c03800c0300d40d401c4108958041f10f402000080c0d614500504029502c96110b0409112464246003901c14040c003070160502600300e248046c0685400d40c20150054843c04440a2000510603400d000141c030449160740c2071139042c4c0c043c0c0f203c4005505d601d07440e50500303030120741420208402c0d00d4100700c48000c042050310294281803040380c140d1400a048500c0c1c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 674742787 1250 674741537 674741549
    0x50910030b120a051209280e0a0e070602060c0f0702120303070c03021903050909070e040203070914030102030103081902030906030412030b0f130c0309080c0a02132c030d0f15 77
    0x203202c24592607440203102c0d0498849040e03181d00030b1300201f40500040109600c468540c00c903031070500070b00080380c3d04000294040c56085403e02c0780e41d04000c90303440700125400050710506202c01005803020314000c11003280028100d00300d4071400c8401c942164403e03103180e030100780f40c03e01c0c4030105134040c4070407440c00c03281d00c0301040984001c0e18003500520905d100c3c140304900d140001402c260141c0e24001403098040d1045449203042c08014010580d5802200c0e5034040170380d0076002c145814001c85e81600c0d070200459003064080e0341ca002100400300f03003100035400144a0401652141005544607500074400f50201e16001e90307000d402c40d0844ca0200340248818a0003640a845034415000508110280081e1004200a00300e0052003400802040c514000600c40804000080c01c5000d19008491001c002d01c0e076140030b481110f0040e9040c000c07560070601c2c800611990140c010a26003541001e50f0b01c1c1c88d43c40e402000440700009030f8031000d02d035910180328103070544465501c05088 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 674744037 1250 674742787 674742823
    0x403080d0c080a15050609030a0b040311010608031e071401051f2301120e0723060a0c02010305040303090803101a09030a140a05100c030c0c0201050910030b120a05 72
    0x1c0c8070384813444042d015000b0503010b1b8a0008242c0c1c0b990b1401c001030008980c0241c09101c107400c052070000d199010100315482c040d070a100c40071415072804400c8036514040d404103550001400c003551403094002c01410381d109180b2103031058a4800070b00035103101d81d011044000c0001440c801042000b140e43c0c204484149a0400078192020030013600c110800c001d0904a450060b12100b2001504e01c40408a01e01d00884000241000d09a00012641099034020301110445001841824014106184002564840c8040140d4020341c09141c10900a00e408501104e0540340d01401e9442629240c0041d9144074040205c00011082c200c0f00c100688a058034200c006000a03980300c6010706c010381614a140000136920f40100105410503501009660f506401400030320700030461640d1801c00b081c14141e0b003110252160031441d4001c0e6050710340e507045c1417420060203005c001d0680d48400703050340d810419481d81e0f1400070300c9440201c04801840306000d0340c903110f41414003003440b40e0312070340d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 674745287 1250 674744037 674744051
    0x5030f03090109060f0218010e040e012922020a170705180306060a03150b09071e050405090103031b170a09210308040317100302090f0103081e0403080d0c080a 70
    0x4120001107e51142c1d0910703000d054002071100040c014000032164074510b61800c032504a00c0310a4507014004001d80c0681416141c4104050240c01c42c20b030890040c000201c004a403100002c1540a00300d99034507450030600e0303403001c442040203961054580c07001040b00443d00f98040c030780842c4005042102940074000c1414503101050b08004180401442119040c504090051055000c203001d004028841107031420030742da002c0c105203040c2030201d4007041c00ca031141e03002c18010012201100d1001d0100c503440d0303280d9101240c05040344030030f07001452141c40300440404e25849803200c400101280d0150380e02e1910b000601050084d6100807800d4070200044003159560558008000d074150400d65003681e91807804803400c5d50000d031410b50011003042400024407401c1d20a43c00d403442900c1c0b031080754940031000d643c1c8039400d2100030a02c41040000082041d0300e00b00075010041122089404c09403a03a130f500019070042054903260b9a82d030101c0264480d401501a034001e220f0340c0c0e04100c80 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 674746537 1250 674745287 674745307
    0x50316020f07061d10030204050907020a080702130b0904060f0b040510090e12040801050a0c081017030409110901020c0a060e06090f0405071d0111150405030f03090109060f02 77
    0xb405007071280e1414040701c05031015542114440749081e0050041c2204000c00003400c002c0c00940050280f00e005956210003d0702c11400000d0102056420941c4a03060503600c1e07003081101c1c500f82144150f055201e00060005444045000d8021403103a4400b1030221541d005010444e6080c4030380c0f80c415801d0400b8022502129036030041a1800100c1c081000c2d07182d4602d0514040203010646004040003d00191540b010f620450060b900f40e1000e00c4104503890b000c652050003a40e20608003039005800700300e40b054852550980084080c00d603070405584003a21002c032000942004820f07000000c0d10340ca0342d030f410300840e091040101c4480c04442d0400c98000c02c6429554107040c00340d4000920405031b5a2107170001c4000c400014000d010a1401c85401812175291b417000c80c01149402c1c0700c110040d1702425225842d083c9a0004284594260f00307070804480000d001520380340800c00c0110071011000c40214410300c9900c0c0081803094040c070b0104100c034000000c0f0001c00d44140101480 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 674747787 1250 674746537 674746543
    0x20310080a111315260703050f070f03021e031f0209040507080408030a0c0e06070305090102070e060303091c051501060f03230603010609051e060f0f100c060c050316020f 75
    0x151048002010b10101c2c00c080301520b0350072078034417040340c2c1d00c00d40400104100000403c2003d0a41070420382d6451591103c66070a85020350000940c4070f001c04104d01c034041c010500320a2090740060480e00140004601c1c541844c020000b070001558000032040e129062070301a070b58022001e860302c4440340c6815111000c1500020384054400c40c0c80f145400740f9a07118a07000c0b56289402081036940f206d20745406071941e84100001800f50088441c0040c40a0309640b80c0340c418040600514500204442009401d540c8500480c0080c2001003d21000c21420011704101c2c6142d8800f90744954146140540700074511440395080600704940302c12681403101c40c2d10301c14100319074540042c0d10b8907400a4003404407a045884a54039050812403890040285619030b804101109442611610207100000c400172002076004028200c6d00c14040c10100200b15102c60300b4500000c1c2c10f030706541d4940a42d0740203841000050008000d0160414980030707280004e2070680000d15184490040c0c481e1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 674749037 1250 674747787 674747789
    0xa030f0c0c021c03020c3304061d010f0f0c15063605061201050405031801030e0c0d020a090513060c0c02150a0c17032d010306020310080a111315 64
    0x10041810301d401c4501060741c080148441c6039040d07e24240c007030003011424a690030600c01c01000a000b10760f00c0d03504896090700a041a00180d550740342c2200d14082c1542c4505444050004120020030310502141000c011400c4440071134002007041031401410644000080c10200d050b0a01e08400b03a4420f40149240021822050004201542d9500010303143c1720100b00f00300060350070401000100200400100000300c2d0000c1c2c90813480784464011022070758001f0003540071390f0052900300e4051911f0300120000368401007a00b21b1190700c83c030308102540c070300b03440c81007a03481c9221b03000d010010b01c0c0c011441c40f0754140c0f0f84003a0254040d00040e010410f403e00d003050000300049e8903e17400c0d10904184450640199040b1040031044030804070070341c011205805900192921a0795810410503000c441009000d11007810340d09603144c52000b0340c0043d050800c000c00c60040001ca140c1e0500c120840c450107421444900c00d03001003880424120724a405404d41e14010b0440d8041d92880341d850 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 674750287 1250 674749037 674749039
    0x61b0804020d080f0d0507030e2e060b1902060f06030a0b0916120c05040615050c0a1406040212010e0304030320012d06060c06020a030f0c0c021c03020c 67
    0x115000c10900703020643e44600300c2d080c0c074020b13000078188003104843e4014a001c0c0142c0e607400c00c07500c034154036040c4d15100b11203c1001100c00b8149485075501000780042c0080028040c0001d800342d40b91f04102c5940d10625490000444a60382404915018000241d000c41c20071302c00c00c2c0c41e140400000c3d40790310350800010424006540410311003a0100111080c8005071134040090603181c280310407038003030201c000310349923503503042c0114031410a4066482100e03d20540301d148400c6102c3c09170798a40001d48502e41c64400c0000740408104d800a81003c0d80840f0009024030f420300c1c1c0103000c1002d0113482d80c20720507810441c0360140312a00208031411a0380500e004d942002e00d00341d4091000b9602040c1102d25070910b6201c3d52125450100f075954a0103a948900d5400440c078803490540e00b080c841c80d0b02140807020014007040c1160002c0c214001e8070700e0005203012070880401c00320380e4912003800006001811190440c10541c0803080754248154403403484a866960095569a00c4204a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 674751537 1250 674750287 674750299
    0x50406050d1401090e1207050303070815030d0305061009050906100309020a0905090d18180e010501090b03070e0c03010501110a06020c0319112a0405040609061b080402 74
    0x2075007807030445502290340140c0302d0741c4100c990750b5229280005090ba0118481c01d501400050107503041004045482d0161302c00b01a42c00d503a940c180035524000f000702000c800c0000c13003168060343d940901c0160f1030310380d0a441c00141ca0030040d0a204100c03514000700420301c40034070700500041c1e98840c10b00c1e40c0f041d4225039134000d0072910300c412000741c000b402e402034000c10003a402195002864000c54070801d0514120f441c403201c0d105080b00c1c070b00019085601c003581354000c14450b40b209407104040e02c2c00c5485002c944a040b0340d2074030382100c0090303000101150b600c040210152030300340148002805c8250424459003068201001c1a220610629043c485201404d030035101c401c0c0301e00402070380c01c594219190621280950345035480b0305200c1d140c00d40d55000f480c1c0c1d040e00403400b001c814010b0000134060180f00707640201c111030702d0041c05095480000303196103c5a603103025152003035104580100300101c062800f02c040d43e00088100343c1190300100904503142d4080074540c0c1c09901203c003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 674752787 1250 674751537 674751547
    0x1090b0d020d24021306022b030504020d02030f150c071e051c020703150908030a0c1b15050702030a140702060d05011214010e102a091d0705040605 65
    0x1c02600c4000c01016900140041758162404660790220000c40704282c09440d0030120030140e1501512500b0446070003420003401c0500c4d401d219520465106d0f00c007070210000e400542e00000c0c540380c26654200c403968070855040d00301c4108034080d0341e0001e0300c0802c0141050203d07600d030b84009a8414501d1502c80d14072259000303101d4100803c4540a50303030110520030300018030b0300075110800c900007600c0c000c4184d0070200016a10713200ba05861a000003d06042d620740408400c098104142002e003003000110501e0310303070508544501a070700c1c81550b440c114001042107070400d60300000c00803420354000b40309484005400101005d02500801c3ca820760700c000c10f2000036001e0165001c04032a10740b80400100c0e41c40d100320540495940950025280400481205800c0c3c03502c2c00c40300b001a17004a002e030100e1607460340040103800c030001c00c805444520700150000713414080c0b0713007000000c440c9081003090a40c81090503007074064403415540c80e403801c03003005010340c031982c820401044800a0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 674754037 1250 674752787 674752823
    0xf04020c190813031b08070b030a02160b01060c0519021f121b1803050318060c0607170702070f0b0a1b0c06110c0a0e071101020a0801090b0d020d 64
    0x701c41c08070b0000c3ca8020412512414058010002074041d142c11151649001c01e40d0a4005a40e8080b52000c2c11298a96070f561201c100c06500b19407440d0031034000d51010180021107030380700917010b02250360f0b17000341094960418518100d0903000490322200e40a443c030380561100f86803180f101503502011505001c40c100226175a00310820328111080c41e00301c03071780a140d0f1a1583c0035411440d9a4039110b60300b2040300352445041c10742c44024020343c0100701c4884502040c414001001200038216400c012892000c282070000c1116400c3c001440c001c0c940d42a810121105604000c007031005082050a10040d01c1d05034643c0d0080140c021804200c0e495414800c0c030700c47c1408400c005a181000c040742c50805140451070240741c0209220414604010100142c014030a96006101c03000c40c0b4039081815042c0d0101501e40c9080185040d0008814802400100440728142c1d5521103550301d4000c2080c2201d114403000b600c60a0251201c9015944004026507140d8100703441c1c1c00d038064448 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 674755287 1250 674754037 674754053
    0x110f06070606030b190c020c1306030203011a09130c120c0504090b0907060f051812060414070603020405060d050604181401140105010203161106040b07020f04020c19 73
    0x3000400240c1022400300400c602c0381d112078020740654048411509002e02a00180c41c0e405442d50016406030b100c0c508c50380b034805074604040200d44400a075803602c81d00800e082d00c140700c08104c1d40040b00000b4071607905100039120f030320000e62462440c070a5015a02d50b03080c161b030341c442d41481c11218400b1500340314900c0c18000080400400400a0701e0321458020f01807070044410341400c0c007482c0e0780080c04d0b50003441441e90140c508d507039580c9482640a4481c00300c02d100014550050420030144110490800c00e69008600981004d0112504290308a01e8002590410810140180010007071519544191604590901030102e540d40d24000410000d0001c01d0120111424147c3c2c86001e100d0503144402c3e103000307854001d1202c40b12880c0c4091843e0020701c80c050040c0e008001000c1400c58451582c0141c5100f290120b00e00c0c404100011f0168010350030442c02d2600000d007500840c90040784844200105940650608810001031a02c815840c64032a180441c019a0303902044406 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 674756537 1250 674755287 674755297
    0x1302010905061801030b0a06020c060d0f0c020303010f080a02090a0209040902031212060306040f0201121b2703030815220b0108091f0e0c0409200d110f06 68
    0x1501c0542c5486443d00180003046140525030f01282c5480000b040600b0048880c01c251003040c1c004114044545040c40340c00d50012440040e010394480604038a03040d00c0c008c1111709100350340199120b50500c80350044406180e403008000b603024408a800680b101075030160300c0380f0b0302440141c480200002040281c94039000080d0301d40503400b0312118922241e0003800610040900e9007070313641e8031001031540e00d00c0150740140601451a00700c0d401913102d0078030103012402903480415404520241020b0704100d41940c100410306100e5030340c1500500c01c105562480402014540652854401030a0024050281c3c5003481104a0f2a0243d032039007680b0125840c0c610740206542080c1c3c05c02080141302d28041c4600040d500004680399060000360b84102d400c107030000d42410618811528020030005a03120307910f010745642000d0665462042402060165150203a0905a50440381911141c95460351145034403c4842000c54006400050503035810760703c262900509200190a600075 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 674757787 1250 674756537 674756539
    0x1020903010606051c0e03120606040941070e0303070803010b0309010606022a0f03150103052116230d02070501050307121104051201050115171302010905 68
    0xc05100083c0264000001d140b0341200041c00b00c040090180080c0580700c44100b00c00c0325a2040c4900071644407481020b5401100082540380b41a80e9811441e00341c6100d00015404280f01c1d0300c1d464214010000c44000300300a00000c2c10713142c00a00981c00340714502800c101c04122a032507060141d82c40130021169003079000029141c803582d44000b0300f50598012215444194202040000e440b400016404040f0708145482c58a10161324980011010004002a8046c442043d260120f0320240134111403510b01c401c07545403035811401c0551030300c005200411401c5103614140504604100151180c4001d190107000c920081400d041e030a1100356450f030072030140500642c481c0000700140c215050a40c94007a2010b20391f6480c01501e060004541ca0000b1958881520603403a1003a804000c181c049002141e003800c4c0c6440200b260380c0d078040310424039a0355950060001150003200c4100688a0786410312007012803410320400e045025000c4030000240b9000402113a01602ca0b10004e880 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 674759037 1250 674757787 674757791
    0x1701290c0d300617030408151e040605160905010c030c0611030c04030b011203080609100306021317030903030a1d03030f1801080c040b0a030902030d030605013903020102090301 78
    0x25600040400510725440b84122020380903080c0c2e20a5070707000c01070314111f844d10380c050100c009aa00510251100062003080201e1091000310452139004102d64029400f50000207083c1c13900c44651503240e00440c091805108607001d042050340c0c1d021560300d15103507140c0342c001c152000528003d4003518141030f468200a6002c820015000c051070050400c8a010700e443c0300032030b6680c004000300e0040b5008080c5c0000e1803035001549504002d50001e42105441c1c111350402e40d81c9032512000c07a00f08080034003400034418820840b000c00c5003203085190100801452500c1035820000f41d4900c9a042114280a032000c41c54200b0004000b110762610009416a0350351021100310341c030345611902410003401d0350910090400e51141030103a200b01c10700c00030145018140007440340c5503084010310b0020551540110401620b080c012034902d005a61800318820781040005400d086031614564001d1071000a02400018140c0c1c880c6415454200310840c6000c45040480c003a21842c0200d6070158 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 674760287 1250 674759037 674759117
    0x706093f051303030e13051302040903020c180a110c0a030c0318030f0b0c0705070e130602070f02040b03030304031e11011a0f030d140a1701290c0d 65
    0x10740001d03c40021710012a14000b0310b6400450b5101112001d455185069105050f11401400c0513400209124000d00480707000034451320004001c41d4203103194000e141c45a2050004c03510303682c05001000070010010500700300d03041c95800d40d150044000a0100000800d01c001818010165840201400b40302102055102c2c00c2018003045550002c88101040707000180c0011034041c2510602a401000703002910301d09118441a802c000d04100901c8903600c1501d000294648000d200e00e0f88030389500c40c00c90074640108401c40f0030300314529010303800800420000030b80c0140e1000241c4128280f0000c01880350318210703008200041e255400b50302c1c14800c1000000c600d840c128018608845d4259140c20071021306407205003d0078070341c000c83c0515106070160040680503240c6105a45440b403500010183c19000c424000c2e401450001c460451140c440c04003804001500010800a0752905110030f0b1641c0d5600700c00c000d0301080010004544060841090210302c0c00960b002c051381d02070f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 674761537 1250 674760287 674760293
    0x7020402120c07030219050d0f020c030706091503050103020607060f0207080c100e03040f0605090f0303040b04090507050f090103050702011407020708071a120702120706093f051303 80
    0x640e002c85000c0d1301501c20382140c070005420120b101513007540c0c020068200121300d5107095034038103034107148038081d4004e110120b02c00e901d0400250b00140b60540d90190000d00c0d011140010040c1c501e042c5081604100050003d601c0d0340c82121002a80aa00010300440c2c1c442854002d01581c040144484030015110548800c0000c11440000c0c0c041c0013041810390113100c9594901ca00c0c45810110302080004004050040c400f800507840d000c0d01c99968554070f80006800d60303005801c41c0b08800b8010078207020745c3d00c0d10321456034001510f082031481c002d010b1103549150f006850b01541014ac50b1000141c034030380f0070742044114a40e10b000c000c06505050102039142da015002c1d49039507104074100011420800d10110a0000e04140c0c160b213048080c0240c1031217080010703e2101541300d084a0f41c51901e40320002002d000780a44800207031820580b414502c100f41000c606a01100300358131002d50020b40202c94614103a14400b07a000d00d03c503106064034640500c020800301c02e02010030020038 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 674762787 1250 674761537 674761561
    0x70302030412061d06010303080711070b04030b07020601060c02010c11042405030d170103020405071404061701061d091b310e221e0201031b0c0204020702040212 71
    0x2801d84961003610030070344c036400c60580c0c4150921003d00020078480105142c180640c441900c0c500100f41501c9099442d42050212039105502c211082003100e0308000d41b03298180006805001c2c1403800114561141e00000d010b0400c28002801c0da6003211b102d203400c4d03542c41c0e10901c0c083c411191540c030304001d6842442d800319101d200300c41c040c2c00b8051581c0b002d6403144100b44602d0b060710100d13180c00d0342181c092000a0000900c1c2c00d06020702601e422600d40288005803000b041c00e95140e0f10750014101c400880840181e04c49410f016511001180101070b803a956500600d042c3c2d03a01d58555540d8a0001809284883c20030f044000010400514100115070018406070560003080b00b240311400c680c0005020721401c054001007101042d072005416000c240002003680701c120110034640c0b6506465500303000c000d04e8503030b0105882e00c11942c050047d41c01101d0002ca98080810fa00140601a40200a4003d100d19030001e5003c7c00c550b0b8a40c1544c00e41068220320f0102d41c5050462140 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 674764037 1250 674762787 674762801
    0x60702071d0415020903301201030f02010306050612090c06030f04061e0903050c070e0405030403061e0507081006022a060f0a05130f0f150306170d12060e060607030203041206 77
    0x9882e0380300290342c030b520302c44600131144203102100382380c58181c0c610b07120401c03596040c4004074101030f181c1c4000141a40d90341c0c058a43d0b094403000088030b0341001e4010a1512300d142c020701d40150414001c100024030000d00325079006800610100302485e00d0a4100c3d03041c00541c801c12021880d0502c1c1c1410306500c4405005010b07000d00481d009141c032507114030080c260865004015034020041400000c07503e03000001030884009050441c024040381c103000b501e1003143c1400c001400d00f420000410b40d410040001800d8030300180103244070f0b050b60700c00354900000d200d00d0490f80b80c0700014040d071120400c640d02d0b1034007a09178680b03030900c04c600100140e00840051000c91804100411018494910b403411503007038000000b0b10302c0c030345200040209c0c5401103100900d80e030b038900001d0090401007140c0b858484c650160103464140c0c10054510800e070b00010664a10b040424403d0014810b45550000c0c81204e055403a00c0040c60704030b1440c03165802140c2516841c0c1107400802070b1a40001c8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 674765287 1250 674764037 674764093
    0xa020c0105061203070213110315040b1009260304030b0708100803030604090602070c03060507030e0f060402210d0201060306060608040308060108060d0b0405060702071d0415020903 80
    0x21200b038858404005030000f15561004154000300118001446c00d6030a41280c45d40003040801d14080c0010038031407903001111041e608820b45a000c07070081c40d1522442c1e9403480f048515002c159402d05009003118803074014004580c100302c0400d03440480a0104401400c211002c90b56281d8807480e180161311401e5500c080800c2d15840459001151204007a05030b03034054000790b00315a194000c01014011250058500c0340e820007244000c21803041d0031202a6000720000f0459042c042001000c85070107003040141ca07000004403043c2014041a0a03030410780440e0040c5a014801d19084014414030001203150f02c40c0b1182c900080fa01034024108590048008110041d074a440030707a0021001c44004002aa0710030020b81d041d8000d900325134016402605107a01e00d0300e155610b00f10004180d070181d5079a40007804002e940e65040054170050050750301103040340090001c10303020783c10300030f0001007101c1000a034104506200c0c0e8107895544000900310360031512140300c1c401c1d104000d00465 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 674766537 1250 674765287 674765291
    0xf02040b040f1a0906030706080718050d0c1404020705060a1a10021b040618050a110f1b011401060804050a061a0916140f070f0c0e010806041a04030207030b0a020c01 73
    0xc0c1d170038580458043d0490364151203a840700e540e451000c0300d180d01c114600040400208101054640303507803000701c00b10b902c1544841d0456007400804900541811682c62041e80108102c3c40050000300b002c03604240601c00128500502c92401c038060f007405050340743c01005900510380b00d01da002403c0041a01103040344a4110140303010310054421034010704440920300030702c004451640b94001a440802824000b52800041b403001c0f03602d9020174141551090b020034542080381040d42c1c14000c4030f5081e4001c0081e2180300e101442240d405101d18424080755030001001c0c424188001407040368041401c101800306100d1204e104400e0210642c010400740f0001035a41c08512160201c144007525072000215603000c0c0c0b2407940d48030100c0c0803c448018490706000820101e07400d5141c85c80343c59803c52190a05400000c2020305a2110049620000921001c192846003042101c210719a110740d01d50788a003420b900c3d1680c0703584014001c044140c00c2006041d50b660240984808090003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 674767787 1250 674766537 674766541
    0x270b120414010b0607030c0314220f0509070f050405030601240c020a2106060e01030212030403030c030806030f122203021302032a090a0b070f02040b040f1a09 70
    0x8460807244140e4183d07800c08010070800010078000c95070411202d00c46c0c90101d80b8a0011001c20700303150401143c007600c40342090721000101d424400410003800f6103030841101d541ca0f103c00104410f00c041c00000600141c14107010000e84a81b046601810000d0121941560b41d82c1c01d004c40408401003001c0c2e00c5544d41030840155100310b030042c00c51500142002440e60130f200e10201a044031780d944211505007040d08400180d0b8502603980101002800740144c1d43c99030040c010440c80000c02c2010b80c1d0410401440021f410003c54407400e0381610305081d85680313801c0843d00c0e200466402c0800c031311a40c1c178662042800040100720000055523104410718829440001c3c0420900000303500010b403034900f0b2625042c0e0340c0596844038800400c1624ac0014041e08403040c1510070030704c580300d2030009064040342048030040740145008a2914a031601d02d880b8958219034140009102d00e4461348000700a40d80d0343c20a1001320300c14402009440943c40381001000100c89081e40925000f02c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 674769037 1250 674767787 674767823
    0x603030801182904090f060903020601060207030503040e061215070e04020a1227050a05060c09030c010c2a170307021c0c0312120b10270b1204 63
    0x440f0841102e41000c155041c00310b403070380300a42039003010094003d66518040408245000c2907610524001c1c8400114a100c0d030800071f06080050b001502554440d000400014170004119811202c1e54004035003a80c0799200052111203807041082c00c54802d41e50940750300741c1c0d41002030337000702e4281e1510072100c171164060005170300076240c0300c9020a03000452008110700c582c10203100d58141d841504503490080b8682480212031542c10f4075181d02103003070035041001c01c12015402629141ea05410280c01c040002d40d26801c900069040040030401c280c1044007103140c00d6a9544803032a02e0403440c1c2c03108602c81020340c00c0e108140a900402540d100b2801000c4207c1d40c003e82c001d80368241000d101c0c1050b00f031130380c0c0000048038840601100000480c0006503480c8190b44ea0366034070308a075018a07400c1d2050f544544a00ca10070b242c2d140411106a42103404080b03900c0310318800700f41e00c040d80c5011064900c0d0503403000d07842c00c0380041c102809031428501c40380715610900c80c507250350074070389 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 674770287 1250 674769037 674769041
    0x60f0c030b031605040902120f0a0b0609100501051317030903160503030a05160602040b1c0e032b0c0306180c0e060304081b0106051503060307031e06060303080118 72
    0x100000e1410300001c0f10501042c203182d084400710500191001140d159122000c0d8688801c0b081042415082080740a04006094100d180c01c4202102c2030480d5040070290220324001600c199810301c40c0c00503160706613049010001d0010440c9480d10b1110a211403084c2d500d039481140010302c00d024100009440c01c2c0c404540c481640c201500441c2041c0d03140b0815155540200d00e840720038602083c520000a48a00040015084c91416940c41e8880620700c011074250f50401c620f000340c149000017500000c0042034a8007000e1014001c080241003030340c40c41c0b2113507141c00364040b021b003002400504580c1681049080341c0743c1c60700c007040154800000e1001c84440b02c0710400020031aa20031340d402d207040700146412600450103d480c1c140d081d81c84402181640070f000c6160394592908100038139244251a0100b1400e00d0031030702e18508803000944903002408010030aa903641448020011082c004e00203640c0e20803800c002541c0c03241000750410030709224900000d030020341090b080540303038 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 674771537 1250 674770287 674770303
    0xc020433030507121e030f03050105031902010509010309020a0b1216024218150604020a09180212060105040b3c0304050c10120506030a060f0c030b03 66
    0x602604140741810141c43c11094824000c2ea401255175119410840c0e01081d55030506102e40c4814008240c3d03040d0190640d0b10580c0a984030f60401c0540071a000c0c002c4450084550f07092901c256200184001a00285840e61002e500320400c4000428080c8110004010b289154810180c040d034030002242d1184c64030401c00001a04003080641d149614a0440b024410b4903880940311051111100600e601e41c1400681c0305000020900070a890b440c424929820017100c080e000d94880c409200360000b0001d88540e02660740024022400c42c070071415403010700100800c000c2040380e0091802c000e500190b5980014503000c0002c0303402903003da000c03181214103031400c560800c401c164603d100c0b0b04000c0e40c404803070301c0d450345001000320044c60748246840d00d00c034030030f0344030700781824032501d070440d18220729003d04010010f070524240c20072040103280b0040740000c00d555440c4000300c1d080c2054184020905030606080041181c20b90b002449580780c26035003080803240800c01c0560b1100d03d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 674772787 1250 674771537 674771543
    0x8031303061b09030b100b0a03050612060c16050c0916030506010305100308070c0e0108030706180201080c0304030e0d030818070302010f030c020a05030d05010f0b0c100c0c02043303 80
    0x160480802c0000e203000d0840740d100010b5814075079207d58900c6100b01961108800000280d52002004034501d40000c154843d141d1000003455107241c80c220b0903270580318000c0801760034510322400c0070402c802080758180000002d032401c0300600f04409140c01c0c100139003100c000464140000180c03e940300f8490310303110348510510710350031514548031160a81d00c204d200703403a524503000c00440c0049003584030a000388150781c01190384420f542000c4044480703124000380c01012450350100540ea1003496544c00c6032000e01203079030300e1322a8035003030b642152050780240d084020440030005154100c0c83c001d21401031600f400690300300f005d108580b9401c60740402804902510b107201c00091081c0e001c803000c440745004036010b5000d02d842d45891a00b0584100d500c441e11540140b040000d4060784038001c00513550310300e0a1440b01046940ca070300400c081e0300505c0e5914024040746900c03071920303070310640d8000d0020049041c010342c03010800e2600c8061078400d50900040c01901c102c0348601001102d130 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 674774037 1250 674772787 674772797
    0x6030212193002160b030c07020f01180603020d06150f0e2b060c0f050406180302040e0f0715020703110a03050d02060105013506040608031303061b 65
    0x68581da07a054149607207a0102c0c41c1040c600c00032142c0b000500c0400e00440541e40040c82e40460f0081c00800d6103001d6040450150801d005214070302c15880107030b03100e150741140d410043d20300100c0100c1c1c0c0c032011401c10b41070000084000084254060740100303007821070340c01d0500040e0740341e40f030220080901c601031301c002484443c000d03041d02c0d01c40c2d200300348942d000500790955005203c1c0b04003401c2c0d45030550404902442107810042008a218581c002003407401c0220131075000301070140c024003482c4201400d02090f10a051042c9028603008805180c6c018403c2084151081d6110354640c0304404180b420300c1000d40c00324201c2010030015002c141c180d1b00505216055a0301c01c812691003d55094209800341d90100c0025001c1c0140846441254001d142540c0361000040c03c80900f00744550700c03129402143d0000084800c00001041984c04290030b5584850303010170b0040410b070f4040c3c02107020100e11000000031000b10501102e00074041841b080c001160720400600c020032291021403 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 674775287 1250 674774037 674774083
    0x10080702061b040b040b0c0601080601030b0f090c0904060f0507140f0c0304080a050a12050a0503010303030c020703150903200307020d0f120c120206070203092101020d06030212 78
    0x42d03a000030094614040728a2a0b0825a8440c1624441d4110303070031501034500007003100e600c2c0200400040c0d00510544004050951450b1118141c500d0050404d94424004c4000034028131410031880b000030780007615180092030141440d800802002415050407401d0bc3c000c610058441c594014448103924401803a00300340004006803035012104461017404141310014102030140a041846805070010303107103102162030161640400a1640c034280301c01803050001141e4440d0580381501e90600340003846041c030701e0081c0e02e007407550741c00145074240c00d1885105008241c4c0004809610035110949070b4040c410280c03034031440b49041202c240c0d009000000161410801600300d6a02500d42c20100d07004030344907101581d80f20400d140c0482c0e0300b0040c4800700b0485c0c1d4046541017119102400043c00c00fa03600a4680c0f060000b901c0c416406140036200d0095000e081284004046000b15a034402c5102507501401151001380d2180b800c4613403510004802003841c181d601c107000d028421003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 674776537 1250 674775287 674775301
    0x30c0504090c020705040903091503021243030606020102090f06071b030b1b09030601140616060608071706073b1c030212090103021e091008070206 65
    0xb4a244800481144a03081c0f0000307036522644030310403c813402542d5100c2e14505004084c0d4040000703e05202c109441000220080700640480d150452800e4500a4564170030174849500c00c0340c85038410042c400908104020010303d070a00b118000341c0b90701d062107035940d1004240d00700c2c055061030a13001011030f10b2102281c0b4040c1d0003441d50301d200f4254010b4600d00c415912900b425260021580e407903c80301071100480e0f0140b4040340c0c1051010910b4134000488010039240e84061240150752030210040c01c60b943e80312800c3d43c0c54604448500c03107118001e8140500a02001d22030302e480ea0003401c0020801c514000c82c1f00f040540554010f010a41710a41e00315415050003c00c110400c403402c60040701c41c20b580e8107003800c1e4640c504d128520125400d00b007014030484000078038103017100390100d180025008140001c504854908250300c41c6505001600607209113400c00c90250403c856000440801c2c1000d8501a40151041c00a4140400c001d44021205071017010250307100b50001414 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 674777787 1250 674776537 674776541
    0x501240302150c07061710060c0f0302011b0302040e0f25030b1804021005040f1403150906011e0b12040f0c080a140d0804031b0b0112050d030c050409 66
    0x102d1103260407420710380401400c6140c10a1401e404c41d6000404409080344034110340c02090b03030440060b414665110303280010150a024145500801100750610841c09250017036100b603060400d4507110059080041400900a60183c001c00d500909001c01083c3c4031845030031030350f00c10003104c02485002c18403103420103103082c8002503074010507482d5020850161210500700403c3d1800403086100c504061041000006214404404104060108101d007122180d40703901143ca00710404084041d030700d4042401d00c065503616045641c10f0348180b0102940c0010514121450403144120b2469082001104121144100c131403c0c0c0045c07204d141840c00c1210601c0e0050700c03e001c000c0d1400f54581d5814803030b038001d0f07215040f981c000750000828420b00c05071400755114000050700035014819000b40c10900c003e0302c080c1c20001281c26409144403401c030f0340c0b400c0d0b541142100201d91b0f0343c4c2e4000c0b20303514580769080300c1d50300800741d0714010035019006401c580b10780c0340c580a06041c24143c003000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 674779037 1250 674777787 674777809
    0x2010c081605120a030f0e1e010906140f0912040e070203070b0f070f0c020a0b0f0708040308041403010b0306150102010212130606080a030f031508060a090501240302 73
    0x945080c20244000020420412441c3d201c50350740100c3d4599160903005800c80e10040221507065060006040400a0224100c0c0c11102c0315420711168400d102c05040c010945000300800c41031400c0f501d20600780c071401c3c80ba40324100e68035150302e556841003402d03074492040415100d419141030000740501221041c03090f90105c05841101d042c612144c5030351042ca0029100386030303148200014001312a41c810903442c03a070142c80c10849141680b69000c240399006903c1003c0c41300f000480d545500b41c40310000c583e0320b0b41d00813015079100c0b912410140a40d074024414081c0c540381c441c07014402401d041c0140c50310f011004010306260780e03070040c482c100f50481010b25030440d5400c009040030140d40180305400380c011501601042c030064508a07003160074580001c561680800c2c1348800003507011001d91440b1026180100d0810880000000041200e0304001d11900891041000590f4031398480801c0324000c074001c0c400030380349da03e079814034a184a00c080130001c500803050000d410012070140e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 674780287 1250 674779037 674779057
    0x1704120b0c07050322061112031f08010506100306050f04200a110706030e0613030c02120109150e0a0f080d060e0103140102120106120605190503010e03040302010c08 73
    0x50725010340c0d0f54030a4216800411207024a411610801c4041808800e50802420003420f00c00303002c580841ca0180d654120389031400040b94008006200d041e00241d4000481d140e02800807a12501c0b1502d40b4044c0c2011108603014611403107041000764464050b802c01c0301d40241101c1c4464610b1402e00c8054072004c02d082205469101d815402c0a840c00e006000440c1ca996600ca4100ea141d00d0f42820031000758090410541070140500340f0082c0424216003000c03805410004030707105854141d0b0860014907000c3e5008003e24440028070206401414040c5c0c0b282e10070450742c020942a1104427940c0c42c5445009034811441000000c2d0b00880e81d94000e8060030900c1c1c24540c000150074180d503011f4004281d40038110b0010002c000c05840c400d0807286e0108020760410360440d03100407540b40148107a07020002000b0942407102c4440c0c1c8514068480540141c071035105003101f03003001001034400c1034000d6183c44240e941e01c1401200380c2d005d40398161b40340c0082d0f500d2503d64408076004a6200 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 674781537 1250 674780287 674780311
    0x31205130f060b0603011e051f08070210050c09030d0c11010311070803100512010b011b02060c010e0d1b050303040f05160e060f0f0a050621090304031704120b 70
    0x3c14595603190044d600074000384000c45080300d02841d1003002081c0079484203000e80d2520360440020b40c410400b40ca1085900d2425007600c1d50755801c12803520355001034921b0705c3c030300c1e00c828829440001c00041884020517400c4408491101604403240401004040d150344501100078031030b50310a401441103940300000701810000745071141d842543c8141c40705030107070455600402c4142081000d4104101400c4c00801c003281070b403400a4010781c000c44e903404000c5101480340b821942d6600a50b080b00c440003008204210006201560320f001441d80c2c00c020030000040352280d04030100380007000a07441009582144c40707559410a95008044007120740d40110b981062558241102c10b000030122072412414508051061200b80d07842c040301a0701031100c075140c0b180c2b943c58084101c2c0c1200d03019038109613560302200442039000c80061040160100c0c8006000384082c000028000b580d000d00703000361040c0d00b07640310044140304a2080c490b4582d0b4180c4208086005203071000e45c0140b40c030002d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 674782787 1250 674781537 674781551
    0xf020a172208030306030c090c09150705032208011a0402090d14150a27020f030d020304030b070516060906090b040f0b060306091203060a0f12031205130f06 69
    0xc1141c0040158020042030b520200811aa80c6000c1220280e1804c0c00e4582201c0750404182c650458403444000ba8010080400c07030544003c0320100311910307107800c28203490301e07075403402c1443c0d14801c1044200480e03e0f92082d0b004c140d442c81841011042e102c1000542c4420485070107100c043d41003407400e1039028071204079a03c0451020800300e00380c00301340000381c0703000ba0410b01c0b41e02c03420340302801c91035400d0b127000303400d010180302c05d204d620700016042980d00c000405840001c05c501032071310841c2c1e05802140000a1850f4000003c1c0069a20a261411031a941e006049955000c1d600d602483c100d0b2009580d408034281d641b00c000202e0041c10007140ca4a240d441b00e600301d65060380c04496101d203128140301403005904681b0b400c804114040e20050805141407542c1d20300103002200c040c00000003240060762001c200303600505121007503039469580d0b0680c90441c825207503429070206090002e5991654034910070b86110303412505803084e200c40e0304d80703d8800f414041c0ca003c540a42d0356200b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 674784037 1250 674782787 674782837
    0x9010c140307020d03050c0d050a090605031306061409150102190f060c0801090b0a0b1c0b040606020f060a1b050304110312090102010e071d0423030702010f020a17 72
    0x208901440e020303488090b60f0301303411f1203024540040110718104000c0144480c55000358402580b01c101e071207074a00705072240c940440c4034202c0226071350028400d0745020b1000615941d5207000420300321088a5460b1a030782d504d03400064214441c40e130300c0d005030003d0f0314000e403100302d1111820155001d1b40203180380c0340e2259503150840340b0b00001b19021a007a4001040f034072401f4000c030340160600703691002e02e4034606100c3d050a805003c002c0ba170800d0440080090044880d8055001004000c1090100035900e1501940722100010b0078580b074010400083d0b52301a080c000d42030b0b400500c4404004015449104032940d130805441190004400f218460660390100029495401814410741e0340b080544c0002e030840d50701c0be548139036680120804200308c18100d03030401c03503148010b42030f00500da0f5186401507010400903036000d191001c00702c1d0400c2840c0c0010203460110b06c04c1c0c0ba450b03014034941805980d241c0070706200a0810440040d401c428404120141840d20f10102804012041e060 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 674785287 1250 674784037 674784049
    0xa0c08030f01050f0d11040209030c1801090e0a05100b270901061e0b0a03020f040303050903010f050c0901120e030c15070507050a0f08070b040b160509010c14030702 73
    0x9103070060190a030300018802032810728040322901d0021240c803450b00c41113a4900c40f41d000080001c910550340880d5024840e02c0030300c01504200c500800a21f0130295504404000300c0f001e0250341030b1149440428400f07803000149070540035400400601c0e0741e400081c140b02c06412844181900100c0b80390440b400340640c50034100e140102004070003680d02c0d10758005400c40f015640708841c811114078006140070b0400c29004103503503140d00c5850380c2e0a400c140c01e42c013a100f948807800784090001000001c3c160b01030040c005000c0704030000c0c400022591000c0c0181c600540300aa400c00d02000b00392000e6010720b0500041d00c14460021448140c03184102e81035170024000341c400c036045000c01d15040b08890b903226078043d00b1820401e0401005840382e5650310304061005103c0e5440700d40160520011a05403040c007580942c886a0b9840c051800303c81c0040c003078503e16000c00c00c40080410003401035003a02d41032070b41079440085100c0c007500c2c0c2c80c62034220500524114002001100051f1b2506 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 674786537 1250 674785287 674785291
    0x1c0203040303020a1805010905240f041a03010303200a140102120a0c020c01050d1113030b06040b09060f01030e1501080d1e03052206230115050a0c0803 67
    0x1c0d0b00c0040e1103c00224024152004520340120b80c1115444144440d03a00f1041d182c003600c43c162245036032202c0009510120405a40038890302000204480300b5000001005009442042d0312042642c1910610b20105000a000c001c0100d02e041c0076135003040403c84c0301e061000050104035541e000042d21124202d890680903a0b20036500041c81d05035940036200c0c07694004982c02810030002c41440c00c02511382035407003030ba24100400000c0c18181d2422a401c82c0c0c0400c980c0c510800d0b6039400c0710844452440340c07441304480000e081c0c00012820b00c1c0c1445800b2101c100a002c1202d00e64414040091404860b0340c034a050542e80c840030540303d5410002c0703d0441d402c4460041c100d506010b0210300d004140740c01e0700300304007202d2040841c2c2c80701040c1c903000d40000790401150359202e041c40025070130040d91070368001c80c4c10402c5100600c030302034008084000546400d00002401c80700c90801c250000d00485d210b240b1544406e49207180704400900c440701092410040510300d540c1d0b244425442 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 674787787 1250 674786537 674786543
    0x1030602030a0b030a4d0108010b0c0604060c030e030706060806010e04030c030c0c030f05060f0a02090f0904060209060301150207150206060906010e040c03020d0b060703141c020304 80
    0xc08820071070744070010301c2000300140c0c0403802002c920719140e40b0a58103c0300c00c04540a03207208107005403900d03248400c86850401c500c85200444011586202c50340710707900c0210703600003801100001303a150403c13003c684500e00c0c0c08014280b90b6071591568030183c980b55140c0000c0655800c0d041440480510140601a100f03010128015142040091500c40180c0204040034041e00c18407002030781082ca0303250304603410b0808140440d16400c104450008503031002e018000211200d100f00000417842600c1040c0240104007542c9400c2165030490158081541d00411402402c1c601440c01c1c2d90580d0b4042d110311005840c01960300c0c04249130360001c0e800540c2d100f400340c01c2011200c0d0144258009001c101c054082c4040042a00070354607030020f40464051040c0d54085a01a4450144000310740409803051212102c82035001703000794442d442e1001d00c14030340740c8148010f00d81807048400e000e0b099a2071903c0c1003410404440d6039400700d00c9440401e6031a14980401c0c1c00ca03070014620480c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 674789037 1250 674787787 674787791
    0x3051e0709082a0303090307061b0f1a071e0c05191202010c030b0d0f02040b041b020115060207300c1e0e15150403240203010305071505090405010306 66
    0x1402141c0303c06030340c0203198400e02c26082404004020f4600103200c0c2c085480c0c2c0c1c9409420010b4803c1c07104840130890030050402c440004009040c020241e1000c42a11843c480512095036041c004071036104c49040c1c88010700c03000d105070003a528440c06d9040b4100e0f01402c1501c0349055041da040c14820030300c01d0101d501d060000b058010280c3c082c443e0203215582818180404690400080e800c0d420100004146070715900c648015510740e580204007585c806002009070f401c01c9500e0400460a2110150040d0300301801c4640092450004100300d9240b41c008196580c104810b50308018031986007a0001d030071810080908c0300c076405607006601e02130300031034603294141001e92680c02c108118032820524144010082903002015444e400818224148000700c3c0c81d80010700004e00811030158201c0c070102d000300a02004952442e4a0400900443e40c51400071040b003060340003d20014040d80c21a90003040418024150881c020081d072400074600f04d0f203800040c0072184207800a0300c000d5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 674790287 1250 674789037 674789083
    0x1b091804050c03070803090105251203021801050415031d19060e0c0f0919050f06040516080402100c12030c1b1e080f0703081603051e070908 62
    0x800c013031195102409002014501e042c3e506800600755124440361007404007010f0107813003144120040040c2540341d00c0a1241c004c0c9800303243c01006500700b5000610085403030410139605600550880c0c1c2180c0e0400c2c404d009588219038143c1c020141c0c0504103001001041c3e64842c02202403003030421388241c2c0c128010805d1510b0030031004603600c41d0802001a4882d00358682c07113a5500d01c00031141103080700c0c50140c80d600d10300300c58058420704541c20901400c080034082144c04104005e44030309802d0300d04000035903492003049190141f070002c0da004606034502003001343c00d0041c042c0c4000101d600300318404020b1652200500d01000c0d110314000395403400b40b507220b9940405604030946e1280c900c8143d490540d12340c50078500c030981d01d050806064035012420051050103849101702e0400b1003684499090401600385101100d146100400c1c404c2000794450203841094012503954a842049589035a00c58402107000b4248009011100394000f500d0032007001120b58001c1c500420000103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 674791537 1250 674790287 674790289
    0xc1207050c040905060a0c0908010e031206040212040f0f140607110c130203090106030f1a060d0c05060304150f090c0509040b0606130f060504050909061b091804050c 73
    0x4001c068445610850410400102040700000e0141d009403080c1d00000b01c5400500c82540c8a0f20300d588000d801e9424224030110f009004000b91510802c45050540c8503920001000102e2080c0c03140001c1080f0884041800708001002c10800ba900c11a07512445044075161000402d030002100e201030381c070900401c11110307840911444141102c0c0003d203c80f0000780000b507008000c1c04c18408150783d02100140324500c003500241c00854010701c0e4800414020700341100441100410754904142000201e1804d0034031000180c40c0c0790b04840202c00c1d4030700b072204009140d17201910503518000440b01030801112544600c0e111003114080c005201d00e02460170704010745072350740f1036172184560070100008298078a80a561140040b2500795440e80441015075050b17406802c1a18118203484020401e0ba4021004005880040f5200c003126902c84800c00d07500d0308100c464a00c564070500549200c62120f101510602130300a0400303a60001c1d5001900d420070084400381d5407980419070f00b49030707 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 674792787 1250 674791537 674791543
    0x14010e1009050f0604080f160c0801090c0e01060909020922060f06030504082a1203060405090115091a1f0305070c0b01050904030309061b02011107030909020f0c120705 74
    0x800040f100502668501501c03125a203004200c15491443c4001541c12207850500040800540e0b01c4401d410b10141c4400515000340514a02200e48401c010408200380d0301c07aa0b4014101c91403603842d00c0865007080d0340071020b9080141c0b02504034400c00c5440d074000b80e5002e21019600518103000038450f1501c0c0c0c0441034540250b114900f410315040610000c12940f070300300c41141e11000c01c08180c0c40303060788442558601c0c00400483c40e0150744c180b01c0d5500d407070b900114001e03481200c0901403511100036a030708031050000d841c4000f000b040320422940145030400003905041c80100390710035403074501040d090400c45071040c0402c0025000104480d8140c400d0315007100080ca4841030721481c030744d42e01c0051001030248604c90106500090205803281d0082070840350b10060601005013503501020b015071007040303520b0255081a0211000040700c5054408581c0c01d0355401c075001e0704d01f0740b040009500944544c80c090500304440e180d88102041020414802c1040c4a13603514128180141 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 674794037 1250 674792787 674792803
    0x30e0409211805100912060203060306010509010b220902040e0103151b03050c0d02070b06030c09160c050102090a26120712030e160e0c040e0414010e100905 69
    0x10b100307400348080078540420780154203841d02900d40304440542c4010170340d0401019442902c60074481d1814208103ca15000707035005210a40c2116020313600c8504020fa01042402070500c0e0308801e10607942940e20382034100c2c1348200f20210080101e1b441c1e10008040e0b91054201066006545004108220005150380e900c40c406050800c40b202000d4084212902c908240808140d00c80c0c010031000c8511400b1500720101414046540f02824685240c100303008807500f034424081c200107540c450901e60206849000070b0040401c2601e110501540d10043c0200c06440943d400c1c0803400c142c0d120404400c018200c1076405a03003180d01d80c0e0302040d082c00182c06468807500400c59005e81206140c0c10b070341056500001e804002c00c60410110700418003000100058032030015036600d405501c100e0813013564107500a604c495510354034401ca0901c42e610031a100300714580002808141c2645031406817642c00300001c51f04850040910b07140c14500e074402440b0799038822900003085000c100c119 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 674795287 1250 674794037 674794103
    0x1a01091a04090c0308030a110d0507030e010c02060a090f06111b03090906010302030408190503181518071a0a120e2508011a0a050a080606010c030e0409 67
    0x800352586a5460014004003803000400f0105d0100120b064074105411007400e1003203039070701c0580380e03401031441c1c10180000342d035060302081c681000d0340c1d150702060041c10540b925640061140da11540d41d1a40100045d01d000d5031030107d52281500010710900078000004003003400b4548516410725001084400000300c00165031080015400c580c440a44603540100c0900300103880703a4490400020501c07500000560740c0292030754824103542c0120156001c0d014110014489851060610703a03200032401420704500c4128000075007881c01001e122981c82414003e032307815240e4a40202e500f1000e1028407502231280860000e0169500c501e0b074111700c2c0c89048060140c9400d040e50030762903c3c088944920a403400140c4d119107000034020203002008800001c100c0b013210802d08001d41545185414842c4800c048000b500e480d107840745500707030740400b000307001541c40750401542d90340c00040084041c08800440700700203607030394414000000e00074082d034a0051400340103040e010019965207 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 674796537 1250 674795287 674795291
    0x30a2301080703030806010306090207050115050103090b0105040209060c031303031e121a360f130201020a0b0115030c090602101104050303040b0403060b030703120302071a01091a04 80
    0x4100c4441e0016000b01100e405007010006922a080120701911540d00072901046c00040c03d44204081544500600c05900e07540140301070703d0340011004da845031000541400034a0005120a2400b54010114404002c1035140342c11094030689040d60801c2000c8500d881c01e11404209048e00505060282c0340f502135032141207082214040c2c48000d00c0300c40403840070350f10750100a4500f071040710400364017401810007018844242c041d1100c17600c00095151640c0021007141500c1d54080700c034a0055040c00d80718607446d60b4207e11820380f65416041a4114402c0c090074102007465501514045c0600302c100708101c002e001c03005030a81d003044010a0410045040420841d40e01148803803a10b00c101001088442244c5040c1c0d407140619048182d140c000000d000070307040110001482100d12a100600034840c1c46402c1544824151001070010a0080007c41c103691080e40240708561060315a001240d12010704010000002d0704040c40c00c0f503a5020340310301c607442e65210740345041c0c0450742 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 674797787 1250 674796537 674796539
    0x1e010315060603021303030e0117090106170706170a09020a06030e06130b1b2a1504050c010302160c03051e010501030f020114040e0a020a112e11030a2301 68
    0x30203440c490240c8801f40030402204040c036000da2041808514100700301d40484d00a0500c1c4501600030f201d00e2240700c18002c104145115031904c0400c1050480307105441b245000800c000c43e8080b00b032801031000d960b09590307e125100513615008488080d01c12030758009809039101d404645458000b81005114a100c0b07581100003071180c0014961190100c98402524082c00070200280d014846d001c800c2c25601c2c100120245150381c0441a038442c40c0d20844d450090a0181050108001d550181964010405400f170950003900106000f401e1069074404000168684008011036030304110740503000b509030a058410100c0901102400c900001c010f507501d150340b22000e0b0440f4410082c14424400103100041c804034080d54002e0408010000785ca00e40740e800c0c00c00a52000b07151001180105040386140c4074001110b014820401480c070b0b4860341e6000c1003410842c402000001e502e038462008040c1c11004401950060f9400c0802081d50f4100030b10340f00680c20140b480480060190700 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 674799037 1250 674797787 674797807
    0x314070813060c020a0c080109021906090e181c0816090e040f0c06171006050a0c0633060e1e1801080a0b150102070b031e01031506060302 61
    0x114003841580d0007800007901c0f02c000801070741882402c038400f81081c4594400012148019008452141e100301d440307007542441ca030f14a50204015010701c0c2c0005604a0301030004228010300181c020030038007003140484640340001c41c40c01c4c406c0d80002e042c2e81d0b452200c03000001d4110400307540162640c2241c807440b0594541c024491161882984c1d008141c5401041c04e100401c0c81101c80d01da040a000403100d6202d0501415415600395440080d50480c0d000509400011100c4010b13560079a45d0b05250a20a8504680c544a02c40c0180d800a60341e80c02407040f2641040403521406503041100c01030750015541000e444041d6002c201400080d0410885d48c0c0c3d280c5012a0034086c00803590441103806101154648003499500c802519203070002044c0d541000514101d4184071781b0001c0d01c1c1d81d43d0160b225404080c00c404280c05a405202d0034030140000d00c0240d0341c095114681c005801002d000b200c1c00c0c2e840280d005540b01e050032101d005210180e801000060251401c00750710b4549110 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 674800287 1250 674799037 674799061
    0x2505040803070807020604090203090318040501060e130e011509060b0301082a030303040609112b0311030a0c0b010801020306060d0209041e02030711161406041503140708 75
    0x502d000309681d000050000456840030140c0d005806541001c41d241d241c84518150381c1d80c082085054849058910101d80346020b000c0d01c0e040c0c1c0c10f15034880b21072000ca0300900a8480200111000c0640c50324a90346010009110355000c0c40400381d10300c50342e145050300c0081101d0441e081028442e904100500c9600000200740320108045d88a001e1412a00c1c603070b811b5040b802d1080703254140400401d0100380a401e8000d0604980190040c00b1f00280842c200706050601001d4441c900c0422680c811000c0000070550700d145000c0e09245401b0300f00e4503030081c2903030f1002a441d80894500c03e14102030014828040b405011154021469418040002460b5020318030384000e00030340004541071991510b0f00420030310f804104e911145854243c1044001c4e40003151680300094082145d240d1044000926000c2c52055841c0c42d071099050038098041d5102d5100c0c02a00428200000695101803042d00202d0000703656000a160652503000280d55001501d4881000b40c40320a1104911000e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 674801537 1250 674800287 674800297
    0x203070c1a18121e07151e09122007030b012d050f040902030102070308040b1506090d23010903140712032708040f06051213020114032505040803 64
    0x18070401812100300c444c0c8a01c070703103d403980c0202580301c840d800d00d81038044c507000445001402542040c9038000d0281c5003007103500540001c2d04140f982d203000490940101000030080484900c2a044000058211858443c130350b07104466103048800100f0503612000030341406004050308084003511480460034801040c0e0103180d200392800269000960780ba54880c1480760382c0036000b50348414040c01c01030000e030790884042c0e841c40c05401c0010344083d14002490081d0740c1c020050740c01d011300041800000d882c580340c00c440003072591400f808116401d0241103411002040007003010205464002c028003401281003151038810302001c0000b910101451242a00c01e26001402d0044e142c40920018007441054051041c9402080184100c44004106440030068000f0405960f410304440758030a506810071011070600100704035512280759404030600504d0143d103141c4000310003001546c4180c45c88558103840034841d0310040030401c0c00c4207950015040c01c500b000c0c50045c0450700c0303100b4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 674802787 1250 674801537 674801557
    0x302120a170a021f020a0306080c01090909050f03030c03040c1410111c020d11060705040e13151a030a08031803160308060114040f0302040203070c1a1812 68
    0xc2068100300d07201308051303030032034400c10801e4420101c1d210b4810b000b0f501c0b400c0303d800024104240481c0102000800707500010060303544025440ca003d261a001b0459840100c5490107072100d01c205411040001e10700500810050b1941c900781490556010704680d4484039110608900b04c0c822650b1740c0009607211071f05402c160640c841c0b90410300f8100020110b01c560031084079074800c098254000340840d0b00300100d0b200c1c2903409000c60b41c8990b4a100c1140d25000046013080f0500401441d8000309410020300401c40440800e19a18448070410050014804c190ba03404450501d60918081d07001d0341e60141d001d8070442c0000e0321070141da803200800344403001040c1900a8810402001140d1804003002d601741e00341c54184c40c0017040e980c4180c0e50f050002e03912000e10312100d000407040703174111441c1c101c00c05c0010f8036603420f100294000a280394203100c0340d0724190700800d140440305201051306520303031806458000d02025850010f08425802030f0301c441181d0300c000c40c44000700e80004103 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 674804037 1250 674802787 674802833
    0x1052a0c09100506090d050f1606030f0b1005070804213008100e2a0313060b010509041d0d0e030a1b05060d1b030b010f080429010302120a 61
    0x91a03042448c0740c800c0c2915090404d104e0052848079041070410590281d843c1903030244440000300f0610b80030b0b9400511903075405800d1004050109010f4002010082d10404c140c0c1d05050703480120b0050b403a487c144154810703201403016001c210000241009500034a000c1d060003800784207914940c140070070542030a000150020130769056516010000070600b048581c101858540d441010030550344500d440c40e440960703058401c68100000340c1e441600320001c1040102069200c0c800507040c240c0000d418482c0402c00c441c0e40e0788a50060041060030b00c04251009025914154a001c1c040f0f000801040005881503d0310707500401c038180e0880d00031081900c10040d404180a03110381d554000d9500c0140010b003400408000e8000c4030488011008a0700808142d4109805450310441203c4c002544560003003109402103401c00e40060059841c00151404050305040e130800074940140e284c00b009004000310700c4c1aa0601c241c141681015100380e500700d84d02c08141e00c4d5a140c80d400114 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 674805287 1250 674804037 674804059
    0x10612080a18090603230109170d0b0a06020f060a0b060708030405010605041b170103030f0f0e060f090301060927061424010c030203040501052a0c0910050609 70
    0x103202c0510501c0580036005040004c60360300d02e0000307008441040c0d60382c40304a1901c4202030192040c40380420703198010b4088040c03041c145105003c0c980c4145800b404076540c1d5200b80c40305840d0744060b18042e2129400610f61140c00b080040c1c60a540103001d04003075410508070940d3381d01c441055520f141d90020140740c0740e4945182c403038050804c1c1e400060300030b490641c0810011404480100d07110341642c0340c10121034005000c4070380390315090001402096202000e00841381c030690f000c01c2001d00d903282101d1100e41c98400500c40703600ca141014481800821066182d1034203104940041042e07071000c1207103120390201140f940040070000c09059191440d17101c180141508100c20300d00440c1c80042c09460800e805000161050380081c4074052020960315555004005507040c33140c154000314282441c000c0111405da0003840e4505042040f02c0810849c0c12881e0090450740041c1b1010b08a140b86501c00d201242030003e1156a081c0f4008404000640780d000c1119103000041c0c503d4400e030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 674806537 1250 674805287 674805317
    0x90f191104030204050403050712110a0201270821040f03063204150212041704030503040b03070212070c0509040c0305060702060f09070302011d04150e040203010612080a 75
    0xd805140d01c00380d000390424003040201a48140101010f91290095408030154110100c4c0d000302031440420007613000062440156000306030458500c422451034401802c6d550300311500b10b00f82030b48254110380c8100c0407443c6c0911034000f07406504901c80341543c00c0c10b00e00072200081001900c0054176050355040000c4200c900e4400c03002504000503590041c8000542081040090031282030311000000707015a40e1002d224001c5030001d440c01d400700e84081e20b440c2c441081070b11140703142c0c11004400300070000001f101400504001d00381c000e010b13926841c00c920042c0c14400762222103000d0700d40804c45140002c00480c2d0130030958509454410f85607450f880c10010030509500040c2181c4546001c10050fa5400070340d052151380b400340ca001300380c1c81d00c1d41c07032560703d01840c00003e0114913503003003c80c01449210411004104014002b103504007450181c0c1d40034000c180c01c00c802c1c08421074100415400d0074040d0b17000900340e1a100104003001038232417401038003510b040780040215107000c404c04 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 674807787 1250 674806537 674806571
    0xc030b0114030a14072307260418050f130b01060f0315120303061e0905250221070c1203030906020309030403030908030c190602040e0f06090f19 64
    0x15a00340304040c00c40c43c1c1440c04006e80300c4003502c0c401d001c0c1140c4080080d0540760241d400d48921981c800881c4200418a0041e1660110700021164550109210000301c007600311003400b0800d44568400241402c0c10076010f28002d400800c0e1401000ea102d810400246201280c14110760341442c0c48002c0e00040031089014110720100306104102c0c40d00c002c0307420307480b1180d4028003520949041150a40e5440c8800102c0f4480b81d10f080c0d5440c4a80d0300f0004041c540d0001a808000c030a10020340c2c0d88164100c1c1c0403195006070402c0143d02000019200e00c5050782c000c1c6691580844c49801d0080d0365940c401001c0c0c190080f0b1008280c01550007042501a03048030440c291701103415912481d1055030180c0d26000f81c0b10a070000b4414090010300050040201d40c88901414050000d511901c06403d4803c046110100c0d80154200800180c05000d0704090307015a00d04102031841c0d007803d40810602110140c0003190340c881000520100502c0511000031540d08501c010544201c01c0e0031901c9 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 674809037 1250 674807787 674807801
    0x31209080310091a030c01050d0906050c0c07170a020103181406060f0f100302090a090203040524252c031203070e0418061406040c030b0114030a 64
    0x28184080140081406803040c1c401c1070f0b4102c80c3c01000301e4614003100d40e901c1041480000d0b0580c0210394200910b5101c2c000500c0c085147e89800b040014031981d940c07044403c1110540031701d04010400c0481084e05004200c000d0a603180031a562503d103e40042e280c004001c0002c2c14555501d465410041d05000301c0c050007900301c181625035440200302c45803544402c8824502c6494040000070f0300d807821051400324010080d0901c05200501901a8001d60000c140c040e4050002140043c21f445280001c41c0f041e849034018001941c80c86031810300b03459002114095a40107002008000c1880c01c042e408481e19102481d2070724894800140c1e13182e5504406c000035514a1081e0021510001c601c2260399042078084500800d00c14603040d003a0301041d54980700140141000b01103e203081e4004011550004140f9010503a803039440c10100c40405401e0f400d0305246e2001c010b030614051082040b00700392400c0c203010100c028000204503a43c141e500c41b08030800880455160411603010342 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 674810287 1250 674809037 674809043
    0xc0803030c25150608010b010203070f12111c090911070f170a020609070b0301030b010b0315040204180b0406050d0803130204090510110406090b09120d030e01050a09020607031209 79
    0x5000c0b0049800380d001a0a04d409001007660070b121103200d0952001080703400351a0440846581d001e11660b4050720b00700015511003c0100750204010110818002d0340382048901e0b41c0802e0100709002d01520300040c6074408081145055005040350303044504844c41c550b40142d040200c0703002032070410391603a0000b03a00000c00c14007103808a265600080c609e40207001000c02c680c425542c0d6413000001d1710003400028140c8110000422400c4040e102541d0410900c9821000c84802d490100d0100e80050780304082a60b40d029146a10b18502d200d41030602000f942e040c000c42c0d0411011850301c08440c00d008210031030010009410748024a01d5011140e0300401c14460828281400f65491851000d0941160302c0d05070b03808907a600c5841100c040f15166110740c400d280c5441703440a0980c01c101465500901d01d9900004c3c01036080c026915004442d40780018114551191582101d030014030b0300034158030b0301c006071025945100503101600e40c546450340a000740d01078a9805011003010003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 674811537 1250 674810287 674810303
    0x3111302040906050301140709150203040515030f070c170a2c090c040503060403050a0309150501080c0f0f120f0f0c0405070206040b011802090603130c0803030c25 72
    0x1080301e0216401a0040304c40407002401403100008101c41c1603a000c0d10f5003004501462010802c059445042000800303007401903030f0410b41e40e480891110300000600b28503d00d000004c0240c541c0c4c2910311280c01c82458030b800c5a24860a95641512107910390b0840d008150203e5000c3d003a078400c8030303141d00e02001c4040001801c108c00380400d42c3c104c08000c03030038806c0c8a22000144154a00000e4400701d13003004009251a1712a520150b40303d9200050f484101a01e5646003008100c0442110410070685e070342c0001c1b0356140c120810300b00b0311414013044c0b2a074850780400800c0d41da0814508a0781c0000c44d030144040400e801501e1030001c0200d6601b91f2402507071100480000082002c0f040d0150560301400740b5a15600d080f80c54080c00c45005082c07a41c0c1400622035140d0304e824007441b41c40400301c0117140850080c005040780e0411540318065102428200b8204081d4048607001424054019800c1d801c05103155489401481d540422149240404e400d03c11024000c0e10307480c3d42c02017a0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 674812787 1250 674811537 674811539
    0x31505120d02012711060d09050a030905011404090209030109120507030917030d0509010608010603080405180601020604080c01020f21100510080a09080f07050c0303090a0311130204 80
    0x221903254030300c508028026518100020300c00880944400d610445904c00c0c41ca800d1403a651070720281004a14126001001840607140326a00c2c1e100b03020000c1d000d0001002504001e280c002d120104e00d41002d410011150b8000c013603201818141c134141ea0f05044050b85460718200842c0c010f103c50f000c05080c1d20030240035035500b9034000000b420007900070f654080c3c205403a041c2c003070a40c0300c01c203036205000d0b48200055581c620080e484150410784160012401980d00e000756401d49405030001d50340d020000804000c0341c90001d1503c079015004a0030700f24146040c400103500c03008010300c050108100001d10b03c00c0340b80700b03604945100d015030130010348401c90124401000004100c1040b5a039200da0049240b80b00b0444000d01101c00040c02280c41c0d841c407002c1120000c0c000b03080b000e0020784480c6050001038000700030709079810ba016490f64690b81207082180c942134031315001c280203803c00c00103100c8984901442800b030ba900100700b18070030030b6240c000c602c0c80d00d8560b002032005ca1002c20 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 674814037 1250 674812787 674812819
    0x2211070b0103031701050402090d030f09051909141302090c0d021605010c020606100315050d0602122401320c070f0b12130609030f03050906090a03031505 68
    0x6015904d030b80380700c0c81000ca90fa2201d081c00704070b208401c0840c3d0701154203012040006d120340c2811000070300e0b620f049112141d031440880c0c00c1608080c0c6001020610b10410f20968020f44181e4001031003960b0030b84402cec186403020048175099040b01a0040038224005407905502d1011141300e480540c0f411591602e00703000e0303481d041c1c440200032240740d400c02000080c207520003d2a280201401013062003040c3c881c03901500104040141051240c1d1450070000300740d520300a50352039681c0203250142c3d0318038040d104401d034a80014851281c20703020329001c04000140e01c110500d26502800c3c410580d4a042c48409080c0b2a200c2d03401c002110001c0c110007000070200003406000416100300c8682c103032540600b2460b00e1a03801480403ea506000258142c6c00390301030b50b03400c03050079020300b207580907581c079007901355102007038183d010034070941a40c2403c3d94144141903110b00000094980c03804c1c0490036a40751054680040c04240c0c4483c20850100a861885401400c009010f0124030840d08 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 674815287 1250 674814037 674814047
    0x30f07080606090105010f08011404110c010902181005150d050414070f0501021b0a080601090b0906010f05031f0b0c06041202010c12090c0515182211070b010303 71
    0x360b28502a6188200000305540076a525a10000c03894840301856802c2591070000381190030754940d405a1241c1320742c0385c21000503008000414000d070003c101a0200c2c01800182c500d00c501c0700400c0c8a244042180c0001d603444190140d45044030309207140120f0760346d00c001900070f00c2042c13140549842d0900081091159000701c168040c0e90584212942e5055452071000e024400d007030140c1c10569406200158081003034080181c0248040c40007521021b0f054a085000d0700610340c60742d039504814805e841e101910315844182441d000b0f50f1008007840060050002900e90300710b08081407480343d11001d480f02c03448007414030100d01c50f031203031400c07186581e850500b610141c0e80c040f07550f03401170920791042c042e118854209403105048000324900c280b00600c0202015501c60130018004200c55031350f9a561448808105900c80c1ca52456001d540e0b01140d84600d26031140c0e1469494001c25010b05592441040b61100005a49426400c1014051045a0b0010980b1400c08000f04c1095007003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 674816537 1250 674815287 674815291
    0x91505070302120315060c0f060c0d1407050a181a070201030f0b15031801020d0204080f0a0312020f070501020f1909050109090b030a02040e3009060702030f070806 72
    0x42e908450514810700c40702d401912042d500c40d8240c0d00c2d840380001860520302c0c014802d81300c0366401c4800d10003100549a0400c001955518400500000c0400f60310b4014080c4064141c40c0618920b21400c10759009010382c801c240d0000c043c0001304061034903003462034180d4401461700703580c00da04080c80c4018600c0d281c2d010f040103e010925040c9e1120000304a03104409030030070080d0421885680484c150305031600000c1c074980c0321900140001c15581028009040103100901016803500c2c1803407100c50a090038000b5070303a03080c0d024552050209911802280c1034407000030300165920b12500946090f0300c08c40c030024040b580005a115010540e480080c0103641d038015041074401140c041c2103401031f0251041c580040c00750034040c000302815a0210b40300c254018111110600203901190a0727030300c1090105000e410000b0440102410f212010481c04001140916614900c128448440c01a540050b020f480042150340454804120800799801c0c444101c4080c20307610841555a0101 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 674817787 1250 674816537 674816543
    0x12030a14070b0402040b03030c0f030405120613030509190f1401021912111911150409020901090e0a0609290906131d0c0303040e010e040309150507 65
    0x62600c0d200300d0001090180d410180d4850707404562621503408202c080c002c4041c4443c3d01d40420400951034501c00c01030040c6400540014644075440c0030200642000d92000c149103640007482045100c2c002c0c2e00314803080b154142811a1940250800f0071403080b4104001121882c2a030700110306100f403251070000711000103960700f0541404500498842000b20040c02406491018a0380018200c68030568115a40e240150314090644100e52800141494083c1c000b0013450300d050500c0800ea07a07411107903006686044410b0740e030100c0f01240e842240b04002160b54040b5082d85207a10234210f19005004c400c1c1c5029a5060800d2040c4c028203892080c11103441c0352100c40c012964501090f05050b4480c0b804005500e04a0f00a0044100000300401d6005143c82d00101c0d291260348601c2c1d503201841c040840b500301c2d6450700d4038a841e00c0c0804446c442d520030302081240342c0c003150f07005040d00c2d20174081528a8071140740c207440002103074011011084c01a8029508683d205000c1d15070180 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 674819037 1250 674817787 674817797
    0x4030e010c080c070611100b0928020403060c0909150b030a02090307060203180d15020304050f0123150625081c0b0d05030306010c030210230c030c030604051512030a 73
    0x4074107140802100e81c100d40f6590090680b00003d0ae40c03114160a128010a21600c60b615000b00307500181e04a0380180c100b2161144c0e103030344034a0050b81c800c4151000e01710a69003000720318510075060042c00400e225448680b1400400140160441c2c0c054502c8080054220b82c1031545880c8040e41701d40000b207801084650404059030b00786040d0000307003a05074002c5810f56440c11071003d04d001070752000304140c2e090300c40e81507445c4171400d007445900c0d0800103403039004188042098100911520207040f0f512105200c1c1d50124903555104215110a900703142c11409103082003201044007290001b01402d10400440c18490040d0340c0298680c01e225000403c0064100000c00c111907500003002c040c105920600c001001c42d40110242c3d030109020f030040303d0942c45058035410a86150003240c046c5c020309881d10710f00c068a09040079030040460030000d401d51401d1000751240b03000c0208024890342c2c03120040394401c9400c0480c117080c0000a809080d0704492400410744c1d86d8000301000002070307 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 674820143 1106 674819037 674819053
    0x150201021e090f041e05070908070806070e1c03230310030b071b0b060616030807091403100b060f070308060906040504030e010c080c070611 62
    0x28200d03126060b96000c100341400000016101c20a0040e030810010b001e104c1507402e0b403003443d800021703000541ea03600c8100c100c42c01c40142e44200114040c05d00041880040415210700ca1a0541c0f120704400b0401810b000c5105c9448149043c152042115200001d12a940300603040c041c2179130f0a0b03401003034103003126455801900d52001807105054108100300001d00d03016400b640c20700f0001441007444072044404c90203400000c0440c181c100c0020030300e951f05000e035100e111080e0150f0745800c40303e1030081c00b84a030583ea0f0300c0205e11004e4002508480c18000303c5101c001c05006001c035030f50088082c0010300425180982d2102d0180960380750000414041e002407806680e9080b1142001c900f8021808006014a40298109000c10001c03e40010404440c218280b0b0050200d03429414007100600400007220f0850003a01d0000800b240d0054290851070340010565000c5 = true := by decide +kernel

theorem cover : BRFrame.Cov 674640287 674820143 := by
  have h0 := BRFrame.cov_init 674640287
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674640287 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 674640287 ≤ n) (h2 : n < 674820143) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
