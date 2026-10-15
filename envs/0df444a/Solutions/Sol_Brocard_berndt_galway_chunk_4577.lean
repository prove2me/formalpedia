-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4577
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:04:10.320236+00:00
-- url     : https://prove2.me/submissions/6df153b6-cdf1-44c9-a0d3-fbf4244b9ced

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 823021582 ≤ n < 823201438 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 823022832 1250 823021582 823021597
    0x82d01030201030906090b10081006030209130819090501090815070810032004050717190209030d0c03021618020f040509070201021e0c06181f0b130501121205 70
    0x401288207201020f5182e941da9025a0402707400c2c1c030311441c8245940c00071178406210013500629810001076a0104403409070304541e0080018900d00b100180c283d88151f08141e52402c0407441c101024001d550b0701082c040003805814000f0044610030040800b8402d0780101000301f00440800000d00c80130000d00104000c541c03081003421036040d10b00f0b400820f0b05c100d86200b40190f140c100020b000074441d50041540481c2c1c0b481d07400141d11030a60842001004040351000507800304199482078800300144000d8481582d40d031000308400c2c2c58001e08044d0241210140704108100600c480310a00981d480e24003405080141d030b54050710701c0b14800e80541d501159128542d0703002c01940f9034040d00148010215499030900c01002c46a40f444180a50808100c1d5a400903000510201c80c0c40c030809041200f060444502c4003010b580c0c1451b5414403a071568240380c54410f0700c5407a0408105081100302000c5080c0803c1d0b0418a14148040080401410000c0c000500717085580c001e20455000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 823024082 1250 823022832 823022843
    0x61d0406083703020303010e0c1201060c020a051203131710021806031003060e01051b0705010902150403061107030e1c0209040f031b08030a09030e10082d0103020103090609 76
    0x5002ca00d040c069141d0b0400d2203801004800240011b034a0380c000c1c0111050031407070803140380d0140d081c04822941140f1402040780c0080080703034049075940d14214207030a1039504100542ea1900061404440b809599000d80310304105100404200c00001c03446403511034100c000141c5403d0450303680b003d03000681c040e140d00b00100100340140d45600084031019030b40288070901c90304400b082900d080328412034403200a583c00d0004081c900c0303080d600400b80540640000b04094002c1d4000032100f501c1910040000e00d00040c1c03c204000b41d60040003d18032000340b14038141640d41d100506288448000588660030354074603481c0c10340c00c01c5d1040d202550040c1880d1a14038091a000d007210b01c141200780c010405204000c8454420f014400240c00d900107407450944c2c417030440c10030290800381e00840c21320054a02d00642500c80c0003941e48102a259a20030f4682042211907001d00142c0c12000d800c00387c030b0071440301c80034841000c99044a5081c80d00007200003aa003416001400c204000501 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 823025332 1250 823024082 823024183
    0x50a1a0d060602010c230403020105090d021e010f020105090606010c0c12030905011b030c0206030603030d050f10050a0321050c030d0506190e0604051807061d040608 73
    0x201160f0544c030500d00c1d51583e40302c4901d10030808610418101030803201c0b101ea032208000902c01548210081c100284000e000a0082c07582d40e40000c0c00c81605a1380003404020800c1401002d40e8810b5068040c0311203030008104030300703100720360940b6075500402e40c0741032018010360201049120025032005003640340c820002d1030000c0c45c3c02000d44c8124402d09000a401149264040488102018000303034551550005d41c50140e0910070160001400f0035070601044c4840652241a80511446007a41c40e0501c0614039004c0b280e0903460f0050b82145015a040c0b00050000907491240720f0894030945113a035000b01d002c1c010844a601c01d04600e0881070002080300207181c66141c1202c1e005105c11500e81408450111112004c601c2500c90710b680700d501140803460340d092a500c803d80040543c0d820910240c40341a09a01d041802e41c001c4001400042a5140600301c10214038040d030701c05c80f0140900cad894603a4560380c600340528040c0c04201c210710301050040e030b181c0f50750b03000c440a0341c50080e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 823026582 1250 823025332 823025339
    0x2030918011d0c030604090303061806050910050d1b21150b0d0308090102040518070e0306070e1c0b07090e01080d021f0209040501030c1707050a1a0d06 67
    0x16120a802c0c0718540060302d400c60007410a824040b00030340729400e0455820700716503c4504200c0949425401601032640e95040811850307401c0074901c2c80400248408100c00e07103080c007400b420110051002c155180440b400b44a955992154400040d42142e005e000242c50340030a100240686c0d4001e1103109400003c00d102110500c00400f43e0078040c181d040701482c00b043d02e0200391801b0511856104150301c01403c0080d00070101960000b01010005080688500100d4030000f00300d0161821240d4400810190743d41c8042d0502040c203080d00903004505208034003800ea4000048814424204d01e0080001024010b001c0500e05410041040103814580c1c0081d14020f0503001d0038440c84400300005c1040c00c000110b4000340d5150f580200350400e071a9806542076020b112150305615001c004034060703a500c50007454041c500804000d00ea0916010001940012000c003000094106d05400c1089564241c00305003210069112042c1c3d0740b10701804842030b03109046001844903d4a400403 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 823027832 1250 823026582 823026619
    0x40203070c2003030d23040614100f0b0c0c130f0605010507050601270606051306030516080a020c01020304050f060601020318150403060f0c031803050403060b01020309 74
    0x415580b0701460001d0090760302c041c0c0118882e10b110201d1505a80200409001600c65a000c0541180c00c03a8561181200344003c01d90100c2003942c041e030344e2a4840e040c40c8112100c0c000065004200d18560743c034502c1c5042c000a1203a0b1180c840e1003910180420798084a0a0510900700d4041c0000c06c11001d084600212000401d107004045015500c1c1c0072010510394094403c483e031b034540000007002c860381b801000e0078415848220851408407000170340a083c0c101c42c0100c1000d001203445940d2a4107800914240c1109a5400402010b04010900c00b0308500d8021454003169180740480320390340e0300c41c00f2001901c0b4164181103650f100008000510101041c2c08503c034581400390b5005840303000049035607003e4030251425031812590103081501d800c01c2803110000206100c3c0d0709056032625500304840f024205c82d4a85078440b4804910035a06210320840358184203800c844200302c07928010400c3c011404014889965845140078a80c02001520340620000b0440c0350810f1030007001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 823029082 1250 823027832 823027847
    0xf050a050d09061b02070617090f0303090609010f05150d1e050309040608030a050d0c0c0204060e06031c0c03080a06030b0403050d050c040e151311090109050f0a0302060c010b04020307 81
    0x291114940d141340e0b03801e00d41344081203000440d209680c3c0d0010071500c070324520105a0019020305c91030f202e000241e16a41c41d00340041e521400d03010014110515100400c1c030b0030340702040382c04c00440b0b150104002050115202c111100101507038040e00000c6c8501d03240c5242d080c840c000c6080842050070754010031030004020a0703442010f48092101a0341c0b81c203901e80c0c0c0d021310300e9564080751041c8030040040302c0300d900030031007403002d854200960340305600070408440c0503401001074190740d013040040900381001096061491507074032844101e04c42c100200b401d50003082c010308000305903010502c040d116411500c091034100924004608051601810960002089000541c10040000d003122815026141110038031020b42c2d0141e911000d1003803804616040c02036000c0c090300e0342c6c0209030100e032080c2c1d80341450040c3c84039926810280050090305140c0d01092040b00507602e42c003010344424003142c040703c1d0305a5205e501c481c00c1e00007280c094201c42200d560098804020401c51a034081d01 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 823030332 1250 823029082 823029101
    0x71b0503060c18030703110d030212030a0207030807090302090a0f020f1605121201060503040501021b070f3507080a1101031b0c08130f1d090d0f050a050d0906 70
    0x195800c0f8000b0a05031503001030721000d001940740d09602295800c3c2007040c0020f140c440d10549480d52910300d40c80080d40c0081e03988800c0e00e68042080070406402c091650b0b0442888c3c10013039101c9107103a0014800c5075004001c03d007400d84613025030750b03d9045038060307a0000f00c05007000385d24cd06091003118010058904151a28440e9182400c58101c01504490f034050340803010100302e03802c01c0740a07202d5a0014200300c81030341d0f08001c0c6219001c6001100c041e1101d60034080c08031140750004109030912290888000e80103c000001e83c0031905801102e05000b6010400c0e10980c4a11040e03420211145c3c0441030b00d010300030700d1200700705101c081514005e500342c07004c0102c0c041052030454030312800c0440344041204000b1b03c901107032030348001d004040c0d440300c0e02c1102aa2101d011500d904150307808400110804e00ca40c1d8100032000c1d1050390b001152200508403650038100042070b6003110100e400900c4070001d000f0010511030b104403800079042000c18800c0b0160740c54450b0081c140d24a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 823031582 1250 823030332 823030357
    0x30903060c0922330501140f0c07080c0402180f030304150206072613150612051c0903171213110402090f040f0e01050705180411071b0503060c 63
    0x101001d4130302c0c039200881004540e1400024007040d081030f0040da01402c808140010071603040c0542c01070010b4501c004e102c00d10600001c3d1409510b000e14203460400300d400d059101d940103124500c2da400b1512004182014100c403845080309503400420f045104036003008100940d140c44541429400103456405054030f41c0d545041d14443c0d1080309120080300400c0d030b0041c6011004168000c4140d020301c559030f80909210150303001210014000c80307480380d0100801c0000059103000b0310800303018104490100041c0510340b90a00800108078030108e010007803668080e142e030300d40e11480c0c0034241e1300d00c4800b541010190381000d03208840049021801152900c1c884007003041d450406000b912140d94000d0245410400400c08020280c242183d01c1c1002c9542c40008400c100340c00d0250a001d800241c4030310345d4421041065040c8441c074801a0380c0220700704001d1182c2c903000c0e4001c50f01c11540107145c2d00303442c121200380312a01e00c0c040c0d8001c03985440b414081c03110302c00c9200d0045c5551130760341 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 823032832 1250 823031582 823031621
    0x90606060e134805040501051911030a0c0506010512150702100c08250f0f051c0c080c070305072d0302060901140f01090e1501030f02040b03030903060c0922 69
    0x5000302c909220314021980007401c02d000ca8680f8046c0070846103131400d01c038205022b04074001400303540b03103801418030080000d85440703610050000600410340504810740d090b0558148125079156500302000e03507196401d40400009038098402e1007209850000703070b0800d201c0058050f1004004900613528825150714110781e001d60b003401c42103000c0b0fa245050b281e0b4660310603d00001c4d00c2c00510301000301306109040000c0e6034101103102150709403082c0c5040000c1c0c0b01e1641c071801812014000c1c20604080c1c0f00300440000b09801006540a00d98000d8600310080e62003800301e50260001285900744005410203281015001f150540c0304002c0a002008600301d10200050140c6c801e803501105024000014004252990019200261181e08580802070a10319540e88200c090303006503601400d80300300074114545401807501c000700031801141050208030009480784400707071244c0721401000400e02e4840e01d801c10742d0920751020940340c0006241001c54100500a1240007641002e5030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 823034082 1250 823032832 823032971
    0x4091a090a0c020d0e03030d0e01061e03030c08090d051501030b060d0321021207030509010f0b031515030109060e06090f120705031c090606060e13 65
    0x881c428031669030324550091000c044c81e900103445891750040307842d405020030012400c800006015000c000300f41540005000ca1511800341c080e1121046074500447c03492904002080d4080e400300c480f00d0b00a282c45070f81c1c0c080100052895440c0040040030750240d0504030b5050b8807111003c5040b01c1c01b81c5c480a850f80d1320501003150044235010010089144c040001503a2aa201e6240902c107010b5034006180000c0440403190f450750488003800041e4030b0304100b10029200b07000d81c030703011100003005000500c80030b00065100c41c80d52030850410340f1403000040d58581441e4200070840c0f0098000c1102c14040d0400740301500c60015120418030413180460b03d01c4000054030600320361008090448000781702e103248801ea0010500703076058801401410480d0500c0015000081e240b144000780c2c00000c4d140060560320030354080014041c941001d070801d519106550540341c04071180000d00b2150030054000a200007010303072905003003542c000100e84a0501402c64040250715910346a0300c80 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 823035332 1250 823034082 823034101
    0x306140405011a060a03021b07240815010806030a060608070509011d04030c060b0405180609060106021b0d060603111219020418022d0405010302150c0304091a09 71
    0xc040c40700540009082040c0c21700c9510a50150240324655041c1ca0a2038003500d048a01d0190320b60010002894038110f05140b80352000c00540743e2401908010706c81d8a4120860b01c0c402d02c1500006050200d410001341446e542404400c2c500c5920083c10042140c80b818032503a103034601e016241c00b40c10070000104485d0f0041c00c0701074119002e2482d80e50341e9900c9640c1213481c1c1118580465130b00b03440c0c040d0310b6031640d124000c142c440d1a04448054840200240f42807070080003810188064100340010700905a0220b658102e21569103d40c40b0050690800314851941c03e20000d032500f031812901001f085488010411031002c00c50b0845556004601e1003034940000c030b000507050a0420f80b403100141400d4206c0444d03505542003d0302030b018560007103074003241400d5841100707140c90308180310112000700c003101481205440801280d8110340c00319100c0e003070300844480b0185001c12000c58081c03040040fa00a002d21a0342803004162008500483c14011800070b407140c0e61920004800b83c8 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 823036582 1250 823035332 823035371
    0x50f0705031207060213030503070809041107020d0b1905010e09070e0709230616030815010804060213080d02010c03140c030411010e03011820010f050310030614040501 74
    0x400074001c40f03203044443e603a608001e5005841203806108030034800000b24030705201900071103010345c0d052a900c4410b2400c1200b1180109041d40743d5010038025040940c9030b1004950a00358085401074107500c500c03030b800c3c00d0200c07051260019541000c001003035021400c1d034664010001c070070455503482c2d141d03228006950b404940d41000203e03000820003150240380c08a022120045510008a90f44070000c907603203a12460127441e02c0b03d90003610908140d0304c416156444480301c400301c01c1c3d5000040000b404a03501800103014250003040307103101391100a030300324010625a02100c150340001c40300680a4500b04442c030380803925100001d8004001754140500c6080c00c4a109491640c2d19078421074500803000c052810400340c0d400d404841e440074410340510030000403038070840354810329021100c02c400c1c0d600030000f0316203004159056600305d15400306418032401e059803a5520728448130b0790701c000d83e40084e01c110305019500283c9401124000d000301d02440080c444003181004004484 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 823037832 1250 823036582 823036603
    0x109020f01050c030a051c0204081b092e0e010e040b0901050705040b0a09030b0a06030605100806160c0807080a03150f0b0c0a0f2f09180316050f070503 67
    0x9404c10069051681c1c440c800030300c05801e1986200d410016040b003e042240c100b60803104065214004030440041c816222070b81c3c00600301da40101c14941a1210f07401151602e0280c2118007174122820b0b0343d0754000c1d59201c05801c402c0c4040100d5a0369201554207840281c030252174034280c20020413504d50701800389910488003611030a00d050f01e080c96120b85030703010f41100383c1004202e1101000243c1c2c2510b505008051864000c201d89042d0b042910840c2c002030007040c42e00402c2c8408100e00000031910780e50200400b00304240101e44e1b0242690301e49409100100400d40c0000c4c16410800c0310405001490b01543d000c00144110745988400203119015000e02014121030800ac040000b000038501c68000c0001ea5200709400c0da15100342c201440b5084480d40510100341251191036076000b8540030500e40c0e000407104800010500c001d0020b8150414042010300e11100300c2020011101600322213503001c5140e0120b410816110103a815007607040340200c96000900d80307800259445807 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 823039082 1250 823037832 823037857
    0xc02030f0a0b07050a082d160f020115030303110c062706060a0e0a020c06041110080c0702090703060503030a0f030e120f03060a080f06070e09190507030b120109020f0105 75
    0x541c1f90480114943c42182105041609100034040d010848115000d13003d4034485429100300300010304094007244410a00c0411607140c16003541015100c1c00c1d801040b0b036014107000903584ca00c2501c884151040c499140d0141c8948002d1001c0340c1c004c04e10590085034840c20240030001d1020600352a0036050b50039650000c90020103002a80f2007004a036000850054014a880d41d96043c09080c0a411541a203040100492075480c5081403018a05000c244c0d160040325481c22810003031650140c2000680201d46010000300124001d5011002810004045036114441e0308c030010444a604013201d00000d0600004a40c1032074001048003090030000d000c0e070700700103426440b03002c19040182200d52101c58124001a030b024280482c01d45600104080c1c03a00340f0307040d840075100c00c40c02c90042d40114010010006021414480001c0300c141407280400c1e140c1710f695049001d001d80014096110204c02141000741005620081c1041d10070340b10420f607842c01d00011740d090b01400d84603501 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 823040332 1250 823039082 823039097
    0x60e010305011d18250510080f070e010e060f071704050607060b031606020d0801080a0c14010c02040f150e0f0403230d0501080105062e0c02030f0a0b07050a 69
    0x80740340a0801421004400108484840702117103120000c07421694901d100034040784c441030203d4209031201c03507291651800d0107600c034100040711440f11781e0010072010800043d03160310016a0300c18440034101c080300402c3c494655188414a0000d075100d0001101c0c07003611a0783d072000072034001b01642e0071244001e09550a044480e00c98601400300340c8030095242c000c855140c41003400d5080e4500283c0040d50090800c014000009010f460041e0007881a95014040c0d0000040c0b400401d11f0071707203c9600c400d60200741e221005944000343d0b0b10001303500504110301c010b580c0b10b083d0f009180807900031041082c100d5413818490321043c4185d450341e2400c1d012800043c0440c0c040c200501c055005c40340350780b404980310078101d601354005002030205107840748010840c8403401d0268542200e0100c4000b401307212902d01050001150044024078507192281c85000365014801a1003100e40240c04ea030400c00d1100748064850001d088112041c90311480842c3c4400c3c440c405681c0792031447c3e165240f = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 823041582 1250 823040332 823040341
    0xb010303080403110723030d051c09050d0806120708030f07140d180e04110f01021e01060f051f0f0c06110406020d0c20061b0a0b06030f03161407060e010305011d 71
    0x20220204002800616155003001c4005601000337600c10b11402e607034030881039083c983c081246c07040b80710180c0d0341580d100d041c003401180d1000c001c0f9003c110741b0b001010b6071418286072a820906080d00704141034040d66440e1241035030030909500426070150054009241c4420543c9082181501d002d494818a02400406410900d105950030b8605004943c92407440404024094440c0c814030305843c1d44882c3e0130002400742d41446406060200c50010001c0100c6040e001c1440032480700000308202400c0010106000e074000e4841f940d0003ca0a1101e65000c002d01402d59109100d5000103119040c0c01c160558418034102070b4541d80b01d4889050042d21003d00500d502c42c5074000ea6001004008040c8000b440c1c8209010880810003d0042141a03007400301c501c003001000f15000307421242021008940200440d8441c0c0c124034040b605044070b9013403c42a2440040c0c9210240c411071b00d0225000b60032074050544180c0c02d990078000da13130b00d9100c80c1c038000169003091584400a800410b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 823042832 1250 823041582 823041607
    0x80309040e0a0203060a29011b061b02150a060315050c120a14280e16080f01060f060e040504021513080114040b010303080403110723030d05 62
    0x60318110941c5040300c12404041d00040e08005040c1c0d842840183d44d5041c407000400c8498140c0e00380548001d4500b801000341001a24018807640c0501882e03090480d88000c0020990000d107107407580030404c005801407084043d55900d11a000083c01800c2040003074558a00341c007941e001e0740d50020920507180c501003074050107030002600c0200d00500a1204c1e04409240180e682c1c81514a5400030038030302000c0240b00c00640700a40000700c000c0b091004040b1440b01d083c54180e01402e03c05000841e540f04441076414145032a0707903940d04982900002514000000d03001806280d0071000b0040c0581c0c458030341d124000c640c850400410071014400c0007514066021541c4540040c000c000040140303e060b1040344c0c010b038484103644650390010b1000714000d1007010800d00e400100e80c0ca2606250300e41d00f0b500b41c0144001000c1185004c000340408d489907242d403082c0c5c0c00860481d482c1380e854100300b80b0306a052800403ca85c1c60001c41e410703190302d07001030143d0170036180b40c8506180c100000a038 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 823044082 1250 823042832 823042841
    0x20c0106142808060411010806030d0503011712030f01061d09010e15040c030203010f0b07080f070201140712080702161401170f0f0c13060309020f030a0c0303021608030904 76
    0x2e81d020588000024020b0000d001c03561241e84202c041d01c001c000303d1000903101c4400507200501035030041c003240e0400c64000d0210703419502c1448409544801000c6668503152038110140e29049002c02030140d0460341d0740c0c80a0503607040d030b207c4107134030303042c54070090750071000d042c0c10550104c0c1200c0100301e0348407075254554222850170045003c3d50040f10100e015565801c4007a030000341c0c00001048003152541004014184008a5a142905588451b1003074060f00d000388185903070000786407045a0007a607003402c8500450264580340c600cbc40c20281590301c84408200040f450010000380610710124410300a02d0a0130b288140c00c50402c1d81001c0000b81604145e0306100d804e03810b080c0c1da07071140d00541d442048181d000da201403810110949000b90090088041d005080c00201070100b0b9846655080e0b54007440c000509940c0c81c00002c8010010802080d01801262030f1007060068444520303095901130b400b160741e6600c007012802505800d51060030240d4006021002892038140c00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 823045332 1250 823044082 823044139
    0x50903070515070c02120f0733030b0a030b0703060e091005090f0a081305100804060c090902160b070206070e13020408010212070f03180b1902030703020c010614 71
    0x30f21380c907002500c1e8086001c4001840712904107600c0444070410401e0108101800340c001d070400c1e410b0b029214005c410003001c440804402c40a40400c80501d180c0c880e41c0000300c1300d03030028500030343d85c0c0c0c1d2170801d00f15034101541e60400190602c00302041d44d1820f14007ca005e502e80c10000c0040f202ca00d80f0034801042e000c1d01c403c0075402903c91104804004024442206d0b0003848007039541c0c50084043d4945400310780c003480c0940d0754801c917283d2031604020003503401a00030001241c4141040c104550b84030054004092852012076000c2d045801c400100400d5489003049610640f10507000781d968190071540800016294040e101d0141402480c051001d07040802c00760405842e0800795007aa0080d880e9410a000c01408010310f06ea44a1110190b42103e401e08100103226185078004280d0510005044c4161440c0821154400e00a5002495505560454a9042c02c1d00c0060195200580c8282250300300701c0c0206070008000c8255271601d000401101c41c0000311101c0041c1c0048071007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 823046582 1250 823045332 823045337
    0xf030b090631020f180a03050706300b030d18050d020d080d0c2d080603150702010b0a0e090304030f08041a0702040507030218040e030f130905090307051507 69
    0x504802d0300100b03800a0302d899a003210701c0f1a25010a9140b41804541c0c1c02c2030381d441804118000c202103440480d1402c180c0384c29103007902c050030360200e5050f020118084c02e1110405440301ca1707000004140c1c081d000030f220860989030f00803445801141d503010f0210010034095141c0070b04000381c1c6000241e03403070740500c09031403d5080e2840e40c450304416004140d0ba150a1030b1640d038864a0035a011500d01100441d07403038148400b0329420f0341d40041022b2007c02d1000d00200c880454083d0b50100b003401040e1811050540d0540380c1203400034040e200142c44103009001580001c68090b004128041c400e88018004502303091841c2c0398500b81d4225004191404a402c000115045154615949a60020782a841d82d00d84907407040c2b004070745000b84900c0c2018414055244c0d115080740da4404062000c56000c940030840401c640c1c00d5110b01c4008400303030344001608001100301c0708101021215040c9003003040c2e69400f0301058480c841c1500c0203005820000718032103000c0c00508030581060742c92 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 823047832 1250 823046582 823046659
    0x100e01020c12010209040501050d0f1b0909030f020708070e0c030601031d0105091218013f240e0405010b0607030507050d020d09170c0306070f030b0906 67
    0x80000ca05107001c00030b610405a5000501500d20f8141401124018141641c006c0401c0c052601c0705c4240500d054001041000c200480c02d015085044828000c1d01c0551000c102c0e40c5412300c0c000d07106000381c0040d0800b5014941c800960540c01041034000c075060400482020b68404260000a50004002038107142e910104000c50522003003090b200300081200000301410100b086d240780034134220301c1d541c060300204101a0724003100303000398002c1e08080c200702802544040741e8180c034503214a90611703810902c0300d0781c1c010361200003200060084030007410804d2800eaa4107202d50703804100d103441c3c4440762900d01007102d0301040e01001e601034000d0000041408128001030340c1c5621000059001400100d00002400000d00c03001c8001c00ca14001082e10540c03c0f0001f07800f0740103910410b42001c0c2001c2642c04a04000e001a107008900101500c400e49040e007030242c06000e4803000c000000349841440201030424204141c010399000b0a00022a20303101001d148101160081c040d0a0700036 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 823049082 1250 823047832 823047853
    0x51f0e03070324200f0306040e010e0d0e150f0d2711030105040c120807020a15020d1713030507020a14040e0105010e0730020403110906100e0102 64
    0x200c0000010322514445102010300150320b28002d5130801d1600340b40c145001007040841026001c22140600042c0a85030b0b1640d903240001801001c810580001030f508008071041d03102804901c41a800c0c040d5140d00816041143c18002034044040e00700c44600c00c01c1145540000784080a0021516201c5001c40c0703200d810340a241005462152000341956844440d0040011400041c5040b0030190000c009034035050b112401d0711075440c03003010b4004460503c000117001d03070301080311240d58010700030441c0c02e50343c3c117992038401000c40548030041c0260f4030740f0201588100301d00c129060322000100c034144c4400c4c0b501d50f40d40105010072010310030b041141c180141c039214200402054022000702114410700284010707a06e0901004426034540801400b20751065600103800a080780742111501c9003600d142c64030031000140001c04451a41a0b495001040390000c0c01982d10503d4031000b00c1080401744000c408040d1803055122610a2001d40078911598400b0406081441250f00d413145 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 823050332 1250 823049082 823049093
    0x30618040f1a010501030f23060105040f080307121106070e0d06050a0b040c090e1801150b13050d050c13060f0909050c010806180406020d0e060f01051f0e030703 71
    0xb2103a00c80c41c900542400400080d07030144a8042c907144e600c8410700908020101d1003001a907000c0c44d80c41c1110042001c40c8090b4800d10988015110400d01c1050180c0c65a540c0f0360350350000b000480304248620204020b030b6116090700401072100301c0c018116612581e40031b0302ca050b444011160407082c0203d000c4013080705805a035010b03000300840025220f408005010075226261069800c0c44000c0c0c5040003441300d04008564444070f1204024000c90300c0d4044203000d03103118007444980c003036030560106403030284000402c00b680700c84001034a01941c4005200744000c0a5602410b40e4002190018880c01c2c4840c0c0016840110b850010b0710b507850310211850754003a0340000080e45c1c0d44060040c10000100002e510000090a00b981d540c0f6142000a080034a13a10150003144034000c0403e04012036070701541c680d150303801c201340300c50030f06440b20329610394003100c01300c40300c0c5003a80001800f070924807544c5001003c00154000c4152441c0780c203a41c00103540500c2c540612034030030000040361 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 823051582 1250 823050332 823050353
    0x20904050703050702060a052703040e040b182a010e09270102030105060a0c03053015090a09020a0b030103030315090c0203040603050717100614030618040f 69
    0x403841d4800088078100000000c2c83d04c4070081840052030326040c1032151a810b0303502d4034440c1a940c270400c8400d544000800e9803c40c001c0d58400400007511005100c2084000e49403d40f04850013003030303c2084990005940d0f952002c00382d4403102c1d0b0741c414652150035080340c1c034050780c81c0d04103040000a80d000680400d0b610a801c840c40308010345d00180010f035012084048841070004507009600707550614000900c0b51007416041011b200300649000101405070060f5030310320030b015012101b00303840442242d10303c0d50018025491008030300b0005460003100707000070035590809031881406541e02580e050080118000590340b06038400000070760f83d6900c000131030182d4800d98020070b01d59907002c11281c45101c0c54220b000070310b041450340450a41d002099804803441072a0204164884c060305403450401c071302015000c1248881000440700e420a000340448859039107068900d00c200d001054940003e031100d5500605103159501802d450341140d070b07041230245000040f80d0009590f910480b2 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 823052832 1250 823051582 823051591
    0x60911090420040b0f0118170303010603271103070b1804050f090a020d0303060909110109050105040308032a0c0709110f19020c0604030b06130b0d1502090405 70
    0x3000120540b101184a01440b100c0c490155003e00041e0525000500c10072500c1000d54100f010b020b0040c3c00103001584104001d046141500d45010b8101800d02d840b580240654008a800d15030307833010049800200c2d010b41c1c4409160f0210b40002540d91001c48030035402100e40c98031519002052000c1c070300c1c0003058540c100c051200c41250b2884184800e4070740042c0500c8458820f0000c0003194407011410542d003c0d41107581c2081c03c2c0340c2d1b03d01540100841c2d00720001c0d951400c10040108410503652040717011090304d80c008095540c200441d240d11580c0002400c020060000c91003040e94411403d40706a0002000000050310380c9504403503070030901d03440c41c581d4030040e000c20080d1041d1041180c21000d002100340341041400305d18000f44140c20130040b03911102009103182078400d1041201003007008101c10303911507985c07c00c0fa0740d1a205442c040c0c1300b140202c15002c0d0400030752060080d5040c0141c0040714650305901c44d0301d030480b1103441880240b03800704003004a40d034640c40351a114 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 823054082 1250 823052832 823052843
    0xa14220e0c1e0919031b1d13060606270b07150908070f0c0501080441012313080705030d06120308060f0306150111100605190509040609110904 63
    0x45901c1c5d4141180c1c0d07003072a0111400003803040541030040d41c0710152010421039112a40c001e158640d01d83c2519a008441d101520151500101284095010002c404418007420200d68450400d001d00381e2144062f10440c41c501c181088440002180c000c401d080b101c0d085c00d00060350003641d85a402581d8804c1004581940030800c0c00c02c00c00ca902d241c90b001502c42072034004600c2c0362599034640c2400c0c0c1038020018107a02c6041100e2960301d0400900c4029001c0b407941d5042140800f0500d01030b00300181140c0380b84294000c520403614803155900d00c900405190f14034003840075120680c1c0355108404c01c1e509d9001c100402c1094201c01c0c06444010244140440c80818040c14000c09030740c8040c14107480760040c1c01c00c4211559000819039084503085914400c03041414006850070200804498081d009415100346036218691020301110380c281c40c031030003110f0901071038802c83d100c03400b440d513111441c0c2000c00c002c5013580d4010b0089a2042401c0c040042c0684000313500d844044a08450b03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 823055332 1250 823054082 823054129
    0x402071407030c120302030a03020702030a0c0b0c0c181602030409020f04050109050f180a1e0b010314070807080a0209131b03140c0a14220e0c1e09 65
    0x1c20a95404200041c03010303424141303130502c81d80c1c1c00039142e2189144210800d81c01003940d800b5035a05004040426070b20440041005656034000c00d001d4210f0aa44a2540500041c014450401d880d0231400308035440a450702c00d07030f910341400540801000c9003800310b12052101003a0300c00180f00404105480c0c0092030307100c0345040b00040030300280d80c2240380201000c03c44d1a900e500c0c1c1c82d2070f43c0c0140008408188141c0d8840e00303603000514141c4d2428045841d410413001d96031100d03501500d007181d02a602481010a14a01044081816110301c400642c2070130001da111131145c454141c020402c240007625010306240003500000380040c0703124003180d40f0b035000703504441c4150b22000030351441c0c02c05012401004030010f400c0d060041010014a100060700140c01c1e00c24903c6a8000c1000b0220a886400a007070030b9440350060341c0d0344440750303408a0000c0760401c41036100c0703032150f091008903038038000e1102e000441096098003c036107040014005c03407400c1d548102c5102a481024082d401 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 823056582 1250 823055332 823055339
    0x3120b09010b0d091211100b1c05010b0a0b0409052503020315060d0c030629070c03082115090112110a06111c0915051306080402040509070608150402071407 69
    0x2c0c181010001da401f400f515200d031140341d64840d207021901d420b001d01410003104035242407013030150042c24542581b2001011012039021107000c0600292219180304100d0369807500e000c00e0201642da211864519140080006018440c1d0025a80a542c00550320713002041070703011840682140d400e0940c00c644030070507011010360503c50000242000078007030000c400584035002d45044c0801c10010103c20008031030050000d85c3e6000b00041d51b2100d4030302c0d07840395400302080d9600c0311a80e90588078200c0038045403001d0030180303a02046100c0100030600366441c02c18001c00400346c1200032954071055072102178135681c401000341c00402c440e490341001d50144205550505071204001039280d0810041c0949071940041042c080d01c075451062410b10790400c5c419212030050758190600c400b003190f80420403941c000440c500541c420380e401d01444d1034040c03009407121600e005940c0061180c00000d9051240d07014480d00c418400340c001458501c550700d0714500c0340d20b4241d03081c4050f48030358401c1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 823057832 1250 823056582 823056617
    0x180207060b01020703120c03030e032802030307120203071b060c0e03070f0603020c0a0c0803130e04171c06090903020d020f1207061103040b0403120b09010b0d0912 72
    0x340503018240b000c4d160803030a69031048618080c003501002005240401d62041501075800f0100540003501200c1c0c585902001d420140043c0e031011804902c6c045803006c902c00d00000a580c082c0e90180c440d0300f81c0c210882000c0009400c01040f81c000c002e02c0000368100300110328002c1640c2802040c01180b011070307280c0c01800d1180e01c408072900130ba01002d01000040c00c088042c009a641d60718001d42d60b0107a42011900e44040c070b81c4080c0c82c4c0d2001c0d11002802001c0000100804110b54041302e081c640e849030480200c40b0210381c081c100100d03013003000d96034040f0301000301603000d1684402c0c0c4552070400012411245250080030343c0070b41d51841c480034150104480d1000c246d85100514010209d601d01d9521800c01c2c01c80c3d030750060310124880c000c100d89900301c00181d03034910560584904c0c140c1001301e141c1c3c00c103a8094000c2450300010b880c0005040c01080c2040001411107802a448c0410704005544110555009150356600103000603200011840560905a480355803900c0f20340da18 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 823059082 1250 823057832 823057841
    0x5040318060509010c060209040e0601080604170403020607020f040f021309050a0905030403030309150c02060a0b01114b0f0613080c0f030a0c150b0d0b0c0418020706 73
    0x10720203011052142d4590381c2e030b01c21003d4441c3c543c8020301503250071b1140d0100b40074080c100c60607070481c01403000109030400005038091140c0d00916964004213282d050958144c415400042c0d0010300130001040542403001000440303101c00703400004c8080881c51602c04a8018a0407400c210394182420403240100b40169504510050420803c0c40746599941c0d0303880c40340388002414581c0350010a02813080e800a03800380540e03c0c40043c490821014030094460100f1a0201c00c020310f88901001154031800d02c41c00194100d100a0582040c100c101981520401c0c3d143c10010540207070140410781d100d0211080800c2c0c003002d401280b03074402c04141c10032403081512845648150204860807c841d07404c0c02d00036800c801200c0d42c42c641c400c42c0b1824103124640c50b46c1244800542c0c04803c0764403044406044d802501c0e812000110f103020b40f070a544d800280542d0087d020f000340b40110f4108000705400503000c0512502d40381ea55182c1503650722414100c801e8155001c5035050600015014 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 823060332 1250 823059082 823059089
    0x40e010209010815241e1902060103150b1c031817030904091b06091a0c060c1b06040b060405090f0a1203090506010b130b0f09010c030e0405040318 65
    0x2d11582c1300c00e80070003044ca01d1119210014a01c1403c5070032046120506046585100003807040d2890b4811141d2904442d6002003030b4a00d815610ba00341c003c00340d1020031001e041c0ca5000d690090b03491040701e940c5000d0000b1080180d440343e041c06107480a42c501504410400b84203455440c00d040b541124000265955402100603203030051100070b03091070120850321091800c4900240e001c0503401c010510011a2400898400d5500004607141d03400042c140c040760485092030f07000d10341d0003070b800c0070038003130a81e000303503585d0000c1301080254860101034410300107883d905060314009c070580503180c4141940e058600c50408018049079013014000d00364440300170001001c040880c00900c590707440c8940300107010010050a031200c2c40344249c010419164000e4116045961100d040d00219408440c0381e00700d08000ba1400160340303030380800fa0343e00e69071038640c4603080801107401582c2c1075108c08421400c000012100b140c8941d12480348502030f50007a5682d0300c405050780490304d02c64007140c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 823061582 1250 823060332 823060351
    0xe01120f030503100e2809112403161806020a150f0c020303151f0806040f0e0a0302010605090903041208041502060403020d080f0123040e0102090108 66
    0x59000461000e4810305034669162920310b03901c3d507600551801400641d009000c1400e01c0c1d809000000092490780d6090250324503001d810b6403c500c500310211190020010031103000c280000c4402e1408501d075a00005c0385131000702c0b440340c50078040025584126821000c11410420550840d51302800100495107000c4002107440d00300200070303541c0d2003008401851340300304506a1420101c541c02c00404051480c40a000c2d192010310065126001158101e6070905e102c0850085450081d009450503145070b400c43c0c40d04d220700d10b0708035420840100a550042d489400721005041e5031300c05d2040c02003050f002381401b000c1500c0c000742581c8159100c113100d030a0141c2072180450000c01110103d40d80f0a0380801d5010035490404202e00071544241200000d00340c03100b00c0140c0101c0c400b88a00d119600792103a003a00d04100761408101039941c00c0f450460403006001146040c4000001541e60303119100f20080c0140004040c0c0e446940480c007540d401107a4180c00c0d507042401a5000341c0c590 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 823062832 1250 823061582 823061609
    0xe01020601061205090111040f0e220308041e201014070606082e14190b090c0a0314010e160c1b0f050627030f03070c0e01 54
    0x1000c02000c10107a0182c2e482d031140d40e2404540c01d84403d6209000d200041c41c500c40d00c440ea09c21055040b605144102d40400003e41c0c00152084001700e601ca00c1d0310300c44c2800030145200f540303040341d001d0300042040320091a4480c9034070f4041000e08151031100e02c80c41c036141520800c99080901c842060b4002c9003d070304502040602260041a400c1a07d01060780c0c69466030440d04144018014a0b4452400c0b13005501c0c1c000d410301310075000e8210418460311071015012100d1015801c03101c448021011800b014004543c086c441c602c2c18100440d05450045840021400043c0a0803020340c0d00e2448010002944103d05806000c3c1c10110303110700340d1800030b540c9809950000d4501c01020340120a54550b13040c03130382c4c038013075800d07071b6802c0d0b8005818401c01c103400060366446051b24080d0b00c004024400c0d0001e0b0314038044003210400c0400f4140110003045c48a070f00c03810001008502a410b00a045400c0000c01c6e080015280e018007400f50707044407602d0040010390080e01038100b0300282100 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 823064082 1250 823062832 823062839
    0x180b0a06140d030c030815060f030708060d1106130801050f0115030b0906151b01021e07020f19050315100602010b3d0f0201050109060f140d08030f070e01020601 71
    0x1000d40c1e42d421741508181e8083d65074004041c004121055642c5e070b00060229034900e0002e905005144070b603080d51151100d9468040400c8103680455200900740c1944400e094294213200b405040c0040301c40d03281210341502d44400c3c50039903808480608a2150300d4004100d082c050054004440c1100d043c1004000d03144000300d05000c40c02060640942c060101d003070700c2d0441e48001c561040090b50410240c41e00440d0f1010f01030351100b107001425034078401704420ba130580881110402c1707600400c2d4800ca07801c080d0600071440c46140c1042101b4040321400941e0351018408d0342c1c0020381c450a01c1000749840c103000a403072201500141c045a24220100701207456001e4413000e00c2018615840340b1184d41c0c00300714403044000341d1001d6a27906180b08110b0f0540c114a0700104548590001e0040e6070700c03516040c0c1212030a2095404117144080b08100c81c0212907410b1285410240c07441c045c01a00351a8a1120f500c241e881006207018141000f1140780e02840070452144240301600c3c0b80e514 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 823065332 1250 823064082 823064087
    0x40503070308160b01060215010e270c041109040e03030105032e11040e180d030b030a20030f0109020906040b041803020d03060801020309070306180b0a06140d03 71
    0x203601004001c00b00c0000c55940105440b42d0040070780380d009140541d19078507104025107510140d511000303d00f4401001148401c007041c80140306104115812407403210041424280c2210409816514040c104004106803141c0c0a140109040521016910141681800211800040e05072100d4005200501c240e42d8041911078000030035022032080c03825100b2031000201e4050302071192451400c0c49440302607402c1401780045400c8101c111119079030b06141003460f04c08507503002d8000d40060310800703982c9010398480300e140c2c02d02a0450302c007908a9901c2c0090008c40100c11043e20100a5910034545030401c0402a0403885000a03c4031007000c1e8041145082e02414030391090751115511401071311580e0000ca555000700b000c0e0f24241600d400e02075156250703000e003100003070704000c004942c0b14014000caa004481c0203004000051a68650100a01c560248080c10b5502854001c1c04504000707000d80c06909140380c0080d85500e08642104081c10b0315007018010000d0b04098008642c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 823066582 1250 823065332 823065343
    0x1909050a030b0705160b0a1103101a0f04080a1101050408060720101512050c060705160807060206010e040321020f0a02010203090c06040312030b0409240b06040503 72
    0x39030201e119291a1100031042d00c1c40e0060103170360070b9038401c0300080100b40082003005c3d5018201d0013034100014607102032484060b20046500d01780c0480284ca0030450507031520050a1210081805207041100d00e41100c1015849a8041c600343c3d8044000081804000000d150490700e090078001d28203407030003008030345841c4018218000d1041e01c0050720741144002e0a904c041d01d140900b80e40103072000240c000700800110811440c04008818081190604070705a4204107811900406011802100f0001c25511100c000c07a6a0b0080300c4205040c19011240c4901612014001e070000c0f90900c0340c001e1801c1016444144400518014000466003141d030a95418800d1468a103046000e030055201030303c50310001cad5402d030b4400101507840c5070341075024500500050007541da00d081d5030303420418a40940d0002500c90201d140c510740da028040c1d8041d000049002e040840c00d03008544400c5110820886941b101c4d240c003400c00d40d45041d03d48941300d030118080301c8590601e401c00001c2941c41 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 823067832 1250 823066582 823066589
    0x218040308070309020310092004050601021b0d14060103050d030c050a0e0409080f04031506060f0f021c03230c1b0c2119110d15111909050a 62
    0x50b0f4511131002551401e0281e0160300c06408420b1100d41d10794034000361080c031a1004d000103000c0607a4900710034139040c001c003409038905a004144151001260070201003128142607407100c81407100300001103900c01780d50f20410000014040a601d0760070702c2400d00100b07070750020415280103040b01c3d61070f8000741070319140c40c442e04e4022880442000840c005222092010308000c40115121000c1c06054000b4015280310300444a070901c8110b40d00003d8915602401d40481c40104c080d200340e91250000b002c40e401c2920440c0c0240c3e1294105c0b011804040c1d0604001a840320145003c5808031500500c1c03890b81d812034001c84e441c20250340055400345401611450305054140795500408010802012200409014000002d03100c1840d8149001449800c81e01800c0e88440311010000703013645100350060340580c442902041085000038be0400708032003c038800c0340e01c001015040e20554002a0462010556a603561100c0301d0b8820340c00d81c140001c021f06c00b201803049031100f030202c8085 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 823069082 1250 823067832 823067837
    0x2a06041424011413050a1d070b16021f020a030305060f0d020907050c0105011701050f0106091503061d0a060b0406022a060d090303050a050f1302060f040303080103021804030807 78
    0x8200f0903001a6403020040d8091805608003024401b2003105940b1101508009455861818400181d003070f48820f00ba200d29060498248286c420803075032a21407840d02e51004010b0000f04914110640e0712004407074025005901030303045001056014400d194200104a03130030142c1130f00c41c1000440070042c1d13502c0240138201c1400824428bc8c061400d4451310909a8001e00c240c1d0785a1001d400104000301107800c8a41c02c180c040792a410b56403101e24141c440b603540b40c0200a0602d14401c0d4440c880d003488801301685d8407400904640c00440344007411180007011152070800c400710606503042d80d00645554507080108200e2560001504403c0c40d0064201002941d41b003000940300c0c9003064a45a0800c07000291010940c1442c0e00440030300b4441d45041040c1e8a885860700111601104c2c400c0321440300c04085401c00d084d4417070401c00300340700800a0340f0b07162074240f003002180c11550003107012920319401803085160074021541c031342030100f030410000d10382904d0050104c1c0d00980700360117 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 823070332 1250 823069082 823069109
    0x5030d0c030e0a080c10031103011e0308030f06031515041a0a0f030b0c0a0e060706091502090a090902031c020f160602010c020d052a0604142401 64
    0x70180240307000444108001d02c150b0910340d450803c1a01c55021082c0584a540341101d85400c1d01c0c001d04c01e102c170565203445003d085078207004000c01324400047c18940c030182ca803903001001031012402540300700034160301c410b100d0500c801494030740030038240c4601222030704004000e912140100c420014940486002c2494613001421481c0030b060030b101e07a5003003002d07100003040b03489040981000310383c4500d000d18895600e00070359900718014200d103100002c5030148402e2903450040082d09545006200c005132031a12642c5800103500b02d40b5182c011180c0200381c010540c98101e49600c0140f400a80621240209600098541d01c01a560017051070341d248516640d00e108014030540801c0c544120740751903084440000403c3c54030b01c070368170056081c9101c4850503807010031800940d0040707449880c1800003681803840000c05260800509403038221403c2c192200800c5492700a40c00740c054140130300f40c80c0302c006040441d15030303414590700003000b4001c5c003800c6074042803030445194242400 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 823071582 1250 823070332 823070357
    0x19050903010f110306040f0e0706050a020f0d300504050c030c0f091b1b01140c09010804080319090602040e18060c0906070b0907050f0a0305190201050c031c1505030d 73
    0x1401000b1152502049100f40007000c6203030bc0e004002003084914036021a00404550427044d96103103581800d00000803910034441040d140c500042e511059914407004c0130340080e043c0e881d0f0881d03400310f400342c0304d60780030704a04000d5003024080300807800b005444c2d244640e29a1000714250000282c01c0a4a82e409400020100d0403084169400031ba90105030200d10200d809885020700100d904171042420031102283d04000810100c0c0d01074041a100d03030764150342e00c0e140c0704602d4100410121412a081ca80d43c80e08154510807a8200c5110740300061712282000c2d01e02844400041095545200703484032000700d4000040c0b4603512682e01c0c685a9a15511100070560f1401214401401d4403030420070300c41e5102020071200c095a800741d441e201d44016840c20416014454817010304987c00c801e24401c813400c3e003684082e80700c0c2d006042103450b1120001000345160301540e4001071110321407102251088660150501d1203411101c2490b02a04020009480e9541d143c802002d0141c0e0001d000d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 823072832 1250 823071582 823071611
    0x141040e060d020a1505030114040605090f040606080a0c03140c030304030f03091211010206070201020a0f081305070303050a030501050301021c02072420070c05010c0819050903010f11030604 84
    0x1034019045c150003038922410402c001038465002070044910100c105001c0d515207040a00c1000c0840f5002000750782c0980b2402640d25140202820903242d281c0c4804c00030521034410001101b05078840e20008064a2450a003003041e040c050001072440d400c482d070340703400b20750b00001608d05490b0000c82c0700036146600e1400352887c0880e9403040761841450301403181480000c112184204100303809440050350340607000c070308138400c080603c80400c47d01c1c09000c1c4c040d0301c81c000322503000144024104081c2e44c5610b0b06807800040d940304400241d400107920388010740c94001c0030f0041c40c0a40083d030a180030a564184118001105480295400301e80b5400340b204090f910741500203400181c41c0e101d40c88006400c060241a503403501000c4807111078107054000750301126510768200f9011524607003400d004441905482c0d030142d4038442d0074001c6010719001c2c1014030700e45070007a0302d88a0342c0d5141c0c24103260a440d00a2090000076203026180119011414200c1c0c0d880076049a0000341c1c024502c962 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 823074082 1250 823072832 823072849
    0x20a0e0c120711012334030908030c03271506011b0c140f0604060f0c0501020a0f080a020c0c0103020a090806100f080d0f0c020141040e060d02 63
    0x4421481d07003000303804140c800c84003030b00104601c8044004040786e9035140941d07143c000b2480c1c01c0300b440c2d006a00d0b100c60810342d0314000e03400c0305080e2074085440794968072844029001a1000700c0c5588001003840610300302d529090f42d000c2510351580d04200080322103c0c0d10341c022802e0001c117030b0009130300040c200d03881070b03401c01e8040004600212007506182042d6058101c24014900385007044660006c891410340802d41c200311009091500d807a051400403190025002c08030300901641c03840b1840014002c0c0041d007d5010560345032000034980540040ca51000541084421441008114072155020954143d112420309026030380b032603049e00031070350811940d20030b44c0d00f80280340a03c060056a10401000c650300100d11aa000c1c3d246c0d07041c10b4942c2401d45010020900c00b01c990303d100750088149400a500506109000d060601da103a401085240218042c43c1c1d0045401c01112010001d40d504021601c400282003506280c2221020030700034281c5441b84c03d03650710340d400b1035490149 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 823075332 1250 823074082 823074107
    0xa0204021b1009030206090703080d020a0216030b07260a050603071701060503060601093606061e02070f051203130b040f05040b0d0204020c0708070b07020a0e0c1207 73
    0x8440070405010b800a00800c4090701c00c80050140f4000b04001e1400010854207803030b00110050300d0b0104214000c0000c1d8014400c000a60044e012922181d000601c035490043d40102417005562030101002001c0c2141c0b590b843e140c010070303c080d04504134140c58206a100044180018440e100d80300083d107400c1941c8c4c00312481d25254181480c030280107400c0b41c03086840550490318552a881d006580380307074290044580c0c821507442e001c07101031000c083c8503200d80405540307a00701c81410169070054800f9030b00881d003c507010b2900305960100e5142160700c00d2401d0b10151040030b00384032420980628520515204a41005e51005080c41c10300480e07a0030800c0210a1044903951003880c100740c0c101e445142041115240000340038200350041840e01400200450f121a90716401c0000a401450f22072005104407507000c40c8421080001d41d01610649641585035a03451040040b40c08003504020a03a501c00c00a0120101c214800e43e0300c02139030001840065039801200315154942c2a4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 823076582 1250 823075332 823075387
    0x6070510111312061116060e0309030319110a030e010e0f09070c02030c10030b12031c020703110f010501050a05030a2019030b0a0608010e120a050c0111190c050a020402 74
    0x1c0c0c20008002c2403064031b201207204035024040320700d00240e9162280941080103800d5001088403501d0b105240036901498041400c00c154006403000081d4602040c0070011000300d0003500300c0f42c8156801144002d0208800c942e0100c1042e40e14000c940800700c09440001840748041f0384104540c0e06128001a002001d05810000a00c518004000c1c02038200714a000b04002c851420122002008407078941203004049400c00406116450003903002280c15000c00100d154145040303074050003c245070000050020035154140001c0020200c17095020130302c0380d0b1000300c43c040043c003d081d110104902451340403007808210070200b40d14510344102d54034200309190010023081034007101140110440d10f01001241e8503060303034a00325111200440140d0748151074110300d0640400040c031918025150890034411100c2c061800c1d03c1e83e46601d100d0224000ca000b850b5000c80c1d20003030300c895100d0f1034911451a45034403000d032140380042e230290050b07400144c101000c5080400c490035a60450 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 823077832 1250 823076582 823076587
    0x2010f12020d090506060f01110a0314120f0a0606050711130e0307150b010914092d16020c060406031107141b240315060705101113120611 61
    0x14a03010f42c070360384120b90131b40c03090030041c5c0c00791815485001400c4030f03102000020a686405601e050342d02d1107801080c0400d01d48104204207803030880b441ea0900a150703585880c082401c00302c858800346c3c0c2250700702000300081403059102042e8103162850111106940704e4006d8418451382d500648034131641041c00d440005540c4080052001c001400c1180c0941c04209003603a00f0300448101c9054801c038420644c6070081e501c581d1030210003e6070000d00c1301010a24034140d10146120b00b40c0c00078845031001a0798001c001c1070200e1085c1400e610f10061000d80841072070304000800c0c034040c0b40070f103000701130740d411003080105490800c680645130021b4400e400340001907030040d503800500c40e18001c0c001130789038512240d0a1040814034540b44401d440e41004030720044a6605400003054003204a40031101c62140d07441d941c0040c426180103001601c0e1a15407940407000340c0b154446000c80c2820100014444c0e6003d001d0b000e010340e003459100400c00410380c00c0840191030100e2a640911100 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 823079082 1250 823077832 823077851
    0x9030106030f0303050c040e0106030e0a06150501020c04020a050a05030a060b30010315110d0c09150e01120f0b2e1e08060d08030901050f0f0402010f12020d 69
    0x8240b5400454404d0303034180040d50b50002a107106000e02e00c240c80c008030100380144040b902a411001c10310a074401164809078050700c4c1c410595014448124075004248028021560306009103449000b0641c3c087d4a03003042c611004046100340700b003d1080020100104240c100b46030064002409041c04460b1609111580d641102c040e02050084441d40311001c04007034040b60324118103c94100361441034036070030812224003614500000540d0303094100529001240c0620072a01410490394591106078140703807503105e0001c0e441e0342d0441880840e40b8407014680c2e22403420341c4000b00080001c55501d402650807000ba00c94410744a0784510600905100c2403141a04080507110300e1400c070400f884842e00950b88424401c00300008070030601590b00c45d145c040c800e00c98200c2e0015003810803007006500c80c804c8a03002940c030230205075114400e004119014942c001d4101e010340c0280c5a0300c1c1481d5001030f1805118071490301c02d100295a01d000c2010065055440c905032800b42409040d10 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 823080332 1250 823079082 823079093
    0xf04090209011b0302120f122409040c1e03060e0a0312140a110f0c0a03091d070f111e0105090303101403010609020d05040507061e140903010603 64
    0x2110344034000f0744031503122502480105030082d070040c0c060300581000c2080c1c0c0346461a5038050250018012003c00100038101c0108080034410b901d0506031008082032400148110041c115941d48100300704030500000c242180106021580b840b0301d445a281c1070314110400016580d44007070000b500d8410001d101020109035203407068860354400c0c024036003141c0b02030112441e01969034a040c43d0b1070005500b4012a41c01244081c1d089540b4505101c15240c042100b44d12100544550380c000c3e5400900705900080800007504042d40300e0504008032098842c68480e00928100420031140d070f07101c15041c05440540a044108401c2e0f400951000d0140442d0743d041c00b4030352000350300e0f24000034401030700801502c1c0221580740c0ea0102c143e2400140c04400c070242c40120742d05541c1c6034800034a0031200c0c4010900c40102c214045414506800c0607814000c4c1c5501a01c140510042078800700c0084900e4030b0500186810119a2a01c1c14816000c1c58003500038120b40562a08001106000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 823081582 1250 823080332 823080337
    0x70206040209070306060e120703050d091a0306090a02030703090c0b0a0809060601050405061803010903080402031005150d24050108070f031a0a23070e090603060411060f040902 78
    0xa0003602c07120350755200d11a048003120200e10503800011041a0000107600d007100c404000d015040f0102c035074041e2240c592a0400e50f51180300d1021070b440d120200480910301001c203080a1142c04014190710b080004140c001c1801024000d00f075a0000001c0c03d0140a0b41c005144640c01031a01c08030591a40100e0006d90b00107445c0c078010076507180004001680010b8018171030003042e955581018944414041e6541041d8602002040329907204146518248180a8114041d964a041c0c50916005160411032410650341c419420700f01040345404c0c1080e19a0280760307054a20048810301400d04250144000818028040002c560255100810380009050700c100d0b4040d03d10142d40d0b102d0600364a40b15110003800c4080302d882100300d11001a11295015034004004614000b41c41380b041d885d0b818440d09400390304000002d010550760f10082d200341c02001510124082d007001d1002a90355600100f0041c00c0300415141090b05450b003c041e03503a0144880307000758035583c0b540aa80082e4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 823082832 1250 823081582 823081591
    0x60302031f030c1a0c06150a05060909010e13050613020406050a150503070516030306090e01061d07020c1504090b0906221b05181914040f05070206 65
    0x20140441d05503400070010204407548009104402440c0c5042514080c1c50680310b034540030001c0c080b030462000e00303118240c0b103080101e9020b2448040802080580003050700b0403405007200b484804480d446400c029815200344002c2c084950303070f8040d0f4071048011402e200800c1030291500341f0110b0301000714860111407081b41c041c400c0035120001e20280d484507205d00481626050300481229000720000c540000c980d01d01245403600d40202d40741404005c0314214000b9540e12010010040b040c803070303418117200c8880240200c900d40003c10a0b1182080340e81e050f10444400810381490082100131051640600180788050003a080045503800622554a407281011b00013840351621550b0a84900b100a010b8140301000c1c00d40000d1002c00030841c40c031350f2991a9010103c641804001a002c2001552215620103000b080d252201c0f03070300441c05000d509040d460500700040c01400d00d0070f071001d030041c1610107860800014044c008640d5000c6002e407600050000c0181d002c1004c1e40719 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 823084082 1250 823082832 823082851
    0xd03150b1218060712020c1501031a0109020a050d0f021218010b0402030408182101091e110d03020304051302190e0a090c0e300a020607111906030203 66
    0x65060b5074051601c0d4a02241c0b030f000096107250718411041d100f580503181d040501d07000c40d0500d40c071034218811034541c05e1700141d4402c0540d000c00b414281d02d00030441c0c09000711890039030401c601c40300007a106014840c40c2c03080b0203454400b081c0481995030b040d43c9030781c9201c1c03035201c240f03050506000c411041b00320700d038081d194202419114a4242030007180c4c012544410605e1509103404040d84401c0c07000103401e0b900681403070b440204204000c0441c0c0c0140207110000401c0e80b028980b2005215000700c00c075140391980d0041402190f50f1100800c403240c004e42c2c0d5503c46054030325080742180700c0c5802199009401c02179803001410f86502420301d00c03440c0790044203105803581c81030310318036070f044006540140d5061090003ca00d00740c1040c84aa051800c00fa10b1504800000500f29000742513402900d0800c60006103204158054083e44d200400e4040c01c40c800d9640c011400c10321480d1005003841266403240c1e402c60f00c4e02c0c824001301004841055801949400c4024003940c401d0300e103c002c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 823085332 1250 823084082 823084111
    0x1501090605101403270601090203090705090c1b100609020423090c0915071118130b07120212070305070e03030d09080705160518010303020d03150b12 66
    0x59000b41c020903540101c410070707603003145c2d106800c1c9145c0b84200d100720000c0562030715080d021002c080280b80c1c003900c02c0302009a124030700031601da4039180e40c9902151064000d0014404c092401d1400c44001d103001101020f40004130101c0b513841c0414551344825468607084000400030015406002502c81c01c25610680e000c0342d240c000c00174110029683e91000c0003001080443c03e256004040c40b60020701400b00c9004665501001a0000c20050f541c1450a50140703955180030300c242242a2094120030400e4280490002240203600000815100e036800110751824007612081c18040400c02d410340d078402c15282c070450500415180ea10110703041034081541140034000d50550200050001d40c1062200010080a401008420380c1e24003010000c140110b0414024884a5401c204500c07100d189000240810900803008034025401d0a130014400242d0200310880e5a01c25444c020071a40388601e840d080c4a0240e80c00640034100004a00c0e1141e036907030540901c80e0f00160b00180c0d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 823086582 1250 823085332 823085359
    0x3020a0b180c010c1e0303020904050130050c0d0614090f0c010309061d031206030d1b02030c0a0f0602071203020c0603070e04050a020c0c030a231501090605 69
    0xd034161055007514682c0d0041040701210794411407914030214040c2481e070003801c0c50410f84c406000c52140003500041d0300003030501311509140c05001d00500f408691b0320001ca8029a072089a81d19200140d18100c0c181c0b81c50100740701b820800100c0c0f43c0f0f001000e2460140d50342c641040248080c1204d032501d2010180011100070021031440384080d40b517005080c848544000443c02000e510b641280d10658070f41041b48410000742d0300e000c0014202d00116a200360b6491540180ca20040c034440c429070050b600c540d0300a501a54128100a00403502c6100429500c00207051941c46602c031500b10314041400135030403203411000402c0f50300343d8007600e220a4451a240321002208100500035034080c0b1040c40355414602c5c021a48142c1500d80104281e4940700010250b410a451152200c2d401041490800200b0f00001c501c0010450041540031511342d0f0b05000381494028460505406040d1a030300790764140584401103200c4407030442c2c15a12a0500e5001340002e004950103141480e000c05d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 823087832 1250 823086582 823086601
    0x302060412150e10110f03010b0705060c07024501150806030a0809060408010e0319030218041a0d0605040b060306010f0b0a210902010806180121020d03020a0b 70
    0x124007410400207403103116003500032103014000032841484405c038104000008018520046c60203800110445030382d0317010600305507103000c0019268030341c004010006040140e44035400c0a80c42544254001d4244041242d10300d0105e0b055042018480701654103208446503240295041e100b035080035500803150101c2c11650140c0466190740c02d0352000206c1c00c0441d09030320150403104802046149402d84070354029082d90355010b0104150b03403000c20010b175004c91180070070603840c0c11807908500f0b059401c0c0700d10a4031860350099034010307a510300e8290301407011200d07920403040f07015011440e002d4182c40e20000800c03003194140d5800390514007040c100e01e00031415a0403100030b5204480003605048601403550301980404050246035504024048003515030f05040807506c910000c0c0c02e000c030340000342910000030b100c188201c9008020300c01e1044803241c000d040d1440c0c0c0500741120020402c20006412404002079171003d261198541016400250120300f64462640700e1504e880da0110f0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 823089082 1250 823087832 823087841
    0x30b090a0f11041d160911180a17030310050103140708060d06050f150a082107061d1204050907050d150b070212060f0f10030206041215 60
    0x4144025408151001ca41d10250496030100020000222443ca071813069903000c144110044280c0c0114a0100500c1405000300001304000e250502c441a9025040405840380e000c1c030b28290092820001050740f50480480c02070002450884c001c221044041ca64941086401208e402c6030028041074951080c080c9440030078504010b040702c5d0705ca10300107a0b07007480d00038001c0e034101e0081d42c002c5000c99050700505024029081c481c079200d080240091b580c3c0c0d41d41d80c040301d010340a0081d041041200006080c405050000c030044030506000c00c2102840c400c0b5000074002c54241042000c0c00b4482150341c1c0b03406c0304103130100e4154400c107109601440c003c1d8400e4651144000c000580c500c0d014100406120030403110014503c04070140d0305001806a401041c0c1c0458045001411420401001ea81340c0700c01c0001003165103000004a4252540144060381c85444c582c04205107180c190a484091075006000300d0b10345848d01e201032852450060103841342c050507000d644c1c440425104 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 823090332 1250 823089082 823089103
    0x10180906050f0f0108160c0f030c02042a110309060f040503150910090219090b010207122d06090f110609010f08071115060103050c0c0a02010309080d0c09030b09 71
    0x584004690724840e611b0102d8410100d800c01b0300c00000d14140000ea03641d900c01c00030781c1c42034480203ca81c480e401404221880540701614200215a00e0104440200c143e00540d507010319040070504010b1091500b035000300071006800c06030200d1a5941c891010000d0000d4a0090b4103c5819982c40d40c02140d81c1003040d6140c0a00b5006411203600c4040d45402414043e40003a007400d1001008070080e03d195015540a00c02c1e1590303a92440e521907034140222402024401c103001c40e1000395803105100517115510b40145060304850710a08000d81001c060300064000c2000c00188102d400d088a021801c0c240442d001c9001100ca40050310780302c02503450600c01a500c290703407100c1a03801238411104c0070300410140a0540d41c141428603040010928903503000c0e83c6400341d814103400140585102405004e60350300107029912202600144000314203809190210b412511414126407d100c3c5545000400c1c2c2005200c100060708120500c08880c4034005480266030b580f50b496072035014041 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 823091582 1250 823090332 823090337
    0x304292503060518090f06100b031003140a0c06170f04030e030604080a1e0806090a021b010b180112170d05280e030403060b030708010903020d11011a10180906050f0f01 74
    0x60062001c2275500340610740c071444800b02414061344030746030f214900c80d0780c2c084840c160380460100c104110300301e0840300c0244017a050150080c0d58042031007060090050002c016001f5980010301498480d07120b4860b58000907043d21040d04160504490f80c2e4040140386000c01e4003e10300010005002c455481d000d460341c0e030398101ca502d800003080b0b80514090441c4058507028888690001e0113290b51241c860300c0f200c00001c860f80e85009000c40344480c000c8801d00071004800401010117001000403981398088164140c100d400c404811003030040d802d01304c95a070300e000300300708e103030720500d81c0300c9037011130741040002202d42c02546030065401035810008540c00c00d0208000013203058100c0031183ca4001c059600d066151001c076421500b5100c0d0540c0140d10142c0380d51070b030540000e009586030410710002d0200710410340002003009080324101e80900d910b0f10600140f03910070350114180c2800035040108151782c820200c8098500c03406141e200300c1e200300a803010f070b01d031510102080740c41c10b8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 823092832 1250 823091582 823091611
    0x415090e0103030f230a031104050a06140d090308010501021c0e04020c0102040312020d08180601140102030705010c0e1306050a120201050f0304292503060518090f06 73
    0x141c2e0f040752102249580c100910200d10308400c111001901468081c1c2400340303035035031100c42022008056881d010780380c5126110401041c8050303215501d102d41a251603080a0031003201a50100b0007900c40c803c4400c010518041382c480c20103500c80394460403500240e0890303101000c01e110280000c800440b0f50800708600340c0418407582800c0d0090900c140b61500010705180d6039440308409942000c1207680180c00000d5000c480310b81140010b1380000480c8034951ba1094030941043c3d465a0602511090300013110406185070300c00c00807125483c0c0c0c043c000380301c20740112502070b01c0381740740b049003900c03a10302c40145082e480c99134404c00049800040900800354a0710700c018800390710503d0305904204042018194000c0c2e240001c600032840754210000d0104c041c600343d40204245c036007000f000b842071000d0210000c04060b550010b9040009501d00442c1050700c00e030001c0c18190f0000c2c1d00001031501d04066041001e10940c0310700c0d0100c1c107480d00308808c001a540c90344030440300e03c40c46d080e98 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 823094082 1250 823092832 823092839
    0x10614090f07200f010e06011d040807021c03030606020c040c0c110d050d111005012304021b0f0c030705090a0e031c331223030415090e01 61
    0x2862040445280b92003000740b40785440f0307409810a840d148808109130745802e05840b450800b00801401440f6a000300480c0300204c5a4980e440c4034040c0014082030000300d03215040d07540da1300c8400140f5200951078000340000c0d20b409400b800c000d01c01c1e070016010724003161006051071701444825820036911204c518070302d03986400b04849403038420b941080540c0a0800051401c1119a10852482e01d03842021180e6180c41841c01d046945c1c2039180702c0c14000100000070703c804030800c02d00c4680829000381031210b00402c0c009c0c011214644084070110ba2042020840810060001c2d40d03090203440112100d00149a55a5868481c40d900a01440006040c1c840c00e03038030400d050a038540a07079207050703203912140a201c508040c2240d206076030707441e045043d1803c0f00c01100402c3c20b035210925100d0404040e2504d2100307140324a08010454034928030401010020001030b4100c0c149410303915281d40300074140d03650070a0092030b54001031400c41900396401201244125100c0e1b50300622160308 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 823095332 1250 823094082 823094087
    0x3060f080d05071b0314100207170702010c05060c09120601060503070f0201020909070f11150c0c01060806040f0c0f0e180c090108100605040b100309080f0c010614090f07 75
    0x103c403074151110001c00e4260145084100d003980c0c01103000e004228202031910003114107207d400d403182c2e001c851040054000283c034060500704910001c13101a911780d101800141d403e031035903400c01442800745100300603824ac80d400103020940025602d6084c201e114200159540030203000340c202084080c000241c0c410300c2175401e10068000d40c4000f41c01e0109801c00310701c1400741562150081210002c0d40c4c44c403103510014800201c0e80200080c60a001040c42d40c810700140580078100c9184001001c519503030b407d400c0103009290410071902285828203103241d1814080d8002c0b242c0301140e1400260140c01c2c2001d00b01036840d1440980d880b500e40e001c06100700d03e40c64401a11500811695200a9403091006802020000064605a488c41c032921045803841d800461040c3c2c0b5240e0381e0200d54490080e154dd01c24024140051840301d40e091500140c0601f0740c03034140d1080c00181000c4c103182c06420040407038411440441c8010803000800105903822100144540041000145010b1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 823096582 1250 823095332 823095337
    0x31d100c180506120709031e06110a3f1b180b1602090406050603060106030e1e1507030c1b02010c02150d020708072603160509040905010c03060f080d05 67
    0x1c01d11b06240b014503030f907a6244030f0300542c3c3c0c03c000004404d21102c1e407c03c1c04598001c249194202c81c601610306880c84201624140e01d21011044504001c0c0310303403100c070b02c5c2c00540013440200402074400c8c3c4602c84502602508480041581c0c5124001d0f000d11140d000704803190044803034825041c0c41c241000c1da00d0072190450144840e07901c556124120158982c0d0080500850180c00040b9251400c01c01b41494101c0603800b544c1058640584072206440c00b042c10282ca400d120883e0311450114003c080c64820600211423410f03090009012401d034055202c0402c1c0b015030785444504540005990a48800940340a400300b4031a0000c0c500524005400d0903014008070089401c0040c80d00c001780c100d800001e011260884002104030074401d08070203d81c0d005e4044400311801c1201440503040d9030001810304a5843c041118403105140507809480510130040c104118040c81d908055004c1c211a11807440803a00d0180e010507400d070720a0f1301009996000e4000e00c0720480c1400201c407240d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 823097832 1250 823096582 823096591
    0x5040501180506040f020c0a060b031b09181f060806011a0c0f2e0902010e09070c050d050703110a03050910020c04050f0601110c0a06031d100c18050612 67
    0x35030385d000340100000243c03016042400a0000410440711546080c030101ca841c43d0700e9520990004d07402e20700aa1070303080186040750082e19510360726120351100121441110040506034022401c815006071070001c412044906071081c107210040c0c2c0d031411581c44040c2030007525062000c20100310700078000c08004040d0000f1240c119865400440c0d42c0f02d04141c10412032a82c0d800004101c0708400d41580426441c910f102801040101c3c01c03640042d1022541030071050190b24041d0001e40e407140114614000c240d0420281c2d996100d20301c0000304a940111021008694412501464811300190b007031240c0d945074546a2614a010041000e8000b5815403401148990700245540c2d85450013214040c02034443c0c200d941d42001d400144c00810b2150008441c0d521100480e5456960682c00790202c0d2958280068800c0c12104810080c0b144148242254810141f0b0003025080707580c80610200c2ca281c0d00d03c1503100d0102540740c0003030365034072032650300c18009d101e115a07000c508081c05400 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 823099082 1250 823097832 823097839
    0x706080702210d060e010e06120a0803041b1d0c0d0605030a08090a272304030e011b0302030706021602031603030806010801081914070e04050705040501180506 70
    0x3041481c82c203080c20b8248032040141c980300040b40c0701404030380303a0141101a04841104240560501c1c0b55408910002040184917800400c54008004001c0c403080d015076030404402a07491502d410307c51318154100002c01440c0002c1c0708001101d5884030920718101d0030b141a848a940c4507000c00400700e410001312a03009907618800010181c0d410000801011300c2003a48170744605440081140070106544203c2201100c52500702c4d28500c0e01d0119252006005800074000c004c054500340e14100000004903844812800d21090541003506000300c1402640c2d191107052144482e040e071711101d4100180542d105200c0c3c200014020303000f03884001221001c84035207900c01e4000074178040c819000441c042518000900038107502003401940f01c070080c28940001d514011900340c0d00d0000231100e245c07038015950004100881d41302d4a0420580080454003066103550905003201d00a44088440b8444d400c000105402c0c603018050498841c803840d1603030f40c0c05203050315003d001c00826a950 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 823100332 1250 823099082 823099093
    0x5210a0b070e030a143007030504050604060e100306081506030c100f08060906010504090902181014030d0806210d0305240907051b0102030405010b03060c0c0706080702 74
    0xc040c0c90810210b01030783d00076081907640c017215444903800c0c203440c0c0314841c0380c41c9604019102d846d02e46d408003550305207601840b82e0742c480550030125000d000342c0c0c1100d90710039800500024a1a4070141030b1016100840702d030081d16560341c1b02582160030300d01c2003001981100d4400f1032100e03c8149045d91041e0085c0079038038483c000c034000070700354500c0c00c170030a0205000c8025100042e0b844079000e940180c0c103070b40807140c9042c0400003a0183c020381c0f04041610b43c90f0482a0304541320084405003a40c5885910742003400c0030000f0705110440c601501c600c0d40c464a00328442c918000401003d415016120329055803100000c1c01840407a2590708500340c3c801c1c000807058040c2c108024101034005a030000768600740004040c01c400206008a0101c83c040c031100c40c680d55070000d1243d00800c0500f0106c2d035484103080d031580158070300d80b00c07000154408801c001c06d1001c19001300d04041000c0b000c3e10b007550b03070740520b030152401000c1d10003040303038030102c401c0c05014007070740e26690444801d004442 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 823101582 1250 823100332 823100357
    0xb01170708011d06130201090302212d031303060e07031410060b1c0c261006080907060c030c050102030403090608010b0f090d0c0b0703080105210a0b07 67
    0x14259a41122040325080e45843d590b410341d1030074130102c3d4004c007100804181214564000034601c0450380030281c41003000c0d4280c9604407209490441480007170741c0c01d5440340001e0a01c11500c8270341a0340b400d608400e0546078590340c0c19011040b610340080001c0202d0b0000d0450700d6400050002d01140d0105108282004c0041904040007a544920080080c218445401514800e995059001180414040c0312400071020f018410001020301014001205052001d040f203013000300301d640700071214000260044100090740c06600c00c18101400c00891980c81000f25130000703086400101e1500400c1041c4412445000c0c0061001c3c001e140500c1016000c4c0c46240c01c82e8420b5800b200170500354001044050380200407980102030f10540241407044130158064540700d1308072000e21031806e910051b81081187c00c545405000c4041d1100d0310b940321440c003e0601c034401c0c0030700b91060b000010108100002c0071440c0c0c0f443d408100190070100390b9030307851754242500508120700b07116148040030b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 823102832 1250 823101582 823101599
    0x20408030711130501050303030711070506072603040203071421150f060109210b010303050c0106080a1523090705010806040905060c0f070c0902180103090b011707 72
    0x9020050040303035000300c1c0d265642e0411164400190803c45140e06000040200795008402d4039407104c00d038204280c21040a481c0701d03050400356009194480400b0a0072000d1260510200600310b80310f030088100340082501e400e005001c1218000d60592002a060104400303800310900b001c40058120741c0100c0219405901c005150782c1c4102c0241e021444000901050130800782d0001c05061401a05090480000341110f10381e006a04ca2000a00d08101c11109000200342c0b00c1074104000a21550b16454000e0055005440800300c079803c20501162101c004610103c80f55484400240000798041022000d4082003c203001d142804002480319686002c20082c4035644d914060000340342400009080d4400103040c06010301d24000349500002c90010360641c000f4401c1043c00d884440c00d82d8070140b14071034103000800c007240234000050003502c99006440c402001903070540c4400c60607001103040b580303c0c101c054991605403004000040100d8218a20143d40c0020703506025203d113000d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 823104082 1250 823102832 823102837
    0x1926011404120c1523061923090f010f0e0f0712020d060305030c0d140931090b070305070806041104030f1101091a120606041d070206070e0d080a0302040803 69
    0x70341c928488174551100001d0001da070302a0340032104448828040840d0380881c1080e4410780901038641b0b844140401c0082d101c0c0e5800d80e41100c3c014403805451602501c5624001020f1283c50082c0f20300d0800494507000724940f440c421590307007401c3c1d03030f071640c0f074005c100ca10000c9152820b1600d0750800c02070041842a025010287d80607900469448407030b5140e951520388855445020880c1c0c000d242d4a54507082c000701e68002c04104ca212a040940d102c1c0c1c80c184102900d004070145002c114040035070340558200f282e049005041000f641d94525a0070790954204482c8080051004000640c1c18500360b888908032017103040240d030401d074036030355030f020180c0c01810207480200c02c00d070034a00a583e0040c0000060320b041d03030002480003c070300d121a141780200f100305003220703001c00c00245691326510309a800806030300c0200303840480003da1005264009550580040c0500800200781c64010001500040005000e45030310580700c0c1c5401030148c0017000c4200406808210010740f00008002 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 823105332 1250 823104082 823104101
    0x3180f0105071803020a0b0d0b120109050606010e010806100e12070f0b0f0a030921050a0f05040501090623040806090c04090309051926011404120c15 66
    0x585400c0c000400740c01040310000104005003c110b00740300680340e00000900301d56110041644a1032113149803406440b00c03c6a00da04000254800000c07144150440d098031809802a00e03103640300c000045810106903840c0601280c50140426124145003002d11343d10051450480d00402441c4001101203084880504240d80304590522001e804000c1c880018610740b40414a402058041500070340907840c042c00a00d070362001d041007480f8840c0c08411074032021803c02602c12890758005440c1d80c1210114000240c4000c0424200901031030071107094920586460240a240c854100d41d114480201090020624040a11000c14042c0134001034039101e03010b031020345007681d0054076005013890106e100d282410110300c0030a4228042c9030035a02c042d507001c508000002d102c41c070300701e5140d404614001c901089051148615072071a0440c0c5400c40003d00820780d070420a00640c01c000d543c05001680401e5280c0002d90007581e00c2200c0e94030440d0210380c01007080340d1460441e40c0545 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 823106582 1250 823105332 823105363
    0x6120c0c012a17010503150c0702030102041d0a090b0c0703030b09042102011515031407020606190308090409030c062a1805120f0102030c0d0608030319020318 70
    0x8030000b90841d04861540809004030000309071640c0360a00090350303011a4890f254100e60550301140d01c40841c1011103500e01d80140081d540c2d00d0b52940703803c1076200840c010704085884c01011600f003928500800c001107801401e00d10711500c904c1400301c10350380031010072008d040d0f0312069400c1c56152200c80a10a83c0035940d45904e6034001c501039074078480566000c00440e498004080034540f2001015026204542d01103280901100c07001e400500040788001c039114100800c0250695002070360070321803c81500d0180044c0015228091030440074040280410814000b01051b41400d07400110f00501902d400d442004e03241e154941150b1020222030318241030312241201d60480d900f10003d44100510304440060b6408031040090003032402218819090700c1a50825003601704060b50204d0503035002103640b0f0601e85a030080903880000341c2d1041604003c00042d20302004410349100cac800c82c0d42e2054a45604503800402540300a000200154005030b040c0010201040707900020120320 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 823107832 1250 823106582 823106651
    0x103080a020c030303040309030609080c0a121d03060c0703030b150306090f04030f0c0501060807081608150a05060307090c200d0f03050a1b180506120c0c01 69
    0x300300282014031115415000e68030030424000000e900c5000d1030201d030b40280000560603000d14103111a40301e11045503150b0311403406101d042c004440540c54000c0200d4440c00c1b1143c41501080e81041004000560f0581005000940c9804504010020903210345800180c034400d00b0005a41441c46400d4a1b00044002c400c04c9024100520038603084200340207404450703d0a5a40140428100031454042007080c100050400c0350035002240134007819400c0d100c00381d46a1034001e40e143c0700c041752402403030107c1100080020780841d0a8400308003075049030a50369101a038250241402030b2402d41c01d4810b4480001d4801e2441c403540b0824403a680d41c202800e5985134034803103054003518070030311603401c94620642c5032030f00038105001380107150502080319070f00c1150240042040d080c422440742800d103038529160b940700500c0b003e01001c0c0044552419102e009028403070140d220f10070002810500070034007101c00d00e005450841c03401c100109000e4620645a00350600880190511040c807 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 823109082 1250 823107832 823107847
    0x1b1809020322210c02060307050711060d150905070f110708120a0e10050a0c050708010903020303100e0906060d11030106061206081504290709031a040c0614090405010308 75
    0x1400e80100f41c24482c0e14000c00b900210350001101448094030540500100050080804c101030584482d941c000074501a218200c9420040c0948100c00700800020040c03403006c21480e405100e0103009428540d80d40071440c00d0b14406445a0f2480d403100d0119214a87c0c0001314040d04010910030407050001e1503031039402c00c44000d0b084030344003080f0301e10900c040000041e01680c0700041d1888a0740c20314000401228030b0078450704100140d0040d4400b942014629024117800000950040d00113001e035914050340e4070304c440f00c9000240c40d8080d468102c8004141d8501e072810b1500106801076041d4880000741000081c01c44e40194040b4002c10291154403100c840f892003000001c0c84100c001c1c1c5070100c3c41d203001d141c0c80400104020300d003554149540c2044c1401003041650b82c80c00700e0304006941028103000d04103600c1d6110444034000081405094003d008907610701496200c1010015603013060800c0c2c803140000114041507880c248902400b99807140240b034005c44c0140903581c0e80c1e012 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 823110332 1250 823109082 823109123
    0x210050105010c05280807050309190f0302060a27140109030305030a0f0612051c0f020628110903010c020d121e020c011b1809020322 59
    0x105a101c41c2c10b000c02c100b00200070941c045903c050090109450340c0710310801d41440d180b07200c050800507203c0b18010030a4000c000002005181c00c0d601128524400301e0702555840b001c071101c0c0200300034540c002c9002c20042c105040540412205400e00c45401c981c91000c0c0c0401480000e41901d03e4282d280d802c004000d0b10f1103810040081c00c1c6024114541151006031442c480586030306407450380d40703e080044030115488003020b420046d491603482003050a18940c5e824846a0f03100c0c17400e45007903050041c14010400c80c2410206030b0041c01e0965110b000544404030082044031480d42c000e411445460201e00c581214804141d10180e1030750f0011090500711007054207480d06541c4140c01d0588070b240c02504524212626000102e00c00c455030950b290301942c64207801c00b038203001003580507058406401060038140740d204484060280d90310f04651031400c90200e00078074240e400051110005c80e80056a0080341c40d40d84899400a481990300e1000a081056901c01070b00d0034501000c05 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 823111582 1250 823110332 823110341
    0x4180b070f05130e04080c0601120b0c130509040c0806010f0303110d0e06210c071407050609011209050703080a11010e280c09061502010e030a110a120210 68
    0x20305490824148031524406411110f4a030040c60420401d01c0b00050801100302c04441c5014a040162019960754811880340e030041d45800310340000c8102c0000e130b8105481c0d0140e41c0d2241d064041801e5140c540703824060034030806002a90b40d41010b040c0414505030070042c9900038211440c400031090320b5800d004207503580002c0c00745110380000c0c5102e590281d11040182c0c42d50f4013125110354035561118501c022410203c42e41081e40001801c02c10321107851740c0a0b10030503009000d2859140e20f007440070fa0711020703e0301500c0d501c2101030162500d01d51240641041201d41d00800040241c0e544c0c945601d041d640b5402112655030009401c0c80203680412008042e200d200000d00a00030000e01c642c0c0c035510b1800b04411410303030740c40c00d00303206a400101c001d50f402d0700480000020303074444040c04040c0c0b0450040449180c1101d0b000c0440920522540080014207005103007483c420280485a0702c0300c0c4902c461262180c900b600300030403d01d0311104182c50441e0000c2c9030658619940c41c0c10b8a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 823112832 1250 823111582 823111607
    0x9031d06040f210b091b060c0604080c1005040516060c0309051924030e030403020d110102070b03070801031e0807060509030c0307030509030c04062304180b07 70
    0x11681440100a82100e1040810943d1401d0602c0310a00d4603558411244808448001c0c04452040040c03140a110110700e0701100015404101e207410412030a000079403150084626440e4485000600442c9103900944582591101030f0b4420941030a2040143c8006075001d8542d6005450b030b550140000b450100010005802c001c070300c10805440c0035000340c11318840c041c050644075200b070007280c0d07018906201a103082840c042c014807000100c0d00315031209510800c00304e0f1410140d027400001c0001540d046a500030296401c0e00e031b1981d11074003605960800641507109d80800070481095080256110b401d19503030304807580d0302d142805d40f00c1e001e101c0b40003c1b5a943d03500304000421840c1085030040b5030130400204443d00d410950500d1481a0504001140004104841010340c05001040851070450841344070050010402046070031600c06d51001c0c06042c404c000c851100780d0341c5100522070017040010f0f080703610034065440d1034402404a90724840c0e0702c03c010900e40c0080500280 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 823114082 1250 823112832 823112839
    0xd140708010f05150a030b040609020a12030908011e0b19061e030908030402060714030a03020c060a050c19050d05010f180e0d18050303070b090d02030c120706020d09031d 75
    0x84c800d00c0004102030541034000544400901d00010f418402d507500210002c0e0303030181011918617565440c407800941a0031303080340020003800001425100500500c1c0f4010011542d0b0260f4803040c5207140e0050020512a50704806c0311024511450440300480c80103203131303a407075049a0780c020380405108001030784161418180b5090030900812045d400352540075078182e4000d0755504680c1040d003214070310903000302042d03c0002120740c10154180c0181a41011036401c6480b0ba480e04058582542d0b0101c2d040030140360244009004e66108000c0d000c3c1b901c0c0030f410aa443e100c4410010030507100c098001d080f40c00c05240041103602c0c0d0b00c40610600004442040085144040240e0b4075243e80e0041001040710160103c2d0326801c0d0300000c04000c04004003241d61b03950080c81e21803081c0d20102c031501c9480c0240000400340a0022086554500500014100702641140c4d40e0702c00d600005010f1790720035424420500c02d4a1284540307016140252254000d2400d070002d880c2c447c0070b0031800c1602 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 823115332 1250 823114082 823114111
    0xc0201090b0c010b13060f0b09040b0a15030c0c0209070c1e030309030801081f0203060a120f0302070e090709051902160c0b0424020102090a03030e130908090d140708010f05 76
    0x1c261032040c1f40030942d504d0b03010940d0f8070302001000034040c281c0480e15682c014100c5000180d9022104810028605192002d211002150006440140988202940000041000402c803038420100082d1082c400c194003a040a100100040c40e01d10b2240d00310f02196032480700c5c00c04e160300255100d004180c40c800038003802d01d122461502d001c40504590780d0303994002c800b080090307941203440400b030011080108402d9449090039600c68510380e00680150260b0035000c0351424a400845102c0c034448401040399915004801d0700501c4014000c15000d5451031500200302254001092102d070107500841600641b4244401c041c10340e940301445641040008100e400502c66155050a03c0142084003400102d40140e0191145041465001c40d0810011003059000900d481d0007a400792941035141d407819100808603040d41c040500b405106100342c0640e131800e4812040f074a440b4840042c042110780c5041864041c49422100e0f05075100e04c4800002c110a03c5240c0d03028840300b08603103 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 823116582 1250 823115332 823115339
    0xb09030a1418040b13021c1104031a07020703020d050d0206010b0405010f0305150607080a080a02120a0e0703060e03120a020412020d0309120609050f0f0c010c0201090b0c010b1306 79
    0x4607484240b5090600490f16400d40c0c844503590360b103861301400b0240300e0565444200b1140001d003080940c0b45a1811880c0c6000407200203001c0c4180d4003581d905c22501c8011004c0342d0198505600010580d508510505001100586480004443c070382d102e2030003000c2983c808a4003904040b0160010035821038144010031490ba448003810744144840d003800141e50702c030031000310701007052140d0454002400056210810007000000e00c114103c641d50b81540391203080500c0113034840c10390908900c035200d4000c656002d001d1313070041c080540b800f81200c04040d542c1d40d4403002e1f1400541c858a103508082065002d12802503101b6902100f4194214541400c1a55600303840c3c1400300042e024485041c10340042500461090700540224440c40e043d00308a031030700700c01500043c40308840b1350107100c040310819031002640701855801e1a0150569000039001120001c81c0300c1d405904200c060140011001c040b10002c0195540c82000442c08404110501502c680d10030500040c0625288041 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 823117832 1250 823116582 823116607
    0x2061c061205010b0d0830040f0203100c080606160f05060105030f0316240905060105010f0318141e01060f0b0304081c020708030a060f08010b0609060d06030b09030a14 74
    0x1c4000c120800c03c0307e20414043c040f20760000340c01040c4100e00b800082d0a100c00d00400b5070780f040c030712071080301240c48a072080103408003038071a000000c0d004180d1084c08200d9614041c0d001d40000b9030144512070340050b203034a42c01c1d03110080c1c94083d00ea41e0010b030018083e43c02c0502c520000c2c14020300c000c601c1c0508014203070f0001c0c00f9050000d80310303424680da80e0140704021000d0000c400300e4070105003c109400e041080d2a02002e1066602003550b401c0702e010298003031b016070307611108644103a00d24558640c85010344042d40c404411120b01481c50074070350f6522680034a003082030002d00000b801d40d0500c0030b0410514184d400601c031a10080c404c0100050214048030000c07488031424603020140e00c041000a80507680c0000c0250902000f08024a40b455101004484055010f0b00017169500c1c174840c04c9904400c001c64000e10104540041030424074018081c0d1215144002092581c94407801803612040d6203010759a080041c071306900e2070340480301c42d100c0d403060b1001c80e103450200c5140 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 823119082 1250 823117832 823117837
    0x60f240503063c0312071106090d2103061401051c0209061b071d072a1203110a05092b030c060506011d010c03021f020c07090203010506040302061c061205010b0d08 72
    0x200c0c8622400202706280f0784400c0f820b4400ea9501c040300171000802028503001038400c0b103682c000001d2801d540000d01c4030320024564032034030040c0c4417146000c0901c903000c20303003c1201c850f2548140d001c22030a41c0b0750300c4480003031000d22150711001e101c0e00c965105050030003400790300c0940303200c911040c40e800030b4120300e8400d500101641404107844030148106481c2d00c2c060000001540c1c25244140c0a000c607504451400e540309540420803940c003400c2c2001c0c00d00403008100001075080c007895070039050841e58000032460340324913000c01c0600c40600e00440c6001d001c040300001d0b0100004820007089010b11600501d090a01109201c0744200002c101c14a8400d582d040100200390341c02494024042c0d005d1034920051842450400c0c400c085010f5480402d4101c0760384075105000504134500d1080d24140c0700010700d00b501c0c280c40d540802005401c42e0071000c03241c04008501a50010742c911410b0020607040c3e00304486c084043c01c22908481c80340500d240200d14403262100026942c404 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 823120332 1250 823119082 823119113
    0x4080417010603081c0b03071a0a0e06181e030d0f0e030109052811010c03050c03071203050a0507090b0d0f060f240503063c031207 58
    0x120001a548a00c15015014503803010f03000100008031506204101d2480050f10150003a003072140c80304500c145603850b0030602c110081c40589c0110300701c4061a0030010056890f15207410340800c1d40f69030000d4000c1e449003910303100d240003c1c50109101e081c0b02010601629001c0124040030b0503005c0865110381002810004109541c070501c0c0703416010343c3c4444002c0801800030400d40101749042c40ea1001c403212008106510442e18004150b00000d903c24626840601e5081205000f001900d514070300d0101202441300c04e1000e140607140400203890094094008103850049008000d0100e40025118022490138142041704454100c0009000c580311b600341d6680d80c0c43c06043c4a0001c005108000001506200700010070200c3d0114030020f03a1520300c00c1a074082c50b9000f014100012500c1c0f540081442400040c40c50700c2c3c1a0012030030039001c01074850040907895416000300c2803800360101644003101d40c61000c2e05042203502c940c1088840320901d4141661141c52460a101c1d0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 823121582 1250 823120332 823120349
    0xe07120b060a0b0c0604020a09111b0a02090a2004120b150a2306040501020a1502070c08030703020d0206070516050106030501051e0f060a18110c15010905040804 71
    0x24040750540c0c440c070001a00502d01ca0380550f40350200c0d110f0403030300c46405441c140c1c45521068000b1a4580061140c44e08640280050030301d05400e1a0799409403854510300c1c94018000d4004030b83c05030b1510303018244101140000011030151854a01e204161103100001f0004014001404104c90b0f0300c0c42d501036150041500e00d03030740d602e1140c024182000303000503036048010340000180703100356480a100ca170003218020307101801500040c40958080c1e80304490050780302d60031540100e95810301820b1428042c2101500e00141c5d5122002c00130000d41c045910b580c0005103450901d0ba05209101000003948041d190b1407c0000c40146203018400845881c8000781c082c0004012013540704100555104000780224602038461030130390004600700000001500c2c001801082000280c0c0d4481c44004149060302b900300080701101c20190300052040d04d41c2e03030a20541056a000192401826510041400200d518400614540103900c114282c90901060000190300542510103566514 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 823122832 1250 823121582 823121603
    0x30703050a110d09030801140904151b0e10030501060915030e060403020c0109090b01360315060803090609040c2a06050f0601020c060c0a08030a050a0e0712 69
    0x40c00c903900600007034046001c141c00c0003500605001c83d5070000c0318114080c1d142e0244903a61001203203144844a20b8007648040501d0000c0c0004120034043e1000d808084800901c0d4403606402c50000b81ca103500c0b003004070710340c04502c1d42c2d00d02c0c0000701c0400344401c0d4901030046500d030a8025000e202075003d29240300c00450301001a05102c0da00c040081280c1d03400302e500904003400d010391146007035a021400100c54103400b180820071405012020f62069649150342803034070301d55910702c030b14025031800d51102e0300300050300800b0701c4107600000d14020f01e01d0070b100b4815283e07400210396945e440050103801c1405001c45607550541500c6502d041503a0208500c940c2c0401280c1d815111861420600c800286040031030940207000b01055228200800468890140401c04420100c84031801a4050000712102d410300401401540c9841403c8810703031b103107695605031250411200003442c0c2c2e0350703481007221442443c040c4103040480d070b00c0039012103420055522040c002000c406044013294 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 823124082 1250 823122832 823122841
    0x180411160209130b100509070c03090e180a030e04051503061b040f1212030e1009111002030c15011503050705042d08010204050f0f0409060c1e050304020603070305 72
    0x10508803100103030707200c070500c201443d00c40f05c04940303030380a0701a56000703406a1001440c0390780180c80032555944c140e106c0e0382c00946007101c0c0d6182180c00802d1501001c415480c1144c0d00ca00070881c18100c24443e8079a007141e03864400910040b00d000806444590340c014280030385a403004581281c001100c4244047c0181115064890328400c95114400558081e00c00041082c034000d0119101e512407c0d4a1035024680f05085041d5201c0c41900d003046d800091010b1103445003588801742c00c0b80710340d03c41132410b0750110025a0f4000c6100168016070070000b0749812110303003400354660802020b059034070340d0b506044000720155051840c2c0401e06a4400100381d02c0350180d003e41c0c005100710101c110015400d80e14407454000c092100240024062030082040c1c8010300030749042e82c00152007107100d26112000c01410744500040f00e0781080e90b60322600c02003400c0740142d100341c3e0f46644400351102554200f4a03d180d50002002d4100306c0144140001640c0c3c03002140c0d0010440d00e80812140c66 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 823125332 1250 823124082 823124101
    0x20103020f070b07020604030e0d11041e0f1a0d0b070c05070504060b19031b050d0b090c091003020f0306010822120f02010e070504110d02180411160209 67
    0x144070006045120f415080100103680041d2951166100b07907074501e02d20400c40b041c0104201405802004000d410120b8400c60401c0e51010800041003040c0b012150445180c01089a09804e482c496581c0c45142a50b03410780125103000c200c0c1010303030301004c03107601d5a00c3d10b90114801500c910200041e01608100b80501048143e000e07010090040050968422219401c3c2e8480040080030703252000680091a0080c81036208110f030941c020000d080e058a422a0250b2040741c640e802c459903080704414980384c8001d5648149015004140e0710150302d010040c4800c0000c81c0c010406004011129400c0d03890f6058a030400001e0038522800d03260704100c0001201c81174649641814001803087c2030065114944500c414103850782a41d850381c240c8100c0c00e072142c10b07141c0c0807142e00402c0104400d00b80f540c00740285003045e1b18001c0c1400c0155100005907484411080b40c24070115844480500d0184541060104d02c24070052601800d4854854298400c8030048e200300840303000a1510b81 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 823126582 1250 823125332 823125337
    0x1517120f1b01020a020106140102161503020c010f0f20160f140d090603060f0e040302010e070801141302091906091805150417030703060b07080c0622020103020f 71
    0x4801000940d00c813940032900a00070b01880c41840c48040c200401c401c81c41d40017040c1c91406842010f00501c2c01800c02541d4241e407900500000c00b016420000114181800c1c0b1072080c10107002400800c030040c400d990507040c1e8861420550303580c0d21441c50061340b80c041c4412552900c0b480084034040700ea15040050314509085c10190861000c0294041c5048001c40d100d001003881c2d488141d00142c40740c2e0120200d030300c6401045210300102e175003440070700d8030181802d5016100e1720000c1034401c00c03059000d040c920313079900145c0746a44800200b080d00d0030040e4950fa02c2401901220003002064001644011000d413a90801c00190003203940042c99076080030b0060700343c0480902400490030390700c030b181407961107003036919000703070b030008041300b003252000c240516000032100b034030b074403420484c50540d03403000d42024141a81d81500080c2c903d842e4015101040c09500c1c081c2d120f0610000d650300b0035000821003c9100c01c40380d980b800240c0783d40b0104003425020710b80103817910940d0300c100b40c80c0d2 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 823127832 1250 823126582 823126627
    0x80d120b010c060c120501140604050103091b0e010e090309220906051f0801050c070818090103060203070f0e060a0c26071703060616151517120f 64
    0x60306004901c0c40c000c1d00b04002054944125000308281ea83e03680723548050404059045922140402040100b503100f0f80000d034540303004180e211480c0d5605814480000c43d15804008003240c0e400040203409803500f210b55200320644003461801d480704001480e049010310104038402d82d0391003d0481072000354012226951b2021042041d41011070355140080100ca443d0810084d8880c0003041c8014180140b50041c1148a88141002d52555030512560455000300440407000780406026680d560603450007140207090041e070342c0c204400000c03c85802480300d00244005915100d00a40701d41d8111074010050b480c00e603241117407a2400414100b42c0d120718840002d180002228250b00c20401482003e101b04c241c04510ba0500740a10120701040b220030754000418000520016220105020201d1044460b004060045181035081b5024410703280c0001e44a00001d01c891582c080480461207040f0b4014030118080c032200c04400d100d0100002078204000c1021a0801003d52046115 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 823129082 1250 823127832 823127843
    0x9060c050319080a0b012a05120f090117070e01050c0f0f070e01050a0609033e0405060109030228030c06120c03020403020906040c050c0115050307080d120b010c 71
    0x8000301d88070042880ea01580c0154160f0701d884c2917108158014520348000c400c10305c0b81c20f103541d100340700280340040c4402c00a44072801410202c006810151009181c0148034551140e140c25032500010a03501d564240c0d4640351a0340018480fa05d030308040343e919465024601640d844051003000741c00c00502c2105000705108000b10b98005090200c1c06109480014a0720132030f50381c0c1c1d0010005000210311903100480c504100c10b00100e45ca5604100d8100544203444801c0001311035a444024840c000e00d8188004450314000f8500d80ba001d62070304481e003443c14103013403400c50300000c4200a80082d0300326600303502c1e040450900f00030f9000030003c507045044207003442d0741d481016003031181008203180481c3c80c080040725941d00a200b42c4065a4000d8007110690341c2d803009100044c200b44200c5414400b050045203080c140034014075815150302c900d150301183c544130915141070b885410010050300410103100300a580620282d48400101e103000c51013880c800b005940c0042c0100b0090103 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 823130332 1250 823129082 823129117
    0x50406061b0213180b0c04050913081e120709050f0d140f1014130602090a03020402030a02071a090312040c0f0f0510030c051c0b060a0801170d09060c0503 68
    0x240d400f40d01c0340807030605c1c01600e0710078866841d41c5604007144141e00031190303c500c01030701044c04114680c9000007000d124040c031a01e400141900c11ba484881c03002d50803000c400000741950b440e0300d0f01c5521368000c00c25013000c407450340c1010000303080541d480740818002c815030f008072000d03c6002e1260030850907040007503d640e4800301d4845602e901030015011156410809403900a1301e09202041c858070101038070720081c40d0300355102070103548803c0d88250b1008c540a000b102590703840c4025030181d1070000c001030f81d030505c40c0b4100e0301c50810b600104200d20442c0e0100070203414044100c1315030355000118070301d032640c071850200c2c1d03481001c1d04000c0e03c0c0b402000b00402c81070030410940381583d008551b1a010114541070881c1910b200004500c0000d00502403018401d1f0800781c1c586400a0110020621000103004113049030003045000b80040d2880d001004044070b0400d00285802c9024054400d20404e420040e00f00e490610449003080300b80003085003441001d000765003c81d80c0c1c0089012 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 823131582 1250 823130332 823130351
    0x1206090c0806030d0206040b190b12010204081002030c0301170307150b1507031409010903140a030e06070b0c1812060403140a080a0e19150501050406061b0213 70
    0x1c01d0302100b01c0d240d034028855003020301c000d640005000c5101c0d5034080f0703000400390382e400c6100a146c0105408401e5a546940700001141d40350f107440ca001d2800b2900050f191751401441c02c3c501150102017141e17051040044c0410542400200ca064a12105072110f80c020781c0f030b101c04e2a42c41604d00c0a82810701d9140c02c54610b8015410a0040c0031080b144207108030950041d250103807040309401001700794207020000c150542600940242d043c1410700241c055581d86503c9000403c4c0300f0445215041f034045001010340000c8080003440c41980c800e400c2c01520f40d18a02200f80283c0100c81c1c9903004a100702059012115070412403c01412070b404440c0001c1040d9039034081a1001c070042110001c9802810306050180c4114414682d550f8070151901102000203281e000e9420005010740d0107034000c405181a41c2c00401481025480407003800b0351fa22104031101a00846e1089003005000c001d955030204040c04504a6400b40100441d01880014551100e950b07158105500709020078 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 823132832 1250 823131582 823131587
    0x10c020a0e04201e010311070804080d08070909021e1206130c12090809061b0d0203070b0a0c170a020703021e07122402040303020c0d030503071206090c 67
    0xb40107a100b07903001001111200030f008924055030b24059004100401d032484100303208588100d4030708060400045c00c00c2c8440e6402c055520594050b81c00f104006001c01c408a0308000d000041911885c21100c0b5003040080107040c85581d20a00c0c851540204840d4102226140000001004134075010740d200340c0d5581252001d07204844a0307205011004001030702103014003400304144c80701c0e03aa09402001101d420001811000015600b1080034484828151149401000408100b01445c00300b054400404c0e03140141320001c00d011900b0910072600055107259641c0d4001954420109805007890400c6a01009244140c0c00811502c418040b1010b1607030300502545020b5803d5444c80d41c4141d45040120813004100b100590140c0e85c1001070308018090300411522508481c0b24254002c5403401141c40c241c0d49241070076031700140400805404010001030404142c0e00384225002c6e13518050b210340401480b45007445101c09410b40c20498a502c45070180090807410040c0d0200074100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 823134082 1250 823132832 823132859
    0x31803070309090c090302220f0e010b09100b190c02101d0619080603030d020315090106030905100e12030112113307050a0308160f0e0f010c020a 64
    0x181003d41d480c3c41c000c0040c8511402c614002d07640c025101c045124400091181da100f8091245441e142d503450100450203858041c4820403100c1000210b04458246d0400055980c0500352803031443c060340003080346100b04410340e0343c8100401e0f00050b054400c00010f84598024040c0203512045021502d03c405400444580c8800e20341401c40546000304014480c040c401e003101112424070203021610345c05d00c50340c2c5051b404200038090b42d0400a4859015041c8e0700240c07007040c081406044490039504007030031203078010000e900c0d0034451010b658680546034600120507034901901c0b0118040004000c00080c051a00800b80301541c1e90303540d490301407003c03942000c00c5a00d09901c52600d91245001c81504034507100000f601d41a00403005154041e22802c4076009074400320a0080d40003007081804003400780c501945a514240c90490004600d00340401d902e60140420040c04a40e0154007220910f19500e06880c8001c0340010400140d82c0b49144d6500203500c00418200450110503c1d043e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 823135332 1250 823134082 823134089
    0x201050f0a06081203090a0b01150e0d0b130309050a061119031d010c02041a03060709080a02010c0203150106050c070b03072a0501050c070c0f0506040506031803070309 74
    0xc0d441400e072120032601099540c80d210320b034000d03840030711a41100780780a0000c50b0400c030200d0031994980302c0c603507801341114826481044810b45c01200840e0136900300c5c0c0b207a101241c0c100c0ea4140788650340e40d078604c41240d02420302d40e0072001c540b01c104109400340c80800054034000b000c120740c29680b940e0090500b6001a10f100e0316000c0c5140680128510507003c041da0b96060300d07030013440a00b50110702c0b02c41a02c1506503041146602189015855034400c501e070f200c0c1d506020070410840802031510300a00540700e001080740001e02001402e00219a4141c41642441e100d100000340b0300000b40390004e4000d600c11100101000010525004801062580b00070b03010742c3c209543d5500c21a8072030008444400200d91501c0d03101070004001074150246580342400640c401111b80c0710582115401c0751660350f12180010b0754014460301c03104401c0280241000a401c1608040119100d070049100c1e280c0510004004100c04800fa215100c0b17030400010101d81d2100320074100180244503e22 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 823136582 1250 823135332 823135351
    0x903030605100207030305030c1306050901020607230a0210060f050a06090609051c0c0b03060f060301050d060504021c0f060e06070f200a06050402120f0a30020105 72
    0x100c0c00109820403500c8000a03004980241070700f035140d52019242c6a00c010040203000004005264034135591150800251009685841d1135001c50400a40b41c80005008001481002e03100c28038006170141207420700122003894907484180e2070009910b0700c48168400c0e071400d0b04100000c1003c603804407070f140844e401294803400140d40c0c2d48040c0d510040e42d00400b00084c29212050103582410300d00a03050000007151401005440c2d140c1d029080d4041d04280f8500100005021b00f603d45034a01000740c0c50300312206450f551400d40094111082c13648001c1103292100e000074250340d0360a6518468108907043c0001e440034520b01041c2e13013500075000315405860000480c1242d880026014070400182c2c580102503054180107540c02410070b942c002c3c101241d074a190f07020603004c0c03002d840700364400c00000c9040d00342881003008001000c2a044665030140d040d08190b6240010741e1001c880d00030304610100320500583c04103d040031a20041c000600144916074954154403191140d01943c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 823137832 1250 823136582 823136591
    0x30206040801022a280204020a0810080d0804020d02010504030803092107050c1908010e010f0e0f030414060f0c030310060914210a0503180402040609090c0201140a090303 75
    0x401131148020807031443c03001c2d54440d02050800000030242c815085200049401c80a00743d41d0000e8241c0e802903400300700180040e01444020703420103c01a01401500014280f0306c68880b0b001004150f0041c000303440f0f90490385102080da4062000c44001c0c54010100d942e6910340a0354050381d981c80310040d00d09240302440c0c00345a41c05640160348055078001c000e00340080b46c4008020314450300140c50340f140c0340070b07543c00039802000f4400d144061000708004180d540711120000c003254000d9420b0555030300301403c084040c11010080ba0103076440c105103403401c26072404c00300c0e0081c020f4220b00451100005808081038200101031807048c804000341e10f4119840302400c0ba4803000314860f0300110440d01c1c078109038030f14000c0340c840402c1e42c0c4404000880d1107084c1423546440c03102d2006407140d03000000c0d442c1c50222000010460040242c0e401c0d4a0185850002425090b40380710f0800e80c81d5552028125940c407e4000304103012078500780c0805803c042001c00c2c01401d00d40d00803000300303241 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 823139082 1250 823137832 823137877
    0x708151512070e0c040b04271d06090a0b16020a08070c0512070b1b0c03190c09110a0c0503071b050a0603052e12030c030e01020102031003080d0603020604080102 71
    0x800c0320b05035503220001ba414136140030240a14a400303150070700344401454481c00981e035001d1007071890149041c440034103061a001516030424101510700156078000c0507109000c110f101294940240c0f450071055140f9074601c03012402e000441c031005244000001e040828055280110810343d002100e94200060102e00060381d03c12140c030a682020405100c03005c03000c14850a4054040244416a4905200c100010f07046c00c03251090b0542044c03400f85064184070050380e00801600c1500020000003148a02005140c041e40c581d40c1c003046007600c0c03880308100d800e2042c0c0343c00316444000044101c0c0800c0350803000d0045406280e0107070300c50107000944103220b401070500451881400145126140e5a801e00d04041c8039248441004802c1c0d00084241c1c01d55540041c00340665120003801a640ca002001c4c0e480c81c0c20643d045a0051050100080301d2031041412030340d1056941c2c3c0d03106441103842020300311a03071010b0f500403070210780010660410340082540318071906090040462 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 823140332 1250 823139082 823139101
    0xa30080d0603150b04140c0a050c071d0c0a021b130f06171204090b030c120105060f0a030b060409030e040e0f070e070507062a030f0c020708151512070e 67
    0x111000d00b0042c800c1b004042510008514000c01503141c032854030341e180480c21141c1d9454484507500c01d5001e0000c08008d501d40000c5132500301d03000039003c80407030325103145003900030f503245400904208100882c5005600d1640c60300c005032010768454200f03105162f00741407800d00902c2c4512404503820719240e000100d04202083d070440d0311a59154445c1410300b8a11b2440c000e200100b09142c15205000301c1c2c64182c1c0d10404d1040c030041c40100085110700c1e120060010031420a189680a104031aa05100041d6080034040e44040152400a940802030404440142e00a0030494101c0d141004483c00100302061011070040e202049030040c03683e40e400d9462580307007201c880c8002502484098009201a00b04c400803d0b1801e200a41806141d480e16401001e85408000401c0d5981901000103005024540000c0d68900103081414541805540c4650141540c90b0035580403c000800703102c002e03504039484030780151207403200800010420755110098010130740b04840500000fa41c028 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 823141582 1250 823140332 823140341
    0x140405010b120d051c06172b090605280c1b06050f131802030a1a03030d150305030d051008070f060f020a0f110a30080d0603150b04 58
    0x500396a5a00d141c28840c800e15801c18040481600e03e6544420b800036200b6040c1714001f0117004200043d1035040e0654055940201c0f0104107039010140408004a0440d009144582100c101d03003403082d5916010944d6824880c1401c111411000705007840802560340805641c901d03078400e110003244442d80c0000541c050215100c1c0c0e40018070100700c0609000700d90320250407141303085900301c8101d80d2106000c1c4e052001c3d002001c0100d40d03000c41004101c2005000340b4050404002c24818090600e90119840344034581f040d02542d9204c0780d0007000305031140403e00045801206481d03d801c001526503001d00010f650708070700c41c0340400c0d010910540c0403030b80030704035001c2c1e00d02d060040385085070507035440c5503140f00401580a400b03403013000729070402c00f41080b45100312042d014080464080044d032038056041260320b4400d08480d040d04c2c80d07002031011b14051003111800504819403034001c2240c4907113a0104003042c00d1060010070080c60b005500003034040c1c030509001c5c04d5055424441102c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 823142832 1250 823141582 823141603
    0xc0c1e0d021b19080f010507141222020901030f060506010908030901082203090501080a11070f080714070806060f060d0506030102040b04080715110a030f03140405010b12 75
    0x5088080061000745000d50240700384401c030640c0076003401d6131843c215040000a0342c0c2d00aa9035141d10400030820f130702000d680d090103603100e41c8508000c140900c4e04540c2c140181140c03c1c0c8009000036a00d440c200000058031076500800d905a25a1603182c41c90013100500002c51310381c0c0c20240800d85560080400e08255001c100045040c0720300b01004551025000c0c2c904180750b5144040b180c14480c1c41003654480c24040c1d210001c5582c5080001498103400a00a1700181c0c94940500c034150a00390032110b20030340103031020b0840302060402010034401c0c154024140b4034050111509180c001c0348400848041c507003947c07201c1c0e42d25010321400c42d110407403090b0f102c1401c00001394400d06c903601058125801800042c01d0640700d101101d01ca900a800c00c101941c40740104001d05035050501206c40e524600c1d00c250302010304401140d4882c4c64450040030300c003070b45c111984020700c2a8440100065a41440011814182405402450845d0441c0d008101ca041c0d1030f02d5840300014401d000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 823144082 1250 823142832 823142863
    0x9040e010902090a0b06250209150d030c021203030106091701050705031305012d0605040b10050a0e0d0b040204050f0907060c0314040801141506040e0c0c1e0d02 71
    0x180c0e50383e0051384005000c4403091036404642032100e05414002a900c00900d15a600031038084010140100000250b0050054050b00300200041c410b81c3c60304013481d0211541403c00312131440241c400a40702c18040c41e034040c140d21012000068641e4044504000c44110001002c0e040013181040d03030a8980881d00030700070034001c101041102c09101042003459005000008482e00c0e10b0b1100d01055007658250643c2c00e002c003024881000e0248505002801e00720f1f0100b08000852021800702292006400d051003000704458400d1401855900221038000702940070840f040d140020b0800c5082d41c090340664903200c00a00690340b8801918002c0405c10018112549042c104940c9000402011800c0204800f0840b42080c10003000d0130142651100200307485042c020003d1b00c5070402030450028089400c11560140c840604a0f000d440e03003c0503007403550340c0342c005100c030601c5440340902103481802035100840c0340508544604002d25402c1e5085800c0c1c500080b80c3e0754113905815081c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 823145332 1250 823144082 823144099
    0x20d052d01030c0e0a1e0b1e0f06031b0d06090b0108040b0c0c010e011a0f0303040b070308060a0b0d090b0a11040506070501090b070f0806091e0c0d0e010209040e010902 74
    0x1085440a401517403003443c8140c0401d41910740040c045002044400c19040c0507161811000549400500080d0072440c0d81d1002c0c41c402e0305a030015074050080c0c16503074014003000000c40c040070104546508240f0b8025607103070780d401514003070030006d04062284c1d282d10751500c038035100d00b0361007500700300c2c042c03600005445840e0b00c030103800c8d115584c4440c140c0390040d90f03910150010007a0030301581004491105254180c1d00014080c810113000307110a06110f0782041005001641152007900c80440d01894042160351f10000410100c4500f41c129400e081008140040c1303031292070b000315100f11300c941d586500584501c010f010030740700c3d00c10040801c082d007800b0500090825602800e8071901503c000305024141c1e03103070074203090803d0716940c0001d000c40d422101800d030031101d010f420010548001c80c4602d00152880d90103482d80910b0382e0341d4400c00c0b01041ea4070106005591420000910400c0b8490781e08007e0782c000d50111040314001c0741081040b60030004103102d1030101c1e82c0c000d4242c20 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 823146582 1250 823145332 823145339
    0x50708060103111909031b03031d0f0d08031807150305041b03050d032a1110021306020f0c09070c03030f0204330f050702010201020d052d01030c 64
    0x18050310b0481601e00812005101401400b00c144d034081401140b00d0b01e1324162113086080014211f080c0300b4406240d002205c00c00c00c00a607000413080c14010b20801c1443d84101c0c0302c0d002800710345042481c140d104c0c28000408007070244050046000d07280a0000d04120b8400280c0182c44403014410068401500f054500c8001c2c0a50001781e480b910904014000ba81050300c041d028642582040d200c55029a1389020002d0301481410712510070070312448400300120b000002c0e01017509003940d08000d50340803802483d0070100b107560141e1943e840c040d0b46940000c1c22500c0ca4030003034403940c0014410b2a000300703081c0402180d03181da0f14802511820043d50344460940d103200b010321044003015a903655042000340113101620240c040d1100c03030500f200c04131a43c01c01041105c0034480f10488580e42d054640e0790020440034940031715080c2240c4400440c00140e00900421240210301401e0208200b8401c2c0c0b44041304880c00d142d90300008038205110800c07603d06409000041c06100c00707000a1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 823147832 1250 823146582 823146587
    0x6030507091104080d03020a08130b31060f11120106031104080712062d18020a03140f0a050c040f0609090b070e0d0f02090c090d0302150a0507080601 66
    0x303140c0b101e1015506403400344c0d900c2d1498646800c24a900d000641c1c08140710f014203070310000d01500a4000c2e5888400703103155440d4034000140142108a50b01c400e003580100b0001e441ea00861005420b030b442d00c2800d680b90070140094402c0744041035103903240072400c42c1c80c42c07036140c1070358041c9498070f4001c0d25603820550203034003c055900320012290700c240800a00d40004000b54805003803012801000c0c0f03c0d640c81c1180558081c0f450301c0c0340700d08403041c070406c1c002401c030b00c120864800f124007c11424035020413041c958000850180d00986052400f0041c001c3c80e4009001a0f01d4600032204007814820815849501810004002d43c102c448402028941600807012100c0c41d0440002d1803a50350f505082112000041102c60700199000c019a0710f80040c0b069554500076140100080c010741d6405400780000e9100030b00c07401001000c81c0d075140b110030036101c4214010b42502ea03d40200d09000c0d5840c3d8643c010034224140d038a0000310020b9440c09111300400490304c03011705644458005 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 823149082 1250 823147832 823147841
    0x10110a020d0302070506030106020102041d0103080a0806130207110f0609131e0f1b03060b16080d020304150b01020307170a12060933050d0f0515070f030603050709 72
    0x141c045111300e1401203099581d4200541c000d00f10360300011303500c500c9c0500554503608400d040d4004c080101004001180c0c03804120b81c0710280e5032802c01030b82d560364400075102d11900703e40c8000b000c0c408142c000400200c0f04003100c845604031100750500f1850420000b00c4c0c418034901c40d4205d10200084503035400f054200a02119200c2020100e000e460300a40301110b003110805289581c403001c82e880100d041021040300c0041e03502c0c050101504118801420b03207d15211400030103140300804040c8003500c41503480c01c0100500941d624205802d103100070401d5002d1401240d85082c01056540d0b00000c206c810b400d03444256960311401101d02512140c104041000c2072150b2401409225407080c480d001c0580019071000030121404400c1c00b80103882400740283d40e21140c00c4c89820641000d41e03034400c5840854141390482150302d0b00c0c402c1c0002e0300c9c03001005803040c261106212440c0900c6070303116407151f03640c0b40c8000320103002c21010358481c1c0c4070107805034002e80c02c14440034010303400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 823150332 1250 823149082 823149109
    0x3081e180c2b08070213021b0d0f0f03090c06030b090a0207050d0c030c060510061101050f1f030611030714070309060e04020c1e06010f081c03111810110a02 69
    0x8000d4104845a000306c2c2c1c140056400080c042680090344c00c4c200400d00d400300d60301340e48080c003c164910800d400900001d44280c840411b201201c005070612034420740181752401d900403131901c0c2e103540c0ea4001030041d00c881c00c1c80d941b040402c800011840c16040c03007696880398210307008013421640a8016524031407a41d00c141c040090101e20100410081d0042601404200780600c090700e2074400009d000700c000035407103801c41e41002c041c0114401d1840010783c00050007003c001180c03031400d03032100915125501c010806410000040c4141020201552050301d403612000c0403001c512001c0342d480d00c1101070050100b214500305021841c811401c613a035400012304018903216100c4071444c6801641d402c00b403180c040d02210011121428420a4010240091080351040c2062074080d08d800c6035009880c0b524010307103202105a44250010685e412901d4121680c0710302c2c2c00b003480c03000a260413280e40070341d4255000407c3d1520411203036410b0710010002e8102641e0342c0e401c100702e80c0c500d01d4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 823151582 1250 823150332 823150343
    0x12010e040f03030f0b271302010e100516080a031808030a0b0a0f03050f010e0d210212130c0b0a0507020105030604020403050114070e0a030c0303081e180c2b 69
    0x1044011b4544000100040c0b02090000c883d0225600400350300100081000403c0300048000d00e0050340c1001000300d15000407510101c20842d4000c0454090184005400364003492041040034095420000e20301c0b600d03950b6042c08042c20380c1c41000134180420400a1511400300300043e40200c0741e074006664684010040301803641c1d921980c0c844800380c0c1d04196020b8200c982e00d02c2c8404000d21032541c0514003103015002d01007120b0000340030300a0441020700c0c0354444400c01700c4408282e50468601c007211186008480c1014217851003040800712048811290203200480c45800304802d90b61030042998a00d40303403a40c107070300450f003c0c6c00140586030016000d110100c0040e6003030066081c8524130f440d10040c545003104004100c1010100210700400d2440f4003440800c803010100001c2d00e805060103a4503498800050b001c411036030802c4a6168a50014004015103207240c452410110004031015404607008111038524080511041020320442c42619445840e6414042030b0149 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 823152832 1250 823151582 823151591
    0x6051003020307140f1c080a26072706051c0c020d18140d03050d0e0d030e0102090a05040e071a07020a0920090a0314010212010e040f03030f 62
    0x240d0202e46801400c0d00018101541103401c1d00440c1480150403c0b4400100e40c0e441000c1c0c0e8845d82c806180b080c1c0d28025103448070014120107424007070891400c04031001d40e04848840300074100360f0096402681d03540001034107042c145007035542550180340940884854450b540b490040240c455502070032501c40c030b80d40101c9040c9284030701c40c4211070001c0103980242c030313100101210040510303031904041d03801002a034206004c92480c4040301e02941c0815500303040050210f040585190249041d8120f54a0030600507000e010008220b4100e8922552003d1080510304200c8a00340c0c01000e4403240c00c00f9000d201007203280f500ba044010f15030798001c16100314584a4103404080e100700c22220403c8200015400c1c110b00b803e01800008245151040009400c141c00d5200d2001016031241c02c80d1101180185a580e11001482c0040d81c0c08542455420300034424103000c1c0d0004203a0700c0451401000000c1c05400b8165040d225945c08070340151500c1040d0703000d03401000f1024000c10f400345d94 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 823154082 1250 823152832 823152839
    0x305010b0921190803010503010b01052106120105130b091902091b0a05040515030c090f060c011e2d020315040507020a12050a0903060b060712050c0706021603060510 73
    0x82c003444416130055404580d298100320a0500750345403000c28a0410404100e0400d031540640b0050185100c4c001c09410a901e82c8000a28604a0309401001a510704000c1c401511000d140c2c0c10f01840c070644a10b0a2556403000c0749072a00c0041c43c80002440180e00507000516010301000c0d409191030107040c49821f414154040d15401150038080800d600180622551401120600b0303c90b1180c404d9900c3c6203081001050680600702030140260303403c0b40c40180d0b9a076480140e8221642c40c4000300403410b0416010402403100301c480036890392410381c81d0007000040172201a92009802000d02c491704070140384400952000700904042c10342c82d101503c1d1a6100e0103443c3c0511a40d1f4010000000c1c9400d10000a00094520300f040c40420030250035040e411500c041d0440340c00800c0000e42c1190140481c506104031000100190401c502000310141c00c0f0001c2d00c4002007001c01c170303604151a030b0b50a83e9101c003000d0140842400000301007001800b135070040395101058024454100e075a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 823155332 1250 823154082 823154113
    0x20313081e12040b01290c0c0402210a0b010503010509090c1008060102010e15130503120414070801180b04050c100f02190c031101210506010305010b0921 68
    0x10034035541c1d5044500302c06200034044d01c40c1d01107026040998030440c0341d00500405140c0003005005080c8140804691080314010502c061400060060019591100c01411590060b80560518144420000046100d506280c8110b1a840006855503851a400d00040018610300100010164401c03002c694855440b80366030032448910580b9000d00d41d0602e80e002909680b90808107072855880a52110756480381291441d40120303440c2400701100880d8208a8198030a100c508000303035940700c043c4010445202e0300d10600d003022106980c0c1c010b441c0c4004c2c0c2e0a039090300c2c60807039131640c1d801204004074060120f16600280702e20201d8201801d1103000ca101040d0a503030002c003040c6070ba4120010740fa0141b060000003a0b000d009040d4020b07181d65040d0a503550380c040034001541142c050415a4000c6103550305d00c00380c00e601c400340301000103801c101510003100d40b44d002900302800050b1359600c0c0d80a80f400180000c01c0c0d0800ea1420150344003803940400d580080c02c0c45000d20b014005071 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 823156582 1250 823155332 823155337
    0x203180115030b06010c03020c0f04091b0f0e0106230412060b01020f1912020f030711040f021204060c09120f1e023f0d03050109020313081e 62
    0x14040c10048125a20710704150524803c0140030324113002402c10f4803000660701080805a00d082115401130124900c4089801800c200070018441c09040c450020002c0e81e0003462001c81700000360440f40c0b0b0b91200526a10200b00380b00303180105561104411603a1410740d521441d1082c0300c05a1820240e560071043c190812400054507110350b10103582c4981d5a050200f1000f41c4016001000040b00c1c0320000e2920403014000606000118420a81218800d20070203080705030b1401201c0d1540ca00e410003c83c02001d00e00081e1141c2e00d802d04440003604c842c000d9424907084103075641c1490740c1d81d4a031030014043c2002e100d4104101190082901011010514450b50040740c421403802000d160100700e22168250070fa12001006501200680d580000e181c82601081020fa10801c900b10140c090304c50341e00500f41d0310741a4905240f070f64078000600210080071582d070030f0062340d83c1c40500e602244415107007244442c20301e606000100b1020780080000c40040600c040c503050f15041c3c14076558 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 823157832 1250 823156582 823156601
    0x12031303030b1f08011a07031103090901031a100f05060c0c030712060b0906060a11070b161101080106020c010c0201020a020d0f1a13140a020411030a11090901030602031801 76
    0x503004548550f0059804004680945074010051214000c00c045a5240d401401d50041c1000500406050164014000e88003c4003000d0030809465071079180c0507801448081e5100d5003071040d01b000840c0141d100f0908401c40e00015040c0c02c5440c14001807207020350111907881680d00c00c68075040702075101013042400800e045c0341340d00d51111142c9003e80c141c6030003414140c0f16415480612045569110460700e000c0c05034206040c500c1c00e01d43c622810420994000a800d40020a09201d4403200203d130307001c06485400d5000141d910100195902c940a00412005a208011084440d40510309610505005004070790b0b00701d01c280d00080b00442c0011702140c1d00c0e0000f4003c0d0302086103c620011003041282c40031081d5182a03001e1400222000f013002d04094814520442103a2007804500500307500603000f840034109804c2c0c64080341c1d0054030540c1c145840d043c0ea00c0c0d40d0412100aa42d40c0754070041c5801c10a03461619980c0294001a1483c8101c070b04120551810720024403501050 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 823159082 1250 823157832 823157869
    0xe01050f1215030d021b04150e160e100e060f0405040e03070b1e2701020304030c0311120d0f021902011e020f0304030309050c060d0e0c0312031303030b 67
    0x1500c07042c0d0149420281d10f00e860400b90f6001c090600c0322801031126005c00040c040d1800103115000d9090448030200c903501000f00d40b4402d0080c0216403091f6901e036003801a05031251070749845a001884001c40880780082c0001c2c0071564002e0483c40c010340201404291454260304041d00c034400101124080000325805500c0041d58000304007504100c0303940045401c02860a60241c0103547d4000f140c0240a1510010a21f4514411080b070344501103009891500840d12417505207409003082e410f07600d05801180e103103882030700b11010001c2c0044500c10826020343c18202c5d240d06840160454150300f2111680910006118594001c50098222101d60000c550040740c00481c0328203005032200c000300c49004101c032116401007036080303e8006900d0b26000a4034040c40c18001c9c103005c1d0b11141103038050400201501c6107040764021104012502d02516003545030281096a40d03c40b91703050011405c014400509003d10104103180ba0ba4002e00f004140139031088006041c000c00e64028920 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 823160332 1250 823159082 823159111
    0x100e0a0f0f230903130312090b04090e060906060d081b060f0f010f050607030f020705120c040e0604052a0933031c0e10030e0d0509010e01050f12 64
    0x182c450040d1074840e0411040d0015525040c4626250384140c5c006000280ca41c000f41044903060910a1440c031000b003000c84540340d00c0e561500c3e0b2502c0907100c00e42030301b0680e20441003ca49060804140c85018041c01040000131085076a91540c06401c44417100d086c1e000c5a056243d85460248050b82c82416240013048092925400200000e801038001040280040e24240540c3c0c8642080702c180581604007017085070040c3c00124500201c07074008a4220b6000c0500c090028000a122801113504480c280302120b6602000795a4030b40441d03000d8140d90003004100010f0300d5a1040c441203602d40400000b03084851400f0440f089825510040100840b1249a054100c40010807104810a0b0030b0740c40a80714034400aa031b5800e2807007030f40c44203c0c4c9128000c003c85000791420b038004640a004c0d00460041000082d00420759102d42810f035010300c0400c0c004551066040701e0110205840d070050080c03014004484581200105280143e420092480780d0030404141ca0b10604100c1070111 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 823161582 1250 823160332 823160381
    0x1b02010b010f020f0c090405031c1b0c020a0302041509020c0604120503040302150711070305010507020c0604030f0b0c0f1303020112021c0c0905130c08100e0a0f0f 72
    0x10140d039000d080d0b00085420030182a03240f07500c007007001400e805045070072401d25221410028254400d121408402240100a05800390440e030400c598103810a04481c003a03002100c02078070700001c0460029840390304a40113000503e040c0d40400e145c4001316074aa0700d180d44480c2c0d41000c90b4040c18169046501400402c0700b0060003c482c078415660310302c0c00c2821400e00d1350b0060341d114054002c80e03c00d5a035800c00030b0500c03881360034034950060444003291811943d9003003407802000b05031003490040c041d28205030041e040c2402107504903a400325503240d840e201a11810010440509481c3c090382e020401c0396226551003010b461004800c1d00b040b07d1407880e40c030014080200e001a115034160050041416071200345910a0080f40000c0006c5058030b0b0b6540e0890ba81205508010350080c6000341c0280b040c0369650055940d044241c1750440d590322401c66643d00f500c2c0600c980d101e100406800241c80300302039000820700051001c5c1c003103800007401645409035000c4648e400c00e031622104142 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 823162832 1250 823161582 823161587
    0x821060a060e220e0d050c060a020702030d05030438010602010e0703020420030106050a12060e011203200d142802070e10080d02010623041b02010b01 66
    0xd40091401d07062568941039280089000b140c0d607010a4800d2035550506401100481c1d04039819495001090b00d80f1020352480c080e000c0d81142807601d12510401002031502001071003100c80c601d030000e0003000480482c220803074095000031320490340019030b0380c04511700c202300f560404c03d00c2c504044080d00440450030300d00c1d61401d050b480038007168103107100b0000b21000030855000350380d01514003154240c81d051400c492042c1e080d050303050a02001000003000355020015007181010f50781e8000c8800803111451050303682a00030403007108540700040240c083c0100d4102e05103032103800c160b114401c248101001c00810b041000313150350441c1c00102050390713020721102c0c1c101c8a00003040b0300382001c50700348085228500f00c08000d81d03007480d000814028004c01400b0020b0070f845020400916100c0fa076440210890b1141d6406071041d1458500c583d80180199401c1d212007084092000c0511400c4200e0120180da41c81d8006995400d900d200c000c0154421203446519000410380401c0e10000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 823164082 1250 823162832 823162849
    0x40515090d201912050c0d08030f1503120c100608010510050a0311010c031407030c0210030509061501030e010e03030f0c071205091206150a2907082106 67
    0x41c500c1503030515554841c440c80211240283c0313aa5107620503c44040b440c3c9107203800c10340802d03254030000c00d000141c00c12400c04020341c8180d01001d9644e1668443c11401004800c00c2007485616400c284031180540301040040d11210b0114000c80d00c0b00340300a101038080398241d070801c046c1c03a5124070820070280705040414008010596031481014650380398440b0740003101c4605030422031501052410705206a85110710690b12512903075850a140c523000e040c108481e00100c0c00f0750090340301141418002d102d01480b4512610290003a41d6901001d1942040258400c6050580d91007108540403024422140e0140e0b200d80210380c1c900301141600030500c00100005c002d081c04124000c0004d86400c5400001481070801e41c1d1200714500c000f0700c03565031040581e60540305200030041145440c554540d2102000c1e18650700c042c1c3c035142108580700d541c140c6d80070501101d000d054250381c4000c00800703045000b071601c4e80c117001c450301c1149082c100c441c0381d524110801100303001640c0b034140d11 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 823165332 1250 823164082 823164143
    0x71703190e09041b0533041e08010515090a0504082101080601051914040605060a02010207031d180a09060e060a060b0702090c070c09020a1206090908040515090d 71
    0x944980100006400e50040a400d044031b14031a01080400c0c41c0402541e8140c4001e4100c044080c5c0540760351148440001d4030381e02c02d11000d5030070500850700d200382c80d050030190b014000d40010310035503a00c41c5000c09000042c3c07080344c00c04410040034906805003200060301d10740e01d2005002552502002a01d0550180c01035803243c903407680d0318a0070039000c0c8048000c45015514840c2000840800100244110b80c0320a8208400003890303880321758103500414007588280c84070a00d4000c003202402e400d000c2c0215983d00a00c6c250105081080c8a0207550b500010321000450b4100c400e51300c140c196413007203854a0b00c1d035000b0010b01c00c414515008520160051110080c103020300da40010386804406024860002c5c00082c0d42d0b13043c0161101c410015040302c410030742d134484d0f030404010090129425807404440c0f80013400300e400f801c07030b004042209420907181c500341410f0004028010b58502004403040d0300411109540e070325000315480d0401c0c000c0c0c050303444040e140100000c0b06200c580c0f = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 823166582 1250 823165332 823165339
    0x303210f0105010921050706030f0c03060503071a0f0c0d11032a03071a06040b03120a0f17010e010f06021911030a0b100503071703190e09041b05 64
    0x10300943e60310000d00300032142c5098810048000712000c0c2010000344c244050414090b4540224a1070f13015009188550300d4410200486182d42204a048803041d0159a6041c0c200f0b60082041581048200d1a481702805403685451000c850f058015400f48070303140f149800903c0344400ca15080000420200102c1000c0c0d440d00c5107944190969a00c007041d9403000f0300c00740201d101000c0c1d0070010b0343c0c0456801003a14014003810010010549030840b4240c0c412810004c0a105506000c10740c4c10103100e1154429080c54040d007426034020301804445020030150101192904506140540c020480c0000704086541848420440c00c400c58000d00d00b59445903079402e04c0302000c0c0c824007980d550403419a428004003600001e0800c294845d001d4800012141032000d060b4482c02108210340b000c404071082c095840c0800001e80d0b0100b10720000340d820910243c060022041d1140d03185001d14500540e00f0403100d00010708072002907070142c541001f2440d80c0d2091680e246861009842c01300c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 823167832 1250 823166582 823166611
    0x30b090408041211040509060f1303050906090f060403080307030c030b1f120e07080706020d0c03030902030114010b1c0e0706030f02041205160e0402150304020a05030321 75
    0xd40340d10a07948194400d8103006160200140280100030264032000c6400800c00c0c0306c982000761040381e07240d500741d4103103021134214000700e20078050004020322920380c1034a03030034246100c2a04000840d001006000d80012291580088598030240207001543c0b040360455100d040a0701c0042c112003106628206043c50940080101ea0320503455008040303003144926148282c041003181c0c00ca0340c4040c840c40c010f0826009241120001c0f8006068801d14811030761681c3e80c44104a0352600e4004228000c2080c900200020912030307008540b1480c000f400201e40200d500c2070350344498000340e00c4002402404560160303d0703021241030b400c07550264007090103208061401162074000343e00c551014955a014020800ca040e074054070010481020301c040d80080354100307d5261120f03611289409048a0408142241d50800e403501450f006046000d00403030f07001d00c6011a6002420036039010000080c0003400d6503007007001b40321441d880740015080d841c01d911000d20350314000c0c001c481c006400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 823169082 1250 823167832 823167841
    0x120a0b0703110f07031107060207030317073507032319020d060801111e030c0702061b160801150317092101021b0c010e0108061519030b09 61
    0x41c0c10542c2c0c2e0300d50300c600303c40c1d6460300180303130540303001145036581000380c01112400100c2503000f180c080101c90003070b21a207400d842e0074040050741030001c0ba10030011420361000d208101c101e01c9460401400c1c4011a403100c002c860700d19103001d150440c0c00301c000903120b23851001c1a4404154520190000011640e11410800c6040b801c1400e4958100034255001c201400c58000d1604503900034110540204050200d8a00541c1580d102c0760380300c102008103a10b00800742107014100d9101d5903c0e8001b1074200401542003081540c000208815402c003403002c524043d480038402542e01c10703504049105c0e0107190041c07450a42c0d0400b0180e2241c41001e4208202040ba50002c40c0150b101c8601d0283da61081500001c080220542002c02c0400c8200f0020b045020150300800e4211151400b07040c010001c000001c3e41d44105c4400240011080c007484036055016040154200e44002c00c1c1e1182c0c4646005080e11a0f0803424070440c0c11005200c1d500003d0360584105400c282040e150150f55182 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 823170332 1250 823169082 823169111
    0xb01080309100c030e100e060403050607180608160c080d0606030c181728030305010e090a0b040302030d02071a09010507080c07021305090604110306060d030815120a0b0703 76
    0x2c4806442d006c0c484441460304494825004801c1c01c200c0140810f07101c07612820080c3d42c0d0241150010f0100307003841c41013084180a621404103c4401c0d540e849910b607210402c030321000d0002c0001c081071011222045001400c1d0744c2c0544401203000c00e002035030074909680281a02d00b500028000d01140c00059011007507011084030580783c1041d07100c40503808141d000c0d4500445c0714154403d01c04202d502880d54080d55164800c424003d81c3c00380005d0341c881030000e928000690f2010f14a5020f0250030002940d010041d543c041d001e0300540742400f180303025401c10303a88001ca0444401c0824280107580c640c80381c0313095402584000003042039203025a40601115406009580d900c50b011450604550b507041d03070005021602a014825801d1000b5440d030b4410003a2011920ac68000d001f4042c0d605000403240c0c40b0b9070006214402d1400700e80c5059404003400781105102012451000c011529060342a10a10361501c0042408075180e0400c9601c810021b0060002c050414034001c41da00e0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 823171582 1250 823170332 823170347
    0x13020301230f0a030803070e09070e10091e1e050307060c050a02190302040516051801230304050607030b15030705091302031b0c280b01080309100c03 66
    0x1441e64058801905000300041c11156480c0d503015400450700002008210080002d180900559112000c86030405002c0006c2010308613600c1000503465803081046103000200c1c1030b00c0b0302181c01c1c55081c03243c5a18184200c030305807242c0300c40e00d040c10180070003406010750003640b8403101c00c0004034500d600b4003002a44490843c410705040185c0c811400c13050080c00d000e00740e03c0c150b00400c000304045800c4940c0f560a282803000b03a105500e40400500c0030000e03000c1c17940b00c440d01030741c80c149400100c901849055805080302070402045102083c00b05000700f0b4102c1401684880545e00c0b481c0500c1c259140010040845c02017504108400360292188407180710301031160b02c0b24913129a2405c504907910f001c1c1101c41680030200998410580c00903500541c0200c8a950603180314445a51070070710749100d054107a0721164400207101196101c070055103080c603070000789850f810700c02940714071036280002c1c2c00a803610341000516021f107141843d0810303103002003411f101030300ca00703036403000751015 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 823172832 1250 823171582 823171619
    0x11031f080a0b040206120a0903090902030f010512010f0509100605010f0f0f050f03190f090201090905091207060204140f03150a060506070c0515030108100905100c0e13020301 77
    0x31074005001c5002c5503141006c1d1011010300300b05101052401c00700c4507000d0183c0ca541600407510060010400300c41c14000c032403103140310502606031a4a061706009522802e056a850a03569440c1032400210712401010b0080c5034100040c4070f0032151140102c201d900300da1009060050104030b12103125004100c11001700c0c0305041c2444040e07180d00090707650b841800454210601c0c0007081043d41e1a07100b0106100b204020030411501d80410280402c8549804002e4045402d502042142007070542002d81e00c80c04410035101e191404440030241130f00032030001c84072150003007070a02c03210b071030040c10306181a801c650802d0b6500341d410100e40c80d43c1305030549068200c08031000442002054000e00000c0101402e0b80da9a900c03603003042800180c150250a00c01c50303961210700c2d2076840000540f81a01d40312809002c660040c8050f840083c2074441c021985405030652071a1990300511030710300400e00301e841e0501c00c00d141d001004149080380e0305030500144184011b1156005512035146103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 823174082 1250 823172832 823172843
    0xa140a0e0705160b0a0c1d061b07061e02010b06030f0a060b0a020709060b0301080c19050d140c01030e2806092102030403050307020f01050d11031f080a 67
    0x4030384030703440e0884803403182c1104905a5940640f1110400011030702842c840d144c0e1444c10401c0042171201218803c08107601902100780c000e072600003528022004100701100d40c2c5800321744030804525141410129440400462205007180341c1c61035825082d4a000c1440e44001c0100030748000025000e400b000d842c1641b900004000a41d81940e1540980040c012810380f00313440e0001c3d400001d40c0e5400c00d015403844c007401c0000003d0705800ca84107590680b4403802c0a448120540010300c5005007030034201c40c000700049100090203465a078064880140150742020941451314400341c0380c094910b044604051400c10f40c070703003944804500c1c1010f0a0340d803a48800071440c3c21441e1250502c900a016000d18a030060304000c02c82000d818103c00c2c0c80c0f001c0d01c80041c03042481c00703984034021403001a02903002004204018584044404040d81e01410418100744101c00b40a04648074400d2428252500005001f920700d0040840da107144900c0b43c080c40d0182c02d002c00240c83d80d449070001040e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 823175332 1250 823174082 823174109
    0x1c03050115023d0e16080111030c0304051f330e060f041d06060603040b010902030604060314071404060311151b010b090a06081e0f03070605060a140a 66
    0x119040b0840042407008a54407013400544600c508240e151320b4404006541e64454031310004810b801800350010740802442c074281103035140e061030305e41b662000f441261a4044c2c074801c1c44415899100350108400715040000e81d104c5034002c09550400e128400418148001040d84400031008a01000b92240c1e03003800480c98891002240c44103211000080d803050a00a15088421072007003003110700700c0c54800f1a4420f0301c07000d0500c000c134802076402030502c4400704014442d4400680085030445005000061030f00e0f45e0b6140c004281100e000007860a07013140008000426002c1100c0840e980103c504100d00c614554078114100d0303840c2c1d9440d0203682c4001d441c0700400e1001050712100a0401200c40003200c082600d54024079440d06460300c1680c0d05404108004c0c681c0c4181011703a03920f04010210711202d01080c0010a801c4401401c1602c200c3c0340755072680a05102411030140305650224150a10000b0010344a0542e04400245211001c035801150303100180e14088079481c55041c01d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 823176582 1250 823175332 823175413
    0x150c0c010c060b04020a0c0c09050603030706091a0705031602030f120603010908131706071215052205220b0415060b030a0b0307031101111c0305011502 67
    0x2c003d0408a0740d00341d8414404548100d41c2608070b581005058800c240700e2529689400c80c1108440c4207481c100c0c1c06601c207203c000e0000c1d04603840600214042c882c8890b40018101221103404421034a002c0080e40c048244103221b460003d0810000805001440c1007600b04641ca040c640a400103035080201e807070010413956142036000a0f0b0203030b00000c1e9155901002d2818840c602c5d0240f084041524135055039040101d008108035004044698590884000e528414000b800c003000403403960b81444940000c2c3c65844d40c0c0561a9008601081d1300b003200c41c2000703607084820060814500c0d0311b0062085101300e08155401810941c0301c40418940d031140d040036509a0908046802e14600e00280894034001c0d0360082c600c107041c510014860040104103050b1542e15911009000ca00e11b06941c0000f50300502d84889421802003c541d80300c450b08058400a07684e00000d580403035503c2e8011b1003200210003100f5241c10700c60008040c850800c0c500d00070116802c0c23540d101c481d403404120b40c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 823177832 1250 823176582 823176593
    0x31d061e09060f0903062a1c0c031508031603051303080d02030a06051c080a05090315011a03070221070b0702070609050a0501140306010c050a080405150c0c010c 71
    0x100c10001c0d0103880d66845081c00500c1d80001d80c4403140d070354424401d1800052480410925196104540c942d0b4441c01544814815016401031003400c1c1084a048901e801c04803202d2107503402c4100c0301c3d0760200e10320760802c003c400323400c031950891445508100021011001603000710603140743e05141c4070341d4681ca010100414003110350801001c4640c00a5101c80c00b031341c40e401442c0280b4600740c0800140d44c4d0340d000c0045400c002c00c05c9800c09000d1451301d2010506400283c160700ca2142011464001800c0004e42803400001400040585070350043c400024480c000741c0410140103101891800c5c00140039503602100221000b501c07100000c9840f02d2859075050740c0c1d100d984a058031169050401010751244410702a8800007000725800094500d840c40c80c403400c941060316200f04007405c4e000d500c2050381c0300824540c1800190350300d00c00010004c0015410441c0211034560320f90341004104541c626400b00704403c1f044c400d0184200004012030340c640e1046090a01c2c0340d000c071241c50320 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 823179082 1250 823177832 823177837
    0x60901031409030c013b030d0f09140303040206041a1e090102062202061305100906020c0a060e01110a080c01151a0406120e03030112031d061e 63
    0x1d6403500c1000c4414084441000400fa08598138204005d00170284c500a00d0042032070142c10300070318000c1303900741c0744881400c00f5100b000c101e2900d81a2842c0820404140050b540d089560f100e40329502c411440600200c080401c4840c0c103450040d40c40e600b025000190300380030382c0c050601d00b6074548a500e280b403407a00d0700311200708015000c541410340c4400c0011849402c803000803800342c0141070024682211902d02c80060000c07112140f0400507094081c051b140d0030003040c840c01003c51880c0070440b40e680c52403180940b0344958a01100b60f0410600030304240c2c5403a45117018214a00f400d210301c6800c1194880352240078682041c18030f1519000f00c0c6070410240d40500f101100240e072030304c40601900544506d400200c561158507566907510908010103a098105103c0d0030710050081500c98141e8034800d0005810100d1030aa0300b1b41c00c7d60a5074800e0307009600c4650104840d000f01500040302001d815a005070b90383c441c6201a0100e110b0f40300382c180c40c5040000b4035404403010b1b9000401d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 823180332 1250 823179082 823179101
    0x30a020403051b1e1e060702280905010f090903050d1b0906090e070513091b09080312070f03230106030501150f050d02040e130c0b0c0c06090103 64
    0x46076805418420310b0041c045802d070006024507000c42850810320901380758040160f002900ba03980c40f440225600f103000c1c1100b10042d520200c100300c804c01607030b0391070113011014490549010710070344074a0740d0f034642c0700c419030084100a0030180100182121400713410100e030901f0230080380d00003c5240480348e030320030719401501a9140124485d445800b1074030b004401c104a0b182c944000b600c0f000305480320b4606d44107035206254544001480e041c415005080c505040c8100c505125072141003210075664031071800700030303058041701e000c0c002c550081c42c81b001400c41038091031410340c3c400c14104403040028644014000e40c00c00054000b0310a0b484506881c54941c01e00c103980254240500e1601402c2c03082031300003030500c0004140002d400c900341a141031180c030b408103d03072610001540d00c1d402c0341c0e1590903c19402d100010701441d01d0749203944501085a0254402c0200b440c0410825043e9000080104814442c055403120b0000d0791480340901141d80382d40f10f0400200480c06441c0345d48 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 823181582 1250 823180332 823180343
    0x302121c1a0f030f1b0102070b18030c01050403030e2e080901050f06010215060102120307020d030c02030301050307030204090f0f2102060c0319140705090109050a1a030a020403 78
    0x22600c1c00c1c822201d010594906401c454080d90311002004140d66818800c6080803150410480d00351400c44003400c03020b012106005550303ca0f940d5428500003a0081c422140d1038501300b2111030f815280a0000d004600f90908245041a00b142c5000b404480e14070b034460300503181c01e140e0000000b207021aa4503080d855032242074000030407480c01082100203a54a0140398206404112403900c0c2c4040715100b00010f03402440384071001c050420981030040d282034154000d8200745009640c207007004510403c0d0307031780080c00700c810398000040440f50fa4240d401e0071508103100610160f640801c924085907012600401c001010381400d076660400d150000700390b61501c017101010408100404121766185c0f81c848012070903441810303038840b0170480346110036110800c0055007441c2c2e1b444500e00c04109400b40040c0c440d030700038842220854140e56400105102180c80ea640c0c0da485401d070340c064201940e1103104e00d4588400c001080c8541501021280f00103c00103003001c9055056500954005 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 823182832 1250 823181582 823181591
    0xf030b0112060b09010212070f0f060f150e060306091914070305160f060c02040915060b030a150f052704030c060c05070f0b0901060b04080114130302121c 68
    0x214440f200030352181124501500441c4040744201c8083c0382a600415040005d0134814160f03a85c5509048003d1902246d006549000707084190803244521181c40d440001c0b08403409080c0343c0d8000f000500103080718841d5200002b080341c0d0007400708940403041103a00d015842c1700c415162594855010005401c810320681b100041401400161407200d59803d52406100544420b00304e0b41d00da5280c000d88012403541d014803401400e156000300740d02d6000b150f4000401c0a2030402105881044d0310081069030048180003410b201407140d101502c1c4410301c0503502d6460001102402e001c0c03480b585200c0c00d4403500702c2c064400340d40101e0070242c40f400804100d034540361070003508039013805500340c0300c0c546001c810000060040007181c060315086200b403004c95030f1980d01d042a480008041030440c2d500ca03140043c0c1c00c6039040142014110800011441c2c0d856008940035035000240301c403003008801c5106001080c1c01103012014072295011140c0d8501c0c0002244214424641c030521f40c56180 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 823184082 1250 823182832 823182839
    0x105063a0b0609010609121106071a011e2312030301060909060e04050a060e0c03030c03030924040b0c09090408090102010c03060b16051e0706020106150f030b011206 73
    0x50790642d100304411164582c0a98940200701d40d040c4450083c1201589400702c804045034807034070919020a4001c003d640b034085141d40e10b01c101c108141180f0030340054900107002d502d00400708404d0142c101748005151511f030180003e035034180d28005406040c070041c0c108040f6110504003510201031441240d950f940c0d940401420f6103240e02c54184410300d022404603008000f03082c81c5004540120040040b0a8031792100c20060000d810049554805c00d445680952400d00140000444400144d80c0701d14104044c0c9050002e418032914204e80303800c001c145c49401c3d000225800c183c10100c5000ca55443c0c82d0a2106440303442d07055036104242c1810002040200002048980000ea000740418481c1060581c181d41150080d071151030803d01051080b0721044040c500300c14050011510644885c26411042d01c1604211b107000b80c01141042c420a1b40901805004041d806210204e0b606c1085d80181901210f00300703c4109500e070f10250900760312655005940d085010380c10440550b5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 823185332 1250 823184082 823184093
    0x60b0909030717250510060b04050103051f090b0f0d05060c0c0a0c0e041208090c040906060b03010e0907060807020a02060a0c02030d030f14061302070201200705120105063a 76
    0x13214602200d9610805610290104103800b40710202d40a0303022040c01c0500380743c01500505002001e03a804a040010807151030321690166100800451100259400180d001e00582c3c1048520070340c01001000b0400d00010800141198422000309041d6201c005d0102060b04001c0500c9000c1c108108a00c00411046000219603000717910076a200303050445c4210090710441b004a40038543c540040414040c54100b6811412101d1b01c6114005000c80d10350400090b01e8100ba08034003007014084041112000082004c20040c1115052080c000d291202d0025030315032660200a00483c00489d0601c00d15000e03c0b203003204035034010141e6a43c045c0c2c01d600200100401c00703601d46110701b08582080c800c150a851603025503c06080d00c140b504444010502039030141038101d04100307465884110800b041c082d545117100a40d409400c41c3da2920041100300c10350740010010b00c0c0d00d0102404035956640c4013682540e00650790301c1070006814017101800b150030040c03d01c00a941800c1e144100031 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 823186582 1250 823185332 823185397
    0x2150c0105250801060e04140a020d0b0a030503041a09060d0522020108010905041416060216050d0b041118090607081b030c0d060e04060b0909030717 66
    0x60102c1448600306a41c401c0c002c208902072009200410302900042c42028030413054907208410241c004901c014591101c0802007404403448403415901207126801103880d8011052425811240c070340c0801c7c1140c82c0c254481c0308a1041c1007a0b007030140c1d00c0c041940e030610192000d100c0010803075a1140700c181100f10107000c0032101d0350080b0301003d600000720410321161140359601a91032900c00ea0802d03d4032801000c001e0000d40781c15100c00402030429070108015020808451001e10304c0c81d14181d00a450720340030740d0b490f10403642d4024041c042ca84841c0f0f0600100da40040d07014010b03403241d0811120380c5803860140303604085c104004101101d1403c8509000d9070a000480d503d42da0344040494024100351541c12402004004032401d881c011780107941c01440300b102980c540310100b000c4500329407030340d440070004041c90b400b00018441c3c0780c0f007035800749130301622a51603501d85a23910341c1c0c0343e00c10b00900a29404255000c560001c4804003a20114511320700d4200d28021081c24480100 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 823187832 1250 823186582 823186591
    0x504030b13290a0f11040605070507030203013e07020d020a050a091a03030313080d1103011203180338091507110d08070c2a05060910050702150c0105 66
    0x6007400313070804100165106014a03034030542400d13800c080c10300b901250580e00240043d03910b88a0b00d400440541d03020f100311880c00e00c0105005c40784024020002c9850020300c80414094804031100101d150f11070021954400d034111861000b0101c0e070700c00280d415a80307810040d00840c10020104805009600c03100703144000e0b401802406c0c0d407400c02c055480c8800c848039003240c240f07890710b0000642207030060022034801e07145c04101c0c45000103072107902e500240e01c01301c0c0744425040f14109041e046205407611804810a051420341141c5401800070195040f280124030f00d0384100c0890a89500740107180f20a020750040c00d4201030345019600d0400d00250185041c004005c213200c81e001b022549070404144000e40203209040c241500c800500400c0f040500003000a10000509413038000100030120380c1403110304803036480320319080c036800d43c02c520300945042224a04a81e18204000c002c40a0380c601180c0d10000340c804101d603e00ca100110340000302c04540305031600819003055200c1d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 823189082 1250 823187832 823187851
    0x3191220070f080c0a030f02010e18040813080a021809031204050d0e011b02040906140703140c0a081501031503080d05070503060f0d02040b0d05011401060504030b1329 74
    0x1140c401303c041003030102c01d601c0000d00100b2002501030065019001440d52182c00902d011a01048444941c4903601c08640840b210407000400318203500c10800c226000e00f04940042030000502d0b40460000740312071440e500b41e481035400140d0800020421140e440d45900d48100c0d003418035107000ca80d203a8001c8407440120301081c414070700c55440745983d8080184d4245155503042e010390240002488080c00c01c0c2c50080e110100700380b8074640c3c0d2106900646650b600003408000c440b140d000303600d40280c103810054908101c41285141d1000e403050304040c018078100700b40d8401e20011390003070614100340c0e020400000c07400014090204050001ca003000b12060040d81e6580b034044419200845000d40c0c0f00318200b6442000e41400f40594240ea40b014000141c2e4804a5000480c2107140401c1122641c1d15902915282c2180c2d00703101c1d004104a080c81410181140e0f540584090003e203010925000c0101c03a45c14861580140703060002d01c000030204e00d88191400b034440b080c003100d69242 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 823190332 1250 823189082 823189093
    0x5150409061505041703130e040c170a0303020d06030f21030908041206110409090c1508040212120a03060e250e010905030d02070503191220070f08 65
    0x8202e070410400300c1c0e805800d03640301450a803c00f02690080302e03600052082d24401800503450030b07007003445007501030300310044040f941c1e19041c5441d002c2006c068100b513a00c01481e0140c00b10010300003070505861581400c0250f11040402c0180d030051203103a0029007e0348182a4000c00e00c80803201d40982180303c4503480e52000220319055054491901c001803840004201c200905601100603ea03580e116a90100b0300d54081c0c4c03428895034001d44c0107124680d5446055030200008191a40010003544442c0c1400f41d0440f00094051071000300b000e8055806030b080b400304480244080c0290b1200c0341401522940c40030001001000a4002e1401c090509000309070102c40484400c50b50780c0402440e0000481072210445601070031344041d078140700324500b0114640c3d44c10b0000d003010800c01c1d0300400380300c0d03d4201054584182100c0305003d018220103080301040b6007401c814910811818011501482120512031020340240614524060000040340040a104002c07049900c03420031201c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 823191582 1250 823190332 823190339
    0x51b01090806010f05130b040e010b1309080909250e101b11030a0804030b0708061210094e1704030c14010b011b1e0206040515040906 59
    0xb603840e0401e0180d482c09a602020400c0a841e00043c0e5030100c40110b000401c20400b140041822360704502c94000c0035944414a0307118905004141c2031482e610400180000350b08d60726a003d55105c1c0304d003454000c0c0c0c0c490b000151103001315605808803207000c410345848041004001010b603080c0400b0f081c4508035800481003494800d0030020002102007a484c40c1d02560b0744c1d02d1010710003011440340c0e0140180d25180000c51041d6010b00700960155202907028504118002d00b40361008000a108d9481c842a60000644c0040c0f04040780100840c0003031703100745034100b4038882086102d22020620f90460341c3c4245034402442400da19450f00d1214442c410038101420f491040c0202c041d00041d0f03d2a80c10b440150f0001c2c81c590030034040d0428030f00001494880081c1402d01040b00000c60391a0802c4c1071403035070311000c1e084c1c4502604004860240d40703a51340303003144591040c0120300d4508029440c010355484101f00c070004c01009040201c9803280d0b0001050720340140c070400300514900750000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 823192832 1250 823191582 823191599
    0x1e12050601081608041e060608120a0f0c020a0e04080903060610020a061107050f03031008010902060d0203070e030d0908150609010b0d090804090b101404061b051b0109 74
    0x1540140340300303d464400c48020705001c0714002d900400c140c640d105842002c2c504400100e0300e58041c0c5000c0c1c0004240300c0d04000c0e03000c0ca4040c040d04001c0c02e050003003015042595124041c03500803a9245001c1c04d0018607400000d04500d442d8000c080198540030510041140c072100402c0d89840139025100c0fa40d44400c10080800d8210860303402681107962a080007800c1c943c03005c0d001201980b10f6a08001c620b032101481c00a51150a00c0c3d5607200009000d941c1c0202c0b00284000c2c61458000e1100742e12035800300d2010301480d000403010640100125523154000d020360302c0819805400c54050160548006201000038031801d08907009400540c444482040b0920703200340c0c0060320000450746072001c0d0102c640c0c00740c0d00c14030a4998840070b007070000d40d4600041000700400c00340490003a84807c100610559180c90020520050b4860f1104004004007a01c0c2291a1800c010b0441c200c02206025031a100441c01003090007100c160710312981d00301100c18100c4500303076a80011682c468841 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 823194082 1250 823192832 823192847
    0x21c0b040e011e0c030219090e010b03060d03030e0c1207060e01110303040305071a0403090e0a0207030f080a020f030c07060506100903151b1101110f04090902011e12050601 76
    0x5907402400710802440707103241c15084001250303811700e401494034003000c1d10000301c0c2e00da008000b07000900410040015200e1002694050700c40245120320350304003a000102202d48950004082c9600d4240b15064048203201c0100b4844010f004194180c425101883d01c0d100b4500402c0f011130700ba003a40180c2c0394440d4032807103400c3c45090b00941c656200c0380c43c2503031650080358080381c0d5403070b103190603404102c04151940e020398071070b0319030140090a0480d00010340000400c104034035441030059070040b90784043c00080003400781c02e00c5580d0f9118200060040d00c100206014022000404c0c0304032880c2e40d0000305800c0e400f803e010000c070b0712600c04103c0b6510039001c4030000642c4014092021920314000341c1102c2541750700009074411288400f500c1614502103c001280055842e504100c1c1e0a0150403080035020004074039200b0031140c205114092405004506559078141000f16405a0034818203001e015680401d84035082c01d004180d2015181c000c14642c1c1480003041c07155024140 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 823195332 1250 823194082 823194101
    0x708060a090507050f0f06280c0302100c050918060f240a030213140910210206130b030412030203010f03030e0406090f0903020f06070806011101021c0b040e01 70
    0x740650510344004c0040c544820b803130651b409802c4150005c602d0361144c008101b081c0784125020035060780c003a5032103003c4039907085010a1040d21f00d009400240d000c284880c442d121030340c001888041d685400c032418004d003841150003400c40d43e00e40040340741c00003800303110301c0303044410f01044003045090004d0b20012940c0001031540403145c46011008000140040001c686001802e002221030b40700162065540030003030070004941410340c98102001c010f903020b00c004000b480302501e0f09010040d180310710354001054180d03800c5181e0855030b40000b03d030f2003c0407a003c03905259817541e1000106070b105072411030700f80e8020926280901c3c043d000f40d80c106c0d200d031840280b2aa203552016290385144800c131a500903614040071072000d00038400d03907008200ea1a400141e403101407030080d01d00103d1400880c8a9401281007120b000d41c040b4082c1e62020080c604846201d600403010790280c01188500030388212804070f6100d1011284e4000e40340c2210481d02481150071240b071403422590486c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 823196582 1250 823195332 823195343
    0x301020f07141c0815130c080604110a0f0513061e0206040305030609090c0a030c0626010b0f040f03080306090f16050903030d0504060207050105100602060a0b01030e06090708060a09 80
    0x1000003d00c82c040c07600c282d849000611450851000b4000003666448000d21109580e543e540624455551000e03407181e001d201510700304009001030310070160038003451540c0010044481e944800951082c0c00765480030b11041e01542d44a40ca40e42e000d40f418803100c40d00d01641c440b02076083d07485440012098025a010703103c0c0e61554850b082440700f10000103040346018403030840e294406849908181c40154055217561003880d0a00100801110950004c0c0b0007419041500d08035120724000c406044071010300d150b6950314031000400c51240035030341c4120010780c113841c0c0010a1140f5072000b1846403000321000505651801e2110301c2401064036501540d1030015800142e46008130010300000000030708813403d2410309070001060f074104590490300303d07402044600c2006824000d42d5040581d1030f500e250440d041150003907840500805a0340040c1e1552080c00e0513074000e90010815a13036880030b132001468085202581c0d09214810040c080c400e280c0003074001d41e124030071a4181540310 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 823197832 1250 823196582 823196623
    0x2150a050403050c0d030b0301050603011112060d0f0f0b2d0405011d011505041b260f06090907060c02120102040e07090f0807050a0312030b0301020f0714 68
    0x10244000100001042241806402c000c00713081c120301003000a02118650340c021038900c440c082814252403010302031a000c1d030704041d24500124014411380d905c002036004e50840903607495000035101c0301d103000d000d40200300ca42030110a02c01e0580c032180c4518010000d242c503c1e2690074a848035111140800f150012744403004481045403002c4003a0001d020f800013081504c030a540d00c6090300c0171407138007140a0399500078454655800e42e01183c003c0404440802201b44401754011180000160070360401c030541c2d00809202000c41c2c03e00161341790a00400341ca501d4a00c215121040c4107613407881c451100c110016000301d0300010b074401900e17107070b42d1141d80080b115400d0003600c9142c2010258955002d100c0417441e0120381c816107100700d281da0790b41014140303084041106101150040750454014040502840e00c1c0c00035020200ea42c084d9030b00c500400020421001014507010640e49540002040444442c044026244040c01034424594a468407441265910620070410886c610724 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 823199082 1250 823197832 823197841
    0x50a0509060102250602100614010507210302120f0c2704050c091002010b01020d0c0501092a0501090315090201180f0303090501180b0a020a1b060f0215 67
    0x180c41504944107004840281841d1100c0b9004500341c01c601d2062640000002c0208540c100f120516400543c2030800080c0d0801802c000c0a014860006040c0030001500c00e0401c80600500d41424154511110f8003000104005019601447d100b401c0d24002e000810300d00512101c40c20300403a180100286424800c0c03062581590103195003494189402400b00b20944860081e01d100b0036550f030b0861303501c0c2520002c04c080500382070300c1c0504683c90a0382e0b500c03503a40c000032101d5414001d03041c51422070003a40340403400360003c07120042104036214040122410700128071580c240c03810300c004450644583c0115190006407102505011042c00781d075681c11002d0340720307440090040c504035828040c104104e001c4000d0650080e024000102c80820034183d0018511014140900c0c00d1a90600308080c415840041070003142c00d40382c030010f0035044841c02000380b43d44c1e40394006a801c4402541c1e4400003900c203994130a0b400810340240e4203003c00d0380b0203e640240b1103460102400c00761074 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 823200332 1250 823199082 823199089
    0xd1406040c1a090a051311030f09010509070609031704030515061516020424030b0402010e0a030f1b120501060e01080307170913050f161806030506040b10121104050a05 74
    0x200c00c4000301400c4c1d0f607c0f13141c1003803514400210b20605090030004210b051014155084450060445003e6003003040c05200340740d4012440e104070ba0700715403000c0350040000c01c004030a03c915440200349120f981540742c3d0400022140b42e200d0001120b5001208402098070040746c842c2d00c840410700481d0b030722000300505d000d078080c0303000c1e240c0d444801e8104061002500102c80c55a001650b00740e426074100400c40d0303400010b00c1e000500540e00c6d96042d5103103948140641003407640c0100401280c0c0d0b203030b160141e5024404002422105400c0120507140d043c998003c00c41801494000c42d5024004a42a04000100c1d0840c60b840a210394400c5ea5074048240341d40c10900d0b583c0d90041e05081e40c80e000d0350a41c0223590103101490034442c04c50410381d03100c1f01003224200c9508103100403000140f0410b49400d444030100d03500c0d4100030407aa59120005070051058000d20340d4065605004400d501b6846441e41078204514a800c000c00040c02c4a0740c50b450150703200c0d582c1e100085000c14041c07403c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 823201438 1106 823200332 823200349
    0x40515240406120632013501080c210c0604091b02010c050a03020d09050a0614280e010f1407140f04050d1406040c1a090a05 55
    0xa91030050b0200060031004817000c21900d81c42610f199006580b641428a000342d0701c50800340c0190700b100c10030981c8003c0c01a00850346800883e89110028102d01a0300c8020800550b80c0622510700003010382c0b50000b2003050003201e40940554907841d005d0006007511010206400142010044552240c81061811603041084601400b074120741191170510180c0ba0142e42c0381140b01d03407500503001103540203040b8807980e81c086c0184202641300d0350070080b0380f002001581e11120103030501854a5840d2510180d03414860b900003200d5548880b1070707802c444001051008110000e03104889400c1070700d030b510040980420035000c1c2d001045a08044211034280d0414110190b61241c030701a03402018000c4000b1100c1d141404180c080c401c0704070310342d00200c40c05840d02d0314100b40281a1480703038401400005044407881c6181c68199104894043d00310900203140504000220 = true := by decide +kernel

theorem cover : BRFrame.Cov 823021582 823201438 := by
  have h0 := BRFrame.cov_init 823021582
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823021582 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 823021582 ≤ n) (h2 : n < 823201438) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
