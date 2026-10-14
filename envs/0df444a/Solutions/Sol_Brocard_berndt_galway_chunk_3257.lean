-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3257
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:07:34.639883+00:00
-- url     : https://prove2.me/submissions/387ce880-bca7-43c0-b499-d0e7ae236aeb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 585611510 ≤ n < 585791366 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 585612760 1250 585611510 585611519
    0x2109031e271005090303181306030b18010e120c190f1a060a03060c03020705010e071511030405060d0e0d0e19230111030f0703020d0507030e04050a060906 68
    0x20001c503110341c20a0300c441c100341d01806000d5400707000c2d081c0d4194060348240401c009215841c00700704503120010b0100365200312020940000d84075182c006917200e100420074401c00012040300c0c0f9080138401c10080005c0400300c0b425646506104103002c03404100803410300e08001081c013481480c1c40c08403441140b5505589010901e076046194181d0703180c0c030501544003d020070090317800c0c81400c00802c608942d50441d80e4440050080034003000401d6424400302000440c2407043e000c2d0580c10784010484c0f82d1030689042410741558902104101c86040b4054900c600002640c05441c401c441d05a19503107000c1ca008002c10f8140c480c04203500c950010166695008411034040c1d0f0f0b4246c42d035601c070820500e01c514001d03039184505248070052581c40740e103070104c50900c030044003c1498000008000300c200b013480c6800a0420610050001036603a08058040101040c609002d040c0b19003010219240030348a240459a0603026645407800a504207007076903c070701d0113040c1d0180301b0002941ca4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 585614010 1250 585612760 585612817
    0xe010f0608010914040f06021312020405060105090904030c0201020a0b0c0d1d03090d14030316020601050108040c0308030405120301120b0f041e0809152109031e 71
    0x11449000d0100725050004185018240100c0031504039403a08a007894860b5603901c0101d440302501038620329828801021403000f4680304000406074041000d506c640c080c0104030480d0310140c003090500400700044c0110383c036105440ca50103174050030941303044050b03400182e04042081800500c0c174150901001940c803100006020250702d243d10800030760307000016404141620448400d0203074000d0041621514140e00240c04191281d44910031101c003c000a40c80c603001503070604020114038001e015000e41c100602030040c40c1c05d1030103621504142e220280004918040640650310000000301071060400c40c7c00e0744184150716090340c96a644041c0100c0c11003168046903204008d03004900c100100d200c035540516000360340812107803102d009826568003503501c01c894080c414040307128166605100011520002c4000554400394a11854a006003042c8107220015100c4103201c60038030000b0565450900e40d070607003212a80e440e03000715158003c4c407800016a9010300e2503280000c25 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 585615260 1250 585614010 585614039
    0xc0c09040f0311060714090604030506040f031d010918021b06060111030306300312040c08010207050d0e0d022205071d010305060f0d1a01080a0b010e0c040e01 70
    0x40e59910f0860f401d4041c0e16602c9a03c20b40f07900d80019404180c41802c03121200041c204440024186850f095036944c1d640c0c01c28500700d4058540fa01110740100605810080c0e00e440c8018146201131503c40d01c10000c0c20b14040c40c01903080c0251850b80441d00c22010754110349605c8846a00807003500480320050b130360b07007008640050000395000e00e0502e01003c00003c5d40d001d61002010a0402c4180075210b0100f5250b03030190704180380d8803411000400b24140000c02c4c180d452900c5040d928a003a04000a84003590f903c00e541e02e81c81001010003051000c03034101c0017182c1518101c601d000788203000410201d141c1030040d6100035600a0744c000300c076200182104000a2517024000c40d543d14200366841e101c130348603104200000c4c00e1100703802d40c841d83c802640180018140b14030399048030003180b080400c441080703c01840a5200824640e40581102e0040840600402c41d501140e50b5200140c2018400c1c1712040c540f20300881e00d000140c8058034042c10882100e5501583e641c144105200f0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 585616510 1250 585615260 585615263
    0x403050a11030d030e0c0d03050415030203091603020d020108190f020705010b0a060c120314070e0f09130602071a0f040c050d2001030e0708030c070909170c0c09040f 73
    0x4140140140854060300440178100084030107083c0180c0200b0a00503030100f00c5c2c0c0220304010041201095404041d000e0103021215a5401a00d0f0301d4041e0030030b40703840c041099100020109082c2003005903a4120607100069083c80c109405403034181c91034803101e0f1418400081d0a051040300c920702d1600e075000d85002c900600080c805813a5250a014181503140210800034084101140220300201c10b1050740e04d200d8900050754010010942c11a81c1d010f40d456000507d80b444075180c649444859400001000c03601000c0d20304007001c41c0b078020b0400c44c1000b046650081901020b0001100501c100e0941b80c501e80080c51410940c014411881210119506000d03010301084504040e11420099a80705007501030101e000340c601c480c4840010035403810907840782c8440c0b0803140d040c04001c0080c0140360045444064104d141c40c1071414a4200c3c022851500b05448080f55440030241141c7c09501c3c42c1c0c07595016410000c0c2d0805002c4140c164002e01c0480c18030040101c00c20000ca03085 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 585617760 1250 585616510 585616513
    0xb060309100b1504050108130c0f05012d140c30120403030515210c01020609032b0227010c050601050f030c19170a0305120604020403050a1103 63
    0xb1080e03010003070b181d0390b506150701856509101c140040e5001c3c000060300045641c008004400d0b0325030b1115803500e11a0880d4805100380d4901708019600180244045600d6103c541c9a0245503c904621f00c0300c485005010041101c180341040e05130401122242c0311381c4410f4841c410103c401e034000e0300c03900381d00301c040140c0101c9402c12146485070940d0403040c407181851240e130700ca03602c08801500b0007070401c01c50184030424090980e034820110008044801580700c49500306030802c682005441a51b4a042d500131404019200d100803003298440c1d00f00139400740c00d1352900100386081e4405a04981c245610004407002100824426110b581814200d452130001c2c02400464940500b00310007091540188010710941c58404840c0481d1100a0225101c20000d01c0000701c0150f0f20b054120501151407605000c1e0307868101201d458905010020800d03050150f400602d0351084488a0301746a40701000b05c2d0060791603404850085801804803032107842e01d41000c40c0b4421000d10a03506c203 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 585619010 1250 585617760 585617771
    0x11401090f0312050d140a0504061a09130309050904050109060606090501080a0c02012c010c0e010210021317150f01270902090708090d0504180f0b06030910 69
    0x504514207030740001d882d0300c60010400810289402c1e03030150051464161055280e0b0f180304a841d0034001d801d03105030038407100030502d03082c01c0c03c1c01030480742242071060101d100d2418904960322070304041e9070040306503050002204581c0c101194410501d411060b80710b9072600500c010b00505403c81c04a2034000d107010031240707a8035032099508081c83e00c5240d01207058003000511034016544a000001c04500010850b41c0c1030088144004942c00ca0404121080450180403068241300e64401c1045c6811302602d101e80c0c80d0000307981c803490118900d20090700001c5403d107040100402000501c2e0300c2030365881154420300c0e81c3c0d403101024136003a91072200c0580003404a000240e0120b04035629400007001d5030900c1c1d901c441503000311030300700e1551701e40300c60b00240180c40342d1070420711601c40703a80c0d003070190304121200c1c0f03007440807180c2c140b01001010b0105000c0d0000f844e41c143c0c6244048840002c49038001c086550184c0841c40c482c6a01071000b1080101030000400c00c08181460010700300031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 585620260 1250 585619010 585619019
    0x10060b0a080c0901090501050a0e10030e010b1c0b043002010b0109050109142706150c07050424030c0609050307030c05091b0706020909061f08130b01140109 69
    0x2010f01404455600040005004126075402900185003010300d40c545501c0014001000ca0200344540a00d600040d0f40c0701c4111319501002c2c448c80306031013000c0b241186102003c440a81842480d52401b400c8223007204081020006c00108500c0214110040d006c0d051038003c40c0b903150001d000c01d6010141d401d1100d10003896105072400029603070140c654181040c186901f00074804010140360703411a00e41c40700c1e00a914034810b0741c40001707415801d143c0d0341880c0c0407041c420400d850b842054007d2009000d40d0503101000308445044d9501a03800140c5603080403074000000c1d540742c0a12060382060704012090001e05140001920110748607046d8066950723040c941e4a5810f403001a00314640ca0750180010310300106001e401c00072202c4015120300d01c8a46500b859440342c0800c45065500003200394590810051142d88044119408500300440307620101c6502c02c400383c41010010988005040c203031206a04408903604401c41d03024941c2c49035911001c90ba080110303075010074880d040c0040c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 585621510 1250 585620260 585620281
    0x30a0806040b0306070807031d0307140a171e130801050612030304201c020f010302030c090d1514040c0506070302030f0c01020d0905010f15060f05070510060b0a08 72
    0x40c00c4680150052134541e0f9810401c59a100380036092000300764460b0407104004210400120084071840040c5582e454240342216459040b45440141608a20254400b043d11404600042800503425940e5071400d01200040b50741101d50692a1038408500710112024a802080c01d0b180014020007071511180208207070703c0d90120519000c1c0d4030410005000400440407109107001516005040d12003910014841d0b9011030700140104c400e03114041c0942c40c007042c195019200a080c02c40c41d49c02c00d0650071a482c0b084090342402141c0001c000c2082140b2115440312803d450101040003401007d06010001001d59003680e0f40c020b200300104080c0b5289040b1400c807a0315800071071900c1035050b400203698020401003486554248401118800a0300602456620501c00029100030714044441200c004828988060030312042c184600380e0003501003030300800581400c5485400301c2c075066240828540c0c41d00c0001e400c1caa40096a241d02601500e40d541c401c1d220302c02181d4490340600f = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 585622760 1250 585621510 585621521
    0x30f0f0c0901120912081b070f0305090a0e011e1d010e040f0b071e18261209030f0604050c090414061006120203011203030e0f010608030a080604 64
    0x9890030800c0009510940c050031001941c40c544030404034029005440b40c48402841103c410702085c2c0803400c0003188400390b86102040c546411103d414000e440d200d4602605401c0c90050a102000590703240c07a071348001e8000c0040000d2021801e0a6840c0c5080c1d5800c03615094421000521040000c0390020520301c07010504006418032130b59580c0382c00540c0034800c3d800ba00070f6400385803114081c00800c051000e02842040240c07240882110207130201c40781201c2d618251001c009514101d0715550340100f5420044648030000d10040032181c4115a100c0e171031071050080f0900c110b040d0411071012140c0686002c4604030203a568000a90101d1512441c040700c0c010324540201006210f54174107207803540d40160041d40d040f80c1341a0740c000404d02c1d0040c140c1f000990130391201d000304083c03640b041e03c40225001003079066080d035240c07100d01c0c4410309000f0001001c0c16191040170040c102c0800c0206501a0480f009211155407821825140d44c0248101300018405600042d128241402407 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 585624010 1250 585622760 585622771
    0x11070803211b0a09030c0518070e1c0b01030302060709181e0e06090f0703170c1c050409050115051b4b06010306091104050c030f0f 58
    0x29950307140501c0030044844000900100340d0842d24000514880700300e07000740c0f20102c0d0b01d03103c00100d0f81c15814031009610303140e480a40301b00c05480006171a101a41c82440d000321490400d08800c49010300060a4520751800f041c2100c0500900c04082c0040c800d0b05504990207038094540d9a15084000c4030001018012215054441d0310f5441380d4000c0c682c000c0c103207503d43c56804010841424200c1e81511070b1082000d07015400302c1c0612003402401d1102004610b2440010942c4a10710741d20594020a291110304a580e8040f415180c480030038052001d0301982c2c41400c290205480c40080e080e40c010340990a82140f031f010011811790340d0a100d01040300b02c00d4a84030300707000300c03d800403800c0d0881a4440b041c034000d03c0c071146d042c4001c081c441c01d0f021480c0d212030040c0d404900c404408881501c88000308014151070100345d034280100d00a0706590300100085185446803c06608219030405071642141c40c3c81c1c10040340145840145d8092609085818202c2d150341841c07074024a0191078 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 585625260 1250 585624010 585624037
    0xd05271e0708120706021e0d0c08060f0904080d090302150106021207110409020604080f010e0105060d15020c06100501031407140c070e0a02031008060106091715010611070803 77
    0x3102d140300c1030f008029241540c8141c50244c501400e0482c81044095001403d41100c400403a04201c0440b0a0051003034101640c82c7c080500d00d032000000d04030701540c8000c0303400741030820040740601403c04112869450306060601c0400c01c030785030082d40d80e0841a250b40080d200c1d40000b040803840412001c038041c1008102600300085a215080070068034002c0301e80c016600d90031800181c484c0409400200344810241c9400038020008509480180d4541c0399203908d088100a8165640b2200c60440350304800807010302144007a5a000904c10580e102c100c40c812030b03040194100645281d4000d0741e200b82d80600c11295001c3d14401201019204030010070186030b400d040010114006d0319041c0c1e0440200c40c121980d4000141c128201540d030050484d4001003000550050700c2c1701340d402000e0f038400420b495850440000c102080c180600d034211209002d0300010341d40304001d0318072302c690b802c3d031244c00c01d5a5070078001e403528021443e403500038064104005180741d0301100741e0321015800d22 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 585626510 1250 585625260 585625273
    0xd02060112081801020c1801152a0302030706142e0b0a0c0602040806100b1c0f0e0115180b01120e01180f02090a0506060d05271e0708 59
    0x7020b00b80788681041c0d91504601c80c42c0e252070419501c1052010400c2d180e400110408d50412001c03c00b4014403202e00c3c03041c48660941800714001a00410080103e00c41440c5003410701450102c3c1148075041004d072080d4200300380a01d003120710202c143c0c00740c1c000c88151003024100826030001078181c11441c1c580716242140c108614a65413008158620052038000500c0c01545d548100700c4c3c000390080115a8891406c100a2a00c0588201c01410380d04200c03a05101c00b0600390248111204085030070641c80e03038460b409018003600404824680e100003804842d4a01001c1c0001039001d200344e194801c2541c0d6405840000c510600300b200704180e69081440020f2003075030004c3c1038148907001e465980d0700741d04d4954210786035000300441c0c89051006101030640c0108070410601070110480d4034945010301c00c0325541c3d03508840644507150404601e43d62202c01c2401c000d100b03410500c10070008983c06405504001c2021100000009014001c106800078000c0d560724541c025203e2176032015 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 585627760 1250 585626510 585626527
    0x8060d030f11070f03050f071d04060b240d11211801060f06030e0712033c0210060503030306060c070b04030807060c0311030a0c200d0206011208 64
    0x10485920340705146001c030b44403184d8418504030010340d00d0b44259080c5d00013195142d400b1000740a1030f001003d100c114040000d800ca0740582e00b498000d04010714540e41c59040f2246034458900b00035445c1c598800f20f01c0c41e41141e9880b40c1c095444961100f607000e290030840304098411909580c42da000302034000c9000111500002c409641c0949203500025440d580c603401e16109003e144040d20302010341c110352501d48080541540d80300ca004100302e400c00c01041c0081c88d900100101480c2c5c0500d4000c1801c503101024138000503d08892540440c0306081d03129030421101d07401e41034504560308403103a04c001c4605000803140385018240e41500108003158951402c0006484e40080310015603000d1a0794000490740d691166200721741c1d204000c01c820092090390310414085460508061121007c6030740c1d080c1b403500c0004c20b1015100d50b6082250000c41c842c4510004200f580014024000c10740c4043c43e9840c12000d000d000144280400800d00c0720081e0100104694481c6d03540e401c04900 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 585629010 1250 585627760 585627767
    0x607030209040f050103060b091b0f07030c021302180307030804061110050720011a060a02030f1b010b011707052503080403092310030b0603041208060d030f 69
    0x19588941d486526450f03007420868a6100c0d1074000d621070702c00021880213200a01405400c0100601c200003054107005002c01128070480754540500040d480e41c0340a945802d1340c0001d24001d001e5041792000a02000420596006002c844041c0b2030070905070b1242420550b440b40e80d404000c040800501040100a0080c441c0e40c000140303880680d02d130080c15140800440300200c41d98070020355018602d64168a5040c0c1d15254407000710028064100b4459840405507080c03d00a80503020005410080f02d200340161820300201c01c5005640f0313848100d081c18048814182c01409501c0d120103a0541e43c054446042010700382c0100340915038802030145c030303950018000c0f0401007164140b05100b900e4820002d100143c426241c40d0264101070400401c505642d07080f8450000d81d1501925202441ca11062500e000032900422800b00d0004e00710f022f0a80e54080c2c40d003012001c41807004001072003141c0008440b103a42c8042075a500c400c03c008032447c211a0140205400d0301542c80f1a030310 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 585630260 1250 585629010 585629017
    0x60409020306060721080604090b060d080f0a02060405160315050402040609050403051b070506090d0614090a060507020c01081623070302010e0703020901170a0512070516030506070302 81
    0x800030f107000d003895001d0301d03440e521100202c54121105800b001c2c005d038058020125542009041e1405c01004250345d64010301c9120103041e643c454414080310b0010481040200d8201240c01d60910f0740b141340c521000303556a9019901141c560180b42c10021800140034824000c49402512000ca101c1d44503280200400000d00160780007078541c00041400d50b803a00499001b20f05c00d558160f9501180c0f2400f90002c90344241a40701a0007a41040040390b4911040d80c3d101d040c229490a201c5400340760000003030041004000084030340c0002c20503100b030007103480d8001501440061010760b4800d10100e07201c081881c14035010801040114180c40f00c280040c40091450b4240300b009890b003d206010060100c01c80e044030140c00240302410540c0c280943c40c07201d800d0000074802142507600150038890305004002035101c598103103a1a0302810440e921400d90004141c54180c940e0340e000946507804500180e0f42403060b03c0d59400ca00000700342c0c0004480d00000030344120f88410701d04034044d51 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 585631510 1250 585630260 585630271
    0x91a090703020910081f030201020d0e0f030a030503090f15180f2e02190f090b0c03043305030705040f0f0602122508040b13060801080a020604090203 66
    0x1076080c040c0c859291107020440b40615a00d803a0102d0710300d80700a80c1031401d501140080302c040901901040141d2b00050364401c01d9146040c140a40c5101c000418051401e450021768184118001541070680100083d0301520080d01507030a90452446216a50030aa00501c50304164000009044071016141c42d2000c044480980700c407503005150091805440c552402400c5d444090905106900010980345031241d601c070a41c14200c4d68100808659442450041402882ca01c60350800e8440d034503586c050310100c1204c0d92183c1d44185000e036a07400c54001d1085011076039002c807801103118282c10305040e2200320b81c100720561190085403150806403109040c0201400042074000600000c00c0c058165070300342c180454607040000703250444030424407452441c204100c08407550803505140c04c0d40a016030105004105180c01c0075580300390741c0107415500c00441d60121408000c0100c208881c126681c984180c0d072600443c03900d501d61030318002d500c0a070800007007008900c039402565002 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 585632760 1250 585631510 585631517
    0x6021c03060e0906090f07050105070204020315120a110d1115040b0406050706060608041e0f06020c010507030e07180b03010603060207080a03140105130207050f07150801091a0907 79
    0x40765a07000441031200d00f50340c100201c1d041035040001c0e1032000c00200d83c040c5e0410b0300504e111450200041c00700e00c10180013901558000001440805115505442428020f1300b00c0c5050010150050744a02c9100e00c100c0d130741100469640d95510700600313940511504040d501c44039220401c1081256600000403e00711401404005007418400c00680024112030b12000e03520041880c01c101103035440d0b009a0244080321051001080b400610003d6146000e654004021550b0400300c201604072880109558000240e4020400d0b040d0001802050f0a40f803c2c003111510011241e01c0d23007101d0080310324114060b0a0703540c1e8036926400100a0a00180c000900c1d9607c0c2e460b0722060b648442c806a030751758000118148002e40c10300c21320b1000784010505030740d15410040029609d440c2218450203076600421640140070040c088140580301e1601210a00c4e0f17074801280000c40c2e00704400c03201203900a000020550304c9070003840903603140000003882d041c000c9410041d81c2071000c1c1011041 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 585634010 1250 585632760 585632771
    0xb011e03021e010207150203030103032006011409100311012a05010203011a030103030c031101140a0522120c03090b0a050d0608010e0a0818041107020411030106021c03 74
    0x150b156501c5401c1198641030280c4071003101e94002901d0100d040d4411140201141030130b81c011076010042c2c0341900c2c4c1c5032401d410252001d680006540d4104131840009004401c0001010450400402c1c0300300400d6803040e00c140c0d50303a009400442080e101c040c1c61840820f40c1c003d00d640c8201000095003200d140d01d0301e03021344550304202d0500300341d0300102c880740e500000500112a104440440040003801154030703643c1103940080c60012401c0004040c04201281c40c204a0020340100151050264040720030b8900607504c0000b905040e909202e030044581c1d107071131010741c901131001d250a421941440c1c140102400c111481040f1042c10307020043d0f000c2c00400c201c415240284004a003c1c0d40f040d440c2d4075071410709800c6910300d81c06001c441e890305460300007410000c110200302c1e0303810081c404d0300d03059052200c543c1d0423007010b0401e6106141080041210301c8401c09040d069000780c40030403144c001442d500034144000e008900250b4130800c07480c03501012440038004203110903e00400d9 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 585635260 1250 585634010 585634013
    0x17150c0c0f0a1103010b030f0706030518031305190303211e020301030606170a030e0f060f040801060b090a120302011e09050f070605090d0f1a041704030b011e03 71
    0x282042c1d640c0071240c014104990034040d190034042d030001d40324120007801c0b2440d81d0001c3e290360b0703954910400e018141c41c5e80c00140701c50b050503134045152200f0015240c1e03500d05480300c0c1d84a0300b964041e407849900284004c211904055085900752039164446142c0d801c80008280e01e1b010703101040c1c4038016209d00d003114400b0f0075019039415503040d01c2409a22541540b500b102541c01e280c00181c480700c1c81144261070745c440000c546112319014103191100050f480e0100ea600e074a04403195400c810000ba0101c00104104000e1003141d44141c000c020f5503813aa074803051980f1400006690184010178140f0650070f84500d82e40026100340000100301c03403040c0074050503900030381d03001c910a0381d02c440c4103090050900959000700d034003501500c000741c100f8a02410314012820041c1c01144580242c0c806c024442800a0045401568140200764003024111910400725030031568040b6401504840d04041d8003030b00d0641c0d90201c09241d1581c28104c0d16210703100b614048045080300b0640000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 585636510 1250 585635260 585635263
    0x3110d0305360304180b22180c0b0a020f0601030515100e010306020403030e04050c0301091a330403030e27090303160905180606041e17150c0c0f 64
    0x100a02d0a030183c080031401e104d036000211400c0110080c047c00703a45000e0072031442c2261283e541d420603150000740c44068160b11041440e900c950003001042141804101e4a88240150080c40c00c0c503800ca4210041420380310340c841000b884018082d501201200f0b00d800e4012580030340c0010101024543c1e103a96900d03880ca0410b081e4000d40d10154005401d00c03c0c903510220440008000303440a10643c1420a038640c16403005104c7d10140c80c0c0d58941c045c410800211850f0f86c03003034000300240c0180f0001003480e8030502e070320350748000c84a005100c081d016160120951f01200e4141c0c031500e420794428010300c441d280d8501c0102e4020210242e034814114845044c131401070f003242000310f0f00c0c1d00c3d05501d40f04001e503004010301c050200c0c80c44100111341d41c20011090382c090704236101400c1c0d03c6140c0480c4950013a07400c117001f40845484c0321041010900610411201107501c0340d5441034001041c5900c54910302000c5d103a0340040800182e910303003028000d0104407c1101103032250840d80d00000d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 585637760 1250 585636510 585636517
    0x150a2a0f1509020a05040f11030a0213150203070602031003080d09020906180a09020117090c031c08131704030303060905010f0e010e0702100903110d03053603 70
    0xc030355080e0840d4610050103216659059241100709041010071401c0d00029001046031058601c85c1e1307100e032907009040326141c009200401039041816224100040b500000c2d400c00b5100658041c44520009251000c3c100c1030004000340d500690301d03003a07440d00c3c1c00c0040d500050240c0f23840301e62100c0000002d880e24005112508601000280d030511500c100f2510380005880304d8491040c005042025285c00c0ca02d554025800050000c3c86400d40d200607603141c1b10039140c00b00c55840440410000200c00308a41c0800c0d0000c900f40d03000b00820350180c070b0050301c3c5865006e0018013031100051440e841d90034541c035600d000325030403d0200301c0b0940100d100d900070340003100060b8940404214041c000d000c1e00b8050240c4d25031140081d8100b4400e450410b1051090711081c000d09008a03140c03034000d0240e0724486c5002c0c101480351182c181009030540c2d1a00003800071900c0381822140d4550b202c3d01c2424062402c07150202c1080c400a4040540600341040b011081c0d204840001d00d004400c0004 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 585639010 1250 585637760 585637763
    0x8210403020f0c061314030c0604081f090804060305180303010b09040f0e03070305030705040e01090b09090f19030201020c0d030902180c0406201506030c150a2a 71
    0x1030020b0510141964142460055030a0007a003090143c00c5820000d001c100302034a9020300b02c040744145540021f0f14044120481e56000140000c020485220119114451a80c004000040700900c030410b1800c8403007150029001c260140070034001389110303030001a0031501c031404450440507680101c900f0b41c2d0003030744180d011041c0064101d40c035003024020307040309032071100c0d0407c156004d8000c032540b0b0748a03705008040000000c001103130746003d4010360b406001092001455036844088607001040c0c02284644070340c0b141d03000030380300100020740e00c00c2a00c01c0c0c034054240036007501061140c00f0b242071001c40c1555002d100d1180505001c124644280b00c007990041400c09650040c0081504800c480c03205440441c8104908480c50304201c800300c608600e001a0020f40720391b4020051104404202407500600003e4079209513101099405070b0300031025106142030340c00402c81680d01360890707144490740c00e214400310140a903500c16040020307a040145400c2049061120418040d0030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 585640260 1250 585639010 585639013
    0x50c0306090102130512060a1d030703020a0c050f22090b09240c09060901090b0c0718020c07050f030c1906080135011b0809010509030906070821040302 67
    0x15801040c1c4a6160040000c00c03058a4141c2e01030451b41da01c03a100d01c002444820401d403690b407103607032700341c403076074000300c885042800307503511a42ca0349402074540d9001c2105035000e040900011480c2e180101292211020052080e9076030400301240c2d914002561011004c41340e52500c0145c0030400c60307900f0703034458000d880240c00021161400c1c40c68014490340c08950401c6050104000c2885103c212654150102c6001d84c64420b42c1004079007517400354001c0f200710f40c00854600340003040094440705980c60080300500101000c0c0c0303020101c0c020307810f1000c4c1507400600f04002608010b0103191201901030103807040b24100d030f80400c04c5000c00600e40114240e0041003041042d5001e030005024101c00c40d8061a4100648681c0303503001c82040006215500040d4100c4000c0425031003524140200100b44030215408803002c1c00030501201e03040b85650812001408108012080350080f9000400c1c66041c9130254070380f880da9412819000d0211340400490700b02070050410041c1c49213110390b0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 585641510 1250 585640260 585640267
    0x90d06150f051f05030a15051305240d06051b0a1205150f0f041e060f1703030f0a060308031503100e0c01050a02030d090606060206070206130807050c0306090102 71
    0x509100c01c03490160fa4262082818a40e1406465408802c59801150428010429031340041c40c01c00e10b40601d60140303a2100c1e00b407001880c0c0f10815007155110320038100c03401c5501030450b4810350143c040403100e55404500c0005c400009901a070000d600200b6401105625a50000d80502503500c512001c90200701c0000e04009841c641d40035a907404404024030368a00a19040402c42a01900100300d104004540211841d0303103640d44090b003032510703088140d807041402e04c408500034552800f030a40c3d0044139000104800d151980e14460004104004529540d120b0138100c08005016182d03009203605d400f000000b00e1000400345008062407030000c069507840d4001c140c540350414800c006842e041495104600c0e00114481c51200401c1c208981d0b04c2c1c4c4074080403411840380c80d24481c0c900d850200980705021166010b503060f1000354080302c110f9298640140c1c1d035000111601441c0c0314080003154000b40c101e00c041d003040f52060701114415221580020700b0814112a4003403545e6020 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 585642760 1250 585641510 585641519
    0x10605040c050903071707030201201617160603020c1e010b0405011502060a18020312090405012103030b06040b0d0902090c04140d170417011a06090d06150f 69
    0x610140004100d034144900e46c440920034030b551584481e120180c140016110030314500072402200303108440c00102615126455070a4601c817024280c01103501d8101e10280160703030780c040090060803840c1c603960b08500091500800b02c01035401070034100c0e898060802c40041e0b02510303003496900130b450750001046a0400700d061000b00c0382c050b401181c00d4500a444150015000305803da00801e2204000c2481c10002c201543e0851149500a4052054215000c41c001e4800c020b000105000c0b40d051026903a03503804a00c5000d01c4e50b90304da140c0101c0800c2800003c0c0a5840329074007803800340c106030406d95100d903400d95581041c0da0b03400400352114620001c40ca092501d40c0e52000181e08481c1c106801c10750740e810b002c0011506280144400350742d59080c0300105e028641203116420350076541359120074a02005551540c900d01c8590300f40b08141c810b001d680e01c6819a5844054081400c00c80004200706a401d101841920440e039114440100320211111880180848600ea002600c0c5031 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 585644010 1250 585642760 585642763
    0x22e0306060210060530120705060f28060b03131202030309070b03090709020406120605040b01080f0415020d06030c08010902062703010518060f0f0a0c02010605040c050903 76
    0x4100c0c48505a850b0040c1408640c1d14480e101800b00301b90482203e2031070042140c85400c0380400d202c00c06512820840c1581044404010240365124100ba100c080d00d03001e044c0c081030001a14202d14103008060000c0c00c00e0f20007000946801031003d008204c079680d801c5200b50960041d80c8402d4084030b01e100146c140302409250000d1420144000c40c51071806100860f110b00041c0a03800ca54000003000c0380c0f48050412004010700503140b402c40d40c460350350002400c13032090405001407207400d240002980d4580b5200c0e10000700f0068403600342d1031b40c0d0010b03885404c91008208031134000c2041001c18a10300c0602c05068004400500000e000d811410141d0380740700795902c0f400c0702da030500380528016150507007030308e03410424000351f5440707002500d051078480200149041c0d01503190104001c00d00c034003122001c00b54200c480584015849034880860420001c844501e00c001c1e19801290301400542e2000c0d00106041c400060340c1c1d034845000506941d902c01c09031001a10200d0b00a441b442e0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 585645260 1250 585644010 585644023
    0x14010b0a06090302180c0406140d0213030b100812031e0720031e0c03041206090209070e030a0201080709031a1e1e0c160507080606060c0703022e03060602 68
    0x105c6100c8103003589040085901310348513071b01a10003042542ca550015a402c21825100e100303000100540d250121191492441c440d58401a211145d000c00440c00308056a241642640c4032040500300072000808080f10507030010b00405421700b00001820801000c910f4014040e00594ac0d1b80c0503540b43c038414440d046040e04d0000c8545070030411501c12031825081c106401000b140b00510b0b02d404480384000e0960082e40d102000510f00340348030004000d242d03800450807034400c88030099507840c2c03410208d80188046030342c0d6805610201c8080c01540c058500c032030348203c1501d0038440b996102ea54801220328919000c0c0104041ca0003030240f41d240300321310b048090b0b0b40c00a0202580c40c008200b030001309442400b070314001110f0000b1035809020b41045428854081c019807644000324a0726940e1500036104442c254000c2c4004a0b0442c54040121042d11000400030700542d803d41e020022074004080c806032507480d40660001840501d40050740c90180b840c0c40c002001803620501900307154 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 585646510 1250 585645260 585645289
    0x10509010c140c0a020906180c0c070f0e0a0b0f0307091a100906080403020c06041d06010203030c0714070e180c06030402370810060b031314010b0a06090302 69
    0x2e01403084038042e40f000100d10003101d030112402070444d241c103000b14107020034000a6000401e41d031307420482c4220341100200501c001407811900070310750380d42162401c0100d074001c4039566100302001c100c160401d034120100940d002061085c050f407548000900c0c081850303000c03590f029254403046982041c1d001c0d2001a0410540c1d9001d1521a0064000d10088aa0050b00240010f15000c50f080c035108000700c088203100542815620790f00c0d1201c840182d00c20305114841c4e003601710700086a0303500c00b0007034901400c0100301c0c4a040012310b5603110032120040d41d151505219440000400750100c02c407541c0514240d0000001c1240c1080f001410800070307014450248408205100c0140c8035240d1502c45200d00000c3e11802040c5410005980c42e076a4101c000394850140c4d000c501c140021500941c00644000b04008056807003d0001807408101d41d10514620100304403008203100000b0140900780d0b000002907000304801c0010302d02d43c10f07038204c4000034100700b41c24400c6081940c00d40b605107 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 585647760 1250 585646510 585646547
    0xa0507121a1e030d0c0303020c1b211b0d0602040605120a05010315050a2a020c01091a0c030f0315090105120a030e010210050c0306010801051008071d03010509010c 72
    0x126001c070301095a445003141ca850820201740038000a1506c60742c103541224000d001130f1240b01d6104105981010400030b1028412a07500c80200c01c904881c41385081840052409804800d81c0c2648002c0e002e92900500c4e90840d013041c24600000d211840100090800764641c103844068000c01c202c031071071005040c2548036103040700500c04215102031111800701201e201149a940d0f0820620240c00c2034040804031601407140008030006100461f21410055422103038094581801100c403000203200c0c0000704840030300e0030b10814034030000421403114101c08803071504011501c510003540c001c41d401c0d003403080034292980704d074a03103802220f0040804807404540b125903204429128503007110010240009482901c141d64001e001e5981c9104407000104002d01d031036080c400f00c55108031520790008030b14000202c0c0031b1a02416224a40e0328940d0b07000c00d01c0e520140b064805440c07a011520146080b103940c0201580c00b400707242d05c00c0c8082000460b0f03144440c075026210110034246400c96 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 585649010 1250 585647760 585647809
    0x50d020609100908070204023c0f030903040b0c01021206040c052215090504180b0f090703020604080a110a05131e05040b0106091a030a0507121a 64
    0x6801c00025034151a0038184000a60b40070b084ca49981c40303116076a0020340181c004215601d8102341c503004c1c00c00102c6040c0b60028001d118100c1e4402c0d000300d5030350070b1401010511401c0c40054005000c1c65000880031b040724601174807401100301580110f8880c2d5181e0f9000141103080070398620350aa0031140584041c0a4401c80040240141c0902040044140c1c064600002d840c0306a4904400a294800307035032001c048048030007031a41c442402410700460030040c24005464144040f080581d40004006a0356205c101100303214050142c185030580c4a0001c0c0840542e60350300040000703011581c01000810301c546000d074000da0740c0081881c4a44110f417000c0000c0c0e03c071101d01403152403203400700295401035840c028107000d4007811300141443c07601c4200001c205104003840d050360710b66190300395030560312030440035001000d03499181c19107400d0010400200d2150022500200f9a08006004180c0c0c60240001c90b08818440c10380040c44c141905100c1c10320360310349480007407480701a01c00c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 585650260 1250 585649010 585649021
    0x403030e030a090605160209180613020f10030b060d050103030f0e030d0c0203071a070b01090516030504080702130501060f05190f0c0c06030203070e030c03120c010608060c0304050d0206 82
    0x200002c920603a02031250010f06610781e001c0c507511b41035105a0050008a07641041000c80c100040b0080b081d20861007054045040d5141201030b460b54a540200710058100701a030a00c16a2175081c04100d00b1300d61104900060ba0f5180409440441c00c0da40b4009140e6166080041216401080e071000340030100040c02d40585010906001300c01c4e0342c0c101050f46030b846102103807400116a0180c490307180e154502800d40300303021004190540c020550501c031640c85210203811a00141d500045514003003450401450083d0489036000340198219400c001050b00070600b005803000f000314910b41c0d07920045c3714540d04141e0140c0003a021340341c00c41c2000558501c580340742d07007425108020710100702100311400c1d21a4000080c1703141c3c411600500250b0b034060280c060340064900401081801e0340c18040d50070000b9220ba08100001d005000d60b12181d210308040e42d00c00c11a0000319504c45101080003441006603030301501110310101da4a1a09080807030500e900c0c401c0110854001c0c005012 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 585651510 1250 585650260 585650267
    0xc060c021309032309060711030d08220602070803070807090b0a082e030f02010909090209060f120d0207031203020f1234080a050613090507090908030403030e030a 72
    0x3042291104e09101444150b007190320440c0542101d46502c800f00003810401c004408510360120141582100e0040c024000b0070349603d002121242e161004201018420a0324046070a01d454010b140051400c00b046e241c5c440260301c00c440d014046000f035010b0080c803a034001e4680c0c00030300382c2221490030004e266600400c45203001e40003110080000d1062440785000b4072102414840c440b181009880d604e1511004440054406a0100d02d1810b00000c840c811382c0524890750b41e00400901e084d0b0354500c00c011254000403a40c940005070740700310f03a43c0040e080010346e5421003650020680c05244d4039061007240c442600a0b0101401032100c12582c00070501078aa0700340c525a880ca10303d5442c2642d00b565003ea0b03461400d0a00c0c1000450b088600700e682841c80d1841244e070740d044443d601d0184c40c0043e6135041d51200e811850f0750300310300c1000c3c2250f4040040144104180d4840e1582c9002c07100659107e0b000640b840c1c031001003800205a0144a011084074608001e50b040052403203002c2e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 585652760 1250 585651510 585651527
    0x61e110a03080a1b0908010b01020604020a0506160204051e090d080402150705010207032f120f0915041502011512020409120201020a020705040e12160c060c02130903 73
    0x10284600070b00820711a511030b41154502da24410040200818114001042204644034110141d4a0310000240c0303540f012131014803e680103071030041d4047c40d040c20700a0a0f4060f59002c04100c081400d0600166201e000d658042c044003004010840e050407103045072002d01070700700c42140c1d01501203013103000c0c1c00041c000d6009804886200c83c640c1850f9a0000310b129042d1300600e02d500c00140c6a080642000b001580000e80f000a010021422141040c0d0f640728002c2d801c103d64040713400000d00740c64500c004c0111035884000baa04008000b400b03d00c03a292003e414120f4443c000ca8288080074a482c1140141d100c0f40c4028001c1c08400c6c0f4034800350000034002c1985800e0b1283c0c0441c10340d11960000d14a035603020350708900700144c480c0c00138000e40000e1180783c014042d41900103072610b0140a140c541620b08405170011042d5500c3c003001c21b900c0101002c0784464013200718008500540c035040f00500c290b80754200e5101551040144c110000011290598901429032001c01d6004401 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 585654010 1250 585652760 585652763
    0x809010e0138090c07080421030915020a11041508010c08100e01091107050a12090909050316060b06071a0f13060f0615020c03070e070804080a0315061e110a 69
    0x3c10340c2c45c2da017402c0418031845141c100d07110a044188a000508000e07003801a42c60707001e42d56203000f1580314036602c00c24910070540940164462081440460340d910790414000d04000e00002d0610801c010764003003101c5540c01211581d655200341c00046030042082075000d1184003d01c18201e00b0620442920941170041d141026901e00c0d1210000f0005803c840400e6088070032569441001d162003401d9811b40405e403000070344161800142d034001e038010900c08a60000c051b5007483c80f00301f0b8008990300000c00540c0c40a03110310708010640c580c0e0009181d101c0c017a50341391403003804190507010f03034000241c03414442c80030b0a4100030003480e07001000004107a01c000d01207414010b070b0400c44040c004070b0300441c0d091020450760940180c0c00207000440a50141d00b1b55000c0c0d981c0b10f104c8802214105c40910108441c98002800207015400420307009215050014452544280042d2010202c0d004a80460f0b01d4030a41c0e4900120190042042140da20f07000c0342c031280c07890070181c85010702c0702c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 585655260 1250 585654010 585654031
    0xe01091406070611030603100b031009080d05010b4512010c0f031d2e0f02091305071d040209040908030610021204060809010e013809 59
    0x30203480c9035644011500e485400c08070038044c407025070600c034450340c1c4143c0741a482403007449142030011017240110f000021004000d0b200381d0303c41110000c041c10070500102e520500421800d00030780e9891043c1d6010b4030160101e140c864408001040214201170241c8003248130350480541d228100414025020300d000c1c55804600e008840030552008c1c1c52030407440154204a10502c00903807001c0c00ba88400d03940e56092100900310881c1c012030101075542e110041e0041e07411100400103100442011941c60044200b4405103502d0000071940c44000f001403154000520307031320500c0c0011500d14055540001041142001c040140003a51303d20540d00342d00d01c2403140b404c444e0b6965815180d05200191090062001c986000c048980c41151064400c58540c5030143c06240700091440c02c226200310742514281c14508281d513861001800030f04650740f00d80300305005c0c05082c017400010b01c042035070304c0c600d0110f0481d480561844040b0750a034104015210214165201c10155401440180 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 585656510 1250 585655260 585655289
    0x20903010e100b040b120a062016170a0906030513050f0106030311070b04030303052509030c0b0c0303040212070e040812060405010305031b010b0d030815010e0109 72
    0x40400d0150000801207100c0e40100a00e40d4041152900f10700d88241c1c044504110b021050f00400850301204030300348003141c2c84020150000b42840e408600c0c03085100c035400c822407000c0c0c01e106410740d21911414240d607441c80054400c004401c1220890650030101003410503503581c1000301200418400d900130940c07102c0100e15454038041d8030095840e002400e503a141d00c04401c0c964007a1950740300c218000b80890300680c0d070141c0042120410344a15807022881c05141d52030860180c44064610711900045101c04410380d40418600d00705c141050310b41d110010b155051009200101c0e5006140c0340000b0411801a120301100301c0c1e078040d82c1101d00b02043c0071290a464500700c217a0300400360100850091005014485000e09031914000715034401036030300c4034140000e981c028030008007540c0c0f003400745080c00c1d080800d245001020880000611035107c100140390f40080d600c007a00410206000c1c00701c3d014562a5900c0c0c890000c2c282040120315410000b084138400707202e038030a0100f41d00c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 585657760 1250 585656510 585656527
    0xc0c0915060703090e0604020705031813060e070809010203060a120609050316050f032703010e01020a1805030a080a0c05070b041d07090b1b1903090e091f02 69
    0x1210480480500940541d071122680e14014010114034018041540ca205c00045c2c0309203041e00880f803c42c1e80c0a400740d410448500c6044096407140c2410f154425410200c1c20108c90a51060000510a0003e4003a46080019010741404c0d00600205d640b80d00400401005450300100e050031038000d14040583c0000904081d4010010362100078054000002c081c60b66269007240c0d001d03030078000d1060b04d1a1200d24002c1503903a00c2501c44060303038031070500703600800c1c590741d42c0d03401406120140004c52b1b502c007224609401c9034800710340031000ca03049050112611840205074006024154010007262035944c0b10303c0458000c400c408010042031a20030020403105200000c020084c64002988075030300d81d1050074900361102d0141f501841032100040050b071241000f20203e031080309800e403510748031416921040f45c56a00b0030541c0e2007044890100c98120b0003d0803a01030003039403130090f1642004c82105440b40e02500000300ca0340301e0126521001c1581c000c840040c0d82c1d1800041e0b8135501c5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 585659010 1250 585657760 585657781
    0xc0414030a0605010e0603060a0204061d1903031d0d020306040602090d1406010e0c030f0615070b042d03021515030f0f0601091505040f060302090c0c10020c0c09 71
    0x4518000c103103d040c540001110f00246544078026101203060b42c40541d1200c8071402240143c2c0703d1940007546220002020842e0044d1009609001828081100440e08070711890303811190303c12400250844e8403104511180d044d4042c064404440fa1a4860f0103500001e81d20000544003404c0b6550000300390807203507600c89441038110f030312850110700a22003207a0f19484800910440d181e0500300400078280e150300200312440346e03095208906a6803500000d00210b200c2a40c005104800c0400641010600540c280e61003648600c044150118000ca03900813280d080c00d140d1001104e4458458001076008255151514896408980140d889051500d91036000d5500c1e03d4150080007a0f2145506002c02c840c008151404125107451340c3c0c446100c000c680c5070702c0c0c0b4140d404070764510074406407030150000c104500341d5140c0400c00da5200d03000122114030a90f401d1045000c0003841703518094041c40030210346040c00200b1803c1400114250b5204c94822810030b200d0600c403400160f42d007e6 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 585660260 1250 585659010 585659023
    0x4060c030905060f040b070503040b160207180501180e030d150e04121812031101020c160e0f04080304080c0a14070509100312140415051903050c041403 67
    0x20058211043c504041c0f55001041205075000d5407100c000d6000900380a010703000300ca01440d401604044542d0b01c071070400d44080342c13240c1341d2421402040350001d2142d1400f50001c940b80081d000000e49540351815400008010324a004441c074180030241a4a010203c00d46101ca18501400b259051301d64598280c0f012143d004a80442d0600c0c06000600854030345820318092142c485078800f0507421400c28601e0800d104034041c0300400e055000000b481800a8050344884000140c00d018031050340c641000b03c0803012a00906841208100c0d929402c198290400150181c808060400e9190364107644801880a091494000342c0e010b02c0910404c02c500d1000c1c2c1001c070718144003400c8144c1589031402031040900c0b130882030012818801e084c541110440e0b5200020f89402420a1025140c0200ca1180c2241070b84091000180818079011000c000e0400f555615075184415010018200c508109030400c0500d443c0c01c0041e1400b0480840c2e0949801c00c8114201c49000ca001038038294 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 585661510 1250 585660260 585660263
    0x31207110d030f0b030105040b0105011d030607020309090a0b0f0609060c011416030b06190c1a040b07050a021e120c0102031509041208060a091506080a0b01050304060c0309 76
    0x30070180540c000c076a15034400482d40c20554418016507800340101070913100144d9029168416203c0100131640c0145a2120300c186180003801400c02c0040010741080310489100c40541c10005044070145801601642d0140341071004001001519001c04c401c0905103d54030300500b40003990720031a64803c6c040c0c0d003400c0003020003401031032101e012001c1400f009458951581c1450b0150791885402805865005980908400d0a2140005107000304ca240b0030704810501041a04903000b00300f0600c2480300d10280c0e00100d004070b040600e840040344030010403035420414240f018100c074a6003c5901540f01c7c10b119100340e04006151603985c10954100401012281b000a02c8036541906401031480b0b17603074952920200b041c2c9e02c03003071000c000c0040390000c028410800108242c3e9003d00303c01038000d03101511b02065142c684174003604440140d8a00300e21480141c0c0c3c1081a15800b011940e0700607841003082c815001340c02c00103001e40c0005840103152646803040c0001c00c2c1d2007a4011003070356 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 585662760 1250 585661510 585661513
    0x3030a1d07061427030c030d08190213033e090702100906060302030c0a1a03150405070201051005010e1e04020f072402070c0b1803070611070504060803120711 70
    0x1141c919444c3c1030581100305950340031303002c2c0f20440103440c5804a40d441809007a40c03200031183c2e40d0b1500d03100c1c41d020021004c00340e4503424400080c95480c41c0000b400038600c9203007412821403d10020f202986c21038011100026803411144004007803a84042c0c00914060704d002c030b12616005001e034141031000f040c0320b515a1814200302d0030310160f5004841241d0003502518854494041441900c25680c082d018214951030440e5080c164840c004544c80481c040e10324080e40043c0c800241520016100c400041c1c0d1620b0a00c20314040700400742004040034244240c440c803c03900410240c510044244000080e880082825500c07540c044412019403003200742d0ba01ca0951520038041d203209456042414100c240c0a082010b881c400c940c00503800c643c4002e02e0703900d48201c0014651265150544200c0324190000c0152410400480a40126260b4007403111089020928144181c1d002074404c508246040290510100403242c81052260400c811641d41c1c042c1600e11050b101c0071040c09 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 585664010 1250 585662760 585662797
    0x17011202040b0301270309091407181d01140f010212070615061701060801030503073203030a290d1a0a020d0f020702090a18020402070503030a1d070614 67
    0x105e0044d1841020035034400d072100c43c2034940741c0c0100f000b1503599110303405818440e68003140e00300d8040e55226807954480071102c22041c5d103c0b8003120100319000e52594408200c0c000601c00c0e84070428081800110598544010144c0003000030360380c0d844281c0070605000005000002e01c045a00848806c0c1c0c140c2c10a5034007581c0c0e0745d6004003115041140a03007868043c1002003220341c810a007240c1200d1b00080210304003805500c4103040d01c82a401c2180a002c000c500d210034841c0203840d42d041350b00032400590384a1070311400a005540003002d0a1076055583e00b40c4501e011403000d91070500384000e80d180b02c918402c4e03283c0030250f140c0340380c0201000401c203000c1004000d56500240450a8880001d0115070a107401403401c0e40100e450080d030004c1c004000800000c115401041641804d07010701278060380680104003281c0c420a01540c60781c0002080140030304541c001c01d0030b030740d08440a10307844070920451a501c0703035200d000700c03410000100742c86854549140c00350f032200400c80c0402c100 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 585665260 1250 585664010 585664061
    0x1a13180908030c0c0106060801080a02040203101707060906030c120507020a1b0501020106170307110f0409050102091005030c3001060c03081006091403010615080717011202040b0301 80
    0x20f4070303084000c036001d0545c2080341c01f040f1719202e042130303034103e44100004105d0001c030340d0708100283d0401401900840e000880000b004050b0b6111300c0c8480d00d0308000f07011100e0901340c0042010f13a181d0040424903062404442c4034641c0800340c0958050408070004147d110244c04a0600c6880300d00900814440000e0509220f109401c4d5012240f0907002040b285075150b242c002c1c0200c0040305038061350000d002e84d801152510322480c1c2e100c0d4008111020f9500c0c1c00d00041d08403040c828055680da90302040c00922070900d40014081e0310060b0601e01d0135071810483c051541d1003900c610180045903158a01c1500c1900a2509201d0304520781c1c034042036031200720081080941d600181c00185902e008261140224951081520b000b83da404070401e0034100d1100380352081001c250307019942c4500004425890180e100d81c00341e056a241e1002e410042801400c0030020b074100c00c3d081c41042d00400c07056070600300558210f42d0541c0c01054a075651400280140007107006202a001d41048030350 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 585666510 1250 585665260 585665281
    0xc0c0302032401080a030e040b0a0e090703051002040f05060c0a0b040b0702240610090e040c0501090815073b040c030905151803131a1318090803 64
    0x403120b112103070907004540e0342c1e0b036082903807102c580d00007402003214030700042890b0070940c201d000d613205c026110340901a81d50a1a02e8248800c890a600d682c010030001d000f0041c09020004a070300351487c0640c200703800d0055071900c1441b42c2c07045030320458000031711b00300c0800c090000000300340d00300d80d00c0141850141850002e04078210f80f0000180100c1c80e07c0e4003c41601039080300701d0f0454140c4109907a495500340b1032643c001105520501c070a00e440000d07040707198a45c462046100f080701e039403c44d2606002504e126410b801071001508102c1c031f000e0200d12190a20b0b5401112445c200e4440d10f000e07074802003a0f400d0b2040c00c003110018142c003c1c3e8039080081c2c0191040800313903020425a40401011011030301181c00082c181c0c1c021104c02c0d515034408100c4103070006030404003084c0701c1000e29106403455010341e900c95407001501100304900c0d10002065a0901c982e000a0f515082d1420014048582c481c05100740c82410304c007103034445010759806a01c46d0740d401200950760303090060204 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 585667760 1250 585666510 585666553
    0x11070303050703151502030d02030411040605060c210405120607090512060402060c03190e030709020429040b0d050f0c04080703080a1b11090c09010c030c0c030203 72
    0x19404281040041040c00388a0301c10f01030055004489440e40d542891071021110f1400b9170304604500c81400509442c44071072000b980110720403203040300100f0141050000b41d43c1c5550110340f0554091122200f1020003240c12004c048030000c030700390303180410b42c1951800d000d10380029410071201294003c4a800008550380100c3c155102d981c20b107903490041022068800c441107409030883c8000c5001810540e000e04171003030751042aa8140030200d015540c802008140c03800014080f81d0b183e041c01d050510070780c0013030907030140c00b50f1034181080c500c02104200c4e04040d00345000b00c402c004007284003560a442c081d00404001ca641e0306000c08030000505400c0d2000503059044102184420900034100d504441c0c00c02d020700410341c030b5500c58070019000385c1c07a00710510100310003070003240c0c80081250445070b201e1031114016448002c28030150040040880b0710700207013001009226138004000103246640b52a050100e001540741c2120b0382c001d1a40029050f100b100700c000151113071070306c28 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 585669010 1250 585667760 585667763
    0x1e0301060809060a0e0a08090a0b071b050612060904021909292407060203010e090c0405091e0a0b0a090311070f0b09040b03060708161d19091107 64
    0x2103c200d6159642ca1030112042100d24405640c0f02800c02000186000090200280c1c010010505280d58a5100c01154005a0210795071440111114038051600d0403a00140c0400d41e0003908024090f154914121005080c00b845a80c01d80f0001c1c00319030f50910a03640b1354400c030212406265a84505502506460030042d0310819466059500d072034040100d000d400d10020105800d079640d4000d40b145074112003030003501c000420411040407404500096000301450101e149462901c91007070b504098191701014452405e007400c3c03180408000511000c1124000402103100c6090401d4518201048100403e240c80c00d200704200c5d03040d84e6208450003402511031a01d00e403143d4039401d465807214060030340c011016440038800000b180001d040003030000ba0000820701d0303810001a00c0c180c0100c400c1400502d541082251122000c0e40310549100b140c1004c4034114113000b4804c420350901c541090203504800c44201c140c1c0c40c02c4d05d000006101e001d2040000780d100c8841e0b003e0740e074842c0b0030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 585670260 1250 585669010 585669013
    0x80c0f07060f0501231003020a050403140606040b0103022a0309040501170d0c080a050d06170a02010306050a0e010905070215090a0c1a070f0c0510030516050408030f1e0301060809 79
    0x500d140303040d8002c80c008480c5d6400610003d84000e803e50107400a403c0103803910204a001d020100019041d5407283c49520040d000410302860b01c2c1301004156495160607504040c0180f12500814015010045d120300324071040d02c9070034480013071403480c6000340ca07110b550160900000040c040d004040810254161701c050760020140c1510507546000501401440141c08111190b000c600c110003601c11035481038004244640c0d1000304000e080c2d91060740b641e55400c00700d80c44c03045681510452000b88400e0700e0740503100d8505040c40910007414071401807080d03200c1c030010b020103100340103e0405880d40310440c0b03298103001554580d50032190341c0c120750240c031031040402c510500500504d1500300c030f01390b500e01e414840d941c6e55a100002c0780044a401c5000d442c003103865a11424840488a82940c0001d15460a4079002e007107103880c1c490000910100304401d00c2022008000c459040104200003580c503050864000b8611900c1481d04180c12030101c004030b081540050100d0003064401c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 585671510 1250 585670260 585670289
    0x23041707050906030303010306090203120d1a0103180b04062a1106061516050f0c01120209091807121208180d120b030f15010e07080c0f07060f0501 65
    0xc0c140480701c0b6056441c16032540c02400100005070140e00005201031002e000d0782c8102188640213060368008c5842c54a02a4440f82005401c407103003108218010000d00c4c05201e10107015225145200d09034401404d40030035040018140020398009180c10081580310031740071003c0358610031260503841102d1300001c00c0020004803180d80000c03002e005420090210405002e0440505843d038800301088800b004003035806004a9020b2203640b5814400d00080c1c19220141340004000030002d001c5203210b80e10511011400340c036241c0344154400c40b645001001100940407503480c00031258081200b000c40c3e605d590041040c1c0342010307244107001e9150803015845031030346800130009010100d0920303400806009003282c440e81050820f6014110b001524500d0f0340042030902c2801071144469600920070843c3c290903640d01a40184a624500403160902c40c2b401000500082c100345400c610114588040e00c1407903040f244055405030040040304501c048000c003030102480388000b00030100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 585672760 1250 585671510 585671519
    0x313060905180411120a0c0602011b0c0c0e070c4d04050c040302152109070504110c0313050a0503030405010c020409030224010f060e030a020123041707 67
    0x74030b903582c05181c2c051402400802542c040c0038000500600380e080314451681280081011650340030060600c50f4004030b2200c6008414010701030b91035004004202d0014034880200b001c4010b08000e6500001010040d40c8070f1660032a103950b01254013514800816204001103031100782414001149044d4450102141581d442c4a0303051840a000d0075060720124080c2da07251582c00150302480300d41049050580700d4000c280e1000d003100b605803c1c4100014020380c116080c50010b010701c20440050103d620f0300d4401541c640003248038280c0a5034803031031055026107501041c0c541d28a001d0701180c0e103036241164285081030031449068010310301e03c0d801150905000c0111816100d06031940c5100c80e62560038080209948141070301140151800146110345072110760000303d228240d06003c0c1d504291070b044664180f680224180321240d41c0300382a580b004038218481640900b1f00220003070400355800b0811003446440d0710f40c02c1d000100405c441c9401c801d5880440c018000b29a1019202c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 585674010 1250 585672760 585672799
    0x10c0e060a08040b06060d0e0c09060906280b0c0102090111010c09050d02190602060f1e0609040c051f020c0a1412070e0a0203040506070f050a050c0313060905 70
    0x1c100ca03590004210710001000f00712040350b12604948003501141c600241c1d4450001116020b110500280d000000b038090320345081c4070728a400c504200c0d401c120605000d000589400d40084030b40080c4043c0240d12000c25600705050070007403500344262a683c204d0034142034002d62000100c140440d02d115615a0507131014403c0304034a00d666241d40490a0400040012032544d03c407049070f01020145ca00c4407103100a01d000d500034a41d50b001000d0504040800c41c1c00e00400400c030743c1c40d13500035046102200d80c1c0006041d030000801d640e0395146442d50306000340c1c04942034010076006898102400c40c003007500c0b0400d0380c2d0650a0340c00d40b08406043c8040054080fa107108501d00c01e41403070700d01d01c828940070303403600348541c111310441d403000d81c1e290f201c80125403040f502c80c082e896010003000280a0103100e82c0d68051550b00d40180190001ca0f00508240159608101040008035801c0070800023081101c908040082075542d00594491005040c11070500556005c1c039003020020804560 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 585675260 1250 585674010 585674017
    0x50a121b050c060904020c01060e07120504020a060c020609090f2a0d020c0f330603120d091e060c1803030c030903020607150b1512040221010c0e06 65
    0x140000a07020842e00c0504100d801e4102035510380c0d11550801605154001c03d06c502c0340100030a1003034403590f16000c0070241403a0b0345481d0341030b40da6050604010040c5d4608624100390780080c2098480d140b02ca001040b0540154100142c00007602d406104030113207202c080324852a10644212804074812140700ca11a1401400c074a02d00b40602c14007084c00619006040c52108410841e540443c0c5851120700c0e0008200c0f140d145840c070b1a50032009003840d101e9029505d900cc5480028600303001d0003086d03480c0c030141001040f120000ca03040030140c1c525040081030707641060107032888142020890454030340d0600115030701c41c035100f003416004e402061940b01480904600003051071860b2001e848021080c1421006c10060440100040e0344a0020744000780c05840c4420801c251840008200d81c002190684225440701000d40000b0b101402c58000c1101580c041c8191349a61000c1144150301032a0a220b12034040009101214154020300040d9070580d2902651651403003404400c0c40b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 585676510 1250 585675260 585675263
    0x100318030e030634140409060810090b040605060a0b0a02060a0c0206010e011e090603150b0307050d0f020a05040e060702010605090606030106081305011514061206120109050a121b 79
    0x40e194403000d00c0161022500020202c0c0303405c240c1d04c014049590043c170b50740a40c00000700940d881d0410f0140580070020000610041201004480c4150715010b40d48030000700b005001070303200d034001a56500c41c414540e008241581d41e0507150414030001135125401150080402403800d02d0070720100380f0010703040c2e04a0320f0040c2c08072290f0f42000350314103002076000f8034502c1e1000344840000760f540031031050100441c0100700e9640c51a0190f00e018090341d081074035040c071a42c010f04080c4020760307a9600c0c1140c0c1a902141307540d0070b103016101054048580e0ba000700d92044c907009034032101c5900841c1091003080b480c1d000300050345d281d4040180c070490944a040e0800740600050106500801d4415004044401914010281030b0f40307031401e403080c803440c3c9048091042c07810041e07550902d00c0c00b00c003800102d641c6800c2a1640b6000c0b1140c00005021038862900591000a444801c0d4851039542e0b4025042e65482031581c1003045821100401c0080024401044800206000f00b01128001d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 585677760 1250 585676510 585676561
    0xb0901050412080915040f021e0102073b0415051e04030e10030f0c05030103050c01032309070509060405060d06050603030424021204030b0402100318030e0306 70
    0x3480049084032603c0b002414145140300d8881c10641e0b10700361090041c0b0551041c60b1000343d00c0d80714814440107000302c40c0c400c54041412114100c29030780129814065450140d1800c81c1000c5c840340311012018209004e000b151214400c01d11140000d00286105902404283e4800d0340119100e5045500c212660740d284458441c400701c2005038a00c0c01030b00309001e45081044041c2d071000156800016050030320120f030341e07121300b110001c110707003d510000002070500509641c51512800e03102c0450810700b42c100b55403240b03607680c1c01c0c0d800110750141e00b841e00c0c0c0b0300042d803130045001f0f540c03015a40110340c4218860760000e00036140c94082c481c403503a80a052144c10344810354690f405004040c1c11503500d40009d00003c160400032861001d0351080340024814610030780d00d4080d06041545c2c840400c1c03260100002d10116100c1c0315602d0700658161001d80c8400d000410450041c000e8000c101001c0d036415030030105055100c00050290070044040d00d42d82d8580800d5202c080038100c0488052 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 585679010 1250 585677760 585677783
    0x2d0c05120c0913020c0a0c090c0203160302030408100603060b04020708090906060c010e01020909100e070e011206080f010606030b030d1202090d0b1806100e06011110090b09010504 79
    0x1d0903003035000382c0b102882c040c0810b4005070350802c0030000e90b040340e02d148102c0c3d8402d401714400e0048020514005140111080102100440000391a0b20808003440a10340200d020101094804c00403035000701098130680f02c0252000010402407d2a4417090303501900b4450003400030300e4107201700c0741199801445c80d0300d03000b0700c081401001e00c1e00a1515030300c04014800d00c61103110a000320000040000001680e64681c6010332000d508060440000d000444006002030000d01c14500c0c3c100c1110300300010b500c811500101d55814030f40b106100054101100000d00d804e001580200c0941104001e01c2410344515085007103800b0f000005500d540100088180c0c203010310355120031b0b008400e002500d0300e40b1030808510494002203085807140a40c1c810801c1050210b001070b41a00c18420103006c1d642400000407158540391b004800d110003035a00481c2860703008881d40000c027200881510251030342030200c400100cc4025040e203c0140c4480014040c01c4c0603c1641c1c8510351010400300b1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 585680260 1250 585679010 585679021
    0xb070f170403030b0414071701140105070b09120403030c050d0f02030a0e01200601050315040201200a05060412090b040302030a1b0b0705071404050f0c0d2d0c0512 72
    0x1500302d805001d41c02c17076a00c00c1c40705400050300384c4103032103906962074109100d00c070b0303880d1981d00e400140e00034160103003034011844040e80c1c030400f01c0b04616000940101c045d211b1b01d0030a42000c0304c040a40301607240000d400010141c010070384140d618050019078191082c132030b8056810100c0b541000005030010041c2068aa001e0b0076540403041d412700d0502032110058006501c1c02d41020080603c0c0c0c0c0c482d2004104500e000c1010703070701542044420181c1070034182c0c0007915aa40180d000c420500d05550075034158001001006450364005084070003a08040c04c1560074041900c00f00710029000a0003c00c400025804440407268094000c1040400b546c480701d400c0012407601d00756107144540c2c001400100080500885030103403014006540c908221a204988124a83d900450801d420410301c24481185540d0041150103031503507514100709502e004003210b4001d07100d081004245604481d8088440c0781d00c5070b68681c070812101e04040001d40c0c040c01042c10030140407480d10300188 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 585681510 1250 585680260 585680267
    0x320150f07020f011e061509050907050c0d03060314160b03151005250f11190306060302030708010522110d060b041109030c01050313020901030b070f170403 69
    0x40d400140d620544040143c009a0a400e4410442d51220000c000d2503110f8500c4045200700001410340e0500804540e444900150440c001441502e02c9100304000003608140200101c2d4162078102c419140a4101044040e008101c1800181c44580301050210a40700001401c046840602c40c01c0440291400c407040c00c03241d00051680c50707a1524a40c049081e5107884240030900c6005499845d141c840c281058100504070028072860a020006104042900000582da046410903088100c91401d072021440349401d641050008480941e0000144001d540c0160140c91089007075900c00c6035584041401d8442c1070300c50032021055035004000401c10303440300f4045c041c411080c5d0542e280c0c0781c80c0010710b1140201c5042c0c807925105c0a8a228514191040c681c2c0004242a4541055a800e0100795208840c0241070b06001001000c680001c20b00c000b244041175009200c08039035030f103170b24160f499107506444c58070100d8100425250018098034503500d40b55031503201c00c079041c4d6803910b084 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 585682760 1250 585681510 585681541
    0x5040605010e040f1d030a0e101b0204140901060509092805070e1009201905070213090314160809130c090807060908031b0f0703032015 60
    0x502c80617074640062044a110b9a2001c1d20000013101464841c00908800760070300c0703020541c00b40f0a110720302c01802c04070f401100d1034074920881803c0d00382c00742007032005c42c0050840080c4803840701892000c200e1000415089001954010350307c84400e500c0d82040b003030380c0c0c014030918044500b143c80701e041141c80b012500e407006035020704100c541c1d2680c0c46503480410f20080c1e50136001503d241c0d00c217104100f058001e00700c90b9459203c16041c104922a031079001030240300900481e0320b00100825900a00c1801901c00b03150b001022464000c41420269004040036101240400c902c0c00002142c5000311081e00c03d50410300c40c602050455650341c909a0b07521281f003c0303510564132810084a14020705c1451102c0519454802683e41001035007803501f281544090104540d181c410300c1000d0f40842a1610007102c1b00b00c7d40740840010140e40d0500030301c59448590b51003803800c000b0500d6032024020a000120f025141a22071001c2c10aa80f41c1c041c105a811160404e90003146080d4a400340e071 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 585684010 1250 585682760 585682781
    0x7020f03030f12040303061e03060203060a091404020108010f0e010527040c0e16050409181502093c1f050d0c08100b2b0509010605040605010e04 64
    0x3500c2c500030300040b208801c3d03003201d211000c0c40f284600c01c0004240d010711070b01d0b02403c0711480300c1001d900010801084141c043c00024031440d00400825102c0d00d480040c80d003e0f0016520a004000c4e0b801c40d142c10301034080350140d0000749404000540f5104010402041e08c2082082503060786c03c0c0418840d240304241071850301c2c0f400c900e11200c455039121045900851090720500c540a00d05001e2600c84100542030914403110003518100c1250820308039000c48905020100b540100001a80014101c1c2c61026103d40090f035140300001c24140c1c000c2c202001d08854400e4814480400350f404d11441c403c1d40701d1001200310b000341d000c15070100e107a0042c2600900021101c100c20a49060841e07000d0801400720342c002c5003600600c203003070150741422140c914100702540b03803041080d01000924482c140290340c001030b0308404a02c6803103040980c80d100c010076490440c1441c200c1300041c01d00312800d040c1c2d5480e107800806d462a04d03005d83c100b210816540d8514420002c000c1100600d4086003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 585685260 1250 585684010 585684013
    0x6050a0c0605151f02060f130303050c07060204240c1a04020a0b04180e19020d15050f010512060c2205030106030506040b130305040b0711030105101403070b07020f03 73
    0x1621200e580da40c850390416002c03013142c803100042d20320001a1a201c400345c400c8107100003a0003001248061704911480c20364040c9404146511003542c00b000b01d00c40c030788000d0b14660000901007201d00c071583c080300d10401404400343d0161030344901203405401244000742030240f030f03c00c0e1107444400132201d2038005000420780f1030460703690140c101480e44275a10110b011501140c131041d40d81c030584241482031078004040c0c03030400e4540301103904100c3d180c2c00081c4035036180c2d084141800a4000625100203618004102e02c0c2090200701200160912800303101d07540559207011807150114180740a0b1910800070340c00d01c010071a03803404020380001410b10410410300c0028450313400b40510001580200040c008505140c140a0940c0400400741c0e07505041e0741311014002070b441011602102c0540d90100c7d114803880c60b0942a0b04107441000703604d50700b04414080c0420107100320404884001d45101050751a1209140c2c5607450f038441e038449030b1000d00240000d0305040c641d400100d54000c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 585686510 1250 585685260 585685291
    0x5070e12010507021504050319020f0313050a061d040f0b0d0b0a050f04030e0f01050405031617120301030611040b0d0204050a060c1e032a0c06050a0c0605 68
    0x85000280080e1800d6840e0703455000703104059806202043d03190705000000b0f5501d14203515890303502d00c1200044143d01c0d07040c09068005520900c1010154420709040d20b030755072182d41004610910314001c06104140c000e000040c460b02800d11464010000c6074403601ca410f04c1020070005064811054500b9034a6460500050b91460400d04500c1d1151003c08500e0500c1d4a481080307900c02401140719440710401d01000c03039005904800901c40482d00c1600d40400600100ca49000341e9000c10380610502e50080030b82104c00c03450206540c4030845859444500b913500d50303a1101098100001c00e4410001400407847c1900460642c09480301080d203000e590742d140320f92550081490007882035002c501031141e0301d4003403181030061641d0700d0034104248140c0c6500a980148502d108409131075410070508140c0510079507400c112034070195042481c20a440051412000c0808580c0c0802c0c81102103202c0d4024070903100d034680c240d07446950000160340e810000b40806800760200c1490171 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 585687760 1250 585686510 585686537
    0xd110d08250305090616050d0203100b1206031b0f06091f09080708070501090b0313021c06060e0c07140709050c0a0809010507140702130e030306180c0d0507 69
    0x9001e903004807412070b50001200c0c90416000e908090002d401d12001c03c0f03d40300442001da600600b59102c04d0802c2c3c4005039a40c4030500000b00c100000e03800345100c0341001c1401031101c0d40c003c0010384240d42c00c0d815a0003503440c406003441340306210b18620ba401804001c2c40950345c1400c501420001101400d0b40c41401281200810084802c0325103000003087e104082c0b0090a00344106e80c01010124000d104003030424001070400122030085038484000800040d1010301088408081240c02500d0383c8240c07480c6140031200c040101c82e003a0b800c01d09100000540c0ea0745004440d10403400c504555042c580c0359511201030400b401d030346803010b100301e680100304a6003e02c1084d000390200400b1954458090300b02501141004100c2001039241108204980360410040290420003011041d520718140c40001c01500c14a6001c88000c0d14000c0e0880d44090000000c40c01401b040758020240407c0141303120451608035603041560b1006c0c0810b5031015210340100e0b0f04000c09040c50b004100300b1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 585689010 1250 585687760 585687811
    0xa0909050a050f0c01020f010c080f150d0506010501170c1e07050124080c030705041e1d010b030f0a080904180605070306050312040e04030504030c03060e0d110d08 72
    0x103d2210f44141e4201c9880c00e079440da010404485c201d100b10000b8484080702c4140507010210040c801a48019084e0009440c511032680000401000904280d1002d0090411a0780c6090900542d40031658207000da10000e41842001071281060510325032900800203c000c400440c00c9440c0805100d06002440000700d00b800741c0904482410283c0b0541e800b0b5081c1030304020341940c010340d46500710000b41c0c000ba403004100070041d80c0f0151804030340c60509100300c07042e0344c64030190351b840149009540500d400c0001c84072100f2101d02c00092000d500c03108100340c0c0750f40d001074200103603a2210304c0f0040010032540c09448140001000064646855900d0103d403080208003200c009603110700b000705694143c4100000f40c2003da00420f0b5081e44418290180d00c00c1c0e00803030790008034400c00241094032400031030b00910b50244448565903030300c4ca801c0e8003411007900c10702424054a40c0d5032103074138030440d50101160740030402071046603c0c803901600d14400c058120741d10200482c60a07200e0061 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 585690260 1250 585689010 585689023
    0x9150304050105150a03031b150c0806030c10090603091e0b1609060f030207150e0312060105070b0a0c11011118030d08070807020c031605041404020a0909050a05 71
    0x70000072403146404071014020b0003c54a2151065194640610200c4d82c40500e012070110700c4207880003041c03020b0810080340d200e40424026180d0802010002d03180d03024a082d401914198100c6078481201010481202c070340244c20030004d86c0004040088034401d8000c03110980c00b4100707508240100c0b808003440300540180030f03184034001d0428003204801e5070030080c07817031302103460b180c1e4080f424070034014407880101168400301500440c80340c05110414103013003d075801c0e40381c0400190b091010710030b03100d40089414040c0000d40400140e802d500400c11641050380c4a0b440e403044c1da6910000c14024210b0700070040400c040b11320b2030707044c4100910403085007035060368100b61288544004520050407a001450080d005800f00005881d04500001d0700b040c1c0318200007481d992022812441d009806010b29451f2043d468200b04030340e070201d10041512030943e0203206000401000885e100f10541d40290484142e1900b00701b81503443d481424098821400e842d400a06d03a1101c81c070300b0700c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 585691510 1250 585690260 585690263
    0x5070c09110304022409060c0f01092a05010206010b0d090f0b15030a0210080603150703061d0402030a03030c1407060203090c0907080a1503050a1a13021509150304 72
    0x1d400414041580352071401c003054a00c1c1020000300074175580071810b44d40d000341421240607260100381040360b020288240b980b42c8114400810010400d420043c080c82048815100760300b8801000c07041515440000c40c0503981d041c0c0050905918108910010350700040054140641c1c0745030b85000590712105030810a400794003240042e0411446824007203820100692280e400b840c844001620703240c2031501846014200380145a13580000b2905241044e090103420941c101e04014003580c0541c094419281d01c48400da408010303000161110f80d2003560041d40c0f55010b0103441c000a0710a800100f121000342c41d140104130220060b040e45904418000c540c141d40110420010310704c1049182c0d1450011501a000c03420b05420107441040003070140005103442da4114000e840d41043c202c401150721001321000040d51f0308048210805c0c8851343d01a40d81c560f8080741c030160b4801e803401c02540d00100a040483d401a111401d10b512030200710350400c9680003c039203280365041c003941c410f5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 585692760 1250 585691510 585691541
    0x3190b100306050709081225020d02030d020a0606050103060602031207020102161a0708040308011406040b030403050c07060513180b030a0c03050d080f0a02070201030e030d0c0905180705070c09 85
    0x101d04144e1b4060402c6142000d0b180d604805001e849440003100398000140c000b903a82c524103041550020484034200900301030340501c10340c159441ca02d9400a81440b4560050404200d86501e9800441c142c4840d40b180304011781c4244000c0004444441c0300715000000c1d030000601e448144000c04a40000010341508c40c040a441c00203002809803d074a6440032003031900c041d5600d070680c1c01402c408010300801d1101145000400e05c0341e00d485044a016005014a2548074600361600620fa41e0240e403124005006034440014454000d006980540c10150a0300824a041200790b01032940b4102203c12500e4454032000c0340c1c0d460030700c48645814040e034150800b041c190300f8401e2130910410008001c20580500b00461003103400486a0000d04010b0056074408003800120060600e40c1c00c003100c9030000040d0020800200d9000004518582c0c0f05da158407503403042003101005d11040d55041000300b070400201d1240c450030007044514801e9081c82c0603192140e4441d0111a284031030980c45 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 585694010 1250 585692760 585692777
    0x20721030b1f1205160c110301020d0506030f0615040f090f0819090b120408070c140406060228030c0804030b1008030702031011070b0f04030e03190b1003060507 71
    0x40c990b0044001c210001101014002c85c1030074410392441400c2c0f0510702d420001d02c205041e003040903c0e80c0400160f04000c000f5074543c5e40b00300c8208020312003501d401d48644070b402e000c2c40c05c0c403801081e0a88903640300d00141072410080020701000e0144515640307030712940c039901c4800040d1a514500c20190040082545801c03052403024400007620840100f8800482d80400250a1340d43c1147c0c00a180000c01c503055880318039162006015148000f040e408040d10b01060a54407090344500b0010b0032202807010700d9481d00c0503a01c0d1403000c0c000420495184012000041c034011000c40c0452191038101c5034001c0070384800c04c05800c5600100c1e81342c0421030074040d00c1c458814a06020b4a80c1002a62400c0000e50000355141e820303601d1070403101d840d003204405a0340c1041c25074060350b40245106040d0f02c1d04050310351035200c00310ad04901083c0303104103800d124180012022034000c01100744580304000ca48642e064010300400c1c010100061080100015005002e1280612180d45aa045 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 585695260 1250 585694010 585694069
    0x603030903030f09010306080a11060a120f0e012403060902060405030a0f03141912181104050106030902330c0c01110105090d03090609082b020721030b 67
    0x560b001f56100150540c808403051000c035038a00c403960103d480c2280c08541e994a50313441a107415800e110010780d1a403401cdc40b612002019038000e00d040029503002041940000e030b10201480852211041c00c2c5407907000c1c14000070b080d07540300000c22800100094145644e44000a1912200c20411110650036480440426421045103060078110300702143c14643e03414014690550300c6004c000420a02110804900750b10354040d01450050740102110025141003200e14008400c130958040c0e4500400050010311920a00045a81c024810311039080e0210301c0e50030340401004414051488007000369500461718004041c0038110707402812070310f18154000360034640c0410344000182d0400c410420707141008514114150b0a03814001010090307402d081c402801032503002000c44200050740095060b59441e5498424000b0f4060030701034000724002410303401100002000400003000c1c640c8200014891000c88200c10700d030014a1201101c0000d121165504800704c60301b400060006 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 585696510 1250 585695260 585695267
    0x3130b07090303120b0111100603030212071a0a15030c060305060f030607030c020c130506031b030d08181002090f1f0807090f0803030a0e160b030603030903030f0901 73
    0x950260080c10074000301451070328007030010256001480070b030942e64028200e050380103c4c640e006803080b46040700c40d50040f58001e000107003c2030100f80d004d88103c405801103000d1042c11202d44a50140091300c0e1146c500d1540e40101101400031441da90300d80340ca06022007003544040005501907001e09100302e01e070000103812206c0191106004240203240c40c011918000b171402c2d00300c0228503000a00711005da400700e00341a082d505442d0700c107081160104070241746d9040340740103e904a09483c101d81c0848400b0141d0110030000320f0701a0000c040b1107a0031801078100f60380c00381c096103501030121110070249090050000d02e141426a000c40c040c1101d00700b4007880c1080c0c10003a19843c849100c407461115841c5c0408140d8420010382000143c0d0780f500c900c10000003009a1188040c000351a58030035602d903041210300a09540c640365507181642c00004c1c40441d50558034903c602c0141c1001c0300707100346502c000c0a00d50140700c00c02c240e407a40d840420041020040c00b04400780c451001c000010b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 585697760 1250 585696510 585696533
    0x90302071a031021050303040c0509011205062202040f05041101140409050c0c070609060215041115090a08100e0f03120619081f020315060c030d020313 67
    0x1080c0741981801004441250780340e00b00260303140c52480d0048481d032001214515001c0110007402ea010220a0004212106501d00140d840403a03590b074032a030300d0b010041c1400c01d400c500a0600c3e401400403d1681040602420a015882800800b824059008503088d5800b03004043c803920313a50700c01c10091240c00d8101500080092034000d0106c2c071144813190752400b9500803444d101c0d9485021800da1040041141c00c2c035100442955401e964803040940322110034442c0d01c0140c01421454120b00300b000e010030b4492a4400b10422010740042c0c1400008181c500510807110001c020b80c0d01650b4510302408001c100d80001840c007045029210030540d22521944000355006c142900084140030058614800340300c0c2c1c5c0400e02d07a44c2c05001070640c5041045500c0b10390116880800d141d04007068001070580314481810315036040c5e080b020205e10044034505c0d4103600c644000c402a14081008144591805013105e0400710410b03030b018226072054408542c088030301d2050b40100300011003007 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 585699010 1250 585697760 585697799
    0x306080d0c08030c211801290f04020d020405010e1503060603070507120309060c08060906010c06020d1803140f042c01030503131a040314030c0109030207 68
    0x141000300c000040150403004202002032882c0b50100020703210114450558080905d5500040c201c4c0d402d07505c248070758030b005440c80c01171600c0c245601c500410b414000d100310407800702103181c00c410704101e82104400001d01c5040e0300410201c0414280d44d11070000c0c141e42140d070200180d865140074005081001d900903942d00481441c010149109415019640c2c00b14080d01c0c00d0f030703403503403501d100300c03024818080002c1c9004179070b001440700581e040c0d001c02c2406109180400c50803202547c00e031504801105e12941c01449000050703140c0d407191181150301d51042c1009801e001c07085e9840360a072103000d0109100c142c00ca01c0d0340e1040c0342e17010708281450380441c0503c07403912604402c244d8140c8254003882d880d0822901030044ca0066851021101d490400c2100340c0070b58691800d40d441b54011800c0100c0728102070404600046040c4401a08210049006280a142d0f55881c1d00c8042c00080411030340c0002d000c0329815113030a000c1c046803240f082d405080d0050921060280d5118420003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 585700260 1250 585699010 585699013
    0x14010501030b15031b0d021606060b16021c0f0b100f080606041508030319150b041a04030b100e07050901121a040c0306140607021309020a24030608 65
    0x4482c10340c40800101d81d04000001d80300c1030038515a0020317182620a0060090200740700254141500c92030b028200d6140303201d140d080c416503a0b01c280402081c011109901c0d4940000c4021030010f03c0d180c072082d040756940418032040004181c59030043c5520020040d40d402c2100e400f000b40c0310005035400d40103400e0031401c9840c95400d040c0120f540780c0000380308038000c0307545810310043c2c20340e02a0210b000b40704d2002180c2c1e4a2819003000c280d5051c1a514800c00503052000001107160494010b0b002d6072024035202d41494500303d480e054070452403060b0038800b0000c0201101190082669520480a0346184010140b51000f203403922400100014100328060002007202d070790101c5044441710705103101143d940e90300b9404800341d204c021865680945091024a90290183c10800c2112010343c200c4000305015018030016105421000f5808a01d542d00121200c42ca40d02c85075070301c1c0c00030707286403a4a500c8000d28006503e16030102c0c40d00c40c0c1d615040b2485a541f40c007802c8051f0920b41c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 585701510 1250 585700260 585700279
    0x50a2004260706080619230f1c0807020907020715030204050d0b07030e01290f0102150411090c1c0e060c0f0f070804050a060203030c0910020f0114010501030b 70
    0x40e022911110b40340100b50401414501042190b43e401d000500010b0890a200300c14650303a09548000380c6441200140042d09598403100502d4003034410f000c90003001e4000e10f013500119400f40a00c036249407085415540c240b06050240c0ca40420302c0307204051907001800704034203001071401c040a0980ca00020140100b00c203020a8490506042d42c15070300000104854403032000503805400c010020784d44542ca401d55145900e910506ca103c540c88800d001c0c821a070456100303110300340d19101a624003607071002e80201840300014540541c0207015180440d102403c0307100041c400e030015590901000f1000c1405000d03000c0010000752001c40c40e89003000f07010040c0015940312600100300c0700c180304d004680d02d078216170784104498091403ca60709039600c055034509804650000d02855005808502d4045201c500000071a030040c4045030f80b07682001c4416040081810348070020404500031041004d62811090050344852201403540d40c880b58146400103003150f00080140e031082c4800c1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 585702760 1250 585701510 585701579
    0x9090201022a0d06140a38060f0c030f030406140402010905061b070e0f07090608160e030105040b18150f091f140703061404050a2004 59
    0x20b1039603900a0314150b40a6111041c141019402020702c052084045003200c01006903011242c0e100c80c840080040d0240721a400030200c400281c40c10345201042814500c0e0190218030781b0070702401408400040680ca4400d52000303071400d607001003480000051020043c0000c100c402d0007030309a030210303011550b0300c41e01e01500002d045020034802c0500071f20300001d02c4800074034a4460030000b04201001c50300601e0303031003240000036101113501b404443c40201c00f04403050304c83c4220000311345460781d4480d8180c031030424030f41c0e500407113100d6042030001c41001900302d52002e006091040c0d000e6459003d00b860000c500400e01d01c010410706503140c208410f03280050302c0b8001143d070480c0303542c00e165105603600c1d03202c2843d000030001042282c2c10243d003800c0260185410450340d914080071080020340b1080e10507025611035000e05014800d80c421110759034106075201c50342c0031602d814040f40d081d80c42d108050100da800300341002c5002d0009002c0c071a40b001c070341c201202110501440704108521 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 585704010 1250 585702760 585702823
    0x60b0901020a060f0b0a03080301050f040203010f060f0c0605070f02070b030108030a0e0406030f050a030f0c020901030209100b0406030204060314070818010b03031804050603060601020601210c0909020102 90
    0x1d42c008214a54558181e01d92801e03070745c4901e68101019003081a6143c40b401c0002458000b445240e2040070016102801c2e070600b4000c0e00e040310182060380700700b5824408241c905188510f483c90800a20700200e40c0070a182d8000c29010f800f9a4a81c0c500010242a00030704012131030b000001d81040c1000100b01c030b90400412a00019450f251102540801c03800240c040c1c4525480601400150b4140005100c0045482000107210391101c030041408200f0a844404046c1c40107544a00f00f00010009030500440d07042c1d02c078403003403c80207007281c4940701441c03944c0140d040840000c0d800308050180343d406100740c40c4203203221021003082e4540702d80c00900c142030060680351103c4400c8000810302109402941300c008001302684d884201d0b11040041801c854542240316605140c00b2031a182408280d0600415069011300310580c2003011107242c0060203070b0031658041e254010350021501a424510207064a2400402c4818950000900e4860100301e5803403450509024024082e86c0c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 585705260 1250 585704010 585704023
    0x603010f15031a060d02070c0807060801090509070e06010c12050309011d19021302041d0109090b0c03090a050712060b060a05040e0604020d0e07030203120702061e04081f060b090102 80
    0x40444c2c950740c1c0c0f010503c599401a00500000a0240056100c00300e401000407407510280c4100342e84910341031307a8410300302c425194240c401c5d41e420382103c40284203409121000c5540550181040044203490342d491000c0fa101107070000300010804000e11100704402c1c00f4500d043c000700075041d002088030f00444c1d601e54295031032004842c00074113210300440d102c4140d040059880385074215240c030394844404031040111900d207849284460000314015140380701d900318198000071400d0180e52004040c5d40703994000b80090b606407095090500000700200025009494000058542c03a52545040000e96030507503040b5103d40400d00c40b1a0f00c20303610000352001c54190340030b0030a181e03c441c000700c3c000f48111040b0f00b00745801c00400e507914540c000b5010048900c2501202c2c4c400000c0e1000750a54080d01c07a00a601c40740401110080300a200000308900e0b10902c1010319050f52545c20038600781c64122290015010320280b980d01c1d8285103c0c0100800d4030a810b0382c50043c0e2400001e48618 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 585706510 1250 585705260 585705311
    0x6020708091309050d0f1d010903050303070309020a0605180d060618020d1a1309060f1a030c0901050f060304140d021606051e1305120703150207080a14090603010f1503 74
    0x14100d8021f2141c5c07040f07072144015900318055a80d00d06048000030090000c00c030703041e0701072000c0c1030000400521071401c540d003c01d16000d10132600c1c51150108035081913042405c0d00c42030303119100444c58541d0301d07000c0281c003248500016520443c6c2e07091030b4103444110040c01d1a5103141c840b1400c0c0c076202c00304002c4103a1070700703000025084a5440c03c50f0040102c5554400520b01d09001ea42003030300851055880300b2400c034100c4041c0c148400400c624141e007400b400e5005042c20720b007445d0b5814810b000d07540240c4911984074421480300301c3c0c2c1d85407041040c8000016402844529010003803040e81501400ca64030702180f80c1444000140c1c5480900019030025a10000345c140b404144503403d14050b0900401c252030402c84c95000b1a42d511035808113440d0403440303040c4081203500c4d620844078450740c00100b803401c100e40440e0544070b034039180d00d12400001e0204920180c9aa5240007507000e0310301c3c80341c81103203141040703a00007a41c845600382500b414900782d40502c0ca800180d06401184 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 585707760 1250 585706510 585706547
    0x306010b0405010c0f1e03031508030f0901020f190b1302010503180109150c110f071418040609060608010207021f11030301080102040e090d0c06020708091309050d0f 73
    0xe42c2c1324a42440000e0030904064510b54048680b24242c0d5a4003892999250082d5010f004802042641c004850624418002558420821140c0f05a521000740004542c140169400075558242e01800d19241000807109207a0b81c42a80c02080681540541c212100c00114000040c050340003a07c10310000c0c001082101c00104456010380e0250050048940e000200149004909403030b080981918a500d50104070321001150340c1c403c00041c8103a64842840047c5030441c81c00230468000715142d20050340040da1840340985a401001d8243c0c0201c0c81401e0014207164142401011034000750054000f503401017002101503550303620030404541140d50b04450003c400c082c15912210142c110228074000403000007018101980a00221501d85007006101d60f80d000c0c40c941c030b602e05e004d0640301080c2c80e0900e220101d40d50b5406418214440d40380e0518090050340012600d400e0100e002c5443e03610b9480c2d80040010601000407032482608200c08644800d900140004038a031519000c207 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 585709010 1250 585707760 585707777
    0x10c0807020612060f04090f080d391b170c010e07030c12150e010b18090d08061c020f0a080d0206101d061302160c050306010b040501 59
    0x24854600112901560300402c566558405080000c800705021216140304a9844076242c00c00d0801d40a414000356200400021004059460012a0b00704241c2001940d95031035903000c5405402414030f00d40d180c1b140000c881114140204450550104214410481800c1d080e080c550300c810308182c0c074294044080d0200a2101c01008070302d0007101050030b643d40c00c21000b60134495000c50b400041e40d0003440e4014949031240f031600c10f01c03550300c00001c100032180c40c00c422000d90107900c00c80d000d10342c9500200368141201c00040c0340f442000004426002750800307100348039508115800f81980641025142842d211b000200e44014401001c19050003a03584a0119a126240340c1891003004000c0e14402d5210303289140d81d41100000b044c09031183c40082052007000140d10b07000c4a10346030b1700e83c0c81034000c62400100c805000c5e01340c50f0450580140c054448680f80050055803148405a844401031418080d0034084240d002c14000c0d0080401481080c40140884050340c1e001e00300000ca = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 585710260 1250 585709010 585709013
    0x1006230f03070915050607080a0f020a0f0312050a05011a0c010b0d0c060f0c0f14162d0e010324060806063d02070f090c020111040f05010c 61
    0x30352810a5450035894000c065020408042d141d02c02c01d1410f240324011035000752503900f031100711720071804054200c0200388250184039200e66071588508100b441039035407048944c0c2e50b00000c952850011004264210141c0b0307840c00003845115880390386400148225490a010302c44c100180100107034402d0000503401d4500e0200750080c4292010240401075411000d0602c039038803101c00e004150010b408001441c100c144074088030710000c0d4100450f800c006005079108801031802ca003515200f03004010081d40c01041c40c201c40780007454001c48131004100e40344181000003c0016000070701580e0128144118207c042e6514150ba5018a440c416200784400e56290158200b034140300c29410710030007184501c80800e907140104c0d425101e48008185050301145095013441c60f8008007100c4100d5511519002860740c20910814015140d410751100801c01c07034a4443e80040a0180d10b031400310701e805509101e0f80d4841101c60308505c0c240750414200300c1c455129031244604101018520701c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 585711510 1250 585710260 585710269
    0x40b0408221e05060a092603210106050a0804060c090f0f0306050f04120c14070e0411030609100911220f020306031510080a14100623 59
    0x18000e1480c440310a0700380d510715045100d401d100e03880a5115051200c006414186103054a0003a0555164054400e0421080600d64904982c0115a41d035405819100d4800248000c2034403000b20754138152003029840300d65421000c1039111030100f0208200c000407032980041c5d4960010b0317000c03c0104282c501407000311800141508850081030515000180c003c41558008040b20f01c0746005208030703620980050b04031f800841c0c0c007418520a500416040503c80c4451412451240000b44021000c1c480c90510b440030036040904402281d00c10b0005125003c03041000706841100244060324109458581b56190300204615007510382c01d12030200882c031500c270191688050181d618000d10943c0165000d24101801a100d618050500128802e00e0081740d10500d40a40102424a40e280e01c408605500408403510b103001d042004c02c0114050182e011800c3c00351420f0034a0700814080c0b1400c2180c2e4200c0704850300e103014000c02c000384444d49641031028190200f225038606400c04039 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 585712760 1250 585711510 585711547
    0xa18180b091b0415050105031b0c0a020a08033c03070905010f110d0c0f02060a03050123030d05090102100f0203070917070b0c07150c060c08040b0408 66
    0x800c40c85400c420429494000503400d40c00b1040341c8090100d001d20002800201e500e8501040d00d01800d100c03040c0055400343c0005c5030482125042084600c140441e0919075402c00008810a900038492140c158506079034008007410a04000c0c40c9050340e050302d8080031410354450a00c41d5000403102c169040f421082c40094050714000c40e581c0d9251000c4020034400c0780e0700503540442c500034500c0d07400341c0c8204e2541c500008a00c5c01040c900c80c0d08541510b800f41c21b10f800f124103142c0c8010400040e1281d02c00b90603040c607140c401040710350500700042c04240c1c2107450035025511400e01c02c8540d680008101c00310182505260745c1e560b0010380100c0c1031800c00d00a09001d6400d06402007083c0100b980150f20030308655903142c456944601071049000c1d10108040301c194042c40091108025450080140140340d8044031002c075941c1865580800b030303030918800442c0c500d00e03040041c0025800b17642d5020703049140c00b2501d494640d94480900c8005400034015003c00300da010702ca10001e0424 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 585714010 1250 585712760 585712763
    0x210c0705060406020712080f040312110c0a0506010e09030a030504020607121d01020706170601210501031a04030804060504080c0f0303180c09070e030309040c120b0a1818 75
    0xe507401031900d400c180c0042d60014000304c1c0c82c9070115100d00c0c0f07050310443c06140681f5210b540e60029031100d4500722003034100c80005004407030303480d540248034601303040081c01d041480401800d81d2071601d082640c20301005038042d80b0141202c80070082e503490040308580000b85181070000741500c40c3d00215025025814000700010803202844c81d0340c3d43c001c00c1115144900c1320b0546a4040418012038032003226100380b00108420000043d20103d41c01c070290f510403010301d40300540100c4004a10801d0031950148140c942da524014001e2101d420107542405100740030900701ea05060b5401444c1c168014005403046035140d02203003c108030b0500710740c1080308000403641045800e9100a44a510980d00f41008403104074103800c1084001c2030304442020300401c459405e51f11100140c4034811000c881700e40c1030104100300403943e0b4451007007440046450f503441c208920321010f403000b12943e14003168440c00094408024500fa00003d4a002510101c3c0c04261507550000e02007031310305523000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 585715260 1250 585714010 585714013
    0xd06030f0b19020a0210110c0604030518150406050310080f0d0206340203040902030f01090e0a051009060209060a030c02061e0a0504110d080406090b210c0705 70
    0x3280c00910000c00c51a9020341d69106941405081040d0440100c0c400c0744586405608601034503003071501a54070000c0c12141c1802c0085c40c1183c1c2246071420050101d508802242e80804c203007030507200d40350220b05e135064103450701c4003051843c882c20b2955004a101d1035040100000026101d24403d1221000804d25a000ca03242e039055045a02e481d00911100c0d0f100620400b40051300140c04241e40217164030141c05514141240b40c0d404480f07205004100c0020f522040000049010880c40114480c60b0740c400c4a44082d41050041e4043e1503c40b0010301455110b02d40d8000401c1002c80e9490410a072400300080c1c0c1e440c0392908002034019200416031004021030300c0404180c06420103105481d03c0d90980e41c2903910456040300c2c0d004504102c442d01ca8010001401c000c076241d0090b03030042c1c082c189541a10034500700084060203d07030800c45528501103810042e25401041c9200509010400d1500b00311220a450300070b416042e22080d8080e940790049286001414101c404c03403a000030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 585716510 1250 585715260 585715283
    0x3051206041d030d0f060b0405040b010203070b100302010809032704090b0f0403030510030302071509080145020d020d0203030f030f06040603020609090714040e1006020705010c080d0603 82
    0xc100c1c3c2e12600600c2e41c2001c01c50030002d1081c4130010620541c0162000c6028103810182028140f200810003909000d06500c0104060b40118943d909603610400310401c048025134118800104011740c090704c0c1510b503a1040c042c506140380005a0103812002c0601a00340103280c0100040c050441010082c2c00206000203100c0c1046020700303014400d41c000e0304e0600503529511071441081e511484080c0058008007810301040e09800903404c4260141e14102c28282c0d21b4254060840d0714071081901c0f002500601444120f24400d2400740901e0511904524a035038414a240d02d00c90b0900024808c02110fa00e2200b10342d5400c607070125541d00602180d85034800070f00c0030a240d520550300300f0b143c00000b50000707400e0329080c0500780a0340d602601403400d0a11703100c01d1020b03550780a0400000e108440f545500f61a00c2440948003c14040d17803d458a0b0030510400140340c005600100c0864000060030f00007a600a801d00300e041d42d010400300c1c0c0d118a0b05040c8402006207810062480c42082d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 585717760 1250 585716510 585716561
    0x4110319030509151204030813061a040b03030406020a0b0a09120207090614060906031302031b041a100f02070b0313350f0708030a02041703070305120604 68
    0x30014268035081a540c106440c48099055252401703a035007291000200d070000180000c0c4100b03150380e0820795000c01480e200c0201d6803940e0039a00d0310324003a440d14000300c0448240f482c00d80a5450b544000790080e62800c2d08140c0000d45440490310080c0c003442d1941d010644009180d8455550250003c061010351401c440b002500c8003030710301c142d050305410218041007103029402610152940207109600c2d0418400c18805190401400800743c03c104c240300c980540c4003440355014206a0610b65444200d00c0c030b08100482e82c40c17182140319100b00c6a50303031001c2d842e4124504041070190601685040d2401c0080b0728200c0a07411216406002009202e581c510030074941c410144556200e08140c002c22592402c4c0c103541850380920341030031116800904001c1001072482c40e0f400728050303292034115143c0f00c00540c02038500f000b6031035001504002c5000c0715030b1039480c1c080c6403a01651400d071591314002c0081c0940c0c000308050340720700c0d00070582e0341d0340f20303801b0b000742442203501d030280216079 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 585719010 1250 585717760 585717767
    0x40510061115070e150301063e010209270105060f04090c020703030311030702120d14010b03011505070f06150305100f0506010f0912020604030213020a020d03020906030411031903 79
    0x35644005c1c0143c050030100c81d081007483c2c0035641610901c2d030324001c1c03543c0401020001c80c600c541100100c41c900e01c0c646104103080000b0b031a4443d41c21000540c1d00c0207100140110b60503e841c489600388000102c0203e0036a0700c065150448504480660311002403403031442c551301c250b60010195902d4468100603860700400c008003280c1c003a403000c00103a05031000d03080007071108840d0100181c215140581b628449000a0442800c801c00c0005260206c2002e0303440200003a00049500040030004001302131500c480100d420299241c40d40c2080201c0d600d40b0f6050910a4005108903114500a1012012103000700000c0d0340007001c44078101071048240000300b0300102e03008911800d020010f0820b500503401042c604020341d0312200d905140200038500d82940a1040341d000c0d41c20000080035a0301e0021031419620364a02c01a5503d480c50800307854514844035240a02d8010b01c6501407964400b4190395006400c4030303080d81d600d01c50b000002d0400902041c401540c5600f1102070050590 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 585720260 1250 585719010 585719027
    0x92205090c2704060e0706090f06090e181f0504050f060705040501050d11030408190c080715060e0c181c1b0306060303030e010b04051006111507 64
    0x140c0c0819a41c1241041041c8401c540d40c240040320803103a5040405501d2454410860344030380515000640005400d60b50b0741003601c103611441c00a007000f54103001c1001d100c0f07400d5004002c40c1c18080012441c04409150840c4010b01526040c40d4002094480500a11200b4400620303401c074000c2002c484611400106030540b4261000e100f0f98407000718a40b0b000541c80e014900316207031141402d01e00b43c01151300c0d82c040765907249215140d40302016244201c001940c050340c800c000d410307202d07501401810b4540d031608100804000101d00c3d4940841d031444121002c580d08a0310784000d1140758010030340a400c543e070001401c1c031005d80405c145445c2c4003010b808064100f104045002d071240040103808040c400e02c0000c104164a101e000003029913182c1140304403000944484555251650000c4443c65442540444e480702611601401d0a1045401001044600304114148025100c540c0d103c0c60003403109000014103400c9002400300b00310840214000408001e600c0c1051000300b43d80c5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 585721510 1250 585720260 585720271
    0x11a19031d0106030201021b030a02100f08100f1503090b10080c01050f03070e030a05070f030b160c080c07053607020307020f0109080a11190317092205 67
    0x34100d01070400c1042060103110f044940503401081d1030800f240b2840b100703070030304403009900d0300c07030155140010f0701d401481503e20344003900c5520186901c582e001d4000d00c8018103072904c1d2903000505114419000489000382c0f0b0340500c000001c900136030303401e034014030800f00040d00070780c8100c042109401910018905807024401600c0c0319030504c03030054034207000e100c040508011003400040e0340548101c01c07501000030024212054415207132901418003655810080813a02840d80038010321001c0e4103800e411040c0b01f1016400017800c0c14004107082160b030310007055080c0002d80b204c0d001c0d108020000182030000c04032a5092482d070001d0b540c05801241480700080c8131586543c0111420080c1c5200c1d9110360043e51420712154204048500d10581d010705016801e0804600c280c42000080481c600c101790603c188100b81c070421145900341003000b42c800340b691780700384002040352a4a854207501403159035160100c01c03000901945030360582405000c0c603040d19803a8015603030419030288 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 585722760 1250 585721510 585721541
    0x60901050604060f030201020a11060909011701140c03070f530c070305070605330a0e0a02040302032b0305011a0d142a12011a1903 58
    0x32640d0b002c0703803041c0300f50b18400a400741e00140116800b040740c01c419454ac40000038000b91400860400107142c4110a03005080e05955500c0035400700391091003200c030b00006c205102446498070103d400c009100051128040001003440c0d901e18900030440e11042c2003002c1140384074100c0b40700b0440d88000045002091b00f015003614000607000209080c0800c143c10b0090090030f0b41c0e4840785940541c0441c00071800c002c4c0400440700820038078828140a20341d842e441400c010150041e8100d07949041089010b04c4a0243d00d07441581d90300405042103c03550003200481d0759844007001d00a000e40e0348082d4160003042606407102e000005082c50090f034207420001e03244a010800c504445090050310a8203014900034011011024050319104440d07000100d2a2045000c032040c00c40b5080d42c22040c2c4001080c03900d030f444040c0f04001c12080e81e64044035402d00c542a03404200080040c85441c20320f00ba19041011200d000340c0480c0d8100c100c802c11854002180780000380200360a16216800 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 585724010 1250 585722760 585722771
    0xe0c0c01060b3408120103060e010c0813020f03030f040312080403020c121e1c03180f15060602100b060c0a030e010507060f0605031606020a081308060901050604 71
    0x81207011800da0380e508896000300c076030920a00250502204681c489810f808002d18412000103a0140003401c0c558003119001c070311545145022021740f48001c900181c0c50341048807a4014550050700f4691000c0301c52481a41007045001003900c1c81041100e2607098000000c116400914907030090084900c40c0340e043c020307807481c1c00003110090826580140140c2182800038114170f4168902101c48590500b41c407014110040720990f810900f205075185500529114141ca490908201d408200282024004441008a1120088004400144003040790f10017101401032900c0016081e041081d0200a1181c5850000e0740e00c0400101d240b03901c60500071358021500303040054407000c4c940d8400500781c4025a68060300c042c5100400036040043c18024440429810700402c8031050b1040000948107081600303040c02d000300c80d0408010424101001c010042d400104d003000a03421000d656110702405140d5868140e2030b42c00b64503140304d01d0082c400c201e00f043d4411401a041102e04015 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 585725260 1250 585724010 585724019
    0x91a030619110f130e010909020604031401110c010506041d0a11062203060507090806010303050a0c0f1112011b050f090301022d090d0311070e0c0c0106 67
    0x1650301048540102241c0c1001440a40044a8010780b04003145048494105144420022410b40042c1d261100321003d020040060b0702c6201641809040d4690084c03000a03c0383d004241715200350310000303042d64035090700795080745000c3d8001e140021a6010742961070340c031000d10602030141610198407652411031a000c0c4211a054001d40240f11705014082d2540c040e26413031181c03042c50300041d070001030410480420303410218122400c48411280400b01c42d0440c28481e04441000300f01d0001d0141510b42440044400a240f50459078940340c07503076807044d1800c0d00303c0380380440807001441542c568807958100800b07442045980c8400340c2e5640d42000d00340400c103082c1c0e044800b4800998160f1020b0356a000d110340000c1524035031520896140c0f298000100303003207134003100590040b142034005038650301118013482d5401c403511103103440c00c01000708009501103800b0b04006092000f031300701e000200700b0144110001012119001c1c04245030807808071030a54080f50310103940f9440c040700400d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 585726510 1250 585725260 585725263
    0x90c030506070c0f0f0309050613080115030816050a021504152c030c0a0e090706051201050f010c050a061a030120030c0721110c10081f091a03 63
    0x9200c0f541000b90744100d402103407a010003e01140300240d040082000c0003044d2919050010b0060900b903d081005c4a807a0000c640e085030481c0c1000d42131090056800c2011420410a85507903170201032080740003401515000d071a12044a000035001004101200c942c061301c80d000d841260191680126000c074080320407900e44131401d0f943e40d040b034499200401141c08445e402c42500b00c020702103604040f620b000184040d801e0358000112018400c04208d523010051180c40000d05407424081e04100501c0e54a070403490b030500845020700d240c482c106103039070311aa04a20b00680c0103030903120085081d080100c081c2c4091a07210364414038002085d000f0703050501c540c1000a035040c1c0c52024414001e000440b06900c041e06a4451120030b0143c40c0200e816420142140071401c98014154011040701406590000c03821514a030009510095562945038000d00c2130600d5240c103a40307503500e21110b1003582c01c5450072206184120b40c008108818030f0303404140728516041d11502044861004c16 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 585727760 1250 585726510 585726527
    0x60f08010c090b1b1002030108070e09060a020d2c01180b040b090c031c080a0606121d0a062405010f050c0309040e060402120102040503210d090c03050607 68
    0x16000524810b4042101080c400c0c042e003401c00300054611200d1034403592842c0b03403d0040d1002c261241e4004010091040204401f50040510000c50880c500d0045a4940c580c50b0007010004019000141071503600c00581c080e06841b00002c2040220440510059882d55685545600190310b014003207030070007020320600075009512083c0e003210350b5160307500c8050500010b050703508144a505031100d1140e40c00e2115001d0030440c6a240200e159041800030403801c0c01500c452191491300310103004180d403104011032141031058011030940b40465040007404045280e1000c41d002d40c41000e010407660341c2001110644140301d51040036034010f101c507040041d03407103410f011600d01c00d03503500410302420150171503c401c601582e0400031482c0c0400d058a40c6070300392030019001034040008503d40480c00c0c45851402000860519040c0700102c0d40d81c000d083d004080d074800c40c00c42c5000065a01d03045909290b903007581400320038020300d06554204200e0000300e03018081c00000500d401d100d01e904 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 585729010 1250 585727760 585727781
    0x22050604080a03182306070c0b03070f14160c0e07020f010e280f02031225051e0a120e01120216060905010212160318380109060f0801 59
    0x40c10400e0a44802603500006503c00c0c17540020044c810340d000714280c0c100010042c01030300006e0740c0d28509034030002c040b0010702d243d100a00110300c2030a4812500c1400303840002030b1803c1c8030505006281840d640d030030240d030303c2031026044940400c480d440d40403171040c0c80100304100900003004001c10b856200c1c0910458100a410f41c01d804074020300000d180280085e02610340021120010f40220f400c3c04600c0e0071900305520006119940f180c04280d004005030503050038000c028a842c0c0c0d4031074882d00c1d000510000d8512241004031089800e108002039140c0c00180502c004010b11030180550703a41d07d2903240850811100601c1c1100a80202d035041040000100c4840f05959100c5c4000e05807001b099410b036509004405415443c10714541c016040c400340001003541c1120000c0a8800e5502034003150b005840710500025264903140b10101c400e6040224910504400c06d0700c07240710401d061031801c0d41c010000540441e154400300540b600d0101c4240669160258207017070f83e2030502c4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 585730260 1250 585729010 585729029
    0x41a0703061a0708030a1e09051b01210e0f01090b0906060d1101050304030507050604111c050705120114010b0a020106060f0c0f0303020f070303020405130b030322050604080a0318 79
    0x1507400c0346ca40d8400c40141001c040c622541c0c804142c1100111107940702c0444190703100c103018410380b5603c103000c042e215900b40380c281c10000720301c4414580e100c0e812722545030b416250052002c8003039091015003203120204008008c1c216280c00c8c90003003000143c0d11001d85d4003079400800d50908161090154036034200c4c411005074200000116402d41c0010030580c100901880b0759000108141b040901440c010501c96548032500070420007051014150003100000c4680341c2c20008001042e89800c440c402c0300c11074449680f408485002d0a2120000380c1e10302802400441c10b031031a00b014000030319117503000b0000310341c88400a440c4144900c0008000c00d159041040005100d4440041114800e10740581807075080140c412583e0031110b0110042500402c0a025900b8900452000045074050078814220b0b1a404280c03640300708030524942c02c024070114420405100e081d100144005004155a5551500265200d200c0075808400141048074960241004494501c3c00d40f4045031 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 585731510 1250 585730260 585730267
    0x1080103030c0804091d0709020c070b1c09081806040e01141f0c11060405060301060813230c04050405070501050703090f0609150305041505041a0703061a0708 70
    0x101c0903242c0c04503008085545080801c000720700b90b0712038056404104a0b102040781e0340714030503a0300b03400c02a103500004421841400215615040040c0f10400c40d045080312958914400b9036400a41081183c110750181c02e1803a003e0400800100400310f04125034002015103851100700300042c440c900c2080d0028074004011300980c01040404d2000c000020004100030f80c0c5508459048900c4507030110102c0c03402e403186014040003000c003424030101210348a00c0d16060400250990106002d2003080100213000103207032092031300a8507542174000423000030150085c026008983c256881501060044945107900c600705030042c80e01444d800740103409068182001111650041c050a5040003040784000411001c580640d1024002c141d4940c400c00c1c5c18045000c007096081d04104041524200410011610044020405078150702c40414030340c41d00e04142c0b440e035082c1107085812400b04014001101e80650080301102c2e290f0350315510454054130404e0301e030b02504001400c0e010042 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 585732760 1250 585731510 585731513
    0x206010810060311100e040e0c010e041b0e120303010909021806030c04020c280b09060f043801080d02030c030f030402010201241d0603032205281401080103 69
    0x190130758000e440007850f046c59209446400581a508001081c0e40503400610f00b5004d00c2d60301c070b0001400301c4c60603602881440c000d0320500350811008641402040806461000d8507a035005a40340d00d544050f0440b6101c1d611162110300500c0307090701c220312410b0f2085110400724940d4442d00c1c440c22009004d040351000417000d11000e544035910007501401100c240c00104106807218600c03c4603418035201401a0300c1c07412205612015103c3c10480e40200100080d1081a00c1800d030302c00e6020515120210302844141c00c0c1c90b03112000f00c0d0919008112101c22848050421412a40b0100481d00b460b24554010f0b0703201d2003142a000a0760700b081008182e5480170000442d0498410301c000a800c000003a100703000c2c03038442c0c01d0361603803110b10010030442490864450007561f030620100d240241000b200095892291032000423070680c0030720f164100e50500e8030401c0700410000d481e054402060710034040b1520390303508407031103c0d442406012a2903160510031260001060315918801d9085 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 585734010 1250 585732760 585732769
    0x120301081b090f190606030509060601050403230a12020606011d01020c01140903030f070c090624180807051e060f1308031902150408030c1c06060206010810060311 72
    0x901c442c2600d03a0301350030840c0e1408240704010040400f80e400042c0da00300444118100000a01900e04101f002e100a1011460010042c615880716100e101142d58500d440c01d41844500780c8003500c07405121040c020031907004500540700300301c02da03900c600c1440080c0b01700c02c0301c1507900381d01030069012206244095003c3c0407a4043c1d0091180710741d081c190f00c5000246180c2c0080b0b2840c5034580041400410441072a103484050522000c05110030760900108c030b000c401c00728030b10740c1d44142003181c0d1516140c010143d5000e19004420341c905500d071980c0107599651224402c10780202040400180c19181d030325580e02180300010035052600030004000c101a40140c1900040c0e0b10541c0070010b01140c0c01c0004015001180c0c0310100340b011100d40190524405aa880c81d6140c58202080001000711003100e40c014185410345403074070f2030b85080351082c04208103e00b0000d0700e000c8011481e0f9400240c03040c100c410f004211074500c849200e00000740c5800b032000800b0070340c0c90b00305d048507482c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 585735260 1250 585734010 585734041
    0x3012703030b0a2718020409030c0b0115090b03010803070f05070f1d130b0711150108030340030c0f0b0708182805120301081b09 57
    0x7440c1c0440e4a841c0e001c0041c0c26040654010f4200d43c0311041da01d500c03d4200903486149520850b02005500c5418040300b0000c6061000203218070750301c5030800300705400741802030b103030b5034000b03800e08440d41e1100420103240c2120306040002c102c94000c0009c91441000840c0d042e075805101450401d2816554524006824441101c540c02820000300b29510b000d00508010f00e081c50315a001c7c1c400a02c135034551030304040c01d42011a8070051480003c226041c100d503420100c2c40c0303061410030f106a00c0090034034071402030b40040007c202d030001a403071000001444c01920040700214100b0b01c1981c02c000c070b142c0c2e0700002004001d40e070000c1e091488003e0b50441d4649019040943c858003955032400d000c030103690011a032040a0310140000c460f070081e14942d0000b20412000c00e61070505904560301c041500d12082203c8010245440b80d540031040414001c2c2e0010844981100042c0d462030745410134050100c241c440d074140381a400105c2400c071540000c3c041c0c003c1d10a9200c2914a05030202c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 585736510 1250 585735260 585735263
    0x3050619030f0f240c05091809100207110910031703150909010f050108191103100c0507060c020624010207080d230c030301050d170720030127 63
    0x1100a011a01154008055004408104140094103802c0d01030100c05c590700103c0080811605000f001016110343d800030070040980d0b054a096030303032001d031103a1803d181c80f00e800c00090b002007104e42c200606424044217804c422500c1403829902c4000214401201d4480601920b00c52094040560740c250011900107d4524100316070f80b51040c00315160070401d40d0010040d0795036502c460703a00b40d05031007194050724440d4040c1c0551180804508401240f015010349240e16002c5820314a0713504000c00d000d40f140f661b900384810000c040010b4955000040c06075030290902c450403c3ca903102240e102d100700c0da0a0221824044140702e4034011603400c84840303040d0f02c110040480c1201d0704024040740e5810f540d9944141c0d681e504070700e180c20b00421000c0300e07d0440a120f503c807114008829241541e100307540c104140ca0304c608000020407110f000403021520002064400d0101d0460100400c45140f1036099030305c1c0d0744400f0715003214102240500b9000000884580202d04181d0444c04079 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 585737760 1250 585736510 585736523
    0x60304050c0301050c0403030f0e0102062206090609020a120b0403030e390405060d0b10120b040c0e10061110051005030712110d020a0905090604020103050619030f 72
    0x5a8110700400d003102d0003a940c0c02180301000c281002015400000468903008500c0d20701c5003a03010000107565a080038207451130301e0b03849040c0342c43c00d00c0043c040c81a9064000409011228081c00d240c0000c01040005901940e01144041495130713880840d10251a4007691107000c40d5241d07101100100b903282c850303401034040c044550718103502820824015001d054901080300f0b501c101d0410003017a09140d2680101d050404020190b41c441e4410421107400940c043e10036640d0070102a41100c0640111010040607011102409412a03d1500c22032150910342d0546e52601e44280035440215400c449a0001100501c501031080c804045c221001a086607210500d0301195002d642040b58034856400d50700360100128a01045800c00070100011200900143c0d5205d00d0030443c100840117000d043c4001c0c4070011501c84940000007006100f40c10017007802d00300c0b4155240d180680d800e90001342000081000351814641c0c1c45105051001408400781c519556040c9001507802c003500c0381e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 585739010 1250 585737760 585737773
    0xb07050702040b0d030e0109050a0501121d07030321141602120f0304020f09041a2502030309060c16030e0f03010e06010612020a1409031018060b03060c04030206030405 74
    0x691140040424891700c43e450b50b01030510850001081c5644030307403103240703d003c06030030811281e43c2258086012443c1100003094000d071202c1d0745814001072510390102845145800400c0c158482420000c00501081d9440c91031803001c4000191812400e480d8001d01000300800d03250250300c01d03c4616840c46005640000c100b114802c1204d07040440340398640b0300300008020851030946c0d180000c5010488440301e4a061a88540712483d41c003007030200c90b00500101040025102000e6000c49400b00c1e1080c1d2800c15903071600940b01d8000759143c105030b12501c004074400203100d82c05e842a10b1140b0703680308540255618221000c114040740b250b0002100601703c00192005c1c000c0036004c000c6003005100355403411320b0040c440070004201d0703545030340705224900d5015030080daa0b02c04860001c42042d21b500302000060704100418903144981441d0000311306131062411500000c0c40d004607810041948918141a100c0d0000c8490803101d190030071041c001458120081d60f00300780210100e468 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 585740260 1250 585739010 585739031
    0x10f050111010b1e030616020c1009080601030f11010e061c0f051f06050307050a030c11010f05010f06030b0a150908070e01140d0209010e07030e100c0201060e040b0705070204 77
    0x20200080b400100c0c8130403202c0644000d401c0400c402500000a0301c5444408050607000a40720104503285600c01c100c421903c2480301c0c414480c0d10040c0c22030006885507545d503803501511079964240100c3e40b904075800180d2003903004940103038003c04090a49417030440094007007078020703005000002c01142d4075483c8080101c00ba120b034038030809403000c0021185440c4030f01c13424030075030faa400319081003c01c00400034850751280070381c0c11500303607418017183c0030b08055401d988070315480c50040401d40c43c040420200078072682196048503001900d0014130368850f0811025125605030140c2c1007081c1c0401004146c0a001103000b00e00c450340381c0341c84141c0c1c517050b10900340045580000000303813642d001805002d0303600640356003012049991303a50348002c036400305811010511851020024060000b0421800b07034012055460404054440360702102c007001c0300800d58642004010362800c1004107003100c42c844458001e6400c000c102c0441d5850050132100f03540724160898105803105050341 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 585741510 1250 585740260 585740269
    0x16061112041205120f070209040f0b0702060a0e0d08010b1e0d020304021003090f02090a020c030d050405070501020a080f07030e0a060201050a1119050702040605210105010608010f050111010b 84
    0x41d0035600b411800c881c0c22400c10342d280101c103006154884104102c1d0080090098040303807840795040d18041d48641d03d500b030840c246818500c01510000001c0c0411282d203a000ca081031080354844006c1001d520701c3d0300210380d1100c051000401140c0c50400510038880f640300a007980305008205021380c0341e5a9420500c65420483d65a0a11034003c003d01c0210314150a4101c1c0075066407078104100340640d01c580301c82040010380079000e40400300c080741401500350111855048200f080b40d130b0b10704190324200002d100c01c850940b018010840041503945c40443c100c0703d0703580c100241500781010f40c2d085200540c40322900300e007404011940b1158645907260420000c040c150000201450a00030f04000d5480e0b00854103c0c0c0070040015481082180324035041d4030044d41717030040d103c03042c1780702041c0204450382010760300c079286000004d0000001c0344480d0309030311150001d000590f0386510640d11070200380070300f94140802c2881405994440c1c4a61000c0c0c00304407001141a0320f4071400302c2c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 585742760 1250 585741510 585741517
    0x10602010501120b13080c03130e0c0904020d0605040203090c1206130b130c03030e130e06010603091109041101020f03251b230d0b0105040914010203150109050316061112 75
    0x169440d800200d52031000b0700110308108002c1c02c482040f00f04030314014a07405e6450cc5008945480b4640c0414411502851a8000340281030302600c119501e080c40b107a61590717040c000c4042071040f0442c02000e2030340700700820094042e004070300c0e40d543d0780c00d41c1c0d0380c800701896801090300041c16102d10b00e02c0f000c600154100001140240c075600e1071840a4028456040e104200d040d821344e0070012501d0842d0000140c43e8111485440d0024442e2010b213803201c003501070742c0d40103503004c00c4d200180303c10300015071620090386000360215205034400b041070036201c0c0648061041e801c04240c110203480c1e0051349210311010300c038460303442480944d000c0b43c1c6500c6d101a00160768610700c3d9112040142d21403401800b000604480300000a2001d642e0141841014004d05004070749070084482009642100c6040380741c0703028020b54507841c01d2214200080038152070180014000030b00001c4c0e9040c0840c0034900c2484c8103840e6094a8203042e02a108050810039040d00c61058031008448a003003003016 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 585744010 1250 585742760 585742777
    0xf0303070f030f080903030403140307030605040e030c012f07110603040605010501180b030a0c03090b040b3310110a1104060906080a033005040b010602010501120b1308 74
    0x3c1c80e02c02042028020480c0b10f0080004d00940c0c0300300300303100100741c00840b00700c0004403003a011562640d03814022405090182d12140c4c00c281081e201c4072049002001510450075080000c10045a0f9650001c100006882020040041e80c0c3c000c5030096a04c0001001024001e0703161030380d0700f03a810020401d513510446040e40c842d0b41d103100500807580d104d803000301808241503807540c040307042800f458010704c00608007858040c0d990151200e1f0030301075003100f10841d801c49035030015071405082440300ca030411910003500c028800c0c00c40840828203403412450601d50513058049d020820300380103000c843c007400d04007401901d10702454030110403c81c600d14030344600500c2196440307602c2448240c0e41c040c1c2082500a080c0340c3c092000d181e00041c0641c405d600b40c80c002c2d0030710414840340c503007111a01d030000c1c2d40680100b52228540003680c0040303010303601c00c0020307542981e03803103a0480c01c8030b02c00c0c080c0c00c1061071041d001e8408212440605a00701400e00301c140748040c12946c9402160f804a0321 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 585745260 1250 585744010 585744017
    0x16030c14030405010c080c03060a09090c17030406020f01060b030402060a0c020301060b0a0e0f15160b1006020d022d10050106020a1b0303020c040509010b03060106020c040b040b0f0f0303070f03 85
    0x41741481c550300580c8a43c00848009003d411402c00200086007210107001d81400c0642c0d442d9410180200046010000c100e20038002600d8104000308640b640d000c3d015001c054403030303503010081111052240c0300c12601840801030a44c0c1740e55003008000d50101161504010064084e40c02580e0b00788036520051503040b41060761400811070240441c0030505016100321403200145030303691a40101542909004070303501303682ea6400032055000813a1305002a000384509001c11607182c60f04400501610850740803650700404044040303030307075021410b070340803000b544000003a840040c0414004040c143c840e05507503d0b28800c10752441103880903800000140d001000b038209110700c00d040d80801e0801c001607080c605007180c038080d6546c00f00050b4140510359400010351002429070000c0c03450f8600800b511010f5944040c000d540b00c0c040d1407014419880c0011012043c5040c1c85411801403010b040e4200c80100030013004248900402001e826010401c1a2400200268164040c2a10a45 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 585746510 1250 585745260 585745271
    0x509011815120902030a061805030a0207030b0a02031e060409080706060f051027051206180114040204020f0403050601030b01081605062d0a0915050316030c1403040501 74
    0x150001c00e8414104910800945481043d0000da1008907219442a400000220300580760213405000c0380d00380301e005025400041520030100740e0228035481105c1c021018509180c03580d0031b825040340f2058450680d240c41070390720340d2070804854802560005000340005850710b91078071840c0c160340c88000101c8119035600424018103042c201c20302c01602045e109000c5044992001038401480504210101c1c078503000180385070900300d103240001d04009041001c21000d400007942c1e032800140c0e60200010180c0070410007085052044036601000c080c04000b1310f4860350240b00080d44030005e80e210598013040f010010410421010b0300840c46500c540f800c3d5072604550505040749491580340c11200604204815540e81c1c6c01d440c640203500d2400404140140c0e41003407009000e4141c404208008540b042046800c02145000c45a0004103404d0321f006c00003040381e02d80b208503070400300356500042c2101d05906c290f1150440365403505100c468580344201000d203e80040300e0884450b910b84 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 585747760 1250 585746510 585746549
    0x7111f0f0605090a02160f0302030c06070e01020c0f04141801061e2114030a030f0b0307120c0b03130201030b03060f131e0807170a02070605090118 65
    0x2840350852504904800300045800c00c000119150700180c041404241c000c155800c03028203c0038002c002c65805010310410103201c0c94041c4d200d400004150b0403074056440001c110030f00810181c10b000c04141d000d01089190441000340003691494440c1d0000d54585000e000b4140c100421806484503503904a000c804924a650a403902a000010706100c0d10f1040d0381800342c002119401c4d152460090954081c0c0140303c01600c287c0300f070015040300100044036000d12008001400711503030321381e0217000078160744a211003540c000402c0240c140d408100c08022107040ca00c10341802502ca000c01d150010b60361101c12080e50025565115581004080b80086607010720864209d46015030152510f4600200c042015410040c40391421480281883c010000350b2500e03521140400105000c9072102410581100d800c1150b0480300080001c0d0300030585240403003a622180c007258000c20f12641442c40c1215981c01428040d4180945402c03d10002154405450050302d218042e29085050340b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 585749010 1250 585747760 585747823
    0xf130b1e0a0b07051207050a020a090b0103140c0f030403180f09140f0c13030f14010528150e0403030515010c020a0911040f0314070e0f0a050711 64
    0x1950b110040010040110034000307900842c003c803c503d4807000060b200d45041c10000e0070312094034002940312111050102d10045903a2201112000a0342c1c20000760090800e03c4c0c2101e801a0707400d4007148414450448101c00d404020360781b0600c01d1400000307080480014404040d101d070891801c08821207428410244207109032441021418280d03903090620341046001ca00000c0d200d0058140b00103104400d40d07020342030307840041d50702ca800c0d46048621401c3c02c44d001c13680d80441d4113042d400d0402156400d02004041e11441900840c0c0c14680c24100400000030003c0348410780000070b4800780002c0b6540500070161055009490109061030101d40403ca00d903090000903041c0140c4e03a80d2100961110402c0d442a58085400020842c0180303900b240280580d034020301c100510500e010080110101b40582104c540200b1201c005d500d07008120002c51089810785d82d00c01c80f0000040000445800c01a08209641852403404140e003019a0504a000e0340241510034010301e6a81030340d00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 585750260 1250 585749010 585749029
    0x111c050a0504020d14030c030c070f0605090306070c0204140a0504021918200f18030303071704020429090606070c0315111c0c08060f130b1e 62
    0x220030081c510b40380e40001c000800a110282154510304048a030101040044428400140003241e0325648804042d036642c003410300070500c41ea0b10b803200c0061442d01030320903165480b0000b40034010035910810215584002410207907070042e2244c0c04c1e9070000700c2c039060071401450600741c08103007407801e40107001039018140146d2025090544080100c1020480b03036144411034008003266110801c25440340010710080b0038280b040c400101000d003040340c00e00504034941c1101d8003201d0100c0c03490030503413603020486120001c500244080308070012404000b6500c14801400020034801122158502c5610448102c0c035901c2c0300116109a454a07910180c0d00500451740c1a00d00103156456400b038400307510000381101211308080007142155000300010642c440700094440c03654040d2544003403401010541031602d004001d030314540c441e4403200e00c41c0728044d10380300c03c1410000910080e04020f141e2010b07070079038807004180315543e081848100000c0000c131282420741c00034104641d000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 585751510 1250 585750260 585750271
    0x370312030203060f0d03140901090e090319080603070302060d1806020306120105040f02010807110a0602120c070f2d081e031006230703021005010503030a0212070303111c05 76
    0x41c20845d00000d502c185030405c5e80613140c00c410303242c640c1140180c0b00401540c10544600c803040c820401c40f00c0d0000080c060180c1c4800240d135428281807802d484642007030b161b244e01038200180500142c2450001001400079200700010360820161880d26040307140e400c1102d0640c1c0010501c010f914101e010ba54060701c070b05001300300030300309640c0e02020100f500d18028144210b290000d0341190140b0510840422075a0a4503c00440c030f1074910002d40c025003021280d42e40382c40202d68400c40c0001985e5000d5445280c940942d440740e110101d504400c800101440549401e0202d02d8a84c030f400e0724082e2a2240d080703642c96981c6030b000c0708070389029003c004e40501d03000d20400078440084010395088640c00e050800303c250728036100e04c0d20345c842c0d0140c0c91200b05000800004043e070000307807030051000c042800c00559884008064507840b5182c0d0f41001a4003c04800d02b03c10b4025005210311407103402c0008a074403a10920024070740041001401542d040080044054030a0040c1507000c2e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 585752760 1250 585751510 585751519
    0xd080d021324050706091a04060b010f090323030c0d0c050601050913081810020a050d090b1b0a06090f06270809040f150311370312030203060f 63
    0xc0c00002c4001c1050245000c041c0801e0b40f504003100900c051401d0001a4403c5052a49868502414880003030310780c6900e2a80042d601c00480400c95204028030010f80340c0c4180d2044009581c90b2440301040514603620050f40420005a880c05900300a0302e51001039a44400305040f003075080c41424960140c1c8428005ca908608001c030283c1000803078100d20350302c00307a0603441c0d14803549280d41c40078018000540100300072032418441500012248249031046080703a030342000345801181c0c901c804c1d00c01c41320f00c0901841082d41c0105010103408007081c41d0b808490a1010580320b1105903801c04a003070340d40c07000e0324807100140001d0b401550400080014859854003004440703600f607807102c40003d4110ba00c0415510159503c68010b81041c01d50110240280c10702d4102e00e010001b01c0344400c0b280400c101b401c0380182d08150380031a69201110f6110000c0866200b42c641d200c030488601c507210356803140c4c004000120044100c41042e040741c0c0d0010303103900c0d050051007443c0a010340081e115 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 585754010 1250 585752760 585752819
    0x60f03151a060c010204090f050f1605180d210f080c070209150d0602041418011401020f060718080319051812010c020d1701050d080d0213 61
    0x400340d1911014506001907556a41d115000f0340064024015034201030280f0381400300802030010f2a800a030700070348800901403d0368464140f250403950300c0a25040100300148460084028078401d4003007003000280580041c46425550001c003039409c0d80c8140b150110340c022103c0859800104403101081504020701c00f030030030200c101c240f4050360000a1182c0c0c1e103840043c60340100758043d0b800ca00300242c00356520282510340840650030a015403442c0781d2405004495510386106c4000c418000c0b16034402c00d590800b242c41c1c040174580484203065200c0d6802c803101c1c0140801c402446031300f455540a01440703603211409143c10030b03540020820340c81801203030052007100341d02e6012103c0c0750803c143e999402c1103407403040594010f091984070401e00105108800c041d0003445041c85c00380d0035100f120508100c2503031101b10380070181c10351030b110000520990030306800c80c0e01d50b28040e81c0c0503402d204201c018001682d11000314201d1040c03d001040104002c0e0080c0d030800035542e2440315a6 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 585755260 1250 585754010 585754031
    0x60709051002210c030a1706030109170901140d0203091204051008071809050603100e1e010f18050c030f1b04060509010602030a110106030c060c050709060f0315 71
    0x190f8038010203001428012618007000c540300e20f201100d0880303800c442501d84132415000090300843d400284500342d84c046c507001640500c0e040c0b003409241c1c2c0c1d00014581d056188440c800601c3e800c600006810706c4003101b004424806540041c21102c002d1390000340c3e136850312032921030130b1051072600310b6410003081c40140321310360b910420607400349a41e1500c100695980407003180e094001c62074a01c00004103500c04500206503420080c80f0781c1c1c0540442d00c0714a40580440203c031012044140f240e00244480c2e00002040b0038032034141d000c20000410044030b030070615022141d90804224a0360500c0300003c2c00c04c101800788e400301d141c00b24043c02d891740811a4050301d41c411200364200785a9060700d104030a07a626071110015210243c2291190343c0c442c400651f8a90101c02144086244000c502a5480e41405440d0030340c0e90081114240c1c904e07259043d20040c0cc1d01c130045905002d850000300e0100f06074402d02c1c006006208140040500e5824000c004801c0155070344046810a2000788 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 585756510 1250 585755260 585755263
    0xd1b0509040b2e1707050a080a02091e01170d0206090c010e060c070306060608100b0d02030705071205180303120121050f060a1b2109080309060709051002 68
    0x26441031903024030340400c1600304003401000071418500b20780309000800c00308a00c0720782c580e80307090b048000048442442d106c004010700140c062003002e0240c1c0c80915540018140615800d800c905044101c0c0c3c404001c140e0f9050501c0d509070005a10031080714811900082c00300000203415400740054420342c24a100403c1e02c3d400440080e40c10b210f03e030300350300340e050b11040d04a42c24600600261209103840389082d401802c3e140c4101d82c00680303036101155081c0d203000e0f500c01c01c41d02441400e03850321007240c50650180d08014031480a11006000c0b41c2e0100b480d4119944c0c444c00c4690f5160781ea00110400c0c5052000160701c40b03402540203001d6506005040e0b06031505558005900905a000d007010365548050301600040641c000d902160010410001d040b500600b40f6200600c05203402c2041e05901d0b00609140c00005240000854018002025481c0706030110301c1d03010030681e0150300c6000c0da0f540103442c0c081c4c4540c0800c04022800781d02010b0600980b000701c03a4021100007528009 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 585757760 1250 585756510 585756533
    0x8040201080115050f070c050f030d0f080a1e060303090b070809040e010b1306060f050a020d080a0b0d050a060e030301050907120b040612120e03100e03090d1b050904 73
    0x2900b6120000c1c40328010365000d002905c503d0040050007070782e036500034500600244440d1003264002d00840110301c2d2185000310700c0d0620224159104492035150903012107010402401076964182d0712003621902c40481855090f0140c0c90f4000800d890b0318526005020b003810385d00c030550505051125000040e174036000c441c2c8075074045030f0200d0740301e00890300d1600518031240d4496100f19560500f020300e482940054044911584407482303030045040054805208a000410058110083e01d0040902580606404c007075200c2d8001510603080307002c00c40340c03000c0581c107035050b6000b240d038281085481e002d4102446e000001641c190351500c1c0105020350000b030503090138844c0680c500c0100310055408003110460041007485032a58940c40d0322096048001e09460600b9100396031401980144d04100403208054000c2508100388640c100061407440007200c414002080f82040c80e60b10b41035400c214274010684400b180354114940ca000c844950300c41806601f0410400c00802c0324030940 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 585759010 1250 585757760 585757769
    0x150405011805090c09040b150d0b0403030e0a060c030608100902090c0d020d1e0c0e0f010f1107080f07140a03020915091819020906060a09180207020a0501080402010801 74
    0x42001d403500c1c0f8059040c904014012500000200d04000900590358522400340c0054040180244002c07402d10202071520f50014040405810204000a00c242e0100c0c42040e0018145c2d680403583d5070317841050780c402e0182ca070001b070340700e071001c0c49a00010b00c05210708421442e01046104032540c0400c07080880204803d0f04d0301004540c801110f01290100c502036601c10310300300103002c00d0b0180038034034485071125070b50000d00c0c00d010b503032810b030290025010140001741240216035445004481d0300140c808441e04014001000c1c0710b803c0010011400900986000f52005100d4042002c2c50294103901c040718554005ca000d040503140d8010702015282c05070b6403403a0568030410740e42c4a0344220030042c0e40112419042019000307808034004403a21414060310310503d2603e101551504884001075404803404012070001c0c07407c3c40040c800704100342405a030065a95100a04400000c0e01860229800003800b00c2189003072402e04010305800d0806070030301e051640008081d414140207 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 585760260 1250 585759010 585759059
    0xb0105090a06110304080a0b0a05060909070b0f0d15060f0f0e0d02010306080a0c05010e03070f211a19060b0d0903021218150403051005280515040501 66
    0xf41a01290000d1007160040c06014084429401d420f02d001c03064120200d800304071461508000c2641803805024103400b6445900080514908050306050540d00403890108000807c1184070308000d2940950f140004900d46040082c9141280107006000c00e40c7c0c0110030482c0d4844c0c0444616040381101c0300409050300e21004d0109980f005030024007441d0040081c0e40325610008082005015940d000d03520300303a9519003200401c80c28166100c82c640541a2105071140c014400368405100345260b03406207152000d100d80c000e880d4900030916014034003480390444c408010a10301c4402c80c8a10100085408002c60780ca006041c0d144c0c1d0154607101c2d400c154030f03060280d0038544208041039900074500f01d81942c880c014070486406810340c0b000280600801c903d40080e8070750031402e80d001c681e04640907041400903500f1080042800401d00072071440c0c0b0804c1c04242000e0140e000c00403c10b51403001490f410000300f01c83d41c00882c14a0b81784500c0c01d1030010705c0320f843c0c40b500170360480c942c170b02 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 585761510 1250 585760260 585760277
    0x30a08040b040807020409050c03010b10120906020d0c0f1d0f060a2705010e04050c0412061401090207060506030703050d0f050417011b05040e01050603060f040c11010b0105090a06 79
    0x34043c000c0740304d414001307507200e8100300100e028040301244010034810104c00801103040031009011060f42007070f4112001c10172909900703071422919002040400d226020044c501040d91f980c1d0400c480d481700410000404500540c1e00c42600708080d480d18050a03a40c010480c070b50f040c0002c50240101c8089401201b011503030502050259440000f51450311800302544984501e694030122114400d840c001860348826503072508207489203500a5140d4440356242600340802c004018031410811920030341d6038914070721400c1c02e65010b40d0207002c00306c00160780e600503030402409403a40903015509c2900244001c01c001000010801c03191142c03401c040d12020b49a2006491a010719880030755081e0020050b1400550198400e10804032501550321482400240440301400385004d02c154a0107401c0040c000c170300c6c150780171b0b640c0420001c00110850700d0030b40c00f05081c3d070366104150340401d01011400500d01400e000f501c3c1704550a01e00343e824100b42c00d000801c401018851082402080b2 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 585762760 1250 585761510 585761513
    0x14090106081311011b0302061b040b1813050907030308090115050f0402120c09030f070602060c130504091401110c150406090c0e1b0405181f26030a08040b04 69
    0x1124454901721200f80a0301015085050103521043c040b103c1e4034010403a0316000031000340f00360a6906440781924003c1c01c000080c0c11004500c280624030f82d82c450080032070315603988282c2c065a0b03c00d80480c005415428603514000e0030350580a44032040036410102c084000e014545411021a9022074208450340c500d2400b050091085c0c081031107403240e00300108010034400344003c120906d001e400700e5201866000c481900d505250081000580044010886541001020381209c01c4051000d2400c0d42d6290002001c460002c103080700c070319003041000500c0c55400e00ca002045020200c0345480c00c0c0c400d2000ca070f240d28400c002090b09442010100f01803000c3d40c1d0240503040e0380301000b5880b85841380d0035503034040c3d8101d807614680300c2d5952050103a50403420940b0104c550251200200112100e031104021100030700e1180030000020464800343c1c0d652600740000c0404805030107401c048500110b0a401000208081039442084480049540010441d501035005441c01031103880d81d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 585764010 1250 585762760 585762767
    0xb0a1404050a15030317160f1206150f02070915031e050102160606090903050405041e021306030b0f090117010e030a0905030f060402010f1112041409010608131101 72
    0x414000f5031032501c01d0b95002c4100341d0041c01040d81141440400d07081555008000d002c210310240c9507400241586145038015030050000d0003010000c0840411440d8075210040f501c0750b4005c8a000000f503003101089520f07501441410090450a14140b00c0e45100e20228801c560651000030060210000711304000c88100070488115076108000750750300c0032000342c0c00c490008401010384200d0b280c4540096003001900c61445556850b480d03132800d10b07140008110041c94000c20681c448a0b82d405004004140c52000342511107803407810f04541e904259004040b42c03046250707140240d81482d282000c80e5601c0c00c9060440d8042c4034402801440c3c0042c4c54090500705111010034800400c00300d040c42c1e0071995280540e1016000c660000e035000100c1542da40c4180c030040c2c04249002da242c61140e10400f00301c4035402e030f080c00701c60350008414448036955000780d106882c0300d00c040d40131035020305c0d00d20440340c01070245140003200c07803c0c0003100b01c01100300c40c00000c0005041c2c012141c8540d00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 585765260 1250 585764010 585764021
    0x31b020409020303040308030420010e090703090b0c04230609040c050408060112061b080403050a020114090a17030106020309010c06060e0f0a05090f1b03030c030a0207090b0a1404050a 81
    0x140901981c0d00c5c0d0b903403031074052065042500c080b0360f6131783c0002ca203d807408000000f00c0c4035150140c0d100301040361004180052003402030404410103898241e1200480c005620a03801405c034400b0303959903285010400794a020b00200d10408602c00e90f40c00b0540e9680d00010f80b40452012540000d4490003228286e540380b04550200030107000b41800040d03415100360300b07400081d000388800d0000c4e002c007105001c4284020010a0081a101808076011900c500d0203400c0301c16083c000000c0045032501171198401003140c8030b001c954007015641d0108034441904070440cac064401c0f19802c1d541003070000380d00e078003030380c801ca5040240310b50800040c0145600300c06c0c0141b0740c5480c00d0f50a4104044a6480020100c40c05480b8074106004515800340000d420000d02e8071250103000d114031041071004207800c0860002d6454030050020a840d84400d00041c00c2d0340d80719400412006180c1840300c019203a403202498451150088104a0210300ca00d20038020364007107600151990300e01421030010f06 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 585766510 1250 585765260 585765263
    0x2060f060303130b0d02280306170a2d0602030a0f05090601030602031b210106050f0904020310080d0f0e030601032a210209060d080a230a0e100804031b020409 70
    0xc1025800f40028101d107201e5401f200d8941d03404c3c043d0548420b8110448049281417002552050f04220301068024220130a800d442460b40c40b801e14000803d10b0610b40d0950099510340d5002050208108544c17013503480703035580002c5c00d000a26110b60044c0d1103280522020f0506900000000e005524521715400c811840d92540c07503c0d1004400788401000490f807400100380b007070400116280f80034a00740c0d140003804404c102e28003000c500a22000e900090800c01540b541c0c00c0000c13881180500114800c14500d80d604086404d48990052807001100a0980a50414030050012842485c21110520418a03500343d03e03546e485008020700d0841e41c044040c5000f8590114030f0052240704064003070f4001c44028182e91204810017868031101c0704e009007204001c1061540fa60b000d1141a80c076017541c5604911599402400b00304c10f5032001e2060400142d5102c40e40a60b440c00b0016150450304610f0205513501e800d0b90054035032400c00e010f00c1001c0e081044490210340c0c850700700c00d403043e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 585767760 1250 585766510 585766537
    0x705091f030b16030f0e03030a0c020c0303030c09031608060408030402180f100816170a29071d19080a0c05030c01050712050a0c1202060f060303130b0d02 68
    0x1454112107a00700032495503122030020f030a007400d559022046001b0185030b51440806940b07035072600351080c801024280204401e500480031207042542d0184099031103080e44d119081e6a07040b5010800d800c0c000b0321100326000580081c024841c240c800a80c603035004e6844030a0f1a07403500c90303000090401d2030122030045020041c1d41008803e40300b9941883c01032841c1460043d400c4d840c1c5440c036499107030300d071203d0441c1400403004108400f85101c6060000e04c541e01503c60001d40350701c0340c41c40441840700300320b1040103600400e241e660203030709000d5100b0070358500482c0b000000194010032003c0e40400522a59070418000a0b05000c292f4140050a015045807501c05084c0703040d081e280b819105e414400d000d80e10703034004a03500840c21240b450b03601140701046c101081c10242c0e181e41000080f041000100894100021201c0fa0b04c401c455066400030b0845190000c01c000300094010816030281c2c00078490f64a40602d01c841c0c110684105003032054480c2458403840000380210f21148204 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 585769010 1250 585767760 585767783
    0x6211b0309010b010923281410030c0804110402040b0c0a1202070b040b030c09220609020f0d0e0c1c1a0103080306060901090b0a020106060305090705091f03 69
    0x2009415031054208260a880c0c00389170036503c0e54600030b459116a03501580001907240c141051414008030b092000088540ea4080300d0009040d1000c5a07858000d0249280940c111440c0d610306005806038501c803614080c01000c18042d0018104031f0003a00080803244e1445400b000740c0d40760303015100a0700c03520041c01d403902141078806603540138000042e14040981403100b406144081642802d0320050000b0701d142c10720f003102146c0c040d440240b0b0483d10303900602c80e0b00e465659508418200414490074011844012104441103d0b015400085a20310400103030040151a0007500d200b0980c000c00002d1f000c040210441c1407107052031201c1c0e8854072040c42c41400c1c6141000d0354644070302940c5c000398815501081264816020b000c090100c5400b400021280c0c58488010004140d06242a1584c44d54600341020315820036065000581d469250510415074944540c40c0c0c0141e2140041180b00d16000c00310703808181c080c007050b400c0c7d550642c001040081d08500c9600a6512100a106 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 585770260 1250 585769010 585769021
    0x103180602130f0f0311100e0d0b010e06040606021b0609040906020a02150f060d020d0b01090e0f0102042d0f120209240108180712060b06211b03 64
    0x2c0070182030041940c0c00a040b4000700318485003040050580781d02525031a41160054104041f0603c600c0b5807408001c000c88107105107031503184040c101c2c5482036610a542d5410280000710307001000740907502035031505004110155000074200d00801081080c6460000d007580899442d128126506411500745004c040030072a0f140c1c024050301d00c0b20b03801d60394040a202107400001c1130554021030350001c8140451400d00e007421013500c1aa200600e0141403612991700c1c102e040100b41d01810480e561400440d005907403e01650401d282e002c4021882c1034200500d00c9501c82000c4018034003482025a010000d0054030715050107459080b000003510b42c0d0b40c0c0801c0841c4c0000301d4040b80501078031030214002d0700240350f540ea00101e8403c0b444c1040f004420045031030760801401c84c0d5a0403940c80305d88000c107a0911484010340480f0315446610714150a02c00241c2e0103c105280c0210703001c1100c605000404035808a00c0c2c0000701276185d05854031500e8a1050700b0b603161141c0d500c40c00000b03009 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 585771510 1250 585770260 585770287
    0xc02151906170a03090e010b12130b15040b0607080d11070c03060b012d0e0102160906030b061f030911041a241803031207080103060e0d0e0103180602 66
    0x4400f030b100382d480303005894a4503480c1d11441c83c02e2003224503101c0f0074012040603555a0080c0396000342040d515049000340c0d51503d042c516070030303038040769800c64180c904400c81c00c050281070040d0000782c03030051400c41d640d0760f115024890020101562661410140c600b035041c1401ca6050315003290b4420303216503ea0401c90b000f444010001400300b20040f0b0b1240c2052000003c24851582d056040c05501880110540d0121512203e05046011740c0312101018400000410050007041c080050302c0c50661800c9801e00c80040c100501c0382004880c80c848003002d50716220b81030082490086080810b6242203406058a1030815500030300740200d44402c0206841840c00b014404c03184010f054209805071081240fa0200441d1000810040031a42d0003c052098200c044042c0480b4604411450380380b00501060f1042c0001402c3ca00042050200d203001d03054540c914140a420f40c803807200005041800900c17400c5040c15122401500489450b99842d080d190f0007060565854003d0846003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 585772760 1250 585771510 585771523
    0x914030c070501030c050702040905012a03061a0322053a0926070905061203040509070c030c060e0607021608150603030d09060c030c0215190617 64
    0x1168401c0d4200061258403d004800c010351369a11000d01d05001e070340174040a020201c10a880541d01c03507803c00048003494841105405510110400c1101a101d00800b61002a402030080c04080c0b1400000c842030402260f4020000708202d180c0d811041d02507210103030009001900034004c22880c2e019040700c0e02142110146003410012000c3c00120041c144030032968048000595408000e00501c003800001c40740c40703e00c800308802541082d000c05c500e13044541e0080000c036038650050041e0b5040c000f80d800c040c080d254010750b051a0400000c1442c50500034412405c006582114109141c0140006294150418001d0052115584c52660f81e29030503640e80d00103115240440140c885d20050303480940d51102c02030705031050710103503d03c0881009012550715000030040c0701d103140154425044118406d1901049203090381001900b15807003807a1030020740d00801940d00c0360075401c80040368014a0908500c2145141c01851f2006140d15044151081a40c0d40c0b400702d9a0800140b9 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 585774010 1250 585772760 585772777
    0x6020307080c07051e0a050a050c030c09011203030902010e0409030305060f060a170903040e100e0a05010305030a120f0c0c060c1112391b060d050604091403 69
    0x1ca00d06900c900b00605a6071007150340141164001858214141c04040401a00281d41d90b048644000e01621054180f4050820884440c0d120080703103c02030505104d0b042d0080c000700c0c0d00245c5c641c90003140d0400d1005d512001002c0590307604124003103a0090300805d00c0080003400402004c801460b0290050005036842d0f40314044416400b00645000c00885a00d80f0040d0b0300d0594000300368040550341d00c0d014000300018001400007103a8090f0b00c9810324450000301e160b034261140b41804502200c170740a0300800200d13007440014000721318008203c07100e40303460f441e12141c00c0c2c01c40380001006200700b4440c8190141003641105034160311118a40b00903015880c204170805003403d05a64940204000321055084400c01000390310341c0c0f00103012450324002c1041c013807c2000b00602125151401c038030407594000542e0400b00d603007c0000e02c04801e030400104489100020014606006520680c081552510000790483d1a6a00503c50a0741d021440c090040b544110780740e1240c02c076951 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 585775260 1250 585774010 585774017
    0x60507032d1d0a1b0911040611150f04110411040302120a0b18100f0606031a090c0702033c0a120c03030b030a15110f092b06020307 58
    0x55450b410055602d8800458600b01c0c02402d10340c1c90f13035503001d03d03501d00040c1c440684680504001a1404a8022013143d450b0445545a40d03504003000035058210750000401942e003c070031079950300503284103502c0c0c200442005008166481d450004000000140d081c0d40040c2080b129490400903000540709491084407200b10440c041d0001c1c980e600250750001c0c00310f406450211306842542d02d1072900384001c180944501d80c1051413082c09440205826000403039890701d040054035410310821060644040d240042c10f003c44002a08490f409444515160340000e0000215a400c0041c011001c40e44925900d003d010800e441003a030384011802c565174941c00c4006100701001252080b507050744400070080600c95154101e03800d98000c0c004400745030761616070184903070b030400103280034501c2034100e0014038214100c0303d41510710314601802e0000c1d051000d40c40c0c803281403003901c503103010548244c006848150011030405184456491001011320581420712207d82c00541c440c0c0d0b40e944 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 585776510 1250 585775260 585775271
    0x6060f080f060609010c0f03020705092401050306010c0506040c06110303160c060e06090a140304050105030105040b190f08070b04050117040c1703070c0b0a0c060507032d 75
    0x4050310003100444560080d40c4806000aa60b4641200a0092294185000441c01c055039407506451003184a00b0303030150340f00240422940c03600c2d42410b43e00a030301d08840000c00f510800c2070700410b40100c942e181448004000945a81d1082c1c088140c11600311080359140c1c28142058540404203000303a0001840f01ca40349003420100108070b0780100e075612002c003081541442d003152503601c200c1089528a866480c030354400c000030496240140310003001f40074030b4402481e21071151441c014030560950410703c010401070ba000002d6a0442c1c1c001d0b180820510b60b401c0000e1a2140c80c0820100d8483c4018808500800048043c3c1c09442d980000c5804103a2220f40d03807041c600075842030f00d0006200514559007908210b00c02904288903031003e030700c0d19840b20142c40141c4502204038800b9400403603007400f40911000020006c0503035088503032030081420030091019829050150181d0348910206040c01d103c0e5120050424152012000c1c000b14801184003510250032803c1078a802c1c003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 585777760 1250 585776510 585776537
    0xc0516180e0a0f031202040e01060503060f09060f120a080307120f0902090106031805030f070303060909080306010c050f06070306080d020105101205030409020c061f06050a0509040f06090606 84
    0x601e0846054002c807400d01003030000da40441d08020344e05c4a022456809000000700300c005e00d204e40d4042d1010381c961a4880c60300c0b0050100c2d040c1030300c010074402c801e05000c0c46025103900c56201c1c03401806458040320003009411a601d048042c2c0c60003400b01100004020750705074062400364403500e4001c400e00507048101a02400d0700d949050107544400003034010000107019601c1681c030a006141c0111480ca01900c609055802240105408840002d41d450815505100340d40142060082c10421070031a0b440e41685400300a05243c10301002c920000c0601c1810003448040c86626000c5a899103003480004002d8144c03841490b400380f24040804a0702401801514840c9440303800c900c0c101417404180c0007988000d1072040c1c8003400100800b01d08040c040c0028031004600d04d004025904100090965104900101d4011003001010500041d60301804803010303c100c9241068848003a070000034000c0810307070b4102450525060002444402c1c1c0d4010780e04a0310303c0e0302c8e896440c03000c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 585779010 1250 585777760 585777763
    0x6090705070302100209030f01110d0f140106052a03130e072c0411090f012c01090e090f01110412120c0804080c0f041a010c0516180e 59
    0x1d802004000d604440310401c00c0c0c286a1340500481c2000a0458000c0c90040550508443d0a80d0900c0b10300d0707600055620321420740c0d008244206651074400c2000c43d02c040c100906075507044c0518000c00c00c0000d152400d5048100c88a1804540342d60803074044116803e01c240e0b0781d40001d042d1884101e251100150403010060114031642081c1c50718410031740c1c0c00030034501d11149410b41018450780380340010342545445c42040039450704090990307515850041080218210303844141e0420071641c2da00040201101d0010500e400c1c030500f101d00c00f080c81341c0141d13104d20054103c200d010080c0410490740c40400a0800091721240c1d0080008030241166000148154050103401c0c1501e03074090300016002d005140c602544a2420f541d80500d541c2e101075856100b50b1042c0e075198040001d1904130300d0300d21012440c0c008115000c201880e0101010403050002a0f0340300d040c0546610080c0c1403003410300100c07211054048003480f08581310042c008500541d94000c40090b85854a40398003580c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 585780260 1250 585779010 585779017
    0x504050a1b0f21050118060609170a060e0102130e152407051e0102030f040f0201031b0f17010501020a17070c1202041a06190e0303040e06090705 64
    0x2079116621040003510300701030310118a0010001d0402812070a242c01c1c404407281c04107124042e0800110b501c2d40341c0194210418070001050803030705d19048041000542040600044407a45003c925190018000c414184440c0c5403014004501b000842c400724a81940107000c0e0000c1040103154050f19160304030040d501c1180c0c150480313410b540343c130301e0700d440c1c220b1103600d44409040b10107100c0e00c0e039082c1d400c440d90404c0000311901c0c0d109640700c440c20a41c2104031514045420700031030541c0b03003810040000000180001e0904103003440440190b901c02d0308203101100420351200040c2e0b010031300040055520780340b0b030307800207542840051014485050180c100c1c0c005a0052420444030b844041203a5105203181426113003c20158000655552900f00240000b043e46006011135005100a45181c2d07000c07081403007c2442403218aa0342c18042d0727002002007032840e90000340828000c0e40e2440060601d9541480301081c00280000410b01c02c500c036420645004603a52203015041d1443d00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 585781510 1250 585780260 585780281
    0x4030c02012006060f0a03050a0c060f0201150504090203010f090308060a0b0c060406050916120b1f0b0d09170a1e0e090c280216030c0b0d23010504050a 67
    0x41048022803242c2c5031280000d105c1d440018007002c4042c0c1d90b665440e2070030850544c00c84000d000c1c0310042080c150000b000151466640c00244441080028012211040b500401d486a03070755691300f00640d00c0952100aa0b1420404c04201d0000c01d810090080030044408512070060100040350380c24a07c4184d070300000c10078008140c2603d42e65030711000383c20024203e030b1040c45480001002200680034680051000c084880e14044d400d08203021034110050490000d0010340755680c204040c070140755401c95075004480368440210280d20006044264406000d11444440044040c2803010080032041080e44446031800c104203440f81900075a0154480030401690384c041150402100f4698003480c5202c40d02c1c07901503066207403801c03001d240464096a140442140441540400401070a115410449201d16256680e81c406680c90b50144080024001c124a80104500d4010740e24401e540008429000601c84480b180b4100901c90213204508003008a6281d0400c1c2c850380e003141 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 585782760 1250 585781510 585781513
    0x3011b120e0307020307030305030403120507021f0e0109110901050103050420010e090705030907080303191e140906060a05101b0209090f0709150e0c090904030c020120 74
    0x1102049600d40041c00300d410741c210903001c10403119005a5040c800d101c05540f0a4407050385904250400402c0900c0a0741c8000c0d90b0342c0b9140510211907000a0b000908529000c2c501c507404040f502d102c0c002c1d0a402406500e550300744505d15003001030f1250802010741041c1c0b03e0b8a40c42e80d980c2e00460907100c056070094920034010221030002808007968410224040c141800c8040d540ca0210303907141d4048031020005440401401032050301070110b08001d00c444001142181086810118011244218940038a589a64940c2e401c1001c0e8240c540841384244204220f841c08110040c00d00401c45003c01180034a600007101407070680c00e500c06450001e0403100c0e41c0701070030006980c9014000c51003000400c284e23010f000181c0d68030401601c49d00c0395402407c00010052400744c62721040d034001c078035030034248a00042441039040c0301300100d5030360404107041512241c411403503911660340c906070003c0c07251f020842810f410068000e031480c400c0c4d031116141003103648066101e0030381c4882d40c0c64a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 585784010 1250 585782760 585782777
    0x1205120405100513030c0b0403110a03030210021308060403050301060908061504020309100f0213090e3007030e13020a02060114121020040602060f10081b03011b 71
    0x694400c8024244e60600074003016101030b103d0301c0781c1c08000065449550905000902441048140400c05500000c01d030340951a46055690103074403143c11064108100341c0c0403035081621262421004003c0043c0303001e50b0098100b0381402401540f090190a011a807503500026484030b000600611450040000214200707a00701008069480500002058812845103200c40061440f50a0740c0c020103560040c0c1d601e14188181d20a06450340c84104002e1a0030518100400003040c02c507140004900e41031700e11005903980d501c03811540c00940c0740c6140082080010181c200604c8080b00d2000c4902403845080343c3d261206a00c01c6500d1a80141c002c2001040202c40c2512060310b031000c010f242c45801c01c40090380514280900c0c40c00385d0700035203601008041080c00d107040c1c00c440400300340f218502070138441c0207951040060800b00841c0e44010004107001e070070607045000b030060300c0c05807808055240306590441d0504100c09100e5403a03c80440d04036410f0010032004404141c031880034 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 585785260 1250 585784010 585784039
    0x13062301060c1a070314010602150406050709120f020f0a050d030305070504081b0f011b030804020102280506010b131703040f0b12061c0b1f1205120405 67
    0x1c032a0042c8004a546400c04142c800a1602c01e5040900c0392082e690005100745a10b900150302e110103900007019074200540200d504103084100750350003a003044000c00c054a40040413140740740d0a41c0300b03810b6890544580c1c0304200300360201101c03181c000c4070410700e00c184030000c000e02c01c04284038041e800320171200c451000a000e034000701d07400f00305402c095007082d44d101c00c82030904200c00d41010805d81e4516400384d1901c0c00d500f00f041100020318100001d00c0c00c074002c403211401881006400c0c8401040042e0031603200b002109860401140304070200c14078202402c1000040610441e070300c0c040c030000401c041c2e49041c2038688241410701004d07000d41c5000414982075410200e0956140420013005c81c1c010010750800000300034803100c581c2d8445802607104a01c4001500c1e0302c0c840d0344941c3c180c42e04503c1c0c0d1001c41500c3c1d60411124140c54039000190514928480001250b465036490000313003401c04290b109003402d00481c261400d6660000080400744158011107620110b0140fa004 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 585786510 1250 585785260 585785267
    0xf03090915040b120706090b180603190213080118080313020d0f12090f05030303011a1b03030a0b0d0209040f0206040e15010912110f060f031306230106 67
    0x441c040000d00300107403403c5054041455021030680050003580262404c1000c50b50140804000300180e461143c00c190441c40080300b14805500c1d01841400080080b80d0000380b05e9803440d142d118403820444d601c212a005400714034000d8480d140403540707040340d5207503560310040f18407250039400396445140da900c180d8007107041001210140d0b00171184d10059000100b4030103405814501618080f010303c522618018a111240d400915080d107010300f081155407000001e890555040c031610001c68081d401c90b4503c6030041c00141e2140402c000c01d003008403500031006500986640b5401d00038010f08005114000d0103400d002900302c030940c0006404a03001c151180c034000d10007008545400e68170240d800200c3c0040c1c2c0d031402d001c0d840700300c111091745c0c000b9040e40041030154500300c000701180d04e810104900c5d8100c4903006900d242c104a090b641d5000894803881410008030751a0f05240403614080d003030504e0304a405526003910304082411841034020002040c01c2d401e10307680c1c24000120f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 585787760 1250 585786510 585786541
    0x4122a150c1a070e04050906060f01090b07060b13020a0915031505040513050d0e01180b1e04050a03080d0612050604080a0320030f0703060f17210c0f030909 69
    0x40c0d080000c4134220301c8003599203000342c03800f0310081d000809043c03d20b5400c022644042c8448581400b20754101007081040800c00c1d80d0710b640e000440020700e4008070012481c1400043c0340010ba10348009446000c06400003040e400341c540b018441d040708000d03008250102c90b0304600301d1a403841c90540400031450150042c030b038403d0701c80500a4865a40c1d0f6038942c80d109031005007402040d1103000b00302039940d00511500b44980c4c82d8040380d410500c2c100f46d810440c4900c04c4c50404100c4048094940740c030000d42101d0003000040c0041c81d000b940d03401c190030650000b04082c102e460505500181c4a071035010f2884d5441c1e0408054031503604d07580d0701c0d246945e109241d080309064617a10111609031450301e08144807141400c2c65903481c80c04d0302001c09400c000034140000d05152400901c404182c0000701020b440c040c0c2d609051801c02ca13100c01c1d1900d01e9902c0044414825000041c140c4107119024007041c4004c10308030344807000c001e0344160b00c1e0b00a007010190005408030008404281c0b03041301 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 585789010 1250 585787760 585787771
    0x120f02090d170f03010f03051011122707230303090108071803031106062e12060f170f1005060d02090108010507180b04122a150c1a 58
    0x49440d01d0403c1203014201d810981c400c10802403c03290070020f21106204080103a03d485504211200704045050074600404030710040200702d010014030320b0321140480c001c40249200000002c8440180c0360b03590790065024000c0c21241240d0742204803800072030031458240d8007d016506140705000115031030000102070608103c418880b04104003402c51514015502a6842c0c0c03895101c40303900c042c03403e0300107407446003d030f000c130446455405040006540120441c6a121894500d81c4400321044500484940050780c0381c280c0000e00d10130900807940803910700000c0c00c40c80140460595444050321049440a9082104207407840421540003e900c080b0081000441c014107030045101107100f60170080031a0364440511502d00d811030002d0841c4071f1041c03504000c090425198502c54060741c0300d4091400c41d41511f03c420440080b114100b00100360400545c1e41c03200982019a4044900c20198012076110100b40214400d01d02c00d011141c02c0003059032081032615200140c142c00400 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 585790260 1250 585789010 585789053
    0x71419051e0c1f1202120604050f04020a0513020909010e06191802070f050f0a0c0f05010c150e0a0b0118111b0705030316050c0102030910030903020c0d03120f02090d 73
    0x3d8004d035428409464400032521a10240380780c0142800100d4601418260001c03513021704000042c1d90b1410007800783c41081c5d46070440c0c10300541601000c1d0003140e000551028014001085520403080d10a101d0482101e0302e640380c1c8094076120780200c6030b80c0101c40e650307220504a0120304d2401e030018a0100d00c11100346041070180d480b11800e210060f210705509802942d1100c041c030006030042c1c0c025100101c00a1111864400003801500a005004205180440001012030043c1c0e03c4100180c83c0103060b02e5030500c091600c1080c040c0e09018808031503c4084000b4074030802c0c1e108205003e8400c0340494600032180d550038840320001d501c9030380b10780b007000da000c507131303501d0500161140740c14856186480c0c10051406600b0702040e000101d04560042c082241266600c4440e20610001c5003400030707403c8250300302282050200d0f81050307000b07079803c080d1038105544580c00a10328061454100a4003201400e02420307407040c00180e5902103010502800840c5005c1091200e1010594 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 585791366 1106 585790260 585790277
    0xf090405180304120c08010e0a050d050301060c0b060a030c0b09031e060f0a09050a08030402010e03300d0504060e070f0b071419051e0c1f 61
    0x89419546046a031a040030b1143c20790700034028128060080c80345204408c201603407003558810464103441071003100790001c1c0c07040e000e681c1629610f960f06201c2c008651118200340c1000f03068191300621042e000400a40d090245100400104a0711a04d81e207000d0201030418107504c140b5803490701420000c103051500443c40075400301003054081d02603100c482c01a0024134107048014101c0c401c6240f18030074042c00b00c002d140f142d0b100741d88000c00c102c941814140c071048005100c0f502c00c0c01550030841c0c0e070410103000000002c2c0d100b2890b420880000700c1d44060312400d4400b0b4035403947e1040092410001840340c24050840020304000480c03500d0300c6202170b84524000640520800ca00c1010b08450a00c00703c146002d041c8034120f1240f00702e040c0380d51140c2d26100c09220a0313044038618051440082004502080011318503100341ca610f0343c4804c540310040d01610704004152 = true := by decide +kernel

theorem cover : BRFrame.Cov 585611510 585791366 := by
  have h0 := BRFrame.cov_init 585611510
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585611510 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 585611510 ≤ n) (h2 : n < 585791366) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
