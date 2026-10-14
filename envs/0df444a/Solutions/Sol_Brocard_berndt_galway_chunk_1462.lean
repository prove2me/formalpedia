-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1462
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:06:23.657424+00:00
-- url     : https://prove2.me/submissions/d3d17082-2287-493a-87b2-b6e908bebabc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 262769784 ≤ n < 262949640 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 262771034 1250 262769784 262769797
    0x10302030c09010806131a0406090209100b0301050d170d0b1311090d0804080a0302071d0606070807020a0504060b031006031e0b0315100e1b0405010806030c130b0307090c0203 77
    0x8000516605410040f10500100d1f0409032054100308503e06810820094148100128840c0000c1800685004102c81282041c0d55480506034151b81c01d0405106e08042480e40c10754080c00b40550030150b4061500c000e040c0c0344240c03100403a143c8540310a00400d405998003075010b032800c00301816000c1a800054542c6060212003a841503111400c2c01d44151190b50811000c0380103080740441071640006a010450302c41030040d0f68045003244481842000076250703a54440c004100303050110b260b080140014a0002300140c503596034550011b41220f445034010a03146c41c4c08810092465040c0c90303480300070070710f07401c05220580d032580090840603903e202031500240d031100d954031036031001c0041940d4180465040000d5003000715000b8520415131248041400450001802c00710940100411101d2908190303410326007000015a41408000d107001d4051040d01c004120070b030380340c545840d20f18141c0800091500e044009050400569420001005003082004104503074008100d40d00d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 262772284 1250 262771034 262771051
    0x4120905040c1416080c0304080f0601060c0f050f0d0c060c080402150f1603171803030f0a15090b03070501020a08031b19030f0c1806140c0102040806010302030c09010806 75
    0x60301e281e40c81509038440d04200000e0304181012038241e202d410000012300030341c0e2840c0121400398008403902c95551000740a08800101000642030001d00c10a120398001881001904e2940341e40c00b82041c070f03000940c14030000140d400039002080c086188221080c0181c00d2038214403928054002c28002d00035000410f0400000181583e0310403200800d940c01c144c1c40b182985103484903414028105052800c00c00390340d10050000c520b12010100d80404410f080c603001c0c3d402d540c3c0d6142040f0340d101000b4050340348680c561002141c000c1608845a01402c010a4000b07814032498060624005803608040e05541c010055035000c00c80d51000d9135413107000030171804106120208254054003039800c48041194071980307890880d0f078045e00701d14141e52036000200552014000c00f00c9503c1c4070b1039114071440001e00c50a00030a44240d805941c00444914aa4a030550300820075089910035409001150403140c0140214602489450000c000484100c0151b5051a5449031038000140c180034 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 262773534 1250 262772284 262772287
    0xb16021b0103090203010213030606050a0608010303030207030e030d091a04050306060607030c050a030c0614060f131b050408010e060403140307121112013f0b04120905040c14 77
    0x1a03109030041000c2c42c0d4017a000b95110101740b01046c0744190f09000441f030042c20440082202d0806041e072000700c070203d9449001c20391039514141c00130b42c406001a01040102c002d03a4a040d01c040100c201e0149003076035011107a91030004480400d0300b5925401c0d0310440c7c200300c2005560340005a0a801c25012188950b442c2014134080c1c1c0c8000b241280100b5030b000da13088039414507411010000c441400b400c400d000011041e001d002408800325841540554900d54840e4141040610384000310ba8090001501e0086807543c81c100c24464603980001402c0003c0901c001300080c003542203540000401003005080035a4040c08128400d030640d42e842101200103054a0f10604250001d118408810030184081001380552940541103545441c81020b00000c3e5050f070880402403000389002044010403c03110b43c124003400d80c804800a05d00b0018502000b05070b0000c503460186108030000c15500c440600d000d00540c0ca40d5000c144100e24041102101c15084028142c00040ca541c019 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 262774784 1250 262773534 262773583
    0x31809091507091a0306210114090c01021603020a030f030201060f090b12070612020a0509040f0518030c030a050c03070f0c0807122312030f01030b1602 67
    0x2464803003400e4400354040807030002d201540d40c0254091058807903601400d003c4800030b002010300c2c0e10007501c90a0f0404012145c65240b6110341c0e13400211000003000200301c001c103007403a41541100a440002c0180c0100034112100e42c1c0400403182c0a000042425450619580010381c8501c042d20020340202204018441014400e50044e000ba001000c0380281858035891560010321680790440e004404c5490010440e080009080d0120b800c141d07510001100c40700f0600000e504143d01e580b0034030000b40301c0034003603980c0c601600750300703110665001900c1d00e4951003500044108000c00810b50f00200328155050744080300721a101111800d22030340e00d16150306900d156204111000c0d000248000c2c00f9010081d004c90740c0c000f226140d02c1141d169036140d0b26409600000844000c01c034070810103003180220341c5c1e0002c058901103007000703031001c0b0044418108002d07801102c4445203510148018000c011070690015003001003060248012121080d01940d0344558003000032011700c0c0203051 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 262776034 1250 262774784 262774801
    0x40f050c0d241d07030e0d0e13020d09050d0c0f030c0f0212100506030106050a120f0f110a06030203070c030c021210050f01080312010b0d1107030f0809031809 70
    0x182d01040c0721030b9080c41c884607aa0540d01c1c1ca07224100d025001c014a0500c00f250328a4880d00490880075402c0300a000440460720040e40c01c503403c8480d00d904840c0d08400c2c8107917803840c1d00c003a0140440b071020101d00c3c0c81180c0f40060420b81121301c1b54003030041895034031011070300030081c1490850f854141100529854200300e1445095058000d40c0142041403040c40d0f144081000b0a04402802c01400a901d0744000c250a172600e6008640c2c00968000080046116200b501090301d809800c5244607104036858240c119000d109098414180c4903020f5001c03801c0c1004c1200041c0340c0b500d0218103504044d20014000b40d420b0002604000548090105569070082040b0190030a4400c40d818100c0d104007000151004940c5601003450136070000500c01000b00481e440000030843c081c201da800d005290320160880c0d02c4042c085a9500002008005650f0042c52103034026103800000d0f400c1640006c05140d80140500001e0b0030610419400e460030390740d2031540c81412110a98030366a840c44 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 262777284 1250 262776034 262776071
    0xd0e070b0a051801030c0c081c0203070903050606060f0306040e0f1b01081b03011e0b070311060a060515070204090203010204031407060306030519050a0203070311040f050c0d 77
    0x100008803040010080ca1a9410200a1400228140a00460704070a03001075044600c84140c4101103003c45503c5000500013000801c1c4404203121000008017808680c20200d81044a426003c100d00810610074098100001c0d40c2c41441100c2191400e00c042030008554000904441c0c051031715464942c200400c00d014000440c0c44e800c08507166032044900c00380700b070100b0311100f60126401c034003c0f0303261113100c540c14030000f540f0492a0b451a407070312020302d00c136140c1e182d10880340b03207804440840d81c0a48040101645070182d0750304030503101144065418150302038100d0706098a000c804000380e8940801045101c3c03685944140c0b550032a002081c09044903c000a50551000401004100c1040b82d090060300c0c00404417a03a00f910f4030400d90494000340000740c1580d0050100744808099803000035a2180314038141c03900e2600580c0801d1411151383c104507813030500000c2c0011079061603c102c42c07210000c13a0f41400207061040d0085681d214589040887c1a1510300164140803902e5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 262778534 1250 262777284 262777289
    0x115030f050309090a05061206060607030807091a0a030c020a020d110112090c080114040b041106070f11030d050f0910051c0603170306011704051006080109170c030d0e07 75
    0x40102c2c1c0c40749821740080b401004c045482600c52010895070b0b42e00003900141b018400c16000d0318280c580162614240c40040000b844034042210040380850001c1d055000c0700160703074600c042903031951032040c070280960303401c50042d10071503000300c040310b01580d244402d60925a0300001c0e110815285200101c510000740700c1030314044d6040034511410003940c0e40c1004100c610100c0208030340301c00e0020b850302942040d10041c0c4003003004008580400d0b0103072501d544154000707281c9450060541c4d0380c43d00f0810006020340b4940c3c444481c004050509006c2c000c04042e1a240a514021700c50355154124059911002d0042d4060001c9405090017276044030b404c80380c080710b200204ea0400c00d11501408440c00708840019001103043d03482d00841d015a4041c4078141c44540300d07071503054404080404020b00958640c841c40842c10024080c0b403080070080c0c000c442c00407a0020712810950048225400e808003000c0c01001022111180802502c410098190001c2036034030005055510b85034454 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 262779784 1250 262778534 262778539
    0x50c0a09110904050a0e01150e0f1905090a0b090312010f260c1503040302070609150804020301090204050901140c030c04060513080106140111060f16031401080a140115030f050309 79
    0x81c0b141461488c0b0941182e04641d010035802c1341665406042421007102600d2010186202550426801005410103a8482040c0089448402c280d48503291901c1d410b5520115542000918a212030384004d41d02d030251007046088214245041c0e00f501c800d40b2041d584400d800200072a40b145140280300440009000410110481150040c0180c0d264070070359044000d0310901c0e000056107800751250404561040a207541500e01c0084240c61107400100102c1e815580c3d8241c40005986500c180c90241c449040009401d01c1a0b028650b40c8810117454a4507000c014020402e043c0101c80458081d00c5080c1303411340c2c5410390301e440510030718103d401148082d400d094000c110101701c00d80c4c000000c01c007641d60200c49000c50480e641c030741d1420303110400e05810110005030900e252800a58a001e041d1078005243c1080917000d450300e500c01e0300540306070780140001c0b030b06211034425012000344075500204030141150380f640c24042102c0c840141031440500182c4180003080c8141d46920038007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 262781034 1250 262779784 262779791
    0xa020d03030606080a06060509060c01090c1410020a0206030402040b06071203050f070c030c120512040602030105091008071e0803120a060b091302091507050c0a09110904050a0e01 79
    0x12840c0c050042d0006008807030000c0e00d032000080e241019409100b08886071a2100c61400c0d240106100036038ac00028100781ca0f40d21054070307038002a04005008000c1050114104030100603e0400a180000c812050215030182c048440541c4d40c0c1011070b90810313411903001440d50043d60114001c0d01034408003030104c0351440034240311160103400c140d116a81001c003114160369074800559254019680c098002100102404c0001b00da0a0020500a0030b50a081c2e0030004454006270480e103080f5022582d0907004001000303581429903c0031b41048080e90102c6c909801c1c054a16540d44280c0300c3e04170103040803120f100880c03000450140180101006496035603a004019034a4000195060700095140000005d813403c41d03002940c201500050100c103003d88814005c2c1c001c1d4200c00340003a482142158001d01d0380c4082d50042400500c140098808680d0080420090f10200e500150f1034a041c40048a82c1c494003a040340c004000c102d5000803640c4035440108020701c00c100c044c21840d840c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 262782284 1250 262781034 262781059
    0x31303020f160f0501140a0e040204090204121109010b0a120f06091508031c0e01021603171f0302010f0201092a0f081e0309030601030c18060503030a110a02 69
    0x41010110041d1010891043c0140382c0c0c4000440f0300c2c0c48203081c2516079940c28040d81000f98850041c10502c4100200701508181d00c680b003220480e4800e500c03c02c89000c0d0402c01c4030070031280b803840300110304080b202003030550f00d0410307604424032800343e100c000c00c07910f072810001c2c81e800740e03203d91540c40e038a52080180c1d603120b10410000b0007405000d40c0752400a0f120004002034008116441c140821064110310300008020102a22114a0450555400b4809501d40780c4c400161142c070140a50b41e40810f15844482c6202000009480165801c0000085007400f0603000c207008212542843d0403005100305046c120300502192400030020285980886c00f0920340c503c082214501c045000c0c00030654400c0480c12100b81b0f0300c10b10500d034011400d94403520841c2001c0044031007030318003524580300d107080009042141c242c00448144101c841c062048803014207015100318070b6510308010031810400041d0303403802503c3c800780401c000a08020f002960074030220003095400b42c94001c00c2c48 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 262783534 1250 262782284 262782313
    0x270906020702030f0c0120031e03181203041106071502090f0604080a0f0206040305010501120c1e232205070c08041211030f010b0f15031303020f 64
    0x41c000c10342a40f19100388a01010011008100d940003580d0503110303601720020400907904001144007504003680000e1002c4469242900c0e1080207800c501449607a6a103400d4040040038841111060b05540c000b01081040015007011242c21079045004c001c8140c030000c000910a1050600040c040000408031030400d1a443d0003800a054044628290016208007402003a00803841030201e90f500908075200842d0a41801260840c000381140e40b815032030b0340b24039003981d5083c3e2010001d10500607a0100b482030314170135400540302c034443c001c850540f05078000700b032600c0c1c40c0103021180c11000c4101d2204688000351600c1d060313000d440c901040c0a4103180d952811040505a1906c9041c180081e034818850107641c3c40040c4d02141c002d0416050042c240c140d038030600c804031043d546c544014001c03a542006200c050303941020010520809123000d2010040c00320060900030301c440b0381c100d8414047c55090301d0f44402d0354108070701c170340301c81c0e003412850070349980c41076140ca0084504042d44071 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 262784784 1250 262783534 262783537
    0x14060105030c040b060f090409020a080610120b07110712030503060a091b11070909050a1713030f0501060f06050301080f03030f1317030106021e0607020727090602 72
    0x310021030545446610705010320007610000c040680d40700c0c0041208805031600603024081c0128003401c0014407210603404908188a560454510381c0d100780c5c00c1040480c00040300001801030100701030403403060744e41e80c0c41d11030030054410010b10004030390141d10710004110500c0104007003901d08080040900700a1b016070300560b076040c00758981e0034001c100d0056034020314603410340320f81804400700030a00342110104030340c08412440b80104100024051030601840c095580078402602c103000c41840d010068003501a0350143c242010300c480c11400c40e1512007001282d4100c1260b0581581519240e0300401c0c0d290801280c000740404080790441d4480040c505135103108007150b299900d0b502c881a9240000c503070b0000c1c400640c00004030809106407002d0642c91142c10743d83d0150150b4010820240c000342c00c024016032010103103031186100000f85c24080c041707000c003070140c13410b05d0030009446060034040c2802413a030740900c0c61a410000c224852401d02c5600e400c110580c1d6529101019 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 262786034 1250 262784784 262784789
    0x1b150617071505030403090302220b01020a05070b0c01090b01060c17030103171b010c030c0201060e0f0a1e02030c0a0908010b0a090509010603170415050a0504060503060d140601 78
    0x402a080005428004001038a106030b401c000100044400200000c83d2280e000800407002c0221700b5000000503102c03159803003040d20f0000d2807000807400700c101890483d10b080c1c062a0441d4041030a08010450200d5580305550500c9030329680c581c0548a42e50162111047c0100314011101c00010141da000c1d03405941103200b01200380c0c0c0e090311560b01e0380c0e01d40070078080500100e1000d142141c4251590004180460341841c040501d2110311840b682114000380070a00440d45400680420607420f00c9248040c1c9610300424415050810151807803100042c50703102101c1d55003069208180a0b1070511001072840d05095540345044480395415801000010b408079440d0100811071000c1070256580344100540001d034128078054881c0e0203008c01501076040340d5038911000c00403603d5840c21814100c2201c08940d079440c0303019005120703224080c8400f0304100040c000001d1540d03001c802c5404841e0586807441d140d4a03583c0001d80d204482440040648007541034002070b100d80800d18a04 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 262787284 1250 262786034 262786049
    0x14040e100c0810030312050a0e0f0c0a0801060305031e09120a03090e060306040f020402160f1103070312050729040501060603020f041a0f0c03070c0909121b1506 71
    0x103142d201c031010301510b03c07100d0000070f01080c0320050f0f03090f2286096100d80ea000116203004143d2140c0c3d0305549007003020700070000b185900581c582d6803690a0924400d4002c003100750082021b18515162651039000c1e1002043c003104580c0341400003440a40d0988018400c020042501c1940c120aa42c1e55214030040c100c011880c5031200151409421040e00d01c201c1000c0c3c00382400d03581e01e40c0d645145030400001241e020383d0910003d11034810041c4402c449512410b0310302602000c5040c00e41c11844807020142c801d41c0058800d00010348182c004e4051807050b418619201d585a01d05002c2c00c0d00d5040f03244020b07013483c0b030b00c40100f0141005a1406140150000c2103280c1e1103407130480c140e101e402107000d240d000420040010300c41140f00c00058032071120078103041c0500d11813441340359403200c02c8108540e80041005070070701c8240d5104400401c8030b07460400691005e82c0c3c5001450030502610420710009100132400058101c070f206004560007071042c04114251030f070410003032140f4003a690 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 262788534 1250 262787284 262787297
    0x4080f030c010b09010f0e06030a0b191805031213081c0509070605040b0a2a02091f030f15050703061505031308091306080607032414040e100c 63
    0x3c02810712800460585d064031550b494200d04021044202030406007071039426118909107980800c2c48108518002c158280200f41c504102c14400b0041c0d07680e9041117200206044a0000040d80000807200d00314042039041020b0b607140791114249400003640684020000240012803451901c103400900000110410858440c002602d5565030b1501034180803c02c100003d001400410b405082140381c580f9010300711000380113012403082c40070235020007480807550a46007107107040101d15034400d142c3c000c0c00507030700105811444030001c03510014003242229040c5d2020f1028001105904448201090060341841c440084c0200054403c2c03899000b01013100b502d1141c4507108032801110b40322041c08440a86484809069200141381a8004c021400b81215a8a00d0003030100408001d00903124a00d40034070003030243d5503060001d010600e0200c161520391142112034405441e61048001045160765020a00030a10040100e90714032038003540c102800f0140d0050b24810f5078580d0740c0d0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 262789784 1250 262788534 262788551
    0x10605090c070f110f030f2b1407020114070b01090c050f0d050907030c0312020111160f03200604020a05060306010207090513240b030c06180604080f030c01 69
    0xc40241c024410000d003c14220124000442e042c200050b04100c40204010507a0101c41c2c0000d00c0d044010f0703510502070300540c1184c90171a501071420250fa110350340703184140510742d8400030300c1c2d019501c0310f2182c581804910362003564481c03001d501600200c0301003142c0e144014100080e454400740b09003c4501c1c102140128030b680f0a00a40b0b80182c00101606e042100c020607100141000822000e0103206010001000c922154520001507008607800c0b003848501500090079601b540c91122142001000980102102400480015a0005007a21800e40185000c40b13449451440c01000c01013602c00c0740486030408150240114400c903004d60a50750744100f40041c90008407000ea001d604104c004001000c455004a0391200c0c540304201072142d042d036a28400307401c1050444050850400300300202040d1486407e440c0b85045006110003003080c070000350300b8415003954484032005942400c00e1503e801c03081d540a420bc0e803060342c4220001050259594000e210010025030030503000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 262791034 1250 262789784 262789801
    0x30b0f09070f120308190203130b09070e13032705010306090b0a05090a0204050913020117010e0a0c09080f06060901170307020d02060712080106020706030204080d0c051e01060509 79
    0xc01c42d0009600d0214a070341c1924180c81110300146010f401440d01070041484503d68070013144112854940c00d08115241cac01d040c03119a00040c08850700d98403445040c011901d0340c40a40307174000e4164200100502c4940740441e0f21082e05070b2190880309201ca0604044d040c1c0e17906c0c3d0b005480080c2d03410092a5a00d5561000342e0300100f03007180e000140c044042c07003a4100000c0c080d274802e90351000589080d03a1140464440042100c0031200c141c1c54004900c119a8860a4060b80c4280b00b0b10840d1994181408c040d40c000c80500700d001c1040c1c0e40c4444c114000c0c000c180c040e000b05010300903100342c604406080c1e43c40303560072216288941c59010021403036461a021000c001c000c0d1100a42c01d081e0a07500340104100c6607079059074042402d100c140009920040140038841c02e542e03c003500c55141c00000ba180003455004442031500620040c0049070001980c0c0701481c045240c00481c1e042c2d1824020704110011018001000c1061510241180150811001c0394000d90380e1640a541d844103 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 262792284 1250 262791034 262791059
    0xe130515012d0e0103080901020304081002030f0a142403060f0403030c020d0c030302031302040f09020307120302030304060510030b0109020a0219020906040902130603140606012a050304030b0f0907 87
    0x1107079100d8a8040c01171011510801c041c100510303040c012a417900f034903901890b1030400685c5080b1030050300001080a82e00c07034004201e811030340d4550244402d40303404041603000040101032150484c5495907081e486064108107484901d4060b040c0d61f400c1c03c0000380c160303140c80e0460b410b4001c00c4c249112181d45910002e0031501e44101340c0d2743c20356104420383c0c0490103544080c000701c03050795101e82c0000150b5690701c030b05036030400200c0c400200c2c200c4030300c18181003002c02c2e0b100e0701d8180200b00080000c00d4001c000c80303901a500800020703159940030305141d901c17205500302815500a50001080200f40d07030b4024482d0503611707000c8a2450150340303a02c02040030b1040c002508104650042191070070b0513040b2100f41d500c0140114007082d1801c12440846080b40d0095901c00660b400f030240b04102807181301d80104003031a14400801401222503140141031042141e59040c0d00c0083c170500ca4180240c40181d64044844c055074180b455100c600750105458850b8170340104c541c00503190210b40e0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 262793534 1250 262792284 262792289
    0x606171b1c060512010903090e15190806070507050114061f0c080a090302150f0703140c03030115020c0915040b0a09020c01051e010e130515012d 64
    0x412062910000ca12a001e18906031040c14004a854801c04101607840003070030901698040c00015500403a4100140b0650b034650003074100540003028403c00720090b0f40b8607201c11500795016808104d82c5900f448001015030b208500c980650001e0140242d0b1107001001e603d401b0702d0092254500784c280d050280c02090340ca055100e01c001c2c817406012001107202103075100240c20f000ea14048a80c5526000e684100340040015141c2e020070301c114038003d8441041c8144840c40c50341021050204905140304519000e4284030f800307040040d189100900302d4002c0300d003140641e92030b0b50355180603100c001d00030702c40c51016000e907410401160420220191145400603a141c002d08000d03c2440000c0150232021500a5400740012400350f120340000d010341c25001c000054a450540880c011003180704060020854101c030040000740b003c59101038000c0051443e0714886840ca1400318540300c14030700b19109407501c1d01c00000700480c00142d100180380c80069514038603c20081050400c50160 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 262794784 1250 262793534 262793581
    0xf02030702010e0103090210210e03070209090a0c0e0f01060c11040519021801030c0903050c01080703061d16050a1b030228061103091b060d060617 65
    0xd008450256105048240d925101814000340840c4203401240e210f2121015200106410800813001040e68400d041040071a000040024117410f540c0075403a0f1182c0003010b07208036003007004105800804e000344c0840300d074414054128241d640038181d00914041b5000d40400140c2c0300005021801069401c62403640008204621b44034542004000e00002c0c1c8100300052203543c0c2c8584c01e04c0903200030600c5002c3c041184441c222682d0004060700c1d0345201910400000c81d10402c0000c50001d2040d00c040000d0034800450b07a101d0b03c04500a246690182c00007080c14a0142e104011000080e030095007000c40c1c450441d00e454405660b14400d1040410006e08005002c0c01400741c40308400ca4000e111b44151180b84c0fa41d0b0034400c182c103a4100c80c400082c0c0ca40c110305000c02595114101c01400c2040c085800c51810000c95515096284820203a00c500034060940b241d5a22003280c003001d080e02c004120b03c5403103083c018080d4142c202c160314030365401c001040348003815007415400811034 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 262796034 1250 262794784 262794787
    0x3060e0621030d02070f110f1008151003090210140f09030307230d0c0c0b16060606050d0b040947041208070503011a0903100603120f0203 61
    0x20684007034803035101c08100d1650105108420251410740002e014007405840c0302d0f132407041c090610040e0516103030a814803620740e48103031149949520f000d240060070542804020740c1d0b01e0210007824082503011a641c0010b0a14070403c0712a010350040107201c0c02610318441000e03a0f040c0543e01000c10032030059600005000c034a0410102000406a811340901a242400d629a407221144000c03080c404d410000b066242c003241d100f0030054003d14072084c0c0784c100d0380d18840340c85049814509000740c8000042c0080c071650100508080e0050066100e102000865a03c940c0100680c000d200c40031103403330420000b40f07501d02d0f00380120441240c210f10308414002d0144101c4980c54100307802400344441500240840700150041200d003c60740e580c0c44003285c5420f1400f845517102030320200e800d04c08030006100009a10600396815504004296000f070a200d00d0703803003802d004011066600d442a40c549200717107032180d00560212032103120300038081c0d041c018042e1030020f030030201440103900 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 262797284 1250 262796034 262796059
    0x61107060509040902061b1e0c0f0405071704050601060221040b130e0103080409050601050c06010311032509110a0206040b0c09091312020d17100b041503060e06 71
    0xc00b075200b48004c9100505051a101441514030a603c0b40001c0009090b0802e07640e152440030007042c0d1540c20410080945489101040040e20306080c407202c5500882d503030750008070030b40d01501740c0080f0300181035180c0c2ca5514052400642e94407003400390b80014020741807403401140c002c2c0b01440002c09074640550030141020f801d01c910b600210f40c52407041c8aa1800020214024000e043c0a14040d5a1281d40c49090500c2e41060303400240040b4100001086000418500403440302d0543c2e920a44c489451041c2c000000d150116024480042e400494180100100f441d01c502e070440700c1d007460a1140030040243e62905000c1d00c401c010141c0c0003000020002030f40c910350264454442d0000303500b0102600c0115805d0501202c0e0a00591241c0c0c980409111900001e10301d8a006440285512000e05000800083e10004a481c0e032085071004641c081407071407107140c060000c9200b21030300c6030344d42e9560254982200c00d403e4046031900c04003160241d01c00a03103900c0788401030a50150650b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 262798534 1250 262797284 262797289
    0x70f0c0c090e030912160b070203061b0c070608010e0112170c071502030d05010506041208070206070b07050418150b180603011415070b0606031308040f061107060509 73
    0x2c100d03030303014580001c103c0b50b2459501c42c1012001c032100c020050420a9441441701384007015500000041c16081c00698010390380021040d07800b04a001c0460084152264415068040c040352100c2a000c0c00001258080e4003001c1c050403180e2030b401c0e40e00b0b182d0340c8008030802800c020401802c2c03400d180000c1400d6502a200a0032102c1022003180d09981e680c0ca96a003030540038440503001a007002451132041e1500d4041d840c00340c081162118030b05490a03c90518000300c40c1c8000345148004a02c1200b55918481078070000794000c8000d2a2502d81404010b1090f401030288444000440400240c44049441041300100320442900046400c10303113140303417a400491801002210355000c2006a85500c4091030007070080c651fa4400c241d204908020621001c031142ea140c10809014100c0460405404650010010343d55585c0c0e03500e40780402d01407402d5544000e0442000020006007031070344d1800c003c0481e136043e0f890b002d00d80c90000002d81c642c00c841c85510006001440320901c1072 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 262799784 1250 262798534 262798541
    0x70c020d03090515040501030510181107021201090b0a06030308013302160605070b06090421020307030f030509060a111606060e100b07110402071505070f0c0c09 71
    0x30390107401c1026030a941c600000d0400182510b200b800a0b101180401080d40c060250f80c1e08a41d0607120f142102d400c2c005100788031002c01f01544000c81c0c031441300b5413810200303108407009560083c00c0c06d0343c09221140464040c00c1540f40885a50300c1100004501800c0b0b03100e00b5041d2580341c0d5a044d1035034a080e510b0542c9040f000c042c9540f518070803841142d415032094070341d00901c419801902110b410200c5484442c0b00c154400c00604c0010840c0e8000aa40e00300c40981c060411500d0b165580c4441c10135208504886c1e40d6030060300414440e902c4030716000005041c100d440380d5100d8200001c4260210280c40c001d43c1e10050a07031018001c584030700d000e40c00c40818205103c060500303040c2102e0100d144002c038401f044d15003665420703090100c20181923046921580c0c01e20040b0039107203420b4840030144503601d00545185039941c0320b07081c0c66a41d82c048601c442e4014600c00b02c1e4940c8854518001e207002e5503008003150f204820120180c2c0600d4002c841c480e0806240f43c801031402c0d40e6500034 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 262801034 1250 262799784 262799809
    0x11112030a180b160c110d1a0108100b0d0f120e0316090f050108070603020711100e0301050a05190207050c030a120e0d0c0506131809051005070c02 65
    0x140351104405024030011007000307002103014062050403402c20040c4c00d040185190072810412803054001004505186103d07100f400d81a9040b1441c0c800c50300300082d804414810701100c40034200d00014000b800002d802c40c0000100d01e08101e00b20100c420401c0d881103210004090441d04000c0c04042000301802c40c01148180c01d203421350300b03860350000b0f0500400d07411100300490740042c180300b400458414030740301c050760490810165040401d241e6070782d01140308003020103400180c13a4082200410480341d11850143c1528001e40c00b0700d5020b001100c40d80b01407400f1790b1800002542aa885003e11806000c8001010b4090800040080080d500c5142d042c2c91903c41c2c9490802c142c0c404100c210000c03030182868113280390041d0001003c0203030703171030983c2d10900140000101091303041d42c268049a0084942c55914000002e000b1404d0307a542d804040e40d181071151204d0f050b00c0c20b0b000150514440d9054500502000803503008840701960b140001510005100c3e00508080200300d0340d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 262802284 1250 262801034 262801051
    0x11010b100f030609020a021509010b2202070c17010c090b03010b0c071203020303091009171b1e0c0406210c15120b123004031103070501111203 63
    0x24241c0e02c4c1c43d440380690b4011442440164092082c81c001c80c5030019240e50018814402030000030244030004000f00e0034800026001c4004000198113225558103e0700c02c50381c0314080184c42c980c1da10a40004000c00300070613080354244052401c5042c8542059416500300702c00050460342400205a81500b202c0140521842807801c0410b2640c0641300150304640709a0095a0360320303007800044d0520340040d10788001541010101c6002544500c0d0011007041c1840460303440b50820b00b081000108030050035811401015000d00508508400f1900001646021038100342c43c0788061008407070551154a000741044114007500c0907440c2c0b154541180140880d410b42c680310b0364110341e0039080000220101c2e141b161043c285000502036440386850446d00d08946484442c0c1070390316108110820f00b0f80d409124101079100e0780d1555030a82030800c10390501d46a903140d14103c0040074412038071a110340304000c00001c456129000b08803040d0404000740020341d01c0602c4058282d04060042c0d40c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 262803534 1250 262802284 262802291
    0x2010b0604030c060e060c070504320f10060c1e021c0203060c040b0711030f0d030e0705040501060507061a0d08030402130506030d180312020d11010b100f03 69
    0x2600c0d503944014002850240390b400026501d0500003034007900c041c440c010b000309800c1c00340d1f650303850303000c204142191419600410f4429084260b6802c541004800400140072141c45030025070305032000030700c545410084040325445d004a0301a004049118800c00a1130000500300000c0d1510844801101d5980c01c05170031000c0380d80080c41e41c8803010403515420032a81804020340c5400c03c14680c0200030480310500d041c2c1000000030882c884c21001502030b2640715081e10aa4a0422084030400c84440c2a00c800228549000300035011440414045103e2a600480e85180c144612412213081d515868034201440c3d60380d034040d09a001d00320f00748800c240c04420b00f0380c40e84108a4556441140c01c250749250901c100018034080f05000d1204520b08030400810751400168441020120b080180c1000071402180504845942009080741c0c040c500c2000c180b0f800081854110b2031700c3d102c8051902d4600c17050741c00c80b084e06c100580e106184001d1200840d01a00052100912a00d03011 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 262804784 1250 262803534 262803551
    0x207030206091b0f12160e0a06060e01050d02030415020c03130f380a090e1302130e0a0203011103060102071413020d0f1505030d0305090307032706030605210706030b010201 76
    0x10b944105583c7d10425240f40c1c15403c108200b000c0e4441d00000d0040c03070604071794582c402c000003003160083d421001125640080801c041c8251003405006101050100b55540c0311201c0000b5140d411105c0280c141505e00f44010505020b207040c3d51050352a6002c1801c0403040002010010025050904103905030540000310464046401407100040c1c1d621690301d024500a40202507900c020004101030800c1d9980c08016500c0984c40c1040440b440c01c08120080c82224076818181160030003581980b070314861011401501001c0c500c40c2600340c080c0d66005a4070702c985100c2904449000c1c1c2c1c01035041c1c411307100b07072503159014100410b50900001901103940c1d50a504480c1c0c412000c92044003088000c0146180c104000c0081300000e03e0280030714200042d034950340780a1103034014140302d82ca4180c540f41d02a2084240c9138001d8001002c2070345555010701800602260188a02902050003890f01c021942d510150021071100010f069107854002d00710028168064800d04654030740098 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 262806034 1250 262804784 262804813
    0x120c030c01052a0c150a020d0e030f160509060909031207271406090d02060a02030f030109050a0c0503060108040b060a0f06111606120504020d060207030206091b0f12 73
    0x81e00c0c0410b88180c0201180c4d2034010030003c2080c5480d809144121003049051110b5a0105411205001c40d062130415400703203070002400d18411407148200f620400c101c0011045001600d43e040398001da03000e1907191210424852104022909070140d503004120078440f1036080c00b00c03294403201607d044c030f414000d01c000d442c4000d04554020003004002442c00d0010b004610404284280308907401858030080502107080300005100103446414046241114603000f8012a85903413200314205a0780c0da150f015000007442c0566010440a290000c0c07502c500740518204c9000300310503102c1c0c82c02662640e40c0c0384034028000305919001084058001068490044d13004007070081030301d9080018403085046880e100455030040c95080200104101d42600305030044840e0100c580003141c0f958450001c00d40002d54040028003181c4001504000e159000c1391241c00707504180240c500648015010b00715011051a100e0303172040340e0040304c05280c40d00074a80700c071002c95141580c4100d00801c40 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 262807284 1250 262806034 262806097
    0xc170112060603120807121a06031f03030f080a060f0909020f060f0409050609010302100f0c0807080d05061e0d140a0609140a0b0a0914060c09120c030c0105 69
    0x444800300b590071013400246d80c0c005181a07660250b000c4100070006000c2071000107400394082403400350740c0c00008500701d515075504c0e84014034480c15240d9603030340d642c3c50010100d110300e02c0c000c000582401c000c50700d4410980107180848200207405543c3d10304001c3c09600401c00b40300201c0e070100c51138846840b02d07140c0802034003003010103624480e02c2d107113000318050641e400242503a215156000060005030348101d01d41d07170b25a84034030b040300610701050000e4440312540700c00904145408102d11042101c140000c004401c80c41906200c2c9886410600c0030342d040c0e80c2c424459147c00b40c50081141e0a1071603143c49428080c030402c5070714043c10000315040001200090320081d0f01c90307130400144821014049051100300e801804824030070307141e0403001d00001c0d007510b6281e1f49401001050040241e0a829803d66900989580342010700030141c25911800304c0301d00801c4000807026005070041150001d207000a00a416295960390045401e03501103170425154804503511245030310f040741d0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 262808534 1250 262807284 262807313
    0x4080d18060b0a092703140f1c02160303020a0516080403060e060403091e0504020c060f0108010c020316140d05030103021504031a09030c16090c170112060603 70
    0x1100000c2c4101d0207000d11080458035000b80341400e003050360a40b0441510f11190864400c100d026480001181c50110340c00340c480140100a840045450442114507074003c2180d2104103040511110303001c07001c00140e00980e01114174904421a1400209000340c0080008180900c0c000313140c0000c0010b8801020450102642e01140c08102071040202a1041c4006d0f69008001030420f841c00355030090049009003d6801d0888250b09003228072510002700101511005006540b1207500d00d02d07050380d07640c0c2103034150b80480c40c0100026000c41c043c0700b005100030b5558007a42c030709429010718014109144108070303091540e0b503410003000c550500c0700001020b1240e68440ea43e515500411003c0045128546000b20041104000180450001b04107050899050402a54444002170301314003903140f044030310340684080045034034202241001540d414003010000e04500e030400311900c0013502031040541410304014489060f1441540712600c1c03240c040499403607120303529003030001ea114 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 262809784 1250 262808534 262808543
    0x1810080403080709050307061205090105100b0c011b02100c0906121e060e07020c1c021c050118051203010e0106050d0905030a0504091a01050406050c0a060516090902030601020604080d18 82
    0x2c02752800a13181c2c055940c10040c000002e2025040c00e00005940d0166440b44251451000850b810217920a412400f0b0f12441512402d10440328000065200c401e1540300450302da2508048644040c0181c4001040d1a841c1e51808000c01d00908a4802405070750300440e207400104003401e07141d074030706d01601000c0c04403400502c259040c082c0020f440c000010480c0b41c4900c00080500c0500300341c112149003e41e80440b1640c1c000000d102410000a5030440080e00a50800303c17a03001f100c16005403405014480e0f4202c402c01c4100b080440030500088c0035403074942c0b801e00010404c10340f280c00649141c40e82c0501c0060700c0b5810745d0b2010300c0e60384160086400b184010504000b899654410082104c0c007000c481e5031440055000200340d0720560040720140200072900840c10307041081034803038441d07119004000e07a0900040d49080a070580303060600148240300c0100e80c94916000340d80c05444181c006105613107480c0d482c01541c0e003010394000f4865a59082625203031142549504146000c3d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 262811034 1250 262809784 262809797
    0x20306130c0902041d06061c06060210050c1b120a0f0311090d0b070504050607060e010e030c070312030e01142409060402030405010207021203181008040308070905030706 75
    0xc1e1504004940c0554010140c2d140f0500081000d1040000140d5641001003c40c0110ba510440001d001d40a410311000d20580702081599490380c465000401b038810035001c560046002d060b000040d100d003103c152840d48003e00100e0152080c001d841c40520f501c080644040e2a5180402032030354000d512208000341e10303030040104407909449007100f911a04560140b6024800000c120140c1078160003c04a03000a400030741c01038443c0c000c0d80d01520700284803d50300c1c2001d00f8031501074603000d1600380b078951034043c500d401ca0000204031110342c0310000c0a014498a1615030784000290f521341d481c281a11598081c060841c20312480000c00c0420503807001508207400d000001d001460301095520b003d00c040300c1d06680c0c034a665140d00000440300036075655554941903029020300380c0e0082d00b140506828848a413070100140c4040d07000b4110300041410740720200f024140c2200a900c012951800c0454007003846103414582c070840a0522142040d40c40001c2480c3c01e4980e4403000001d00d0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 262812284 1250 262811034 262811071
    0x903120503040c0b030402091b0903030d0204090f02042615040b07020c09090c090c071e140604030903060c031418010524120a020918210a110a020306 66
    0x6421000c4070240845138a00350541c50103a0211b4403190024020035030307861030100c4000304000380e5801c48450740009820f881d11201c882004a02941240c01395041c100d08000034034403044428800d44086842005801041340825080d028140540444261850240c03040602d42036000241e400c0c0140d00c66001c0c8603003841c0c070341c0000b82032200c105081c1d0b00c01d40130001885102540001c401c01418421518003196880d4906201a5071041701c000600c1d207008c909111502c082e0785030400f001a8001c1000640603046c0714155078036011b080342d00034003040d0050f034184049602a4013050042000307007000a00f2074003100c2d040d000040d044504811420940420020030b403020b006a90304002c6404484620210303d1209807502c0818140782c80c05020140c64007010f20703004010b20704d03149030090701c0c0e1032030b60070725107680d803c00c0c0a80e540000403442820a120049855010208812480e204416040c00d50100c000c48545001184a251a2292855030750250743e06010031030244401f40185c074500c14 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 262813534 1250 262812284 262812293
    0xd120201050a090503180102031603020f0d0203130e040213110406030b040b030d08090a15020403020109050907020601031514011404140405150c0c0a05010b030f07051f090312050304 80
    0x4100500e56840c40c0e08003c180b400280002040d02d000c88070310b10341da81880082400403451400752800451300f020580c21128149078002ca804014150007038255040754aa00c0d074286c0e0f884c420045001441e425002c4100004070300d425485030014801016074400d04a190340410031b0b240e03601604201614006010001a6007511a00202d000162810311000e100e5800081d02d0315a03100d1520240081c1ca0005030801300b080c010b14000f0b56002c0300d0040c0350345844103c1c0d0f0094205000c104c0c0440d0160307101284a10f08000b00b10300c604e00342d50041103281c1c00c5503594013415810700c0e080017490740c68a0b545044811035505481c003a18030800b04900c880419400c00c400e40d180807070b0300d4a210303003000141b202186d00441c078107071501c544c8241848103032600040b5034205d100c1c02044d0221802109003050070081d042d00031a40d0a07108404844c2c2d810220418551103210307510075a030380b00c40f07a20805d01b0007016a0164800d280a035060001c0710b036585e0b4981c502c00116040136a030004100008000810 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 262814784 1250 262813534 262813541
    0xe011506030e07090c1701141908061303020c10170c090a0b07151a0415060507060e0106050406030807050d09120209091c020106031103030306150a0e0d120201 70
    0x10201881c092207402c4081d64415103440c8a801015061610380c05501c2c111801110040d107800f400781c12801e25507a407004900348000521400030310412150100b1440c100c040702e1003500303807800342c0d018049588401c0702c101140300010000320298020810301c668a5070700c2004a88606030541c8560f090300d0a0159082d4201700c00500b21000042c080c4050501610703005da60906031a1044400c544d5180c2034202803000c80c9141c00c0380ca0205003414020745a96200b58034210344c03203005079001e104510703030305040303840c41003560142d81c0000d43d0501a00c408120542c10440741c294900c00000742a0707803144040340a9031115081a500c0007000501d11080140400c00f03403003074600c0e51804c50601e50400d0014903a0958241001e44144600008103000300c106001c440034518407a5140030480c4032000c0d029010303080f03501c019124421101001c00d50b6050110850344119030040c4008005260150341c3c0606400c1602d042040102081e01c016161302da120380007081d50b001d2000c42c066081070b620001d094 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 262816034 1250 262814784 262814789
    0x30c070905160906050d110315040c020604030212160606090b18040b071110061e05040e060703020a0504081209040e0d140c0a051515090408030403030506040f0e0115 73
    0x102c0320820007a5100603030110140054840515000780d4500181d4403d101501c1b50260060782c5500000500840501e10324a8425001c0255001c3c00700024484060740c0740c8804550160240c0c1001d1087d0445c0b1001c0740041410703504190f0540c00c4003665880304011034a003504109443d942d100d07400c00f1703540340c21000c03030b2032004801d01d2140f100d1a1a54610a001030701174103010900100141c4244065418001c030141c0740030102c02001150380d15100d08031030f402c8030718110700901000f60011034103086ca030194804200b0300500601f65520f481100310006d51000c81c040c820000240b10225500c2414842d496902e030070803030000d0301c3744084c6040100322800b102c23218446500aa002d40301e400d401c01c421060760400040c0542e128126400420300704120000024401e008202d42c1c002c894046000707850283c010000032100c1410440180460031105440183c8a0802440040d002034440d030401540600080d0000c191040b1003034a017401d80785041100d4900d43d4503007150054000720300c45030500 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 262817284 1250 262816034 262816051
    0x20f060a27120e0105040b0a02070f21020609030a02090f0717060904020409053903030406170714041706070323090703240605090402100e030f030c070905 68
    0x15070301d005075282c01e030081c01c0c02c02030020b0101c43c03089080581e01540036a401032841020300c41d030f45c506450000351034040600030164110050072001c145040e0b030014410005690a4880306664141d40070480300d50400c07078810364140b00c1c88a0035001238558400042c0250344503514041b090820f4bc3d00980300180e04000400006d0054081042540c3d031100055000394040c2c40003d685001400c00c0c6040108000c088042c02084a02e00100c0d5040c1510388500400c0840d41c02c03071071000b140e04060308c03841a842000001043d24100480400c020000c10340c01090f03e0800250780e00c03098165655a42040d805031300180204403404424034018032a0307540c00300e600c0c40d0030441134031020160700d0001084500501c96000c03090025010260411100020790703042900242031038000c44c10314132408840b611288560b418124001014100807030418060359004004c4420002c0c9540225250a0382c1c0004079071500c10601201c2200f6401d00041c8103c044040243c101030741000d604206450000c0c01550 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 262818534 1250 262817284 262817351
    0x6020601030605090102030402180426040302040b03061b0d020d060902120702011e0f11220b0f040e07050918090f06040f060b01140406020604120509090a0507020f060a 74
    0x40180e41e4031504034500c072b00e40041d220315900c85007803119030700c4100c12400200003a10072806000640c4c40c0f002c0e0040341e100720743c18040012803a00340f5403aa501500d80d4450788401c1e80207102c0b040c03142c8024202007413800b40d005061011b0640e40c142910125800051060f5000510229069541d5010303036011516000900c030f80c0880340c50f51f5524528800e00600d5055a4580c0002822170a1b001100002c000c00d041540390780080f415481a1107509002ca01c10614a040000d0340002072416035003c0008402d0403410f052074114140320703c51004118400f0403204003c048900c3d500d044550220700758400019106140c1002c0241c0307001c44200c06981103034445000c002c001041d40318541c80ca2781d0720075004500c0103425001a1003001030410901303210f4502040201c0c556600090b00c6110718003495102d00210180e07101134425100b80c0d08601d42103a8100b0004d4000c201c26040305c0c5d009011841100e2041030118108d41c10400203503000105c0c10384071140b082c0303411034013101c5003808179180c0e0070361 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 262819784 1250 262818534 262818541
    0x302070510060905010518060108040602090a0906030b0a0e06010e0112061116020a1a0d09060905070801020c010b041b080c1b15010614030703091b03060b01030c02070510140708040602060103060509010203 90
    0x8ac1c20340b44010b0005020300c0c0c000812402c580c83d060100c0c1d0081130b202c0c00900140b03840340b4000c0e100b01012030381c590b00145001d080501404000607192f049460014140c21680d007003900d5220f03200444842507501d03d88841c4404580c0710751a004001c04000700c1c10001b0010500e00c100041c6045580c001841c065004100c28030f85001072084a034480c61480002480c5100e51400102030005400701070940e010b0900000b581c1034040d0001d014000348800204220800c02e01044101c034403441c4540085800c0750104105e00340616161a003184510096604248800c90000501000c2041c00782140d0026030228a0700304007880721501420250800d18203450301c01e8140046408002d00e010109525044d150050009090110000e00e0801a03800345480d181c1c140311014008800740d10b40007038640f4501c4081c0507c0800d0440650358000c00031003000065130401c035098000010f1750783c0084d0341000041c4c0081e8501006000030901900503013840d42c07440c200013040784c000910302003c40c0d0042080 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 262821034 1250 262819784 262819787
    0xf0e10020c0d0204090b040807150603030906081b0406020c27060907050418020a08070c020919020904021912182306280905030301050103020705100609050105180601 73
    0x50711154000d5649060307441d9140006409000f030404050806089a0140814090041c0c01848010f000700350100384030904540e031504882c0d4911001e00024446207003802110b1069142c26041004500c0d021003070519400210342c90307841a80818096446007281c11001c0c240f45408503400d40d01600c041000744400d030318510f03003003800404e400d201c0c4885d10001000039000e1800c3d83c000d0121107081c014891410030600e8020740c000000940410031070b000048100d449465413050721580905110f0702a11220121280c1449004c001d26400d40c02740242c1c5100d403610b1001d05182d031917844c0645c024513001807014000c00f600721076040301c041c105103815141000382c5849050260744500a43c00600104040d50040511030409140310300651003800b01100321009451440c00e82440940140b20511f20081c04071035805100038916041030004120943c041c1d030290891500841c1540e400805e41d191040c2251016007114071421380d02c00040c8443c0c10010801881451904080c80310307820442c00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 262822284 1250 262821034 262821043
    0x90b120106030b0307030b0703061409150907140d02030106090816032006160210180e10051002010e06070e0303030a0507030e0703140f060103032115060f0e1002 71
    0x841c801e042d154001c60081351410001c110045404c990000c0450034210b4001f0003820380c40c8207001804020104500306490012642801064802c4840e001d00796101c2c00e0001e4107a000b0f14480511054424641940300d1200c000c03c01c0c03024113100160790350b04203113000d407031640c85810003150f03503021000c042d2030b0f01c068024031015260001c184403a050f0040040088104441c800107800500c08101c041c0344804115001c242c01e03200310303996405a000d40c50225000d4000560b0740c0481542620200308000d54642c490b60400c0015484500c0e5070388482c00700c0c8606280070000b2005039510803445d0058807080c4045a0400d01615050700c1a0240783c0010703569000117000420240d5651020404446c0290701c64640395012009441b0310650301d0070404001d400c4842103d665004a1980d03035405400881c520b030507a0351540740c0340c090919404403140c3c07800d191408003070210f5036031000b0344100b240c03020741c0b00040005030342d1000480350f07061005001007001e40025000d142001c0c45d0882154020a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 262823534 1250 262822284 262822289
    0xe0706030510090b061c0f0204180f02180d0203070801050c0307090b07030c120c021203071709030a080715060f0620030307030e01110c060403080c040e06010809160b0307090b1201 79
    0x210301040b000e17064440c05005201f01646100400d10005001650703040510312502d038034840004c20083d0b40702c0c03400c02400703a100302400000850300f500d010000501d0440240381d03c841c0041c041b43c8400f40c6a94085003140c60035580c01500d0000481008a5907500c002084054542d00b03113810704040701543e001c0c01e00c081c0140002c2040302011020078520348580e00010003036800402400403801c461003010b8590f4402841074969040c42010b070740b00c0d2022801100c4a40c00060300030400c0a015071103000d0142c1040d00112241d407400c0781c00104d030040c14003803c4064215400800c20043c540200508801c900c804008070740201410000003245011050f40d1340300103503003000b08071800711040e96401803c4003804200c0c15003020400500404002410500c01c6100c0d803241c22081d141d0000d101040c3c0036610403449001308800009059510502d0000d41100c4044211105001c1d0006180d99080c0550842405410007100b0018525406000755000b01480c05a003450028801e808925105050 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 262824784 1250 262823534 262823557
    0x17010605160b06040e0a0b0709170c0402090d060e010b010306050d12030c050d020f04060305010b07051207020d0506042006090a03020d1b06030923100b040e0706030510090b06 77
    0xe400543c1644031038110708004100c2c407054407141e08881c034102c03070300100680e10b11001038500c14000c5641c05000000b440e11f03c1c020f03001004510380c0b44042001940c07242d41703c241c001c0441803e01c0c0c0000c285004034405601880e00104aa1441400041c100c1d0510740c05103114401011502c4042603156006e940d940300e4601d804196401004016141c03880307031152690503d440000c04100d40c0c50440e01030019900c0542d030900c2143d0344c89005a000b406070035805403650b00164400003500f10003038010300c00c480c400340040a400307900352034580c141481102c069584808498464038000000c2c560340182d42d4048441c07a051000c640c0114480c50010b00000b4040c0807c12540350074044d6201e210411352040840c0403001e2510f41d00010040c088031071007140d9190f095145a510410003020480600d02148001c6c45900c0200c000800581000103042d90810394035604040402801d01070310028103103c3d100810682000480e81d10191410b03400040020310f02005000b50f940c1e03000844e4000d8806 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 262826034 1250 262824784 262824803
    0x8130b040b090705060d050612030a081602071503020c0106061817030d0207241103060d020d02090c070b0603030a021f020c07030b270d11070806071701060516 70
    0x212a00a0303c0c21042d604600e0f03100201085407803444620b0b40046225110a0304e44203082115491800ea0741d00a011051011030b15020024151118000c101c45949006204541d6031a548031924041c100310071520300c00190300003e03400340c41202402194010071142c9010030010700b4100b4500034041441c091090225000f204086a80c0340401c15216540500e1074210340c1c0c1da800b803915907000e1991901c14a880c0d061440f141c038840b0000e1161a51010301e0501c9185565a07039010840c21150242080340c1c40806028800056110f00103040d2090b51224403460f9200780c0c0d0b040c562001c1800a040a1082d40304010520065074007040050703204c165501c03600d00d030701d048501a40290107460b400460910030315200006022502d5041c0307005900c03100641d04048427802401c00003808203104001640c0c440e612210f5040c2c803804000e00e40f68900310642d800d035600c0710300141c2070000c19600d0100160700c0314058a03920314202105801054031381480d07881d00c0c0500c1c90303a40b107044200c0b90180c82e100340c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 262827284 1250 262826034 262826041
    0x150201020d11030618040b01060806060d0c0305010807090b030a0618060c02010c080c0a0903020906010215010e04020f1903060216021002010507030b030f0709090606080304080d08130b040b 83
    0x35016100311022030141407242609040484410380c0086400c0c500c5120301154030f40040c0b83c0803220b41c0c02150031401040b0325a080c828180d41c40100504007e400002c10045805400410701c51100841e8032507030041140d51401c082c00d80340c00503c4c1c000156052130a00c030f20241d030741e0004002c5011a40300c18003044050842c01d01458507501140c01070101d9051203243d44071613038194000d05061056440d4054180c035000003480c01c1e07003d10480c3c00007003205900b041c03002d840c00390a10f503401141417048607030315007540d0741d00d90980000382e10111442650005000451610303804800c01184240c510041c0b601c12000014401c1943d4800509482d03400035007480c142d030700084200301c0790b500908020044003007500000d000f4282107851b040040d1900c0c5145000b803801242c0c003405401c10390000d0105505004050b0000d245264086a500f0340d07403000010b84640900241008250240180007415075441c8040c107020780060501000400c84482400000c10042529403ca46c1080d0690340f00e0381d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 262828534 1250 262827284 262827287
    0x9160512060a030f1202011103060d0b04061e06050306010605030f0705070305091f0e0306070c06020f1308030408060f070507080912061320090609100308070b0106030e0c0a15 77
    0x15100c3c2c10103000c3c0c41c014000c03501800b00c030140c28111100349600030410242c000802c03070368a0000361400ea52200a290039078010031041201140c00601514001610a0313814500718031a401203403881c1c041c5030300c1f1a000c015502d418040a40105102d0401501c1c0d8070388000b05e2039a00c40024142014041c011a0030000d15200704161400c8410140140c001c04c12448400c011882401608000103550719011111505020800a0141009403100c0c0003654041d80c5102c041c0d000341d16001e651600921030901120000904040140480000345642d1400c5c810100d0071b20400a01e441c0c90042000203006403241e00a013121101604003010a84440f61030001a00e000049803460160341f10704c2c1d051103001a00d10503900c0046202d0108042e5a1007e82c000c00c0132915203a044551004c0c4140c0095214108030b8a075a03072005074020711060003602c130340c0c40803e160816101664190340050040c40f00c00d405110b8400540582c4004201d003000400000f40d114482d4001c958000030044102660507 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 262829784 1250 262828534 262828549
    0x6012603070309080c030106050102030a0509042405010f02030a0f0f030e0105010b180d110d0c08060c0a1710031407080f031305090106050708070f120804020916051206 74
    0x41248810349a6504060600a125181c1c5004003142c40c003404c0d003641e07401d18051040000f201c03010380141d03007058490710081e03e468000080e40d94000c1d45880580011080c0300c8a10038030384140900c0035610700d0400b00010a121058458002958000c1000014454112111020300106442c2190b0200795000045001e003007403044800d115800c04001145441140000e024480801140107007101460000c03c10040545840034009900c56000c0300b145042503212000818010482c501c843c0d50340b41d40f00ba1400d0401c903805070301078134041140c1c0d0001d0b03440603e1041c109501c11061744181403003241c1280d10540340c40000c002d22000102c440b10003405004500080103030f1420784103c0d60640c00855241c0c1e0040c3c0103e102c840381420003080500c2c10201c1c1a0684000d07680d55401e1140c141e862a0b6254084002500c1c0218000e04100c0013605a1034200ca144200b036a802040381014810700020315030151001d00c90075840c010041ca4594020281d4124964001c0306108640700e440c086010b1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 262831034 1250 262829784 262829849
    0x30105150f03130201080604090b1504020c07060f1b05030a0806040f06121a070903081e0d0b0907020105011203120e03030718050103050c0f070221010903020c10020601 74
    0x107200002c800c0102c40c1e81080b040c070440c035000ba00d4400159840b0303002c210440d100d244d8024021103114001c96058140702911010361074015000525281c004040e0b1807500c0704950000c00050b09204918006507441111010000100b45041c650f0700031680c0c030503071039000e1500b040c000c01405000151582d40c5a401c0400c2c48440c0301030400c1b140e0b0711585408103440206c00c00303941100816402c0d60030441010121441402c1507075459010034110b554240c11640072041001c00511516000280902a100100031103003001c0300004105901c20140700f0440b1000300000f055901d000010400a0105100c03442c0140d13040c40c103080701416489040700240380d0b0040c2e4a6440c4400700070801d408d50006c4154a49540419a05200c42d83c1d85004400b641c00440b100a8051418452070384843d1800f8043d11101c0c1c401005190300b0080603200c90305626100c411006a13a466000c0502450f03014424107501c03000540300c0e40700d10b02d10310700041d5803864184034211307001c2400c0d0212a01c004003046070320107 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 262832284 1250 262831034 262831057
    0xe0a09030c29090a02030712050a0804090e0c0f060a03020702120615011b050718180606091a180c0d14010330080c0d060e0a0b0901030803010515 64
    0x1c0000741160541900302680508090400e002e00200e4800000066440c41c1c0030b500500a240c1c0600740751614040041481d0304031080e10907441110006a1050081c10140c00544000101803e00b0940d4074a400080b00405001b40308000300ca0040f51a44411030b9001511400c0142c1ea0345c0551000c03813113819000078a4840750140205020312070403008002c14107003a007640c03103865040c80d040c81410403112000c4010010751001d1010800620b60005140c0c961128850005a50a945040b004240601001125070310b59079282802229038034031540e401c01082e141e0381202000d0800108040c1c00026051080302c0c0b103000c0000d03461007500701c100e6100800103202403001060700c0c2d4201d10120400e000c12502d0143d4071401460006000c1d1046201e500e84101c2000c001858113800e031240d29000d002c0a10a0408103c61001605180070307000003842c0201c2c03140340a01d0301c241244129450004501d102d041f0720001040440e03662000e9a06407501141e8003c250460002e03c0c0c6c800d44030b9860760f00e2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 262833534 1250 262832284 262832303
    0x9050f06041707061107060203121503011e0507090602060c130302030a061506030c0f12061d0a110c03180a0e04050f070501020f07090e030403061d01060603060e0a09030c 75
    0x400b4400007080400443e05151a1500b07a0680e407000c5039166078040c010700e00140d0040c0480ea0540114078111900609490030900c440c62100c0d0200782507031240c0c0740003443d900e00e00d0800d06110b2102c1c03085941c080328514021145909210001f034840344003405800c00c01714040b49034450b804180c4001e0000b141c0c020708881950001d8604400500884004900b0583e5403507800242c09001b4003598080d026240e0b80e048008442c4c0703e00f510b070720249542c040c1c40781c2e036074281c013065200e089200f24002c0040b0041e12030842c94113000e0712080d28210100121021400d001412031178000105175084450800c0001c1b51546400010581c07800b4554410021402454280000d01c940407e402c01010480401d0707885142d01c40c00160790350f8400790b4074000503a1000504104010b207580c84409503503000030590b0304e050368944070758060f41c54804e111402d0100c103131951414580b0920800307005261504080c0318182c9400c40b8808403107030080c50b000c5e034580c94150b0076081520445810806503482007050 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 262834784 1250 262833534 262833569
    0x1602190212030c0f100f09030f030509120301060e0f0d020102070e070215040c080c0103050411040f0e120309060f0c0712020307120306090c031503081c060806060f01050a09050f0604 80
    0x4661710440b0280d8408500e161641c0384421002c0750144001d22030301901c6003001240c0303904080f4000c000040ca403404900902503080000040c03280290300030401550b401d00c4425100c01040952580c10144521801d0f60000180050342c02003401c0c01201c00c9101891307015901c0400681c1800c3c9403003c0051011208070803c010419150000380139201c81d04203c03031141508000540843d40c0075074000e02035400880700c84000e444c007030304225264080d0100206540184001e40391408642c0040505000400300800c130729900c0400c0001c1e448440c104605259060151080c2014411650081c0482c07641c0a40c140c50b95000b0011694010f60045a00c454a144414020001c00850007a032070864100080c3c204851f110b40602804c00d502040342c10151443d50f41c442059600a600440c14110030f021041030f408040c0c4601e400402800001d450580f801d2020005912201c07903189060250a01012028544c800480b806854040d140710f02d0b29071010380060100e02032544195001190181007 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 262836034 1250 262834784 262834813
    0x50108070f1d0103060209011809050a0524010f140d0c020609030a050910022a0a0b121302061b03091504030b0f0408040b0c01051602190212030c 64
    0x200300858100d44203100400d52075020941842e000301d5591080a9551001407001c2102603008000030301381410314149140103501d85003008802c03640700c03000c110354400801c0a90f840da4000c4651203030120380d110441d015403107225400007a44261250400006001034508a80144031000c008400800e03540d88500c800000c080c003400d4150610350040c003500001c5140d200e4008152680c900075521500e0404125200b440002500100b01d02e0441c45100c101503049070101c540d200380404240c01103266a0311390070a2184001c090303841110a0703c010071040c0400604103c91640200342558036481c0070205000040d03c03400354809038041281540d40062042e14000010001c003142602c81c0b02d614115009564810b008904c005081103044100007280c0c20340c007260140d0311a200300006400c1ca6103030700041d251034021920000c616913446061005043c564542c13042801c12902c02040e1401c7c0c08010728204641c0324100901070391421400d01c04080f420b000340e823071081204044a5107103003890704 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 262837284 1250 262836034 262836043
    0x402040e0403020d0e010c080708040e010605040303090501080f060d0c0509090f1905060711010e01140618060f040f0219031410150806040b1008070314160c080d050108 74
    0x1000c41c00b44c840c5042c0070b080c1c140600e40c8801117801c142c444946806030303600d48003055030000c03808a440740000c20004c274006007040071807400b801082d5581500d443c150702d40a055402c00d608130b80d05010605c4204500c140f0718220030780d4000c0302038038111544002480c0124414229411140c2e201c00b0344420081903100018009001501c000101c5958009104100007800d10190000c0c010360403003400210020701542040d24141041d000004449600c3c5550030b08580c582d42c00c510341000000300340102454003004100c0300728118880f01002d0b042040005510181800c4500e000d107855000f5419002d206a05403081c3c940d4409042001d60000d0720001c005190f03410054401005900105401e10b40c1441e0702c2c1c081d07074101080f606851400a60503075801d100103100c0c0340d0190315000c44d24519180d000b4000d00001e2191a4903910b400c1c050710140c1070710928010115090308400400800024482e003844a005181c10700b030b0484503540c01c044100d03101d00c641d0115024205000001c54200000c0d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 262838534 1250 262837284 262837291
    0x60308090f061c05100305060103060c030f230c040f0902040905090a0b0601030519020d0c0e01020a0b0103110111070e0a110c0a1203020d1e0e03040303050a050705010b0402040e 78
    0x480445000e02004208010350180c0c6014a002643c0021840081e00302c2c3e03400b8580084407001d0711a00700f03680743d40d000d150440982046400b0b03a1a40b03602b035045901130280d440024010f140500846c04e0102d140c0c464800301d607074402902030990340859084682d900032035010303000e58401c01c03204640b0b40d40a01c01a500c54444c002a062600002618008011031408500c2d42d01010000c4113840d0b40700110050440980001e80800c511100c003205950b1034070081910000b07000002c581d07601d00e02009004010344000140c10742d049561107500148010751a141540c0c0d01c072000c01031211400c401207540c0061266010900d00c11841c0101c1c0700141031a80034465568814207100c0e5958000e9440381501a802030501158131289480d4000355504020a024207030900d80142403280300c0700603800b0399100d20034800f82c020381b01100d03d098081c940591203416040d0030055161600c3c564005040e41704621a44d0204040803e881d01000b00a4000705102c141c003c00030743d02e6a40380e403a00049014240c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 262839784 1250 262838534 262838539
    0x30d031409010902090a0203060a05040c020c01080c0c0d140c160918020f010305061f0e0f030607050a0c0302030c071d160212070819020c03060c040e072106030809 72
    0x5010a905000b42140f00d980541040c859441c1e038180f50019401c0508001e81c404209800810b8a84461041d00e00203215a13004009603001907001415111b4040e01039000386030100a01c3c1ca400000041c1050040c50603d4643d00a1080c510380110358002d0038082c07081c501801c07c15992a010481c206070a80d074200c4006c008401c481c04203a0071290081c2030080d00198084120404d660103544426403040c006000900c04410f54400c030962000b088503043e011810600e251b40f5141403410105008490640080c5024200004094aa4050032040104200341d40903001c04140c402c0c010380f19481507031000c60700c0c02501c500d07203000000440b0f100704148004400004495804120382c09880740b080f600a0b100030300c140c41880740b95031b002100981d1750900411801c1250360492440544c1d07051903901074030308005207600309414810050110001c1c2c21092000b440004a22251282c00031020b00b041c2c0b854981e9a4030240d1360035000500c81070364030701d010360010900098900030302040c4800c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 262841034 1250 262839784 262839821
    0x91706091203090c091306091401060501110303060409020d0c060504150c02011e140c060105090c190507330c0c0b010317070804120506010f0506160c05030d03 70
    0x8a29071903060000319800307009580300391040d6640d41440190b05400082c04900503807003400c2d90700ca0030f0135200070794812900c000070712141c0d0500c09803c1c4640005003009290410709111b001c00b01a07034a00000d0f0080740708550750302d1000c04564540b9503e08000f580320361548003039661420054000c1e0850710070103900070102c401c140c140c6846020450480341d4140c44500000e106c1400d200f1058548880802c18082941c03021103180110102901e84025a00b005004540c108018002da8140c05450301c0f81c214414840d0b42000213003e00441184d958514040d61100024240126400b1003003e00e110505581e040f4020f4002c258903004007007d00d611001d2104c1910003004036801c81c2d06580250110f00c01c2001440010801004501c0c07003800d14000c90f00707219903500d0b4207031258044e6120711021010429a0343c02c01100b440603a0060012140c5480e44524040104990b40300748000d21b4070104d083d400358010024080f6022000e0304000e0107c400c07070003e4810150080c02c1c81b03151f01c64070502d0b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 262842284 1250 262841034 262841053
    0x903010b0604030807060c11030d020711150d020a05090d0f02010e09160503060402070209240402190e030109050615090a05010501051e0f030a020d050f07050901050a09170609 77
    0x1005801c4408a07540311130450b00d800030315102c0f1030040180c196600100900381d00820410398042014200520b01810016914042442c0c131a084034a100242d87c0201c961454408100204c081030b2003d03642460b80c00745e030f14001d0311021151840340075240c40d40861003620700000d20000d0701540c03403614404e0301c990481c06a1241086400d980441c0d0500010b0031803000c980c14644190040c5400c248054400341c2090517540c0081d8a11100b100c01305e10260740c070740c1c4800024052283d28001c411055404510b0300040000c01e180442c03808100d0003c0c01021a40141562407d510012216800005480c0e4030b04042c412050481c0d0200b6401e84190f481d0b1000c03071f0391301d010791140c0d904864058460303e1400a1031176907204000d1842003400a6160248034811408480d03100039840b4250012005a40d051584c20180460344c000d000d01c402c040488080041903a000310071140d00c2d000900740251540010003049178408900d810448900660203152055901d0000c0c1f25401501c0c414141d50b850071 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 262843534 1250 262842284 262842289
    0xd0203131416050d030905120c010f09080309060306060c060108010b040c020105010e0f1312030605010f020c011d040e011a010201180f06200703090e06031603080c0c030609030903010b 81
    0x4002c04248400551040040200785022070030b00840300d10030b00300000d0450b5500006071082028680a44030382c1c001190304034407580c0c0200f0403000050103042150902e400c041403e0341e6801040101e502609000012400c40e9a90400341e441c2c00c0d8001d41100c500390b844403d610701820070f0983e0280224180206c1050090042c00b66a043e1401015007075116903c50a40d0701d0681c0c07004d050581c050b841307150404049101900c000300c00d2109924003050f002d150a00060003804021180011500005110052683e12454903d0001d040d0305507403200341200710001d80280420240c003101d035071070802112040a00d0003030206070310360240c00800000815200e0443c280050341001803030049601502d00002d00780307601080c1e03006070070180fa0081d4440d040f035040c00c99120070020f1740850702c00c0c42c007004480c0780e450b046944140207502500c1c0e14041100c4542c100c60316400014006400840c2c0589102000c000f0404124002412542c0c1d40c1001c00364261039601c980240c3d400f039400e04480035803a0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 262844784 1250 262843534 262843543
    0x10f0605130507030908070309081522030e060a08060f0303040501020703060f0605040603030c05122515020a0804110402090607122001150e06030a080f0d02031314 72
    0x3904050403442001c25580d40c0301005100081000091681e244544404603843d540038152091003521003445450034040081e1078080b5910300e41c40280001020040170700010005100410812100c0b042c090b04203250036100742048101040d044080801e540c01c045074030020b8580100b0b82551248119102d01090548034403941c0141405a400200204002883d0b81d2184080c0361140c0c01c0001c01a444200080545c0c2803640150001910406408144441800701a00f0003044000f45464918980400410580d513940403003030321640344004009110000721a02c045a0180b03031308641d2036600e00005058540e003690f042d100e01547c890008100d083c175200711141c0c074600804842c2800c0081c0d0320981d001d64100e04100c10807000ca400c003011700401c02c100c0404904000008500004407500546c4050030a620450014008506001d429100443c400c010290481001660381b1895101045248540340002001d503100008010303041e8468194551000c0c40703080700100003640300d0358040d0f91b03 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 262846034 1250 262844784 262844789
    0x519020a121508060c1c060e0103050c030a2a0b0d06080708030a0903140a020d0605091006050a0902031b0a03020a0306053001140f0702070609080d1d060c0c03010f06 73
    0x158060f90204d05d00d10003e10103020400e003541169006000b01200d104150f68113540a0070a000c40000140204030f01445140d2090038180c0042c0401d902c00d0301d9549440c2c01d0030342c0305484180e20900051420b50407100220144c6907501000e5501c10201c86180b004003454854240380340104000072650502c0070040b55403000f620783c1e4600c1c215046854501c0c0f032020503018071415204a46100c001a01c4812204d01018040d000c0003801d403074010050350a0504071242460810703e840c60600c00750703031001c005000392410300c0c200503103d65031344c1648041c0026101e5509021b00010440f051260352540007086140c1ca907640510681d0b560b2130902540c00b1543c00020b04045800e060303a801c0207640c000c4070051401250000c038400410319040e0704200000d0b2034480c02402c06004002903a070f010082280102144e207001c000441c40c02400d541c03100ba16420403420810f40082490b0301940389400f5907a401d5009181c42c0d0f45020f0342940d660b40303505000c1014000e501b0a2072201ea403020718402c0004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 262847284 1250 262846034 262846049
    0xc030c08030403051c050405090906180304030f06090201050405151309020903030a03092a1401090509181204080a150c020a0b09030721090506070f0201030519020a1215 74
    0x11100030780c0500700310406400a141742001024440022640d60788503290303000d0703020380002e0021420312805050420681801815640e4020841000050b000611945066400000c0001c900d4620700c01241d0501c210390105901100c1403071950001280381c8000e12601c0c06141c909100f444e5141c020005a018030059160300d074000b4044400d416000341c201d807a81a128401d0b44842c00c000002604441e002191800f8085e00410340901c01e550707d41c2c4e61011490000d0034a6400289000c002421111006200740c26651020304400d0f000740e81004005400c28440020030303115a294101c0a940750003103902901c0ca05039545078801511814410b400782c2c042d00b46d0103049002c401c1c0e10342c0120000d0243c0702400520003000b070400811100181031a41c060322036071541131108804030003030640040b900300600c074400c20002035001400e0182c802194a6082c200411540c1d5004c0c80c0083c0486201c680c9118940001851700080d944031004c65a9482c0d0010108144000d010ba01e1081072218051040e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 262848534 1250 262847284 262847293
    0x240402060307090b1c0f05040b1902120403030c020d0905030717070e01080f120406051602010302120a02090a0b03090d08100801090b0103020a2103120207050105040c030c0803040305 80
    0x140941809801594440164201a144103136203040802c556406650309400783c0030440744c3e11030549420b009440c03810390154001e1120b03041540359008e8490001d00801416905040c98400c01842c64044d81d0001c4074a00f0100c15600e89424054003030324000151724014080d600e00480602d01448800381641d1003d0010070420b03040185103030402000e0740b482c3e6264800c0000c00035005c0000000b490103440000064802030414400fa540380c00104140d01024050501c014442e00347e01000351041c40323a071f031070842443e01910b00042e002031080c140780c07040301b0328003004001005c940c40d0020482408250f5205144941d0340b0341c3c62205000507102022190021301d07500d110b05104e42c504035003001031b4400d455810340d51108140e0854003801d0b0201c90002d003041c0100154500282ca050043c1440b940c5903d9010440b003103d045903040355001820700000300c1c07603940141d0031981914201c0e035000008104a04050800c00c50803a91444200c8044400c2c0c58040303165103011096400312503005d0001e0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 262849784 1250 262848534 262848541
    0x305011d241206040503041508090c100c0213140912070b0a18030306030308060901030f03030e03130b04080c030d050a0e240d05070f0e040b0402040b0c0f24 69
    0x484010380c03101a40b070748100b503814422a540028005039008a1042c401107507601d00d018078480404a100320110184019036040048160020038103030034600c8102c441c2100118030038015901103403118406900007003482d890b42211045c41d806240c0f18a60542800065918160704a80e0740640103076240060780140f00c10400500c5060040740c101401d40c1300414610000c4022106140201c1c5090700042e80f900030800c240f641092580b0f40000342070301c400324550b055440b50224140098001010165181030740c3ca0526000e00030390382842070030004146490b60380c10071003076030750400c9c041c0030014080d044032001c06180001d00f44c6c859032080d03141e80c0e0829400345025911000185040744c0c11031400542d1701c84210201d03079410300403144145003980780c2030702c003280c541102c000900700000d0004a8a645490640191f480044000119408a000d8070001c002c00c000e409a5804118408400304d541810040301040a09074100114102d035030190001e20544040300300e900300364000f00205400f1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 262851034 1250 262849784 262849831
    0x2100513111f0c020a050402071208070e0d1b0503060c0409060504020703080103020d0807060c0804120215010b0a0c12210b0d03110327030708120306060901020a0609030305011d 78
    0x80c0100c075000401da40310740da90f646c0108090340d11401e01103d5620860f20007040745900408180d41103203e5207000c0f084140810041801492400307030250440034010401110b406200b0001d002800700603007911090f0070007000011702078000740904c1386140e00b030940c04255414103109030b610f0550590f07101151a4a0f580030b0042d003a01e0404180d030400020407404011510500411581d0b00c0307144d0364441d4510305410050804511031600c0b90440d000040848203200140c0c0d400b9041d540b002d0b40c501da403080b03410415108203064410040c0329065480a81030a42e800c01d001c55210782c041d0301202268421100200d080301c1c0c01c0c0ca10603500c01c42107020036004c00c0c8144858040070085004803440c200325124036001055401000010611030522054854181800703c0340082c5040c034020300000003130040030441d034040200418062a4040b45c58085a8401c20401070340d15007180c2d0801c100035190400802401090207000a5809030301500c0c0c076400c0300c4007800c522034410034405207103d8012504 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 262852284 1250 262851034 262851047
    0x901030201140f0301032904030c03030203130c081b060703050a050d0b061801021902010206150f060a030e0d05040608060f0f1201050a1d06010b0a02100513111f 71
    0x1907082c0203a106000403c0c980000800450195000d6150310301405a400d212061819a0309017440042d1008000d2000003070b08035107005049580341c14090b80f00d580d41c9078000c4681c4c0300d0352005011015034580c00521aa4040384a40e01d18000002104000119005110251203070344030080c0003410400102040e0740c4600c010300f100c52351112022511074810b60008125410454510303007034049603c480c070400d680401000c00e240d441810700e0211280070741c0010b92100401001c0184080082e40d80004955070707190401e0148a0040c15035446100310b010007002131040001034030141c81140706c81c0c009a4043d8080d14100d54041ea100d00d015581c50040c414071020000945402c0300e0020428091659400c4d011209243c1c2000002054030348400c89200740d072501915040c3c000000d044c01408200302007056410f44084131085070f500c9034408000c034a0050145c40340358400c0d1810b030500000b51504819548031501641c0703451443c6510004001070041d41c918000310452850ba040c40c0107030301401 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 262853534 1250 262852284 262852307
    0x906060d02130c050412060e10060f09020c010e0a0506010303081e01031202010b060d090303140606030412020c041a010807083105070f051215040b090c18010602011a0901030201 78
    0xc2d20b02d040960311b542d2080c030070316a92011038a00380c80714000d603003005040020504902850009000032464030012142c1c2071018003034080c481c0d80000306841c1c03140d004d400500461150070203c404040b03844c18078984940007030004030f00040d80c6002154210200c2419542c41407401a41c18405034a16903400e205442d00311483c2c4195500c500d14030041d41d50304406090340c11001140403c245007a460014122070001c240142000d8100062203115110b143c15664450780c0201d0b403180c2502d9403d0260311f0101d01e1504942d006085c04040140802e40a012040c558403c0e220301040e510340000540d00c4480848001c030b48001001504071364011460080704201135500c15250340c0d950161191401d000702c80c1c0146400c0001501c04120900b0070200d41c860308aa504094568030b11814083e13000c100c0c02a001400d0b024401e00803800303d05003800390109440000b419010100b00c10802c00d44140800d102d001c000d54640041070082c1c00c0d09182401d0982d5005051002c0c0b81e0946d401902d1071500d00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 262854784 1250 262853534 262853537
    0x4082104031407050c03061602010623100c0b1617070c030f05090307150f1107091a03010f0c021b090f1b0c07090b100c0b0402060903070e0906060d02130c 68
    0x14000106d4600b40b01250191900310720a0940010340403000e401c2d107015034420f0f001080f4294411040d5880c50b0701280d00041c040740d40502545248104413826103d506000c1c03c10b082e11018404a500001c0701c480138500f0036200c0c1440403668080c4000e01c1c9170b04031082c6020070a0042d080000902c00e52210200c0c03461800c0460070440c0c034002003071030f02103580c02840c41c81e05c40154000d151a000039050a5042041c80c014004015101403d51281d20b01d2245c20b801039110040040302c0104034100c8103c240307028000300481544150410094044908680e0160184044071000101103004022050401820b4950f40d510743d6070018059400042c1038a9082100c40704000d5141011001850700740303070700d1004000080c2440541d400b1504001032944c494401c0d22035400c1c0994005101042594200c49190496625030001c04e04a00c01d00045550502400e1008240c041c0610380c500e0282000030200c07142e507680c020a0000d404081c1d00083c1d440010480105081d07450350f00b0003066000355 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 262856034 1250 262854784 262854793
    0xb09190e070902070309080c030c0d03030c020118030c020f150f18040507090f0f060806010507030201060305100c12023f0c0a02010c0305061302090f06030408210403140705 76
    0x58144040c12071304810404c400048200720100002c0d80108102031012000300c01070300800386a8070020765840017100c002000d00d1344555184605600070351102c048410421403a9000a54515004083c0340710218128428240340030811410304000d0030744070311043d00341501440c6c2607448100206907009000310100c1c80300c07000304100300e41d2107134002c82e0b000d0416038480c00c0074907040c0101c1061000b030507041000c1d1481d00c0c410401c03450343e00022498200c402800c14668800b21030034120301620302500064010700c44c105224100302001da10600208602d0340e12400f101c12070341e1a140503803081d840d0003005410441101c0034180c1c522108001c2903494480c03444040c1c00e588801120594049803006a802c40c0401c10000c41602030260200403055883c0c1002a468000001803120701e0528507900055404154548941c0391300b140e110000130300800054803440c0c60304d4607501ca5481401500050030140310344440c07400b4400b10450150740e02d40c81d42c05540000710844c1d0f82640007040d007910184038 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 262857284 1250 262856034 262856039
    0x1e11160b041e1806060906020303060d0308090a0209010605090a0f080709230c0301030204140603150604020c0102041502010e120d050c0904020703081008070303140304080c0601090f0b09190e07 85
    0x590840c80c50780043c80220101d011440c02c0405801c0710343c140d20070f0003950020000c10409030b6030040d914400c60b9142c1046440c1d13072145408580783c40c0a60304029001480b1000205035290041d001d800305c24412191450f016403950a040300c0300940e4030480c000f55101e507a06001640da9034101d841c04a0540460500c02c4580b20454844040c0507194294141d800000502c198100790003115046c60720500c11071100c0c2824000710381e4804d0191409007c050030040481e49030b580303d404451600c841c0c14029502c4a44589103451200c8501484202541c605054900c4086010400d6010848101d100d1402c000d02e241c0408040d110041c10071140e440100130103202d9540741e00c0900007190081d51861498600600658a0201c2ca900302404640c0709120800010341d005601c40100340c00d49e4040c0b5182d031580e160501c07441c025610340c402036005a00010544039181d030300ca11b83c5001d264401303100100d0b1000502440903030990351030070310b0303c4150800c0048071300d140c01441c0040d40500441e0a92075 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 262858534 1250 262857284 262857299
    0x6060408030d2412020a1a0d0903021e250317030903040504060905040c08010b03030904110d1803080f010b04060f0207080d0314090102041409071e11160b041e 70
    0x14a030300040c2000d021302000328207504001e030b840000380c01c904483c10b804c010703403c03100c08007800340c0a10311960f103466414140401d0f02c28041200b44000360a814030f0f070300001d00c24a54962002a042c18170104003280022800c04031405d03090103c1c1d42021018580c14440300100301c0b03c2e40002c0c40c4100511081000054648842c81035400400e604140003595040c18030f03103400700002c258400d00d51a81004032001d020fa402004482d01d50108580000c0d140d201c0d51100440e501410031012207d0340b611131071a60201e1011110f05001e84a0340e0b0303031032651352001600b0070086800e0260410741c4400b4171050103a90700800040900891a004030b800503a030f210190351514407003008040c0001d44990850180d02c061728910f94000c502e00380254203141c20081c07500e0f1942805070303100d0310034400c00c80441d41543c010074021042103040507400b058400420005002d418605011380482e110b4201444d40520542e00030105075011071030b60f503140502e84020b000603007005054010201002030030016408 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 262859784 1250 262858534 262858601
    0x308190225060c240515010f050405240c010905100213050f060d050907050126130804171f180305031906140102060c18220c1706060408030d 62
    0x41d207040d0804141e1b032805000340d241c3c0e680d89074041c03810f0000100302040ca494000040d541500c90039a040c1b13080408920500c20140e10901e2406800c00c80050120700301407043d0410030029000d0b2044540040c05506d80100724855406072004403c01040140034030b10f0a0b1403200c28590303000300b90900700802e4400260031160142ea1036412588441070420155822124802040e040c03400801031500b45804800941c40005206080c103081d142003c0007001121415034000c2c149481d0000c68602d49000c085035a00506c4850003075251081c00d1809041321903000e2090074460014050000c40b9241da410340740380d00050006041d0458180841c1d500128501c10f6034001c000250010744110451380000e8240703000904030410b2201c0401009044c0ea1500350030004000b01903070503810711008800000c88010400c1c050711400d5003000031640c40366501c845070811458244003135500a40301d517802c004a5209510403829141c03c14040104880301c141e010320a0f401319078180391240340245400c141c08 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 262861034 1250 262859784 262859843
    0x15090d06020715060503101401120f05030703020d0816020c0409020a08011503020a0e091905030d0f15150c151424030a02011b05070308190225060c 65
    0x50750b9201c1089a89410064100007c0d1403150402a9241d50f01760a04c860303005000c2e00b8120140120720304200480d0212202c110364005050fa9111081890004d494840345800c00300000e41020104140803c60a141d40381d52005400034801d41303c00c5400d110140050320406d030b0340484d03005000540b10b1428002d40f80322140f42c0001c041d4007401d40c4100a05841036400c038a40b07001c40751003000540100000c1050001c441082030500340c210500d420341c61449901c4480340c10034103103c03d004014066400c00c455003420002250982034541c191203540f0078a0810303040016684138442e0001c102c03e06204a929105140040380c010100f010800b1605401d0741c0800c4c0b00340111065a81502004110490b601c60131009404001001d030002000030300c400320461003a550f0010748108004003002042c0083d41d0200445481d43c2d08032040d01100c461070001e60300540120740381d8205032044024406090744100b0174400c0605c1c00d20504450310600010300702c0e0741062030362401c0200c581c0404c0c40d149 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 262862284 1250 262861034 262861073
    0xb03060108042409061503020a030b041704060309150507050306042003010602030307110703121218060b10022b1103030f010303140c100e24040b010515090d060207 72
    0x104040e0390301c0c04408946a1008401b2181c1d1121400d10060f920b82c0070390002c0340c0d00100148260f0710f075400c1c0704841c200c944031800d000e21000980002c4c0e1582503000b0500103070155498400e10b407900c1c3c1c2a6001d40b80b08544000000320700700b0004442c1d142503401100710860105074245034207621300220070309510a8100b1000b6178008410014440e6100f20821220108500980482451640c1e120255000c40c1800403d0002090300106c82400b254400707003601009000302e58507090541448402498047c01c6540501d2a5140c400120341c00041d000100d800000d4900d060301525800348072413001000c65000800460742c1400d68002c00400c05503008000031501207116502d10726000d4400c807040002c200e010481403208035004100401c0d00c00e07405100d0000803420000300d560503030421800c0618030424011040c103280890850200d100d00c120301c00c942c2c005d2244d80b80c40410000062062500e10175000403c2083c1441c2420410241568407400c0054109074640d0365400c01a0800840b408 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 262863534 1250 262862284 262862291
    0x60909050105041407030b06040908120f040b0903040b0f0f1303080d0b01031802012007091b02060610030b031203091b06090f010305040f02062a070b030601080424 72
    0x814010f04e072458601ca4013a100060440038a0760740c80352142034008140c107100310342da01d02c480b0511800c10100ca48000b0004885a464900704144954404041d1015588900d00d6000610700743d00000840302907500c04000c031070404040540104680c4e00440389940700c81000d100408200b140740d50814051171180310070039114a03183c404001191000c0d43c445041500341500040103640070001070764400c0e02840e0294442c212810440d00104011840215910031034400240c0e0503d20392009401e04205107284554185201e012079646106583c1c2c1ca038421244421050218081d501401c00c9400240c00d96036000005008526160001c03600d5007219008a0700d1140c81c140c1c1d03203041d45102003044039120b00b07040c5400b0100e124980b04030315260602d50743d00701040501c00607602c0c0c0500c0907402098a6030354800c02c00c40e026592218007a6032080000c2d070b0058640600082030060aa5001350702d918203584d03902004460b200b0340a802960a4861300c034490078400c203c00801c60460b81601d0011 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 262864784 1250 262863534 262863541
    0x51e030a171e03040f0303050402041401060507022701121403180103050601020607120903030f0504080a080106020601050315070e03070303080105030705091603110c01050108150c120601030c03060909050105 91
    0x840c5a42c0310400c445000c0000304104400164420340754980d81e0b07018900000c00303980f944042001840a00b800084d200c22180002545980c440001c0007882c0c802d89840046001170346688400740114000820a0851000140204050103c0c8142000d0043c40704982e42c0c00141086410340e405000c0e4111400d02c003000307440031560580030300c90b0098070a1004145d80d190101e40144001803075010b0000e0141c440c0c440d102410f04c030b034011074000e2481e454204070b507042502e4240500e6002d10000c10100b2007a40001400a0010507414100d07400640548036141c80d0303c491100f440c20040c5240b05102d0515070306031181c5c80030002c95016600c25210005039504100c00c052404110390b110358443e88000c0d0412146103400141d22410410608000c03030000ca04001c0d030a0f00340142403800d4001d601c1e2200003c1c2049000070549503800700d019140b8041e4132203e1140c1c000b4441c0700d5181c0380300000074000c41c625500c29071088611403420701c3c00084080e100c1c000c480c1600c817000d80580d081d0b034480c400d0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 262866034 1250 262864784 262864807
    0x70c060519020c0d110a05040501120209061008160c0b040b100b0702031c05090d05060703050601080403050313030210061d090f0d0c26030a110301051e030a17 70
    0x80c1040079900c1d000030214032040e50002500c29151100041050707011990740f8900761034454900002d007000510034001c1c0d40e165044900182d920040981c483c0607260701140c59800d1034085680d80001079628945d01d075940400c0340c0400b254902642c01000b8a02403c1d1001c254102c2010303003d980b0540c0350300090b04140741040919030450b0003040c0c140c80700708400d40040e40c0000303d03410040a012800e40000501300010388a84c020003a070150080759081c110010010085001407140100c0c0d00c04200e00d407142c80044070061001c950003804074a0800114540303030031800000710643d1003803044818111205078414281c44403680800d00e0030400d80c0d0b9034408104014841c503484540c01c002004001d80c10350460f40c2d40c401c1c6440ca00180130a1003240401c0c820f100e5543d0308942a11031840c1303000b03414100001d03010f602c04c44000310103a18101b5040744141c42c100440c0c0c100c54004044480e0482d001d0f000650b5106032040d01589441800854000115185502c69072000010001600c80c0860b101 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 262867284 1250 262866034 262866067
    0x90102010b0f0a06120204091d01060603090305090d050a1407080c0f0907120b041d0d1e0f02011407030c090f0312030e0109050f0105010f0909080904020f070c0605 72
    0x3280e500c19500031220103115281d0807120301c2202c1340c918140c4900c0822800d007000078410f6402c03280405007000015001d80403003640d40c60b0b03a609004002c218850780c0d2001101101d141000040c002203041101440c18070781a481c08002030f002e80d06855641c0c603282d5884d40402d014144103141c1303400c9200c080000b00070501198000c601c0c1569810f04008040c000118510001050102400a2414010f41c280150307480f8202600f4042c004010484545201d0840058000d15400380392040703072a074040707481c41541000202180103880e0710900c404844190780a16030100d0b00800c643d80c80e503003078000c00c0070124028024a641c2d00c1c0010080d150b204020103c000c181c11840443e10202010400146542d0010342c103d0410714002601094504480b400b41000c1711010f801c0e4880d9110f4003c0780319041d40300d81d040f60302c200540780d82e40d80d4400080e81980c0c100c04016184035400d100700e64207400c0c03e4000340301104c000d2080310314080c020351710201a05050f4001c01c0000d1804111700c0315001800c034 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 262868534 1250 262867284 262867301
    0x60f03020f3c070b06102106170c032e020304080d0c080f0f180d0e01081807180b0607080315010309021012150602030d150501020d050304111509010201 67
    0x248841d14107032840e1114013080f20b004c0c03d218041c1701d42c004403007a40c41c450078040d20082d1000c444004a90f540c21081c1020f840c885c0074200f0055040d46070507405400004101c0051000a005008800c846540c611403440600b00c551040d0643d0701045211079166100a611a5104800032503c40030100207130411220030380617610500100b00188050075003045041940304024440d06951660758100103602d0088180207006d103442500130800b04550003611740e40008101f07030380d000308542d9000d0700c0308500b051160030b01e030f07003034000d04001d01048542c01c250f004d10303550100d4045580400f0b840412516845120301b074460000c08028420005100d1151611260007460248020000c9400051504428825400070300000c503084841c41011078100740003210181e0010100310b0395521000c0e44a9004a44041c485450007030700500040f040303100321084c3e0700b044c3e0040881021840003501d0716800503200f5203030903202c1d4603120120355400a2401c01070940e13548c82516420240c0019096a4040 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 262869784 1250 262868534 262868647
    0x1201020d0507080f0c0c0304031401051819110a05030a0317060406210f02060408071a03040506070f030209030109030c1406070e040c0c0b0c09130204060f03020f 71
    0x201c00740076101d244100c204d900710401c6800507607903038014200c903450352141d60300c0208612400861038000703000c1903000314407550f00d0806072103a4401a0000b5a1108074240311140e80142121a00c008201c503103515142c1090003919892402e80c0b140002454544808012400175000c41c00492101c500510001d42002d000e48043c8220380c10580800307a40003c00d28080c41040b448605601482000038403201da40e500900707001d6480362074140b0951034003ea07015800290305142505480d1605101c01c80f0b00c501d03045070203040300e6102d00e041110741102e5200c96004041d0280520031071540c00b880341b007100503c243c5038041d525900c0e242c450a41410b0741c664081c0c6130030900400c080340d60030481e031091400c0704990000341440032580030754100c540c5c602c020700409000020003003042031050003085044030440346003101a240c00c2420042e4810703070041d0700005089600f14034145010750080c14190400c0001d05041c0030880c0680031450720700c0203800a0b18400030000505240b80c0149040302d90211 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 262871034 1250 262869784 262869797
    0x507021c0f14161406090904110f031204061419031506020316060b060d111b071406030406020417060103020f0612010509130b010803090f092806051201020d0507 71
    0x1101d80080d104030381c1c3c1c462040b0300c1944ca00614503e98a03201110701043c1b0040034060306007018103000903255103030245903018070100c3d8482526880e00050760308401c00300903c02c0785402d040c1001100c4001280c030305803514020030300519040480701d41040d0140d490654000400150004030758091305500d80c0210195041001000054040004400b1101780c100001061080e2404040b0b02140b10707100845010b14588046001c05400c0500100742d0b10804040c10b2240c40b13629030741c20340c90790b940d442a021000752004070401c10303041c0784020719489800b86400505180d07031400510b01820581c00c40440c20782041c0300510440c50414040c1010381c00640341c40342080d020314105112101c060103200d202c0c1058000003140380405042c01150a03612420541c500d50752442d88070341d00e40200c0a000e01c507003210440c400c8141480e02e01e1f00d00c603600c2d800f00300020305045071100111141e0450300c6181d0340c2c2c5440300883d00b5154101441c1550141d180010fa44605807600300c02210703000f400b14400c0160 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 262872284 1250 262871034 262871053
    0x9090606030906070e190608090c0604050a030b070519112e020c030f0f040e01080610030f0c240207090507020303071206030f0b0103050115080d0507021c0f14 70
    0x1000030310b140c2c413014508180c0304000d6420001000350900341c021844032021440c001c2015a8859481400740e080402104e51103400c02041003480e00482c01415004043c0d1002080410009000907400c55401d0134001d1030188601c5511401540301010b0300085510100701000c504030804c080c06550341c28031000314241c0039040c000310031603062000200205401007602400014188112482c540903002803640d91b02c1800500e60b07058205110b50400240081c0002031002c001246040c45a046001428442821581c07280680512010142c9503180b03001008995420030410700e8003110211840070711440c0030707650300a20b428499040290014107040c20300c25015000800d4a03044041c60901c00300100c145d45820b001003005e6400504855902c4a244081c480501c0546060702e008074020300010682201005000440d4443e80449a12080a40e000540b044000d4000c2d030b88010290440000c0c900d4414103224601c4405440c0540c804074510100025181900340c1c510408001e0448620b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 262873534 1250 262872284 262872301
    0x90403020c12070f03050f1204140105030c0c0109210c020d0327141206190b0f06030c0a1704170a050c0a2406050d060f0905120909060603 61
    0x51010800c82d00900820b45011100502400807002400c100340c0400802e80c0d590404a68031065104000b0035802400b0000c00d0100c4e02c2800c4605440300114880403504900d401111103510040668181d10b4080c0040e29a100c02806580d003004e0003034802c1e504180d40c03004144c0e40f10800124400c1403224a01c0000c0041e120160000ca4003600b504141071048010805c028015401400313402d4111010840800c2032070341f40904440241c0c050301d0701840c81d801c0c00c041c0e566845050714508101c14150200420141003504a0000c62a002d0b281804824000010840303541007550290b40d4000301007080801c0560041015900311640d01103040c8034106500c45e020034281003013101d003080d0340000d056403201d03006404650740552001e04840d42c0a04604001a440310513803404420400710710507000312080180110016124018180c04129413940c1d100700061a0240b10499403a07110b1714264003055040c003859402411a104850361580600308000c41c400740240101d200300000d00c180722090 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 262874784 1250 262873534 262873543
    0x80f0a090c090e0316140706050a020613020f0a0902030103113a0c0602030307080a060b0f0702030705041401170109030507062307030608100e0309011202160605011409040302 77
    0x54041d04030000e0500441c603000d130305500c181d028042100e1041398021080044450720000070607180c0043e540a184c41d29801c031014403940b20a00016031264020480f035404203544000381500c001c1c0146100d10100d004030b145454158803070407200c0d034080010020b0001c9102010000f0f0400c503642c1762185403034101c0401e00300f0080903082d5245610309282030420089050010340580145c0c0011007140e0b56400256a41d20491754640064407800200d035070180240150700c151080e01d14218140382c00c0c40203d04e807940240348140d0f070521801c0c40010300ca07103682c0703c0e940320444480d0601040c0d60600350445011510344029600b1685001a04400719620000751900c280d0f001d840458041c0f008000d0b0441e42043c1c0c0f0b03107050028004003c0c00300454156001d50221546201990b0b20b2000c1481c403102280c2c4281142c0b01a134008010341541c56105d40902d40407904548801030801812051111103051408000c89116544c0c100602510100d03844040300700740105c426207803c2c905558000e403503 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 262876034 1250 262874784 262874789
    0x40912050310050402030c030a140402150702031509010608070b0307021b060d050702010b1806030d08090325150b180703091a060f1801060509010c020301020a080f0a090c 75
    0x2005004404500e46074610b00410b00180001001075480341488031036207006a03c10b80d241004030389070081510340c0701da052202e0342c4101e800030550560202c580c1c07a881c0701c590020307100301c0c2c0c1406904108101e0402c40403000d4003e4800c500006100742c24034030102d15155850300030440c200400d0041140742075000440d9407240b10034205900008107101d01141c0c26004a0414000c0c41e400c4c50708000c00c05505501041d003100c400c43d594005549500c0c030540001900341d9003507030103030000040c1160807405800c660340c00102490441e464403000c00003d00c002c00c1034400800c111085c80301c03508248104c10044400e104d0f14210204410340503030000031015004001d4441201c095100001c40181c000d1b40040361840c1c001c910314001601c0c00b040d120308110111007103403144c8a81c2c0602ca186040c4000980d0300f041003031003801481d90038060b00b60b940e5001004840d04001c201030f200c0c80161402c3c001b500e20303074140383c80700341580c10070400762850260010300007040070b45008880400b00b100110030300704 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 262877284 1250 262876034 262876037
    0xc03031305130e01020a02010903180e0609130506010b0d060b16020f010221030a05100501082a0403050a0b070e010203040302040f02070615170a032a0501060b090a05040912 76
    0x20b040054079004040c0074041c088500c41d51000c5050102260103420070840c961003544d400058080b41c0e44d0460614510b401035070a0840340a0000300340d401c202690720f40040e61501180303212038503661647e24090702604069162400858100014130bc0c500508001c1c005500c41642802c0c4620940030714000c2a08019205030108007202040f41d00030700c40c04a050b11601440d41c0b0485009082420650040c1c07aa0790304145483c00045d0700d0543e1145078004e9403030503980c00381183c4620325502d401800d409015030b0020a070b5080c40e02203164100040c0002c51240c409000c0c3c455072820040d0107154010640014130005401e0307000b042e80d000c01144c096aa0482e00064036a2042108070001d02074900700801d03030b1303182c11390400c05070544101c0c0000b1180240c0000c8001024081007075200c1c6000007008001c42d02c0100d01e00c140202100701c03800d550b8614409882e107920715441e01425a050383d803049505085c0040c590782241400004600503040994061200900907910000050b000842c0c0b0350 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 262878534 1250 262877284 262877299
    0x71b030b040f03020c0f1e040e010213140603010305120705010e03040e070206060d020901060f02120313261801051614010c0504080a11010912050102030a2d020309010f1802030c03031305 82
    0x1180b80d45d2300d0744203007170040500008549132101c506807070002c4030301401136407844506103204a040e0328014040340e0680398014040d00890171504c4e83e01d070321134021072012211552980c1c08480542e9081010300010111030390411110304103141c020781008005130010f8010364030b0900c4c2d00003603105d400312503045a149290481803407245820807801c02401d01d49410300710030004240028030003124034048801e4001c1c400e500c824601740810124103000f034460300c0c54010041c018a1260b104003406d688407903806060481c603024400400003440c1041d82d804071000c0c0d251908a4180e03400034130501d03040d90491f082081c81c09007805462640c0c1c0350a148001c00c0d810707400203440c0e601c3c1d01c20440d07a0000e103041e0385541e030301c1d80051405038040d40085450040c464604902614040c0c0c242c4410003004400b010f6000081c480d44482da0003950000340900802d6403900740b2071001d40414407604214500d140075080c04204180304041c105012124500c0c0f09500611030b000704992040d0040040380c004030b4484 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 262879784 1250 262878534 262878589
    0x1060f1107030b06090108060f04021c081204120302090102331e0c0703120c0905130b0a2715030f080a081b071b030b040f03020c0f 58
    0x4858100340340c00034811a00078501d000040010145900740030361340c00c6415109680c0c0707601c80e46994820844006440c205000085405800c003d0281401d044600302421351441e05070701c5041440c0d02141280c01103903009800c000070300550344c0d06130814540030310381503203400700c0080000d5030f42082d8400c0750343c6043c05c28412481d240002c200d09030407900905c0301030b1003440c003006543e641810460500700c3c0c00c00380c000010300c0c07014404103d8104661545800b0785007448038040c3d400502c82d1000340404e1043c0640049000d950302d04040151209019020801180c00d0b400d000c0388ad041540914460f10020103240c1d5549155140380c105040d0030741c0c0000720984006200c20211003a64005801c1c414007031004000c1c010f4460050444210726210031100d070701c80c400046003103544200c00f15a101e001380005400140552400ca025980c0d000c0c400d40410784a440316070a1150030f0780c00719450f484d81d002034800c043c0c061080c08480e00e000ca0b441d403e00110318001c6007903c00b0040030952032080d0020360 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 262881034 1250 262879784 262879787
    0x1621050c1207120b010f0f0503090f0f010e10110f070c032003061305030d020f0c030a03020a0801060302160212010915050601110a170304141501050a050f0901060f 72
    0x1501c0c05038001c080400041e040100014003c4202c41038a08540c07428009104125409403407010500e1541740e072a81e154405540d0126030315003026045031018042c0880c4d00d000e12004002d07001c49003541c50000502c101820001624101d114050058518100b6a4440032404d154003903941c41c60424480c41d594113170398039001d407401115820040918400100c6c181c1080008884403c0303005003941103c24070348a458006c2000640d40f10b005041c0ea00420141e103420300a42c019040080c0520364150820408100340340c1140c101140c1000000e40c0402c01c403040990000b0001e00524072803c04600e0300000b00e0440060b405522006030241c080c401a0201003c0309511000c2101e4210092205081500008801900d000e4900c640007c210b0320701940809000300303664072003503842640d0116001c001c800701801500000c2c0305407869140369140c070f00024000d020b1101011148040681d036507040004200c0000e05503040940517030f40300c025074081c0b61540c02c98241502c2032800d12460401e1103490 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 262882284 1250 262881034 262881037
    0x111806090403140c030301060804020406270b010903050304090203070828020906040b13050102071d01032006040303020106050a0f050105070318050a03030903050f211c050705031621050c 82
    0xa14004c03444000b000161259111310396500a501c211014411a561000b4603090714000003c0c003060760f001d0340b40b60188580745521040f003141042c1403d081c096925150142150003a500080140d0307000010070201940c000542948404c000c005025016800c00b06500c0c0b0112100141240903400240300d5031075503580041d10300501c3c0d0b1613121517a0b1001800f80160040140c85021301510440c2c401090041e01d82804600d080c4800141d400d25a20790b444055000c441802100300001c0c008100f140f1a450300340003480070350b01039000070078264038000c2803082040035540f21040382d1011500900181e82c0c4001202c03995509071502c50f46140c00040c00894020495000ba5480600024004101078204185d40704581c019425540296400d6400b1030b200c407004c0750f8030303003d107450940b80b0505a8000d402a1609070411b8144140ea503c0d244598003c582d03044e50100d0101c2c41c04020401c05505c46401308026081a180c089040303200d44c00402074910990705901d00460300d034000907560388007850 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 262883534 1250 262882284 262882297
    0x304030f03180b0c0106060203040b0f07150513050c06040303210605040f09110d0b01120807050304060306030b09010606020706030b031207060204030b010f0e28060311180609040314 80
    0x140418842c0c2d5464400070346a01461054204d5424154002283d43c004810b032411110010885450194a484000c49591000360308071178500709042d091174140010f00c030700c03032080f03500d4558805100c00c2403c2051902c90899041d610841f400c00c011710010303034415040075003003840380000b400050400d907c84c4040c00302508240d4000d440c0450300400c91566821024015002d228405100d5140d541808000e140344000a0500c02c0c4c00d10040000c5905111a40110ba000c2c40e0b005080005550b94a13081d40d101c1e07070041c0000394444d0414801d1040903181a60010410002081001e20300180a51501e0381da100700818955546898800d43d10240003021001e0347c146401d5a40340c1032031414000a4200d800192041341c44100081030f407502d180c0c080410380301080c0c1e03840c0d0a0f0740c0c0c1c20b18a6040072a10500e03603207250300025140404107403034080d0901840c440c1019801c0f2005110910045000400b074000c1c80290980500c10151a03011210743c1081d01f5291200c01e1603404c82540210f489640d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 262884784 1250 262883534 262883567
    0x3b010302090d02102307020a0b1e0f070303060909020102060a1107081909080f07050409020a030501090303140c0a140708121005040609060602031c0b0d0302060f09010504050304030f03 81
    0x40411a00c6158844105c03801c1e2144483d0008403504d40701028481030198201c000d410850002e018494100b40e00060300d080000d60000e041400e03c8200103110a81010310359280c4601302040c00401c03d601802410080c143d0003100b000382c5401500000d58401c0c01601106140b5030701c283c0c0311000803944040b5501c03d80c1040e51700da80c8444002c20859440f132003034054000503002910105500801289070368008144a005100e91800c02c420030006080403002203070b00401c1002c00200041d400e00408480500940300042d036840840382540c001400208a80350320303401086400011a041f450310b00c3c0c95110340c140030307403070301000e241c9148184100d403541c0204503214030030050346c0704440006006641d000d0310144a06503075940b51806032240c03801401d000d60014059404c014664000075010905590004035152888402150442c1801e480c1500142c12040803c8083c0d0520282250003801e0f4070001c1015141039101c40d03460340584d0100514100e407004262091600c618400c15119092 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 262886034 1250 262884784 262884799
    0x17190509013306020c01050703120213120605060402030903040608060d061410060311040b0a02070f0f0302010e09040203121c050f040615051014193b010302090d02 72
    0xa80821904010041c118202d060400c0c80401d03a18404600d0300240e0806848480c20441d0994007a2540390030041c0302c1c410340358203105c00c01041c0b403507020440042c061003407003204220031303800e0403000d444005160a0160b8010801d00810031000004c41d003c07101036150011094650f88002034050310310750300240ca203905110300f402e454210540b10341d001c5c2000011a64180755140010780c1580d13007441c030564ad111814401000030700301c0b0300000c0c80c04450501c1a60112515000f03603100d03d02494110301c09985881e00c00b4800c550f00f24009411010084640c0b074000d180c20390000303075600c124041c80f100084000c01c031444000c0044589000c0b41c550340034140000e16202034001c5501200303c0e815140701c1c1c10300e283c02120064880f070840542d900a00401000300000005403402408040a403503804c1c0300f045500c040c45001c10390070307510000b41c1d0780d190768003016105d10030304503803054002c012010501c1d41050000d80071044042c5100380282005030f1980140000528441007500020703411101 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 262887284 1250 262886034 262886081
    0x2d0304050105060307150203180d0501050a05070e0102031305040c1107030f120c0201020c01050f0c01052401090f03170d020d05271f020c0a121719050901 68
    0x306400c03951040c1400c0d011101c246940c0c03070040050140604200003d0b802c10000c0c45001a01c41da5408880100681980c0c0c10036581d58601e801c4038403c80d0b000944507a40d00600c06800c1c4e1010f1030906580092004604040031140000a0401c080c481d0501c1984e0351660100107500840b5044050911001511f01841d680d041c1040a60300e0341d14101d45448030074501100c2d40d4003c0c0d9100034116010780c0100041a500d0006440300c0c3d01c0010104482c40041c481c03411a031109010340c0b88035141d84820b11495070000094480082400c00c0c55030306024411009200e96140304040c0401c49400220580700c241210342d40c01e43e17034841e00d40700b11110703030000603010303540704c220740045005402d041020100040322005400501c0103060002c02a5004006250300c004407074201e506031001491070040c41c0010600c0560300c0d01451440880351042841000c400e80b076000044003880090702e141c8030f842494503100c0b8010035071501c0300030940c9550b20b0000c54003210096001201c0110044840c0744a1076 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 262888534 1250 262887284 262887293
    0xc0303020a05070e0903090906012f06060303030103051b06040306111206060a05120907080618071a07020d050f061e0a091a2a0309010e122d0304 64
    0x582560007034910384150f290008a9611201c00244101c02400c06075007012842400c002c40301501408450402150100715000f2080c4c40c860580d05040032040059000720b241c1c0f81a0034068010900c80c403d820038001000810004a0f08543c104104541d4800250040e130004946015039000a00b080d483c2050741510b00e10100000c1282d510407010082c500c0e590304040119a00c10b00d070300e800c000b60003408000e00480b08401c4041d0010f08403000e840314a9114908989005000c40d198440d07980300038510241e4038401d0080300301502a01e4440320741403500e814910801d204400c0b000340145da0310802442800703000d12460032120000400d80b81503080900307440514041d441c0320b103215400d094000c1680c4150300c6c0b2600101540c850314030f141842c4c00d194070a100c9a80100264810041d0b000c501c00c02d20382d50007020001d1504812401d032681000031403e4215090200765210070f500070903101c08071019403400c0c0c0d240024003204000420441102100d240150800f00c03109051005c802d120400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 262889784 1250 262888534 262888543
    0x714180c041d0601080a1a10050705101b030510030b071e0207091109030a06050c0706090b0a06050904031e0504050301060f030311060f01050922030c020102070b0f250c030302 77
    0x3d080076a40e4645603101d644031042258400c648008121a40003407039000d50620759010b00801c0703500c0c1081030419626444032403c25a074411710500b07690740c84a41c00c0c110600b00c00e00f40741c0d070101880e04100d40c2c035007260404210300c4503010252182603440f0000301450f01c54044480368280d0020015042141305001941d20560740c02018450f07410004003e4001c6008020354030780c0031004008201c82c40050325120003c04c1d000e00302c001285400c001c100045001c90288040151041b4000d0f01c1c1c03890310200040c1142c8442d00210b116040c0d10040c800840e50141c1c42000e811010160007000d4080d000050754a84034562100f90103500305040014481c544c0a884800c40e07000342c0310303000245002142c0a451302d004a699454607a441401417045052108001d41c0c03000302038007111641d00040100a1350a110340b0003c0f070001e00200031070310440d681400600000e0051004140c02c00c145c1c0e241d1010030340901c1e84102a00c0c4d002e100f9803e010108404c0c10b9030169041a015607000e616030800a49a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 262891034 1250 262889784 262889791
    0x61406090a0903051605011b020604030e1002060a0b04150b04080f010605030d030c0302070206040b0304020a0e06060d15030c1508010e1603020703031103010b0a020714180c041d 78
    0xe49505000900810340c94040c001d2841e0b0b15540e041d10341100c51056442819200c08107403060b42d1386a030322004210540e9004000c0801c103030010200d41c501031900901030514581042c0c018002100d142402c581c00080031a000707010307003801045048005c000308004001c2d41080c010020148a400a2040700c075000600c19107241000f40c42d80740d21106201400d035060b030310070140c0582c40222226030b41032190b409068901c07280e180151070300721030b600010400d070030580050806400001c1848118034050b0410401005451911407444ca803010028520b80101c141c81109aa00d42103d91002296140d0020103154088443d40e0403e44441c04040100b0110002c0301c041414040082034007540899014415655140c1d030810074100c00c0300032006504a02000c90a243e162002c800304a4201806540a00703842032080fa2110070501c4002d28014055109100c00c3c0c41d1040000c5203503e84034004072407000803000300c4003e9141c00ca0060303914803559101c202410b940382c0320400741050403060a0302 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 262892284 1250 262891034 262891039
    0x20d0204050102060c031e0c1903020901021908160804030203060f060909070305030412050c0a08010c030614090a0507090305120304140613060b030c060d050a050718050603040f061406 81
    0x2141e9250090b5030746522054451101f0000024249483e41c140649016403000a00390340b68201060b070003c010041040b11848408650003041405455904100211f103920100c0d2040c421500e15440700b05813881090402c06000304049100824814100111401554003408a0b006403030140d040955602c425101c49224000c0d0340049250344400041400036240c001c00514039091401420b091a60402002101c5d203024043c0040035641d00d5042c1540140b0304980041402030580200030110340b95900304c1c13000020752540400d01a120301c0b00d800d6020220007c0020385032100081a100030b007141e40010041c0c840d00c110440980c801c1c20103180101e200c3c060b04180c5888042c17001d40c560b40c04490048c0702e40307000c50030a40464400c0d0400503140340040d080d900505890350104101d9408000c1c60310965445e0f1040c400c0c868168403d1551220461078500c0c01c5030031001c0d180410b4010303480380903c81d00000c00881c080c03042c169061040c00740d11413010012803141c95550f03d19a0b800716400c1d031 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 262893534 1250 262892284 262892293
    0x12090b090a14061015110a1a0c0c0a080a02070e01030305070611040503060403030c11070906030c060302090607063603020721061d030304081909120210030f020d0204050102 76
    0x1120308400034045001e1401324090b1016103041c034103243e424000c041004010015800202c040a281c24070414499500034001904035400034003001c9403485016140801221040028400e541c1e00803503070740032481d40700c10742595804203038004a280075003e410079044e841c800000017082680060081c843c803407248800703014508030340c6000e548901961003220341503005038002900083c4241c1c06004203920604201d03610341000c040580c0380022a400c4081843d95a407010720602c010320001c7c1d00146081e14007503140240001c00f1038110700a80e08010441a101c1d000b0407040c860309442c80322495030281003586038411400040001e60000c80c800d4002d40645c1e0000709500351520750030f58100303141d698045000d081d01d5543e00000c10454828240409692038200c00605013031000314040c0d4007440f00951039407980c0210211242400808d1010701c05030741030400004000d1091a410700d41c044407800140ca08840042e0b01410015850cca05540b00190b2070f12200c201d42e016005581c401e90848 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 262894784 1250 262893534 262893563
    0xb0c0c09060a0512011d01020a02190c03030c06110f0d14010e010b0d0209060708090102070e0f270f07060e0d0503071103121303031215050112090b090a 67
    0x105103058256000c5801c9484030406006a0a20000c400340441490000007000c480c0c02c212100041c00f1665036903400d940024152200c103030304120020840c0400d6401c2442d500c0e0035070b00d12a01d800544002000d00c11001142c81c01c1c001c15a100c4032071511621a265a54642c84d041786041d94410014400d0152500b050002d00908008000d03042c0d80340c40850354451303428000d1011640c0c00c01c030b01c440429030f000c009002a030703210070010f060441d21a00030581c86580b0b68001a051003126044080740c10030700010000384455055450b500420f042001c1e41400464036207580001e0034141411085204140302d40700619070000d0341000b220050703035881455040708402c100110a0103880a0100c3d4004d12200011440000450440c000000c0403134028803c0d100307140320980c101e601e940d0060660b01200700705254200c00842c25002c0200b4040140101708242c2c00c43c01d1201303015050401c5000103c070110700849900080d101c0ea04103000400c945000c0502030703039454805008a6264080d940344 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 262896034 1250 262894784 262894789
    0x91b0311130303140d1a150a121d160305010e010207030e0405070c020d050312160503040303090c1a0309070902040308031b0409050c07050610050a0509040204150b0c0c 74
    0x15074030025090750250034401d00d1620b00f00d03a20120305100e066180703010003030742103400440d118410b40d0001c450001c1c40030701030b075008020401d000d94296001c03502c2d0801a9492590b4000e000a8048244802c00a01c0c0d0304c2c09048400710b0b208079405c5104901c500b038001211003070001c0307103401220b1040d0002e000707403101c43d0400ca00b40c1c000e089009010030f0f41c1420103a004d1409410442e4060803524088056080c1ca0b00010b03020000c40380305071342ca900300080400300000000c5456a10164200e49817601c0b45078544018090310004102a0401d551414080d0410180c0070a550090000500e1075890301544045204954401d407032880b1035100d03408000407121400d000b9103003241d40004002d0b0540e6606a11005862005001294264402c10021400031202e00c9014020812070b1281521211145001c61800c08094400360150075051020406a903c00140606481c01512aa00e882d01e541c804540038001600f55440b40c0741e00402c0100700c59941001501c15140a0411221000c85490a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 262897284 1250 262896034 262896037
    0x309010516180909171902060c0a0e1207150203131403060c1e0f04030b06090609070c2904031704150506030a06060306021b0102090a050f0109091b0311 67
    0x1003055101c100d40d82c10404800564403080e9444d002e0051070030030b400703814441e40c810b41c8541e42110743c24206170300b4042080e070704124503684548000d041c0c0d03162600c05440a0072840c001c010062007138202e402d189804801c107200600051489201c00c4144030382ca150083d48030340000c403d40c00e0718042d1000001c0d40301c8070f84802e11045440030300641003070740303690641e451650f101c0c2d40d0842444090304c032031010851402d402850950112001c885c0c0721421494503481c855400703081188190041e40a11600c2e80c1c0701d0f4252a00f01949041c0384044400e24580441c1590b43c9a00500701392900c80c0f01d59112034410441d15100c1e911a940b00d441620220903030001a10050341d024260b903280d00c0c2c1c2450408025841140c029500070110f071400f2901c5d5a405094800740d8200b140d02c180c01256542d64030340c0b011944405041100000d5040000420110f00c000825101382072052081c05115540d5034040e40c041c1c03026100081050100801e51100305407000103030351401c80068500381c0a003d2001d050700 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 262898534 1250 262897284 262897307
    0x712031b090b030a0e0f070306090b06060309121303150c030e06090a0209180d020c040c140f07060b06030103031d040204030b070c0602040f081006060e100516080309010516 76
    0x1200605540321240ea58005202000e883c480d45d109200341b40d291000c00b005080000c6205102c003003400e82c0a0301d0b240d40e021b00064a002d004103003d10620500410108442814460070008151180c10006811460181c954000b03010780c1c0440d021959482c65940004411507000d45050104907030b40d0340c08907941c1e03008940142107a041201d90380018601080c081c3d07002200c400032034441d03175880310449041881c1284008050f0b400403003500d1650074540260213640d01e00d400c18805200c3c50f152040450710039158440c0c8405800140711082040d95800328004140250005450b5a101e1074050038181650282505010303003202c14400d01c1c41c0c02d000b1141035035400305401d90b1b2a158008240c1c0c1c0d0248840d0220781c110f4003803102094210810300088010180d000c000c0821010060071a02140c0803900400200103002420f410261103210702c4003501e80517490800c1d9580440c3c0c0228508c003425400080000000200344092124150000c6000d2100310901c0500d400541e403082c3c80c0310001c0c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 262899784 1250 262898534 262898549
    0xd05151c0605130f11030102040b0c01050405010507081306020d0e03070c08010f02091c03030902120c010e03010212270d030506090906040309060c0206070c03080403050f0d0206040204020f0712031b09 88
    0x884d4600007801c080e007900804000a4005418152180c2001e4400d410a008aa207140e41da0006c206c1440024099150443d40f2414501a18208070040e0048200141ea0180485400082d2426081e149502489000207042c0c00d6980307a007241c0c60700c034803c40c0d081d20a0500030b6080402c0a481c840c054421140c000300001c040303000c426480700c00341900480940d015018140e9800c468005030700c604440154040c211005046014603000016041000341e000d003a000303070b2042c40301c0f1007100c442d1040301d60401c00301c1c28480c10881c10082ca41541041d0619014207074058002815161601a00154041c2c10100ea0202c507550319040016510720701210b025001a400072410402c0c18003d1041c41002e500182110340b4009098441407004541d5034003c455a10b0009010000e0000510940340b080b42c401d000703002c00c4400010000d540301000b80c4040d2160768001641c0c3d000000303c40441e02c41c2a807180601a00e0b5400b0400900240380141d481102c0780c0c01603281440c560311944401c1d045c0c036400c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 262901034 1250 262899784 262899803
    0x1d0c040b090d02031515150f1b07031208010f051815060c030f07060e03030f1f230f27090c1f020709050c0d05151c060513 54
    0x407541080201e40600009a8050042c0000d0141c02080c010095200f000900c0340f5400c00080c0314180415440380007241450030b80e050204195071549802155015480400142c0036a06002141e5051440c160710041500210503485081c1c10b8004454074101c4580700300c0c8000721039845090100304810b0030040c242203c0041c00181203021007000c141525800981054188446103842c81e1a41d0702c0f01c403040d0403030100030038800b040000502030001021520400345045091004007014100e5020780040901ca0310054114514003000b03000b50000e124400d0070703030310381e950045031010111151500c2501800e0401d2080f0480d05010304490f212801801d17200c001201c1404a480c8581c0014019209078081c0e0309101d482035803643c00c0c4c00503681d4004c1d40251001111500640b41000030380c0501e118070706183c10420b480c0d944c3c500b5914451050003003c6901d54421190907400c180e85d18030294030542142000400c91008108200e0492107080c1c100120b403549200344100807071846004000300314 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 262902284 1250 262901034 262901047
    0x901060c1a07090b070605240604030b071205071805011d01030203090307080c0d0329011b060e212d0c01060e0a140103030f03150509011d0c040b 64
    0x300c030280309602020b03e151001025440c0c00c10f0040943c00316609840300e036110818009020340902c80344040d05c000e1480214012618004203889000d90700c0013a10309101c00d030004101d18041d4943e485d040c68600c0c0304109500c2c0c560740c0900360100c0b11203900440c0c0742c0080c0200c0c665000d5681515011141280040180b241000441c041d600007803824055020034411140010b0031a00038081c021121030140c441d002c40c05034001d007200c0c0402071075401c441007407800007071005040c00001740703405007031070091980d0340d09030341c03040d0704203946078008041d186800300c60811014007245011141d61070700c000d41c48608031301001e212a8000d01042e45841200c01501c8800c40d81d89034000350720030003900100d904040a5a40b141d003115144d80c0f0500300da0287c0c104000ca0078541e44103044c051504050305064650440d2002000300810310b55003803d065581c5425181c2061000090300103080091103404030b036031a0481c815045c0703030b000030b00c4020b0800080032600c3c0d00b04200503075050b00c0900d41803038103160 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 262903534 1250 262902284 262902323
    0x80615030112030c0204050c1b0c010f0509040209150a020111070506010501050901120609020304110306150f0a080106081612050307171c09030f03060303050306090603010222050901060c 82
    0x102c20758200d044c00701140d842c000680b44c0d405014461024061065140c03400103010205040300140c500070190001c8001c101c2682e04040000a600340b135140c02d61b101c40c40980450020702c81c213403089500410303402d508a03c0050300001007a16100c294001d00c8039900301980c826890051000040003900070324010b02640d489000601b80c01d00b014504141804e141f40001d04c1124200d4001c642e0540e0000100814410090f04022500d1010360040c1719518084011700c481500841d241c40c07151032701004081075036071140c80c02c4001e0612003000300403056440010b142d580d036603503807100c00c40c0c02d030940000307421200707600350340324983e0004050351600c42e45680310001b401440800c6a4851024444d42a04605c1c911400c01d0b07103440c00100044081e0681000740118425000b40d00426007400f10900000b036204040e02e0b003101090b184415a40c88000c00240a8010400040d40b0704840c0301c0102244000381010108581d010745840c10b485c2d0721104111140000300074050100d49401298460f5035 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 262904784 1250 262903534 262903559
    0x90522110a0603061404020a02121207020c010f0503070f020708030c0705040f181403041505120a060f21051621081605150106050a140c0d0f02070b030f0103030806150301 75
    0x45449c0705a80032241d030300b01000101d406c542d402d400d004802c4010014465010000c3c1031b803c5000342041240c80401c504024140d1100820078010003640c541c4200c1428001c00c00c00c006801c0101c1a04d40f03a0244062495072100700d482481d120302d003848864028103a25100c1c00c00d60181d0a61401240c44440d11445100c401140040669100400001422008141c202180d01c0c2159560942c0da00b59450301203002a000751800d66607d00d010030130070010545148400450300c503038040140c107500300b4001416800300342d0005002030042038059044461030090000699410b141925684449590158171000044e00001c0244204001c6603121085560340400903d114804031416200d00703100750700070a042a4006000b00c0d6020400c00b00c200d810035015010415110b50080c1013102d007a500780e584a40401c0c2d90401c0c48507603006410198800c0c000d401c050314580300c00590f81c1c02c00800300fa130465024882600095800301c041007441c0380c40e1701c1801010072003a8209056034204100d01c101e4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 262906034 1250 262904784 262904797
    0xd2a020306011e0f0611010b0f03060613060b0a08060a08010509031605010f0903020c030c04050402030c0105031e0114100f08061c051c030c0810090522110a060306140402 75
    0x490709034500020b01c3e501025044c40074004a644255076982414280d5094501640c1098462150600c03440c6a079100000d80c982e01c800102c4009400364a801590002048150402d5000640c000b400c480510f0304030b12118024402170303400c040c9465940e1100d40c22100e041c0c410300000e4004100c05070502c0583c0b81e4050301203026100018400d100b40061404031482103804802581054401c119145020300200c280444261014800c0d450650f002a44412050404906010000c000300c4c500003d042d1603079601181c81c1510f00202c1d41c5800b00c081905008110071340c400c4400b0b140c0300703880303c2c86082c4001181d05143c0300d00089031078043c02c1002c0ca107010601641a40396800b05040426010068074611050000560a0b243c0d0402001425216443e406400703102d03080741803041500c800720f02a01195035008000540d511003a070381841c601180c020154545000420320014800880034480200e0011160700f014181d842c08258103989151043c1032508620340e01191036410306800400f00c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 262907284 1250 262906034 262906079
    0x81606050307050904110c070302040b0f0105090d140a0809040c030606050a0e03101d0601050105090904031d0a06171012032111041406070f0f03110d2a02030601 71
    0x1704000c401d4075401b0036411840c85040e02d0303441a401002035041910461441c0d0740c0036207019403180d0164001030000d1003400c0701640218410403120041c40301ca11076286c8007220b0350058645000003410315801a410142d5a180b145190040c0081300c18000d100380011100107488460a0a032140802d55940c042200c009030540285003c4d01050074180c803503080c8541c1240c8054090740c2442051074a05101604010f0600034104a554101e03990340e03150075032050745440e19a00b10a404c8400001000401e60380d80c0e0030240f800d00114806400c55030000030032400104400c083c0e80c6031400401c0400082c0305000c0381080c00d07944034001c01d10426213801c6110310702c04054121524003c1c4401218481146200204004201800121030080c40f0a50b0f8a5049a01c0e5040c107601c0d841c1c44021a0309413038000e01c80140c000502c000c247c043c003009034144071601c0982d440403c06400144c1400c034010303104100b5801e4420b400c003419403441c90803204190007500030895a030a105542400351004028000c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 262908534 1250 262907284 262907291
    0xb0402070c0e1317040602101505090a020705011b1803030f0f02070b13030c0602030418390201150305030417120d0b0a060507020915040b03010213081606050307050904 74
    0x40c003103400300c0c0c0184c1144640100003a81c45113016802410315500f6030b8000314940c10701d02c21013142c60280c00b4420a132001110380c0d901340c2d20b5004160000b4462403070003c1055080869881040b043e14013a03030b8401450b6210150882030f110400d208036a040c2c040200440d0a84000c1710240384a841071850404040c01115007590329281d042c0d0958102c0701c0500b80416104009004106d420088000207002d2030000b141490300340302800c00a0901d9210018165541c1c0000703006c610383d0032020301c20f0159040c02403c00c2880c2c14490020485410019502560030140c5182411041c0c660410440e40c00c003000c0c500742802e1000b2103009281380c084050144c072603070a000d0f0411000c40000c002200c0c20040005c1c0912510b018000c45440c154444018020b0500401d4050b81b6203031340c0682d000842c4480d1042c041c40140015000b480d91007407094042d031011810300080c0c10480c000500341c406443c01c441e0340a480400c00c0c0003607082030060b200060014004181d12a00480281a21400051010 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 262909784 1250 262908534 262908571
    0xb0708090a0f0c3215070803040f110609030a0b07031407020a0308070e01021e120c0105040506010e04030906030b01020c040c020313080309030a08071703040f060b0402070c0e 77
    0x40050031042c0710b068501c00e07080641040b944070309503203e1107800c2ea15805040240d01c1c4500c010411a03501040d40e01400700c11380300c16200c2c40c119049641c66940020303043e80381e0a003410100d04000c1001d408581c0c0c201908004082e6207804e0040e1340d10080300a0080c8140392035070795500d9919001400340310a041c0c0f952041d05241e001c0240781071140e82c855000b040056001c1c20700a2400201510440911400e0448940c03c3d981c0451903460f02180390101080c00001c1c42d145519106100c400600210000f1503802d0b0092010b420490045004074210b48069894000b821405c60080e60010f010030001030042007150702a800c61060f0203014015521807010000c080360a50f04070391074160050b04001040c180c0840c0c1030150601a0404130021414800304000acaaa075204041000d000b040000c511482044104001130a0060b0446035241c0c5a04052500c80042095218202d80460500102c030441d400e0a01c2514040307900312400310344192600228281c2020041d15082d20484a061007 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 262911034 1250 262909784 262909793
    0xf0a05090604030f030c0b0601140d1d03030a0b03063601090b0a0b041404020303040620030a0804230d050a020f07080c010905040218120f1f0b0306040b0708090a 71
    0x208051701907121291701d00c015113050307819460011f0040b0f05103c9569130708161040702c00d003590b00c030200700d42d400503640c20040228200355615010001d5203110000410102c024560000410302a082e02105c80c01c3d01c9540c0504e0b44407040568011082c29043c88004850043d5100704e0307030400d0b44000004010003591212401300c4012543740d5100c0780c8a101d00c603a82e0606100d829074448100d0140e01840c02c25500107a180e00c5917100301c00c2081003e80c0069203d985032408602d00100b4842103035684c03201345502500d04001124141d450300c595000651640401852901400c56420701500308030100c0c40c01607032940c120221b28800c52180b5a0035035031403802002050060143c8200030170b40741d08407400040004090343c0120380564010304c40010bc00500078140c1228a40032511b010b6081e0920781040e01c2c21650307031800341c00740c070480b200089807502904002c14440014030040c00301c07045c03d1080c156545000c0d1001072008068400140c1107a2081d00d916410111010946800950030380b01c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 262912284 1250 262911034 262911053
    0x608010b19140708090a150c061505130518030a171504021605101107140f120909010603140a0c030b1201020d05070c0201090e070507150902040b01050f0a0509060403 73
    0x24101d59907000015043c02c9031800822442c0105040309945c7c8808500400060280035283c070010449030300c44280321150102d100c1040d01a210141c688155010b8240203103015241c2a11507141500508d03090f105402d10200844065030313000c1d101c400400d0040d0304100c00c00340c40100b21000f41858135410b951555528001040184400f80141c00111401c0c140386041c0305000903400001d5240c5001007280744940c40549502580121981041030243ca00250514142c944410002d01444004405412041001d4811200140d4620500c3da896200541c12180e00a00c031126040c4804002103d244440d04008180d250324540840e4211081c4080b968200058400441c56500410724007c104041d00c12a64000000d180c641410072103900040c05148403400b80c50030780c0c14400005030311a07020300b04540c0440c1c1d0000a070910391b008640e01c40c0040c01c04a42c01c07807141d81842d20314841903202e181a6519080c04202982ca030003544c884c02d450707951143c10b07281e411150034000000414183d00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 262913534 1250 262912284 262912297
    0x6080a0b1308041206090c0e010609030b0603030705010c020604110604030b36030403060b06160b07110607030614040e0c040b0a050301020a08060a0b040303020318061b030d060608010b1914 83
    0x100041b070491704070721b00120802d2450700b1603c400b80b601c1c0010007034a0f910101d03a0045a400c00b00020090f12140b01081c2540b040902c06000c560820802d44200c070342c0026031074466400303188002044403200c0200607070f0f44150310001c3e103082c0307581000c180b1140840042043e411070201e034110111011200004612b0b00d004410b00064001080c208144405801950001d50044030b0840c0361207108072800c0480700514001501c1d10340c4990014403100d00034050800c1c003074030f254202c600b145040d140041c003400306406601d900c42140020715107a4249402603000d0f0a801e200600a194854005c0c0b000401c031918085034007010010000500c1d8030284018100e01c0d1b00350b503d903296807400e031041c4003c0342600c9c0d001000c508000c10040021a9000c802d4a00d1580803007c81000e0a0321100010102d0003847d035000742d0070843c08080e2904100000040000c404910000d0101a41c0da08040c0c42241e024810f4000c100000c002241003007c40b0806026140317245e0404000401201c0c521921540180 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 262914784 1250 262913534 262913543
    0x303010f06080412080405070e0a0c0f03020a0804111c0506010611030c060c0703030b10080105010e2704020301150f230f01030e0c1302030a06080a0b13080412 70
    0x4010300020000c51804405041c032420312048500345035480c044d510801e02030080401040c000400c040102c01c4c4909001442141c3e00c0c0151070904000800040c16445e081e0780100e90f040c0740803900140a4025540e22085988502c0348030b60f5a1b455074061003182c1030340c06a00541c0c120084c400c3d040c40c102c1d905c031a0340c0510020301181d03050000c0a01f0200744400c400314070303a2042c46000750b1000b000540552004c5009805611041645000d90152441c108002d5101400f891801241c2d07a022242a040707510076a1140104218141800a807440c402000400248420030b61802240790f81d82180d0001d202500010f0400024500240101c5260300411028012100104400d0808005010301541c007036681d1810160001d002564032007103814031a041c152200c004400d00042031094455585002c0d0101401c80d042c845c0c2c0358001d5100708c41c142c40f40d510f090400b04d42c0040024203844240d82c0420480081d460740302d400d030416204480219807410081001040e0340142003204034900707204 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 262916034 1250 262914784 262914787
    0x50a0609021c0e06091209011b03030902030c060313020d021201050103051b0910050108070309050316021927090f1505160503010501030b01090306110c06011a0a0305220503 76
    0x102c120b010299038100042c40c059500c40c0c814040e028001043e0086184058902103907103a000c0001030f11401414000c0381c40c0d0420114180050607050f41090010900c03c070f083d00c80b000d001ca020010a8003060b61004159008480284014107096004241d41800284481040201009200e094030303026002150b481d04050b0444260800340c1d03054020468049900300300030728101103980c80c80300e00d6205007810011440c0210740341a000e98403007102e02c0d40000a0b41e6580510340210b443c14030411504a00595031038500500c032001198002d4181c9100a00114102c11030100c00304c0880100c203400e03e901695050b404002420b403450300c800ca07600c600c0150000c040760802d40341c102c440061010034200740c1d813112034030810303881821a03064031070900780015a518504012149a001500020412072078058080d602c18264400b0b4142070066008888060380c0350804080c0604d008034540d150000180f1030038a0b218000d8015940c002c50303045403484403010921410700348400c454000e0b1601c1c0c20 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 262917284 1250 262916034 262916077
    0x2070204060311010809010908070f1b0306020301060e06070f020d1b030320031317010f0509010509010c110a0209062e0207051203030a020d020c0307030203041e0513050a060902 78
    0xc01201e415809506c13071000b0000031006403900340c1248900c400c01420507040c0d4089a00f00508080360010f0130300d2070901050100d84900d86640254000c0c025440451518081488285050002c540c00c090303114091010700d8481d07900348585104800d0084070380c4044a5001d1f076001000700c40c00c0d8000c5009503202414044101c3c0140e1100c1c24010300b0030341c0c1d50000c002c1c28080c00300c20a00d24003258040c88600b240307564441105401000c4140350300141074104070500000c0c410540081f0701550002000b0000301080c0041900c0c205c101540c000c1f8503811008400c13002d407510380080c99001c54082c0c00f05165241d859030000f82c2000c481c0103842c110156102c002c0390607a0411244001e0320703081c0d406003803400d001c90740647d0342d00004015520084d000035040c1e8801510f030301036a921356004002c6948404c820326011391030707800ca070040b21064800124088401e20000e00004111100a040d00801046807401d410260000810000b0032a0b115031001445951600c01800503848910a540103400c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 262918534 1250 262917284 262917287
    0x180207120f0311030112020f040f0213140909060c030718031a0901020301050303160503040f06020718180201110a02090717130503120702070b0f0c0c031b12010207020406031101 78
    0x120118220f00203540144018009610103c2c5042e02040c4c045801c5070b0005501d800240140c41d0080c0341d20442d5001060f13020880d8100e00050003070743d16101007a07401d00700040600181c40d0040b0340c211010b600400101e89004502c10080d90000c03401c0c6002c10050b000001c061422251070f520845419213041840d01103036482d0418580c001000300000e524651410780040c8e80c030b02910041e02d100c0280c864080b42080b10800c200c034001d003000c50b00f00c0001e6580c1e4601039100d03145485100618061240031001c00c00c543e01c5204107281c2c0030000c0c02c0701240702d078004507030038441100c1400c42403240c1c43c982005603503017641e11340c0704400c0c541d200c1aa40300e18480b440020240508048000048500035000245005c006e80e1890112850341814603610004101d18202455121042c0f1f908005002203025178180014a070498800302240c030b200e00250245a507481d1360840449440c000d00b14541440c3c6020031800b0500f030051b400141c14500140c0008048625950040b1280003102c041c407240365 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 262919784 1250 262918534 262918541
    0x1003051b0405061801050f1207091d01020c070303050318010e01020a1101150b0f12010b18010c0201091a12131b03030c02060304060f02130302210304180207120f03 72
    0xb038410b0b84c01900c0e5440707400f010f07007142e00306008092094400b00c01d100d0168035440700703071804442401d00301d072071007541d501184000340001d02290020081134400d80c0020300050007117808140324030008000c3e451a60701d003144c46800140910080d0030141c41c1c6011040d009020b15a500e0000e030380011b030384d280620740c0503203604022407400e4202d034100300c1d89001480e203020240c1c0841d9800014107594840700c1414485a02c11402c0b40343c0206600000801c000d01000c2c084c142d001280055041100c0e03501005507000c603500600280040c0d8074030005c0c4003074100940c2c4d040e000b05140c2c00403070038020000303031041e200e031400c4a08451400c503030910441407021180d4140f142d26020074402c1c010a04584009208515203103029001d14800000300301004110380c84001c200c010104115200d100700084481000304520060348581c2c00380c1ca0b03901d903a2180c04010010075003440d00071460180380c41d14410754203111000740d41c1119802c2c0000c0e000301d800c5100c082400c01d1503643d175140150303101c0030117801c5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 262921034 1250 262919784 262919791
    0x30206150321090402070b01060206070924030c020c18100f060c06020a180b070b070e0f041a100908060a1a040b040635060906040b1003051b0405 64
    0x10354003074110090b5801000c9165000151410045a681c40c24440842c010b4407503900010082c10005000190581d4007280180c0100c010b17541e903800300ca580f1441c40d0300f560001840d04607505802240501c0d014000d60041100c60014010303030702c90b14010b9001621104240141070040074000d803c101004004100c80c1000d045030007050b000b189d0030810001c05484407504010070700c9a0029000d2101d50085840300201c00380200da8000d010380b1b2b0034a42c20107400c11141142c00e0f0301d030400440c68050003840c810380a00c9010b000101a444254100300c00f40c800d40007620070102c1d2001e0300d00945d4031031502e4410180f6454881c9441c00d403403e10082d00d0b1040007020605243c0ca0003400111107164600726401c9004210f07000309a20003140b00081c0100600d500104244c2c03000b15140243c03002c0c50342c017480c41000301d40104403150000c4402d02d4503a20b0895100b00150440310000b40090840c803c444c0d00083c41c80c0d0040103141d01c0383d50391072034040382c40c16010a210f2002c441c0c001a280c203000c4ea650 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 262922284 1250 262921034 262921039
    0xa090b090f0403020618030408060a0920221b020609060a0902090a0905011506020106080709182907020a060501050f031c0e040612030e09090a080a050c010903020615 73
    0x2168903240e10f00a49400c409040303580805120009624084401c00944003c0c000b080140d030000d00700311003000d00500e4080e90458144209034000d49200341000101001000080c120008640c803180281000480d6400a0305080740d42c3c59140130260440c00d00c0311841c1c03405400512050808070311552070f100d0000c040c14016800c105207100161100c620483d040910300c0c0003c14010824609503005d4542c15a0031044004102400600d0301c1d8150050002c4036050f0b01039500c180c5c0c581150340700f9540d504030f290400202d600588030024030718000840062002d4840303408161407140502c14405019903001c07005074030900e0f04030300303104d154469680101400c403503020b4036000b0000401d85a1203001c031a10702d002410302c140c601d03444c0a1882c05460780c0f0700410810545482c0c030000020503444010580001d60f0340a0000c10303e0401001080c02180c100c8010401d80030640c1d01c1e070200381e100c00c0d03a034403c010043c070825190745000d006450070345110345c010300000d1038159100d45404104081312031 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 262923534 1250 262922284 262922311
    0x705040e03042d1502070b0904060509090601051e01090b0f04030b10050a171b03010e15180105100b07060609020705030309120f1b0304030c0b1210050906010806010c020a090b09 78
    0x41401760001a21001c4078140c4203c182c460280307200080c028001984501d401c0b035400800c001c0c0070fa80100781e95040c3c503c00c94030309101c06822502003090300d600c07106050105201c10428050440310038068060341806542d180c0c9015242c5e03495003006a0141ca818a8800c12200c06001d285040c9054001805001001c9003501e0b40070701d1295074403142c51000070f1f40100c00c0c4400e5405a142900140300ca10081400c4859155107031000d051a42070488a0298a17419590324103011041070091a014041801030322a04a0800c030b02011141c0c0040c10880e01e21303270307074a10020706801580050907286004401560302c130321f0318134a1a401d00f0040803800817060700802c0120314801e0104151a00c21441045001114060880162440c030564001501600b12601c0010325003c002d40100001c07100015404980d4643c0d0f0003281d1105018059558400030500005805500c20814a17600020500d45140d1907020354000c01c000d442c090300a10265170f00c074454894141400c0c0c440c2500043e2803908078 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 262924784 1250 262923534 262923569
    0x403020c0306060612090f01050903310e07030e01090f03030f050f0c0a020a0204090c15050309060f061f03061401091206051905070201060501091203020705040e03042d 74
    0x13035601c2c481c800741031103240c00d050007060034640b04200c42080e1601e080000c0286080c400030143d82e80c0c0001141d100300750116902d5003000075184c41680042c1c1108120303c43d055080c0a02030a0b074a4005001038109030341d03038a9600d4a082e00340a14419103001c6c1c06100c00c00010703414028280d801100034141c5050500303043c03045204010700340e1548540139240464440020b6842241000b2625070083c0d4414201545502800381c1c8807043c400b190001110003500403200c1d80151003c3c0000c07601c03a04036403c00000100400003428480b07500040041c40c10b940300407200f4119000711005424000000ea8800c0e00b8480030f100402000c030060307003d080c0001d1303803071414001c0324006001004c0240300c00d03282c10101d40900b180780700040702d41e040000d050080d45401076009000f800184103071030004504110000340c054505ca0002142601a4040c0c0728070f41c100030034000075140512442c1d447e44002c000001d411380704a0360070110350340ca0580c0c1444502100000c0340a6810b00c0c0c001440caa141803039107 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 262926034 1250 262924784 262924789
    0x2160b070204230a0c0c051605040e0d020d180512150a060b07020f030a1509020405060108090a0b18030720150d05040206040e04140d0513031106210403020c030606 72
    0x80c0d950103000200b000c142603402107021105000c1da4074009056128512342641c001c01d56411040c2503c10a407000c02c02100f00c1141d0580d01c2d0440d40300640580c1080b40105203071032045030000c0044454910b1248a640e403400482c142000040e6032000d80e81000b405244400d04502c0307085d030070041d080700a0001d203040007e0101d2902c14044000e1085010010840c6152400d01405502c1a0800529442e00e07500d02c0c083c10240040d944200e10561428001030869801140c2890264030204010700594040d07a07100550144050801d00c0d5801030306c0364110b1800da0400042000d42d200c3c2c0f01c6c89a101d0410b500025110181e803055603c112021b03090029105405000c0e2541c4180c0d01d000841c40d80ca460020580e18030994110401c0c4208140c200004d00441003250140c1c5c2c0c80308000c6a6070628180b0003200c1500840c211240e8000700740c041040822001410046110700040201e49400d4045c01c0c445420700d1680f5600c81c1c0c45014404100c117058050010086591040d00900030900e0309100 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 262927284 1250 262926034 262926101
    0xd030509010c090611120c07080d020109031202161e060b09040f170c15010e070801050f010e15041d07021b040f02090a06030218041b0f02160b070204 66
    0x4072005c0083d5030044200c161130410940801c0030110044903590005135858580310051409008286d1142d0758280201c548144950001d103034043d030b40c001c2180d0b040c0394000003940c08414000e5282407185080f40104460481184605507a107411070301200e61440c1c10742c142c0c0d0180301d05c18480c10b00c0104210210300040c001000d010b50006403443c4105401c01d200c0746d64000e16242d0411803164004103466400400401c9060f130b45001d01c908182e50700c4643c1103994013803d0027503541101e2f00103088200c03035004000382c10002c0c0f0000e140d504034420b0017201000540281c1c2c041056001c2103c44281190203c0b01c1d40e07500541180f01404100b000c81320071607031809081c1115801983c0e140c00555801d041d55054848042c070082800310001e907a45401030194000740c21041000c0040c0002004034070b014410082c03020404070403d0310180300704000740c0d8103510001000041d4001c0c40300c2c40701c0c1c06901e00b032080058008254487e032074820761300520040340e000c03422070307141041c42c811800c1e062400c03560b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 262928534 1250 262927284 262927289
    0x110702010e0a081203010303140a0c06021305120606010801081b0d030c060515030124031e12030c0e090121032703020f06190c0204110c0d030509010c09 67
    0x7460032400041001040031184954094040f9024011071140784000710001141241d02951318014548262646604070348982c500e48804074458a04100c0007611700d0f005002440f03400c2c501d81e9040c65807100803912200800002403201d0f0800000c0004c65078010b20018050101000141396000704604602180380b68500c20520910b5540c5008003014030600101d021543e105400344010f0a0000c80915a050280c1e0712620a50038070380d01025105007103104c25103200d614280b205e0982c0c0340d03072900700f01552080001080c13600201c0740080800c00c03014000b10140d0f42541c000030101144040100311134600e0f1403283c41000d80c500100601c000c9a445000030b006041403c08110005103400d8076450310712001d20200000740340c1030035591701ca0b2a41e0700045900070f4618030712901e01ea5040200d03a2107240c013030380201409040c00c1d00f03040b48112405d032055440540009400d82e00e4840c64542c54100e200c2106495100807410010aa81070141c0f50300001e000d0001c2c040c8070110580500900c0003070 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 262929784 1250 262928534 262928537
    0x309021c0b0f0c070206070807170c120d090501020c031c020403020a0b18100f08090114011a0418060314160506090307090c020a1403090607080a0c0b0a0b040f11070201 74
    0x38004100700030f003124126412075500511003580c608030ba00e030030703415600101402d440c88000d2a01420410905208a03030f26002000c0162945042100070a88150005600c900c0c0c641c0e6654081000214244020326030010403400840d11000c1c07400b05140c480c2000342ca1101c0309801030100b0030060721101140800d440101d10300a403150404550007030041c502100c9164010710507040b0740941d40e04441c5c0100c07185115523688095690341521182038440300d040e02d400404040c801006001d481d0000d400c01030307020310380d02071900f5034522007400030104181c00410b11903a1a54200308003e81440103001d001c0ca580701030200c0c01e01c0ac50070092682c040b440703600d008110005009401e0383c0c003409080060f00a0790801c2140321041c142c001c0d500c042a40c41141c03003c070030081c60519000000280c4d00184801400380740713000c8440c0d9812072203400c1108418144100d882a120018000d511140c0c4151020480080d082c0c440b641008191030203541d0010016160075038603e119040c003000c0301d000540a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 262931034 1250 262929784 262929811
    0x100e0d11030d0207021c06020d0e0102091f0c1217070c020f04020d1d21070b0105010f110f010b01030f18080c0a1401020903060a05010503060a15050307060309021c0b 73
    0x16400030071440c81b070500710940080201c0404a08200300d41d801f820043c041207030100030302c0c504240203601302d10402c06120350110b9401c90300501803211500d0410201524913140302074008030780d5203000700a01500c4484c007064030303401c400d0b4010090842e030b19800380c0d05140c1404013081d96008140000d0010314924011500040c820a034002603410007502c0000c40040c01d2444881a0030840d01c0340c6403e001482c1071a041c0140701d48402c410f6095882150300f059226656900e060300541d20310405007010b100f40100340300c401c01e200c0424000d11692040d048000b1a60f51203090004080700c0f800100602070a00c0d00c10f008880d2a00c140d03444218560106840e83e55a0603070310202d2030060006d000503d200d441522000d04240107401502403480b042e000c50744a42c84010b441402d41d0000d01400380c040d400600010105012a002002000201d640d50a95030342c0354404a070400d903c0d0341102e0082501e0310808005c6050402c80d4082e6100c0e400c40d12580150a90380d95545144040d0903032002c800d0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 262932284 1250 262931034 262931047
    0x50712080705190e060403030801090f15060e03010f0501060e150406120504020f2805030d0e010c02190602070602070b03150d0602160f0501050a050f07030e070503100e0d11030d02 79
    0x201d1303085840110060159407034903070340d02d40200300000034016454002e040550008014586026804003103000440c1c239060750f420101c04440043d01000306950564883c0d9519a410042d4410b0131b0280ca040d580e9000051110b00c18422490b1990180c2d0030b410100308410030949a200c1203004207008030400109964590340009003140d15945d9000b81d0142d1000c20500d00300504800c4804240e0782e0032030241003980d40d1400c05483d440c03c0d0b54494003241c0e56441000320380d071142c119000003d1004180380d110b4980c4001000001005030403040c05a0b105031410320516030104241001040c42105040c914640381410b40641188a028039000d00e041171700b11810040701c0c0e010b07070f0490420303511802c11905041c10240302d0403000c200140da00d03518006c0402c0300c0c0010350241511480e205030030454540c44000c4220024102c05081132001d0180c442c0c040703190f940074440000c00d80c450303181c082003541040c40d00b00e04000e21400c0b036030280440184040050680402611841c0c8007040c401a101c07607 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 262933534 1250 262932284 262932287
    0x16030c05010c03050907080a0210120906051614031303080c0d0f02030103030306060f021f020903070824010e010509070e120a05070605040506030a0207020a0e0705071208070519 78
    0x2458408000d04650805440261a641c180d1001344905c0002041300c00c0c0580d54909103855250202010750418268004450200d014400d041c0b2100c0300c800c00025845481e450b00c0c1c0440340305407421960382c9106605003a285500889000340e6243d02c02c0c500c1d103141400440144580d04100c3d0003000d000103007000407444500d110941e5580320603184103020f056450480080258400d01007200800c1c0350040125042c0d20540c14020b06401396001850656801744000603100914801c220455408000e411030f140c4080c041c0800514000c802008101d00b2403544d00c10341c8502c1c4000400c00e44191004102d6080180f200a0444000b920b01030f5664450700b03001c0300d021658064440e0800d09110071036048880005000b10701d070780031700c00b0b807120705072685000c6a0b47d1080d0321819038420014008281d403412903a00030300d41944010301022243d56180180f441e445c000300c50070408600081803581c180710780e03c54a051084018502850189010304c03010380640039561000e80b0036242204540ea480b0b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 262934784 1250 262933534 262933547
    0x403020a050a06050108060f010303081308041701060905130203150c0706090807020a090501181d06130b07170403030b010201140c130807060c030c030909090803060f151603 76
    0x25400c8001c0d5a80b6514a0400c2d00252000b84036a203118410500001c00010030172072414162941a0b5454246484544081d603006c9011a03003580c4410040000241d052035100e0100400c106901c004500c0f513282c92208001c81d040240701034a0440010a000010b03a0040b94070500704901f024921856155403e04c400316005185005103514980005c440920500801030200d85108542e940c49040e220702543e42034410038881e2596000c02860310a10b00305081d00245071661400c08002c02e4296910384591030000c00380c81e0800c10010011051050151002c240c40d40320740c090070b0050282c00700c441440041c03030001700041c04240ea24060213105a01c00c0d006160020480800841c0c02d0400b0350a0140e150302032075030541d40080b9030100082001c40403500d001140c0454a48003602406610155074085c4040011401c010880101042c095100e116110309980110340035a1649050420700502c00c101e0b0040130310490309030a05203c100f0910040b94010101c1117a42c0e1503186191a09580d074 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 262936034 1250 262934784 262934803
    0x402070c03080a0c020a17060916060f11060708191a01050c010e0601060807030b010804050703030c150501060509010327060b040f02030c07060b0a060f08060a15030902100306120b040302 82
    0x100240706d03000540d01d0040300544031a40c0d00c2030207803802512480c1c0510b9807042038000c1c5005804d0203450410006005001c0171100040340d0410060100d1003c00c1d00e1b04004d01280c410010403504c5090008000b803107110710309152081a0204150040b92840c1f2603a1380300500c080e03040000001d40d000780341e00e0a41000c1e030103010300c038200c84965845510223450940100c4000d40040d15001b140c181942c0714944042c020b0740c00134007500700381342541c4040315401351011041c0c07198030308540020302e651035900c0ba0383d001700201d603102901c0d2401d801c0010309482150424084442c2d040d40e030b80030018003850031003131050741c41140000c11410040105010f0515103030040e070903910100c2000002c801c3e2000410005105241c10400740d0310304c0e000c021036168580034a10000301c8401c0da90b00f00c9401007942d41d4000a00500811359103a8800914a0040105040500098540703050b0400c41c10700146608102c03c0504050101c142044481e50000b03c0110000d0106c03481c100100d41818000d00c148800b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 262937284 1250 262936034 262936039
    0x210f0c040e19090501050a0e0703030e0d08160302062401080a0903090506070c050406050a0e040f033f050601050a0507020406031b14040c0c1b090e070602010b0402070c03080a0c02 79
    0x90455003029170081004451603418907051540c44c01c8c001034003081c0d1105072030b49511225100e480c09024040440305e85841190500b0f410884c140b1302a69500c001c017001ca00c01d9000704500d281003554075850542c030500e00520710f43c0a030444102e9a8101114a41c800004400058030174506c5c14100e4100b901d9030300c0725070802c1c00040c0d444103200c07000c1906426910292400c0c00074550f03503024850701e115030784281c0d2000c0441f0780200700010712400c100c0070741c10b000e4038092241a60000f142210b400d0b9115001240740c0c0c00032014414260004104004000c0e400030402151504400281082c86172040310002c000001890208554581c1d10a00140d90482524031010401c18180c1040d088140103c401d50184066407031103501d881c1c010701c1c1e00b0480300d50341c0080d0403045695014124011175921550403084e4080030444184a2165000c00f00007040200117084c508440642100c40d030615050040d4010030544011a911030315a00460740d0203480c4a40d01d10142108a8026410f40d00095 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 262938534 1250 262937284 262937291
    0x30603100e07090e0f030a0c14011811090103020906010c1704032607021818101505270702030d0204060507151802060a02010b0402210f0c040e19 64
    0x1400c060000030824241d03107860b0404c004491036640800d65034032032001008415441000b817507004511814130340c0003a5102e881e81040d4800424546401d4440c1c2000407040880c0d0301d81000103101d8403c40070501c903581601e28200c5541075401103261640000c113824144100703c9002802c000d0303540100000d01d801249520f07240c3c1c6d264689824001e400a00d03496540d40071002130624611810201c0e81c2d05a8024846940f5508d003800001c4da1040080043c1c09041402002000c03003181400a030341c050142d094002041980541c800c00f9104141d0040e82c080c055401c40c5964084405004007a0303006c0302d10b1060140c2c2d9950908a10f541b040e5810f145101e800071800050300c980002c060641548113030314134040c040180007080c0132654082d2103620000d000d00d910340e005d070800400900108400c0c6c0f002203910703056880420242d074400b50401c401d00c0c10078142840d040c10020051a02700300f90f55030314151420075505240080c0101d01408801d03c0001001c1106490810607119410703c0320001031 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 262939784 1250 262938534 262938551
    0x61b060e0304030501110c0604060b010e03061009050a020a12050a06080307050601030309090c0c0b150d0b04050c0d1221050901141f060c1407030f030212041a03060310 74
    0x166282e40180c442255190300301041d0204105102003070744c0200e01400001d2129560b40d0300d581e4090311002c10010b05014121a0408050300e060185030f118100f00c50904142c08d18204a2104035200101038011051051103040b1703d96031700c402d40c121802b00440d004100c98075004403100013020258841c1042e0301c0001008010000c01054450480f400f80d00d80510f0703a603403101c1000c140c5121070644000601000d0700c40000410074003825811001c204240543c6040807000700711103110580059500c000d800b4100300412800708022050074005850100b109503603991030007140401120680d06001c68001c8003001415424429600c13001518018031245c01c099001c68001c00380c84682d103101c01042d0000031f400741e08040c80d2440c80d0310034051880c0e213640b43c10022220b041e45040d084820341c1902d0000c050302e0303408009010145024204210764111315240107403a1070807076540300550820900c401c102d203141000c043d400e20f2100002465032545c0b4140064285540e004050500e6850705005 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 262941034 1250 262939784 262939811
    0x2030106020d03150506040b0c210705010f1a0d030309050303070915140d201902191e0f020a03060c09080f060c0a020a080d0f0b06030907061b06 64
    0x800d084180640c804000030124413510000c2c010490280b642c202c1410402000041d4450340149107441c40c40040e541c000200300e244007410090031501982e101c5d40440c4540500c6070078412260760210790041044507444202c07035280092066040b90b0300c540c10040180c0241402508044055603100c410f4982d249002c038005020994030340210030010015400c4440c3c2903006901842c80c614411549a091600c107040000c060000182c905006500310f01c0283e14060741400503140944103003140304030329005220700903c2c114008103102003c0c0d5107148214080b0300c0200100303140110207814060000e6403810105066050b20030000d400a02843c800014402e0aa0159940c0f00d1950354110040b81d54244007959181006841031a903000720011803288175000b00104035034041030045d10a00350030f03a1161030703244d00051b21880c034403901ca1528680e613036102d04c15002d540780110761040c207506219401a54519141c0514801c1c45103041c069200c082044c0f98101e10564042020711284000c0b000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 262942284 1250 262941034 262941043
    0x21005190605030c090c0c2b0f140a030203100e0a0b09090a030e0904020f090708060307060302040b03070818100605090601022b030f0507032a090905090c03010203010602 75
    0x45128651501001052520b0f011913a80010342d8010025401c45d1205e000e102c4040c0c0c0301c00d003441183c0c03281d0845501c1e00c0305242c0000c8058242e5401d40c070b0605a0701c62014188040c2c05108a04104100c60100311504174031069440d450428503006880e80e89200c920500380781e40b0303000300e844991110308109140e0f456070000e10294005a81c6034440343c880405180c1c1e00c0b030881400a021070b16414030030440d4200030212030b83c810300040c0f0f4400c1010044020030591181a1090000100640100421400e080003002c000b44150300e000c501d0145400001040d40c0001307426a0100b04a8501080d01802201c0c1c007500c110444000b40c401d40e041c0454a40d0081140d44a0140107070801000613403d0b42c000b1a0309221601c13290611142c9440c0c005050301d8255030140e04400385039132034540c10f050115030b107c1d040c8902e00d40e440000f04104112028000c01e000103051120318641c401ca200f191590042c108411100c01403008078080d1900070440d130a00084258554040d80b0100c0000b480581c00039 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 262943534 1250 262942284 262942321
    0x13020705010b0306070c1b0e0708070f02060103080423040e0312010b1306080a090b0403111911040c1b030f110109080403170c060411100512060f01021005 68
    0x100802c15150031505041c0c03101ca04075800c101055072206240003088040da0750942410f5290840440f040d2605104000d2410a580c02030005504400f04001e1070380000e0401c400740180e0005040700d61660740d940745988224004d80b100140603240100c03084000c0d21640000910040081c40002000d01800303030303642c1100000040345100080005603591800089940c4680b42c408902020b07030501d01c0550b000c03400034080c1c42600d0703a241100c80215004c0c42039107000d184252744210074031450703160041c94107075900d5014204100c0f4000300c1d40041c51192030703402560b00954000c0f0b001c00c84800280c803900d050701c0c40c100d00c2c4d040c00207034001050383c0301729512107913904d030b488001d1900804018182201c0c0041d0303005201c03c000b040240045440380c0919005c0490040c5101c3c41e0203240c02c4c0107401c0c1582603800301c800ca070b68203164a00340c1c030b00494112503442d45c503d01607040044200b00184100009440d5038011661098010704503442446510140380c51035400344120304040d6034000242c00f909 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 262944784 1250 262943534 262943543
    0x60130020d0506090709290a0b12060a1410110a0f05030c06071103030c090406030503072105120c07050a080a120c0c0f1713090f0509120403060c030209130207 70
    0x1084c206c0305841031607515180e8030382c61900c180c2c2a903116012602c042a520743c0c0044060000030301140004c0c000c0540c9503045803520841c2c18410240100b444164128904071480d800345803805803211000b0088044891602e09020303141c43c1000c1d030511151842c05821010500b921209000c030010003030080203000811207810780d80d10442245d02085a41100b070030743e00100040b4544c01000c4000d007c0c10400103100161056807603403610314682c03100341c040703030300040a155803091080d0b003440f9450806424180b441c0360548a400c040140200200303804001305000c9603220500000700500c00260303900080c1c107652865a00c42c007401c007001e0b0308244407a031800c140311032180138401c40311848600d50180030140d00d055036070344584941841c0c00c0b54501487e000d02070381c480848040148c1d00200b400c50400511034040c100080103440c4001d1080542d0780c400311a02e036240107408125422660040c50015040c086600100d010388601002903500c200c00034031010000e40998010100c45210b07 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 262946034 1250 262944784 262944793
    0x20c0705010809060711101406040b24031308040e090f0a110906030a05011503020f0d03020c0111070302041e0c1103030a0b0103111317060130020d050609 68
    0x403000112126482202d1005071504000c1c0458415401135186580301d4000c03109494400c1044001d0070101d407210200f80c0c84001c8000c090021604203440344110712841030360610110204801c030441e4041e4078007070b140d10319180003000600003414140320781c7c4074982c0041c111382e45503a1506502901c2e00d06542c0500c80f400303441000940d00300000b580d51400380e4880d20340c98aa002007030411007000c074000d0800342c043c040c18a94400060080c404c041107200802994440e1904500502540d1041044041e024420f0300c15070801180d00060010380c680c0092804c2045d150032285901d041880c00d901c0290860b0400220041c03801807406040b600c4500c1401c00c1040312000541143e641c07012030641503907030300100040b80d0001c4a90f0481e801454042c100410400c401c1c0c2c68604565100c4000240000d201c940240070410800c144800300000150007840254140b18518003005422400c0d00d513040b000041110b0b402c00182c51041019800920301c001c0d91b050b03400c1441c0c541d00101c40c402d10f603019 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 262947284 1250 262946034 262946039
    0x3050105070f1b1e0512041703250c08060405150915040206090102071701060501090e0c12100e07020c03071211040905030c060a020a0905041a1905030a0501020c07 72
    0x1007002c60b03503001d00f100000b07034641d01566216000034801448070f0701c0c04220071628000104034100807010190240710b5880b039440b0b14001c024040c8030b5084281e003809030010000c080e440c22030340305405009198031000f41d00007122860621980b02917035021b01d4a5004a000b040705015010583c031203601d103960015201c0b9691000340036118848007096840c1031074240081405414600c0107001c4000c1e041c01294007035615901c9054100e0000300c8031003210b80d150201400706503030081d0740d10b0003058501070340079484c1403000400e2968060100e003191600300d16000a00d9031140442e980e4000c1609a100c88000d0502c01c0c40203403660701c80d0200c00d009201d1520001103180f402100300100682202d404800903c1034010031000d00081030007501c140c4000c0c0074807500e40a0034042e00f4082d84009800682e540c07595000a854039081d644002d105900d0701c0c00c030501c44c07050040e141350401c804035039500a15940d14200c00403640d0750b8000c5a050b00c520441c00301003010550003000341c18003980403a08041d5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 262948534 1250 262947284 262947287
    0x603071202030303040b06061605071514030112060b0604030b07110705030c060d06050405070c05010e0102091c0309030605010906170a081917070f12050c0f0702010903080403050105070f 82
    0xc06254009401d64002c000190110716448005e075000340b8000c0581d403910520100000041c6a100c1040e41c850f0051034003005081c02e054940c810190b81411710309071600d00250a850b680c001485900c0b614243c0e45001c41c204080e80d406a64840802461240c6841d00d03410160300e5003030225446c41c0442d40c2c246018011020000701e800440710000c0050481420101c144552504003041000340300741c4460010900303683c0c50281c81c0c0701c0c80007582e6503281805141412420340c0c02100020042d03034810403981015458240c923054506107100100d540c1da030390a00e001c5410101c580e101501c40d9180000120b060036540d00003004451003030500d2200081028001910395800e00001441005d04122101d144600c469005107012000e0030700850341408903801d4641c1002c122800c40c009860814050144c5400a68110304844125020801c0e0300d060300c0782c00481c0c800d040c02611384481c0855104210380c81581900041c0d54400c2100ea105c60f0b591500d030340a030030151031050108500c81150b15515 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 262949640 1106 262948534 262948559
    0x50a1b023609012313080a181e09062306040312030903031805060109020f040f0810140408090d06060b0703021c050903060c0d0603050d08060307 64
    0x51913075050140c0207074503141050403c60328810900c50000703191144401c08540c000296581c80d000d000701030b554680950480c196400070b00d00e01081e9080701d0032001c810000f4504008000503160110181568541c0c0140402c00460f0886490030201d50303a200501d41e04040c0040346042d851391035040c10000741c0c101c10f0012a450709299010160b16214500c040418a000000301c1311b40d9944d8152500410b204540000d600400c038444c0459603101242e0007000001500000d2543d240000740e104c41c1025100b001e0b040c5042950702d030441c46000460700c1198801592480e0820550410a2260b4007420960350380b6580c02005c03540d42a02c0c0014900a4042d4004002c03e524221451100c10a000340150030003805002111007034600045680d040903d80d505e050300d40010700c110740d0062006510207400c1c1c1c4695005054a076400c20714103801190194242e1b148540c85d40d0031002c3d074 = true := by decide +kernel

theorem cover : BRFrame.Cov 262769784 262949640 := by
  have h0 := BRFrame.cov_init 262769784
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262769784 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 262769784 ≤ n) (h2 : n < 262949640) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
