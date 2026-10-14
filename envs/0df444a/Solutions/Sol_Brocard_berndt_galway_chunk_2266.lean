-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2266
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:11:12.331852+00:00
-- url     : https://prove2.me/submissions/eefa6a88-2cbe-48df-901d-45262c43b5f3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 407374100 ≤ n < 407553956 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 407375350 1250 407374100 407374127
    0x1020403080712020309180a0c020105161808010e0102030a0606020c090118060306090c1a04080d081801020c0703200102030f16290f040f12020304050312090a060503010501 76
    0x507203d441900e80034800c20544400510041c818644d15088544c2601000d50507a000c018160034105034007891801400340c06c0c0140c000e801c0300e501d13140507003a084030704203030300d2520000440e1410800240c0040034001e0340801c0e0f102c0300006a80e420502461002c03034032503501200c1950001d03050740101d6507812a84c181161031070605000c11407410b002100007042680c100805180c44c091035042481040e0904800f6906000a62001c5a00c0803103903585030f000b103200b121a168070084800b404284a02541900055a6154004400c5c2c1d07018070079080e600826050801540400c0d82001485907600e094a40f40722200300c150034400103040001e48a00c910700010803070b0040020344203800c2c0c0b141170b10900f00b15042812007040d180c46000201640d0f01c008031100e0921600e20104a8080440e1800303401154801445016680d0559170840a2252400e8460560005010004903a02c041c0101d400328400350100c7c56503048400108096080a40c200004000c402d000600880c0d801075044a46035 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 407376600 1250 407375350 407375363
    0x70e0102032a0d020f0c01032c010b090411100302031501030504050f060f1008070e0103150e01050c0c070806010b0304170904060e010302120a0b18010e190b0702010204030807 77
    0x2c03070704940301150024a6014001a20400d5003001200350b0108a108100b40790006640104440a00440648a030701c0000c0c405540514840e4a04500501003100c40ca204440040381812a2000280303140b141181c040d80e141612030040007c03071520689084d80d0288505046045003000c5014414004140d030400f8117040d0b5503004542404803c0080700070460028044500702d14102c0c59a075034581d0700750b40a6040100000307000c25418800304165058507205c0349440841e80c42d68980d01a08034080c036000c90b209540340f040b124454001c2c0542032052102c1c0718002d0361040d0f0081d0051914006030302c501c00c290020401403000c51401400c6a170003c0d0000025070096209a851401d5442161402c80d440362400c000040c10140381140c0c541224000c48a545403500441c859079250f0b01c48040c0204407082d0080000c004220000c0c10018a00b100e100014001031aa0950f91502c0d03285200b0030b0007802801650402c100c000450380d50720036003510080d0708061441d0b8815009000d20280141203 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 407377850 1250 407376600 407376637
    0x305220201020a170a1101060503101e05010602060601140316080601110d090306060905130219030818040b12070e0c16030c060b0a0b03060405250f0206070e010203 72
    0x5580c400c0150100440d0440580c00000f0140f0000e0f100c00d900c108001001b00e070051070300c0100c410703040c8111f074202c84014011b80b01d0554950300b072100804000c1e0b001101007004040d4510403c206209540c060300c0c047d0014000c6040c00c8002500524110ac21415841410030400c2090003c81c040280c0f1010141010b004c15128040140c807140070340c5007610213611881c141180c030254010380b03d10483c0c3c0141020800701e911204d451040c0c0da0b0441d00444450010000b80005040540d552000700c040402c00801d4241c4941e6405007030b9000301c0320581c048501e404202c0b000e18140c41103005070b090881e10315401c070305400d04050b21110148a1040459600310020b646021140b08440344955124204401c0c4495880c02509040350040e0943d00303246800400744542c24940000420785007a6114603096684007801c000c0588001001c08101001c202600c0c2d0b10038616032001c2d0b0400c5100c3e10750506144003100c00916240c0c0040c48c4e0f90400240304056840c3d0798022049989454031000040c04 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 407379100 1250 407377850 407377853
    0xe010209032401050105032203090f0807050f06090901060f0309060c020609070f060e19120b0a0f060b19020a050f1006290705070e0a1a01030522 64
    0x900400c054140c060049841d02e50141003000c03101c220140500c080c0c101d0607622100110b07a0b034002121444c036542d07a501c51000440c5100c60150f04030510a19018aa40c0d40740c82d002c2c05980034550000110354890501030000b46040b0301071800202055890314202901003000501007541842400c0a003c40482c2d07040040d882070300018407207500b120080c049400520700017566500c0c1110a004a80500720000ca00300c0c000d01512070881d01c0d513035900f41e0380c02403a0f020000c80850450302a00300004544000980185008101d00d1490082d20340d010b461a080d404075060700c61044143e100280b5003041403003508000e0042d2030740c04c140503c2e080144294004140d1400d151400c002e040d030b104c2c02101349542ea40000300b58116200070070081c4940355803a03c0c1040c2c8040050740754140050528500000750b621900505a5980204101c49400b540c900110302c81000688176800074030b44a1903603542081180d80b2074040c51000f0f190801c20b501c3c0010310003c0c014001c0d2840308400f000d400c138800 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 407380350 1250 407379100 407379103
    0x260c0c0607050303040b04082101060807170c0a0c0b010807082404060f0e0114060a06031406010c0312020f040603111e09130222060801120b060409050d0804051207020307090e 77
    0x408896461440c40d0001002704850106034000b441800f001503030040015581c0b078820380d080640304180351203916158442d030381020070940100c0c090800308010b240c0020085018100f06500a041c030b8800341c02d8072030a002880e8246a2035031400076a03040d200d4800f16001404468890340030390000390008020204451902c041c3c100e60f03122142540c02c010b8030031000d50048000d1030207000e0440b0680ca80740e41d1800c00b41c041d26401c001400b404080980000e00550080c88d810008038800e103030034030040540b102e15508980105c12000321104c0041020b00c01d8980500c220b402c40030000060b203042c4076000f26a410520010102280da001c00480ca18440307841e212040a50042e03c07031019500e40c0c0c208046143c030f121780b1450140300002042c60006076280151302c0c2c00d06807440950200903091581d00d07912218100641030680150340c9000300b1010940600c08c2100d1116290703520317070080c142414860325100e01c02d4241d8408000c20000c0e4001640d00141d05802c0b126601401310352101240c1809 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 407381600 1250 407380350 407380357
    0x13050c090c0a0e12100b0901080111040506030a0603020a0e040303140c0d0f020f0d1a1002280f080307020f0304300c0b2d03060409260c0c0607050303040b0408 70
    0x107900b0b4030072135075480d041e0001ea80140803802c6d41903c0203030a9aa8601c00b29090b94201034100c00510000c00080c00a800d00500171544a44488808258071390741c0e902003481c0c180103a100c8a0001c0c0140c043c00100f6905d4024a081071b001420724900c079052115240b1201e100ea070700003950041d41c50840070303002151a01902c5242d0000e181c90703900e41c3c007c441d040003d00780f144102034100b075420701c89009900d031030704005090203c0c0d40d000704084034810792525544600010f8140749440d141c0e081100251414003480c10b1036220701c03070064603418200406880c2422401402c0141e0300148010300c0244844103a1040c8e0710103100c844400140e02d101c0b0468113002c0c1c0540908050074030003003c154680c10708010101200b5103841841ca9903d402c0c0103c203140c040300d0400c91103507000c2020036500d16164100a00302ca0245404e44d00314462803100d5100342c05010061152890040740d41d940200d400c0c07011162207030041d03503200d2078524903680e483c1d281d1000502c0103000480c101b0120b018020f00c801a03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 407382850 1250 407381600 407381629
    0x50f1b09220605040b060a0509011206030b0c21041124040803120c090a1203032d060803042414070303020715021e0903100513050c090c0a0e 62
    0x201c00000301004401c00c080c04241c0200350245003403040c0744525050510490344480700981e602070502d000d4800442c0c00d5800d1a646180b420b84035600400441d003a80342860081104801c041ea603030310062021200710941180620500300c8241c10040410141d81c0403281c0780c2d404540964404c1c820041c1c081004851100761202d05802190201d40b000b400001040d403007440c9460140380d030ba15600302048511900c0401500481700c00030400c4500540080d620500d4400e003004070b0a11040810782030154000d1a900618020040820321024035520401000e048184040d600e082c3c02d01c4100802c4203035103c3e4031525040728800640c200c5201e00c04101541c510b1050055488900d0300b07000340650803081e002d8840780041f20881c03610603030740e101701c40d01020f024215801561300d0400d60000b42c1c02401c0c00581600504041035500441442414869011450004604206030900d04d14020414403ca4000c00c000b100740424000301c602660000000fa10703012646062140202c1d140d4145802c8 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 407384100 1250 407382850 407382889
    0x1a0f010e0f0c0c0312101d01120f021503100f080d02030f0c01091403040806060d11090406060504020705060906010e04050a0b0606120a0c030f0c05040b07020a1502060a050f1b09 78
    0x180030f06c991015803100d0890b54607440e8201d41c08550246410b69031001c4c41000200b2031440c941c0000540101d50611038503000410700342c03101c03055880d80940307544200c504805620300340400307200d0000c290420301d0143c40c03000001d000540403410065030703034454143c0d601500d0304080ba45081c440e0094002c120f400798080c15881c030006220940c0380d50f0b40c1180c0034410301d0740100b00000e01b084c20300301046014960001e0030081c2d2540382009000b05110081c00540d10039483c1c180109494495000410b40303503104200414251800d60a0b843c103121040c0c100c0c5400d000c0d00c01c10f0202050001581c6104207410a1802c6500e0b25403400040e401d00c1a2020801d81c02e088500b00700300036034160f002c16a14103150311700784005080c4042140440f0124845103010400a020500c4411400405450713601c0c07026000842da9034071070152004480c0340040c41d60060744070008000c42c035a8a0300419070030000c41000d1040c142861044080001d030407811f04030b013041002c2440401582c8000c05813602088055 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 407385350 1250 407384100 407384137
    0x20f040c02030a11060c1603090503031603020609120316020a020d0311011404020a06032d0507090b04150302070f0c060e0f060f0306010c030c1a0f010e0f0c0c03 71
    0x182d10b0750071240f041008542c00c0014402e54500109a6a1049802e04032442c580791028546020050b600700d4145d0400c848800041200d8508100902c1100003c6008031840762091400910f031086c0141201425000b400c05808002030b000180da40040e414051040c1341c81040381d0403454444052400395100030101691024183c0141c00c220340180014000e00401c0c8040240300d010748000d84c1d0080d04601080b0042003101c1c469480394030003240c010442d00500060121808120301d80507504503400748e40f40d040c0300a49421484160003011480201804d0600e40718040110280c54a4000d052640000d5044104424951001c1c48240e10965881d486078681c5001061044050843c50040d01d01106c91403c1740307003a0080eaa0040e00d484652443c60362407600446141c510700c4030860510031b6000e524000039001d5804403a010304000e0410596140100070140c00903c182d00012525441c1424489204005e43d1029480b00c04040548d50300c0e51035104540c903510031f4101c024140318012 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 407386600 1250 407385350 407385371
    0xc080f0306040507030e1002030a060e0f10050102070b3415060b07020904020d0f0f060209150a121508010606050706050f011212090e0a0e0f06061804020f04 69
    0x164040e41c0252800c0e6020000b0b6078540a0503400c80ea8070320840b5055074410811039030783c4400c07030f001541d11401042010459a60b10701004e88540010b56003125078103c92000c0141949400f201c2a008180074802011580d14005a48045102c1d80800203160917030386005082656200b070b8100380740c1d000386880081ca5000b078100380b08001d10000d07030352041c00c2c01c0040005400811002ba03500c1990014010744440d1a02e908008103041c6108003280c51815501c61758001c144082d198006440c05a4000b6960310107041c20800381004286408812500520142e50310641c00380c02603107002c1d4824000209084280e621002d4074140780e00089041d0308115010580d194482d0192100521400c014001c82c0c5803c82d241080079024042c07040b81a02112030380c40814410004000201054104007902076107400a091401d2002c40d4442480790321500840d10f1241d00700181d10b550201c16000c1c0107507080c203100042c4e04c805600c4451140e202c45901280c255030741c442009175811070040c010828502172 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 407387850 1250 407386600 407386627
    0x100b0c0d030608010c0e091012030215130b040809030a06150302041a0f06030a290f310605030106030b041703040308010306090302010e0a0809100509030a120c08 71
    0xc14602000a0409030005030f40c10741405a40d00f44860fa40b0741032402c640c0d64040c490744d194000c0400d000d19510800026101e0b140444102070710380241e0241200301c607001642d05c94100b01416400d0116001d000303038000300b18007690b4150844c3d80428280d03a160075102c0001d00e000d24094014200500d080002801220025280c008481c800d40f820700034020882e0000d981c00c5111500c4640102c800843c10b03825250800043d03a0004886100050b0008440b49404a0b00c00c00909030404012800e4220268500760301c44084001d422504100c003452010024a0344c5219101c100843c4a02a500300c81c10f643d554100e1806000c1c054000c201c0c01c0c0d6a420482c54184059a0945180b80a00d400c410f0544401e022a442650580c6402c4541d900e1035443c1401810a030b9010b5017155641c000418003401e05204d8040810700820189844040c99001c001c400344081c0362280030303c031040010030f40300d03140490100d5203250004400035501450400c1903070030010341d00004050301000120740924001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 407389100 1250 407387850 407387863
    0xa032f0d090515161b12080601171e01140d060c090b0c0c1c0b010e0408040503010207030c02100e0f09040201020f030d0203100506040501020a060e0313031a10030b0c03100b0c 77
    0xd55550204103c90b42152140c0c5c0050703044041d0041c280c1d18858142c55004c2e420391508480103241c00301d14140c0400840c007881109030790403088214405058403680c4800d200b000d002d050801c860003120818900001c0c84441101c000401007030300c6040e10840307a4041c2907501c0003803807042c05041e07a400020001c1034949020042551082002c2011a51003444552207060141e90013030218036541d082881040d44014003c00848a10404010104a9840c00e001806201e0f120303403600c1544008500c10040210341d0812068104003005258480554401100d880540010f072400d41e0f00d500c690004074108040410002d80510002900280e40c090b1640214072810f01c03826442180343d01d40003048002d210f648a4103005903c00c8164030046032040d4488240a07440c203080f2807030245a103074034665280d901c0e030065541140b03001c07070b00c204a807004e0301c07103940b118018282c50042e50542e0b96990701203602038840d801c50f01001c40003a5642c1e0403240b0b5203024002c034150301521465100c06050341c0b5407 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 407390350 1250 407389100 407389141
    0x311011a120a0c0b0c0c0d03120c031505040207060e010c0809070902030712181e1106190f02071d010303030e0f0303150609060a032f0d090515 63
    0x9454031403003030401c1d0340032522040d442e5005106400300c61030224005050b400480c0070441c940694032458030185c0e1280e86250495109440d40f040011848125500700d82c50064240103040c2002e40114542156405000c01c1c8c0b48110740068680d16107090000003069901d140350368540c40c100c0c101c41169040409144661207800895042075164003000040e8001621103201047c1403004c50b172502d0010f6006414441c0100002d4810101d841e155101c2c8031000101100e42c6040b407028000c148004070075040c107a60810355802d4034090244003464039200003803480c2d04c100100d41c445500814424041d00008042070004410f0401c5031400e4501c51040a20048020034a131189014105001250a0002c2c4e020000958150340c2c501070303807801078002d044007983e20240030031180c400d680d0b51101800700c041c10341e540024420410754404011301c0c400c0000f1240011025184e07050000c2010031220030801612000c03c45520703034a4100d1411041e26045c1c2c03481c2007001c3c20000100c42180114400380d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 407391600 1250 407390350 407390359
    0x109050f0a0207080a080903190305060a0909051513060501060306140102060f07080c0f030a1506090e0601230c0c031c0504150207051507021504060804020d0311011a 73
    0x1611500303040000c911a03403c00a000901c14001103101902074840c49600ca0342100a80e4a009900b404d0a038001c0000300180d40403a984409002081c241491440042c0544880070404c141c42610f915954821810400c02020f041000280c004210030720240c0c1095071105092046584030351015000c0c00351030040c0080c9951032104851951710000302c9034042d02c10340c0481240780d1103140b01204d20301c1d00281124514042003140b04003104884008501c0340c0c400d241300080800036401c0e16104482e455001d501040034400003400340c4158461459040f010900300038280b181080014840b0582e90420761500300c10100f100c6501d068089425180b44034103d0555511b045c1c07185040c4034440c8070441c0c4100251f400d2105111040741c000100b190000c1c0b41c01241c5041d0743d18400074114480e085d0150b1040d2102042c44c1045040805204c682600321603582820541400c1f4024440da44c010000b80c4070780ca18a07030301c409050203002284040e0049800078007803c042c0b0007401d0307021401c03448490f016 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 407392850 1250 407391600 407391631
    0x60507141b010b0d0f0c0b040b030c0304050c0402040b0a0e030708150604180f0605010b1206040c1e0c020306090106030f0807170a0305070e100f0c030302070803010905 74
    0x152446000900301400640c0d0180303092450105054424003030036203140309190359400e020030709952281d845035030040c40b4009a0110366414038181c0f8482c28150320503682002c00344024080814000280ca600841d0728031000d4a9a0b241d0034214540f18604010580081c4001008610005000000e0903060311544482028a03400c0041c555241018401d00d986600003e016070901015800d1030b0ba00820000c001161906070301d0014041d01c0c2141c8003c030b44690000a40301d0401141e8040e2600400b000c0030304138140f0025800e503c250000080016202b250b85016501d1a10302030381c4524450b41c198140030581162034800507100c038000302070030b074801d108120025200520501030102940d038856442558080195031b10a0150403140c4119095a40d219440d040f0580c8000901290b41150398049114104141e0141c007101600d0902c03805034400c148003024141d00075250541c100003074038110184400604041b4000e0103048401400d817000040001088030301908000d0181c0122281751b40d0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 407394100 1250 407392850 407392861
    0x5060109060806130b040f0507110a030c030c0212010606200109020a0506460206060901050907030b0901030f0c080304140d0807020d0606030c1509211e0605 69
    0x1440d6006210700e80004400800040c01c40c280420505903040d419540400d450742c1c450001000d5612041054403c55a00c1c810000825445940700d02c20009400107801074848985000340304c60801c040140500c0642080c11045450b00c89140c0003000a2070003c10950f500c40600820800c0012603429039101e080441030b6400106216501c48030368000c0188100e6480d14007071001503081030509042c0d1030340c0c1221080450b01d0602c10b4032656400d204841e050b025400c00f8602c20390304004050411548500d04001081d10b03500c80c0b0a0560794201e68071107587d074070503030100e02500525461070b4000901c400000100110005104078040c81002204074094036a030709181d0b87d001c1c0d807044800c0003107241d5050280d4109490100d2509005024642c50f00006802080116268100485000d0740e141410414442d490000c1c0024160258640025a00c801402030500801d802100071118091200103601c003d601211200543d0290b0740b50300803141d00000c100c40708220942542c510741044001103 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 407395350 1250 407394100 407394107
    0x606190e0f060c072303031602190302010e04050603030c011e111903110d0501170c0306190b1c080a02190206070b071403090714041401170a0602040e0a050601 70
    0x40580701200d0081800500c0d088051a0b201c6911540c0c170040c480002d1448003684040c401041c20381500800b500900f401c901c14040151303440401d1186414030500107000603a804050040441003c42d800703e10b039280c80000a003144149044416650300c0d2008602c104514110018013690012004000f0404882c000b540c89201e0240a18485000060580a96030207603000560410368150240c0c1410988100742040b07450a03041005040005041100780f00c1c4c081041e1101e555082d030142c031960410104c000040f200741d40481041c180c4500c00ca5285485018005001c40d021480b0381035000700034100750034580d020b8046000140200801654050311644030320000035409400c071450022147c1b07681d079014501038581e2003013201c0d511006a607800002c0c00b940c0169428000342c08081e24008c40d2081901c001e081090280d42051060241e43c11092181411a1990f03104041c00c014106040c6060131106507005090074408100400d15410700c54103a886001c1070b4200700180c1d1039400064 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 407396600 1250 407395350 407395357
    0xc140d14092a1c140328090303022e09060c080703060b0304020d03170103060606030c02061306050601050c0303070c1406090a170d110706060e010b040308030606190e0f06 75
    0x200d41044080415221246480380e02c0d010460040409404c480e800c00300c1c05007141d0101501180c1c008602004228814511014848a0000e820002c1c2d90b145107a030040d441b002114885101c8441c0c81c110034802c984a43d0b0400919118400c0c20840da014a00e445001003404449080c0001e080000141d5454020f11510003580d816070b040ca800c41e6100d500700014031400250031010005241540700d001804031000b14061403080030007003121800c0000090442c0c8039201c0c44021544100c2c2888110040160103006440e00140003042c0b6a48d05801a43d151256410848961200100b002101c603402000301613240c1c4158045035444a2803080e070340c0d9500094420640a400c402a5040041c120112000b26075403400001c80c20606241c5001c8201e9420303441c02008000d00080740c004004040c0703e0311001c0c00d96010f20500a504000420316180503502004280890000110b6178542e215003d90b0812000b4914210703a40080c03c0000302a401d00300c10303440c01485d21003817043c8a481c1c40f82c00d4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 407397850 1250 407396600 407396683
    0xf050c010219180e161101050907180204060e0409141203091e030306011d0a060221030c04030f061808070c051e0409140a030503090c0102010c140d1409 67
    0x15101d50340c1710b07001c514400141c030240d990f00f40038050380c46980b805400c0c0207092003100c07044041c7c42481e180460203802e07029000311a000951040005000050f084a200c07100080d041c2c2d4006100328940c540001b04154003941a40d161180003005280c20140c08011849940080180d400d0180c842c160101c00d21030b10311111120707030010b000240d07265108000c89a0b12020591280c01001d0303125000c1a104010358002c100140c200b001500d5881400d6500400080e192001c2c542c590f20300482c00b201c40f40500e000c01003030004140f201409110705500710441711005200300c12018a050314245020764820407003110740202e80075000444d4641704900400d074203401000c0c5007203034001c02d08010080400c0401299206030f6981e082c4a40d00d41000101c407414401c0d241d00d86d40e0b0600e540040c0c43d003039a51030a10b045a04104000402d03a600c540c17400110032550801a444031614146170000c0c1410501041d100c10a4804000e40c03a10b0004d0b44131110906c20160080c0c088140f458428040d0980c01e0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 407399100 1250 407397850 407397869
    0x906180f15060e0a0504062c060901030308070215101d070e0d05210c070e0106020a14030c0d351308070c03050705151201060f050c01021918 62
    0x1000c11002c1d01503911083e042038002d00b880106500c0b94001001c85105402000d91103e203070700d01000034081203128480d62585440001a5490010006003030444140801402c0000c1400400c001a0081204240c001d01c45101d1209910700541d010034001e11038803501013038800104400040703c040c981c1c403a010343c4599540024042c40101401290000751000305c403503128001c01504824006c00e421569040544811a0307070b212240c84162400100750802c650f073b40c280e000108110f540004010b846247e210201c103403030281c441411420743c0103000300d25105000d08000080d10a6218034480c2c0140f84102013091008005900b140006000201c0000d0645608010030b42d0905106c1c05010410312070003210349040a03e581e03103500000345520894640d40f002e04207110b245409008030028001d502e0446062403e032214120b41c03001d041c4140d80620400c6008101e030700f8032440448240001c90302c025541c03080a81042165a086002030000043c1da44011642d842c140800000880700c035442c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 407400350 1250 407399100 407399141
    0x3071a091b0105070204110409050601020d051603030923010e03040503030912010b13020403020a2103110c12100507030606090303050a05041508090f010c02070e100906180f 76
    0x42101c60315401d10300c0c841c107108050004400682d1107019028003580c3ea84109911945410000b40a03900c0c00f605540c10b6402200d4104c2d003156000050711b00288890080032010380c031904041d001440c62036001380041000a102003180c00100701d03401804108074001308800100006599180d000d103014060380340e08200700ca00103d240c00710783c412647d103414000007010034841000a400700c070356111021140d50041410025890301100c11002428946500d09071043c40c00aa050403a031a01c0300103042c03200350303806654040810444400340304000350051001c2d9071500c000e140c0d5240081c030f84d80c80d030034148000a545540720b406818225907070750b01d540c000e0f0340c1940d40940381e03600b10b0940401004400d01c40080d440d01225185ca28240c4262568030740b50801201e0781e4200002007207902c0c0390b0b0381081c803110b180341c2c0c2c0010321204a4500130004080c1d6103c003c1e0204440c809580203400702424080040340b004002c81280c078025465807020407864200182c07040c10b54201602022125510700c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 407401600 1250 407400350 407400373
    0x120e1c0212070e01031a0603010b010e221e060b12070f0e150408010c031103010506090d0209150a06081b030408121f0909080a18030c030503071a09 65
    0x190314a58404503040c003507524483d20341800401c1084268802e80d0004592808140d504400000e5180c0101007034001f07102c0f00d00000000303481c0c0c0c0f48000886000700940701c960401a03120303c5409030711103403018040c002104030022034040400b101e02e050010030700d410400504008204215600304541030101200b80e50740900503144000280300e0301d005c0c45121905801180c0d036603004400c844045468542e1518200f030fa806e400c54400030300500c14035192189600c00f03020140152411618102c50f5035540d0000c607000300d80010540c01c1c000b5001a26882800000714241c1c40e40c0e0443d000507100d030300d00c0a9070346030122281401501c030801c1442030110300c004814000c4e4029035000740542030300b51800407240c42d1600039a02c21116001007645800c3c00130003003013903202c90000510109000b400301400e00c0d10780300000d02c2007008040c24092107040311045801c14032038440042da0800000e000c00c90303690502c0c070344a5100940c12285003100745052440819189138090140c10307448024180746015 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 407402850 1250 407401600 407401609
    0x70b0c03040203160303030f0b040c090512010b090907050405061008040b0606190e0103060504154103060609010e070e031015090b0102030a120203040804050d120e1c02 74
    0x5081a0303011300400e40a25690080703203c5401c0118420380c0c0019004603140e100004481c0702e400ea41d0301c214140901c0c07401c034a80c40407882065030011240122580a050705040c010004849456002034983c0200644101d01013075480072210103527420300c04d80d51040d040103850300c040b00149020411000c0400d02284a800c0d140f6407090024000510f008d249034603120000c005902e8080005140982607031465038940920801400c082d1812701000d500ea014050003503800303010780e40446a8641c1235070008020f0319550000c0e00301c0030021850301c0032040c0c102c808a60a500c100ca00034440d16000c05c1c42803c152030070604032440356030064001d440e210307800c0390030301102403610b40d0610440328001c0600b0264032881380418600c50500c1d6410780751269107415264034502c00c1d070641d04140042c50000380c0200303545150319820440180d483d503892904000b94099600202d170040042c0c0b9855040044903000310590a400d03858900e00c1d103440303200304440c20083c0e0488a000c600f001c4103082c0107040c0b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 407404100 1250 407402850 407402857
    0x1060902190e090f10030209090a1a1603020c0a0212070609050d0b0a1a06032811040501080a0e1006171618020405040903020705011107050a06052803050901060b070b0c 74
    0x30172010802089a40e5000143d03010000c0e01c040425401c420405420810000c051400b0100340180398012440e118a100c0702c1c5000c505000410b241d000109148140c205002100f43c95600401c0c4000c44544c078200550350b810385000c0d000c041641c546000c5000e1400390310300c9070340302c0c0e00194041c060780d1031540400c06070071898283c141004031455850070603590364000c1d600c2810100c6a1a241c084030311030f0080407034400c814200c2d00031302d80281e4410704000d00049405440d420300700143c8035215a81540010840001e070005540125041003502c180301d90845021542c82d0b03c4494906d4202c0305485444011b07066520101c100c00807402c020440c0c008603810340803191840018200380c0c0c1ca4000c0350030366150780c1d8120300507007044c0000c2c84203607000509403c3d00c40c1560014103840e0b0504000c5221045240940b1041c03110110f2104025018503400f0307452407864032020301400e041c3c800040d000e03201c243c0300811a0750030650041013036403490081d2268143c0040100031151601c02c01084584d1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 407405350 1250 407404100 407404111
    0x307021516031116081306050c03030f060d060608011407020c0108071220090301230426120907060c02061617040303020a02010f0e0303030f071101060902190e090f 72
    0x1601809003aa98081e48014403013034a019403000d03903444c02c001200310300240b05900044180311042c0801c44084a002050302c0c0d0001c0e140061200301d40b640e0001803a0505080d00003810f65080907008600d030704041d0090781c0f042c01c4040503405285c8521070240c0e1034000345507a080c005800c200010b0056881900b80f0010b103a0507a100040400700c2c100c03070344490000d02104460302840051341303d9503820b007486078a824504500c0c2c5000044211010081401c1c400751018001840036074822100c0340c5d5803840303084103807110000281d48072010f000c0c812019000302d588184d070b4041c0d0749000509500466a003400d440e801440705107411140403070100000c0701070ba0103842030461040c8090300900600000c1c00650700a80050261009030b20006100d0542d8149003800c105501d6101000ca440000980760061411640c00c00f141d0380e0f040d001c40b400061701240c50b5803903080072800074920049500600c0004044102c600034003000c01400d07541c3e050f1800c90035400917501800118120036450702d071504003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 407406600 1250 407405350 407405381
    0x601030b100909060e1e1008030d0501030b070311120615031509070305070e1201060504020715050903091c06142811042715081603080d020c0705030a0305030702151603 74
    0x440c8c0310101680303503801100340040c00c41d40e100011f0051142c5107414640c04111840e060101c0ca0380c000301c04096000302c0303600c4420b081c0c103400426211703a100340c0c03100c004805039214140c6914005c0c4440e8008940c010041e0f000c0c039007450114580911a001c1c207481255185c03141c0601e45620000d200100d03401d00b411030683d541c0d40202295590b50743c001042c5840c019407483d03031042214034200080300d00190280c0e4166000b0070600e0701d140c0760307905080b0085245084c0d22001085a081a0f4090800e01400d40b41d00e001e000200810001c040070740380080c4203801015139080265200003c2103c405900b8a1800c81d000c3c0700400c404d1000c6114044105c042c0b00710a075450000e4148001a58588400551070401d511001d001d000c8042001d166007001030351342114000d1442d1507411a42c03107903480034010789070001110b0b4000002044044010400601100c642e24036030700300100aa04142ca00b680140500c1c4820f44c2058841c40810780214505100c00500004d0f0329400e40040a0500907500c40 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 407407850 1250 407406600 407406631
    0x8090f0105070b09010b011803020f0103050c070f050304170a0b130507030b190b010804020f01031a0604080d110f071e05040e070602060c070f06050601030b100909060e1e 75
    0x28041071074003400b4040130400410155860310000d8402011389001040c12020360b20100050303075560301c0a8003050402c0c01c00080644507011032000500c0b6104016016401c0d446413238003001000030042048800c98001191491000a003c60b1500e44940001d0003940307881e00407a840712005030002c0c4180d0310410480d5080b07943e980d6481404078044422400c00c2e02540e4044584050502800042c2c10007480c0243c2c503441c2c903900182e1410000d14500d4109550b42c000104e401240c8500815200c8004003210f4485a9659080c0e540344410344195000030f40e58046081d8a210006a0450200e4030001a02415040c402250802a8800c1c860307000c21208d4000001d15807501c1c0728070800506030002400c4110308052000e071070041e004d03110080340802008501c010031400d420340405181d001e400800d640d10f4a80040340038240203445a940155024400d21107650048208401c41d0f010300401d02400395200168990f5a000716600e040350a920300d0007098041d541d4606540c4004c025031100e11 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 407409100 1250 407407850 407407853
    0x50d051e0a2715030606080f10050a032004020a120b0402040e01060206070f020d0c080c07080105010f300b1b0a020304091d0c0d030c0807151808090f010507 69
    0xe03a0349480c110101e49140018003d102c02200b40d21640c0042e42001d01c001c0e4a44940108070b40701c0240740d244100b030807201041a200c00b0000e50320062a00418030391007142c40c2c0c2000100c145924100540002e181c0350807040c00d080c28000c2c0c813200032540d190080d052000d40c3c01d840142c0224461036030701541c20000854a00007000402d80603202c03503401000d483c50410f0005d0265007051b69081c055500010130b094009901400c08141c0d43d078401f8140d42c803102c0c2420303064504281d81d0800d8032035501b000004500480b4914825080b0b40881c0450858180007019540707400d10182c40ca00030341456102900d0110f1744041c5682c0e00804245041a054941e803c0b240c0445d41180c141c41005810000702041400c029016401803c2c10095140b0028900d51560b2969281581c54a6003e501540006010715000315480c04040e900301c0ea500e541c030b40c050300e40380012400560502d41c550b0720701a00c9580121030030100e0028079038004001031400c240d00301000f8000c0c080e004403d0420008005810 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 407410350 1250 407409100 407409137
    0x3030c0602070b0408040602060603060907181e05091203040f060b1314180105060d060905100e0c1e01080604110d09050105070908060c04140f0616050d051e0a 70
    0x130301c41d070300492069450b6030030a031001b03091800260140d40309074000340920040b0381011400504480100c2c110110074201c171104ca20203000c100404d10010f40c0e440c1c041034003c05058016a22a81003038043d500280059650103210380029a80600b403e0a80040500000c00607403001c140220018410031171804050302d20f10a0b14051180c0d100c08900000900000d01d043d01d00c5180c0008140c0024061460001c01241d400402d41e000641880d232249040014004140407c0d0200501c082d818020030245013403035075a13241c0c0320b403e19000e082001e50010070440802c0c3c4100c00184140e44111a94071002d0800010f40080d070b0444190400820160100c0b620340d10840754014414000420180381c41c034005020140c02d64003603601600701c0c1e4100305d5001d0070f0742c00312400d0b1003102c0550103280b04100003140d02100200000c45d0021000903907900c400c2680407101e44034610440844010303062b0017408903020300549240351000c034490410755120301d14020203041c0540607850203d030400c24020301031 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 407411600 1250 407410350 407410373
    0xb03070525030e011b1115070c14030d050a0203190216030b06030f060408030412020a140303040b09070f060c020310020313050c010f0509090403170c22050a03030c060207 75
    0x202c0110f04000100d005030b5030030150341d03032185283d0800360707030350410079142c3c40f005094141c3d18520075069035010f80c40e00886542544d1016030041d80d0b4140710340e1075400c4c0100581ca4800301c2e9200f80b1410704140650740c414000c5608031000c40e1301841c1442e4010602c580c8a03801103058005500802500301c1c128400300200340025406000c00c0d090b682405810f0505041c04074282070101c0e00082e04002c0440e142500b00c0350015481072840184420084003241041007000c001000704505005042c00d52000001440c05640030347d034444a03548400720b800741d03034044a01c038001c12010480000c0081d5070080e1294a5441d001500740c500034030180f103588040381e00c2201c010ba03690841350990000d001c01005000d007041000e00380f0311750000c80203401070024064503021510401c0d180d800942010300c5807130080c0301b4070200d82c12400709040414000307030541c10440e175a440110124551400c500d01195a003002c4035005025180103d0641d1000c17a00c2544400c805e8802ea0b40812407000040d02c9540e0703c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 407412850 1250 407411600 407411603
    0x151b08042102031e07030e06250b040b06040e3a0519020c130b040f090c15020606061b1609091109060a05010e131505010f08010b03070525 61
    0xa980d68030060004032040c81000340c1e801c1c801140078030030480081e4200c00540140321302140c0b2140c9440720703009c02c403242421600c0444140b08030540ca5100700020801605c3c042c3d0b1140142507440c0d91400c0a01c8220382c180ca000f0001948081000800903549040800c42d4209143d041940800300d880140210200070010000003280014004e01035900c01001d01c003030300a0780c07001d042412000c1c000250382419200e081e00b40c80c0d9039200d0000700f03680c4a0340662201d507d00d450500500141e4140305059010912441038001d07150101440c040d480481e000b4030889005203114113040c2105030801111840030300700015441090b10b404410741b159141c0b50300512429102090b0341c000380ca0f2910211800c1080c1324021150780d01400019500c850710301d003d0341c0d403c0ca0040ca01c0b004043c00038041d039140b4211b03c00034618004c0740c131a241841c2080b40c0182c490a03240e1080c1d501000764211488034091040e00030500084c000300380b0311845a801810b0280265519000390116050040002c0202c17000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 407414100 1250 407412850 407412853
    0x212060a050903031302040b010c050105100f05010e0d0f03020c0919110307020a02190f03060b040b01050a350c0c0d050c0703081c11030103151b08042102 68
    0xc00610684901401c2d0740010b40201540c11030901800648554101d01d0000b1f2090b41c5804807891964481c804481d00305070040c1c000c1c00542400d4000001440c56805420303003807505184041030b00d5000d454400fa60358000b400f0450307000d0458a68258080441c0310840440c0140050705070a41d81d480c0b1034030b000322481c8044240080b00100b003d4111a0b088106d900e069000384104a555070f0085072001030f194040e80c1085110000e001c0c2800611115005408042404100801030020039840a114400103403801c00038445c1000054a10303000d031802440006000585181d00c40250081054013032100505198000100d400c5403100790404940280c150a00400d001c074520b00108600b58006100b4203110b407401e903500262a0701d50b0700501000c2e00d400000100740380301c111125619005203800780700c20480b10f801d19031404420b030310030700c0259860180b01501d0381a000b90751103003990300490f208120100d10b800d1601617440540082054500c00c058030000d42c0b8200c40210b040502c0040b40c0d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 407415350 1250 407414100 407414113
    0x1203040510050f060a27180302011401030f020d03030612030c060c1806180302030706050307120513141f060f06050336031201170c01080a0e0a0212 65
    0xa00c1421114010120f88101410030244500c03612000f0f200c0050780c03100d00c1a65440c0d54502a01e50b402d90482c5070405541d450010300b40b4160300d4118640d61030f2803003a0300a00141c00ca125445001c05820701018101c0030340c1c40703504801481c0100d2290741c080d1107400e000c034101d540c881c80020030356040300040d03020030310341c441580401049120300140115a41045000c032160700d218841e04503100d0007108203121610307040c0781c10301c011aa00c4500865000f41101c0c0074a440e000001d200741c009982000100ea2000304402e6283c040340a07191182d07803010900001c0064135212002d400b02e400a8180c40343c01104a03181030400800102007050904c840c0c0881d400e49419901140e0b096680e00036420003034103000b4084885038040700d0000c540082809650084014a104107055500050f60714851200240520111080b0704985040791180305440c02c0a6104004060316418016245400076a6640000c0d0b0000d206502840700c9030039800c11200310020650114901c485401c201f1225940080c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 407416600 1250 407415350 407415373
    0x705040f0b070f0803130f0f140708210d05041a060312040e100e010602010e0106061106191d010504051c21090803070804020406090608030f090312030405 68
    0x10000ca801000c03032000c680d15018464440c1016107840c500024001100000401c2d0f846a4005000c03950780d8005000d140300b0722481c5040001d2800c3c600044500a8030100340d1044940081517501c1180c4084024041e01041a072070014060382050000450b61014040c0c55945d00c3c0c05d00c6101d1040d1702c9a40860300c00011a5a021048203000b06098030940c095103580c1184001882039074103c40c0303212a55015034484d50040b0555010301d400c24402c580848000180a81e415040b20600841d400001c0160544a0000f1140103109c1d40f00e5642035070200303020804007009200500f03002514050001404480600c80c0512228204090002a0f45031828442800806d0000c1414919010030324801004c03880c00141442010b082c880800219440c4602103040c1a5004440910791002089a0b039107802000075126007001d40e0185d020300d2030401c0c04518045d0a124400c1603441c110020350070000c0b030500d20210707940186c00b0903405000b86180c8030701c02005100918025840383d005801d10001a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 407417850 1250 407416600 407416619
    0x70b040b1c022a030c011b0e030304030b070e130213051314070c060e060403030c20030f0a030f020d24060905060d0212011404060f0e01090b01021005070504 69
    0x201100d51040320300c10443e0402d4004070210144036908943c5181c070203000b18030120380c114040c442c0c100189508011028411043c0c100041c0c41c00051903d50b50500e41c882e00c03d05a0740c0c01503010040c4060440f1010030329043c082d110340c00d00e00e030000340040c2d42400c0501340d02040c1e030046203c3e020a4600d07188140b00720701d421402e050000c0499101000384100130f0795200c81706100540400d0600603818044011300c41701d600030056815202c82200e0640c02d00340b0703004009158111151001801c024408052484859100c00708040030400440c10008500e0784529683d03c0403100d042419912500820b07100d03240e0001d4002c0f00d4510340001001e44840c1038003402c40084014003c0741c00a04d040501240d50849a000191401602c0842d281c0014004400091045221031800d04066100014100419909804040780250f5080c82099600c2500b1041c10129020f01500b1119140050002441c00d81c00803540f11014411034004440841d03000c0101c8105454241c001080003a0500403401d1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 407419100 1250 407417850 407417887
    0x240306050109180510110d020705100606170123090a021911030301030b06121c020c012a0501200903070608040f060902041d060609070c030c080a02070b040b 69
    0x44103403400b80030072195a80d0364840c0c5d00600c022918560b624541c0f2502d01c00c0b4000e80d0800c19098004654902d00c60901554034615504456496070800c200850580e11607818500042c00f0310f0034001c074603428210000c2d0b40103103403014100340550003940043d0540d50550b07918000c14014000507035415030041c404041401007403203201405042942d01030b00c2c500c004207c0b4110f981015145049445001c00180820b1300f02d8400d221511941d2140b070602468108000803060481e022a001c01109500544200c3c0c08280f03c7d101000b802c000326820039605140d8009058801e0380000392522201448109088902030603240c800b0001c100c1003524102001404003511146c145480c044c940b5658080104035240c0c0300034071954030b40c2c01500071512a50800042d25000b0308840c0c1d00c0b8130010741c2c00345e640e420407100d241c42a580703032020412141c014144070014035010359401c401943c05440c0e07800f45a004001013000c600c6201000504e1003140c90180028101d08420156103140610070610401d8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 407420350 1250 407419100 407419121
    0x4201b03030105030a120c0f03170f06060715150f030515150409050a2405060a0b0a080c0409050c030a200318070317070c27240306050109 61
    0xa0007040140401e03900043c51444081c0d210003071a0402c0f076092011281c080705503000608070860000d8120401d03421018009007071114425400c0729543e24202d0400403441982c400e90030160400c0b0381c8000c2074241c50300c50b11044c00d00e0401310300300110070b031608107010050f80001209105240f051080000034014404544640c5801501a040c800d020034012452032103650f00c01c0e56201d502504100051107480303d216046100b0188044200c1031959510050484211032030f403414001501038034000608800f0b441b9104c5804c3d0420161301401e4035011402f80c80c0301c4083c40c0c00e100000d1100b01d140125846105000f294070303140e0810b02d0303410059500701e0a0006200ca404d402040e01d00d511001540e5200e1040c0c03034142030001c0c440f0060b13400c104d0903030405803444041c60b5040c1d00b19034034480203025461107aa48a01003503529510040b6042040144542960428811b0040155240c00c20010120707480d851003503507010031403040140b4001d070b4001c4840503107078401003125a4141c41000700c0103 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 407421600 1250 407420350 407420353
    0x11b05160b030f3c09210306010f0c062c0f060f0601090801020d1a0102070b040911091f020705030a021302030705040e1018020403110f04201b 63
    0x18206041d40b150700190080c0801000e01c1c602c00e40d8402800b40d0800c09100c04102c0391a142d41c2c3ea0700b0501c02c0102e4600b01d80242461040d010582c11b886240417644140071b805805031402c644078100111105102c020038041000032000007000825821700c6040302e1807004001241c61110017440303001240f400e04500c1d0400e034000c07001d5120b2880d808201c0035400424030200706500d42d5007100585203070119400052ba50340c80401c0880d83c0305017581c02403096400040e03c110810780030000490751988140500e055000c0300780020031951001d40c114a50301104595124144100500801c130ba000a821041401d0780c29403000c0301119405000f11009080b084c7c0250a2100c420317000318a40d002840c103015403541e80000040d602d0781c490000d540280103014001c030341034140080d00450015440c06918000d51540008401c480e03200e03c00c03901207a42c8284408040d400100402180b008520800f64010b80c0303540c04013a82e4140d44408402d03002d400400e442d224901292045002882e03440f601c60103 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 407422850 1250 407421600 407421607
    0x230f070e070c150c14070f0c0512070b030604140c131502070b0d09050d050703080109020901140a0908010f0e01060e0403210605030a08040303020c03060c0f0702011b05160b 76
    0x811035078000d0380f904681510011a100d04101e500721691120383c510070f840f160001ca100810003902203021071403a8007410113445899210803c03c0b000079075440718084540e202903410407681100030301942c0d004400910020740002407861401c0c060404030b40560104c100010082d052400c444a140c0140c030b04c03601d0300c408128000c0c0001c0d650745481c0c003c031421440c020841c05105505038001c810100da04c1070941e08030040003032014000d901312604c118042500c94002103604611882510a5494141d441041c034501c1e50601d40c1d003e5001e44000002c110407180d0100b10840240905021500202000959010780c000214212a59038000e00c480c10184418017011a034090501504413500c40c0c101c444003211300d52050001c019071350220341c26018140c0c5110a00042a016204490003502a41c810040c600e00f010380f41c1c00101c4014100007001d100181002c2086800f611700c1a1040c11310b0002a43d188441082078a00c22070115501c0d13028a001c28407044485c030003100145007421043c0e06 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 407424100 1250 407422850 407422853
    0xe1803030f01170d0e012a06021902060f0c0a020f01050c0903070504060311010e030a1a0406050a0e151e0a09021503010605041a040b030a1d0d0c230f070e070c 70
    0x1545c10005001410484030124032150b0088004e007141180c0c0030b103540a00040c01900e0407001035080000341d02200f648a40d03007060f2850012406502c07070b205802d5064060341d50b880c070481e1903400080c0104210b10605040c1341c04200700348030f001e010f20b451380e0165455070440c00400d450700206400c0b01d800b071402c0c40c504000080c24560303000040c007000d0030203c6501d000000441d280c640010400740c200420712504004481c0b803107c0440c00745014020900843e6604480c2c9001d8071494814803116034011100c8001500d03400c1c01141e0026080340c0c40c084c0c03180810803400e400d0202901c0c140802960b0b0354508003185800302c41800c220640d8000305042d0340c5000c001409a000d82d02c600e00c06400c0a020a40d14954240203d4016180e0154980e460382405508070004103d04e003590f030120f149200c81840582c800143d2124060a07507030350404c24008d950745122400145800800c10300c100701c00b052128900c244041441c500040008010007032900030040c006c640040c00040500c8001c084040 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 407425350 1250 407424100 407424107
    0x40507090305071508151206040b07031104030b1504020405182401050d0f33050405062209051903080c0f0d0207050703020a14040b0f0a0e1803030f01170d 68
    0xd50146c3e420a412031a021060080b0b404403000040300c0c00070b40a054100020407451002d054040d01441e903042000e904031141c600c0d4a803041c0d000c0038200500d11400030700c488241c43c0d4600300003240a44090b080569500c080340c0800004800c0521301c3d9950f40c1000185041c10315015001c1c3d02d4811000188002c24002a00912421000090f4152103001c0c00401c4011074011044814242000302d0405800102c00024a24032141014030380c0e4100c0c50000d05441d07c0c0c0607243c011100148100c41805926169407000803410000c20700c0691508003180104000b4010b4404a4910280014151a80e8a0000e14125005180e0214000240f011078080383c40034050351000c3c1c000940069940c45241481860a43c2c01c0c2d0000394070080c02c1a002c9011401c440008100f400240d50600054005c04100051003021014080d00141c18540c00c1024100c0070409039005100d03040200c58584c90110300908507441241e1a40810100d1401000f640c1801c51400d000c09460001600b1120304000005 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 407426600 1250 407425350 407425367
    0x30e0a0e01180905030a0302041e0608071107090501030302150a15051e0a08030c0d090311060a09180903090e040203071e050301020c0a26091e0405070903050715 71
    0x460200040c0300c10010318202683c02054441d4104084070303207842c845000180694841d000703414041240205a00010004c150900143c5210b40c076070320300c10742c1d030f54904594442d288220f5200c0c0303200c0e20350001401d0020b442910f02841c020b40c0607100140f03142c103d61020800c05018100365520702071500001c24250b07054081070360701c21103032425000401d04512140c003805450040d4040d02c095400100806d0000040a050849509440304c000307982e03009a039a24031038400507081c2c0d41c0c501c5a50089103403043c010038040d075180c1051445903840d001c108c400b03000d813040300b0210195036884140078141c2141c90000200342c1c1101d03603021803500341d003c40e444480522540564942d40d45000c1540340000c1480c501a10000d0000c540328007404021035901e007481002a1840030610381c420710754002e02d4140d10f0300c0030107040c11b0307510f0715614000b8030070301c401d002e0055101064154000e02040e0384074000c6038011900d650320005164158100070f07041051940c0f15440c190412040c40c051107070030120f0ba = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 407427850 1250 407426600 407426609
    0x10311150f090604030203060f09070f06051914030f04021804051504030e1005030a050105040605180a020f04081e010e07030609150e030409180b0609100302060d0603030e0a0e01 78
    0x100307610707400b003070000c0381250185400007581409101d08000e810030f40b040c1041d11510303c9000321165280d480c1120124190103004c0c110015408119414201c456520b42124081c02071404201d981841c40c00c071481e0381c105a501c104410312070300501082d0b1501940c08040c02c00b4142000c2a5414240d580e650b80e40780c0c541220004420100c001001d041c05851241826071000d0014446075098810081c66a407049405003c0c0c64600000481c0c1814984100400d60764041e01050b540e00388030480d0f40d0343c000300900000b10b82e0303000c0100320709102d14040580700422001d40200740d405489040c58035a0a150b20070314040341e25092a62a0511000856008594202c8d41c0003030f028990341022900c040319252080b9001d828940c44854603640080140200c0d00c002c0000c1040700c0710030035070140200009001070a00c41c0c2c00004110280b400100550300300b43c004140005242d50383d400b217203043d0080c01e03680341120b60b900f108105054000306120014402265403660302c508010700c802c869075041c003a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 407429100 1250 407427850 407427877
    0x10615080105120c03030c0313150806060c0f07140103050a1512140607090f0b0405060a03182001030b0f060a030c2001320703051e09010501031115 65
    0xf590621801403000c070506500144c180d80d642e0038043d8266607283e202c21032458a0043c1c0c0e540014250442801c051411145a9201c02e401c1c0c8600040102d281c00c29414a07a041c000d40c0b608442c550301c2000310400508041d90801c1074401c009002400f260310050020401070300b08040d07a114682c00b01291002d1760300240160325200360500b070600445044c40c5055604d44144424452415008502c030710072610030190705c2c20349a03103030070f50001710740514807882d900300c0b00c2803040c401c00300d0103034000300b041400890000604074010b4680c90001301010058440f201c940c046440f1195a26010302c3d9070f184019298642300303400c11408a4400e00c5581925020569181da482c4d1400d88298941c4088042004184542c01c40c0981d0181c02401144102480c0c1c1d09034510058150007c2a408030030445040c508078100c2da600c0f40c0c02e4001d40801494404203540302101d0354502201c010340e450144003400000100b41d81035290002da020885500c03d0710801c0e2810041140040900844040c3c402c0e111 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 407430350 1250 407429100 407429119
    0x90103061808040311030d0906050304080d090f0c060f1803060e0c18061807080a0b0f060d051909050d050706110307020f0105071107050609131409010615080105 71
    0x1070840d074416000400080401000060000a01410f58201c980d2610304406903001101003000030b6038081218402c10000c50801d100103804242c4c444050310000301c400f1400710340b004080d501e444440721502000c6406509191060101580c0000303503a171a0350a03801c1045004499003c1403840d41c580b0b100041103076482d6482500607a00504c852071950f280a0030b0503040304003060b402c500705801214828000c050100f0b6216603540c1221086000d555140c4881000703444485900002d07080340c020158100c2d074141c124860507115000100047d00c0c1030200000c580c01d041d030300724004810800d001c80c00e1604040d0001c0c045100402d0386082c0e50b0f280c5c14082c1d6240c12030301d800c50144c80800340e0b071640c0f680003108001506401092032910300500c140204407a94910703800355402060740752001c000350b01c000700500690034124020500c0010042001c614150b81592030f40035604511100715140da058018070000c581c0c01d0054602404200c40e80207404050320b18010102c080500c1031a1140c01a01f = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 407431600 1250 407430350 407430371
    0x108091f02040f030c0608070516020f010215180115030201020d08100503010c080f070c0c050f0301110412051207170f1902060105150f0a1107080f0604031d09010306 73
    0x1030707044600800702c0c0d0315242207080e40c3e4108181c02c03d020b88544004a5400800140b84030310803c100c822040300c1045100000c0c0da00c0c1c0a20a500c1080074016055200b410b407001440c0c0d0a91640f0741c450010040c0b40100b00205030301503070955208078880103d0488146013400107030707000f15080640c1902031030001c0c0d069981155450031066250f00c0140c00d0352800350351001c20b903401280c2c4c0344580500d107203600c00d503140e1080403900e10341c000b0005007001c040d201c014070262912629580300c0020042c00815a0010450380c2c40710303035006500c9100540b07070b0302c9001ca040040070b1102d080b4031918030b440c0d60300340702c2652500b001d001c1c409502a4120038001903044030340d0034034009880034030340380c92803030b0491040c0c585020b944d0308400e00503144588019440d040301700c004823003280c4502ea4078000842c101503240800380d414898100303408041d406590f202083c0c40310b08002000110b1003c1000b000641001e040c0030b840d03495820003d500402c03c0c60900c1d00d481d1100117407139045941c803400c0044c400420 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 407432850 1250 407431600 407431663
    0x204030506131a04080a140304260403080c0303060a06020f0a0f0f0f1208060303180d020f090703050a0b010906020c010c030302190201050a0b0303040f12110603190b010809 76
    0x200620300941d0004010310040c080c02d00f0140000e44411741f02e1814941244900440501003200c00522081d0344185801440004200340301c0040110340d052400d01d0f84a544141c201e0b0000300c40c0180d281d1011007005a01c0c54000814401020b50340042d080711030856100c5a01c5103007020b03010703100500071000300c0104210703c90341d01d1846030403daa01c81205407504d411800841c210b00220001018075002c81e407030f03140200413101450342440300e1084485896090001202c02e10600f682e0008070f01001103065160980c01070b01c1841d040d034000a0300d20741010302900b04d03080040e041d8100f101200003071000913000100c064a2540900f40324000101d5480c08801030301c588c40e145240c12480c034440306001901500114005e0325001c00c240803030304a4400307040e0b032801180b15402c1d2000e40c0e000200503603010110340034800750046c030034045407890072004a1800c3e401903500c01c2814080060821014410f48038020051100b440c03c0036031800c1076048540d4422520030300b0003003c2615414181020314 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 407434100 1250 407432850 407432873
    0x10303050d0510090e060a0c080105130b04180b07030501060c080403080309120d060302010908120313050c040c0c060515030d120902030d0215010801020c0d0e40020403050613 77
    0x1083c024003078811742e10200c603164441503415640250500c003030301c55000c0c0900b000a050341c101403c40a10302501d4031a0ba406082e9044440d45c2090741c92000d202c010766034070318070728103030303003c5c4445d40110308040b6001001c0380d905a11990030000c0c4103000c000001c00050464048079001000d50b134498a03010b00ca1801d0513440d242d20791007050001868440c030141c58020380100c0e070003600d601c142181e4400100da00d03495031109000d04500100001800d83c41c0d0741814241d9940181c089440300d805100c0814101c4009003140c2010440402a80c410400c10b4040d103544050300d2003c0040004481d00800c2d0381d182000803860501c03101d181c140c2c0307841d03034154490740039650010221380d4007848130740c0b01a4032900700214648003014040d00104505105008603100000e112000301201c0d16810400c580c80f01103080b4a950110a46517046902c8003006444030390030310140c0001c525440210180c60941d0f24079400342000900502c000c20103c0d501069055200d000211034110000e07003483c4c100007503034 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 407435350 1250 407434100 407434109
    0x706021c060503010c05030c04033008060f0d02030a0b0a0f020403060914061b3a15060e1c12030911040516030c1b050c0901050108010303050d0510 65
    0x44203010030034480c5640d03400c200c0442e60142c008000d14440a4001c6401e448111002c20300207004100800025802d1a414000500000703000c142170120038110a608080346001107001400f502c040c07003101c1c13528903418034000400b01c031a480d401400e507002c6500e401c50032101425201c1e1200c001200400540c01103d00940c103035400b19078880d00c030300e8404010300c00d070070040d00c072000c035002c89542d40d400008080b4040c401203104c0245584409601d81d0441c2d10902c04051040b8600200c20706850140d580a281512400310724403010f03d28202120480784205988100e0210122082180e00d801c03160b6865244000e680d4078402c2c8101c000d240000705c00e0203100800280703030540500b480c1c5e03602d0340c80050004d100781c2019070441c05920401c01500c00039501800c5003070f03501e001010083c0c06980828481309841c02c040d4501040c046401100340c0300014162020380116541007007910340700500e903000d0582428051036650650320001c00d503000301c5076000c9a01d03540318003069291841c580c5880040 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 407436600 1250 407435350 407435377
    0x9070e04110a021c080c16110901090b01021516031109060f031b180d050c0a0b09012c3a05011802011b06061508070f090807030206070602 61
    0x4211441c0003d5440c0048841803030307916018030015a0344c038861010380b801002c1001405042056075016942d0350f503039010381120301711074002658072036484000030700b802005104800582c011a40e0006818011a0008026011116820025400307120007103003405d02410f181c00100b840c5800c0d010402e40c0302da071a5155100070046a180a2000303200d008521800b101490210301d0440000001034074000d520281500083c9107107c400e41d03040000410b034080307024000311480c5400300f4012802012980d00404410400042c40c2d28665801040501840c1d10390700c0c2042d1540c04a14003c1100c5c00c803060a280f1482c118003d83e103540d601d50144960880c0100c4040ca03541001d181d4941c240302d0b1001048034a5420000300c00740d140c0e041415940e21a8041e1298103801c05c0c0c012075112444941c1000725070407039440b1350220b0b80001c800001c05501c2920707100c01105040040000d410000e01c2d00c1692304102103144103016000011468008590b41a80e80704e4440c00c1c0c92403ca0080c1c0140752085142 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 407437850 1250 407436600 407436607
    0x30160b1509310c0308040f0f06080a050c1201080102090f030c03190c0e090c0f01020a0b0f0a02040e2e0312031a0d06060f060314011e05100519090509070e0411 70
    0x41c003ca0030006d10480342c504180e2969942e80759401600d00103a4407d5202240c002c2002900c0d0301e9142d000140e002e200a07032442d1030080c00554403480d0702d100380c1041c0c405070350100300d225140c14080c0c48001e020310210020900803410700b00003a9909400c04101c8800484034000b10200600a15100040c101601310840703e840d281c41e925648403032028041d8441d112035048018035500111b0702e20324054210a103005255158440180c0103600546146100c540c05c006c0000c1030754103a06858001c0c900c1d03403030301ca02189075540c000380d800c41c4a4008002045410400700b0003c0d645070408140010103080209452045000d03040b201500944210740190300c2902950811805a0203407065a40c2c00008a4602e625001d0407412103068140150f001d120300001070015008152864403a11001c2108030070140d124400705240000e100038560100b140031032820002c0120745034900551980c3d18000821900e000000380c03603404040c0170441803040c524a40c6847c1e4540d030708285070f21509a05400d54 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 407439100 1250 407437850 407437853
    0x20c0a120e0a0b030a05100f090914030405090f040503130e0601031a0109050d02040e031621052a0607090306060830160b1509310c03 59
    0x80c0412540d410000154034902449103501d07200d0072580c2901c000c001c82c2c0d4190781d1150595001444090b1800c00440ca031000002130000c6500e00c00406003a800002103140c0c8010716003804641180001654150010301040c4030680b0344000c4507038045001d80200400e501ea904046040d403103022a60b0281c10501c0304081400454a0002c5001b030b0000c1c1c0e0301300240311b040080b0700380580440041b0340c00680d5000003007005141114042074298001003001501c640c090700c15500d103034080f58001301d50314040c0000c1c2040c04680d154502d00b104d4a080c0800a98a100400134030505c00c007010005801c441d00c2d01c46031f441420218043c80d40d107003901100c0c6d46040105028001d800c02e448121503e42c107006000c101e803a0003040844507005480c21554800d600e000c51150020260000c009010606021040b020305d241c0b00f56610403030040304d20381e5590420010423000f440382081001d00480a1006011034900d204080480c0c80c0c0381c150540301030000201140d2101440840c004d0050786080b40040b0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 407440350 1250 407439100 407439113
    0x501050c0415020105061f0210050703150f05010228151b1706060309031213020109230405090c060f0a2006041211010f1505010509060715020c0a 64
    0x7079490500c110b040c0c500501070101e083c1d035003c40d26642c100410070340b0706d1101348a00140c00707101007042c01500c20040310f01c0001d208981e021520300e00000c0d118581c0701c44d031144e28400c50001d0b08407516102e261508000000c1d40d2040040400030600386030300c41c0045400038400807401520b03405030410541c403070f00c0229100500000c0c49402402203c200c2c6540c141d5010340c903442c1394210541504800b40d83c454003088034941004012030082e00007008902c422410107640c5521601c0c076520002100d920310f000060003040a038100c4410100200400c0d07100d030302070207440088100201c401103103a0391210b2000d8204090180d0b615004000450802e100c000000042c00c1501c0c042d0759141d400403204e0300584a51000321540d10b10a4010001190200e20740d04a0400025400e00b001e600d8005401d0074142103804844595146035550130545504440c0316612800400091800f40d003020b10160005005100e007480080408516850001e0000b00a406695050719090266040340880d41003c1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 407441600 1250 407440350 407440357
    0xc15020d05060406320604080d0207180216060b01050415030e0d080f04030c020d230607050a0e0f13060305062d0103020405060d12050c06250503130501050c 69
    0x8074401d5003402d001150015400c4c41c020400c41790000100503010118113060552001580110b03040b0b1000c000c081070000b01000089140421513000b0215180350400c00139003403242c01001101c0e540100010701e80011682c942140054101000207590110580182d60754803965204202c45130318440009038041d090341c007070580c0e01100300c296043e5418104046403a5202260302500762045c0b68007145c00319103d00741030341d4440d102030940012600c2c0b58072030b80b006040382d201c01400100b0016a2220421003071000c6a088285410210b080400c0303c94094842028852400d00130304030844400819038644c0c0b0000700010b41c0d10030801400c0d4484c102103450740d504031221894528443c01102581e01d60741d103000da0b020a96241c44000b40d081d03074200700103031101502d801d42c444114542c80001c501c800102400810107910b44a07a113458424503181071010040c0301c8040c0004101c1e810080086036074111002c070083d8504507030359640d544030302140c030407403030001800e40d40c0790170b040203801c51070003005 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 407442850 1250 407441600 407441611
    0x7081609080f031b03070b13080f030c0c24130c0e04030c0210080c0301210b100501020f0f0a0b1f03030914061602012114010e060901060f0c15020d05 66
    0x200781305988151100d40d5a11401c0401041c030503c1900140200b1041200c8c43c40b082c0c4191000d80c907140c04c44d0210800ca40042e1014030807080002041c00390410200807254071003030850b0071a00010415840301550040c01045109600301e076132400e6040101c0b83c07110310702400458140a0881c01c0c42d0034001c05180d82074004070701480d080c0701d4417083e0601a82c03c1a100d40d40d450112481c1d0780c2402404200902400041710b51403440f0b001480000c2d0303285900310310401c00d414405800c18a80000203241580401d0200ca840d040b860b000001c01c0f9001c070b9400e41440d000303480d40803103484502c1d5140d40740c034425603035441008400700003000b0550712040c8641240c241030a0700403516148401c100840c881c10100811b0b192400d940200154010607100b454405003030392046a480460320700c00e0607078242035a92410880c0950040c80301c403203001c1d01030742c01800940c1c2c261407030b6040800180480418002980c00e1154818507003040161024030410000d00d0640203544460590740600c010300707400d0340e2 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 407444100 1250 407442850 407442877
    0xc0a081917010b07062d1104051807021e03030702102901051e0304050708150f040c0b0408061005060f18040b030105010f060e04020307081609080f03 66
    0x111604034480c000003032594100400c148180d918041d03d044180d40125030444d007560b155000001d500d000340c00400b41400003014082e024a104c0c41e00d10f0100c58102c02c0000f0240c0c014003062103141c9681d9907240842c070620120880e20307107910f8801ea152031650791250340d1848449110701c01210001c03001d10b004200c80d4003101d400c0c44d1402031200c02c0d01c1c1442d00c051054030b018000004100546405500c85034018140989001801140500060001406000101400400d00c42000410080c040052905001038000d03444844040118600080c20b04021b0300c4605021400780884000300500802e80d0003d00343c2d4840c4da58841c107441b000b045a03040c1034418014400111420142d044401c00c00100641524003041d080b04889985503200c411904940d6a1071500420b450903c20306010f405e021070b031011781502d4002d00514088100d2001405a40144140003a264200b5070b182d030411007010b8101c500117038101c41280c54029075882001d00b40700e0451841d9241602000400c0342401096 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 407445350 1250 407444100 407444137
    0x313030306140f0915060f040305060903070c0b03090c030102180405090d0503010b13090906021e0f04030308090307060f0e0c03031c0528060e0603060403020a170c0a08 74
    0x2044182c00011680070306401020444241c075261800d55015503101c50110400300400752180b010446540001e046400c507502e00003420b10a0103410040c1580c059910401103140ca034030740d6240900341c0000d202da809080808008102c9100b404c4c842220f640001074000c54813054240180141c0c0086010a9400b84d031074240440c10030380c0049011403482c00c0907150b151a591800412140c103a002da150342943c94003800303000c01d4a50300c0d800307180343d041d00540380540c8420924422000d807080e240400984a481000501c1080b034204095504030398242c1407034251960342720200c0d030861046920052080b441c3c6030381e00c01112103d81c412094400c036002112149024101407540e070784a07054406900102450050030003c0850304400d911003020b04225006e82540348a50220030092407456141645988003401074071090040315a00910440c01415a42410b480207500c3c0c001c0080064200a401c4119280c02d1692400f21800c01b8966000c43e202000182046000c1ea002500c42d000d44a0389207 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 407446600 1250 407445350 407445359
    0x2010644101e0506011d01020c120114060a121b031a040303180b040204090c1203030b010e01030605011b08090a031a07050705070e070c080409020c1203090d0c080405060313030306 79
    0xb8403c03107200d4101070f111150721143c0700690051880700e100c8540d04502c505c03c1c2c040d00c5a210f81c0840450010340750000301d203507a804c0040c0920382200070f29141c0950701881c0704002080c450201a50704581001c6080700020502d084854007044540018040c40c0d54100303480842d44c0080c542c40c0c0304601036035040180e9188a60000d410040400c400b0b4100014000400c0140c81d00343d101115040c81024400e204950300c401050340b105100300140c002c20343d40c0752001c10650f080340007184a2002440c04000580c10100041d02e21503640003454191200c1d00d0301c4901b0407204c0400c40740d1742c08004024203125a660700d00304101c106280030322407821005d5000305000d103004500782c1c0c8441e41e2020103400114106010b00200e103900a00c1c0c032003000100049400411106801003001d08090b240143c0d0b160b50784444a458007907528101d86201d0420010401d05000c003061105000d8600e181006402d14941440d002d54003454100a500007000414000003089200308849414420b0300c0a00050f0b41e82c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 407447850 1250 407446600 407446661
    0x3030c050708012c070503010c0801080114010b030a0c0306180b0319050a030f180e1806071e030e0102040906031a090c0d05010e0f07060201064410 65
    0x10b4445045120380c4140d0a906444000544e007094201030100e07000a03a8880010342503900c04140540864242001400103030002c0c05002010050400e01d844954500841101b05110040035028016981c244040096203e40c004c5402420035035403030000044a034009600418650020610a1252849550905481c4081c2c41e100030f41040c041e2254450360786040d201d00c2c02d104101c0303081204a025200092140700880300c064600c01c00662036900d04800b2203000000d48000223041d41e80700c00100840c1c0c0e5800720360142501500e01d4454941100100160060041059480420b500228001c44c0d110000c0c0c1c4400308580c0a003004000400c070b8144d05010072802a101c15005030442444a81c031400c0c140c01010341d45102e03d00008a06c00610310300d904105550603200780542000320104002d40c2e09015800280a181c503c8044600c480500502145100711740c2100141101111a120401c02c440072520b6045c15002e40e00300e0b03058410505c4c000c1040f18104035141c490030020040c90b107070 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 407449100 1250 407447850 407447861
    0x303210501050a06030b0a0b0705060601030e2b050c0f01020a08160804032a0b090609010c080609041a011502160b070b0a0f02041e0801140705130f03030c05070801 72
    0x18050103c50300b071820306004402a1034a0464150041c107880030018507402a80010040a8003500c041e02d82c42c281200010280c506080580b802c41d400094803000440c0000e49800c1e140c440030402c1100107405c0c550980c1d06000300380c00c6503d00c2c01422584800c112064009000c5d40480369282042036981c604003c0708441c2c1090240300007124540042c2c0024000d065040c0d450105003070003c03120086254001d80e42c440c0c41720890340028001d051129202e0704000098020700420001d1160621782c410003440c003000100740d58800d1203481d02190621103200c0d5200c901d5202811516695a121807182c64201d0b04e15031083d00500c201071110080c4400c1540320400c0d10400c0d4030440c9446d0017038880d6880c1500140c828540340d80e54441c0d801ca16582480240010f16920324641034500c061235a00c0583c509950080340580d04158001c019405403100003a408455800c156460700808000210400b10715040400300c0042010040705158009900c050894811030071600b00d2a20f9094171400da0b01d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 407450350 1250 407449100 407449109
    0x10602030f0a05160809180c0d1d0106081608010c17060a0806101d040b040f03050d0606051b0d09060c060b03070609082b03050402010c020a0303210501 67
    0x80007806032036410081d58000b822800c0552400c18189101545080d81107507120508860501001410107840d00b008840d20856501110542105241261050055200710b9448602a03640c6800e000d8040e12a02030002000c0d5603040208445502c0708402d1b6900e80c80d44009251800d4000b500007a00c06050040e400820019621203884d80c0ea9442d03210295038014140a42c001091130740420156010401e0034031840012402445440c9401c88032510700400909002e46400c28408100c045100c803010340d5000341d80701220020301c00c0c0905040b210740c0030f0701030000c444078104000083c11540c4040a000b04c02d17080d0036a0403440c065840550360328004000c4203004101d605e04100200d5000d001003250701800b4141c04100c0e00340e503000090524015030440e001080e205d4a091040c032408001c46144900d00241100d04081500c4007180b14206080d402010142c41e040006c045902c1005001041507020701212410384d182e240107844c6804912407001d1440d0003000c1040080040d0080038100e4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 407451600 1250 407450350 407450353
    0x130e0f06090a0b1008060102030712020309011206080c090601050d060303020312130f020f151308010c050c0c061c050906090105160801050d140307081e0f0904050702011b050409060509010602 84
    0x6440b91300e0255a0114028a514103500090207030b140455080510701c59201c2c2d155000d155107600210024051300d035460748901d00c031442d158040c0440800002c1c9089040011680d1850035610740d40101c0d040e1154072000703042603007040c10001c2010b400102030030f684521608602141d541c0c80c02d15203000343d8502405441821540d9040000d0b0410307190381c00400002420b4046910001c0c00084000d9103c03000f10b2680484e24041084103940a2098020b8001907160035450145030783d605580d100380d04540315108001c009861506039880030710031828008034041c2800309252044100c1d84841003107030302c01480d5080000003010015000c00d1000d20380f1854a4815640e428501808040b6510102c210394007403840310031881d040c004101401c0403910400301980c0d10b05131418001d0110a40d41100a8460024003403001d80d80c540409450628609503400507565a80800483c05070000c04c1c41c034100206905080c20259500000030702c2620511181480740070780e200300b8420182000d11444006 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 407452850 1250 407451600 407451619
    0x3090307290124030b04020903010926030103080d020c030d06030506270703030305150411211320061305040b0a03030203070f210c03080a0603051002130e0f06090a0b 73
    0x5140a94000c174414880644010305140041c0040f80c00c684150b9400c1e5050250809070390701d410038481c4403003801a06540514290351450b0b4400c1e6541c0118015460201e80106d82c103210010100305640600c18210300500c00303542c1e6418031688401c0d095690240341d102c6a04202c0b040d0040940c180e03c00300e000310040480f2440e41d00c049004000203048484100302140030001180d403640110b0b0564258000d0480da5000941c160101003400401c0744042005000100a0f400000c400c03d1100117170814213a208801c5c1c00c200ea0042011000c415551012020510710380380c40c0c02d0080c58003582c0c0290740c10042c4942001c104001d0001c41e03c80200164810010352000445042800480500c500c074084030203259030459419069154000d10006480c1e03070190414568441c139400e8001480c55010802d190550701e409885000c01d028111105400007810809010304264050080100c504140003d0030001603220403403070309039401485011a80049117440256110304800c02000038001400d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 407454100 1250 407452850 407452919
    0x120d05090607080d020c070e1501020604080702040e060f1006090803032206050717010e101a0903010e010e070e0f0415140901060503072702030903072901 68
    0x300c2d40c09030004980744901403107443c0001200d4005050b04000801c007504a6504000c6401040c010040c100a403c10002071401030598001c20503079000350b000f10400340c2c0d62460f80041070262003003c1111503a481818208160580a9500c240c0a22a240d015140c0c030ba80d1a0380841d100611405044c219400410100b200d44101d070b0f580545d01c0c000c2801000030802280c50304012214100c5000011420400c054105035200510945c0500102050441d2a051514981d041c06042e802079001801c903c0703c2c403228160f0b000058650140004000340b050600410065020b001e00c948200c0252058450110300381d442800110f10510600442e0240b03940d03144c645a1400c11228014905540d442c08000c10351004a041103100e201145e001003140b83c580001c2c9490504594020784d404007000001003001098a40d40707010180000300056141c0d01c500704050300f035204440c00200888071450190310308003962106c80d40c034440c0900c08603029a980f10351011307140c0c40c180840c00c0d803004000807c0c1c8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 407455350 1250 407454100 407454109
    0x40f0f0b090c0409031b050703152406020a0209071e0e03060f07020303072d05130b03010b181503010e010807140a0302011d04021c1128050c01050114120d0509 70
    0x20b8400f070240702107480303e0741d40e40c80c0e040240ad10454860800750b129840c5201c0c0c0d54011481800a201d072031200800d00f86021402500d810b010710000b0720540c42c00b408115524800c120065031100c0212403101e502c00301940140c10172414121140c007034021000003c2c05808140b40039031040390f1030b8001d1459a03450b00301c21205e0410b05540d04080708062100440d0b10344011011608402145d114a03503110380c0c110503482141c405500140c2c083c4403c100511008a282c0d00b901e0340c680181401d00800314001c00015086807001002422094000c8000501e980044419030704850140c41074901c4a502c444140c0b179040589074102e034011849900030230041d40300d4018100c011164510341100c001c503500001d420783c3d01c401784e803441a00c0b03050310140040b00e0724460001f81c14200d010701450309401c41d59903154121041c51600c03005100c2c2e45200c2e406802841180c82011020008005075030716034005884403c1d686012030302521702c055110403181300c002420b400e00d01c5240c032550b060110f03490400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 407456600 1250 407455350 407455397
    0x30d090e04030c05031b25090213030506070c140705065401020735030f1806090a0314160e0601080609041505040f0f0b090c040903 58
    0xc408014108030100f001c075009001610b6910b115030714a8201c50984030360705103017148130360440b10b6103c8204004018901c449039244115602c1000c0942c4942d500e182c054441c0280345d10142c014024602004581030340b00010084080c0326031000036506101080e0155926007600510fa00000308000c01440c01a0911058892901440040d007188034040050000c002e44000b516080c0444030190204070750185826000b91042880200419850030b0f0310400003140028801002d044101a5041403d800030101e07441130441c8401c5070f030703510540314000c40b50794016040c1151a000103103001d080e500c0c0100840c1d9035603000804407803025095480310001070740040700880742413041e42d0034904610611600b0380010718600040c600e061070404009014090014096881022030104000016a0350441d901085c040102c000815696a25040c1112401880060403489100079900c0402040000c0503210720701c60f2040d05d004071200300c107020603289445e00090205c0c0583c0010640301c0200c0c040b2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 407457850 1250 407456600 407456603
    0x60405040809041401060f020c0306011707030f0b060a1202010c02100e0a03060f0b030606060706180602040b0a0f020102030903040509040f0803190b190e07090302150c0606030d090e04 81
    0x1c5910b4020810005022a1a4040a10711100e09440104111500096001811555800034000c1060b1800c0002d466440501413969815600d5003a2846c1240410042020310741c4510001ca00d1411801c000903c0481142c0c0303980b04111a28002c508a0002e101c00c2c08040d83c10f0f1a4814030803120341c2003000d01e180881000c420004110003170181079071903039803c0c401140030f80c100142c40c0e0b40003200030094401150200b8060307400b010610840d5140c0b0402c40300203640152002503000000e0407104048417031203c02a0020740042000701d01c81c440d24008000c3c200550325a00d001018465041c2e0030703070104a0344d0400c82d0f081071008111506054011950051040340b000782090095a110714032034109032140c010000060310b441040d00c80074428502c01220850b05007403440d43d00994259910b040e0b0058204165111011903009800758003200c2c06540d00078582551100005020f50359500a03501035952846000040740c4282808240380c40304e205140da82ca500d50703003001d01040070084090070 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 407459100 1250 407457850 407457863
    0x3070c0303051b1009050f060c09010c1713080105090d080121050f01060510020601050904080c0f0d120c030203040f021c0c0608191a090a09060207051005091506040504 74
    0x10f001101c40074050704800b0402d01800107480065420041d240103400c4414107203d610800c14401901558000c5c0c0d00c2d008424a0b100090404d149084da00c024a40301039000c484074042507140c0c05280104008055820f880b0082201c0eaa80c0401036554028200080b0040b80302c0c14010b000c0501211a007080c18000e10383d1000801d0050744c4d87e6490401c10341014100b9035075525050049140c01404003500007010301c01040a5410070300021143d00380504010b10b001c0b000944182c510505103c54180415048261545480d5624000e0103001441040543d214078003030301403100a000e4801c3e00e0060b0b0f0445030903412801c00d44c0c00d104120516482c0c8142c900307082103002000032541034242d00a07000960707403407800c0d05041c10940841341c840442001010300b4807481388030500002450a0b0042c5003210380c001e542d04e07a42c110100030b01d54280050b002c02d000240d201e0a10400045030b20751049801d004124603502d400f5510b0310b5200c002c80340d1050548101c042800c518258111a410600800c07 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 407460350 1250 407459100 407459137
    0x30b040b1e040c0f02060a18020d05071410090909061806020d0b1f03050601050417150709060c0b06010512090a03030b0621040516080a0c0803070c030305 68
    0x2000101500901071245900703400000e6005000d0900d0b015182c600d2940382010ba41002003a60044d48480c0010844024907584a10000c04103040c50b41ca05007c03500503101400c1d80300142030080e00d41301c0b58003d80400e0407402132040402e0910421031015000955150607816041c429580040c1080c000160360703090726600d9200e0880b03129000c0c90200c030303c00c0740300503a28041400d0a409484001000c14820044240f03c1072a1b068014080115005285000600340d900c01c0c0050f5428000ea400003201d43e012110700a12000700060311000f460b1000300c0301e5520742d4490108881c001c2e210300032800020007840030b80e00010499036205402c120141001800d0040d00443c81018010803508944154020340090051540503c00c612888009448003460070501e8540460340f003040d44e248d103041c0036031100000c0c24402c052140f500b00310140c0c00d50b41021a4ac420407036560348003d00c0309841504940c000002c203a00008125101c4c3d546c00309080003414559101038820350400c0074071818029018 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 407461600 1250 407460350 407460371
    0x411060a120501050a061202070c08031603090e0c1219020f0703080f04050c12030c0a050c0907020313060c03030e120a09051e040c1b0804151b03030b04 67
    0x8000380024480503940c1090500c10509010160303041a0b1016000300a04035041c050541c2c8071303e00c44200911980c02694546051500300625082a44060700b07500001c18041601a041c00014628034081d43da404001c903150b410103c4010020f41d0201c0020500704811180b140d0060f0200f50300401c0d07292402410100d40034000c007640c1c0300d251001c00c10400040e4440c10035412403900360700107580d9030301d00000749841c0d6a99a0b42d090030070007580c0b062005441c0000c4c420000c104685c401050003094584e10201450072130769441101000d03e2051a018001525151000003a0340301040b040512152947c82e15006960307410350074006604140c0c5850800984903c01c202e40000d005031003056540d00c0c0080315000b405010a41c000c2846400414120429801c45003c030109002007202c0008403d117040070141d402031071144240c444085d110351848240300e070740f1000d0300894003040e446c10300c0c448900d9070440f1449918041490316601103006403000ca44290b01c04071540a02400c0016260b054 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 407462850 1250 407461600 407461609
    0xe01020a0807060903030c02061302060903100e0a14190209060a1205070f050406060e13140f040b070c1a0901150f050a050402091005090d021003020a08010e090a0b0411 74
    0x81003c1d110700d80c8450020080580c14450103400742e036503202502c2039050864080c0850501010041c1c846d580114402010365000c0c07091441407591030104100c0000000507064680103091010b545401000b00c00d0034046901003610a00b64415201c18442409103501300101e008002d4420340e04100002d9010541c02c18078a0703891900f5020b81e00030132840b03141c003e20b460710900360742210f40194202001002002c1d001842d00078006800c4861300c0c0c1c180e051000f60401000c0a900201030f01d0700d09028080c038507212000c00c500580c021900b1108a40c1e50190544070540c0300300c001000541107032903601c00c0c03e4a501c034458000e00c4420000c10606150040240b11440c00d0b00483e2261841813010403062410300300744802084203480550030640c1d101c00240401c0580e070040d00c14000005042e24156403032000341d140781c99005021541d1985c030160010001c3d0042c401c3c0c0004a10124004140100011130b101e200c2d82c401c0b0300a0081815035500d222a80001400841d2034a01c81d00c07103605550348 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 407464100 1250 407462850 407462857
    0x12030212070e04061e0b0f0c070b0a090f120809040e0304092c151b040e0708060307081b06040807120506010b0406090b0f0c070e09010b1e010e01020a08 67
    0x120380c0d00d0001100e0b01c04104012a000c0354005108510000792131510305900000b880c044441801078592a07901c02c036803082c254410303401341140d2030103108008102121218003522020a1720b659203141681c0380c409150040000b80102446800121507240c00194000014589242c3c041c0c4045401c0030f000c4051441c3d50400c1e08400c2e955034a904c1080011140c40542d85c3c1c01901074101141042008003007140c0b52940701501101d107050080014025102c1c40102110410000c01da0340d41e5141c0e00e9200c404080b506984010001c3c6118002c20160b280029184003a10004070103002d40f1101c1c0e060030f20711294000d5203c1d8114206010000d400b070010300240f0024a1415103245a240c524501142086816008414540c900f84400e1004950003640d8a0544000d040501c2c0c1c1d07641242814140340c000c98022042c588105603002c00c1c4010300d1a409409815980001c1c02103485120401a420501c815911080e410b00c1020200301e601c01c60403540d4694040c01600c901030b40d9a00c41402da540f = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 407465350 1250 407464100 407464111
    0x1051905040302070b18090a020a03180c0509130b0406050f152d0303120103110604031a0c19210207030c08090f0303161203060308030a09060e0d031b0503060d12030212 74
    0x127034082403010989415010352100480c1141300850b0030310641c0c3e208000304005015050052102c180041c5584401540b400d030040c0d00640080780f00c0c5040e00e8003d010346000c030384e9140080807032400300b100303c0d00511903603845046c01499020140c0c043c21040502030480d07011080e060130300141a41107510288014218140085601e0443e9030540c1402e403860007140b202207000700030411081000c103071010355400e40700c1440a000091611307641c2d02c082081c0a1a0b02039510103c03544440080303c3d8000c1c0140520141c3c8001c2c40000d500d0b01803a0400f00d001743c030000b4000c110026010400a4415801007100c100000e1441c4850a4824046491074201001042c580d82000c8810000d0140040c00c00340e00011074902844418110b5450f5030560002414220203c0e07202c03454201040000d812801c1110114011104072070b641d11030007005003036a0121614060300c4400648141341c0f042049903c80c0e0005001031a83c10244d5131940f41c010f080141000070584d090000c101c041d10b9441d802800390 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 407466600 1250 407465350 407465371
    0x80403080726011d06060712120216030e1909110415081812160609021009050a080d080105060f0403050304090e0613150b010e0a0801051905040302070b1809 69
    0x10360501a41e0100d01c000a941c045000c40759900b0417070142d440c201150401503001d03004446580b000313201a02d0600f4541c4000910a0002c070b00001e210914a001d41c1c070303260107607642e55480900c6805010002d400c00da104448106810410703c04244542c010902e0404403e041d42c1c5010f6441900d8100c03c2e09251b0304c1e0740042d01040900c40780755101c2c45286242e0050030082d200f0385d507168002c902148101403205d0250045081120203004c1213500c01e50b82150090042059800d0903030b00203107400006d008861040116800201e10114001201c0b403445075561610485a400e00342000050340090100380d00c00c00c0204004000103505001400091122000c003040c080340004c1d900c3d0400030001c04036181081c44002580c0424100992143c296805010010fa105031001c0100d5040840e000305a800542e2503400003024141580070a1117103440e4503a00c0c1d0785800740d402c0c0c20152041640c001d030040e4400e500900040142d000280308890044d2000d42d0204414804030304a844212402c8184 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 407467850 1250 407466600 407466677
    0x8100911042409140f010c0317100501030f14060613031203020a0909020c0a03110a0b0108060603010513051f2d0e070b1e04080f0d02150105010804030807 68
    0x54076081000c00004e000e140e0344050382041007801050b00c00501c492002c0c10049040da82c0b905060243e0100c004100c20302c03008a00529000203008043c07455885070a00203858030034072a807150745c07500c01d050f201d17180a0b0607100d2a460780e80800c0400e0300700d40000500d404100d10300100143d406402c00300030b550a134030050707280c124542004e416810290b0056540a00401c6803282d088804142019107640c5801d00b00c00b55503220082e1403410729018001008240f00720004a5103800010310244035900440c003d10083d44d4620f0344070320200e1854030040095014420f4858075000011440d031880008080009150b80c0b00b5048030f100c46441c0981e13840141450030700209120031400750007102d0b480003008011092405442c81800c1c03040035480000480d98646042c591190141150007d01824088882c8000c0381c0651640700c61680000c0d41c013501c51242071082005440d01c80741c1c1220070507115000300b50380d6500c0c281e8214000a14000c1000913908040000900a80c0492a031156000827400d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 407469100 1250 407467850 407467919
    0x30628080d050c061602010e0109080d0f020c1f0b0a0b0a0801080c01090302040b040b060a09140102060601080604020d110310031e050c010c0303180f02010e010810091104 75
    0x8142144018800b0008208202c00c5407100000301d031a005113400c0d0700310002c040059002c03070040c903103121586080d508207a50b0100703210045000d0550880e4001c4200941c1c80c0c500c4100c3d0817403154900d480c00030f0f00001003514141d401140000744428480303801040150f9940b0020f00c00726242d40249000c84008900a2030503a8001702090141807500c000b40303010711901001802c60780d060301c0000e101380c1d102e0000701260745560300102c4068001401150b1184042040075120350064020f802d1690103204032a00250b20000782c05000c0d24041e12842066124601400040c2d84003401c06e19040fa20381800014409811004510902e41c13071755154003040c213502c2e10391a03240220b940010120754180c02d05c004200c0126140c10040e000b401c0c4014414080e26096015040b0075114410b0040740f80d094a090003044005140c40b180b0136a94510303016100da00544030011700741c2d0b040d40740355000003060115281640c0040d800452a0030b80a0034265641e201417402901d00034113030200b011803a0307140d2 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 407470350 1250 407469100 407469103
    0xf02010c09030b0c09010216080f0f03070804030609050f1002030901060603051b0a090f03060b041107230a0f060b010e120a060b01051c2909060603062808 68
    0x150014060700e4101072075031550301c2c0c0d080b4080001e010440341400001d641901680204000c5850800c03211420140680d24040c543d114036458000140034002c6c01a108100c3e54044115084207500c030780410308003815901d8001c001c00c6080b02c220703080c2c4a09040348105030300c10410b8010b0450b64500c096540d2401c0030060303003036440d0303544414185800c0c0020f200d1040950707442c03501804d560344c4090341c0342c0320309803011280b00d402d40c2e00140c02e07504416808010f000140d0003210b030102c400c0e01d06002d0756488910031202d507c10000098840304683c10102441210403080030241d000d54000c0320b50107201500c50aa0350354404004903501540c0b0f10f440003503544c2081d8401d4601004540c003000942400b000151203546000c4010070b0140c0d24596445541c2c0240143d0b903200c041c003580c1c00c0d00b81c000060030900070881c0c61280310003460ba009080790303a6400c806284001c2c100c003400100325520b070300c010b020a41d000a030000341e1040d8002260700200c041d080c803d680a0845000d4515030390314151409 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 407471600 1250 407470350 407470361
    0x3040807061a0a05040e06040602090102010209090c041508071b051f060806010506041203180312020a0b0906010506040905131406070f1706091e07120b030d090303050307090e070f0201 81
    0x607011700d040000059501801080c0340340d020b03401200169584c22003000407070081c46800f09481d03010b0100024405003052001c05403043da035641401d00b16100d414142514850000c80e214400604102c5620490360403400707a068030b0900c240102c45002e0740c50740761050700001c000f151102ea19500c90082045031410449a0700402041e80c0c42d5141c1401e0407210f80da66009581c0c0a41800990801c01c036000002c0d407966001540c000107500380c06440c5400094941080890130354100700c0304004079003c03d0340840c6440c12148010038061601d45459030000241400a060541c92500710b842280451075900031040140e0101c0d001d881940b03004400a05241400307401c5400b005587c035940404488030a120741c0e013015044400d2211070b41c4141b0311400380303801403010b9510840d440c42488600340d00846030298154554809111080c012001d0541e11300b0b10512040000d9610034040022a016400079600b2049501d4400c10140d2942c0c0b045440600503142c4030001003400c0c0608400a0f8280b007103 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 407472850 1250 407471600 407471609
    0xf11010e0c0118060f0813170306030114151e04061d09010506010504180e2a061309201206040b0f0f0907030e070807080d050c0d0503040807061a0a 65
    0x2981111400d25800605508040303640c00305100d18200450320500c2d00d0381d00328021550003203035007a05000e00c3c0350000545c0c008ad41d00358029800e000c00a4000300f100f20042e44184c1c18500d100f90340c10405000c00195092290740f82c0390501d07280e56100d1094985006e4200500f8422442d18460b1584600354500124001c002c001d5992400d010301840b681c0c484225011210031481e2901a5131081d517403071b00100b401d0f03000c0402d2403086003240030940043c03050b044d20000d40720b0507400381403200ba81444094490074a5102030380761720f60024001c841c19a88501c100380021522690002c40503d00301901d680315001401e15900c00e2810058246081c0c0504803400d202901c010780c1c18004100480e18190f10b2518407441000707000000740082d4804d03840200005451400c50740d845a680b041e01d40ca0b0b030102d002d005c0442c0618141050b286004100300c40ca04039070b550042070107006100040310345070030107841111201000c10a101c00300701c05000d01d42c0016028040c01103a82007280412205020b590312 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 407474100 1250 407472850 407472887
    0x1109150108063d051e090109091a09240409060e060f010305070b07031b030210060902071a09070312090515030601020c041109090c090402040806010806070e0f010f11010e0c01 77
    0x8104507902c26005c0b5034000c0340040086515014400f0040e10032158603000001028070788034403604801c0030070704000d034002825648001c0d0b80c3c0b0303025824040312a846403403c80c44a001e4503609911300340f551208e00c80d117005200c0041d200d1400d0a032123007010829102140c41c58540c200502c28031809201002c01001e181400c18504092a60040c1c0180b03058111009801d40694418003458024041e03014580342c0c140c401c0001c6500c60744e149000750030404042d0f4030340484c5c00318403a5090b50303008100e000d00f400d00000d000183c9142c1c4c5800103e560361010a04014001d03100007040c0c0c8410400d6000245030810f01d035160b16140300020b2900900c0e000c0346219078240745d848021748a160017140c0d4041e00607030380920341d50b90301c504030074407841512800ca42180c40068001041d4001249082c1030718560000c0c0e40d00da440741c4200f00c3c4c81d0000f08a038242e0103101c0b926000074545c02000403a161406c1c0f803c02402c01190700720a031313007100c0408560100d00e4005559046d41d40d80e114009000c00f581c0e207038 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 407475350 1250 407474100 407474107
    0x180b04170f0d170910020c0123010f05130b040212160206060a090f09140304031b050a05040203060f030d0e180115030510080f0a1109150108063d05 65
    0x140000e115800c1c000301c1c1c50f110b900400200e40350081c28440c0704013803040800c05642d140100c0c4821030080003060324007940601003481d81c04e0269140b040060480708003050180d111401c0c84200a16100320030189400c156456282d20300680311070001c0c00e084400f00102055602e003050032500c04803260300c2c01804540000b030030010103a542c0d82e846820f84584680c0050902000c84d0b002005000099010300b100c004140340c0c1000100000041041c2c0340325244140b0b08075180e84100c00114000d004043d0300548040d030611050070141d018580c03050000702020384051507400420b003040369405040e0000345013002040c4a605007003400301c4e00610384124500c490342c5030401d2507a003c41940c00081c01c060701c900202d201c0342c003c09810005400c2100c281c614003444c158445540e001207060482c0e0505003a034494050740f405400c046d100d51045680600f0403040a001100c411000902069101500000402c11031609050500b01450308a11000101601c8644081074061a080580c1000000c1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 407476600 1250 407475350 407475373
    0xb030a03081603060b03090703030e010206040302151b16061107020a360606081806040f061e020702120309030a080d090b07020a03111b01180b04170f 66
    0xc05952051150700100e0030000d00b402c044025140580c4005900b00c00401480f8140f400440c204d400c480c402d4a884d1100c5410100680e1141c13403c81d009009604002903240104202034685948003802484060203282072030000b55064101d407145030030740e0003080c641c6001c020042c4181c06071844400040d904007810360740051310b000c41c1809119506c0401c00304000003005407036816885c0b0440300c21880c0000c015207180d1030040280303104200001d0301000c04541410300c80c4e40c440c201103084001501c1a9076454403130b001400c00d4407038103c1c0c04c160f60b0b00c00c07006100c0301c003984941c114011110150b6164130703500402c81f00750007661400e85160020030a490140e900003607048049a40306104a0b154441008078070b004000450014114076901c03410043d030660301082c007a102c00d120340c6440d106080c0e0030000381ea0f01d8400d00248840d40d08003c07c145540d6001d071421601e8444212841c4c140c2549420011042d50020b61102250503400c5007100c482c48404c1c070001d42c00078a194010018540030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 407477850 1250 407476600 407476607
    0x1605010e0f19020f06040b190207060c1703060111010608160519361413150f0902030a0c0314030712030b0f0a15020f0f0309060f120403050304060b030a03 68
    0x49002c000e1107000e842045101d5500d8103005d643c000c0001001e00354448c034040001c2e01414560780020001801440310214405000f070303c507102c1a41d00000000305550401000c41c2c84d6500117030401741480445c110051003ca000d009880140c45030708080d00d84103480c013030188900100c503005944501082d01d1800a696682030402080721a240200c188004440903074000082a4054007011074541e0000400f0400307194005a00620307441407030002c0c55854070301e410401014110f004103150944c002010fa8040b05400c441c1d00f0161b05000098941e1090380000e2403c14594011129114203110400c14402900c0b003c1c10412610300141d454403015039242ca0134044c200804c6414580da800720510790340c59104c40381d54400b00140200c1c50254403401c1742d1711030300c9411341034000604c2041c604011600c800f2034a1050004204002c40c00c01013010304000d000d4020326608500d500050060407640c50040752581c3c05140242c581c1070740c03402c241c2030010036105008a030a0203a8400b54818001a070b1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 407479100 1250 407477850 407477893
    0x180c030501030206190507060204080601030209060409120807110106031b12080307120615020a060c05130e13080d0605030111070f02210a080c0d11070306111605010e0f 74
    0x4009044044408070300b1426211801644005000340c0e10108000c02c212f0400240c0c503058034001ca40c410450ba540d60704001c1500d40c0302070001c00040e4443d24009a00703004014080c1c012003075080c03090042040b020a40c1c211910303a030065480c2810304001ca103414000180038005010138071a07684041100c0e440390482d500c00506414200008606c0c9540c450650380d01c40d5010b09000c00b43d4207644400418005d50341e006c1c1590607941c42d841c00350640744040c001d4040f1014044502007490745145441940081c040c03004128008520014980c00d002032402c1000780f81a0508000001d481ea0804040c1130031181048242c0e819a0300c1080090085401d420300d4148003981102c00c1500460b0551005840444520040d0f84500c01c00b0a0f80041011010140400c440700b501140c00070206800704a030302c400072445a001c00d0304060024008034026030446180b04041c46c00b0300b031410503852070703800905a00b4401561240d56400404003990011310442128040840c0102601c0c1e078612029020800d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 407480350 1250 407479100 407479117
    0x9120503071d0a03020409062013090e0312040c031104060609091a0a0b09040f02042103020f1e10061a090d0c0b120f040302060c0a03090c180c030501030206 69
    0x941c030301c907242c88aa55282141c8040c0da03020f1b0080c013030740e045464084090b18180442046682e00b002202a03400310070010307903640007004070044003180d10f03010300724004080c0c48045007424003041114030340031284410010f000b2032081891200c8140b031800c10701c03080e44205844512403410b2003410010641e1009140c000d6411040740065281c00c018600c3e80042e1090105a03001018034000003548400403014000b00481650140a03c4843c003102100300c0c403031030107100a0008444042201581c004084a1400c3d1090044406850a4000c4030307252001d402c1e00d1b03140d80c1d090281103515141c0c06111150300c0441440b01880303894144100da6540d0850403504603034078034011580aa0f0703541c9156900110075000b03540000f241d03450f00801217003903000218850003840030001083c0001d1000201900c01d80e00350b0b001d44140e86038100c0b5101694001c2d0f100b45c00f0503445008050224044d0389400c002049201d4101026130211141c5105541c0442000b4007450714100042015880d034800301c1c0e0940 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 407481600 1250 407480350 407480387
    0xe0c0a0809190b01090f0212040809060d0906020403120f02070b0d021b010605030d020619050604090503031609050a060504120519030201020d060e15151c0912050307 73
    0x740d440d044842d103082800080030300b00564540c0401c0c1030040480318181654403030305041c01030b074100510082c141e00c609081d071a5101d100a0009011600c003c001e000405001800709240a07104091340c000c7e1240b02c4000c1d90583d43c0090208100300b0241c000801035002410308415807511610069150b47c0c4600c07030703442d407840c00240300c006a166940c101c4071200f254182d1000100f5018141c14001e003024040c4500911840c101452500d00000d5007910a803a042c46910702e0000d03165001005c0c0c40094400c6800540301c0c1803c500094041c00030b10b12a0559001e03d95005561700d40007041001d21381c0c03029004a10b140b209103e1107910000312410754080100140d400030152900038a480d80c0c1c2011903210001c200d0041041550640050289540450060102580700e42604a01800035554103215603085003034150681030015241282d042139149150422582101c60030070040d0702a400c0b500550788a180750200000b000d000c02c031203103091074642c1c11450700c46400780108580300e4569522 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 407482850 1250 407481600 407481617
    0xa09021e01031107060608240a15030204020c16090c0e1e12070306140c0901030c020109051e1209032508120a03050a092001021203010b0406090e0c0a 66
    0x7039000c0e8002400783c1011105090391402c4505041c0020441402a11154000e090344003246d840700f19901c2000102036104184647c9a0320801401800070356012065807640030030002c0565594401340c03034031548030380c0904400380220300303980c0f81c0b00c3c0c8541003454290f20f4840c00714009503002c4600c01001805586501c1c2c3d01c001c11080c9446445954180c40d400500b849071b4134840c2001259400403284100c0e4140a121160444100d00700e070b0071540700c403507110140309240e031542c46a00181005c40a03800001200e02150f110681401d80d6500303c95143c800c040c10340514084104004840e603840c0310305503400c1003000b40c0081d8650142d180003c1ea101d4480e2410180d609441f40c110000703056560445100600e070390340a5066400502e19000464035100002c0c035003c0780c9016003050303213a101082c0b5007042d0303c1c0c160224130741d440b50103154110300c034843c22002003000080080d0301174141c01ea25141c0f5140340c6200100311080a810185042164005108080700000207440f010007160400070318 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 407484100 1250 407482850 407482909
    0x1e060e100e03061302100203030103030e060313150204060e0415060e1201062309060f120c0901030c030c0609030305070f0201030906050a0510080a030203040b0c0703081b060a0902 79
    0x1d08406a4500940c9805040140500c98a108084000320361080e1140780c5101402e110582c0c980c0000d20020b4041110202e00881d2031504d50001c5500400305a20087e40c401a51a056207412580d400518a10703400602440503c0e00100320302d11104040303409024040861104440a940ba44184420300c4440118014169108085507840b80d58540003084410754440c0d00031135020012800a032405011410486181001005244154400740c00c3e800001480414400083d04004111420340201c4080601e5a5243c5513018000d50055100c0ca0003241542040e080c01e02d010352101c810312071040c004000094029099410040e00626000030440310340c00140d024125859006101910707242c108040760445500003801882000780762040781d525428995955404008003401507030052008020418411009020303419504058507141d60340da03960110640c2000c03042c4021a400c1c004240c0d208a070801c60b065001d03805172000e104843d410f4012540820b08003150340e00c2c0b001c07055105035 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 407485350 1250 407484100 407484107
    0x30904020912030c010b040b060c0a032007030f17090a0b09013006080c030316050c030f0d1b1703150a08030901080906060901050d140a03091e060e10 66
    0x8041015010980e83c0c1c484c540c030301c03940c02018041c5500b846540f51001c40c107424281841550200b403104801440c070300e450f94600365189061a0703400c2d419954000800801d03c0c60900c41c0310021446010b8a110100d201e1801412a204411200e41c07114400d100845544c1d4a800010b0b04a4030b4510800d5501d00741d00740100c2e400c00204103100d2804101140f090500d406060311004443c80d0a00c0030840130fa2110700f0591143c032101070659042e40b00f4000c00401d07010407418040c1c05480ba00489071604c2e44000468180402580400c00d90b4100034034103104990811301100408480342d100d0850140c4942ea0003400c04038545801c0180580400012164050001d40010740d0f4801069002055520800b1550360f601502e00e42c0e00262159000c60188000003900e58000c2c500185504c40c070f41e09100601403414480401590034180050246080c68030500242c180d150103540c030b84030728500300080c00711001504007030b0003030300b0261900401ca00c5502400e5410a500e08444048000300d4080044 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 407486600 1250 407485350 407485369
    0x302060126070b07060c0801050a23030f0313150203031305030c01060b040501120504021e01022e05060910090b0d05030409020c010c0c0c09050c0d020703090e060307080309040209 79
    0x50801c2c0b14401e40480d64544200291a04500c00c080600c104003030804100d4507a9800e2080300e0b0032507030741507080c4001031040d602d1a03c031549080c2c1c4040f41c00d04000000b4030381060050208143e40000075030402c040c8840c01900c000d89040702110003441e8401c1002541da110007004014088003544040381040404e00846244591010090000c180c681c5000a05036119200341d0303011412140813600b020515000d03a40c4640e800a045120071000065815443c101d0a100b65046005031031100200c80616402640c4400380150102d41410003842a20110b0b180079040c1031107034909500300f0510103440c10b003510036a84413003800700d81441d040c008600c1d000581d080c01841350001240201c1c3c040c03030a46c0035000c2c001c0700f40001e002004103028117640410b80d200000d85a944044001d00c0541e515401c071903000300601040620b031200c050000802ca0300040011800501c1000042080441e19004213030003410480141452603d0828407a03501d02c510004940166004200740c1415503030350002 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 407487850 1250 407486600 407486669
    0xd090603020a03020903160e09070b0301051513090209030c01080108030d0b1504060206040605010501030204060207060503101a090f040c0507020111070803031008190804030305160c08070608090a03020601 90
    0x1b00e4182032042c1914405801450180488c20401c11b0f0020746802d00000b1548222a20f082006107140d09000910201d40443c42d0105503001041105880115408103080020082c8240050311081103104240c100340c080c4101c981001142030051150b180044102d4281d07440c113450010740340c03000742c5c0811003401e012a81000060000324000031595004501540702d544a840100a1a030301c610054080380103a005400040e40300e05003e001040c011401140c202c3c94688048203065995401c0c212005407104007018404c0000c100980e850030b04080580c043e45080310244260020020000c06a019200c03004c1d04000d011180150140b4080c0086c1d406841c22030b040d25600d181c082d580d10001c0c0d030700d4030440e00c191040a01c880600316484141c40c90781030744003039218a80b03840c6460844080d0001441c443c041103499058400165042c4001401888a5000391890519100700a0102540240025100c3c3c00015290000075400305889041d07400305c10100da01c082d4040e80036100b0002c00182e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 407489100 1250 407487850 407487853
    0x120b130e0d120612080a050d05101404060b0f090612040f0209070e061215040c0e031002130e04050313080705090610020715230d06080d090603020a03020903 69
    0x1a40190040c080342000c00707281c0341e48815541c03400b1030942c0710407203550f481190310584040203601d0000f402000100384070300036881c040d41044da0300c0c1c00240807103c4c01e80d41e603c030815500c08200540c5042000700000810100c1c2c1c10804945030400c00a1140f0485c07040c01041800020404516607a030800d80b507007405c510410b40380510385413920b801d54040c0d01d102644141d500e900018441d602c5165810309241e0050002400d0443e44a02100450300c09410042000ca4259030541c85485a02c08e50b112040c01d40d4031030134032a01070782c241400e100020b00e0303280115004000c02d04041e00d0400c1e48808407207014040c0c4070a030b030b99810820304500511203c0151b685906400051100c8009111029580100c604c00290344401c010002691052065000503801c06a0304121240a900b03042480288038103012080540c0c08004080205040340401d1000c02c0101e40303452207011610070391015050030001400c00124010b406040c6c040b0a01c140810960002144035050348a038058400d080030280 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 407490350 1250 407489100 407489111
    0x50a030e150a060b040b070308131a1005030a1709061c0b040c1e08040305090a06051e0a020312072c01030e010c2106080708030a020c0301020a120b13 66
    0x100010403080103480e1440c105040c40f801189040035a4101c5044440d102c10325883c2c10b090359016126000700608120030326003441d01301000304140c642c2d5040140703080d400c03110041c0740482011400070a0b5411060190b4010005403002400c86e000d440c059440003000981c8521030759001980501c0b544c56004160090b20f0101d00240c680ca03002000c2450b0201c605004030124804100c42803240c02e0010404692041c442410780c5000340032a5420038040c0c90590701e4601803a0104240341055442900000c0c000070b11060007000c0c4250300049085880b6002d4134019810900075500d004040c252418500e1103804141150f001d07041c0c01c540c002c80d103269528007201045561a1450381e10004501082c100301c00698001418810342250f919152198031074905006200ca45024495501c0200d50b9078404010038441410040701c001801c508005682e0f071001110300a00300200c805125002e68010b018210b1032540140d40c1c000c001842c2d080c00518921080e0000390362650402d1181461842c04 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 407491600 1250 407490350 407490373
    0x1806060e181b190e03010c0c061509151409041a07050c0a1a1015030f0b06030a0506030d020d02070501111606090623070303020903030d18021003020306030607050a030e 74
    0x10300c14003446200e5440301000b00240d4802d041c02e031f072400b600b850000343c94444100e0000f0700941c000c11034404580c0c548110540c0350480c84084a0300c001081c02824422170b4100301d6030004440e003c4441c003065644540504145d03940501210201241c504140090400500c003503200700e040e15804c91007132084654035542410400794101d0215002c0050204a000160142a11000b004110b84100c5e09445944410b20713002c40082480301c2406000300e803500c20011942d0b892401942c000c0d0055140040c1600b0300e24101803400101066203001c0d5080000b0242845030042401c00444800b030a045881c014410350150410211030042c0c118003000c140301041c440da001d181c03201966110344031185080d00f446c80c1c2031440c6107454500802c1d40c100b0403030400000c4c465000380150020207001c03607007004460584071007504c1c00f9076a01c0040c030309191100c00035880d0080a1864128250a08501e5400d00381c020944405c801804c0d0003e0202c00241d4140d014400c1d403200700c41d43c001c20b069600140c0c02 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 407492850 1250 407491600 407491627
    0x1050702190e0f07051306030b03010617030d06061e08040f050f0d140c061521100c030b010e0d02060f0406080103110402043b011806060e181b 63
    0x241c4090f006070124500160206008400f2940040035010900084500e402d10490240c0481c00020f509035485550005070070700c000d600b080c07146610502450300d40c201d0a00351422600d0b6a40320008110520b5103c0381c0300700700c1c1019400407189a1411900a0b61103090032804021030032401006880780341903800460300040350440d80e40600341d80312030401c9441d03542203550740154210040301d500502d0118100310400c07003508050070000380c01c0130b201c102486800c401d1035507035200c44060b5810452140c0c070380300910b00ca41001c505241c1410807800041e01c1c0020100700b0040c2819000d03004000ca20303419542c0c1c8500781d80d0350040c041c00c0c55513100d48642c0000c04401c02072000b160440314000c5000300b01c0c070f001c0c020b480076500c24006d407a03102d030031510140c0d46151189071298030740a6003686400c066800b5030b0322940a050800c00089070101010040c60849045a201000b00150b40c503c1c00309070ba403015102001010310316100c000e207440c0d14100024103440200c0a0203074840004035190304411 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 407494100 1250 407492850 407492879
    0x40c122306090c06040b0414030c06070311062a0307020a020603011203080a05041703180604030504240e10110106080f100b011407080d053903060105070219 69
    0xd0b101518507603100c1400740329403400703a0701600e00d00d50014407050001c980302c21000e1004130b80040444014002840200722103510400c0d0590014014041840c0e1000c400c101e46604004a1100c2014902c400070904c1e50b50440310200c1c5000a0000021582d003a00c01c020750424036800425255403075960325400b281c0d50081c0c0d0000c6000c15a030800141d0406204c0c4589846107030842c13012603840d0303170703038514010241e10040042c1c41401c1040c03c80406440700b086254400c0d440394a840d03603102d00744250382c5110364801107510759035513410b4610801e440c1d0111914081d004217954101d044088010151041c0c00c040c0c552039140d618001000502100000b924408001140300b40c40701030484070301f094251074400001c1404103c66034105860b10640d14001c0c024280156421418041c28443c3e44054402c15149180022080e0302c614500c008051a01040c00481c50845081700140c12040c4c03c03503010013030202d0b05100003c58140250748500700c00c07850034500310303050126040c3c4612400102d4503 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 407495350 1250 407494100 407494111
    0x30f050109020a0905120d110a05010e03030109050c2803020403021c03030b060c0d0e010504090f1a030f0a02191505070302100e0a12030608010c03021c05040c122306 73
    0x2801d0280008080c200000d03085507000c0000c014003187d0441a206840c3d02c0420301c4041c099100e103480c4040401c4003803098051881170207002d55901c1d403506001c0015503101400000c8403110070004d42081c40011400e54100c14914800c00304c0031805048290300a0155920280d001000140240602d05a400721702000b140700391010000c0701981c9050040d140285e250040c800d03405000140741c018003c1c10564100398052524601d06a2154078585c00d50310b140710001100303501c85140c00b80e000341072800440c0384030095000706809014203070781550b2403900036070190180d0080c00742412088032103407803c006440010881602144a8640140590701c251000e500501588030826440c2209000d01d1420383c20003001005d552030207448101a51a04003004414150744a4001880c21402c0c00399041c2c0c0003568034016110105004000c2c49041c010101c5444a80b80108010025028500300300030f0b641d88651190410203240b42000d6a002d40d00c80e8081d541c60b40c01c241030861a40000c5032031154 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 407496600 1250 407495350 407495357
    0x1605041a0d0614131a0406060f0f05030702250512030706050919020405150901140405100501050a14090307180e06040b130222020307080f0c0d0b01030f050109020a 72
    0xb6652540202c003500355024450354005040011110700d88155000030700440b80c0029a010b500041c0400039044407695842100800c038036103010100c0381d0b040150712000030914180780c0d29500c0c292800035240c203141070507000c2415a10140c1da106002512407035003d05400340c500b4000b08101a02e2035034a400051084819a082000041e212a000300c2d1080705002c00b01280b0544010341d13400c200140000602c40b80c1400302d0300750045500d41e50688064000d00100030204280345940003070105841c00144103401e9440c10700070810090760710030115102c8505518200e11900c020032503580c164400c2f40500d0354141310b460340c0416140c03050b0005900c01c54461208010342041216070307940b0b49500b200e002d04010070090000d607070303407408046688150b807008141d44000d4041c0d118a0886c680310710100c425483c0e0100c2048500317908901c5082c0c0014000041041618003690044118070070003109501080e110140002140d0180d00000380082c01048240980d42c2c540d00030310b000b504690350b01e9001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 407497850 1250 407496600 407496611
    0xd090c170a0302060403030203070c0f0b16030522141c031a0d150b0604080109020f01021516050405030319121515051e03090105100e1605041a0d 64
    0xc254005070806100d507168003e021141e4071034034160029023009240000b071260082040c0001460f0348220500a4401c41c003c4c0c4040c288022001e03041c03a0341502807414545444280450896a41c01c0480c43e0b406103044007515241600d00b114103080c9003400300005105031005403000035031010411009403000d079800c00c110102401410705100da0a500700303401500140700c02000c555400c040c0244041196404140c0d41102c60200d40d140c1e0069100240607550b40c0442d4046140a14120004100034401801c02c203a0100c0d94021044000c0c240c54050307003c0a1540401e54010030a55000701001400c0d25180e1311200b0481140890300141d40000071070208070001c2e500d1180c440d600d00c007016034109942803401c1c85040b462008200113a201805014484118a02580050800d1072203040700c000740c0fa810421282c41c2034030400b8190210030440c1c04007e00a004003010042d60100031404801c210324103c0c80f0994442c0304e03640080701003480140320100c3c8200c0740d034018a4071040145c000c100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 407499100 1250 407497850 407497889
    0x301031419032c03070e01051503010e15031005040302030310080d05041e0503030f041502010c0503060402070f02130e060c031b0d020d02070b060f0f01020304051002030d090c 77
    0xd8921950034002c0c081401402200000d15810800d10003066103092411560004000002d103071102581c401d80c000c01c42d81c0014405400d000000d000c2c1c0007500c2c08903506650405074002d4039001c005144540c4103804440309081564204045a00d5030420351080129003000c1c28001c2d12580101c4401c100180a03d00000384118009420b061003c069901c42d814507040c02035032001c03800e5840119a1411a80201091554044c03004103007080701440c4843d9580c0c504440c14a0110765030070300200f5a40b43c103142134102d0340c00404980e400b43d812600141d40d0483e9107850002540580c4002c1c0d044090500c0000890401e80c0c04800900c981c60122030039035845113088007890bc400caa14144050070090030103564201640a0610750100341409810a5003000d02c59080780c00844041d01c10b403100c00240179441c10b1001f1400c400354000c0e40c800380b84042001c00270b592441148113540c015694040600c0c003103031083c02070394210110171409025103c0c1c1801d0845401019001c2d080c001e0325030410418 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 407500350 1250 407499100 407499133
    0xf040b0702011803050c010c02120712031107030b01030f0f060e0115140d03111f09020a081603080901020f1605121c1b12110c04020c07030f06020702030303010314 72
    0x3100d505c000146403100546004550050100728100e03000100c1c0901d21a8020040c454600a040d5044061301580300b00c0c100100202d05400f850700c036980010000303002051030705000c541500d402c000c04000b440c03040e181c5102070740d8072850040c01044c500201080301d00f2044d08a450b0340d0043c0c22103d682c00d91035080d0503022030848503c95a00c20645001400040d014541c5101703040c04080507900840c501c440c290b0000600694400310305962404800704503d440111400a40300c03000c01060035080c25802151405101d00002d071910310b0105108005078400c004006694080f1011b03a80707601c0c445c1289c188402c04a01909101c2d0301c2c044c0d403284100000146405c038588100001c1d503410014807100741d4259040380383c1402c00940803d8800c010480c010b9223038540a00f690b44254669003440c400311b01701450500400c0c030490042140d580241400034280382a02d0300b003502480d40107103034503140e00240720700300009401d800048000014454200c1445441c072041c8016903000c20f103001c0d0b151 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 407501600 1250 407500350 407500397
    0x70f080105150316090e010305070807270b0301020d02040e010f120b070513170d11070605041403070909050a03031b0816181710020f03060d080f040b070201 69
    0x6406080c1c0910028604d20304005824800b9909402c28440d01d0340c858007950207a81003600282c0c0e641c1d105040400070b0100c1002440005d09014551803840c9100c0c11041503c600c104010b9105d035a02c031340e02c8440a41d0294100e88200000a00440d0b0f42c2d940c4200c107400c000360921500703032049200840001d1541660303a0490041d98403004010340c90355102030a45058008544101524452820200c1c0030090180703010740c160a16801081d08854400780140340320103039110030142e9003100b0010840140c002050300c00352081003203540c0d21011010003081c5000c50a90001c0e0740c082c28581e41c0300c140200450001000c600954040c40b4082c84040a5007518804504070b01c0001d2060b000200c801c2031802c02c5982c00c0c00240b81441c04460070415010511515800c00040d58000d08200b142c2441c081090545000c0341e20010744c204551081844202d0200800160150381503074406401c11042c501101c1401c10701c244504d498a4a40314441a01e0300503c0049010845481c0307102411200100340 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 407502850 1250 407501600 407501629
    0x11040213030201120b04060b0c0d022803030e01110c0f15040b040203010905152a040603020a02100e06070e040515040e0a05072d0e0c160b070f080105 66
    0x2461440c0c40c560044030508201400d84c1c40d0b1503941c0d034461529030344034000c0800030241d9a0b5030946860040300b0003410044603480031001d544c881c140c40042c1c41038580c5024141d6000c1803843d00310140905064002e010402090034440d444c000710401e083c102c0c80051f05182d00c0b49003c03661121040003e0b1996280c60200120004a89a0001d000140c0158119911500c003030008503003412141e90b05898203c003600c83c920012841400c0000f8940b800380320360f10b0101d51407c0061061488514904544100d0181c401017540000d82c20f00e000d4002c0010a0410b03412000c10041e640c0b071440b599031031b600e05039102c600180c58000b040941d403030030780526405121300c100c207c1883d20765042080003d19240300c03102d040e03005005810011840c00d1164000078500c0802e84500c4000d130440500e2078110140340b01910710080788061000900140480360f10207140a99907079140c0e401381e0301c1c2514821640c00105100b601c0c0d0100584140d01203020107000b5400c1c0c13201c80c04c2d80d80318000c009640021150 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 407504100 1250 407502850 407502877
    0x70b0c0616050903160e090a0b0a1805060103150c0302180f040b04020c0709050714030708150d060c14210a152c01050a03080d14070903110402 63
    0x41030064481c01d910203182045424043e1a0484843c0424100f20419054002c2900c0e0503e04104100e4150394455100d00c2a001804200b20a690390548150001e403045d034260b582c4074002e0030005c08956100450035040b4045035003035a540d203421509401021400300707a8604101d9550421400f80c000c0d200c03c1e2301c10115200c1d00c483c86105000b0148484039900764002e84a0f00c1d24142d03034540d807008000080c2004007070150700d8201060403040d9440039103803600b0846043c000e15801c8a0318030903a030b00a9418a0f140c0c4c0a5103407010103015402240c40000d46c00440030340e20034208450303544580c140c0c0c00c05480384a01120800c0820225004840418080ca09002018260b02400808140e40500030500018507a40c00f10440c0c0c84150290700442100540b0085c2c1c40d91420445030520611604008840d103152304020118940141c0c030300c80100140c6002c00c500580c0d03181900400e800c400002d2040030740389840b52006080200c1441300341d0315003208440340c0500e0b0809000300c9805059020 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 407505350 1250 407504100 407504113
    0x151314160902180a06020102040501020106120305070803100305030307030b10020a03020d140706090506100f1d0c1603230315060703020708060406020a09210204050a09060504050a05070b0c 83
    0x5901c40301a50041400003001150548034071680e5503890550405031006600045e01c0b9810b10001a08459050b003201e00c3c1c181c0c0c40110b9200180c0c1c400200c03045294845001b40d140d4070b56008250404100f5000104a800701008010500b03501d42e000901000b01290f1140b0380407450001640c071030701701c44005801604107904a5a40c5801810b9007004012286989481c01101c2c0c1c43d80c0f001ca038a001c008403450b41001060106148424290b1000761044541d01c0c801d051070400d039003c500030266403034103a541503180042c2048030010142c41c100c40d94452030061031000d40ca401400c440b800c0360301440d100f0100720300c50205108642500e128844503400840300907040020003900b0341165030200c2c1188601d070340100c0c4000050103503501540c8108009070310344e03003080000342a807040340c1c212001c0c43c502d4001e41c09664400d91481421590140d8000510b0340315420044080d211244000e032800f03081405100421400103903c500c05805102682c1100c2d84944c0501c0403440b038105628069400324 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 407506600 1250 407505350 407505359
    0x6030a080a020c031606020c060c10050406060308030a090201140f07020409020312040314010b0f03102004030308190605090414011506050309010f151715131416 71
    0x810007000c203000c850040356690104030340000c0c644800150a00d001e16841201080070b15010002900d440b00110740c1241004014070284d642c40100340c0201e440161981d01240074084030781d122101071901301c0d01055903482c280c260000034003c450303800ca0018051490b8444a04e03951030984203800d00100700d1078548201c60702004003074441203070f040c0da040c05035a0b07100d10502c0451780280001c40c80f512500d9a100754454200b803c603200f9003003050042c441c00d0f800307480c0c60340c010610001d0403c42c40d42c001806450401c91201070160722201258482d800500841030540200255225040403414544880a4200d51005540b603a00c03a040d000a01c41000c140000c0100790600d050012403000050a41d00c1c1100701c4100030140c0c0d10240128200009000814200380a281c280140c010014070142d241c400c00455100c1542c484c41442014220b54060340c205c003403284240d041982c0c84840f210b4241411a096022080c401c01c480708050318081c0c41c400100411a030022602e941881c5401e245003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 407507850 1250 407506600 407506613
    0x10e0306010f03290f041e121d0415050901092c1906060e06011403060607050309040c081906030f11030a021206010828080a09030c031506050906030a 66
    0x944c1c00041d49000c0080c00c00b891103e00c00f480303050340340c42c00291800c1905000d6020705140d02c0000c104002200024042111410381d03401d160b62914244021140003150010326004818a440d4401c2c02d108030894111401d01c00c07003007524000c6900c0021030340e0b0b400b92141240c02c24100e07034215036682500c480c2c0e580c03c04000c50300c1344440c50042c1d404840c0d082c1c3c022120750b00881b40880e07180e40e80e41310600000c010303078090960201c0c0c20f081c21030004440081d50441808003d140c0c41c4514000180d41003002810300135911a14000b61090180700341c40c44c0d016010348011501207a81c109850485a0205803d008050440b6006481c620714661551240d1301040e19014040350988a440300410058640100c0f000c00d01d220000980b00f030f075040000c11410558120700508001964181041e1f00703001c0d0b01c1c0b00751a015031080030303103607280c0550109403420380b2594405000c01c0c0d0b00c1c010000a000300607040e440390022201003000000d842c0e030200804000155030043d0180c0c0000c00c003000103400c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 407509100 1250 407507850 407507873
    0x60603150e060a090e01020304170304020102100e03040504090606080d0504030804090c0c14010b1c0309180608030a030905100c0c1103010605060a050d0f1803120f0905030702010e0306010f03 84
    0x7020f010803a1035600d42c80700900341c41c0e0440c43c0d1002da80d0700100b0070090003464400c940c41ea080d243e402d0783c0b0351701f0030b40c000035900d490310b100e00b2107501d0391462031205100d010000c583c010b1a0160040c4143c2d9500e00b01080240300e103108103a0a0700455200301c160f90b00c50b400f143c00b0350741e000c981e81e4103090030015200000c1004015580602c8640049007012800c1c034030402d0000501840007203480304400051018030303290b90001c0c1e0400b50751210101c00207a0005498821b50f80302c501410782000c6200040c038041d2403140c0c800300640c000040c1840c5503940c95003100e50b08a000748100ca11400d004010300c41100c0f410b21090001803107010054001650340844040342400050000c0707841d40c0c489000400c01d03800082c46201042c4001503800b209040c90142c02008031060300d040101010007440484450b40805005003000000101c81e2400c1c1f6051b4811811201c015504106580040c601240d0701c4c1e2029006a000c80c18604203103185180001d81d00b416554580120301d00c251031030361650010003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 407510350 1250 407509100 407509111
    0x806030709090807060c0e10030203040204090f0b0f07020a080904020901030605031204091103010317030a02130311090f090d140903010c08012c0c071112010c03060603150e 76
    0x1280000034441c20705000b4000e2203402a0103580e40c2d884d903407801c2811100044001d805000070502d4166040d903800710112506401820003503901c0c0c4c0e591002400521b0308c01c000038180807502c3d10040c2032000b044080c0b403248150b84c16005803030311030317400076a07a4001d032100007801d00704c041040d0801d60500e500070782440740041c100410b205843d440003905228100e0007201c5600070128080150304011b01444080c00c8000c001d061955045403140341190401c02c005006074080000490a0401640e04903403260700c0b5041004111501d070718000c0d00c0c0c201924005480f999440c03020480480001a440b030140c001d0f400140120041440103440e41e03280030754800c4002c10140409042078400f8007031020140c0107a52101110741c1449000d80e00c890303c0001107918151002c40f1041c09011001d04990001000100b03652a42050701d0041941003203514010340108442040411644054000c0605403a032520203110481d10b80008070200c0e40304203403c1c0070501c001581040a050b044c2d6500343c121 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 407511600 1250 407510350 407510353
    0xf04140a020907030c0e12030f0906070618030f1817010207050f0a12020613031b0203030c0c101d0409030201060806010803121509060f061c02030a1d0d080603 70
    0x3850a400141d5284012a03441e40800d845850f2001e10541c4080b441c0800c01d000c803100024982e0040d02180d0b240148400803a40c244001440c0d00786079244800c1e80ca03015400302051109101450030035280080da000d003280850726810796121041c2c0504004000005582041c01c5100d180019000525140c90004a2103542c01c203e8000032920901a514200c3c05404c01017001d80c0041c548014641551034112003107401501c03d01c8880741c051b22072610101d402d882e1211042410058040c011800303004002e40c14400040e0f03651703030a100419082d1500000300c0d60404074580300441035852a0074a00003d094601d01c4298a01342d1400d60710507042c1d28013a100000d0003544801c005c82c0780810030b0300414440c2d440400c06081902c54001c1c00c0d0392003101c8015180070000c04e00701003040c615001e00124405c940c0103500b0a241c0d25010b042d0740c5c0814003880c039203c0ba814501034846c001d51096400b0031a140c1410f100c41c10009400080e103019004140c01403080307021207a0100d6488001500b4998075 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 407512850 1250 407511600 407511613
    0x406020f120103020a080a050d080705040e010311150f0d0513020d080c0d03021c0b0d0605011412061e150306040303060e06010305073603050c0a09050f0414 69
    0x100c98800140aa050040516140d07950560041101154107540182c0d0660301000714403000420202d69507841c050b07031307092a0b0440d441c1c203281a034460155800200d5403001d08000001407028400f18080e22420554225102c000b1040e445441c41c4541007846514003400c0103118046880d40e40100d500c1030128062030901e91642c4d00003000110000750513200c010000c0b83c0c0070665902401034041014290070700f1071802010394504c0400e040e01c80440b218850355981032032080d4503034500204209600c2213081040d50307164801c0320401d86080c00c04034050302c201d20700c031644650f0008001c0c1c024409580c0030002c11640320300c00740d0542d034010418420302000802021082d1401c11a040c05580310744ca01052030390400032080c2c00c69000922950400d41004280710034950130104800000642c00c0f0b402c0310386801c0f4500d00c0d02418020200c4800c4c4898110000140003002c03c06100b442821140c6c000c80135990580c0d081925019900341210b2600900030400007000040c02c01401202035069804 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 407514100 1250 407512850 407512867
    0x190309080703020f1b1e01031b030e0c0316090504210f17040b0c2110050405010e0709050d02011403040b0105040605030d09180e190326040308040602 66
    0x600e504820400c80142c1c2c0b0210302c01502507014088000c0a0109079144039103071100000041d13076205071910300031061311001400c1005074825000795011f03610030441c1c1e03040100841f0b07004004050800030301c8064010380b000903545143c00704001558161145040c03410746d00301053784004101c098821100390040143c20300c10f0820130960050456403039190114440100403003d8004400c40e841c1009a241000800000610340704115800824800403103482c0c40d000050041414403000d01000c0410b01002004003420b055400c0c041130f10310507103060001d41d0741d07085090710104080e01d5040104d118108280114180340044076007507401490124402000d0881000380c503031040c1c030b00fa0740c004103031001807003181403e0080d500180320503801480c8a110701c030002407081400740202d41c000d081403c11900400c42ca03401c0083d10000c0c120603294a020300e07104103018540517810440208200c034000102500800c01085603001c888804860165101e81c0c08a4040200920889425500303009009 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 407515350 1250 407514100 407514113
    0x3040f0905070801090212040b10080a050606040e0706090308090616030c110603010b0912160b030a0b06030105180a09140109111c1b0b0d02030f1003020105190309 72
    0x4024581403500240c1400d100400400d03400051300242c00d500d00412951040442e103100c203690082c1c00c000444d410703888601850304d4a4034242d0110b1081e20482ea580c10520001040c0a400340d44111000c00c00d40508032007150300d50742e1034801c0a01082150000301f000c6440380000f00700c00c410040c142d501d81440750304c03212405400a10158006011064140c04101500c501040001d10403204507041d507260101507000d80c807070390146034041c04d0103403010380030008200314104c2c007082c42e80c80490a003074807048521420f4000300c421001250030300440d0f880c00e0a10034101d038181c48014200ca86826000703100c40003c80c202038000009107685440709001300b0f540c044c9400810300c00c000042000c40721741c105221403205001c04a40b00b0501500d4040841c080034402101d8540d01210040343d41e6000000303082007074283ea01080900c000081c5144030314040ea40107600c5950b148556101c9610390502c3c6c03840c84000c5010007404154100110f80e6000044290200b40000514010030346e98490307515078 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 407516600 1250 407515350 407515379
    0x50d03050d060e0a0f0b090105010e03030d0204030308091e06010621050109020406030b1804300201020909090c01080f22082505060103020411120f06090601030c120b01020304 77
    0x110084070030f0800340710300705081d80126401010106014003402800000007081240103206441c10b110600b0403a07001d545040c42a684116048101192566aa403c000d01400c10849000220b0302803c1911268107200307a00400c0c0300003200b0000c010982c00c04209954001070190b082040c1540200c080a145801c0d02403a4041d00c04c40e1400740e2101d2400c17901801b07898135000524803d660b42c4101500c05c001c0d00c1050f640c825000004844107664802c00344200343c0080600c240110a000f48640900d60150001c1008010070380308021241d50f8009140d460314000d0110340d000480034804120415a026042c43e08000d44001084650516501c1c1c0c0f224103008041c1240e04200214056001c01e816141400003952860b00741da28198107903950540383c560500000f841956500c0058100818603416200801d000720031381d0141d41010a00d034410506c0480e0918403071000100091555442030040a65220494032403886800d0380011100c00b428456440300e04510084c400040c2003c840c4411 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 407517850 1250 407516600 407516609
    0x10f0b13080d0216060e1309020103021903050405100501080312060f060705010e0601050901210302030405060d090204050604020c0309091b070812150f0d0201030f0f020c190c050d03050d06 83
    0x1340704924000c80ca95078840641d500c42c2c01840214040e850268403402d0080600807010240001c59243d5440182c0082c000c05558940c98180100c409580b0340c3c0584c80540503c3c058021900321985105140d02560401d010b44a0340d50018000c00303140c5010104e041c0c0c0c200000401c82c219181c03131200420095001940140c4050391210301c072500c0014140201d070f0240c8400d0740c0c03811407981010760104143c482c24201c00b240314135840003030b018580b0074000e4402806005110559a01c01d0b0105d000290080701010387c0300380d2409000c00c2d0280361606c2101d0b44070f40d44001450500c800700c2c040094010000f071424101d01000b5100440042c02e600042086134410058240c40d224555001140414001d20380c0829401c41c1c500100c895803100035040300c03802d0032030701010891500e1004a002d040c004501c82011400c040001d0302c01c80c09030b0080d22480c1d180d4800c4888101300840303110450342000002504000c0359074024003d608001e03021440290190501d00c0c5403000d044108401c40d5083d030310 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 407519100 1250 407517850 407517853
    0x409060e010f1a0604032a1410020a02210a02090a0203040b0709050105070605070c050703050c0112110d180b130209071d09071404030b06090c03010f0b13080d02 71
    0x1041001801a110385645101200304200c1090f00f0100800d500344582d0001904548a82004e0000650091007580011685590320400541d031180380c2e80509485180c11841084030080c1035500d148006003144806030010b2400d14809003900d10706004690b11034045044d8000c140e400005a00c60505d51801444614401a901e14180c14170558041c005010307042000300d5920200f042e680d1081c1512007a98128400050b00d0702c4544043d1454072a00500a225000780e0500005000300800d110030545000c1c0c840e8001d080c0d0540100c400c13551661012030701e01406025032480c40113540c1c0840f1607803100309021170543c8a0740c0c803000c0c01c0d082c045489500070300320b01c0307410b2046080a2030103030b40143c0302d800c2130381300000241003a1020003900000b01c0d010f902d0050000322201c2c4116030310030045048940c0c0943d44c5860b8206031401607005c41d40700d070088400d00e01251242056404a0b8100d803818035000c8107050401c00103003d1030740551000441c80d45883c0010480c00003d11495012549940 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 407520350 1250 407519100 407519111
    0x13020a060906171e04030c05010501090225020d140307060b09090c012a06020c12070f03030b0d0210120b010f0f110109080a0507140109200409060e01 66
    0x104121610815401140070007004400820079250404091140d0300d54900c802007507039481410000702d41d080503035070445002802003030105054029603001d103558007910091201c1d03a00e481500050f03109400142021010b80e012003e4020205e44041d410b00f4402003c071700d001d005035114005005558208111282c0000800f0800c000c40e030310031002c41d00300c00e40c1c0400c01ca103400c40341d00d0745070b9088401841c180b00d00d11985203503070002e4042100c0705448550180c0d0700c8240c5402d02c14000d401c8100b40c0e40796403140b03140318008204043d05889100e60712042ca03100150b8159012000341010401040d00540031a4000d00182d41d00c00401c80c1e16031030b650300c010441e0803100400c1c00b41c0da100700b111070600420032050080a6801141040e0b40140c0d401c01a201703a00050040340101114100505514004101c2001441c0c0c024000c026541c00f40b1141030048440f01d04c003d0032206a10b1008080d10686101912481000000c00710070005c0101b00082081081c0c41c0e801c140c0d15444516640c5940d1034 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 407521600 1250 407520350 407520353
    0xf2102030c04150f14070311030c07061704050604031101020d0906020702090a0506030303070c0809040c020c130608070e131407050a120210050c07230901060203031b0901030e01020313 81
    0x403000703901007201500d400c001c021013041c405826640c0c0d2851a40d00b9000c0013800d0020b150281444049516600040700d5a4500280c0110340700c111a024442c000f4103440c004a00380081030000b1402140c10038050500c2e6140c0b0355080d40c00314100c2c8440760865400b4040e03004003403801d01c00c07207003911701600d07000da5118058810405840310041c20784128034540400e0064076200001035a500c0002420032405171409400c080f41075024074007100c0d503c02c0c00e000d183c5a4946e40419101d034410002d6805100c034440085030380007070b01c405000304a4030b03a1141d0070411880c0000c40d034054201282c0e041a840483e0039403105040040c4000220015901c910000c204504100d14114020b01000d209401f035220780341e00107114400d0100c1c10b003003000804105003400d4441800010001c084152030804201040d01102c4a60700c516a269407103940b603107000042c2d031400401101d114006503d02102010800d598074034258008005080c1050b6840444d5007070903100b44000d601035006a030b0040c0703500109 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 407522850 1250 407521600 407521619
    0x804090603031101290402120a06030b0f090c04090201090306050f060a0b1e1b03160b06040c08040210090b04060503090c0402090312030a0f06030b070e100f2102030c04 74
    0x1160b101c642240e1500300310052400f50345c400300702550918501d0840314000000094068020404115219200c1e58280002e41c95698001c030101c80c0b14903040c0c441c0ba59040d8182c00004170442d00c40043e074000d807018818600c1c04c0d60001010328414144000a82d49946521003152011210740a100c9844c409119061406d22081001045485002031900007203829010302c1645215814002c6240030804001541880c1d01c0750741c0c200c5050342101d032034286440c00d070700040034a0310060b100851814040b416504140c05200c0321070385581c4030307059503441e01d50a0040e90255070b02c00004010261001107031030803080005000a203455a981516030a0100d1640e051442c1c200301c807807080d84104021944e6490102d10350380000041900c1a44039950420b144000e811a078100c3c2d842c480c03805c403001c81005100741d0442d000705103da0320717034604000090921514016101c000408603c4088004021510a00190102d030340c0c0380140d41140042c840d41c41c420ba07001a00c003030280c014040340501c00081c1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 407524100 1250 407522850 407522867
    0xb032d0f060105010c0b09030c030a050307080606120402011d12070602060a15050603250917060708060409030c0b010e0118020a0c02122e0605060405060f0c0a080409060303 76
    0xca18007514865241000180456800102c000c04c042c00c800300142d00f080c0d041c0700ba10401c88400d816295202140c130801406036004580102c04554960701161503030a0000a0381e60031080e003c040c400070340711031b0015035141c4c050340c500c000500407494514840383c81e5002c401502c2c0c151a0f0052203c282031002c00b03810400001c002110180c5440c05900c82042c414103103204951080c2d0303181c2d5072512048200c981c4690780207616000400003840b4031040391f0b80503080d401283c43c100c030100b017041c0c016200b454550b0701c00d88500000820781b6020449a103040d80c0b042c01841e00c00e0802c05070240316640c60801c282e000368444490401d18400420044003241101e00403511503000071441d22500d814041e00c502c11600c3c019015020000c0c1c0e085080c0c5007040340225001600405070b0a00c807004149142c1200c028a5143c8864203148001aa50a082041d5002c0c0d6000400c041d00b0400c0b0000301100c190040d00101c0704a10035000c2040101e01303440024805032160b0480800c0850460402809a10 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 407525350 1250 407524100 407524123
    0x2161403040501091208090d15060e0a060803090a051e090c030103030206090a051f020408030c07090c0c0203100e1e0102070606050a05010f0804080919030506090606060d0b032d 78
    0x1d40c00221713140010301d103000316541c480c400c40382c0045516641c2491802c442c442c80c0924203152030300c04003056024004090ba0310440c04800244010b5840343c102a899001d01207005070030491894040c401841c1c446444201203000031000845098000001090702000f0f0314000c1e0003500000050042c10707414041d07258003901c40d000a0165500950b211a80c941c014818821080103082c0550100c0d8aaa0115002403080c2da0480f901c0c0c21011034480e84901e500c1c81041c901e02e2a00a142c4085400f5140b211545034005003e0800d100704c508991000c0c0040c1440041a800362043c0e40c9203128030111142c02902503800010303268101d5190104c2191140e81100d41320748c09c101410045a80d11a01074203e07124113180981041e291413600803004e00402c20f90990141c151904d0b405001805071091081382d00880c00c44840b51100c500c2c1c0340c0c4410090712040d40001081080c1d08060300203420004440300c0140864440800480a40c02c80400711b58840f0190480884114406902080f5414400 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 407526600 1250 407525350 407525369
    0x50604180303020c0c1f0e0d0b0f0930180d15050a021804090c0e010b1c020309190c0b21060405010602191707140f010501050a090216140304050109 65
    0x803148185418260346e0101300c8401c110400080000039225482010701d041d90260300070585082009440e014100c04a4030005284600d40400c40e242000040d8681e1102204400d0040c1103001d02588072154002500380454048001448040c0c0e00c4003800b4041070f5000742e682e1461051082001e80c1900c1c03000c0d012840301401400901980000d400d45811401c804950001300d4007100d2134001c02100c213544c4912100100071000007000405100105092480d89640c1e410b10f45892481000302d00040c0c40000349035004101a405e0300004008000d65140a824240314040c0e40300c0030b040d516405000d202e45440011b540300c000001020031801d40104048400340003640c10310400968540260010925100c18020b1b864248020010b1304038051050303440c40c4c0d076515030504040b102d00d03405a18464642c459008081801a010712400d07068620040038034070000e141860308400f075003128900350360400d2041004000140c0ca01401d40900489802550b1030b145424005401c0692540c04650030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 407527850 1250 407526600 407526619
    0xa0b0d0c0618091a130e1506030c1e0910081006030201031a0321120103050a020a0812030609040312020703020a05010c020a110618090702010b030c010e13050604180303020c0c 77
    0x49116010b92480780d100a6406017074100048100360013402c2e0140b498840da0180521103d01d00491040ca544166001c0d4201c4242c01e03802002e0002e41943c02c105102c0c00032011618070707600d142c5135038038a4003e25125400a0016241c1e04003d06105181a58100e0076030348100400c1156050300910303801150004030303490000650004203480f1481c40300d62400080940300384032004108103055230a00c11117000558625a1030307280850b40c1d560309010980c800c0c0c9590a00040c0d07488006544c0030b030120102c0d201821a101d03803081c00b40f50389001c0c01c01c0b424800d45600356011410310348060003d0502a82c0104040000c0c0e04240703007151884610601190800c940362000314148421007480c40b00300f030360020303640d40350400d14403082d401107010079512003805824441402c1d81500000e00c64a4220140c40760540248015204c60128540343c5810045520302c03040d4445584e1303c1305501100241000c90300c10000030b0a0022014001030840200c0e50120f50f002861408010442c036802080e01c00c4c1c0407 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 407529100 1250 407527850 407527871
    0x106140f12190603111f02191a040b0601030516020c01110c030d11060105010c0312050a0b030d030c0e060711060c07050a03150b0301140a0b0d0c061809 67
    0x491140d0344102803203a01030400300d80340410641c0e8a515200b091141080000d44918190751030754142a4400e224620348040541c0032500211040d91119840d001040880a13072080074541c1090600c003a51403008105c00300a40031f650401051080344990416011482e103500050106d5102030024405181d26408240000d500019209001d40c02402c0c00c51f8403054a0074964038000051070003a405000f101c6207080300b0390300410740c8904407840209460084c0c1c0c9a90045a4413610503c0c00390000d40014140c050041003580165080000c80c1404641100c0306000319281403034004400c00041e0b43e079011107a50581c814069000444200d0303900349800c04a0310b032507040c008001c0b2420b22400e400034050300c501404124003001420701074001c0400d0f1b5900d0402118012080d0300d0390800c98140300344400245010300c101309800e0001181411a902c5e02451440240403401c0d100e44c101001c00340c1040410300310a40300c80180959038405d010b1b45041b000842c00c0c81c06aa00042021f81410504c2c40c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 407530350 1250 407529100 407529127
    0xe03100b041d070b070c1a2508030105041817190201050906040b18071d0a0b0d0605090712110307060206010e070f090b0c0105040314040b0d020912070e010614 70
    0x4c40b184c0d80c010a48503034a0781406d503030f460250351000806030700c1c2422154902a100c4080d0040b02d86442005e40d0b2840f1040134140c0040c1041001800000d08000620030b81c0b070700340d001800800100031150030b4800703d966505503000d650301d407081003840701180f20040e02150790403401d0904020b20003402a82440c00025550701d4018000504040e010f00009090a0f590451240000001e0080300d0b080c507592400142210181d010004c512034520700041c03000c18450240100400c00542140b12812154540d80010704018003814528012400300141104503850808140341c0255a11046902c400081602c1c0800c194080c1b02503404c03900040254a00c0e03c3c1e8140d034003103494207042c48040700180c4c0132101400150032000b00442d02140b02c0700b8070201503000ca072049201e61104140d281d0080d03c14a500e0040c0d10407c0000802040f1090b40c80c420340d0040d04000101400c410011007101f0700c45400c040d400e03049032070102000c000410a1503440280c600c4c080040c0b101042c0390010f80038800 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 407531600 1250 407530350 407530363
    0xc2c1f0b130e06030114070c150b010c021201020906070c15021912020c0603010b1305060405030c040f14090d17060607060e0a0c060f030b12070509070e03100b041d 72
    0x200358280880d00103003080e10203400403460701394001402d0307045141500016104812007079041c0d2710000300c09030410710071300310344602c24066405840f580c05c4034a440d420454004241500418195001c0c00151f18548840000d410718900c103a050a06807405d248000407100b40001ca51011984480c072119043c07003140c040d41201607009045060300e4501c150003030f4908482144a50b4002e04000000101c08610001600c2c00059600c104c10320280e0300c60400c613190041d0700400381d0582100c088c0030344508c2d055100b10110f040b00c00c0041401040d24000da070200000b00c6030290282c100c15aa00c540581c03142400d81d034003941b01962890b6042c0300300494040e000d03100000340b10a580781211400b84004004034000607a20404a60034107480d0300005142480f142407601c0442d0a011141c01580303003081c5032401516600006080c402d03e00f2003080780300c84000d8482c2082c8102c0d22885a05074405008450001d001c074800462449400c809000441322840092503a0a10000c1e6600c0720000100d0003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 407532850 1250 407531600 407531609
    0x1803020603040219030c03060e0c01020a150911120a0b090a0b0c030402061c02041401020a08070314070507091a060903060a05070e030a1a010b03040c2c1f0b13 70
    0x29116000c204d03010101a4030740c1e5003010b440c440e0303022000401c001c8181c11520203070101c8820303920040c0107034006a907a02c0006030000c08a1a040d0142035500e0a03940c440b11400d4059038454a02c00007a4001c00d40290309203e28207030b603410007100c21080c0807010b1034050b0007105040050040000c540c4501851980240110202450002c0401c0541da54481501e0040300d882e111400b0a042210b03081c00258041d00c80e01101c141c044042c0c03038140d0b0010813910019034110030018604400381d581156007000614002c0c0300500103110760000300e0400c108110107007100e11030024261054598a0607504c207282a00780c402c030000c0084005c00e84012034980e410036402c1d08040740b04c0e00c17a02000d98840130f90000c0c640c4c00d841440002001d008440c02021044007075481c03c02226600ca810754041351004a030058091025120108150b00300d0781c0c03030300300c001c28104400c0c0703c0740702200d5100b680e1031400e84100305002d641980301d01e03020003100203030801409484452454040521030654042081d03216 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 407534100 1250 407532850 407532859
    0x30621020a170a0303090305040e0f0a0510030206031504060308040b1312110103150918020901090506010f180e0901020c06180705010e04060503010c0210050f04030c020d020a0e1618030206030402 86
    0x20900d00305400723202503801901030803564210070f24004008100d081400c03a1082529401c0c440800d144038408600d5006682e00a81810b00d035503210004007100017001c042c25074202d03039034140c004081041400904050320400400c240d0742e910300c00d007001c000b0f85142c000e15488281140e0740000502c1000c19440070351421700700070940c10803a15902120b0503540e03101600e018205045042e40071529400c501c1c2492003110100000e91f218070003807046400840d401030109082d1404018841d00407c2454026404a80041d0449880c0d00454550200c181d41d40c0703a01d690085410302d595241070080aa101c00c0440200018041c19046a55205064810a414082c0340d941c02c2c0c0754ad850365004000580000f034000d0202d01ca14400081d034178150309407004606842d002c00704041c0c140038a079443c06a6010b6031809640301480c1c081008030001000201c2e40210418000160301081c003083c00e20620603103824030328030b030041032018105ca0701003c401c1c050350600820500050340c4190990703410903015107 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 407535350 1250 407534100 407534111
    0x306090303181c2609010c080901020f030f1302031b03060601020a020a0b0d020c012d18080f16030906021e06070c050a0b01030606180506010c02010f030621020a170a0303 75
    0x4807070a02a0b1341901115100341c0c8241c0801080c0c00054010741000f807440e6440394450741e07880283c60300b00d025040c00c4550400e030030000b040f9601c10300300341140c120180c2072000000c052582d000903d031548182843c98000e02e100c0e03170070a140c81c00380702d402e42c071000c00c1c0050519082c0342d50000d0740c0040c480c014040c084102042010000741c0f103605070f50120350800c00070032580010340549200c003520910000c80703040e001d40070b902940a15009000c248604a080c000c0c03810f00a0b40c40108e180c012106a05002c04240040b00012041100c491300705802519183c00c4617040000003400c1c07000c11090960040d00d50101051414400100b1076440700032868003c0c0e00e40d9882c0b400da410300d6005c1001502601d00034001005100e01a4032a200f2621901c940c0214801c4c04251481641c104a40f0310340411001d10789180035500500c0c04c14440c2c1550300d00001d0558a030144040104100b00800000368803007003a80c0f0445c01c15600c0d400241c000780f0b02e101c503e038a100070b82507512200b54500508254a81c1c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 407536600 1250 407535350 407535377
    0x10911121c050c0f06011701110406090b07020607153206120a080301080d09141003050a0209030f010518010b0a0b130f1e061b030c020d020306090303181c 68
    0x50000c41c12000740402501c1c0c0e0340d44d481d002501954a00c046000d4523501e010054000c6d0001c80d82100c040702ca9a841e50340802e80b80440c0b651642c0c0000b0070580e00903200700615400110040c07208001d00c0d10741c040014078213001b041100c27005842c3d000c4000e40344421070924000c52034000341007640410212001c1903a00c508402d0702d800d1a400b8640102020300c08000410580301c00b1411018505003903690701d261559a60704031416404030200c0d10b41000e920f18a0a0070345120741c020b1540410f1410300540707450301301d1020910708010356502d0300340340e55100140203074964062520b030164200d0b4802402131507581c4000402d54141c5104140401d030001030315002280324205400f005200b90822460825501e2141811149002c41407034052400300c5d10102d1458028041912181c1c80e031208a84a0b03103a9079400c1e00e03040480d080a0f644591a010032070700595013002000d218281070405181c90f8107100340c000e80504544031000c1c090350000b81c40b0015a110b40135a0700b0320040c01345444011071805 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 407537850 1250 407536600 407536603
    0x6090c12050a0e010e0f0105090d080a0213031203020d1404122114190e0309060a05040b0f0702011209050d0c060e0a0308190b09040305070311010911121c050c 70
    0x344422450f20b0350070040c5a1804020200b1001d00e0803030b0b00700003405150380c1e420360917440d83e8101185c80c0110304400086840d107840f5074041d10080c40c400e10602a03c0d41c99847d5003072030981c0c0703010410000344c000540300e9103c01d46015400c891900e1842c81c080601380359a807034032403a012240480411181011150b100c410740102d0460403e9010b2007006061120f200008040c4400c54081d140c19550f0540c492880829106140481d920200a9403c010b100820442a030740250a0102000b01c10b110100d1a85501402481605000003080c0d81e40c0700c2c03510024204144540c14240860328200e2410046031020a82100c084a10b284c158101229882c041c0c009140445420005100d40a201e004058100510301d00030000381c00075014000c0804511f50613120450309068008100201013400a805074005c0c10885101e0301302240d440f11004e00140c01c6401d2076a0680d083c1c0304850114080b07040c0402000311620300d10016000081001c2c401058644004400c2400c101000401c250034a90 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 407539100 1250 407537850 407537861
    0x50703151526040c0302040b060304050c090601090b040906050f12070909141603060b060a0918141609051507032a05060a050106080112062c1006090c12050a 69
    0xe4410540c0c43d080908149102030244d00040303018a01c2c040003403c5600c1c00c64181c82c4210790080050040004060070300503000380140245050080110380403038400b0030074019101402c060700f0000b4030145032a04000c655045030302c2045c010030389501c04115a0034003240000c01d4640c42031001c13851508070300c0c002e07120143c410100c4115008100d030359461484102c0c040400c4a0055505001c0c040d1030004200045c070441000030301003001000d0422400d54030311032540d19240911000560199040c007a01b06900003241c03541580741129200024603034006420300b025003000c0d07510207101d00803c01d00c440140b00d424005000c0c09100c0c80c50a0f4408851002480318800500c00040d8804242c50100d640300e000fa40c00c100702c02d080000100b03181e880b51501134101ea50300d03c500b059464040d20344200901140c0c1d0307252030840301c44111100651303480c0ca1707000c00340d404140100b00200b0403001342011181946c0092240509040f00900784d6540100c000000d28508000001caa03100c94052200410 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 407540350 1250 407539100 407539157
    0x50d0c0c080a0201140c03090312130605091c05040b090d0212030d0204140d02061204030306081e0d110d11010608070e011d0402031b03010b0a08010507031515 70
    0x500016480c07080a6040d04120950b44042e1461702c00342c2c603018548241030108969003030b29640181b1101c424101c055100342d8000302410a5800920182d807100400c3c3c3e0b004075031641039640144404d601c001b1a0041070003645001d840c1860034942003890780d0011b071040d60a164410040c0701c90203001d641d2100b015050184503102141d6490f000c81c7e01100103500070b0310400c01d16084140260043d402d103050040ad440da4005c0c03000f8a07000c426000a0300b82d04010b441a000c05a81d281c01080c2980d00b0803403002d4094900c580d094914980030030561074000580b0320a0f042206818000b18009000100c894000649040540b80c14094500c1c29004040b10340c41400b00d07210301080003409424094003503042c0d81c05046c4101c80341000c0f500401c10b0f0401520000e42591092485c0481c00440e102491b05410005002080017007103030f800206035004c0c9400001190355100c0c00d00407583e8141c81000070340c1405040b8014043d10f0000300c0110203500041e64401d0200c01d04400ca10640344010107130946 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 407541600 1250 407540350 407540363
    0x6080f010e061210050a0f06120f0c1505030117011a01051b0105010e01080c030a0507030611070210020c12190204021e040308070201182409080109080d14040201050d0c0c 75
    0x400076403040c000381601b40c400300c52162030503200b2100f1040303e02030501521440d400700000041c80303585a41c500550000c0990300790701c03c89804a101c8814549402c0480490303a1100d489505105503440c00178401100c49049a141c91440e2089105410354518110000d091045c0c0703520442025203400100150039000342d5181c6000460610031008640341600d0644d0110380b5a0483c03441131668501c20210b0141c00c0d54846102040041d038a03130081940c242d038010465003001450f5010480b0003ca42c040000940c000f0030000c2580d00340300e9903001c800e0102000428540155840d8410810245000640203039000100003010491840c50709c10f01c4015240c8a40da078a960f800c0900341601300c1d040803400102d001ca0000c560b042c020406034240c40030001d030203408240e0045d031401d01002456540e4140f00681000180c00e00d800e21030815120301855103240d803900103d08100449101c1068140081040001c2c000540d038000d050300c00c94510b8560000d8040890300c0c09460b10810103200520f0f6 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 407542850 1250 407541600 407541613
    0x507050a021e0418050c0d0b01150c020402072303090a060e0609030d110f15150d0503030a0b030111030c07020111010e070f090e010e0c0607080d02121006080f010e0612 74
    0x48104c0c000c44c000345170702a2090707640440c105000c0014001107080301030145586000144070108040c0b0510888090a040914004650b0b134081001e03600100c40079504a5204400098010103a031001a03090403000050341c50520703110001250741040340205020010150b501140315110402250707101640201100c00004400000420383e9140003c08842405200d4490000d04400100800224001e13803911510f552100000703503070030f800503861a502042180c03521020a20500040d40912039140000c0303400c130040301c02c2c1802d5070501040307090900740130030400a41c00081c4055400c00c51342460320545005001b42164090412502011228000ea020005007249522640300440e050840240025001c0808180c201d03000c840c0c4104140e0000c0840c1038562824600070808a0300c140c0d4060704080502c00b030041260403850000c03401d41c982c0c0d000d0000e1000344070402c03030060141d858550307051310340b500b0f01154051040c81455900b030701040c042402c84c2c0e0b8140403460300101d080101d921 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 407544100 1250 407542850 407542871
    0x14150403062003040b0403080a090614060a0602120304030804141504060b0906030606060a051209250b1608090904050a060e070305030f03091f05060f010507050a021e04 74
    0x1440503003a94800000d4802c420450380c44400203407481503400c00d04210301c0740d4070354802344c0b42e00030700030010f10728a40d5030101080068014800c0d03150202102e02450400d00c0c106041c030525210a0300a4000d550200c800d4104140100701203d501544c50700d4540b00710345551034058001525542c5201c3c07503000d2810400150013480314128802c60240c9014403036603050200784008500700791116034158000c28006206400e000e001000b8200340e6140451600072008440c03c4241c1c419115000150070101c17640c0c03400d91403d000700300484124803090083c946803040c0e84609101d0904c0403000009a503d1050501a4490950745582c0c1c02500c0c0c1030403031a16280058442c41c80e4182103410502d0400140c0054000042010540b035002000f14900610520740032010b41004000102c14410020301c401c03c0d200a500a121009000b2170206d418149803041050148000060904200083c84044082040000e41c078081c0e03901910f072100e81d05100700c031020700c44822001d01303500079040161014 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 407545350 1250 407544100 407544113
    0x91a03030a030c3e1009030801080616210f11120708011203080907050a08100e0102270409020a0b070507080109030e090702030c100b010807020c0a14150403 69
    0xb4001102070780d44400c0000d60f132404031259074605400c9a80002110500d08a1409040c0003003181010300c400c40b407150351840030000c1136445001045001403001300c01001091000c00c011a00074140c0d4600080401d9107c0c1c00038180c09103003140f0841450f00516020600c2c0c80b503031210042011400741400002c40c90081030f050369208010307244540007103100080d044c43c4038000032410385150195088803041a500d00301c038a8400505100c07414080e0f180c000401e983c5803180b11000b070482502800d456410300c0c8108044034200101d8511a900400074030420809016402e0107a20001544170316030380f0f560001c50300270421000000d400441450300418010f0044001e800164800e41c100d40b00252205440340c2683c00310440140031a00491514801c0e1411901c2541d12841b50300c101ca04220741e11b000703586040c00e0140c910826903902c3d00c1000315542d0184803642d00c190103000030906c104000c408100e06010a204000e100074003038800010541d201e8071102c010345032090f0031585441d00c0e8107107032 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 407546600 1250 407545350 407545361
    0x9060b030106110f0c040b0a0e070305160905130509010b090c0d0b010507080d111207090608010b0909011404020c07080606090f09070509041e030309121107091a03030a03 75
    0x3080031840f6400212903000c1c002070708000307490104010380009540441400040d0030300006880c0d211007462001b00b1070145010000340326442a960110703070383c1407601130041d250138101845001c00100302c1042c071441d01c0c0c1c1c3c46400290b40903540002860b9442e607503070a0041000138117265101c01d101040c4000e040341880035000a6202c2c050401014a003d0b0040d25184148440100301c210240721a20042026072f000030500d0084c40c5030689401310100c2c4440041604803002c001050455105010250b800750050740500703000703100b840c50154580001074810324140b0a000c2403000003015410151650380584841c0455002141c22080e2181440c58407914115a064050071070b450000c3c25540309091b480d030103008020b02801a807400d040900c4440c280013002030b60083c20303801203401044400344202c911503000c4e550004e00e032006850290718000c076030a8018200030040c22100d00b03c40001c905c40003150482800000d0010a135030002810554160840d507240c00081400c0098a4058104 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 407547850 1250 407546600 407546609
    0xf11040906051e1501080604020c0c060a090312080c0306040f0605060a05043803040204060b16121d190803030720011e050a0b0402162306070507030909060b0301 71
    0x1400310b5030307940f4418582c0710040101e04c0b500051041c000700310355080590040c180802c0400c1600d5a0500000c041811070f40281c0081001407084102002072040e040c100b41d44c0c20000c0e2604075a41d04008007090090701002d800e07184103a96801041d20542d40c01d87c0240c005200207041240c0f0344811080280060304144a440c0c00c0203042007240c00d602d00c0c00c2c1c00440300b10510007101c000350745440c996000c4a400080080313800569954020450314009d00c00361a400130680142804189949040420f000a50064406101250030344043c08142100e200c440d0704e4056804550700207891051000000203584100b03141d000000a108806074007040c086982c600e000c2041e12040307000d11a1900300c1d00d41c840e8008103a22680380070100141d0681050703030042442c00020030040f0b40100090204c0c1c0c0940064020805810203250420280700c02c21202102141105111502c101407420b031208401441b0004008000031180c1c1094010707070350200034101e080420004191100c01e5101903501c00c3c006d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 407549100 1250 407547850 407547901
    0xb1507020406080c10080c0d02071202010c2a150f0204050108010b090901090b0d0507060305090124030f020303120114010e03160e0a02070204020d0c030510030f1104090605 76
    0x400c3c2038000007110f80c915007001d400c40b00861030207481102c040d000503007410005541046a040140d00354005441002e004100104412408400103801c640109034864144043d05c509200b1103850b80702d0b110107481401071020b40401a85c90608908540301950311451494902c07054400510303a40600b00b41d5100713880342422030342ca907051042c3c0c038080e1500040c1d00101450040c0021079040d000071440140140500401d407400707a42d09404c003082500800e001039600e4040082e508403d024011840c0d030000180d80340f655416843d1482082d03240805008500c6400c4c200046407000c004540d42030600036000740217561030701502c21801c1040510b090010341c00c0c00003038505180105007600c807a1030086003440400c0c034210b50001d403200010108480c640e801e10003000581c032280001d01c803a0058220002d0fa0380302c2d0120140840ea006805520000d45000082c0005201c207440710b204141c000c11100040780c802c0000402800c3e0702a402490942407000b032000413281c0a041c4412840b6524 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 407550350 1250 407549100 407549111
    0x2010b091518011202010c031110050a05061002031b12040b030108010507030506010203070f050c03100621021309060902061c0e011b08130c15030b030a150f0b15070204 74
    0xc6107640c034034802c0c010b02a585940c213082000560181102d051818801d040506040d08400d00450400740600104603c140c0c40b5070410621581c248111030340002c08540e01040c850008a00079941d018480030320050400c080b80c01c440c04138080049071040c9241507101039030396841d01d0090106410078071074204950b081c00d022640e054003d0042c54032440043e40210f082c0901a1198040c0200036901520b1a00400c8040c0036240c03000c0c0100700000300c0200c004a00189005800724a00303145d5040d0541c1100c0c281d00040050f81c0703012032200301442e0701c4004500034206061240007840f46250003584290b0008056000b14466064201d6041c0000320410080b480748000da17099032030301c2c0490007034040b0380c55800401c54011441186c101200220700c1405010a83d2007000d80c46281d0410154150580c941651181d414059801c1c8000d041c0c0181c1062100b603590600b650b840780700020344403a215040441d4012965101a0301c030500204002e120b04500c504408440d444001d041c0d004a0820 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 407551600 1250 407550350 407550379
    0x3150c03020913020a0309050319020f0c0934080603060f01030c0501050c01090503030109140703150605030618011401030e03340b0412030606020d080601050a02010b0915 75
    0x30700c00d88240103006040050b110500f04801c5000398004030350301c81419076546900000c103d040000e8801c0c1039031031200e900014440c0300041d240c034104035039140059205998601d141e0312819440f540100604400c004030745404049420342070903142c0b560344044030006555002d66070000e92640100402ea0a0311a540c458100d0301c0801d007070900000c0c055072402d020400c19544108002d09410f111170000040300e1030140c0e54141558401e910145800e0344541c03c1000e44e10b192461680c00c62401e09041104a0102020718024941407051000b40040407000403010784034141c00c007c48072901c4800301441d6854202c4505010035007842180000d20f08542a160040c0000880c0d0700c4518075200c60103a0645d00b1400140c03c80302079404106030a44089440010b0610510310340140e10507141070312440f585400040448040b90710030f10031541701d0300f01040001d4001c03142903041402840e050303585080300001a030240041c0c000c0c19820041c2c5034204054840605c0084410440c01c40e20b425105408 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 407552850 1250 407551600 407551607
    0xb1e09151306120903090614120109060e0903070507090b0f030109030f08010f0e0f040f0807030306030b060a0302091b04081b0f03010522050a020a120b0714040e041b03150c 76
    0x58400080101c2c0c1d48040130303c041030042c01c23000f4400c1d10096015107041c04460b45521a010280e1103510500d80ba80410700124811589040c4e110010344010b608181098642c0f0755504420321803200d516640c1c010074802915108044281c0c00310240003406981c0251130020050114804043c0025100d80000b107110715a80c2407074030403100030500c9019280c44110b1403c4500c40040c200329603002c0d04825a40c00200c0440207130200301c0c0240c0340011a513295007040b144030301c00181400e03c1074148210070310050b65103491240c0c00141024000c00b00c20055898201d09204582080b44c1a10841072400304000c1410035282000c0c1c8142e8401001c40c90100c02d00d4240c40081d2458601c40720140450308508803041d10301d400941c0640d04849220702c490300455804a1960404d400c210314540140c030a0001c460b00039504500700c0e183c105018031100d0f0a001041c000e070301031a0310700d509507008503090080e00541d869481c0f0303070100e540c00440d642c0e252207078501940c1c849440c0402d060103441d0411038003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 407553956 1106 407552850 407552861
    0x1e0c07080d1704081602010c05030c0d09051905060f0919090506100504062d02070f0e0919030314010f050301060b1e0915130612 57
    0x4000c0002020908480080c0030800070075400d0000140e04031045504c8000c2c40f2905e901c52103e68030040b507488016110282407403001041c1c0c08007001c404506010902d845842398500f0a550b18248203030140c852a8941103100f000c60300700041c0c18848000d140100d0049449403812181000190002101c010500300000e8440c8051004030b0b00c601c122504180d045a0f14040340c500d2030720090191189015440800c4000c050a4010004007a500f42041481c42500710400f080074400030742c0c1ea1060b20502c0c0003181c135120300040780c400c1110a24059242180a0241d2013140c1303101c007801204e0902c00b01c08040e541c05042c510820503922003806071820702607022545180000b090300350780030f030341000d119088104082c440440600c1d0403003a08a0100410341d85030706c548000500d264074101c0c69949a0000081c060800503030102940080d14141e40384c0544c425030200203d421031702c = true := by decide +kernel

theorem cover : BRFrame.Cov 407374100 407553956 := by
  have h0 := BRFrame.cov_init 407374100
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407374100 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 407374100 ≤ n) (h2 : n < 407553956) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
