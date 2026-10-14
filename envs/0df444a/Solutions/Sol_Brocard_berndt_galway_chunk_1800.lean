-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1800
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:43:19.778106+00:00
-- url     : https://prove2.me/submissions/bd39e2d5-7689-4941-b5db-ac64b89c970b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 323561151 ≤ n < 323741007 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 323562401 1250 323561151 323561179
    0x60819050c0906040f09050c03220f020a0602030417070b09120c03120403050f0106051e01020703020d080a08011a0f030402010e090108060109180507031101020a08030a05191a0f 78
    0x11401410050644207179840d80185800c0a040807500040c04150b0445c40410402c809182c603000d605408070b070718905180b10507041d4100300349001c006d203400942c40007031030000041069000003d04162a1000c0c181111070b545a84610b80d1581c640c491500100b4090004000c2441c00b099011850b401c0c15041c0d45005000f20002410a401d90006480c400300c0880c090040c030400300020900794040c81d00030400c09007014001000c000b084d80b0710310014451b8154030a003d901c240405002142e000e40780111600c2740d440c11542c650403041c404400580c007103000081000001c44100801c0112038080707031408c40d0100c51000260300041069041c001c08115081c007946070001514000c5c200803020f010554108901e90041e1440c0da05007261500522856102017000030584204880e0301929243c2c214200d40b00607404c0185400029181100104c20010080001d40100384203203028001c02454240110315001116582a42d0f41c0700d40c0e1a480da00c1d030079410810300c5808250002414039021070301c9 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 323563651 1250 323562401 323562409
    0xc030f04060f0908060403080a050c0d0617012306010f0e031006050a060e010e0d1e0308063105060a05103c12020f0a0216060819050c09 60
    0x100368000c00024142c4a96101e810f68081c44103000703041c1c80805013006040640780240740143c054401542642d42d00701086a4203402400c40300e20201890040c0321150340d840c0a10328640d60054031107050350904440104040c10060b128100e280d840c2d40c1b610b200d490f900300444403da0341c2982072007846000701c1405843d076001c020b0a0074800c407501001c50010704200500081d00d01580c401e0051149100340004140e82048214403407110030b42d02890440c0e1075040c00c1052000c50081881111410100c900c140355110100d5441610282c0390190382c1c0c802540711840a000e5010000004500080c020754500078503002540c02a000030700d400e0341d01e0f0b107400000307404510003078586d000310320040030200b0701e1080221503c1e511280d030046e81c5c00005000302c5000d1980100ba20030000c010340680d9a90f006049641a5886041c0090f200c0d2f440d000c0c20340c0081e55911480b14094110719408400140c41071003500402d108943d5000d480380800728500654014042c00741c240b507131900040c0024041602c0d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 323564901 1250 323563651 323563657
    0x16020106122102031603031a15040915031101030e160f06030e010504111002011503080a020618100c021c031410150e0607021801050f0d0c03080c030f 66
    0x8002e9030801981c810095880b00e030b0104010030a002e540051050b0034001c24405001c014150b0503007000b051080819041d0004e980000c0c614680c0101840806160b254690000d4025511400360821004020302c1cac04c190103610300d100007003130142d47e6810440705500ca500f200c619200400701b168060b032525540780b100313143c840e0080001c01c0c03103080c02080807550501072244510070400c020096800e2648904131200c06848000e40982030802041d800d2038400d41c0440b41d108007000e0080c00040c1c403850720182541c04032006000512501012a14502134040845c003d070181c1c1c40104101e426080041c8054191107100c0b000b58015410000c102c003c011459001040c4195400240f81c03851114441243c80d014060444007400c1440501c01d4000410410800c0c4030b45003414516200004c0001d00310344101800290030a83d8039102d00100b145410905069400896561100100050a120000001c402c01400026807444100041805400100550704c03c83c0141c81c5480c2400c421881964 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 323566151 1250 323564901 323564903
    0x114041113140601032c07090e0129030c041b080f010305150a0209100305010906090b060d0203090a0b011502100c1d060418150e0f1602010612 63
    0x3116180040080e00d407564a81021801c011810008651400e907034414401d4014581418580d95101c0f54001d101d481442481e00848501154491460241400d031a0341e1940f00c3c0780380c5c0500700440041d483c031040c00350264a100355845c084261050300d0782a002200b015622540501426001d0807864456018410030640000700805210000c00d0380200080b00040902d54a54541c0d40103000044010940d94070442080e401c001c4030303480350040080207228070030b003c0e070b44041c4500d040f0303082c990542c100e94102c6030302c2c1c801004151365800d904000c0da0b100221305540f000d030400180080400507806190440050341c211440102c0340d995220aa100a80114180042d079032030b000040c907410019002000c00c240c84c00e10400a5120001c0d1a90202e00800202e003c40328004520075241c10041d20010300c01d108015151080000c4028020301c0c0741202d03100148580c40d40883c61114903030440f80100751040c8413034907580e01c011a01301c2e41c02d100366803101155207a0710005021140501100340017 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 323567401 1250 323566151 323566163
    0x5281119050318010209090a02030714040e070e030f030f0711120a050c0609011d131505090a090b04021c0c0329150d020402070c0905040212031317011404 68
    0x1900340400c58034a0380d2040b0403c00050f81c01040380d0702c1207071204800c2a810407a03400000d6140e482c0c00074103840d14600d040701c060040b00042030003c0c9130011424000c1c0680c207291121146200e0f804141506c80107030340103121499000b006607030a00c0d0001001000b49038062818074444189071000140d00d51342c013818200b0380c0c1e40b05241560610a05011402c400c4030110303652458081103500291290b202d040c000d00c0700302007440101c10152984001502c5259440d54100038460901110801c80505c901940b0f00601d42c0b400011070080075403055191442d04486001c43ea5581c0c3d5007009441d541141041c1c48a9202c1c0c8400030000d403030020b10001030b40c414003001c442d528849481103d42001000c0c044d080039950018000382002c1c804a8034038480040da01c0184010303041c00401c019101e1448003d03d400c00c25000011092900d502c0140640c1c0700700c64050701c3d240c4200c9620b83d24003480b07049048401d0b5081c070030051810103d48500f032400e1007100214400221100700c0307025542c00ca50a4500f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 323568651 1250 323567401 323567407
    0x30d0207031208070c080d09050105190c0905150906041707090b01080609071b020a0e060108061009090b0a090c0c0b0105040e060604020a0207050918010528111905 72
    0x10001e0002c15184220b0561400d29090700c0c110380c004200c1c40a081e000351511000007800710354455103410103042250018000d02c041d00f4a600c00d076640f40b150701003c1410500e40488000524881c100703c200300c400060202e010420080c002c0903880c0d0004182940c4290b04210004100541481c5404d940041d94060f0840610788040130068840c50740100d810003034036400308034040c0d84200c0c1d070f542c00c88407031b01d0101e04500400c00c4a40d14249070040103940503015000000740440050780c0f240c400c032000c0c1e0725446580c0b529014491402038074100c001c00302d060f0310b1042c03181d2030701507000c60300c0b2001c02004200180d0303582030f240003150524099180015241c17656001446403000301036004050681e005c024612107007100c251115805070159118940010301954080d10130070003c0003505004240802d6400c00c172132315440300d00a210740320445509040018803800c170314020500d00c0c0200205801800b1000c5500040140426034010704403050910810301603130604190180340d03070140d840d03041d6 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 323569901 1250 323568651 323568653
    0x709031205040807061412090124080106051203070b040305070b041104060f050a060513080712030e060a0e0f0a080f01061d0c040e0a0e0307080901110c2d030d020703 73
    0x4c141007403500a0000d00010300440c2500c40c00da00c085070450034030314000640a41312180610f001d001302d40000d402d148021403880842c0d50020800d24111703640740c4002c100c00c699030005e100503e02a5141442e440c0c2043c4044008140425a00c0394171600c2460300f0343c50a0b150b644c82c042804c00070f03202034540841010f540e4040741018402d900140c40e0003000c0e03400051400c00090f8210a0600440c020400e010030184218009124554082c041440964100039100c11003c0d09004c8848026000145003130140903103818024100ca5016190341d0f50060060401800d010324412000d6803160003561820300081d0600c4240040381e20804400e0001c11060310b0b20f00191802800a40d2183e14000c0810034058206200000c41d001c541c540c142884050385c441d03400000030420705c0350310b010901000880310300308110b01c0000c05c80c421090301c4a54000741c03441d2740a591041003402003030300855178000d1940c130b1103900392909202c2c10b800c2c011032884800000100c0d05142e400204003000d6880f1030700604c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 323571151 1250 323569901 323569903
    0x20d0b0609090c060d151508060310060302090109021c0905060106111209041d060109020909010b1804050c0d091101080702030f0316030b031f0b0111060f07090312050408 75
    0xd034002c800301c802070a681404000043e494403462064942499903502220014601c0c3c4914400030403502c0a41e00540c40400c0000d044d241003215038a1080c007445106c01c0d242c00003440b40f482981e030050100d0746541c3c20070041c0c00c001c0d8015041e8425281890320b58850914440c0200c010843c4504c01034000c551402c007001d0400d107964850a11642c005030030b0f02191954100c01d82c2c41694085601180034030224003c0a0340071000c51302540b0500801700041005000b03a00185001c400959640205a82c0d446603942240500e40c4021030309e040051014005241c19045180c00c8189078441c6880c084a58030309404a402c0b107039084882220b8200381070029a0491000e59124640b4006549440e03140382800c40e0b00d100060408500385528910001c11500c1f0364060681d8090160450384000c41c054040340c4030f19000c1c006143c459040c45180221540304208102c1001415401020f0b662160109403040c204000e115800b0440e654100001044004088180075000380e180c940d6a030307040a0f200303 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 323572401 1250 323571151 323571169
    0x5100e0105042307050708070b1005010f0e010e0f04020d0f0507020102030402100807090906120215042102031c05070303060e281104082401210807020d0b06 69
    0x158031440c0740c039020600c91074001c1d081a01101048550b821203603540c3c44c2c1030355580200c0c40083c207040d03408540714041110f400640340c0071300800040d4083c62940e40d0300441e2b448003240e0100c07000800f08103c500b03d41d4005c1c58a200c04a41c010010300f20070f2145000324040b03801c011a42100a5110240302011000610615400c40c00d20f00c001d5107549465004039030f030302c02802101e10412821000141409101e92912005005100d0050041c02d564054002080c844440180d21400b0400042100402103504481c101c03042c5010401410b510b0322510001d003070001105a800d03004040308503400b2080801d1881c0310a1007515240c2d103a040c1401e0017012140a500603100002c58001800380030701c0d8040038803802113001c00500c0c16141c03a0840010140c80041e0036841801c01c08134001c0f50021005c280300c1c2940d4540c0001c5084c5000d004130030345840c02c007071080492448080c00c4040750880811100d1165501484850f0324040c0d103070380482c0303c0000c4a401511884100030a0215901e010444 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 323573651 1250 323572401 323572409
    0xc0616031407080301271a1003050405120a050415021f02030601140a02030903070f230d021903050d05040f06030506031b0102072c0f1003060b060d05100e01 69
    0x500c07802c0800340d60311041d42d4801070041c40f6a81055140105102240540e9001c4004c144441440711812800c2414090290182581d2103050074509a4003600d10911600e407140303805c0340c001c00025691503032040642d40b218449004100b01084013040843e42c1003101d0b00c81500507401402c5c6094414086240c2c549100c11a120190040042c040c80780c0c1d0000d10450400c0c100c8411542d1613800c104140d2079072140c0c81ca40c0e03806004594000442c1141600e28208a075050344207622807044450322489401c2003140c180d84c7c804501c02c04040036040818180c0e000030124540300c81e1541c1c483e101c640c40c2092030392589000580c00501407106403100032016005090700e0030f00f8000c500348480042e48642c180d60f030215543d02d5011459095a10070400d5100074100d0b84c40ba034200c0800100d03c240741c0303050580c007904140314040c08a000030480a19061081000c2c60f44030481c181159a03003409032080004856100c88140888111401c0a1141c03074002c0c0b224200b990031161801001100600301648 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 323574901 1250 323573651 323573687
    0x1c02011b0e01080c07050d08160302130e0a141003150902031e100f141503030307052b0209040c0509210102040308030f2a0703050c0c061603 62
    0x20030040555040400c6000c80d440034204801c581d600c1104032200e502a490024100748a10926090305c1e5800c860440d0081e401c0002409804445003016030503403140001d05180e05592143c200700780300400e400207070040c00307002d00455192005403121206410546942900c0001c82104000700a01d0084204c0032b203109240c1030040642c2900000c1d218542c1010300c1d80210301040f0701c000b6417902884030710802d100e100320820400a00b048000001c0103e03002c00200452840c01080101c08407080240100340010300451a5a689c050b0498480d00070401c0003c94400410340c0c04400000030079400b84844640500603240e03458103007040140d4040380c03010001c1c00010003c21465480701c505030100c440e5581790344c85101103140d40303035402442540c0c405030010f880402403003002aa04140f46010f40050100c550302074440d130b000c1c0d6002081c25844a5540f88081240e0b0700081d0140028014504a0600340e403200c03400c1d9030104403103901190003c40b100c076689100c1410150002c18060480500c00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 323576151 1250 323574901 323574941
    0x2214011401060225090506010221040905010e0c0301150c05190203060a0506010203180102031c0e10110a0f031e060602072301051606020f070204050a090201080f06010905031c0201 79
    0x240c1c80302c0c86014a03000d1599507948441c005030a5900030080889000701d10203013424450300b022b400b00c0e02a0810301518262a0420000141c0c9440d84402c0d14003078884410803514503403030078203012003d140c105114001c1c03000701e03032400000c83c00071b102e00c00c1d9110560300c01d508043c002d403042506144006024800c610718000910005903400401c2e81e4041e0701c0300500c00f101504c0703e0010307442e5000e803400c555084015004806c1c814a00d82d0040e40008031030b01c1c100c0c0c00c8000400d91b401c064401c010070109a811041c010510160320403020b00300c2c9a0002c0c240041c0118076400c46085d00340590500c13510858445404010940d410041440101000e110301c40310645000c92103000c03500c0c4451200c1c10000e02041000c1c2108040c40448941d551042d0219a50398030701442c00c0d01d0f600290001d91243d89420002071040386940079030802d0a6050351103298a0703450022825140c2406002c65041008a510204443d1003c0150142c00d607201c034640144004040c0c402800d440c0c0c00c01044540701101c0b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 323577401 1250 323576151 323576203
    0x70e07120203040b22031713050105130210050a0e040f09151a01020d080606030a0216050d121806050a0e100203010f0512030a141905030406110322140114010602 71
    0x20347c0c05640c01d20b51003042085031604c0340c1d024000c2802102c003600a500c1c10040c018440700401c0f80c084114820707a1420f4400d01c106100340d409000c0c9a5591300417074400da40c0c0f007400b0f00d03242c1c0c40440300000c004c00028038103c140c1c5500341144e107400c1c1e01096141c1d45003d101401441c421810702010070910043c8142c1d446044014440c020150905019020100104e54221485d80540d40c02290107030b03003240d406801e801c10a03552901c80c00074802090814080e9000f88105001f828190040e003c1004280c41c2c15035108801010300070038880e100b44e9100c240f00714500081c480300001030040c100158403541011440003440000754405440b074442c90025203202240030061721820001b071b04000d103e0480c40c11301c820b00f0307104681c0c0741c5440c625030f60342450700143c003c40a5802640100d40401c08000304901401e902e22060f075004140c10307015480f070514840041c0e08950410300c00d0840720040403800785440d00b941d038030b9902030200660030340052044035410005514042d160131b0300f0044040346 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 323578651 1250 323577401 323577407
    0x60201091b120f02240706060b030f061c0c0605070b0f07080408070512070b070e0a050a05060903070b03130302190b070e061605070810020c070e07120203040b2203 72
    0x18040000c010300e002c88003c00540d81c801d406210405071a4407000070010340540c42d0f280540c050a022680e20b45030940103e2803a0001042e680300c1c0510840c0e00074540ca40c1020002e006000d81c41c0106604c440140c090300042d10048070000030159034403141e4443c1901c1c41e240c0d281c410300401d0030f25905000c10070020b05a034803030320441d0030a400c0358002c0e9a641041c01e00c42e0420200103101075841000080d00c02c00c112103500450302c102da4691b1552803581d4028100b1540407824441c043c0d10040e6504180200d1070400000c203c00c400050440780000e9444102229581044a03655a24840300322103030180354061005a01c46146112480c80035489565104000e01c0c0c0900301d142081440c0700418000d40340c5104031030300070035840701c0354042a025240013a6200d042d4060818640160b0195103042c1c9103034020f403840c8040a17000b60105600f04000c0c1030008800404140401c5009102d44690078a00c1c0300071801a409007950b2280e528003841894144802042c5080c0d88448003d0b00d800420340c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 323579901 1250 323578651 323578679
    0x12090f03140403080c0303060a0816151101090f02120607172e0501020f0309090f0604091707060c0e0637020a0516060801090f1401060201091b 63
    0x1505080190030350840c00301e22407160085401c02480c1c5680042c10724910003001020794401e1900300c03104002c170790f218040c058481c0c440c05c0000c40702c005202d0307007032040701c4038003200c000100000e1074010b4018940c3c5112a0130b4031030300c802c166400c10600c002c40042d81800d842c0380d246841d141d8000c24042c241104001e20300d90200a00700c80100c100c0002c211680c04021007020607410078410341c400511201c4800303078811910b00c580da026124110340c0701402074010003590640b00006080288035540c82d84034102d0b09000818155215903035010038030008220f0b1311a501300c01079031100c80f51250150716261044496003c00502849010000a4203070740d180740072142420303140d11075131440c043c0035904100207000140e480001c03616045900012241d0000c1d285049a002c2c01c100d07845448030403104801d003c4207006080c0010600b01c014031401c00300307070072000811181040c00a240700e803040c956000f02d0020b81150700181d454040310002c0c4001807098200344c520240000c0c48083c80e00b40910700500f = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 323581151 1250 323579901 323579903
    0x3010803030c07020a050907050c0f0f1207050111120414011a04020a0903060e0f07090c021c020a0b151002300d020f0a080a0504030e010c060207060c080712090f 71
    0x800c1c0010f036101152181120030000340000381448103141081c443c00751003500109284146031041c402404064600003c0c02018000c0d00030240480c2030403840c1e141d00e1680411815039882d900e400c2505651120b507001401d01118101c000c00c008c0c18140341c060310b01c0210300e030b18490303da05080a50b107920706ca10a495440401c2200d0041c0da840c200311054903020304551020301400d24207080c07000191004207403100c00b0090302d0b06450501d900c408180044a071001031200c0180d2160841c40311124401d141044141c81600444240040d10b40da4801984011240e007010041c1c40e00c02c1d0314040c140301c40e581c3c0c0700e41da05001801240e11301e1695142c4c4019080b050b104d80d4001d40c0050020b07c01800d08960000c42c00007020342d0786e025059030560b1240d12960400002442010010340305035a184201402568555a5400c498610100445400c940b0071410f95403598208500e800144451146015880c81515002c40c01d00d440381c8040c09881c0200c030340c0d8010ba803c0049000c001400380300d04800031 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 323582401 1250 323581151 323581171
    0x210020a0320010b040c02010b0117040c0902032701020403020a080307050d0e010504030204061401021501140618040e0a1103071a0c070806010f21020f040b010509030d0e04050a020301080303 84
    0x1851081c0610b030302502030b8804403500a4070f0b0050300c1c0071155040d04002640e400a0700d5031640c175400303009500c480c008116400342423300d01190501a040a075001142c0000f00c0091840c1421040040120b0180009640e4017a6a6000130301304214140380c1032144c004d00b00103004d9030030308040b0748400391115a0311658908004902c0c01401c49a0b01400079100910340140c0304024240d200e030241446601d82d480c906015200c2d107001254a6908001c006050b2500c008401d402500303a101809042d8105690840c030781c4040e256030414a03191071050811070f0f0401001804040b2031810480d04d000c44d00f0202c4c0e80240c200b070304107000440411354104017541060b102c03030380d036410382c2820207041058a0700080d80c640248400090911120b6117000e05841c1401c224001f00034200c80c454034031140000d4000c2d00035031401d02010b003d2a09900c001500070701030414500d0000c1d00c20019040225140420020980030f4181030f01c6d0b81818403805c0c2c1d20a0f41d4a0342140b40d03505280715960f0701e00006200d2054 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 323583651 1250 323582401 323582447
    0x1409160f090f0b03040b0105060304020d2006070b06011101020f09010c08041e0e07050a17070c020306090109050f160e0717270601031205070503040f0801090210020a03 74
    0x40e00ca121240000d00c40c07402c452038000d4840104080551040d40d0540d5180740e8080041082d20f03112080320300965006200001c681d0740342d9500d0349070b006400c1101e040b240113903048218903100c0400820301140701e002d0002d45072405500147c00d80c00b031442071a000342e00c1800407000a90103641110074a86c0242000c04007040e5a2078030030103d200c1c41d041241802c8040700c10b241c255035042540402d6441c3c85118102954410408442c903019440031314000890b02080c004408418074110b94010481b0728025840c41c000b600407a10300342007179601c10030580d9140c2c40c00c0c050207002d024807101d03000c41c003020b40b40c180131008848075400124021500c030340a50a0100307040710b026030111401540c0d0741031b66068900c0d00250f2050003509103240c0c02884401d50918510b0420f0100320141030301e90084001c0281301d89402c044416811030710040740c07a84410440030506007051100d0200400031100003144079040c0d84140881c0c40d000f8805901075501020083c0c000940100080b145c2c64004610014 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 323584901 1250 323583651 323583677
    0x1b0a03050f0f070f0b1b0903070b09130c090510030506061207020a051c1101020c07090f0b040e01320705030c09100e0406060e011b0309081006140916 66
    0x4a640301c2ca00c40108000d00294514081211158005101d55044488841905903040201c91144030b40c002c1f666241d002014207021100200e40581190b10014122103400c00007518044c0c04c42c1e90140e4000041500401c080100c3d24100118950790145481c0500080c10302d032012580c5030040c44405210600384030000744010380b003000100b200300d8003c400c50714102440c028006200d8080800000004c0310803100300e18a95050089501c3c00c400c08004010562808070418006c04040c120180c3d025140c5400a05c19a101e011703d8100d030100000008030012803000b03481070301100c118251200e207805c080a03284d103440404103561044d25400d000340c0d66070354400203210701e2250402c81c80d44401111842c035a000d511510700101e2240589082204544a880944003c05011407481c0000d0700040040c0d00c0c0b00c2c01a8001349094440e0070804102619a059181881c264911004e0000e0356a98104a402d83c4001c49542c41c0806540e03801107410601d6226003410700c0740403880140301c07107211006 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 323586151 1250 323584901 323584927
    0x6030f02060304061509020d1a0d02010806031608010203152202031018231003170c0613050d0e1305060a0b0a02010e0c040e030403030f1205010603021b0a03050f 71
    0x4035801ca55040b40d00d00094407520303810008c0d005540d029001c1840c0603201003003503440e4020100200801032211203468483d80c01160728040c0200495018020480000700c414140414a0080c0c41035000140e100d00e480801003000100c8801c001e44a111100c00040b41c0300c07120440005000340740000960f8941e00c02d8007590030502c2c582c0c40b03840641c2181c0d11000d4008440e43c82200f9903c0308541180da103100e42c0c0460f0740005015650402c0005852400700000303558685c091042c0951245903900744100804c55a040010841341180d028601c0c0e146001000360502100108072002d04002e024022400081880c20115084848400360740b08081030030b81d650641188000c0c00d046082e1680d8002c80e000c028013a04601c1c0183c0d20520a1440e00200e0345410700501c1c0707050501c00000d41c03c25142d51800c4400f85215111041800b0840c40300300080c0d201030082c3ca001e000c0c0c82d1030144c0d0380e13055840c5c0107150f0b001c0c15650183c1d45d001100b4120000707620104581c0d1401200100d142c540183d08051 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 323587401 1250 323586151 323586161
    0x71b03080403060c1701030c1203020a020303030f090709290f040908091512070302030403090807080c120d0918061e0f0e09030304030c030c0503030a06090605010306030f0206030406 80
    0xe4111000410008100321180d00a90004403071540c600c500b001d10840c00040c50602804001c142d400592000d0000c40130170300110707800502034412603848030055004030341541d2040e5280100314908108129841c41c0401c0480d000b020710039002c00024642103142481e86440c01007409103054581c50609081d502c1c40036982d85810002c00800502c1164a4004c50a511942c0428002c800a04803190906c100005850f00d00181011034111581c4a07031084000354001401102800942180480c000c88100100000390980400828100020724100310f0742d4810b581c800302e456070002ca1119015581b1024800c112500e0302810744510b0151100d220242c101c5800403c02881a00002010750701489140e000711580c02c00c80307125041d110444186030650848985140da441000820000307445070000d410703031034041e28100c60f44c03555540e1020304503403095424080d00c50b1100e2007071010380313407912889004000c01d080c1003202500d181d440c04c0007000c1c1300801a03c120300200005080c800e15401c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 323588651 1250 323587401 323587403
    0x301090b0a080313150c020102060103060203130f0804091503020f09191a0a24050309070e0c0d0b09130b180109050708010e06010f0b0c07051905090c090105071b03 72
    0x1070f00e4989404404c581035a03d95803050510080500024081300e600070000380c940650113901903c00c80e070071522010041d600280032410f01c902240d07600030205e05840320440550744180b0300c1c5d581d510f160a56200c207540424842042c201081d1504000580d40d10b1852401c45400b600c0c41d1000ba9514803441e100d0f00e4038809500c000500700508824180040201c0400c00c0c00221045130b90305440b05a110641e1950301c480c50504212640601d40440c022805564440503a60481d500146c48050007101c0100542c0c0b030500d0a0700c0802c11410400780d42c09101440e9005640d944102e02c0c01850b41450a03100c0c90001e005441c0e80b4005c80c0d80c8c2030b004403d182001c0345000c002e1048070f1080c908513646042920500c1301552030119044035114001c00c00c2c9040340c01e100382d41040d0310b05040344001c881d40f00210b4090f0b64800d10500240765100c1da00d000b400d0f1300380b480d903c2004038641014040c00003001404408107000401081801d1381c0c000080ea8030843d042788500f0308050f00042c1e1074000c6081508 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 323589901 1250 323588651 323588653
    0xb03010204120507080a03051b190b0402010e0306040302120d02160309030b0a05060d06110c1e0c03280f050f011d0604120302090604050a090506040e030a02030301090b0a08 76
    0x81c01003403141016444a440034030500c100c1d80c003aa501c4134507a4031803c480c100100020020070994000d100d4001e900442c3c200c1c000140d48803010800b01500314448524803c0318058100001c1100f5503800156800b9a40010380252805140c541d030029100c1d2486584440304c40d6001c80c1c00e910400071035055600c941c44854911089036400c0c18040c0002c50700d0710080b41d102c0c1840c3d00068980c3e000c1e004003401404c000e800c45181069aa035007030b000c0e04078003015102001c4180316100d1804410410701c1c4240c0c0440701c1181130a140501a141424181c0900030300a0f4025980360181b2200f440c1e80b043c3c4a1a8480101e00700d07031551a003003440302c030000b0b006440c1d0300c0340403042c4a0094042d070046107080c1120200310b0404040008203900c40381c084402626039140905042402c90007a00205500800203000c00c2c80d240c0c44d140003c00c0c075401a002000c86940e1035013000045d05007841525001d8030210021406c1120121000f9502c0c80140a110782ea039485000303c03c9591103030350800d000307440e401d4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 323591151 1250 323589901 323589907
    0x14120c010e091506030906161d0609041e1a0d0b180a0213050f0601030902101d060f090307090216060c1b2108101a13030f03022415040b030102 63
    0x1013903aa5860003920901e0903190441d0b046108e80b400341d0030600b0394030b1000007044400495041000801c0d0842d0001a80180d101d80c814000d0401d440140c41c10f91500c8400040c85040034003111404603000b000c240d01800b1080d02c5800852588083c3d03541c02510f07100c0b15098238030101c1105040044200000b90400518046a00c00300300e00d803c000d02c28030805809850b503030b46050046042da042c00101a4005440b030310180f2034a0311609151840d422541065901040d000003c00c55135806000081c02925001c40c1d032060500d400d00902d401058094000d500340500c01d000803480349040e0b0701c020032031a0f980004488160250070860701900f2030303482c49502c200d81420100c089070651242c2584502c0880c0348500c9040c0940c0c082c174020800150800361680c1407803100b1480d292072896840c501c00042c004252480141c825400285102c0e2520002106c95451b01038a4003500e194014548640c10b02081c200c4404002c142c1e51103030602c20044503480d041008280105174001d401e07034040d4000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 323592401 1250 323591151 323591161
    0x6060b04030f29010306020901021c05130f210c090603030806030105060108091b03070b030c042102010219060f050103050616031107020f0a0f14120c010e09150603 72
    0x15064420180307019640f40c8a0221144400225601c5004464005041030000500c04a0013039409400140c0040c0120740c55600e04c003a121800d2000034008800240000482ea5040c00c40d007500d010007805540c11070460701e070502c0c0d0000808201c40c80340c82c0f40c81d80c03200840c4050050800c209001048035070810020592603040c010001c1408541590080d0300f090041806940300d44000b51041442601401840c20100788400d0b0284840350055418883d009002c200702c1807000095018910f0340200540c1d6515000389140501d90600f90401e12141240c0300343c001d81d0300485d0001c558032485068042008917850000010452085001d04c4580b602d03001000300040081d002d80a50007034982c0b10030350540954120203030303440c4106002e043d510501c01c0390010f0400000109514100910007000651212801281802c1c0380e4000c8034501305025000b510f90810f585480c81941012014112000e05040041c101600b07900c007a9008011680000780c420784015810150164020403c0d80d480c101 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 323593651 1250 323592401 323592413
    0x10020613030809151512150402010e0d02032406100507080d0204080d0e01080c04030c1404020c0319090b0301060f0e0303190201051e090d08041505180c01110309090406060b0403 78
    0x1008020900485c130020944155110001b4203500003007e80310104415500c590044030702c1c0030701081454000c07405408420041c1e80500c0042e484040305804402c03ea039a84180030910080942080d008004101e90442e80f15449021109060b070850032042d070358124141004003d114544c8103410710701850340c5d182201c40d840000c010f0188426a6224a1a2521403050840c0e206512008040c984161030403c01c44040b1000d5000c2580c0080006050010b40d04031941075a2041c0b2900d110004090304070703500c0d030b40c100d40140c001e0143e00000600307560500d0005070000ea41c0e4416002400a0700c81000e00ca030703234100201d84c40d4412442c001c4000746041c003070181c06482c3c152500740d0004401180c40500005c542c40c56403140c1c003594020440d1200500742501c401401800a131540619003188951149841c01000d000741c0c85400000d60400c0401c0f611814030342203441c02410802e40c8a01c112500d8400001d40716000c038102c03030244090f213503482c01000a02d030581c0715800c210004030340042403040d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 323594901 1250 323593651 323593681
    0x1091502030903070806102607030309030c08070b090603040c0f09150803070302031b0c090c07110316090e0703120801081e100b060d0f0b1002061303080915 69
    0xb205804484803162940001502c0300000c0b2002074041d01e04480070040074401806440c1d40c01c100c0c40420004004840495080a00a810580c0481c856085c200104124801820b000b40190b80c090180c003400c100014103148140c10089108410220124084c4194526828000c01501c0502407040360348e007000d8000f9028090311f00c640c40b00c0760f842c00102290f01000701c84582d40d055010318a410b1168482d01e00308011440001502d203c3c90610a207191245042180110443d44d940340d03c0e914245030901d0020192001c1c6400780d004107400c030201c0300458254209440804101052141d40c040d0310628004182d440602508105034500780c2164000102a040c1d072940c0040c0d40d03039050401c550107955500720301c0003402c0740d00c500101141001d0543c041d0b001d0740c42c000c010910704022520035800f6960720401412800d66200b41315555031801c030084071707414419400078103040c1c42c0203080f40e180854541d101406010160f0002048528148920f12508442d0010404039080c15112900b1082d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 323596151 1250 323594901 323594917
    0x207081b0d1d183c0c1216050706090b070e0a06080c1b0a03020606100e060405040906090507080105070207060915121509090c120507140109150203 65
    0x505407004907000c10003024650345941501400703640070212249040f030541c04004182c07040011003403c0038840c1402d5080050921a40d844010400c215078100402d5521406000c42d010141c082049403020717140703000901d82c444118000b41c510f10f2292081510b05104286005103103d02d8456014104150700030200e00981c0990707683c0c60414841014071130610310b00e025403404034104000140c1c02d4a40c000051802c500320b5501c0708a1a250400540d1821801d140d04401580205041001b41c0c02c2c120003210386051a8901042c51a40b14004180d1920941c010607003e036868111070001c0c011a41c1040d80c0707059000089860855850302264001c043c02e40c1e09000500a084c00010036600c21840c06003925800010302a24800b4400103860a0880c014144c0940b91158512038090410404400040281e1580491300d00c1441c45c00a11010f2590000000b4a1010468002140f0000741c2d00701640c024505601c2031148050060300c0c01040d65100e00101c820407001c80d914a0b80c040085c00c076071 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 323597401 1250 323596151 323596157
    0x70f03050c011b060509010908071a0f06060f0702041503080d06060216060c050c0301020c010209010323061324030201021005060f0d02060c0106060203220602070302040207081b0d 79
    0x1850004641030510308000c0c4040f0280c62150301c02250180d0b1000c0d0b00078118500000d00d414032540c2d0000749801462043c3c41b116139142401a511508405160f44460101d0b1902c070145000c00c0000c21030701a885607000901004a10101103482c2c40d801415080c1e8001030031040b031035503403170120181e91104040ca400305080a80c0001c51070300004500003940c0d41040d07204c0215040c0001201d6582215100782e071644070302c001c40441a1028070061611130000400581d40c0c0100c2d1002509862609480102d0342c400d400700551005040006140c102d14101d4524580da900c01206001808805404103111103820840c03180c030303100341401e803811a03100b80c0030f9620850b000364006040b51405c46040c0d411000b85c180c504a6898200d4070084000d100412031800c1010017010182140c03040d030052405a0300006482c07406040b001050961989441c0b0300c1c1c40c03160b0074030000075100c3c44240310090080f2f0f0041035000821040350300f9035001590481c100c100441104954503a944942c0140b2008 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 323598651 1250 323597401 323597413
    0x1011070c080601030b0408181e0102010608150f070c1a0601080703020705100203070201020c0f06100f18020a0e1818010b1e010c1709040510080d0c060e070f0305 71
    0x4864400b0454504881d00700c0740f00c2c425580d0300e40301c036849036100b40d9001814003000000449565107070358900c0c00c4d0000c80690111917403101c0002a00315007103600806540c1c1d00021103903c00d506031410145e84803894080b0b00c521600c074848155001c03c100c0500920130401c817020000c52000341d05034144180f90903a201c0440c2d40301c80740c00303604038468103070050f0407074000c0047e4400112040d001590014014400189030a103401001410140743c284a01c050f90406002d01804810201e501c0000e05030701c91411110901d40b800700704400c1803001440b041300c5e40108100d040180640c6881c00003041c00391101000ca502e14450402d0118100c030f87d120540e0b00e80300710342c6441c43c0c14411410200c078050101d480c0ac201c000540c04020201d4405241000403000010300050342c1e01c0e4014865100041a01d5100d080d00340801c410f90300001d00341034944803a00400c0102c0304000031044256152401c00c403210441d982024400f03003180155500d0140320b003007400200700300d50886c0441101d000b1000c0c2c541c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 323599901 1250 323598651 323598659
    0x1c030213050a060f08090304050a17240417040509181b2211040621050f0601050304030c0516030203100b10050d0b03011d060f07050415021011070c 65
    0x141c1e0b00c60b039008620002d0810401002454091101c040d0406100d0040f039003800d03035400000340f0071201038010100410042e21140814039081101107058511541c4c00580038040c07000035070084c0802000941075407000120425580c940710100d801038140a0301c0182103141440d145440403c1210407841d41d845070406440048400410080c64110010091030381c00c828680e80360010341c0300544c43c0b011241c1c0c600c80d281c0030002c990020401404c89403550000c1e421501e09003c102ea885112405403281000c040041e508010113640d85d020009080060304e0b40c43d90300341150040d48900c3c0040072031080d000144529603002c10710a049a20843c1195910020480034100382e442a900454000814050019642c2d00034001340007840440840082c0450107840002d007540c00c02c0b844030400c485031131240c40359404203003c1d0a510a12944510b110380c10300c00c000402501c070300d200740c024038010b01201100150bc248081c0c485941c1c0444103002c5028800301840351548440800c403180740f20584001 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 323601151 1250 323599901 323599909
    0x13050708090f060114190801200408030304120e0a06030632061b0105040309030309050d03090e07200c2701050d02040912030609050c07170c1c03021305 67
    0x310103490030358042c003e1640380030514145041d01c40c10b5103902190709408154a000300000560081800d0800802d442000508408040f40010500400311074100300500510a00001700c9400551222413002040d85030f041c1110011484070031564420310301600000d01d954140c00040981ba0564240384070350600b4643d038110b0b4a9001c15940105800d0381d0300c18020301e005400380c5030101480181c05003a50601c40c0c000d0840b40100c03411070118030142000d0090550005228014007400d852414003e92180c030040c0c19a9030903c1210b840340d211100040c40144503050b442d2007210b05c80e40c0301c04404511401c2e01c1e02c422443c0d0b0018001e6607080024000300004201403101c14a00c940f032010641d003024240000708039034201c02d981103503c81c0c0c0c0c407400150103900090aa00e030319a400003141c038100100c0740b05840004d00250a03a00303003486684007044da0404402030203d6880c020030b549150003c0918207101c1001d2741d419070039808d00104113000e601a00241403012102c602a83c000c2d89910800c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 323602401 1250 323601151 323601163
    0x4050d14060109231b040e0f010f030201080420030a03030207050d05090a0e0705040b0307050a11010b10030f06030606180509070303050301150e030609030705070806151009051305070809 82
    0x1c001400d5080200d00b040c00c0c1c058200d900150300d58480c0125007001c0000350004d90144e032100240501c0700b81005184442c43d007080b0b001d8500ae010441090b407950700020803840010b0006001e01d41c0d04840c007625a2044960b412501602030241c400345009810080c00039002214191403902504041d480c0c81fa03c2042191075404008040000e081c1c02c08c0281824000010043e005002e0200001b20724410b045000e90300c100065580d4a544206522006000b24204180c40d00300c1e81c18601050800d43d500134240c200b240c064940042d182071900780d411301510107540b0103800319103000004101c01501003a0042d1800407800b050000c1e486003d12290744200c10711015001031018030050240d540701045852a01c481481c10040384171140c000641004000c0c1c2c0c41c00c40c0d81e400040d1401c01c004052241200070903080303010304100e00c3d2141d14012803840540c4c545100700f0a203c4071040440c010720400c4c01809014003070204554500c00c0302c000400040c2c0b0424042203280700000d424100008203 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 323603651 1250 323602401 323602421
    0x60f0903260408071401060e1501080c2502090406020a0809070b09010804050c1216060201020909011403030d060e040b1612050a0b1206041e0302031c0204050d14060109 74
    0x10341c0300d035541e0b9448040c8150080d0104591000d00c00780d401564440c01d000f5503001d40400e41202c1400c4c20704448401c018800b03a110103052280100c00c0007070f013440320019a56180400c0c000a00d804c4200b500c8210809022040254031080d918184024443c0c2c03607018011403007081d102d680c00d40e15089900d136603c01040c410540a41410400a6199485010b1040d080f611901c00c88070743d900b0780d9001072848600022000c42551100201d21031100e03543c1400001044540021840c3c04070400205141c1c1070140941001c49441002443c0a5103040040f0740d44400d0000c010014152206c65440c201903041d80c080d249908030101103201e11440844142c40900c91740c035400420800d0504410103804c0c028905001c0b266a0300d00c07a495516901903000001c1030030006011103240501d0110020320200c603106042d40c0b40e8605910009070008204d85622200322500c0380c0d1a51485000c40103171003142c00c07040e0040411030380c0a00700036055100702c16880000054482d1a03890314404011aa00105 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 323604901 1250 323603651 323603717
    0x501050f0a0f030219080402040f0204080a080309151003110609031e0f030c060901180308010308030a060b07080a03060b0a0c0b0c040504050708180a030c080313060f0903 75
    0x401d03040d41c24054212000450000d090240c245000100d0300000c040340801e0040110b5040420841186414480c140729810429021411b013410010a03503552880544024082c2c800000801c40b410010041081081751099482d5403920348031703040c148014400d20044511180c04443d81845d8070b4200c05440c401d00000d8000d0522501c41020b141c0300c020410f401721402d01031859801e00320a01070000300f40c0300c036810000b0a00750400c1606542141d6558501107a031540001c51341001a520820342811203811142c034903120303121000300000900e10359001760211080000c96a00700040b41c005052080c41580742001241c0c4c0e940c202074024440d010300b4100183d44242000001210700d0545500321582c0500705081a4884004c6003c035002640c514001c10300310001c1100040075014130521001464010b48074003c40c59a02803d5a200d0410080c003c06010000540c00c2d000c050100d644660449801c0c015021202c406c1c0c0020310040c0810f0b03002a4410041c1d01040b25440360180a15040306 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 323606151 1250 323604901 323604907
    0x160e0f0601080a110a030b01170c04030b1824100513090309030804030305280203030c071415091501050f010311040306020c010f0b0d200109030803010e100501050f 72
    0xa00460b01c08400030103508516548403684440b190f4040301a14003000241c600284284400d40003501c0d030700c070f01140517002c2c1004c41c2c200b24030034031813506646c00c0380c2d0b00c02c040410300e4980c1c80c1d1040a0302c0300b000b8101d1580c1314281070307500394100105074070000c110b6840b0110381c19219400250b2005500c0c1c05602e41000000d0420268844030b42d001414940c024500340382965181c2d5107944d40da0740a0760050380000c401050b014a07501e600d0072520310111000007100003001d0101006516400000c0140e231200101190b80000c0c00500f84851421820003403d0300d0382440140500f4801c510b003512080c0c55032082040b2840c0001003c010b050684100a026a4141710f03140c0044000e0200039030504145c2c1d0007400000b00082c042e00151141160400c00070900140d1800f80c94200c42301e5046c0f2034400e103100c00031080420501c00c554403030000d00f0380750401d84808490050328620459071004000e0711000000040c0700d81e05100640c06240904460510b031030f0380740011100c41c02410a00340d904a820 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 323607401 1250 323606151 323606161
    0x8061302010e09040f0312020705030d0c26010306050604060503150f1e0a020c160303020c010e1c020409111e03060105061306030b0409060e010e070512070e04060f060602160e0f 78
    0x30800880c0900c0c47c160090b2520f40070f5a82c090071900b00100940340242c55451312600d1304c0d08078543e0b045489115161240180308105959290380c410b03c0090049552403001c201180c0f200c0c0c101c1c5003c2c0c200030302222403c1500c10740c502540d250807140100c0a000d1100840c41460312040d40405a101d400600603050305c1d0311007031000070f612194980b40b0500c03031402c3e42c12841700701c285a074005600980103414052180000500100032456065200e0010400304002c0400c04034080841c840d0162800980c001c0107151003814086d007040070301c0d400f50984102c594010380018056549607010b0301650b000366650000d1124a000f0324076450000c0c2950700c0c080c82541d1003940188070010000f0004914180d03540c90705012100989040301c4281d44440007005820b10401c0000010082694010380e4004c00409881e111001c40c000d03007803010708410114091200d20380000c60301d102c0e14141004a07580c1c0d400301030740d035446010200002120203000001c2d80f0b8030181c20684900e10400030780840d6914 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 323608651 1250 323607401 323607407
    0x9030618060b031c030b130507050301060f03050709030f050109061e0b0904080313110a0b04080f0606100e01050f0315010206010608070c0609030c15020309010b1e1908061302010e09040f03 83
    0x42d00009031380009403046247e420388940d020310350144174607440700d95032541001e600820304c03403400d698202854203100c240450541d00c6000001129003200320005001d41900d03000b4054504100080c012609004402010303030b0400880d0500b10700d00c1c1400b080b14803001170502c03404a0003124041c03e07a8006100041c290b6805a07043c640a610601c984515440f41030002401680d15070000b51130220046000d1001403001c0214109043c0f802004151900e40f83c0d0019018045a201000401800c644004e103d41d00030300c10b070740034089905400c503245c0c0b41c2810041100c0015140a9005101d4100001030590140d100e0307900a032402c3d070390210114055260180a003e041100300d0030002c1886201e00412400c40c045c1441401d040c4000d40e40303080544480b420f540904207024440c072001141c954075180c1d40c202d180103120055610301c00074000d0414000d000e22041d48102050b0140c0c00820002200164008020f07502c00d07200d10011002600c00e11046402c1101c00074813807241c1c1d148880110340 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 323609901 1250 323608651 323608661
    0x2070f0803040b0705030c010204090b09071b03050a0314010311030d0903030e0d02010e040e0109050124090f11070b01030201140c151f06091d04080a0e0109030618060b031c03 77
    0x7000d05c0c2120701c0d001c0c40c000f0030f5089138041d40c0458441c2d9039540300c1d00c11500c0c101c044150403d046142040c0e1402d82038440c01e07000000c4140040900100240c1580158043e42181d0540c0071507203c0000150794904100074405a8940d14921038003178100700100d96400343c01000c05803a0507680d000401c41204040c000d40c000c203103030268140315081180e0182030b940d5006541580986000106405c8004e18019007500c054029040d41815099201100301961901039022038202c042c000c00d00388055210107000b021022018180018001007134014409501a014122031003a80e94486044005107081c0c0640640303580105690080b990240d284030a1014094000b10300da0120028090500303290f1601344403560108020038880d80b0308008450600c0340c40c3c180401005030105603403030599a1082c0741d125000e480d01c14440050320f45507032a48192000000356a0120042020b50288407580c14a40c0c02c400d8105c51f0203080400c01c40b00c50602240e54210f40c1540b6514075502d80e001d03242540549 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 323611151 1250 323609901 323609903
    0x911040603020c0316060e01062309060d0b0103230102040302060d090c0504150f05030102070309031b150e03010b010e01080112060b04090804150207030209040308070c050d0f02070f0803040b07 85
    0x203c8180f108845ca91031550002480b184110b000141d0500220905402d441440e8428240080c0b610903900b2542c0c1c1600041c61403250884558800c1d40d03640000440800307500c1d00c084c18140c01c10001100304248000c5c1b0030502d11270001c942c0401c0761850102401c0c0d118501000350045030603c840004041150000307450103104100321268981c403400410300703d808202c51003900200c004400c0150f060040c1418000e0071303041d0b009604d4014180c502602a16951000510346e03240740c115000c0f02c611000000e000351528401009581c0402000100b0344d18131a000315102e5442c10255240c55801a035100e4122103044c4c441821f00d80c689025004880301000c400d54040e42c403541a4125551140300d1307001c449102d600501d41715410803290000355000c403500d50f015540300c01d10610150b519509100d5200c0d81c18946684079590720300f0b003215101490040203205115611507080c1c00da4200b0140303c0200001d608446810343c3d0380715072041c00411881880303820f401c100310500c400602d02000b01815 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 323612401 1250 323611151 323611153
    0x60f0a0c0e0d031709071401031103061c05030a26090a060c0c0203011806230c030403110f010b13150911040b0309060708010506030405100506130c08060a0911040603020c 75
    0x280e203940d20082000c0c000302e8550a00d90441c1b40c09101e181c0403e040074800317160a1a04010904019001701d03e47c2c0f10141c2410b00c01d1200d010b4100c250759484c103911180c2d95001098a4030741e442c0d0344010f02241d003210310f03400074200c0503503001400203030a450192240d020000240300c6110381c0e4503041c00038044001c10341e0030004420704040143c0c07402d004140c1d0704902c5684415441e80d00d4240f2004071030000000c8e944a0b405484100c5580516011241d046141400031580e282c0f900d14041c0c0e00c58040c0c1d00c00140074050711140313400701342040d4040882c02d101655080f680b8811692280116203100804074501e51440d0001d01054106a20031340c0b003070b140c00e880c003858075071222611005d40c0c0040300c0c85034003503101d201001016540702588a0040c0400d40d005400d5050982d030b03031912140440541203a644e550710005540c1d0f9141e03002518541604041004000c40310700c001821768804503001c0f400340c0d12150700022011064450b290040ca6202805400c0504010046010350b011403840115 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 323613651 1250 323612401 323612417
    0xf02030702240a1107050a1203080901060e04050331030b06030c03010204080601080f010b010806010513150201140603060105010c0803040c080607080a1d07090f06080f060f0a0c0e0d03 81
    0x20030100c540140060480c40e181c480003590042c106a20b0f01714031750003450249a01810411484510103210b00c0c0c26581400c180c20340b66520a805401440150320107040c003c084d1081c03009110000c0000c00042410070340360070ba04155a0258401d0100d0701100300700300004c1d014100042100c404485030480300090130384011040b2040044d09a03001a00007a00f00d030011401003007044020802c19008203515002400744860b91b00019110f141e009140d60b0500c60b0001d224100021860030500c0604034840d04010320105070f60000b0b0091140095403401820550042036035860005411030480714169a0165581d03256514801613800c00b03001180d00c88010f00c0040f85a09051010364440d0080e80d4801880b4581000c821040d00c14090720158644610b040c40e03456090040740c45c1041d581042e030082203e014020705035008203103640c49001240107086d507200326080c02182a9024850a0510041c50344800458904481da901d602c1004100c0c2100d5001007401c100e100244070b24000d08180c40 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 323614901 1250 323613651 323613709
    0xd0608010c03020901080106020c060f09030115060e030c0a03020904061e0207030c1a10060e2e090e16030510031a0403020d140d09061b030b03010c0f02030702 70
    0x20941e0440d0380d0410100750042000c501c55644080550700414491000300080e83e406004102588944120004401400500903c103030700c09400446c1c0c58074498030141c0f4003650f641c500030700124030000010f00c240100907103103005191000d10241078a400805101c802d44840d6203070320081683c400010050700f400f00014004201302c0c0302030200b4030b001e91504c541e900c40303a20348910941c1806481c442103d040d0030911801c079010a03481020b4907003030700340a1207014003640002c55546500c6002007125000c2902e84882c0c8241c8a034060724001180c4a4903041da0712414032040803213048941d00091220384c0028004903100fa00303c00c0d00520004006032041e0b0f20707500c4c0c02080d4541b00510182c1f814102c000c0c40205036041004071400041c40c0742c00e1503c030410803c844183d21401ea0400176035501c1d68070703040074840070758811001c90620589044146a0114000c0e000d0b0501200141c03195103840686402d0034000c44140d025128140c1c0914035005440d801c200302518020742040740c40e884824a1383c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 323616151 1250 323614901 323614903
    0x3130c030c05040b01081e071101020f040504050a020405031c090b0301060f02060a020301050a050f03030c03130303090515040303032f0d1506090e0405030c060a0912030c0806060d0608 81
    0x80954020125103411509140c140019a4413004505040021310010001007014207005600089541c1c50701310507640302c5500071640404e0701c50021905501c0081c01400c405480b000400881d030080d5400d00c8151703611041c203c00c0380114442e4907055082101d002020701c0030300b20820002e00544c2008885562a8a0b08160300d8100342c100710301040c0001c00030906542c04001d080e60150500c00294619030401c00403490001d028442d00d809107070380600405180d581402600d09801f03180080700c2c1c903406101045100300c61144810350200b01b05201c0401c4c2420708032460303c881c0045400883c40d141ca5a64103c004002d55001c80090700c095114140b40c4620345c08a80041b48602010982c07030b5462001c00da02101c41080c501e00e03401004400070403480d034021110f80c04071400f400c2c0c0b490069503103080490551041c07500d03411250080d0400c07ca4660702e0f80e4000301c3e540b4021b50300800b0728100c41720103904644120034500c4c04602440c000600c3c0c1d1604000514140200790070101e1540d903103003141 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 323617401 1250 323616151 323616173
    0x903190305040213090c0504020c0f06040b04030f110601050603090102070b0405060a0b0609030c0603090709110a11030901080103080c010b060d0f05133804051605040605060f0313 79
    0x1200020340c980c0e0900c015480c116420b001c0c41c1c0c44140341004401c580307035030785180040780d885460700480e00440c8500c454541030041d02d550700b100000751f89403032a081c500f03540e0307404080394110b0100740da030201d03400708521500707104620200d1310004016036420b0104015142e04002d219400c103640800c000c0c80041c200caa40c0e0760096101c5d000515850414400c0007099030380c64036000d40151400e02c501ca425a07000900d85400c002c059038180d039285c440881803424240c03a6001a203035282010700c0340b4410030a400080007000d2a6560741ca00c10841408040c2e143d100706c01480c2d0005030b21100500c00b242c415001003c1c0324080100005d550030500000c035869800c04d107516004103a840205080c917040b43e000e8564004d03800d03807a095104000c0e81d282c1b200d000c00300c2c81c16000007052888081803040038041c071b000c450540e96000e446610300b1b894566036400c490300d8031040340d615540c000106802c15009032001d0f5003008000300d04000c1d00d0240b100c50382d0801001b40403640702e15900ac2c0d010030130300100 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 323618651 1250 323617401 323617447
    0x16060c0f05030705011b051e03100b0406050405030c121b12010f0b0f01050304030206071d09130201110c0604050d110a231c0605042402040e0f01120305030903 70
    0x1250006c500d11500380c400040103417010034400100030304d481510382d822043e0f0322100240182034603525146191264200e49070011003200b60000b6000ca03001e50090007510483d0800c50480340308102c86010305c0251510038810092660054900d01a0f211503036242e806105805450701240e030325421446400d42d0710304200d588031169034486000c1c141c01c1171646907082c55000e0a2103455420180c1d0001c0da10100103220001f009001b1000c0310045003400440d1800520041624070b550a104540d01c040d60040c01c412404100c24540c8aa002000855442d1070000000d0031641010714210a1103504144640111440600488030040c01d07a079052640c405801c2d15110500d140146840e40c0380c6401c800c05802d48a00b50b10412568928610516466001d500c03d01c00704242d00c03545000481d405800b4080c2079141c1035044d0000104031180c0c0684203d40140c2c0020b095500ca4038202c42d080d800038081c0c3c40018032028011008680540011500a090f40084a01d07000d21810202c0400d8101d005d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 323619901 1250 323618651 323618653
    0x602160219080c040903050301151106072105150d0507050d111206060916170a05100e09030306210a050307033507030f050103060e070816060c0f05030705 68
    0x800d0000030400c20414401003c01e0320100850300c41901c015103540014821003801d0315070a00155480c1d440b4448078007071703071082100b140c0c15810301d0007003d000800454404c4204401104000403004850701070355015064022411100c04504811310107105d16081007500c152050303010008681d100c85210328103083c019403001c000610290308024050034201641c0302582c0c4100184070450b030b2041c0350103070081c03042c018602e402404900155485040304880081068056041040481c00b54200e5031280796900445520151900c9844410040a03110901ca60740140300044140c1480c0b64128500c4030103520030a80110358208032841c041604404030742d581c001050960406800040110340c044d002032096444054140c3c0c42c44680035091050300d11024040041071403240aa40506482c0a822009003c5581c5038182803010700b2000c07511001d54440c0080c00184404007292a0781701c0c0c065102e039000c95500c2c21f141120307403605500b01a501035100d0b018102c00502c4c01c100070036000340309074 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 323621151 1250 323619901 323619949
    0x27060601020f060103030212130b0c06010303030e1902150720011701051003050a0609021b15011a0306010201110316030615020a2301020418050a06030f06021602 71
    0x8002070501150102101c031980c014001400001d8001c2914940b002c0e039001900d894056a400f031b0075031200d0031341c8541503c01001442100000011a40ca416203010f1b80341031140e841031248180d5540001202c00d407103041903024400c014902040014102d1900511460400d05c0c0b03601c03442e60360000e0800203070b03401e45844015403455800901001c10300807604188245c66140001003a50444101e20881c101a40c03100020050306059011101404001104646491520841c0300c0684100041000c0f103103c0c90600410002c0101c20260503681510035080300708240a03860702c1a504060112810742d5200d8500a0342150b5410155100d509003940345010b8841c43c8601030210348607070700b01c2c100d0f80350403460541c1140c0e00081c80c0d094040e0b102054071008070100d1411310001d5016010b00070b5550000800140c0c0240c0422050340c600900341040200707450784803101d011140c1c980f0000b4052910700e0981c601088140c1d000d8101c1400d40c05600524030340f9580040e14001d00f4414202d050b0b01c841d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 323622401 1250 323621151 323621161
    0x706080a0c0519110d120f051512010e10051608010b090d03020c030706170709050d0303090f0b04080a0215040c12170a0201050613021801082706 64
    0x20a0150380c0003000020204100500034070014000d20541801c10944041500401101803054004010801e40b603401c0c0e803204074410710010075858404034054007040c14040d4080e001c003107612455010301c801d0b00750581c400c07054500f4030003c0c001c2400710300f860755070b0f801c51070b0016103082c09088840b03190035000041c00d21301034240512003851051200c08104000740140901000c0c1d1040392840101113441000c600703218607040f850040003185154141c001c2940c006076250700075000c1c407070640b02068140001d6540c003104959000c031511176550310424400a00010074045e91080540764080d0580e18950703811b94841d460a010156070441d1043c6c0006915500940d040c40a400c00b01c450a0305c4040504140d11808038aa00074000e000c100b00e10201002c0820a01c43c10a43c0d203030300d124810380c0e00c0c1c560541c0301a000307040407940c0d42e015240d100e1070140d14913001c4c800ca5210110214421191102450044559210081550b4013a40c0030061501c031034402c041002048201d0319005040514007 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 323623651 1250 323622401 323622407
    0xb010b0a090b07050604080d0b03011803020106060807020309010507080c010c020708010e0307030e0616021e0a120503030a0c020f1005100e0610030504080f07050d141c0203040c0e07020706 83
    0x70356100418484003440b0fa0000514003040036500a0781002d40c007038131445402c41c6240107103082080181d0661a00100d076030b1382c00000d414071603d1800fa40080040c0d50750f840e03081e101c4000866001005810401c00c0c1c00c403540c090005070070402e01804130a401d000f2005905402c440c408403400002d0b03031202c40d040200040c03d000e100d10030800c0c02d0155003440542c4e41d018280c00c003440246842180081011810311105005042015400030020300b80000203610200c1c4446250702d200340184411035002c14010810010164140d61000003140396503140000d03a002000340c98010400c5005600602920f03d104009801302400b0700d51000070641444820300040300f44036400b04081509400c10400c01c0d50750401101080001c604010a491341c49151840380c91050500315a80c80b940031030f000040c0b01c2c00203040c40d41150319858000000400c1f111f901c0050191614480040d9500f45400500600b00e8003d180c01c580b085480081140d1648260108114204c0e004801030784420410880c0b558 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 323624901 1250 323623651 323623667
    0xa02160623070908030d0207020303070507030309080d1409040b1f0f030501090b060a140d0908040501020c0906030304050d0206070501060e0f01120b0106030203150a06030b0127120c030b010b0a 85
    0x15801c004107442d2810704c403030b41c40e030007072250050b00c1640c04101315042d506c061007100d03504c1d5441002e07625040d480385006042c034445800340c0035542c0700d035151440500f03000c1c00340c40400d01a100c0b001c03410301e0f00710020000904080c50f8126003288200848444241071070980d030110091684580ca60700030325110040c115807050744200100743c01d0051140058943e8000c03582d1100c0070b4901420b040b210032280611034800e8155068003039140415010508c41d084010b002030f036030300741d09403007500510744100000701d03006030340755035064104000c00c000c1450046a041072a40c80a00304030704180107500c4042c21a540342d407055000c0300200c004c0003078800100150b10301501c50b00b41e10341250301c0301d0b81ba50310810805009400030301d0f50000101e010200800d0040740f035560f00500784405241c8841004000d000400341190104c0d19000781801c1e038800001c42e0608283c02c00c0c0d07080c07101c54a01aa1000e829440f0881510203684204000c0085500d82039000c1c040c0803640146030740c580c00344000400d092 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 323626151 1250 323624901 323624911
    0x3030c0e030a0206030a09081215010f0215010e060a050303130518070c030e0604180f060603060b0f0a030e15100b0301081509250504051b030a02160623 67
    0x142100b90b81c800180e80da00c00b900d8100500300d500081301420342c90212424411202c004a030131080e6001c21180030031001001c0b540840a907102c6a029203150b505a07a900c1103040b001040d25400001803002d00107000d251903115900410b22441e0a650700c01190031948001e41b00c41e031503101440188401d05010b8801404240c414042d00c01e1490308000c02003002c01d036900c00408000140803131030003a94446055402070091480d0030000c418901c0041c000410004038480c0c41c2e9130400c000095403030301a201e0700040b61850309006242030342d181c07480c6001d640031504040c00d143d550325551007140000c00c558041c01d5002c10096100b810f0040710400003808030341c044400007070b0810040c8000500031030030750703c508102200080c0d1070725518505424810001c9036407030291030320f02d220450010030039140b0301190400e417010840b035100e003101660725a009050f4003880a1040006c290000450b078020009007007480c00c000d014006035600c0c81c054585090147c09141e105a0220640c81c1200c00301756001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 323627401 1250 323626151 323626153
    0x6050a14060607031b170c0607020c031f020417030403030e0d0201120e0c040e1006050f100507110402030f011d04030e060708120a020a020d051317010b0d03030c0e03 73
    0x1840d20760002106071040b008000c081003a01e02070600160089100a02e203103a01c407030341210310b040503002e240b081d0700008a1090300707109030000718540300d00119916001d480068003401040c124070010700c080003103c0a4410300e0613420400028450080b006d004400e15520018580d107504e075007001007081c1200c1c0841403140d0204803100300141c0e0010b00346840c0b403c3c25403003c41d405040c09400390810140d502d540b81c1150500c009142002c60205500b081000080b8003082451b072201f0600204070815030310741d9044800c00079001318890042c00a82082c2d849444507180310540d64000c07809a0300142ca403945100032803401404071480b01482080e4041c4094500c44041c5050b0710024181100d001b2611300a4000242e6030060225007011240705030341083e0200068182007200030b0003580a520070a00501032603041d000558410412034401540b40403031480894201240307600c0c040c1038000710101c150350340e030749030111501e501040814a034041d840016168440803006041c0011180c002803003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 323628651 1250 323627401 323627441
    0x5010902120c0108060409020301090501090503190809060403050309030c15060f010513350606010206090318060904543503042105030a240306050a 65
    0x2d81d03400701d0041c0d8040011103004c01c1400180c000b090060401140c041d00c50b500708480c54003400700000083c0171401071195004221000782c1340440c0e00c0317001500c0241350b40e0007210210700424031640c0a10340007009003044d2460820b01140c0140381030804051010700c4107511040110a240c00c1f0070b0b8030140070085c2007092401400d07122a440c10780280c01010b40c00f85249810050702e0200c01d400c280c80a6401ca840750310300b03642c00d0060f07640d0242240c04a0040c442c1300001400e0780c10210668030342c107080c04040f4400c8104442000241d0b0003c0e20000d806c0b60380d0b2031000020010013541c1c1d21000a189041030303401000b140415005810301590207858807484141070040a000d1102d00300f150341c000d00d41d2000740c2c0b00071024034103072a2a011250040d8443d0215200d140740031000840c095482541c0080b00c0710040310900c00d185018020355004180b0500015040325203680004058050600481c400c03401a0300840a41028070307001500d0180c0c5e544100400300304248110414030242c4a20280 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 323629901 1250 323628651 323628673
    0x103050c041b030c02012903010b03150f0405120d0c0915050708130b0403140607020105040c1811270301020403022202040f0902030403020c0f010806042004030501090212 75
    0x11403801d0400c00c2c4020940c0d100c41d403001003407003944041500d01910652040203014102c0c4450200e0340d12032998480c0d40b0744004192140740000c0c200000c01030002d854030065448160010042d1002082500c2a0082e040030704440800034004200982a48800055000784600000e00c0d07055940c010715620800d00c0403005101d40c01c88196a07010b580702d50104d03a04c01b07090750f08035400380d42c1354000303940300001090100400410040707032014104000100c92840d83c419004a00340d600079640905041062402801046412040850829030040d00821a0341001042c04da00b940050402081d10303d0604010f8090802841c00380001d0a048000754109402c507000108070360307100c2000464440919403400300c81d110a8041c0d500501445105500b040e64501a09001e50b0080310110014041d900140313460345407040c4c40701d081c0d5006946103920381c0e8503681800024800703992440c03040e03100e1128505a6029000050002c2c1d40700e0700010031249204c1c414468030940c00907044102d80c000401c22030b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 323631151 1250 323629901 323629931
    0x41e0804140406050301020c0607020d09030c050d05010b12061509100909150e0a031b0b0a0f020c06040503070506280b01050c0a0c03110114030604090c05030f060103050c04 76
    0x9019141d0841d80000714418480010b0028041071344050703095400801c040081c0e82012034514441e8241d502a0344e0b508801500449080c4030b540801480c0000b400320500480c241160250180e6101e0780000400d459007800090503011072140c40043d69009008228940700414a884110340066815400c503040200c00c00f01e4400da9401034203262a620a4107101b444892084c0c09030003070754484100300b1b070300c4040c020b00d40700c1e0690f400c00d0b0f02141e00304c0809800405070512107000d860304080f5080d01a100c5010744c9000d000540c000255007034090000c841c1e1480c0500c8054011481500119614040d5140c450f08006004114445600302151401c061540800601003d0500c000000071540d000c00c0050300c1600403180c52040c0c83c0703e2a004181044800503800c02500d018841a1007407013002801182d5141503411071001850341031002c10f000381072680200c00c181e403040c52070341005a2035801007868860f40002e00041544203500410500c4810b002c80c405036101a18140240140481c2803 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 323632401 1250 323631151 323631157
    0x903071505161109011a0304060b1f030608100203010e16090f0909051203010b0a0806030721030909090b16030e190308130b061003020403050d08041e08 67
    0x32142040c0040c408031914031036001c4070314030014080700c1005030905080c241000c40341000203a000c1d08081002080e44152081d81c14048100444002e01e0343e5200e603102c501404507032400356003113040301c184e0f002141c1c2c0d0101594402c942507030703000484514203080d26103007a00c040f4040c1c4003107104100510130a601200101d03400503454481030366402c00d500d001c42d2603507055030103209181c04295010500f42c101e9040501d100d4014022540c0302007129000c100399110038072a582004000700b00900106000d01802d0764003e50050685040e20b94400421007001b0f44c0c7c07181c6200c40c04e03428080404050b00f040c2408040c0c50386250400aa8506941d65140700001400e10011035001c080961701c541d00c070790400d010403048002a50804140c0414031000050030039001c0340860954000a0b4244154a40c0c213804d0580120348503280751100c1050001e901d41c0b000108080640810010000c034000b04004c44004aa5507107102851070141850f40d4200d1030194242041c900109e07141e004600c0000c2a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 323633651 1250 323632401 323632409
    0x1060801290904021509090112030e0102060106021f090209090a170415080901020712020c12011806330e090c0d020415030c03080c0106050a060f051317070317090307 73
    0x2165503e030b40c910708000c5d4050121401e5010700500d0000c14462901106020101e2080e1a82c2090340b0300e11006a0b00c6150900868006034030840d078000041041200340c00790401c0d18500029065650f0700401d1180300121505405540540924000c020302503035039460054000d0fa03664200340c144104095108960b08240d01041240c1002c20070540c000c0d8111003c0d03542c4041050180c001e52070b4080d4440210141c254421b4802c200d0440c0010018000d240f40006036041d11582e0081d10380e100002846400400c00024502803002540b0385208501c40c07210001309044070b10f290b80b0b00314804010080c020444100764110600007150f60300c803016400c000e141d0481c1c000c20b1070840e015440704c40e80000e0f032015201c224409000014003501c04010014400c020000f40030ba0380c1c9407000d01101031079034402e0303000280b03d034070044101602c00c8002d0039035100c101400f4000c865a84422aa401042218034021900890000c2042010000d40000071002c408038250900320301c800001c0c2c0361030340740c0701d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 323634901 1250 323633651 323633659
    0x2b140d020417070806010e070905130f051005010801030b07090807091b05070809010c15020f0904061401050d111315110115090e0a051c11030301032a03050106080129090402 76
    0x8602e0160140080d02701074440039001342c0c0400542c6148001400400e0041d020443c9001c0c0814105400761205005032a010b855121103646150349880000758020312000c1000b010b07440100d0300c401c040c800c010040c029800081103500300d01c3c00c103101503426201d01405020741004a00d0000e04040c00f40e48440c00c003420035260358005410100020400524040b02d02c910009a08034540c0c42e12002d001041c10030f840c100030315903c0b62141d400e202070400002d070100d01d00380100c050018154020035180d82c071500300d441c1800b42ca80d0421a04031302c02e030010410501c02c0c0d0030001e00c00341c0c081c1c0c08100500410000340844d8061020710001c0b544540030340b026598035601c2d0b900303d250b010040d003070350710b940082101c042000180601c040c04020300c440b02c001419a61025a00000000669050700c0e00302038081c40d030b000c50503040509650f01040c44c4070310b02e02c2c00c800000072440a101d2400200024000811a0300d298945002c07910345c0122040e101c00e007043c14280340d80c3c8404010707d502c03941c195 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 323636151 1250 323634901 323634929
    0x19080f09061b0304110406061205060a050a210215041e0510110a050d0818070311010e0316080f1011040b030402060f28022b140d02041707080601 64
    0x2013000780c1c10302e8034171008075005800c1c130100168040c0d1220100c0c80500a407031080100e91640001c01c4403205880c4900c0d9840b030003e000134000c113070500700d01e41444040c4a902440350f807120380c046605081220904e101c001070104080001600c0b0303094401010840c0646100c24600786400203034085000c08206040003034118620740b1a8504102841d04950004115074414449400c000c0240008456868031517200a0403202a580c00161070701c203603940500e4006d5903041032801100c58406000049515115088408860341030340e19607000a031081c1c00c05400c0801204902c645400300c0c5804550324140382500d100300901c13280c02600d00381d50511800c0d5030b40b52111b00006034030b401280c035680042030303000946054040c013409d4058800010f400c20001410f20b074130310a13612401d11600e040720000c00d10304100c020100e00104030070b03405080d00f402d04210440c1c015411141c0c1148049404042d800035003401425042c00100540a4400700241007460030451740e0394880c00180300c0c1101f010016 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 323637401 1250 323636151 323636153
    0x50a230a0e01060b030103110102060408180d06020a080906060a060203190201020c031b071a1803100e01020d1407050a0305092b030501090209180a0219080f09061b0304 74
    0x1900204601d904010003401502d071203081d00c011540c001c1c40115044901d803d0b590450f940003040140c4902d40080d0854280003118855854110b07582d2461a0f0000c504440f2400041e034910160000030b510f942e5180d034a2520720209407a1800103862a0b100348280d40c02008886d5000003142c40c02002c078003040c194200b4901080c2d019001b024a10401e90002080c3d2411071b940d000052404e103d0343c40d0444003440c2d5175148000321500000c2103c50400020400030320800c80c55080a041d54201030220b50700d5040462228086030f00800c045001a5000a900120b080c85805590210750452040e004c2a050005010700325202d1040f80d0000c0c1512030000601961051109480700b26050208440030300d081e40618162001c805020f80119103005c00201d81d5900c58400c0d503060302c1780541201280cac070460380540744102c4020038407000250200501034080c55400c82c162298842900c1c2c806441c24490155000b5520041c11a1b00710f5001c5420042d044003000802060f412412440b65629180c0d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 323638651 1250 323637401 323637421
    0x60a0f03020118080d020d080f0c03180c090106030905060c03070e090702010b0901090c171006121118010f020c0f09060117100f0909050c100512040c09050a23 70
    0xd5003c04d40e01d005240b12480e1841c0c01140342c8580e910f5a1351820010b07560f86201d8016850f00b42da00f080c1c07001007440081c24032103502203900d803036824442c00c881e000c4102e03000003001e0b0711098000400283e100c1190100b08002008541e40202480844900750324010000811110792060410310508c1030728040f91040c1d00030b42c0103104410000d020301425684469110020b0032090710120001f07000520002e003100c0e400001c290140150540c894440c0d490228112a0121149680e40c42d0b59a070315130780c80c100c0c502d10008217088006040803986206c0c0304000500090a0142c1c00c80c10f40d0044a4080c1e0540c0e02c811840300c05820803903021800e40c8924004071580c4040850b510300e12802002407119103170440c081442103540ba902004c0800d87c4407500e072000d40d005ca16000704646e121400344c1c400c501e0b10408000d045140e5140180c02c22640d10b03041c0741da40c030003075405494071501a0700138000c81c4080c0c00f030140c0c041d07041d030300034400c0d00034168800d400d0103a03040503040035980b081c0c00b181034022 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 323639901 1250 323638651 323638697
    0x4020f06090a090f1b26071107030f0b0603060403120f0209090907030209060315160c050a1b0603020c1b2d0319050d030b0315040302030304030305060a0f030201 71
    0x100c5a1000c000c450112081c220040442c0b940800498844c40c45c503e042512550340003072180f03070604090001e082d088895418015000d440d0381c00780104038010710350103002000040001c40c05004468903404150910007490780d0040c0100d4001c0e00201d040001290301b00464210b200c011340c0000804005944101d8024003548031030548c024608410301c00b51003c0010344e1030070340c0e00031140110b00d40ca4010406543d840e0001b11403d4180316000003030054004a902c290b050301107428030020a00320342e5101410b003500c0f0401260b420a844640003031b10004260b440e0040c001c04d0404518044024484950b1031000640310715841c9400e0060900940f6980e541146c0d215000c3c10050040402a066070404000c0742d040a000748601b11042c0b441c1a9090000100c00b034102c0b014020a24403c14210003034414203241c41d8251180414004800c8074940f04184524000e9000d942c50707040c285030090540364040c00481c4030b010f81c3d00c0c090050802200e040c0044903424205000f0444005901c83d044907 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 323641151 1250 323639901 323639909
    0x1509040e1204150e0a060c021e0f060c010e06040f060c02030f040b0a0c08030112060f141602070312030204060f14041221053f04050109050d0e01030c050304020f06090a 74
    0x80c00c40710000346c2d258002c442144028400c90b07140343d051040003030782d00c0c40b0307503540100551221210401c5d49a0b800e00c08002c2251468a02c00400c0d000e0710401070b9460000260703011100c1050200c002814407205209442509445102031841d001030690501c0c0540524000d510f4004c000042e070000a0b0700605030001442d0784210170944039a5207508800401d410407805403409800d00c1e2942c03c0e20303aa81e205840840f214003850118540380c01c03004c42c83c0c5108203803142080d0f100b01d09002c00465031201100f40c4d0a5800d0b900507030b4a40c00c00800900c0496064140824054501e001c0d0360808440e01c1a142a0351803450ba030030400718503040c104001d103070a00c0801d804440030400c02c014158841c006000103050080b805040440120764180300300c514000700d00502844103501c02c101c8950a030150f0304980190008102c83c001900c0d00c904202c1e0790319050b07011500d05420188596014041c50a50b000d01d0b0900508529054000c10040005600081e01c10180060500c655540e544d030914090 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 323642401 1250 323641151 323641159
    0x301091109040509160801090807060507140304080711030f0a14160306020c01050c0c0a080d0b100207050a0f080c09040c030b090a15020c030909060f1509040e1204150e 74
    0x50826951954942c40300001c980c3c11080741740c1c404035018505010f1501d40d9903020100d20314050356504c4010040001914803410840700c0b1040b2101d5403409406035000e10302402004d56509140e142409900001c541d0041c02500098035090041c000418608160b913080300404c00740b040104501e50404d034040300b0f0700d03110b0b0385502c0010091058030f81c054504425001c5c02000182c840426000c214080c02000412b0b0b030b0700011030f10000a00f14000f60244044100e0042034080c02400000c034003456260401005911413502040701d0b00e45011128010003039460980c0e0f403d41000c8055403a0a4113101e054001c1c50762402040401025401c0f0400850304400e08a5050508045068850000f07400954100c0d103804148241e40350702e4422505401e003100021890081038805202201c800104a242d100740031003543d02c040e07103a00581d031400407480c1c1c200566512800007004202c4014060903c035a621041044844000110440741500c0c2841084150411111021107005588205241d00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 323643651 1250 323642401 323642411
    0x310501021c020f070f0e06040b030304032a03060f0c050c0a0f1104060608012301080402102a021302070b060607060603150516031b030216060911091308030109110904 73
    0x8103171054141301c00f80c550150309141c4030344820f0200020b581c0c42002c1a035264008000c20400100b88450a103c109603a4400240b0340702000348040c14030315a94020745110780c69101c5906520103612415080038002c1c02d14508040c4031900c2c007540d500700120700811400003501c042c4180312400084500d42c640041c02400100c0c1c403410020101803007032007901c00300162500106038400320001500e10085042e95000c400d83c1d50764080096045c4260000401d0001d10300018211021950300c2c40e83e418014a9001148032203841801030445900c0340c2111007500c14804900012500d000445d0003490484100707844076000d04000e8000c14060b40300814110105122281200c019084035204280c4100b00b120850f855031819016140c0151041c5a01405000c980721510b0099020b84419175000300070002c48400c5650768400c80720f40b18801e0300c4541010710403000ca840c1400040d60b01c0340c1c0c04584200d1628055884949900040c041e80b10203e4507000c2d001d504241180545241c80001401404 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 323644901 1250 323643651 323643659
    0xb0606070f060203160f0e060d0203070507020301111c0506090c030622090210050c0c01050a09030c0e040c080f100c03020c0a0c0f061b020d0203010e03310501021c020f07 75
    0xc0c869041c241c0d0311021503201042d20135134034000c2403496821200901081e00e4200b049c4020130080d80024858414032106200410168509100305002c03d054001c03050b83d034130014a1100d0b1200c07449030f05081c401d4244070800c061515911040e035040780e00c084101c3d03242d4540c030380052503650003a45000101e030144500042c1c5048660082200c0e0b0b4008c0d1030101c072580c42130004403440d01c0340d0407486d0b016a109540d42c074250b500c00c10040003119860310300b413400d6980700d0b901d036000e4101e250f2004000003054000d200a00914083c840003d1895074000c101002407450040c4e12808107058100d045a40c40c1030b800080390091b01290003410342c40c002c0e5010241c01d45400940c0d02043d009000d01e2810b00b07035010a085009848000d00034043c401c2c04514800c065003000940c6444000486c2c255485124040060b4820805401044200524051000a400943c01e90748514110600720484a1002002240d0b00032500c400b603040c1728500e0f20541e94554009903e01400408a0907143c811208001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 323646151 1250 323644901 323644921
    0x20a0c11220c0e04091101080405070b0a020105010f120b0403051e0a210506030a0222050f0a18080412020a05030304080c04060e15060d060906030312050709030b0606070f060203 78
    0x7142c11200c42d242c07110800d055009102c12200c020500824400078101072540a6001d07102481c0d02c58410070803030b11040c0e04c510502c01035802000c1800d0140c1c6d124001404036019201e0ba00002e010304a140e1200d9030782c0c1d0b40366807615620180019041c00360002e0a08035090005495441e00a19458480c0e80d8540e4908024040300c1c8024a0b0140d8001ccc040d86403c500b078417070281c0f502440c002001007154414940030031114503c1114015400580752400e020141c81e180900c0348202c4803826158150310f84000143c064039120005001811302e90801400092600c000313480960f04515221112a0180c0c070102c0d010b007640b80c01c1650f0602c800b00b800540c83c040040d135103050340000c2d1000d00c0310a81c0c1e10340d0008058410b441c0072048600b50310722000c5608010003d00500000c0450200310256036a0b240811101c00d90001c0d000242103510803030740354115006140e0007446a103041d2030514a540c850441a80000e00620f20a403400107201c41400515510040c04c03a411820465490614030040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 323647401 1250 323646151 323646161
    0x210c0a0b0a120506061c09020307090c0f0c080d020a03020d110d0f1a0904080d05131208101a22210b040809120d0c030210020a0c1122 59
    0x5800015900d005920380c05086010f4640a0343c0003406043c1005103084030080e443e1040700329400c8040e522403441016a030100000001000380c100005418403041c03d00510190501301400300b4811000024000907018004844c9400084000141c0700c403242c07001280070f4854441c09641c1c090802c0707510f0181800e207500406083c0b51b0390008001e404000c40111050300c82c004408209061000c0c815004c0703050590725070b50300a03c9080441d29002e807082d59034084031000e8920405030b20100140f8030800480540c4403044040c02e0401e400300385440011618141c0c2e281c043c100403580951403402d0508180425901181951742c040c0c0c100c400d221a01468038507482c0708459206640ca541150481e0a40c01d49080d003a070050020304441d83d0700e4503a50142e9000b01c0e00c1c281c01440c174020501c0071007018009640c00903050381e00c0e2070220b40340b800c0080c81c020b981c0d035040048600c1000381040e440e80003064444003c1d400300e06034031008031400006a42d007003000b8050f10104681d010b80f81d0b40c8401c55000d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 323648651 1250 323647401 323647417
    0x804030c0f2a05030c04150315020306010e06071e030306080d0c020f0904020102031b0309120d03050603072106060905132018090c040c020a0203010b0f210c0a0b 71
    0xa03940d07401075511880c0b0344203030680b041503015004072802d8a41070030290894603420007451080d620742c0f40d483e40c9800103142410554000c0680c0801402800c4d81d000000c00d1f80c00c0b03c1260554200300c50b0f601c9860780c02c950940680c0700c08174200b41c032208042c040c1e0000c0c001810f45070150b412104010303001404010070b14804074414090b1312208100c0c4d1400785840c5000e00e40603802113003048881a03000c0300c0004503001c400054403081c130010400742c1e030384862000c0e5182c120f000380c054044280806815101c018100c548a500203a00502100240c65800b200000c0711140300c02443d501824004014542c6400c003090a508200400110318a16841000c0c04c6220788868902c001380c0042d600080301509a05503481803005a4601e1041101c049035038001c4c00e0002940c5c0201d20400014080703a146072014405031b044003000005520702031044120410040c1c40c104440103440f4009040c3c000000081d5909801103001400c2800b03041043d08448070000c1d00c10b00308540c461110391565041004 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 323649901 1250 323648651 323648693
    0x1413090e010923122104080d1506030b030a03020303190612050601030302100c0905121c091502071d0907030804060834050313061b020106080a0503030402010804030c0f 74
    0x40d014051401c801103405c00c560300036520880507456a0540c9070201c1c0a4025940c401091017490080e401c00c4c81a03012400070100100d9060340f506c540030702034810140c070303291098008c0801e01003c650040100c0341c0c404100c030344100310318200301002c8000705802d8000071450701c00b00e82c015003001070004005058a000e80c013150400d841003144d1009171142c14486030005252100e04101c0c906042040b01c0c00072801d0015110f0321145070039907503024000e01510100241c4111410030800c0e84640112001240c00c1c0f024100c6103007801d5500c90628240581340e0328a0b41003000150b51002c1c00e012440195a11080311f6030b80d999941402409000700752981518000707191440c2e040d005603140c1c0c65542e10a40400105101300591041d610350308010420080050800b82c030000150b5180301d0030f804000c15000b03164030710804041c020308440d860380019513558452075515010440020541340c0c00340e82407070030310303000d68aa2404580200800e040206042000d800c40810031204180311034000032410 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 323651151 1250 323649901 323649913
    0x3140c150720010909051003200604120218010314060a0b010f03050a0b030a140d02060705070b06030102040b0a05090102011a0a0303110c0303040e01061413090e010923 74
    0x9128000d100d4200010501c0036502c01003910300c0c2c9020441982803005041886900e03540b01959000d95070102c03042943d070a219a0f080c800c01c4008118280b08000303000c3c155400c4800d08011810502c40c90007801689141140040708642c1d98440314040d111070b260290f12103503548e2a14603170b00d400c003009410307035030080c000050040c0349640b15058140605075110585050880c1c410382c001d210280c200880c6070745540381400b10340c1341003000034411449450b20405060096010324100035020001034115044a811b10000c29840400d6505542d0800100e060b80d80350000041c0c0280706c0c0383c0c80f540d06800082500da0030581c0140142414000030703002400009150b02a4a22540d00b09a645a0112242c44240702091040380b280d0000001c08040780c0b0b402ca1010b001a155030007507400705807a0314040d00184032899110f540c1401c0343e55840c449508010a80c0d2090681c02205d0280c1c5a103070303546180c080031809094100151103a040402d0f83d0001003204e004a0010f4200314500f2178512841c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 323652401 1250 323651151 323651179
    0x5121c05030106081f05060a09090c02030705060a0506030c220908042619050f03071b09060602030a050702031009060f0b060306030d0f170f010e160c03030b060403140c 74
    0x170400b844540c1204d14800078007a04040c1000413a81003030401c4020881c02100c00710748415107126280344144e054004603260411072403d1484d100004109401490400043c8580c030b031000500c90640007801c640008040b40081090360b944400500301e0445c250a0000c514144681c0c40014015a900a02601c26404200c8902a180392101c1d03250105a44040300400804041c0d007008441e5a105106440810500c90031852545d085804240c0d02102c02001c8200710a4103a0641d0004154034202806a140380c42800b94585c040c82c05103a0600070002503580c119075050081030b105103038401042118141d2803c0c820003d01c490005010441e180c00d6100d2283d1401100340c0e840380720001c006010912501034100d8005908880d008207021350150b40c0d02224000c000348504c201e09450381c4075401e46c50628001140380010307022254045e0400445190326030700a0804650641500700400c1180b810310118020388504d40c0051b100422502410645500100d12031001074401c60b45006880350b1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 323653651 1250 323652401 323652421
    0x1e18090902010804031404030c15030e070e062101090311060702010612140a14010c02010c050906030406150801140103050d1e08060114031503070f060905121c0503010608 75
    0x203040030180c0494072201c001400030f0f204a4040242c0300480702090f080c680d5070f82e552010f41c0a250012522240030407000c00300c00e94180701d241250407101e80181401840c0003822450040080d010b1409260480001840c0e034580b005960fa4501300c0034020042c0104508000384103070a6505e8464090241c8004034068600c140102c1c0142d4284070781c00b9091000555802100700c0d000d8140daa11401512a08800b28500011040541d48000000304a0b0248220020700f141c90700c42242041c0b01c420720019155442d403400342c95000e83d03c044000b82658884900342c680d484164402013480d8280702038540903d4603109180e040341d200710f0480740c013008808030a5520340c40340340c24024002980030358140035a02c01c001868002c101030504166851640c110540c19a00c201d9080c4580c0b00c078400b4040c0b040c1001c01444c8014942c80c01c01c415250704040c00144803c00c0ba10800d8410f59030040c541c2c0d507601d01804190106103000061114405c1c10301c03005042d541007403140c2030100700c07280c0020b0050700b0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 323654901 1250 323653651 323653661
    0x4060c02010c05091e0d0807060c0801230109030b010603090b0105040203010b120c1611030c0d02030d0c1104050109060f0906080c04091412090411120c03071e1809 72
    0x1181d611443e04103040b020074000000c9600450002c00f860617510740303403240c42e68142c183e0280d00032042d80da0b9810f074a0400b102954000c21901e010807840e00c0040091021403c0710140030540e040443d542c0d00100d50049a5481403604094111005c880000030902c0d090f90181090320301c44e0038140300980c2d030f8008010032400244076024010344100490b454003032807401d05035849800071004904000381910200c6035644850404c5444020b810f00e003422616003000f0845402c1c90455800b020030595501294983c503640403444240326400c81e9980800c1164a103e034284000a0000c2007650703983d1000201504140c030502401040c6582c0124071960140100029124000003c2410510b0442400010441d0350b074180c513040070384c0000000c0504144202050010141c1481352071301c040004102c02c80b0045140900011001c100700032141e422041031030350101a4142450301c9546140301a00c2d03030790300c0c80a0702e102c04590146440701d00c3e41004007507507100714021408150507180d2160408175a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 323656151 1250 323654901 323654921
    0x50c180f0f10270e0f061815041e20040b1c090b3304020a030b0d0c03030806010c08190302090303160611031603090615080604060c0201 60
    0x450552161007140c02c1240c0400880012031500328403811080084078190b12007001c0f00440303800701e441c04000000310308158540240740c0100310b4059040220001c1c0040f80d5240041d12a80c00103000a6040074940c5956003154002800034800482458504510052400e5948115a140480c02c4030440980c0349040c11040011012501c1c050424010144540000c054002c07025040e8544802d151414001c107a803080c420340c031160700c9003805444e442d41c14502c450300803910510510701c4083e40310b03141064024a68152001603440040710f100310080c02e03079140c200343c000f01c1c1031020004203c881d81111080b87e009a4498905885980045591584101001c0c110341018844441c0400805016050003480d50400500c4c0c2121324001c00d040d9000052001000e5100603281b0040c81060f0140600000c0580000d83c514641000561003001c1401e405078101a40d5258a800f040795550241180700c00c0080c1e002000b694815403556500b40c11a002c03a0745900301503070032800500501135403081c1c0c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 323657401 1250 323656151 323656159
    0x6050703020a030c3306241d1906020d0302030c180a08120a0e060c210d060905061207061409010201061502071508010501020a0b1306050c180f 63
    0x2e040c0545049a50b030349000740540d54100c0600c40040c81800740344110140c0e07065040c0c040a81c051000942c0126a1281d04c401c19012180c076041009290540d10340340c050801e030a0518490700711805094451500c146c1c0d590300702800c42d655403100c9030b44141040031140d86074200d61030068215011000da00045d0b690032407000d42806110001c8501c004000700000000d840301e40c0c01d590f04e43c01035107031405003040c0e621035581c00549080d60640c4207490f000000c7c420382c2d01520301400c0740b446594134040b00703400c0364002104050040d460000c80f401c440208540340000d0001c030352500c83c480f0081c9401e580b01380c0f08100740c508000354004040b0b1130740110ba020b5185c0c503c2c2c4145040c40340005900406400341155a6480c001c01d1403030805207050140301c020343c001c0c00e01034108150a20706904079100c1009106558004001c282c1e80014001c8015038400c440c00142d84030389814402c0f510515030000e20030360401040000400c803200c064024040350741d0101560300b0028040c0300c48034142103040350708 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 323658651 1250 323657401 323657413
    0x18150b06030103080c0a0b0c0408070806010f030303110d091104050609040f0b09100e0a020906011103030106051308060a090309050d0b010506180a060c0303050f0c0912011b030b030105010605070302 87
    0x201384050302901c0400041001d94801000b542d8443d09540c50845044412200c0440c0a01c010348042154402402d5030f80010056541030a001e4078103111301c3e100007010161101c164050420006054400c0790320402418014200c03240382c400c44d04450035540c0fa02aa00d080300107841441c000341100d015907003000c0588420b020790341f0b461032030600003001c0310420720900450059110b4244a020ba80c0003020002d082c0402c890b00c108815150040c0655040001e6060a60446c1c28040212411103103a0304155036100c1cce42c4d4200c0c4500c141c0d1075010380400d0041c0003c11121895540150741c019100f44c0e034941a4940b1142000746504c4041c00240101c21040b00510640c01d0040041422520040450100d200301c400080e020342c4043d000b503800107400250801c10150103004168010b40b9400304441c0601e0560804012802a05000c0344200d0800d10884020f00c0c081d03008a2201d11b21103c0640c50418002010b00680b02c0c00d44c0440c002e600e0700c0d0002400038400e000f41c2d0404da038194050f1071 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 323659901 1250 323658651 323658653
    0x60b0c25060e09060a050a0e0103020f040c2c0901031401060801060b072004020712030c080708063016080309030309011110020415080604060810020a09080118150b06030103 76
    0x43d40c40c40080c0341a4200399600008a02030381c0d941104001861020305c000050341c19441807050b541c1030202854095428013038806500c94018280321221072011484090540840110314041c0750032404480c1c00103c0000080103004400c4542049409424001e0115544c2e4031641c0c4d0884e01144561070b02d1145c240204000554040d03c0516501c02e80d500c122103811820740001c080b41e129203400c886004042180641c0181c040c000c40703070584100e0030142900e24140030083c12100340104000e214150142c21844017203164000039128000520703034000640134030440303656109040c401180d0380c640c04840c0081c030300307038004221105d0507406400355040c41e0300d050042d5112040c0c414045510b00824080241604051024200600403554102c00c84400202d019144510140103a40118246142840f00c0000001d1142c42d0b1842058010303a06c1f030000c03104481004c02c2da0403076010343d420410380400300102c50f0b03444003c941c040c07990101c640750425441800c0b2000d104003140c2100041c80100 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 323661151 1250 323659901 323659909
    0x506090c1902010605131407050909010b07060e0106030620030c040510021c0806040605060c0a02010f0e0315060306100f270507081510020a08030703060b0c25060e 72
    0x461a0182d0002043d80368030390000595140490025030186582e0348611803114012201042d001440c0c1c2c180340d80303494014008130721403803014003801c00c01503000103c403410804254031219900b2110402040840d80f40d20701840540010050684011501e04864400606007003c0f0303401214850051840c1929000c00e000521381e40c02015015030192401c040340350894100300c00080c03400b40d904e0a03881c0c90303c002040200c658640009000b140140b0160b0045080010aa44090b0f024203180f02062043d501c125600040305250743d405024001540c03094038510164179000d01d40032005c0e2501076071000402c2002003810701c41d40c000144555010045015490030420481c03d0f001c0888015840140300801a280141c44c92000501c0c1e03036082000006407440c101101120440d12182d40b2803c52800030b540780c0c3e40c04009403003140d001000c1205070b0302961104005014580d080ba4a4520300768110b5260801200742282100c04a03000c10341d0444410804004d0320a1526903019a4030340c4400c0c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 323662401 1250 323661151 323661187
    0xa020d0206070804030c06081302060304020f04020f040e0f090c0108010e04060221070210150e0c0c0d02030a020d030501060807030207030e130e190807020d050a0f0b04060506090c 79
    0x5036040301c020005100814040001400694020310600c58000e180901c0100010b20003400c0c800204e4200603c030780182d40b401c2c12a5040341d01280c0400444c8440000980248146c00c1589040035001500180d5000f055030124070030b00c20006490705070fa4030310400649494291b61070a000400560040c8101c0e20100c000300d800500940d00141810000355100203201002d840c4203008244ea54200020690304000d40c44000d00d841905000081400c00c00800d080841c2c081c82601c55010400030b01c40554000546401d0100e00044a070a041400006500ca84c000f9402c01d00502403080c0710b40f0014024041e0904031012956085110350740c0c0c007411002500710071030403402c001c181c214101da940d68441c220740c4440340c011400070b481c0e190606c0251900b4424100c00b00c540c201051722a0120b5454400c2d501c000d42c0503181544d0b0805036103000c0c0d044c08545000201000702180320030080c000d06900c901d100c2d520501c02004181c582204020030614207d614134014030342045250b02e000824181 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 323663651 1250 323662401 323662403
    0x3011d030a082d270319030b0301021206090f06010c0209040f0c060f0906030608030703050a0c05061f0801200d0905070e15060a0e0405070507020909060906010b0a020a020d 76
    0x281000c0d01c000e02c4011641020000c1c0005a8500001030044503013100d00301c50482a2a603c40c28500203400c1074a03070f16800b50444003801e0021200b030303540702c0300c0c001e422441034404018021036480d883e000e0849803004042d2030481c041c6003000c000440d10b0140103241030042c41c05851755104101c6c035600700246004002d104076010b10050000d0400070f0005800140508500d4071888801c114402000302002c25507404541010309003c2c040101402c00301c1103502868152070501e80c4c40d030b1061400d40d241401c100307005045124500400c124a52013400c054040f01e403003441802036598a40c1c00500380d0303030b56014000903401d00c00c2e058620381012800400c000110841c0101c4c0103105602e0b143c0c1090042c0c0d12000382c4900801c10450b1152a01c5c503c0403131560101c803c24201041408000c0400c44101101405256640c000c6420103006d4000e4410165004054030340c20726080f22082d4070b038501034482942900c0f03980004a409880078040d42c140c0229603000f0005503556400300070f00e000001c2d02c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 323664901 1250 323663651 323663671
    0x50a05061c020f150a03090b07090303090e0907081203010329070c14010c02030309060a0501060c0803040302120424031e02131205071401091802131509030203011d030a08 75
    0x500002400c00644c0944541141903e001410070074504000742e0454004110300100704003010144002a0000b00000940d13030700c0c004800701666480515842c5c000c46401810080c407400410340880c030a01310040d8140ca1280f0b400d4902c400351816041c0170030b690040c8039000d0613040c0c00001d1100b40314203c00d20420b4043c0d0303c070000d028480c410440c2140c90044200380160000001c00c00c4641c0308002407500100605410007040d03243c02c0e00140300d400303c0b04000741400000004101450310030404080c01405000304a40d45a903109840465424014142412000b5910803000780b5800b81c070a1003410b42a1a051940c2c2e18030701603801c4000c4d03201345802010800c83d00c0c00800c0ca40410624440b04a00c11801000003e04102d14200f0030198184698104169000144001c000400742841441d41d00c0402503124005121102490009078000001d00d061181c041c09540307601130381c0c44045034000e80080140703030445406400385014030741081202394000c100c58003170548212241548208149 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 323666151 1250 323664901 323664919
    0x18010b04050c0403020a1415030702071d01150e030309060a0c08041707080a020d0f1e031e0c050304050f01020a060204140906040e1c11060a050a05061c020f 69
    0x8002500701da4090b2214240b08501150600c21400c202050901030310030319081040d0750f0075110000d41860010080c1d018103417804004940300030f00800010014001c03d91012500c0e454011174001250070074854404050700360140d81d0306a1740104c6808080c2c29011b0081c42c42e0414940c180b04642d030200c0003400c03c20801c0451400850021409803014101c0c11503503601070f4042c41161490114281c101c0070141e080f074460200140d0f11100b010254640c070502140c9040e9045c00c0c1120180484075084211140f041f441d4010142c1c4180140200e2a0445075400083d107038200440300d00115880c02800350380700300024080c91400746020700d060401481115a08c003050764501c000d03038010342d100081072841d03802c580400c0d142c03c030840c60340500300344c0d020401800c0d8601d40560b1941380c043c101403d118546100604580302e08548505010458116842410003031a111b005020460301e0030903c40c07525000c40c00c07510300070066005600050110794882c4585408011012410101a90f0701c05000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 323667401 1250 323666151 323666171
    0xf03120301090203010510110606040506060c0d020c030f0708070e040503090a090b0a06050a05030a0c02030d110d06060c0201080c09210604020a09060f0e1321110111031801 76
    0x1910045020745018440940c4070351401047c004103500c0740c1039050030b00250a03518141c4c107100042440d401313141210003080944503940458051300c2030021244003409841e020340c00c25074001480c0c500070300096086031803001d03810f001aa164000303802003480c079400c0842c080080c2030310b201140d9042402041500c2c6440011300000714541008e0f44030681081e101c0c4038503000c52900e8107a19008010605003545001d0810000510328030000700040e0685554044080f060f40c420400e581070343c1c0380d0780c408001c60019098100c800b0340162403550326017401d0a60101c2e01038450a0042d10b002d9041e19001d80c1a00d07445c00281154105a429903000043d014000000941c605d04070780d840d1100001074885030030107005110350302c480c1d90045803001d0b0a002e41001013030001c001c0c02c1c4c1211030090b032010240d1a00d5a40c0b940125021307402a2410300c00b40194401160b03004898084400c00740c80c0c04440600700310606003a100c20071a80304014406100003446400300038555a56040d1860000038880c0030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 323668651 1250 323667401 323667433
    0xa050708092701061101020901050403060905070b030a0e0c04110a0c060e030f0301060219050c06071523160f0813021008011401020304080304140d0609050d14090a050f03 75
    0x41080301210860400b0010800c1a0300034910185001c488002980341c54042c00020341039120700e04c8000c09030b41d6076840a805000040c42440040c00d04010040e60741d0600300c0000b4050090090401d0580c090b40480301100d19051080740c02d81c2c1d0811015034203100c45c0b00000d6852540da0b560582c1c95907240c00c00310a18590500041202c00041e40c2115102d50401038000d1400e0300d0b0100c2004500080b031070442c007080b00010002c0620208441161b42c0b5200391901c21352449400e11801001d509195800b5038650065001012080c89009000903565804040d5000e130344410303240340007040c66004001030040c0704003901d6034440b1516029901c114503950204601e03040c0d000c00107000601e0440140701250070041c030040038017024801981028100007400e5141d108034800c00e000850160300300c84443e20341d003400650040e0041000c1004c031503142407150711480a100040d0004200102140324145200192100581d028041c20701150600050062100d0008103150307051081900070030096507 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 323669901 1250 323668651 323668699
    0x8210c030408100605031605060c0f07150305070804030804150908031006030c0507050715021c0903110418021005090607031d0901032a0909050a03140a05070809 71
    0x1e0941c0c001c0c110201d00711156011035240c2d070000b0380f180c1c100b543c110f803403a47e42c00c0061040c0d03201294540d41d41c0000c0160703640707803040244100c001c40c05a4580050900300c00d041c149100240c545051205a4032200115000d0108450081c042420200032902107040d000000901508140000074a01840c2d29403100603081100c440c90701c0c1249140c107003c1c040d40360151700501c40716400c2850405a00d9038405466000074051034500722422020f21083ca071017004504401120501d051490403131501000304110301500003500c208100b444e0111940c1060311030721010070303054541c030102441c00d0303401c00c8250896051880c1c1000420301c00c0704021741c0e900005000143c880d03100c0e0003d22102a628050486100281900c12100c1d0340041001c2030190354184410001ca024003d0801654580f100c451030094000780803c914001e00882040000603041e000c040c0240c031001400610069225550b00c541301050380015014418000010304810181c4010140102004440d80d0040c854000f194 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 323671151 1250 323669901 323669909
    0xc28020d060203040218150d020d0803010b04060f050403021f0309140102130503010b1014040b030a0203011809031d12030c071806080606011b050601060e1908210c0304 74
    0x82e4000140011840c0208034917450030000e0394140c14500d0300c82800041c16141400c1a40a4424035000c0402c6544c1c2c3c3d030780340d04003d6200c0401038aa5846505250594006018010100f00710300d0800c8620f50040e415642126401400c0084000900070035040c506215019036060585501d40c4800041c441c0040403c02c0443c42c00040c1c4071007120a004450040307907404a4040d0b458140b00840e5903d038849403440000007418503114a07607440c880c9001900c00c59102c03022024010082c440041400c1e00210b040301c030010900e22003401c00080c0003044a2048000a004c20704042c41c0601c0000011351000031500010300305c6280c0540007200f0381c02d5074460072500c1a00e4010100500074640084014803000d80d09900c1040481c0c1000c1c500d0b03035034000260016050148072140f4030381e200d6129241114140e840300030344000e969680b05c041c103034166112134a88125610305d880c6410311701581c8080100e602c00340092004030002c0c2174014010f203401150001d842000c0020f000a408200007d000038 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 323672401 1250 323671151 323671163
    0xe1626010b1e03101812110a031d0907171b04030c0e1012030509221401080f100926090103060f0302010e1302090a0e100b0c28020d 58
    0x10341c4103001c05013010b207110807101d54940b41126000d681e40d0a0040301000d85d9000b4601c4181d583c0d020740c240e9441d40000e041002d14403c2d404801d08042d4440011040c0400c0c0c071010003548007030402000b0a00030112503020020760150001500c5c158a440130f19000006072126054881d601e489282c1c00360300641042c0c507203140c80c0b0010054840080081503201c007489501c071410340e05000b86a401e0031030740c1901904012010441c000c03581d940c00390706004900d0002210943c03002d02100c1c0b40c05882c2d207440061800749240000618400003050421055a24401400c001d61505603110000c9c55025801d44001a10306004880452600c80d0000e92401d502d5039030740c641c09250300060580d4510f810030481d4060051003040180d0f0000c3d51101c440c4011520302d03800102e111410f0001f402444001a80318640103400145001d84001640c0035110f240d6075110f4241d1074541c4081036100d2040703001040da0003148481c9411922880005280010a00100304503000d60005410304171110000d84003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 323673651 1250 323672401 323672449
    0x10050309070e130602070201050906030103141203161d09240105040b12060103140a1e02030105011e0c170a020d111011040312030e1626010b 62
    0xc044100020002040d484018410b81d01c1d001680d5400403000080080403141c010841d00110f80c06801580d12030300300070341a0740d225a56800c6c0170404d501e41c811003180074000c80c1000303074111a0034412207100d100501c0004000e04d00b0300e071040710a188855000c884000781009031030790f1540c902000501428000c0c007c0804981030318105007090054400b107505001040100300704841c100011f4400d000402d900c0700c4200d41d140f2006802400e40345182800080720307802088028005640061060407099a10340c8204003090f40800480c4001c0c00f6003404100c070000c0d4022000003508100c503040d521840e0441c019509640c82c1c00303241c034820424040c150341c0400d8031030403d035041000d00101300c2c442c502010480c510110998031a10420f5120320041d44441184001d03601410445004644c461b43e00300e440c6c502c40f00c00a0091109075040c002d14000c9464840800f4180c603035413010703201c0e6107120080c0041c40c0300c40000b40cbc0c00b21500d00d084a54845029201c5a600e070000b491740c55010340707541c0c01 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 323674901 1250 323673651 323673661
    0x31602100f020607200a120f08040b010e04020d150501060f1715040920011106071704060e15040b0c0c030405040908040b040311090f150f01030605100503 68
    0x3044001000c49081001100306015101c00c1c0d000420070340200141c14241c0c0702c010016043d4202458032011042d10348180b14000c010458450304108010080355121104248c01c041d0440c1c81d1607003668041d2181e07007840010b0103240c1c41020859081032004211041c042c68640c0c40a840254200302c0d019445c0e0740700c004010a03504054030503014809071030030b946184809492422103160141242901401100c01c01a040c0c89a90203d03241c035404c9180416031543c0c40000c0c0304800001e10035580000c922030950140440700042c203d01440c400d4031410b00c01c3e12130500f220010303100148140c6004d911f0307640c102d400d0001441a1038007041c0000b407106082ca03050030203d0300c8130300140c10400323100030400034840e0300c1d400030042d5025a902100c022540340c0c10f03400c3c2150359001c0ca400c001e03003403040000c0000c1000511400800c1040041c0c418803050340e2212800841420201c0c0d0310115880344c0b1444001e04d2811890344003440005040c0000d440d0340f40c0d004150b00343c1c00c8170008000708800000f800 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 323676151 1250 323674901 323674909
    0x3180f110405040503030a0509070f0305030405030f0d08010b090103090812071e020d11030d0212070210091e05100e0c01080609040f08180402190813022d03031602 72
    0x200e14248150303030a2169040c2070b610f0541d01d102c0140100500340d076620100d00100b4090100000400c0c4510f5241801522820501e17101c0d4400c0c49880d02ca171041c41140d9040c1a0085503114a10600307840301c02c626880c004001d08698081e000c01c6040550300c0108400150b80603002e46858100100303080c91034600601e0181110120980780c003030246045001055080d40060842c140300c145d0b1500c0908009607403159031540c09644c040e0001c107400884e4060340903407034083c0d5622404503682203c82629a540d1030004880700013401501c400e2540c4000040c404042c48030b0032718035210700219010742500d003a41d13204807900c26020388429003000001e512250390050b0816003213001280d80c0301d03c5061503900c0301d03241c681c1201c0092120307030045460034202d00302e0003840310350500150095641c0d41c01c40300e00c0004034004640b00008070384400701042142c0840e2400400c0b00f90b002e00000d6400200c0c1d03c80c021045200d038201c0d202c000b41c1c0408107131251024406403c0d1960040507844000601d0300c104 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 323677401 1250 323676151 323676173
    0x7060b0301180b06011d03010203040609170a0926010c031d03040506030a0c050403050a0b01091a09070302090f04020711040b1005090d060603141006060c11040c03180f 74
    0x60b5503030641d2003050808034481e502040d070400c200342045004003020035090aa010701243c01c40d039042d44044100018403000381c1040c41d580b0b1080b94807a826002c0b803030301540540224003140b00004c0b9103041c248072405d500856004140c101a0490340000307500303a40a400d40d81c0800bd48000039881e04a500d0010a031501d1285801d41d024026604080c10031012502c24080203200a06841e216000d4601060180f0100c402541c2c01505454a030000d81c01c22020030a42072080b0750b40c02e4507020440031207450982c0000b40481c0000c1681d074150300c0d071020460107500300e11030f0503902840610b43c140695903a48020082c20303205560804500c800c80301003008907061010b036507005a00740150119082d03444800c81c1c1244d90103c0c0e50750040d08140c20240001c03e0720707810003403400403032030741c0350440c0726001803c1c007a46140030b502404516280d003c200c2da0384520f400002d005c05800722446515192903000980640f5080c07070005010a03861689943d52044404199102101c0c0101141030000100b00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 323678651 1250 323677401 323677421
    0x3121a15090d06050403050405151206180f1008011a150f031909060207050a02040b010f020c011103120403180609180e0106051207050306100806040813050607060b0301 74
    0xc0c03908250908020900000101400411440d901e10008041502850643d000340c4405030403505610382441401e0400d40c08000110340c008580800200646080d884025078545159094800c503202d0706480303924660050840011440c51210100d4110303130911544540c03000b200c00c046004c01d4584103000c00183c61500003980031000b0449685640b41d03800450340c02410100c000032841d445924400300401140c5c500802c0c0381e00000d0200280100010b802103014022a410441c4625100055aa0280f0100349001503081076017404070540c0100e074401030b110203107819603150100e9440240c9020200310f60440c0403814204070301e102c2c2950300ea141c00103841d42c2d04140744036a06109030301f84005114001031030259214440d01c40c400f6400c0d00010300421025203540da010300c00d050003545800d003a0007240d001e0300c100070000b10028034070407084085850010280a540d02e640d01c80000326804650000b41541400600080640b030349002003080714007907140040c600c0011400c00d82920300c1000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 323679901 1250 323678651 323678689
    0xd02150a09030e12070b0a03020706140103020310020f070506010b1b150411031f050a0c0c020f01050a11030403032c010e100215010f141206011203121a 67
    0x16403080003d070002c51039940510b080fa02c002c03402c1c00080d0b14500c1d00d0f141d50412810420003240106000790190081d0000c9445417500780404040681d40c07403c1a03000348000f070340c1680442e4000c031748003029900800940c1c3c0044161031a140049c0c079140e2620000b0707449480f0449000440270400c030841038980c280c600d15080584115103248002c0007400c00c1c007410103001010100352060042d90300f08a00c0721040c0b2200305143d49180c0c108c46800081c00d04882c180415810034400300032680c0700c0d008811681d54020818a07500601c200115050382200041e44240803949845e10040315003000030303000640c42070742e03508800048100e0000104000811040c1040169140303c0c500b0780c0c01218084400109a03401400c0d030818182c100d14260220fa8075030551001d0400205c2c506240074200d1080e640748180202c030500075641840001d040440510250750881d00060144800e00091078800a00910340840d60281e1030840e1012555001016100c888220b0032519050400020b161160036a41d5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 323681151 1250 323679901 323679911
    0xc0606011e05091206090607030f1112090f0316030207060801030201051e09060406020f1b130e070e0c09040501060908030d0f0204120818040612020d020f030d02150a 73
    0x1041d945042907081840c207040c0400455400380b20380702c1c84200c1e200e64000504440131405d110b55582d03110b0300c066504000203814090100507824460143c41e289240c4200c0b8189004805901c016040001030300c40b500a0058001c00760984400300094401030044003c07480800c8420700e8040e07d040040c0d0b1020b03050041c814010005030380c100090300d0200410110210910800c0c00300200c0620502218550005002c9400308416a0000e14600100c6001d01101c14590070840c20f40300c40c0031010b07407072907201e0046ca24004065140e43c005400f0700b4038107000c40d500e2039200c003170341407502a0440c2c0040d464000899680205d00e014080c490042c1001c3c1030078040c0a040540140c1c40744560103040c10705075260921a24900700a9040306c0003031410700d6500c1d44c1c2000034078120f030040c1d01c041d02001c44c040c000c4204803028074091041c8000c4a0002d030408003010701030360900014032601d01003660b01c54181304a04125417018440c080c0300c440c0365800351500d41c12600c00307a0301101000c1c0c80952028601 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 323682401 1250 323681151 323681177
    0x303090e011509050d1a0c070201180b03180f010f0b040c1d041a030a030302030106080a05090309011202070605100612090203490801050d03020a02010e010504030f080c060601 77
    0x41a003c005a50050300c44541c01c0503142070034503090a0032100c03c1d8112101c40100300c4c10700c2401c009001402c4c401d0b0b03908603460b0300304170001c1032981440c011021800410400700d000000d104654402a072804019904a00c013440c941c2402c4612194030024055259407803140c06190621440f0121191401c0c42004124180c044280c0700740841c0a050080d03036100e000700013201c0107000d0b030641c6800003803c5070404501ca2030014080d40080c4101404211014080b82c40501c1c01d0240070320450b1524000c6040442c14001110601d51041024903403039030822150f404188035024140c03113004452580e0014038134120300284000000c05c08545c0701c4d450504414010f940104080301021400da0b4401440e0700800101c05001c1014600c0005010b10702c07500041d0740c0c0c0f041c086520381601c81d8a6050300c80c0c0e03880c030602c0959844c0840c02001604105402c00040d07000f2034051441c42e506150960812703032a0b135103101c41040071201c25200c41c0c00104540780f40c41e80401035650b020300d007842c1c154220ba0031 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 323683651 1250 323682401 323682407
    0x1020604050d030209060403050106080a031b08070219120302011409030f16080412110306010e0601020a0b0a021c060e070302210603010207060c03051e0709090506040e070303090e0115 81
    0x3900360320104044c0c000440c00300c2982c41800303560145070010000c102d482d9940004a83c1c076002a5011004583c049195550310403680041030b04183d082612589414019420003c0d062440c814050a4106040020820300724a29800708a14400d070000038103411035001a80303000400a00b280220380c410440e0300300c03040c081000c1e1080d1248105c1d810202e8050b074942540c8900031900002002d4141f045150709000200c820f201c20044143c060f04d0850340c072513400810010f000c45610340503900803c42c000c00a03441400c20b5501c5514440d00508000145484c49005801660040b0010303171562018814a600e0a400d01d4105c1110300302149041034116107d5820005aa43d1802483e0340b100000c82c0c80d242034048480700c5520034010010921071284c003900604007503030000710090760f051800c240420074549080c0036042a8840c0c461840c68640080040c040007400c468000e510350105c2680d00c20104040b202441c0b007070301c0d82ca9040d030401c0d40340205150140d00260b40c1525440304003202c150 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 323684901 1250 323683651 323683663
    0x61809100b0414130c0e060121060b0307032910051804140a0c080906010911070609110312040f050904030c020a030503030106030e03070b0606130306060f060e0102060405 75
    0x300140c40072401424410000e001018140d0241c01101c0b0701e9802c000b03281c00443d00c43e0003440e00c1442d03517801d9651510050030711203004039040c03400720340c0c1c59051520040f0031800b400750104039203d01140c265210315002d0442e81082d0b407084003003510341410101e1007840b0009102d5589481c0300044110110038000341080307008036040414000c0025903000022840524902001c202410038401d40c1400c00340c1d00702031001120011a110328000c00b10003694412000c47c1e00440304607006043e00e900784208070000301309502d200d40c0f01202c10002d00002a050740100000301e4001d5404480d090414028541010030100d4880001c2030308210034031450f075070301c84000f042c3c031019142d0202c0c507611413509a40c455583c000103503101d00004800010814000010743c16180b46640034030198407929011903030307030003201c000500c100913440004101c1e04040b0040c00044081c0c038080d9802940d04c0d1288811240550440760034200b442c2401d000c8650000820400e03042c0038801000180741c117490302501c1d20f03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 323686151 1250 323684901 323684923
    0x70b071401061e05010c02310e030d060501020610050603072604030908061003030f03091a062b0f02030a1a0906161d0f0a06030906050a1e02030907030c0806061809 72
    0x29582030030702c0c84000c19258054000c23400c01d0b400300a614624113a480d0340741c00285004680134101100820194070120703c4600030b102d102050310344107052138100322203030304010091400c0014482da03258181181242900c0c035810100d522810a04042c24000c00c80040c541090b4645d9105805215002403810341d403608691301490280a500840c050890150414400241041500256115140108011aa0250707200321140007244215280d185161928851020300c5410070340240780100f84442084038503140300a00391001d00646551b00000748400e04500c3c140016120100302c1c843e0783c100440703504140d0045260710007801d030101c018a440c02c142c08040200001d0a00310b1040d0315242c4e10340700401d130b0007003110b5070780c4c0d842d03210080041c0903002c0181d440e40d003400040340403501e5902c43d50765141ca05140b00702044a0b5a0043da010394405071502c3da00d0f07c180000040030564001c000c00c06811043c02070171650a1800402800c4130116003020303103001e00c43e03007403000070070f40001e412003d4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 323687401 1250 323686151 323686189
    0x11160303020d0e0102072705070e010e060904201201090506090403180801020f1e0c2104050a0b12250f17090d0909020903070b071401061e05010c02 65
    0x450300f4000100c0c1415000d1b880450401c98038004402c0c0304011100840180000c0402006580c0c0c44560485205003a140c5142c08103031a8a000d008504040303008210121001d4000b040703128240c441802072490f02c09034280a040301060b42d4150201c211a1a401009603030b50500035401c10000090041c4005000102448149210191060094000b140051800300700031515200c2c504446c10981e8071001601c12448001001000c0a4803800243c5185000200040140c61003100001b804500610540f08070072105100000c0c06071b07100341620001c3c10340222400e1300c4503a10092080046000342c48031096603d10f500000d0402240131071665610510314100700d0308184404280c456200e41600005603d01500411801102c0040d5500e0301d807a141c1d441d620019a20100d8000300d0060203882c82d8540c01c0b40c0c8080107286046000350443c540074510516070203072080c6c0840e0844019a0220510f4100c02c5984000c9981c14102c3d10014002030030035807814a03a550014000e86003c115040d04 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 323688651 1250 323687401 323687417
    0x90a06030b100605091309060507030501080705091303080603120a050702040f0203240d0602040e1b04030b0c07150911120c0a051c02030a0f05100b010f111c11160303020d 75
    0x742440c1d400100f0f51f244c01480401c02ea081054000b0050042400b07800e003e03218501d000100c605221000b40d1180c080d0b40c0c1c00824281050b50308482d5004050602c56051180081c0e00c80c000c83e0580090400c1c0320251a060358030003551050100366502c1e081d0f50185a84103104100380c09580d142450840309040c0070841c5c484070600005481000c03200805410144013080118442c0c01c1500000d0040750380034190900c05004400d201c0d02032050780002400941418007107040500c040024182c40e902c12160800c00070b41c1d241c165012610180310595440c22034102c10007044c2400c00311040744101c50304c06800010010f2011598807029845803d010b174842e45504103101c0741d0340008100a1b64000c0a0b1620070380f503414000380c108607140381522180261050303000744510f14400d804141c80180c50314aa10003045070241d9410241160348091400b40c02c081f06200080c3c2d0241c140d1940702c039120028046941d0001c140383c410128030260011009900a0001c2500003c036080d2541081c41c1c0445 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 323689901 1250 323688651 323688679
    0x11206060e220516090501050f0306060a1211060a080a060611210d020714060604200901021c1d04020f0702120f070306090201030e2811090a06030b10060509 69
    0x860484104c411580c95102030001040c84403507600142d049a03400c440c0d405268101c1c004051f11000190341c1140c0c0146959010004107000080720294980600031040400c2ca014011072043ea2100300040c0004004104103c0360103410b104220240c070f000d01e0146031014440e481d02d1780d1480300cc1400e4070131700040c0c81e0001131188500100c0c1c1c4080c00c06036081d9100c03a098034201010201100300914280501d800080d50b81c1060b1013841003c000c01450401c003280c8000d0702180642c0b0a101c40c5046001b082110030700d00554101810f600016991501107861082003802d007403075040c00b02c49100354010004004030720082001e0b00c181c160111603040b041030580c0d001516100f00449501c100c0d014901000061180a922101915000b030b00c0a20080b82c00129094441a140c0081241080c00f030045d1060360a40c00c9000803035500c6007003448100d564040010f00300280481e50404031580b1a41306004000c600d840380f5411034000c1098440490074094050030501521081500400755003160382 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 323691151 1250 323689901 323689903
    0x714060702030d0f180503040303020607030b06031302040f09051b04060f090b06070c080105100b03160f0c0f0c0602070605041a09040902060a12050612060f0601020c0603011206060e2205 82
    0x590148400c1c05c040021090f0752400035103d030400d00c000d0f000341c0207541c00941c0440c0240600c4000030002070006181d80c2d20541c03a0040180760310816a0015602d24003087c0814451003080440303030040e001480501c1d0048240800e041e49032241a00850a0210401c40e110317540061a040e2001c152000c180010381d6000308031103001e0600054105600e2030000a8001010b502081c042d880b6a03c03d100c9454491011031810310083e1046801300c0324810300c902c5489d00c42c120001011741c2600c0c100e614150703d904e60815007a030300341040d00ca08d0b50300c03282003000c0d0784c040040c540240421305181d402c2901c0d1910450400000c031011402401d0300048090341c1d03950320351002496980c02405a522988203400040c00794102102a00d02140b8200124245141c00050040001442e01c003d091565034404158216200070b07211905502c11000e08111a0361880c1c0598064001400241c030304040fa420a01c0030b58007180d004210083d400b400b40129081d0070b07100c003849040c0c07141080c00c001003146051 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 323692401 1250 323691151 323691161
    0x10804060e150403080604050703060b091003290310140c090d17130618170f06010303050d050a0908040e0714030a0c0809070b03010522020d020714060702030d0f 71
    0x160398540c0b00c031040100700364110f4100c2d8025075090b102044590b0364200180d00b228103902900448040500c040f20072840c0444c0d03030000b0702807685804030700c8406088906072a071580c0f441510305400c1000c0242120b0a0400c51280c5106501d130013405251500c0020b004070200c00383c90613400720000541100982c6403c0134201c0c801d68080d45050032442d9911419004d40c003c2140081403010240e00002e0043c417841100e503c0f5001c02e0000418145007008076842d48403600c0c036000d0203006100c0c91040806080c0709660085010b0b8036101d5680715a8288101250002040703215214034100c02000805e0340306080d03a0640f0222080b0f18400d44178800181c683c5a0210309008601000000b08917042240c0d40000841500c10f40b240000c544a00d110030742c8841c81070140e44090071040c00104150710300a00d1280003000f5042904100032500e24502d0240d074042c0c280140c0f280e8000800c0760821161504049410b034501d000b40ca214186030000944034412498900840c1da15026080c072103032500d6011f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 323693651 1250 323692401 323692423
    0x150304060b0901120302060601170c090103060504050106180b0c12091903110a080730060c0c15050f04060f0b03070e0115020303070c20040509070503011a010804060e 73
    0x350302c856070346400d508104a007243c012030040c011a0003240403540a01d0102c005142c004031040007c4c1d8078680c002d000c80d000b150a139410542c45880008a030f03111071160901038115992141d011006010402201409a9102d0a9002020005c1c00750300b000100e41d01c031205984081450f81c4c4e0162100007009012a103582180c42002000300100b0450301c00030070505010240c0700300c4c1e011940c0f4041d294a81000344640040510b00c11010301d80d050182441c6140340c03408002200911890352900b5080310b004040304400710314941e0550080c0300d000c92301d0140c404a101424030161030007050301c1070b2030310f0b01400060030b03180c0f90900700c082d0403015005640100000340488480d10341d25a000b0f41c0f141401e20488600c880f0032201a40100d00c040300b02c2c0d1103100e440e1900c81d01c9003041d81c1c034038800c1640003482d2140c5048031140301c2d046a071a40207007409070340c03040d008144241c1840d00f0982100c00e0310326079248200c155004026944d03080fa0319a648580c02120014200b1203c250f0300e4140080200 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 323694901 1250 323693651 323693659
    0x503010e010c030e01021806070503040807060203030601030b0a0b0a2015100503060624040b0d09050c010504050a14130509100e03090d12030b031c170105150304060b 73
    0x4000e00012030540c858902812281e0b0140202101d625040c1d00700e108507500d44c2400c1c00b0403401240035045c480002e26025100d03404072864142d4480005042070b0349a0040070060304004140000c0b5a0325002d035040706001222001c40c606d281150b110141c0c41180c81700c00c00c1c4205099203080d002200000003a4440401040e903000602640004070080740c1210500a803a0400101160f10f090006419107c0c08026201c0501030070b02c030910400302030070f8407241c89100c1c1041101003805807250000c0d0200380e036111000300701e0f0005841c0850410a040129074100601400700f000382d41c0e02c0d41038000888000500030640c00caa0000071884005150706c85082d02c0d4286014490100c00026030484800071000040160300001c00304141c51b84204165140d1001401c01c507040440d0f81e18002c10791011090030b000940440b07150109080c4840d19004002455030900c40180080c0c200307202d8050401d40001c0300d40c0740d6040000140492114456422158001000280411100e68840d08100310010 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 323696151 1250 323694901 323694911
    0x40506100b1917070905120a052503021816110d05090301020705070b030412030903020a110f03100231090e07120602280e09060a090608011401060f050301090b0109050301 75
    0xd0034607815803003403900a07000d2508011040031f022075200d201550041c0134080203000c0c40d20042142c0402d00d40c99014200301364002005995800000300078600c0b5107011541840c00c00000390021200d00c400d2014400642892410540040f604400d806414289aa1107540c01808280203010b40702005040d841032540105100807018055071045220f0300c1811803184980d0000c405480c084e0b10000c3c090780c49544401d00040e04201c1802028501a295290100d0700c00d00280ca860b00c2d841040d0300d002c2d03000622802062213045000c515500d0f4500d0826038541da025044080d01c0180f051781c0f00307113680c1c4405806980d400e02c010b40c02403400320320140c4200e205003084002940800680d010208011620001060068408050b601c500341c03a4150340f1b0b480c00c020f0142d0440e0040a4540c02003464202042d007240314402d0901510b820f100002d03031654a52010901400184c0203802404011442c8210071984041181d0540b00c182038042282500700d0016684e1003400c2d00042e41c154200 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 323697401 1250 323696151 323696161
    0x1603200705010e1c0804060b2d011b0803100506031005090a06030f0b0612010e0f010c0503040c170109061103060325090b27040506100b1917 62
    0x20080c111490058008200442050903181d41d1108070460007280b0410605200035500c1c001c1002540c0306010700c02c085100c81042000403184c01224800c2c05201440c10250b403020140c125104070703820001c0c01c009080d1520201e591655460700f100042001a002000803042d06a550140c4003c1030044c10107507da05107a10615400c0d0503c5c0640c3d40102e8901000411700d40c51405400e08480e0800b100c1c108010741c64542c032080c02801004140c00103101d4139020100038091190b45024106030019001c01e01c0310214803400d5800345070600d010404140305100114034254503820403204c1020303c81402295a00b00303503000d8a41d844016000614103d81c2030341812000000711b00c0b0b408105d0681f80004c46c0d810000c82d520140303014040d030078600d00c0810f1105035003651050700f89000081c40700c401e003c0390203414400010501d180d400500d410fa02440f0404c0402c10085400441e40c4800d10360203420b01e100c541890040c17404c03400c2c0c100d00c8011481c900501615500700c02d0007140301405c0981c500 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 323698651 1250 323697401 323697461
    0x3090a06110705010f0513110118260606030309011107030807120201050f012301121a0913050a02011d0315150301060321050d050702010b01030c030b091603 69
    0x8000b0958043d400c01c1410059504a441414868181041c070010415116203503000f120040c0c0035124140101c0c1c0300c1c10a800d840308110031004240080081100592508800541036480c1041da0301590101c4140159a40c000c4162410a0301c203103400c803850010000f541d45407000c035070303c098200a00016606c042c032900316000d2120100720b400a100c1c5480d007022080c0c0854092055003508418028206083c88000480701900c003c1407400000c005c0c2c207103800700101e505a02550303441143e06482100542011000c0716801410b5140d04c8101da81c081d1222074070303480c03000c1000741004085c2c0c04010381c6030104050318800800c060119801601c89403c40100c035035043e00c040b00b5a002c10700100419150501842c000e60b40e204144a48010106003034060551401140800388542401943e2200030310744240e07441160980d002081d034000c0383c03001608035036040340d03030b4002c0500f002042d007100e440703200c2581c0c0c0000c901d1a0b0010305241c130210460080103024400c1c4243c4480e01c0d01c080041070 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 323699901 1250 323698651 323698657
    0x308070b060108060d0c0312020c04060f080c0a0f091104030b040605071e020a0602090a0b0d0203060f0d051b01050c030c060108070b071e0503040b0408010c1206050f0603090a0611 79
    0x82c1c07943c02c0142c8503c0c1c10441d000724400c0c80100200303840c810034030008145100d08007408490b030045a501013000b000041c155417003070b0400d8030300c03400b41c001c10001a90b00300444446d11505441c44640309081039002e40f00c100c440d00925418642726032000c0844403141c2c0885000719000140b00c1d0003070404bca8004050f00042d5800300000c6e800c0109109070f5a80707051079009425450b00205140d45c910780c0c804000e9040800400d45c04403004000040030321248004000c6c12108150040e980d10f80081001a58800d07140214001e282e07214114001442c000b0b00d0081d10b40c0640d584d25440c20203007004803900c0c40b86c1503240c0d1440c00089054285610b0000d04e15040c0d80160003942c80d400e80321001030710320340030b002c0c1c003e001c8560010003e480300c1035a42c1c44c003015a0046003501d20300b41d00e48003000c40541c00742c0d1020a4981d56004952100e5501c16540d0515010000c0c080c08089d2170440080c1a2040c03504059218000010200c0c01034a0104004141c0b01e034040400e001c03a01015400300c0183d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 323701151 1250 323699901 323699911
    0x604120b0901060501110a2d0c090f0606050f090a031b09140702150417030f06010e100e06090a180605030d050a08070f02011d06010906050301050c040306020c070308070b 75
    0x141c02e043c0081110b60142000040004d0000020034a1004644804514000c12000c4400c1c64100c2812801902c11150080380784a0044282045072441d02d0801d80445074601c03210040c0c185000001e02c0640c0d400340440d07054807070007603900d62130b16032013000a07502d1a00e07507000410000c6111154461003121a100301d00321141c440b01081444c51100460317440800440300c100050300306580c00d025a14502c100c00d2b03006401150040b41800200801d44410343c4291031542c408440d800030130078107692180e104201640c4c10382d003000a5003401d0b4400352412500d0045c00d4801e070404520080319440740086040240580110140f80060941c3d48600602e0f503406840d000b40210075240000038003401c101c0345412010f50b58108260b442103030442c0c4a0b0341c02c6c1c40314421952500c0c0c41c019544020803d6107000aa040c020701983d51400400c1c504550040d4001e9005c1c0c0d0601c400c00000c806210b046c1d808890300031002680d40d17a801d4196a007010b4480d00014140240404d83d1014032174600d988a11071 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 323702401 1250 323701151 323701153
    0x90106110d020303040218041e0609020405072607140d060302010f1106010b16050d021b0a0e0a0504020402040506030f0402090f01180e03040906120b0c0c0316020604120b09 76
    0x2071425008a03200d100840307010f500030b0800201141603005130182c0345c0c3e209004508410300068008000142d402c0c5811003900d1842d120b1000303100754546442503d802442c981000002c46400808045408407851203032072444020100203a60140503019a141540180a00955500142040000030302890200b68001922030440300c03d07a900071036038940905070580c0100300ba40c1c40c000c640d10781c1c1c2d0301c141051451120f41d2009040000d00c01c01041c69004000d401030100007560041000da50b0303421305107007442114002c0c81000260040c0000e0344d0010808140441c1e182e1f00c60010034064440c6078042600321000200708043c010b9001b50860249108585000131500c80c1011425820403c2c000c1e05480d030441c1400c10080c5030b06500c034080d10021032050340d09243c2c0d40d203001003c442841c1e02100442100c0700c6008100301821810a502054107440340381084901c1196964034040c0b000110b802c0c01581480100355075554081d40c00404080061088001c4513240484490005444411003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 323703651 1250 323702401 323702413
    0x608010906051c2a1203140f0904110c060117010b0301020702090a0207020a09060803091507121103040801110c0c03011e09020402070b090a020a06140703030c030b09010611 76
    0x2149004000f540ca151100b4040000c01070751a16460b0000200d030b540d10320f403084508508802c46000c071162000070300907006101d0192040707080180c880200750508464030b50041000f00c2c0708044010507113203092000d4800090a14501030222610700c54140c5800462092a00002e01d0b0540756490b518031344031890017808101e000c071060500741e0052040003036026240340d000605800080e030203002e025000600c00544540c1da60f0100341140e0702034012035420b41000650302003a04090340304810110f503030340410b882c00341a62142d400c1640a00ca02c1c0b4200000130f5038914038800c040050301c016004120003040004910745d0010303495071010781880d1450080e0f1680511614044c0f140034002a044400100c0c855a0f40d105e400c01040c40c02c6c412a441176091107190086000c00040e24800c5e001c0800800058055004000c0c1d00007869100004020b0140c04503001e02e4092019505944d6041c140425402f20410068005c1c042c4c2107240303a0841540400000c404e40c2c0403189556840c3c0da2420740e94 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 323704901 1250 323703651 323703659
    0x613031806080f0919050f01060e010b040b09150307020106030c08030a12020a0c050a11090112050a11010c05010c08040201090b0a020316030504080304061d1c060f0b0a0608010906 79
    0x1840c20030380c8105404500d01034002890350840c40542c40d032101c00315040d5440d288480b104860725880e44141510540e0106103840780f180c4091003490054050b440d0102e20380d602d8404000d200e882107010342c0300340c40e10119040002d510360036400070301402c201d2039194880c07401400c003c0c024070503440103451100000300c00054520005c812507080700b01d00d951b8003609044102d001c601030351050000408000019100402003401030141040840c400c1454000c9090703250104034228030b040c1c0024411684c00000400050000070740b405000368065691440c4483c07960040c3c1e041d510847c0060a20350910201d0114640c1c462500c03407040780f00762547c503009919080c0122560050010040240e80100101d5102c05c0426400310b00c3c65100c0d01d096882c16845551250442d0899480107000ca00342c0305100b150f00c400030000400105003596181400c4004d5445202d0881c00303404080c001e030340e95441e041d89400198000c50307928030014140c01e108543c2c1d450000e00310b0b1400d2081416541c81d0200100f = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 323706151 1250 323704901 323704937
    0x801020d0c031118060903010e060a0f061d13021f0201050a0204050a180204092c1f0e1006080a0203011b0c0b090102130f03140d051804060305061303 66
    0xd211500110186428250780c0f1810505021110049550080c021b000740c0110356400d02449241034000c0020340502c2c1807c1d40e100e8291020307a00e54002460074540c0c00c0c4141d01503810700065000e00c00900ea80f89499030480c0003820400c0410107500840407021400a4400c05c08409a4030b00382e5074002c100c40e44d500c1c0440030807070041d40121540041d6201c0108401004d609070300b24141c11208006240c903503515005000c07a42c1d20001c1c03040250080602407111b0045000080404005902520150010220b400c4d4814100c80820300840d03919030011040040c200849024102901c0c410000d0a45410300d2958030855100120b200e5030a11220011801c1a14a105451000798a030120b000704959544403c9100c001c100105a41d402e01c1880359a080709200c0c500180f6408605402c100d0a40c1400c5501551029804040d54400704400c000140c0c080119440310318566191050401450005009000b1581c0003520b84c2c4542001d000340c400c103e081e038000451090301d40d0714030380d03000403141 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 323707401 1250 323706151 323706161
    0x60a0509060402070819020105040c080607090b03270304091104030c09021b070b03070807021c1404030c03080d0b032413150c0207050a0f05041104050a0801020d0c03 73
    0x109421403508008115941880e8001c1d006a07441610704e28280920b036102141d4420943c14200c0050b034403002400184104914000090a41e2101a2070985003410000c1c10100e502d21841d00030350300001c001610b09194640a00c98182c01042d1500500c8986c68002c0d940d03001402180301b29403030001d402d010ba0078994100d0b0100c0b5880800603904501d003203001402500082141b002e80004003d1040c0703a03100c14000840504030050405480c0d0801c40c00041489400138610170542d8400d01e4540c071550544020303a20558154942050000c6d981182c210403400ba6a01c0100702d074001d01e60103c10041a400130f0309501090350010016220f1241c20036a40d06510b090341d10f0031380c685609030380301c29903604051903000c021000490f030155085d40d00c0d80d40e4840b04d40e0a0747d07800e0303a5564403001d0055040c0803a400526045a4041a5904240c02070803224100d100b854400c0c2da44008050360343c2103510940c0d0081100400303159000e43d031001c44078082d40c49812030b030180920b01a100c3c04100d01030710507 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 323708651 1250 323707401 323707409
    0x1210120b06060d02040e0708160906020c130f0c020c0f0406052404120302100b0a1a030a1518110a0801051c0b07180506071205180406090c08060a 64
    0x14203421a166281030101a0b80040c03800e4485a408001c04a94030355102049800345245941e2011140340000b42c43c0781d10440640c22200308010124100000d0fa400540100d900f40b0465054407581c80081c1c06a004094904500e50070f9424002d00c0e0105540208030000032840507a81d100352100e5040400089034542c2c0201c0d81e0041c1c5003101c1143e81a060b01050303810041c1400303000d18068640e108000301c4080c0b03600c100d0060b03004140c1d07005040210b000e0980c0c4040203a07400300c6074608080312141003c0d040241d007106403c01200290005041d40c01c0f06c644105001c01d15041680c07034003c403042c03001908080901580c10311f11401c80002c00b99003156034590103603079060110b908000030000040d001010556601d00b55110200129400e818103078028901da80b1080600d0340c210112085d40242030740818441c400a104c004080744a00d1900d0f40e05d9140707403800076070300c0c0f004c80c2044000e0421084102d80007450140d0201c0d4604030b0307520078090340b101500e91500315a203100c10040240b01d1401 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 323709901 1250 323708651 323708663
    0x31d0f03030f090f1603020414061c0201030b10020708060915150103090606140a06020303010b030c031008030703120f05070918020708030f06040c050c031204080f121012 75
    0x400035000d250002e4490360000d1042040d50403050031800d00b41c0c50207560b07842e100c0910101860401c03c501e454420004140a0a00305180c2c40c90b00e0b00000c0c0305c0542014859401d40e0002d100d06003160f21942c04024000c0008019600d0a80c4020000350f440c0028000c190132480745c040459140500080c10090440410104081c2561010610b0886610100010341459151042d40000401c64000c00016041440170b8200c2c1c14818001c22400c1800b5a00410954100300014000f4081203c21240d00280802036565a030b201c4103c070f40f524650591040c00710780000b140d80f80c10140e0000b815510b04204c2541030200b207000d04c5041c3c04403134003628110046508188100081c3c10744c10040b5601c8200000014207000e413a8036000105d60044034120003501c8018200700842c513003032040d00488440c07464a642040c0e010312180382e80703100d07089000d203040c00d07103e00040401003c841100c20361604401015140e0701c0144168000c401d0035500c000a1400c076460124001049206090f00a030f000702c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 323711151 1250 323709901 323709907
    0x15031005010f090b0307020109121b0807050c120606090124030f06080a14070906030f140c1201050f090f070605090d02060c070303080601050403080301060f1707031d0f03 75
    0xc019600400c48107001401c3c00741c2c0c4000040c010340d0201c0518030800841d0000b260a14107460450b540c5032a424500041c80b018880070703800c0d119040c465020311503004410340e56501140c104030b498120b000050035488242070782c4282d001440450302078003a02e0103481d81d08503a40c94081c100f030a0108442c00b4680b1102c0d14000080152180e003011030105622240016841d407501c1003281401c8002c9010b41314040ea0b40f0715000c681c441000040000d00450108001da2421aa141c4514444001001d810380052010741610340790140140120244002c0a00e40400820444540682421144140e11001c4040022032100b4040b4240a85104240203815054140081900d854124218064200c80030410150040c4c0303070031005001c01e031011002840003510310310340200302d40e40040c0361034104041840100002a2110203403410741d98541820450318101034030440381c010000c041d0b500c900a05005200c803164143d4048000030841d410025001e5031049100c80c0e68400c1803a401c01c4070745c010 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 323712401 1250 323711151 323711159
    0x9090b010f03050402180c1c0b10050a050c01060f1d0402130923160909150c0302070f06020414010e090a050903190201060609091e0b040608060c0702150310 69
    0x3d600050784144002c00300360111442e0b111803881d4140869a5080d40c08000a490f95088aa600c0255662200380c50501c90700f842c0fa0085440383d01c00303680b0745003401350100e100300102d405102074440040311440208102e990343c1100384980c48140c421340d01c003140c0c254a1044142c004c010414400c0e5000b8288564640b01e9000990081ca40500182c40340106840e03202c03508601c0c4030b1523102c400440c00080560314400f000226808500c1e91017003403280d280900030000a01c03401400811210142000601c4114010051700684100940202005015420302040168590181c4255911000c69083c0d5a804800646003140d60046960f8004010000a084074007650003103a44005d02d4001d0341c0c1040b020040d00c0485407032540c20680589d44410b4140081941703c1407001c000d00090105101c0804904050302c3d110f80e4042c0d006008581310040718034a0345450300104c000303005440880c7c506250a951404980d042440200c0c8103082025010390f003490290240c0c1c2c010440340f00c0710740041e460 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 323713651 1250 323712401 323712407
    0xc060609090f03030a0504120c050c090a0f09030c120504060806060702010519050d0c140711040612060e15010e24131a190506030a0b04050108030a09090b010f 70
    0x40280140480c1c802d0000300320041500784007850082c00c03150408500b6060070315001120541c540c0441c0204001c41d440b40c40030800003d0010350505060f07442044548030b10302040c0240c001c6c10006080c0f2403d00c00c10008041d802280c5a00640c0a548416440340f40000200c03814412442100001442e9a011402610349240200061481410a94600103428000200000e038005162002c0380000c1b4018560741e04070f0190410396981d91030700305000070100c501756045000e035010141c14440001c03010480382d10b590740b0a0010300b00e1882c0083c013100c02d13071a201000e80004103801105029110446146400000d034550503035000c071281c1841c6544010012813102c5003c1e81d08541c0007840070410f4056201d401142030720801815012402e500005030010305031401001141c010b03c20140c04958086882010206907441110003e0b56501e8200106000e400c140e0141030b0701600d42000012401e400200030700900385681c0320318000a0784d806405007103070b00c01805140406c1101c8900804144 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 323714901 1250 323713651 323713669
    0xf260a02121b060f0109060f05010f030c1106091e06060f01050f0d0212060117150d0f0c060906021212010905180601030818040b1c05030f030a0c140c0606 68
    0x10001d442058a08044182914010301134480d43e007015110f9005000e4800300340502006040c081111104403844c00340000d021045a0070b525081541c1c03042215500c511481c11811701d03e0b43c210445a1a04081000306d440341d688926284441c0044088000d090034046000c3e1f200e0340d401070400c182d20003c0001900c0300d5016403064000e07020104084e0744240b18600c0541203020348010001450b10b00400094903d160010f22042c035001114100900c10800d0003d0030a424070035243ca41c1322002074649908180300714140103142403d01200490102e034010300c7e00e411030b43e0036800c07200324840c40c1498a40911a0344850783e058040f200c0180080800341d04603c1d003150031040001d01800915a1460a041003a00112507405000030442100b0405c418914901507084500b0070400c070410b000641c0d104402e200c0c64289041c46205002030204c14030a44201883c110f01c250307924580408908010586480d1840c0482e8074040d60010b180150410b45a4841e050b4008103119242d00c010018011 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 323716151 1250 323714901 323714917
    0x12060412020d0c0b060607140303010803071203020304150f020c12030f010506030f160509030d0f0f05040b04090902360c07051b040e030706060906080d0c0b070306030f260a0212 78
    0x6001c500148d0a40740c0c1c1000114000c0c130060002d140c441181c0d1500c458030156401c0c00070708260050051001040c068078544803078100611002a8880e1022640c8002e40181c1000c0c036007500035980c8805025141c240218800c200d06620006c080e0707251020000d490006442c00000700300c0e400300242a8000300401c0c9003940303125003003440c1007078001c000103841d210861071500c002960741040e50300410f812448601c014001800d1003400c0900b40181c400081c00307070344220f5203a02e84401c0500d00795120082c204401095601c0c0d05049000e000d007090200980b08581c1841e01982040001d8110000105450041c1e6210000c0c184003010041a5070190203600e08403603000b40d507207043d0240742e40304000070f101442c03081c880403c170149042103803002c403031042d8407440b91038121400c80850280d0008509249a9001e1035503c06030b1110641200107011680000380b408401c0364144052051489200844040780a4441d99a02902240c1200342c003c4bd8400320141c0d02131001a555540440d020348000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 323717401 1250 323716151 323716163
    0x9150315050a060c0308060307290706020f0304141219020708101418070e04060b030102030a02030f1e0636040c0f0b0909040212060412020d0c0b060607 67
    0x2a45450000c0d011070281c3d07201c03002041c0ba0f002c90300c2c10160040c3d8003039403285044008d40750b0a45441914504d2508250020f100342021984808039405440240c40c460f6420210454450007029035050b00340d031068600350740152207114846020440010084000d49200c0403103410541d0030042c032003d0504100800c4194000c1040118220a0412a415101713104100214280b00c512101c0408144042c0003e0b00340b02c41c1d01303544a050f18002074060b04540514400564503600ca081c554005c01c03142d0301a55241d4000001d01c03010b0811600694010b440d9129074115030f89541c284804001042c601d514100c0461400040c810700d402d60802c10b444d6030b02e0848004041501c03100c50700e981c0e074000300003a0f1950b981052100344114000c166002e080680b002e1510942085c51010150240318045442500c0350b10001b42191035003084641240d9a840c112441424185003600c0781030802e180450040c4a0a20401c2c115882095039141a940044224420391a00000d114035688001d10903640 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 323718651 1250 323717401 323717441
    0x9131112040206091008150f06030c0a12060b040e0106031a133902030c19020609060c0c0405060a0b03013c08060f160f091a07050607091503 62
    0x1603144c1c3c080c03c500030075140d41c1d2106c041c600440d201d4804803810090320302442800098101a0b00c0c3c0104507501b1051030224aa107445041a00700c44200c144401d40c003003181001c00000c5d4400f08007000e0270640300003041925040c1e88034a41201101c0d41302102c1d00b0385284000940140d410030206002c001c0060300e10104011400d40fa0391034640b07191011681c40c154100c40d14100c075000b1403c0b0707801c00044600c099841c0c801882c1b5400c0e41d40301080f80c0d104003500c054410380115036a000c120303150000b01920668076100c600c0c03102c3d0780b20a840030402c1d0080d13040c0740004140e031410001e1441942c8030f100450341540d00340130f01c0e00249080400820341049901102c140c5030035a03141d00e02155100c140303e40448508005440741402e00143c0075500448824040c0b0a80310420f42000707200f41010302d05101c100c03c001000302e42c40b500c65404803562030000031003114821301c000000c1a5160140044030a180c85030007044036a10003911403042c3d1120200e10301440c5078420f0b00b040041e800c020008500c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 323719901 1250 323718651 323718667
    0x1206060f1c020f0c0715030213090c1b080c0f0c03250306141e0112121707020304030501180804030209040602040905072705060405010c0c0b04080309131112040206 72
    0x85039071107603c59080c0c540c04184100076580b8207400321903154105282c150f080005030000c41149e0714003801000c80e05604e0b40e0a200645201300710303242445144080d1903103c0d04181c1007801e00c0354070052002a850061400c2d0a0500700001a0817001403800f40c014a08805101010381080c42d00400079410f00d21001000400b281d118002d204a00c060040d405445041405921443c17415000c2c040c00203c160f140104120b03603d03443d5a40c209a0440b507107105d015800b1408807028650f0002e81c00d075564220b000c0c0b2003c1d941c00005801501c1c400e00c000c00c1886e1400c60031380002c208801d0000c01c0404208800d00050420114003608584107517405420305459a81070000c2d40e00c04c82d42000000d003c102c03021440398054003011044d0f900600d190315454281f0010983ca031195000729030500c04c22160020070461b1504044000f003040000b1561280d80f9070007015169403180d541d9602c0744c1150b25100d0f0707160320a8440e260a084c1e01c121258a03103072b040003088280e488018401c1c0e0f8045014003102d9 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 323721151 1250 323719901 323719927
    0x504060f0509070e060a03050a0f090506150103140606090d0b0405060708130f0b070e04091b0e100302040c09050d06050912040602120705160303051206060f1c02 71
    0x200262408100121905041c4818022145801449603042050701c3c80b40d001c0e00c1d00c4d00811120301480c40e1038045080e5840b0031003240941191010200c0040c5001c0448091100120700d10b405150040075400c20005c030440110300340c03000c0040540e203a01381d040215069144c60070040c24520400740c000207264541d9100e4209642d03045600b03030703a035400040404c455564020340c042ea20a09628001001c0380b0142c82e41c05000440e55070080c1706e20946400b054609000b10003021800c0f10041c401d01403500c15181ca0464403a40307130100703420b2200718080400d4002103c2e551a1051803203003025040503241d5000c01010b0701110480000303010210070040b60503122032100c04401402034070049082c3c00c00c1c00c2e0a03460100c0c1011002c904003001d12050144903404203500d4450300c5081c66061f00c82042c2d0902608040c0200c1c3c00040300000d0000000825400c00c0142c081c1c609040c0038100190b0300c1009000d0a44107460002d021400e00300610082c081000541d0314803002214401810301c0c03901d0b5000c03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 323722401 1250 323721151 323721161
    0xd080405100c0b0a060f0515070f062705010506060c060415111204020f0603010b0405060f09031c0e1903020603180f010b13060608060607030302090d29010303050307050a090504 78
    0x40c90070b41c5130b0b01c0c1481003a0444030b00c0e8008081c10707100955005510b0003588c4060252440003000402c440c034046040c000e4681141b1000300098049003000c11100628007005250014221140d500b05030000d08545401410ba032000c0700420b000d05183d0740c0e16910a2001d0226201044403e0380d03642550390800c485102400700b4592910100800703041c00e0041000c0c2c0f506203690503105600030001030080040c44000d0300c04a278410b4815940b540014006190103000c0e10000c541c151103143d40454501d2080c0f080c1e20f00400c46a240e001300c040b501000d11081403562244502d00d24440d540420050401d41d00441e03105158022180461070f11802c80c0d07013800d1707441050b808180e4680181c542c0303900d040c444011010400c0181003000c1d074940070018001c0000103008620445011424605240c020740481d00b41c3c0100408207210011549881081808248400c000100a04843e20792108860b00814143d94044d2251400c1d42c2e100003040752036910010751002000144030340040c09480b14050 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 323723651 1250 323722401 323722411
    0x702031c03110a210c1b03050f070813120506060d06020904050903040501090e1303050703170a021e030712021305120d020c06072a050d05010b01030b0d080405100c0b 73
    0x813140e004040f242d2408a500072502c0340c0083c586000c50802181c0e41128807001603100b880040400c45180b0304054078140a10190310780b850300001680c81c00c004e0780fa03005040519a512031001b03a80e880312005100b081d242100140f0a40c050000300e00781d1300e4601c18110f4030900c9440b0251901004c48007040544509603440d450941c00424140308035a000005174000e0170004910f61413503d00388000b081101c03082c0d40c024080c41030010381c84c2d040c540305141d0101034140c8107919483c941070209481c0c0081d405074500107141c03004044100c80380038851084034010f42d96542c03920b21407100140050001d51040e40044002c480241c0000740d41e454003550941c072032030f41c0d8020b0181c10b02008400303801c142a10354001d120741c0013081108000303101c100000c0d00031251031405e00b040c190f0344182380700300b42099004070b50f106060b46119010841c0540001100350001e07a4144402118481446148044003100821594042c4028403103070034052148110000985030180002c1c90603210103019200030b5035 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 323724901 1250 323723651 323723657
    0x30a0c06030e0a0c0b130f060807030b09010302030d120b1503091c090b1312080901120b01090302060f221e0f03060506030f01060605040603060b0702031c03110a 71
    0x100a441d4040c42814080e020300d02c094000d1070ba6079510900d504080d4000c4101c14a8007140c00c00c1811401c84c0545d015200c81c042d0241000c1c0c403010007801040007150744900203420094016024103110081c2ea049030780c086c0c0244100c189000040e1141218982013018007580c1c0e40c0c403d50365a540c6604452003150202d4425960704000a025080c150440c840803c88100390001c6c000c8294086108411a0000f1103c280c80381900188105404c2700c80d840356500044003a41002404400c0008050300759090300c4080080ba00e001e0a2015140c404400c2800314111100030005410900c006200c140e520201035880c10b41848141a2105110201a40c580c410b9810901201000304c81000c0d018282c1100000c07410b1800e80201241d01d07080c0001005591208007142c080e4074100403600c0c41c584180000c0c845c0a40702c031001403994020f40309000000b810300c03800080307503503c841c11203480030f402402600591400760034894116021015030b03410940d44580500007465000003912001805075 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 323726151 1250 323724901 323724923
    0x50a150c081e01060f020a02190501180501270305150906090307110f030a050618010606080606090f060409061d18151909050105090f191e02030a 64
    0x80042000700020301d0b01d1008654003607001424854507800b1811954107150800280b030034020101d05040017038600a400c034401030000124603d21140c68030076204283c0c4c442c1c030181d4900f40c03043c0e503901084c8941404110f524100d041070a0aa0517803002e81c808451034501003541c0c91f0340e003605c0c240b400d0b01d00d24501c05604061003103581090180d42e801c151000000c50030100386480d2803408a030840591841100300b9640103050352024803a003120240c104e0240c40c00340c607250500390300b01d003189d698611455282100c0420024010301c1d04d9030048102508035820100c0301c0c014086000941080c03254417150a02000a5111490046901402812503016002441e00c040e11001e590701900244000d84030030f4881546207070006e40851030401005000070180c40d9889010218801201c090310700030304003032003202800340540080d405000b04174119461040b00c103040a0300c42e5403603038482403d0340c509035128020170800c0340002403245101c1072282e8640300070f6002901d4111840d804907003881800e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 323727401 1250 323726151 323726171
    0x601110318030f0a08160212061f050301181203021c0e010c210c03111201050306011401021209041508010c120204051c1703070801080f0703080a0804050a15 69
    0x14480c003c102440c5400030800079aa41e42c1e400903134040c6480309240c0f404120015001d44d03660244003e822052031042d10024142400404484100000e46810440c01c132280026035090504c01c1100312281200700c0302d9200120b680e69a0b07c842c000b91210101902405421032401454001c050346040e6a440001e080010149241c00d40c1c0d04a01400d080c00f00c1800203403031881c001e0704982c12020300020006412a44440150010849540d229003480c2c004500303180c1c044580b09a46069070350440889507980e0340c9440400480c16143e8120340160000c0c18402801136400001e0400780000400209000108030700c4884002c1d41640310646a0791611b2600c1b00b0103400c8013443c50085542d68003507251508206c00b158801050b0f40030a0140b2802c031026605005c1868444442802a13008031596400c1840000307111040a000d07480e814082e145600172100030002d0b210040325445805c10341060245a000e07580c414004000351010700030080070400091418031004503040c0d280000003581510 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 323728651 1250 323727401 323727403
    0x10611070e0a0b120316051203010b070b04030e0904080d0b01080412390b07180e0603030d0c0513060309020f090402010c15060905250503060111031803 67
    0x50420a1442500940300c240300c601409038015a01200c902c0010403031142c0600420101c5100c20441001e5000c0031480b2814000b4000710950000d0180085600742d071440d00c480c502600c001e01c00c091803034604112520004000c1c031042a409030107030411604040100c004208041c0040f0b4044540e2000021300012210b001d21072011000800e2030141d541c1c1c070b0503a841104c07004228413034000b8071001c045180503181d401101281364041140000110b0501e4440e0500e802e20364210450390405840000341890344191642c0c141c03803080e0705d022440b1901e010484105074001401c0d082c0c041c001004401903808444c081e868801c1e4055983c00d070f0300d003504455103265a90541110082609000032200035a44a01c40488071080031500044140c0340d40c401a100d0050f501002030014545200c0482c60000c144d1000040780e2080c00240956513801c40c0031100c0001c0381703c0c150724220881d080c800c4007030302c5080a154081818103156030401400d529083ca19000f4003421001e0bd854134034000002c1c14 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 323729901 1250 323728651 323728667
    0x4020d05030d060e18060f06040e0106080a06020702010305011208070f080909090d020c030f0318010c0c150e0414070c030e0310090210080403050409051009090f0209060a080c010c02060705070b030106 88
    0x8640005401b041c01c0044000c0c21011001c0d085600ca40c1d1210707901c1c01c40400c2035012500902e000b4045030451001482c003a00650808070050b4003003498070780001103000c150a011107410358080d035140d242003140d69600d869210321120580340b1030390a00a003840e0b074845058190003900660000d21080103948030091074404030000440c004c1d0406003060780f0b0240c0010070b8502d070000442400980d20150001200c1d030140f03114000d07002c0c0b040c03200005903102c0364400926011003640d03070f080c00d60200d000500041d01c01004684000204900001340300604c20503858091030f2007032600c4855200d4900c0042d260403184051030f25010350300c1d01c40d0011413605001d200f108c5225410a01c00900d0f140e10090210701903849100c25180e25200006c0400040c0c8451002a0460203030801c20070b82c250070b180c0041085400204d00070080500407035900d107040d07003a020484e104a00208001508400111403200f03006400700c3e0066424407400c2d00140092140c10098044091155107a61420b02c00070a049 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 323731151 1250 323729901 323729941
    0x306030706110d03050414060708071701060e011206030b0a02090a1401230904090803070e040b09010605070312021216110a0314070b2a03090604020d05030d060e 71
    0x4412940c0342d0030b001ca000300300302c00e40c01c0e003e0900045c00c1d0b1b00c03420001030044040d10908500e0250404020b10980c0002403d801050950342c0c100000103040080e01d1060020f0098002042246101400c1580b2030304400c0c07049079500101040c1c1c41d50300e030b880c542210700503503070700f000710b034000c00c40c081c040c00c0c24058100185840d40c3c0602000100c2c0c0000b8110441381944509202c01c2809000d92452254040300d4411801400811240348141000c1d102c2d900280c2e210300015040300541c407503d01c0d09000d00b11401c0f400404020203640707014410f450300d500c2620103c080c80080b45001e40002654030140c511b4040041c107410310351030014aa0603144010303000d040180940440d814864480008484400641c103081051a45000b445a201180940384005140010440400480b40c2d494072041c41d0b4181d0b40743c10004a001000380f080d406000c02c0b0f60000650b80000005800340c90244440725155020f902520704d07101c1078004200944000f60000c8a1101d510000d109810b08c032841c06192071 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 323732401 1250 323731151 323731157
    0x20d060920130b030402010c0b0903071e0b011502010906060e1f0803040306020304020d060c030638090402040b1201060801270b0109170f0f0f0706030e0c06040603020306030706 78
    0x101c04040d1450326220034500500f04411030100000d402c42e40544030881d12150000042c00484c0b0b8010041da58a80c0041e404950140305500c00c0c040003200c3c2485411510350102c41e20860b80e00700b6010380b0443c0388142400b000c564035007403202c0108065215180c0076121141540307005180202c250400c0c0380c1901388081000b80440810080344101100307031401d982d4800e50151b076030345450001440607a542c2c180601920725040001d02690740540c840812104560713a1915400e5191440324651111804011400b1070060341000180f003140004080a03100240018182901c54039403101c0d0341c10803c4c5d16100000008010f01c0150b40254010740140f41041c038607004085400001403540c5040384206040a03110300807007040368020000c041c0580b0004403144100b8201c04442641c4516481400200b03007c2c548090b05140c401182e15205416071600420607685400300031001842d020030301c0700080c042e100800e003aaa171360b0001000209200d40d0050f032241031840815041a007294484018 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 323733651 1250 323732401 323732407
    0xe06010503040c03080f07020a0e070306050f0102030d0908040e04080301140402130302060a140a050d0e07050d032006130302010b0405042f06030103030816080907090c03020d060920 80
    0x80c101584100541341d00502e226112610250005542d0040c201f00940c000103032480864000c2e1100109d138400c1a40c1d603400d11240395078600b44044078903c44da80d2401a00704000c08401e192040d00f00803040340c03040005038900340c2e48603c0301c84094010740e011501880004010022742000b01d06542d81040c08440071442c142c3e0090388240e00301c103140310081c01030202180001590340139000c0c0c41c3d195280c0b4481c0580e030b003112010003030803a44020569403080303250500b0740d00704080004405040c5c0d240a49040101e070050340702603445012801c00f211103203403100418041c1a405010441c0600d2000700062030070881b0b0700e4080e094030040034a59018031b240c4410800400c403800600300413400301085d80c11040f1184070076001c2c610300d0143d00c1c0380c005000100000c04c2691062030f26104581a07412414240c140da28203d56a0005035400d07012540016000d000e000125404440031111f2410014940220703031007101c042c0c400903801000310695801091360a482c00040300c1c80c6100040302041e107 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 323734901 1250 323733651 323733653
    0x1020f12011a0403110f190f09060e0a0203130c2603031b091203040320060403030509040518010e070f060201020a02062a040b04140109060203070f05070512070e0601050304 76
    0xc1c2e0b4055480040c1c10342e40a001091081c0c0c440030035401c0d0a841c0a04668030f0004446080c500b41ca405109900110b50b1000b00000d03c48030601c1240d058a410703000708101920f13014a2040a5040901400c0c220009558540001040003541600a117146a0030b03034600c6032050741108007003410031031149041d0800c1042040602005007000c1441c0d0181d000315884100d0035010034842001110b0070011440b0014000c000d025451106254076000c8201d18404254260140304990280e03103c010045041071003e50b50f0751034203070400c560185c0c040140c000f0740541c65442500350760f4003060f41200780d088144140080600710300c00b0000340c4081c0c002549003400b050300003961010014003050700b4009401d801c03011400c28a0300500e08aa84201042e1648e0716840301e8202680035100740700c8218402108542c0075401842010112022500a0760410090707448074061a1800e0004450703c3c0140407005c2600d40e00c48188807806104000148200e9040826818201002030704c9941404000c5c01000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 323736151 1250 323734901 323734949
    0x6030d030203040302032b0905030d150303080a05190204030311100b0f0f062101090b0301110703111c03140603073f1101030c0f080a11040801020f1201 67
    0x3d001050801c82c030103003420302038151400032254280c1c2201f1240c145a0300c3e038144100040504503121841c8410420724010042c0380c203001304244002404244a900010f00d500c01030760101e588035021203ca003144040710403441c000c99110703030000c8021901c040000c6010400c02c005407041030044030b40400c100d900d1040000d4490852500302c0741300f8040b482d08004243c6582040c2c44100320a103680360080135103e00015001242405209403480c0b81c0f0115a10614050285080341f00c4070903c102d1030b00600303445c100c1c2c48542101a002c524460700391031106036500e44039081ca040103207036000914050310000e01d440a55001e08424405e5110356000c0c030442c0c04008060155008600c4580289548001c8030500c0d810740254000c0106012044101841a140040c1903070300026030703041001c2506000c041d075001d6031211891000402d5840010450002c50f440581c174003010300581400c003a5104070050a9078044000041d0707a40000c11411042030250b0100e07805400d0400e140713402249041c0c800 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 323737401 1250 323736151 323736157
    0x70927141504020904020d050406050103031101050c0f070204090b010f170105091005100305011b080c0309120a05090301091a0c0a0f0e0a0803070c2d0b03060f0d0b06030d03020304030203 82
    0xb0b1140e58005821440340c0e480380e0480d600c550920609008600e080c1c100b1000501003440140d003c500c03001c4980c1c80d8030a040c420584513000e048452401c0941e01905039038190440d002c202d8100c0e030f45400000114042c007095500901095441002e15410728000c05c0c403510325a0701600031070381042d05110000102144008a000f0303c0e141c0003c040e40d4080003801d0906460740f000e4195481d141e88030100c00404103001c60710300d0551b04e9280340341d161401000e1061000f1290514281c205a268209074000d000040c0020303c401d1500781e080c0803103200040d0031030343c45c4001210103000110040c1c03a8005202d800981c80052040c016007041e855030000f500100154190707404000e1301c1c15451016070f03103032415040540308220442ea00c5800c1403400e40b400450387d0054541d01072003107400b40296002c58103a46001841c0302038200c2d007146031a070101e9031500040e1a44d98044921440030f0040e8885108010540c0e000d400e190000d82440002d00d410310402c12851030800d401003040002117038000080f = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 323738651 1250 323737401 323737441
    0x4060518011509170604020f01090303080402010c03121103060a0504060303140706090c0305010c11010501120209151c120806010903020603040303140a020406020f0304150807092714 80
    0x80c0d0701c50030b84070315085030303103050782d40180c002e202c2840c1d655000c102d000a81148620302c00d50301104003c04101c015240c0c84110703c801070000c0e03a0000058015441014100c4003280b20303003002c0d0f5000078a41c4141e004d41c0c2038101030501100c0c01000300192450821200b500522060300e00b04040d03070454030300400c5950076940b0807035150000280a000c00040342e004081e480e4022142c145415120b15002c0c0c081e0200051020001e85010503070007000718184039a904071104040e40baa102441c640c00d201600c80300900000c8001c401100c0d0000c15280e9011011001010b94050000300c52149481c40002802e9466482041708076410060580d0f0003000c1c00d001d4070f0301114075640307a6845240c00c501504030400010014841c1e0741c00d000344042ca54001e0410303aa00c0c0c0d0240d580c0e100c09100210755901a9105150580d901c0c5041064040d000b00603040d000a95450071541c038945950030340b240140b02400c0d030112456040300b0819921030b50311694211071580c8951200d50f040c0740000e0000c0021a840e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 323739901 1250 323738651 323738669
    0x70e1012030e030a030e040509010b100c0c0f0b040302120f0a0303180203070303030e010b04050f0604020c0f0a050703060c0c17162103050c0a1704020d1b050406051801 74
    0x10380061500489004280c03101c001d040326080c1d031041c94002c0a800541c0c10340d90049007800041060448103014070310000c580a014007000d04103a2400304d0318030300c04c41d409a584a40e06000414109501e854584c083c100d0542065921403a600c14010842050f051030701d003c0e08415064210301c100070510400154141c6004500b002000d40e0f1a070018540c0791000354548204800081003682507001a4011aa802c1c0200540010b81043c8000c1c2c1d01b00311500741200b481640021000c2c80d2030340c0500700039003050048034110002c0e1901d45150a11080782034a203a030001c03070208208181c40c0038801d240c144078600911000301c603907200b40601002e2035142400f5500415411031842a5102440d00e0a4003c800341042162a100308100340440144810001e030402000030305024075001152029030032680e816000b80071080140081c1000030304103c0e07010800451351400300304800410354085609000700743c0e81c18079003020042292070f20340c40103024841d4111007503135640003203030607504480382d82e0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 323741007 1106 323739901 323739929
    0x1503020a0614121b07051f060503030a23130e0c0a080f090c0d030509030f070f06080a0603080a0f02072103050706110c0a05070e10 58
    0x1140c00000002c03c42c01070540d01810181d03034003c04c1610382c8000002e01101c1020306500a0600b40d466034080540117002c1c18803d40b4900500c00c405008202c02ca1510020940381e0040b003452600b400800c0c5000c512000541c08503111081c4000f4065540710320101a440301b4001a005000c8240d60900c00101d451900b402114121f00300742d201c101003581d500d01b1110750904000e049000e00d00a07540381030100e46640705140740f010300c2900d4054030b6035080c00601d4a01060000ea400ca03c2c0d00130101044050304502c2e8000c01e403022413400b5410b0f5501c0c8240100501515440201100000a0026481d59018115520100c807a509850380f20341e603511010403d4190a2417034901c05c03405000c1c24002805a0010f00b0304501c14003000c54041c074510446a0550040c484100260b0001c41c1560104401840003c0c0501600d4000d0181814551038070301500e0030034042c038801d100c680 = true := by decide +kernel

theorem cover : BRFrame.Cov 323561151 323741007 := by
  have h0 := BRFrame.cov_init 323561151
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323561151 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 323561151 ≤ n) (h2 : n < 323741007) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
