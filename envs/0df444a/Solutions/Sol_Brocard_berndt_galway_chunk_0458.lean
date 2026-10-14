-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0458
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:55:16.103556+00:00
-- url     : https://prove2.me/submissions/e823c1d4-2869-4cc8-979c-9221c1b9089e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 82194246 ≤ n < 82374102 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 82195496 1250 82194246 82194253
    0x7140102220f080d02031b0a14100b060c150c0f04120c05060310050105070501060f0815091939260c0f0d0614040c0603020306030d12140405 62
    0xa10110148100180190880308000d094000981300000d5580c8100c01460364a000c00303c1c0007003040c010500c200c1504a4000d0480c0d01070040080145886668101d812003040785400c9299469041002c1a91b546c000327000b0190000311004608486200b00040000785180d4080081503500c4000d2409880506051528110202124503040341c0904c51a0011481075400340204040109280703500401d4aa0a2074040c3d1661820300c4c00c0381c050130b115004039401204079100410154170000c0d0b0b03c0d07503000c10407103040242d4071070610461300e03400d9000c1410105001c81107c80045280c001d0080d900500d01070021700d40d203000000c82842e101b00320703601e0715140800d13050410500030721840c0a60510070b001c2001e442c0c030004030f1130303075988084c1004d1080c00b50826400f00400d036078400e0403000440750440018402000c10b455281044081241c1c120f0b440c04002d400401c1980c072070310030b40e441094054020000102c2043d000d443d1301c02c0c0c3d9021340c4c0a55443d506410f1484520100450085200b803005 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 82196746 1250 82195496 82195499
    0x5030a020f0c0a060c11040e0607020c0d0f021c2111031611040f0509010c03060b390a0f0b07140403060f060e0c04030b060f060714010222 61
    0x1d08264902200d070041e64040c41080850780ea42ea0150802c0320644e0810000514251a10718031030001c038607103a9485850f01781c10300000392010841c68464400c507030070f8920458080c0100050000005400350410b102554410014200f01707221101c2640d400461000004455030f03007400c40d000c0480194036074060080104541c0350001c04644c0340d5901440550308004540798902565440440d001d401d03107050095103001e80d00c41d07a200e6005040c84640078022464000c1815001e40240e00c0d900b000280b8098001400f1081c443c159140220a5100d00c480c9200400c0c260041c0070ba440703601003014000c62208a8440d40401088903c0c1d807041b6091200c841181c144450b4100d0014030340400d00c00c03542c880c00c402152031400c950030f80e40d0084000800002e40c814460040c14150010710300ca014001c1030011080e281401b910490340f0404075841181d540209000700300ba801001da0f504420140036407800110450f101c01268201140014280028041c81c0440302070441c0c2e40100d007980a440 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 82197996 1250 82196746 82196767
    0xa03020d110403020303030a0b13020a09050f010201050108030f03091507020a0c0504060b0706110408190507140915032509110c0d0c11150a021c12020919030503 71
    0x2994641d82805500078205403854000c252240707c020002d24126547c0c0d98580c40300d540314013005014851101d8115201e02c0319440c0a807020a5a00a491050141204c9248190f105014082c1a140c03030f00069828000c144000301c07660303040039003a90280d000743d099601c0446413082001e441110658000d2140c48620b04001c0c0d501145030300000e01443c1401418000c00d1441001c545003164003520024000c0190410303c0030320b000c0c0380c114500d1402810b441d01c101a29010864048900840503607244039620900701100e5104111150380018074a000103000c110120482440c07450003500341c6440540001a0102180707070003140011031032810390248540c04051203405841802010101d140004800d100c03a62501031502040421176440031100800c01020500303240903e0140c408a403442220714000e4054112042120044c4a2181c0c90390204500090203802310009448605540303000c6d800f030501a50185000940054a162000c03008058020070701008600440140d91210003060 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 82199246 1250 82197996 82198001
    0x5100e03030703031a040b150d090203100606110a051e011d010510051219020d080408010516020a111e0306040f060c080408090405071101050907060320030103170f0a03020d 76
    0x2241d01b40103925002c000d1100b9281e030407448004514020312951600d07100c403503800c040c0c140120000e4060241c2c00042005050300d42154096a44075143c07800350300c000445c001d984a00d4040b014003168000000505003005038088699800c141c0000440c01c194420b6100700d80701400105842e207030303644504100715003074071085440180c0811511009040180d075901e583d540c01810303904005080f40341400e0215600c0e10b03a090340855009c44181d4542d070343e030120b4034020081107134140044941060914000744c030115009042d540c1c0040c0d80c201c03041e0864144682520329a1014072328014041e10107041d03036420059144124441c0181c005c1407010b0b81340060517140c0f11280072040c00014410303c00042c446074107881d50300c042641c0014140e641c4080071500c44d2002040342c2000d519000a00c00d054a0110b20f100c01c0c1ca90350b8605100080d0012465280d2124147e1003500b07906d4107000520000d111015039564400c001031005080080c040140f00c0c1c207502c903004c620040781e030004030300140c1e80090 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 82200496 1250 82199246 82199291
    0x3030906090f030711130902120102030f010902040501051b030904061202030f0106210203101a030c01050f070204051e0907080601120f0305030901060f080102042d05100e0303070303 80
    0x60180d81400e04655400e62920f031105e40191050580021243c4124020351200208540060144c4507051075204e615000703500582d0803000001011001003803200250003240c0c1202e40682d43c3c1482c22603d4410441403040d2451101980c0c0001c20a045142d42c513405000d000c0c040f00c5440c00c115074030320300c105441d0200c01030800140c1c1e4180182000b2105840f0541100702087c1c4e10000c0b01c1c41043d100090801c01c07810380201d48a481c0c032012f10141882c8a40e010610034054045a010040c2c1030300540d018001c0070703074242c160b00e8100003d070010f081a820080d00000c5032802a00d9050f042401c003400364008854100c5241d10080d820020040200b140500400d00001400c00e15074107130f182c0300e83c01e100601018013882400404580c1c580b0b02548110000c042c08040c1070f04032515010200d000c0d6005104151075081044170304008120030002050700004890800034900d890401403210706400000644240022800c80c4d4625450600c01042564800e942c0042c0e0549145409554042171 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 82201746 1250 82200496 82200523
    0x40807140f010c080a0212030a0f0b040603150b04020f03070503040c1a0f0a111c0f080f16090e34020a06050c07020604030c0f050d0c09020901110303090609 69
    0x920750303500300740d0300603081224030768115403003030303070703c542c030540580c03070003880840f8091410400402c00007050656488200c0b40c0156480510031400c401c0200019a409408080c01010717011103207000b603061590201c040c501c2c02a1000d400d00e511907061440c7c50700304485581c08035000104000c200108020410043d1203c030514400c07981000034241007034056181149400c030800104614014029482400c0c0205124121044000f8448038030029140081c01a40862000c000001040780503c040768880c18800220540316a14240d0001517000717080b01d04001c0c0819844081880421078000c14894106900060140729051580d8000d1045448030b100c06011440c40e03441c44030342e001c5429200d080e0011800300391380c0c03a18890100f2511036440000d501020005002040064000e290003c803034000110310151580ca03014071003103080c1120014003ca51401c8140718500559000d00b00810381031604200003559a08030b04d25583c0180c8110003560f200301d04100e5242c00c10024000384622 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 82202996 1250 82201746 82201759
    0xf090703050a030f1713020301050a0c0e0d060b1003021903060308070209040c0803120a0e06040305040306181e050c011d0108090309030a03080114060a0f0503060109090204080714 79
    0x185440c0e060301c0c2ca5107000c000782004480700302c0d40407041c81100314241054a5042c10705080c10451034076009551050700c124003e500304000a03c00c0441d038460360b5114000b60b2218480ba01241c0100050000ea1034412107060307a0b10391120b1219211003250300302d1142070b0380b40141e0f9410103101c55a0500240c4070543c0416080090074000603036544207407071071198142d8480501d6226403408200001e80e64000c0010b40c031010404441908504c4003482c003a4841040400c00640316184179501c030502194042d003c2942080200002920b4ae849100100f00c80c0084141400c034641e12054070500202d000c05900d0400e802c00c1091100500400b81072042c2401c0c410b040302c1760b444070700c001c9501c00c8601c039041c4490040001c0600c2d0040c011202c0daa4401003e0751081c01844c80d01034490207081c0520720300030b205440300e189a402e0880445189180340c3d00c50b100c0512901104580e2a80000c040c5410080c4410b40021412428005000a0a00030001d010500e041411801100b03882c4000c0d14810030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 82204246 1250 82202996 82202999
    0x240315030c060815030111070606080a2609090103140f070302011d04020903032a030403030c140307060e010618020301050a0e041a070c0c1d0105060c01180b0f0907 72
    0x50710745400c44202d64181c14507040c141c3e00d05a8100081150b411402e8140d401c2920051048900000401000b44202d204200841c1c80782011940d41203440b0380141001f40940d07680103000c21a0000d44c01c161076420303078107250400403408240407020a0b8000c907030b1326a000103510310500c810b20081d0103110214008105903460364000030513940307480385001d8551300102124141a1507139012034050400190440e5560800340d240c5803900c50300c580080c80300d4140662001c140100c04412142101e405607030b065640801074864807108074400000e07031070380d2008100d24400105540200b469158540d4000540d080c60200c4440b03480061101c0b03d01031500c1000103001d507a0700c8020030415180c4c084081485950303549094000b0b000c130012086072896804041103c1258002101504144280220307004260782e0103411a49000305a8050040c081c4040188928107141001e4040520314078008103400300504d40014020781883c805803032081c140020000d0b5120f1414206400502c00401800e0b1503 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 82205496 1250 82204246 82204253
    0x25080d06090b10030c0203070804120c050907080c091f030c020105062209050c060304080c07050108091005040507090e16140102210906030106030e0c0102010516080604020424031503 80
    0x1c0003162100d006040e50382e0104003000c0e06c00c00c203417050140e002e1522070b611500d890f52104400d40c54041100d81c000c506001080074200300c40c0c00d5000e2155a207038289240c03a05c00d00c05800350044044203400040b00c45418141118280c0400303c120f032643c6001803038aa400f50002d01390340005040d04e004141068000031414550b5440102c2183c0500000500440b249003550a0041c43d5030242e600c030324003205210a11030140010071080700c0798002c4480d400d03a00c2005441c5c800c0e007100c07443d0240d04810310540b041c10440e0007443e841842030050718805178455040c45c00f1251510510440359002c1003100d0141c42260100324040d04180945c80c0c140314200000139500c1b00507084054180d1003482a84000c807807120300b03030380d620a0020a17480d1a50303180c900050042070100902940b0340304e1000140321950061066078021400e58110401c40700340300303009859034003002e05000c0c0c10076400c010000b2810a04c40f4002a14070441391802c03221101d406008040e034550b0410784151140307045040001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 82206746 1250 82205496 82205509
    0xa17010f1202040e030d05040524071706030106030206130302030111041a0c0c061818060f10110109050a051507080f060f0d0501050106031103060901060525080d06090b 74
    0x780e60440d400705050401c2c2c01c10318114041e1440c03400d40c5d5820481031004004020401d440442440c0e40340301720156100d00f00c07402d041c109a0b01080404c0c22584040d0303005d03240201e900c0d48800080c0c000700d0060fa407a0b001c9000c550095000c400069007210042c011868203004011403d14484510341c201414446140344e0382002c07401c45060810001002d881212042c80440701e0b209000300038944890301020700003040700450041c0c5200c0d4990104500000c50481d282038001c0c2000f5184800c02c18110081c00480b500911080090010011a0202e014003d00070740040074450b20140408d0a40c600e0110314000409014085080c452000c00c0080c07681305c11007581c0589400d0880030a40c56583c0030400300701c5000046600080c42317445610911005412150495105035010821151a1250000b06000580e042540b26040200401c4044d01c030304090402265000d00d0200c0101554010040401410804459101d8045400c074039565282c802c3c40014034260109004c0c0f060041c000480 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 82207996 1250 82206746 82206779
    0x5100309080f07030903050a0303020304210c0219120c0e010b0c1b13020a09060216061b020418050d0e010305040b1605040816032a03080c0a06020a17010f 68
    0x42e584040307a9541410300c02c24060001b160001c0c00d030f0b80104c03200d060003400f070b610071681611500501000f840080e030005000d4003480019540e01e1141d41019800c000b0340c80400c014440ca0905111000308108200d00200c503500c6100740d1071801403c0c6881c000c0701204005030310095094405000d0601031603000b0641114190180a00d403260410603030006511807507242076649001d2012a034070308040c3c1c108070520103554098084400710036810303103d02c42481485c0111800074000c44084101c50340e811001c1d0100e907200a00100d51803000041511040c10400c0050ba455441101c0c20808560400fa00302840c031000c0c41d05114030300c1d19441d0403500810190008000003170000594080301c0c805d1060710701500d072980644e008201c80609002e2001aa80002e8528040a03080c50107410340c003130f0070b18902c1e80700182c28403103051a58640c1c08194024009010450080048040004003984020031048641c2c1d190003140a500d407403622032940058002c410a120b00319418098030a1900740010b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 82209246 1250 82207996 82208017
    0x20f04090b0c0d06090c0e04050105060c0a060203060301181505060a0e04111207150806040614010c030e150301030b0603010504020319060207060504030207180507050706020a02010221010510030908 87
    0x5a0742c0301406820802081305501c02c0710424030301040188440e40c0720882e00c02c200c0080710f00340305a98032b800030410302e4820212016803d510400c80d6100086154001e107500000c01400011000760b060000c4000d500807180880300101c48800246071021544a51500310310243c444107820703800c1032440c046800b400b03000079000030f0221710403503055507a010001000450075026034210a44d0ba008d11031550806803843c50211311031000055150820380700e800308569040811100802d4000010741e03140031540380950030000c2c0030312041102c1d1140c0c150f94815595918042e0f030b903503145003080d02a403200640001c2c4a41d04201c107001c0540e800189401810165000b410a40314042c07070800004e01c100140180031504020400080c150003165581c01c83d001b440c52450008520407040d401c4800880c0c45034041001480b00c90003117212030780a003c041d99540001442d0002280140c031840c0321500e10140b81e8010240107000d141081038991820106d2400c00b840380c500b850307544031100d004040694 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 82210496 1250 82209246 82209271
    0x2101109090c09041104090b040b030c1c0605072114040b15031608010c091a0a210b19050312030618070c03080601080f1906091107020f04090b 63
    0x414424070142191a0030070300a004100384041d81e0030081715500544600c001892070080300c2422800c2a010300e491030b00000713020b021442d01e14000c002e0305204250414401c18810040c800005000744606070050035103071034000384168250703440d5400b0f454005c00140c2e00c0c0d0504505420350b0794549403031500558410103c00301503485030103400c4018510015035030f05100c0d054802180600b514800e00c141e40c0c1c41802445000c400c031405a400c0030192089040301400615540c04402c8501c001c2d05451085181007a10003c0c5101c400700c81c5551080da80b0400c50741c84000001c00e25100b035143d40080300c0c0e40510807129140100098603448a501c00105280b17000000030074556515012506810711070741160118104094000d082c54809030049001c180f080000c03d1441d0300480d5400d10405403441c0580113075444448500740001b800b007007450400d480e8030002c1041c49480c0640d1103002c0300c0ca54041c2e100d81c15401005030319104030309400e015130314010085002c1b59000210583c040501c080f007 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 82211746 1250 82210496 82210501
    0xf0a02150913110f070f050c01030b030a06050a020d060914061207090b180702030a0305060a030c0506071407080309090c1206010c0c05030d0302190f0f0c03020c1003020403030210110909 82
    0x42029442600001c41104c0400140001000750170102046c40a0164040352507018043e0019401c0325181001d690341a0710001204001413550b42005902048040c4090f0610b00d503403840105456968210540107a25580c84440202c1e000410550011041300c0900b450340f2107440309501c8085500620001d16290325a04209440d985060382d180b1400e00304000f92440c007200025141c1c1c014078048000281040d02203403c9160100c10302c0151391308091858580752174141002920341c030408088900507010000c030f542014041c08801c001307145d400050350741d4000141c100503d9443c02482d44901c1c1c0000d024844070500300d40407403a4015001c0c01d1a0700300c0745060800e0200d180303080d40040c0d403610078000c201c001c50b03506070041c025280b00701490101400c00c02c001503e08240d00d0403003074005000e90b09070035010342c4103c481010300f5010b03005540842000d5004903000c01c0381e000d505008250005010420981d04000019011680300b0080150101034185000c00d480350318201403060403883c5c007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 82212996 1250 82211746 82211771
    0xc08040c051c0203031813060302010f0c030c060509030a1701030f081318060501030b03010902030d12020c031603080f01080a030f0e040203090a14070302060904050c07050f0a02150913 81
    0x41d0100b082d00201140d840c1c1501c0707002405081002c44074240217142048440400000600821040da58141c484007003101045204035169025100140d0030051a0040340002c120f01e0b02c0398601581900002d141e843c1032206002d4210640c050b1f0004110701d4400c01000821850300240701402d078803444072540c2b1280740022084c0380300380e034000c0c56600011510b00040203c135035011008861003a2030500c1502c201204042c201c815182001e5010b4011242c0000294418028494100030710380c0c005003000b030001091881c40d041461301c011b419060304410070a26810414040d40003204007140502c82d03050041c030030346660301807800600303103c202c8142c0203000340209005070600d000074004644900d0160b40c0b0503a00c0b00503150641e000150001221079051000c68600241ca4003c0c007581d00d00740d411014840180001440d1000e00c070401e00c1400d0000388180705608440100d20000e1103000041d0040005030001d000c0c103500301c0c0404100d48080d80d290070701c0d4112401900940000c1003400d0f42e0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 82214246 1250 82212996 82213039
    0x6130e0606070c1d0a0501060e010e0415060201091b081005070c0b1f14060f1605060c041505071e03170118061a0702060a020a240c08040c05 62
    0x42e0020210700c241c100200e5500c407000c0c40c03d4041e6050039820b00b0740b5201c1083e203c04407002800384c080001c1109130101c1c141e502458111013440c0c40030700005840500640b180c9040309880d046600183d45448101e0140128145040340f031042030710302031259a02c1c1020850f030f900a03d10300161195201c40016802c00d0007000c00704821030f0020382507407a07803901100007800240340b6010800e08404115000c100903600e1b801c0e103100094003030040d41ca803917648400518030780c004440745d1154103040c240740070004070203008003800b0f00d08041039552100d003401445204081114201004c0080070300040c2c000c40d0398540303000c07000c86814144811160503030904542001c118101603030480e085100000d205c0084070120342d0154a020700420041d6110b61540c1c403100d400749a007402c1e42d1000d10031f034800b601c0c1000c010200540745004850081d15140e844c400b880c11030608107a0360f40007074000c07451170420034095540d101d010380c600303603240d45846c3d0740d6802c611455010301401002c207081c02204000740c04 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 82215496 1250 82214246 82214257
    0x702070608010b09030703260703030b03010e1c0c061b080103030f051201052b0809030c030c03070501050307050d060602010b01030522060b01051c050a150b12060604030609060e0105010506130e0606 87
    0x8235000d80d104114140030700900f00c00110b1f54069882d03d40b012025100200f04000403a00600510054105458080380d9000c26400256045071383c1e00b424200003070032444031050803891510303510300300d40c51403d020349400c40200300c1c0d106101c0b0410607003c94a60b140c00890540c1c00803580750081c4a400040c02c20850700d10406903011074400c0c196403040c084240d01421a41004030100d030b05c40c0c0424410706480d0741da506010380d0182c3c810702044c46950700503000742d40d000300c00d4584141443c00911114050782c80c103030301c80310150755900182075080d43c0c140038666120490408980860741d107400204e8070b42944d030320040e12056552121900e41c0c2e20900c202ca5003074148031100010340b01015900b6000f0300e419500040e40c1490301040311503c0f41c0354200b10b4111462404114103208000940b03040c035440003405550310140c20400440051590b20907085018014880003484d2880d1802090031a0741c11303000a84030f00002c0c00380d500c04403004401001526402000788080d9140e07000072038004d0140 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 82216746 1250 82215496 82215563
    0xe10080f06370902041109010210020f130e010603110903033106050306090a0b0102190606120b0709140609040b032b0909110301050d1a0702070608010b09030703 71
    0x2018140300b0040803600240c0b15540210340070030200e103d224080003603110784400c840c0507030411000845015042d80c00b42c0a40303641c2c415514909112260b8080f48140603801c0307034500c2c004200040c13002a5051017010006055410742e1071810842d600040d6682c0a01c459444908107400110000c1c0c4051044030000242076000043c52140c4070703400602107030400c549075409440c1050010712100000c1c06489881401070b00900018030b10001c96442c00c000c07180d81510f0681c0c90b0000002c4003080c0c0d00b00f0b920405d0141842241c40c0c1800c4a00402050950340103500e0045007030380c2140707140c0e141c10480300f0081d4122000580e1841e4000406c0c10700701480003407155840c900c04103920401f004401c11491080c0f5030b4a020145031584070341000c07166072414100e1580070610041c403207400c080c1c10460b01d00e80640303103145442404101410180f4000c03590100180c01945080140b65000700f00e45024220222000d410540e5460219581e601c449c400507010192180311111080c00d04414031904451 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 82217996 1250 82216746 82216831
    0xf070306031e260306010c0c081c030e0607020c0103380306010b04060e12010e120405030c090603060a0b01050c0109051b0d110402030603030c0102040e10080f06 71
    0x80c400e00e020a00c228038407003030300c500544111503e43c55040c0f60030342850300e6410000e01e003151101c900440c0e030628081c03401c44003925030724404190704408011844a0030001100c2900c16120054020183c2c1c502c010041c1c6c9690004c406d01044940100324090341b600c007031800085910b6181804c1c00ca404549001402c40c1c079056501d25004000d0003192500c88000390700f15075840c1d03a1488192040d00c107511030400001d2804000840b1841c1c040c45080000d01641d001003000144119600c0c107084250081210081e00058208442c2c102448006c1018070200c0c3c03420300502d4501c0100c0d45400000b002c0c51451641c4500c00c40540c0c0c0200e0039580102e0b001c00080140051510b003540e900c4021400300407003580c40c2920b426552409403600401c0340e07400101110600b4806043c40080c3d0400303000f10381d15000a10045401c1c035003d201410083c414403511000c070b41006810505035200e680c00010842d041070b050003d03074441c0083c58907040b02e00825640d1115030009003404007201403000b102d1034601c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 82219246 1250 82217996 82218023
    0x30f090f0c09110412031202040b031509010501141b070e0f04060f09030c150b150304020a05060708071704050402030a0b0406060513060e04020f0403030c030e03010b090f07030603 79
    0x22003480030105403441c250041011890101000f002c5014502c030b03581e8091610030030040002e1180962000c07640308007001504190702c0d42c00b410305541042b41d4201146410001501c0d4a01d884495203005020070f0038482c4945081400011840c86110034001840c50b10707503035040c100401040070340001c1c50b40ca5007003d81030034140c0b2424090ae00a0340c060399400c1c100802d400600d4414850001c0c03181d85519450011105030b80c0c1c110007440710304d02031003010399210f1500c0e485031510541c29410884842c100c6580b407616204018400d05c0039003285011b4102070041000103181d5008440d09160001500c8100400b19000707000540310f00e410280d0020b0011081c40948001d903084400903c10886045c010243c681c60100e840e4059414030000700014040c08100c15070240d1a00405d609014101610700060050300000d550f000368000c0300001c0303001d20b80341305151f031200c50700034501404c40080c084c816004000801c062009042e41c0524581c0b1004603000a0190703100c01d005540c855865401071 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 82220496 1250 82219246 82219253
    0x31603030f020601080c0d03080a0b060301090e01110304020607151107080307030e0f0717070812130f0506030c090f03010e0705100201020705060106140403060204080102070303180201020a03030f090f 88
    0x41c441450100240c0705400c004100d140e40820381d00c01c2d0100140c085465508181c4045038501c0f4050f20002e05107641d41e06400c0d082d151107005601070003103890042202e94117240c880f421a02d454102c8106000c080c402c1c000140c0d1204100c503c0d0030b80052a8101080b4640303940c000030320304000c0c413071620603001994000f0803a031000514032561154800300002c3e04602d180649444040211020380d0f008140f061144151801c0b015074000305140c00c8860b5991100d110074a172103041d48402c640c0640c00f140300c0c10700070b9980651102030407a240407540004c0c9444041580341c04083d01c129001000030440100644030b001c15000c440000a0091013680e5011001503101d4502c2e0184e070340070309640102040c04c203005000f01d9030a558044000c1c001a0f07e48074003126034284030a4038452001e01000000003050650000e08050003e840005a840c5020f180c05411070307000907140c00d10070a0a549800240c0c2c0c000c03d0381c82d40d440c0c06080100300f810b0010380b240000c04d6640e0005040800e0700021a051 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 82221746 1250 82220496 82220507
    0x13020d02060c010609091518080307031806091115040938010813150b06090604030b09012a030f1503060b0315040b0c070c03080a050c010b060f1803160303 68
    0x2c95021f01403205095440b8400303541a241008a19035814401c81c00c0c0e680092003560003140c0c0f0800a14000600303162440e0001d4148807602d50640705207032030303608440c1401014100c0a080b110100d481c1d0303810440700d03114284a03014a01c14504001d94800076211380c44480110211020740507150aa00e02c0c828008881c4400c4486082d140026407041c00a080310924200179540d16030480510748020003c010400003402142c44c8041e0050014050110252038a00c0600091480f492401a10b46010240c5908440d0340011a1a04d8848110702d007440041c0b0421080d0907100034074000c074103087d400d614480903116540800d118411203a40000901c003207a4003210480320103c0a0f1038000c100c3c2074084001c14020f07100076003620380b02130110b085851520014901a880781d009880c513940d41c0e80f00d101050f00280d4405001c1003001402c2c0c1d203074510078442c8d102214030455140d4240303000c448600e1200e008801108819030840002e50413555020070038400084040c01071102000d89a1600605 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 82222996 1250 82221746 82221761
    0x1c020d0906030605130e0a12090305240708070306050a06050c1e060c0a0c081225091802090d0c0e0a0501050d23010509030a0906050313020d02060c010609 68
    0x1480c0484082045882402440100c8000402d03011905803802e0000008200c0d04140030300f00c2c80790810480001c3d054014074020a0b02603190340350901d185090850a004406a01c0340c1c0c0181e02c80402c2252041d040c004540010061070040110b5031029030a800900868100c941d0120640341c0019081e54804000c1501d006c030641a00c856142010b07124600f181120703090443e54000c003000804940c0c0f000c0c007a02d0070540a25050000c130900b40c0383c400e0b05600040c0c0018a07030698404000b40030500507081e0075100c1f00807421145c108400341000f400b00700140035111540400712090390603c101ca0b01a1580810001d0034002514100e15109840c44c0d004c0c4260725010b6650f00001d60700f16032500c1568102d8034080c005882100c000e82e0307008a1515203520200e1042000310340344840010900c682403090302203000860b998a034900c0054400394a40c2d02031010044100b0070000e03850912801210707240c2d4103940186062031a880007e00a000da46040030340c2d503107007200001c0e800a0070b400424 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 82224246 1250 82222996 82223023
    0x60518060f010f0905041a041e050c0a062c0f090c0a02010e070f090b0d080c011a03070f0b13080f0a021c23010e01090503030a06050301060e0c0c1c02 66
    0x1034400d6a1001d00c603003503407002c480141801e108074003604480702801d802958000e1013030f05411a6271341174080c2c0e2a07040c4a030603015a900e900c01c41d040f09040c10001a1500903102030b046c0f21444c030022907640401072040440c201040d2540e59110011611624802d46c040c1c10014817402c001d240064901e82281c0180718142c00560034400403a144d00302c0464031100791080400100015400e0101c06000340c008407003003076000915903c0160120310300c030000d40360346485d000020030041c044d03080041300050780c403c445101e031300030242c1009580c00f495111821070f22003400060304d541005403441e92041080c0d1140404c1c1c00350391401a50b00e0800b05045400034821900190f6800c20101814036480039440c00821114111a1481c2d64500d81b0030f5000807000150004951151a20f8000c0e00b0758151000c01c51f4079510200030301101700c03c1405090003600c42034008003c0940f5006000e030841c040502026681c040c0003e0785012070340c092046003d94051616090810680e5850096440d03d4030480c1e030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 82225496 1250 82224246 82224269
    0x833030109050615010507030914030a080a0f02011104140d0204020d0e06090706030c0801120c0305010c12050903090303040e0c070c030308010305010f060e06061c0603030c050706020a020904060518060f01 90
    0x60038940c011b00644031119011b039180c903405801d1582d00b00305e2400d031000840e8517201c2c0c0400300e4000303000d46004000504556030303003660010002034045d0954442c2804d1507a07552091105114940040003c5990b610342211116500b000c42d00104000b4451600200d0310a0700b001003001e00920f002800da40503682c0034003116845990341804074100c98181745208000307044040104455032061140041c818021080c08402a030399076102421108119101400729000c00111102c01a2a105199000340720304003462034a1010800030751a0300c154020842000500c0001c01c20100009050750350690b84030300a800c040e0b4903801c020b030024a00348012074007582494a056030301c9100d4003600044911a888203100303600d4480820050303030030041210041d00070040035201c10418601401340114041d172036541c980c00d454103044d42015595000082994000700c0601c1c0103032541c2101b264016008840011280c0303a4203200030300c500410a00200e1441803109102002102c0b103902d904940c440f03c2030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 82226746 1250 82225496 82225531
    0x9011205010f03031229062109010c02190b07090b030709090507020307050a02100203130f050102010b0306070206010308090406181407020a020d020402030a0b090703020a020d08330301090506 84
    0xa10058600307040e0403000f018034501144205006c8926101400c1000a01a40c01c03c00c1d44a9103036544c0c00501c1c8841d00703078621241070050350170702840340c0c800344507040c40070341580513070640c00c0b201d6040d00200003001c005241001403a0203114018000103031003013241543e900c0c1040040200340480d14003402400619120110f40c0d114000401c0300c02d0540c2c0301d0080c001c1000243c00b00422111200d0040301940810420140d40703002071121100a0310201d40e0a4801e642000f00080c21101c00250480c0298001b0b028003407800c0d000100d440c1100c1d407014807185d640b0704200100300600100e03440b1920103a8500181d082500071500000c240350705082e80c54000c0e640c2c1c45422070f900c1202100c040e40101c0440010000f5080c0380d0000d50b4800780641010404440c40000b0880d4120101e5250380081c3c0d002c186000590703414012041c00ca9100d141c142041e05111486004001c011021100c0d10000a5031101040c6d5801507030070380303509004000b00640c81c07881c1400c0d5100c1d00b0494006000e010283c24 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 82227996 1250 82226746 82226777
    0x70f050706020c010e13050405030903011d071e0e060105040308030a020901110616080a060807060c0c0602010501060e131103010b070212072103090812070b07030504080a0509011205010f0303 84
    0xd110344080c5c2c0080070140b11168555004006250141c000c0d28140420400c080c0181c401340100703090b400510b1845008940814080b44c240b444a81003884220000c00d1015082d807405440b15040c3c511400b207242c01900d61f680140c540344117541c002450881c0100400c50000155805003045403402c2e02c84100801c031803860f0580380c0a007140d04a51041080801843e140e00c00c403140d5a0186072900009441503c4681451400000350711100018403443c90310307420080c407503813104001d00e0b1741d0000327000a50400d0300240c0314481588a1074040c801034850010000465002008070008006045a03696106c049401983d4841d4900b6805864940d1301f4030402600041e012040301d110003482030302c91407270020150790343c0305030f1006400700200c1c1000401c1c4076900340a10900c852000320100e6079a0a10315082001d030a0007455842498506010000031820380b0b01140c0d131070501841d2082c3c0d550303542c000584488506503c580101840d1400200740366500d440030000352130003512038400c401900768 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 82229246 1250 82227996 82228007
    0x151101150602030427020c030306010f050a0e0108041a0a0c0201060f05060a030b120d0201020d0b09070207090c090f14030c03031c020f0706050406060e0709120b060105070f050706020c01 82
    0x70418005a108001c20004c001100482c1c55024181c00c0d030060350206030b071643c00c0c01d980102d554240150000401d1021961304100007900c00c40c880c1c200300b402c180c5504800383c081164540600d041c040d0110002d404c2254400c0c5c004080d0210310070103049400c4c401d054034010050795043c0030141d0303e80035000c5182e5911a82c4a02100c03c010102d0f03103450500c42e0210090245100129000b214440b810707a500f000074882010210b0284e0b00058a5440003a2104160745000c0d501c0c82c05180c1e40741c1844403643c1d0110794402a200021400f1903003640c1e02030202e40307410300340d40002c1e0f5440e81718a000c1400140ca418000d80890110102c500209021080580724823848001a03080f1228040041c82e5402030b801074140c00c0d8035100c50078105241500c0e0350044c0d41c1c00701d80441c0c1c11551400b0600540c60b01c106140e40013005e07071424503095414a50225440c0744420000b602601c0c404000074a43e81c031800403101c0c02503002a807014081c3c8603261069440e200d43c0600800b5000307911444440354810b0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 82230496 1250 82229246 82229249
    0x6070302040b03130602040b16020a090506130b01020309041503120504050618010e040c0c06060e06031009020a0b2206081303080403031d0c01030621140715110115 72
    0x34140703861500c0710540c503801522414005c448480c2c080c40002000203491000d4808030058029000d013911403881000701c1c080c0c072500805003407031500041c4059a2038280880450305045100000e0f56041140140c0c0b541c041c0b011055400340c00d10396060007800058139480708480c460100d02110903840b05013540c450089000e1980c01a40900000d2241c25441c1c226040c01141030425022484003400480c040e03861881c51030020508046001040014a00c0341d540140010020500103003400350000b9100c0b4048a101a05141c54182c2401903544a2815100802200c2d000c0741d9503009080008031018240a41c004800c0307000781001400700d0013401d10a108801000700000f841400c2e560554038420050000c5e0201070340c0321450014001d0a0740100d400031002002080e412100c8000102520300f40d40100c1c0f802c02c507205911a040c1c00c0d1403e1a0411035000900b060751900d8140315031710b0200c207680060030030b51298100f4200f84ea00006040828140140203001c1c0f501045081d0010b2400c3d03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 82231746 1250 82230496 82230509
    0x20702150a0f080c0d02030a02040303020d0e010503070e0301060b04030f02190e07110f1f0606050405150307021906050a050601050903100c050705010e0309030c01080408030c0a12020a020d020607030204 89
    0xb1070840072145218000969004501c0d1040b0703420003410a003520120f1f003040343d04c242c1040d80000d00348107041c0c040100315084000c40c03a00c1500b034502e0030002841d0f03000107461a428010584942000381e902900000c014142381034080e603c866880c00c000b130000b80d060740141d01460441003e1202080c440f600d034016105046c0d114413491300d50020440380b885c06458888003d008802c8001c104e003070248200292610341e4006c0e078500c8a10b2000010440300a54030400038010208420003080d00c404087c07041074000031500d180c80307a5681c0002c1c0d041484d02c441242440c4240126042080081e90000380940d86001080041c0d50f100d400544451248a2400383d15070700107400552040744903040118070a410b460700e00d04011242ea219401d4400c40303d00442c55801c0442c0141c1182420048845600c40910704540b02d400c0684070340c05244005030800440c0d01c0c001401c0020303c0d006020302c3c251000552011950307a0510b050003512070341c18022140060107a00c1c0441c82c058070a00030368054859 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 82232996 1250 82231746 82231757
    0x10080f06040807020d12090302091501020703060c05040e0403081023040f0b03030a0302030a050a05070c030807050f0f0309060a0c0e01030e0f06090d0809070e0a02070f02090a020702150a 82
    0x40c1d41d1129080c0781c100030000c0303038005e548a5034500003581c0740201044c003a00301c0e22001c1e182e034114810890410001440000d84541030720514500d0b0382c1c00626541241e0f0040310014200a4a50f000c444601c5540c01071170328024090280001c00d64013480480c031402100790703c03401064440c441440071800c1c401901c1e0340c1c40c9200000080728a000d91000f00d044c070502038001402425a400300b41941c2008100c0c0000c01e90100c00c020450b511406016030181044401300321034904076002420200c0707030440140c104401c500c00a04000c3c0100200d070165902401fa42c0d0700d44071074016035807481d0700403502150180140b10124500d510640211108a102901c40b4500150b02000444c01403e1900550b0221f105101241074500c0e0240851405403401401500021001c514013405088000e0207181007a885002c04000840085e6819074000c00d51460159441007641420461001c40e440c0c080d610400820a008244201d82e0003025400e20a035045002d10022006007011806040c0d003050110301c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 82234246 1250 82232996 82233001
    0x50a05030907031e0302010e060103050d0503040302011104230904080f070201030b040c05040f1406030a052503020307090b0304080d02070f050d0c0b01080d020714040605030f0610080f06 82
    0x50168024580c480309034821200d00c543d403a21604119810703160000714040001c52400d0600d0350a000d840250070340300004242c1e81d499a83c40c66910085080d682c0f04222003c004142054030030740002da80303100480101901c1d10703101ca0f03102e03079040c00701c03039040b6552500500115517a08001d21018802e64011907140d09080607150301c9001c69101000c200d04166442c0c0000400d640c5611a080303044071a541c2c1c01d9151810700310a0302c00315620b50000c005010071380480b81070703030b954000417207901800040000c40c40d6200e403000b40309040055801440390004103521648080c0e4541d01840c0f16403c560b49078041a82c2c0d07454103d09a10007514050001c2000b04411610300025800030140c1d14440e02c0318281001403911030900708a083c84889002070720151080c4244100c0001c440d0150600f00041c190500d14564040d54070300c00b0b441581000e44405800065540d6a94400300c0180406002d44009500021100351500c030200d44071041c80f41030301c2e0701007606200090700154843c01c0d5001841944c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 82235496 1250 82234246 82234267
    0xb12150a06110703080f090a080307080a030b0d0812160c0f0605070e0607050102070c0509090a0615180e060709050108070822060c0e040510120c090606021e0303060105 74
    0x7411400c146a41c2c500c01c076080040000c035000001c08101040329250341e01c0c2d581400c20004d86407030903800f41c101c80d40184541d00c0401d8210382201e84905841c100040c0d860049004514243d010140c0030b004484003180a04498040584151264807042111405040d901800303507555540c503003002d40050703041ca4100300021107a40c89135030401e05904180c15141081030000341e0343d6005102c102c40e5079401107010410840704509442c00742500320740c030210b01c0c07600c0d003e4580d441c0706d20f10303029011545540c00c5110ba01845c0702d041c0081e000c403015400c07a9070181040040506010f0a503030b0303968030a5800180f0b01500c40d28101080e03803c1655489100d4031516000ca902480107084141c0010101700c21101e1aa645400e194001c1e200b40000b0a050548910142c00442110341403030041d41020100048030340843e0385601034030132601203543c020510b41030080125115070440002546440740108a6540000f52121280c1301040e254001c07208000101d038030390201382c480c540801e00911001014 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 82236746 1250 82235496 82235507
    0x70206010b070b0916060c050105150622050303030a0608060610050a1805060d0e010c0804020f01030f0b0603090a0507240c0302011503080d230a0b0109030c0b12150a06 74
    0xc4042d0358104c0300d1282d5842c451840140491b404440070554001440e820000b082c011154481c011980c68030040d118500031591318882d00c82e1146036200120422010300140c00c2644000d0080030301225128540380240000030b0096024110142c4503600c0002c009150081c90742000c00010741ea000d0408840c60000e5404001c11240c2d24607400e900c03100440c154a850024040d08003030300c0008075000c915880c0c10741c2141c45074501c4500b007000c1c080401002d40c07291062500392a0081c40c00094070080c8140d008010141c100c98640d02a00000500945074800034a40510600450035238102558071060743c40440140700b4645d259101d8440c810f040140a449480c90307071802400007141081c0594504190360040740c10440b004040810040302c44178941c0f040c90700f400c04141420b03000740642d0034140b1503003a00500351031b29075481e040001c480d40d00ca13036000c0700110f90114080f2144c0d42c480080d00c01c51b421800c040015602903000213040c00b40030302504d0b4403a51b009010b0040c1141002c0b02200d8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 82237996 1250 82236746 82236751
    0x3050c0d020a1e031e05120d0204090e06010303020c09090a060b0a0308120f060604060c06020706090b0903071205071e26030a0c020708060a0509070506041409070206010b070b 77
    0x28024180240065014000c2040760f1641d650310100c0c84407941149440302840301d4a03800c541e401018050048009a00040c1c500d00280d01380629076252000091403c01912454020340410750528041b01c101110004039103050740d22940a860580003070a09002d0401c81c00c1b204040203034801c00f40c000101c0c090394000500f03601c0103400400e1081c0c89440304582030344036010502c0048021010020002980c400a54100c41c1c1140c44030315041c40c0c0300700103041710701024000d003103580d0001e601000c0182551202015a41c800548100352400090403a180d40202c04182c8844d0320b5880f0b002e40c1540f08800321a000b542c80018014808001e0b240c0014842da0b68038202d58851043c00c8640300c01c000322110840601329245c40555a10382401c21006454150a4580c150743c41003009010300350000c10f2070360f4030038642070000669a50b80020b19180013610341c8450b0b04040c0006000c01c000880000140b800182134400d02d40c00e0f2111301080365109402d200e0103041003070500ca1140060031000450f0b8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 82239246 1250 82237996 82237999
    0xa080414060d0e061803040f3b01060e0105070206070b060d141e010501080606010f02101103060f1504120201050415020705030609010506010c12110d0e1903050c0d02 73
    0x10b081c800c269000701d0890b4001e42100c01c10380d20810401407850410f1315030a1484004402a5040502d0241c0072410000580643c128140b41816821010442090881800300482070f489410403c0424492406d0600303024000c0003801140904d8000d500403001c44a80c19400380c1002c2c43c180598071404100c510240110350700000205019002c1080c81807081d4007603c90002600000c10390a2009140c00202c15400d8405c0c1d0400700100710100b03021958951141c02030802d0b503034507003210340308038289554080386041280c5000f1504032002e08000145106480030381d001043c3c084144108103000d40440c0ca040b0381044104028403100c00c6000c4000f0060788103040c218181901c6100403440e0a0380300d043c8a0040e03108100400c85454200300554014101e04000c114078180000000c00b40e11880720040d0203002c01c1940101c06610a0990365011006d18040d110f102884820042083c14003520083c45040c0f0001d000b80c2002e134002c071060031203520000a100c0d082c0300e101030040b0180410001c0c0d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 82240496 1250 82239246 82239259
    0x141e0702011211131d13140a12091211130f050112020102010513120804021809010b040b03070f170102120a05071214040212030c012c0a080414 63
    0x4000000c0034018001d040f041c105050303448400c40043d226813001c85900448060f6009000038081140198105800410040d40c40d901424141000901c540f54119a0300c0f6a02c1011218002d214007181c142c1c8000b1080e030740d11400d0603510a00d107041d41401c030402900d106d02d20110344581d40b42070920b4540080300d5540114100ea40c034481d800c201c0d282640030070810100f081d0034008540c0c0c20302c980c42c3c2c001c4018130f036000c4c241d6094455854124009140c0814010f2000110f01956100541c44400340f01d0038031132a607180380035401140600010301095010fa800d1110f010300b43c3c9030129450f001d0790242002220003e24104584540510b040d11041c019542088406c0740c68100810b10751040d0b140801c042558100103e0061501c00c84000c0000d2051400e01003005000350f600080c1c0e0442e4048411000072034042200c0c50951190f24500308840d881c01c0c000b0a05d0304a0601ca0704062581e846815081c0c000d4001215111902100d00030704680c010841440340c0071500340e600040b500040c149 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 82241746 1250 82240496 82240517
    0x30c0a0e0a05100518090f01140f0907020c1005031501140c031306090504061406090f0a080c040f050f160e0913050606031c0c0f08070303050403141e070201 69
    0x855895014543d8000010301d000640100b01a1020084404460196440301161401d0080c4a0300700e0010302034174990103081200200d02e40d99800450700790f80d4004080b0025414141806075640585440f441d01815102e1100d403105800b450549208030b122080c044000100c01c0d00460304100c1c00c43c0c90a04590090103201390100040010f454a14110264004042c1c04c2c80006801503003075a028510540c10807100780540d0000010040c5282401c0e1010b80c0c8400b586800906912005d807a626001069010001603500000070384184ca9801514104140c810740c4003d1010382d0070840e850b01101d0742c40e80200d500c40c881c041d800c0b20308001c6807411000c4440d8031800103000030401d07035042e488010488103038000c1c01028850140c21480481c001c050300d0307294521081d14500441e0410301840480808002800344140b03e0000e0380e644242016030740c050718600507006200c1581d05070000303441c04c0800f502ca9440c840466110701c88000c070a59101801c0046c20150743d20a071802c034100000e5440 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 82242996 1250 82241746 82241749
    0x7080a05070509010f03110105030402120d020d0f0903050a1e0c06020115081902010503100b0309012703021218041802100309020a090507030b06070c1a030c0a0e0a05 73
    0x5280400d2181026107400c5181074100a8102c0068001601e10040720104000086019046035101c41003800c010ba103030782e95400040d058485403000741120780145101e0b44007059010070000c07850b60070740e283c03805000e10035041116041c260b800000d00b26404000c0c140040754081c0d41483d000c401c68007000c0d0119030303203035502c1764150256803081c2e000d41c0d114024501400108031007000980306850003044002c14030070f00308500400c2440081d051010000c0490f0b44001d042035220080d01552440664a04207030140c940240940d11016408000350344060600e41e01a5029181898250340123000c40003101551030203507804004e62181d500c8009054450720f40b1140987c0800d24003140e1000c0b090000d81c010310028540c5429000d0405150030000c0d00140e82e40d40c800740540d01d41210004a42c2d43e9808158000c6ca0340490456210380d0108080e420444512243c2c0c0546003d07111a200140060380300840c1400107940300a1441414400000344501c00c1c80703200f014000080c01070228658800 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 82244246 1250 82242996 82243003
    0x71809080705010c08010605071208060303090d08040e0c040b040e1314061801050601050a030207080f0f030405070e011d0915012909010f11100f020a0806090709170708 74
    0x604440c20f9440f103490308602c54118941600400043c00c10500c3d0042c41c0d9507092220781c4c860040c105001c101804502d09860410988114500113002245034404508100740e45410078410600c03d03026040016070005038080c00c0d50704541003812603c2c2000d007842e13181d01d8a010300034880c164018804040d06d0204e01228180f0341e00d84105805014181052108000720074020302002c40240e0401c0c050100e40c2c2da001c012142203180c146001a124012440c1c5020300d445800b8010340e103040045003410705100c009008501891103101200d228994400100320041002d20866081800c015150055644031090a030f512140100940c3d5000c001203040c0300300d0302e00a8001c8168042c1d2401c1141844140ca0100d60f07101b008a01042c2c140b913403400008244038003c09004081100603980c0c1802c0312010441e4000882600f602480804a01030018000790002c09c845400038400c03902251450408515a0303004054544e40c0300c0081d803d02500f0700600780350740c00b4221144a59030002404000c1030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 82245496 1250 82244246 82244257
    0x1006090c080f1b0d0509010c0306080601050d02030a050d0503060a06020a020901121104060905190501080c06071707110f060a0c06021b150105010315060507030f09090212010807120507180908 84
    0x120740005c1d03e400c0245841e42191541d000708800e06245c00c2c2c05000032400001d9040c11118116920b039100c450b6803012031304101c0010390041c02e911501e0640c4031201d0700314014600c0744500382c0d010704005035a107804903614034180d41c029401180f61001840824421a02e4180c070074010060149044501c4000c075044038003681c40b000401c1d0340d90007800b40443c12007507069542c0084000034043c070750400610360b8480c40d20a9a60b40f155900040d40e40401c00b899020940d580d500340603d40c0c03503c0341820421901440240424410f40ea41c50500c2c2080c034011066a0750700f2065981e20080885550b2041c3c02036000120859034600f0403807158000002c01c0103400c0c4005103544c2c82d0f913006d516090015060b141c5054000e2125007040a00f0f0000542c000c042c0c0d000a9054a07004802921090083c0c0f1003440942299188074000035007003100c402d1000719503048402e0b250448010075a0382c4c0024440c03144080004040b5002241d0800c05142c440c0c2089007601280d120002c0c0d501c5203035450010f1540417 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 82246746 1250 82245496 82245517
    0x30f0b0613050a14011205150a08030a033b0f2a030105090d050d090209160810050607141e07030c24030c090503010606021006090c080f1b 61
    0x5014091282c3d04016425030b00401c48080c14410341401d5600290035072100703c44405825580e1b90014002c1d0600384c1005c405420060803000d195030311003403c141c03258401070218020a0030f0074407039040e1034040e541510408850701d0011038502d2008940884a22001d19401c8403842100100b94a5140c184548500f005d03030307202c580d5148d40c00c0d40b4241850b0909100c03454800e0b49000d080091840010035924081c088510b045541c80c041c07240c000c0018070f507104000c0c0d000f05c0c0c0001003000400d00d5280341c0c9281c0c000354450308050ba940010b001100e4541d070003500d8000d40188001170001c1e02c41c4a0040848080b0710a0782c040d076085500d00590401c000c84a10007607800882c007002840f61140d10760300a010a85044200696a034096101010014521a04140c0c0e00c03035840d41c000303200720480c10150000030001d008150b45c0340c0d0000c0d0350b28148851014140c0c5461800903032070490b441041d25400051316680507658506ca00c00d41c0351200203010b081c0310000c24038400b1648001000034074900d0318 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 82247996 1250 82246746 82246777
    0x40e0f0d02010b0307030b0f0a0603060c030e06100302150d06080d0302040f06080c0304140a02101805011716020a050a0f0b0a05100302060c030c100e06071806030f0b06 74
    0x390a1002400e440404440c54001d0b00040002d0001c5004201800d6000c000c08071040b195848207a01d48006010782c0d031000e00307294a01182141201da15412050054141c203040351070079101c081e009914003005100c025070200400301d1161a2011500140a8808081800003901e0b80c0d035031602810041c0040c203100000354001014050b01610108850240c542d5103400e00d2140307880c808903101884003800242c0310100043c5022107407038040241c0c10f10310b030b405001250321201450b00509441c980414040c0c084e41a14000700b06948240c90611100c4090a004005502c815203210203480d080145401140203650060010030000c00c02003200c01d100c2d055241940c80c240c00c019403000f03c05040c02c5440360074001400040501c45141c2d5068035012075450f60341d079042c00d440c01c1c594403400b040d1001d00d008441d590202c1c40340e10f80c0101c00801e1001d0130b541c910b40d10081c0071142c0d00e2500c07810004a2a12210a1080da440b17640400180d601d890000200100d5440020b04107401800030006d8055 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 82249246 1250 82247996 82248013
    0x4051801150306060f0b0d02090406030501020d150b0a02060f0702160303050304030206060405092e0f090203070b03040b0115090515090307060e0102210d020304050607080c1e09040e0f 81
    0x182441404024803010100117207080c03d1400c044035610848811003803150300460807001c6d03030b030b0380d0340c0300e88001c5600100031035540d1640d020002c0900710001005284010b00003000401d40501004c035404069194090102c3d40c2d21003034124803005024205030114850394940c0350503d10305002e1000654082d8480d00d490346414980285402d40040040340202c1c2040244580d40600241e003c5c1007100e80941c0035800c5d520303420040503181c80c000f82c01c040310f41000701901c0c9801640d4403a5030f025001740c003076404241d00c840c100c01d003510042d1001018a20542c0c0100b003d03907040c0c0d1582c212030f24a4580050180d0345c9500099000c058400703000118280010148418581048103038000d0845003000c07000d280000c00080c2d12074a140405d1103d205000200b8518901007008507422a0303903c48045440741002e0500c40d40c1d4000840350f22000c5403801e000715101d40e80b06401e4903158a50f4043d2204c56040491205580d5002130003200c0c0c100741c40d5803183c58180c80502c01c4820f140c590400078005031 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 82250496 1250 82249246 82249253
    0x616050607090f0608092802090606030606120a1107060b18010b04060e0105040306060b07050607140703110a020405040620130918050a03090311040c020705040518011503 75
    0x81028000344140010400b04010449042c0d5024088070003a00b040c0b1441d54981c0d1201e802d1060030849500e0481884c5804100040d1300c401040000d4000d48262900e0b0b0f8032001800070f644000c0c1d9030141e00150a1050149403822111300d80c1c2c3c000b01c407600100b00c81000b54080f5046412410046910b40d8a94a801c0018203101d1415102c1060300b80e8800d07000d501d86103011040348100c0c0030b04c008110340c40031400607a03405076049070011940642c0410070150b45034180c001c0c82d00700d40003c07100c60058202040300e85101e407032400050071f503003100d041c0703031105943d0103542c3c1c0040d20184a003580a00c00c80c0c800966664454030340314034010400400d204a0300702c10052b80011011000b06107403000c1c0502400101409031a4060f203094520000d02820540340e01807143c0c5900000800714802c20806101305540038800c1d90450344035040e180b004032001010041541d100a01c024016800031004000b140f80c56046a41c01014007012900064807000e03807c0e00b5a06840f114040c21041c0f00f00c2023040 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 82251746 1250 82250496 82250503
    0x60a2f09100c0b0a0e0a020a0e0702060702030c0c01030f090b0907030302070503011413050f060103030e010806010906081f080709090506060f1807092103030b010305060f01031109061605 82
    0x140070070745000051004269211992441d001c4c14420880f03642c0c040900742c10200b0450050719070340050240401c5581c60ba0000650841101c8240041c05030402142c8580c1c0008240c80d80d000b80d080141808180d1000114010319410701c034860550740350421034011402c2c150100d03010f544010094a442829800e019103007a01580c4054060383c03405400e000940c0c1010720850300482c03900b0035807401c00d40d24240f42d494446207a082c0c2002d400740e20000010550809000b00c040102030b00c4881d086c0d5035100054800b10228400d23003000c5104000010229147c00c08611041c95004602a480d66140c6020038941000c50304100192907440c1d070700009021781000301c0f560000e0300302c498030560959013000c903108140d00003014020620400205080d140034110540c00343c86d203100117442c7c00e018413524086588042006801185c13034104d81520651007030146034030904000e8400c40d0544107c01c0110300400e60080c04002d1428103010350605a5184001800e0b40c200c40c05218644488a0512505 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 82252996 1250 82251746 82251769
    0x1803030509010f0f0c02040504020f331c020306120709020903070f0b070f030e03030304030c120212040506070618050705010908070303020d11010207020a0305030a1808060a2f09 78
    0x10f001c04100d00000842e80403410701c14160b4141c40206051f10b440c03001c2f523002c4220006450380300c219205010701034624624420040c01000e2961481400c4c00c044841d4030340719030740e0603d610030840340418884031802d800464000b000076000847c8010b95100b101d040c141d06400040d843d079000541c058062a0404c03016002c2d1200329500400140741200c0301c82a41b0030300c400240600c090070365100905000e40c1e02034422110286c00d50f5600d20f420301e03008000381e003c2c4404540d400f44601c1d82c03603040d0384001850240d100c40445498030301424041040300c59005060215106a01e40044182c0c410018005c1000a440b0710000d16510b070400002620720800798110a829a110b050100046a8002070480d02803c05007858442540c1d0120b8007800ba1240c80e80117900440e49150000401c68008000c000f190342c0340d650715100c0500008441c00e02d80c150300c500c42103a88241c000c2900d00c8000d034003c503846000115031585c0303a03060488801d2811551030a080343c07548042114602c03400c1c281d101c0c04 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 82254246 1250 82252996 82253027
    0x3051006092402070b0409200a09050405090c0a030804080f19081602120606030c030304080c060a230c010b0111030304030e04020d0e100605010905090f07180303050901 74
    0x70203820311401d038070302c00c12448180d114280c140c40e120403694024041c16000e8001600840c0ea166190240f0300c0140c103081d403001d0344e0300391381d0b10143d188021a0010b80b010f4800c42d95428404030b2a1000708030180401900c0400c07640a501240e4525035108001940250f00c242c44036a100c51402c5440390609480086c0741c280d6030405d55065107900d20010b4042d540582c030000a54691440603c040100204210025003164001c02448503004c00080d40c503128030070480865030084940d2003403680701c2c0543d02c80c01c4080e5120354003020062800401401085945183c6090388514084d16111810642c0401880e0550000340e8405642c000303000e5244076100a0a20761003585c030a8090641c0c03840001c01c05410400a0310030003d09a5594046604200030540300b41311804503401426207446404981d51002c910b012400241e41d4003a1f80d2100032240003c10016056541c0070910082010040420040112000c200d90481c05440c00c180080c5000e40c0d80c498940102c4000034042c2e24a282515 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 82255496 1250 82254246 82254257
    0x18090601050f03150a06050402040305010f27030e0303070b1f0806071e0c080a02010605010e0301151205210702190b0d09051501030b04021014030c03060f09010603051006 75
    0x84946000030100d01c481d4604c070703494001c2d40d0380d454410010107041e00034a6000d400000c0000c00c1c0301c3d05401c840f00221507504100001c95091201324125510f06219240d2007a07404500004603010302d904014505002d01900e15040d080e1703448402004045a141d40400320000d5006294880520498083c0080354002e00d11410400c60161016031100221500f811007280d41c02c40081c4201105070507181e2040c0441d8680000d2000a40a4545406228000361902c030a0160a1030140910800329440302c503010515801c1144c161145000203000f540e041c0f01d100f0300d881201e41e208400794940040d2180c015100c1c4054030403c40703d9045034026a44001588001344600801c0400315400071080300000600b84650345041d41c20104040a4016440d017041d00000c02e000807101c03490b10a42c4211101400d807044824255103000e02e01d20f4003891841c00303100080050700190000c54012030700400e503039812b118180010b10a2a0240c00c400b0000e0380f6441402003000c0c19818840c090402401e00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 82256746 1250 82255496 82255519
    0xb0103170705100c050c0609010b01111b010311190c021c021818010f0204091401030804140a08100f0b013b09040807050d171609051809060105 63
    0x200c035600d095030305030216644c0d40d92072129038941c0980120740d40e480005081d240940b8203151814000d00380c580059004c10030f0f20303010b100031100c003242810821010660020201804200447c0280b041000340300540e00100030008105200d005a41c4d2030745c003030360ba0b264148c01003441030011021064441900d45c0c0e181d80f80c40001651684240345045812000e0020983d48550810007192040c8410b01003652904100002c2e034851500207005070f83c070300142172080c0070380c020941a0142d42444040e108000500c814860b406c4450001001070781c0082055101c01d45540017a420010007445401c4801e81d110381c1c3c000d106d0018000d034403000400b400c08640b00304481c1070407500600b44140202012036a0111000c6132064030f5011802004003802c01140c1c0c1c5010f00d0182101d0703005841c103640c14840c54101c000b80500c141c01089155010003030806003915004a201c12800d10030040c2d00501c5000300700814242c0301c1c00505940c0c1c0700c800348900050308006004504121040e0131150048035076060 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 82257996 1250 82256746 82256753
    0x807050105190b06190513030b0405061006230d181b05030a0b0402130c0809060115090b1b16090b060c03071e0c060f0206070809070501030902040609090b01031707 72
    0xd40b4411302d1499801c417000c00b4508001c4500780314140381300781c2d440018107000c4103112941949910452241c0c0c2161001d4540e0300310481440b140c3c0c8161030016104919450220b41043c50140110051328221400c02c0724074501c00d010750300d00012220512440c0c2003032000744210100441c0320361480c156402d485a007031402081d102c6070701d0705010300060f1145020804549800485480c5681d02d100100100503030b0754801004940c0984455080303220f02c03130020810790070000c80100e9440c0503489094140385800d003443d100d178109a600c50101c0c1c400d2031142448000a000b09142065a0b0301507078041e80c14007003c0003c07039650000d020300a81050140c3c842807080002100c0c015900003a40500400000581440f00501d80344010007440000d1000205590080400005000541c0079038800e903603980c0c41200c0207078080f07071600c440740c0c400c0e00204074030750107036020030318450000d0300205115840b180d128090310750040085400b07a5241c07004000b4401031009008042010170780c840e182402648 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 82259246 1250 82257996 82258009
    0x4060b190302010504051005090d08090114160b040609051b1905060a03090516090c030f0504120f020c0616050c01050f03010b030709030b04060f0506030c060715090807050105190b 79
    0x44902845102003144081070044041c1d500c010320007000800c1ca454545010b43c00f03a00150336040c0402c0300915490300001c41750050300c20b000444030f000c8096003610f03128001d544c80301420650740f440c0c0da1511751300440c1d07040c0004075100300c1e003104080c0141f6000041c04600e0007100507410714038040b0801400380f030350ba1200302d580c0c1100c1ea290101d10f0f0341d0382c1d040007030034481c802c000b901507030381ca41000161135105500642445c0380241c0301000800300700f80e03000046d51070844000744182850040c071145a4000c055884000c4443d1049510140100c03001c1400d076444400135462031041c800c03059003080700401141064050a207022410005000710750075240c041801001c070300c4070000c0b00040d050392152083e0310080d50010780304c0549082505044004001c80094107281e44d040c030300025220304000407509220000508403030b01d030281644071000008001407150324041c0c0c5948080c0c01140400d0060000b0b60301038000000c49040c800f428121801c421134a060482d81090500310180ea2001d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 82260496 1250 82259246 82259249
    0x201080a060b030613060b0a020d030b0d0201121d15011502010b0603010303050901170f04020307060f050a03021b0f030d0c020105070c14070302060309010e0601050303070f021e0904060b190302010504 88
    0x5403040703d45562001711070320260900e6041f50b1403c284c04100710000550001c0d0401d121000c1d51820050800d201007400048407049070040c1c040b40804c06010000ca01c254805a8034410302501805c0501140390814105081c0d840403003c0e10b080c10340140069903080c1c0e08034200e0350640c0020054943c46902081c1070703000512001c2e0600502054002c020703401101050702101a0458070b4480b031030608440702583c9402d40d420790183c4581d1700081202170041d199024049501d49415047c411501c1040340654806980c0d0510702404894101c902d080800c605881503180d036001e9a1941000f507003440880c1d10540521046a05003000c0c000c0464000c9440d9403001e8106aa100300c41050141e020301c0c114180e40700941141d000000c004400c1c0b419844481e9040104041d00d40d1345e680c520406580e401a030350007410110110340c1d0b035001880c0110804405400144407170082d03000007000030b00040c900300d07002c2c2c42c0395481c2c40e01040c951a061070102c10620800101619003411a000280280142d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 82261746 1250 82260496 82260499
    0x904030f050f0301152003031513110a080a0612021002031b0c032e020306120a030215060306190f06210302060609010b070f02210601030201080a060b0306 68
    0x5901204904078030820884501c200d11010841c0c0e29650307a00d40c1caa10340303d071030600e500050902510a186500c03090010007403400c0c0500860650b143d642d80500002c0380f00e0001b550041001c410604c544410f8000c00b40107a503506c1585d42c0326012105c000d8101503006240c000c145161000c18400056140200c07204e040e01030b2010400710580c480182c2c91071082c000c803a900550310384240b400c24400040e00280341300c411b43c2503a15030844101450361100c61450000007030005480d07200c180007800d40c055580210010002d140d50b001c2d01e42c1040c1824041c00e000e40c0180c00004a258107030200c004a69003201043d0001c0442e4601100c0c0000c00014046040303d2064803482c0c00070b030f9001550494000307010402120f00042c0c10000c030f51000d4a11422085025004510005007a85040710f9001d0403a0700c171940c071600c0c100b201c2d5200904000c9802e01240d101c296602d21300c40301c1055003000140307040c2120040c607240d415800090604c28004201c0400035007052414002e8800e002d050780d410000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 82262996 1250 82261746 82261757
    0x6050409020307050702090f0103021003020c1f091205121b070303200c01020d0b030706050f0c1f0e010b0609031018020904030801091113050607021201020c0d0e030c090403 76
    0x10358410440c2c80e8418040040c0d401f0030000240401c15401f42100c9040768421a400507402c1c00c1d2090540aa001d03e1907599082d0700500f8242c80e42007680f9107a400c1c10310404100080110705581c07038420035400c41c1e09603000214081003030b034071024682500c143c0141901507002c01e6090303030b000069194410400024200b584661000c21030714000c001d400340c00030303e0061540d01c4501500c2a18001e400c00c1c5607240301d06082234218101800c005c201007058810554034035140108408001c0c0e015401040100703018030811008101818401c4a140d1140d0255080030070324000300444035080d00c03426a0554403031079040110030307801d99000420070109042c1ba03d0200340703440c2155007425010042c003400303500211010204030425500c402d0f25416900200010804041e41101d8081d0a018026820401313210783c4806112602c0c1030341c040c0140c07a10050840f446244020142c0e426a0800a01c0c04c1003a40012800c04105410440f1403d0b0648181c001780201c112038400565000e102500c00b07024000c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 82264246 1250 82262996 82263001
    0x60e21090a03020a141c0203030f180a0308120a0b1e030304030b0702060906090a0c0e250302091005160305090d060912090803030f0105130e0601090b0a050901060504090203 76
    0x1150300c4940381c01142c0040c03e903080c0b6070f66072040300c07490035001c0713440e03071242014801c0382040c0c215091900792100d80140085040882941045680b80e000b483c0c102400088898404125a80c00c0a50409944500e0300261111202080c0b102d9050015113148102c40c1001e00d404465104d42001e450510700010841c03000280070f5000ca4214411600040d01680210f07003000501500020310b1070140400c04120390741c950300c0d5042c4e6a280c581d03c4600800044100c18100709007144030741d000d904113413081200440c002007510b03e008081c0320f051006010a4012910b01c0d404e20700058202c1c0c006180d0706100d407503c00700c00e410700480310311030000905002000ca0048060344940e40381c500c486600200401c00380c3d40310300b01050b601c0010303400800000ca5003070000c5100100403050360700840c0615940b8020fa4241400c000c00c140844007600000380c1c2c0c4140100d5255810410390b402080c80d5500081c1580c41441031105035030700398000070f0260f2410801000205d40c80400c88084502c103800050310303034 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 82265496 1250 82264246 82264249
    0x1090608090c0418060906021801112d061e0105010507050705091b040e010e0a0c020a030e03030c0106030309090b01020c03070902161a0a0b090112032f0604060e2109 73
    0xc2003801c0c00341c4401d00e0806e0300300800c03100350300402e400240301c2c10f404a082002d0004594004640001c1296600102c1c141619101083d100e401d4003d81e00200f00c1326403088921007846c004080325500c1000d0040112040c0c00085c0c81c0029014050a190440c03900a0f603403140b07955140e5078480c03180240404400210805881172043c2c0c1c13580c42001140e595a41c0e604114100041f00307004d9268501445404909021300710300c60300421400d940c02400080d20591403e90fa81072000b0000d0b90580001c10070518003200030f10032100594425210b01006900717096038001200e0004d17000c941558450600c10740715a800258140c100e903c55400076035681011a802d6a41403d00340000b080e01841004038601c82c4040012a441290b1000e030401200088108000300800e0030b200e13840a44132452400c5010a20550320240700b5110289186c403494018000e95500b404c000320041501d0300100180020030843c1d005144440e41c515005104e961411003040001c0784100300c0340100c0380c0c0c3c0000d01500e80d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 82266746 1250 82265496 82265531
    0x2f04030f060605040203090d02060108010507081303091a0c0708030a05030c0f04090207080910030515010323011214030c03040b0912010c02010f2d0c02100c0e01090608090c04 77
    0x24140184c425500d0341000c101650752000d400c400c0f000540070300800420302080510600348034440642c1c51030040d454020300d21007010711030a8140d04000c04100302107540d1005036100c00001c010803184540d80c6582c94002030030300c6420b030014451900100f10380c25034a9802030640e90804499107109a0718003114a40300c0d407610a503481101041c0c0045102410b1140c16405019440801c0d54041044440031030210101c07101260400040c8031007215210b40d9510030ba222010040b1000c20702441960400c0700341c0d030a0b4509a0080d01c007428001008410821041800b00820300c10301d0042d4100705008003007a803a0b000d00d00600904240c08038415030940e441c142c1c60400712015000821030310f40e400e803000340a00711010048010720308080700103170501c03503131124540c03500b580603c240c4545040c00340c0b040140c4400c08501e030852042c0c9041d40c0601011348600c010000082c0c40d1200c80061400c000b4194480c540c0c0030400344000d00c0c0030040d0213080801c580d0701c40c2e43c1c2200c1c00201c100344036030303600903 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 82267996 1250 82266746 82266749
    0x13060b0d0f050a0b011512020f04050d080c0114040305030105010e06090d120e0a0605070b0c120702010603030206130b0601141308010203040606120c030b04050a020909012f04030f0606 81
    0x1103407500c040341400780312012407100030301c3d4001c0c05207003000e80c0c03a480581c0e02820031700c0148002030b0900c000b130b00e003500d0140e01401e03040001e0301c0f40c5490302e41e40c0c0c0c00040c3c00f42c541580035204038000249548080c6000d10034515120464103c01046d032503d610094124041441403d0500c40c4241d90104160380d080200c5402c568010318100a2960b02e0512034400410b00501c00b010500f90110800285042c4020748220b4050340c0d2250f00d40803095643c100c5100010b01841c2b50b160341445240a2003000b0340c00180705140d160300005041c5d1460400900e030600c00740401c5181001004280c02282803000d600b5807041d42802c06c880030030528564a00c981c4602d05440140016040b00881d00e8007064005501807400740c081402800d45a0382c0b02001520084401405258548001c100240700c8a044e40e92003806030701542c0c040d682c01e4010541c1100c041b2001e0301e03241d640c5d0358207400c12041c0c4d01d8061030462125002026010070111030701500c0c031650001a1051520704030030402c21a20380c000c0740 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 82269246 1250 82267996 82268003
    0x40501030218070306230306060303091509210d03051f03030509010e090a1a03010c0215070203040e0408030402010809120a0c020f04060e010501110303090c040f0902091512030313060b0d 82
    0x25072150001c0c482001c00c91b90180e41500c01d001e214003240c01440c0010607aa1340000c002d00c5440310301c00001440000b40d00c07249045402c44085090101100b00342104811880c0701600584217a86a001e001801c48100900ca03440020309490201d500d0000740c00090b00b070b81e034107050140d911010b180050341c0c440100c030b5401d42c0c052003000c100300302c8820940240300604403965810b038111401c08200b6099803e60100200140d005501780200c00608000158200d140c0e80103803803805850f0361003044000802c4a00781c441840c0002400f0465910480281e4442c0d480b1000d41110030311504d0001c890320402081c58104040c00c020502555281e1940c1c00d6941030083c0f0403c4040d40e507600c11f007034000c000d1290601041d4410080c9120500c00b1049034418121a000390090a0b80f05003040004d0802940d280d040316a920b14650040c1c803040d0981d03005643e80303800000006065410071100c1314a0003190704080c3c2040c005c0c0b03c003a103130b104007504480340e11000225803804203070040758801240401c00b4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 82270496 1250 82269246 82269269
    0x507090c05120901020702120d12090525090203040605100602010207050705060307030b0406030c0911031005191d220305070f020609030316021003050105010f0f0915120b040501030218070306 84
    0x1556550800101240010030300d44072400812b00c1c0c0340f03501007110980c882c080c10540054400300c980992048004071040352852144882c0c58466103000126001280c0845807290766900f44140b2505804802c4000c00e800d20003940391852941d1141e449811600c5882e01030f0b940071000c5804a0f00030740114154010240040106695a0601c8182d19041d07200e000d01c0c0500e000e41c00c40001d1513842c02c0743e105031411092a41d005182400384100740340303058010b1a9580b011040415403044038111a20b502c290703400f11464504121141c0300c1c0d24110503003008003117403d02045c80e00194004098813202a084812603003d0383c16800070072124801e02c01c41c194113001c001b9051404248003003603a00303002c1c000da441480d88801c801d810340c100c5e0401e002c0c079800724090341c070301464043c420400d036100c2503101c0c54803405d4a40d440ea2044520b450000b4004003140100c403c10760f4080880c07180012500003242e0030b01440d403550300841c00c080c42c8149040740d2988034200042d40f29010b900560001c10202c41007 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 82271746 1250 82270496 82270519
    0x408150601111906050a02040302090115030b0a15020d050a0e09100306061d060301020307120f1d0703140706140a021603030302030105030606010e03062202090705070507090c05120901020702 84
    0x43c400c8020b8400d0007190075a2a00d800f1450080750361096400f600e9004d040a040ca908000036805682e5440c04001c04254403405445a40c0d1280c0c240080200701c00c0c48100c022020450f40a81043c801030281010814240040503416a020440030450b075015a90390890303803200b80b00e01d245c8582607000030f40b20a0502c00006180d01d03503403080c429840c51068428140d61207442c205400d0b8030055503014005819900000701c8048158042220f1844e4400002005004810b0790011400d29000282050700122820024811880c000500445610001e44034560415801401901d0004403a804806000c2a0b0000d44c6000b040a441418580c1e000340c52070340c0d034a150007000307075100f40185406070183c20040780482d40158100c64450a00a01408440e9516004800460151030b1030901440c03040c10008003503141d1003049409000296100381da20006401c2c12440c2c44050b602c4021a00d1a0030b40043e101940002075520102c00d03030194031440e403200542d09000e401401c0d0065030000c16542e5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 82272996 1250 82271746 82271773
    0x8060f0d0f081b06090703030801030303051305060c040602010f05100312210b0a08011e0f022505010507022e0615030605030607050403150c0201060b070605010317040815060111 78
    0x34889000c8040f10f0803920140d4600c000d141d200e90a038030004021070b07003c02c01400068000e4200c10fa0003a00d03001e42d200389521646600703107407581c26200c61001d0300b00001c003441038035420700800b008a20100000c0c003042c140200810427400041c4006450303000503082d030020440c415100812004040400c00401c83c460400400040031440e01c501e22900080c0300006440038103015040c81e403511841400602da5141e00c0c40000ba03e0300c43c0d0084036040d0700300002c08280300141d06d031341a6480d40010b2401d0b0344846141031403c40700c01409010544d44105000c6504110b00c1c0203184010040c500c3c84400c13040b210764500041e10382a04003800c1c5000a11000c0c040d0b0b80c0c5a1b00c0142102c4080b4100c6a4940f50307038000751298420750101402c0d000942400c9041950240c001c0c00d0312000b40e100014506540c2c0072806419007010404860480d02d0304010000e03c500140703c90261081c0042d01803503e0b03d4025140c0d0b6541820311404059920300b40010101d0703010301c95882ea00c800c007006030f8920460b07605 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 82274246 1250 82272996 82273027
    0x16020f0303250c11120c0301060e0118020301030b070509040b04060b19080105060f0f07020405040305070501060e010b0316030912022802010c1410090f02010f08060f0d0f08 76
    0x2e04450b1420054021055a8410103c03103c650760880441042c000b01041401502040f41d00c0400413440b98150040e1207440902c03d220080240da54102c03415418000700a414a01c190041136001c0e0050006101048802c0200c0e074112210f400d165907a5130003007000ca0094840e04208560040c5415400520140018010400e1030104011406132810300881603c02c0802800b4140c2c00803400d119100b48842008002d0644924181000c0d0030030b9001e41c0000d040e64022581240000e00c04180c81e0200082405000c1c042c0c05040f506203482d604092031800705010080680710342052240d80a62441e0003a4480b00c0a640c104624581d80d030a4071030082d580f0765024149250070080841545080c801d601d2250715203c0c0e0594880101078603917210038a40304603100500d1141c0c01511103c04100186209000500d8450003070080a42180d0001510b03c000700404da2043c00f4182017088507030b565100c9215108001103540d2844103041d402c00c102d5070060303100d009040c1a030001e03400340e0441900 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 82275496 1250 82274246 82274281
    0x90b04060c021c0b06120f031911010c0c02010c0219030b1504060f03020402030408191d0f0a05121e070e01061e05090d0f110a06030e030316020f0303 66
    0xa5540c9403c001104144082d4001001c401a0000384103401081aa1804490007a0034006840480304035542200c909030459000802541c0c101400f604030300c0d000c50b0800e28030000382d0100d070000c000e07260031802d01400410b40140000d040050345a0100c045640720300b200350000300b5900b80d07056500d44914050302a1401910180c1c40b03c821003448820a1802c0d010f600150b03103d109045002a2031682404040d400180040f80e000006200500c50f114440780100480150307030340e03410180350685031440010900a0350090207400c45061880c99074444060307079800c0760f900780c1da01980311811600c40b40c2000e601007051070585070003a0341c01e20400c00c00600310381610a540009a81c503641d4030300a45a481a5442880007012084107160100b4059000341c40101d1000e400e0a84240c250794680c411030b00740110898182d00d10f504050118104060820040e00450800304a0b0754071000340159a03000c0181803011940f00034100a1100d0b10900030034104461440440391a070030f00c007460701c0001000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 82276746 1250 82275496 82275499
    0xc09011205131e021c02180f010608011703031801061a070606080a02130f0b0603010306020a0305151509030115080607110d08011517190e0a03140a090b04060c02 71
    0x40030380d400e843c820507404003101a0b9004161521542280c41034501d1070318500421307a170040b040c01129081000d1042c2d8584104a409a510120342c1800341c003030514107041c3c1240d040240e2010618481e07000000449401c00b95401c1070074044d00e03c81900030b01402d260741000e00e003181c0e102100300d40384454070050074a582c482c45040c450641c6a01085540704800343c2c0195000b42c14403c41c8190310540d90041e0300381d0401c0800454003413102c10102c1c82584c000c0e8811a80d06a00080340c94000e5030500ca280c1d005640c00e80b151001030300d490000384005c1245070b02d9030b02c551400240021b140d0341c01d52041e035030107003091000d5201c6070351401c030a600d4090171111040400d201c0d00c2c3e585209140816640004c41a949500c20325900744254415030522821103502400031640d40c244800c11640620b905c20380d40c1914102c0344070000a11042541d82c005100c50a5500c07106403000080d0300801440da200c020b00c5011758035007150380710807244020554004841000c1c0042c01180700caa000340014880c0c3d00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 82277996 1250 82276746 82276763
    0x801021b0c18060105160204050c0c16030201020706050d0e100605130c0503010e04030e091f0608010e01090203060109170c010e06070506181e07050306060a0e0c0901120513 76
    0x1202482041070302c4400b000310b61a40355000070183c0d030240000d0041070811216407207031900982d001c102110707001e81d20090b820340040346408001408000710480c450f541801c03449110310b142c2c0003079503503c0680200700a0003004190004100e01c81d603c03c02c450f5240c0803c4460f20301c0c43e0030303c1e03c00524980c02071502544d90514031040000040c0500701502d851a80c0b42e40ca56842c02441c24401039015104508002042c0d07a681001c0e642c45900a000790748441d10740c0707210720f49980116403010740c90340b094080c00803031001004204c0303682035614111040c1c9000980d89968a80040311000180d07000b6088070b5460201e0407c8081c1c0000b02d1010780a8281c0382d031400d414040c01007100900404d203005100e58810030000340a6421650a004480c031641c0c1182c08038a085000e0780300c004880b1054051035403181780c0800c4607150801545402401c01d44024896900f0900d20f01500306004000c038281c1d0a0010b504102648224a60500c0c0c3c074807208100842c2c202140015038100c030441092740c2c40d12 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 82279246 1250 82277996 82278013
    0x60f020d091505010614090f040f02030a0b0f0a180207030e0306100807092c0304050a0902030a1803120c021c020105061201060b041811030702061605040302010e0f0a0801021b 77
    0xb400b8160606c003080b00a11002d0401c52000c0400880b1060000c1540d045a01d50440031000d09003400694059180b0140c08101d81c1c0b42d0805000030000e01d84041f62050111640c1044a08500c00401c80f1a01f031003c00035176110349600781a0b41b42104000c030381d500b43c070903402000030480300b40e04440e007543c440c10140d0b00ca070703991001c402c8240e540f00000b01d18101003184441e0f01400f000b11440582c0c032400d0b81540e042c00d54481c0000c002384902d40c40080040e0b000000c000e46814980b059821a01602c01041032055580e10003c0c19001e00b010b9001d0050b61340d400c2070046078000c000c2c0069052602d140740e0301100a07100c00901030701050710b0b02c9000d802c013002000d41c00d2206000300340699208034941410300f49461340000b46600307180400703c441a6600e2440c514041e107070005510840a5400920781c2e4181041ca1380c4030031a40c04d40000401070140014030060307922000481484400311050703900040c0010010b881c101803980075100541c40042c540100080035021441c407000d80a054030140b4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 82280496 1250 82279246 82279259
    0x403030f09050d0305030a09110406090b2803020607060605030d0504031b08100c110307080403021c0b0106030504030201020c070602010e0f16060f11030406021b040b0d060f020d09150501 82
    0x2a000c020004c0c04194140001001d01c0c0b15603008540aa00644190300fa142d41d481c0850211011034102203c1c0c01d41f100d1191169007440d46c404d60510070811007240e5608401080b039a03240d01c45000080c81104006222803c1c0131003034002e40e014010081c10380d14603c00c40c0d40c01800c03c0d80188011100c0c5882d416441c3c04c7c4648180548089030341440151495100da01c103100004c01e0105140e80070b11007403020200055004002400e41c1510903034a0700ea41e14210300400040100b074400600b03420f0011903c040002d0070085200d41114107604006c034058596140503406402100302c4035000344903880e400a00e4a60540080740b00b62030030b1041e1030a188540c4006600c4501008114000320388003401000079030320561001e501c4003510300d003010038640e0400c0001d056500c01d078808030040e07001d0500460300025903400480c801c00d0441c0e0401190001c64080780106072102400f4003000e50381d0000624184040d011201d81400c0040c04005407900d41ca01000c10942070541440103500e0100080340c1c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 82281746 1250 82280496 82280509
    0xb040f1a0703020604020103020a26070e0909030405060304061415150903071203090b180102190f0210030b030a1518020306040f06060b37141b030403030f0905 70
    0x165070160b0180c41c4c01e035915001500030b0350003030690504002c5180b0008404c10541503200000070180c1c100d065550402d10802044180c61080c8240308420b02c0e41400320240c000000c503000c0f9002901c6464913903031541800001000580c1700d01d50800350400030442005c0068880550900742201c0044a41c5e19810f0008044d000740c441c0c003030701940084800c0c0042c0d814203510107016442450b00c100ca503911801203008640103403d0300c1c0382d00c1c40c0000559400e1341c1c0612044140045404c6580b1a56105448404003501d5120010340983c0c01c040c08401c2940c0b186d000310419510103412150b445001e4a03100c8004049119a4803080349000102c44190150280002d1010340040003890381d0303150342d241c0005030600b100c0c0445d00c0302c0c1c0c0d0701e07000039581030f0040c0036282c4a084080741d4824801840c1c000301500381d004020b1070440c1146c412031083d15410646101c1107044020400d600e07000c0c0d020461020b2070041000f61154400440e0020405030710003685800c1074260350300c1200719039503241800b03071 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 82282996 1250 82281746 82281757
    0x12160906050f040b0c0a020d0305030709050105091e010e040c020a03090e04110616020901090c020c09040819020f03040306090c0905041208060d140c04150f12020a0b040f1a 76
    0x400801007104101c13800115016000903948082600c0701e0485075030000d0035200f201c90040700403c80120410030155001000d1800810003030805510f80341d1001c1c001007841642c10b00b00008001041101041c0707074403540c2c00c0000c1c003070043c108002a201a0b40701943c0c0f400c2509003140020b007034101c082256840f0b410b01501603a4065078030f20998042000300300007600000035542c001c07401401160b02690310403c1702402011121000100e01503607100003400d011503219018010907042040c0710004405400701d943c01550152101604002500101c3c14122102c0180405220200b0040144031182c2c0c440c2503181e10907041c00b80102e94501e040c44c20760354125005450b0400c111000d02030503014001180d48141d00606424200e90195141c1c50707840c0600d040341c1c0303442e0702038440d03502c6d42d007014413030b1b0360b04249901001080c2c54a0304c603070315002003000e02505800034041d180c01c004545424986070040c12610032201c0c1c5542d04d400c0b41a1840300c4611070784900c01204203c043d085110f401c01c880 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 82284246 1250 82282996 82283017
    0xb0904260915070312150e0703050702100c110609060a060f0806070507020103020706050a0c021002071110170a020913050618060a0b0a050711030708030d111216090605 74
    0x1400c1c525902d40d011100d42280d0b0b0241d0502c40c181c0101e810000303891248004501303800050440c440d0800486080b011402005442030518040a2001245c1c00160381d001c072000d840c0740840c920000d814210341c40c0b1729480046100b4821314060110600000c501303d07200340340c00701302001749550301d51180446480d184218202c1c0d0300260041503065204e640240a200e006042c003614103100b984d54207045803400c448008040e9580c80d00c03440c2c10b07a41807101e4400d4414a040640c20001c10780c4900d10455602c1e507605105400030b0b503101c3d0b007050207401500001090946a000d5614054490001a50106100c0c40c820003518042c400b4185041c440c1d540a5000503199070800d80c02c5014a0010301405032a440e80020321b80c10008000a0201c02030462000640c3d469460b50f0003031600112080ca900340c014829040030005000301d29001050312070704046a000403031103000c011041c54042c41a01d140c04845003a0004001d0401e07034032082c1003158415075854001d110355501048400d8098111401c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 82285496 1250 82284246 82284259
    0x3090d06020d0b060a050a0e01030e0d0305060d050102040f030c080604150504030309020604082802010e0d140a030e130c0503011401020c0a0303030e060a020301270b09042609 77
    0x18003040040c1d01414902c0b9281c407001071030302c1c0341d00700082c0950007141c3c2000025100181520425601040031050058282418460030b010b0500301a1140601100201090361301c0d40050125a600881d0000316600030000310358998a030b006c0030065042078041996008950580000c0c0b41500054041c851504034882d4071030302d66501501c0018041c0076105504058450400c48056030300c4500410040c10100e0003800e22000c15106006e406859110540b6401114110200584d03041248840500011640124408280d1030f015040005c20150b0a03c0b13449640300c80001c06410031241c1c405e80d00c1c22106d40039000078943e01542074804008c0d00f20300089041c401007046c1c51405912a205d4501401529500d03031060011078041e801641c4260002500c2e00883c00310440188030386038125065481c258610741c1040424030184c001c84426012840203101c00505015490340202c10802d0001c2248445007040d042080c0621524000b15052204520f4920901c483da9003c940503c480134181 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 82286746 1250 82285496 82285519
    0x302150309030a0804020d020901140109081507080c1606021b010c0903030e041d0307060c081e0a09050604050c030c0a050109031b08030c07060201050105060a0509150405030a050303180309 83
    0x413214640094003ca8025607111410001a591442c006001e0008a21096880c030b840e0800141a00300300e90010603150030100c0c0c0342c10b0a40840c1d03031030342e8012200e081c10041601e9041200080d0322070880703401c051040002d14a800c00603030f50000c21244482d1101c50440410000b640d0342214801e11444021071005c803070400000b8080c6a40740c80903040141300003072030398402c200e04060004040c8645000d400c00221001048200d100340c03501d0803201d01d011300480c40d14100b0103c41d100d2404200c00d500b511100003e1100d400c54204000301c9030b00c00145c81050405281096440e0414009107202c1d01828111207064145807189400300c400580da0740802c11329545031200c0c1040e05c040292540c00c028400441c0040e0100020f144042c4000020140c2c0e03440e102009003110010f80000744134000030000040a030303078031005440c07040b1b0701140d001c8808684d0800040c20341c4500da1201c1e0f01802082c0c2c0c0c1c070301401008400b0310f11903c0340d0241303d195084108022900c0b07224040782980c1c00b8101201 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 82287996 1250 82286746 82286767
    0x30210060b030a0504060f15081002040807060309080d1803090b1c0207060e0105090a1202010606090302010e0a211b2106140a1a010201270503040f030507030215030903 74
    0x1260401d016020004000d2541004041941e1656442d81e41c0403a42302c1c804c00425004109145141c0e00c0c0d04400c43c11300382030040135621280c05100c2e0900300740e143c42c001c0713061101901c11160b50071843c582c10020003074810341320f00707040c6100304080e0b001c5840104006070b107080003400c44007071581c42260440b030364000d204240025048580282c407a10fa95461003401c01c41d003403141c540108680f000070041c054191400d01c5242066a58400469042c40d20800240350461503480c01e807a0f09003411181440f1150214010360b15540c040b03a0305818942100041007800c0c2110080207008000101c0c2c070a581c003c914800c4c00e5640314003014080803202a48230303c8441c0402c82900c910030350001c204522415484240500142d50b50101e041d51102890b41c0c1c0180c5140f54008a10203000911019003030b141101da194100d1220b240c0c0f03c61850030f1000c20040c007807088401420307a503d482400262030382407551340e5400c4c0d400f080303024101c02030f045040701010b1000d070b900c2072400c174000303615180e0b4110 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 82289246 1250 82287996 82288001
    0xf0e030a0f090806010b1b1908030405010207060c09080d03020c0a0809030a0501050109050f0108150718090603050c03010510030c052407060c1d0105070b070e0616030210060b030a 79
    0x400074010007102c50030102d8001c40921076107000300214070807280c0b036a039000d90008000040c401014850751082c10802c004c01c5400140038016a0401c9040e604e075036883c24070728003910134440000c1041c1d02d010040b800441c0c02058103401d641c00c440450794415840e15003901280302e1040b8403103540d8003416681d00003030120801011440c0025081d94400540743d40c80c6400d4503030a070018810144c03035004011111208180060040100078010680910720002107030385400c0c05071580080107449412050145451104a03008140c044000c214982d501e04240e5102da09800307070b051283d400c2c030011912190040e407042c0d040d01e400c50307003500980b454a02003154601c5066456500c507449288500044064800a008814010940403480541e4154000c1c1080090084e80c841159450800078050f6844400e0300e0005600c0340000030a0b0700c03994404e0351007805109000b03034030580003d203907101c050b50440d080c3c0304144240c0803204c688207006240019901c0d24020803020b00801d100050700040f03543c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 82290496 1250 82289246 82289267
    0x230f01110306040e0a0f03032412030f0509030a05070305060a1b050a0e040f0e010507020715080a1d0a0501060509040f08180a0b09121c21090b06040f0e030a 69
    0xc101c5584502d01e940d0032603e01c6c00c910003a8042641c030308070141d042183c6141a6028201d544000c1e00007401c0041e01000c803500c0f0340016040100d884001d000c1240078008446003d44010708544a00e1820329129540c1c85c21400104c0c0c59008520214040c1e0b0014010341038130f25242c80c10f550001440c1c48013210140c014211400411540420228813902c0d03a1240200210a000020800c20b228040c12820b449001c0e10b07000841d40003003400c0001c0c8520004084c0c1203101454140e00039190001040c0284c0146e50f00000089040401030101c003800143c0e01140c40e2092000b132084907921002c000c1c100b0300440700504005000e10b05c1340005040d0000505420040c03000340b81e004d16184010550049041d08400829640058290824900006001001c208800080020b0840b501d141841c0084c03000d0000207000303080010340443e4207086940010740c910194100080782c10b0381080309003650f00341c83e80c1e40607618040a120b0705c50380314060501c2104442d8000e600e00030002404841e200f800 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 82291746 1250 82290496 82290521
    0x180c0806190f061218150911040204090912080114040e01140106020706020f0a020f040e03160b0f0f0603060417090a0801020a0f05040e061507230f0111030604 70
    0x48480200302038900300081c10152246a6486042c540844e540c1d03000c40d014550300c00b2019001860703050004003840801100d0703060f4914003003904c40d410b00e0220710080b203122400d0f0b802800800c0203e503000180d0f001503807190003164404040c10540f00305441c4290280100c1c14080b008980c41c00d09400c00b5003004000c04c55020000070b10085071884034080d4442078006134016042081e003080280ea0400030b90b0b0514030b44001400c0e0400c0c840e400160740c201c0e041009406141c032051240013508040c400d40d800130020070880e200500e45072520020000048401c0c0181d0049200802e024a1603044994420034001d4014070b816100e91b1600000424070025a28445008002c00103554640c2060b4030004d040707050002d80c6600c0b0041000d4803000807045100104141444204442d55100620940020080d030b4807410030714103e0030202061059110140220858080403040300107428003888982980a0a9454451444900c03c0c241d42000080f8080c2c2642030000c210789280c290706c1031040010 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 82292996 1250 82291746 82291789
    0x80301140423041b03022808030a120b0303040302101e0507020102031617070302010203040b0108160b0a090e01030b0402010207050405150906120f0709060b04050d030e010c02030609010204180c0806 87
    0x580346d00098203110100c0f2000d412400e11200c10058890170030086010302002405541440e019990062440038a12207501b9482d4480031071400c1c9403000d10441e0042d54001c0d16560a004171403e01074079081003410945d4030504045030344501c0318440c0056a0302c00d036050b80a149080c0f20589103040756800c901040d5140311410b949a071a034070031840140790300c5100e90005600c91410303003000400c81505901c120b440e40c00c5604820802018000c0c81c100703584501131456268500c8650448104c0d095070410701ea01c1c890580084140b214018038584240c0c402d03402c4480d40c90b00e4509200940e0341c290303584010034000c0074510b52685000050f40350f0001010300703030703800d0a0031141c09035140149541540907183c01a850601008516002e0807025001c0c2d2000316182914140c04242503442d000720142c1000140110341003142c0c4074a0f000380360031307070010100c03652814110b090a000354407500c940d00729044584030800e1444107600031807150010986668a05e5501d0f0403d02409082a415040c201c40 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 82294246 1250 82292996 82292999
    0x110a050405240f0a03020603180d09030204050610120209010c080d0504050601060e090a020c100617101a040518030c07050f0d0c0b090d080301140423041b 68
    0x4403039125203803081c2007824414012212103018548182031100009005510b441042246a1100b5060008a96040c0d03001592580e4020070024030b00210f04c8800d46a0040c884034940e4551700881460607640202d5040049845034030401040640c002985808039401e622114405403040d4080c11000206060042c4240c8c41d9558068036980001c800780049641c0700e00b40800d1007000c03c04540035119500300400410300001c00100790b00e1000300240e145540001d525201600c00380702034602003401440610403a41c480100003c24118182802000d1203114809054240303140100c024640d0324010842c42d42d01b861003880701401006180e45110083d0080e80f40c1c0b0400200020450b9510a07805800f0450804040207418800b803100d86208584065600f00420031044440c03085030859443c180da2502c280000c03409550040344d000c0d00c64007000c0700010f0798074140e40543d4081310b030480e003c1200081c00090341d00522071440b03000001c01e0a55000500080b141420312004440607480c0340210b9 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 82295496 1250 82294246 82294249
    0xb01030b1e06100509121002210c160f050d020d1407020d020d0f15020703030b010e0102030d0c020c03071e0602070308120a0209040204080a032a03050f041d04110616110a05 76
    0xa00904007106449030300042e01c4003654270300e00580c0b4006031940c162182c24200744d40d02c1107460040140f0340c05440011242c0300e04005a102406030007036440800d58a00401c0c0754030194841562624045c08940110805114410b5940494185a40c000c003104092081d903001c0c4040403120503400c40d55403030541095000b01d401924203512500b4120740150351340c01ca92030028140c07013000708924144072781481e0a03840d0ba0b1b00802511001584108001180410204202e182c80400d2003501c4d014010514049030303145405a0100603400b070051f018006991314081240d913180703d4032026141c00001d001c81d4400300e206198140c0c010f0004031001d400d090840c00010308030303030007036000c1c070203590001411404060308032200c002c1207801c403c59404240401c0881c14400c1d005a5801010014005001d491140c199800e46000d0301c403154010722a442101c11802d02c60f40240c4094900c1418100b404402e840c09104a80341c404a4821a0b000c8105640c0c0e040390310302d440680164085001c01012809 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 82296746 1250 82295496 82295503
    0x6050c010e1207060b03030f040909051c02010c0206090307030801060f0e030106060c0b0f0408030c0702061c151509050909010f150f05040605060f0c07030b01030b1e0610050912 78
    0x10352070b851a01c5551503190385030103030446108400340c0f40031740c00910644021004070801e5038200c0b0030160300400c0d40c88103403500505200f1038074004c420005810140381d14031076055200c1c04110300650200c440603119859425a207010b641401400240080010310195204410b8044020f405040c40203205601c02e00003400d41d006074002500041841c942a028400500c00d89030b00a00d000302995a14101919a100180b00091a0b0b2002c00d0001071604c0c110f468440c11541d42000018004814146001001002c0d041c3c0c9912400c51604441e404602411082011801c11125481c6d80c1e40709460031043c040c845000502c030201555036014107400c20b4849000b010201300810000c1c0d8196810401c0002003040540c11090203a45004810300180c0c03501400c540410b071406600396160018041348510f0311180fa0801004041c0300c20000040015460758035014981140f0200440c01c0740d504802515041215003ea105c21751054401d1680c2c0100700610417044060700e228070754030329019958078 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 82297996 1250 82296746 82296763
    0xf060702010504060b091306110909040c030308010611030d0b01050c030c0c03010f0e030d0506041b0807120207030c1203110414040c0201020306060403080f0417010b040c08070906050c010e 83
    0x1607510b03181080100407181c401c8403030610084526922604008106c1e00700c0000c8403000401661f0f403003070304862000c50b40302501c0007510010040c031003c0c40c01d4509921a4403180c8402c402050010001040d0349008001c40c907075010345140110700700003800d00944003801c4484001c0d4140f0604204400d521001480141486810500186000c0016805142c00c4991090b03402e54918508036482002510103c1126200c418900d00407801d40c40f410001801415013844000e40583c12032a61000b0755040000c2c240718184503103480314881d900c000050140e100d204002800500604045c0c00013400c0c014810701e800f9610f103400540c407180d66650220550090700000101558004040010326040c0160101060300b0300c004e50440c1003c4020030028000c502008020341d001050700d4105991a42c00d4400a0941031600041c0f414102500d0307000b00340c0441c00c54003803810b1102c1d403141180500002c0d0f020b00740660b1280c81940c03910004982c26041500342c6440e0f5503e42e0741805501d0300c1001082c8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 82299246 1250 82297996 82298011
    0xf04030209040f020f010e0112110f070507150504030c0e1308031f050a08060f0a0207150605130b060901030903050904060609060206010e070c03050a050d140105130209030319020f06 80
    0x1888841500405c100d0341140d1204070f040010000c20b050b8240d034480748581002d5820304010907401607003400720505000328006134001c80400b04a0000380503000032240105c605000c0c9545104454450031907151040d400701400351501208100800c00b00c241c0c1e102e60008500152031140c2d00107695449003a44162800007200510810074044040940c1946000b060100e03100b40350b651400e152603072928402403155404510000000b4400b001d6a01214030040d80070754503450403041d600c44440107100f64000c0ca406110705540010060015100340c2c2c1118400400c620b080841c280011009030801102c21410810248800303a040d8489000e044090442c5840d1460b0460500b04000c2c40c10070144e108000480000042c03208054100004111540d05864447d0392101c00c40305c144c0f170342e1181c4503400103050300e4245c80300740c01c070006c0c40c90505840048501d50004001c80303000038264000d00b0026685608208060380340303585880e44408242601d8015580c507007020712542c9080030402c03074508 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 82300496 1250 82299246 82299263
    0xe090f070e0303071e0203100c020610050f0108010b0919120203060f0106090b090d0b1503010b0111030f09042003040201020106091a040e0f03070303060509090118080f0403020904 79
    0x8000349801065503240850207070011428804141c8805420044807418000d0341c0c0f2009840d5015910107101c1840b500325503000070301c11407140000c000d60722501100e0701e4800c5480c0f1035000c00c10345480010840805416981c00f0010303400c0542c424000d034054421a54066040c00d4100e074640c040c401c0b040010940c8010382815880c007401854103000c0c00030400340c1518004e40041c040b16410107003050a41d41c55030b030015142c0c514100465981e000301c813000742411000c1000c01454078500d404031107c0300d5060b0001c0c0300c004c03403c100560b9140c580d184050440d400a002c0e01607000c074071178040c2c00326140c01070021421104400c100300e14202e0010052008890000030031040d540c09000d00e0005080240c02040503800035045003524034217071526207100399164181501784400800880700c03469459001c0d00d603070340690b2070040c004103410303c00c060188906100049901c0018031403400c07000d001c2c44094014032802c1c2d5441c01c86510100714010b000c40d01340404805030700d45504039441107101e00c000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 82301746 1250 82300496 82300501
    0x100b010201062c0106050304020a030611070b0901050403120c09060e13022d07080d0e01060e07050706110412140a0503040303030e100507021902010201060b07060c080901090206070b04030e090f 85
    0x1128003d000582080341840000c01c00e010060f01c580100c00100c83d00f10800240b6060301c07041c081c03036900c80c841e000303810520601e044c028205810351100e401380740f1039240c1102c0740c00d90b183d01c0d02c20340c0c91105a403800f190840c1e40400102c2d000306014500c0000003854840c4010303482c2d180710101d8000540c80d551611001c107910704a240456040c241c0801e0501d42e0300e0408010ba56140e260744200706200000e1a1205800c0598440942000c3d0291403200c1030304405103406240144036801046040c2c805a023403105020700116808102e4069400411001555500035242d05214103210a440d048a22440c40e002c00495800d001800c0918829980420a6011424030518007901d4100400a4925000034444040e07000200191502d00b113481d007227643e190320b00043c2e0040099510000c0910310002d40d410800c01c09502511102c415a21880019110322000768202d440004009421400070014072022403802105540d0240c441c1c501031130b0f1100d1801c0480c40150060f245d2808034400f02e002d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 82302996 1250 82301746 82301819
    0x62105040b0f092e1b08090c0103060e01060f020a050303010e101409071d0d06020306030d0c050705090a0b120c120120030c09210d05040503100b01020106 68
    0x280c107400103900c40040a030040c042d41c0440002c085808441c00c10704448001000c5034800e80c20445e01a40c407403030030400442e00c111003e040e4810495400e18a400f0721110132900d90300900c1803030140c1e00700000781951603003061004d85070342541141410951041000c0c80e40041c0c0c0400c01103029000340c0300c20070b116040403003c3d82110001c41e0000e44a41a88842804c456240c0c080c140b40d00c401e541c50590b034440141440c100007980c00041054010103403104d21000d01640b600118011401603048546800c486c804c211071038400701100070a103402070b070700400242c5001c0040a4020a042100244650710203000582010390480c07035440743c0c2c02584041d921460030415103500400500c00900c826032514010212022520807004c81e2814003102250400d0154400c2d50250300010b49420b5614640c0e0040d410801c0041c0c5442a50348100c01d000c0741c9252041040d00c040b21805002002c0d4402c602e900b01002c3c2030802e02c942d04541d62080005038100c1c483c015649802081448068010420344 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 82304246 1250 82302996 82303021
    0x7030f11062106040605040606030207200a0605030a180b07030f1b0c0503070c0b12060406030b040b06011701090e100219050c01020f0409060e0a0b03030301062105040b 74
    0x15601c1001c0601403403840b42c100e05001018800b80103400041d030341d110f5000400600041d002584c00901e0900b010030507540541c0200b00044c01103a036072034045004807003201180030081601e0f07007210702000c0800603140500702450700100e505101041000c0710750021462010b42d60020781c1c95035030341001d112010b0f0b01441b4034082d41107500802d004a4000c5444002d80c0a0302240105c200815400b288085c0001407064030045075000d280301503019910a002c500503080031038494016841180811214601840b0384004c44e80d02c13412001069981e519141840d500041145041c420044104180b007032000c001c6034046c0085110000300075618052040c604001c00003480d0321a4030402000140d24a408200c1c03088130f1a07480c0590f03682c03a80c8401c1901a011304807a40a040d4004900418400a5608044142d4209031407501c001c1e0340b80d20070312041d2004030003400d030550810001407007910320400e40f842c0b09080c20b003982000804084040012282c040754151204054041440310114062 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 82305496 1250 82304246 82304273
    0x606080105240a24090905100f12030206070e0402121609061b0f0816030e040b010e09060f04020412060902030114072f0f0d0e061201030f031107030f 66
    0x15074605120904283c00d91924103201c4c2a00410020b001d0b58000407a4440d4801c08050309518100703024504083d189400200c20758001c2601101800c0c4000c00d160500103e030b105c43c03a0701503004220b644c50b96003003a9080303018212041c1d04180c0801903040b04040310030000e03025940040d40c0300103000f5081401050041ca44d0003860801061550707980071210088003007290240c2000b40606440c80500e8010f62511410b03402d40c3c0e0140b19420f51606250f00506c0c0b2442c0101c0a4405004100c01c0c80d004450247e41da0142030340c440f0082c408140c090034500f0700520200006040146415198480039030b410a2852040360303401d88071107500f411800c1c00e002d44006600303c680f008155040482c1e001d03140c44052034407028040c0002d40b81c420311003858218125130040003001d80c0c00c5540c500c500c854669032a03121b4000400e2034a080b0002600308007040f01d02d15040b400c50302040742d081d075550b1600c51b03a2089040d0304001252a000ea00b285081c00b01000641c49071404c03415500f80c0d4600412881001d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 82306746 1250 82305496 82305499
    0x305011208040504050c0c0f060115090e150a0902121b04030506151507030201020c070609050d02010503060d06021603020c0114040311180907260304060507060608010524 75
    0x40d0114280000e000009031016620200e4010400e50f484401c816890f001c0c0f0483c3c00350038800c03c03500000001c03020031300724141c500454801404c001c0428042e11b444c0301e58810480e44540c203100055184520100c07004a02500410307200710103641e210013400341e804c81400030300e41c81c01c080144001e800c2201c0301d840c002d00c1c1c02803085090501d1521000c4e280ea8005007400d80107880d0100c2c0c0307403441d990b44036a0b8052104a004468580b41c181c1030007030003500851940701c8184a007000105003540900c2d040b4040728002000c4d4802101c2d95401115680c201904154224840b06c51400c00524a0700103030046140160206481810604009207052003904c0028180120070102449200742c4104076810b030ba8008400301403416209011a1041c801070fa1080c0801820800f403281d44040401e010003100c0c14030803170f24580c1c000c41000710b107100d5000c103060300d0030b50007000104205e9000d1805841c1d8903000702e100007452560344865034252207084440e00e5141c4c0d13000f1504903400c2840e48401004220 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 82307996 1250 82306746 82306769
    0x70503010e0c010c080f040302030a0f020310060510030207060609090302150c0307090b030c0903010f0c02150f1b0d020a020c0109090e1b0d1e110612060d2108010501030501 76
    0x100d000000c0c101441c2c80a014040805c0040c00315990022442210010342d8003404a40b0010402c1c10607900c4c0518948007240b03e400345e04124a42114540150429207100a02c00b40f40c41070030715410350003944001d408807002c50321504002502141485090700c6240290050002c100c040c00c0303010320356040103010362001304081c070501c004250712085020503903146c0701056640c1d440b11000c81a89016000c504c550641c00c0c00390748449000150002c9072415065000c58a8001850b07000c0c032800d100c2111100424410500061010213018520200075000c41d40c62500e45030300c00c3c1344c1005a81c0102d1000016a000c00c100b41d9455a1202c410360013050741440070071600c0c42c8024841e07100c03c40b809001c03007494001400036401e83d80d18000300c488580d12404031903110f844114209d0030401d140c101034a00360042c1403806000d0600f0411200068104c0403000310582d28903003088602e40c0711100985041000040112402051201c0b55465100d20380b03072083d1350b6140c20001401c1e128160003c640860 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 82309246 1250 82307996 82308013
    0x518010b15130e0f0a0c08010b0405221503060c02030901080c03100f0806160507050a020d06060f091401060f0215040305040e070302120a0e073305040305010b03010b0907081305030c070503010e 85
    0x509ca10240c8003522400c807010304245c1d0307168980780c4c441258601d4200540c0c1c0744c680481020107801c02d40c802100d220315814042d1202c1d0680030303071b1a4013500e410300d400704140c3c50018550100c2c00009581c007141a8000c0c1c40c05540fa0f4060101c10261500305d22440d601c10018008441c0d0081d014480100c1d15280140c50100780c0d0355559114002c1410090080b0111010725080000981000c0c2c050070000c082451126603806d02c00340903001c4c0c603074030380c1800100b540041039480c4680c015000e0015241c009191146c00044056402075005005401308842030001066200e481c00380140541507d80e005070b2543c0d2000ba4400b0b40810103418030307007940c4c0317040d0405000c4000410128102e410060400e202280c22040c0c0305200740e83d54500c903c180280c40e0100b00d0035034006c0094000d90780214020080c2c406c80340c09060072500d104904c40d6200114000007000d6a1141110750b03441001d0041c0007500d02c5140c0c0d2840d107541c1150951644940003d1410f10643c20240704428079a2461802040700d413 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 82310496 1250 82309246 82309259
    0x10f0b010e010804060b12030a090b04030b0c0f0c030304060603050c010903210e0303040603090b0709030203060a0b0414010602010518031305010f1107090518010b15130e0f0a0c0801 80
    0x22140545003605103e030000028090120300c3d841070358180c1c0050501101c6e4480c0e0b2101c15100d6100d1155080400c1e80c0c02c00210700250000c082e5010340e540a0301c01c1d100da844020108070917800c421802c8103441c201700035103450a2014409180558071a980100380207095291647c2400c0a503a00903040101c0600d0030408280001e80d00000b884025400441c4004070301400c4030041c0e51240101c0e0148000030300040e201d64141d200c0491a400faa0250900b9111602d0031650b250305880080d40c90ba01030004205801400d138000d01b04e4a000410010f05070601d20030101820b42c00340c3c420f0025075960410400b5524075130441e140c112014901540c5480a64008414120094055103041002410081d01c09070b0003081d0302061000e00c2412103104558503d803400240c002240d40420300107070310b0904407046105010b55803500c107000b0020460803040400c0042540c001c0c0307900c0c18281c81c548200044140b18a03032018051103007030140c5010707032810000080035920000d07010703810031241c200100001c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 82311746 1250 82310496 82310507
    0x161202030a080708060406030f291302040b06071b0302010801120804141203221502150402040b060c01050a0e0303040b0112030203070c080604020a09050c0a0c0f05010606020f010f0b01 81
    0xc03440e4205840580c80303a9000c06c009111540000300344501050102c418400101d10002409002c070040c5000592054211422000123880a07014000011411401441c29420511038030102405041c284031158595000190803c841102007005041d01442556030260b41680906010003202c107201c0717160759a04031148101d11560724244110085240150759039030364180d03074840c480d003142d480b403841c5001c5107404010008500300c030580b000301c00280381032018580700100825070040c0050308040308100310003007001401241c0c0603541e40c03111071041e603448015046192582000061074641a8812001c6030081404008203078404c4c420480003402c02943e041c1174903500303103666007005980d24082e451400790500c0108400032140340419080d2000a100d0720607402203c00c82c94050f80d4110300e408072142a40c0b58024201c0070008444070703500550089141c24800c3d803601c44200070300d4403003908481c6c0c15085540140c0003000328511000b0240035001580c4400803080210300800b04c0003814 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 82312996 1250 82311746 82311751
    0x1803080c041d0c04090c09060207050f09010b220b070203010f060e0c160206180916021c02030408060a02030f0f09030405041e15081e06010b0f0d02161202030a08 71
    0xb44055510000b68024030718010f41d0001d2102003001d0080d02220389003c1c00311031090140b00018400c00130005900d00c3c180707a20321400c20f006041d400b5107900306240341906511412200440350682c002c00d4081d03555007015840140000d40c19a9101c0034184105802c0d504103524401c0c50a0501406006d0500ca85075116086070b900b1003465039540b6a168450008080380d000654480070102d0181c01800600c86100f050304804c032181c20907540c8407030046810041000b61400140c1c00300c0305e0645031710540c1c05903c29401300d81c01140d09086e520310405161a4040300c0e0460400d4000c41840405080c8a841e5a001600e01840310068a88032403043d80d00d0041e40b04847c403c0307840710000c01840040003204902030f0503054050000380f034a40c560302d22400180c40b484009202e50a20091500d41c081000c0940c80c80c81d20260003580d00c1c20850400703d0f000962003145040c03040150181d03807003c510060008008290360800482c900781420b1414100030780007032040d90001c0000d6807401c1d40c01101a030703 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 82314246 1250 82312996 82313039
    0x1005010201050c12070c0b010b0405040b0105180108100f030c060e0307061d0d0602070302010603140d0c080705070803041403011104060c030c05120d15120201020601031202101803080c04 82
    0x2c0c4c103542e820380488400c0844003020b00122007100c008214004844000e205840c0d095a060103082c0c002001103455101d0110710040482d000042c4082c01c0d841800b0f00c5c2c0d00038a030448000c400e10384580c440c0c1c8859549900442e64034081c0d00007005aa81c01c10412000380500710091700350103290440c0541403a40020042c0d260f502e801c4054901c03540c402c0140c0001c01e801c020b0440d140e44007032a02900030f03c0a0301054844016000f41d943c03040f240080d4241842c01240d40e1448010380301d40e9a404960804c503170840c0c0c2c0740030b210004242040c040000d0030080400f0413a0b038182c060140189421030b01701001561000b50100001e024480e0010302c0e00428550500c1c00c1e244028007400c00f28200400100c940c1d002c10700024007900d035101d050300440003101d9141469030015030384415441c0c10648115000f805030f00074100410100d021010260b5645100d8019681c07078400b010321000032545000c5e07880022400300c280c0e9106059100940c0781d07100d22189106880e040c2011090071501e00a880c026 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 82315496 1250 82314246 82314277
    0x5060a030507031512020a0b03010b04031103010e0a120f02010203150f01020a0203121201050604080a03050304110a3215070201020a02060f0301031401060e0a020d090c09051005010201050c 83
    0x100541e201364040071100c900128111001c580b1101207a1080f0801d04050741f21382110140420714243c03110449040740e901c869464a05403469540c10850b014641071264507550f40c4020250001d03090003242c281902c20303030303d81e4840c2d681d9800181c1441e42c0c040c00c6c082103a00c103100f000414020001c61080720b01c03084034040240040000101d10707082c0c000d00000d4042c003480700e198500b03080480c081c3c802c920100303c1e80442d40c0c1c5c841c002d01c0b0b01402103210b02203050340300c01c0824022034029001160060301030380d915500304005402068140032a0f40c01203642c44c080c0707540440b015601d01c0301104140c22912600680d81d08010000f1803440b01c44049482d845400242d43c402c6a000b004100d1905034054001c0da110302d5200002c0c0c80c0c54000340f10079540c0ca041e8480303021403110184500b000307460346039400c0c0900d6201d070709a50000390011a8070081081d620b6a5030404540011826801080640004199881c0080080b640031030f0607803140e415681040c003072242c1e0303906200548601c0b2280140307c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 82316746 1250 82315496 82315501
    0x1080a0c05010c050f01110d11070b04080717040f090b0d0b010b0c2104030c05060a02151005120d1e0206130809190603060506091309050c15070b06060405060a0305 72
    0x144e4180144454581d41d107618141080280d415039501600407524861010000b41750a0704181c0003910542d1001440c0c2086d820001e030000f040300000d45080e038042c000004c007881c0502d01c504032a07442904000f400b00350b030b00c0d030410000341e030350182440720b5000b9a981034181b06555110700b200d040601610b5503c100208545010700002c018010700006011a0248030b001c1090048480781d005003c282e4410041d1407012075582841801c81e1006542c40d40102200c42490309600c1d41e0002c090000c020680261400140554499203040d002c0c199a101070300340d12410440107084140c02002c140340051905041d2100e031070700031840716400894098801450080342c80d00c11120f02c52417031001c1d40b0013105d0f907a50701a0b03410030f45480183c943e070b40c034100091515a81000030f98014003c0d0f644d40056428494110b2040035001112814030550440300d480f2844400108501c050100c900c0e01e110300421200144584904600e41103101519414600303810000405d86910440c01c0308018140c59101 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 82317996 1250 82316746 82316753
    0xe070b07150509010e0304060309050c0a06050316090e01060807110601081005040602091005030115030b0a03030f020a05030a0c0b060405060108040209040f0f0c030b070905011b0303060302130b0901080a0c05010c 93
    0x1c0103864100c0046e29074582d25001c000c3c000f80b0740110b050380c0ca485508052142401c0c010441c90545545480e4117007907a5030303884400381c0d01000003214070400100c02000551b9244254240e4042c00042c1c5540140c1e2a240d48028101c0e5001342156034154815001007049c11004544401c400d5203001010401e650b480c03c0403c043d12030000c210b40c1000440c0702d1a140c0560000c0030358180c0e61a0641c9113010b00c1100c40407000d440100840580c0401060703c1000000d0181890b002d03c003480e40140c42ca030917103d40b00c40741107400003500030000c1303120020940104202d0b401c403954032200c2107508001d2810000c000811025004100038003440110012900f840051602d008005901034030b8040c2110151402c0080c400712403208030f56802c6200089100ca501440c566020b4032010394988401c405503003e9030b01e0503803c110050307003496540c1c1d10100c003584844030000c0c3c10502486000c560340445005011356800146c1c810142d40e00b201004170000f034030a10b50340048980920706000102050304 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 82319246 1250 82317996 82318001
    0xc0d240605060705070602061021061d010c1403090312040503070803010303200120030c0c0102030c090f030703110d030909090506010302040605120a20130e070b0715050901 76
    0x2000280c0c0000d000c02c01000700304c0c0c00984201941c2d181c1d426100c0a03100c90038003555204050181d1081e80c882e201c07900c0070381c090010841420900420000ca8a2007440480d01c3d4480c030341c0079000385565100c0307040c0100d6503000091280f00380c00090300c003455032808100040d124020480c00342d842002c058007003000c0c04420000d9841d010703004480c4030743c0c0303507901c0c903000e045000c0c5c4415003820b0050000881100c4034040c8507880300c02d09100d05903c0d8000c00c43c090b8100c107600c020321406144d1024400c415000c0800d2001d5031060600c44005607a440c11030080100d07500310380105034401d5001d100280001030b004e00c1c80c0914410240c5021a85101a10f400e40e10820076800010441d45003603004018000c0c0000c0ca18102d0b4003d4078100900c5844105010301c102e07440c24564000d81c85204c82800003182e16091903d0440c000075960728003600c03280002c01c2c1040020303d07090710a4886409211030401030004d03000500d0b920600c1440e10005940f540f544180a03070321050816a42d03000200340c21801e4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 82320496 1250 82319246 82319249
    0x180507090b030c0a090f060e010e011b050c09010e0c0f07030306090c0513060e0114070c17030c0c0d1e020103140108150105100e150903030d0e0c0d2406 67
    0x18409039850340f629924142507500310b0401c160015114080014a05d508a5a900c0588480d42d5403002036541040c01501c6000500307403013504100a40700c80e98100d0401c2030603816207a100e44040d008415070001049504041a04220311004000c42403205846070f0100329501c10700900c1c006c81d160171103800c1c103800070006a07020600807810011a00c10003603004004008041103400c040c41c600b07403a003000f103c0000381c502e107080c0400d94401c0c0c102c2d4403030301905c0034040c0640314000740010140c64464118079802c2c907100d0000c1320b41c03010500d20101803090280e03019100301038900b8640c034660340d12006488498446c080d010380d24540320304030559100b0341021200e048000c9242c802e550351030261598920118448a0b00b50110400110712458a8031103c00d0070300780d1740d0b035408550010074108509c9000c400540d04454804001c81e60142d203090001d4003803105c8903440010000181894141419645041d140c07103000350490f0b000c005401003a42101480754507158003401034240013841e0040c80350b0b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 82321746 1250 82320496 82320509
    0x1514030109020304050f070302150f0702031002031e0709121515050f0105090904060510030609030f030b01020a05061501030608010e01380405060f1c020306070918050709 75
    0x4008507036103100340c00450056120344201c6855a00d0900c2c05c5849000d9400001e50050b6641e1003101e8a103612030207000107211902e9102c0ca010b200d680043e10701090b4015401400d900441040242010300030002080160040d50400d0351804100c01410302c8040d00910082c00b84400907c2c0502403162054101400503280030044100086403000ca00c0c1c400e4860710f48150b480107000030140d489001690551100942880480d80361a510345024290082c030310040d000f4205000000706100d402141c030348900030b4407580b00c40309600700000d0a031584c4800884c10742d40002082e40c0020400103595510520440103036a031021030800480c007130509176010040310340c2004a824480e04041d808030641401c08007184554560603c2c420280c1c00c800703841c0c8000c0780d86450302c4038064103040d0071503607208000600700b00d1407882c680006056851864121741900711103800b820304500741000390700e410100e42e0030480da42d42d15241d01c60200190b20311312081c07015200c2c00850203950180c000751025000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 82322996 1250 82321746 82321787
    0x10603090602070209092a09011203030b13020904050705070f03031a0316090c0f02120d020405090103050d08010e101e0e07080901050105010905130b0a080601060c0501110901020715 80
    0xd080c0211a82c038000c403494000c1f1408203620410401c4821030044880540150940c0d129038a4010f03082d01c40c100026040d0203240c1c98410801040d03951403e00ca19103c034081005072220001c2c414070080344e00003000300701401403c02c84940071a1070900d6170221160716285c00305203403462074030890514640d45541605403107007025803c1c000c1c04108910054138070340030042140301019001101e070311649856480241e00b000450139401c0425400a24042d00303101000351400742c0d40c0001c951009401d030310984864015090b108406548061a20f004000f4010030701094104500b038140011070034800c00c00d80301c040707110349408107040c02100401040b0840c2000045e01d440c1c100a41181003c4490400c103510701000890690b014556083c1130300c1000c2c0c00c070a56284181041300007030050942e2180d114880701d40c002110b400400c002ca000c1c01c0640d8410701c252138036140803425100f00004030352204805100105140e64001130080440c0c802d40d80c191490703a1b03105d50030303240001c0700c000c5000c0440 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 82324246 1250 82322996 82323001
    0x60409021b1212130308061302040810020a1e1d1c050d11070617130f141902060306010804140304060206010f060c030e0402030a060f120c0f0b03010603090602070209 73
    0x2010900078099403048548003d40c6991030380781c00040410042ca004002c40d00c0407000c01c2560400e0045407411380580382d401444c1c6a00d0341d52013854400443c40e00c135803240d0001403880d89294031007500d402d00351801840c940864102a005402e070b0240f014000d110040903030382d0309010baa40000b2000d0442780c0310381b003031074440d250704005d03466203080400c490205031441c143c00500000040d150013150030b1070340d03903c1044900c0c0c010a046407101070802c06990b2400d0000802003554600300c001d019114082c2c1c900e00700c0d950084a030900403c0080c05044540d43c070360303032030140c2ca43e1001c407030340400c2c2440d240c0425901c4c0d1401c08006650140c0c04c0030544008680490165000590b640c1600d0102440500883e83c5040859000c2c2c0c0c1c030703800200054021642c1424a0415801454105403100da010681a844c3c005003640000c9076485900c00295014100c8140104940150054104005010131150500d201900c20388010b21400d000c0640d180e54180902c46540d043c0c64810794002c0c02c0504a0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 82325496 1250 82324246 82324273
    0x10031103032b0b0306150409030e0303030703060f1202010c020609010504030c0b07170c03091e03011505091302030718020d090807030201050702010c0906110f03040803041d0402060409021b 83
    0xc8040c400b07a202864940f03000c42403103160020382c45106000c1c40b04a9000481e0306020301000d8108600100c00780101c00034080055a810b00182d44a400650f50020f141850150101e03c481e42680c46200314200400354140541da002c1c584800054043c5e035407640e12071700940100d509124591020305187c3c405e080225081083c4001019014000d02080805402c0125411061b1056019a240540c400c00c104100c0d8108900c6099400c01042d8115541c0003040001c07900b035030780e0207104940c00140070005000c0d43c80c000c07076065000203032030b1320281c514000d03075000c070396640401d008240d00320040f940080900241901241c1c0388d021042000d01c0304c0d401c5898003202503003007064118099402c2c240024003540c814800c40a00c00b031540d8401c2007091074201d007a1a0100e01802030b92160091404007807d100040004100400f120703001155214030700505a41201300c46c1540740d400c290714200703001c056038502081e00c0c02e440c0d404031f0060380c640344400fa80c4000000311254085900a4081d00c2414 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 82326746 1250 82325496 82325557
    0xd050907050a0b0403120203040e0a0b01090306050c070605010e01290d0f020c011d0c010c03020114041a010609060f12020714060a0b0409051e07120c0603141003110303 74
    0x449108080c200142c03a0741d11b01c244e0b103038090340c01400b01201c0c206000817100b09240d0481d0600507410705080c90102d450762225001da50085500c0c40401c040024401c0800ca44c034032805005004940c40e60115504007500c81d89040d40c1107501d500f8003010212100391002c0100c0c202e0b078580b0742c003d17001c11068040c000d100b000303900402c41c0c0c0519540f92200c034000b03106070302213619103891213030300940040e04c5c2000041d42d0580400740301b5011590f0f03843c2c0c50310117080c0913a505801580614000c01414041060741c4401c00310507000082005641e00c0d0401c242504110480960381403810054854021044090300038061900050001d205041008810700f00204041d4020300c003c00d02070151940c8901800f041d603040c00d800900690004d948001c041041055904403d107014081d241d4607540c410400000a864002c1600c2550512600704013050f0075200c0c2c014510340303009200c105890182080400a8060710000d4a030f090318002ca9080d41c3d4082c811a0321006a0302c1b4000c0708010584020000c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 82327996 1250 82326746 82326749
    0x2132d0516020a050703060f0603060501030602091c03080708070c0203060a0e10060b030f04020a1505031509011409060a080102040b041409090304090f0b0a1409060909030d050907050a0b04 83
    0x40740100103112a0b840030402000054001c0014070010786955180320003405401c1d00406499038400011000031031500a01d0300844c007a010242e207071a03200e82006402c000f1507450720380c1450b200b10345070006900b04003410750000d20b1342000005989d40e80c409568010400c1c0b0300940c540600800c0000750100b5900580c04044000f04940000c102602840100c80180c024440d04900500009062440e0700c1e50440c0d2013840500003280c095501c5040e00805800605d080000c540702004200784141c00e10300c0c007650704104444c07840701c03545400c450111818405c00d405018403056000602692902203a0900400d03500008558940d40c030003110b4103070341141c000c8400e0b60010141d4500d941c5032a14901d03015164030740c0614941494601a40001c0581c40c80d01e90303c00b80c4903029282c182c2d48070348010300201401c050001d8491581d100300003000d0002400d80e4400c40080c803c0c00700c02600003007541e8080100340800942c5465101d52903152003d5942b1450703001031000d10208900004501500 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 82329246 1250 82327996 82328011
    0x905010b0105040612051008031204050c010e1302090102011506170a05040b07110715050304020108060d050601140d02150408060901020c03030a0f0b0a030305031008030702132d05 79
    0x2400c00300c0e001110588103503c2250005044080e428541c1c2e103060f4041500407080c02407540446544018081c150380100d02d42c47d0169125900f04810302c2010301402110070024640514030b51210000500001001500080c0380760b80400d000d00c00382d000750700405c4003030780103d0080c904030365440c4000d0012100c0e140360400c107410000030900c101618001d075802154000700600d942d40d1080c4084520340940101302060348610040000c1c0c65000081c12194980295207040d600d281030300001d0a007680162031071340038580510703506002c9440880c1241c1522200e85c0201c0300340b513060300012403c854a180182d808100d402080c40715084020080003100d0030346003511540c0d551540d0850803030086404600540d001000015012003965200b0851644a600c2c0010300204000104188201542049010407000024050705400001802000b012410025403424040d80d0105245540c9458180607107921103036a0914948000c202014415a955030100305044102c03000c0d0107030000341c0f13103007 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 82330496 1250 82329246 82329251
    0x2030a02091815030c0603040303050c04030602121501110c0f1207090e25060806040905030a0206010501020c120c130603050f0d0305010f0b190513090b120c130b03010902040c03090501 81
    0x801e00e05020507501c400030f05c01850103055039a6601c1c140c0c050100217244011151081101000151040c406041e2003201c03080100307803034582841601d401031526001281441113a43c0e000b6000c800005000c00202d80c00c1d140100040001800300d422a40401d810644a00642c10b010815201c05c0e0700404011400f01d04862880b401e40352003080320100760205400c000c0000e01c06101450059006980040000c0d000107810000c6840d00c40c115045055003d0050308084010406980c0c100503080c20781c00c040f1460740461000b441f000340c0c2d03954682c900c0780c05028545101120340010782e11180003103403c5003d517401c8160782c40e0b00c83d446003050303c42c0c000441d1800c8008a0801d0100c1442d00c00d40308503001c682d1038648584c4a58088228051040302003080410402c08a00942c10701103004002107138000c500c5600342d00c104528501f08017540312042d80150000e10060784c0f01e400c210543d14070070318000385031401c800100b40074142d4080d020350041c2c2004400704555600d64071025290b07020300000c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 82331746 1250 82330496 82330531
    0x40f06090b030712020918030d090302060411010201060f060c020411310308041206090c0618080f07060f020115061d0306061513181b020102040506040902030a020918 73
    0x583c0701104061402035041000d105c001191f1041108040451441c4402100c0c20009042100e20071345645d00400c600681201050004020043c03441286645090000f400714500f481c020105101e00d6108010401030992300d04030542d22250701c212941c1c3d540c0076206990b001806410081e28100901d00e40d190484885210f100c01202003440303081e00c1c0d0201500e46824500300b5070825405a43d5401c1d20304643e5141480c0001c0c1d000c208140c0100040d49810104407404074400120b0130f8141e2090b0940d40001541c40001c2401040381e105450480c01d21030080c0c408814102d005240c3c00b207425059400711324001c07801035007185541d0140215095204582c4801d8018191138440c1940c03003541002d210580c1000c2e858a51025044182180c040d0650155950703400640100042016070f07081503603814250860f040c921803104e04201340c1e0000758901881d04010600d41e00c11445880d03012940800404d0980c0301340c0c0c04880d11004021301200c20f403210046070044624040c2d4180b1940841c0010 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 82332996 1250 82331746 82331759
    0xc0c090c0906040909060b1003061e1d0c041d01030618171b01090809030c180402060703030e010912020706020d17040f050d03020a2a03030b040f06090b0307 69
    0x407a414608040c0240341444c1c40d004490010308490300c4211112030f15542078852035124040c46ca05d8480840c0d4000c54018500b101030780c1b40702e04803c084100d81418800a122510b4120b4408140d08a1140c0301007aa940e07114401004e070080e6000b144180700017400003002c110749900143d068074090a010002d00d00744c04400420300c12400c5006142e0b00c4c48036554801c50740c108000e0000c1080c114141d0500340d400e901c1c45030860ba01e4800855aa810106a8a50f181010400e840c0003010580c1c1408115400c180c515006450081000b4402d0b00300103885010503100780c120864083c00700d40203000f542d0301494905484182c088170a00140704801000812902c0080c6100c07010300c0031780700d00c1c0e44840e11034003034104004003c2083c0e80020442c043d80e80059070800c281160312005680c0162600e80c2054018154a00d280364640354400da0b04000001542d007581041d0381c1585801c0c0040c9802c0360f080031030003034414803002c3c1610701d16180e40010b403500303079810007400d1900c21030035101030644030031 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 82334246 1250 82332996 82333021
    0x2010e010305042a0503010c05030a0f0504081215040513030f030506010f0c0c0803130306060b0906180307150c03030b030102030903070f0302070b0708090306060906011d150c0c09 79
    0x3c1d4080c0007031000340003010151420421446810102c0381c11030780595200d00102c0e0039507580031192400180300004025007280b0903c83c0100c145c1020300180100e04180d1140540c5002c1e00c4e4641c5c40d180d9401000c108005010900748407003d101500034011880c0c100c0803540740500b0040c058010820500d40c02502a10078882c0714820b6105071031302103040c40704d40707003c917040207039100216000c055900011a11940400151100302c04240860403003508600e440e005039030640d480b400d1000c84c2400900b01d42c1e40e1b18416500d50a041031071115204440d000041d1803c00316030b10144944182d0004900407551200111004a0107920140203081c00364003890701300e10007119185c05a420600c00c0c40b001405041c0c000c3c140c4c40c0030340b0403110300a443d51142e000d84d41c4001d004807001e40d000039090034181010300903030340d0042c0103c030f0503078040c60001d0020f01261019801e000501d100d2103114011503455440713900c1c42c0030303480c240a900d80e006608442c0e50b80441c1ca860522070322000b400074040e140c041 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 82335496 1250 82334246 82334251
    0x180601030605070807022d01021b0f120c03090609060d05180f06040c03060c020f06070302040e060613051002070b070503090109120f0803100b0a031a0d02032a10080402010e010305 79
    0x145004802c03008118100c9000003010040b407d16540801c0f040300740c40c1000d1603c0070700c0c030984030103000e81d0308540f42100d240c4141c1c0751410000c98403d001d01130100320040281e0b0388098041c1c0344290340d8201500080c1c44c501c100a02c01c09210320b4941071000560204c0003114811100c0c2c0110741c02484c00d041c0940d603446013224014501402c008051000580d10740004211503030900444100c2035006441e281040300c211040000680d002c5070412455091401c3c99070003a80686450f440d1540100e8041c981c4003070b50181901501c0085420a0050b100708248402000309040300394807407400d80340a544a501429000d80050f88034000462409460280ca0010a138451004614100300d85da0b030396040c0d00001d20040f00c4400a84000a003004442c00901110066640c00104101803100300e05090150b8036042d4000e064084a14005880c005658104d8010005411000c50b541c00110044110300550361368200c01c0c4410f807051940d40207001070740102e05c02d80f1940e1200d003945d0011011107504 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 82336746 1250 82335496 82335523
    0x29130e070b0901020309030706170703050c03071404050301060603050f01090c0c060c140301080a0501050f130305090f0a080f010f15050f030703020301020c07080f0a05070e18060103060507080702 86
    0x100c8000c0107a002104000c00002906006603070403c14211b0010f400e0401c41d034480008075414488605c0c18985100b1042e611086c0340c02e041025081191030301d405800014400d030180950095031514549085058800400004009001554541070010041c000603204804020002c030b0002c40c03e03813058010450303151900d5452500b91125030311000090308010503400c0503c1500c02c81d91101c0000440250f003e040024000e0030404924074160342121001016600188000070901058001072007100300169018504070b6140c4202e1000220903105140155502043e40140001c81850100d040c042100c2a40001c001119181c201a026500a038121104042c88100180500c0c640900b00d2074003100d014040b940c0c0d6940320360119003240e06c003285c1c0c5812540103600811540d001000040346100445008d084200055500e031683c1d04c90701d00a007024500079100080400c041c41085c1749002444004541036541c1d130303041580081c8030680342100040d0714500000d98080c000910300d04922003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 82337996 1250 82336746 82336753
    0xa030206120a0204051e1305040305031303050903010504030c0c0f060e060a050d051504060b040b04030809011e031407080f010306110c060f06010806030a0515060429130e 75
    0x907032003825508480101002111a030a00c4082001c0c0c035002c200d50b4030355103c00c20001c074183d07040b000c01071040d41d1710780e28080c198106010400020b40c8441a01d421100000c4088040d041034a0150b0b01d60041e580121b802d9032a20082100740365011000d8a20580100182050a5141c80c01e02c1014502c5001d05008986e21180d5041113051010080c8031035011440e0180c2080510380494054410503031f40d8101c64188440854114601445040010145608003900c1d041c68490182168001d602c0050038160011882681c1d6074080c214040400b40c030a022441c0c03100074008080c2c001d101c200b020016240c1d00800145596000d0408180100a645101e24090786195144005840c1104080e00a00f109114102100608000541c05041060780403840c6141c054001003081070003c1080d44650b01402c5a03070701140e00461481f1035202c0c4c1c0c80140d9039541d1903401140207003420115440f40e0280c032041d10968a0f5001500d105c49401c03c070303402640760081d0b50040f03050f0b618082d03e40b100d980 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 82339246 1250 82337996 82338007
    0x1030b090304080c0d0c261606021005060301090218012103020c1003110d05040b07020606130e0a0b241203091315030c1728020406030c0602010e0106050a030206 71
    0x14006952519040c4501d05400c03209841d40c0148048140300c241c0019607034407d0701c08640300c2c034003449141441e006c0d80000300031407807070948004e41e2041480361011036079035034102003140e40d103080d0045010283c025008804242c908402c2c0c0380f41000910401c64500317000000f60319590020302400703040a4050307004102101d005020000d800b001400d201040c555901e009001317041203003000c2c03ca0028560300004451526040c0104202c2000b0420300440d0402020001240c2d20300400e01d904d586a1030300001d442c0200c1449520f04002c00d2070190a19001200f000242c450444501d1390b0347c480c10300081125030042c0280b00c502844c51500c1c100e203030401d000c0c4070b1407820b20140e80005103e0450010070424103403450070609060030b030002d55148500340800d000c000b032221031011850710342a0060540041111616840c56460000311101d84142d440c1d503001d5540f2500280040c44e00f0407801d205a65603040301038003c1c004580040360759400c0040000740d03403070b00300b40c2142101d40180143c1d1414 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 82340496 1250 82339246 82339249
    0x2060703050307020c040e010209120c06031303020102090d060e0d020d0503071202070c0e0108072304020304061e0605010f1d2809090c080105040201120b0303090d0b01030b090304080c 81
    0x180c0000f40450210304c030782030542d420b980d128050034000c0680c0d98001603842041c6001d010203008480e020303451583c0500d11030441350b200c00c0100c0386c2c0b000903142e40c44280f942c00d00d822406407050b11903160b4480060507494080c0941c6600c0b01540c405031804407502c0943c182c0c010390f26000288400b501141d4148001a0664001c01010319054008140107281c03422544e50039200652680202c41303079044102c014841e040c1c0c2082040302419100120803c00c005070b004800c0700c94004000d003400b50740c010011808100b042c1d00141361240601e04502418040b420301032000340402c1c4242ca0008000019005915000c1c010303d12400b00300c40b40d4104141d81441c28003000b0314034804084100e0f007150a1f60100c280d030f0340c449180603080e00c1c40301185004640c208101902c40301e8000070120303407410086c040140c0c0c102c0c140301010445080041000d01900c03000a04500459110741d41003075113525898100b000d18510306060300e114090241c1c19441d608401d903502d004d41e0203065101d900580b9150401d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 82341746 1250 82340496 82340507
    0x6090601080a0605090c13060503150d0f02180411040b010504050904050c03150f01210303090c1a04090e03030112110301060b0a0807020c0402031006030902030309060a0c12020a02060703 82
    0x440b03070103010074843c1d40c84001c60000c40048500d030000000c04124101c14014030340b1681d000303110f40d207403032429403e00c1162040c507a07018002180c402d444481c20003003080303c410f00c0503003100e4000304007071036000031034140180d0134a080383c0c102d5551070700aa65114a10b030521601c1003400d0107944090034181460180b203c00b1201810540d25131144010220642e901001240f11320120311021200300e0610b800d0300b0300c051a040e0480c1403c1c60f200b0a000400803089500c0c00d03401a0140b42c0894400103904011a910701d032504007094000001418094141c22400140211103c00e0790401220400c619441d8990000303015441c0c000c01e52080300d40204400c048401c0c0c101000400014080f551038907182c4c1c80382e110132003c2000c5400002007042154040c00020701040017903c2c00d45c41d500c0c5c10403003200b60351107a000d104281030380c1740c4240c0e0541d10b013042900c0e042440a001c141e681ca6030048007505080d105030003294004050f54004907110301c0070400e91200755000c0c0c0740508003000c59030244d44 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 82342996 1250 82341746 82341751
    0xe03130509060312271005030a0c0c0c1205061326190903020909071a0a02030d090804181503030c0203010207060903051c020c0304090b0307030614010e07080609060108 74
    0x10f06201d4440d502d03054040420050441c03e14a000342401030010b220307803841c40050382d0005449141c91070002c030412608441200e0707001103011000540200445829541300070040d43c0544900212035010540344603e01c01062101e000e14210303141a51048071285a2006030316004101c0c0042c050108034000d400040030340080f000b07118145c00c0680b40c080c0d5404a0203102c0001d4001420a5070401c2076061800020b41c0004080014012139410b014603030500041ca49002290300704006150300d02107100f0320545541020704d400501115480f400e103103010f03030014040d49400c00b000804800680c885842075000500202d462085990300d1900c09070b42403441c1440680c0c055408026a600041d503912541c0a894800e40700c443c1c03070b424084110700700ca108050018540e03520402225109140010559084940f00341c2c0108400300440086802d088160b80000d090605050840c01264a082c0485040c2c89103540c0b0520b15649182d4101c5141c14143d400c10340140004010803055481a0903566 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 82344246 1250 82342996 82342999
    0x230409020a030f0309090f0605090c0309070e0c0903030c030d0621080f040810050702100903021203060102030c0d08160806060909090316031e09030c091e0c02010902040e0313050906 80
    0x80344160341b0a44241541d05510100c2112075655000b071102d07141400f081c5401040110681e41986444203580307503103d6040c000e4408952032800091504010b42040320b11401000d030580e5119101d500c100c0d603407074101004003e0101c1c24410f02041000f8420f81d2544000d07104085501058004c0d181c4c110213034010454080070030b20030040031500342c1040110a0f03152100b42c0b0300041034500b004009007040e10b10030200d03135543c0c10003254030301207640003495a6603c09210302e03040d62501c1d4180142d1551141101c103c00500407011030f0341010b40c000c1807962250400780110610130b08120310468001c402100c006500280a010742502c60800b90b1055500103410011646030074030708112404ca503851950304800203142042c084084801440300c2c81005a014104406040e0642e41c07001500140c074014803884507507604400c4862150300c0b8868a41300700c0003030304000d1840740035002030181410080a80c0250b060165041801c00000111440703240c000020504840c105010400d801e0b00103824a07 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 82345496 1250 82344246 82344257
    0x40b0408090f06040305030306280506090f18040b060603010b0301120f08030903090a0806150913020a150f080106140f0c0303010b19030621030c050601230409020a030f03 75
    0x1840320f803540c00050020318011801142c803803030046c08004107c0198400c42e41851416140480e14100500c507440a4840031a515500c0304480c2c0041212a58500e400550000700036840251000c0a001400c1c065400f400ea61003a41d83d442d428060644400c1c881c1c100c980104100400104003010b2010085034410b00320030120207850b80711202103400955a246c4650000190310b05545801902440200b40807800f8202c0c0b45030144030403508e200744000140c02139000760b000503074081c00c6800e03581816a006002401840c0c40e041101810210300c102d40000c84c01c1104003106641c007860b00d4a0403510a60f841c0c42c04044d0285041242c1c3c0c02c9012a6a8510801c0c440c0c0030500d003040c00514064200aa0542d8642c08410b08550303504400b0400801414030f410f17024481c3d8041d0780194541410204032182d0071013064034080350310100200001e031940c0511b00000c112400b10284104a080000d00c0403025034085c5800c100450300d07403c0001758010840c90007000003482d00c0d0504a241e074000d003002c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 82346746 1250 82345496 82345519
    0x1b020906010309030c050706030609060503010b09010b1b030c0a0b0f090a0311030d05010e041b030f031d100206040c06090605072613081005010303080f0414030705010e0601060503040b040809 84
    0x4003490700c00280c2101c1e020a82b20402400340315514414100100300482c001d02480b03003e180801c0da10300f01801181030040c400549400c03518030200c10410002020000c4903510200a8140c0303444080c2c1c0d0008407090380810f8003041040110b5407691b8022510788014102800d02540c0968130684080c11380d054034001030041040090303e501c15035000300b140d03c00d0000103280602d444400e0841c1907140c0200d00c0c1c1542001d00108052580b440410b6034182402c040d1a00050035001250300254002688801102008040280d0118245003c1c910448075009189d03203071003050b20040b0880c06500000345080c060040803072039604043c80900042c00c030031a903502a00c0d004071031682c405101c00440b01030343c00d0b0070000b03d042080380e1140c01c140040108159411564001d012120142c0402c03025403d402c041820300c041c1072140700f40d07044110103c82e80c030b02d06881e000b400b901c90102c4e0b8108500030034000103881402041142e1089038004984001550b4594503109d9680100e00f045411100501c030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 82347996 1250 82346746 82346753
    0x9010e040e0f011b0f051608040b030a0f06090b03101e06080d020f01060b1803010e06010906080705030607050a0c170706020403050d020106030507051509040204030f031b020906010309030c 83
    0x1040b808009140000c250014914508442030003d001c0241c01c01408200ea8690181e1110594003404204d440740b0b00e102c1c1281c107109a16008a42000b02400d10000500030001c01e2540040301c0180758070010312026603036199400031620403000054042e08500c003100b43d40c030703015030081103010030f05603816007951200c40302401210055007242c000755201c181040055501081101d12060050000b80311150a2241500d03190184000302499440481500341050750300303400c403201c06400b1008540140d030351004200007820052259808500503070750046001d04020800d648a03e8a0303486041c50b01c002803000711401c00e0b4548042e128180101c40100c103600c20000100340d05c500031000035071194114144542000b131480b40742000c2d60b14111080000600100f022421640111002e28100021012a03100351103408180b96203d0305c0003602000b042048441a841c01780240d403034144620184c24622202400680044d50080c1144002620f661094206102203403107072601c020032607a945d0303 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 82349246 1250 82347996 82348003
    0x60509070c0f1b1a0702030d05032d071b05120702120f0102030a0609090201090306050c04050901030f11010503040b0a05070c080c06090105101206020d020f0f0d05070503040809010e040e 82
    0x144000c690310000c078020400e0034880103503850504c1a03024214504141c582c002992040b014500c0e00a0043c007000003241c007840f16095403480348092120301d240d94114181c07850a503c0032a400350100344481804800844e41004545c211a4071074000e08202c9116038552541e0340007000102ea1140c81c00381002580d050a0081d000f401007950005030312030500b4a410000d5840740c0d040900782501e080b50890150ba40820140b08488d0071040006a603105c0d000045994401c41d0052a0410310a800000070001450100c80c1100e010b04c0128a030070792500c004503170903c000d035030180c40d01244c60007081100d951580131503040906810130900340700c2d070b42d82c1c1c2e4031042c0c02c0426000100c4e00010104205c00300d003030007001c3d4044000803d0401d0542400030100c1c00c80308c04640a0107142e03000c1001d4a001005a04803580506086e500b143c03600440c0e03600307400340e611948076505c0d52420500800e8501d070180c3c1c25640629801440d9a00341107440313004403407036140900c0007a4007030380310030581c41c0060091 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 82350496 1250 82349246 82349273
    0x40b030c0310020a091202010206040308070318050705090a06230619030f0b0a15030b0307080a0b0405100603020f0d06060b041502061501081803040e0c030712060509070c0f 76
    0xb03100240c0c40d0050301c03901909007146a8041e0f8210340038030380c4100040c1e90101d61190b10a502d41824000f079254824218010a441d01246c5d411210b030840480070301c10002442c000319a002ca9030381c515030781d44441e080286c401600c540341601380700405401da4440c2c1c030707591158001009800c003130505080d154405e0300d10070701c2e41c0705001281d078401d02441c0105883c0107d400c0d079030055511003041d501e44184c4440c101c55020030b82c7d0402d0341e201468010303668203101990040248070202c034002c0402d81010400d900c070540303007200d0354440d111402038008000e00888040383d800502a803880c02d509030030303c50750304200e03102140e0b859510f85010901c5031005000e007018009802c500c001049044a0181ca094005005c404a040440304010710607039001010310f501800c16546170b1030a1000020451850042e600104070f044c6041041002821404002d18840c0040e40da039084a88207070031030300302100c11900a154208809100042071680940c00e40002c16104a181020780303038064a5041080d20344 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 82351746 1250 82350496 82350523
    0x60708092109010f031a04020702241b0a0309050111100c03020903070806040209180a060903030b040c08161d1e0108060612010504050c0c030a0309030f0914040b030c03 74
    0x2290101e070b83d503444510510401d00701e040c104001070500e910103803a02c1e040c0302c5851250b5000a004005c6494610442c1d960750581321a2914820b55080040c1d902c2e044103d200d0b507044070101c92000014130009040c80e00d180c054584040c1c0d60306040044441c0035031004034410902c21150290200c540c00d100d0707041c90100c035980058a94140b6010141042010340c40304849a00c9207040c03102507900d00000700e8002807041e500030010106e0000340b5041c85c4484201500c810f2030948944181501500032100001084508100701c0341020003e4504240c02e03038100074128080103040c2c1007680144582c4102184070120201364841e2000020f010150700e2000401c8514000400c10403560440c02d22074004d00219120b5050424040c1c1d02c4034603820521850740301eaa00c41e0045a601c0d2071900881e0000d07607441c4142c2c2d550780c0c5100c41c084d000c1d02644008600080d46440ca24011510030700103207080c0c9038511016500703a1039210420010f0a030325040198103001c0c007020801d09690801c50004c04818 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 82352996 1250 82351746 82351813
    0xb090601030318081e0a0807030302120109140420060406050c0106060207080325020409050109110f06161a04030207060207060201110406030906140907090f02070506070809 76
    0x46103801082c552080f98814081103026a0a0218600c0403c0c40743c203a5074103821102525482640f898034007078807640054843c00e8009000018540d05030002d01e01c41d10062454550341e6642c003081c40480324403014901141003060041000149540c10345902c40740c0320700285042c24141c43c0003400a5005038400004944000340c080400c071002e00421008064038006030181c0e40c606807901d52648511400144a90038860071030705d50b80c0812048900c1560094020800407900380741280c000c001b418401ea520502c0c50030000064a4054034030300c00102e020302094101651001604400001c1071401c50300c03100300307200400e081c0d00c0b00f42c2e1191185000c3c1e401081e00c01d1800501034244042070304510b0071641040381081a0300034030340032507007103031000d00d0000754094190904000500007014095980304441c0d06020407010001059007da40350010100501a03029a09808038459444014075035000369000420440c000c406003a070000c54002560010103002c25010b5803480085940a803411 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 82354246 1250 82352996 82352999
    0xb070c03020c040e0703030c031823030706230906181801060f1419050c010b011110020702030a0b0109061a1206040213030803090c0f180105010e0d0b090601 69
    0x40e41003148203110142a00c04104c0381d0880350056841c0d0f0385500000d818400861608406c051145521400c41c00810046103003440d140c0174a04ca8803550003100d08030108040c8840b004c1d519001c00d0141c1103501c00e440e0300304042a10880442a003d125900e0102c60a05120400241d240c42001300f0f89074001c8540d150a039400703030041101704030390b078601700300002580380044c4141a080b80c82480052520304000c0c1203c0512980c2c0d280074420012240e1800c045140001013250300100034003811a1079000174000b4080601c0112000624100540c005500804296082c00071683c014030700c0c030303001a0964a40034a25101c50300200003e070321040c640d5944000c104034030505236175941101203419000703a2401018207034000c800c16000e495940b24950008200908003007a22094006551101c0420f07100d2400c04c4405441d00c0720340409600404105214919920f050000d10000484001b52544164207010044520514804115800861050084000c40d090402e110f00c20400b00c0001c2100d517 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 82355496 1250 82354246 82354253
    0x1e1809060106051204021318061401080c0d08090a05120d08010b0703050a0e060d0905010203010e10030c0306051b0403080a02010b060c120705010204170a120f0f03020c07030b070c 79
    0x1501640514200101403000b290348024021565030065011504c03030004c2201e80e5108001001c1c2170004082c4480800e02300400c0003104d070050400c0c0b00a00c920f071061a070780c40c10607c2d100ca030030840c11030f400a80c803003041c000190000041d102303180f00500038141c4951108081450100c2c042012035035030b441202c070040260351000c00c99025103000080c180c101505d03541c000d400f078040e00362201c0c2402a00b01c1406a1034450b50192500322141c10014803405a160805600075030082c01180029503d40c0c0c001480c2041c540254001c8a5001007d42c0c2c0d0680b554540c480140030183c48280984044042d02080d06614005040518081c0c81502e81c0d13403610220203421501c41a00441c002c0b038041c81254803081e008580206041202e0340000d50f00c0c00580381550080c030441d0000001142403501c8101001400201d607d4024071032417a08000340c2501c80700f5501f000564002c0d0000075403004004940d944660040d100091100701183c003000e40303da96202e1060002c032040741c005014400b0003c2171 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 82356746 1250 82355496 82355503
    0x1b04050c0d020c150c040608040b0a0905010c030606110d020715110a060608010b04110406030b1512060306090102030903090607030c02041a01091205030301031e060608060105010914010e1e1809 85
    0x38850713010282c46c1c5450090080c1c01e58000410141103d192203001036400116904034910a0342e110000304882104008080c004207143d0044000042c0d6944408503030781c0c0e000900001c405041d80040c500c40740340554401c030a0048180707003000c005d00d42c05440054001000201c8080e480703a01c1c0415a5802d05840d5803c6614845c03040380325600f020107104998031080704603800d8a1091030301140b14045040441c2c0d80c88845140303400e0031200062408204442c94800700d009450480a480c403035120b0000300c40c00c2c3c0c04150362901198004014580c00b526003240100116480fa06110200011640008045030b10b906404036440c01540c850480b00d40e404001000540500d090f43c20703031002a500c41517070702e0205000c02401c0c40355008071078485100c500280025960b0141062099a8071400d1203900c6e00c03c00e01c51540454040100420041c0c0e1440e04040d041d42c5c180e46040040e8000700030414500c542440d001c1e00764801d20600078903a181d64100803503281d100e010b00c0740d0508040001614 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 82357996 1250 82356746 82356751
    0xf1a090303150103020a0302090a1508071d090721140702030a080a02031807030503070512090d1112031201080c0907021504150c0c0b091b04050c0d020c15 68
    0x51500304008200c03025001440d0900c07400340030310b4011386402e424241a8024820f55116950040803502d0000704000f1024a2159021035581c500c4d41c541c0b1101e1050f540800548841c00d0320b082d41c10340d07415141c201300c0a0390740e111425141840070354004e014010040813144441c1c1c5801900e510403808541d5160000303d40028051000b1460001c1405000389041009031850303812580000209800310709514030f9820551840050f1100c0300e50740d2610070364a50100d072088a0070b00800c040015000501ca09646106001402100d4a946541c2c0ca50981d0301d090400d056204000114003044d0a41c00c1016060900013085d820001d541000c010f01e14080d40f11446030700c40d200c3c0c401041043c80c4d020541407041150040040704940340c40c03030315201c581100f00c3d840300c62a152803060540075511071100140240030390038201c131a44800004a4a441c3c50a60450003030082000e01e50301030505134401a800300c00141145d0802000e0744814050b40d005032458451070b071005440480e1003003c0c110498 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 82359246 1250 82357996 82358011
    0x60904020c0105061203030601270b1b010b01030504020609040b01030f0f14010503011505010f1e030204060e0301060305030a0c020a0801110a0810080a0f050312070302040807300c030f1a 82
    0x18154032305900004d28018101515500700c10074544600d00341d048401e0070001400d20740e4103a54896940c0c0301d030102c0800d412480302e6801e6082c0415600ba550103031080c94011074001d40520300d407150913005e10000e00b000c000c0040c10581d44903441c1d800c0b86014414410742e26401c500c0030a40540104058a4200341038000600c07907450490f1070b030640006071542104407902800c100c141541615802d071002e121a58402684140842d900c0a140d9032640c01042030320883d17200c600c2034040780f00074103080b14810b010050040c1d1041008006041c020311010283c0c070b01c01801141a507403200852400e60710002d4000141c1231020604140b2242c00c2441103a014850301c50f1200384074644800c40307a407201d03c400e0240251700c0b00c0500c04184001031013203500101100103605130034108a84000d0080d4818811300007203005414020030604042414100010b0007034001950f0540003d0f000c44060310000030403201c42e003140800000280c0b2440000101c1030181010030000c2c2030300881d40051580c01020701 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 82360496 1250 82359246 82359253
    0x30702011119031e0911040e011503081308010614010e01181404060305030315041a030307141e0d0201060f060f0f020c04060b0c0714010c060902060904020c01050612 73
    0x40801054005024030302d40c50383c0c603011640d03e4140c0000511480800f01110000741044400e006000e00c0c3c20f6582c000d42c4081c1e400708514850515014203d8a4001000701900140030003080410300b900060059450200c2c1d40d880950b03038070070340a404c54582e0307401200420002d03d09102c55680040a80d2181402805d003100745c451071400540003115a80a1040503000118070558552216840382015560003012607a8a0a080058030094541c00c00c9140c455820a0040030b074000c42103004040e001c401400450904959689003180035003c4a1125500c3c81101300040c00080c24000c810002d10104000c0e100505980301c0003400d480d4190001c07072002c21780b501d007001341d150311881c0e61440c0205d40c80c100104a604240c01c0313040c111280160307035100703003444c030003141800f00c00b0300410b1050501d0dc204c4a03142d030b80b031900652041811381e029000c10810341c0c460020486913085001d10501c01441c5070726000310200098100e030031804219071560354402c2042541d003005052000303048410b5005 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 82361746 1250 82360496 82360507
    0x204090f0c030219052208010911011103160501020c011b0908010203130803040201020f3a020c0607050a1b05040506030a02130b010c1a0f180709020c10110307020111 73
    0x1d4980c0300c4c9200402041000502044108080c0034080c1c855244510324110b00c0da84c03158054060403080b88180c500055001480c2c40640c0580001e090005c9031b400074604084110040c002c1a81448100f03807420b54003001b80c00b0003440e00303100300c8242a10952115051001d10b02e03000706400501d4000c008141e1040051001c40b00517000c14010143d4042c0000fa03490f515440100d040690441c864001445071980800608030a43c005400c05402c454444170081030046c000c1c40c441c104800450050f80041441e44039600f005d10003455424044c200f1905221030640e11a051441180c420381148103814509010a140500407640c2112041700140440121500002c0e241300d02c195a480120707646041c1d400c03142e400780780000000360f0003034107658584440000340c81e5000021103540241070486000903645000740c0030303058240c003030040c01002a0390a12a190303000750300c9003090041c07611469281d542c0201480c024010000c0d61140e2050b01d03402d20180183c00e40d41c05881411404005011 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 82362996 1250 82361746 82361767
    0x20a0302040c0c050f07051201090b070c03091a07120815040203060a0504020f0a090e010b030a110d0f0608010501090623040204030b0a09020a170a15020d0204090f0c0302 75
    0x105094a030111400105641c80c07200940c2c458007803100c000d1590060030380320058180041030b180c04070b900a03940001d111710015042400c0360003c03680107150320320381400300f8152482404000c45d030f10302c01e041c00003005071070380c003091040311b02d1030502080201c0024425040010440e90701d4281d03901820000c03d941400b10104241c920302c2480c503401280d002c400030b2101c0d40e42c101400001c0401a00440d82c400070005989030540c0600282c1d0085503229400081d0142002d0794a81201e11070050702d4116141e4440709006002010610303041081e00303018000d14001640714001691208017400503040d481c00032040d0039550141d205408161030b183c400c0080200b90501c000700c0c111070000a5035507110010009000780941d80000d4031640b51201004030a845070f6001030a0303d4022528a44816500d01c1d40041d4040d8140408843d50800302010340040c02030307034003950750036150080035040c8025100d00c2d5040b81c2096002403d8541c0b41c1c4405041d50f5003074407071056021f1643c641540b91582026 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 82364246 1250 82362996 82363009
    0x40b070e011b050106030212031207050708040e15011409030705010e040e01090c0e01080718020901170a09110f01091e0e0c09090717180f0607021c050702 68
    0x148024203000310040c0100003603115031480348009000044020440c0b2850410a00030005800304034001c40c07004102000045000013543c400d8000400c40da00305a99100b421a540d0300b0000040b184545c060102041c211072102910744030b0302d0460384c4051901c81c83d000041c14084610365407001c0090402c40e41c5145d031801300d12441039480a0816040c541018004500186942d0b003104440394138040c0d49100300210142c400040719003c0d085d00740e880e6201c050950700c0d04160300c924440501c0e140380440100100303070080d0006400c14142032651201107070400301525011194500a2079660784288100000c84010441095059171a1514021090b002030040a60f038003680390040460031010043c4031520740d119001e4109070441001c1380c14030307020840b81da4125100451007120f041c0000b46a4074070952000740031101c001d070303440020b0302c13000c81903142082c1000864a40380540e1064041b05c0b001001518064003065000f0b20b40002810300383c80c210085102c00b0000c01600b0001c84015035a9070 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 82365496 1250 82364246 82364251
    0x2190804020a051504090507030e0d03051e15281e05010c0c0b0a0f09090203040c0b0a021e0606010801050109270b0d06140a2a050c03070506061503040b 67
    0x103840c41c0f18800361405400e813107401107600040d0582e0030300c000c000e8a1545a00000141d494541c1141d0f22960490000e07030540d00c04503011502058160030703401d50f480f070075620650048900b107144480740b0341c1c02c40030480a07511415020503004030510b01101e4085d44c00358200c010700c2030640d41c1c08241e00000441107020700c42c0c80ac15040111010300e58003404680070343e40c0002c00703941c0351065566240e6407018081c81120803265010a0100000042c8040d2500131644126413002010000c5810b1000710300c425004207044000310b10034001d0000c0e01c0a0f071140e407080d52141e40d80082100345440c02c00100141016080141000001c000c10003a480e86290301c0da400080b020b21164075180180d000c90300910300e1340c00309580440c4079a008001d2118036409042e40c0320f4510402c0b91965a0088000c0035a2420507820440e02501c1c0382d486005140d06405207120651450690300d844a1100100c0c42c41d0440711055546030090028030800d49829403a1040d01c020342440b113411417400b521a8015603400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 82366746 1250 82365496 82365499
    0xb0a0503012c0103110103060e010503060a09110a0e06040c09050102030f0a020a020901060c03020618030f0702060708040e0a05010e1504180b01290702091f030203010c0302190804020a05 82
    0x4002c840c86042c042c81540480121400941810b59a500d01741595a0507034007003818046460100c0100d0300c9411140614140c901c041c00419082d161441070304000d08805400355612850400da140341540e41102c00b200400fa0219440241c1c2094800c0100300c410742420407040c00744412081004d41d0700030040d0740c4080c02d00381d00e07030703441b014007040682c102039085400950140b28070001182e20764020240d1141a4001c3d803c661709540da00145ea0b04100b440f80040c8941d90007401803000c84c800500050140710300c064030f80390500e400c603900c040c0260003030b07008444415013000c2042840001da01c201030060103009a10784007400c003606040e00e8003200d0780b0303200c0c0140d40311b16081820150100b41800b002d030340000f0031141503948580381c6032010351042c040000084905032101450b00b9010540d200c00c0d03002400c00c8410340f940c0346034000c056000113044485103007510001016a9083c49617001800b0700c2e450259945004003d40800604160070320003d000c01d003010320015880d06114041613030b80 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 82367996 1250 82366746 82366769
    0x702010e09040602070602120403110114011205030d050a09020118030c090f0902090f0601030e160e0709150c0b1e0417090306090114010e0c030a05060d050d180b0a050301 75
    0x10b480c1020b0000c0e20410202a00c12800041d402c81129102000c051107180283d5940142e05103810505098548440c00d19100c0020600140090a17032003003504022131147d0116480d007184541000140c035411100c9030309440c0d07a08801c4040d540c0005488100801c07071a6014069030456036084802000f90060300c2420f60340b5081030500c200305500241000781c0052002c5150300e01030f08000784124044070083d00207401c4c0b50b02d40c505008009810003400c04c201003004215428203011001404000f001d4408028004100044070942c080310a0341e6407145664542c094a2503090044480502804800300c280c5c294109201006203541d030960080c0c1d20010120200c6015007982d01d0f140600c0007816458000c0509201510b1815030281c2c0507880c0310080c030b42d0079aa80c1c0064080303411080b640a006a00300b003002601d01c003c01c0c1c0c085c83e07000c031006010352156100e507203071580352000561403a404540c1070b010031814401500300d00c0c00200b1a0ac44241e240c00c1100400408900061061084000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 82369246 1250 82367996 82368001
    0x1c1b09140708070f030f0f0501090c030902060706020706141e0c0406120e0102091201060f050409020109031b0f030305130504061d0c0d110307030e072610020c01090201090b0702010e09 81
    0x178405c1d0003031090380856040c14440c1125031812400140401e12514162a2a240d5060302035402030140035002c42c1c0040c4042d00b0700210b5104e0b0f402940c4020004c5a03810b6841201d4462003900d0f0b40711600941004c84002002d01d4000d40400f6640d8001d80250700c0844d0a010400030142c0c0000a004406a06032000c2007250b1801085070281c01144100c5a114014000e003420010055111604480030b03506540d02255a80b010b0004540726640041d0008501c100c041c4082815541802003201281881c0020300d0b0391100c106440d400c503908118000383e00010181c0c010846030222070080d01d42100d00300302c82860880c524000b5100880c00e000140328550004d01d20240d14001c0c0e80141d800c00b4003e0240c420400d12060b0305900890b01c18000c646000c120003110940064008240e814200711804583c441d00c980e0004030f80d00300c00415940c4596222418480b6003400034012460f690000811482c551f48005807807a071140e04203071032500d8140800b00160f0b030300c117094002c80d103410384010b62140c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 82370496 1250 82369246 82369277
    0xd02040f110406020d1205060105031810091103011401081b040b040603060e0d0305010f0611190506090d03020315060a020703060204030b0f01050904020108061c1b0914070807 77
    0x421a14081d91012036011400150158020901042d001c90907a01d858448850040d8401100c034180c585a0004200340000340c01c00030100c1070390707401204101c1241d1001000560703003010f68400000889100348411041569401c00340106048881100e1340642198109045203503034420155560f01d0700c4946410b1802180c85036441611a540c000e0018030605071a41840c50191040d201004010f01c25159013502e4640b0a00c2206e050350340806090395031a10309032049400d0307999400b00145034000c81d070020b2140548110001700180c481c1c03020301304030320706207980b2070030895098048030502d40100204101c944041401d140410f41c208e03082a00c40d4444c0c54203d1421046400c01040b407440000c000c014402c07001c1d2600d100b06080e51038012680c0c0c80b80e00b40450600c00b55402404501c03100041841498060b4148445407040064040b10081a4889030500344074150410484109002c0c107004000e205e014040b40c1003002a103035002130500e050300801d81040200748404000c0040c0d1b10000a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 82371746 1250 82370496 82370501
    0x80d020d0509150403080307020c06070c12021c1a0115080115020a0b0405030405090a090b0f0a1b050403050d0c02010c240c1814060706020309030417030c0d030b0d02040f 75
    0xa42c401c1002c89031301d864403440c0c8451395034000c1c2c60550142c864072075100407514011040f284c400f03520264224995142100f003409142040300c041b42e10880c45980e0355282800c01028160744c41c02080e03668950042d1244292500e88103030440c1411100c2e00000c8030b00d5907003201100b030440d42180d1046401c2c6000300412428260607960050005911006201c02e01034008040c10540c0c1d8110707028071440c2c039443d81c0340044030400d0100501c1c03540d000c00007600c0706403009546e0350700040c2000c020800405e402d55a620480d00c1850840100744046818070502400700420a160748007414640783d284d04a400203050202160703002420b1761044ad42c0a00c812070ba41d00c0710190070207105000d10135001418030182c1040b0048199400703900d0031140010351416003040703a03826048007030703c02441c2800319101c00010358130080607440f40d0712040100280c411245071003d040c0400202c090340e100c440100c507450400c54880c182204150a142d040d0384c10f66500e00b0110402d650444000901c01034a0103840007 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 82372996 1250 82371746 82371769
    0xc09211205030714030708040b190f0f05060a080c0607060209090a0c1e050f1e0301030501090201081308180f0a06080601120203100302010320030408070c080d020d0509 74
    0x244950032012003103041d0300300c00a1400b9003803503200c13074550b42c002a41d41951070000b10f914000085414002c00c010401d1080a141c00100c001004088091000c4c00c0c07100795820020080405950751000c6c8a03444154840d56400ca501202d0302240c0c01d14014415a40d6541c1b11002c9114003000901401000300381d60480784042da000d8408400da01e0f0080c41c0000801829440c800482c1030b116903405000d107002003080141010703445541c1003800c40712102c43c29400980310740c4e80703427294000030440d0325101601443c0210f118500108400ca81c9100040c0b80c1c00020702416000701d081a0054002003104007a227010241d00070000c84031070002c40000d540702e00313006801c58000e03000c41c1000c9605a400f6a140380b02d50f0080c2c803100f0350450341c2d00300e0b03004910044802c1c54046075010f00501c010f61103500000c0003400009a8158600c880c030f06088069072054801321003204001400400300050b2003180c4000b00900340c0030380000ba0102c440a0b4856044580c1c0340e04000d07000542e030055aa44029800 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 82374102 1106 82372996 82373003
    0x50c0706080903040f030b0a06080f0307020f0109050d0f06050c120105060d060e0c070309050a080d0309080c010204170c040c1202070302070506190801090c0921 71
    0xc0d81480050202110b900080000152000c0076020500286002c3ca40e042c00604004940b14211016948072a400c1d03000b00512900d40d0101105461005d501515403800300440c640040324801c4964010f40d6010707030b400c280c032420700461041d1066200d200b141c1c20040c03911411070f150007074000da0720a401456510b6006014509150001d0410f5210818010801e41c0c0c44a54950300c0740c1c001c66425461300f070007143c40400e00d9444564080105400d440c80541c45082024003500d541207082d4003014541c4403155401000411030407a24212003000085494a031510b40000b40351100c820701012602c0703000603100350341c9801d218040304160f0300e44074008041d4039220030700081d4210010960030350003a46000036141c1c403003400030400411000e103000c5121b0070042d0040c00340712040c0c11600c2c2c078502e80100241d002d60000f00000503200004482008440c0800040054242281005 = true := by decide +kernel

theorem cover : BRFrame.Cov 82194246 82374102 := by
  have h0 := BRFrame.cov_init 82194246
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82194246 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 82194246 ≤ n) (h2 : n < 82374102) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
