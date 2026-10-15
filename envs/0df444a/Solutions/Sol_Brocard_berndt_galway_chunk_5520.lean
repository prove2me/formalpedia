-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5520
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:08:12.012042+00:00
-- url     : https://prove2.me/submissions/ea79defe-277f-4aec-9bb2-cbd535cd262c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 992625899 ≤ n < 992805755 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 992627149 1250 992625899 992625913
    0x30b1e011223030a0305150904030e01080c0c0a060906020408190b0a05070e15043c080a110d02040f0209100234051f0906020c090f06030c090a0e 64
    0xc1c1c4003040c10011075107081c283d031040c001140200e20030b0700140e80200d1841001e90200169001164005c141141c0550210300c0e003040001055030f10090403680305210004e46820a01c410004d1501d4805881016040715190b0030782c5000e000480c0c2c1241c008003a03190480f82c040318000038007000d15040c482c0036103440c02c0d584006a006c41e01c502a0a210307441c3e45e650300510141c0c400030444000700d51025410310400030301c00404ca1061402c0300d0b07402d00030241026440781c41850f034112854400704420040c0701c10303007840400c441c0c0000078140e206507a01069420b903604085010580d02203988001a51050801112828802c076230b038002c203c12081500c01200304000d00c0001d1781d89001207560007005640118021560400c9500c0717034404a070816003240c1c4200d669034006018284414000b0b000c4552030507851030a05d401005510082802e0700280080041c400001131000c0c4008080c01c82016154000414a07501401803151030007000b483c1030075a080180c400401014412458091441003107 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 992628399 1250 992627149 992627183
    0xa08340206100f12050a060e0106030524070807020a0606231f0c060609050702150708010b0313030309170c0d0905150a110a0308150f0a030b1e0112 65
    0x20180c4402e407600740500c651281d00d04450506041c0ca402d1045e034060065854001c00182c090080c8440c0c411072200100b049400c5003001c41c1010b041003800c3c0400703100000403214410324001010761002050401d0b00980d03543c0607044c1c0c100400b41d100200300900d44100844c07002d06280500c0a020346084c0c01d40c154103218800c0c00749071b03018104484904001400201c1c19a4400c190704040075109403400310310285d403186884140c842c190b424a001d84c014551100c00300b00d502c41a1070340649189055103055150a2a0060610002d044030b84c900552a01c854107050107501704845040e804003a03415040580c0d014100c0316085141c001c01140034042d40d0300c2c071307451290101c1010f4410080001d59500000500d0540540c00500c182c024484d078401e40c01c0741008103201708c0c8401c6000307481c1c0c24907502d880301090802c00202c207074051054a0889446105496a02001e000c0d00da000b0990655501c40b082d05c121220301c200c51130149044038a00100d15101d966071031680d20741c41040000e821060701 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 992629649 1250 992628399 992628421
    0x5100e010503150a0c050c0604050703020418030f050307051908040c051207090f110406020d0f0c05060a09051908040e09010204321c260a08340206 65
    0x40f03403060012521480100325560b000b81d200c01843d241505100e450140d0030301041e03040c500100c80543e0180c102c65070420075414140a0381c110907a0400b1000d2100c20b26070b9001d00b801c2c4611555a08200300030001951407805402190301310440306400c070760b0a0941800003801ca040485044a42048108000609042040310400a007c007a401703419580d0a0038014001411071103005081241c4030012400d0301c0c01c5000003040600015806840e501c6807111002e4201910414004108036940f4a0280460004241103811103000d400124140400342066031400e07580d48500090350080c9008102001a200014400c4503418240da1506070348456005e400c0740598400c1c0358440402031852032405050410020f00c504804030640c01c0283c180c400b2920502c1030100058440d5081c0088401340038040214660f250102d18840243e075010703030721040300c9004103030f4168148110304000c45c0e8484502401c0c14464501181522092201381c0c000003900481700e0100ba015011713050100e01c0c00c001c1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 992630899 1250 992629649 992629663
    0xe060309010b0a090204180b060d02040b0a17060105030718050a1409011521021e1b01200c1e1c080c2b0e0d020c030f07060e0a080105100e010503 64
    0x410542c1f1003219102d002c1c0600544044100a54081300c10000a42c0c24003640c800742010303107440b4490644032001c4e1000502600895200800d10b000024100012070383c1c000c0880f9400462880c024080d80111461543c005c00150411940a0044030000c20714100881c1d001da00e980d01203440400301d903683c80c08501018580844440054a81142240804414440840d0303501001000500e440701e0040a00d40c1407100200c5118409000903180e0004d54081d1403c11580440c1c6008000003030f084c440035140390064072007030b038011100840c86001c0050144020340c468000701511010390324200e42030984500b0282d45403100304000c2c50011800e644500c0300d00b4812412642090302c0d0801400c8200520864000401480840c50003074104105082c0104a58456004010501da15070880007904049450320000d009501c206014021a41d0000d020380444545042c20070308070803a400807540707980486d00404015800c150901c10000c9070030082000f100c40b84d24000c403d5980760010581c45840d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 992632149 1250 992630899 992630909
    0x1b010f14010311150c010c020106050f04140a200d020702010825051c230601030903140903011811031b01021c090f0b04090c05040803030708070e060309010b0a090204 73
    0x660141d0701841c0c2c00c050b480c540822800007101404c5c08020300d102800d507032240e800500143d45070442000389080a400078052250116018458007044c001a0800004028a401840e64031100d4905a4084194a1b802c00c035499401007541c840d502902d0601035401100e0480c00142904c00040383e040d04540d103c05903075040341c1610f4036003c03061011100c0f6081444e40034622a0641c2d071500c4221180c1c80350b0f250108401000d0380d08952204025080080002d14843c181420030780f81c000040d500c84080ca10b0a48050019600c40480c034010030700402e090803401c1450b100740b01c503081c00e001c4101315070340040200f00c0031210507691504078103071800c071305100003409603004160641e800d0701907081c0084132518918054100c1c5a42d2003900048250b16406487c1d4044001800e00810f02c560085126441c1207080061510f85070170030965903840014003410400c541a0b01180c0042d01c501807101d844d001c01445980c4a00340184240c0c020318005030700310f214414502c00010303140d81c10b00a0b601294 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 992633399 1250 992632149 992632163
    0x30706090219080303011a040f1509080c06040605070f120801030c08011e020703140d0c0207050a060c12210605041803020c0f150c010b03210418021b010f140103 71
    0xc0d10b402030018201404d038584483c0c000023030001050b0112401c289200800340c81c20070408d400d00d50200649075035040c1d0031036085604094036200841d1103e10071182114101c0c50700503680c803a1420800054085440020103100c100040059015406544241a07038020109a03807a00c1e40c5901d094220352403900c401d40c904884854008aa002030f0340a400803e000341420b14038802d5480d2480c4841d40044a5048c0c410756402000441650410058010b00010f4030280619410040082d1044004c1440106050004a080c0c0c0c0224071928010a09540405003030030a85901c0344100081c15150241500036484d1000c590300c0b040040c50702181494168014065142c6168240b09400702810001034200144200461046090314020114000b80600005005546e002018102113410141d000e404202c948120300c140d002c80c040b10304a914014146031080076884c20750010340102c041c0c140c0403000d0700c00754080078403041d0012600c0081c0c024040090100b86003840348540000c3c04007418403 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 992634649 1250 992633399 992633401
    0xf0902030402030a150f1b020f010515060319020c28020108010e0907050d0b0f06030a031d130f06053307050a0c2d0602030a0c030e03030706090219080303 68
    0x3c5030401140151143c0481404541c170098800c06c1400e43d0710002c50201100001c4030201d180d903a042c0b01840c10074440000071b1040d401c00d444d08140c0c0da1620802c43d4400c800c0040441c0d0011180645032005c503078004815522074681c01060340e22117401030064603004181425110004040800c000b81c0c5581c16103c2910076400d0091040400700000d00d008614070911401062681d0340c2c099070b002003481008501d080345030590584040c810082c01050103039001242400021340c1203000050240202001082001d0102e000180440004950100818a000c00d4452404c22641001046c0e0300207540824840010001c90100014880b0850201048201050300889901d60040400600502c00c490b0780707141540380c0442070080c41c5c0c0581b800000d940720346148000030307005000b42000f00000d001c840034505440030f5202d201f00c02220042011180700b401c1010f0085041004441000d400c803a103d201030700c0c1c840700402031800240e2080c4075005081c4817692240002c0b0059603d600065821 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 992635899 1250 992634649 992634653
    0xa021905100e28080c010f0c0303090f17070b06010f0203120903040b040803031602150f19020406030c09080a081603230301031a011401051c050c03010f0902030402030a 74
    0xc00d031014402d50b03a1061040854904144040c1c028800710f400c9040c0c0452490b01c0c081502c0d203044501c0d200725050205026070a03207466040054a42c60b941c04d4140031503181c00c02d141800c09402da80b0384c001e20542e03120103140700c4a00039001030280f003813180b800301042d9200d107401074070410800c60484006900402880c0308843c0741030b940c0d6400c1007002c02101d00b016201d41000b6a10380154104801c940d1020082084040440901c0795148071180054102d03140b0702c5000300c1140e00010035071086505083c002c00d0040c2ca148000440454500d401152100d44540707009014200520f440000110500c00216010300049510108554414650303854810074146441e03070b02c090008298180104c108c0d1000b5001512140951902450406107030380e9030452800c1c00d0019540b810040c44c80c60000c005018604241c46080300c224000d00b40b8584800084d03200c03104000078070035850f090506220038800030a400c1006141a5074a0701e244480c6a9107a01c0c005089000c12200a50306a00014031f20700 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 992637149 1250 992635899 992635907
    0xe06010803041e0803030c120106170412050702040507020304050a0501090b0414010507050d0206040b0f0412140d14062e030c0306080a050618030a090e091603050a02190510 76
    0x458030000828900b10726560311080c170b055410845d400703000c6904c00101002e090700c02d044910b0243c40c1c0390500ba0b00c02c409004001101c00d5000b4401031081c29600c20310801240148240d0302903c0e40184140650b10703007040300030346981107480341602032002400d0104681d03018000b5403099030000401c0501301880d103c000c40c081501c200c082414040104010030100b102807005545103086500240761030b080624000c8010800100406042e100c1c850070312002998030141004540810311300400c4641d4140d6000320707148100b40106100503d89110f900c050601420114419a400c40b0f003c001000480c4201d0420008046e82400c900c04044000f18414044c3d44800d003000c0c2c4c945400a0050344404070145418440c000903101a80264100034104071b11651901d8048072840196043c040a05006406456030b40540e090300525440010050702c0200301c000c600c40203016808011903503c0c2021520340301d0503581640030706a12103102124804c640140c138100d6101504985030b0b040040030440d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 992638399 1250 992637149 992637179
    0x2010806190302090103050d091a1c180609020a080109080d11190216080c0a21050304031a0c07021f2309130b030c010c051c0c05010e0601080304 64
    0x500e03401840d200c0400541c51301210b59001e50f1144000f40140154004003400180b035560040c450b046501c0154660781d1000340c252141d03103a50908150840381c20102d0000074009042d91003010900d00702c41401886034a400c4800c920b4000d4400d1900591a080514281c480e08500034104038002c02c0150800e8605a024005080080141d2410010030303060503100800020a0000103034041083d07c0c0242881194000c000e1066000504c0b12480345400710b40241014442c4c056480f10a1b04010f01c00460064203050165109040e0303640c503900c0e45130241c0301255020b01d015580c003044000801084040d42100c006035001806031a080c003a1201420040b407501e4009010890191008a01006160525000c091220301410b407111801c005010448100b1512219258100555020551404100014812005c4ca0f0000e104440d40c1003042c40d007402480080048101c099022407400d9001910005d0b6511500003840000018080e007a80d800f000e018884458100300b004120403100d50707500b6 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 992639649 1250 992638399 992638429
    0xf06120a0803040b0708480406050a021203191a0306280923031213060516080705090a1a0a0f0807020c0f01030b0910030c060c02010806 60
    0x580403a5841d41e07071020590802d803400c8400c14142028064010b4100410303a42c0003000c0700d03441e20f8401001d07289400c0007540038121001003940412101480020b00c001d4080242d1864415540380c0d5210f1000388694044540540140514961700010060403002c490181e92035452585908042454610051040c0d91002000b0b41c8810b51208840d00d0a114241c4100c05104100500015805a16180c04620000030040d00d18080138400050021880f01d0415011180e8aa4002907003008007859480354480c400710b034070042e2080044e41c42040d000c501605200701d006004907111100a40c8184000461680101c0d100354000380c01c80c3c0c4540050170714400010041c8245590354042400000310428061001c2840040c00c1c9003082c0d00200000c00100d814503041c426460629002900c403451540690b10403003000e241c1c0080383c0e02c0b0b60000c01403424020044030450500320001e4084c600d80348021034440c0b0b0210310020340c05011b000c241304a1901030310707200019a0b5410402a80c10019520303 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 992640899 1250 992639649 992639653
    0xf010806070509010f2a0b1b1608040506031510030b0f1e1306140a0e040803070504030812240d0f05031204030f020106091109220f0b09010e0f0612 65
    0x84419406c0700c0302c01c1400000481c04403c1c0e0b216040f410300b05010720008180d504c0c1405c46480f8030b40d000b4408811600251020200004160079914202c2d030039120301d0348056800a070100c14014400c29204048200d07440480f80007801d1903201e4001d03000d503085058a02c0d0301c40c1903005031191b030703042c207040c1003810031003400445c9a0302840c100052a91868440080d041d155150b40522548500ba042281d04040465800081c64549008841007180081009000c554084085240503010358107070380103907601c0408192558284036000c0d0380c13041c00721089080e05010300e8100351000d00703038007510343e8040d80a012100441070548480d8120104428102e8961004025820545814140b46401948240e8811507400c6090314001c0c00e4030066002285040d283c216405a620414070071200d2143e01502d0092103a8180c801c45045030441c00c500c0300000d41480340f0705060400561000904030000c544802c0b00380d0720780300e401c40c1c0706504031a00f2078825030000108400345865521400b091a800e01 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 992642149 1250 992640899 992640917
    0x53406030c0c12030207051209100c060e060114010f1e11150106031d06010f0e0606071b0504110c03040603090503130f050f0609030d050d061a030f010806070509010f 73
    0x2071041840c000e01c041d4180004c0c1e0214002e1b013000070070700c05c0d4203011042c02407150401c030034800020040301e04200d09034184a086000c000c10030006400c80344400c41c5000960b40e240d0f030b4454586c8804101d0921450000300c010900b80c1c001c0e4002c021910800c968040140011059a0310560f03c0c051321080502c81403140c062100419551480c0a0b4041d200030740d0040303400d1889131400082c180302009040144e406c00e01c01444943c61030543d010444080b81d082c06240d46545020400e10b10494402600d40c8024a40e001540002c4200201c00c981058408021124900038840d250303000344001e161454004000401000c5d1080c1c115000c000d0184040e0381c6052482d41184540c02400e5008101c0b0080c0020104010329003600e03500c0720007070140ca499141c1401c80000a444a0a0f0341c000810321401013400c4c4c06440590344141c0242041c0c02d40c100c240d0310400d400d03c1c01904215081c0c0d00d803114070400841ca525020501c1e902604240d21042d0810400c1c60041d9118420380040341c0402100345 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 992643399 1250 992642149 992642153
    0x902070f2409050102040f05032e020705030a08060f06071a0408040f060801050112050405030703142106030c03010c09060c151a12030f04090e0118053406030c0c 71
    0x2c815880424410b400060341c4078509184c90600f580d050307004038401d8010f134103e400c450b01001405850306c0421103000107007491040000f03000f4007a03ca0046c05c28403021454040140d0000384060003107104842c0c480d084004041000301c80d20403000c0041c07032502c036007249810030007100948640152050390300d241040c0d1140c9542170f0420680d400803000440c404010007003543c121000c007200e203404450611603031402c1d4542940d0f81c481c84800404000002c0a4448031034201810386100304003001240b40c0000000900f04c56144007511700600c2805204410f410510701407003805620211521103480551405000703464040950400b07440449180484044901c0e241c030620450681d01710006c0c2054402c20140402490101c52100030f980c01004409607500054064904481c0030440110f5038000c04180540508403900e10708a001c0c039a04020010004046802030089039640c0820b60f0707455011b0403c1c03040d83c0d400c540310399802036190300a002c428401d0f0400401c41602c0c0c02c11400ca0000d44e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 992644649 1250 992643399 992643401
    0x606090316030b0a1a01050a090b0406020109060b0604030201020a021318030c0b0f0603031e0706020f070213020901141b160f060e030705190308070c0504060902070f24 74
    0x810001c9000803500c100340b080101c41e04507550418481c030750400907120b8241c84a4065088088654140f00c008181d00340c1d01489030401402610401e81c07000c6d119a59808068060300e203481d0209c40306800c0006c110791904240c000e48041303d805a0047c001c0305a9a024040381e50712807000c101ea40342d02c6000c1e410034070700c540200c0101a4031170364510036042031500300070668040c06031001c2c00303281100007440380f183d40000642c0c500c0042c803030001d83d07074603055400142d81c1d00c1060401091640017007962022071001c60003030403880e8001c1d00c00705000d914041952040b1f200d803000e030b20301281103218541c2c0109401d50152241d00c402240707403076035102c4c3d280400d440d14400242d036000c01001d041050003101c0e40c00782c1c48002011242030440c5d203804000002501c525003801080e003d202d18000d400c0310401c5080c428401182c0102429070394495a040c800705080c4107014450141d407c01c0030004078034000e407003200c3c1083e8209004401d1500070341d541905218a01c25120003e03200c2e070b0080000d1b5003030b13 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 992645899 1250 992644649 992644663
    0x3131406060f03010515120304030b130203010c17010303080612100c0f02070b040509040c0f090c08060a051f030e0f010203181203070f180311030c2706060903 70
    0xa4100100390300d141403810001e0500111080e03600030b904102c24000c400f4912046200000011a549440301d2400c143c1640b440c040c175403025200c5080103090188075052080203d2115000368024018140915020380741406290381101e00742c41ea801c01000403170301c00c2010a4000d14001c01c151103000a0600d11807410440003400c541659075601e4405505030480d001284000036070001e0005c185c40d005840200f0b00030741c400e440c05041104005402c1040e00a40070005e007201c0c402d41e0340e80641b10055000241042a06000450f600c2070100340c40346807000c10b41d0300300c0d41c00406040f1150803103070540401e20322703450240e414507440311080c00084805024541c442031414000503140e103072a00305e450402030030406004964016200d00c044c0b880419003201d502c4105400c00d14080175600004139201049111205c0e01d41420071000310030000440e2688003040b2044040341c01451441040000414200c98140c80c0d1590f1000c03d900c041d0000590940d000d200204400c0c200001c100100f070901907 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 992647149 1250 992645899 992645933
    0x1603030807080a1b05030c0903241012110f0901060e150a0807180302062a011b030c02071701050402010212070c06081f030b07021902090403050313 65
    0xc40c180c10056215401001e0350740c0107200340c400340005002400011070800000903600b00704a0000002420000001c0440780300310009811607541840c5440180702c02d00c541c5a40703580a070a803001040002c1a42c492110544128081c4001c2d07180c0c26079914404819580f8072160091007242921015a403868001030090840391200008a0811010009183d48100c000f12042005120881c42c007544100f03803680c80300031810400052030310081101200324195000a502510018400c01cfe2000085500c2c002c0001c4401075074175030344c01d090a25003a00c1c0c07102c07035240340d504d501c0807404080340c071130303000300d0b511602d1030042d01d21060f2580c1007500c511000350702c50503045c0c0d10b80f030902c011940d0400103961150300d40181142042ea41d40c0c1c03a82600780a0340720700810045040081a03a19401d070200510203200481d480c01059a42d00d003044000004841090160144512640303101c00d800155001142c0c1c020301c001c40c555290b9900303643e650800341820a4011108016200280c00c194406080d05 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 992648399 1250 992647149 992647157
    0x2010f050f0117060f061c080403051b0d21030b06041e0b12160318050a0618210c1e02040b0f1f02031c0e060601030219030509160303 59
    0x5810b110405840314034a1604007101c4d40501e0800403001c0e000c50f00686c000008580040d0780c112403d01d031140500c030424000c1c250020001c0d00104201c0001809200c00b205101440d01704105282000a9003441040140810120010070070854100e80c408031941d01850400141c5815041e0219006410507002028020b80901c5000d076140d10048007030000b4035103101d01c5031500d85480019000711a002c3d18066808512450201169002c0c4d04a0042411102440d84030001c0c9818010365807944040c068840c1d074030380080b41144004080c40124643d800c1401108066016903880c03500311018510311041241512581300081c076003481031002054030211a0b00400010300401003251551120f4610541e007150869205841d400da40a10052488801c2d00d500c044464082e4214402c10442148020035505c032020072000c95070000c000340000404681169840c400150100d109004a14078012442e00b5100007940c03094101e00d5000e180001a698008001c8405c2418610703140c2048003c6 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 992649649 1250 992648399 992648401
    0xf06090f0909011b0225050102030403030f030f181101081e1e01080304090506091b0309011119021b1c03020c060403030f0f03060608011203030e07091b020106050102120a02010f050f 80
    0x4111b05240341d00d07011584da01e1084150340fa0400107513880c800d6110090900c0f00301d900f5041a5402540005e250b01c058110900100d680005501b1710b041500004944a6180d010500400c2d40300307102d41841030030300d41c01c01c43c04480c0c0d118001e09e9503100145540841e111603204e403521340d0740060320700b4024080800210307241c1c1e051540780c0b019130b81c005000078003c03140d2000b000000001c01c881240200403490889076240c440000c52030143c0000303205a803901000140c01c0c06641a003003081c1900511030360a844d000c0140d5200d0004507602340a103070b5405092080740303860001c80035001c3c603115840782c011a40714030040c0d004150160000d138420740100e0f2101034000d1503103400c2075540d4204c1d040c51404204843c2401005040c000c8180204d009c40107602c1c12040070103000c1d50051003030b4031070380d82181c51440e0b41d00140c40c017400c400c400381c0c60040d80c4400e5694a0500501420050303901c144c002d0043c804011b04144a560807281c502800c56488900c140d201001510038280601e40c0c0b9621244d903 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 992650899 1250 992649649 992649673
    0x3050109051009050c010507060213150201181119081507090602030306240c01021c0b180a0209040225030809030f0d0c02030909010f03020f06090f0909011b02 70
    0x520b560741d034002021500340394511002943c046686030b00000d090924070346445803800c00310028001c003040201650104280070520303044091482907071030752070b90007400b500d42039902ca070110303169a000041c6107858540c0c190401c0c0c034002440301c650881d41e580302840b10780d07529075191074080070286e0044011262418003003159032000481001d8400c500086146080400c00705111000e4140f050480d00040b03003080010740e400c241261030540707082000f0740d01c5401e1020f4421141030f4a0088400700e42c45c0240009860401c07003c0c0f50031210304000b144100d130303850ba110300c40079502c40d008050b40304c2d0b402c2202e249509041800003c1e000b815403110702111303540c3e2030094413840c00a0f0004200f1351091011081030503484084414403500100007094200c112030041c0d295000d03001c2041e03400005e1800101d04a01d050460b803040302d0080f40c0040d85c070740c891403d00c090b0b44581c1c1d041c560400942c282128190602031031903500701d00707600000150a1841511110100344031010340b00144c22a211a580f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 992652149 1250 992650899 992650903
    0x80309070605030402031f1805100f0501060512040c05040f0f06090218010e12030c1b0a0e042004020d0b1e0d0b0c0409050a0c030f06081e07030c0305010905 69
    0x6860340b03081061543c14541c00003580c4a00600040410100e103e00070030030152640c011600c413540d00c82000303024201d00e244c82c9031a4144d80b030b42c0760170a91034003082c28445626805664100c8042d510b6152400c0c003480c0d161000100000c0095464910f09800090b1716203c074403540c0c1a00014050014007030041520b104240c602503404001541d005000440003852502034500c8030300001d0070004c000c0c0d07920300d01041c0c85110b030b5000049075001c0403540e8100c0034404510b10752050341e2101c1e014030101d80101000300c140c04500032550300b8041d42d8001b40c000f0320902401e8404a03d801e030a40122400c0e14006000c0c1c0e40911010302586841e044481c1d46820b007052400010031240e035100824000e00705c003145030034003050390180c00000800302203504404544220f038050000d2810900861900d804c1c140081c10022019100191038504400c0c4418001d1286d90709442e41c09000e0119018124101c680840403680300f00c8103801000d50000002e0103115508004501c10400418106e2081c20254 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 992653399 1250 992652149 992652163
    0x300204030209070e01201c0e0a120b0a02090d050f01021c11030a050c130603062d06080703020409091b121218080a0f02030d05091e010318080309 64
    0x180500c20880400d50481ea0845020300c074502140d480c2c0701b068158000e4061034415040b15011200c080d0b0418a441c0355030100000150040c1a0346910130595121aa07030549802801c000d82103002c1800400e40c950b24030b03001000b410380006c10340110054039841c1c5600780001c2481100f101e07035001400144139400c0075051900b001210300300308008000d4031071203040c500c40108210001a80d807800541c0c07410079602034a00c0040303981003039a0043c1e214100a170003843e1070f008035202c041c8490341e804146000600307e00a10382d0300044070103429140401c282d400c4c1c40f0162552007815001d10010840b0300e01440ba00744003502070000c2c8175080424580c01d0707600790780c590481c4e424034843c8504100480e517110446e5103010813030314000326902a4055000c1c084425a0012412400398280e2a030034083e14201c0c001e0040d00840a0b5803400c40244415201840fa41805036000214280c0c0000c01414801e0f401c0c040709818180803030840651100c01812110181d01280c250101000384411920100011 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 992654649 1250 992653399 992653411
    0x40b031905010e160902030406021c09030215040312050705090d080d0501060f17060415090911031c230a050717160b0402040905010219020f010c050a300204030209 72
    0x1800c1139400b41c400145a01000d40a143c2d080b03a00040403408100e42d07981220014184424a00d922443c050140d501a00138018203400622490305600c0c007141c2d640c04c0c81070090358561a06507018251b45514006841c00511100a024060014600380d848031461100750500c17070800c0c01d64451141d5008401c440d0103800000c10400502e12584034150401c44050f464001e4003164005039589a0028010b05007003c3c1301300d1020749c8030744000340401c91034008150040c490403980c4400d001c40700038035588000940d81910044c0c00b030034854503028000c43c1c034000041c4071007014242c1410b541c40c0c2051154403000001c000200000742c400e0a018105d5098a01400d0000c1200d00c3c3c5a001202c0c8600e4a2944078040d0142d40c2990101b001c40d41c40e9030000e10010340c040e00030340d02d4002610404000f80b05007070068025014400301c6a0074104103108403455405107440b101d06050034600700322590f4201c5c501c030041494002c032000742ca1040c14070b0100c40300345040d00056541c0d419441405544400030300f40d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 992655899 1250 992654649 992654653
    0xf240d14060108041b0b0a0e011209050606060f070803040b0f0a0507120b0111100614040e0a080913050c0301030c09022a0a020d0f1b14040b040b031905010e 69
    0xe1141583e8080d0f0301d2a04281c1001010800350300050808000c02d41c0703a4001c1800050008a2050003500040084c0701c01e0b109807a07015441c0c5101c8035440c15294002e100402d65005100042c4240c80c000c405041e0b41a006400300b130401d40141e03a4080681d1064400f501c009510004100c80301d444815001d42c0310b002c244046c00741e410f02000c00f40c0542c10f165500c2d0003003a03d4019214050344030300389080040d448181120f90503504c41d410341300100918007039080c0c4021480e580c1d010f2414540120b420505420300189080b08980c0c60b414625000440e00c0d552007501d450003510001880d0103068000d5001078461135480d491840c100d0704180150740002210383c0148040d04009480f00c4030100010081e05141c032094114800c218102401c200000b54070089070203403202072140d82c0c50541c03400b502c40d111500e804071a8580060100559210300100c40358998821a0242000e402c0111021400ba0022172400302c401c0c00642010615004c00d86020011003d800c1444070901034000403e8280f80 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 992657149 1250 992655899 992655901
    0x2407050a170f040501142701200a0204050a0207080a030203061903030807080703061703091008060604090b0a090f091101090810020c071511010507020c010804020f240d14 75
    0x9029510b6010b184542414844044664140098501c0c100d801c4505000c10780404909410b00d0105e2060034043d180e03001034541d000403084106802800407001c0081001000026442e50030000a84030040c05044074079000c1c030550700010450005451900450744001d42c59180070018081c0e004076542c3c1da5524440d90080400c00300341c12500d0340d174100c8420300e070080980d5910742d8143d001d08610b610040741300301c2295401040510200141c42c0380c035421900d82050300c2d01c42e90122040303d401d0b00c01d0359200e14200700400c65840c0b258070020350404040c140220281d5110802000c4801038806104265140d410701d10400c190039103d40c9120009080ca6484641009001652000d504004816880d4001001140e0b03100800c4004010301034400385c149000c503826001440d0f182d0044580d24950300b00341c04a410b25001049a00d22040103a50308610390b959070b020004007501e000507664000e4000c2c6c1c041078036580a480f070740444003040321034103581d24906c080c114129404c03003021600100d500f0b4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 992658399 1250 992657149 992657167
    0x30308100e0f060f0901120b0a02040806010b0711032a030a080a0c0c05031c020f0c060703050f090a061e09031e1b1d06040203152407050a17 62
    0x104882d000800302d041030440d50758081c0403c2d40f0203c01c4003516400214040002150009040402d01e91880303009a484d9545aa0545038103a0145003c0c4070150303080b107070040c8000c01d0180081e000440c020ba140d40105c0c2041c1c0003080c20326804c060641200c03e000000031042010f004100c00c121001500140300e007154540f00c2178140c1c096036400e0300420000003905020b01202d0248580a084020103075805480446180c40c04510300c449600e015000b03585034aa108070b80403407038000400b00070f045645042403070b82c0e04845581c00440007261007801403089030380c00d48460081c90701a002c5500d072600c01044200152040000c0c1050786410440c0e161800d0002440800c0080c41d034404440d84407007840f00d549002c0096144141d8051f41e00c8940e03000003e0800c40003407442040b04000d0240310074a0300e0b001c3c03c1c00143d200854800b041c80d0a440c0b00190141400d0f540b0f01024040402e49800c250040074040d1090703401504103035015401510310b18140659086400581c8100c0290035103070440503 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 992659649 1250 992658399 992658419
    0x1030b010918470d17090103110412150f150812090a1a040e040321090b040f0c121a01050a0f030f030212030a050a0e300c0f0703030810 60
    0x20364140b10390319440c1d410400d007a29402c4943d0102070340f04074017503821507000c200c2075060382110242d80e000a00782001600e5800c0400122002d035104104410b58160031034844404002a04d128100c01d1507955108240c5204517202d1804880b65268a520b2114a0002150300c1c01c9038071003c15400032003c00443c1415502d01c1901e00488885d1405440c07482801c0c588100f1600541e406440074030f81c1001004101540100c0c11603020030a1003000382910300e099849400c8070340100d00140368040840c0400e000c43d5400c4400d0200510448910074015194514030314418240c5004642641180720140c0320300c070811f2020740c054101580e681201c0c500e0000030507074080c001d10006d050b4600080701d130000e0520a00007000d6010394241015540e04200128000074081103600d4500036241a42d18400d4034004204d050301c1e140c8803510b810008a9040000002501d40c4083c0510a4010801c464140e50288141420704480b080074068907859428044e160100c0200200c50807980a00c050050a4078 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 992660899 1250 992659649 992659751
    0x2100501140102060138090a080a03090801020708090915040e0c0306250513030204060e010e34031b050703091a0f090f09090f10110901030b010918 65
    0x15051b41c0d907403980403280700f4416210f81441203410109104020608440001d54640d40c07a2284d9207036007841d035403603011500303d02a4034070080000c541000b40e06158078019610503000020a0020f002c4619051300040c111840852400040d8001c07001802e46442e0034404940c3c0b0030303040000a502022100c3d0701680c200041030001c001c0c4640811390b40d002c41d280d40310410181d0741c0504208040e0740c6500d400d0507c102d003442054000000f0f6400219090400c110b001c421030100b80c5084002d05102c0080c0b0405180032468800b0141c0d01e0606254000500c0b12210a49409844907691040b007810010507880040d0007880c0554031801d01d020108000c072048800e103c101d2150366440700031080020740c54a21001070181c3c0b007211101489410903000c10320390f200c1c8084e4021100001c012200e00800e90b014428100d151204c148000382003540240c00200c0b55460525000000d80c0e2241a01d0640c00e0b0200d0817900c0310307a9500e480d5001100c035050f0108010940c54900d200c0d04584400124003440303 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 992662149 1250 992660899 992660969
    0x7030c1701060f0908010f020d0e01020702130f090c1401090501110a060207080c06040c060207060c02010804060515030303130204060f052101110c030304060507051201060f021005011401020601 85
    0x9210440c60f20080d100344100c4001d84040802400700300030403143c000294200d8501c203c070701440c00111800241c07051084440303966001c2c0c250f007918070742115040001c1112840102c0f106407504025030004a4541e00340010b0714449150380c08104600000501d40d4140b508800d050110480c00c4039624500010400030f1103510040240e6598200c0c1ba080d111406064400b04041c45414140300c2004002d4100e802550b559a003110304450341d482c030495a041b143c0078042d010900c07020101e00440c1c0380381c00596000c00604101d09000180701d02191440d44100d40f89190130001030005000c501e4180200d44c02800c100307071000c507618141000101d008070304201e4000411090070302041159030a4000d8003c081001d00081d444e000c040c0381807a22036208031009c0300c007a0b1420001a0041d80a40240c0d0112a82d142c2c1e45050341e030800c034080d54000843c84000c0291f108814205550407980c1c095a80a000ca148615040100c803500286c50f211041e08843d2110a50302a0205d110310050440084d402e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 992663399 1250 992662149 992662157
    0x9060d02030702010f090b09010e0607090519050603041a090705011403100503060c0a030e060405030412053306030c06310f06120e0c010c03030b090f07030c170106 72
    0x42c807000e0007a4010003d907210042824208000d140610210040403846901c52100900c01480f00682c01512444c04503207510104601d910140802c2c20b141c00030340380e1010b0208041510f51b49600002c2e440b1b410880b011102c10030010000720503410662403d503005080c180040092504010001c0c20a4550410880014501200003000341501c0b409000c024040901074800380d0400d1000a502684145e41400100e400c0100c0310b0502c46000560b2441a50010b01a40c00e15090204100c080046081e00356074a224080d00000034080e910005400c000b002c05844403a004c1d0f508140d40007210060481c0e01c00d8022110120094845000311440313a005c14a0100602d1180c2d00c01c1440e920010040426815080c040881c001e2202d42c003074002d489803602c3d5030b040c1d200003500c002d0603a500210b8441032a00400600072255000c0d000b100c1e142442030030302103410038071003012804007501140c841e0590106442170017046500740c0b207210020003407460820301824080c03014021060062003110204 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 992664649 1250 992663399 992663401
    0x308010e060301020702100e0315390a0c1514010308131e0303080f01061d0604180b040b0a270e0307030e0901090504031e02100908070c0b09060d0203 66
    0x7940d001c0d41214000c2e94001c0120030300c0e24100b44024405820742c2506402031040710740e142030b29142003070490b200f011420700b8003000f00752802240c14041500c04601080940b65000c91180c45035500242c0074112407035441c0c2012946d5828500750020041d0b0010000e1485d2000342203900b40c580b0581030569411118080d40d030054480003134424a03c6900c00000d0803991072141ca83c140304101c44008581c06540c4100c0f1586980741c581c1ca80081c00c0c400c61010941392442107032500c8400407903214803a00244250700f4a5a645a641d5131402031401c0c0781030990b0b941541004901d024455031a000f901940e08583c02410223950308400c041141490754003501d2048102e4140940d0f8014262026015060700d440d00c0207450007a05081032100410b10407414400007160812240c0300c2c682c0b00f2a00740d654401246110794040421641c400710b02030460191207406015950203004249005200b80700309507444655040000900b1040d8102c0308c030404040050300700070b503114816910b5031480c0030801681c07 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 992665899 1250 992664649 992664661
    0xf0b010b0a2f030a0804170a0c030c11060d14070815011b0c030507030b0604050f0a150312110609010e0703081c14010509060307081f06260d0c0308010e 67
    0x10401c882c0d034500d5500c1c4000903ea5040503400600c56002e14070902d240310340e0180001c0900114043c103501c40d00001c0c6042070740c0c0301091181e0840544a400344a03690140341c405408160b03640d0101030340544468035028490081d102c0c600c80b03140e12983ca80741c100c005082c210703580d10040c440301c00402d0404c0f95601403040210f809109c619000381d40107017806501d5a8a1800c076403510610b02c0b051310b11001140c000303010350400b809514829600d0307841c0600320790350325508800207103800b511701d2829078034440000c80011802840004120344075101c10a050340900203241c54514014941b041d5641007400541d4040c0b40041c0e40c5060781c0c0c3c40b00038142c9445003030b18002040310b46121030500d8207040c121000002c1c1c0c43d0341d9143d030689000703891707401e860b9440030141641c03100c1c0d9124040031684412040600e003a80d1000c85c44100c60344a07004684560b651071050401e042c0c0003404044824810b091103008841000040c0c1c2100791424001d0b00d1a007a6240a00740c10301c14810313803c041640d0310000701 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 992667149 1250 992665899 992665967
    0x121707090510031e0e06070903030504090207081e031f030f030e191503050c12010b030c09030714011b0507090f1d070f1a0d0b030102090d0f0b010b0a 66
    0x4071410000180c1c504003001800c0144c081c0104240040d624003901000c505194450b040203401c2c6ca0b0183c440c185007914102e140c90003944081002d560552041c800846031101d1800b0b141e40c2e4000c0140e81c2503c030305086074802c0200400c0c2d00011341c041d85c041002c000140600140d00c610b2901810300b0a401c241141c085124100f0070303880040c42c0092000b0200b422440504049191001d0303544c20465940c6400c0341c03c49601c2180d8402105180b44001008107072040d500450340200300e00030450510710500086441e08036107030000002c1e01460702044080756400160307002c0c140340326104202c5141030f60b00c9044c0c2f246218020f0005051315144000700300b41c0c8903003145082020303d02d842030b0f110f041609020744034000380c016003040111000c0000f940c0425184041030761801d03081e405d0314200203160810003d1400c201d03811740554007801000441d40c0ea8000503800c003800b17280403c101c14031928100411100503004000b04000501104a00540c495042c08056050281910b045c20306010000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 992668399 1250 992667149 992667161
    0x60612040c2402120f12240a03023d120506121009021c08031803160303180807033b04050414010507020604030f03090f03050c150c04051e0f2b12170709051003 70
    0x3a07200b140030052f0400c107035402160465030081c4044104005d4036202c0c100b000e1007010100c03811140d400088564026000755000860a51000384500da00b4103000d8403031203240400315400c3c0e542100102c2000000074034415542c0c0010b00501c09140b904240240d000d40e0403030015405000c040e5a04001659030b031892016601030b5401070740c80c50b1034400f6807400605914840300c400e64810000c5681c00004d60014420440b80070819100e01500840d0f5420b0000400b0001c1c0b041c0d41c86d41502c0c0302c1c50704200e0b080c49618003942d219400380440b8501410b02a101000c07069030002007614200f0f61300003043c001e040800c0b41c83c0e4507140c4180d5900074600b0309440c0038907140b910040340c240e08040c0b20035150120000e0084034001d840c031001d24000d0400c40910581040c1040f60807854401c501c2840f4036000402c070a209003140030402c008488041c564914200028040382c5081c1e281d01da0880d0b144d0041e5064801a8500d070346103000d4078051400624040749441141d0040b418101220100b6000e90420 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 992669649 1250 992668399 992668489
    0x200c0402030c07211d0d06230c041203030c210c17011505070c09061202130b010c0b060612040c2402120f12240a0302 52
    0x159124100800401e450303a000da0f804407070400303220010303502403101c00c88181c0f6040302540311528040b80e100780b0650540703101e40304036600014180801e4001100d6108988080f80711140d02844039039451000201168050b0001302d91b03003c240810407045014507052034050394103140c0482c46804000c01505c100b04420002d0320110004104003111206542c01011603250903620b43c1040c009101510000f814203016283c1c18503c0b0f203c20300d00903070080e4010305005200300207100c0200c3c0e9914218003110040e80000341d40e440280c49034001e524020581101c54034144204200000c00c80b800a0170422001500900024440c2c0008045588142c203446100078070300b41c80b00d2140b9240c90a070890309424050504241844481107486249481d01c0b0780d0400003a80081440c1020703089000044d40100d0314007000141c080004900e0546540700c418043e5144200019411202c80194a01341000904217400b078800b070181000507070380302103d01a85501203c4680d01d000c0c0707031300560600390740c0e00400 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 992670899 1250 992669649 992669651
    0xc121b061a1e01020c19080a0308060301110f16021306080106051503100e040f2a050f0f040b040e1f15051008090c040e0c030c060406200c04 62
    0x941218042a40d000c40c034240000c6641904810b5116901403241010070303446030043e803040c01e004901b81486a890340b013200359200004079040ea01c40e00d0601e8525110f000300c000a40c03440500c400390500340905603c0e954442e120500b0036501910f916154080e000028440750352051b251810b640303480f00410440343d10100b040c021503881d00c8880b030103170501d48145800340e1644e4100914581800302540e0140000070090000c3c6841e0070f201038040790025009031250201c4964900014543c1d22a2038546114507015901118105c00c42060501c1c1d41d034010742c001d210328080c0c80c0080d6076059a40b1503020084400051029040012030000d055924401d43c3c24440c146803010300f81e900c0301014450004034081480394111112038980c20148178402c054100c1e10040041d00c005008100880d84094401c00711031094440800003802c0e601640070f541c0207504214a030640a09003488100740601090b80d07a1894603280800090038100c24804944440d4004580100c2808050095610662000340 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 992672149 1250 992670899 992670911
    0x7080d0c0909020412110a150518040c030b0f0108010810200d2007080417010e0a08090111060903090409021906090918031d030a29070c121b06 63
    0x10305141c4a10207407040c2d070300c2d250329038032031711f001034061080e25103a9480303c005549840081c0c41e5130704010360312030110220500144294079540304400780c3c40555500441c0b000201000d202035000c108240307a0411182c0740052004020002e107a41c141359040ba0002071440c040f1a50f0b100c0198140410100001d0008000480c07001c86e810007250807416142d81d280800320024130003094821103400030300a40041c0410060700044030200403c148240c2c0002c2480f4060000c2d00b4209021300310100c80708000410750700400e50307000c0c141d8003c160030140100480c1c20200140e030b1381e078010000c41c14426038480049100f1501c6441028540000707003408420480d807100b00c040c0601016004600740c00b45484025a00c005070200d550403d03c5d019191420714035000e4110304031749102054405d4140c8910b400310301c001200c29004112402a519a99078120602c0c48041c2e140000503145004001041d4440310200300c12946e2140030401c64148824180901c1c2075406649407a010302800c1286040 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 992673399 1250 992672149 992672159
    0x20c100215090303070924030c0306120507062601031b0e19140601050904111603020a151407050a0216060509151c0f1b020a030305060607080d0c09090204 68
    0x301860180c2d5903610741146d0070742c840c543e50500306c0d942216074420315900d40041c240c10340a0742c0f03c1e03002c5414925001c1681c03a03e812142000d412034050848180e407094808007c0b00da804103886001d21258800306406140d415049a50349006000161449000480c0b11620b404666850f000600030810040c5040c03510010119680386103c42a502181c06c0850f01c000c1e00b4212482079200d100b0584520703080004202c1480b0040c00918001804180c0800c41c06405c004c8001d15a0946482130b4001c00b041d45680c50b280c9244080f801700220100d05202c59200c180900523a4141d011001d03140158844504046c201d1602003038a030f10b100200c0034150045803481e40500240440803064510014121109012030428840c1245000f081080070000d055a9902d0781c018102c4561181c0010465199075400740d000c1e021380c0800c1c1405070707101e0030140e0205030301400b485601100031145a0b0a04c41140c5509101e481442802c6038102c0c0d0b51900c04480b5400344001c0c0c40034000302c00b41103448076218 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 992674649 1250 992673399 992673403
    0x50f0301020d05180709110f1308011b200c121011030108240a020d02040503060c1905030103080a080406092f09040c0506131a070c15020c10021509 65
    0x1100c42c2440c54005c000c0081000c0030300d4000e240c0c0404132282c07100d282100d01002d4402642001a00340030700070454500040700b210900601180002c3e402c6804440b070040a400703084400201e40c2c1020805181c81d003011540c07408103040c06100c0068825812500c5801c140078200014130078034020a5162140e61001c417000b003030245069409039800caa9808042c41460f01c48540101c0303a02010101ca44009007a10880d0380103081010307280c000140c1016100e000090a1031001c80300c014194801150203410f045000d1010380c094849420028038550454035a10524821000108140f06001303000c10204542a1f00c0040e40541100750707005107036280e040900021144000082800c02d00a4007043c00b0320744440c20358012075120640030302e0707a032400f014030100b5004081d072000c0030010340900188000302d8030301d0803685028080c2240d0b580c100d545402c0100409030740100300c1c5104441102d491080d0001640c2850940840f5210000e0308050000c9103041c4c410000c2c480d4010010081c07001d16000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 992675899 1250 992674649 992674681
    0xb07260a08062706060a14032a0c0c060702310c090e040b0a0b0d080c011109240918180d020304030822030305030406110310050f0301020d05 62
    0x300701d80d5004a460000030164891220f0580d141050361100007055807850807200a03c6203001c1e43c1001d0031080d4020002400c150012111203480e03045a8528000001c1d02c800c11402110740007803024142001110f50303039075a2110f50310342802a84001070100a40d0b48a980354000482202d4445004c110349010800c11140724102c81019507041c544800c0829010301c00c68410341e0b10609070088265659103a1207050200600b0070942150380300c00c1c8024980b00c80352020400c500414800b83c0e9804014070700ca0071103440c070041e020002010321108003a030b030320401900c0b40349000401c0001040395205032803256105410260343d11140c0311011000300d00304400b07218482c2c524104061030148006640c5a02c40000c60300c2000103800800003440001c555101070013200c45440e02d25680503000e5001c201c1403600f260420307000310314080108010484a8065848520102440b41c1c0c21400c014040818000f40b0340651882000d01d91050000d070f031403d40c142c0b03222080181060145090040e003821002c10 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 992677149 1250 992675899 992675911
    0x15050708190314060f150706110316020111090d03031410090b09070203031f27050a15210b100e0a05090a12050c060a0e160b07260a08 59
    0x42000c010911030010f10680500c1135402604080302c4550f45001c200b0000e079412400c00300f04400b8020382c000306404e881000340709801503c0c0310f80d0b01d041800780400e1824909030302c10110ba042c9103942c800006a2015120908000e485e8252040306602e0f00340c016009002c03003501d04422102c104460360550140c140304441008034200a003241c00001c0c81141e5000b101d500300564000c0000c80c09440001800303031441721900010048071915880505a00c2c40030071900745180100c2803000300b800c0c02e5845002d410030700c1c0080810809421403081c0715094050301c181443c40c01042c0c2040b050408102c2c00880711603012054600502c0e01c854024070703040146c02158a400301d8680080d90036802445054007a5034620014103031146255580317281280c40740000001c0260074051440013100411440b4024001c495021a02020380c403400c9141c001c4000a2280c00e46030084104003601d03508084035041c2e50440c042c150394002429070040d407010600250110034600003020f1106075880800c45000b04 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 992678399 1250 992677149 992677151
    0x2d050a12050708240936060a0506030a0c05040c17010914070c150902060c030307030b1c020604031b03020a0305030408010c0804050327100309020a0902030702030301150507081903 79
    0x6003130a0101c8200a1024200b2034120000c400881e5003860000003034180c2c1100d4104185440d10050072070a549030300800c1c0c00030564491010300601c1d04180c0107241c0c0c40038050340203200001d4143c8030302d40900100d00c030300c1c4c0c0201c7e51178200c908680e201e0034504101c800c00501011140d46d444400b68002d0a44848910011982d0004904081c3c0f04681c2880c04640080083c0030101081ba8168011310b0200c42c102d07403140c801c100c01d03601f5040c14000307948200805e071400550042d80d00705000d8800702d602240341c01d461401403540010794860381034030292a0002040000d100c400c141d6001e440301c10342c00295100042ca18000f0800c00000000e2040d560440024490034022a40c299000071301941c0081098105010101e19049140c8003003480f494088102c655030105c40000c40d068540f8040d88000007602c41208609608242850000905900c030046145182c10b1000035200d00041c0914031101001904100c105842041510071094001c504e942d5034255100c01c02d26603c4511030504042 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 992679649 1250 992678399 992678431
    0x1d040e0a1506050622030c060e090115020325050a0b011505161b09060b07021206100e15060406050309060a09151113060806012d050a12050708 63
    0x24081406072000301c4402522072400e01c061117405c1502c014a00100b1241002c1c0c21200001240d00d1140c0040105000c2d1162070a4202400c03c1c4006008142c01c03502c01c82c2c200031051030003a540041220b40701101c80066030701000c102d0140540032050071501030100d21450041100748100f2500150490b50684a038458120841c54151071034060b40070040c05d0403140d0071250700401c80140841182d41c07640ca8551840980b20888001141d1040d081800c84050200f820011410510040c004800a039002030040c0d05d4298160b000010310350041e01c00c07101200010844002003a0b0380f040d90702c140201295115900c0e002e0040c0603400456044200f4410180401c1e800c040703500c01d961a80b504800390020401010038175a0140110003072482e14114100003550000700c60362110009415a90342d00034642c20404001400d41400b2030a903410340050140d40040140c071610b91040a943c2c3d070070300f29110655103009503034141040007981c02c05410801000003803544034202620071841c40e841034001c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 992680899 1250 992679649 992679683
    0x1006020111091e040501090c030c08010f0b0c10020a050909060607020d0327080604120801080703110105190f021e07050405060a0b130303030f02090d031d040e0a 71
    0x203071000960600401c4600700240c4200381010140407090350000b24103d80b5858110340800c084070000d038820042c1b19540d400b0186041d616010703550701107015140c04c0c070055042c0608002800e01512504414040c0022501c140342030900c41c0503501c074a80b01c1d045449924686014265078050000103110f84256000201c1500d05034064404042c0c01910400c0c21003015901525084005506080c201c00c072031000000380a40280f8400141c032260000c0c1c03080c2c0c2080c0ca404881e401c4400342e81004d0208040c014413064100280f140f0031250030040e0b02e2a0010b4160060713030140301c0e009408018095440e0820030160304001d01243e585402d5003105c000e0b02c80b04260041030400420780388410b0300001070800440c50103800c0350350480c10040c080703842e1580d2400702e100d865015020006801c071b0f48210070824188c040c4103002a600500ac8190f25100e60480020181aa404001400e01c02d420900c201424801c100494542d00c01400400203500d070320000e10380c2ca809980c4100c0d203c00140c110040 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 992682149 1250 992680899 992680901
    0x2b14070603060b0a080403020c030d120c02010207030f0e2e09051005040e09190c0e0603070501050301030609111012051f050616170307030f06050906061b100510060201 74
    0x41200c2d0126111810b0008000c002c803805203011b80180c0461245914412155a00b4080e01c0c0e508000e40d1601444440013a0a10081d120b1010300c100542e403050040c100480d4020001c41c940c0b036801e2502100360482c40000450251800341030b85074001e10326a00c9420181015200c00c09104940c0713035182c2003076a480420118100c540c651000140003070104100608426038404c1d00300c21100d0a0750007010340301c041451309900f00d034401d41d40c02400400c10050603d1700c12195030002c0040c0d0140c2026420400081c0003440103210041c130142e5104400005e00c100d001824140340e07401042c002c200c000c4008001c1007124003141400740341e4074041c0401d240c00c095411080740103488920303330b0000501c4c0004111141e0024049181289070513140034000806401031101c0410420150a40341c2c1002c1c1d000404440030000304c101075074a0000144020350381d400340c0ea135000e00101c502030340d81c80e11107110800b0030305501d442e404181f2620103101c01d0070344c0e02d400a5208805d090500081c40b0303504c0c2c00c128 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 992683399 1250 992682149 992682161
    0x3040804080c330702030a0c0f0602030a020d082d07020d0305040c09090f0501050103060501030c0816140301020d06142b0f060b091315060f052b14070603 68
    0x254003521002a0b031001403100d104803405600c038605500d082084d0344d004603082500501003220505a0120706201030359200c44ca0b68003410b01403000314100000100080e42c0c0e040030042c0c0748103001d00c040015164015424000508640c42e24907181d207140c2c01e50413452500400d49204001d40034a001080c4598401d1050600c81c5402c4400c0c43c0100c2d242100c040c00034a000c1500b62040702ca1600d02c1c2004c20b03804d0044a000310311a0030005036961440c2806221030009400206843c2c2041c000990705c44500e4103514207a511303000000f280c042460340064020b00c17852103c84d149a080280014080f1459000114002001d88451003400765800064020013013401c03440040105540d07001700801c2d064006280300c80c0c40390400090f54050f000009110550841e034694540b0301e9031001c0c0040080303860086803506d02800003800300300d04000d10781c2e504160034040c1600504000c000c600b0115000f00c03888407242c44540140105101506262000031140741e010380716840340007000107000e4070910900e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 992684649 1250 992683399 992683429
    0x40605062b150509060102012c07120510110c34030b010e07170c07121d0904060f06080d110d0c020d0c091b0905040b0303070312020d0203040804080c 66
    0x107001c0b00b9007407204101004078050200c0d4110341d83c401c880221840102642640304103c10180e941d80280c0f00310151619601e03404c80704100307018100000001c1e000080d2940c04503045440480c40c1e100b4410901030500031113040c2c4156100d40f40022401782501404911b50106141c2c14a2010f100c07061102816030407480001d02820703100e8010041048405a0340d90841c0c240d181460304901000c1400542050a540794251100d0008400040002d148510440600181082004211340140409441d400d00c00e10030b00030701400d400a0108010350f84219000c40c440c0e5003c1000b141c0ba061202d40d600a0118180b004c02e50100f0702d5841c0030030004010250b1364440e603e031005040603a0901041c0008204101c2c0c18100c4036601103240070b5035019000c000000c520160110084c280d13801404000325512040c0564030f404119081620b011048414982d00760030000c41c568195000c800092051007044c17054544040144410000c400000b002181c00c140100d480200c56801005090a02c004072 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 992685899 1250 992684649 992684681
    0x90408040e0a0905010f271709120109030e010f11100b031906150b04050f19030c0b09100e0a0512010f060e01030501050f1501030902040605062b 64
    0xc00c219101c00416207560151100310045a49260340c0d4405081d1011042881d8845460320701d101c1028030000000506085402280303801130b01c55032104c001858146041c2c16500070700003022802a01c131248039101040e20a402000700020b03904004015107680c41c0b6440c00100b018040d080041d02c50303051647c0654001c1c0103011010b8107812a01e000300b034121649505401003140c14190641c0348004410f1080c01104046102c50034409001c5d038043d02a0080200150207010074402a01e5202d00d644180700269004c0380090348a498036007140406a1001b403c2c4180541e0201d445c18451001d4450000700b0381d000742d020b01c1d415106079004200354040e0342d000360506c842000301d0300d0030008401d481040c5100000e05021281c0c030401c1503907220380200c143e034200f03c001002041000d110f00c0d540410030700075440c114100499035215460202071500d04040d01d80521801355512a0b0080c001403200401180e66450403952100d1400c610311014503584c4460410b60800c0401c0780103500b40c0c40f044181c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 992687149 1250 992685899 992685907
    0x2e03150c031d06060d020d0807380a230c07020112050105011b03140c0f070b07080403030c0804050a0e09061f0b030c0405040e07090c05070b0622050c070c05090408 72
    0x414452000d405c004240da0140c3d0007410000882c041e60002e0a09038080c001419456502c96241940c64480c5d04640c4010b0000c06d0181034100c0d00c580000750004031540f404100d030580020709054540c021034100340c800d0680d00074040d000c1c10350001000c10904c00c0c0c8403e070f2081c03c0c164100d0100d54091048a0100f4040501d01c50700c0709924120018492185c14080808402e14001105a80200100043c43d40c0888880660716008005200c010010040d07001c1c509201541d921a6074000c40c0310003020b0040004400040000900c1620041c24000d024420300c541c2d139144124604109807000c0c41103006a101003141c005000744030200c4502992020500300340b1782022545242e2000b0100c4248540c01d00000c40c0322754071801032250080080000b0300071a401d0a11000844801000d414280502000fa29001544402c44e07103911603c100c4080040b1030302c800984099541682c81c00741414070381010015031009041c007038401103005841c40e4403d651a01e09103d417094090390040c1176504240 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 992688399 1250 992687149 992687161
    0x4050c07020f040e0715110a030905090a060302040f090b061009050d03110a0308090f0d0905040c260114014404050703030e010302032e03150c031d06 66
    0x90141040b02002400c002001039250710240e06244040d0444002d62204581041c800d6900280c40081020f540c0042c5c20315810070b90b4050522009c1d4881c030b81c0100ba0103070000c0d6194441da40a00020360f0090028010f805c2e0040d040300003401a40401c546114011001c01d502c0d04202c620100c410301284c6503d983c3d5070038503040100440c0404012410072486004000d2004030601c803500c43c4038030a88480e0440d00341038103082c0c10a040c900202d10f0f02da10a0440700107041c0d00c03905640c101c031810b603000030711915608812076404558040507011326149030b45001c4040c03000c2c0301107412200c140840c4030f05180b080004550003039001070600d00c0c0c1c0e420138420704c240c0c1c0441003000c507a5034000c3d84e140c01102000c5a8038484250308540c1038a0380e4104d003204109040d002080800030001c00d2a0452451400d100203a20301e0320082d90000640c126a01060341e02502d0310346800143d60846005440000000040740c041d00d10800d80f6800682080f0285481a41304a502d610a200301c43c0a4030840c0c0c0c800c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 992689649 1250 992688399 992688409
    0x310061b1104020c0318011b0f0b04141f060f030b0c0310030f0302010f0c030501080a060e0313080a261909030b04060c020f06010b1218070b04080c04050c0702 70
    0x781585551156082010150f5090104020a01d000385030b003401c2055404640090307c2c00d00d40500611240c12818148000540740040040d0340c15840555200035440c0c90501e2a50030140f007070440c100348192500140c50300c18ac0406c030389003410307a00c005000960301c0340d002d41490032151100425201c0b0050201c0c02491440307003d5a070085c440140e1a0700b60b540ca072104070285140c202c041c0d0140c0d41d100b0b08003d501c40306000e00c103040e40031400c003803203c0d501d4281d00d1540c588181002400c0665140e03000c0011079000d0080f18400a00c210343d09a409131554960780e03d0b510000030443d018000400600004180e80c02c140802e034602024160038a160700008001c807001c01e030f600c1003c010985002100103185e182d41e031030140b4014440011003100d04840031349032a203008407400303480d40414010005c00000d11704a66a90403da0080d20268403012404030040c06000540c00c9240103035000032a0b410b61400180044462400881d92200c2d1850203100c01c81d0000d45902c0358200b002c004010141c104 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 992690899 1250 992689649 992689673
    0x10b1c02090f03070e0411040228110f24060f0121020406050c0d080f070c11030304120b18071a120c0c0c0102011107020f011101110310061b 62
    0x40c103038440300b00e6100006824840140c00800032030a040050000f07000342148510080d140a035070441c5032840105c50721000c0141d1200300f20256050a0050508030b1243c83d200102020034000c465202c500c42d44d666441d06980740c1f0118441640d000c0e030481000381150707102d000b0440980751aa0f8042840e00442d0303142c01248401c180700800d008020410151840100024280c558032542c682200a900c10300301034030a00715104101d0150180a0010f200c0801c1c20b402c001076041c07464106030f542c030742100100e0300302203540c1c0d05000203d000600c03034112070500d6000030b100e20b4240440741e464089910105040c4142048076512524003400310904041072844000000346101c1e040c10032103c021f104003e070848480003824070124045030360600c100215406094240000c1c07110710951400b4109a00070408003034030544594404600c0c1e07034010198010408c4600d0020b21a05507080304404d09540140d84136003500140f500b00080d884d01c2048000440d00c0f5089641a4031940c4d9225044d40401c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 992692149 1250 992690899 992690917
    0x150a15080603070312091508060a060e030703142409060601050a09051f090f27060308030c090307050f090a1a041d06070c0b04170d180b010b1c02 64
    0x1c02d0010100c00300d1401c498903985c01c022641c03050200340c200820703185041462400c000c00e000d00c2c003060203003690700c000c0d0030750a680c05494444005d070122000203185c8203440d80080d010003c0708a200c1950740c00422004604071400541a0003034642c2500e00b03800110484144c5881e4120174086440d40d03210fa0003c0000030303103900d4000c5003141c039140055003008211310520500c52540b448050080c0e08140000c0080401c40c0c912850075250024420b1000e8400c0f082c035080c11982e100c60044100c49500c8000915082a0603a032280382085080003150700280040380300e4402c0c4080003816260425069444071000740004406480d02140000174250074000c40303140c10b0302440c0240d42c607111845400b060b10588041341c0d8003c1169098142001c402a10400401510203100c1002c58003119890b82c0181d80042030324aa180c1031003468940e4007550f2140d0881d0750410b000412441e6500c078003501100d018040f1480b442c3da0311500040e00e4400d07000d0300c5e080010410b0102c178025034144d004c0d00382c103c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 992693399 1250 992692149 992692153
    0x52b240f050c070f030f020325031d1c0f08040605070b010f050d0b04020d080d090606080d0f080c1614010b0102010903091a0702060406111c020a020402030c070f0308150a15080603 79
    0x80c07986601c040c1c03c01c009010840b03a4080302c030302109259102081c1ca0b5903131901100c1c500101034060118a06000851002d5070b3300c4500300c40e100c100009411401401342d00708107840e481c1c0362603085c000e01560080c1c40c16035490043d1400480c19061a07120002141c4004008010600c900d40e20340f01c01c004014000d1b81e203c18000c101d8004105480000c0c107244400c510001181682460b000d0101c1d400740e0441501a400b200308140314641010410f810032400782045001c41e41c0d03c2e254070740d00e8441c0c1b49102e4803555807030130740408000e0504010f139480d04814000b440074034803040049007201c0c40d55a0180c00510918410044c0c0d280c4138158108812000710107514006441e0049141c1d51300c10ba0207040003507580d11500448241c144400148110140704c90301040c505040025030750f0704800006071086500201003806040030000302e03020a039000304180c3d000c8c0b01c3d80c180039100500880726070704002c2280103100740e107151510f24413055900301c14403601250f01180040300c800c4801080130303400d4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 992694649 1250 992693399 992693407
    0x1b010209030111090a0617042310020a0816080a0c0302070f0b070807090315020f09040c03090605060f0a0b0306060c06090106030c052b240f050c070f030f0203 70
    0x107840a000321481411005001562600d14005122825180381e204a0400c4503200ca803402c040d0001030000d4105801000c80f90404280c80880f031000f001260f1a0791042c0701d0072100c0e1100801c2500a005c80000c1e60b1501455075035105540301403002d01910900000741c800c80040c09001e001d030302081c04c10149150040c1080070941d14800c0d45011034609035201d0500324204a61a43e00180d1254401c20f01e251941210f40303181c3d84d8a4150b80740440c807420075038001c00c800d00e100142606440a114000f0710520401041d2a0098000e00d51048152406c50400340045e4003410f014111100c0440c0c080c00c0207500302c0c50a030400382d42c2d030006000c082d0b000c2020030150381c45603400c01041313001d28110000003451500d50301e0038041c3d825a90384414020040380b91060009030442c004140c045101c9901814444501c0ca001183c00003020b00d0440c2d2010314003001d440e02c04c0180d0005060390700310307081049a905c0300c80d00b5011034007800d40000c012035425814840000c0c402c01032209440300d507004403814 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 992695899 1250 992694649 992694667
    0x6090e16050a0f030213230a1d06010e0d03030905120a020703060504060f020301180c021501050d0f06020c012016021005070203030d050718210f060c0f1709031b0102 73
    0x150348000e510400f13107c0d10100d501c0510412035081c901426004413a0500d0040c50004080d03464a40142d403442009019800a13410341d0140d452403080c1c0348003c1c08240c2076991494040c0040501c4002070703076a48103144c581c09400303131000100c6505ca44103030024000f903072441e44c40744003402000b401124500c1e00c03490f81d0349001c1c07002d00140d03020b41001802c0c100134600c124030307640450703108003038000c1198030a0715181218250485e180d8107642007620401f80307015150030001007908a5200040c141c030b20025407100c0b104019400039084084e11689a052b10010240300780d001d00440a402005540074102500180b4104103200b40061103424018240b000c136800190441e00004046600c09440354108070505502143d6090390180b0120b0104010703003032070041003081070751844440f8414045080523040c41003e440c8281040da1005c801e0000180b2000700421a20751250081c01041e0400050b4000c0524240c1545c27050030540c00941c01d118003429130400c01200f603524058507560030010880 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 992697149 1250 992695899 992695927
    0xc040b0a0e062d0f040e06221a01020a120e1311030403080105090f04120c0501020c0c09090303010b0d0b01090509100e060a05030601050f0f0a06090e16050a0f0302 72
    0x980d00243d040340c4039600e42003181803224600c0201451404000821200a0744015202a5030617900c07540c1030407000b80d8401c80402c402845c2d01307064182c010510300d0070305081000c9802c2404c04108124800c0c1d020345200e001645e0f0741c11a0382000301061680881e00414a104515014035070320010b060888041509000804031400d00c1109030a1160001c03c00c002c0c9900407018600410050f14074814510304510b0350300c62080c01400090204080540c0c400c00184180e2002c0001e5820400866070f44588440713150b99080382541c418001e029440000713030045004400c0c1c8e812641081030b600c1c608410740000c28005d017008071803d03040c0021802c1c0401d8645406c11980c2c03003001c40940811080c4e06048840e015014010034a42c41072101020038085920007117440b50440e0016070f2452128200240020512803202c500030f90840d4600c4000207800740d0287c0b03044220740c01615165407585918a001103d0041508200c4c0868420031103024070900c41d030201a03040c00d030b5240050070b001021456003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 992698399 1250 992697149 992697157
    0xd1103011205190515062239111005071101150621060302060a050a110601030f021314130c0b13060804140a2103050c040b0a0e06 57
    0x41c0c1c1c100700e00d0440420428100035000040140d10106014102103940d0b0640c0d0b03043d0303007051030304109140011074400d840700c00c4040000f03903603a600036074040b191158200c0100040c0e20b5060340c04071040e81203400d0b000300c0320601b006440444030203011780740c46441c107648903002c40c102900240301f031840d00480341040c2e11800b8055070883da00c0d00180b110002005003507941c0c0285035518500e030000b00b00f2090343c001e810240f10400001c1004000c06c107242822005001950010f5080b01000602d00e40d0954800014606640b030b42d100d03003604040d03141c01c655484009010007020182c1d41401d81e40507140600070030130152004c2d05c0100f546861044181040740050310244941070200071401d080048446400c1c0262810345055800c200c104120448103408030310614007401404000310701444004d0b41c03078055001d02038048407440c07000d520341009444042c0000350450300e414000140900c0c841e0040e01d000c0c004220045007024144081c41c0f0143e40400400014080020300365030f280d45809000d8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 992699649 1250 992698399 992698409
    0x4050a0f08030402030c0f01120b0d05010204080a03090e0105090f04050109050a060510050d0c050103020309030d1104050103060e10060f0c0c15140a0203030c0706020c06100321140d110301 83
    0x35842c1c0c202841858a4000505401e074410703002e44203024010b903400041980c10b808842404940310b01540082212065400001b41495000140c082134207280000c40301d29481c0700381ea500542036030755501004412000e006e5140e101e06100c1c0420b43d03003850065403540081c0140c0000550605030f95030342d07107015902c680031900c2c50748910401c4603040c143c4503104000c04068401c0305408550342e84e4000307400340b107000702e40c18150301101050004d00100190707001450307400c1041040381242150f034151500244640303030010781000400300b0020110040740703014034406000101c4803810841c0a450204002c10101c0410800d0120200440d09810001c0f0003004070300700d004444c00414a0080c01207011003000c100c0900d04021522410358008201d03940031841880d41c40c0c40394128980600a80b00318030956642e441a8010712007a1102024024100da110f02c24206010070710303a607540340184400d0400b001040810103000d200341c844c140140389801c80c0580020700030030341b01c4402c6a41d410030b8100c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 992700899 1250 992699649 992699663
    0x306130b070e060d060e0601030b0904063b070b0a0203090f010e04021b0d0207030309060e01050f0a030c030e1906051005030a080d20031305100606020322051804050a0f 74
    0xc00c1201c1c46c2c0101d0fa030343e0440f0080c40c00344064850303036020a1400401901c000c0100b80d07203c82c9455008031968414062243d403592044504145062040c03041f01943c0800c081405041c5c0b0006445402034203d5505000540145092850840802664400451400d41885911141903c032940c0321310081094042c00850360500c0c14076000d01a1030401c980e040308007954846c01d010300c0401e0b000741400c400c0319058642049042c015900407111030080d9680f0b10040c40001c5480c82506070103400c54001c0d000555410080b46c8500290316603607425a028541e83d00c16401c051802040982d04181c0d030000f0158860304440e0340c0c400c04245000b00704031064580a00c0410100c01d59151070188200d1860058052244580003032180c1d080d51101502400d200e80b4804070010402000744801d03032140032800010130110381d540b0400380d144d5102207070a211518008540341c001e0042001d040c070981d0800780250028401d090703003081b20884040c1c410741d0a0b100300302c00130f000247c1c40c02004a009214181c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 992702149 1250 992700899 992700911
    0x1e0501020f040819080405090705070b13020f03010504030e04020f072a080102071502160203010e3003312105070f0303180b240306130b070e060d 64
    0x3c0c00d900340b00c1d004454000ca07208405014001c20907480599003965422034840c6119203402e507003a1010711440d003005065a0f035050400801190100005042c1030080d141c0404c5601500c080500700c9500f2503008010030340d84034561400d420554040c0480c008138007140d81c13410030707151101c0f00b07041c003241800051510f40341004901424506490300080800d54029828204550b85401036600c03e01900d40c0c01a5000c00d60b414280340c0b560074000310540180c000c0113003501108040ea12401c20050301c0d01041c8421485c0340e0702e045d4070b0810b41550305082c50041d00f19200d0303109100c5110300c044c4610030f011240402c2901e840c0302e0307602c0140d001c511030311281100c1d00204031645040840c600049091180030320100300400c600d80549041c4136410314000400103000c00c1c0c002d16448001101425004d030200400c012030022800100a030300840060302883c6407400105580d80104480700f803600110340280800007842c51425a801c07041c0c0e420030214184071180401d80c0c58101c40008100c0989400c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 992703399 1250 992702149 992702159
    0x3050a05210a091e090e2506021c05040312030615080106020303131e03050d0b09060307090e2a090108030a0e060d0e0f0604030207080604020a031e0501020f04 70
    0x4032440300755014021504040703803140041c0800995100300250300b407020101c24102d5401030811005001c1c4000d00300203a005004196035120300c035100b003040a8507248070a000102c1da9201d40360494903a40d0050103218104c2d2071441001003511141e809101d8144000b0000450700c0c1c10720400e030052a079000410520b45450a000c0195141c1c1d952f0031310100c900140102580802125031101580e981d0346030354400d503d071065000c48103070020340c84c00c02c000e0f00384000c05500000400311403081101c1440307080d00d40420861561002d99045505905c07050302001180707142c0d08000c4034102140281d40c13100d050b2100503803009121442441022a112500f900146418025280907107440001141440f601c04000340c407002007100264411000842c0c441c3d506e4107107800400800c4001d00030f50340f9410440000d60b65400c801d40d011809409840d90100305078400040c02803080380c0050845010074a151100701031040c24020003001d10608060401c04518240000d06011b10702c0c111242c0e80e18548 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 992704649 1250 992703399 992703433
    0x90f05070609150c02010e031f060e06010f0f0201021908040506100f05011110091b0e1b0702030a02030601030521191b060e030405010e010305040b0103031803050a05 73
    0x1600100140201480103001000040d001d1154400d0f00e41465413641000e8001038076400500c0c0e0216a2600c5200883c440c04030000700f171000568220481071000c0c5880d440c5005e040700d0101e07a95400503c00d80d82c03000c4903a00c504141c940e40c1c1c60f180001480c04000c50035492852184905140200350003406110400608001a0764440184000c40e0344042c1054003020306003205105590400101100310040b04405200742c100d80d12071000100b08000d40b52402c20041c071001f54003003d103032423401e0300090414a04100b0620520080c2a200c9455269606191203030300090001d0713030188107041400300140c60401055020310b000f03200400c003ca109400c2d00c035074156100103031401c4030414000104052849104000c0020070350a00c0400750100c104c4002c01c16a0071107001d406141402007240b414a8040002c2c01660b200780d90740089524050015000d6800c240c84c01014640d8141c01080880e104049040000e0f408199819006689484040c03510881c000d040c0c41d2604240c14000c031031140 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 992705899 1250 992704649 992704663
    0x812060a0e0a0b18070801031b080318012d051803010504030e21030d1a0603100303031b080613020f2115130b030109021e0a0e0c0f1c090f05 62
    0x4c0d02080c100910304198010801d03401840010b00303160045141c00103800e44080d240c805406144100c035210200128100440c0b0a48410b0704e020448410700c02440c500310300f001c0e07620140302c1c0001a40b21072440f80c0c22941030348910200c81e042248026101003c1d6030a018aa00035802640d42100d0318a00504002a081805107045882c00708000075107803110b404812348071103482810001620528605001e40151800801c076648160000104100004441c82071700640740a03541c00c0000d14072121940e000c03281680b400340041007207132000074940d181440f07001540310a84c40c809424000010035118040d00030103c00c0444408909450700c000b0740c8103450660085c05606004003030102c0d00e01054152605508904685407502c04488080c0c03402d401850903680c0c0034210228800051008100c040c602003661841030002003000102e4403a8209550f0042d094201000d00c1c0405503103d902c401e038032007040d0070414088070f0414405000b6a10520160b40e00540c908075110303042d4a40a403c100d9 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 992707149 1250 992705899 992705929
    0x2090414060406350c181602033103060f1409033f0703090506090a020a06030c030b0a03080c060c0a050d050c090306042d0812060a0e0a0b 61
    0x825401a1210b20020040c8035030040da10142604c000184000c45030030b140194010719048071000300c440c402031814103042c3e886075104c449282c0e01601400307000c0740c50b0f20402d4800510315401f03401d8201c102e04c4103400082c15100511080169940d070390b032064255080a00d01c01b07041591003d0341c4100002c0f050020354420440d80140d4038002100c551107800c02d4103103800c1c0400710f00c2c410b1101c102000482c01c03d2482a00c1510080c00d81c500b140c001400341009007400c4070507000d00c3c800305039803a400003494103a19034005c06c035011030750030800c0880080002d54030749010507481c3c4400584a440f40d20490000d10701603402c0b00d60350000b800f0700c149042c00207401903042003003c200c500000e56104003560110799075120086043d132180c003001c81d081d000e10b078100c50b81801501c00340720412000c01000003214098040009003110102195030b80c02e8000c000151202c5020000c078441203040760700855100348010311040e0040e0302da041104000804032040000182c0d502106401d42ca4000301d1a14005 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 992708399 1250 992707149 992707169
    0x90903221422020903150421021609050c130312020606011b020402090105040302031006080f072612190e060304020d03140c0a030c0c05190e04020402090414060406 72
    0x1540d03600b840c40c401d0501c0600401d12036000c18150f02941d030611101d1072659140b16080020301f400e04001c0360707031910080d04503103400020313809102031400842d201305d4a000036000c01402c0303894103002c2e4024160042c0820814a002c1040d140e215044041c80f41c00356000d615016807d040581d8041d180c4200034046a050018511400c00302015a2801a000ea54103807405038840d6820300042e1031a00603500020b5040c002e1812042801e203556020324202c600d003608440243e031a005800c1d88407090340c01081030f1920301c0c2004015120140c0760f03101800718600308407001c04e440841080c00c1030b00141d10420380c800b0307c100403801c6107a100c0201020210100e038824134504007940020b400749c0c1185c20040078081700258803003040850704c05503a038000041c01640e00e05800784c94014070055910344216480380d81d0304004900d07420103803290410940642c0420030a1401d02050248658006200301e0b4032603000c1060516a031650300940c10a101000b1210340641050010041940e480e41c01c040c07440 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 992709649 1250 992708399 992708419
    0x30c0f0e011511100f0b0a060306050105070204050615030f0a0b0603060a05010f020c0616031202090f0d2f01030b01140a1202120907320909032214 65
    0x4919281031040d040038101408001d04503e803e6041504804c03440342c40524100c181031100405401000320001d04541000f007258036450140e003150513501410340020340510110006003895031116820000c014460983c85607401807107000c991040705c41100d00d11184042c040c450066020303209815900312a95400c601d80440454000c003002e01c9850304008100c104020018000d1100020308840980190740e191310306007501c1129540407404a00155070308a003036807a03581901c25284080d0005158400c00200d420800080320060780c0c064904030450b5070031700d00c0d46590781020b412552080c010b4640306840c0301c0000d81200d242603021410300c100d035503da2202d03083c00c0b0300f1140507a5072400c010301351011306203880d4000e02a054070720740c0041200c014400488400030703409085524225406c1201400e12400410109001501c843e480400807400421403411000c1c0a501488001c1120f0030b08040c4400d0100340701b106510350902c19807030340d000c1c4401c554503801411490b100303039501d10720 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 992710899 1250 992709649 992709659
    0x20c0601080d0804241505010905180c0a2604020414040c0306020d02070f05070306050c0c030702090601270f0501020706021203091603050313120803060d0c0f030c0f0e01 75
    0x40400280011310103803180c01c1c40e0b660320008000001e26181c01702c108000a50f0310402e07a10800c0f865010303150102c1c802c5500090540780080107141550183c07035181c0219159441c1040150304900031700028003e109018078408034030300382a4041015440b9074010f042c282401840308580c9190714401c204509203040102046450750003008603644100016a24204281a8402030089140c01421204d149100380113000001a0501c240ca00401c42082180c880041458030b6214082c4100d105400600840c5d0140c0ba016030042c1c1e00000604160340c0c240c54244801d14040c0481e0b10001c1c00389205801070283c1a101401b01024007020300003040c0d6a402d08034042e54400b141d400410281000000140c050f541c00d20030001440b4520b003044400f581c492504544036000301c250016070100040d00001d8000e60a0441039210b50030420701450b6844038018020f001440e51406d03241502080302c0004c0c04540030300003000440c09480c0f404e20075400c08103070b400c0c0d10111f0ba2241c44450740903801400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 992712149 1250 992710899 992710907
    0xc05040e040210020718050a1508070e070e0402030a0f14190e0a0b10080d030b010c0206031b03070909050f0106090e0a38031b0d020d060f020c0601080d 67
    0x20704150111060364040440f21001c070b180882541040081c5001c0c070001c141912895081a40a10318604042c0305807201000e95203001c04252042d0b0007264410b6404200c00741110402d2a041021032a000e0800302c00240401c013680d0084d580d065019a07107070510802c0100f107219014615940c40c00320740c2d250811200c40c1d08000c0c0c1c19442d4910060b5140c400141c000c2c0f04006104106a01c1584003a0030728010002c552548101d10589007180a224240c600d2035119218120340341038142c41e10484075085800307115030358000910450326114202011807482a0900c0514810070a030355410181c94140700c0c40c541030301d030b0117028041c2000000005120554108541c0d1040c3da041c3c0c00c070303400c076035440c2c08012000e0201c0b46d1071003e443c043e44c00d403280060104070746003d00c0ac9050078081520a204414580e84501500070800c00b0b0701c4030740d01200c003441d2603a607207070700c450009111414080c05501c603901124050041c3c0c11506900042c0d2561100e01440800d00419005003c1e089003071201001034 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 992713399 1250 992712149 992712151
    0x5041503020301201b0316050d08010803030907030308070c1703060f010801030c0b032d04021819051308040803071707032f160302040e0c150f040503150a0c05040e 72
    0x46072a17400a01c5202c0325950400680d9152014035805038043d412900b441c0ba00c400c69035002000141d150070001c1a034803400070403203010f200e411005184c8189961000c50b004000a40344900700042c040f0240d0100f0001084010041c800119651352400c3c80403c100002c0460910141800320000040003c10100320150b0704481480f0324080d035a9448550074410b50009a0703c0491100380310036552042e50000b146144554404c0c0e0741e5070050034a500150140b034500b201c06d040800802c3c032801804051a03008903800507002c21411a80d88180ea59a000e41e8005030841400c5501c042180824440e1055014104240d4031044914040c0c040d10028003007039107480c400c529110030a104410300350340c0200d00c0c4140302070401520310078081280402040a60741c0300c180d1007613052a40010300003074082030110141400400c28003410410f80b02e0780c5c502e500208101c0d00d4092080c0000505510140401d031100440a006800e0518000d82480111202c800700c82080020501c010310010079164019 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 992714649 1250 992713399 992713417
    0x4020a0e041b230f041d0f10020304020d120e0637080c0a120f090b0907151803120c03091d0114030f1002120114010c1502040504150302030120 63
    0x2049041c0508400705c0c0151040030b544021035071a0511818107000085825108022804141c500700c40881441106a02007590081d6001c2c03074014003040021041c2c804480108200d013002c441442d516000200a508210750780d000200d940800c0e101d034110804c4440362980711001d04005600c51001c00109481002003090750007142c00921030019600804c0701174610440c2903001d1161a000031000805022540c108498041c0210045407c1440c049454019540c6855050718140d900702811900809100c01e0405200c40118010010030f2118650200164407510b580c0f07058102441d00500300c0c10540d002d65030b4901200d09244200300d10b0040d00f41119203107101030100301d80e9030001a0601000c2500415548510b5460300c41c3c10800380c000d400c0c248040300d966212680c2c0e90400d08151040d4208203400100313000c001c20001000c41c45c550580c00c1034002c0040c00d00341c450f00072404880c10014003480c44507403210304200314a001d00604500c9a0304505100580b0710b400300d103004a000b19501 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 992715899 1250 992714649 992714659
    0x304030c18090203012a1d0d1401020d050910050c09060304020103021603090f0b091503071e02060a0609020a02121e040b04090b100c03030504020a0e041b23 69
    0x1980000708568100030b18450b002002003205501c005030141c144140d0040310300e2100110100c40d4082402410250034000b2840c1455812050241c02c0082480c210002200c007140501c1c2c019116400920251054000c10000040c3e2403d080071480e1030302100480540d4168100001c1060446601041e1802c098003510559140c0e1500c0c07006270040e0241014402042c034158076643c0034035920000700c104440a500046504a407560780c80c800b28450310910740d8112480703c0d44c2c1803c074107908000b1a8880c500740b403d0310020b030b03040340e14580d201014030003034005900003010301040d0391040c4903142c000c00c00d480d000c40c03070f1942c2d1000280d102d482188240302e056401040802000300000860250152000011541c403038580110742c4903500240242d050300c03031814950941509110424100b20340d200c3d11007041c1044d445d40e049016280040c01240c012088d1840000d00c4001805914040c52154070031782e44201340c5040000c5007140a50050100c1c28140e0354020b02104c50b440004025002958 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 992717149 1250 992715899 992715929
    0x1a09041104080a0b06090a1512080705031209010f05010602340806090c04060305032704090302011a01020d090905100b03070903140c1f090801051f080304030c 70
    0x3444803980519480800c043c05000d00040401ca03019400074401c0404a65072162512003202c100102e49100030b90702c00e06080c10b032050010556591820701840d104810f03442c64010141c2d2203c0c29a00310108114070700c41d00e60180709286d602806580022201034200700709070361515000960345c82c42840300e241c5c06001d00c862181d8444441c10008404070100550900701c5035640845a0384180440b00401d0340e000d8003400b40d000d40745c0b0340502002c407074104000358181110300004e00c103906c41d60304c12440488540354104000303807a54011002e80c14003d800020340141e1044611501c41403c001c654111340001000a4003160809030074010b40b1001c810010f1a5a90031142d480002010740040300c0d400360100800ca141c0358440c0044040d02e1150100341d000c01a030300b14440c2e46403a0744111075409003500d10405280c519140d59400e910310b06d4030707260300000d69409455084034010b80e40b020f0a403480100402d0003403d00401080100340301d000035407038185951111040300805004442c00c201d0010 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 992718399 1250 992717149 992717171
    0x40b0616140601062303480301180c1407060f0e0604021810030807020112051008150405030d090203150a061401020c130f020d180209011a0904 63
    0x250a900111000341207600030b50b1a004080d05581d1651000170380c001d410400030200000c0c08080d03c0c014004000039083c80c0101c001100868001101700c4005d8451501880311803651000c513000701c910303503d000c07103903254185a9101e2080d009108074031107880c20301070700c00c0d0076a42c8000300d80c0c00c2c1c031482c40349a40c440c4113900d0f104019000c00c0900900f514104a45003015100c0032402c00c1c01240b0032201c04203200c0c400700c602b00a6060490f0b15107002c003100e190410219500400802d0305900c14035122000c400b188904000321401a1803900c4d40c0800341005020034802048401d4643c1f00004110440f46850ba07551035a03845a1502904856290b410f0300b411502d0410282c00075a14000f0710102d1450142440701c0203104074811911b5003080315940039080d5001089000209001405094074440c040b42100003030034051403096009542081100302c0c00c030040c41908040000c40c4502040900c080c01000540003040e003080b50002c0709102d0741c00185205d03500b00d4240210580740844c03420155 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 992719649 1250 992718399 992718413
    0x18010509010e15090f010c030c020d2a08070501020a2409080703170f3306040f182a0207030b180105090d05040b0f04080106030b040c05040b0616 64
    0x81d0039240e0b000030f6041580540c41d420700019041046095405100d48181003004545c403540f00c510103004103d101c00c1810150070600d9a040f00c0074001c00c1070725041c1c07201152045d41e0045400c00503901c10b4603c04240b00084013480303a103001b440309200a1885c222107840e0203402d400c0c070740c42c249600c45a61040f40058081c9800024055400084d40c1c0d884a0f11070034080c010f0407540c0ca074641091446d0300095510340000f00f2850081103010107400400000d007403d81081041d00b80d6080400818000d40b2042c2d54030a0005c1c009444102d0310003504901d401040c803d0440c800348a10020340c14000224039151003041c84003502d15000e661803901c1400301406a0802200340c002400411390f0030104070001c1c40034040d4910030403016008002980c0e406003040d8440360800400340016104220401a4410400c0900100b2110050b86480c25070388405a5003104c503694411680c08070500c042105120710b030103105000303040588081c02400c644400040ca54071885004814400744059140144603203 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 992720899 1250 992719649 992719667
    0x402101d0f04061a1206030706081303030b09090309031c08040215090603010f151e11010b0904030f0f0903030903062c1605030a05030a030e030d02041e09021801050901 74
    0x130313a44131aa5490140c907900741c060340018402c0140307844000200c0c146003000600002107d00c03507036603070b400c0e500c0b900d054405a046550058080546851140c5c42c0c941c2c0307144100d400380c040c01c0000d40e902c3c00d0101c00d0604221b004142d800c1c410a210b49481129034004c2d070815841981140c034885a4001050441e16a010702100c045c4c104e00e001c000806c0d5a09a400c510007945c070812034014044404203001c440c1d041c158019009080c150403200300d640c9001e40306214009000c8800416400d02d62008200d00394806c440540000d03c50000058001e078010719080100302280c5003002d03003241142c401030400021480020309030b9640b11403020800d03039400036040109600348154a180560825144d80c0c6030316124201d050a1610100000c1c50300c0c00080c1542c00550010240d4181807160000350024000403035a48031f140003c00c0305c04c0030034040d48000d20203480040361829010906195048400ea000d4200001d210b104100020070765501c001c40046090092070714660700e9500d200107e42000f4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 992722149 1250 992720899 992720909
    0x30a0b0c07060f150b0c07090e0c13021207092403140a060509010b130311060408030c1011070521090a0303080f070306050d080d09020a0e0402101d0f0406 68
    0x11404104160f0b20034290403490041d0041c002100c0b1075078403004084510320030011504c4450b84005e108101d8003000d81c00020280c81000c1c180c0303002c03500600c04507075a90303d600c0c84141c54550024050042512842c03c658000c0c80038507006002c103080940b100f80d0a0218010014041d10052501d004244644c100308203501640c07920003d2814452001c0010340024052a0700c541c001c0300021030b80e1060a000c0d900201d0400c4481f030190751654403400e00d844044600b03581c00400400002c548024100000c12110540000070609151225100da0444100140000034401d00700a800d0100340b001803401d80d1031940002e005440403001c060241180b2030640c5250308401c0241000003815040f050552041140c40800700a0f5950490124100c1d0b0f054010305038020300c2d440510000c108003101802c1d0451013040e001074140125000509441c000c1c0c3c3c05492605010b80410086041c135840d0600c1500c40d906044044240720380c0ca4038041c0085004860051420840701081c40d9110f40241c00109 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 992723399 1250 992722149 992722151
    0x302070606090c0e03070e0702030f0f0f070b010906060c0b0403030b010201090b010b0a1101090201090e070c0b0c0a1d091503151f06050a05030403030c0c12110f0c030a0b0c0706 78
    0x1500e00b0f00641840108615140300f40a542030000f21611040c80061190010703234095403400010310b10344209c1d90055550303100e20290500c00b400d044402d01c0000e021440c01004840c01070342c904540d110075550707103400c00c200300b0100d200802c0004180034885c075009513142c1070214090302c13a500100d004140001c00940818803820002682041f80d400038108001c15968549084030b03070400c60b40c260394034504000c1c0002c141c41c001b0420704501401d903030b40001c40d80c50941203c2d090cd0708d90818a6805503410000e050001603100995074008800011a52440e0000f02c0d040403204001000203400400c40c2400303503a6506031400c40e640c00e001c1d03424074800440c2d240700d441c1000651154000c0e145400044154035401c0301003031160295080c0d480c1d04034071b03513038407403a42e500c0d40d60844c0500310320503019040c00214030b0303103d001410503900030401d44544c2d0ba50800111821180b10b15003042c40d9007944058000780307041206034401044400c4c4140c0c00c6080c800302038a4902c42511240300710381c00034041c5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 992724649 1250 992723399 992723411
    0x9060207060f02030a06051f140c06010b0912060712020306130504060501030b0601110604120c15270c0b0705191202070509010e2413200c0d030207060609 68
    0x15466960113103000d00400c0904000054440c004e010230741c5540030941e005201d10190344002c00d80709101c080d03c1da0f10303107820803414100d9190f1000d1915000ba00080451100824003201d203080c000c0c180c40700c40314818010051800c202001800650070308000d039101c07135000800115245c81d80c2000ca01c42d8024104100120721349030402c200100403c3c001100c1325800701c4049080d039880b40220800c00040400030b0720507622603070b03508080c00310002102424008000c0c4102d0218041c200380f45505088010045082015900104500030a0f1103d20806040c04a0000041203108030b603007017580c6145984c0c035079551507810218500040c8000c400d01e41e094107440d40781003060107001c40502035450340846014580b41c404009031035009009419010640300700242401d10640905030700208001448151071640201040040c90801000c0c2101038546081c401b0741c807400c207103041d0102103070101d8070306049400341810745880c4000d0720381c02016008641030051103036940c00340c002040301040400a03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 992725899 1250 992724649 992724671
    0x16210201090f090b040608030306010f0f03061a0c0f01020a050d0506060f0c070e0c03160e130e01060611150c030711070e01051002060124120e011d0d0509040906020706 74
    0x1a0030200c41050045040c92000510040000140d900400050b1144611506042ca007123740444151224040640700c800000c1c0c1d03207581444183d4500207005070181c2d110070345244540341c00c50782613000690342e20402034144000ea2120544160f01c2180c02d01181d41e4551000060071070003180520614101e0012382044030000001e000070803a04101600391555481c0340c5894a02d02048075000e84911030b82c8a00324180b8400c08199000480c000c0c43e038041c04580034400d40803154501401041a03540d80014042c5d1174004884d4071460343c07214010300480f100e1902e8a03059a0002e020700c1101d541c04004035094070301561006031080906400c641400e42e50301f100b142000400e00c682405200c04008001000344003090003816200503011400310b072842d055500759031240d0b0462001c100300d11010b1102611400e0300914655040060000c02d2143c40740400e80c1c035652800d1869181d5910046981480c03682110070794400240c104c5001130006014180b0304064414400028036131450040c80c502 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 992727149 1250 992725899 992725901
    0x1090b221707080d0207061403070201140c0c0114090a080a0207091407031a0306060f0103020909010801060e0f0405060718050301140106080114030a2d0c0816210201090f09 76
    0x1c8a0303510040b44c407900007429040c1d8640d1400e0040d040000c030041c500340c0b03548516000a40d0445454800012419504400c0740c0501070240ea8070032032040000b62242c5511000d01583c0b10502101c201c92840d4100015140c1c0d840c0500301004140030004510034a205009100b25802815201411710456544005841c96044103c5807103010a20301445c06000080a9645040895001d8010b00300c0d0f841e8101086803143c085184141059020800c560264451840040c002d00d80d50002195981c1020012624224000c20120b000ca50440c1008041080014900c1c1c00c484c6500b000100005000340340000b81405400540d0190300f0081c11f402c100d041011740504843c641d907221810383e40c0f04d81c5001c0840b00007840b8183d05603c03241a0b4008101488584d05029a052510110442c4101c0c444140c04804803070540d100c600c070303030010001c0e18424040c03003c4070b4040840f5000b0290a2031114242c9481e1009039400304092031403000c0843e4000c0c0300300e1001e004101480c01030140d83d090900 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 992728399 1250 992727149 992727163
    0x30a050303370b0301020f13030212010c0c0b090715050334050d0605030712050d051312051e010f110702010903020d05010f020f09010201050601090b2217 68
    0x3250325407200740c80b1101d810780a15580c40c600380d41d128418602c0350b019009020b000040c0c00d16515542c05c100c07040e80309001c000144040e0110030200241c03580346004000c50000c20300d60300801a410300324072820a550100610b25076907481040c03000342d0384450a20600e007683d590412441a1011115040322603004005907108080e20340c500b00040300c960103007244418800d041040100c0c41120300030451400303200030301342c8009203410010b03c040d074030000245404d1b80c1741e00c0300803080c4203071004405100b014410010070341c5142c14a24503103825100364a10b240f0b031612500b1099500c450309481004001d2045a0040f80d00c40608065510803040c403070300920861890820451500c851080b00b2141130f0151146a40c05840d84841e56155409002c031a511706281250359541c0d0380342138540110541b001e0f008050403440800d442c0c045420000e821182c0c0549401e040c004002c0041100b541d100e01214401c5041c582100c0754910316004a444008440d004114011000c0c2140d5040340700c00103980b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 992729649 1250 992728399 992728411
    0x90b010314010618060e1b030a0209120a03030605090a0b03060610050c070e01150c050d1815080f090a050c06092e080f071b290109110a1d0f030a050303 67
    0x40f8081d100d140310791720120751040047e40c101c0da0501c005051844168041d020b403039000303800c80f00c00d0b0b0010114107041c401c8000741100440da03504c00a20450a0507085150b000c0203c0104100300400c600000750399020050805214083c900e0200035481c0c4100709646407070541c2402c40f8003041e100e4849012540090084130020505000000c40700c1c1e1140e8202c6400c95000700241902c1e440c40c00c0111114040c125104120109040380040d40c001c010302a015040056a00c102e0b003410f0043c0343e0180c200000c0c06405080e0703c060054004150f02280351000d00400b01e401c1692000c2c0c9038045011580744005a03064000000c0b480c2c881c49092030440fa0441485940f0a50700f03aa074500b030740c1c089000950384000040c02c0300c40c101319140d031504240300009010b154ac039818154580c4043c4980e1070604402010010340500400c201c0100740105402441da840390303c0d0920001c1c1c5801440094060741c1d480040303c00940d44219a02d8501c0000003411024054405c004810b04005542e030b0300580301 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 992730899 1250 992729649 992729669
    0x603080d090b1f030b0c040f0902040503100606020c1e0a03030903052404080d020d02180a29090a080f030c160f090509072103030f090b01031401061806 67
    0x508184028060b40e540c55007501880003c96007507403100c400d140001000f107110818100400704101800804c0400285614080544d441f418402030604007024094488d00c0c440c200041400b07443c0c3c010561495180095130b882a861812140110f05507540c14001904880204004010325078410100800d0324082c0d0111400d1543c500010814601c4902128240f00c0c14280803500040c5002d0083c250840640c401500b8032203a80010710403640454450084030000701410540350070310110180c018003501010203202e2140742d4084405407142260102c002e02c0000c1c0e204115030b2001c03142e601500320082110840030310400c48941c1e81e402425800c0452080e1100400ca841e0713280420815217042001e02e401c05441d0400c418064840500410b14500503040042400130540d440c6400d92560444a900c10420a09025045170540440103561908081b00c05001c1041012420b04681d88810307d210701e1400c0c0700515004101c80c1d004031a46000e5024041540d0b04541c006506a6500042d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 992732149 1250 992730899 992730901
    0x608060d0c150212040806220c0e150a030c06030b0a0e090a1412040b0306131a0a0618060507030c0803010308180904020927030403060204081510030f060603080d090b 73
    0x41401c4136004501c240404c40e809500011011000c070f1184200c003c03092265902c40840640d180b00d40980540c2000549194100c02c0102004420603100803501f01903440c00e50303060640d00d500c3e10744400c500851003815101d0300601c0094507001c03100801400400641c00030b81c1032a0b040c031511604040130070350340040c510510355080743e00440d2009254207800c85051405203418940011500000d040c03942c842c03140380107980355002c1da02400350008140703500a164080300c030b001c00500d8411500f0880421100031228240c42d4505800c102c1590660b00f044c0307403101c03014a0211031005081c0c0008100c2800400004204080d40010b0106007002c2ea50741d0554040d00d0b0b051200c60302c1e003281c01071342c00100701011400c01c001622610500e811070070140d0901c40d1000d64082e285a2256004a1307a00e41d0004081014100501c070420b502c0d40076170404481070401d803400c00e061407660700028142c070180c610b040c001c100b480e5000f000291b6000328401d0301c480700400c5020082c252000155982a4194 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 992733399 1250 992732149 992732173
    0x6060e0303120105100c080706060611070509010308070609050f070f1205030a030b062b050601020732091302010e010203130b0903012408010e06010f0608060d0c1502 73
    0x710a0710b004001240e5403110903071a02e400c00c5207407504004400144290b24084d0008203041d1001081d51500404020842e0f6142440060075000e00c000c9070841d1fa00840d2061001d603a808c00d00c9411203804c56005505d400c3c10b030510170300602000c80000c1461182c49400100c021000c1403103003c959268060400d6559030b001c00c840000f041c4803004150707401c20800303002100e010f0340c48001070090280020f420303d0644240b408050307090b02500b42c010014140740034001c40050013541e0713000704288042c04400d4034080700718001402044185010125132030b502c1c10f0041d5178902100c0d002e4401020107a481c1060483c0c00614404008268000b6109800c90070203540000119011210480884441c00c0e15051010600e5040001c466074035540f10f02500103011594040e05110203003500c85ca807031741e0345880482801c40c3d4011041c80c2040d081500100066020a0210b00071100b090510380b05941c1c541000031640318400200522400c104003000c5080c0d0340640d00701d404101c0a4084407800320f020 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 992734649 1250 992733399 992733403
    0x110f0901062312160306050307081005090d080c0f0d0c0f120b011e0e04021b0d14090103051513051605030103080706090326040b0c03040b060108060f1306060e03 71
    0x44090f04491000030000f00301c013840c0d81801e2100400161078001205610380340003a0030070780142e00c2107526901441c5a01a16038041c81825041401e130002407225842c00c40c009014000000c1144000400119050801752008404c9464429000d02e04204c1c841c1d800001034480d4205007644000164944040000c1d950684075a02401d00140c5440b0341c408034241e11410f1400c4464503d070b04002000000c8202030700c41f800a02030303200038203540044104007206814940400200c3ca00e0400c0714035040200c04084c900107c5a21107001c0c640070510b03640347c9120f008451140d044040e0401c180701800c1802903d2544800e018500c9200c2007031642440308000c5620380004c1c040903100000400058001900035400741890b24440e062000d0200032140c004c1d060540203541c181800310481003048104800420003942c0710b8070b20300c0490706604041c0c0b14090003540c003c0c480c5040c0102800032918550340e115042c6501440284542410380481c0b0020300a040e03148a044003180040000030541d03e00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 992735899 1250 992734649 992734657
    0x3020703210c111b300c190b04030602090d0b041a10030201050d02132103080c0708071209170102090906010804050a2a031b0501030501080703110f09010623 69
    0x40c1240038210f800300e000400400540554a805c8901281940f0030503000310a000344269015507400380081800503018400d04510440024000781c2e0240c800307100d020704100030342e01501c0d0810001615241c030040420000382c803440c0040e002c407601204120400071201030890300c00c420702c010b020f0030b500c130302c2c04100082c1c10fa070200901003801070140c19051000c85e8050600c010700d5104403080c83d640e0307a400c2d03c0000c0f210394040802c0b6044480c0a801e054000c16002d030021150000c051408009850b0448180105540100f11021074952014814881c41401e006080505200c10b4018001041035000358020290701f40101c40002c00145a980548851403186400c4806004100b403c2d6a54201c0101005190010002800c0701843c0001000c0d10304005544121428610708070b005c140c940c40503806500450415013400c00500c0510800314226007141e07805024140200308000000348012800b00605030403141c1038000241590b0f00c2a00c44000e002e01150014880980c2c03803803005503110b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 992737149 1250 992735899 992735923
    0x90f10080304050d0209041109070c0302210307030207060b150d0b040c0503041b0b04090905010b03010504110607020402040902030a0b090c1815190f14090d020103020703210c11 78
    0x10b13400080c8000f40c18103014040d4014412a102007a082c9004006034241a0070349143e400900c100d6031140c03c068041200c1c1600e610300c000b91034103a45401e402c1d54924440186141c04050f0041980e208000321a000b00c161403800410011004402a04060064114182c00c001c25401c1121400140c200f03071080705411403035039603403514550303e07030300d824103000780d6449800b8140c4400240050189024005440074003450f03c2c011030082042e080031401d40d4080c409042c801e914102c00e000018044400f030912580041d1005c039150100c078000500240680ea0005110f0f5000100700200d10364190b0100d12035103c111198455922076414464540c080c18514800740d01c0c0c650282c240601d0a80360022100d152165a58a032840744621403150f0031140001c40e01142c96211141440c5d40c01034101004200c48203d51070a0648020000d034100c050385801a042c103034001040414548202c501c9000901002d054442c888001100c0d6402040d541d07400000068820450400c170100c04590310b07403a51 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 992738399 1250 992737149 992737159
    0xa060e0405032505030f0307031425021f0b04050717060d061e0b031b090c1303050d020703031d030604140309120a020a120c090c030209090f1008030405 67
    0x4900c400c540b1400300c085504640f03640340c20b4880e20b0000f1010402008903800640342d00ea01c03810005800707810391ba40f4403691786800e8005400c111145a101c0003032403201642c1c80b0922040d0b04000d005074200420ba4121289404034007614103054400c2e03821102010605450400c00e5554425040b10900780d080c08030100308408401050840c50319105600f00ea80c05040009414000303205030964608846040c3d9817420b88418500f000c81c5824803030300071240a041c1d0207980012114000500507000102080038000340416104c00d029442d4400b074010759030102c211a004240210041d503620064401100001c40d800d0300c0d0501072840000040342e1a9000d001806030703440e2981c580010b0106080500106d210610a03603040e9620201c0d1103441c40c1070701e80549440034060051180e544069080b0099040c0d5038090a000250138a41c600221150b100c00010f01d110f118608402900c15820074592201e003080912071100806507005004246250002007101e95503041c29441c2d00032449010f42c41 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 992739649 1250 992738399 992738407
    0x30105031612151b030509070e0c0f07172205010504031109040f022d100c030c08070b0106090e06040603150c050c010203010611190b04020d0515070302030a060e040503 74
    0x250a00e03030082410f40d0300500850711070030703901c40c0183c07803180b007801100066110350500208820070f00c0100050f0950070f4142d0032a25000c40900d07800c2c4102490074842c102d0002d00c6c0c0c1d003800700f109602c0c20240c14800142c1e0b80d40034803202c1c0ac0c01507520301300854803005c1c6400000070381d5800740003245c08580d88070619071280c801182c20400040341c001c01c20f84904515007407080040c0d4030a02103304844001c100001c0400070b4402c0ea05040010301040c5029240150354281c0c81038111030b00800c203c3c3e2510b010716000304945450025401600d034010040b08001001003451a0000c58600035200c14480c003807200c1d0342d80402c01003911060304c4090700d00c80044520300966130702500141099165810003e203005038511200e0b0899009900a20010b0516036248142c4002802070a0745003807010750f0507013101800d0b214040c40c402c025000920400c2ea48180d102000b4090210301e0416904581d42d207018640114040c0c00f0350700803520012030520700320000c1114110314400e24000c2d40c210b4011418 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 992740899 1250 992739649 992739653
    0xb070f1707050c0c0a080d0207050901030209041b150306330518030708030d06060932090a0e0c011805060a0c051c03180302100b010908010908030105031612 69
    0x3580c4070000b940307268000c5010741242c80d00e0b4001e000c5c009060010042015410036003009042c15080c0e00014401c01d0352400400259481204098000742c1110340c20400c103100384214840d002c003a034440130345580304d80c070254180358040c1d01c21000c89100102c1c004070454486509103100241000c2080540015511120074600c070704043c00100d000c1c13003604100a07502000203440e1807242c1e804143c0c1c9a00c00120b20b0002195802a50300074a80d6041100c072540c00c2034640ea400e0644c80a49000040c01801018010750f6034025600ca10354002e022640207060080340350020300000e100b1752a06214040c1e55883d10351141c2c44d441642c142044116154608000400c4200d13840f4a0355541005080400c2d00c000c40e500b44041284500b03000c1d081c9085075000c09011301030341c007652040002030524551f0100400d4000c10600c521003c0d800000441c9d2441d50016181440d960300000d00661030040040c00704280400154140d800031421170307260807603c11030400102000d00a2022140340340801c1c00c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 992742149 1250 992740899 992740907
    0x11091005070c0905010e161d0102120f041815060c060b0a030b0703050c0f090f030a0501050903031504021c05190203070201020406140712140c0d05040501030c0e0120070509040b070f1707 82
    0x1110800c14415504c8034034bd00c8103840f5503500250a081014040000c0400520500904072101700d50340318414480c13140301648800c4e2000782c51041a003442180080b00d001c1000c558450030480c04010001c9c0c402503120b082c10001f1000c1200c110300820325003000700c2c490140010507110100d41c11b0720380302e14040e0040c040c01400b1a031154220740505c034005164000800a0107003e01c5911440021600ea19011685038a51b401e035044050007603104124403a805000b40c100700c4414000c240e07002c141c2da00c4a15607403a4914502c03d200821520110521000390b03419002002118030b40e5a45e11b0110b003ca0101140b548a074500c010040ea00900342604c055001e007841745800c540041b41e407800c0c654440d0b006403c104400b03020000068000409101b55070300752013a501c2d0200503280c00d079400780c1c4140010705030208840c60388904800c0542c900b15500340070040c20300909006420710b101c0d03003028a4041c2e03590106440d100d01003a182e0403007610f02813195010003c40741c2c030400d64071200c0d200d00c5800c1e9 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 992743399 1250 992742149 992742197
    0x15060c03120f04170309060f0c0c100b03012403020d021903110a0b070507060503100810021e0304050709090206160c08060a11091005070c0905010e16 66
    0x86280428081545640d81c0701840c9885071003084101011460a45080740c4840d13440356900f41846803d01c20b100c07070428001080356010003c100050501d45440800d4020380c02011072441c0b0521400500407515400341c3c020a00d562800e5000380a03024030b04014101d030704500d030000030032103085d100108054a03042100c2004180050305c004002d29200e030321405440c442d0342090b80d500c80940f015200500704280504018480c3c600070a04290060b528147c48140511480c010000040b010400180d44c130012b010003420741e1412108504503031386880019403c0ba84c424001001205a03241c29800ea800c1124401e9030300001520034581041c9a500c0241442c1c04166004442405444e0300900c41c080b802c01da050043c0215080c15142c0224645000b0b0002c0018000034104030090f046213115000307032095248110344014440c8881101101c503402241405002c0700c5035034000090703000a43d80498143c4000700d16000003503440707a101980443c54095400002500822005806a00241d0f0a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 992744649 1250 992743399 992743417
    0x70c02010e04020306180c03010e010504110a0e12070810060f030305270405070206151c15020d050c0c0c180a050a090b161d06040510030b10090302090f1506 69
    0x411030700251304045201e01e00d0850700034290207c0000140030102407404101e00400e805c079024407400c0a002c80c50301c0d0b140621901001404020b40400d0040d0780d501c0d100550002c036240440e9803142c1d85505650ba5159075881c3c6540442c070702040440d84180c0ca103075010a894040d01e0380d03480c005007280600881030790074007504c403401900a2050000da50f94003400d8011a050750050009013400c201d20f242d6501300810742480707131070340140d01c00c0c00c60414101350703400703d401c1210341d9050400200f007000a44201c6400d50340e1146400c042040c2e0281c4003000d04442c10b6800102c607940c030300d180140214500c0002016550403450780c0000d49c000102d40149901c550740d94000708551040f0380e241804d4000944410001e0350799021005000380c1c2c4004080e001402c200c50036031001032000e000c28002e01c02c40c0038960251400c54603207240903000c0d420844078000e020b064140c0300d0100c0d80c001080c0c03a2003400128800d001c00750100303418554460a8600507054008042d07840c1e040d0a0402009521801207 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 992745899 1250 992744649 992744659
    0x1c0507060f110106090218042901030f020a11070f0e0c071e060c11120405010806010215070804060606020f07051c050709020705010b010207081f0b09090d020105070c02010e04020306 80
    0x181c40d000c10b10a009500c010b01c02030402684400c0b0380c00d1124414400345003800d00036840e212280528516080501d8074031381b402c0303510902100c10180124090300000351205020f40c0005000a04964890a4000520b0003801610030542c0c40380c003d40c82c00c7c0994810038006507900008100c00d000000010f000c3c891240780c80881828a0341c100d56071a00c80f0300c0c02558019a114424000383d600007950180c0020004050311041548004032401070103203008050401450000050969008101e0300c2c0040300a00d60400c0d00d40b800d00c00040202c0c200b1a0b007294030500301a00020001e0001800510342c240c0c500181098504210500451500341e801303408001305004c84c11004207005018802c09002d0750b500160380d4208500b03006080da491480014115801540104442080424895411401007021900402c0581481409040e07440d91180c0c2c4001103400340020714070006008100c0e1031041d0002d0110b80e54903402a40c14084410300640030410036400d010360b07480c00d0f90003198000e0000b40 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 992747149 1250 992745899 992745917
    0xe06090c2e110606010507050a061116080d0b12060711031b01020c28031215090903030605040e0d18211e020607020d0c0302060f04051c0507060f 64
    0x9803400e030800039041002c01c080c0c1c1c20100c000d4030180b010540c880801c0c00c2013890729810780c1e1650f6450b0f4406401400d02c0d5907445802e45a0b028000031507058624043c29220318412a0401d0b40e22a80301c010b1520010b451300021625a0a041407403a445001c01409460340b5038440806846e4046c1d1100d030003100c1d0100300000c5070081d18040e5a001c00404201c00103072556210007045140654a40a0b0001c140501907911040b0030b640d0b1005000944c1440d0155140708502c8607070300900826030550100885880020400b40425800100a05e001c2e41e014446035a0707490034802141c10031042900c0c55040241100d00740c0e40a25808100c0054100c00c200c06940d560320070805500030780070b14a2000d4415041c440901080409280004a20449080c05460f4541c00589503100f0780800034040c424100c42001840264820b810003580c0191506668002491002400394085d004203407007441d49120f2211680190f01e820ba59007503018004194060405105880a0012480038410804030f90 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 992748399 1250 992747149 992747209
    0xb09010f0524180f0405091c0210020d0506014113060c030f080108100b1c0b09010e060108031815190311270301090b0f07030e06090c 59
    0x88000c0407089820740c40c00719540c2650080084c0c104481c824240704504010078400c200401080b0412845001c030707202c0c025006034840c217a080203183c9019003511440860380b410b05100b0360f0441c1c4d1007034009a89038040006400c040d2540840c0b4011420030702c00100154030303210044210080036481040350814240b03072140e40408031140481c0c000c01d000074144880c0f2410184c03c08003140c17803121142059001981403484540d6510f00200c1c6100b0361580f80d440d10022515046040b0340030007614030740d0421446007070030031900b030010603640d40c0025841c0c40440380c1801c102042d600d041e035680e20042d61506001c034040510392000d05d10210307032040a00b08150000e0040b00c0051241194890141c407007548200c10103402c4889081648031306950402030b001082c0034280a4440c010403030144402c3c011000c80101c0d00508201400505110120b014045540799003a9584e101d030900e0340e014410281e00c14001501d820080d00e800321903070700a84420720b071440e00110b0340d0480d0b0070001c8036600080243c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 992749649 1250 992748399 992748469
    0xc0703090618051e0907090815190f0c0f030e1504020f27011202100809010209030f10060803070812040510020a0804020405010f3f080301090b09010f05 67
    0x1203100801050000514a555805c04418841d0b00c0a442c1c00c0c2034a250745005243c0d522090b9010091044010780d00020745031203150400b4481e102d011b4101081006000480440104071340b50541c3d0200c1d4441c0401c0804c540703e401788411010209000d000750740f50b200c00300402920060000c0741d10412884c560109520b600210850241041c802c2c0444245040007060f4030840c181c00640900110168040158540d03851110b010f44c520716140340c1517038903001c0407030080c01a50106607260280c20030300600b48000041c4201c1c00100030804000e42550345c480c42d0350302e10409500812049060100421400c4042880c43d8024002e90543da00284c0780340c800004c9912444000c4042072550041c041582080e101c3c0f5030240440040741d80c802030a10075410311111041096410310200301160181300c030b95218188182540200c5000b2656400d4a00840075800034050144031501d8014a030b0b20515083c01442d04880f408525030700124100401c0c40641112034810707405024081c2e24a415001c00 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 992750899 1250 992749649 992749669
    0x3110909040c090b060304021f110616080a020301050d0f030e0d23060910090f020a030308190522061d07050a0503010e03180a15030507080c070309061805 68
    0x2c500180d0030064100b0420b9011100450401c82c010f56080c020000142c0303500710702400017060078400c00b112100d041e5080380e00c0c2440c001101a46c1c012401404407445241584183d500c55503100c10005a407000d6980089010074400d0650112039034006c035000c030740d01280c000c415038003900c1c103401240605808208200003200046490000039080e40d079090300d424908601aaa40700050308582c140309045540d510111022205901e0f610070b01007081165116010680c90741c06400c00c03e0310342d6641000790078004202c45080350328030312800342e05010a81e48a040c0c81003091801448039820790030126140079000d2681120096600c1030f01109001d0b00600b0f59550b005044000c105060030301091060f44c04042d80018004c2e814914101c45811000c4203031041038412040e45000714020f0030000d5900e10859010b1700c1c8111200e40c6058103560f054011074845c50aa4448074801e07190301c1c041103107903ca40c05c80030b00000e00704502400118451964544220744031501401560307280d400007811800 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 992752149 1250 992750899 992750903
    0x8091201140412021c03110c010603050d020d080403020a1b0b0715060f0e060d030c080f0301080606010e0907030b011e02030c0d030501030f3e1206090d0311090904 72
    0x8411001c21042011501e40350040b140d0604c00351000ca02248a1049075130075039258141416250a0b5145401034440c040e9a440c41101c8002e0121903620f00b4802c0e1200003501c1420014003441c10f1412459018820090140b580340d4000c02031042940c0b5428000c0d907e810260504111020002440800302c0303004d01290740c000e408403804200c03c0c0321060308a800a0344410045000c03000104a4030140644c1140d02410542e031001203481145011101001c850000030b101c180003141051580c2d60074000b40d4181c0d1601c208580e6140c0f80c190041d655558010b2115034002c4150001640d00c0b8403e400c4069510018104030b95400300000c810100d100000da030b19001a84040b43d285a010030400512240c0700c1c0c6418108036550440d299003010649100c2c02520f002c0007491489102d4401c00103400f500e86900240c10042c2c81d00115408e8120507501d001882030742c1481d00c07407101000100301240551400300013002c50030441d0b40b094010f0203011400071b229140c18444c0340314540724002c1c111b01c01c074 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 992753399 1250 992752149 992752181
    0x5070515070215100f03060915060f030b01210201110106030506011d010e16080c0403080d0506040b1008070f0203090a03030e09070306081504150905011d031608091201 74
    0x100030030030043c82c03820007080060601d1000d90b040090801c04107900013500d13000700d0082010500d6003400058100c3c646040903105141260011b411810b0402c0344c82900d10500000c10580d070382d0000516804c47c44040c1c03059084544955200640c0194102201c0700340b0800040340095898640300d01b4038409901030182d02c13102400700359095081e406500d02411640001d800c0f10b0421405c1000d00da00002c0c0c0716814080d00902040c80018240c013614015580003861a80d1b0716041d00c1c40c60080d140580e003040c092800d215a1401030314000d104c00000003125920301a1590b1290070841321605142455801d5000410203030840d600e800000b1006940240c840095000c1c18400348080d4610050110040600c2c040d0244143d40c80402c1d085a5881801a0b009c903544490404201c1210400c00c1000480d240840400802c01d064000980001103541c0c84070365412030a44c0c16440e440b8144804900b003900401c4880050050800740400400140c010080103c181c01500e0854800001d08680c403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 992754649 1250 992753399 992753413
    0x172a1305070f0201140c07030c051507030b04050702010915020306010c061d1c0507080307030605130902040605010e1309060e0d030504051212060f0622031103030a020706050705150702 81
    0x2843e024000c04901e14122400d035003d40c907040c240400680202c02001b020401d00851080a00c1020001d0400b0800440f1608041e42080382010b030040c4418046140103a08020000b0b282c02e0040c03061280064100514002085400f01c0c40130080d800240924180118640400045500351141c244020f814488a01d42540c40e1071082d894030700f14003c3d0014555035500301444151b0301505030f907041c65010385030380d40300c0d00c400106601030400750b0003040d0060102c82542c9811f0005411032550f03580240c400f04903003511103004540d00c40e80c0900554011155811203031000304545e00030000300e80034a000190306075102c020030f404c041030300400000080c0c4841c02d12007401810b110100055800200d41c0740b82000c112a04000c0840084c40c542c4520088511403030582c5403103040740c800f4906150009620850b4007813200140009010a50b03600b01d50701114226410000300b1114141055001020090302d002c2c411aa1a441204121101e020b001041841880740701031160080311150007800380 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 992755899 1250 992754649 992754677
    0x813170a0c0515040314090409080c01090309050405060609011b0803190506010c021c0201020a0501240b0c0c13060810061716050d0c0e10172a130507 66
    0x181c15504100103d55500201c02d00c8000707508042c0f044a8145a9a401703030721140464001001070408040250105030002140f104025065000740e2802e4403a07201d04058a40321010310040361400c07900c280c1c2040003000008403540c001c11010302a50300b810700c1c002c110035850351002d1170f07901306540c1162148601c01510f02501c94034020b1a6001c0d1080ca080d0804188980000300320082103a0084101228205030b041564802c0c894440b0792a0008001d102840e01180456009078000c00c012140703107001040414407180400403038840003103020080000070540010030806407414410000d00590390b21000484800038402c85018000c040000202c10346841c0c81410400e802101030740310380d04200f014810200c01899100c09880b002d45e00b0302c0c03d0800d2032600f1040312401c2c1e0003100400a1000c04c012503a12415228070a030381083d050f580704d008640020070360300c50304003040410b80c81c007140c414290b00300004504040c0e44001002c1c80116403801c0043e000301d030800c1c0d41c59400130317040c40b4501d40 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 992757149 1250 992755899 992755903
    0xb060408011b0201050c1e090d031d030f030304110d0c06030204061b0b0a0209010c1406040c0f0b032a13091a06091002150f190501060813170a0c05 65
    0x1001c403040f400248018580741103410003901c04c042031547d404800049a050071070030541540c1038001c0c003901d080003414403414080e208001d0180c03041041e401200008185050101d2180070b1900303208000d50840c0c56130350310b19090b00c0341c0b400d006030042640d51b80304011548400800005080c0c527200140d0300d90a0400052403802d401b600c2499a101c407840744d100260710018444d5101034000001602c0c3d170701d0f03900100d038943c1c42e00300040c101407581c58034a0341904c0089001030042d07203d566101329407580c81a80b0264000302d8811803900c3c107820300c000b48103200c207001504e4500d22845010009501000720603a03168000400c204003903814400144000d840074441c224401241d0954041004d03256000106a8850302a160b4050720072035101c1841303c0d000304480480300c148081001c140b403605d40c2600043d98411904441340c0e03004d00304440340034100d0784110ad0580344141c3d6503822607a00d82d8076580045491138021a0072551000e9003850000c42c86001e0280340545a54500015019003401c034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 992758399 1250 992757149 992757191
    0xf070e01080c0a0305150438061801052803050c190302090406030f0803040308060a150507170a020a140f060106080c07050307060b122e0b06040801 65
    0x14140680c0806009080e49102c007540c01ca5803182c80c0102c1c4a98a0722140c1e0604001007400b66040f0741401d40369040d2000b01441814402c2e420743c4001e00d081c1a407100490f40080e000d0380c03140c101c44100900141451452104402ca00c0103050142c9004a1301816002c02030444991a031698a0300180b1180c0c0c946c035000c0c16030420660b01206003841007207a22001030700c00840d030310f405056000419a64a4880d074001d000110b03008042801d001049003044580c0c0e60040703400320005829200018481d2030700c102c0d25030a480d1855010400c9095254054480350b001c508207a811451408944042c800d00d00e0042c40c400195034003411080c1c55070b2400d1070250b03440814104503504521045010304500041707490460f003881c940900b20f42c40b00f046c8583e4a2082181c06071083c04005007a4090240da5006448812415940354824a9030011440d49544070000100040b0341300081d40030340c08050444c00009034880b00b41c009250400c0e10700040460703000e80c0c0329540c0d99448070703a1011184169220b070 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 992759649 1250 992758399 992758427
    0x1241802070203120406030c020d021e1e01020a02060c13031101200f07060c05190311010908030f09010e0d0e06042c07020303011217040503010c0306081b060912010e060f07 76
    0x40110038060100691504ce110301040d080c1506c0364609904414200601020b880321100d8400350b0155404465003c0d610190b100d001512a40000c41c106080d4441221a0307084540d10301c814490842e55030f801c00b00a02c0442d00c0c10017150301c1d1600d656064445010394204805001414500e8105015900f824280d6011509226031520344030080754011441900301d0101c0100d01005244600d002d85018400c110701c0070080d8071300f04041040210110085004200c0000c41d44d0f071a03600c0c182c0050980d16410100105504604090f15001d801070a0701d00d41400f00034900c504080d00e802c00c582c08500002c1001d40100110040d10014800c10441250055901d1015514641c140386450300202c0001400500100380e080d1491141c00a20050b1400307004010024040c0c0400c40c90002c015240c907003d1281d09018400ca030302106101001c1a881c9008040c0219051208400401c0790301c80e44551122110f5499403014011510103010b80c07032240c4041041d42c1c3d054100700780003c000328080254 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 992760899 1250 992759649 992759653
    0x3060108102d0606140711090c0c0706020c03072c040201050409090c1a13030f060617100f0b1e04020705030c150601020703150911061b01241802070203120406030c02 73
    0x346d0404035034500d0b0a005440815624111300b44c88082000c0b207148070300f4005411500510b90003090165011070100a0654128221072096448010312141c2a013018180c0c2a48203480c00b440d6494406411582d034058014102507007000c0d0345103580d00588094071011102260610800d100744801d0030149010140d6402210b8140305000e040c0c02013450746c501001d060900344407960000c0005d070380c11002c00780c5540342d80c4000307107c10284450355422605100160040c01d00340801c0003800d1511072000d90300d5004120910341c4000d0485005030321803050f08181c20030b03002c02646000c9901000182900e45000e0028021903420766400c008501c80a010b1a0454004060030004241045400710000c01b003420001031071544e038500688179007240d5a0503604504046507983c0004055030f028551650042c000344250000500c0080703aa524592207001d2450ba92101403061a05c0450aa00528103183c801489d04041d0340000e80741034590301d00c030f002103140094103101b80780e4540102ca00500305800 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 992762149 1250 992760899 992760907
    0x40914060f0d080c011802130e030910050d06080a0b0a060b0708160c1e0b1201030609020a0308070f120516261903060503060108102d060614 62
    0x10078541d4284000d0b84541040300108060102c240e04035401c101c0110b00810100c0d0292601c1c211190a002c820b81c8114240e02c0b9060600000d8051052204c9100c406103251030718003000c020140d08604508010072000313002d07282486c102c80c891200941585001040c9400c19442e040017540401029184043d091200802a0000c0581501c00061f8031000d80b9466004031900d032003d0001080c00540840d035003c50000c0da040d8000c5101058030910301e5003440c080d4a800d1214a10b10541411640c032a41c03d100403c0403030520362100c0e02d0144000c041d050320300e640ba2203c08047d0003001013a1880380304440c1440c100500004254078070f0403681441801c20750b440c2c0700004100040c060203081c051602080440c5108400300031141082041c2c0700c5600c07004900c1802c540c0900390401d140110b840d0401c007060f103150002d00c4074103c0340c240008005002880d001b0901a261510054079040c0e204515610070aa50140002c5003d4a02c00700061a81c503041c002426070040803000740103020100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 992763399 1250 992762149 992762161
    0x120112030c02010804061b270e130201020a05070b180915040b0a05041e0b0901030b2404020f18060a39080d1a060712090317040914 58
    0x29100000280c090a180d43e20317544030700340320380a84254681070708a03c0c0e640d807194040540010303039880c152003403100402030054000380461000d1000d01442c180355050310005111462604040200d152061040c3c0715000400d40d60a4a0207840d81c1029204100c045140d076980311210041a000740001c45148400303040c008031001c20f5001407820103000c1d030780b0780900001b6600e40350412070080c140a0010803080704081e0700140201075011400a255044c28030025241c90540442410b80360040e00141507900c420900340e991103001e00300ca104046c1c1c4288000d0550752280301500100003030070703450390b80d50200c0318050039140c0c40421401d20551062104961240d07200515140d813800c0d2071020400d200b400900a9070341855800143e00540240030028200320a40d030140045140d85442448411304107440c400c500d00c0c071292440e41050040c0100c0c00443e0b81d50f6590700c186421400d0103594144c80e52141c440b4010308410b000b0707201c840000e04000008140c8a4440b02c1c49000b400060b4a050407 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 992764649 1250 992763399 992763407
    0x40e2401060f030905280201110a0b010b1b15010e07021218010207080610080d0e060306040b040b0a0312020f030412030f2106031a161110020d0212011203 68
    0xb1050120405039184020810464108010106064115110301c00b08500e14000c1d0200c2414000803070005003521484281c7c000d001644900041c1d1000ca041c50b180c4c201900d4007a550454a44028602d8100e402c840e5080f00521503509401d41c02e2110203182e6042504820700e003000505290110352041c40f0074005808110282c130b418a1110590040d05a50200101d10b003500503003041285014801c144610340c40200c0001080302c4442d002d840280e00c401c0f400381c55801c821808507821210030000500107280070345c80f2103c00c0000400c005808000d510104100c2c0a030344c0c0048900225451000d1a587e404000d61a03800102000862506081c220340520408503031800170144030721800e41d9400b40e800341c28110042e0000942c0030701d88400780b505410103490745101c10344808180e00d07038013088510407050462240b41a03283c541c54800e003490307048984014040c090240e034010b2440e02e04480c6c0380ca0004000042a000000d600ea500b04150b90084420680c890012840c080d0441c0001a400c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 992765899 1250 992764649 992764667
    0x4060c1b020f0f04140c03090f0a0c0513020c010f1508281e29010b03040b04050f0d1805010e090c0310180c03050106030509030d0209040b040e240106 66
    0xb50303092100039606401250245c14001c003500050344205c020410b0011410026620a20400c0202c400100b0141d4819444803580302c0080d04001c2c843c001800181010211100d01c01a071020061030248040006803c48003a1802e41100c60385544100340e8484c41600281c0c00303440b600e0080c000748241000c4240c6a18082c425400e06d450050004005011440701103209800740100c10815032130741842c2030003022000040d80306080401490380c141e182c1710020014141c504810000d851602d680e00e4400481000030400c0350a0311035000c04030168101408200480b83c41600c400c2c2c0c005000b00c0007080501d4050f004141080703c4c80003234082d2503075003030040e98101003200d1501c0d640c0e032600f18806400300c20781e82044510035410031302d003a414121507100210844c940d5074100020b0362039100860075507030143e0344540300380e0050109a6509109900411062400500000d41421004085003ea6450401c9042540c1003a4002e1143c500c01c082c40301c5a160424815002035810f00c00040e1100340 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 992767149 1250 992765899 992765929
    0x120c0d060504021212130608060108010b0c2d070e091c020a240b030c01210f090507051c020a06031a180732071a04060c1b02 55
    0xd20381d00814150744400304455a00384076041903c00343c00d5119050a0107901041002034075131404100050700c90301c03034582540601c070142e545850a03480d00e0b00040250304140c020754050f006100d682c500541122881e0042c92005080c0c00e600c0c104021070560070009923a0004c040d1303840c850704000f54032002144064810703d58070548104504240400c074941049510001e040b801055060003004189510034401e202e11220144044040a07081c943c4452800700c803603000c100c00340e51004603041c1961b04a00410b2966100285101080703400d14180c0e0b10040081c0d4060300711903804d100a00b00012100c010484490f0101d0302c4070500e40c0800c50003105441501e0805540b103000c801040380c1000d840e120014000d01d03203d03441d003c14003002180c1c03009442034008600e004c414015901e01101d00da40d207441244452404080c0307041d182000540c45203c00300d500924401c0b8503a00060f501050700e0049010b008001441130018002400d61180c9210083c0d10141000745c940060340d0b00c00c5284450030f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 992768399 1250 992767149 992767151
    0x207050309091008030304030e0f010c02150307121802040b0a06090308130306091a0601090305060a1a0a0b0a2307030c1e11130c09092a050306120c0d06 67
    0x140d14954040350f9000140c100000601000003400309060b40000c2c41100300340c0840d00041c00840500066403402034a1400035001200350348086c00c904104406907074800c0c841d0a284900c00c00d00c040700802c584100c40c24082180101c0220f800b90f051034803681c043c000007514411900c0c0e040c024082c0c0b8501c00c07440024154075000807003071441c007250085100110b900c200184000c21581c6058902030b0034124000070303c040900b0014180c0e6100303004081c1202d400c6006410340d0f440d042d80b0080a0b0044e022446030a10030b0038150b00c40c2e9211090311400405010b04e6054441c0b80408004103412820390f0100403805014910240e600c481404980b215541410451206c0c0c0071840c1c28003182c505ca20305440304140c8200a80140800c20480d032140c440122145119440014101400c498000e403036000043d9074414144085541c680c042180c0c0390000382c00e54150a4090a01c4e003505c0d03500b0070044002107021060042c10b003030003940c0241400509024010051150b00450000103103003402911203 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 992769649 1250 992768399 992768401
    0xf030a02070219091a040c050702040906110c16050102030906090904020f060f04031a0c0703080903130902090108100e13020105071a010e1501170a151401030b04020705030909 77
    0x10342c1d5034801e86010865245014400b04da0300d4022400400000c1035403090003003444140300b41ea1800341f0035101c5603039660300c0340d1303040240d95024000180040002211100d9940c0d4032a490001d0440203021507462440c020300c032280c20482007156090392607210505541c41800720003541c0e512681513825001c800d44116805940314000100090f4103031001e03a4101d0800500b18000e10850802041070700c0c0610501c140600c14542036108140085800c1c504206040c0814000684580713040750300181805c007202d0810701c010900180580d41e540c401c4541e03550004e00e11070300d540c0110081e82d02c0964000d41491540ca411400301c100040140014080400e851428085a01460544249c3c40d003140810302c050025446d246035001c0207008160241501030b001070044490b40246040301d20060b528688040d1845000c4010798001410f481c140b2501e0b5220441119991601700c801001d00761410b02d0010f944000240848a0f0110220b01032401000300c41d011480001c110b42c8031160503184c4004d1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 992770899 1250 992769649 992769653
    0x11d01080c0a030f050a1b14030a0e030c0102031509010509160f03020f0414032b050a0e030d030921210207020a0f0306061706130c090903020a050d02030f030a0207 72
    0x7482c201c1c04d2400d01920700b40520540d0284d03584803100310b1150751210f9a888144100076120b00e8103410f060b8280260030000245a0030958100e0108d14045008507818156111a214266002150121074070586d55648081a103050000c1a0040c0010f564008582c249001907500f2501a400c1c10401d00085519036a5441d100e49c0c100d94080b00300c00c46440d16640c90f2100300c002d10b04900d0059100b80701d00e80d4000d406014442c0d030040700006030700714658104402c100035209a044280210240400d8100419141c3c5081c405c560390310b801650009448150392901c180404a40c610b0001c1d18900ba83c456600980c00500c00f11060b12804006036920072402c900b90042c0c03180c0403000390003c1d4550800034190091b80316050503a031048105200b102d4481010b21409070324000f0704c4c070f0103500c92000310742031450008240b44820b02031000410501e0311b03142c98005071070303500c40200c00580c800a01c003c240038081c814440c0c0803500d84081c0d032a00e58000450b1015002c00341149031819400a02a02 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 992772149 1250 992770899 992770901
    0x702130b0319060f0e03040810050c16080a201e030c0304060f03060b0a0e19092306100c0b071707050705100509100b2d011d01080c0a03 60
    0xb180c400c4080700d034a4410061070a000602000c00f400344020b4280345000300c0450020055606480c00030004020821410702840c0107004050844890043c0800071030074900441789203004040c0c000c0c00c100c0c0d51040c282600070400d050b1001007110382030500c0e104010806002c1416425818507100d000800c0c028080e04505512030000e411909100000e0001555a0484403614004160f07490800c400d40d900c1e0100364140c400d686544000640023580041c0c14075003420303485503080d22400c204e256540c5850f8070304201c5c2c440c0c1d00612a81c10030711841140c0303022161001607200c0300581e102010b803c00c0c0c142c00340ca654440714006185103910000682101d00c90302d102c1c10024103001454416042818014003140d110304010396032800b40f81442d4808000e07a010f024001c410800061880010108504d402003032001200c0740d00c041d2040768030342c800f00d0110000040b8814025449410031401c03001604580d0980100b00d0381600380b4164290aa070043c5089031703c0349074064040d54405205070120 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 992773399 1250 992772149 992772163
    0xa05060d0f15030308010b030106020607030c020f0a0b15040603020f10020a050601091b080f07030c030b130c0e03070b09130204030b09071721070606050603070c0213020702130b03 79
    0x208000307142154804a2030b5040e19000d0071240079490301c00c3c0c41d0343c82c0c4013608000c0c40f0034060000542c2c0020003250905101c0da0180304000b88a00c152000784112101d103504000307480d0015981c000b1101d09000d49402480e0800c00c04000483d4100a01c0349107038081100d144203414424402d1008140103002d4a0082c08502c04482e48041074509640c0c44051150040c6640180000c0d898002828620140c0c01031540e1800f03200103461181d666034030024120060001010b01c1c404050710b0f001021055140c80c0c2800100384031048001c030b0900b520f00e01c004d203401c8420358158407a90251008101501514080340e5007144291179040d0701108210303181c0d0181c85168070003000d80c4241410060211400701e05103007980c500d120711007044c42904e000c003581c07400c1041e8064481c880c80020340c550601c0500051000511070f00011841c9981c600c0002c0060b0002c1790328102090b1990004021032408001ca9100080e080c802141003031030640100d4201e504c10f4042c015803a40e07850307c0b0311f203a40d8100900c2c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 992774649 1250 992773399 992773421
    0x608120304020d1b0f120209061912050303011811070b0c070b010e040611130605070218010b2d0f0313020306090a1b0302010c020613050409030309120309020a05060d 73
    0x449008402511381c090352001c0381700d200400b0000311000724010503201d0300042595001816110303207448034001c102c0091003461502d840c10300181c000150b85c0c5035228001c0600c50103440a162650f00d008040108658050448000c603880c0040303005a280596056500198112641c10050342e54043d80b00348510880d4805890040f00000014032402d61b80a414800c62095000740070000201000103103500400901741164660b400003403010318880c0002d0881c4c2400103210b2601d171a404034843c03031032000c02e8100300708104000401c1d0794108800120300042440008514099802070040200203010305541111001c000002041c40c0014031388401154036002004d07110315003009440b660f51001c16031400c441f0b801076002c0455000410b0603045003129010303181c0c0002d1490035400c100b65640682d00010700c2800300040426103840b14402c41e00424842c0d100003803468401c0c01c11a40341004184040100340c2000d2407440180c079581510411a842510516116158401c60001404450b03203c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 992775899 1250 992774649 992774663
    0x31b0a02060d091a0609070302090402160c080f030a051b0f06160e06040812090105160309181503060b0604082a03030703021203100e0f0702010e010608120304020d 72
    0x20080325094030360014a0f03ca00c103000c0c04509445850041003070290485495038004594000101041d0080c2c00070b00074400700502c010301d0109202d44001c5000d40b1070745c0039100171a5154007841184000c001c0250560384000066041440c9070900418900c5401c50301081c0208000d04014011810844007210341c916505035101494810004900c224820070364070b0000d0188085c1d42590704010007103505540c506030280890f2144280c0c4440c0603840030b40c0d13441c10003204000e000c0c0f408101e40c2200130030b684640c0d01c41c5450f40c544082007001d07180c8420921561444d106618058010341080c0350f08603030744030708003048005031345000a40341d00540d23220001e24000d00036400c0714840060202201040100c07840700482c0342041c14996a4041d0500040140c0e0000d840e03071403101c500901542c3c1c054015844407030095183c01c00d02030150826a003900300c0c2c4c1082d00901c80c2c0e0913020b000e0350080d100000002c0204c10701e419035003661062460014040d00200001050030342d00c440c1d40d43d40300b16800020b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 992777149 1250 992775899 992775907
    0x50c03370204090b060f12030d0c05041505030103060b1c0b060105130b130801050f070e0a0b0f0a030f110a14040b0a0507050606040207080f16060e070503010b090702031b0a0206 78
    0x510104c076600c00c4842c240b080c001c2d5000d0004600c3e000c1b02041c901b4410000031803d017005101d010005100d01c4402c50180075080c400025210000031040c03103c00040c2d545c85449500d1072901c4000d8805c074090b0103205401d5014405809030781c40000c1001540c10040c1d5006070f85941c80180c0c1c1c0703071142410001e941c0c001088046035150102e0000c00041800300e01d8058510703503892040e400c0b0394054403400109500d080c0404c52480c4116000d042c2001d00600d201c200340c0d40d441145225a0021454000c41440851481101e503007620070100c04403080701e804c0c007142046450f540c2061064480c2181030080c0406040a140070500c281e801501c50b0031145550741d0030854015020723400c5800c00700d6035407066600041d409e003010300070f071003a1035808031410b410712070240000401c41d00203100d2036006a082440e02d4001c941d041c00307451000e03038422000d4809541403409060940d4450b0b0f0388640255001c80500c000640e0010448000300711444081c1003501d4003a20701801d20341c403404041d6200704046 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 992778399 1250 992777149 992777153
    0xd1a12010c0e030a1703190219180b03010b1b0114190c0e04090203030d061806060e09070309020d1b06091401090e06030a021c050c0337020409 63
    0x151014140d5101c94440b40507901c8000c08141d510402001c0041c1441d852143d803103100804440070316089444105540000c09480032008202e0300003c1c002241009421651070342d5030b402602c3e403100150070f507886400711070400f01c1d41e080307502c418403a0240b00d4800040c0f029504240b084201180b80b2024021703c1503969022140800704000c2d2014110004043e10043c0c00064600c910201b03412542c8540e40b01005c14401c020003000045010f0b038150208020380c2c24824518440d02000d01100044c06e840c0700000c08945c41100c2240e0402801d20064005c00360345950351407421032b441601c514011400b0b100510104201009003000280a1030b494070032045107a12503100c4d5016954180e40f490406940c81f0035007181100380c003610a000c103480d08014005043e45c81a195801200541256545a080d9010401200c95031802d00709040c0c00c1d00741c030400c0110612068904c074034101c0051219070082c040310b01c48500710070005004654014130021800b21400110400150010401c00c003405681c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 992779649 1250 992778399 992778401
    0xc180c1606241a090d051005090d0f0e09181c03140105010509040c140a020f0105010803091309020d0609030e0f030d0f21060303320d1a1201 62
    0x125030302d0328515481c048801190003071010560403208800b041c1c5101d014400100c1015500141e0340355001820000140301040080084004540d200b002c0041da034980403042c5c1d410280000000c2007001060702d10002c4156002c0860b0706120b2084a040130b458480740c9120701d240030f4021b8040f40390300601030f05020340d0041c60300e04003520403552001c0c0052202802014001402400369a01141052000348140e08255000d03588814050400d4122100803900794601e61b042401c500e07005034019403c800c8564000e0189600504982d0004c504159440700000c0d17205c8002c403d42d95003265101007482c103656a9144290360396411900811003c5001e06004150720007440e540c5018a2220702c002c400d45c200080c0c0c060042849076180300c103141c10080c0032104030011058002d44080622040d1082000c01c1c89190300552094454418040c2092881c0c1d40c0a40942c42c92818104516121a040300d085c034201c0315410414507000600554515100c9450880c2184803608000d0542d05c5810b54130701 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 992780899 1250 992779649 992779661
    0x42d030506070e06071a06010903051c030e01060503031902120a0503060f030a0302064b01080601030534090606030f020c0c0d0f06020304030f110c180c1606 69
    0x70780d50703200709060788401031105500c03c9103030080580385016420000003406d580310a0300b11105141159030240e036500ca4031315200030b448500c0b140402c1c4141812000e82c151180c41c42c0058564002c1c4290b9142c04002601d03805401442022490822100d4040910034000d01030204031011103151200201e401c01401d0b0b4208440326401558130a212240d13529000905185a42e8107600805940d9034480c0e450b40720002d924a034510a00d050310b10611825005401a08042005070940e0314a010a202d10100684183d1054a10f03810810040c0082240800d0450020018401d81d814030b43c4560300c00030f1300000f0503107030629801102e400031559104603000714040b01d42582e01849814404241d9038124882c501400741b10b58070401300841c090900c00341e9010a46e000d1454030000c410251240340c1030768011a82180003030180980901851342120203140060030350002071846200040204012448003029200d100099600050340c5080b0041240c3c58003180c1d807030040300b1150620303100307015102c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 992782149 1250 992780899 992780911
    0x91501091701060f080a0507051e090f06031c0e01051c0e1606090e041101050c0d0203090916050a1101020d110d0518060a0507201509060903042d030506 67
    0x42c903070000205e4441c00142c0d60714958008000d0414186040e04000040d20000180040c40c4ac82c910300058941e10781c070b138040c4210321445c8502520b160403c101810484d00359000301c44140040401e06185a1160303400d0140c84081c28180e9445008080e503041d0406c40c1c0380d00d240304500300060307070342c090710089560a91041403030000541c840d1245002d64603039250780171b2215000217690018012450752600451580e1040c10005d1400c0780c2407a0240c100058612240d0151f400080c0d140c0c480c1c2001403100c2c1c6e10008403a40d03580035240304a8010558800d601c440070130042d00c0080030107001c10030b41c1102c403401d004a400300308808082500344000e0700503031a070301412807030103001560100441044030407203841c0c00d001d0810707a0344014008009041c050215801c010700c1502c842c2c056081c840c00050104851b0b4010b0201c034007846200c0805480c014409810364002d0303014440450000002e840981e407210b103246200d04048041d1100403d44c0c0e805054040ba109031001080c01742c04609180101 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 992783399 1250 992782149 992782169
    0x7020a030306090b0f041e091b050a120605040219060f020f06060102070e040c0e01230118170c130c1407150902060c0a0501020901030e010b09150109170106 69
    0x150741c41d01c2450071140d1320140c45801101e4072180d22107031b01c0c040c0c0c00590078414103190321069081041c115401c071140c0a2088854007114450442c04500e0710680000802c01281c2c2110b0311802c0004443c13212040403401011140c03550085811581e5503038521141001c510304000020f55103120092104c1620b404800250007031003080440c50b200410841d11030001038004043c2c903407078160702c004201c800070400e503102d403005840440c0c000c0218080710b00810100d020700b8200c1c02c03020a245c542401d0907401a05004000842441d040410252602292190403140000f4008004010300f400300c1210940e512400ca0050450101c186921201105080d070b69412041314202c081407106204045014120781881c6036501540261500141101e900c054103181c20b02d00c84040007803401907001021030301e694010403190f159585c14451202d0701c8242500074845401e07075401081c01d8420190204800d0a042e2414210a9000d003c0c41002041e509040081000151520340e00038101c501a2154007 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 992784649 1250 992783399 992783411
    0xf032d06040803040b070207180f0e060f31050610050303070309090203070306051e040c14030a1a0d0b0114010c231c050706060914010e040f0b07020a0303 68
    0x40100055281c070a9501c41c146038590b881d1516000e10880c401020101180320b051804181b0b54080355101d400e41952500100e4601e1000081c0b401f600c2c4450002d69445c1c1c008000c00c1550944594403d42040104100c8280c0010b01c82b508002000d5220341201c1e00f820401c3d4980c1003040000d5441e00c901008c84204503401d880340c1c101901c901c00d1b00c1d00940024401142846000090380c002c40c0c0140d07680c1000254070f6694030125031340c0c00c030314080015090984c0d00c4001c4e4a0809001760305800b903940c41c0145c040360a00c0300000f21400058402c2400c42d6a0f01040781c0c1110148520000000740100700b0307000c00070030b407804002c8103a09004540303104a00f98100002c4d54064148159010381c03150001d94020f0000a00b52880400c0b003818809070b103d410000c95980d8040d0388040c4d0a1085590703015600c0e00c403410f20606031441035000c00c040b145450403505080c4d40703416107181074401c801c0d0804d80039111810306060703600b107002010342034050400920803030a4000400c1c2c500c29109071428010 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 992785899 1250 992784649 992784733
    0xc0301020910180302120a140115030b0402060702090f15040504030f2601090c03051005060724150501081602070b0723010e120c07030305090f03 64
    0x380c1c0901c45641d60044601e04052a042d40184141141c2d519403010607065599aa00026407403c4110200f4110790031103c5900144403008094010300c0f50540020303c141701040034813104811244c4805013140e45d004010504654480086454030f9400600070046410b24140f412603414080d107140321103134044001c02c0e000b0b0409008071440b4a8050321a11000d4070402c90580e00c441d81018032600c2105044410f50032400e04400ba58041c01c0c90ba0400034287c00401c0002c0c040740c03005440001070881410003004944d0316002100c9000d41e0001c6400003054010300100141620701c50384000540c142801194a40c90404060307084500903030341d04140703850304502e140c034480c02c0f030b40e03008016000803005019800c5090002c1c100640300366902585002540c00b100680a200040000240d4481c07403a503000c0101040740945448040c846e65151035041001241d441410b0b10000b001c2c0100442d0000941c1e90381100d48040d044003030280d6050503d00c0302d0f001014a0390329085130400f6050310701024 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 992787149 1250 992785899 992785901
    0x1060215011a0d270b150f09010303052803202a0a0b0f0403140a120f0209030d03050a1a030a020d260403051e06060d03020c03031b0c0301 61
    0x248050509981e91500408010200c0942602251600c1c4c5401040100c82d654404c204d140d40e240d40558003002050406101c131781007869131840803034407414403203032610080e980711091541100e502d410941d540d010b800015401300003420302102c4581c82c0c52051211040d0b015000368116540900403007455070369558907507401d800b0340c0c4001540011004112224060422501111207550030122a0401002d6440c00880c80088441d050311003024000d01c4101a00a20100b21070001a4a140d0800015890040842c90301c510900d23a0591104c442440000851341182d0130b4020140a4a044016020018014110540707221441f40d00d010340480f51001080d503c0c19612800601904900580d502040344811041006070b4651111009203c1c10b80c41c41e03010205086102c1f11000d44580c0766042081c1480350031694038a01c4911078001320402c00001c1a001c1d03124500f00c49120b10780b4000e040403071801c1014180307250907100005188070000100591301e04c60006880481381502005000c0c54 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 992788399 1250 992787149 992787179
    0x1060f0314012007020108100902070c050901060302070201050703210603110f0f060702060706020d020406020703060b010f0e06070c03050d0504051509030303060904110301020708071b0f1e08060106021501 90
    0x309103140c082c440940158407c104298100c65200080c0001c1d5032160311281c226031002c1c4e82180c061030b074940d08000710308215a40d80e00400e8182411803c00000e03400191192041d42d01c020200070a1508203080602c003500070140c2001e02107801c0145070b4981c80c005030754014440407a4810014909034410528082d1031f403840580000c2e044a0600d0010b030300340540d5802240048503000c0c0c09004401990010344081c00c01441142d00404145145090006c00c446200b80c0c0c4604018449441c0381007540c00526521441c0c100742c52242e42c40490381084400100140c0006244c0c0c011602d03150f24080e8000040c2c419548220703207180d141c400f0f03c103055000b44926849560035030410b200250041c81c1800100d5807190007880e031a04829a8040000d0899003d40401c80780048042940d50500440401e036000703401c442107001000606009017540301d80441d208040001038410b0307221800005102e002c500500340141110b046507144c0c40c000e502e541c00030b445000252526800040c81c010001c03500707 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 992789649 1250 992788399 992788451
    0xc0804030215060a06050c0a080f130f03080a050c0c0406060e0a080303091c02100f020d0e010504030903150209150306030f030f04031203021213050601090c050904050901060f031401 80
    0x3081c040c500d011401c3d06c0035004494840480e00a410100c0c000c00d15020003451190000d03003a00c0c0d600d08442c891074440c10035070303001072040b005100c50a2000914210803200e202055042c05901c0e461410390b85860080103c00c2c0640040c10403000048540e00042d40302c0203950100d400c00e01032038079007200550304c0c041101c401c1c107154003035200480311a405070745411014880d441510b40303510865503101c080e9900085101c41c41c5a00203400c2c1e142401a100b500035125401c1c001b4440c90610b603e006046c0d58013030102034041600000940c400c2e0340594104c0c0c900d08009009070b003065070102e030318a64540003124118000d00500e10000740a503004001c8030040c0460424003403d290464440e40e030421241d40702c4009041c0d00700300c894201e42507000b11320700c1b401803400c0d0801d107100540307403503814103a06078022030318141403240100090f034001b0107441e41010242d40009540c0d40750320701c2078050304056010840c480d01c659000300500c1483c4034140c4000400034000d0024451154503518404101261 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 992790899 1250 992789649 992789659
    0x504152d1208040e010b180a0e0a1d160513020310140411030a0c110c010f03050417070b04050f0c0a0501030c110106090b0a050a1a03040302100c080403021506 70
    0x414016400c0300606076640e0382c0640e0485003090744650310150035101c203810240011101248007544903040209440f0252020740d105c2510b98a4800070b0711480d000a80106049500c501c8240310135101444107603809011002107800c080032030041581988400d000b203d0003040e0050058064091030f0007224003a00071007200101042c5002d01000f0700c10b40001000f80d00c561916900780c0703035161000c09580140440c0d100084e880007140700207840182c540550382d186404c21803c0010a0380c02c111034118507021030802082507030b5175240c00385282c601000c0d54100b01002245101c00d00106103001c0380301c1c620400c1225000d4912003a510f40d22410001540e40c0021504814407a07544280c01004110741c0b1802d2201085803c1c444603070a40f501798120b950120b560350707410425450b0038100b1b07a000340300c01c0c1c5051100a0511f01c8040c2d03e1400b0a580c01219180040450109842000b800717200b01c3c3c00010030000d203146090003c25116007900c050f0010722070007480c46001240c0c1c5603968003400340106 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 992792149 1250 992790899 992790989
    0x60213030b0a0911130209030d11162301030e1002031b0910050705160b19030e1b0d080f07151a04050901060806041b06110a080f04050415 61
    0x810000c07030b000d1900031840000c0d007c2c00040d0040c1c50801844407000400e84503503001c201512603252528810100700d01506044603010040003850031580c60a42c101c45560350090020351005038040e00e45803072403003c140314181d010b1848543c10ba001d1402402070b840100001d20b5642e5034003030300d070240d4800198814a0014410200340c003500082076694480e0301035032800c410200300d503c4500c82960200328141d100007100d8800000c13000c030314001d00d000c0303080c10055030440da080643c0d2541c0174135a482d58004d1168004050b03988000c0142c1c1851380c46aa040d0780e079120211201002e4000d03000481d00c0354004500c0020720314246c001c041848802d591071203804100681000003601c0081c2840501c0d5607941404104060180503603807145000301420049241071819245004c1c585500c44820404614821400030038003041e05040182c10001c2c042c2c8900d0b4400310f044043c03140741c0c420ba52040c901410010070451024016003259281c0452860801011200000d004d00482d003140803a2003240e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 992793399 1250 992792149 992792183
    0x20304050625030903050607260a09050d050a0e0405010501051e04170f070e04050d0825020a032c090a0605060a09080d051306080a09060213030b0a09 66
    0x40a00101c2e615141c24a092840c1002214103400c03142d041580000c220340c40500601108214440d044582131030101c01d0826110408030940d80a034050114116480300030640032425901300950686d00310054030101040340300e015065a010360081000320340c00340c00c0c8503203e242c5803051904842042e19003e20308051400490582c14010f091080302850600001c6080040c2e035100c00340c91500200280049003003d10300e6460952a40d100051800746001008001440070940101821036030401c1040307626400110120031420704842c1e240c0600b0f000d400008a0b43c001105102c1038041d032181072207692022003a4004c1602442d8a11000f003c2c00d94410303080c00d0140c0031b03e50254050000184241c0c441c40041c02d01d031302c00382c286c10000e841100c050080e02c205000c044802c1e041030801515101c0700c910303517140d05c200500c030300410310150100058082c80741d500000307d8194026821591401021101d4031007000c6030006442d03d44060f80024600d411a214208001d0741000c0d645035091211 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 992794649 1250 992793399 992793409
    0x20d02011e02030402120105010b04030308090a0305040b0c102a020c03030412020d051006031e0b150f03060c0c0d030213140109170a021f0f08132906010c0302030405 73
    0x648103c1e017140c11b100344001014000e202d03641c007174008030901070340c0c80c0d145080040095001404181040c4c000c5000200009d800c48120380840b000c000c0880e0700e841c2d4060699003000c600803550030046060038030921602a0383c2d1190f4402901a291450310750340f1070307001243c2d58080300c8071680e01540300300410310a041100100d0192071b48000c012500c0006107950319410507440d00290240d160700c030b850a004220200941039680340e48030304080034807011600c0340e510b024006011007103041180c1c03000c202c242d203c0300b6510143c9500601220601e04010132001d03403550024100c48414002ca540350b02c0441e220b4021540355100102c05048a075080c2402440d022110049132414006999000035019600d0598282c500503124040d10744507201d40188030b406609e00128240c43c0108440c4d034421103401c4400a0104440c41c54890740c06d6035120307818179449041c08000760a07003518610520713a420317621000342c035406103940d002c6003c0d440302401500c4c00303403a1490003400740c1c00501c0288054241 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 992795899 1250 992794649 992794651
    0x61201200f0d060b04030c170d1b1e060605040e06160306180b0103050a0b0d110406081e0f0a0b240a0e060109051f050f090303040f06020d02011e0203 66
    0x1042100b0300c0c20b98aa225031048583c1035010b118101d0340440c0400c213000002d6010001019080c4080c0001032a44995980b0b80411107103020034020b401405440c0318240a007005007680d4040300030008448503168003800c172410003404540c3d06003040c4010400c0d08281c0070b44440031000c5801000b10340c40c0e0b141501c3c80780027101e070340c03a00f0103903500400189850212031070168503490440009410502c10001410360700d0080c40c00720003604144501718140c807510304031b00c0b1040e04100450009991580028041e209030b43c0700f0340b080d2245052403036446620f0440180b0020516045405044085140e1074035400380e0304010349000040d8002640182c0c44c001000030007400441e6420481c010400054100e591580010f02c10001c450104a429604907140a000d464102d840807058000c4440000041410270035440403c800820300c2603011440d0019524682030040541b629030340c50b16907400010180c1c3c440d100040c451800217000c82030042c0f260690148001c03c03407034801413401d540c1c1c0c4043c0d44 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 992797149 1250 992795899 992795917
    0x1505030f031c0905070f030b090705060d150b0a05120f01030f0209090f0319080f0402130b0f1f020d08041109090a2f121b060d0c0806120120 62
    0x503d030394607040003400902600c005000c1e00241c01c0001421802c20071184000102400f101e0362095009100654a8109a03a0040036482000c2800000c101c1103041c0c804040e0302003024081e0200b0320042c0103812801502e5000d000b9140e4854559032902c0d03069240d5001e00c00509010569000c5501500308500b500ba8000d03000012a0710301c1c0070311034019141d275010b1034117980d0302c03100c001c5402c45542c1d116001a0b0407200d21410704a05080a400080708080c0c42e4980c3c1c200a6980c10340000141c030343c08400c44265000402090304042c15480180c440d0780038064010050050342001110310780600d12007030069070400e01e484007088045060044941c409020310320a849001d2862000a9030507407090749500ca890160116112036046044c0d002000381ca2081c801c02019110035a20480055890416000c4200c401010000f880204441d40329512800b2501c0c2c0c140b002c07800340281c115180a00800068485482800e55800104d08030b80014480b001c4a680e480e05c540a80b841c00c1c000303401020 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 992798399 1250 992797149 992797151
    0x190209071112030916170d18051207030303050702060106050412060902030619051302060331060c02240406090302031303060e060117150a18061505030f031c 69
    0x50000d07031102c05a41c108807041d5965600070b0345000010310940c58960000c001004218904554a04842d40c03034100703910226003085800b007418010600701400001c010f03c005050300501840a02103a92160214001a00403a04100c04500d440d80300282c964100c40580da00d1030304285c00c0c44181d0740405216807056606176100c07440b070340c050b0350203001250284c2d034014040d00401d401d0446c140152480186004545140c030401000944c8808040700e45c40414112062180200c0380300441d41c59006d01c001051308081a462402003241c45d501c17100381c00345036400311030303140301280070300f0406400c800d8240c880340d00e08102003000207040e81c1055a0f0903200c0c4c0140c07800d0844030b9030404c01980c821350060b50300c02c0d2903040310b4130840300610840f800340c890801c862000c07440171007515580320a80c040c1e80701007020120025000740e20701d0748060302e807601c50100c04506100d5820010003400c0400c0002404900c0b241c2c001130b0501d000a00c0c58003161111000c0e6003001e41e1040f11811440b503501c0c40404c0c039 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 992799649 1250 992798399 992798413
    0xa020c010b06030106030b1e15160b240406120210030609181a040203031204080c100509160f050d14032a010e120702010513060305091902090711 64
    0x29581c2d0b1000c2e501030040c55400184104c1200d0821080c0501c0e1008800300c000c0c1144904050f07143d08024030f499210b00020343c2d0783c035550107418641148624101074001d01606050040e8aa481508510400808210707481c12000202c20407007281c03e10f2088602809403413003600700500300a4090381044295043c00665103540700140016200030a184070788a5480c0380b031b0f08080000d00d10000442d5165a00c0d03c602a107459130109549200791000c020a14003170304002000c200c09401120111509a4141e4005103106c00307405001c0c0c034069505090034041c0d07061007100180c1110701c1c0c1044a2240742c0303940740f41e41340000344034140340209401d640c034000349414002c0400041004000041e0741c1d440e0007044921104444991054140e1504100d9052180d03070892440300080d141c8403c00b115030b0f110342e151030704d200584181c400c0780d00d0100501059130001642541550225106e1082007080d2515925200080c407490f60380110000d6006c41184c0c0410481071088800f429180c501c0e000702c0e880 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 992800899 1250 992799649 992799671
    0x409140f0601170414100605180f04023c09090606010c03080601140f0a020d090e0402010e01030e010903030e1c050d0507020102090d110f1c0b06060904141b0a05030a020c01 76
    0x4105030360044040081d1030f200208860308100d8278020040040b00b440e000a41000f44038207040e110082e01c040d2003080b82969440e242d080329024541c440603d070768030800850714441c1c003101002c40c2c101014402d032480c05c001000003001162007445084160742d6050b06003e2907400703450084014000604119090100401349a4520300400c2c0c0541d2441c0211b03259404c118001746004620291181040100c040c00c2280c807000050b0160080c0c0c0c2400c0001e41d0002d1000100d0042405c0c42c03402a40b90309085040301419091352140742c40702c0c1070704283d40c0707409500d00c000f0750901907a180100c00290f0402c04081c13049819400250450401e10000d442c0ca0315903c0080c1b00340e14a11000d96081d0341440c0c0b0805c01e460800c034000c0d6404c0007516800c84d9626000345010b15480f030000050006280c2c00001642951b420381200c0001000910030402910100300ca213443c000c0860300384000450481107620300d6a44002a1800070125580e130b64615900c80043c58040e40122030800129034036240e000c11 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 992802149 1250 992800899 992800903
    0x307060203040c0807080712050102070602030f06030c04020f0912030d060e07030f0c0c030e0a0b0c151e1f0e070c02010e010804110d050c03030409140f0601170414 72
    0x280521005a22410b1038103103a001c0b01407030b501c41ca03800d501c544810480800d0100d4070608481803100c03005007404480c14280d000e8403940c8001040b5600c00010468540b003d100e20304e0049105504441c41c100c100c40c00e01003244165a40300c240910203100f503a1051400041c00003042140c2c405503410b182e448028282a60160303080580c3d07803d0003200b081101c070707494403900443d440d0b507003406c0c0310009403140058102c1900d080050b082040c000d0544806880c0c060020300100074101b4002d50b1989028011074403000d00314a602c24403200070010030035001e00b610340c0c444030201482d41003d450b01c400e6413880341481c161a0151380b0303041501c000603081031051841c0744652055141c108212903d44001400d140304410140c1c18800d5807030601001c00d20394035550368045420384003881c1c030180720305005290002d24000b195041c0b10000e40401c110030709800030254104810003202658445040c1c4001d00441210454001541810100b44008511412981090062000b5005600510b01440c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 992803399 1250 992802149 992802157
    0x90c21180f0605060321031b13030302032d0d020a0c05161d24010e03061515030702060a02130e09210f09100216030f050c01050a021f06050303 63
    0x7a074800d0f56601008440e00f42070180c907000c4110b61a00034911255450820228040074095940800c250100a00ca8101c581c08890340448000c0c55016101c0c0c0d2450002c0d540d520080e5003241340c08200102021000f20100c4808680024072a1103052040400e48603000b504404406000c2164261762440407800c2072201410110022001e40c1c80316040c51000c40c9030220211680b0114003024080120720b042d45207902102e2144410424800400100100d0381c14443c601403991500800c0e0134400103106608816405503030a6074080d40c00865560000c100e40400c5541801680006000684000c0164000d042e4003503041920b103180390721400007400001c8111a6000a40e0025040c0c07048420440c0380c624500803a0b540440c80c1420402041e1200d0185440883c0144031100c0c070540c00c103000b0300c580b809148070810b264514a41e0b0381810341e00e54034600d8003a5064002c0c560000c055500c10b4040340d0401800713400070301551110100040040070031015031182d05a899a01103560f0794140010 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 992804649 1250 992803399 992803403
    0x120203120c012c061302010917010608060603190b0a09060c0c020f120a021207090e1b03150f090f0d020a05010614010804080309031c06090c21180f 65
    0x9075007420750240d1600782d1a0011024810b0441d1450883c601d100240c2c450340199519200c00f91014144010384442a031900148004150021003001c030150551080701214100c204803403a0742c07074440515441c2d03000f01607040500150100003e02150906070040d0b08550401c400299100d45900d8110896045c0c100400010307034101942e90541c50032204184044000b100c0c20040b661030100d810307075600600c000c000c4c0902c1c03000280302017485043c01424014000540140700400e00200c155031a00b06030348400c1120060340c1c02d901c00500b000521400c100c0d130070991401003a1510445c86c0100c240007000100326209076200b403400004c0038407170700000307000503001840804010b150460075520349400422030443e40c0d0048401d0350303070311800642c0c2043d005002c1e55a641c81f80340b0f8a43c03e510074154041104a50345d9401c48103691a6070101c8126204254104004089004c1c05c465040019107448500d1413603109651008406a1200c85108850002030307015203416a1110360034a141c1c041 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 992805755 1106 992804649 992804651
    0x30c0a05090a2d0c120207080a1215080c121908210c09011101050f0103030e0f03071d160206040f11031603050f0a0804120203120c01 59
    0x2012602d02c41c0c40700003400300b020480081010b131481c1050100001c03c076000001580a161081c0d80c1b01c594041d12451400c1c5002008a80745420308994020803669070150000003144042c0050051070300001415050303041d1803c2209004da450002800c940014506504400f5010b8a5003586a448016540c8401011100c0b00ca0140203903540106000e00d0020300c030038000354001078140048240c2e500c1003c0c200035810f00782a03d00a0300d05200701081e0000620001c4c0c0070342c1180d40305102c0038140c95000b0b00340e9000a071821156502407625139550070b400c007804d0075009400c50f0303010000d10718082d1420142c00c4001d54440b00184064241d07146900030100f0401d0642031a1a1004010308540c0510414032003051510842c1c8402c079400d115020241000c01c0012a82c00314054200001604291a1242e49401c114401e681241d1500907850075070795250030030b0042c103a10800000 = true := by decide +kernel

theorem cover : BRFrame.Cov 992625899 992805755 := by
  have h0 := BRFrame.cov_init 992625899
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992625899 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 992625899 ≤ n) (h2 : n < 992805755) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
