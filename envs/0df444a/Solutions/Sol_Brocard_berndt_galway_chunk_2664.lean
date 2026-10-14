-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2664
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:22:35.626983+00:00
-- url     : https://prove2.me/submissions/9aaa8547-55c4-4815-a9e2-441194702104

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 478956834 ≤ n < 479136690 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 478958084 1250 478956834 478956857
    0xc03060109030f150513120903151a0d05010213060320030910091506080102071a04020112051005120a12030b030a020312040807060c08030703110903101a01 69
    0x240481d40804890b4001d441c02140d0036149405011890034084030008149050100400303074a0300402041c0303803030041c50181485036101c1c0b011100c507034060002410351a52440014058422940700141464440480e00c081a91040c0080c1e8204c0140c841558243e4001c559400240c00301d50320040100901c0c10308001e010324132120500345181c2e440b0503810f00f580c0072000911310a0180800f48040049440402000b822450f082d45400809040180141d250560100d0074150520856100e69041100450300500000080603900320090080307040008140c1800e10364086801011301034680f01155460481c10309082c041c01840d5203601500503440521100c021440c0e004403035041316007514021403c1600c01d000300e454408504802505481803200301450158054060010340300c2c442c0a0351011030b43d030071085131464081e001c05416400c0801c08140241d009070f000c240e4418444001900381002d4000081c1440c1d44258034603c229181c0f1032000000000e100340064100003401c26080c4100c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 478959334 1250 478958084 478958087
    0x10090507090b2b020d0f0b010303090f080601090b3d09060503040b101502070f0b0403020a0b0306030a0b0109050f070807050a030902060903030a021f0b09040f060e03040f0501080c030601 82
    0x25003038a04815940100c400c0002d64a0b217000303c0c3d01c0c0c40d401c8048403000780c4035450000c0c541c103c04d03c0190005a225040890300c58582800382c0101daa80300c0060a050b4208041400204045040c01e136021506a1040c840c00320013401071504221941c070103095141c1d00343d1a03c0c288451200301300f000c00461800521405030800c040c0c0b504a904081024050b5403414409004da07080c1e60086102c210301e408030303d0481c65002406d142178030414180c0c07101b1181d4400b402c8a250040c0d00001b0342c086011881400381244c0d90000d10b0780003000a0450700c44621548521461032001c0c0c105200311500c8100304003001c00d12000315034004a05150003c1c01c1d01c0c107a400203003280203a604141c10180c8910003141036580304015100c1d500c0006040d44d5441c0040030307005c2d6a4900a03049a018101d5440c61420703100001d100302600204050b0400100341e50355070301c54071300c143c13941400c07140c1d0355070b07445d20380c0c0e5041040000d403000d17020004610100c03500340000902001401810544054020010448944d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 478960584 1250 478959334 478959379
    0x709140603040c031410021b010614030c0d08280806190b090307080d0c0209160f050c0a06090c1806030c0b1b0d1e110c090910090507090b 61
    0x260740100c210107840c08070111250402d00c82c065210b241d9800412030000e80385e0303203429510000400d1000ac0003940e40c0c03031003440b18440c0081d00090345600100500001824800340c20f070100340c868045140341c40642d03d90145e48440c00e0951000e449803c1c8043c410b00c6411000d12600700c0700072290780100664910b003204903204c1c980200c0403d900089020307051920100211301c05801d200f13058548102424000900b03807405150180c0c46501c811001c00d83e48046500d1550b8a00d100341e0b034030545441e030344030113403202d60091649508500c64103003070f0004203100c2d01c20450710340c1c42080c842c00914544031403001c0790110403015008480c0b80800402c001601c1f15501f40454416000d810780318010700054504000d03030100d14200381d010700900701d2945070b4404485182030840380c070b141100080d2640700b20b4000310b0803000c0b282158400184031501c0d00c0e0181c0d80f5544454602c0803901903000c400e29000c1601e403261811261644100c0b410b1181d0304e01030107501410101902d0310000d0186040105031030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 478961834 1250 478960584 478960589
    0xb0c06040305090a1a0909011a1204030c1a04030206010503010b180402010311040308030105010f0e010e010c080903030c0304260a06051504050f041b15050f04030b0709140603040c 79
    0x388003001030302c1c0809442e1040210020440f81740a40c00000a0440644a603440000340e14400c0840c48004503141825031107115015988580641c2002125408208412005003084d41445020b10341c1070300103034a032101c0c031074110190581c4100030300b03080c03401925125041c0c0006209034103029118174a03889030350794290002040c0c080d1207a240ca6600059000348400010840f0101001030040140f0141030700450407203000780d03203003801e100000380d084508003012091640061161014003d0540c820381b80c460b2464080d95a0034681085480040e00d998007902032103c03c0d82000c03c04110580f03407002e950660440000b80101e941342500c0c141900c48403410f4000300940d941d040420009a0311280c085c10b140f04c090300400c00c90400f0f454041c2035110890b0708480c0f5560160703d00800c003880112070401c488407034410366001c1040c0301c420b43d5282c100b180c00b90102c0909000010105040030035071070260380c8540b502440e01303050200001040301c5410800c1d004060400a100c00074992040400c01c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 478963084 1250 478961834 478961837
    0xf070c02060f0d050103030c150b09011520010e0c03030301062c030d0e0405060117010b0c1002040603050103020a1a18040f05070518030a17031801060b0409060b0c060403 75
    0x165255040c02d1804980191120030300440d10307200000c000c0540148000f0041c500588005074501d0070b4810070820742d090703001c00030b4000d9200300041010441072000d5103a4007030541006c04124841080c01030600e40d41c1440289140c2d1100c140491044080c009041364400035405540f4545c100035000c0c008103050a001600c124201c8858201d0050b48a50340c4010003004003651115680d810005041e040101c006a1140d49481c0c0030808030341c000d490600803504100001300c0ca503881d1004141e03054206c91500c0704540142e21100c11144140d200070400b81529413400140c40d4154018480316a003260021142d10541c41c00da0710844810205407085d041007840001110030075070021a02415541a11171b110303d052038144034035035070408040c0c01400c43c8100700c0514550b5620415070354403565000a0101800c030749440813010b880d18005c56000c403410b002081c90f0a1640556421252035a01100454802040611160442e40180001842c01e81000da05080340341d0000c54030307500003400c000c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 478964334 1250 478963084 478963087
    0x150a15060e030c191a030403030b040c0f1812052d030702190305060702010b01020c030705150a03020c0610150c0506060f040608010c0c260406050c0c1302120f070c0206 74
    0x1101c4010603c80d026010720b0200085c10481d1244514041c0c0098400b00d002c81c3c2050030030388180c1080c2c82841020b84517075648640ca50082c0c6000d642c0000301c440d54000c0c03e008a2000324106402e801c00210241c4503100501510622148800d1600202d2851038001110802e51020b403100020030b94072415012290514282c8618050002a801035800200240240030400c840c8076010340c0040708202c000e070280c407149256a01050740301e1a080c06005d501c04448003000a0b800e21680145c01d004a03c0e040c0140f806907121100781c03a0501c111214000c01c41c0c00c0d90140801c400c42c50b01c02d40303110203d04000c00d02d10000c1d030382c89807200c100800344d9001e80e08105103000c1a6807a43c001e80002d000b01c07802000400040740d8010900024240c0a4920400b030004c240340158907405074140e08002d5608e83c03400c4c10304200c0c1c100c503141e00a907040ca1040c465442540c1040e80c0344181960715000102e40140d032028004000d14004c040148100420b482030020080e04903084001054059412034949 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 478965584 1250 478964334 478964359
    0x714240307051209010222050607080c0102091503011d0c030f060d0209090a020901080f061b0915030703180206040911070b010305030c10022a150a15060e030c 70
    0x712868060f0402e04660003291405204846206600400004509240c0d030440c000c00400880040074552207825007004040010502150700c3c0c0019040c6440b0703c900241c90000c041c000200c02c81b0364014005000680080100a034202640c1c00000584540d0f050901c6443c0c86024001c40d800003c1c096440102000000740440d0f9a03d8469003689070300425841c00c0f41007129045a641540d18003c03405440103d0010401050014240000304107031030080c21103688a8074911880ca005503a182d5651400340055181395076405680c8003d4003d010710383e0744900e400c100c007c059800d8443c0c0c10381121508404a00543c9800049500355844110041140d0032080840780491180c65170103044412101d00110400a0201c0180101c00c0a80200c9001a4681c083e0174101d2007503007581002802400140303002489946483c07007071071588a040d01e61403d640340d003000080b0710440b00044400d80d2105403203c0310501c1c3d005038001d402d0300d25040c00c0720b4200c0c20100c3d070b45104002034544906d0100440 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 478966834 1250 478965584 478965587
    0x11061503070b0f1605100b0d0b01030221030f0d0f0209100509010504260f071211210d020f0c030a02040b06070206120405060115050d1d0304080714240307 68
    0x1321104039030750f909603041451003810b00c60b03210a5404c244a002d5400c0203190a2540340c1040010b18040d0083c11060659217107030708006084100101e180181d200240840101c2a0140050480c817441040c18a41d902d0308030316041c0459405141e6020401d1051183c80d4264903900e000f40b24812041c20070b5503941303103585d00503a00d40c0102c0e4407261035406140040c0d0044100504c0d00c011814030313002101c54004d2039124664845955011342c2c03371040044d101c9507011610700c969044c0a044040d040c002c012a181d08542c500c0181203070f48258a5010680b50034002e541007002052880204014100100010300065103980750b001020b48540d1303c41817661103545d00d660458100c240e0007440d1646d58503456100810580080b1000d48040c011b25000007604a00001000b4444c503159807214074040c4101381104c020210b280482e039500785005503407071040341c080000300301404800b070041800320718020020040c1100404c0b0a4002c4800060a0f0303504180c2c2c80340400c070403110404154070b0342d560240 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 478968084 1250 478966834 478966837
    0x2240708090c06070602120f091b220c020c090106020309010e061b0d08060a15030903030e07171c021207050a0f0b0621061906080a0311061503070b0f 66
    0xb40300303a10950019801c010002243d004283e0651400782103149a0380302c0380c03240c402540c00ca900550340c2d000160706454803800400c00c2118070f1030050540aa0f19144880c1c045140d0340030301c2c079115981d59404c5c07440b849601000050300c1640122940501517060001c000e44900801c0640b5051000741039090310166074040c19140100c420420507a16140c0c94002e00303a42c1c00040c0072031004550301401040180c1440d400e0340b4241e49503490b90090720641114220300070324142e5000d5041507900c40c1000c1405070284030440050129a0703015030210303119502c29082c5003401c00440c0da444c560300c40c0c511000f070300810503402d040315a460341034849101d400c020741000d41c064001410707020f10310541c50820004c001ca1070301501040e2490600c03a4000c000035040d100021b600c1000c56441040024a041c1c0013050f105c0ba130300b0981b03c0c0030480d5640c5178242c0d80b80c103508103400c6003ca1034513624010741000420119034400300b148401c0c1c0300030100001180d00d88003517000d01c00b048000029500012081d0b4030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 478969334 1250 478968084 478968103
    0x2104140a091104180608030f030c1207030b040b010306050904020904031404060503100602010b01020721050f010902040c170a0906021b0f07051012050a200702010224070809 76
    0x21061041181c41200b422840d0301602850000d43c2d5410a2010701c40700b00e1080b0001d5a100c0313401507181c0403a0550002d42ca0300014020204103008100a40c0c1d02c0500601060141016480c040340b180084010441176500b1005587e04142c03600c6020884c1ea91003003006504031b6010f581841e51500d45080c00c840d004801020810300c0a800900020031030b42c80360007580700d010789640340701c101503c0311012800d94a140d5910341c010f9001910600c90249580400c141400c0c010980c00101d0001c1c0da1050700303055803ca4200483c0c0d6442010009508150203218152550381c43c01441202c08040181106200a0110041141d6030905441084196411284d40020009600382100740a0401542d180d06014a01c00180150a00014907042201c41ea01b0251010b031109211411007041510040c1f4004205014103526086c08852102c400d0801d80303448409088440c0c0d0714180da000281c605100c902c020140038490940d030780c03502050710708100d401011600d008010351f00c884c6120707803a041000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 478970584 1250 478969334 478969349
    0x6090315040b0403091517100f060c020f0d02031c050d05040b090709051303031503060606091502030723070816090e030f040e040f0c14032104140a 65
    0x1401d00c0144400c030040325114500c81c1e510198a01c0e02d032045c0d9502d410841489038086500741c85802d03035141c85a03c0301c036800348070510b84d040441c0e6180c04200e4100b20f550301c401c012500c564410710541c2061201d0803441102134940e40d105a0301540400d65401100d00500000500b50855802c01840b0f601158850f050900d0140900c0c00c0030f00303000f5010700b4151001c00942c802d1110014040300140100ca10271015421908038038000d0b5102500038081a80340040e03014201200840000d401e881074002803c10355035031490850400e405280381070903030380022007550300c2880048005525400010f41c0d0500e48040d0240d0040c98450051902c00d0a421085241c0078040241e80070114200303c603400c860130903005005a8286100c42030712403068107007216668908110a00c41090210310898106200e02180581d6a200b81c9445940e030301c03181c101d039008948400c04044140f40030400000c100240d095910030b01003880440702541d108900c1001010046440205002d6031281c08090050109 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 478971834 1250 478970584 478970623
    0xe100306021c150e1b0d06090c1b02030706030905010207140f0c1903032318040501050415091104080115091d030d18080a0824030606060903 62
    0x295155400780c1c65041102c600c0c40d10703101c0c0e2010280a558001822280c614200002d9600c45407080b202205003e008031401072001c020400c1c1c1240d031445108000c0c000b5200001d10f0803140703140107000007121000369151400000400780940d502180d444211f410714100000d000c807051910310f01900036040050080c03400404150718807003000c902c8100c0d171450101603401c810780c103500300030001e410900340183c0303036854010910000780a0400c1c44012000b420906107000d045051000c603580c010560001d04503000d038280d22a50800d8002c25014000c102d0301405241d0960941a020400c58410301e160282c80e00e14964005072207800b00d8002e000ca54009200c0d05e100348120081243e481c0c856514824a001c801344030240d180d1902011220000010314604180400040c004e0402040c1420045000c803500c3c000245c80d90307005001c1c45520f915098250302c0d00f900614401ca0f05590b46030701e03140c0402982d9400e0350b8003080f40b9a00c02e070101c4005841c0e540100201e0703c1c0c0101c40c190710088008 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 478973084 1250 478971834 478971847
    0x206030907030606170a12051306020a3020190b0609040203030a08150a180615050a2f0604210507110d0203162108040e10030602 57
    0xc0124100c020b5a0155005000c0944c0ea007000b182c4030003041d80c480c0c1107031308402440b40005645031a280b403103022520300f19042060503040f281d42c95400350b00400250b84404c1d025001c110030b000b191074800c1c1000032616203c410070100d00c6802c07085151f4800401060307032041c84003060540c00a214840d0101c044403054440b0186401d01d0504544003035428106a0000480d9032811040080c070840c0d025025605141d5168800e94840c83c000d0b054110b180e40401c0540b06a45130401604000c00d210700c00c04081c0500301c2080000c4407001d4001490b0b0750b01c905201d07002d150b04002100d50380101458540c0e010705c0045842980d10f007000b0007204049807004d0703107103030b41c400002481401580200c003840030003c54100301400c030340020700d0038201086050007928003048403694200310310b07480504000c820078804e078002400c0c800c45001c03a0ba52543d0154087c01041414807000c3d808119003440d0707030251011511107032414005da11888070085003010004801c058181c1d00c410007554403c10541d00d441 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 478974334 1250 478973084 478973101
    0x70f141602040b040509030405130b150d0b04050903040b1b0d020a1205130b0d0e06090105100f050a170a0c060305061516080309190c06020c060c0c060304020d020603 73
    0x28500c00203a12031801c0c1510b080451a0502c6050f01608841c3c004625142c909020702c4480f81c502485913117550ba031102c4440640d240e580d90015010840f5450b80c1c4c2c3d96500380c0d040c000b2a200d040c07400c0e0003589818100100b4110000494047d5800c10b85600e4658990324131507a42503035441c0f415a540d0296072010f2901540000300e82c29074078881c101c1c0c4c0c0c9100f400c40d14111001c0c040d01000840038030080c0400c000301e82010004225402c1000c40200d00090107060480ca44001600c034003410345e6554080115550b00c0c8800c240103072400c000444452813070b010009040c0c0407240104000c510801503a40440b25042181c01210381e4800c915865076569900060014801120058001d0341012010340414903c2c00885080c40006022f90502c1c0002e9100d4075040c0d00b0043c8450710b036200e600290040402c01d1036420100921480c031100c0c1d8281468402410807487c5105031f401501e05204c00707a200b550208408403102e00550312261240e41e01c1c000a420000d0a81c000380d00180004140880d40 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 478975584 1250 478974334 478974367
    0x130905060103051525050706021c06080106050105093307170418090303061a031602010c0512060f1315081b0f0f100908061608070f14 59
    0xb40e000d50142c030f409240050f1001d440000c1200c030381015030710b1450403c0350701d083c0d16800000952285481c50070100d00c2e0b80d41c1400c907030200c0d01d80c4030900c0000c04803010020780780c014040902480b00c0244800c038545000a4074a016a1000a110713500c047e442c01d000081150301d10b60021409644684d81c60900e00004449903c0a0004c1e01c1041a0b201410f00081c0d070f940032101254401032149940c40315101c1c0000080925160480406854400000748000c000307603642082c9169001da1a981d080c1281e02203000c03500c003018041564103181e10750701403e400109551840703078210544050307691b4203000910284d40000c001c0e0350103410400e14a18111450740103002400c035580302203c4071900c6080283d6a6400903c1540d40e00d10010300401c01420b0030005c40030707503840103007008140d180d9160000b054010102e02c00c03400201114020480d44c00104842030300300004510507a014818080010142000100700209000700021480a018450354034a18200d100d9031340c00e51075241d10001c4c84c600 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 478976834 1250 478975584 478975589
    0x301060e070f080f0106120b190f1e030b1e0f01050102060f01030b070e040612030c0c060801080d210e0f070801020c15060118080a0b150901141309050601 68
    0x69111503100c140140078240c0213000b106080000000c0b60f213008001c039520f01c002e500008030700d03032200c80c1c40380c0b582c454110201d0444640340044410605040d00700f5894050b680c44494a00c50741c400004018030950500c01c1600d030000c41c14001551480c45001c800d0710102a02048460504200022844050000d5040c0c503130990a4034444e40325801e0f460303140c010a000181404010304085480380e4002c40980c801d508000d40003044c5550740fa601c280a007145054164042066420080c0400001510000103032240c1e0030203070013550412026030f540b0100d0301040001e102000b40301c6071025404107c2030700c50145540003400301540c5040c02903280d00419140741e180e0300c1482e80c081240003041c002d40e8250240d00c3d0003006105100a0001c10803030029200b40c0c103002a8180912122104038010006014044000c05960010f844e001900040080942c18a5494042041c00c2c030fa031408415411200100c0007075207200885030004513140812070319103081a00d0014110100304010914504 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 478978084 1250 478976834 478976837
    0x1180909020a050102150a0b19030b0108011d0709051b07060b0411072f0909063c150a06090509060409020114030a020d020a020309040b040c0e0d050c0301060e07 71
    0xd5942d150010b9a442e006c0c843d075030342c03c0c0d050580004d101600b0f40c0d20906803040700400c4c000a02016402000d110380158205071244084280144204d1000340140d156a001e48108010981c10307000e030440d158a06e5004802c0c0c80703910784012614042d601392050320006241001103540e9940c91419400803c00e800e1118090390400724006502c060403020b81c1e40c040d80202281c8842da6204c00c150040c11440025841c0030020442107041c1390703e920324454070070340d1028000d101c01e0070444094590b9101483c00c402180c2404d041403160101c0c1c0328064110180810302e0054a42c941480d0200c07026003280c8240e8004600b02000100d49038400d0245c4115041519401207607200c2c1d2007031106032115040042d010038064060000c42c19170740f200460388543c0206005080020f85080101a42d0040d03410000590003c50030100b54a0b00380300f0103e0314002200c1c00c000c4006018009080424a100301c07901c19105c5222040620038140000c0b80e440b07900600070405a0b49034040030034544400e5802a0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 478979334 1250 478978084 478978099
    0x40c031209230f010503070c083001030302011b171306021908100819050a05031206090906240102010e071518050a031410050f0106030e0303060d030507020118090902 73
    0x3c5540242c04807400f60420360346003107940026440f40c04040e406422010904403494501c10b00c0d1520f2601d000c00001e40120314006a54590b060003400e5440f00100c0004da001500b440241e02074210700711030f000c1c414030300d8901580d58a814441103000e001c00005018a400060315400206290354010545115500d48050715214100d08403518540303402060110b6021903a402000b0744125026410240708070120340c0d183c50a6a00c1c1800c46c0c029503075400781040a04180309007490030051040d80400c00c00002d04040c0f45ca401c03508007017002003021040c0d01e0750207040c0b41d4031039200703400c008400c1c0c044004894409640d803003100e05801d9080144000200c3c2081e50340d00c0c0a128004001c1212802041c00c500715045031986020102400c2801c00c0a00c00c00c2d020403e103000900640d07100e240807000c040c58030b41c9050340140581d10310b4940102e6940003002000420359030b40380c5a003525509403030801d031121401d02c0180c80c0340022030b41155101301d40302c00010302c2c100b080c1c2100020505c00c0e6602d0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 478980584 1250 478979334 478979359
    0x10203010906060c08090f031e060f0604090b0612100905070905130803070509061605010506030606010e012102071506031509051f0204050a08010e06010806040c03120923 75
    0x304c42c00b500040d8010a29201007080f84114a002c5030184503c040050030f03214201003a000282c406401003000d200950860410402c140d001890041c0d0701000c16201030040d026036958070582c00d400100340612841c142c1c00e005004c034604004d0401d19450582e0204461130341da003802c27a0313100203501c0b405003460b0411000680a1201204060115038081001e5056499003035040d182a0030074081260400c0c824408240000c02c1c0503058070786e040c020700000030715041100505080610080c107080c10f01c48260304c21441c2d660700005c2444080c4c010700031240380244502a14010307105503036015166060000c48012403a91039400741c02202c0c0704280f030f9400c44d2184240407080d2080c240b005403031034101100c1e6500031002d121850b041c09a010f01c1c01032a2585a100041d0f41010603000340c0c00d0740c1e641c0c54141c0942c1c2c0d0104281e40c09804090020021458266a408a004481d000081c203c0c010400c810740d400c1e00914001e4043d04a00045000444581d104070305510313480c03207646200384559101c8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 478981834 1250 478980584 478980587
    0xc0b07050106080d020a0c060f0c0807350d050c071406090d031104050f040b04050a09021e24091c02010f0e03101802060d0510081f1a030f01020301090606 68
    0x204030547e0710084280351903286c00d030151244031400c20303c00244400c5041c4007002403603800040511600c02e545800d504422140384400030245441041d02c1d07401000c042d081818940d030291400f5030300081021425555184e0f140360746005811005200700895100c03900340c8a80401c02c40e00c1600d08800b19016040a4403088040e1134501522140d681010070080c0205d0400381e50f002440d00000d0710201d0b4020301e080c0800c04464080b01c8003240140c2d201413010031850001710031401440f0100f03a241e00c00028800095807000002c120141901c480b0748101ea003613102c042500e440d80030040010100140383c1034080c2c90320198070343c101e00203807074041c9061800e80141651f40d89040f02130000c1c1707801401103e0750402482580c0c18904007200070710301d00d4010b946000040040b0900340c10b011401c3e0426003100d00e50429150020603058004c8141e410a6030701c074640d10907143c1c0e140f1001080031008006041c081c030a00c0d415583d018040c40c0351700300d061f0f003054004604032101e00c00c0070421241e0742c080 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 478983084 1250 478981834 478981843
    0x204090b09250e0702191101020705012a02010909110406170403081b0d1803020729161e0b06040e060a0c02010b0316030303050615160c0b07050106080d02 68
    0x3508034900b0701c08001444044101903540382d00c4045801200e60151a004114200d4240304000b11070084c114003a280d425641485100024a020300f08008154100c0d060008c0b044020880b00009480d101100e105583c8264950340007008143c10400644c03150440c0030181b58024080c010100b008a070f269490355400136503092207550966104c0155440340c002c4030102444420714400c074071200340b1949054405a2040850481208080020680726072402038180b8001d41c0c48008003401c2c01440c20390354601d03032021003040484521402e640300300d58a0313a0084d0024072a40501160401505104880360802c1102e44e91409400700200e41d68800c0200401d94541c12105005600b2034404207400c0c000940000452641034000404e5080021001c41e2801d0a0410088642156007104006050b0544101038200e40283d40c0c401800d100d510381044c5074800c203000303124510000b0380384406201110b4400c001508400d008103035610100d00f04140030701003e0007603900030300851481c00c054600024 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 478984334 1250 478983084 478983133
    0xa180b0304021e0406060305010f050409030212130317030a050a050702120921061b091005090301060f0f030b09070e04080a031e0207120f05160f0204090b09 69
    0x8424914555a603030038001c5243d044424200d941e10403950900341030343c9600801d406461181c0c0c00003600e62401d020500e107410b05e980301d00d000318900400c002c0403076400300300000311030a00f084182e5200361181c90410040195800501000c0c7c818041c0300318040c40500031070180381180d501b444a034503404500011550291b030b02c41c0c050392020768503100070041c60b006010703c210000d015215410700901400190b594014000c04940c00400410020f1102608021050486c0d1018603042546c0c210126540d0f800124414060100109120166503000d40155015022840740007540340c0d9030303a07410904d100d2a03000c01c8544c000e84100142070321000190040444208810ba88815240e640f50980e255001d602c400b000c154950b0034021500078072080040300da0040d041c2c01030f80d558880c1014010350ba442007035102045652031143c000301d80d01c00f00b5100ca910070040c0380e40098880b4a2301050388644808000d40081c105500001408401d10125100701c5096054585411161032065002c08604 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 478985584 1250 478984334 478984349
    0x1d0702010b1f0903060c0521060a030b1315060f060201110304030e0d140d030f0b130c0e0901030c03030e090714070c170a0302070512070902030720030a18 68
    0x42144102030146120b64001d0900e1038180b00005985903182c00c8107a40346848444045a000a60030b500c80514070115000345002e0402060340f81070607000a189480a4030018002c1940704c804106000c21000405c0e05d265800b075248c0d0b10310000343c58140058400c0c0d02c680d4444042e070005c002404d40c01809171494a5100034051403556846a8080e9100100c061048c0c3d00608400c0d95000041c0550101c01d09e44038040008041400700600000d003a50446103a481009060080c07183d9140c6900d4410b011000d1004004500031840d02000c41d1b1780e5040c1814250301407200f000000511040350940f0003074070300a80d143c0402501e000d06106400b80250b44039000100360500c0602034002001c05011680c3c82030406501240e51030023042d0300600661110101d03074100603041000c15030104000b50040c002580d818540c4444000f11039115019446003c003c160000000303516548904804200c4c900c0014101c0c0090510401c101d6494100c8417508011440c2c2c4003d40540d5860b0504210854281 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 478986834 1250 478985584 478985599
    0x4020a05060717180307270204150c0318060e2b08220303051b01051603020d0b030d0207030c060503061e150d0f2304170c071d0702010b 60
    0x20f50303400000e903038050721801d44600c20f20109041155418003101000b072130b0f51a900d1590820841100c441003e80390940990248100410050080021707108002c03c407c5040003088071440d0b0605403400041914446143d03205c007071010880355000000d00510002c203440e00044611601003007000745855290844140d420b0780748240009500c1e800030321031a110345080c0080c01d41c905031b69480300b001030b800481c0401c401040c1c008066080c0c0307a40c1810140840b000b444030f41032928242e4200444003031b00c101015000561050b086806400007254013030081c003251128604104025184c00e020301040380d003450400d00008449100700e080d6401800001e04180800c4400001e10782c0031901440500d4003ca41d41e0384a0384403002c050701500050041314030215079040c50b440203404031201552000e116100128402d41404042c2c084254040d0f40f01084a00d00903100400c9003150003001202c0d1000c3c4a018404221003418802e19401c40403000c00800c4c1c20f481d014800d030f09031408403802e990803281 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 478988084 1250 478986834 478986863
    0x20c03060f061c0602040605070510060f06202d070303140304050c041515080c070b1e040303023403120f0f050106020606011b0209071e020604020a050607 68
    0x80401095040f01101c50500c498407510303544d04030590700654001004181c02160650900c4014065628000740c4031408105c0310742041000302603074429014420801c03586015001410300e00c040050700d600f4250741264040301144004414400d1170800301f034030346903841e0a00c0000420020703000090700c8d415107070459401c82c42c49401c20140c00043c4261442e1007102d60880c40743d1202d01c0b44801d404540701c0822401070030314100807c480540d51582c02007045400802c2400500d101c20381d0660750380311503004181c1e11a00d4461100500364120414010b141c0d07010b110415406600501280c070080d049100c03601c062014224202c50b984113031940e107036007424102c00003174451040380301402c64100340014107480001c600d00403501c3d00300c40511805e60350300040c0810b5804200180d40600d0910707040d981e2010710a280c4c2e40003800303582c6c000c1c01072000001148042c1d00580c241c4901c8401d000c140d000c444480d440082d502c01042e43c0580c0501581c00d004510b038100fa0040326601030b0815241e41c0400e8 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 478989334 1250 478988084 478988089
    0x1140d0204090209090f060108070e0a0b0a0e0a150e090d111618060f050109030602030403020c061206011d0a03110303090303030106120612020d060c09051201020a020c03060f06 78
    0x1010550480c0c0c05982e8007001001640d90051260140208200401c810000404039914021060f044440c855014241c10044510700701e0789903038801c042c0800400c441404d000400c0a42806400158036140880304002110070710b6848a450381c18a183c15120301551051640f80e1200180c170341a47c950080050684840e00550000e205040888101c0d1400c560b50303038000d551404250001343c4014003c04208034070030701c0e0307028400c017030300c82c080452101d1880d010002c1e040002e680300060806402000140c18180280900c0c580800d014100070741d180e40c20140440c0c3c0348400c580e00c2c1e001c1140f03c40e080086203651f4101e500d910b5000760481401174195103d0040c6e03c48030092550307044c401084030003203070384041c0042e60081103540c56a032240c54806003508103440d0300e074000c0c1d461b03400030391501405a610010024021030300020005201d003034000c41110100e515401c015081540752480300d02c1000154000d10310480c90303900740c3c0d00f0142c05ea000c00d902c58506444008034045032320040740491 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 478990584 1250 478989334 478989349
    0x50402180301020f1c0e06011505040e07051b010b0a140a18020c0609160905070c020a0e0a11040503100e03071b03111f0302030703090506040b06010905090114 70
    0x28003040084408600200000c1c00e82c0c0c00b44002c0d01d1100c0001c1041c075440d500c80700c1d01d0809030080040501416030748044859464005106e1300320541c2240004150240c021002c40c2e0180070f5000701003859240420026005500801e251403404030541c00341d107800c00c0184070b0300818ac0c800502250086203072903ca90703480e0214107001588410072a000047e028445501e00f10f06c3c0d0240c180251b00c0d2030000710500c3c1060001090b4640c9508000080d507442a810308540341580e501c00e1000079551555170086078440b00c502c8000b90000b0b211203003c01d2540c4c5524a291180c400254248800c06040d4910311041c00782e4443d00e601a80b081c1e404849094068000340640700200301120b052130280d0b1214401b000000c00c030484070048a040902c2030043d004146040c424051310211100340b041500700c40000090710000003050f80c003101042d100b80c400e80003062840e400c54100c82d40c1d81031500345441e6844080c1c039094007250807100700145504001c040e140c12908030181d4448600c2002c810b21035903 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 478991834 1250 478990584 478990597
    0x703060e0309060403150e1c030c14070b1b0a050910050708070c0306060e0f0f040c1d15150406030915110702040c02032d0403060608060709090b0901050402 69
    0x80c0002d100244032510b0b404041c000440c05041e20311541000006402c04540001d80c060311150011020356850090307020749520f919502d807500241d07621000380c0456008001641000429900090050901803190a018010100707040b40c81a6801055814031062080c1640940800c40034049282c6a03d0308580c22070300c0302c0ca141452443c0c440903949a840e075a0020808441c000c107210300c10700501120b4402c030005003000b90018041c40c104075444010380c0310001d00d008a00c02d400800281040015126040100541c0120740b02e12884888800c440301c0044900ca15032307042c013107566907580ca010780b00050200c44801c1641d251500b41b1800702c005d81407000003a1007000b55011501290440b07071103054141880c034109a601d40d00284100800d413681d14080382c0c1194014407907510818080036840300c82c2d41c04403440110020084114170410300443d800605070701d1a003040041c3c03c1c40c01140c0244070b62015524804072645607812403044868205015801540130b400501150420b1390040c5038 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 478993084 1250 478991834 478991861
    0x5030c01080a0f180308090c01090504091104020c03041403030703090e0a020705030a05091c020a060e010c05010f090506010e07051c1515030f090b0708130c060504170f070306 77
    0x801040250401c42a41d0480440040080701349041c1c0040c50b920440305500400168040c180c101081d40000740001014041d051103607030b481d42c60b04100510041502c401c140c000e401952910400180141c41c0c0d0014803a0310114030210344034100c1840d000c011a106903605842d211016400c0c030210144081004120141c0a9401c00440c03003c10020000780c806c00c045a40e40d6903480d0740040034440c000516811080a0700b4076000c588006990f6001c6507016500d440c03620307640d4040e4a000407140c04900f03000140140d480c0c842e40503451407240e001864800d00a204440041e41d03140401001c0c0c0c0301c22211000043d400f44203810541c07906100e030781091908014081017402da54485104000c10950000c1650001850600f03100fa405002c2c45c0d104043c0c0b81001c00410301c19444005038030305d0040c100b0080111040014201024441d04050556000307091095440d4554901400395805400741045c1d850000e01c08551900c000240c1840b181e00d00c0002d411464959076401e0040c09030049084c8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 478994334 1250 478993084 478993091
    0xe06150102070f0f140906030a021306090e01090b07050703300f0606080112021c020a030f0b04030810050f19090c03051504020f03010611010f0e1b0a05030c01080a 72
    0x1d41c0f0f82110150f20041c1c0f19a40408502d103241007907030402e160b0080750403030283d556082080950384e400b0a0b01e82d240f03030b010790301600c413580d40a120400410b0300341c00c000101403401940000341601540241206445200c50115035150428242e401e80101c3c032000340054802c040c5c144410490364009402038245030740c110000b81c444000c0c10182d8401c12601e424142c2c1c2d543c010003555902c840d880c0e006203401d103440c0407100c1132600400d0b00c0c29494980000a440c2c80c8011104640b82c01c968140216048095084141c0785032402d1008032005a8042d00010f0500001c542e1003440d03080141c00700e6800400c1c2014102c3d03250281701034590703021210715480c0c541a1000800d4000ca00451500300e12542e4000b8881c42c000b41c07078010403180c8a1515003c5e43c4188850018040c0d2241120706440890600c010a05142d020440c0504a100c0748840003078102480c1c65020b060000703081c050f54a403044c211024040000a2102154080c4102e0f58168070401c414043e07940605603084d007040300e400010 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 478995584 1250 478994334 478994339
    0x2060f16080a030212060a08030706150b19090506130e04050a0b1303090902030f010519091107061803140901020c040c020606100302040503330106051801030e0615010207 75
    0x74040c54001c0b10240e80030980009548403546010301146030b00200880e03030703c01c081e800c0191103030303032400f89210041456076203c41d00c2c00c0501501e0070100040c52042110f55a41c02c5041c01c00c02c2c0c80000014205c0071412aa0001c1210701c0c0140603030f8035a259016810642030314040015540080142c07050340c483c0a001c030400c0c041510501100d2003032a840c180c18203008001d18005100020550002c0c41007407040c0248080c0101401d01c1d5411a90300304d40941c54049122039009040100d94400c00e005490034101d40640c4040d2405841814000c90003006111070304a4440113031100c560000b0000f035055000000190030304d10103000100c40601c115100000040d000c11308440000150402503889481081031130700d0700c4800b201468202c0c0c902036040074500710100350f980c14510040b030300180012400c203001400d0701c0c0303000f40590b8015448281559550310040c1c450384c0b2040c2144c0303189070300700c0791224154068060001503254030320040031603681e886078072498130031006a45070443c010306000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 478996834 1250 478995584 478995593
    0x2030f0a1d090906060a0602030c0a0f03090e100501030b0102011503021e0411031f36020d050403111504170408121908060117070504080a0311011802060f16 69
    0x241440b40a629008101301d003004000c00c4401001c503801101194000c0104e80c01088000c500610036550001c4090041c2415103000c0e540d81ca00741c1c0003407650800306810400b40c2c039408000401150030a0324100135522485004a084c5c4120200c21034003481084820001802c1403881c40054246001481840d064038034001002d170740c0400d05005101101209010003148130981c140010244c00c203401c800586000c003100802d0627a1058080b482e451201d494404819540d4425002c0084031310031940c940c2e50121610040074143d8082d400101c1c0310b6a9030500360030020715003558244a03d51400b080c0d4541d50b03924590801c00e0081d020749001440000740700b600c108089203120941c0b01c070f0300b92a26449800a20f00c80c4402c0009001c008441c014014540d0b08040510f640c400103d450b603000340d80b8400140c03401d00c1191320840e40b0340300304044c5005055110945045890103030000344000b03441115002c61551503054007030f5000341c0422000302150300040c000c1c0000040000a50f10850407a1074 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 478998084 1250 478996834 478996849
    0x10e0c0c060417210415021201090b15191701081009020a032f0a05010801060315081b01081014120109020907030506090a05010806061e06030c0406020d02030f0a1d 72
    0x41c513080024040601c010011010010040c40c180f144045080044802c40c001e941c40062264452466446110507500e4031543c443c00008815001610303680c10b40364088582000d0500d40341070000f541032313070081c0c84421f69180c1c203412503207aa40140420301c4d600f1514801040d5a2804030382c80581000000009034000e00c481d5024160000201c821070004c00e00c11010000e10000e1a1080754122018040d5a0b040358000781941d0040c42c2c00200c224052004074035004098000381d500c0d204656892100100400c84c4415090b000c1c0d858030701a460340c0900d04003008981c00f418032090345428810710a030500d1f415100034a681140003051032541d64000c01e40e4540190340410000340c4880030400c0d141440c50115403c145407000c00c010941c03400c0c42844d25038a000d01400c0c4540c490b958054032030709000b9134413100c1b0303035000300880c4e0360b400c10401c0590140c0c890700c11035016008900c0758101143c008019913844801c0e19080c107242c0300640d00201c55003002d00c030351a400180701b24026880c6845a10 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 478999334 1250 478998084 478998127
    0x4082809140f2e030c020a0803040f1502040501020d0e0a1a0f03190c0203070b150d02182e030b0a020c031c0f11042606040b010e0c0c060417 62
    0x20140251043c00038400f40e00b0301d212043e0780074182801d01c0c1640c890307030028040340101d4001d003030707141c0320f0f01c03103250507410404228400f4155680d4900c0030319046000d0341c014022604240c0072a15600400d03d415500c030050f08150b1980910301e0310b41001250f01c09840740b5041c03010410540c5c03a0a1b41030700c030f42501da0015191040a0b0380b008040800051181c86007500d420058002141040c415940c2c060302841c0091907000d81c40042d40d075180c250f403600c00b6000d06207603000389801d0011010410580c1440c03011a54002900c20700c000040900b00c21004594070003d4400b00002413500f10307110340c14101c0c805000d040c3d500d942048560700344401403010f40520480c4014950896240c0d0b48504e040e101152a041030241c40c00881040d40c0b1141000c9404407079440004640c4080c00304c1c0c00c2c10b4400c240c1e0068110901510081001b04010381070224103844a4592801690306d405403540c10a0140c6002c0d0b40c00d07644082c001c140400c1c002c1041040d00690200014904072920721211846034201 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 479000584 1250 478999334 478999369
    0x3090b07021c090324060b120f100e07050f0706090f0204050f0907030f060212070903140316150b120a03032702130b040504082809140f 60
    0x110b418101d1680401c1000e00031000d0310b0030704861070454543c071900340c41107007081000040c15070f6299800070701900301d440180100034039103481d44580040300000c40d1040350480c640981c2d02c0c00148541207201c0404058810044c89202e05642e1a14190f50590009202000d041001c0c80300b040015007a000c1c04802038450034840462030f9403441440305840c006041041c0f043c6030310b4200710a2840001e84113045030f40000d00695444014103150f4001e104584200010300d40100421034882e400c00201000c4030b01c2480d02840c1000402001c503101c3c090381c1e032000d49000c190004c12004c51a840064061302149820000f0300c206c41400082c034140d5401c40030480ca0f0040c944802c2456054410110204041c0c100c503500c25001403050101011b038007000030320820840710140000391241d4030034800070380084d008004506040c02c140183d0307003006084541407814403503403031025007800182c0182c0154680f0b83c009202d091200f54009980c0209080350406c5000c500080c43d80d0301c466007010401402d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 479001834 1250 479000584 479000593
    0xe091f090f0c02010c0f12090c08070f06020a0c06050c100f0506010e0102070b040b030903040b04030f110f011d04140c0a0215010e150f04090b0a150b04051003090b0702 74
    0x20300441d00e068035a809121015a40740c141101c02c01c9400c01c2c0008103c250601e405000c0d4444c0312000002089860030103031030140917800c007240c280310000c2d240041ea03100c0c0b401030f52500c0d40e9100c00c03a40c8a000e40d400500c0c50300012801c0009038011000b803ea480490b1094030b400c0207280080208484201e042c00040030784170014403034203581140061103604800e01c050211b041c00e000ba04806845079101e4840d1001e80040050410402801550041c26603001c0040d9113643ea03062400980c0d16040d01034803501444001c3e822240380410b40c0b501c40300e50603121140a0302d101c162800c0290303081080305030010b864680d0796984c1004011114840d11840075429181e0300d80040007031808000c00082d9019a5010005010044010900d541e01c040140c01d0024040350200100341c0d4095281203c40d0003e040220041c20054103181044c407400e07021b0b50400c182078111158072405810b80c42181c801100404c018406820300e25807030280304102c1e0402183ca828641d0710020a801d080794a034005810 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 479003084 1250 479001834 479001851
    0x7020106050112140c0c0304031208040203010c03020c1902030708100e07050108061f0905090c0a030b0f15160c151d01080601110f011a03060a0c0e091f09 68
    0x8010081c0440d0f00030003402041041d80e80c110114012202900300580343c074010030146c51203101042101c01550b4054890300c00040e07880005403550905440481c880e50900101c000c7c0c00d0301c60300c252504a41d145005281c4441c81030480c400e1266429804e076054066030a02080e1803000308280c049800c00c030300d00000d410240580140c14585c0720341140d0304100402e8248040c944c1c134000b05002e28450070340d44444402d12400d06036000c855581c800d42c0c0003100034080040802c0c2e801c0c090292500103807014810313001c0010422086040704001c5035444405840c204201d840c08101800713601d401362002510010490b164101b40301080d600ca038020540003000756082030b60095018540711102d41c4070304076000c00c0310000380501c03500a1405d41042403900301d099000c2e40030030030f40020b080c0b10002005401448071480e280706407596105406880344001007105560544260392000f01c180ea54050502000b104200688401038009411250710345011402184041d880000401380d41500207101306 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 479004334 1250 479003084 479003087
    0x12a09080a0201020c270a050a0f050906010b070c090624031a0f010225140303160311032101030303060b160b0702011409010603110a15080414010203070201060501 72
    0x141190030841098000400c07010041c0d0b00050742c000b1200d011a100c12400088030f8180c440000200180240c40c2100400c0c080c502400ba440207000e1070300031348140300d02400003c40105694003545c6d40ca141d0b5001d20010041c8801006c0030303248540c410022840b0941e0b440a04600f0386002d50000a49010b00f01500d03440c00d607050b01403441e004100d09080c000140441d030464500b01d4a400514051190f502001040b60302c05d000380c8031030904080070309607501c00b808610f8048941c1d601132507007542c40042e00d0380070a2a000058400b0103050325100324140c68107640850750389822844060711484144010300c0700b82c2030004032034903210350308021011541c5141402025074410b40d0004400010401c09a510103d414482c52500350f040f800c416442d440744171040307006040201c40075505260003018021001819007044088034010100c41c0b14080304035013004011140c0b40b103880b100304801c0d100b58104a000d2060ba5070311a001d1036001032003025003a00642a684211000f80041c0d56030340f410310456 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 479005584 1250 479004334 479004347
    0x32403080901181a0f0c0109030309020f06070b04020d020f09010b070b07050a051e0f070c080c01030c1b02010507080a05030a061a0d050c07050d02150f0609040b040302012a 76
    0x2800d03d0110445070381c64454807540d02c1207021190a0300314400a04240003158000860384a9000040200105030060400900801441400700c0c440c200e15400d1080c60305e40007068540d09600090106140d403500e41c200840341d048044106c0c1c0041070006540360f40d541e181c809600819070100c0d0a42c0e40e001d149050f440702e02c80100350b0000d0007028002d8000c200d501c241035420454003c203886500f640c4613002d008241c090744405808451001805200308008060034100f201c519030100c55214074114010f40c1501d03002100d03200010030180b0454a10380006880303c1020340181091440d00341c040c0c4542c2001e5000d03028040c017052000007401024900c0b03100c2d4100405210194029403040790740c04030b8403440761b1030119406a44070404540c50300103980c2100c80003039020040351f546418104029403139240801036628030709000400a01810a94401d451007000c0041c000300c5580e640f680c1d00c110315040034005404542d41c410b81d0240c192803102180e00140010901c01510035403c04004000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 479006834 1250 479005584 479005607
    0x210803040f030807080c0306041505040c0302040e06040b1f090b0706060501020c0d032003090402041707090605210c1201050603070b1312080705071e0801050f010501032403080901 79
    0x410217060100241d025001c002c1ea41c0050b01200c02040b04100000e0300f50a0180c40e0700641d910501d001036031480f40c1c0d09940104200e44000031a0001035480300300300003c4448800055820410b220280548006c0e400842100c4031510305040d846580c40b034100340754035080018100c070100e550f40e005000a68042100f080e090b08201d0780143c5582070345d50b0051024514904900c070201030b001c040031003040d05005640b201c01018208640b0380d039907102201c4c2824207542c0c40d1001406512000f01c1c2c0d0075801d000b484241d401c0503003040000c01d0a1034038400340740c09819030103040c0d0140d0a6004419030321803c0c030703001036500c100c00854141481001c01d41080000d500c0b0303190000040111080d0800007004040864020f1444458554007506200d21984940070000b440c1340030700c1002042800080400c5030f2040041103d020a41d612620a00d00301c0c3c0c820384017075090798226401000700350321a422144810014507050155180840320366450b44e4150b800840d108000452910255644810440c0c407 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 479008084 1250 479006834 479006837
    0x515030417090d02060c1606090803040b03100b070f02131a090411030601030b010f0b0c1b0f0402040305010b040b0625230105040510050907210803040f030807 70
    0x1450400d907544000701020721694007030491000c1000d58680c0c0d106030041c040960050503507951004010f00380e42d200c41140760024102444400046180c5214806180c20342c0d8040e40254a85400d0840841c0690401000c00340c0c91010301a01250b0342985401030200b0521580960801440500c1045110000961501c83d4545407000c441c40b6400000c0a18000c140113448196081d00c0d603080c5541c0075003002540c3c580500c280000001040300d0011114104d540c45074001a06944501812050380f041100341c000340e44c808009449107004250030b2a04112000702f071a401c0c52210b601003403d9800c60380c030940740c5035564040803016040900402c0708900044585070300e40722016580b1218409046004186a0b03800b1320f43c00100609100c034130144c00d07806408031907412038100c0c445000c1d2a040764100c0382030291403146900310016003d41801742c01d21001405c1c846060030040d600e4290b0040c2113100840b80241100045100c036002140628000c1c1c400e401e0b10012828080c1200e03001604050 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 479009334 1250 479008084 479008087
    0x12072301140f100512030c01150807121203020c1c0e04051e01030311010f06230d0b2a07060507080906010305030306040b0117070e030106090b03030d0b15030406060515 74
    0x1000c80700f0600014150f4130300702e400c50b00117034080107054a50300501d8890150780d03180800d03880341000d291034240c0407500c9640480382c43c1d41d1a8916a0298410b49030000c000351806140030301814000e40241c400a11194200c0b2200156410569400ca00760300c20301010401c0c07118034109a003480c0c011140e004181e00c21300c1e13050b14a102080c0401c4c2c00f05200181c100300c2d5580380e01900c0002904180c8110102000a004640e102c81c92031240c03400381c558142aa01c01c9516407143d03401e00c00401c448498114120780d640d0b0b6075103c6101c0d040c100a160401c3c008542c2c5045005a105060141003c1d83c0205c0001449103007a003030241c221000541400f400ea07101d480100002000041281c0d0b0043c820b50700821040c20000059231700542c4500044242401e603420410040c2d8800810461345c00110000c0c05500d6483c1c244d2070072034a00f03146141e01030300308203c05520488150031010700c0110241c5030307a00540400a032828181c00549007100c005460311400c0152b480e16481030b8100840e10010306 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 479010584 1250 479009334 479009341
    0x271f02011103101205071a19030e060103060506010528020606180103080a2c150705070b09150d1b050306030c0103050402040f06080604050105090d0212072301140f 72
    0x603e101c0c0414803402d40d82070b00e19500c075401c11000784207a0000346800010600801d00c040c0030b0003299000300d060014158220000700038054807034080c0701003c1040c00042c03c8143d003152690005000300a040c5414003800300a90890301420407101b4240030010700b0340e012202e00c114002414800e026080921400c0b113403d4444680c040c2060140c1183c0d84510103030340d40c0da0000d00943e02d1580c480072a030b0440301500045460141c00f1070144400e0001140c003a0042b65201c3c0e40c5c43c806000301a400741a6610000e024469081203000801d0080d000514030301703c4e04000200101030341c0c07254202070440b80d00e07a04038420105c02c50f551f20401c0c081c0707070810504526180c0c0c0820317074030207000c051141019140d034040b40075522682c3c40240c0e441d440400c244105034030b4003121580c8440903034040710150f1038000040c010140c08505105482d001c2c2d030203440700c07004c282003108450704182425102c280d400c04828a85022115921542e00d45100003c1801c1c440d000c0803c00b2808001d18a0380350104a4082 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 479011834 1250 479010584 479010601
    0xf130e011502070902030604060504021803010c141b0f0d0c050d020a1109041407062601061e030b09190c080106120c05070803130c0902090105271f02011103 69
    0x743e001d45000c0f05005132241d441500060191619a020540181c800105408541540c3c1e110b00c180345801d03030091241d02002e10b41141e0205480b04002182142446039118850103190341c144007055601c1100d00f1004940030150800300c8880c848404180001c501808000e014080540036500c5800903001d4030360103860b001c101c41c8032010003d01c6001880300040030004010a03102c000b5000d101152243c54845001900344110a440122000d920144045800c801d025595058a200e80e6400b070030080c0d064010354a0481c542844402d042e261840c3c098a074407116079140c0b1135046555980b080241c48042d80c1c08403000d92000c0810040094010301201e60000b4107021402601180051401c003440d0040301c0070300580e40d00500100000040c091384003c0001617000d00b50140450b51186545d40c1052403c92040c49641400b02d0014411100580c1941c1d490303155208074003040c95064000100086c194070700341c5e0f056074103417142c0c0d01126011560900c034102800c0c007101900c0d4510f0915810 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 479013084 1250 479011834 479011843
    0xc090109110c0607020309190f060e0d050d0c03030b062d120c07140604050d03090c030b270d020309040c051201090c0f080103080913020f130e011502 66
    0x2203404054030390303264404068100085448a140300340c10340d040c07410070260094a941c0440c503543e1044900c844402141c00345002c0c0c0c54110f913000c078034954113240350501c2074514048000805510040721000100405c0090142c0e0902e0081350740d0340c070700048040c5000360071070b41030101c1680540000e0110701c0603003280b17001e0403201615405420580302c4010050050b507105044281071b020811209100b00d50407040045c01074140b140c0c0b5010540d0243c40010396545408460142566002440504c00c4600a502ca407000c54041c0d0000c0b1107007034980e04d41e03c100030800d80782d2884101410190111080d51410013801091150002e002002d1030400000e41d030740903000626200b0b075543c1416080580c050350490b0303582200903143d4840340d80c0d5210071000070038421668002117096840001c102510507036020341601e1380030421070700784500d80040c0580c441001000c4284998208100002e1410342c0014107001c801c403500c12400c0c01d05150242031440c6040e8031594150541e6148480702640119 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 479014334 1250 479013084 479013089
    0x9180b0a080a086601050114040507020d0309060615120e06090703021905030f030a120b21070302060318070b09011704032105040b13030509060702040b120303010e090c0901 76
    0x84e5800f00815019000b0324401881e101e12510700c83c0c8203002c1d04448106401050407141039002c0c1c0841c1305507070000d000640702d00b00d0b07261006802090070501554020f43c0a0701c0458001c0750002207407600c8001040726003a5203c407000c00314421220f4112142e5150058a040710408400ba01580c01e116941c0e6a40d0810342c040203104d424190030503000c00b03450452b01001064001c00305d42c203d0000240c0c00b601ca0384288120000a036a80f2200f0100313810a0045106045018007004480c1844031400e0440900c04800c40403c0d01a460001015030381d06d1025500030360115607018001d842d0b4003045072402c0c1e9150300104140d4402d120750782c4039a8000907074550b02d40c0c085940e5002ca41c0c9500e403c0f02d0080005007042f00e0441c2d41842d13070b0003d0311030364001c0307201d02e124014190301c64840b00c4046a5603c484880100014410045030ba214144030000e0000144060004074081d408040000d1300d400300c04451680c1580080300401810042406954004103103401403c4a003944401140d82c406050 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 479015584 1250 479014334 479014447
    0x1e030405010e0d17040e0c12060105070602190203030a0c080f011e09020a0201020306010f03150b0a1103030c0c0c0904170a1b03080703050709180b0a080a08 69
    0x1181035007060b40b2650f06080000303030302440405603100000c04103025500a0b0180b442481c104000140b01c40780305104640a40c58480108001c1c2d07a200c5d4011680350f4000307582120340d103409000320382103218545460b1040c2c1003640c0255840b0300d4620b244004442501d8044400c0100c0642408801d4124204950540321080e62205400144044c44450100c450780803602c098400200d8001d2258190302450044409036213140381101c0c6100100c098903035003611815142c0e1001010065044500010a0008030714102020300010180c520b50941e0002c8849000d00803000030100e0b0344003001d1040c40e1592400301c91174019400d25441e103d2902213046400490820001584120f603170107084520040403e040c2c401d07041c1c80d01440c004080070415580c2c10007003810a4082502c0c10301070403100c025600610100546000719403201c00180110200d141c0c0c00214802010800020034008008c90070b0140d0b03d010391f01c8815110000c4100714070310004220000380d000f07001411100b103043e40c0041d10003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 479016834 1250 479015584 479015597
    0x3050405120f1212010e06010e1219050c091f03080d0207230c041b0503041b06051b07060905120c1908100c0509090702150709081e03040501 62
    0x1c1611181c60450b6182607400716200d1800c03c010071514010080240e8940c0101d5669240da865107000102c0704295000d0380428200402505103003880024490041c0c10101151100302c0c06184085d0041c21880090b103064001002924080c28076480d41608603504c0496041c1c1182c800d040c00d4800c4440c1c0c00002c1c540500080e40505480301e0b5016260b18907002010a00310f11603600c8454240c2054841e006c07518091102405590720703051140c0140440d412a0215120340a0344081303400f98070050003150007880d00c103010603070748958a00c1740c00942120748680e036850743c0400c02c0c0d013201041a202c0f00c11540c014401403041e154000c10450480f0002d84034100941146040613050101924141c2d0f0440c92100c0038002009000c0250002c85642206031801c3c3e0b00c648580105862040c10841d010940c2040002140d04100b1142c50340281d60f48143ea401c8400d038142941c4030803081c0c80190020f032001c1410f010000041c44501f40384c040da1418001b8800c072051605071a8011441528140406d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 479018084 1250 479016834 479016859
    0x9040b040f2901031208060604050f060d0204080a1a16080a1e0f0606020102120f131202030a0f050307140306030a020d050105012c0406050c070203010c0c11010c03050405 75
    0xc211407400e5505804200e40240301820b200c8020050024030054400f0101015403a50503800340602a010b94000741800380341070b090800b8800000c400c102c101c2e80105040000c0940358132144050806007000a01420550519040180183c0342e065500950f00311031500340182a0070603015607010345101e0400001ca583c0e40e80c0050700a000c0b60103200510707100116003440311600d69004640c1445007032000c1000d691a00c00881c00c03402950200d144e00c1c11160086008010301e0075145922070314076215442c00c03040d00d60382c0346103140e00912120050b0780045800c09007150081c1d91310225480918200317045107400030008202c90701603042c2c1d440c0d580001000c036165031400d1000301c00c0316401400d21040c40c1024603000b4020042480b072100006441280c20058000d4200303845030b16000c101100c4413685994544c2001440701070f205182d900420080c0c00c006850a01551088205540341d0b03201c490035038207088411030600f0400c1030400c098071403c0d50002c1e4021083d58140d607016900807003580c4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 479019334 1250 479018084 479018093
    0x6031605040b120f0d09060905010c020d0c1a0904060b090105070f03111f061a1b1617070b0913050402060d0204030818150d05100b04080c010e09040b040f 68
    0x258400d142043d24000d8042601d40d07242c000800d084e15040a60382c1300c80d040d80d01d04080381c8840c1c2034080ca0740018400c41800000d468001010003d0300d0050380e20112455440301c90b04640a540300031110081c0d00440d4034105031401d8807505005080380810240b402c00d8840000b800c0d441800002401200420201001c2c58801d42ca0000340340c00754804c440d52560144004402c1040704001550b0b50390802c1c0003c1203401d403101c4040100895015440c0c20700e4850b02c05c40ca060a40000c08008174418840038894083e440076200c40140941d2401c0c2480500d0442030a082034001d03000481c4c00d1004002942da280c0b940031000926500c81c010003d440e48580c03001511500c10310b5141c400c424004070303001c414000044014003000103101c081e180700c0e8982030148074000f900032030104403401701445030288104050f04020b44c02551015000061a1a54815502c41d00140c2007883c103030f442035555814658010840010083c070440d0f8504a81c40c141d0b50301d50490350002d0000f03090980d01d290041c10071 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 479020584 1250 479019334 479019349
    0x71401140a0e07080c0d03050c0c04020a0507020348060c010203010f0f120b0601020c030a1b050909210c0d0f0f05211b03010e0f06031605040b 63
    0x102045490522074284041e00002605680c066030889001e880c00016141e070340016100c0e40500050803041c8200210b443c10b40e129080030219031010f02824032014411755a0b48020320149903243c890688525a5005040c5800320f841c0042c6004003003c81d0f03a080c0b00184110304052040078001881034a001c10f800d1021804000313501540000b404955080d4580064010314182d413104c62030402810703035400d00ea007240c1d841403081091801c0c02c03d140c1008200c0c10241c880c3e00c06410b00499480e44504404203242c0720a0300804e44606d00c181c1c00304070200700994000001414111503510040c200002480c1e01d404888020003000048918101f05c002d04600580d041a42050107440d600c04e180c400c0504242190302408001803200c5202c0580b550143c002cde594440c501c0d00814103400c1300b556900d64030200143c400c1c9000a0981e142c0710b403400030f1500840c003810789403020300c84a0a06410541120340090a00e03840303500915004a00c002141000d003084aa080324081903414801c00402c045 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 479021834 1250 479020584 479020601
    0x2070501051005040e060f1303091d07081024020a0c090507090506210405192003010902060a0c020a09020415080604050105010906080603030c0303250f05071401 71
    0x9942448104182054005803a400321001a1828049505540aa00d86981046500a01c948502008074004411030a0030200252007410640211034464200350b0304a441064500b107511404010814182e85c40700b9020f400011510782c035035001d070a040c250740350b802120b0703400d08503000604401800d1500c03c000032210035401103c0010400c1c0c9a20602010384411074910001c1201c40d0400115400d01401315408080107a0381040c40390000c400c0761090400c007070000d0380c55110f0b04c48a800420301520403084001d11500d80c100c05441c01310402050301138140c848503c02d9161002034000360300d400040f50b400c1c42c0d040c40c00e43c1c0d0a0301940700007415600c440c2c0140030301c2440814007250843e0f6503020f01140c01504d454854040c2da40341c00300019503c09015140c006041048104107103806922410b404c080d000742920b080281920020313246820440d075210011400c0c40350b52001c2000c035a0011382c02c00c280e1524803000200240040d00b98441d40390700902c100140346000c10050801e602c09441c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 479023084 1250 479021834 479021843
    0x61505030a06051c061104060909020c0109051204140a0608190e010614030c1f03021813060e010f0815070c02040e160f053a0f0c080c0a0b0d0207 64
    0x300b08040c11100c02811880c00c00300d40745486d000c0070204440c0070318107403001c40e0f00b140e0b03c0740758103424400d10740065042040c40e40281d64030344404400103101484007640d60607441c1b0b0000d03112071504003801e88800045c140c99001e07580c40030040c031413541d10a5000341e20483c03040800c040c081000060000a214040300d0000d10351a00d4400b0848084945c07803000340107030880031281c0d40c1c0820300403c4100c03080784001280071a946100b2074010790203a000303407034288082c0740303c0380c2c03419125004116103a16400000d80065503c0e0000d1041c802000810390141500b103812981840c10245119600c0f141760030031303d801d420441e00048440d84140302d26a24250701070401e000c49103185c10515643e034020303000c1c9400c507075400c0d030b0106150309181c1d1120200e0b44010b101000004807825007030071502d4071300310030603801c1d08007282c00c80c07288059009906210701c5003001303050400e4241030440c4880784035000500280c124680403651907895508031015505040001580d038000202024003c0c40351000040 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 479024334 1250 479023084 479023099
    0x90516030e1c2c0f0909070b041203020f060702150c040503010e07050405090a020310050c160302060a180f111216140904080406030510170c0f0103061505030a0605 72
    0xd2459031104009250386546045090101000c80040f1145806200c0d80c58008400d00000a0f10385031002846030040729034815140d015881c0c1c602d40c61154016000403111210000504081688c1000158140f40240c0d007e40000d04140034000e49600446040c12548003440010900c0500700c40122002028020300800c101941410600c0c0c46603098030405100b03e01d0000058036800c0702085451b0303242c0c2e000b0054402c440400d81c0d1500100300240202100210078404c10309040300c0c06202001440c0250010207a52800488120543c5c1000c00011034000d1002c0e0388a0004854800b03940e4065072221118030340e0b0400a010034051000c62440d40b14602c15801e501c156170250322150301c01d5580142c0b12185c3c51403c0c82c18443d92020a0340c0042403910100f2042122a100358000e941001c11840d10201c1c450742c40d0580d0354401c03404a0820034039044809074181500d04145036030381902083c20107111040c034100c5401c0307100c0d07481041541070200020008503400712552180003c1d1800a00b483d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 479025584 1250 479024334 479024383
    0xa0b0a0909050a09020a24110a060e16091a010309030329010e0a0e01050d0609060606030614040603030e010e060912032706160f0c06050c0106090516030e 68
    0x490180000c03078000c3c0e000703507a06e4101285402c005400410021001c04034200c2030540c001003200c4d186e00c000d40c040006d004040c002030000c1e1a40c0034400482c2e0403040241030000300c455981949100c15800303140854500b072590200070b110300d0000034221500f42000035042e451400c056001d04100000102485c282080c54030001280c804520900310003a80c0354150810f0302010b014050741c0f03501601c4040e50800c80100304902c1c0c03007001010864454000440c040d405582c4010a07540e803a0481c1010a4031004184040e03925001c06001d40b0300100c8082c007801c1e10f5614040d0a5100c030705c80c441c1c10000c08180706a466103400d000c9400141001d848070000308110840c7d00c0d00c9400a2000b0740324612075800910103030036020f031440c40200008021510303080006841421400d2002c6040b50300c4020710b943c3c80085410610f080700108400d032039907130350740c04c2e102901030850318a0340244e881d41c4d20341010701c201c0303024080003404403800314100000c05a401101c49031400070340980c4070900c00c050f040340 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 479026834 1250 479025584 479025601
    0xf03063f0c1a03040b06120307060606080115030c2f0a0c0512160b0a0c060218030106090e0a06110408070602100501090c0f120b04020703020a05070b090a0b0a090905 73
    0x10003048406201c2e1021001c0820700101000344010345000e1701528150b00861614903001c0640c1c0082d4080204682c5000a196203c6054420079030209000c5419000100100c50140707c03940341040c2e843c5800c2100a04503100605000d20f15030305422501c212094041c02114409450300d80b10101404903030f01c2110f88d141007504843c1d20700071540220102c00304402441342c00a004441022644901e00c981401c1c41c100c10165041080040108290300102c480800c1403440140046c11850000c0e000540d440d4003850309444441c0d01483d4058a00095402d005001081c3c80d02c1185e8010740c0411071100c040c81c4101c450056400c0410b20b070094480018059400140101005140358014007560781c0c0c448410381140c0b0403c4c121400303c2d50801280042c14270511100000d0004140001500b00c4107901082c2240c12400701140541c0c402a1640c09000040040000a015108034a8648100400869011000da124860070b45402040c160a140e01813503002c03001d07011380a020061803400c02c20707 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 479028084 1250 479026834 479026853
    0xb1801200f010c050421021f180608370c0c030e0f06040909031701080d030e0c030705010518131a040606080c090418030804030f03063f 60
    0x400259840c0c1030f01902070902410a440c04c0768071488900d544103820030300900c2000030480c0101d0b44403640c52607140c06400650070700319008840da40c80c4c41208150700500b1340b40e25140c1d0043c50500403140e04000d07001c2003c10300c6004008190f5541b8a20510f248040200e000105c0c2280e801c040c2020200b0b4401c99000f030300b03504542d01950714091031441c21402d10200080a808041d00400c0c10003050204002503001841d00b18030900d80000190b202ca04101c005140c2a0800307501500b080400c8405581d150144a0505144102920310400c641000982d034500c948906414003201081e1022850b4005003083c0340400042c08030754201a400302280b00804200c5441d5118107048040080c59082920501c0140c8555846515881e1241a008a042e80044240c20303031040c1c0b84c0329140b0236604a581070070311040c425250807000741414034000d0404a00c8450740010146031034010802005402906107840240d40c03040786d42d1602c44081807030001d940d100000d0000001c030300c031541005079151 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 479029334 1250 479028084 479028103
    0x806010605090306070c0317180f0c0f010504080d08090a080f090103110702131a0a03050303101a09190e1306060f030206030a0507020a0506070e0406050a0b180120 72
    0x302652a180c2d960b04046c4e9145841078130150000b01401d00050046d007010b01c0241d00090701c500c11083d10b1038290b2201e40303088031a0910f02c41541158107000840d0a0201801507004402d0903d90f051504008040f0381d12000b94580c042000f035843c010442c10903040c0803a5142d0760700034243c40c4c2d5a610f4004544102d9100000c110f000030703d8000c0d507407404500c98064825051b401400c981d2001d2488038044041d024008a060781560507036040d5090769075805900c00154481d0001d140c5a241c4445240140d6084e64041c407401800d0700841c10001c4091021a4000c1404a4541803505061160818400c009401203410180204d05102c440c60a140380c2c031450510684c020701c440e5440701081500c00c0141e11001750005d00600108403040000d070030070303079205c1c070745104445140c2800e0300c2c0c00b4606007003901e915001c5404414128602d0825004c0c0101801c0c09440074800c2920b029054400b80c40340b800c096008511003690700300345a1140001c0810b840883c100f8141b0f00400450558030f522149 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 479030584 1250 479029334 479029339
    0x711100528080f15100909090b1504060b04061b0b150a08030a050706020d0e030f040824040f0609080c0313090c140304032c01020f0a050606010c020a080601060509 72
    0xc6000a2400b500043c0c56480f410a41c000308032100600700c1848400078441106034241b2070004000300d5005590320550f2a414003c960480c0740d4100240340c0100c3e006107103141406203003000000d100006111741120300b21101ca103401e0070051401a180340b172007441000002c2105095400f40000c0d141c003260240482d81c022143c01c04c550751b48a020315900c1c898007030040003081c070901070480480c14035806803c803500c0111000c5600800d0307098542c1964002c2c4401920900081810302602c20100004403003801c1000801444518035080b000300043d00030402804e80d00726845410400c905c541020b481035074010042500c6040b802541a102c0c0c204810303021003503280c0800040c00300054000c3c400259016218507010400701c03164840980d02c02481074043c40424004d00d488030702c008031403840e01c6401001e102e09061011000a051250080080c6802e9211403070290201e00301003602c9400000900304a40b0007026480030400009282d40644594003c51000050f1b1503041002016640002c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 479031834 1250 479030584 479030597
    0x605091014010c0c05060a02150702010c1709060a1814010e240105061b03040f030201090509060a170c0d1b0f08070b2a150c0711100528 60
    0x1001c0110b4003e00c9a94000c0d024000648080086080690040c40c1045c1d091054400800c450403034200318002c141c441e240141c0d501e40502011903031103000405c0030340343d08216210380c0c20f1490b030f96942c4541c05021451550386d0385000d03804004000c08004043c0b58006400d402c040010300c10a4002d00c807ea14540c1540034a12071a011034141107441c8002c000c0e20f600c0103e0b107900b400c2c00d001284c0c10004940038002716a543c5988071080400141008104c1c5050b16040b0301e0640c40010034440d1240d0103180104491018040107a59507490002a102081081c0c800342810500d01c518046800d41d69607081a1f06181060501c032854800e400500103154285054a03174400040500341c031944110407040d00302c40c0741030011410b03450040c5030291010505101c4580c5850200f00708110000b031801d0a83d001c0303110f9148015030103040951181d0b500003080d0030024291910f065982e40700011034881d081906007248018000c4090314003524074442c50f090345800d800f1095903200c580c00f10400c00f2645 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 479033084 1250 479031834 479031869
    0x12006010f0f0b0f070c030c17100c081303051c050402041a0102030a0c110a0e07020d0203180d17130e0f04120e01020a080a090e01050a08190606050910 67
    0x101e1a00703500480700c540035154a803010300004040140c11820040f18206e0050f28008003103400b01c902c60780640f2154401001031a16400007503d08510101c002031801c4c24022611f00c05500f00482c02d510005020071a00307560307401c1c80c003101c3c1d510580f01e80701d10091800030340c4c80360419641d020714881d51003550200101d00320071703811110780a10407041c0d50050740100b000d0035a051140d200004c0c86482484031075201c6402400003100f11a003070b04a4440c04000c1d030b04105d50365504003c1c0e60079241c9203001552502c02502d030074401c0090031502103401403210000e04010044075003c026000c003211091192600300050040d82d13640b0042c03180c00d8a03107035904049401028038a034054040e59200544090b80e10701090107462400450354550b056004400601010501310002414020034640d00e1718655410050b882c41d0204042c0c0010340525480381003440f1480f00003e4181501c1003d01c6004180703025890420f019110304c0d0400354000c0c12883c04c0c02032101c0300e01c1c03510042c0c510b1101040d01da0714 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 479034334 1250 479033084 479033099
    0xc12060905010b0a0c0816060207031214160e0d0507080d140306130912020606030111040305100e1e0d0f111506060909180616120506012006010f 64
    0x4100f8014440354500802400c51a580107400c5561074510a0700300c0c03801c110b50100c0608000114407410b903000d5400180c200105036020300a103901841340b8008200401803082d0310030308080003e001c01c184e09a4041c0c0c09003458014603000350102c1009102203400c4c08a450066118a100c1c030404010f0b00c144034078041c88a014000c40d580307050350444c65034155611002005124502101091031151b51000504042410115517507408905034000b450340b802c01d08141400c480c1c0c808030b094600c800a12043c00010004950384259001181b40403c2c00c031080200c19041c0b1000129242080f070b040300c14032609100208040c5071007210340e00c6281500603143c400b074a2424000008100340d401c80541205100172400d2003540004002d80094200706034680801c248400554001c004400401140106a1020045036500804101d400c0701030900041c006440901c4041c180440140c840e40002c240303910a60003c2c1e04d001072141c400820340941c5c1350740b0342ca4503028082c43d072801d9911400031800e00d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 479035584 1250 479034334 479034341
    0xb1906030c1b060b010302040e040c0f05032802030c030f01061a03331e031e0d0807051e0307020715020c04110904020f0d0510030309060507030c060c120609 69
    0x100320b4020340209105036540d070000c00003018030a05143e42130101041070b00c0b000c0c1486104a10402c0740801290600c1ca514440d4807150f0b0055200358850185900d150094080d0340200713410443d10b01008554610029041419000c0d6564052250000c080c0e01164150000e200b1101e0071440305641d85004014601c481c8000c0f00c4955045400307036420101d8005040e682541c0e1001c581030038141034419400070386804410b9402c410b030a0100340d0904200d01d400d010308034150244044d100c407030400c501003103a101c07040c890141017030015190000e98128040c20443e49840c5014a59400303040c06004624400d400640e084001841280804140650301c1c20607140702007000c2d0014407124114400b040013a1110112408402001b8064405207850781e0028019011300c40c45c0441c4c480b0f407030009620441d6001410810403044020040000c281c210a001d4143d500a2400341d0b6940c815003000d851110035448001c00030b030b2400400b045a160b00540000101d01011030a01c201c035910010807054 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 479036834 1250 479035584 479035607
    0x70b06040614100e0a0801061701090b1306110706050f0f0c0d020a211b080f0705030a180b01050f030102030c0a050304141005040212031303060e010b1906030c 70
    0xa070501e00b0030200340c6400015010843d04510304140a2000309010480c0303080c03658440d40083c1e45507c420b10842c00303840591140803114900801140c0d0385500ca0791b095540250541401030510300d0100d06014050300418440f60748108641d503507500c186401c60003000d0403540d41050200000119160440e500075180c090f2520f00d6506060500d2900d03203000035440b988800c1c043c00405085110007824046007042100c44441340020b0b110140203945045201c5101d8030410445c6120800001d84a0300008582011061030007985950300c0d9a40c8100a1186104c109404028245a002006003c110007410780c0c006650119108010b2010304d030030b074003041e1108140090b0034808400c400303114001440d4494092400c26840320b5101c241541080c240007844032031603854004100c250f08203625500301c2200501d004524004010f4904d81c500240c50100401c041e4543c200508007030720940000307055400040c020400c28001c2d403001d040c10308880c4076000104e0304041c11030003218000c03074501d80d1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 479038084 1250 479036834 479036849
    0xe0a1406010c06020c0f07090905120f1c0902040e0f0d0c08030105040b03070518010501030515010e01080a0b1c0210030b181f1e0f0f0b16020d030203070b060406 71
    0x4100500b0b5450f40040d42100446005512615107180c066402c1004220002c0460b4180041ca84490b404d00700d00f08040d854075601140410801101e40c801c1201c01c0b60400d148801849003616081116040504a4150080d501500b80300080c0082d01011503241d2410f64180e01301d40c0b10b80b25014040c0d0345803a6408000d4500340081c001007240b401c2941081d820340e8002000d940030503458800140c2c411001c09845a02100058010b10803560944140754001445403030a190494400000901401c0340e06003907030410145c0400f050500c4c0d03035034103c42a0040020300300c042800000009118000c85050140c0c8664401c0d107150040d00e00030f01c110210310720081c01481c2d0102d843e09a40c3d5110401401045000307464a4403500c959a207010148060074002003001b14210301c5041c0c50030044002e4000141d0b419401004029902480d40b0600c202c0e4080e526040d00c60f5001d6402564800e4a030328041d40101081007100300b05940800180100c0c1d100d111090032944540051000311001070040c441d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 479039334 1250 479038084 479038097
    0x3121f1403070b030c041e0e04030e120d050d0f1a120a05030304030e011806020304180603080c010c080f07020c0d05010f0c0905013209011106010e0a140601 69
    0x4400c240c600480304038848040e04075a08280e0b1a90516100e6104458a4051040c00b2806110b2205550741e480b01c0c00c0c42c00d4000c00206400d04051400740000a040102030004121030b60b141c94803941d88820f440085c1c40d050320f2022540807809403140c0e00065102c541607140001c60140090680b040c000300e002400c031f00188140b100300134401c0b0f104801c00c00b418940f003250701910005100304000c6208234480e60f51300c00491580400981400e0143e50860304018240b04103001707580e03000083c0c5044070819100958022441c7d44080020a41d642014008520000b01d60306040e00c1500401040388a5599003c0c480ea00c2c00d50910030842d0a64000c0d0050304041c031620b083d440c003002d40790341490044d00005580445012001c00701c48034652000082901d22000b000f0742d603001141100c50b42c4d58200c04c000c1c24484140c40c0c1d100c1d001c00e411902c50028000c40c911004d81d2141c40d0745580ea810b00d0048a4607541c440c0007081d01580121400c0001c5810502d8800400c5029295107000d04810385420 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 479040584 1250 479039334 479039339
    0x1140406030c030f4b020d02010305151228030e06090406230103110a021f1b020322031212020f04030f0b070c030f080915010803121f 59
    0x500540149030381501d0640302c6070070f50700384400c90750598107280d008407071041d040c0f4250081c5040c100d508803205c003003620a81007880015803140d03070b821090b05909213000240c540d54511a50011414803840f10f8021010301c1c04039142820015080c103000f00250720152165842d0649034407401c8107600020000307089120452040e040100207404030f40e40c020004540c480d100c03103a80c400c148004c010540e00c82c0300780c2c4414820396014070561610307900c445803a51812481020107581d64200f440f480ca80b00c0f500d00c4400000c00c81642c081c0c1102814192640c20700c17180064025035a82060032242e60140e0701107801c00d52045942803003002c80798851500e0692405c0a04256244100c1c0300e5840b290316002c0000c0f80100100800800140d48280780d054821403e86c00d1032001980e0052005040c80410008400880d0304254402e607420b0091802080640d1400d22a60502d40c0c04640b4800e19400d580006c140c1000100103420300d480081041e0101c1d55961080c6d40310341c0d2840090008540703000c40103 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 479041834 1250 479040584 479040593
    0xc12030601090504090501020703080f10030b060303070606120b0903040f090c020705031f050f011d18120a021606090b070f0c060504180204030203030d051f080601140406030c03 78
    0x2540d840081414100b078059500c00c045015609030329411640d9943c0010740e403040540200f601c540003035030103101c0740c03551800e03406021003404103000203048118a80700241c0c90340d40400071524419803050050004599400e80d22102c0c143c40582144c8144883c000a07120403800429542150301185ca0306a07158034005500c801820381c1c1e045407085004002c8003181c291000c009107150203110b1818070f94042c1081c082101141c00240a4441c0c40b0303000d031300410445403504c64052850107400c03a4280151920007001d242d289210086000e03e010b2284881840500e40001d00014900f0b5000d907014400c0348503803480b031016a801502d0116107001424881c5946c007902501c00588142c90042c81600c0d26125440c0f11000c0703078401000201c00240074021010b00751000c0301d22034010700d01942007908644c0003d13201d0040400701c18860b6903400c00689143c1701c808082801440d00028201c469844642c8151079410901a460981d8011121000d2609092203554100c030f8011107140d10803400c5584 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 479043084 1250 479041834 479041837
    0xf010203070c140a050a150c03090206030c370e040504050622141c0503150f0d0f060e010e1906110903030c010606080105060a050d09050f1b0a0b0c12 66
    0xc8420544a06a0b030000010000c01400e4146c50003000251800801c41290905480710903403280109410100340d800140c45400039680c00c0108010364944501d807105400e007814243d18203140c40100342d1400d007035198000740d0f08020031106079952130402ca45400305000a58400750340c020a1984000000354428000341044500400400b5020000c040f00c0c2c0c9a2981440c5810301071415600f02231488181110b144028246404031410714605510b001405241d04900003d56140541c8413014040030702d40c0c400389140b28560f403102c088500381e4a941000030040c1020461258150302e4080482c880900c0041c10b00b03074000c4030027010120807616a075503001820460a00c5010a402401709940c590340034000303451000c90050000035168074210b8020300101d010b07400203001c0d28081202340c90503640704e800c4a01813075103804017064216441c41c00c01d15000414102002c54011101c4800210b645082a8003071181c3c211161103982c5d40710345040c0381c1485440310343c00582c1c0c081e541c4501414480700 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 479044334 1250 479043084 479043113
    0xf0f030d031122050f220504020a0e01030f0b0117190f0b07170f0c0406051308030a030e12041d1b03010b0a1b051009050709021306020f010203070c 65
    0x40520f4100100a201c00c44040000061980803244044003030040741401e00300c1164446048452841d80320b00b42c0310781d0340c11811028250307006a0f02e440004c2d065480301c2c0c100c140140300700038001400d0b43e500c1c100700503d481c1505040341c2d0780c0001d50000801413492440301e4040c1a0b804003528540c200c6d03d0445451100d100e0303081380c10b00e02510b41d030f40119a4803000342d44514425160300c46081d2407903005500c0028028880354041802d030303060018111114050750b0070b075540750421665a40091080910000c1140d214140d41e00c00010303404e104590603001490452814802c03504000d042008841d8280224090880a070365120b502d0001c01400c2c02025812520a203d000c50400c00706c032441040c0e60003600600301e1000d000900a4141d40e1000008500020080709030860341000c2c0c0d1035075203c111460100311419202c0000c0404d018062200000802d89402c0031035a4003030001a103038140c0d0726485a40094000d034600c0211011040c004c40784100203d9031100c2d036032030113070b034400000a01341d0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 479045584 1250 479044334 479044361
    0x2010e0a020f10141801120603110f1305010923060d2a060e0906040b01200118140c0907080a0903050c0f06010317040302010c0b0c1603030203060f0f030d03 69
    0x1e8048034080d604140042c40003c03013150790345e071902e00360b580050f00380d11882074507681040c60040d0410214511110b64916644100c0c0c41c41180c5005a00150041140041c4031003407501d40000042c500e69a50b00540000d0802c01c0307442407090300e07402400e07910841140d085030420035000c86100005c0800c030346810149000540740120714030b8849203071510121500424040f540c4e56180a032036107400309606030b03c1030040740d0038884581c0450001b001500c070405d4500d5501044d03c04412100020740108410389506016010a901d05040140c01ca03e020441102c003801402c1c3d1100044c1001c9481901c10815916100c0c8a61111030382e22000f000381100036010003000f8051070b1000c1c501400200700014152000b407400d54114145082400e10411419560345410002000141d0f04030707048158890301b00c010008250ba55441a800610800d8603c041200c044940c0f0340400d501036020f580555402d44030034843e000c0c20f20030f20588043e072034034a550582c054641c0c0740c0d070b41d0310039000581c1e500f004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 479046834 1250 479045584 479045597
    0x6020d260714040602030403061a061206030120040504050903040f0b1c02160c05030304062007150206041e110d060f02040b04030b0f0c031303050c1501050102010e0a020f10 76
    0x1000c407400d50300a50807410050304002010024081b05000b54000c84030701c60240c408444454ac0004c20a00c1403406d40b07800c02c42000c00060050764203500c4220180060303031030000302ca1030403940f49801c1d6000d8041c50744250300c0c00c40418203d07000001681c06862840c10350f42da9080c10240c0b003102075000400780d003101c94a0148800e0162246002910400542d00c0300c03c8e40c42c000c545880e842c3c144650300010f01a0748144420040d50354040f0a034140d0709100c150308410b8144412145081ca546900300c0810848030080b01c04841d540021914445c60044034580c0c0c1d5101d00054015041d140560003422000c1c003541c5103402c070318283c8120f0320302031712400c0d002400c002062070240581e00a0307804402103480c081820010300c040f0f920700b194812100702c14036000349811200d0700c0c1c0b24003015101004144403405288e042500030000c84204901b00c0040f9480c13403d10aa44940c034007000d006441c019420078013030317600300e410004078441d20a40c0100302d4007e4405850510403c2c1940303c0c941010001e0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 479048084 1250 479046834 479046857
    0x3090a0c09020c240606090a03171306020c0a03020603091c02011b080112060903020a0813061409030a03050903010b0d1101020106050612010509280606020d2607 71
    0x203205450394010074152102580300c0d41140207881c1041140b80f00340003441041e2101042c006100c5000c0c40c1d01140032552240c80344903001c04500c5150858000501001440c81e010b1490b80300b0304040d140742160381400ca00c2641c4ca0300000c036141d030241d002d220b801469020081c4010328282003d582d01491900441d070949202c45480c0031281c0c2c0084c0002c015035503802007070158008841410044101504001d07502d940b4241c116480301d0302c02039001e0b1041e551070800f0020540300388020100560031145060300da15082136240c4010707015105400201c1e03141c0d00280100c000c01c009540c80c1d10001409464100c0140d181074800d03500041d4003ea055582d46100c12090344c030622241c24050103020442000e503c29400642103444580000b44a07040c217220142e01c210741900c00c2419201c00360750105103130f10740820500e40308540140e400e16044a00001c404102c07840e0748031400b1103d80c0d03070880b00080e00e10341040c2c848400074400405007200c0f0000280e0002c80007035040d0341140c040d10b40501c4001 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 479049334 1250 479048084 479048093
    0x90504080c150a05070e01090302060f12010b03010e070906050d091b0306090b06010203090d122a020a14060a0c1b150f021b0d021207120b0a1a0603090a 67
    0x1000204195042e110310380a11440c0c1d10144600341d40501c16080c02030405105400103840740500380701c02842000c0014000390301c05e444d14181e0308040c01e003240c03003121561155244031450b0000d0103000208001040000c603040d109034080c5085800640b1242d103084209042000900a410030540b600d8004000343c45a40052100440044d4040d440000701c03210145016410307500090046811941705100ba40381c1c9949880111340c0680c0e01c16045121051021015510084000507c1413400da0f46241c91482030394001c4148030080c800c40300810400d8a41c003903003210b4404805415040b01052000d9516503014500003400b0901440c03500403081c905040215001c2e956400802c100f02c1030192007891a50032458240803500c1c2c0c2c3c0050140b490303c4a020301c080040d0004894460003485001c2c900b551285580c288c02241d07890140c44000e6200c1e0000c1041000500d0308564411034074001940c0024148250311034124081c800913640000041002102d80014004408900445101c2000038 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 479050584 1250 479049334 479049343
    0x5180f060409020a02010e071406210c09010f03052a07020301020d020405012615120d0302131a09040c140a0305010611061b0d0b03070b04050f1801090504080c 70
    0xd00015030b0169a90a82010003820b4504c00c0c14143d6090303000c2e84d400c0c4040429920b010320701810540d07a0540f60520503002400c2d01401c0c00c00d29406180500a02a00c203000034020070031020281c891441611040200b1411520122171085860404e0f60b01d032050f0011407105078001e1203c100030b49003000e4540d000242207030b01030b82034103441c0c590001b410800c40d40c0020702c1d03044c144440018203810080c09400400346540090407c5050128031390081210340ea01d0212110500400048030014105121f0243c021340c88500d0b10401000c5602c000104500740402480d516054030000e541451440018030001d860741840b0201846066502d00140e2170a0300301810b2000c046580104107545080801380582056100c82c80740c40c0c00003005c10080d114084800b00d41443e202d501c5540d940c981e031003a0401428202c80345640750141d2100050103100e0003010f0010744500721054802c500c268020031000c50410f0f40c8084004415070010400007a2070343c0225403040c02158581c0c44e0052800e4000d041 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 479051834 1250 479050584 479050589
    0xc0a03050c15180c06030c0703050915030f1f080a020909030f070c0e011205030a2003040906050406062a230f010c08070905091003080301060c03020d0201050705180f0604 75
    0x20b40f00000c1c07076146201003040840c0319480103881092541c180043d0101140c03040a90140034488001010112502c0b5001e8540740441003800c03850b100d040504958907050025260b48080c0d0350304056622201e404011000c0440d00e18100500401c00150b0900500d604014410b000c1c0d404148030402281401000a020081c403d4401d50b00c140d041c854040350454068100911141c0180040400a080042112403a6066040c4001d00d130380e241e100c030314030000403c801d03c0b09400013040001e08920380da00b1140c1603800c1142c061081c0d607161301044440b1a108a200b03034400c3c50260031100154001e84280900500805581c100c1d00e907061103200343d1005510441c0925071042c504c2c03403600c01080c8200101e13803c0b1803800491a050018009041000a008031441055130102068081e2505504c280c011580481c005469603074486016060500c0d0810540242c041c005c55114080d2042c4643c41c403070000750703d03007501b07203007a00408401d0240450003080d0416081074848090356121000b4000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 479053084 1250 479051834 479051851
    0x1c0e0d200a170609010c05040e250905030106050303090603040b070c08040b1903050411060a021504030206060a0f031212020d1506110c0d03050f0409090506010611030c0a03050c15 79
    0xb0b8034140d21800d840c0440044c1340d21182d902d041c0034035414541c01411502220707e030300f4445425403a0341d81c58600101307401020740e16940d080c10b0a481d000b40c100040030100c5800300c008200250ba6a018141c5174400e11603c2c603803103403081000400140080c00000d81142040c03801c08a0218241d58080103603029401c03140c0c0013400400c00c062000d009600b910081441d520342030003203040503a240307408400202c80ba04d1281d40046800034256100300a0504050380c0ca40b50303c84281414200079448807001c1d02d00c14061004200701180321020801d81c0d03422030fa4008001c10301a10f118904544000750998022005d54080103000103021081c012068107001d00f5200c110201e2802d1400340683d83d11889960154010501c00700780e6a540341d01e80740c0300c241c2500b0070039a103901012a4100510840d00301986442c6401d55450900c100016a281a01c81e280c0350500c007030b000440074070380c0c0380100d41a04056610001c14080024424405088a00c0104088601418400f0388071141c4142c201c45411 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 479054334 1250 479053084 479053109
    0x507170a0908071d070e0d061a18090c030303090304060315091b1b0201020a0f0206090603091f0504200a0f08010f0f06030203150402031e1c0e0d200a 66
    0x44a0462400f640d94212181b03040180c8421030035004200351007980c8002900080d41c4d010708207109142c05800c0311460100a00c20a8060341800701e0206121040e1100e0500d44a000e03e0700c1c20303d00b000000c4a008820707080040d0b0030541351400072409041d03001e4040450101c081d070000303000040c90043d181a181d44003240070040c080c0950086c10342d154209030b00b083d05400003000340581d80104050040f1500044d40520101403400814030a01c51150701c10340010000041150008000c40e105a15010b118602100002400c05000079503c098030007a001540424690401c0f04c075051642c80c25080180840002c1d943d915500c110070f004640c810401c0340d4440c01480c189001d1441003460454100100b00411800c0d5004203654483c00d040c004020f208142c00b041c1955820481c20891144800341c00301c0c10201c502801d6166803004c1c2c6200380c0c540030600c103001d43d00d0142e07141429000c0d02070000f040d044d4040d100c01001c022015401a140c0400005104c103035107415070000040c002024030032 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 479055584 1250 479054334 479054369
    0x6070b0402012d0302030c04080d020d1704021305090c09070315080d021507030912170f0403020c040902040906060b03040b1b070206070212011a100507170a090807 72
    0x140903c449220310004500400f08001c2c0040d22040c2c05405000d45850011303140d940f81d01180309070b442590000b5075035106102004154a500142c40c90701d0440981c0c0d02c0801c441000304100c0103500c241c0d4000e512141c031f10701d0095401b802e036002642c454108011180d240c500c8402098102c1010344041c00003d8858100300d00781d04000c1c011400a000c1107006060001513550000c1d100d60b8468098100701701846c0104180038400d4000310b0b5510b070401c0d000b94001c0311951020b0074280c00003120048901360040024808068007240d2441503416401034030962179104200402804141030480c4e10030356400d40280031072018458280500440690f8644e070f814141440138040d1002000c003802c68030118412010f0305288025585001da0546820751203202c18030014013040301d0b07404806801c3d882c0c610040c4420358850078140c030021050340c0c0700c401c02d244003e049901748610880502001d40182a48100394500e0008203034080b403903e09058160340b00c00400d410b068107907002c58103007003980680 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 479056834 1250 479055584 479055587
    0x510090902420304020607031b060e030a11150c0a0c0c0f05120a0f020f0d08032401020705061b010219030515120d0c0510020705010e01060b040501090b0f0906070b040201 75
    0x1645050710b1000a5401e61400b80d00150580c80b6040d0700500b0800b04450501000c580841c603104910b40c409024003164444440250b541e40104d989600054400c00a1202c03140010510340c2c946a00c120401c8610f40ea042080301495021100b4041040003080100c80400c480b03c90000240203458250202649010104115462118905c0010b900004001f2000848181c0740c81c907032541c140c40c0741c240040c800c00003414842d045900642010400003c1100c2e00d1039116040e03254490030354600802d44c040ea401207035039090170b020b0560042000c00c00d4040d22001c50b1501c0810848140015250101072944409809201500000443d481e20107029407140258004031804d00281e940d00c03110081296040d946100d042500b40078800040c0468090210a014080a146c40b04c0b105550b01c0080d071500600a0032110070010b119440d107034001c54a030500d44221001c482c0169500c2840701d041c00140e1906034050480e0b07101b002c208011f02c210340d0302c501c030240072041e000380012512850315000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 479058084 1250 479056834 479056939
    0xd0b0405010e010e0117150901090b07030c09050904110409030203071707020f0103050a0905011802130b0306070f0c0204060b1209010902010516060e16180510090902 73
    0x801c075824201005103c0e02c1040c004c0d00e4111900407000f07913110785c907481080c1c0c2851030f00d0f0384084000e0150001c100d100c02054200200d424410040081d40d503403845022412500c1140455000850810b000c20140ca444170080380c202d070040b0540822070014200040485211410807000358001041c07403400d00016420341e081c40070305440b035a850010686d00040d254144400418141641d800c00f14503115a5079209642d400d60000c0200254034420201c0701500c0c1c044030080780304085444902d400d021450003940350310300c0090700070300054030342c0781054410350f00391000c0e2010842c1900c16a4050303a1140200401040c4142c01701c2e9039082ea400800210400060035030200381c2c10400300c100141d078040102e0f040750443c1c0e070103007440440f14030344003014000d0100b0321501c2e880340c103c0b07442c2d00200c0d10422404541141010b102d42c03004500c10181644e4044481e290f60b600d4500c02049080d150340c00c01e000c80f501c02080300d40382e5101030307001080b01030101d0301e010903040d9400c1e088002d1880400 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 479059334 1250 479058084 479058089
    0x60915032d070b0901091802091806130213030807030c0b0f06011403040f14011404050d030e0a0308062b060b191406070f15090b01211101050f0d0b040501 68
    0x1c0d1a403a00d42070000192550286200d00e2916182e0b0581900100c100c48e81940c40c5071200518041e00000007500e10b6a034400103490092007031103216095140c00601d8400c50b40d4900c3e450140c660300f14550340707516186411170882a81800340d000b0304040000e0311241c0300c0748a600c0c2c0c01c80303950050800400051860b01d0000c0e224103425810014040411403071040c1300d018aa0150420340c00004816142e409800181c00300c040b041c0380349083c03204014001c500611344040c555010040c2540701c14085a0760b00300100e024020230090408078400741424022240c800401d281107521b030110280c0c0110001850300d00c19031301ea50341d9048404207440d20221324040c5144070380714220950304114207140100d83c0010024404c000004080c0300300074884040c0c1c000d4503003081207054808207030b200140143c10441710071181001240000306a621500100c0c2c2c180e800a0b0407501c0208a0a54420300031558141e80e0038140201406186003800301c90006110052011a000c0f076880c01d001c0500050f82d9042c1c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 479060584 1250 479059334 479059349
    0x9090516090c0801232e080f0a150303080c070c080f070f05061819240f17090f070902130e07020c010807120204090504030206060306060915032d07 65
    0x185901d41040403503809210f6885c404440503c90f101d05040b82c420707125100710650344003008000f1640e0a164015504a2098129446d002c1e0b15983c0c3d010041e086503241400111003c1e003020081c804039101b031141a0380f000f1403520b00307481c2c6010f41e1074124402c50350f6030040d803040e0707c42605100208824050000103207040c5405250080c20500040c9090248016101110709a80c1038900183e40d81c0391480b4a042e00c402c56280c6058484803108401000d02c40f03402010050701c006500600c4c840c500e428011030350755070341c0c1004c02003c61006800304809081c8040c140f160100c01154114184958401410719500050740c40029004c801d0242d2160362203500030315075450412105680100f038104a12100b444c04850307030b0f929800141c9100d601d01030703014401e910104011480829561107070703000b0b40c007076000c66070036903900410940d842100f10f079481e070010481000314a582c1203003014002d906000600717a8003400e403030390240c00007024410034106c940c201c5548000c000c50070512070440070389100b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 479061834 1250 479060584 479060609
    0x501051003050f06060706060f082b020706080612010509100b0102070b0d0c050c0607020307110f0f04020c0106051c0c0501020d02061f030f050705012709090516090c0801 75
    0x14080d43c0749840e000400890007840d0008090041140d154000c0300501203d02d03d40c0380440d03c3d84181d0760350b947c0410f08041940680b0f035011034040ea200c50140c11a22042d40101142c0e4240340c2c046400010281800343c1040d0340015504c0348103004c0c000e0a1180400c28010722102d8400e01d0103400740c0e040d00d0310303441c159000a01d0610013400c002e002c4490016420b040440c28084440d01210244913118500322039004040c00c0c000c4180e404070050030001c1c050381c10000c10980c44001c02402c54520001140e00c0041c86102000b0307410550054124401c00d880002546a681c4011641401403c40d0b80c0499080d10310819040100f11282d070300180c8001c0c401070000501c100c0c0301130f5540e20042c01240146542c10200600303409031a194001440d400180070380008041d2402a41d14011800781501090107c4215200e00c8207201c2090b807464130700300c1d208001503d050200d4000701501c140a90b00c40c0180700030180b481c20800d154000420000e00001036568030803134001c0c6029410b8206210840c80d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 479063084 1250 479061834 479061841
    0xf0109022812020d02100c032a0609060608010c17070c03050f0306030a2907030b010207050904060f021201060905010c0b010e33030c040c02120f04050310050105100305 74
    0x9040850341e00b92000c44100240380301e800c2c0001051001002002540112101d400c0c8070515444140641d02d184aa06c480b00044605006152419003644869800e44500d08500c8003042450b04484251f60007400c0000e40c080e00c5010036405c0d1055080b0100110ba09000c2000391481107103016540322409107002c0d20b42c4801a41c000300300344110300050407403290120120350b6a640030300c014880d1950105d11394840f09101004100488000384c884455120550300045d4a18042d000704400410305901400003542003804019602c0340240040d100680d03103c032100040101403000b04a4000ca00c41d66010561500f417004003800d425420050400444005000018108002c110f040d10000002110b1594541d4984010900c00c080c00c0002054650620742c0302034800301c0350009801040d0309489900c0e40c0c540901056941a950501c010303400340031501e05c20826070028080c41107880f6542c078505076413800000e1030009007038a0000c080d5034a0340100a140b9101401c4200000c00342401c0c0880e02c0d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 479064334 1250 479063084 479063149
    0x120215090a1e050a09050f060102060402031e01110703090f0639050d0519090f0611030f0a030b010f0e100305070c020402041725090209060c0f010902 66
    0x41a10880b0b40001540108803840385020300300c0005408040c140203882c90742c0e0302d152030107890b083d00d0076081c200310b15020900039440410341d148140c0e0090020921144454414050b0a001c00001c2885559078030035200201070000050090074040e030f541504403070500d1109854134050b58450001d000003041040400521012081c140c0081c05940d680a1307080d0444458000d03050f241c00800a00448010b48103d90304403001d40514022040080c0d800c2560400542da80c0c0d45a010b244a41e4110250410006204451100240c0a00d109990901030101904012504159020b20200ea12404a40038130f5034403a9026808030141c0c0b0388000030080000c0807490650400381003004045c0c86400113081503000b0548100c41940c0941304541e00c80c0d940c2ca1000402d2181d0010758280d0050010919200041c0c0100502010f8240c1d4403101c002e10300b422001c02903010b400e4041c0c0016003030008000d0b0302001d005680b200e5503904008500d1074614410005001c0148201a006460160420b02201d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 479065584 1250 479064334 479064349
    0x70e01060c030333170c0f0a0e0a02030a0c140703080406060b0c03130b0a02070e040f0b0c090307050406060f0c0f020d081902060105010c1203060f12021509 69
    0x5400c6810041d40204050070210064015440c0c4803052125200501c0211014420000803540058140c044416190f805c1800c4880c1200c0941d800c0d9400000d012100d4507107240c0e02406075100070562280d0315901c4842c1d40220030100c03030184007181d01100300410510b150041e10448a040d26001c92038420701602c1a10341c1c081d41c8009810000010001070802c00c0551192006e0182d00001c107496100610340c25507254081c110800800411aa0019900c92448180c0c0d5480c03010760081c5c441c7c0c6052400d4462884030061003981e00044111007080402c02d0f030000107006d0315030200415a550320810516103400035941c0144c1c069841c1003c100001c5601c12124030028990f0324000e13440003254140035254649400b00a980078070198450004c11010b02c1c010300819201e000718020801c1580c0059071120000d200b414081805d1050510000b24001c0400c0c07417800c03c6003000210262114040100315a0f80d42160003904200781040303082d4641407950402c0c1090809100746040068004a00007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 479066834 1250 479065584 479065589
    0x306181c20101a0103140f13080f0706060915180b0d0203010c09081002120703020a0c050607030b18090c010302090a1e0306050c070b010506090a170304030c08070e01 73
    0x1002201d416110661818084200c0702e0389280300600501803101e40c502544040703e00d10b6400b2030325021110110701c41154007a4818049802c2c01e4405a0720320101d860020b2214400300c0d0401c00030403410383c00c0c540240c05000c40e21b000300c00024025081c00b0040044416854403080d4240000400700240781d1a10710b108640710300c0850110361281110003060110203040d500035403650034245140203469201d014002111180000c5443c0c045905171804100c0c46a140c034000c050369200000380984e1b00980051548904510b00300041401d5901c40504050094580100007611510000583e00d048000d08410080e400f2079101c0c40d0400148007955a10300e400000c0c149600802d2050081c1e581301c1162001f02503601002b0419003051450440300001070000701c40303103450b01020409440d041e86c01d071074441350311003680546e0f64200010840d25400500301c0c140c0c0206d44044c01718803051501000d5014010103401507031140c0c21480d01040c185420742080c00305512541e0104581381c5c072000d0b610b04 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 479068084 1250 479066834 479066867
    0x80a05180a0213061d07090e0417070c03082d0c10180206070b071d09071404080d050423030a1e120804030f030c02030405010e0409020306181c 63
    0x100042071541280984960340c8041c501944010300205c202c03510940540c4141900e50300d02401c99121500384042c418180c0c2d01030400015400d41034403185500000704203640c068800302c854150740341e4881d0701d50740c00300b2030440d4074052621180d80d280420b08002030858a21b401c22504001000c07501c10b580d01452504410b1581d00c403000005280502944010896000b6100c25581c030b2450403c0300180000742c1320540010400c1c1d204240d4208401c40004071001c000f000480d07241c0301c0e01c20407641140001e0000b10800c104020000c1c0c04d4408001220a400c0103440d2291500c2c9005500414035240a05001c610441d1f103440e000950780c08106028120b60098020724010402c0e865086840c081d0a00142400358400c004220240c101c400c0c036101d01c0c403d680d03680c48100107203002c9007036031a44038404015034014403061280d0360088180b503580c40409000005c603402241c00091030000b003520300c80c075080030060401070007240502050825400d503c20081040e2003a41008001d00c907410300c4681e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 479069334 1250 479068084 479068099
    0xb010e0613081e06070905090406020a020c03030a020c03100e0705010c06111308100c050a120b0310050f150a0e2a030108070801060515070f12080a05180a02 69
    0x301e0028031032160790142040b03008450f028000c40810755402100e8412004503031040400203504030303100d8a0100103540019000803440e451b503a54140183d0002c40c00001513000da0718030388071a41c5040001c2c00c07200c2c481d5802000b00c031200100385424001c0700807014080c00d01700b0503014010440024401c044030030a2130071701c501207a2410420020411315484142c01600090411001c0740c901000c2d82c2581d45540036502c2c2d40521004040407252180c84001c0407420a0150b0120311340a040c03203a111024112002c50607014240000b400d043e5800c841e0b000704c170303580c09c2401042180c8040a0340e20000c01c5103203400082010000a14405092045403407501e4640001940040b1017601c0780c1c0c0e4150890000d003180d08010ba20a44190024040e80d511407250600c001a48401401413508a0303401034149000902525200b0541d40e0160ba02541e5000600700050000f40e1791445c2c00303000d01c5680d99400c285041078400034003601c20107484a90112804410b080000201245d0728100950458110 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 479070584 1250 479069334 479069347
    0x91103040203300409050a0605010c051507050d0204150207050a300203010e0d2c06070204020f040803031009020a05180a051503040b07020133120f0c08010b010e06 72
    0x304514440c058450203d240007160009145070260003040c0030f40ba620b8014040d15448800464981c50710000141c550b60068400c07500c1c140040c40b010f0303003084151a2440c0303040b1021202d002030364082c2e80902039a41011a0342d80000390705101c150050281194850f401525240c000080b181044500c40350300c0810085e4003a4140146042008440d40607000740310340e20802c480c460315250407030540c0020985000703814000b04016180b0100040e40c54042000001004092051540002108a0300554200180e01c0c0a04003a0b0140001341b940000a41d03903803501289409a00140c0e5100b01101801401020034241d003150a661071000200c038185506822580040d01404003a44242c1e0800b0540c900764046d141604011403150b8011038407440a501c807042d00702c1c22030f000750700d981b4148115584210311480c5900307a86c541c07800710300b04100b80381a10f4100030603985080d400100c81905c2d01b0343c00350342001440d10740ea00c018000c0c01c0003044505400d0001130701c4803151002140c4280350000d0030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 479071834 1250 479070584 479070643
    0x60f1103042105011401050607080d0212091b0d15090c09060602070e0f010621061e17120409020a0311030703060e180d0503091e07091103040203 64
    0x555004085207041904030a0740a0359102051203102c1042d6a00d500700013500a04084040f8283e0403100003401c068035103503207512441c11681040328003040198081040c801001000d4800c1801603012001800c9000510342d00e500d030360740d8010660b90241940d1f45024000c6004c0c1c0d406000c008902c070401281455803460100c2c42c1d030b8904c1c1c011408041c608a804190980d00242c0c3c0400c0d80e102444494044d02e4440c021a000c5400340f1804001442ca101d00007000705900800c1c04401c04000307008a038040c1c44011034103a0f800c122000e00780202d00c04008018046400614600f08040c1e040036184078043c0c04442d4119110714080c5640042d00021101d80e0544664040c480002034221a03540b44d01700254001c02903e420b20900c0d00a0042d1b00200d20904c0c00b000c003103122052030400409203039240704020340385c2d03030030042a01d81c09005901c01c5501115000c100c005051204c50040d102c42801c141485040300c038001c080c0c800c0c2020902c03c01c80140c80010b000401661211485054102c09030305 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 479073084 1250 479071834 479071837
    0x15011209240606090807030206030a2007121b0b040209060117010b0403110114090d060e0319031503050a0209150604080c0315130209060f10020604020a050109060f1103 74
    0x948181e10201c031000d00004005070300c80b0003640c50640c2c50071480d03a540c103001540c40707582e40000b95200e130701000400c11240413640111128001c12050000c000340803c6a03c110b070300a564192038121303c2c00d00510105900840c18009202d0000101200ca0307050b0f1154184154001c000a000d81c03524004a50b0f02e0303020301181e20f454410f005d605042580c4800a061300340c0c10500c0100e408281d5845086038030b41c002c034030561354500c5a035442d0b8100360301d0300701304445c0c1345400134140c48103559040a40355524040c8004c00125003900c045004100714490003c040302c00303020215400c03031081c4409000244003c03c8141c5400d80446d6290700c4c42c2c440c940785004485406881c43d502240000d0b0004282e440810b00e00c0b40c8910403426918a601e000d48010f103401401c80300c2004100080320079000501d40503910a401610150010016060301400700360804540e4840c0747c0564454400c00c0f003140b43c11425440a088203203007031181c0601c0c000c001340c02c0c0c492505100041c01204008070004000800 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 479074334 1250 479073084 479073113
    0x150c060b030304030606030c090e060a111201060804140303130f020604080a0308090105010e10060f0c0602030106121a0d082b1d07180e15010306050f15011209 70
    0xc05603a500c903505d01e0302000800c800c1c40112621082c0e080300080a45441c0701c3d00a48208880c094030041d95206130307001c0242040183d80d03024120a0003101410002c00314424081c04213078031000c906042030304010340c0500b450022803c281c0d10410420503001c5c8651744481606034040360f00c0041004a00c001071a60049030810716541c82603800880c1450b034807415160041002000800c000d9072906110103403080304030782c2a4500c201c284003c00a044c440c040e0400c400e4460715000151b0b20745513071604140c1e8820307070007000000e01000a04a0300c40d190320a0381c3c1d162054001c40c183d00f010140c0495840e280380e00b00602429008a202ca103004a64900d0411204850f4102c0b00c082d0791103410070005081c10040d00320411204c600800034614005880c00a4418200c00301500c403c107181041c001d0100440c0d118482d0007060040e02c5400c88c0c102c0c0c1c95000e1071041e480412286010b0100000c50b0034014107140741250580c00030650f990f000341c0d4011083d040c41001003005006414481d00401884 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 479075584 1250 479074334 479074339
    0x103111e0312090d0812010302100201050609010e0c3603030c0604020103020714060a0504031e02101a090a060806070f0c060c03020403050d08040308060604030218090a02030a0804060e010504150c060b 88
    0x81c90030321602c101001d00d41230700d108032015508a210350204034200d034000c44000f030300400fa00b4010b01046841224083e480400f0107044c510300701c4913a018011a0315010020340103181c1c0351501d444000030249000750500000e400841c20300d01440110341e40c070b0174003070406414143c0c0000e034201400300c0c070340c203011030700c03055038120380d402d080c4826082c00400c030855081d800110003405c2100e040f40c034542c03800c520741d80d00d85c01040902c1c51243c0d554010b010202030546120078420900e1070340e07142c010100d407160441c440005503942c6080d0202e0700306a00180003c0400a030350b66107075949600031281d818103d070070850004a8111006061f4028455608040e00c05d10920941c4940070b82d00030b250b24400d52082d81d4090190300c40c1818080d490050b400000d40c00001001c9000c403520100e80c550380d000d49084110340b01c01105401103414100000006e44803001c1c0018148056500300c41202500402880c01515207841c0ca24591a00e00780c4504030b004100c54403088c0000d01c01c940d00564030140d0700 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 479076834 1250 479075584 479075587
    0x60a1208093007060e0d0809040b06090424080f0304061413030b040c17100f090b0c040305160b0f031e0109020d1b0203030103020d050a08030103111e0312090d08 71
    0x8a000c1c0c159540410f10030240044d510b032a0f225451708150742920101b0383c1c02210a810113880c0020080500140c2070f00e1608584288040201aa21401a482858007580290503001c0c03002141d90030450098000e100e0035405203803480070100f000000c503000c5406501d0040c1c01a00e9010001100e03200c1c0c8100e5090781e409000020003030254000445014034410100400d40031b1f903400b9002c106460a808800d40e6400c601c00c040c9000100c0c0d0000b60f81000540d5000481c2c007403c0d515075402d00800d4800429039030002c9420b000b004010011202081c2c28070040700726151910008580d02d114035044135000540100100d00c1e801041212000000e40703a00d260200340d0384844142000790000e074a032100031340c10001d203000c280c111010361038123070240f82c0c0c042c604c0d5030700b140c003800380c0d40c01070718000c80d4544541c402d000e000c210810090f601031445824041e502c04050780c2000b00007021000380d494500d090108814240e500001d1203501c8070130018009440e1a50b506c00030303c0c0300a0800c0081d120000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 479078084 1250 479076834 479076919
    0x1e030d05070e0415060203031305011103070c02130b0303040b1b01060303110d0306030c030f02030708120a030c11060708070302070203010f0c080f10030809041e05060a120809 77
    0x8012007000107a40b0b080d01d0410195070050200441507101d17128090144e00100701240010460042543c400c1e405103001154802170781d8007105050340125142000941e2403800c0070214544044d10384104500c4140c00d10585c0c128000103a2a84100d115080710700c42d00003040c450b1901c03680706000340003070006c00800c500e40e80c80c1006403c41c020542d04d10b140d80180c1851644881c020b10a100c1034035000305160039241c3c00e545e503c2c000d8081130081613a26100d00200018010405c010302e0040c0c5400301070042e202c6881072005020340e12003483c1c0000740460589c109403103a20024509501502c607103050303030b01c60b110030708150020f2265030000b9405500f84021501840c3c0b1035080340800072030366070b41c020b0741d613075450701480816000b51100004044012020004103080d40d000d080400002080064030030b06000081c1c0c03100718442c46209015840d50100185460080f06034001017008078441c2c01041125514011280f140102f01482118025514842401c800084030031210058604644104 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 479079334 1250 479078084 479078087
    0x503060f011119030212040e060d02040908070f0215091f090b0f04081e030a1202040b041517090a0204200a09090b18062205070507060b0a081e030d0507 67
    0x403e0b040d00940b14182c481181640f41d40110703801c9921a007a000081c0e100c1d0801c110400c1c49050041c0e034880e40b100b0694007c22603510003480750921800c001c40c030b91070710f600c1444002e80d035902d00000c012400344100d580a456110402141c08925814010b0804203001d040d2620404c1e030700800c41c00b11020441c40f1403007030711000030700c26618540111007100c030160200c80e6510f031159018449682051000c01c00503801078007410040e0802903c0542040c1c2c41d05510510758115a01c0640d00311070030290030810302e80100c2c044440048820466071341d4034100040543d030781d8600500034041c07991000b007120704440c4060143e9072030110082c203580d1290744c6180100052554010358107030f1898034400c0030491502c003840c01d80f205070f508600043c55441d54108040782890606010090303412507080b59200100d8810188190800d40340c0c2602e906041c1010b008690801001a00490013400306020700a00015902e032080100180c1c0c42da18140449021b0441c00349a2001489500780024013a01c81d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 479080584 1250 479079334 479079373
    0xe0310020a0c03091703041e0513060311040908090f0f0621150d0803070c0c0803250f110117100e0a0207110105030c0c03120a050907060503060f0111 66
    0x89001e961344003240c0d601c4040003161050302c045100d14507130003000100040118002643c450341d8071018910421503807000815800882960160740c2c040ea01d280600030411030580212802c1d0301a10100080049aa1150341610520400c0c03485154440b00010b41a524081c02031324000d40038200c0d6441e141080c0c050000c01e19000d81a400c10903211001034007030b41c02600100c2030803d00808401800c40705840c3e1000c1ca42c40940341c203081001c030f900e1850128040c000e40000070074030710005650300c8980301c80c0020b848404c405403501001d07440f8020303404910155400b2500f80d402994080c0260391313020060b9a102c1061521900340c1005908200501d280e04000c2e8085403c2d0040314455540c501d07020804074800c0344001060312014001800709544500091544208503098051a15160000c141d28681041c0c400040700720303080080203c041040c0c02982c1e006880c0000901d03005040990262040c04020304a80c01180041c40010082c0e00c65207040c2c00c1510703690151010026694000e4902 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 479081834 1250 479080584 479080607
    0x240d14010e0121030f2d0305010f050109170102070c03110a0506190804020121020306030c01031806050402010e0607030e09070f02070e06030f0607020d031107080a0e0310020a 77
    0x207807540400065909640b00740e0092604122560303031168403241e602540c0d24034280180c4c0003081070b00381c4011a45046001003000c0040001c84000101d00c1004000b026207405800c03512090403410300400150b6080440d03001070301d00000c604480e809242100c6030090051690160040040030000418058420b980c0c99040d00e0590740440c1c030b95128000d00c00c50380700e022114482240c3d070841c2c40ca8214401c2c0039003030700035105240000311141600c010001c4040d000c8400290560300000340001c9117070400903188030300c4003824180000c2c1c00309501604202406c130750141856440d400002c0841e88151022110b030440107081c0c5441c0d00c5130b03040007004546003002c40749c003d822120225007414090030004d01902c2c1b40341d00401c6000d04003500030480a5001d00019054480d4505000c2039000501840780302d45ca5560041c0248d04184000606070b40d10a000c8981000040100d900815004001c807203004d102030034200202015240424a050703400151550703018408103c0d2909681d01c4510341c2c84 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 479083084 1250 479081834 479081849
    0xe0a080c100b010504140f090a0c020106051c150e030711031e0601170307060c0f0f1d010507030203070501090b1506090d06183e240d1401 61
    0x580c0c0000c0760001101e101d2208a40451000d010802110110035404480e8030400344c00e01701c2c0e0803298004105400e00c1030b203001805949814030014030560901c1400000c0c982126070181d10700d503016030016844c46000000c0c010900c003641051080d03050750001c4510041030400c40380c2e10102c0b030618001005100e030401d032003402124481c042041c180744c0108505541071000d811aa40303041800c01d81400700e00d03030280b22400103100c0200030800301e108190070b00c0801d03166562135298070340000b0624420030000005011036405403111040100d9482c95400c1c84c02c0c2040380da6a1114241640f035400b07040700003442c0f0342c24078941c0c20801190200d01401840324444540790b2a0021003006a9801128100381e003040e032001c0c031503010401c01c4d00900c1ca00034521005d6003c01d0180d803070b1045540b154034810003e0078448190900291460000521020780e40c1da1900c550780e07103010009800f0701c9840d01d800e5915a841d06402122a960021564403410101d000c01c074903035680d2030b1902e040009208910 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 479084334 1250 479083084 479083093
    0xf030d0f0b09100b0913020f090a0e09030915040905070914060f03060d020d080c1b01050c150604150602010e0c01080103030807180b040605071b0f06030f0e0a080c 72
    0x1402030511022007805900d18010032071945080c8013080c101c5400480c040d66104004400d080d000505520042050101000c1003039551900301060280141d0240c0c42545117403008801c20906000210554403902c0085510b52051082c0340301085c0e05010307503041501c02d0343c41c10701481a8190020801d01c202d4200710030880006100b80d041040d18040c070010f03420140c1d02040056220f1501c01a440f03019840141450900c140d05c0c5c8440e20160000d840d034110701d40c09900d4030050039440b201c0307064022209180161500c081c0c01d00c0203403584920202000500a40c4002c070310180c1da2604101062150f05540a81c840e99901000b80a40342c0030350b03034100b2400b0f6441c0a1205500c0b0f09032060603a5015100c10142d5141d040044542c51001c0300702c03000540c40e000c40820071014410052004150541d40c1d2074545031281800e40c2101a000111681a14400b0080140c0c042c0840309200301c0d8600d040c00035080003040d0a48014002c41070900110b4080d800d0580c08011001e4007900030101c0310700484 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 479085584 1250 479084334 479084351
    0x609020a08043e210d090b04030c092a03240b19030e0604060c080a0903020705120705030a030f09060e0a090b010216090204090c080f04030305090f030d0f 68
    0x21038404040d10707070008440b801d0740c4400c06001c000301071040d00b10101418000f034500f500b0305408100c86813001c03507132041d8000840c2060010b900050380e00251040c40021481c152440d03454202c41d02c614802c06841644852036a44000c0340c0052403034984403c01c020008810508038010300038090403410000302c0b480044211100000700d12b80f6020b9421080c009844c00030803407031002d21034801f0b0f01540304154a649402041400522284d07000301d111f190301240f5020954805082c000c00107100c00c4030180b031b200016011980c00551001103c07030507110040c140400c40c0045050044941000e501407140c100100101580300300c1110b007803501962080300e200e443d40d4080b2030100030010070561003282094144141e1010741d000c0c202860050044541c00080400084c601040c3d951005807142c0d4007103400c004800003400b5070700c032100107490450728615241041411100010304090308042d52000002e0102e002007000c0c3c95544c05c200c003120340f1881580d11503405042c0c1c10340c070300c07041e5800c0c010007 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 479086834 1250 479085584 479085623
    0x15060509030604030e0a0902040b09150c1213091a09060306040c031b0816080c010302120c0310030b1807090504030509010c0302100603150b0f060712030609020a0804 73
    0x40d102500401070141140743c40b980c5048a1404143d00700d40c0c2d0050001c0c00001e607080442c0f00400003071484220710768644140c0420404058084010200c000074200300800880c440807510001464850400f2900c601004426803011101a0040000c0070b00d00019000c1845050740081503e0600300c644e00c00c941c1d02e4034285511780d0380c1500d005080104000c0309100142060550300c0390b91200e04c10036007505980e0a4880c1c0703011261500c03030034054038901c0c0c2403101100901c03001003809030a003800d61410300e59a1103070302d504000400107081f060002c0081403072003501c070000384000c6411846c00760407170805d4602c3d056404001d001c0e911007403040c90000100240213008240c812030300342c2c40e040e0400d03034000015141840c03140c01c1181180698080b40c0e2004480744036900c0554001c4038009018400914400101c44440e421188140c1440c1c0084c17010741d45540469110542c4005a5440d0f5101c428040d409450340743c0162700301174000710b9850f0380103074006602841039014402400440602184 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 479088084 1250 479086834 479086837
    0x506040c110a08030402010302190f090801050106230c01060e0f13080921071202090f060303030c130b03040b040605100305100c09030c091b1b020d020103140a150605 73
    0x612a10030b0700302c1c90603800402d203414040c580c400e0040c1409480c2c200202c20a071030f0f0720400c01c0b00d040442e1901d000c0501182e84940800301508040c402004903505241015104451280c00c002d40d031040b0900300100701c0d000e6016281094102002404003e4440d400d000c20310700c0c01c481640342045d0810018031404600403000b61041d8002c91442d01c0c0640880c10300c0a61740e5201c2e405000c044e045282e10002d12003c02202c8010403080c5481d441205c041d02c100104480e0140090615511010034041290b40100849402c060103030040c0e41e94440355286500b0010303065110080c070100200c100000d024458981a100c0ca2003a0000c100d00c1ea41d00c11104a48109070201401a40c00070079201d010701529440081100c12509104111036500e50383e6020401445d00645c0c4810303100c902409849414400110305d520f004d0030301b0311045c8140303041c0d880070841941c0b000c5d11071082c8510400035039001b9886420000008502c1d28076524296070000050700441000d0302a61059071000142d46100c0c80 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 479089334 1250 479088084 479088107
    0x1306030c140103090209092107210221090a120f03080606090603150102060105010212070f0303020f07050106030312090b0a020310120312050c0903031902030405060d0506040c 77
    0x51164036494104603600d0000308607040624140341d503580c2060003580e2801d040034030a6103102c00402c1d448030b4203c1c1c2c18207103510303d442104a008040c02000001103c1c590b0701c407540e20981d81c0101031b2080b44542207241504641035aa00402851811007504010000a110085003502d10400c0166100d40c0000b881d080000701909800c414070b9040d0000781b0404203d5080ac034001c03d0305091180c04c1c2e00258aa40c0300341d9a5401101503a0754401030f43d40c05002c214010a002d0000e0400c00301e800000c20300034451040000e007840742c05d8000340304060103941500c00400d410181213485402d40c0ca030050003440207001c20341c041072050081540c40c20042c000c0e196020b40c00780050300aa264405140065000985002030071f1104020204500c60961a00442507000c1ea450035408010141c0e86012600f001e403111211500c10080440d483d2000001c69001c0c0301c1d0388541c0b5aa10b0a69801241940955000141d1000c030003c2e000c0c1d254513090300b0250280308211000c01c0303001d03c0350300305030341c5241c40d030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 479090584 1250 479089334 479089343
    0x609070e0d02310506100c030302070c0306090b0a05160c0305071703070804140102070305030402061b120a03110a1e09030b01030807031d03210c01050108010b130603 73
    0x400c195455400d2040e2814070705072002e810710015410300388050038030340140c460841c101d0b58840109280b403050760140d20781000042e01d031320050a420f10301c01441100c0c00c00700039081c10f80004c2c840c81001051441c0f000110380003502040807201900d01500c4122055035440d00050900c03012851440100310010501e46c000c0c2c03511a002c140540d0180d4181d00094030035120308480c904c019401c0042c04004600c07801c4942e0b1a5601031900340351420701034040f903a07801c1d03450380306100c403100181d0030000322a04203404865164484080950402894400241e4103ca0307000d2880240646031200018010640140d1402d202c1c6114219040322580201154403002507080083c21140001d0310788412a240100d150404200c0c7d100d07101d00f80c02d02c800380c0c0100c4100f000041c6540034141d0004c130003004030740310180940f414600c820000703a403003c2441b400144c515420000c100456161001c440708201c1c3c40000780455a507d0394600d000705a0501d071a0301a07444100e0f560b40780d1519101d01c40030b99900 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 479091834 1250 479090584 479090597
    0x6030a0c080f1015090b0a030e070602030306030c01031a030a050f0c09150120010c091d0f01050609060d05040b1b0a080a05100915050a090b0f090c0f0c0d08060907 72
    0xb41400100d036413040d004d516082c481094408541c45001d070006114201d0300d40c60208602100111641c50712000d6400301c821900244103200e026a808501015110024a03000c80d9040c00426101e408401e0800302e69030500c1840b809004000c0046401000d4900801c00d6505000d000c105000041c5401c0304d21480c01c070040180350215602512000f01500043c07481110200076000c081400c4a00840750500403030342504040011040460900c1110388810078102100d041540043d14403100c1801442c3c030404010170f40460b0b40c0c54003020380c0c0b55032181a505000c90b0030541003421250a0a8810384001d4040e51844038111009008859035400c44d03903a5140c09551b04a90300d401004041c286241c987c000d5040003034508528060219001207c6599a1000345488100018440594411074011b400c1070803642a984d10b1880710302e1030050965100701259035454010f00c4034400e140e607000040c03030046600100300c035000031045000c80d22525200701e16240d107000c10000820485580c07001501 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 479093084 1250 479091834 479091839
    0xb0a080c091e1f08180c0910180c020a060e1c1106060402031e04050c0d120905030c0303070201110a0b0412020d021f09020111030a0f030b040e120f0906030a0c080f10 73
    0xc4a0840c0c8112845c00f06680c503a155103030026112910035030b0144d031110b000510600c912003402e48010440080350800f080780700c103445006520307480240005410702d6070300c08140d00124810b1144450791603040f0f40000c00403d4465018103c90800e003180700061013100001035050900d4400c80b4000d18000306800e0303c49440b0b800e80d66044030003c00c200c5441c0600728891070700b40c0303500051500311403050810b1103da02c1c2d036890061050725203600c031521a5202000c41c16440c0c5001c0100c809041e020302c2c24601b081c089086040c94003031982c000030040c15501d01040180090400560311314503065081d41c0741c5862505d0704903612042d551554180c010a0181b159400c0e0315a4800c0010510606001c0c0d4a2040130340c0032401c642280d90044003043d11810400b030341c5641032048181c0c41200301d80412403c42c032a90b0640d82e903101402c0d4490b00740000154482500054802d80304070742d200900b5203a03a40342124414014002444040022500080c0440e29009418000522410341c4d1042d0f90040c0d41f = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 479094334 1250 479093084 479093101
    0x6050a031803020a1e0b010603020c0c010201090b070c1106070302070315050601052a0105040309090c02120f090a080304090b0915180a02070203100c180b0a080c091e1f08 75
    0x40560805c82076840e10380007040000345000310b0180200070b01e440050b00c44d40c440010504164842e0740190442e49002d41540000380c1140300d5640180c00e5183c007840300c105c1480c1100c00700d038900c0611036000002141542c1051780c0020410292445800c0341612030341480c1c035243c2640d41c00e0750103d021540c28841c409103400c000794211548880b01c0a04004162503285641c2140c109680950016500c0380c0c0a01240a06000ea01001605403009000602c02d1507074030400c60045243c100b2921900254064444e07072100003031006440000c050b02d503181d580d43d02c0d00000b08000007009000c4c05640000031201c0c0001100c1d1351000d800500f0700310203000d00714150501660700400d0101c4895080c4003403c00f584082255a001c900c0603040042c01d0100320b42c028108013080302e0202d052075000c81d01030015400f02e4060300c0100322942810b05568130340c0c00741c000d0320717000750200c2075004803c01e0140840c0c054003118050940c40c05941200112541c0e2070132030b002c140c050840b0f00c0885c0d03080000c201e01c41c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 479095584 1250 479094334 479094353
    0x90a0e040204060e19150302041a04050c09060f03060301060b0a020708010c050301031a07020316050606030f060c04031410090302061603020a09030305030c071a070e09040209010302090901110406050a031803020a 93
    0x11806c448803035400c580c907a40002e00710340034114400040d66040034166201e0a062003440c3c0c21002c0c4a03441c5d42080c01007000104a48580c954250148502201064480c1c500750401005400d81031542900c441c0e07110030095072088140b00f0b062656003000e100742000d50103407084a05980c0c01190a0b068080000c11002d4000b9002e400041184000c011f1900041c980380500c0c03000c240700300040d0040f403d050080601e01030114030001102c1d0000e100b8030901280803c01c990480c0d80c4043c207204000c80314a601418651001c2c41d080400b410701e400b1808043e40850901c0c800c08820720030048001807020200e040707001e02488103007c124218003c1c00400e00a02c003070b41d0b02100300340c400351620f03036640c2c1c40043c0b07104141007121303010f0307405800d101695030030031030784c8404150940340942c80b840d080c5c00180c03014a040c030000e40114040c0e00815400703102034120303801c1580c08a101541d110754441c0024010742c00250354100284c54103440a000d640d02188440d40a50103a008000c0440700351601c40d00c4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 479096834 1250 479095584 479095601
    0x309050405041106130f060c020405011d0402090a0e03030a02030105040e0c2b080c21120f060409020415060e040501030812070c0c060504061115010b030a02090a0e040204060e19 78
    0x1100020f21b580c1100800000343c07403180e59001c0d00000a00c10f000a40f003068000700b035540f01030003040c500c0c00040c2040e10b6100d07404981c3c98510741c135150503480c0101241001c1000034000001000b01e001242d400540c1210402e4804104c607102408056456442c0c1c01902503101c250401c0d952040f0440c00101c803600d1244001030300c03140c0c810390303100c9131240d000c0c0b0301b0841d041d00036030886400c1c0741c0d41261079111041015900361400c50b8441d03200d09000b10003803400240ca590300e00864459251390744210030b820380c00b43c01002003003140ca00760b0309003c1c0c01d0310503200050a410880603407803c2900490f4122940044a03e04014948a41d5020004010202d404000000c501e07240400d50101021001f0103058a585560b241030000c02407030350b4503c5125521f40d600644003a200c0754181c00c001811030b81c114480c03640301e864800c40781000c0d2148d0703440d107070307018a0507400030aa034517940c1b00041c0501d10850b8100805666640c034064008411074a134100c188820842652111054015000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 479098084 1250 479096834 479096857
    0xf12050a20120c0105040501050603030f07060c09170a0b01150e0906121e07090621022701050319020918010f1803090906051509060d020708070309050405041106 71
    0x740c0100030a010600d07820449414101380c1d124010320052060a102d8240c02040940c003441c9880d61000d0404428400d188000745140d943d0102031008038401d01c0c0c4d4034007501c0e10f100b1081084014160355591060101c005548105d4810000a00c000071403241411520301d5031500b02101c3c040f003080121042000741041d0b0400c40001440c51354202c180141106801003030010301c0704501d040b14207031600c41c071074220800c481e1801d44180082d51a0741400f52841f81306c5404100700501c40e00c0495201c080d0302d058030089501181407c4d41850740200d070706040e68130650449820411054080807d4420391b400a504400200e01242c40d2409500350b0320f1000407400000f11744201006e54450840307500e00c0401d06203182c0503c448007015840074100d0f0042003046070030f2002c04c1c14180080c5104100d1180a8000721001401c96520785810064603021821040308540311000760600c1184e0b54400c5d2801c80019007040c102280500d00b9110f900c1c05160414040302c1000ca1910500c2080d50004c1d00024 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 479099334 1250 479098084 479098093
    0x1020a1d030703021009090507020d0525051618110405060705190309061b031d03010e0307050c010816090302040b030316080417010e061308070f0f12050a20 69
    0x140c5c69080603034203001515600c00491500d00350302c100c22104050162400c54000d000d01030303d22030f4490181c078944003144202030000c4079103500400b046196050010414010700307406d8400c5803803400c8940101d48080011440403000c616111081b0740002042040c218010b00061000341040805400c40300d02c01d4040702e035000e0204a00c407011300061041100061184c100c2485a2980020f04a881c0c50f40d00e40c100b4004c0240b0368000d05148890603810703c451040344040342241d5004d410008101c10402d00341c0e59a40d40d5414650f440d903040c614204e000c180c1c9480820381d10410321141885c600d14640e00c05002c40d0960742000041d00742651a95070500c410f02100c41070300c3c01c0000400440c1d00c40e185466403207240c00303d80389801140d0007100f141c9914201c1000740806000c5400ba90000c1c1e040038070381224130799107800000c5014480d0042c0407154101d500104001200747e104c5139190107050b508006641c0e2003030232100d80c0b01d0080044001610302d0710030142d64849648520b21011401e0942c0c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 479100584 1250 479099334 479099339
    0xf020c19081c0203100602240717010314190809060706062408060a032a1503050901061203050919080a15050916030311010b1c0b06010201020a1d0307 66
    0x561405020012070442c440d400014409035071664084100204042d00141c521050161001c00f14506581107091140c1e00c42030005204902c1050000c03486641594a01d00320750b100d0401d44412410300080c2c5845208001070903140d211036000c50a441540504502e1801c102202880035a803c405021610366848903000308206100001000050070388150f24034405d800070302c4c02401c014000d0302e421300400358100148041009240070240603650540c2d41c2e02c02030030702d8a2111131100f40394000070748000451142643e5680c540c01489c01014090002c0c0700d010388480490321a5034140da4000d021403410030001807141801c8141042c4c68001d0300310100d001d40d85540e01030800c66449400c442144001484040c695468170840b5081801680181040003112524145900207400050240111101c266032103440035040042d21110141034002e48a01c84070004d0380d6400f24500440712580b0399800140b5a5205100b55500300c549503070b9810001007645007681d8400c42c1403030900d0b014010003501 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 479101834 1250 479100584 479100607
    0x303040e070f120f050423030702010c11060a080906332404061805030712111c200108150d0219080607030204060804021e0901030302030c010f020c1908 67
    0x101343c0d03100c100d04408a03480c6032914040c00070038801000061048552800b070180401e000041c1c0d038039030303a0a0804450740d00c0f1a060040304211441c2d0060f03071207400000c081a0b1702da070117200c181c0039015140480d5803645138000c484108601c0c00c2c00ca00f440b203000c0103150040d08035107811340e06920b502500f00c2c2d0801411002c071104006e0791418880802c00002010800302e903110b00c0601907950407201d000d071040d040000081d00e4100600c070320744080415860782030030300c1140460171008400091056081d400300220000480030b1411090b07071444214000d951207144011184c00303610205075210144c0359075144048440481210b001c0342c000c6071000f01c040060310f031140900c421908005207118118507043c943c41c0780c40401400c6a003010700601c030402c030094100d813400f074201d58111281c082d208144070801110120b210389560340090b10900000034141c000c0010803650030345900034494461190023840030f81c803c8000f952059401102601081c1200510b00d05180307101e80f0155103018880c212 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 479103084 1250 479101834 479101841
    0x8040201110f010204050f01020f030a08060a0b1305090f1608070207260f0a1e02150d0b030601081603081b030d0b03100b01050d0902031f020909060303040e070f12 72
    0x32011181d0390b0004c5d0520203480c1030150400030301c00034402415007200c95030900780c990050640f1401400000384c08918130385e50f0070200101038002904100e4a4010034500002e0f01c0710b0501c030f01e074024101540800d01004640a25900c54504a2000800000c46050440320007070000c05240450203909400303c1c0ea640508907544015100031106c00c15031010121844c2041d02600c110010b984c0301d140c1c890001501d0740c51000c80b02079844020f142d00c4156001140c2c811118094000c0303d00310015850400c03013601c1e4042c40c0310079416000c50f03400d03030780345c2021036500d000942205050310040d54007040040c407004018188014244c0712036036007010a564507840d54102c0e00c00e50720056140c400150142c01c081241c2d07101c480f54800d00340140d8410f140040c18a2260401d4170003450f484908540a640b002c1024005582c0c41580507042c0c681d41e040d04000a4002c000d6507031144400d0008201b2515002040e80c00b6580c20115144403901e40341ea0a44414002801c6501408280400702800140c10f10 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 479104334 1250 479103084 479103103
    0xe071a04141f0810060512060d1403070f0b06010507150b04060f080d03060806091203100f0602030406020607031a010f030b1507150507050a0f090e1e0702010911040b04020d0f02071202030c0c010804020111 90
    0xea09020816980c54444ed04100c01840241001001d001e04004600009860409051003400c001303091100c40c0c0224014002a0704458803894400c0c400040c040e00014051450f880d85a4003044144d88030f101d01030b00c038203080d211100d10703902000c2c1009207c541c0000841d0052046030500368610380c3d87c0e4003421101e027035078040740140e000410100041c0d9014446640c5c0035941d86000c1001e400c0740031180040030b10780703400b440c10405a81c40d0480d00034041d0340440c008580081c0700501c1800c0400c8101c03400c0c1d100420844042c50500c031039080325401d40c003600f800fa00b900c3e105c0c90304000c4c02c0007080714001140c039002410006e000c0800581c08520030040c500840040d015062003841c03c00d1a0f4611400c054444011a894403024a006c0783e408080401561421200841d07120050b10000340a03001d100030b03460702d03a40352069004840707525071300a041c25849190303030040000380c201003682c0301d0081d080710f01c40542024003603c48561043c1040799001c1e1050402a0110032903002c0700785000d0006 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 479105584 1250 479104334 479104343
    0x60602010204261506030f062e0b0f0906040e070503040311150403050c120408070503191104050c0d050a0e071a04141f0810060512060d140307 63
    0xe00f07001040025110440e80c00d1000e40590154059a6641c0d41c0c500c1e4a0f10042030240e0070030081102540c2c14440c451080c036864007100e00d2810503121358901008aa21307039810306070048000c11045900f00c2c6c4050110760b03003d200c141c209410426181c8a03503000100f0607921003420800410710344800003829004076043d41e5900d451746001d280162120900c03100d003640c903601844515650300300d00506554010b5040c9007490301e400d05449490701c0c1201010549204e51400700c0c000c24841c1001407640304555044084407080303074286040d00703400c0f4100a0041c10f004100c54000c82c4609082d00000c1d041041a0b1120713203001600d002e04401c03100c00fa0f80444203107131640c0ba6500141d408000b2000130b051102650915100f0150443c1510700c030f103110f00140c2d5410903c2001880d075480c0c8041c8800219000083c108900c4000300425520045130a0348100060b1310012030540d1007030081d503d0440c0300b01d601c000a80c894000f04600c005c20030324203d4180070f80d20103003080c040f0148050086c86104 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 479106834 1250 479105584 479105587
    0x60f13080a0f0e04050402031e10090323040f030f02030c0a060806210d0c020a08151806011a1e0415020606030c0a12030521071d010f1d040606020102 66
    0x6050003c0038040c40c660240d125a040500b4800982d9020412111001c901b45402161038a604000c03400d00d48621101010302d890654bc200c2071603000121904c0ea9014032040781180011b24200440600403800f50b1403092001810910000c0e841003c048902c500040849040801080020341724400d903410038400601101e0504c0f1071802d051075518680c3c400c030703004200102201c0041907510b00d54199000c08100c4804074880a544445401c0740c041c140300d200f40e0390b000c0c5200401d420400e80c181c0b03000c41012044403d031070180b0408141241658824140d42d0140b0303605222100881e0003990741c503094031604484c03004111071307210001c1c0020700c40004080d04000401c04040d00307003040100294000c0e08106084c24040e0f0781c2024040c180d450081100c0350509590a0840d0396010f250f0303002e41a421001026403030303c5243c0040c8c1d84a00d4041da9003c010310042911410b10aa10026032408600e05582400401d409030946e480540010640d0500e44401e07000020151a50f991180001d42d50 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 479108084 1250 479106834 479106857
    0x301050606190c05011515030e0708030a05070618060203090f070602070e0a0b040504060b030f010b06040b0a05120405060a050c0c12031801020f040f120807030f1101020a0206070207080f060f13080a 87
    0x7054041c8527130040b812009801e6403403401400a89078424a00200c00300f090000e626004c000380d560120450000301c00c801d02882d022464184000d40c0141ca0030b80e254451003960b8501c0210000c1c8540549109074041c00810b03152000840003103501618003020b4a4a94810034041d4450384030b0036100d03500030796011619032115024035040011b035034401c903296410540c1c00c907031540fa048112380071075448620312903440040000c211050b02803804040300c25000c6c1c40c2844103018000494601510501c8000c01481c2c850040300040e521034034040c0615500102600101608510050b45c0c1c0000c0c070341401c07224003514124882c2240c0c080380d11209505804201441070f064064541006003070204001c2400310142e44540c5880e01031071400604214000940368500c03480381c8449001c11034103600954488500403000f035224403049803164014411000001110b803c009100200103501d480500a0303503c0d00b1080d0101400020400b4580e500103800340d800103144180244590101d0b503442c8c1c100c804 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 479109334 1250 479108084 479108087
    0x90c0e010b09090118022a010605010504030317061c08120a020405130e010b06030412020d1b0605130803041b050102150609070e0a080703020301050606190c05011515 73
    0x40040c0c11070610360380c0602c05401240c481e42122415a00390070032400d2903001d001410406485005104000580c1d012907020b00e80019040c0100340702c3c03c4800a0220a8030340004544902403440081c001a072401d490b80c018001100290350411005400d1033304001e50b140d000340401c8e5940508590030003000030900800203c5020540d085030444d0001e40c54181792100203912040c001c0182c8000554402c042c41d07000000358040c400455024003895164509800c01240300c55002007114054003c2050b500c0800c2d100f208080c4400000700301c0c100607002103844000c002c000c0240380282c007d05685007500441d50310f01c0030310300c2284100700c945c1c0c0b0800c41c000a141e1689443d40114150360001c030007100544c21181e135151b03029030182c0c0d042295a417040b80031910790b0250100581c20900d14000440d2014003c102901a04c1c0217a000b4000c54480405000707503441140303815650754807400c1103400b039248513103142001d66005500108088440c0388460800d0f40b2a940001000c00484840c9190719 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 479110584 1250 479109334 479109359
    0x1210020a170604050103030c170405030d05090102061021030e0301020f0705160501020a08030619030309050102011404020f12030c0706090e0105030f070915090501091d0604030e060304031101090c 86
    0x30305030740030720480d45981d5016060908040c0c0c0100400c60002703000d228054801c09a500070400141100c0c400b0000c418050884c7c1d005154040c0140514000150078141c8140003800f1149510410000070802c0010340210b03a80d034081c01c80030804841c250f204980d4090000d013654001d0008031640e070f0710251500c249004c04075901048041c51030b40040003143c1c1c001c210b5801451f001699596256135000c005203140d000c805091841206e02d51001c81819230058613007003959070a070002c00841307455590740c2040780b601711030080d4400b024000b14003160800391050303010280d040c011a42084921030071641444c5054002100103024150104000c0942200c51030050800354090031201d84494140c640b01d000a0285912320b585400386903050100e0384003d480140301800040000d07584881041006d4550101ea0350842c01218480d9038005501045460107030354151160958070741100c00b486041e4100810a40901084d1302d008815403a00b80681441079205141c0701d4502c9050418040c0072 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 479111834 1250 479110584 479110591
    0x12609010c09120803040606030b07090e07050c0c0f0301090b0a0b0f040b03101104120305040f0b0c0312041104020f1b03180d0f1403040f1508061210020a17 69
    0x40200e810380c01c1004503403104583d0074003a004913103117540780e44a041000150030b0940c0000d020784006020081d1070355004c804c00091f1900d0143c40c4ca015214090b00302d80501515072582280c2d000482e0090b4985452015681013580140000ca111101512404080d0720300701d400d60b940a4030f40c02c0c0084185000800a16105001c035003c005004030035001c240d59012140300910b48958800700017807849181d6090310020501c4005060800109203001045904180716018640c44c41e00c2e0007140080e42c1c0c01c00c2e148207900ca44000c5041c501010009401e94030090000c0c3c461140030761120350640c90b00c0c00244145500b8000f20b0b9a5002000d0240d85030584207021070304150000c0c05421820b03032000d0401d5000c401d040711003030b41c2d05d886800e1a00828041040c0144281080302807580c0d01c0801102520889184100d1085525074500ba21244401130042d0440011034100005e0090314180076196106600b100c101c8a03100c3c0303c41560012a03124032624008140551f0001c0800000700c401c03c0e60 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 479113084 1250 479111834 479111837
    0x30509010b10121401140618190518130305030c130306090b24011413080a0210020f120f07020d03030204170109080d05070c1a0103020a081b040b012609010c 69
    0xe0300d42c944030700360001800001c50b0511031f00c000a45041d5400d01c4e00001030300d050f4014103443d0300142500c01e003200c007211482150f0180314214220702c3c0000070308111038070440c500600002d0910840d54111440da000610f613220081007403045108070740e01a29211301840c407448000070940d100d8100b080b01400d0090520079134a02181500405403c05104440d030000203080403070301540b040300c41010a010b000d00600404440300f0b80000c0100e400100018654003d464041c02c0c841c0d0f03801d0803611420030604060440d401801c100000012450003494096640c408a82c00c01c1407903800221100300044003500025000300d02448a1035205500b04001c05204008010000d00d541c1c07030a01e140200d00700141404d40d1840052010f50081c4940c1408070750110030094410501e01100744100b9007800268062442c1c02404500787c0c000040441c0868224000a01c0740380244003044007400103050014100a012001400180800300303240546c929846000d20103485c003d0b2990f0300f100ca50700c54840 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 479114334 1250 479113084 479113121
    0x1050f0c0313120309081c180b040f0f150e061302130903030204080d03060305100b221d10200d020c0a0f0f0c1410030509010b1012 58
    0x850407092003942e02c0c26552100c004030070120803e000390b00078844100050640e0310005541c14010803c401c0a009420b80ba05041105840f089080290400089030040125003014007050115511104426200c1d11802030f0408042003503940440c003424444540d400c8540300c01004d41c1e03101c0103002040c0d0282a0310b0b036440c02c880050b000a0007002609059038056540c4507824000e0500c0f9030100e07006406601c0413510548220600100246003602c4144c81d1409204006011031403103020f000c99540000b01100b43c20300e840121090794100b600303101c1548564405c0c03012610005811060070396203a0f4005082c104659000307480944032424410400c0c04c4503017980c91070815424003a00c1400ca8032070380c010388844c130b0fa90109103820100003018044a1030000800104401040007030401c5100745102051540d0341c4d40a00d8a13a401301e036145c4d610941d2020034034038242c401d5100726400000031001190002c000030104605040d6020302000066072290303040780100081c042c98051141c5110440c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 479115584 1250 479114334 479114341
    0xb0a180303020306030d0f2c0301090f0501050703090b1518010f1706010b040b070501061a03060118050307050f0418050601080d05040513020d0e01060e090d110309061303080c01050f0c03 82
    0x140081c0e20200d0120b5980d028019805441c200108423014200001c0d008100d000074900f400c9c0300a05580c0c0c4102c48035030800300002d108a1086c0110180765034000f007540755946901050740600040042c1182e003083c00940701b0f0b50480034082840c3d000b0800d00e2041e82946082880d1609202d0074446901f2032075000c00010080403035000c04403011240e007000c9031500d416017850a90301511843e40249440001c800150010100000045019a000741c80300c1ea0803544000030b13510303211145e1003580d0303054010080820680c02d25440031000e0290040c0001881d480080d0030502e10fa145400a64095021200600003600c00f0412902240d40a04009090504e01800240a1032159803825020f40d00424080390341501c917080880c403900940c0c00bd01806488240035851a0411181140e16104031013030384070161f0142039400300846204c0d01941c58080d070300c1d040c003810354440022401844c1c1141000004164000b000c1e124900d00701c2c001162608100c1d003210782403000605603422558080061 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 479116834 1250 479115584 479115587
    0x60f0411190e03030912070b0d06090605220c0309060e0703060531081b061603060b04030803060d05060c0306030c04140403030f06121506060203040b03040b0a180303020306030d0f 79
    0x10391340e11174011108400160400301081c0d09202065201c003000420120f400004c0c011075800010542c1c0c002d4604012040d40c032820428041c02c1103401c500d452005a5115000c07120503041001c0301e2055041c040780c1001d0780d40d202d0044442c21900001e840e00503507800c3c020001c650044035008107518140000080103d0f2208060800340054100442220300b80700c000c222141b81030b60209202401141c020385080c001c0d4603140c00080350007522610040101c40c0a507070183c894403003600e15001c50142480d05595480c150b540c0081c00045d4010300e410112030000d142000594444e4850f8881e094890404106041c9000c124072111403080703080200303151005030704030149648242c042c5004550280d200380c0260051075103801694004d2910366000c2d0500501c241034400421800c07508005003540e810040380ca901075030203001c00c42801000441c2c00b01c0e00000300a0340010088400090521850725881c01002c3d13540310881c0466000300821000341350901c0a161643c406080800040400a40 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 479118084 1250 479116834 479116837
    0x1c050606030a0b150309060411100f030b030c06160b06030318011805040e15010801050606040612021c061412100207050c09040605040b0a0207110108060f0411190e0303 74
    0x503003926290f550039542c240d980c44146183d5010005500c8550303d0604140003521900102c0f0306690340c2c80c01100018450900501071b945980440d628500c50420300e1002310003170100307100490b6061258030903e0446644140c010603100d92400101c003003120311880d1a041506000304198800e4200307012280e481e0402c9207c064660100b481d00c4c2589040f8090359080c1005c241e00701d15003291405035a50030081c0c000420968210340303e1354079049070380e0b501074007802d84008507407641e00000c0c280010080c890140060101c4a042e190000d403d0800303019460700c01037450403030700c1d6540e52921020000302d0640308407104030071400e880107010407010503621a42c890340c801c1c440c0d143c203030300003200d03000c1c01001c3c407501c41d00c0880100f05602d04e0520b030074604040c201c10340303040e101d0703a40307010101d03240c0402442200c82c000e038007113090481215800015501d80400811058200520344d007441d145030344901c038030807030303035203940f189503110100751441203060f14480201006100203150021040d580000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 479119334 1250 479118084 479118091
    0x102160201080a02190f020f06040f1403041703092e08100b0309010f0c0f0f05031801050403020a110102150105091305100501050114070b0f0702160b1c05060603 71
    0x201034205443e003206000091203001c9880c030302d2000340350156903020350021001483c508680d0840d074940111400580d128a8142d82c02008102c0c1d00000c0380c00148031901050072801110140c90410b40d0754500f0000c04240c842c0e000f08290000505032049242622800e1403103042c000891000081515911a074801c04914039003e000003040041c841030000149280a480540380803600ca06110007103501030240704038072414042c01e01c000010780d98490708464400c40380b40c0e5265800c264405009072041e07030020342440000400d02415030640c00c02405040e000314407a6004050041c0036041082d9819030b000308850441d04540402d550b00c22001c4e00b05410b40b5022900e00555407102000850302e00301506004013103005001036000044802d42c0018100c40003038849030b008200b0f24542428134400e042005103a41d00b42d0001c640c1c0252900f0102d60701c2040340c0100d40420350010444103103550280d12150b1030702000107807503c80d00d04069134101c003010914001d11090500c80c001030420300009 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 479120584 1250 479119334 479119337
    0x216052b0503180102190504050a0509040f031d0a1403011d07170c090c13080a0b0a0b0f060c1f0203010807061110140108060601080402060d0b06041d0106020f0102160201 75
    0x200c803038030b0760000070350403900200d009070303a561546106c903c4013401d96003062040d50700c03885c50244000b80d03d0030513031102482241d00200000c494401d940d000e881c1011b4080c040180340a1000e11482541c842d000d004d005803207aa03864440c019900820107094030014100d1015503116808202c40e41c50700002c0a500f5200c114190800c440f5220080602d401c00c81c00b0706c140d10078112824042c0161944000349003107144c041c480e82440c0d0311240f007150b40782182c0000401c03500703182000032244032440d88842c040c400c00903c050600320828000400d9a00110309180084d005800c40740300244022503c00c0c440740c1020001d5007503624200705242c640340311b481000c092203400000da4224000900c00180d247c110850208404400c0c0140790011100c01d02032002188590070100c0e032998080d11103144110790041c0000d01d42070702e90b0000d4000d00361060003980c000d14144400301c1c0d1001c107400200340d5640c000c925052550701d0294002e181c0b03503e01d601c520250b481000700c1c1c454a0840550040180d030203 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 479121834 1250 479120584 479120611
    0x10c0816030f061e060804031715090405010b180c09060c030c0616081f050f030a02040e010b01030c05030f0f071209050d021612060f0216052b0503 65
    0x1021000d4014000d441035020720b1914010300818078003811034602c2a4841300f10040010551035450640f8000000e0368050081903103042114042141c1d5442141c3c0522425044030040e610700d008038400d542e003510200c40c01c1c1d4490114401703a080c140a6620b510f102c51214000b1428001c41002c80c910030030601754007919002507000440e02e0b0030011100d05c00780d0a000c4a1882ca00440201c00500d601908200055612808141850030b1074140106110002c140c00043d00d180804116126001e6080a9014011490010050707661849001e0009541e50004141403201ca0001021207440183c1407040c42810700074440100c984551095104c0361003094500d05469800c8240c4034801c400303005609550030700c8256410440040b40100f01d480c0340750200c50003c000c1c80b07807188500442d4040d084aa910145108010400360b821250085405510040c40c0c4280180c1c980001c003481001911154403148030041018111007002e15881c0c0c01c07035018000010b48600c0104680700141029030358100 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 479123084 1250 479121834 479121871
    0x33050f040f0204030b01030c050406060e030616021903030608150405100203060103090b0106111501080307060b15040305030307090918121716021605150f07060603060617010c08 78
    0x45a0480c1d0113590050999802c42d0b0790f85c41d08008902013409814000e5050030b50000e4503901803503585840040080c0500344a40e43e03403541d54001d03d98030410744c04610920403900451074080b0401001e442c02135801003a01401c0c5111305150401001080c00b1045d03d26081002003080421401465050390402507036903201d140c0100c0c06000c6d001005081c50b88000000150645c00c0000c1c492035000307090554501c6490150100885c1d02c0920623000c89800800c0000005211a444954600d80042c80d01d55005419641c55502d9041500300316a903500010501a0f12074100703625000902400c42c3c10300007409086e504000d40c2030360000c010b01e060003110011841d10b000da50410705c0c004e88a80341c802c1c6854090000110041c40c0102d19001d8010304905110819160443c102521400340840c040000410348400d09944210b042640d0080107000b00400609a0b0050000a6025800214041e400c20303007146200b0301c0742ca4501145038900940c074950690003800142c0e01404100980d00c4040 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 479124334 1250 479123084 479123111
    0x306200f0f07080409050411040905190c090501060c0201020708010507050708071e05030405040c0801081e0f030c06010e0a09150506281a030925030633050f04 70
    0x1d01c0b0401002100c2c04140840c9002c541d9001d24401c500032800c2c140000405c01c01d21040390a464805415900f00008541084c030054462054051203209030000d402c1c4d50b20043c0b001c440c0282c00c0200000c4861091005544e410480b803c05019044c0003013199040424003d86141314425005110f14000700340801031114001a410740306166030769946e0305005c00d180440c1c0302d90050140c41c0c030031072400d90364200c424482c0c4460740c1600c2506000308580d0020240c0802841076428604881d8882c2081a104580d400d1000e0001280c000700101060750400700d019072040d1009206100f9145010f00050101d0072003c2075002251203648001015220034020075080341c5542c2d1054110459200103840300300c6140e00c0e00d000c49001c00e040c2d1090405800c248070062105442591450740030b0000c8081000207409018104280322001099040da25a01c2c801070710740482080104021000c4512140c00c00d41f408684a04800854040c26a08220010b603007140e100300b400f0b000d1340c3e45e0a507451041 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 479125584 1250 479124334 479124337
    0xc090f060c010c080610020109030210020d09050a050a1101140a0804030e0d0f0b06010c210905120f0d020c1c170705030d111215041b0302040306200f0f 67
    0x300380d040300030300c82100c07003070310107130a40b082a00c0e4540074000300019080002e01c181300e10b141c400c0d45035002d00200301000000c2000303500403030726144059a545d81400c0004008124420b541446030018103010206030070021400c0c0c5c0108440c07414050120080802c0410034003c49008018605250300c1640b154102150180c65450b000e5801140c41c0e40d4007070502250400300e82e1611702c620b5030b112855907060300444c1c0301d8814a000826424004100702a4081a01c2070b000300c62000d0701d000d2103da44d42e200040c0c0c407030410402c0601c040d085030411541c1e89005000c48960407410703000074408c41e0b0030744010a00c000008400694450304e404501c408200040e007229100d82c0000600c20f84403500c0e81409603ca0780700656040c0c3c091b25202e896401110309406071504070700d0074a4401038550341d8a05101b103201a015a06d50304c55541d00001c0a8482400f860702206112548d0058843c2c1c2145446400c58051840034800340d22040c8040c0d8900715140200d8400803082c103d01500c449000350751080c1d9 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 479126834 1250 479125584 479125597
    0x21030503150907120b04020f030105150f160302010b0114030a11131d0a05040507030b06010c05151006050301150309020d050706050d06090e0601060f0207080601080c01030608060c090f06 82
    0x2070409402d203d4100e6002c40340b40b08413182c420080100045a104100c101c2c4201d4900d644100710520042002d032822020007030b84981188001031400d10980c2d0b1401c80c9901200324007014402d03102001d410b055092140a030383c1301e42820000c40b021400000c000fa603000c000e150711045078540701098186010442541d62400c0000c0400d08065107c1c1242e410110481e00100031001041d400144600528010507008a4101029041041c1943c4811722640b4000745540e05020040304002c0003d0010050302401038020644034016041c0500440c10401d010340c000400c12400b4801400707410310b100300c00e01d810310050500103050002c5101051036210001000f4007a03004800d400501c607900b120080081c1c0d51055820008207845005c0700e81110f02148201c012075020300014801e02d0701404409184166a0040718500e640d80c0d44007900c0e140098000e203001341c200071560a610350b090300480e0068241240504190b00d45103e501103180504d8902c80d101301500b140c150b1181e16900b040703544 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 479128084 1250 479126834 479126839
    0x20402220902040303030c08130b1509091e0d090e04030c0c0b09130603080a210617010e0c01020a080a03020f04170f0303070509041508030406182103050315 69
    0x165aa10700840700290054030050340400e0a101030314912600c24580030f441064240c98000d0b80d0200c60700c0700400c005009210610154806407a00b0007076851104c0140b06402020040560303500801030040300c0b842050100c1da9907070180e4420720003135800c00c0f00181a9882506e4801013980d65060032248500c00383c0c005003507001c003000b003c03900301c5290000380094003096401041c01040450180c080351113520015000540c28000311003e58810160040c10b02c00895000c0c0340c400301c4e206914111761440d4010403881d042660180440345c001e01501107501550000307846003c141100103500c84c1c0b1a1400103003102c80025030804058001d038180d560100c03240034165261500e0f200d02164812800810000c02e100d9030044102c41c4c04000f04aa1082049599240c00c2001c00c8041c00080c1ca404010345009150340200822407030010001341c001061107583c0c0303120500e200308038a610a221038100e11041e02c2d003d8942c0d2070649020720038200c110b0b81031918a54a5445641091500f0080c507405035 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 479129334 1250 479128084 479128147
    0x61407021e041b02010606050f03191d01021309020f04060c062306010e030109150e0f030c0706090b03040206090f043c020306030618030c030307080406060819020402 73
    0x40901c0034011004407110f00c60f0002c000032520350100303545602610031802c441c0c890400000b18410701d1035503134104880d19a58045115619906415000940014240703541da50104000021107040c0c00d00000030702500c0c0b81107240c600c0b0724500841e54842c60103840180a1544404410040c0c5a0700030f203101e01d1110881ca51050024121480f110130907515180003500d07100c607288851a042c8505c8110340c1d80072070325010380c41c04544402e001c2c000030f0a00b803103240500403d1219520b000c0c4020209246000060013803036040080203400340d0010340103d03d0000d41401000010384aa1302191200d1404484036295003880300005000f0f00105104041040805500c2d1201410501c074505d0030b05068a0000b1842e0981c48186401c0b03003c101c82d0b80e9850b41c0441c01094000d00351383c5078070101e072644009507490182e00c10002490340e403059a14100040d5810300700418414288501406803003d000a001e168110b0a19001044481407010307100e02d07070000d000590781c55031425003047c2015146141 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 479130584 1250 479129334 479129351
    0x308040b0a0806011107091505130c03051f030204110d0c0305070f110604110307030b01080f1e0309130608010e0c041a030d0f090e09030a09061407021e04 68
    0x45168000c180c0c01c4010440b10400f0850319030003075841c2c4194a04280c000c0402629040e00304014049445c205814140c41c0b0801041d2070712421100c0e6400c425940300859076a20b00b03072004085810092100c414050b0081040c410f5003040100c84003100e40480f80411000f00419500205100340d10b190060f5502d46800c00381e010380c050304403d1241140d0703152480c5c08550510151031020741c01c0d032440003d40041d0300080008400e81710200c2c80b020040c0407501c1c03591308c03036684800c07441d002c0c0c10802490307001c0820060b02e0881040303961030240035441598891500300900940d40e0041403100d6214409035022a0660341c941c0d80601c000b805840000c1c462020b64a480a840e50103125400c4d005e1410138010020941c1a594612405500503006040c2059840b0045901a041440c181c0c10401c812000180c981828055503004820a5024656642044a002d0326002030355104405002c44841480380344c0d5a0042510001030701038850f80f140c540780b00001d251001e0b905108661241c42c0c602c40 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 479131834 1250 479130584 479130599
    0x3050901020432150405090c09090907033f031104060e0414040f02060c03070c1d18100f060e040602130b27010219080309070b040f030615030804 64
    0xc440f180100c0891100b207011454180002102c0d5011040c803000c804000403c15410721651081d4007103442e290310ba08283d01c010000e06030104c00c0d05d009040340e118200c03e10070700c0b0314460700c000a1a50318650060000d0b40d085d130b9682441084500540b240b20009120400b14043e81040c0082180c500701203640b592100d20181282012942250249240156407580e0b030103240019809260054050203d286031582000f440364007401d8501c2e0f040c04188080000a40f8034441c0c08050842c8005030303030000026a00060314040000c0ca40c05804804108141c0d03941c4010414660f10300320350ed400f00c0c00044140060010302000e07407100010300080d004110520040d9805001120900800340d540e142e620900e490b518000c1d01e01c0100c8404d440307030500316106118034440300f4150040c01607503d507440700b41c0c0710381c245038480c141510102c100000b04024200c0078040b4002038250100303403a003400e040c14010310b0300b0060750000074100c1e65521144404850b8255140f0011030340564000e54442e2914103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 479133084 1250 479131834 479131889
    0x2010c170a020f070302060301050904030c08030103060212070512190905031c060501020a0537050a06051006021c0315090b0112061202040b041b030509190b07030509010204 76
    0x403003030050283c00d0890140c0800070403100201c03500142468156401c19080240001c000b6000300c05201100f1100e80c005004940514001c50140500680f90b04071078003040340c0420020b00d41010840d00b0025203040210070b201160b0030241c8001d03c40c0011031400500b00040c00200d8000e0038a110116204207440040344000c408500f01140901c141550303500160703035a0b1920000140300f03820070040406258088107020711100303203040c20381110130940c004441013805c01707107002d46542e080a8801402e012480c0241d582001609114450071481c0c0340009440d40102c000c0c90710242c0f43d0b200b034003440e02e03ca500000a040f0106d03148110b000d9803012a000141a00d41c0c1140c00315400e1040300260111a20842c0f04407107802c00381071090482d590030003000f000c40700d400707940c000d40d1800308104020b40300540313501c46211618001203905110500620313142c4800d10000c2d400c000001d0900c0040d48022090750032036250304003c1525103e60241c0b90182c025500100707882011003d032070510010700b60 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 479134334 1250 479133084 479133097
    0x9010e0a0b0111010906151d070c03020a0c03030e09160210050c040e0f0106080c03010608130c0e1009060909050d0f110a0c061d1f02030405060403060203041e0201081302010c17 78
    0x14089003603940d1b05000c23041d544001d030460003004141000540075402010341c000018800e105451030310303149a90710740c10680540c000740d0000d1140b000001c0c182c1000340350541c0042c10804c4540c01c2903d0100025030b60011410b41801180e26003004c10f0940340e0789001d60300513003030f804281c488915144040b640064000d1081000003070519011408041c10b40044074141c4100d5500c1d440310340e41c0c8004007030380fa10a000c804c991110f03071180700150242002100c14002c071503584407529880c0c9084041c1040c0da6060f005541494540312018000910000718020900340e54145090010006407064920070071079510303090180211100c2c1070401200b024984251421502c13000c41151010400070711030611715160b540c20000e8068244907038520001c4140044606104481c609078a405c040344660304107034012a5055004004d001c20010311a04103608020050442801d0942640008140c540c2c0641800d00e15804819100103691145e022015940d40240c0614044480303a40c50034490307802030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 479135584 1250 479134334 479134361
    0x20120708151003020f011b060e0708010b030601051c080f030a090309060e010207092004090902040c0f0804020415081e0721080a0306080703050304060e09010e0a0b0111010906 77
    0x700001d0710564001c034030381d01075a8002d80202c1100411000540d405001003080f801030310740004442c0d0000f0518041c410102c0101c0020b859203902d04088942581c0700d101d00300748a500004c005028589600c80b000304036451780b0654140e040303160b04091240b032080c603e003070540d80000410080202000d401c158903a903c6a619a1415591180c00b140c254040059590041c0c21665081004600d940c020b46c009030580304003410385c03c00312004001c25501c00c0e0301501c607158403000c1100c1503203041c0c41645440d22550600308901a401c00c401015818003c000078440c2d40e440c09000211010903030701c07501400c9840201c69001c02408c80008000990ba42d05240740d204510000c500500410404200840914404116098607540f02c01e5075030400c0c105202010381d82c0c42c0000712034104000c410001c500031405140d86504050005042a0115139000d0244041300d00410481181d500d00e1640601c1c1c81e803001882c0300305040101c031000104042c4903829030030205040c0c2880f14580c003ca0456146 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 479136690 1106 479135584 479135623
    0x130b0619080a030e0a0b0a0503040311150c031005011d0d170a050d2405040c020106050603091b040c0f08100b041d0703060320120708 59
    0x2d40e80c0580c006400c0700700305043c3d420450902400f03402c40d040e00d1071a004803914040d0a520018100400300701c464440382141010a00c025034042000c42900342450502c1039102800f60002d40d603183e4030b080002000922580204664112207000241c0e071410b01c403800d0304110328001071000c1601c616000940300010380369000003e00c802929900c1d55134880d900c0c0c0c0740c0e070700441d020b541c081a24010f42c2d0381003101c2d21201400c10000c452040741d01080da20b00e502c130100e01602c619841903420941c00300a0214003900840c0100003080040090361130040070404010030385180e42c0610000c0b803205101c2c001564070494456a02601d0b5140d5646d00382d58404403191181d000307500c035903440c200c03aa16560050503a1002c081d00603038036240901515045480b01480c5c0c1c03a0001580b05803a400901010031615440c84071001460020260399410f41e9501700785803103255840682245408 = true := by decide +kernel

theorem cover : BRFrame.Cov 478956834 479136690 := by
  have h0 := BRFrame.cov_init 478956834
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478956834 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 478956834 ≤ n) (h2 : n < 479136690) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
