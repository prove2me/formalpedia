-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1909
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:07:05.259983+00:00
-- url     : https://prove2.me/submissions/b37a6be4-f1b8-4e99-b0a6-3b41ded34a22

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 343165467 ≤ n < 343345323 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 343166717 1250 343165467 343165477
    0x315091806060609050a09060e0a0221070801170610050d0c0305010e030d1d0a080c0a0c090f05010b0c03030f1e2502160306020f04030f081c02070b0a091106 69
    0x3c00308500705818080c50405404400040c491a501030152038a013140020308284068104a507143e00000c0301d405100d4082c1003403000740a0748680010754034145100074040c407028003a108420603d01e10604640000146090080120556040501c0d20340000c120200440396821500640f0301007000011402c2882881b4002e4042005180d070360140b0b40781801111a8405041d802c07503200764804010b08400281c8440c4154010011030740c924044102618007503110200070500c185002000c074151303450390808220502910410701130399803206000403c0340250010720302140e00c00c1c000192401851500039401c00c1000c1850210380c21410990352440c0750072554a0800483c502c00074a03180c80c04800642411803620141c070036010424481300c502c0d8140d10025280f175070080b0307000220701d4241c000c841c01141d00c01040c4086103d02d02e0507100c0c0d50045100c1501034009201c290554816074001c8495159010401403019581d000d800f0000704007202080d80d80c8442d5141e4150540c944000031b00c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 343167967 1250 343166717 343166729
    0x4110408010c030c08070f18080d1806080105030d030b1516021807090302121501080f0111040b27060a171806180307020a0b0405030d031509180606 65
    0x10408040c440005402d0b41c9040c511030003008260f100300220700d50700580040c500310640c41e100348d550f071106a99034441d10300ca42013800d55002d15010188125000740792290110443c0400944560b42c1d4441a114140b00b40309603038240c0c10804020038210b211b540685050300c0024442e160079180e1034070109013500714000b03a000c0564015511000d6107800391800002000f000269541860070f850010030341c1940c0d2100900a07958002c2600c58080c00340804040c0c2c840302c031113035a51980d48044080e690703d4800c8140c3d089510340b8006010000c07600e001c03101074410107181a850901140c04000d40508244da81408400044000c0c0000c1e540b00802442d074001c0f5035a5030385824089401719032410b48003900640007400384641000b031182d0080750695003c0c600001241da40101044c40034154070039030310021341c0580c41e810085040c0607102d002e402507074000d404482e04000e1030f04099003161008603801e1130407440c454003048100d4040e00310040b203040004608108080543d685825102c01781c01c01 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 343169217 1250 343167967 343167971
    0x1e120513030e0409030e060a02010209030d1e1403190b0a14120708061f03120903030e0402071a090c040f020405040e030310030b15030321150319020411040801 70
    0x490525a02c00b00b19804440210390400c00c4005175980078010051840f0120301030400032a003402242d0007941130326944500070b07081d0740300081c407010b0041400640b0342d8401c03110305010820510040c8552000c01107001800002c91039a2198106007120510072603090503910345403c6820001d8842d500c404001b802181071000034041c20100b088452074145041001542c8119010040218001031954100000c00820440700414010003140c2e5105a0405408240e000454142d590340c00150003040724042d6071051082c108410821081c4d108004020b082d1030014070640c280064503083c1c00360441508411651032495410124090391005100402c0041d40071404000c1c0d8146801041e0440c00080042c600d5468501c15645150440740405041d001d100c1000400d03050700507080307806110005013103e8480c2e84c0e081c12041c030b407d08410300a044040c0c0102142104104441b04c080c0080000d01615240d05416001000d044000c00d003030380d0041c0c4a403404036000000100601c0036200b04400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 343170467 1250 343169217 343169251
    0x6070c240c0804060b0d11090c091522030201050a210e0705120a03050f0c01090b040f0203151b0f09060408070e01120b040201083c060d031e1205 64
    0x81310454200c1e400d404d0045a2688250300040c1c081c3c3d858004001c0c0858249010361910121255240035021010703400c0002d050044180c00381140c054410b03c1c005a032101c500210b00c11003070759411814032000340810300601140031454014000c03241e210050303000c141084c01d00c0c0e92883c419568821608412600602c0051095041c00300e044200c000c7c001006002041c05560018890320400e00e90801c1010701040b42e402410b0203401014482d5000800608a800c00c1d00b0200b88000092008038030034400c0c10440360011584000d00751140e01d6a281c0120a641910300c0007800c3c6d0f0092802a64040c0304100e06d1002c0d40d0782e00f018001410340c050081415074188142d2b282c0880c81030300302030564019113051000188010581d1540b290782071a00b50060340303400b902d48550480c003d80240a1654990a20174010000b000c4401403080209000510f9192749041c841da02c60030340d401a000070f0042595400c0c580400704e42c041d00c40414949440d42c600d000c0890411942c0503200c2d03c1c080600c80b10 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 343171717 1250 343170467 343170473
    0xc17070201020f0c010207060f020c031f1d0c060a03060b160308150d1410091101030c1b0f050a06020409140105030d0c030807090906080d080906070c240c0804 70
    0x41e40b60002110000300b4103c0740d2130001035600c9049104440c1003080340c0d81080d400c3d5109201210340140c002d8112040d034000c00071024440b18004c55560001450100c4040380d1503501e842da803140301542c10141101c555000c0034010f0b40c2d80300940380428035031240d0b40010381e5007280004011443d802d08c1440700700015803800800fa0080034010a090114a44600c0c4c40f82e43c45d8100d42260a0388609508511144103480d24103105401c18241c203400d05d00f40c03104040c070030011804003149100b40e9080051500b0406c00391040c00d03003030054285088100303402d000010001000e214410380548103c403050805039413400203a0344617030003a82c0041d44903003100d1800c05401110380d0142c84214080c208082d01718a00611400d40000040d08000840e40803c200b00d00452581011301203102d804e111082d10f0f034405a55801c02c3d4662900019501d10006403000740206404e03000e42e5039959190410101511482807951140c05400e019045510103421090403030300c15041c0114141c1c40d2f080031031401c0d003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 343172967 1250 343171717 343171723
    0x80708060915010b09091521160e0a0509010b060307050405100f020a03080c0d02300412050a02010b130c1202030106021e10050405060a05010812070209070c1707020102 74
    0x314102c03600d41000014030107100407509903204424241d5141605035580000c82d9101d07183d00c00c000750001e01e134600518510510100b0030b80001030010440c1d003541c0081c215401000724074868407908400007004540524a290801601f0034058000030031035030201d00001d8107591040d110000441c000003410002030400342d0440008a0315420b0a401c03c24100d18065140d01c10701c0e00080401007100000f038945501c0400352400241805011501c600b00c0901d0031969a402180d0860300c0030141ca000c99011602090541c1f00e2176210070402c11008228805883c1d9030040c0b600d43c0255500c6550a0401d6119105490741c004203614022407407130030002000d40040481c0d0608034805004000500c4042e800103481d54034140c1a000f448502c6404030003c07802c22080d00316082107a400c1406010601c00b0002e80d0074024a050501084544d81e641c0c051a510114410300c0d404440d024000000540350150f40c02340c4c01001d5040c00344890403e59210800204056601400404082000c1056513410 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 343174217 1250 343172967 343172983
    0xe01030c06170736061d0a120609020d061b020a0c15020a050609010b0a090912030b18010609090f06050f151207020106060f020d0e0603100807080609 66
    0x2401d084081c2c040088640480000080007501402001c1000704c0049030300da03c188544000c2405030290226440818581d800024860200004c1b80080544040042000c1e19030040c400100715079001d81c41d2901110518620b101e041e44e1440e0703110104c0c80942c907140003100f005446080c00107043d482581b105101624003c095500715801103580500280c2440405010745519403041e204103003035000d04a1a000c0300440081c058025101030007604181500010607103041142c4401405440350646011900c0c0140041c01926401191149160080d40316110410016000e815542100a06910309a20a078411400111590340406c00800d11380314603c0b0b9455146030505c41e044c07402d000584007084a004851142503114030811207103201c5800c03030700204004840007100d841d2500c03000e0b00038501d0b8440c0a02013682d100321555004c1c030106074910100c0d03d80d02c175101d091250405000c0c150b0001840e0808560107207601082d5030500b000341ca401407142200030011490400b05560500c44c0d8 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 343175467 1250 343174217 343174229
    0x20f0a05100f1a090901020d020c0304090506060f03040b0604021b060105090a091709010507020a03060903090609061205040203030c01020c03070c05060702010f030f0212040f0b0906060f010e04060801060e01030c 93
    0x1030803c030701c209000700440390650000102e403441d2140e15105c10780340c02440349504842080b4400a203403001050080041c1c000c40b0003400f020002c40d9166030501000740f10329000c0c404124030800c00a000114000051130304401c010700018181802d280c40c9192901141d50814002d5000c0c00041000e481c0000541303a02140c020828072038070300c49913a540c2801510060009140c880400c54035000d9225006961003150018040c501003540e80c2031030002489241c50035000254404000704402e40500304a00c229481556454018202420580c0042402134022a8180020480f910300b2000c240050005242100040d5980708c07480c0c0743c0650841480d600c15801280c0a1120202507a0080d580c120320300520308000c1162042c007403241e80284100c0e50700000316100c400c20f0005001210030501d50161080c00540600d4031001101940c0d410204c80860740904401c4501c100c03548607800d00103000f10042c00c003044060311090003d00356011504000c840d174010900400500003954400c00003444 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 343176717 1250 343175467 343175471
    0x25091703030901151508060f06121006020105240a030c0f050a05040b01020c090c2104030215010e1302031006080313060e0d03260702101406030a030c03020f0a05100f 73
    0x4603100950305105d075810700381d074284042c1800103420b03912601030509100100505d06075030360a0b12510391450000c180c50b00f82c1003401d0108040389850051240e180900c48410802518459240110654085a491450304845401f100200148030b040340ca078064244d84100314107980c100010302c11040d42a9000c5446207003030030407000050343c000c2a280c0d802c0c1000e88640d503081d900c1c803503041264440c06040540742010701c0c21110f894030941f00168003507842942074501d0f6201e09821070220410a0080e2124090740002040c0a04a000c0040722202d00c00340985003002d00910078013007100d8444c0c1c0f1000803504001910344003503e0001080c400b82080f828581000c1c2d0a00000c5401c19140003070040500240b84ae0050442d4000c2042d0203191040401001e140e10702044001e44804544941008850500100c82c07444905001564410074000d001065100c040d524225140c07400c008040c0d040d07000b503660040d403003502401091541070060000b050001c1000c104001114044100c20b50924 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 343177967 1250 343176717 343176719
    0x140f0121050106022e050c0c0a030302070c0506030f07050a0c0b010905040201020606060f040b0f070803091516020c1c05070b03040b070908030d09081603030e010606082509170303090115 82
    0x11888103503007500c12817814800a90781d0b40b031a030354000174441d111076040d0303e104e524008002c16034560001c0c00d40c02e11078600ca04d402a0b6941c14000a0700007a81c140c0d040d21400d00004202a12900117005812024a0503d0005400b80c4440c489003c00383c00504055480d402000107558040000d01d4118030161245458007951185e200424092401103400011001480e04440d4242d5020f540c3c0280c1c018940c2c42e90b0703040404c20b00d40e4500c0058a9441d822001c0d500040c01103040c1d072819600107080d07802900351502071038100085c0051942403040000080c018140200e0350030410302e0043e00a0011883c3c1d80c0c1040c1c205542603400090408081100707041c01405078640c044282e4101004c24a00400c980700c1c545442145401540c5011290001e10349444040c580d258000740d0304006140000c0113443d031211021214070030100d6004040207803c00004a002c00035103032100c030b9041075250140155071203860403009c40e03400e2540da818542c0040305003d660607080c400c10352680840109c0e12116 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 343179217 1250 343177967 343178023
    0x70e0705070804090b01091a03091e0a080304060213030c030605061009060c0c03140c180402090106050c0304051305070e01020f0705150910031d07140f012105010602 73
    0x180700f24016810200d4407980d1000459008403030110180100300d1409980701d005020b0800c603900100ca043c8541d01c01c0c007240341ca020040d100c1000d00e61104c2c40c0a80304250781505c4450080e030029004030703161582004860510340301d800b419800b6601c503188422481c1d00d582441003d4820140034144a41150900c40c42201e42010303072641110843e00384010700d00180e05250502c08450703440604409001c8084844407500481c6041e026202100c982005c51780803039200a404c002110001e4020020790010303c2081d010308050480c0701044000c41e8030349615400410440480404040050307504c81c400e11030741d180c000000942440c020b00c01028142074000d100c9175211064819240180c01c17009500800002d10811220140005404410800165400200140410381d403030410810f40c103600300c0d2165000310b806011030318a803465101e1b50900d4404c10503010788013040c0c1da040c0701d48480b441e048040d00621300303081107540c60b000040c0c0d5803412401909007038400b2000c0c110b21408083c4400744e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 343180467 1250 343179217 343179233
    0x408060f0c0f0a0c020102010f0501170f0a0c050f0316091a04140c18030106080d020106080706120c11010c270b0f030402031e060103060b01092301031d070e070507 72
    0x200340f00a1909000b900d0140c00142c3c0146015103c1004850803c00003082540251141c802e14503c400212440100048642030700c0f448145030040c4034500000c410021413900d24a5814007810007000d40b0882640403089500020013540710b03020b060344440c200c9089241d04111000a45804c1c0e40a0128024841c02200b8900c0028410840c00a001c1581494018400d1035420111005002040309544801207d5511008a0344a600540c2410804141c580d0b0124400c4120b07541c5407a49804048500450405000b456100350100028401c0056032100309000744462070b403181e00d0700d13468203502c40602603034418008140d0140745401c140401409604000700d5040e20b080700741e0039031261614070009080050000d0180f04105030304d85684454000842d04c4c03130499110f64010006860030743c0065804100da8031800384000da070302e4030b8150040400c26410b13a481c14149030010f4650741300c95010b140081510b03504800754bc092a4244482d5940c40311150304118981070a0b824000c0955400c80 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 343181717 1250 343180467 343180477
    0x15010207051c020d060b0d140c041808090301021905070309081605150909012601110a03150e07030c0207080a02060301051504180506180103210e04020408060f0c0f 72
    0x1c01341002400c07400c24014250320030340318180010032403004d45a450078410391081d40c40f20246000c4c050019180e440303103003510403201250204841c000500c4a144c550480c10f40103803420a4041d5000c00c401500e10700d150742ca10b03010500e84e4440544502160600820036000381c0c10444850b8020b0040c0100c14030000c801c6800c64500b103492060000da00031031000380b8000c8107001c0360028840c100204905124000c44c91705604100c00c11030b607003400900b42c0f40c26181d21801c0207004000803c03680c03070b00c01d2080c1c01c80000c008650500120b40e941d03c42c50303050b640104989581c0000d03076440c0c40d5030803580c0c10700401c40104050002400c040c041900051600d200600c83d40380314858001c2440404d5051a0641c0c0c01000c0100c4082d6a90003400a60000780c2000c4840503c54005511000304032441080e038241600d81150b074021580c200b00c1004824004840220002d00404070719a100c942d450340024000361848401810301410110201c1084090150081600c1c4006001c00d00380700c013089054079 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 343182967 1250 343181717 343181719
    0x160207061b0201020106030803010f181107060c050c12090a0f0506030a0b180a0615110d081003141c02061605250c0f0501020307111002031215010207051c02 69
    0x20041071107840140e0040c00280e00c02000c20002000001740e14500d80261000c0301d5001001e0300b2400c8000603c182182c6070681a00d50611060009202280344c9600007807042c072441c1071551901820025192808040d9030703c82c5d200342d000165501490a1a5020000600001c0c2c44541001d003404005403481c003000f824154980e0740c8003021200790b95038582224880005905645090038685c0d102000b80c58540280708045440c9440d8040f480d124840b50704060f50208090040241c00c68000c40d13114002070070481300e8039a00318010000ca0240c00d032400313100c2030120040c01e07a41d541d0000010406100d83c1c90303a0640d000b0004220b0010042c80b654101c1018500d0030550300c210707640080d20640c00b10300c4031150102e1026035020400c4210f05090301581c500200d400305580c1d9942c01283c0d01d104403c00201a40070381008201c1d40d04142c2240d90360140d4078010389084c11144601803598076021070b10b41d1800f8078500d1a0f80040d5070184071020241000b601c05c224a0030f104000f0354160b1003c08002 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 343184217 1250 343182967 343183007
    0x70c050316030f021003090c080c030d0503090a02092802032505040b0703031506050904110a05040902070f0f0302100b0904020603011e150c0213090f23100516020706 73
    0x55282103200b644102e0f111980b050717202c2c0351907498445007070340c5503030318030031710707000c0d00c4cc3c100b01801d4140944241d03442213601c80c0c02044005540d50910101c42006440c0d6880a069100f0ba5111701442861a2200105d100b4006807245000c40390345032041050044001d00306e1450408114850340013003201c00740d401c40c1144a599141c68a001c5005240c0b698800041c0e030107042010480310f40c000c0080c14060340807142407010200400e0380418034401d0244980115108110400900456401824100b030054203101071070100e5894034110040c081e0320440040c0c0298804c07030701100442c400c12038070180c1603510400340d00c1d02b980460510310040c018003840c484007100710742500340c1d41000034018103240d40d1100e0000c0c5440d0710103884201005412480303411803c000f45c94004240c85602d030031a811030841da00e491443e80b076007032150f8800c0694a01d4100d0001002e0f0003810100200d5170b40d0b14103054006014038040d4151400c103010140740742d0864200c00010040365a00040c155814603081690f = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 343185467 1250 343184217 343184239
    0xc0903020d1406130201030c0e0109060c020105070f03091d0402090a020d150801020a090b1603050304020105070b0c091002010b09150a050909010225121211070c050316030f02 77
    0x11452803450081e4410143c4076440820404a84041071048424401c0e2000d0003003010608080c1c41c40040c1414040c00a641000d0400405100d4101c41103c41e0042c140a07140010907115042107a07842030055001c154810030030048034200c0541c0418111803401843d005080550008071444000390545d05507540104072810001003642c0100000058840464103207235880a40034003070f4004500071000318919440002e4044141c1d0100c8241920ba54010740808020b80da0503903460700003510580c10400309100c0517000600021107640143c0c0d4060000d40c6030010760b0f003004401d4000e07001075011a41040b40c20442da41b00c40500c141c00c80143c0e11860041c104500114440c15020b500060f4080c2004d0f0038003100d4901036004041050501c0d160450858101035080520100e585000340f08811034013444022501c1401540c0403420490310104044200543c2c0c0c810a800c1441c00340d0799500030380402c104034541040803408448024152000992864855a450580c0c840019004148010b0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 343186717 1250 343185467 343185473
    0x11505071406040609060e0106050603180c06040f08190201051611150909011205030d050907050a03140d140409020313050f1b04020304080a0c02030f0d0302090901090c0903020d 78
    0x75281c0d80c49200c070402c40300c803841d2a041100207403403040c40948400340341c100b08040402060003810241c600140c40549181c44074510416072160b89110346038180070b0480946060b40d2040020001000144402c228443c2021901410240c403603402a0703640344480c24860060760080b00741d0f03214120f0f10880010070a1343c0d084c500c1d1002e4401c00c41c1c650100c00c56450224995010010744282a030a640d4070700680e80701c505151100c03820070390150041d4000d2096145407035058000d03952044014082d11410755468004c1150301c0e80d55002200c00d99081441980708800410000a625460745019005018a0060900c652249020f8240c06035000000203800350164001b848035554094205d83c948482000e44507250301001c82c00f1450f000b031240002245281600a4a0040b50001019403401c12610f006450300c2400200880c1c05d03003c3c0240c2004503180500c41d540000d2090b45000d80d1f100001702c1084900c1105801002c0818540344196811586c000105800d90313a041e50384d80c006a0280c2 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 343187967 1250 343186717 343186733
    0x3050c070902030703090b0f01140d0c0e010605211506090a180c0206010e0601051801020f0a08090a0504060b03040803061201020a1e030e0d140d060e04020a080601150507 75
    0x500801e034034078000010300c5813050381a0701a542c0180110503454164840c4452130011000a21840d14207101c00710103100c1900c0d000c0b031109100c0c0d200e04010304002d9507900c111256001c09134803101c0800c070080b41c1d000d501d094120035001d1850400d40e41c004a450064000c103600340150b265580640b00210f0422119207401094401410001000350614881d86660a02800c6403800709030050055400010381c05400700c04d82802420140c54490800f00c21186061a0520102c000740c11403090101c1142640400e000301941140112040d03a660340500040c082910700c2548014001d500d0860304002c44142c2400340ca82240d8000c144641da13403101c0b0000b0764507025107850104254400545c101d07005400074112108082c00c14400c100c8018400d0b010340c125101d111503502a60060341c000b82030380784148807040d081001c00c1d680d41e04000703d242240088506541100000302c240009200a51902e420054000c1600360002d0007558180048100d102010f84640c20500002044e081c04000c0c1003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 343189217 1250 343187967 343187969
    0xc01170910020d0c0e150f030a0605180114010203091e01030e030408010504020301180b07030c031b0804020a0f0803041a04091806110c0c0f030c0a0806160302130303050c07 76
    0x51001e40d19400c81401e07410040c441107081c41c0c0402c01100d403148143c1410312241b0305d05a04d580d24981411a032061034406544014070038180e0a565180204040e56002e072a44c201002241c030b4002d441d030510f0094020610005901410b560081c0002009991590505580700904c2c015400c8000100801070703002e02034a4445820500000c81c0c041170099055024600c0356008a0092116500074000114080d0700c5a1014261261160000f01214003a401680881045240c0003400b684040c0f040031120341002400c40010f100350040c0002c0d4035044040303038090408260400c46142c1303095082a50327445078ac4150010380d001d0405110005500606450080522040c10b0150311651400401600300d640c200711030541c544107810030001c4915041d0740300c1070384c000010100180b1a00800c880c004400464640c54441d00c41e02e1401e90719040c04040c010940b01009100354249000341902080c5031602070000c0510602c03a019090141000c51421240c0505090b551041c903502010700306902 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 343190467 1250 343189217 343189243
    0x60b030f0f0105060d11010f0903020411040e01140d03110f0102040b0a02190b07180302041112150a03030e0607050601080f0705010504050907030b0303040e0411010906020c011709 79
    0x6200c840302500380c40030071030516240011000304915030724002003050034042c51001404213542c20000b4802c55009400d032000201c5541002e0140551b02e038000f0b02621034a2103141c50096020a0130040c1441c030750034440c090006a000040c5104504011407207403112406c010f010400a9800d000300711400340000d07048030320361000070755945880381d804072a590f111310300810052141c0220b68861680b9040899a0756034003807106259500c03800003c07a01030550210040e541144011b0000060703507244104c15400e0619284152200d00c80444001d0790f5400a004003c10002415110900c1d0b80d0503240100b642c1e81400d10072058008003010035410b020700342d00104503105202c0040341d161030001e0000043e0011400b03c4d402d8580f203a0045030580141d206250304140c40201181c4070724060703000036120450185c101c0e824641c2c1c50420000e1880c0c25a404d83c0c160401d16011641564017030403540103030540b4002010150000c2e00000d04400038080e84450514400d4041451001c041c06020800a4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 343191717 1250 343190467 343190473
    0xb010c20060f0a0c02011e080109020912010216030801060c050a02040f020c060709030b0c070b0a0c03090203030d0c09090504050a120306051e090907050913020a0306050c07020a0506030c0d0207060b03 88
    0x26900c8400303800c0450212042c0d01061142200c2c2c402c01c03031110001f42c0701b80400d559000d1141d04c0c101104029410260b462944086100721881c40c1031006d201900c0c000300d0f40c9501d0404e04a450601400c11003040e0400010008203100203c0426800034008864681c140d800082469080d014800203010304842030241d802a142444542c0e50f1280b91103080e01d00456916680b9128003040c0113440c812400c001b0300034030060000900701d0040343c2c0400c40e10800383c200403c1142c01c503400641960700074982080459505c122400e074041c0d11840d18806004203c100704000d080c1900c0b040e940d00c980c010000d240c0741070b201e0f41d0404a13105c1d0700000003c000103802601001aa401042450740503110600e000d48050800501107110004119080ba10050301200036911088014043c04856240998000d888003000200003201c510400e4031444c8104009a140e07245441000701500712a4400c0c2d100d03031014014170005400d11011074401d005c09250041ea54070301441c04802401d8040b20b0b80303a00d40 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 343192967 1250 343191717 343191727
    0x206030103050a02090c090a03060915110a080a060605070807020f04021b1204031a07020f03040b0403050f010603080a030239060f0c0904020a0e0405090708010b010c20060f 76
    0x1000c00143d0243c4980f00b2294900070383d07585000b04000d405034201c0f160f4050840c0000b0004a051584000ca0b4640200c070f420100c98846058803096520b0000a0081000c000070000ca00644c070010480e0000420501480700c1403510000409a004510000d080035200040309000c5540d50068a802c0f01d0740a4130654940070300340d001c02140c5440380091502805610240c080304042201101c003680d41c040b00b141d9441c5601c4004c84aa003400400e8401944102003d030010b5032001c201502c010422a030346260355506500e44503040603031403256140030b6030502500b0300010b038600f002c2c0e851410342841e0060715a208040c0002a0268540f402114443d0000c06c1d41444061860031607444c0455508447c0b9030348071081801402041251030380b80403c0d00f80101d110600e400e80050090700000c1c580b14042200c4040003c0c1120829104512654130a481c01c0002010a00404020a0003400d0003284114103440351002030081c1d000f01104400d000d042c0d22596074a61040d5074500040c81c40da0f503210 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 343194217 1250 343192967 343192973
    0x4211e05091804020918100203040c050a15080a020a03060906030b04061b09090f06031b030c080c0108011a070b070509030114010b07030e040e0d02100e0105071e0207030206030103 79
    0xe9801041c41d10b000700c0480b03480e4003020400e020602d0265a0140c4103480a50300d0000c407080b880c900010584c00c600480c0740c14200102140040c7d8000d03406660b491403070900d00010003c180e82640e00000f414080e40280c10310325504070300307041d500801900c005039403503008200440051000fa08040081443c005000c001d0010b200300301445180304500c00c102c118000380900d2080305802d0050f600040e00e0701030503c80014290001041040449008070303909490355504054080c030034100500c1d2044106040041c4407040407a10000c210f40006050f194100390300081c40c0340c80500403922100d00002d45d44240b185001d0450781640c0c1c107ca421061800c0c40700001700703254400b20300307a4400d40c02d0045d14102d500207002034a0407200701c1100d0524181e103a41d03055485a414205446d8070a540300000185c1c410300740050b5a032241d40703601400c603a802c0b8000c00c0c1d046980e803030000241689004108140c980c1c01c40c80f1a89503e82c2400c07100303032100e40d91030200e19000b1660402034101201000000030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 343195467 1250 343194217 343194227
    0x1a150306030c0402120a09020a150807020c0a0503122a07061106071704050c03250e0c03070c26040513051012050c031e1504211e 57
    0x840d011001d44541e10880820441039005501e40198180c02c144013155107001180e02c078510151019204a444c240d503480b100e03481003071800c800f00104401004100101d5414411075105070001ca17030300580141004042591680c9051246000c8200021904000201a402004e02c1c20f900c00e50b02000c0d02086441c1c64488030f0b1440703030030045805080102e5071110042805032042d90650356205880081060035440c020001c0c00a0780c040c0035a00c2800f0458401303014480d030401c00d510500b03000c00000c03544014a85407940c091800c0303900740410321900300c10751400c03690406c1013403a010030f40007440e007040498440b040c8014060424a0746500309940605800b501c01c07070b00110303540c4042c280036030208025910104ea403245082d006090901084901141c00b29100d802041103410b9100f015020030300d410105541c5503104038005050240c130400c100f00d07107465144190301900c0c140c00d060340c074410013000f02500700d615407850805500080b44900d0f07103401110b40d07003c00d640440c18500000f900c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 343196717 1250 343195467 343195471
    0xb040f06031401050f130816030306050112151707090501140a080c0a0b0c010b0a0f03021c2001030b030a030305040507140105041206110408060106020106091a041a1503 74
    0x240020803150b2402142e8418031440d84035102c0b202c0380b103486035600c0d00c04100e0000c00110807100005c05108294051070f50005104400d40310340c8001861a041c10005080b602081c00102c0d00e4904007035054282d0101000b0080468185903607a04821498030380e02d40c14483c10750407000040385440000035440514940c085001c01c410345000c1c03445d58403040074640301c0381c0d480303007190300507001d49410048185d0b05402005001024400040d0350300c18080000d10440c0140e00251003045500e2080c4254504020021413501c0c2541103464030021030b56900c5158242c035040c1c0a02e4020981000c00d41e64025040982503010003019201403100c5444c010b0002d000a540640d0f542c444c1600c08211029110784898210005171112030820340f03007410103414501c0001040f6507040c0c444100081140f510b601810190007084003510340c56040c10310090848640380d01c584079031401d181c0700038403d0614500c2c1c0d00d16503034103a0f8003040c410f0b0380d00b0041720f5075a81140c140742c102541140185a205a03900914 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 343197967 1250 343196717 343196723
    0x6040c031a0907050c010c030209120106050901060302030903190c050d02010b03031e0d050c041e0e061c0213020d060503030a0906121b12050a140109020d0b040f0603 73
    0x14442506408404a902503010100c850094a003a0301040ca0054003080c1d110000780b40c200d150640b00b4140509640075000250302003500814140d60701c1c41d00c0d006100e05640302200030401245000f0003d03a1100045c0714031020306a0000c0421072440c03051044522040c4007040c0c81c00c1c07009650034001c0805160000607601800f40e00c01c00d0341014818001c052120708020010360518400c0e80580500741c00302c90903040306100c2000260702140d010301801d48a000008445601c0b18540324078081018202d0f00e03d400ca81844450500541542c1800c1d550080c3d000e5540710900101c862410069040b501e40203540705200540444214060b0740041042c01c2ca01401803001c642c0e182d003413655074011041010080f81785d502060005034442e0600141172a03c0000205041c468401c5540c0a00c040003c001c0010b102110721041543c80c034021150003071481c250800504101004e6500344c10f0b8180035522065400040780003920080d0707040840d10443c010820080281035a415400401d102e120072 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 343199217 1250 343197967 343197971
    0x22060e1206090304090b030f0f151e0a0908070219080d111b1906032901090501121104080625020a06090f05030a02010b090c07020a180908030f0604 65
    0x512580031001c1081800780010748001c1d401c10b41030801c0344020b82410328805802d8400c1412143d14104100000d034030480782c19010b400b0007103e14100002540c8028440000960401480000641071003202944118121400903000c01d03103103002d000354800c03028040d52040c02101b80880206c1ca031101401203c46400c101c07800010701300d1003500e6014804c50068802c2d004a40c41d44000008440600d84801c1c00412102040255691801a5180907001000040d03a01ca0609812150f00b158524010a650051561400e80000002c0c01d49038540500c50420840022901c81d0089980140c501035038203103501c5450b00c3d1225819641c0c3c00b800c80f0300101300054500f61700c0466501e0780e2031152100d01e607070251071007004a40301c18000e0105103200b111400100094007000c01d00900c0074008125690b800411f03540301c0081004890302001c0c0140301000801c02a150050350b0308816542101d11a1440d020008041e1803940010881400c014020030000400c20464101c000b0055100d07542c11201 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 343200467 1250 343199217 343199239
    0x13030c080d05070e0109091a060309072628060f0e0d2604020a091e0207081305010e100806060c0a0c06020d0512040201110c040e0f120a080c22060e 65
    0x80205a960107050091105695612344c8140d0070040010355002c5055003c880705603940d810480e03041480d80707102409246004404914580051140110000c204940c2503118092002c4035048a61000001807200740c0d14100521021869041500701e501400d06607000000f502c040038104c02c50041e51100d080a0f125070106c658074103038208a0049802400c135900301c42c00c220702c10004000041100d5030030072140034801070010441c00108200e520550501e40c603140e2a05510600d01400d410090510401040c10186500c9003a0346007509820740c50000c0143d150640410650700c14514442c2c3d1038018582614207105d25100804210350b0541e08a802c89003220608807a24091500d11494107060400458050f62240515461490035230040d5007550300c05000040803210381c0c1c604240c8503044000010001030090012180411030199502d2030806991402403840200074140c100391000840c00c602d200d40d40303c22150307811494069001f41a6201c03000540700811034107a41d80315405101e6 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 343201717 1250 343200467 343200479
    0x607020d09081207080a0e090420040905060a15080d050403170c0c01030905010f06030c0617150d0f05030304061b030e0c2403010f031a13030c080d05070e0109 70
    0xa810030910390075007000d03404c0107401c1d590340680b40e018540c5001000352130358002c0f802d0360340c80c035106002d1842400c0da465200b00307400d61440161005003105126078074120000340030500c0824040c0d070003a2540790002c0c10690040b207020405260b90030440306031280c20091074406130480700510070782e03010b40e4804038040d070703410700e0040248a00c00c83c0c04030b190410741403818194004c0e013015030a1449980042107205906049008541d220741c07040e03500340c440e0001001800e030000d102c20200c440110220601d446c14ad455039095041c4210030600441802505000740500c5904030b4800c540d001095aa6a0400d403d000010301950009010b0040b100141900e085000c6d10407810b0b200d900401400c2020001c4040250811100c034078070031700ca2400500c001512840000650181120700c295042960070f60410340c840072044542035056a0b00c100601c0710010702c03140a82801e545c1450301b02c1c0600346910300301c1c0980c0a60b0529281085c2044103012090341c100602c03204103030302070380c41c00b03c295074a10f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 343202967 1250 343201717 343201723
    0x100e120c010507080f040f023106210c0e10050d0303050402180621070f17070506090303030406051b0705060702061612200f1e0403020117040c03050607020d0908 71
    0x950001c100c00c18a10b1f04000500f01030304030b10702510000110082c1090925800c1710000003905034820041d41d5804240600e8400c844113408d1a02d1464040303980c115a6900c11014034024082c80d50450b48000010b202c1000d145120f80207808082c00c40d130151007040c5000743c0500402c0d90708034031800f00c0311503a880220710f01d200b076442100e000b0000b40c1440a9100109503402240442450a025900010800461042d90a4010b25410680498100d00c110190341407011507002039100f20000c011411540e600001526041500081c0004041e241d4009407034502d07941c0f20000034455804180f070800e100020888034480c08054007621582d6941c04162801c0400c51201d0801240c409001d000340e007180340c0d02c132320308201c940344c40c1c4c0e130314245540807100e515005840c03240302016002428541c401c2e030240c9145004c001d07a64000e8101411503001820030350b01c4604003c90702e801640000e00307010034880014019138014068072400e091201c0000d4035034100c07111000c08200c41d5040011a04000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 343204217 1250 343202967 343202971
    0x51b06040809040b0d1e0515011203080705040e0c0403050d08090303160e03160810020f04090902240d0c09030c150909060b1308030309100e120c010507080f 69
    0x7859076141410080403c070003029500720f0700e0b070005c0401281200240300e05c141030141502803040130811306141e1030102e00c0c050354034000307141e80c40c05540104000780c082107012582c2c55140c1000c400c0b940c0e0307100b0300b11000d0080c4d9100e85489a600c1d0144098410b0321402042507038002c800755104417102d108166201d02096420806c02d9104000080c420541d84080c1040100315140c0244800403403400241f42140c19402c05502c0c1d4103010041140c2202002078a440300c000c0182542404080480249180036910500e17000b56100c3c1c0c1c9030360465403072400320342e1000c010074042c0484c00590700780a912034019080302d21126152400c4142e80502500d00442141e43c0039503100261401c1c0000d20a142072109500070510550880c00b02e09291640900c0014124a180c4151144059610045104402e620810f0580c104000344160a040030482c0c0803803290f500c402140d0710700d0703902c3e0203441d0002541d040682e88002207001c240c810300c190040c034000c0800d6030b180002611000c070300700854442 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 343205467 1250 343204217 343204223
    0x20a090c0c060f0207060e01020d05091c0806040b030a050616170402060a1803060902010210140a0c02250e010906080a030c03050d06030506180102040807140a0b0a051b0604 76
    0x71101082000495a03008a480103941c01c42c05418200c1c0c1e9518070080d610040d01000c0c890b500030032540740b0407800e44135050b4000303440001403403030300fa5401c000c400350004001007034200071504001480a460b0340d040060000005412075003510503d05103245c40700c40648400c070044c0701d4101c0c01d49003103101320b605228121421034142000c0d1a942e01700000366024000305411700a55401c20076425401d449040d0085000b0040442c80c802c80e84002030411004c107000d4000c4515140211001c5a9074810003540310070101c00004540e44080e00c282c0c40c100d8070410b050000d480d698040d4100c0c3c400c81c00c152007181c14541040e103160740c9640d40030f402e40b109400f8607080c947c003800304400070174419020406294000e05080b46420b039150315800030b84d5900d410a80341c0e076005000380024020015540d04084000000071410075044c4024540c40d044144144400000d415000500507603406404400608403c049c55541381e1000c100a000398002c0ca8502100440982f02528400c2012855034820b0364 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 343206717 1250 343205467 343205477
    0x15060c0b0705091302180d1202010b0402070b060d02030c04020d020901020709020a0c080f070b1008190201091406040b0301120507060903030203030a021b102f0301030204021e07030c020a090c 84
    0x14184c52007a00940141224400040d19280d02e4041a143c8040c4424101d00404402c03043e886d0300da50180c00c3d02e032609001400f55104201d041c0100d40d83c101c0590300180103c0e4035624041c46030001074540b851504002e0380c402d00c0003480240041c10380e8010400e040d820780075100b10f259645000c0d400c9008a000d0302010030340e26124280040e640b02c0051100251110b00103040c00c1290b200c54511003400c881f856031001411030240300da05000c000000407240d003010380300e54494480e400200300742035a00c11003040c1f0440c0800035059543c1c000039280503140150540f45c032907949210303c00989a0114068420b401042400300d041c521a0090405407a00364008600c0c686843d182d004c020b41c00041031668016002c80201c040703a2082c8003258804142a0020590203194a0940e500f00420401d80015043c44255400717912081815207045980483d80144c440c0d80d0001c5130078881181d11103404040800056110030160001441c4007030900035280030003055110038002c0c04480d0b8207d45100420 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 343207967 1250 343206717 343206739
    0x10e0303040b03011403071d0f010e04050705090c090d0b01140a0f1401030e03221509030b0c13120b15010c020f03030c0109080903010506011e0302030a15060c0b070509 74
    0x2104030078000040401908441c56240d0b40c07039800c251400202074404234114100c05220a074862045039a000d04030300c4100c50a28200303941c0ba01d030741d8107187c46680e000e11040e100207007180c4040c405840301c1c00d01c041d10484082903d80f904241c111000d01900c80e6202c81002041c99905002c080d4000707451424007e82030143c14109002ca4135002d28550f5810540c42c0c0980d05a40c08080c000b03808801c0003e03403025400c02007411903480c0380b0303a60781103400650b442400401c0255400904001125000b5840311955207030f80540100d58440ca4038004402c4035100c00006080d035000032000c000901480205003d130f220140b03100503c1000b41031840c0000c1180c600c1402500d0400500c20b03030707090f00030b08903031416040c60056425940010f40c142c1e03c07100c0105041e0385508013800b900d64040e10074030302020402924820042c0061031a0030f03031000c2650110025402c3c0f100b44d4840440e0408482d030303607110306030384200081102036400d02c00c80c0c1406080c404a0640c1c1d0190003910095540181124000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 343209217 1250 343207967 343207979
    0x1b0c0a14120406030b03100603110a14060a030510080307050f10061a090a0f15020c040506150706020702040908090f0d11130b041a190501050f09040f1a010e0303040b0301 75
    0x75040040c2c5e80b5078036008203042d44908940d107101e1540118840d1480c550080c19120812450b640c1036403001e40c1c40d4665410724001035503920b0441c1c480321094140003c4c5c5840d880f188407000100d50700aa90305101c0040c40809000300091100030143c0050200c3c0c200190406481d42a01c40d00c0c0f04440e11200c0e0b00a000802481020107008941c0018104403221039444131007208094103680582d5041d00f0306020303200c5d055814810034804070002c2d02e050149003000d002140b0320344103500c078058481e03c01042d803a003040104d4044500c1c1e5038000b0424854201d060800286a502c40160b15106442c00c110034071a505200c4031504039540c218000c200500c020f075003031080385540c4000075131526503503101c54489980e841c810040e140b51550b142003940d440050170303c101252484011040c049204104000c50f0380e1001c03c44413605c00005806845082d901c01050207814030305600441141007002c0300c120340c80b040e4590751000d01c0c240e0b81e40160b00248001d054483c0725a0149828030541000107100c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 343210467 1250 343209217 343209221
    0x110a0615140604050f041b110d021513020d050109060204360f09170d050705120114010e03011a130204050d060203040c0f03050a0b010f05060a081b0c0a1412040603 72
    0x2240c00140c03000c5803044120041c600041207c0700040c4c0414204580c0d00c074500020071842030000c265000914002070040044264244010b00c410050740c0d80900c00411900c44503282c00e58154022b000740b048100728030304000a500a4012a516050311000900310494021130300c18410b0480c81094a4a03000313110074001911509109284180d1a2126600090305440030f0f681445260703001e00e81c907100f02200180507564058800010000280f05c4c40c665801d40b840950704503602c4258100c40c103829031005130390204000302020f9040d481c02002900240b003030800480c0c420030448003405100805d1080798100e0040380602d0343c008a50a8906000941c0e55004540290103600d800705520703903417201d00800c400325400448183c1c00c10602e0204100e1039084042c05012081905220b443c1008081180c0d4042c60f000b44c002c00c8001c1010800d100071540034105240711001c222a525207a100e81240d440008000884217224180d51121b00e408010078484020880030000b10305e00f41c945a03003100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 343211717 1250 343210467 343210489
    0x50a0c0b180f01020414010905100516080c1605060a02070e0901110a0f0801060815100306080304090204050a1401171015030606030b031615110a061514060405 70
    0x1101c036416042901c0d008010000d002d2908080300025a80d5404c0c2442041d03d01100c00c00c0c281031150424061116581c0d012214051080c0d5107085ca4503032502a00030400d00201101c054507800c00003808100300c100204540d14445400c0070000d0a250b0355000348107451103541000d00c0160020340c0305102d4401c2d1515404e0300110210000304181e09000f04044440d8800440000420071800144c5d0702c0e50340110a0f030380106100d0400203503030b181000e80c200e01c0c82d00840040d4400e444040d48240c0407030203584544042d10f522030880e83c4550300d07061010001c1d80240903081c441c00c01c0c01170000780e071003191010424801c0181c1d903030510008501d00011114901030a542041c01e92240040341d0a1030504030a8170800c100d03034000c903900b440d029003d801c80b031080b925039010707400c6110301c1c000524110301c00c0c20480c1d010743d5041c0103042280d00d085030001441081c1000300e021b983c02420602450340c0101c2c0c98031548109007400d07655660300b81d29010940f00e0b045a008030040c00b04000c40d00c0c00d880d07044 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 343212967 1250 343211717 343211731
    0x70c08031f080f01060617061302030c0c010507050d2922111c0203091b0406030206040b130807030c0b030c0904020313060c05070b06210d020f0d050a0c0b 68
    0x28820b03203440420f0b040c802072040b5a030050b9500c1d2810058554012001055158004044030306818600080751400540c1c2c084901210340000c0441c0042c460030040741c0100d030420000704010b0414450043c2240d02c004ca19000d95030078907648180c01d00448281c40c4907030601e80c16070420b05110006120712840101100d003840c1610322944801c1101c5806104d101000000b80c06a480d4111030b80c40c03030641001c1502e0000f440c418410000c40880c0000c01254440300e513110000c01c0c055450006020b807426410080d00700b41c0100300010403a50f504094560000303900340140c6802c2c1c86820f403030f039200c03030b103101c050001741c900d07170003005000c0303814005503000344600840a2030045c140c8041001e0764010740702e00031880c400c1003a9405002140c414074100200d0b0346042c0c2c1c0307040300d130381c51b1502c101001a0900e44180d0080806428075654070380912801e60140b070603a00c030001c582602a484900144280c0d28900410112144192088045490b10b08454442038411001d6442d80300070940000c10790 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 343214217 1250 343212967 343213021
    0x150601020f151015080601090603020a170c0f0c0309090915070c1b031101020c060913050a061e1e12080c0f0708030d0f06031e0602070b1608070c0803 66
    0x10920b071498444d468098501910f80c0402820844001840d00d105507002100301803060080c80344c1c3e80ea00c032940c520b0811911480d030300e00342c45003100c000702032143c030f0340c400712410380013401040e80040840602401e100807201d80350360f40e80f400082d5884580c280300c034440c0250b40300e00041d40f460041280d000014002d160419100080c032403081c01180c3c11f40c009172441e01c2c3c1c04208080f0766a04014a102c82601940c040d41055407400c0072030112240000c404803420340b5400020f8000995a200000511129505820050220020006ca1030b403a015180c4043c4030099200150690f8400440072071308034001060320314030591034404564111100305a1a80162407034103c0d40e003c00c2100d1000307072030880061580c400080318003900304c99184010190850401c00104040b820300c4010050884046d150007207510350f14034152000b4403a034400102588001000d100d00750308a00c418445814503078880c14106d40b80d90074203854581a01c0801040070404000090060102038203122108000d4080 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 343215467 1250 343214217 343214219
    0x3090f0b090d2a180c050f0d0e0105270111070f020d021801080c0102011a010806221a010e0307060e0102101109030601170a030c03110f150601020f1510 67
    0x40208000500341c0100f40302000740c0d402d0052a0040c15015481803602d581000298141e100141c4140510b10005091080c04208840c44541d603403c160041c1004000800c051701d01441d21010652818400702145c40740d1443d2101181014401c40d1441c1c210780742241e041280c0d03580da05076040b003080400c80e0888504080d03800141c441103500230044040d0100340f5003a60501940c07620f410a201c400a046a0504602c507505140b0003040d040846030a1904030020341d2007001084200049045107050141d4008a000c00d02d40554820f030034030120480e0105c41d0358103e4004480705442c0a04803540b607000b101040112a003e0603072104010410b0041c1c880c0c643c111001e40040f108284200d1140100000ba441001e14040c040c081c05400b1201d0b82e00c818010162459070388420240004050002d4540c0503012f050040500c80038074210202221240903a08881545a4411071403411310040d440c008200198004030705040c0d03100c1080d000704040e020140c5003070704c10319001d004d2101d4031440501c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 343216717 1250 343215467 343215503
    0xc050f04091a041203141602070e0403030b190b03160306051201020405041805070e0901020d020c15070e060f03041a070c030e03160b030421090303090f0b090d 70
    0x240a8410350640354204a0794034050404904c070703907100c203040e03810140b4217506010b800c1c40318602c483e040f8548a5100f880702d000810181d00e850307405d401c0f0258903101501080300301039054010701c04401e01680d650745601c03500410050b80c403100780505000381e8020300010320140042c0b1250b40c3c924482c0d00d000300742995034101041401c5c007100300025003650002001c1c4000c1c2068000c0c020340451030006001140c803079071207598403000c1030701907000f000b494040030030440802501600c64145c19060115911440c920f103c03030f43c4040c03145603030131103203014030010b40c4480c010701c81c0002c3c0780d070081c200c0d524000e00e90207491a07079403004208540010082c000f040700c88410200d03451140080c0d407164501140541000340038409803080191196115036203080481c040380c00403408480300b031824140c40f5111032a284000304001580400040000207000000c16030040c0701c141164002c0d21440300242c2c5501e007410030450715000c0c0b41c42a1034100500902c0d41480029264107070f00514500003a411608 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 343217967 1250 343216717 343216733
    0x1403060603040813050913061a010206070807020c100f0f0801060e0f0310050a050702060c13120203031207020d09080102070809010f0507060e1507080f010303080705130e0417070c050f0409 83
    0x1f5401c1e8802025201080082105134810081d280c40c0c4104a50f90b52802140000d50300d52000f080c00080000080120710110300030440398800700d10003000d41c04046507040c4c0041041910003510702c0001c1c0190004d55029004405031030589402c1d030340d00b8260b4290300d07040c0300001200011550700f506c51030000f12880c0b2010b11906000302181c0b007010806041800c0c00a141c040098004140180100928484c800150360b5050407506600104060395106000003429070103058000f07680440708608000441d40d0100784286240e901d40c0f12001415201c1d0421400c07030040410080041c0001c2086651540c0a5107414a0a050318030b021440d15089987d4101651250082261117038131101c0ba0140028500d409194400c500d860107450703074076149c0340d05040d0403030601c0050b0921980b1808a8207080c4134004403034020b0020250b07003421940e04c0c401943d1010701102c06807072000a1000000d0210003d5088030b4000c0e0304940140d0805d4281010090b048610101603a4481d0780d440410700040d28003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 343219217 1250 343217967 343217971
    0x915050f03010311190627051002100c2309030c061606050705091309080c07060c14010507020607110309100203070312020c1f0605090c0a14030606030408130509 71
    0x143d8442013149440380c09111117600d100c21501d00b5495240c2d414081250f120140a40a40201c2190162003903651440c035008885900459000851310a403028401c0d00050323103403040301c4000c00c20000003010480484c2c0d8041a0b8070f64254100c0f152401d403514844110151414007001425901750030350141c002880365200c6080840455a006820814450140700315507020034141802c7e0f00e800500b500180d2035255403000168040c0d580c0c01c02c0000e200a0348103440d201c0b00f094080340e880d0307501ca48000e04444001d12040b2801c0c2c0f0300203558100b12206009840c003801c500d4004100d10b8549080c00c0d60141d10140040440307200c24440c80010b80d40b642c107071340710784500c60f009140c0e40d80c0141002040c448004c2040800300b401049a180f00a2000a81c040301c0552b10b0181b1110030410104200074081035801035601030501014021035000b0300000300071082098a0300381c00300005a5140d5128007084402c03a43c496001e200250114175604024190070302c1c0c105140b03201d03548074000200c9034002 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 343220467 1250 343219217 343219223
    0x71b0f06021c0c0f0507050a0902091309050a0311030f03010608010608090a080d021605071d07080405070509060d050f070f0605040503060601180b030903280915050f030103 76
    0x1440410820141c040c0030002e0540e4020050ba0a101d4220001400744150440d0042081c02819444030501105202503005040000c0c6003030348141d51001458041c3d0401c00c21184600c8030105c038800b001784a440b6044011354840f01402000d015502d090703601a0180b440c04078a40270401410380300ca0800d60065003c1c10441d102e21b40154188500100203407001801080c980e801003a049010401c7c880c151510601070300e0b00542c0e5048a694004082140504011b010381303d0384c0310100d030a883d040d1054485000700107510b41503507525041240c60b240d055401501a4000b3345080c0034038208039858a501940141a10300103880503603580d483c0421680413920550405e1400307100c44621910341c01c005181d41d01c0c050b8101814100040d88502020300514140700800300030b60148650b0550309401010881c3e1040c2d12850507221890b101e07404003819000c035510010984000d462400040c0f0402940303941c03035031151070901c070b40c0b0035004d403102030120244003080c00424940c600d42002103000e144 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 343221717 1250 343220467 343220489
    0xb0304030504080d052110092408010509120708070803061c0c080c1e040f0e0f0325050606040c111b0315011a070c0302130b0a0f080a0206071b 63
    0x61600d46c10002ca0362014260045801c4604c00c4c0f0403a600a42aa0b42c26102a00300c0001c03003440394030704110319010055280641400a0100041d4401c0c1944078034410760b0260180c81c1d049076444421911481666002000c1801c180131160103c0c0401c0007961703011202910300100b142c2c007064003100540e90310b84100c46401c0d2130030082c4100201032019141c090001d42e10710065800000c1c1c554520803816801c180141e94039000b050704d40400390450090b0340c08c4c00c815201d0b2441c004420a0b101e504c500d9442c0c0c015003000307000341c00154415801165158001c0050301c3c16445210412000d0540501200200903c46040c2c101c0f88000344021041d00c0c03800442c400e400700e150340a060a00c2d22501c1020000340392600100b01580c02c084042070020010746039280d440646140240302148590006900034403e10410400c0340115441454681c10444600200f9503aa034a404a01440d600900f46d0f50340001e81d1210042c14100d01410840340304500c0d80392004901000f5101a907169480100d14032 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 343222967 1250 343221717 343221727
    0x305040b0a0e151e03090709090c050a150912021503040f02040c020c0f100e01050703090e1005040f0c02210906030f04120207030201020a030c030e04050a0e010b0102070509010b0304030504080d05 86
    0xf041168000140300184e802107421031a103005190788030440c0e40300710f000f000c1d200c4c1000340401a00d004040007500008051a41498440303030300d010710710661422040071900198010400c400000c000c4a6400c0d03000b0800300c01c03206c80e041455813580015200b1903031481c0c0d40120400590b590f0140140e1000f46078010030380c0c0240070b0200a10707034048201d0703607024014040255000d50380c0007104640c105803c1c01c02c90781c2c486141ca800c50b4124120760024040401c041c3c00c0c1b10b180305040341421308441c0101c60038041c05a60300080b030200d89165100001503400389002e8110b00c5c5415980c01030400c000f800311414001c0c420081006680700722800f203034802c8604200030801558040d416000c4441c0c1c4000c04600e806e42e07001079928000c0400160600c003683d4142810941326501c008880b0383c02034000d1000307041c03010f45240504250b1500e8205542803240018455200041c4881284e40c020310040842c0d290200c40d0080e43e001520a4040040400c000b2400801c1040200701440c8a03a688036034907 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 343224217 1250 343222967 343222987
    0xc0a03020609070504060807140d060e0601030b06011d040b0406030606030b0a061502060601030b120d1e1403190b10050408070605070201080411010201240e07030501030305040b0a0e15 81
    0x403900f140c0086118130319081d014010f10350005400c0301501da5541c1d1440c0100503840002c0d00310154410000c0000b402c203804407000c524041400f41c101e0388a840d024459880e150b0054800255000043d01125019101c5248601e401d411648500501500009034141c513515010b0507901250010342e0b01c00410f005100b0b94901c43d1080720b0040401c040c034004004201d010003519198080c000d1070401d9111500305045554070706441b0740c0d480d00c0f04103c8118070701281e0003812408a00d03180780295400200b16445041c050103080009070000305201f4556651942082d182c1110072004c1e5900965441d01150f45440702644103800c00096260301d80c8840c6003148003031504040fa0440010804103010000060b604030b10300d560425440075000c1c04040364540100c0c0140070204020341c882010204522040e0f0030446817074160f407002c028642d00c6a40396842542614020700c002000148100701c02c0186080400107005071302c0fa0791410004401c016000261900c041c0300c40000c4444e800a103441031 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 343225467 1250 343224217 343224223
    0x5040513021e030613060305150609010807030308040501230411010203090603040b2a090f040b21100c09090b0906130c140d02070506010b0301030f03050f0c0a03020609 74
    0x400119a5040d442d14401d01007030394105491518103000898040041081650b0b0691a25400e07640800d04121465a90901d507644e111050381054a25148001040c01800c01180c124140c4501e640240509481e582d4100c4085e00f00400c1590b41c0c0d5600d40102e4078001d417a4009942c003a011807050760540c1068107104004429801003030341554020401c0c07405d80e81344d40040d203510070780100e8096107640e914002c0007410880c07603900b04403100c0b19588400740c0c00711007006480080c2013640d0bc02e0300300c3c10100c00d100498046250b62a402800c1400484613241d1000902e4425061a8140e47c1040920030380c10b8141c480d12440c0d880445e030002010b0203000d500e07204503c01c0410031100c0d2911400e144000c40c00805440002c869103503101c90100391150b0040000c041c180e6403d102c1c02d96511800c0d468100290800329044a03d40a00000001c0c01803034102500e060380d801803445c40c50034050341c0c4c0c01d41d00c65204441d10f02c0c00305010311816041102c1805000501030080d000b030000b40c41d107850b600341 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 343226717 1250 343225467 343225489
    0xa0b07060212180d030905150403020a0b010305011e09020a09022101240509010e041d071205010e0a05060609070e130c0806150f07020103021312030905040b09060108071e050405 78
    0x130816241c1032007200072030740c00070343c1803207002a1040801d2280c4907814100e080400b0050040c110301a0003000100b0400d055004c05000406501030306e0000710b000390742d40151030b03a10401940c0580c2c81070050002281d150700410f10030f8060307200b000390640d0b04011107654850990100c40d9004030f40b04403584580701d000c0b10080d1256039180c810724150f40c040010703110041000c5c99a01941d80d5000080d40c01c00d008a01409180d608801ca4903056601c0820130b4101c044614200c90700c0d400c15180d05201840013584011403035002000d054160345000a0080301c24004003668200195180c1070b0109884002c4404d01c0c2c0d060303455010501c00d507825000780c4900c4003d402d00307000700224407408092000300001c0d80c4190100000031560fa500a0004070040d024582d200e0300610060f910000c1d4402c2c0410070318070740070300c26113078444401c0c2c0d240b041000700d850070300c11a5080300035100003821640c030070b000f0250700620034207126080c1c1c040e0041e02128000d810f817028000c40e03c0050140040d00d44144029 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 343227967 1250 343226717 343226743
    0x303060302010e0402070b040f26040306060b0412030309110d030305060f0a0b120a11030c04060f050a0e0f0d060c050c160501020a080a09032f0f0a0b0706021218 71
    0x1d440c6c08031b5540c900740614402000030784002c000c0250030f030400c03400038513200b01100300c154080a80140a0006181e550291200b00d80c55032500400007208030f03600d03040ea800c4a01c0c0f251404500025601c054000d051846021582c1c200e42c4000071003559103030a90039440728040e513000a283c0c0f509034280404005180400b43c1709172103850b402c001c0c0c10120401c58201e00d080308042c809540701c034a481c80262561010440c0480c501100308800340000030094400c844c076654601307440302e8107680d05881c9c2e44210203006000498064844440d0305015000c034107180c1c0090b0038100402c2050712210104c3e18100804c1d0001600011660300980041125079404030522440d555550300d80f0300080c0d6140c144120040c189000804c210742c802c1e0151407035400550f046a80c100100d4014103007088800025810700010030341040d81c2d2080d0b818807000399550181c014201094042c10803081c1165504030312400c40b079183c3c08103c00e00104984070030803402030032113091103017080462003445c50030401075071296 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 343229217 1250 343227967 343227971
    0xc03080d09140109150b01120c02150a020313060207141002090a08010b1f2001060303031406130522080301090b060c070e102705060d1709040212040303060302010e04 73
    0x29002040091200170290440020005808030748003005030f070350820b4801e141c18414504803048540d0303500424810304040d55041004e0403070345c80f0f42249049001c1901c004a9101c0188004800184180d004142040c0266150b04030300707900201072450700002c40c01602a5030340204103681507042000d814000350915030000c0c01034040080204880c0384076410802c03150500004444c140e6400760900400460241c0e0107440d0210902003654040c1c009840304030f000a140030180d140c4441e6141055000ba8070007807000380c000d05c41031103550141501604200c0c0304044544024483c1195901c2212607600c2000060703101e601d0000204111607151000d035003d100b08000c903045010003c5104801e850110760004025180e00070780c6201c98495800c000c46580f5a03d210100003012101d001c081d0040f8004244002d56990050254601919900406401585104148080400002c0c00801c60301030001400c0101004412502540560702580481d0707036168240150b503444000c404e0a50300664003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 343230467 1250 343229217 343229231
    0xd0f11010c0b510f0603041109070c051c1101020d0f050a050c040312050d11070203012a0305130c0605030403090b04030803060907030b091e130b01060c0c03080d091401 74
    0x1c40b42840401410a0080700c0c02208588084c0c3e1086000b40850b200034107100d03283d2400740703040d00960703141940e4144980300410004103400d10690010f03980c1ca6210000c1c1002c01e042c2121511410684c0340d054048c090030f80300e1040d84200074409403030f0104404d5400305240c500101c104040300c00151004413094140340070032400794659800c4a0071aa88130000d0380040c803005c40c040304c481c0615200b00c0741944c01d04080d01e00500d9600e002e003407203500031002040079004c5d0401c2500c000880c445400540c000402200603014041e501c0345901070503513400c00ca000d05840d5110281003140da004940491004001d020600d039002c0d00c480080c294403180c01d440d06045841d4805180001001e0300d102c1d080020000388a64402d0b00f0411040c0405400741d0740d203003450818000311410703c0a40b25044040c032400200741000103031680030311a800000341407099080c031104403140100c085065540e006140d00000014840d00d005090b0365448440008a40c0203920b0600c070f02071160f000c880341a07814612 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 343231717 1250 343230467 343230571
    0xf08030c0703120210090c140328050c03030d0e0d0801080c060f070c080c1e0607060509120706050105121501090b150f09030c0d0f11010c0b 62
    0xa000080d650007903400601a84100340c101c1c038145c504803420b80101d007000036503003c100480c002d40040d01d941c0e600000704d103480c00c000e1658400e88035446100c0030030301c41c14102c4801d000c0101a54110300540c260f400451222000ca480d642c899420009500e590300602c060314882030029100444d440e1400310082d5150411030b81e80e130f100e00595103114800000d255402d21040208482c0019440268071142968410f200c0d500c494409406034050b00e0298030f17a51740540c0c05080b102d603640000f0502d0b030410741146c40702d0004100042401e0345510580388074840610004014107121445840702240c0c5d50304000034404032108803404176115606c90009501d10303032850704055056410000c0000b0701880f4090000d1400d50000c82002121000010008a0081c0d1784c001084800c2c820f0b4200c0d00620402800d20403500c8030003801030220005040c843c000211141203961202d001450080300d045000d840700c5000c2801034442111412071001202540450117503401da50708182900300034680c1c1a90 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 343232967 1250 343231717 343231723
    0x1506050904034d0601050105070f0b040f170c1b060a080901020d1107260403080307050f03011d0c0c0c090910020301151e090b0912160f08030c 63
    0x1110480c002800c400b03c034090043d90f001c021025043d00c44400091015403e507070f00210091541c3c0300b194000c100022409501034800c40d04402e45c0201c2141d500102511403001520001d482123a07840181046407011512007100300c206040ca00300050383d103103240c0700301906d01480301c0202c40e400c0c5060740c1c2294080d6140c4050301c46c00907040c1002d80301c07a43c400554900900c9210b8010748004c2c03802d20701c0041100d20101170450b840c881d811170010802251b141c0c0340907414512608100324070070401400020b524401454004e482e5003040c40c2000c44442d04000c1c80d4000760400c02441c0b110301640d042d807c00c5080400e420000381006945408202c1d4400c1f511400b00c00d49040c05880c0060224640c5d01c1d00700f0504c11159401c84c003c544a50b103401100051800f903000c10000194140000c8600920100c66059400c2c1641c450f032030f4007440c1015000043e04411800c40d807040309407201c600009418088200c446941040b002d6109041c5044c00e02d2095080d009180306138000d00c10400089000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 343234217 1250 343232967 343232987
    0xf03010e070314130317090a0b010f05030a1209050d11042003130f05010903032a0801140f130e100e0c060c0708010c0504050f010309030c02010e0409020301050103150605090403 78
    0x5003c00f038100400d80c1016500405c02c80d5812030010100e004208660001155001d000c07440744c00303030309c08a9a80340c07186140c502c40c1380240ea5150304090002c00024800710418240840381d400c00441944d549d100240d495505500152a14201c844414100c0c1c50503109050360011301d25400084820701f88450b1015000003070404007500da035001c52a061250100740014a194094002d12030700d051498020b018104074245c000e403040145006040d03403d820b2088007078600790b5603101e41c1e00d6883d00b003003010300c2c0441800d141e0f0801c17007056440c03003035460346c2a941d00d8505072020042030354407a500030a85041511034451200070720302400413181d0b05000c0341803d0070035421114141c4406c000c0c070f9024100400d5a000d44074562808440c1d8070120b41240240041300d00403280c186000c00d00e01c0064007581c4c02c03200c00900180d82c40201c400158000c403c203002c0c041c800b8100080c130750496030110707084440070313041501c590064a0125000f80d00344d01910014040542d02d681040c10541d50250a41d001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 343235467 1250 343234217 343234231
    0x180603100302120c04050405010609140403141e070b1506041d0604020c070608060f0901180903110109030309061b08070c021306060507051e0a032001020f03010e070314 74
    0x40914003c1141c9020014100100b03802001041141080c2c540180200f0342132294840c030700e050440004042c0840c80e8218410740e0540c840031141e4151500740b0750349034400d18015403000d5083c044441d4440500020f0103110b4440e503001c04503030a10480b900c9000390a80700c410b118820401c8180190107482c420311114001458a40d0b41580f0f4072400100a4040c2240c88410352041c5c040c001f40e01d961222a0324020b040903540c0c4c0901052550a00100003024040c401400d001c0c4010381c0820f1000e940b1500545000f450100c40559a0f145e009081d103020b900240e002a490354000380611140d481107140410f4419146040a800040003510984004060b40b0510015481c0c0e802036454060b035140e0100c0c203500e01003040c1521200b0203400c03508880c03c16200741c81124030030070706441d113192024020203104008122641059030210703500e1080202548190055034031420300e1590074009020448000c031100c6441358105941c100030004001d01e03c004060400f14080385092080d006075402520b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 343236717 1250 343235467 343235479
    0xb0912030633031905060d11010e01020a021f0201180f02010807031b2a1709030f0706030c021c05120402060c060a0e010b01020f07090507110102030103030302180603100302 76
    0x82c036110407105401d81448040e18a6400420450300000381080f0283c030303d600c0c003401c0065480700b0b4140a040601000001e017100010065200d00b0b60080c0018240410144100c401c583e01540c04a82c04a0810041549401c5c0381120513601b540c0a01030164420703000700d0201c0f441d281c561038100c08019a0039001e818440201d021926046c400d0308003013860b12a00024001007140b42000a00800d1020a0105481c044011100030800303441c110411058100800d1754900021040302600e41e400201956418464000b44005004040c0640001002a07886c000341003e00300c00701078188091000c10740411401c0c030001300c20041d0081e06881a503c0f0300c0c01a03142540e21440411114454050460309030710031201003221200e269044038038110320600c0203002c512134681c01a695041142642643e039045080144900c0540d5489240d01c502c0b60303d0040403104004c0310260072a4000e81040e0002900001c6510250345038031315a15079040b0a90f040c1303142d4648100c0e10403140c0390600001348268 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 343237967 1250 343236717 343236769
    0x15090e03211f030506010501080a151406071a0610050a050d0908040512071815030209061804030210050c090f040b12012a0201060315180f0b09120306 66
    0x1650310041425505080705034002d681e0f40700d0a005664090074819540007900c140c0000e03c180015000d400001a80600c80c00d1210b4103046d8010300c3c50f68140511034200000f40007032004203144a0707004040d9144140c07002c506040000502154100c1e00090750b042c070804010300e544440e44402155152401d0120001e090070f081d251a00d458856944100d90010610542c82c46801020410b13004446100720200004030b2030300907041c00d56911105031003c1d14480e80041015040001180b94058802010741c0b42000d440280107540b09810354041d00140c0c0500c9021101d0040e0740714150700f010448035214101540031001880207002c034003c082c06103480d00520304140d11070980307a02903042c4010081c4010070022080c0b0070380c0103c480d00d440b400f110036151440c800f070040c0700c0c1c0000c1d43d8000500440c1803100512502c003602c0b80d4646808035802640304000421144000000d0992241d404940e150801e04980c2e840c22001740c24844102d20104280b1409659613041c0409020301e18440079601 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 343239217 1250 343237967 343237981
    0x3070b060118031b080c0607110609101e09050a031401090b0a020705070504060e041b080109030f020f0f062e0f030b0a02090108040b0c070615090e0321 67
    0x2a054071a203100b0704501c0d60003c002c11060442e98403545207001032504d60940d541c28203a9a81601450f0f15401420401269000c22001124015100c002404031703440e2101d40400309042d0360702e000300314000035410703034008846405450303250141c0700252400e031408500303100004030341c011580320007084000c201480d2040c1840a4001420072a084070f0600c5140c91304800c5580a980654001c440754010710740c02140078a400d1040d0400c2e12002c403180c0c441c3c0c2c0d0725682c03000c4400003242c81e401c115004029002644400134003c0108640c481d5403421080b0706902001307854052010b4501c6a280c00040f104400620001010396019921401408650796078a03042c0501c005c0c0b603401d08200c01060b4402080102810b42d409045030b20136000c0110f65515030740c1d100c4c2240540580c65002402c000c1c0810041990800030300d810a00c848600c1b4900310040c1c0c0c0d0300341111a0ba0340d20903071240d42890100206100703407081c422480b041001039464030b5a480c0c1c0169050080c080d4526000e0346001c046141 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 343240467 1250 343239217 343239227
    0x1080a0b040c1d0303070503030c07020607172104050d3e0607090602030301090b010302120a060806090f190f30052a1f0501090c0302030903070b0601 66
    0x1080c0e001074800c200400034a0402021040185048121001d044030140c0d21401e0020440e003006030064051400d5454000d02da03c6030b2707801304c841607a010074103100d0000441c600f07001ca01500035003210030540d642111504061071074002e50584101a11120400c00450300204070720488852034a82240c3d801102c4004030141c009152442180504000f08401540c0b1079400d020403d90110085910590b19400101c541c0540c0b402210010380003400100807000c035640012600700d10504025040c030b1444003e031814500e04940410145458070307810412894240240d83c1c20020b06000707054002c9000e520603941718900388007882038126a102d0001440142511000807944c081c601f08440c0d108100740c4110361130344004400107031803004030020310a8011801c9807544400803200e000400c4030000c10102d20441c0c90354181840c00b031400b882078040c8000c0c2c100d01501003a200c0028055041020000c202d510025800c001d145c410824092403010000c19120f4541d848411009156580300c01224 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 343241717 1250 343240467 343240481
    0x4090221030702030f030a14090a0b1204030f030e0a03050c010e0f0a060506090f01050108041104020426030304080316140d0509010b09010b2713020705072301080a 72
    0x101114050500380280c0c00c080020b203003540c001c8048841c003103c00000551030307104001c06d0300c2c0440d58200c00c54201202290107070031041001070000103020340d90940300c0302950101c20840440094003007007204040e0042100c20200c500c915013082040300c481207603a545c0a038004081c0601001003041c50440d4000d4003d550045494004e4071001c03034016003890382e559070b4000c088503e907007014001040da0a110100c10712500c030000c64541264a0176005580540c1c0c060700c240c03901c44011b100701c103190300c1c2c5000410092903400c4200401036040140007150303810803040090350360420800d100101ea07820080d61703081300105440c0ba40b038650744001598048a1038901c006428804648080003003e244e0120f88070b0110f00c03000740034a010b52010001060004d00a448030304105001c03200384caa40c00d14201c480b41c001445081031400c07890300003583d242e04c5e02c11610790990700060000104031040c05814000c00485800285410400004500c454081d480c4039040100d071a0002d4a540f1087d08011 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 343242967 1250 343241717 343241749
    0x50a0f0303061a07120e0f03070608010504060902032703160b0604051303140904140a021b0a0305040311040204030f050a03030c0f0c020f01110709060503060a0614040902 75
    0x89844552458058040c1c03200388203a41c01081092954607014248008480f00b40768004407440c51340500d01410380b1000d11901a807074005540c5001c5440b652400c21244016040989880c1c5a039072410b0100300c166801500030314034450040c001d000f107a00b201c072000109501c2110304001080c0341168010301c1c41c003c0f8001040404030208440d0103006600003118007482065078288a5540c4580c00c0030a400c0842c0c000400040352115000347c01d105110180c464440f000340080b584684482040701421015a08212039030f900052185010010aa54803072084541014141c6008141c8000c1c0040c020791002404808050b00401c0240c0e8844e1704441c0556404210f0b0700d214105d5060807a130710384000400702d000c00e1038201c040c00124044c484990f08030300d10b980c03140c05841459080c0081c1e090000f0031b803410b00c100c900107041281000d0001c10050069018006005840d0000301032070700c000940308849180c071f0600c007400401c0e8800d484085407101502d010031100c480e032012031aa4616604c1e01 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 343244217 1250 343242967 343242983
    0x308031e0a02090406060509010e040f0e15060315190908090904061a012c03010609020a051815040312090812070c090e06060d050f070f0e090609030313050a 69
    0x39030203409078003500b00483c1c203803030400003a911a0300070354003482030b00364003400318a0407844103295140940152a90502e01e2130b0210784820891001c1e890708401460f2403e04440c1f003c20040d590804012034002d00321490f0090506042807043e2080e554070ba107420100941e100c441410901213450200c55040c5400b81c04405a441e183c28404010142d0b0380712410000f8001100b00040e6128030b4602e080344400220030728581d40300c032020190f407800c22032026401d95240c80000600c00182d1024041c1c21800e600c0f41c80e610b20382c4805400b040228001554440c034481c0c00849125410a025501940c5d400b0141c4010b04514a07429141e50385160b002680c513204200704000041d0710707000508411407103403005c891066187d01d620301c10368594040340342d01c41e40f12000041191900042074108140110300751898012003104450400c8069000714141040a920800600022900e85076000707891034082d000364248403040d1500d030310020300320000311241010700300c09100042c805041c11580c0002c0b8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 343245467 1250 343244217 343244221
    0xc12040c080a0b010302120106050604210b01060e03060c0c0309011101090b07050a090e130204020a0c080408060411040209090a0c090f1d0907030809130f020c0606030d03020a08010308031e 83
    0x103240c1403c801d0004034003980340003018034008501401403205950004201908207402d1002c801c03a00c4000b01c805200c03423583c3c1902000490507854145000c0c004030b90782c0c1c461a2605005043c41c1c01d0024210386050301c000c2103005209113012094490400003481c12550640308151024054042c0303100180140c028201404181c68000c0700800c5000c01948481ca400e03030f6103060030714503844200c0e550180d00304482c0400c001840d040c0e0040c101c2503d503040441d03201d206921900c0709078015803c0301101d42d100c507040c00705111510304d50407080581210203514040d8044085201100d02610030103040ea1a101c149001074081c0b89440058170180c07404040d00ca1340e070101c007000c0c1750580c03210a9142d0702c42000302c2d60000c00441e40605694004002034604003c05050109200c90f13420290802039a894066102014500040c07422a524400500c0241003030803c00d410010076542c3c0c03c0c280751040001c1d010032500008024110382e0454103641d00c075a00c0b1503008940d88092880d2010746511402 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 343246717 1250 343245467 343245473
    0x9080628021810030e070326030106120b09241203071505090a0507030b0709090e030a081f0e04021203030f04111012050402041518050f0c12040c080a 66
    0x401d05103000001c442001c1c1010b22003006801310740440e617001000f0341040b035042c0049030307948050304aa4803d1030f01e1011020f1001b001c550442d0400e030401c030000f600c8034281481c0710520780911105003078216620040c0d401d0240b2141c008115800410004000c40031402041d569514151610000a0b400b40d035500c01c81850080305a0071b03e100c80e0550b003407500002c203002550014001c644143d000004220280c10741c1c070382204222004052400700010542c0c0442c42c41e015015100380c04281c0c4008640b40c0b4403058020f4150707040101003005c0f00c40c80407640812038400b0101002140e01401540e0790684131400460390300a1030428641e02884000244000030015400d07940c891030203036400740404002481001062918440c031240091680485500c21048680c00b03150417501c028000074044441c001442244042a40300000760009100d0540d03148115000d217690000000b060180585000d5081c21000e0085a0f1000070f03e0004100003801c0203412400040a041c4050407076005100c180303 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 343247967 1250 343246717 343246747
    0x12010605040617010f0c024303030e090411270906070f02010c020307032a050309040c110304030314040911040314061e07030f0e0106150908062802 65
    0x80c0c3c0a00faa58070300182d2401011031441010703644041503000d002200d0101e90f16216030030784058074a541da1245420324000e084801e0710701d0321407110203060703400140c51410050110501084442d01030380220007048005a125450410a801d0441d1f030b603500700410740d59000c500c01420304100030036514841885641c03040061682d1017440c0c60713960300e55002e0342600107d082e555400f940d0800359006010b220b00003030068900c02514981c400c0c60f8040310b21100c2d401488000907a0b400d8600b0b40000030074035258182401800011082070034402441002d040b040303903403442648405010090542c000300c0e00030049100b200c0c01015480014008030340c449140e03416641c03091100310f601c045040c02c400c10078400803444070b03ca55030410b1103001c5461800c4804034115801019002007607035030f10140e10740424034890040e9005001700009495410040c1c0d20303012a1912a998051007800e9174100088030000414551000c0c012101c40c030200d813103d10317082a01404904105805001261000d40602e80d8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 343249217 1250 343247967 343247999
    0x8160302090105011706041d010504060506041a0105040314030702100905030106170a1211011a0f090118020a020c0901030803040c05040e030f0f160c1706011202120106050406 77
    0x807074588129982e104010350381c0030408491008404004400144c50345482e07448641c883c0c2e010030f40917290b03c001416180c00c5440032681154415034810074413905050900c40c4036030052104048020860701440081d02e14082d07844001e2502c0419a04a05d00840c00e00a48a03490750103000921074808030a07029040290a0258602a40c6080b60000ba05020b52001030902d440d130001801000565071200030003105008891400c1c0042200d100b150f9150900c15803107002c0074220b60041a6240340e0030080c64441c030704180b80c0300345c00c000010302018190154040541142a5005940f50401c01e0168184560700e01002da01c2400b0700c00020034402d07401c00451140d072060320b1050815403074908220172580d101d9080d40c0389510920880301c04030301c140c00501c045ca0070070020508202c0103995003400703503010a004841c007003e07181040103000080f00320b0080702d840310009810558107060044080940a81010348130704002d98079400850300a51203c009408007030424848642c0781c9914901c8030000e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 343250467 1250 343249217 343249219
    0x3030f0901050f010b04120314040b04060801090212011e080a060b03010507030e03091306030b0a090201020625080406020d050c0a02070f030b040303020304140a0b0f0f0402010c021201020408160302 87
    0xb041c00103103a440440c89460306039540829424140707420a00202a21100e2000032428828107420420b000e6000740080d000a0284000c615030790307400d1001c020840f81041e4050300e035550040c00140003541c0d001100c0f07030544120910a103100500e1100c83d072440b89450f4820310081c0241c982400601c401508a420900020390084c403087d16064001c408079002845006181d0b002030004400514004d43d0b10210244200408145241c90b03813242c00841c0400e49094190b03a0f03585c1021411940c062040f941d2040014078107a442194a030041141d042850f01210100312420000408210644d41900c43c0e00b82c014a08000510300303413055418551111907484090311075800c0006940300c002041d0070990342c4c010280015500c030396800303401a40000d4070840c1c0e0881010343c0f416034518100308503c0c4650059030505c0d15801e1041020b07000d884003070600c5501d40481010000542d070040d06d800f42c50303581620400c1402d00c0941a241c024000c6030001d0031103004020390700e4100715172850400c013504c2c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 343251717 1250 343250467 343250471
    0x70b0f070f020a17090103230405010c050f030c0d09060216110604080c06030a060b070b01030b0c0301120b040303150e0f180709020d06091e0b0f06071407050303030f0901 75
    0x1c10340c4401d9981d030b610340c000148000c800b50840400b0350050340242c1005a810f0401260300401103003a0001100801c3c02810a51010310410081c08002d00881b40c2002550500740c1c540131074250207001c244401405012200e00c000703410340503c2031650051a100f03411040454944c03810f5013401c5441c24031080196440d0b8101000e04c0321a00e048001c580031180e8250041403d0080c0100f0b0000c1030300000d0010301490341d42c0f1701c005400f0104800500505114000c0315409605526040d81908000740031203040d92401d00062100803880e100404400f9005060300c8000d40d60380c5400c40203040e800c4a00307041c1504410703000804030160780507a0300919042410f0f00144c0d0340c2080d1003c1580c140c00020b01690312100c1d0800c01e4443c260300a1542c2d00f050070340842e501d6251100a4251070740b51040c840c04078007904003881e007840700d445034030358401c42202c0100742d803c682e20029089004e0301002621861000300e2070101e20700100031520003400301505403030300e030300c1d01020a1a10040440b01a19254 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 343252967 1250 343251717 343251737
    0x4050906042604060c050a020d030210200d02090a180b09240d05121303050d030908031f0f03050a02031006050102030a120e070311031501050a1a070b0f07 68
    0x7901036142d440140900054140c109483c21308126924000c85000f0b40d65401000c502401588451014041150007a001096402045540710080342d01841001d0040703030386030f0010304103100711030100d03001414403102c056220002000040e510701e400758081488003800c124105403001658009800006013100d004210ba40c844048203d0761001062040d00510142d0b1000d03a01e26246085280346402402102c1c040c442d03c07191840aa4080c8040011680425070100b04212007080b000307000000a01d41400500c01030f80d9181c40380d00003d050020745289440609003504540d0000c1c00040c4000303000784010344d99034100181c2b0f440364110260300902404818003800c0041d40554400c441041e4025441e011995504036052030110811411442d1074610054000380c08000741000b4601801d01103100b00e1b403440804d444c0c81c250790f0312003180f40030b60801000b040e43c65540034011140b2101040c040e603c0c10000390b4045108051005081007061000d02604442004c0b15500c11403054031280d45c80 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 343254217 1250 343252967 343253003
    0x603120c0c280509090c04051902120f010602030c0c0913060609060302010e180703090201111b10030c120c0302090603010e0108060a110d0b040b0a09090605060a050a030308040f020405090604 84
    0x903104031a0307144d991b40720340d113021111304055100e940d000c490400a4043d500403c4400e0090303a1010400403055030703542c014032038903003200b402c804e00402050000703611341009507081503181c1c50310445840c40b030340d50300001401c0161001c0e45500e01d1a48250b0800405da115148140200075034081a80020414861010b07241402d03d200b489260bc80039041200e07903140d1f00b044001d04841c0c1c80c202d04000c0042c00d010010501008401010244003020000c001d1080b0140440707901e41b801c1d484101403d0a40d1545000c3c0c2100c0200c4060540110124080c041d0103c154041e03c10503034410703004030340000001195030b20392106034180d40d1002c00341c0c1c02d030f5201d05030300c0000d81d004a0080035141d10100b100e1507002503a0b50190268050152002c030b030341401c0400240c10031141394045818103490300030030030810010748501540004202c5003c1c020303e0601c1d000c40c00807441c80c0401801c0c000000b000c1400c1c0108640c21000c8581d008200340400d03d0007010054480b1001d680032203d41c1d02908001c81c007 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 343255467 1250 343254217 343254229
    0x30436020c1f14151008010501140309011508030c010b030606131a0a080c270c030a0b0a0b09040c0305010303121a041104030b0903030603120c0c2805 66
    0x503a8401c100103000781119a10540240710b0081030010078560741c0c0c0400c50011510606961060158070a03890400c06028103014800e160845043d04010032080144826030700310060814140c3c107070300d00c9602e83c1d4400c494640104040038181c41c0e002e404290004111f07500100410b50b00304540001e005503942002803607540e0005442455011142c807148200001050344501500d081904500c005605407402140c026549500308030407581100300c961aa0741040048508000380000140340c01880d00450307480403d0020340284d81c0900c0010102d0341d010181d8206583c070200041c0011a501c0ea65801d0031559480384100304c0c000c07070a10740e101c2081c6001e0710416049a415803100c04041b0300c4401d01000400c0800c030040b48607190781080d51ba0646851150790051000760045564890540c00c0c01e0000d8900100301c000650f10410410450361070101d5241401880c0303941160701c9500c0021924280407040c0c0030960081041d00001e2010200c0303081103c10f0810101e072000016480d85d00b8044 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 343256717 1250 343255467 343255477
    0xc010c1815050a0e13050114030c060d020a02070906140a0b120c0c0a0534081f06030f1a060307060903021003091728080a0c0203043602 60
    0x20100315400151200309004100401d1105010721300031809151010024051203d00d4036107556880d035404c01404194140c1112000c2c1e040d040300100300d07117010600000c2051040000108140350041003080340c0030f00811555000c1c000c6a1010300655803074a0f462010070b58184070b5184103c185100020b9407124510842c0c512612080101e111656101241e400c0341e4010300056402d44249240540818000e00030012440003032040c9000195501c007031860050301440e080e60b0f10705942102040320130800030b500c002d9030314849480c10040040501d5100100b80c107174000303440040d01020302000c00c8625004240c401c911807480c19002e403640403d06030703500c500303011724004100d40d60780500142c81d1009106001c0912031a011540707507520ba40701d20801c0400355042c3e005010105182e81002a1b2100451101401006010408849003402000c4c0000602844c0ca04d555890003000e045100b4011039000c0e00f04600030900c488c40b81f082d0b9004111500103e03041d240d161110741c0044641130f008543d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 343257967 1250 343256717 343256729
    0x4150303021e1f050a060504020a050a0809070509040f060c08060d0201080405030c190314030606040b16211403040804031205071b031109011512020f0c010c18 70
    0xc2d07074858082d808815001c0114008442c1d201c1c00040c0ca040c9980034209010403008400041558105024180c0607543c42e900164070690041c000c0b035000ea50303c40152445000280f40040c0c440d1500e5001500300704082d082590400d010300300304000e100c40902030310b40e054401c1604028100c1882d50031140000c060310f9103940035401c08481000f6610a83e80309400c9406071007524a07000b0340340c402c0381c030b0b18010301c850800082d00056154189500b0401084041200448003407661a140300000c0c80342c0310380d00a8168030300c0c012680b040b80a100803818210f155110100380705c14041b80824201d20302c40e1071608800107280c0400d0074070b080104002d69000300d51010303501e4107260840d510030300d58001c045801d070100030044c00701c4800b2405910240c4c418000e066a421001d50075414145804002c003500c4034050130420f03004000c010ba1384c416101c0ca80c029444d01c61b6960f0b42e90f54400b0040d116100380804012404119003442e0034040d8002e113043c2d441516449121403286011420f4107129125031 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 343259217 1250 343257967 343257973
    0x907090603090507080a1b0b13050d03030f0f150b040317090117070c110f0a090c050721020106170d140d1d0118150b0d140c0415030302 60
    0x400c4601e0094000c0803610348144240c409440e1294103407032900309440002d803050f501e000702420700ca1444c804032070040e28102c1041e518044100e200320701100c109100d207074001d4142b05031000c203041c0b09510451031f40740c0d51402800f441040d01c040300c0140c0b980d0261144484500740340011154240802c0b03070226540851a03100240d803c5141c7d0f007841d04140095814042c1030240d4144041310f0a040903c51543c503185c1c000b207116241468401107901d404070a000f0806801018480d6541d1032070041141d1480c08042000141c2030b0044a01d802011001480115240081c50f03580f804d40343c42454201c2c0c583e000304011356540c105519015040551100da5030400318040e201e6030300c074a02c0034484060f007900d414908004495003d0803119100d5241c1c0000c1140203207640314580a02a1f040070050091408101031456201d9000603401100709a42da9681c41010a80e552540f8528081b06900204503e10510078410503a0715440f00c2c1980e984140d2030410f0301c1030500841d002c0641603d03015401 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 343260467 1250 343259217 343259219
    0x40207081911011e02131701021206120c2e0201060314010213090b01050417150702060709140a0305070e01060230092b0c05060408030901050d09050d0f0806090709 72
    0x100d00000c1d44070039455018071440406c0401e0015507250141c0052044100069503500c1c0904121040030300604170901c100440e100380c21880c0c80c0060700800c0350300112551811043d0729007071401e00792141000000580c4002000116154041d8030030411240035008036000d454000e60404c0c07c0340304480002940c0c404504050000008036400801c03450818100305140c0354480c0141c1901555403603980b4000d9020b03001c50000340b1003a0341c07000e401c4480d600041c195030034040d0014010411b0742c020000743d0150701004482ea03594441da40360080d508042503407249901c0706040d40d2840340034041d0101500c0b8440300119040e009041c42d40f114102d41c01c0d100b0000c0000f00703120351a079000c0ca0300d1941c803884110100c010003035995007058480c5018888002c003e8407034075203002c03810510340c41140300e13400c2408200308001020003202c80000003441c01d15614400410040010044000c000e4003520540303c40140700d54001c0081c104542d015261032070300c3c1d40c80104010400d101181c0d60000101c4803a4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 343261717 1250 343260467 343260521
    0x50a0b0603180304031a06120d1202090315010b030f01060207081e0309150d06050103020702101103070602070c090e011b121d070e1f03030503040204020708191101 72
    0x840300742c0c000e00b0041a42c0c9800d0740c07600c407202c03000d80400e0400c13140403544040c4259031900c004062000b603122000303400340035070040c00981501d100d13403801940e0a80002e04034045503401c0c85114502c0148110000c803950711089100100e030000c40329101c80517210000407900c5800081e0071000c441800006040d5010300000faa0019203d1540c54180f9210501194401d940e40082c0581c050300c40c03080203902e03000245020000d5078500d038001418184104523403805a110b220181060f400942403403007080b032100c61914554814020003a00d81e80c408a0301104105041d00a03034110b507907000c070501480c42c084060034221402d440342c0e641120390b401d03140a800c500a000102d040c030300c0711000041d02c207000fa900300d80c0701880811380c400e150800d2006000107084035015a400c07a20b022040028030703925030f4105140750310a000140600c40003200041c21075580e40c045559140c2e2040008d91107240f44024500c050842c1c00804010612004503c0300d105014801c090040c43c1584441c03200030381000c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 343262967 1250 343261717 343261741
    0xb2a030412031806150f141504120303050a0606080f071d0a0b03060a0e01080303181c0c05070e09030f090f0301050705030711060601050405120106030b0118050a0b0603 74
    0x210442850340314520b400100c4094195407061a0241001140b05803c0407403c1107401c0150708051034100901b00140b084082d00c0600030001a41034030f040750000310306881c180d900c0c01917502c902403520b40000214105a4581c01c1140146905d41090000588822040c0c0300c10701c00b00c41201c9044c8044c80002c00c9148156031400c40781c1000140d250f00c504405011410f01d079007031780140e000354000105000240c20441c1c4224020300109202110950400e01120b4aa02c0082d0402e0700440c14068000907640c0c00740020601244085007600c140142840701611203007043c207042d182c1e0f016214001402101e1401614402c1104c80080c0d807a2050354120315485400c403001403500a80c5041803405a51000d1191600403826500c90646a24041000900400385401c1c40296904454103215280e44c0107410341e010b4583c121680b805a2900708105401002c46610140c458800c3c0c0c000051125200c0f07148000da081d1080040c4510383d03a80d0104408d88500003106600240300300f000980c3c001c081 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 343264217 1250 343262967 343262993
    0xb0a05120a090c06170a020301080a0305030702030f0d1b0e0310090503070f0302010501081b100f030b0d150b040e1b0a330e03070603051306090b2a0304 67
    0x42580054165181e0700c5680540909402c80804030f032050318034886031505e0b81e07240d5603c055401e01c20351440d8148602c15840e01c9815400500784400030000c103c0c007078001c0c400c0c0c40385013039240340305a01c5404404450340505070420307041040000c14407900d07451318400c0c080e5100440300600200040080101c1e020f0040c070801200341c0c0d40f40410b100201c0042c0109044142070f6000341e001042d84d504200d002c60400b042d011750014110702011ba050b106840d44500f00041e01907504105499a00420050b03020384005540103600c0740e2004110010401ba01d0076030120101e1105040145099600c00e1100311161003009003042d501500d80b01810b44042c8118000c5a00e0280c00c10340c07100e9642402d03031139484400e01303082282902100151001016040740000019485c60920644c10100c1c0110740ca844582c01500f040580741d500088407204207941000040d40c1c0320b881007255545c5400c00c22203100d800d80c3e90707010404010070360792034031744000c02d5240203c0c0321440450b14503120355551510140701 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 343265467 1250 343264217 343264231
    0x403091a040b120108070b0408120913090c0f050114030103113606010305040809100302190c020a0905010e0a0b010e0405150a0f060c0f0812040c030605010b0a0512 72
    0x400c00011034440d9145020b000301c07480a0007245015411710100509010181c0c100ca056144248810843c0e400d0028510b80415013250580b651240c450340495029030054910b41411030031701d040041045444000310702156191040c80304003e80380c0004607081c1000e2441c0c140b4010307003030006102040c000014604011801845203c40400910340302c0c40c00780d180c0c490b212200038090211030644c04e140b03104c19480802440c0800c545c0c900359440c43c05601400040c035004503507440d0720040090103681216420041c444417a11101403c5400a1000400c072504900481c8101d4001031480480e009050594481c407801e18401e655030441d400080c0850030b0894104a003040100d0040c0d1078500c00e0b9400781040e4100f42540708940300c207100c9004803e5002505101c00080108180350744107140e2140998001c05480d580715290a014420340215080020844075010521003004001142001201e01c00d004c00d0005a80c3c8a109440c0360048040a0002c160204801d8400340500c60701d85a01c104 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 343266717 1250 343265467 343265519
    0xf03030d0908070b01050f09040311100609020927070c06060e01060302070506130507060c020607050d0306080d0c021008040609140309011d0a0b030c0d0c02010c110303040309 77
    0x404800380300d003039610100e025161100000f84950a201c1c40090290250505a6a074070380c00d02d140d00401c0c0c3d603080082c005800c00c100080f00e019181c600f840502c03202400348038141301d0f29803201840300095010b4030003e8404d2015104200c40c0c280d40c088820001030510801003006c2d0344c2d06c48195065880c400d01141c031540e5940010581c86648003450b8080c080c9a9001030b00d50400740391403480c04034040c01a034410340d120324100d000070340000380d88401d40e41c1034980000e801300b00c0e00c0030036050301175000e009115004510000300c1103a855030084c002c840044049452131301c1074440503a92030704040800394014846550550b0014000c1d0740c030079003080c4104070008100d00e840d00c40d500855160144118541c1002403040701c15a440a1508010b61030325407109035104e480390001c0c02440740b511a81601c40400300c00580341e49020340a480303003281003030020700c80190040c2c0002d008040c041c5c0315002041260f440c1183c010000401d80f0302c600e6040d2510440325080c6401c4021110b005011805451 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 343267967 1250 343266717 343266727
    0x29010b07061104120f11040e070510051309051b1e090a0e04050109060b0a060e040e010b12030403030305010e071b05030d02160c050409051005091606050c010b120c0f0303 75
    0x10f9803c0c18204207800790036451720310200e9160030071400503002c16851240d41081c80e144000400400c514040305c2040350b5070320b040228810140d480e4010a50751039020443c140c80007a1200c820f4008a1291405c1c0e800c0309110311203400d130750f004d034001c100309060312091840c04903100c00d032004000d2003000e030018442000780741d032610361703505030340c003c5404849a07512208620b04105480c014648280307809c5403200c0041e410200001e040303a100da40501c1c0701d1625807020103c6281c00790f00c100c1b404000a4106203d624009513042e82d41d074010701c01100000c0c41c2c00300004000ca1234031600380c0900780303541c0c84242c141d2920346070440d02001d445095907980010811400c41403820710050084154840c10140095010f007030160f11110581d221502035820101c11400165022414406500d140040041c0a45a800e451407500090201c0807a2403840c495020811640000c00390240f0300ca288001d000d641d81080a2140044031404d007214940d00511140000f13250082c0043c003000ea01400b228144 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 343269217 1250 343267967 343267979
    0x6031e1f0602030c07060518090406020d0c1e0f35090d12090804050d0c030506010e0a050703111b03120c0c0601060212030f070302090d29010b07061104 67
    0x8030a035544024056400010582e400000a102d020020101400c005040849007948407a03407080c8a00118801d0134008000b404101240d4113076501803002410400c550702d054174016081500700301a101e00041c0b04000d400c042442420b10130840b00e5140d035010209a0b0b500075020300882d10340b00c0601c148180c80c0840c7c8040c0c18002900c1e02c252240c000a000c044642c82000d0480200654450039050600d0581004115500d003180c003111411303124078201b4186410010a240174680000f4010300441000041c0c45e00d02c0c840c0c15016071034600e003c01203030303ca0a03401c1d81101c040303210b040c17610b1400303000d160a9086199140300311a03104038196803802060b00161003034100111402807802e840072802000c0350404001132805880e560001304070b4003030340009034613160000500c0602ca01070a44c000038500752281d01075504011018004001d065560b160588136090300f11f140c90b0004480e02d00e00c01e21000043c01c82d034121504114510b20b403401c2c1d40c44038800340a5411070050000070401001030781c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 343270467 1250 343269217 343269271
    0x60c020c030a030806010e0301092604090603080901030608010e070b030c040317030f090d0203090d0212060a0b03010c030b0906090718170105070306031211100f050402030c06031e 79
    0x78003480303980c42d40e40c0c1e441c5c03481c009000b4200f0211902d0113603241400c000002000d440c0c12001c1c41407020450240300c507200c2000e08040c4a03c0c3c00240146007032250000c00c000c04240500b42850302604c0c144a410b445060320b030b00329000030240c4200c0da40140e03020046e45071050011a0010709a65140e450715440c4e07114403080d10707800b204002422074000308100028110f00c200540001030000944560b04a4400080d62401102c2c4020703c26001030021004640d100c0b42110303444040d21080d41c04138603141c0c00d10401010321301c4079a8041d509041d02e060300c03244a44107204140100030b000400940b03030a0207100078000010507680920001c800249004114001c0c044000c0000c5081c0c45411601c1041c0e0600b900c101420942c02d05017041020f000141c0d206200c8400854246002816100070881346458001800c6420440c0c51400b418400000c2a82c5c00c114460360007035045690103400142400440e00c8100c8601c0da002c1d030002c000c1810100007202d050b800440e14483c1c0b4000c40c10301900020 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 343271717 1250 343270467 343270483
    0x2407060b032a130f020a09030b1e150301090c090e1c090b031302031c0306140109030204020319050112020411130b070302010e03121e01050a170307050102040609061812060c020c03 79
    0x1c0031902c04c00e01001000203400c122644001010144ac1c8a8030160b000780c0401403010f0221013484080c03030722a00c001d482c07d600240486401551f15084207507510200401840f440840d1601805070010f101e0380d054160130800b806084170740e24118120700e400e100800d1504064901c144602c1c024a0b03000141e034040203000800e03040b2080c04d5503000c4010202504658050380f0030040302400c6218a05aaa0000342e070030200c3c1d4050702c0c0507a40e40e4816409403a06050514042071700c510f00800400e0b070a00e40030345042514401d50b001c2015124025022045002c0c2002e0220f000100180030710010030004090a0203502c46d000200d0140ca00c003240c07a0454100900e42c8050980f50404c0014403114081d18084198031040d8541844d410705001c02e1450005001e100340000700100c2044403108100229400c0c2c0c1d401000854880b81c850b61f00030102c3c86a40704175400240c1c5100001c2c82c581500303005074100e800708184640e010400350345850281060002c00d400f540294000144d1944060000d40d03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 343272967 1250 343271717 343271737
    0x50f011701031a0f070210020d150303020601090c032c07081207060501140916180816060f02030405010f05210103120f0903022407060b032a130f02 65
    0x10180303a0303646580e10b4a0000070600c00100f04c0703800620613565004100181d08907580c040c0943d0f10f4400941c0c8201a1004140c1898900d8884c4400000c0c0b50340810054142c88010606010500d6102c0c4e00b20190b900704e05020740321112010209400d411980300e41c00c06255100180c552407a5038080050506005071306001c2c040b24000382c5082001000d100e014090310500c104010040301c2c1720003051001c0002025100001ea414031360341e905900440e0480c11f14001400d5481d4400d484a0429403200a460344241d00400900310125800707004d200d08408a6140d90f00450809103464011103020403084601014000c04009001a50512003d9401d072034065284034003aa5146180242110031043e0445041212010b0a60030095100341c4100450703804680c400c1161100e8185070303040114425a940000da0f0015060b0f04021803074004400f4200c0880640c4ca28680021001100422400e034469000508000416080ca000c0780d08007440c090542000034120352011080040380e100c21043c1c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 343274217 1250 343272967 343272983
    0x60c120c0102210403020c0405040804091d010e070503031e0f03040f03140a0905040b13052e0303090e0a09080c070503060c0705031c09050102030403030b0315010f050f01170103 78
    0x30692103c1e0000c0121840f1104498645a62030540c60094598607090b1105101e181c40d040820148121a41664040c1c45040c9080107075400b010303000d4000320030076443c510a070b5007070461003240340c100070540c2000c4a0001c1c01452030001d83d600b50350300291229900c451600d0007803101c0202e03a40c2920180d4881c03841803a400004100358100501030040c1d510b4410750b9801304002c11241c1942c001d40340001c071101502c000c28013030400310014001d89030706502d4590303261901d030410021050303002000c00c50f1500d20f115021b2082000d20040074001442c04061702240403a00b0400010381d150046580c40a41d0160009210f581c681d6108200d51000140e0042d036804690140681d20342030201c5604124045101443c10346141e94a07a224094038003050403d01c0c0c01d4690090714081c1e0f03002840e010b80d2110086549192501d0301a00400da0b011b07500d4001d110f01030188600c1c09503e030f00c0c58141c03505003a44c0242a803500d420030042e00f00c169540340c100140d0203006140d440c480a46107000e58420818 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 343275467 1250 343274217 343274227
    0x11030702011409030c03040e040f1b05122d19110901090203091b300106060c0f110a1d01090b09040c0314030c07030c050306060307180225060501091a0a05060c120c0102 74
    0x30004144641045420076403c24034250031034030240b41b500078800364ee8480c84648041d40c48601810041c14290503000c0e40781c0ca030030400c00c204c0b18010560348078800320b800007107a90300d8001d003200701e02042b0303920714140d400300003910f551707038000e0540c21040302c0c008046c10581c44050018010316010144000b200c030100390703560a030818003802000d0183c90f41d403034100e1034101c19440342c1c060a0905a00030300b200c400c00d501c014081c3c03220680d550107040c50106816000700a4410091414000d03ca004407c40c50001402d84a140c00d8031001e000380e400806521119046480d100d452102c5403110032800e102c10068191010018005000114007446c0f2201030b0034501000d240c103140d001405248a50804074050006090f0500d0080564140100068540356600b46079241c0700860030b103400c1d0014003401000c00b00a883c3e00040d058841c18001070015035403080d811115100e1401c000f0390f01518442c8180030740c4c1031200181c502c03032100008407464030f404070b00007500e83c2d0310140d034428090f500010 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 343276717 1250 343275467 343275469
    0x10110c0a06020d090206181e03030f030403090e09030702041b231b060117160e1b040308090f0a0506070b060d02090f041e0b0a0c020111030702011409030c03040e040f1b05 75
    0x80d0100304050b10f0a071802081c450300c00180d10bc0c45107245228034007201001250030b2610401c5000040d10003095162443c0c02c00c08905650303500701100803031045007004094555000200b410036480e52143d1a40030008505035080d00c6110f10802400040c81010b00c0500001d05003248010000b000103006443d29504040180c14078100030a44080340d544914040c500360030720502130340d040f60140f01d46a03c0c951150481801c0b1405800c2442000076004503020045c809404000c2c1406441120154480d0200c1e0040c00841c1f9070900c1040e60184003404a00c001c01c480403421b95020310010070000c0d00310710550008101d000103031041110b480310002000f080020b210061115002d020b060002c070f42c4802d40c1c0d0b0a09603940103002c80001600c0b4202100024001d4000c003400010004600703882e07103071a0030000d000300310746903008015030181408228105c5010086a4441095034003840c646410701201c501a0b29000c1c108507109202450b4003c040b034031990041c01892181d0b1145205245000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 343277967 1250 343276717 343276729
    0x30c040306060b0304020f0907022d0607180b09030c040905010c080703110301031e02040e06061903080403082107020c10030510050f03010905010e10110c0a06020d09020618 76
    0x10f005545148410418003016913a40c0c480c007020040111104500caa507800400ca0400f282d8510801c1e0b12120002042c0d842d41c0031250030601a4400d50440d0120382c0d0721b6a0449402e0404405000454503c89090100006540081c1444070340070f800c444444001da00410110340c60300c082039a03180d55655868400035841402c176500444503203024030085000c100311017078903c0103100060004250103104010800e00a102e03610080d0002c0040000000c0c1d00401904e07003404490003031042d0090b102034a01c00c4100010351094030382048440c0d09003410359880c45035550107103a0240c0c00450740100d492400c0e0016030598407170902a8094100140200c0c140956011108a598181803c00c2d0400c0f0a400c8095484003c41e24100e4862241e00308101c04280101343c0f90101400315400c285864003549000122402c2c081f8500c90b040000e0445000c02c2c034002c0c0100c1e008190180c02141c0c0e1040454881e80103404c5c603919101002500c07442c0c3d07500180840d0301140314041c00004040c0300444a19100e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 343279217 1250 343277967 343277969
    0x9030a0201150303080619150914060f030f070201090c18050105120a0303270c0305070801110d02030603070b0304030c020a0b0f07031422030c15080a0c14030c04030606 74
    0x760098940ba542103590152100400034101c9004891000803040000d00000125000f822590181c0c0c03100a4019401001010b040c0246051700c140340c0810001400c202c0115000b071044882034500b0742c2c9950202240540c0083c203030744119900c804042020031424030525000706086080c1340a4101034008480c01d03601e0582c40a4407561100c2e194010500b03001c078548495035414900000d440c03610485490940500203c0d4000c914030a1000d6400c0084000303288003074a000b030f01160116540c1d10340081c00d840400d0241070007004213100120803c09650040c3d904007070020281d40358a0345500310080300ea00122401e500044d100c2d42000194100b4241d08005043d070342c07103e2450503100f48121040e42c41501030040c10800403400f9402441c1c0d011059462401754a03510513900e40b4540718510400c45c40d400260b64101c0b00100004542c021012500c1d02ca011580342c2c000d0079521225014003c000d1044000c0c00c0c083c10851410b942d810b000000c0d8882e9000101d1a45c441e402d42c28004d0840e221 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 343280467 1250 343279217 343279241
    0x6050709140415030602030a020d0e012a020a2906030706050f0a0c020a08060103140109021011100e0318030c06090405060a0f08010b0112140103260309030a0201 71
    0x10982080c07140e1090040d0403031100100b55000b00302d594030180c2c12055001d00e64030213002c1030310200902060360340c42e400074125409605820303c040364459070518201e80b144048964441c0ca140200c80005462034080503485203603006a8903031046e151114800c0801b580100035002c0c203c003d00242c000c90404905030404400d50090a4943c18240081c01342e12805a0035500070001240e11249a4400c080011a10f42e0252854000e01c0d1b0313503411141d9403075003808100c0300202000c000304020101445101d01c216001031020540c0385520300103650441004011001d580507500000402496901603202650711207002143c0d212a240322a00d245419000d440748281c01031020034103240e0f41c2c0740c10b60f000e8020440e40000c45480f4100040d41c030385016844007001c506401c0001400d01d0042d444054582002e032904044c000e00c8128060480d5040114290740c00c10600040c8042242441000212090303022103240e5501c513110414441d41084420a80c9a0700c00200c81480603070a0140f0b20010384 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 343281717 1250 343280467 343280477
    0x1b010605040c0203070b0708060f040f090203060f040b04020913120c11030706021209030f0a030e040b1005030703050429060a060e03120a021203070507050f3403140703060507 77
    0x24171075884a501c041c018000d8020081020045035080d81c6030981241d10310002417003049040060310b1101c012f8005290164800c0c01141f001070303083c542c1030752074134031595002d07904020310b0343c5940c03c0211801c805000c0c40c0c03e00d0030015030100041d91fa12550328035001180c5624500205600d05121403c081120203400bc1e00514010001c840c0c000690180402034205550348a400d0000401e00e0030070308160102c641c2c461f10b00c0150078140c0202c0e8001142900b0303541030004035104000d1040055403040d03080b000420400010304154480d51066822030f01c0b92007018210540c01e5441c0c1c14540c01d20304920840f509110500015181000780c2000528407420b0884000381c11100081e103803503403c10704098209001a21888181c8288404096000e80e01c110b543c4900305a00024480d41200e4000c454900c00d10345000c120860000d140300e0b002e10b24103038424142030030001b003190814a4800183c1c0ca2441d400300800083ca5145c400b80c030000a081c000c250031032660403c101035910140000c41484 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 343282967 1250 343281717 343281727
    0x60b030a0c02030a0905040b190b0a1407031205060d051623031207080c1009020301151809020406050a080d09090b0612040812181b13050c1b010605040c0203 69
    0x2a0171901c0c00040720740440d00051440c00e03420100c0c007103c0071501d51076220001d100c1c0128402c941170000c1c0c05d0340d498554400919207040510958984101d03040600802e0f001001f4100310602c60300010f5100303070050b0112055601c0c40c0d407641e00d803019030070050400c0c8000d900103200a01d040c01100800e00c54080d6810a1000c07074501003500c440520442008031540020400c0c1409144011141d101504008483e607825058140c94024001808201e20950820b80c08000070390851541100fa80d511714280c01da2400c01c680008001e248904003241c200d80c031840c0002d100d903075081c0014001c02c12040034150220401c840101701150f00e42145e084240340001d82a440d48604058032981071079508071404030744072424040107030b0092848882e1042c00420421040c5040e102c41824040403010807525800e03902c080c00c1e115850180e54440c0c11100f01241e48154800c20b41020b90018483c100e41d91808a45001d60300d925180e0210940080c1c1d11840104514140ba102e92054500300d440030718244 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 343284217 1250 343282967 343282987
    0x810060b070210020a0506010e0f07030e15090c1806010809030a022a040c200309030a02101806050705120903030d050a0e030a02060a0501050603070c0f0c0306060b030a0c0203 77
    0x1401001d1001e8012065014980d440600800c2010100d54010703045402e20340c0e642c19080c3c0010001c90300d10b0120100034002c240701c180640503204c400450031018000301c07840b1805c181500d1100900e032800030701c20810100e565480705054045048590b45605107246000d000240213040c028041c140590300c00c01490f000365a020070810110b201441c1e120082c1c2c0c503001801403e5404240000b503005141054503203030303250842013850a1402c8032900c8020035030300281003900ea00482e4405a09908201401c00052418984001c1c036030581d4141007414400d980c800b0203120b446c1e600540c020070000515501805401c10083c800030f40f4502c02a81740c24000f1700441c1d20b034000d20542480b00394035080428401015a003202c040410310004490715030300207400003036031032009440a20010b840d1000124030b41c00c052084903c10078440c1c480c0c9041003d01d07a5031112050340b20b10241e840000500000c00040c0d01c50140d40c1c02006440038090302c90401094003021110544c00031410f540c03082000c8510 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 343285467 1250 343284217 343284239
    0x31d0d0507060209060d0f0207021206060d170c03130612060605040306090f062309060411100e0a0605040608131e0602070209270703020d110310090b01081006 70
    0x58180c0c0b040d000758450385140040f801c540240c0568144280c10000825420079056001d040b0306802100d00200c84200540300e20307140ca00541d002900010200ca45034046041e561902155054450200d46000412000c5d9401c6400500c00d16503449843e6004000e6240e10425074241e80314500c604106041c60207401411601c101e200040c0a15150103554040c08100320300d400286410000901414400c140004140803e1103c0071054818081c003003007a40c9030020341e852185a00044046809181404010b420121003262104101148809000b20744480040c2401000c481d20394649690400e04088c00081d001040d00c100d460317451400030041031001c1e0160380401d82c000030ba40c894103d2410480081d200c0c040000e5004000c83c0103100c5503a0114204014401c001454062480b080d15201d68548405100c069445440c881e140300200b01c07250048443c03298002e0440d00655074078076955094895015041c1c65000c080d0004010150007442a40c02201507181c003000042d0802c46000360f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 343286717 1250 343285467 343285477
    0x14070b0a170403051c05010501180f0303112803030f0c120c021510090e0f03091009080604050a060608031606050604061716090911091f0303031d0d05 66
    0x3909010510201e0b0a01d03016800301d0b040c05241c81d607482a5101d000c03240201400c002c2c480d9a0000d148507103080d040c0000c00e01118242c85080d00b40006140c0b0b03503181160305500d8949011406d0040503046040380751014000c0a200028082d0008400150300b005001c0b00e2a05615580c8682010030154000f40d00c072110014008209000180601d40004202d160580302c50001c0b002803000410301ca50582074101036000c483c00100c0c140b10941d018100d541d19000c4404c50307401194400d00003681d152030094658408602c4914090b0101c50752030403075034640708041d01d068035140c01211a6034180b000c28041c48015011040044d80b511440c001106c0204001500250150b5500c01c045805d07643e0b950802c400030080181c40c400b01641ca6180503071101c4c042d22407540e11460046000070f044400740a000001600a0382002c82c0c0380c180c400740251414000d0901d5259000000344010002c1203116003030113140250380018243c1c00341f000c00b90b14032072044001a220b034080340f10080d030140d100c0c00f01c0d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 343287967 1250 343286717 343286747
    0x60a020a0215090d15020c070f1701090b13051002030c03040501050f060a090509070e040c1502010c050f03070903020301020a0e0118030f150204120b0402040c0e1c05030c01060314070b0a 82
    0x60245c2041005070000f13004180b5a0850f074051580c000401d94103a24122056640000140c4c003a0100d0345146800c840400e41e00801c0c51103150009205180d0503050030882500503801e807207520310307202851001c80c1d00440b501040b800001c028070041c046c0900c504d96020441c0101d040c0542032010000e203140050788907a140fa1a10f076000102d110310280200c034018242a0000d01a604041c68414400b807a640510a200d0510504889182d4414001d081111030141c45103440c0c2280310365400c02d9644002c00e4401800f800340d20000058a0902c02000c0c0a601540e030309400d1802603000402603492045610603074800c60401b480403030b4544010301d141d10303400b411040e0141b1610008901900035640110782c190f00d010400c00c00e2040101d055842030380b080790100001c0410090036503200240910154100105080d114813082c0c0680207a50380c0343c025000c1301c1c10012501072140c25580b042e00100c0d0070310940d183c01400e0000410030580a00040c3c050300d41442c4113024005c014044d20002a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 343289217 1250 343287967 343287983
    0x70905060715060b07020907050a0f11010b0919060501050304050c01080405160e04110402070c0603050c0f18180f040b0c070f05010b01020d090e0f04020f060a020a0215090d 76
    0x55020026094440e0302c5042e400c41090003115034a0360000401c1d0441082603009400c60300004000a106204403190001740d80c8480d440300e0f49201e011074514031b00b403455000c59984d0303c02001190361408405441428a0719107070740010100600780d030a481665200740d042c1b003402d1090100107080400c140b0b410301001c2c40e04140036074682c10304c3c51402c0781e0307603c000241079a82e40010400c1c204143c1c800c0d1043c0d0060803110041c0440c001440100e2203403000182002501d8079040c014031340300f074101941218140c01c2090402d8a103001100455009605100a12010ba01601800e044c01c80203400c10b4440c00200954600d404045d0019031640280000d21500061000804c003a01e03000907a04d45907004901220103400c2e524140f8000c00010005502501c40d031030b103e6120707501c41c010540542c0c0300e071400304080e91200580002d503400050800c0717a104a502c03440c1c00d101d88850000d803100348499802040c5d2a01c1d1801440705914030040b074084800805c03c1601c0c0c9541303031810294452070340401d039 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 343290467 1250 343289217 343289227
    0x10080705011b0f0c121109060d02010c030504051306030b010e060607060207021f020105092e0f020c0a0c090b04020f0a050c011d160f150c0507030804060c0b0a0507090506 75
    0x31514035441007420040c02c00130002e01c082061081e03108400c0b99240f00f1621184042c206d0000c010045000b120103a900002c1b44d8245e9005502c1960b41c0c0c0031162280c104141004d03251000070314401c825090488060f0f070f80c1c80b020400d016440d4070003401400c09195840c0c0c18200100420134a1141d41c0014103a590001000411511841c194001c2d0b01c0345a8010302040c070400400030301900c000c0c1d80750b140505c80c0030030120142501000c0b10002c4c101c0c00d48080401420291808042d04102c6021a07030240d0a1041303804901c001c1c803100c1407142c41004c0400d20309080403d940308641c03c00196600807071040c8001004468003400b183d1019413a400d101e51100e0038194540c1c0540303070050101e8804110414800300b034400000d0040340041c1007108030a59941c41360300300003280140b84030b0300701c10059010b01c0340e40250160001e10b0980d0300601c25903000a46a0312800c00b40e03445a4810070005100001c15024032809640c5960000c400746003d200c1c40c100b4140c0240124058001c8521a140000d1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 343291717 1250 343290467 343290473
    0x1021911040507090e070e030303060f0a0b03041b141309060f09140c040b030d030506010912031e0f142203050615010c0f080307050408030d0510080705011b 69
    0xc048030030220010014003a601e031000000703241030460303c01c030396101c2d0024000c10781160244000801881e4058002c2d4215503035641040404079402001582210b03017804080f900d4800000114461030041243c02c4195503001d05038000c072000380d400181400c5a4811060326a501d120221b001842e00c03e0000c9a000c64505000b070041c0300f40c40d400c0400d285407022034010040e14400f0104903a440000f6601400c4000d01071009a680042d4440d9040d00880340e0002a1800380d0310107604880f040c90f1100c207450f288c0b2008484c1c1c0880c42d4058011034800780c10400d031145402c0b0015280600380c9000c1020725031410016002c40320300c0e54600c05200e40410640340f2203000d42106030032a084030300403200d01566410701c40e840d0710701030301d43c9006a0083d1032080015409100360843c10356010002c5000c3d2221a140c000044c0c00c05001c1c102040340811000501c81020804ad0040d804e1544002030b03141018240040c520009a000e0b411541100008100d5607030031600c5809049020410001c561000b89 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 343292967 1250 343291717 343291733
    0x807020d031d03030a0b1311070210090305030f0d0b220f2405030613050a0f05010f0203150901050a0605160501061203090e010f1229070e030615010219 67
    0xc4982c80c41c1c1c40040200a49044507402048401000756144100c00f070340d1003880026201c2c81d174090340048004214003801130500705540c0340041c80744d1520315000781e01c070341c1c9075415a4051000d000d02f4a902240c004410b4000d88510300c00200110380a00203034140f0010030350050304242151a0b00c0d692481e07055900345d0705070855003500144510004071000e98001d0305da0a200d040c060f2038001d202e00e90004103142e0310300030100c8401d504000206081d40540c1e499820704000f4503c1243c880d5220400d501442c011400030310b0066a4640c80000d00b08103d0b818803101c5801640f0031031280e1494a800c1080c0c9411000300e50407005c5114010440d40054240f060240c425944450034110f00303070701c120052503840b1202c442954144e8404c4141c1341d99821000d0203071445e0b4001c00c41c5072501c02c030203117000651700c10140702c44020740403a071031b12400f06088007094440b04540140c04145803140514483ca014403843d94041c2803c400c05202404910000359998100c181d0000310713440c003065070018001c0310 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 343294217 1250 343292967 343293011
    0x1101090503030a0201060911030c0f1c050124030b0603060d0206040302120c0a06300e010516030c0206150f0102031903090320250f0801021201060807020d03 69
    0x58100c9a0f241440d5000a0084c0714038815043c14500c0c044c0750f03070078803102c64048a020705420a845410503c07903605120082d03001284500d100b400410542e6801130450144500a0020340c4809000414200f000d0600780c0700d9a0f00394080620345603000c20207030344d0541601d42100e0166081042d944803440410401c0c0300d80c2d0000780d0b011000003500100807000081a1078201010794080c0a0340d40e642006661942c54000c0a6041780305501089180e0a14045100720026030754401064045042e00e85500f142c02c140d46000da40054414035424040d00b502681201d080c2520007058a4500320211003240890302540798400c600e04800080309a100b0070035070343c0f84040e6410100da00d030740303008010b070041c1a0600e00304d003c102e10400d021a40b1b2210072507005c1d40107900c0081c002e400020328504035680d0600d000c05001304040440441e282c1030222050000e40089400107a80300441c9141c3c0303019141c141d000340708000c8a407003042541c1d98007003509030580b0f0b40c909011542e04006441e10200001c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 343295467 1250 343294217 343294219
    0x30b01020a0b160e1804061d030a05030a0f0c0201061505041202060906131401020d09030302060a090221030d0b040504021e0a0312170c03011203051e120f1501080411010905 76
    0xc03288002d400301ca001500b05c2c1c02540b01d070a04100d1480712100d402c80c604041000d05805800a110600089001e8002507510a00124000510042544a040842d41c880c843d241c0140c0d03541c81e05112045c1c090008954003449070901a05041c604800b00d2051091070300c000f8003502c80860181c0c2583c680c00d0944070502e02051164540c0c0b0f44400c40a22400360300c00e4075a0041c440c0c0d0307005000003401021003000760398241c1e000d03245607a2641e00d19805050881307402c0340c00400180844d0a4007a031001c45407508030102024555a00c10302f0b8021042d1034007048c0e442d1042d481e0005000c01665920344c001e400c1108401919250070152002640301b0849a00203000e00080341040568554400700c000c600540351210000a9201c1e60701218240c002400b07061174410345d500b101804070b80940c014064200d41d80f010146050184121302e00141c1003440300002c05d404180c24015115025052168400341001081800301d0780e51000038004000640044c1c00c6540c2082e41000030b912030090a4043c1c24 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 343296717 1250 343295467 343295479
    0x40b0426071704030f1a0106050f180109030c23031b01180902030a0608011b02070501140408070803040f060e0a140f1e13090b0402062203080703030b01020a0b160e 72
    0x40381c1c0c10b0407900000800c202040b51b56a81c400890810b0103441503c094800c58031400d42000c0c940c40e0191025601061041c0c14840e9036040000041d80c0e03000b0f0700c4060405d0b1403544580c0d0320000740904086014940013072103508100040850304405070302111056200746003810315004a40207a80b640700c80358100c8150140000200204d180468200c10219100710008000780006030814109509401500d07000580003110700708600d40c468011180b1210207502c1c0300b8a00b507620002e2516004a40c0d11454850f00b0106080010740c030711050031401000030742001c0120b121a400021054201030141420204110303020003c29180d00c81e140351044006001a000070384480007003944601c5100d04a0b124121104418124100c14020103402d19880382c00e84400e070700d4076420018150445c0001008456040003a100039041200383c601c019401814001d43d22012820001c003a907224564a9040d980440030300c00019058100044d0300000ea4228044c072994a2142100c1c102000d0410a41c444 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 343297967 1250 343296717 343296743
    0xb0613020c03130915140118030b04031e1e030912020a111e0603040515130b0c0309030306010e0301020d06091b0908062a03040b042607170403 63
    0x200815030007a00d21010150303581d003030380c4c003581d40026641c0110301d2078400070400a43d0b0341d05140c002410504001d04101400c07140b445115030310303034810b9415130314030002e00c01855049000b580078050703a07100310100130300074a4015062002c814414461500b0045050300a90f100764040b8021a030301c80f20010315014150710003540d400494a003510903404a4601e0050f500c1c040d240b00e0442841280030034a411081401c008040c1c10061054555000b400702c00030074240202c103094030aa100c500311f401d07215028100f915195000800003001100104180201250300100740d0364414000d280c4103450030401c0c0c01182c00381c001c0c0414030520f142003140102d4071140340e402130001250304a4003d078940354205011a140403192103005215040080417502140600c2d15014007019800c110000e200103101c281c45035513004450a88184071745000380020000107041d8121942642c05404080c04405484401188035510340140368100300b40100f181d00031808243d400860700520818022 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 343299217 1250 343297967 343297987
    0x40f020f100f02161d04080c0105040c090b06070f1e0c060203180402090114032503020306010e0a0308043807051504030c02060c030c06070905010306060203030402030a0b061302 78
    0x1644007400c002c4058010001c2a03001e4050440c42502110000b80d124075003801c0582d003802d10074a01a00036030b40c2c41d808210070a070810013401014041c9101d12581d00440e40340034005801c64081e034054504c10441040000c01055103081d180e0001d5810401000b42d5500741100c40725050501100280314464021b800902560044050a40c0001d40c144408410300968200822449524666130200d201c041035040e1100c48940503650000d241e42000c6042a02c80b200110013104c13034040080026000010080740b035070700081c1644c4410041d900b0288030f504565400060f4010b501841064501001c070710101070b0080c14540c03042101c0705074445134540000054448bc3d6021860603607040c0f10300300880c003040d9aa40340c030074400e54150340c034009032003450760030081640e0003170000f003965110902002c050110280708240c000e41d21a00d5081030741d490040054103a0340c9607803010095400900402015032408942c0d0b030705d003e600c021500043c5d40c45900046881110500c4011600d10104e105181 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 343300467 1250 343299217 343299227
    0x1e0601060f080c0f03190f06060e060c0a1104022703010507051611060904050f040510020f090d1a07030e07050901081b030c063f040f020f10 62
    0x1614256a900d601ca0000120180e030b0261058070352052070581002000300b13441c00c0300041c3d900410340c04210002c542c0300c801d00405951207190607414113980c40008014039600b2211040000c8070644410b42000041c01e4521380302c1101c914041c0004c0c5a4401454031a0b580b0f90440b80301c1c0b90501c00b00000000150105421a01062400c2c1c0c020b40c40c0c1800300e4007142c00f83d800e64051381144d01c00d8803250815070381c0f2003c0041c0001002034000c00c0038842c10005640d103020746031007034698130b24100b1140b0305400d007141390424141c040700400e44104400300310052140b04650b800007080d500c2c2c4000c003d5600c1e0030313511644501030910308480c5000903c5012a81340c4c00c000701c4005010211600070f502c440400042c45001c0c0b09401855010350390101d084203031401c013503000302c100800751440c100b00c9401103010b40e4884c101690003414041100304006a01400380400003907840340d02c0c14585a01001c140380d0690181000d000301180001d002d0031507442030303c800a80500074080d0f5030300103c40140548 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 343301717 1250 343300467 343300469
    0x6060513021b070503061305010603060c0e0f011d1521041101080105090112060b03030301170f01050408070f05010e12030610020f030a1b1e38091e0601 67
    0xb03881040e108410102d140001d0080c203a68008000c1c019075122140c140c403070f01c030013204110f03929502e42000101094040c440c2e81e507115903a403034010558490104011304142e0000300300d81404140d400303c110424204905040404040c0c174101589105e100420b881801540024107a003822200800107a103844810a8050340c4034880d102c2c024900d110041d11440c1003401000e03005501640100014020303a8040030816014540c002690505000405d045030710176000341003280d841c0d8000020655040140401801d4054000c00440c1405da452030510320400d41d0241041c03461030410f90512101303510803101c040801013100c28401c3c0100301401203400440d0100e10900f00710054511440c00800c80d82c4005204201641c5840720086007981c9039420041d030000c49150480b18070000994421808103072241c00c403003070121881da80c0781c001c041d602403c1c08428501c6070b01019941d12a00c502e024640e030909c000f080c05841d645d00b4112868441600003001c7c0580300b9025900300d1150204a0314 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 343302967 1250 343301717 343301737
    0x80a170f0606070803180d02030a14040f090e07090501031a0a02160303051308070b04330c170a0b03061501020714010c050a030207290a0c0606051302 66
    0x4521a92100200040c4500440c0c0d01504401c0400414000881110003035510045294100300c1859958030a18039004001e1b07104005a0300c002085404107070004000d01000c001d120040c1e1809080101d154000c24491146007086501c0e482790001101e82030103010003a08880c030003000a03603580e08006025010041d148814140140d0200340f4515650003200c0002840c0200e001020115540440042c24000c01c0700303608440f090600c00009402400402d18140030b204114100e0800e410301c1003645e80702440140c0f00e1942c6509410b50300c0c04a019a01c03417400ca02000254034960802e003a5a1680103a003030341141940401001500741407039219101408007a02110119641c0e0800451042101c0d00c0b6180940c0c414602040701c202000c50315412000103161244213443c20b81d03595403074003200707804c00c40160b00700b80c1d402d000801607003c000003810341030f880602000c14103503030040151080c2c0d017200d0308100b00141004103201554000100516028082800f81c5445c00400d03002500302400907 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 343304217 1250 343302967 343303007
    0x13020f1219020313031110090b0a060603050105100302221805060907090b090a12050d020d020604020d080d061a0a17060f010f26040516031518080a 65
    0xc07541c5101584242c81c840e0f450320b5040003590340710b5241600c41c070718940380341c1c200c5115600f80c080030103456004548845201c1c0c0c0d4a40c101e81080b02482d81503d8140d04441c080500e0400108900d40d078500c41103031a215203041c0140d981008205000121415030030b0710300c42da05540000038034441e2007010340a400d8450340701002143c03110f038104812003400b81d031084000307907500000b8008904190010501810001d0101d41003c2d500d0f00440940c80c825402900c481c1c0010341d07141c00c5207405001c50740064407a4170140009182942c0010040794284070050103107200032800040044803680040041d01215a841c1205a508034200c01194400701c4103e0006080360b85207501c50280d01445800707040020008142c030a005001100e80072202c8410314108030000006030f0780141032041308121000314400340300e910328180c03d20a1510841903039007030503038004480800201c3c0201c00782e2083d62800103000308a0320280d20345170302c081c448400c5c003030300c14500011002d0849401916903414100601c0074 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 343305467 1250 343304217 343304251
    0x60718051c1203110913140a0506090a09082713150602061510050f0f09010e010503100e1302060f03090609030c0a030503040606030b0f04060509010603030c0213020f12 74
    0x104805981519000e000100d800384100c00c21490006c0f055118450404070004d2004460465890110300640300c0ba516542e43c0d800b40610360130300d0558680e00110502042c003200e45981c1c3c50004921076501e5000711070710381c40800300b0305941d4040c50580700342c0002e120480381001902e810009111208041d02080b40b001070001d4040d00200d0b42074820701d1030f284607103d24454842131240402c0b40035645c5080190800c0b2410355510712001401001c260003a405854010000c00501505601000541809010310810030344050825003441034038500b08008440d41c541030700300300d40c0250110000f58070a80c0807903400c07000301c411030180d8031408218040310030f503840d00412903440c0d00c80c04a8460f201d4100d4441c1101007409000115001031260310f000072040d17941d440c1d905411405407152040301c40c000c028001488102c1c01002d80140290008009072840d55801074088200144024080d03c098011605408203a605580c84042000c202650f0303010240511902070000b142c41c4041d00c203005070 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 343306717 1250 343305467 343305503
    0x209120f060a06080f0604080703030e0a080405040621240f021e040f03060209060d090609020906011b020904020f09010f080d0c0c05040f0f020d0b010908010e060718051c 75
    0x40c5182e1074170400c800303400e41d500c884d281c40400740c2c420034003034052584442203c1e10780700041000a4209000c0c01095855134105002c03c0144d644070b520880da00c1d5500880c44101510000b4299082ca52041c48140101c40440a840002400d0810745101904e040400c540005094000b480101400914190007511124041e089402030340541c0e0380740303a0b46900c107000040c8685c0c01004180c1d0000c2001b801d06c545488481c0603144812401c41d00d80b42c60303c44260441c11b0880d80da64010000b400c2c40300300302d203417030281d03441000b100c041c080e2141020101107015500c410217034004042c00504025103035a1920a0381000820502c508001c600c030381000d03284168480c03040460344a90000302c040e0414541402c200181c40541030354003806030b491003040c40704503061006011080c074000c00441d07135080c0f91002400c121000d03400010f150b410a55203c8400002080c85e0768440903d08041c0d50600840d11600b07131005080d08056008a9080051050490808601800d203445802040408010300b8 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 343307967 1250 343306717 343306723
    0x90603020a15210e1603050c010e01051e0409051f080f03030f04021f021c021903050304030c0f0507030618020a050906060d050c190906120209120f060a0608 69
    0x2903507020010f0444030a2002c4007038441d40e90003003c40700043c0820440d41c0710903007070b0420740e80c1d00a0b0403072214a014200100a41402810882c030320900303004441658007030020704a4414090010746001482d488044500b504078141d03005048001010000d52500049245109402084e00c0180015040b0300261500c00082c00d40c00a61200000d0b6056482d000342000c4d0644000d0401c0360301501c03248145013100c0100b401303402c440c0010340c000c201e8501c0c18403014882616050784d440c04c541041ca101d6460300b004d4078000855690529000d81daa640f40e00381158a031107a5100140f0180c5c6100c1d5071010700000240d00801c0e6070150104006240010400d9046207081440c020740003840400701304298034060038640d034000c4003c2c03c01890013040c219600c0c104d9004a403c0c0029030710200d0783c0748411580d82040d403911061400e01034402802d224026103080d043c401a44d0415400194a5019840d03d000c4850700458610443e40d050280e0f881c0144c84140454045000d00d16040c030000e0094800 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 343309217 1250 343307967 343307999
    0x1303060228140d020c0102032e030f150e0d05040e0c041202011d060703270e010e0a06030804080618060601120203100e0c0307030608060114060703030f06090603020a 73
    0xa0b40300c000014208005100b200e802107800848519402e0000041548081c00294844c005a00c09065104640c221b040891003600c11142498001d00030305000040c1042c001c004138070703041122441003c5000c14000003421041c025210700d80203100c00714400f0b64100c0701500594001954004040d65900015801c80c0124820106642401c40c0c121025500504200c03076079114505c01a0682158400400d0695002500440000e031014030783c54a426001604001e02c005601000c07d001894401007801806045c028820709801c6140401d030741c480190311100003075a0002030192a1942d4458003520b0b0401100e045c10410007204050b40c0303050b00458420302c40c040503111210800e103070a04640094000030500c407018591100c000c54035040c500c0d84584140c0b00fa0310010381e01d203440701d000ac0c282ca40c140e0007640c05901c48030045c00b05201d1040b4903000017034140c1e074054554010342409c0700a4110303d070f09000110f180c03c2c404036a03001260442c406480c0262000a0702641c0c2d003036003403805c00035 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 343310467 1250 343309217 343309297
    0x100308120103051c0f0c1703090c1503040209063601051e0108010b0f0705010f061a16030f0c0b010e01050103110903072d0b0703080a090b010e0c13030602 68
    0x10742c1c0580140c005c61003c0c6506c1e006061454a40e0305c0216883d40310f5005540703c48459102c000b500c481441d041a0442c0b80345151440c05041d414180d0200717009002c050f043c0c40c42107d130079040061031042c00079624095840b902001030700885c1030f401418855030038000d0301e000f44c0d103c1c07482014648664441c5151110184d4411415030310b056848401a042000c40c2848070404010070310100341c09010310101c45030076050006000345000a48090305a0b080100c205011052214003200003240b90351980b01901820081c98454402d031044403500115180100082081030000c00c200d6080d0048034103903002a00d0411000e5510803604810b40038582d490350781030340800d0082c01a00c645806c5455003603154065090070280b405c5000c0c2c074280f4543c00000005801240c084185644107600c03030f81003030504504208843c07150301d0304580cac0b00341402034400380a0101e001c20705041d00d001c200c502c01a07410b120400550303120b240c180042d501c082c03491039810400c40400d40c401868581c0045107602 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 343311717 1250 343310467 343310477
    0x30c19020f120a1101031e14100e010501050f0721020c030f101a090a090303050c040305061303051905090a06020c060d090606051806040c02010c17100308120103051c 73
    0x21603136a80c11140b402200c00302c0c1c1015101c0018030211854414500100110100040f03079250043e2081c01d80018001d2240f1070484031407134200440d07145032400905440f070070301c0c0460b99100401e1114045106618000f402e080c40c5c1c681000c0e085801e114040b66000059081e1003150002c44101a0380314170b4024400601c0c2c009a00c0202d18a804e640100c0a500000c40d603a000444e2580c001410b2010403940002081e03200e610380c03410140d0505c180703580009211001403c0038103584515980d450000c1c0080d841d00200c0f0841c00616000740300741ea21403070707402000b1502c07c021740764010180d07008200d815028034628400414100d0012071001d01119024001394107242e4000c3d40c100103014182c00c00c1e6071540d62441d000c90583c88100d94170407140e050f03400c3c0c4070702414094140b00031901008800b40071a40b409425400e117542c00315656403400306170f40c541e005540342c5400c4003c040c442ca520052515400141c4015401c4150201a040300c0c003c10540b581d0f40d0b21140781c082e0401031408103030001a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 343312967 1250 343311717 343311733
    0xa1b020925021627020403050303180d1b03090314010e24040b0711060f090d09030506070c0c0e0403021608010612240e160522020c030c19020f12 64
    0x298540d41c00c000e902c0c080301181c5000090030700d00c0000701d81c07261f0401d0712584c100204201e0030b074200b41c003c0003c200265004141c030a5080d1002090688100c000403c45c2040400391010715114040aca8083c68020310001903842e4036013581030007468068500c00042c040c40920002c030300511404004210a104c6410342e030b6645966a0307140101d4001c5c902e00c01d0040c1e5981a009024041100520904412184104905203030f1242407604a074001040100302034001d05000280001c40c0c1983c10565500304480c001d1030600c2d05200150183d0048008510a08200f100345503000800a41d101e5202440101007900c80c24020300382c4405021b000a4550600f090400054400307903c1900594100c01881d00901c94a0321f5800742c41001d6010381d40c503407081041e030021607100300c01000240421035044407000b101d14220f1096410001070503580315400314000c045083c2c280704441401004030f05551940b441d0b2218801154003402007640110440c520b4081c8500b400d1401810142e1210001c00300301d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 343314217 1250 343312967 343312979
    0x60904020609120a0615050405070f030c03111c0e0a03170402011b0c05040f15050f01020a23060703050f04110102160b1903020307050a1b0209250216 66
    0x55403051403440c3d00b144107200e611900e04001e001e80390640d44110b170b010902004017410f8221103510703504000e1141d0301d0304040c481c1c2c05821802c0c500c0040c0c003504022440c06541c80c001c0d0020000c0849504400c10005820024010021400d940e003024014007041900643c0101c03a076190710701d0708010046200307803103015040888a1095548144149040e5441d501081155020f0f031001d03607801c461344c1400b284103000234070b0580203001185030060401c010541d4003c4801c0410603c40c420309020b2035000700840016482400703030000703042c2c00c607034480340c1440110b0181540100c2d5011100040c0240c0e00400c80c3c0718441d028071805001c510341d0f65001074170381c1d40710410340c400301c90f854505620403004545407155260480307400a2680b04105a11200000e02d0641405090a0584101031042040040705a0880705966640d082882c14400c0700c03010070703100350909001c494080d60041a8104000e4404c1c43d09524484040b10007907906880280700b2026640c8102120000038800d031604000e01c00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 343315467 1250 343314217 343314229
    0x1716032a050a0b07030e04051302130906050c0a030b06040b03040201120e1e0709060501051611060f0c0d080415020c010902060d0905070806010503030a03021b1b0f0906090402 77
    0x100c88808860380a20307690303000202006655408449034603400f05200c414103401403050301c15541c017900d06001900e050b54000f006130503155402440f4104c442c0c0100c4a6076060b51280080c141d0100007005542401154403105801a50150000a007004902d284500305134080d1400c59140c0c5042c2400d54a1f158015114010b4480380a041c0b6642c0d4141910409010440c0c405582e48607111440000055178070b0f14200800741d045038500a04001042041d81da05c48101e860501c0f144450300300050061402d04903900c5010441a801040443d5460b0814a1030000b041e0440d005030032942c582d459181b081d80c18207801c4a01400c0c10070701528072510544190001d187c01c01c1da070000018265441d81c00100b8070341080520007011a0b56824039800c2003810401f020107805542c000707085940c0350100003075480c130541007088101a004510032130f0501c0070000c0c3c40e0f85013200c0702c25141c2d041d6041d0091036a410488803850720801542c0407500f01c900b0a82103c901521003c5d10085541d601c54080c004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 343316717 1250 343315467 343315523
    0x1170304032f0904060203060109080a0c051203040e01060224090d1803020a030c0302090f01080c010e0d051014070e011e020a1a0f07110a12050c0304171603 69
    0x905180020460042c5949043c1460b2040703124950058503410100001040c1c80201d400c250107581c031640040b800300d000c0c0082503045130f00454000c004070340209680c2d401c50007103138080c7c2c000284140021641503000b060410600311240d807030113040604200c0740040352209907444616600504282030846101c0c03031040407040448607a41c0003803941c07a404540f5252aa6001350b480e0a19a03600b0720440c541406403680064241810007800d5040060790b03922481d510791900e05100765060800203d8584030100220703190001c06884e280710f0a4040139011306039480155074641da8100000f00020300803154106080310680d210400b0100300410004d00d015519500b03802e5210b60702e503100006040c01e26800d5002c40a40c03003c1c0460501c0b48003d0b48070351000d050502404800100301090314000901d2002003600000c401c802c000c1d4041041c0c55a101c0c40c442852940000034002c214264000308540500c01d040040314071528288910380c10030802400010082c1042d68074940000d00504501a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 343317967 1250 343316717 343316783
    0x615091902040b0a02070314010506060f03040507120602030604061e06080a0609062606011206020a0c0b100512030436150302040b1e0409050f0a06050117030403 71
    0x14946030301e60f103c02416801c5421280700580c4441001c0c0104070309010500e0100c00d41f0300081c0094280040090014003d48071899564540403000800340700007040a9801011a606452008603840c14800044c2d4411121240542d060a80005a50019804081d16802015211203c0c1801c1c500d040fa00020060914039401e03844000200740c40e00303548a26030003404d0041804842107003845040c1c480014060513010075400180042000c0b611141c00321804581c00100180e88547ca401e081e01c01c0c0090300c00140a042568040080401c1a06482801d035101290b2445c0040030669080d50f0b24071490140f140c0015800e840144008143d21071814460f580d60340301c00203218225892422240c0001c01110359600d02c03241001075081070311a04040132420707507000c0103030454908040b5002d0100c907102d0b40100d54440207070050140a201c4c80f26a821003206031484100c1ca810104058030080c0140c3e4000041016800003402c3c0000440301126880200040c00c54020a01e443d8401034014120b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 343319217 1250 343317967 343317971
    0x40207061d070503100e030a05070f05011d010b0405040510090507081c030515030705010f090e0a02030a0e030a09060806060903060a150b12060607020a050603160206150919 76
    0x1c0749110000e644001040100006201141c80e1004241c505401110110b00062412400140c0c4000200413550074070110300740f084da28501c0f40b40000c014030b00104060728552a00074420440801144103014881c5044002d00000e4545400c100c2201e0701560014059807051100c1040040103400044c6010b000d04151001c2a40d1000d14508245000d042c1514a4080301180400b607605440f5007600985004010305a02c184000400e584030503500805c0d0501031090241d030046881000c070140036185a030400c00340c90038003401d1840170350000d94444200f1810041b00d5618281c00000f41c1d034500d40c042d0365600300715140400035130300d10720043c00e104d0b003019040180c0c180c0c0d614104072950149075240c1d80003e113404c040a098103a81a1030304402002d107030400c806048034003800d050325000413040740c2090f80d4034002d200182c203103905944103030382012000c01000304c01c00c1c3c0500030160300e0550350250380f4142e032040081c5101090701e00c0b0081d8031141c07040115001c0c0c000d51a007003078207107218040 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 343320467 1250 343319217 343319231
    0x50709090e03031f180903180b03040b04060f180b0105030a0314030603120c060f01150215090f2a0103020313030507050c190f0e010608060603040f020a090b010e090105060904020706 80
    0x160800070190800700c8851b03460303050120030190b120f407100d048206c40d0001c0d2450581045144502031101070300282022418102080510101d42c0c0203441074001d510b000c02031003105c00841c400442411b00c0540f54041c4c0d1302d0000505d4100800e084c103e459059070b4810007010700c050b80d0b4142d5000503102c55014072130b03809040100181c25000708030b001540c2c0c0c010003e615004c0084120024140c000e1140e030101d1101d256859030300010f0940c0001c413620f80320742c1c996a0b0000960714100c0c0066111189200710150010110307010002a1907131081d0415034424040108019010f84c4000d0b2600f03a059003003407a0180210340305d1005401c08500c9501030f210300c541080700144002c900c0492010300e24008010822800704008802002010802082100740d131605a01404008004045078052640080028200151409142051a8000c01c0d40000580b900000c000420703441c1e2001d4041005400640ca407481c20060301c90403104018001858195210180b00207504002d01c12900b84c0e444402c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 343321717 1250 343320467 343320479
    0x61306050301060f090b010918020a0e0d0b22020105040506090d020a151706030d2607050a03180506280f0207020f0607120f11030d050709090e03031f 66
    0x1000c00425904e100c201c038550400482d00c0844441000d00c50520084210030440f140b9007415029401d0185e21006071111110034060715100b1800b0903155010b00c03002d01c084104024201200d0152010182c01140202d14a401102003a514580640031031000c1c8020002c510304007000f04540c0c04041c0015010004e07e5001c00c061502c10b400c410035841141c51013404003a40301401545645007511002c8040c00c026010035255075850f2614070400c40060300c08041c00110800044840c0007100c0310901034500060020300c59046054800006806d2000c1c86100d0048102480f88058129000d0030309034544503d40028403086ca0040d800303801080c000a01c02520600c1400541c1d002c00300c0169503080075204125501b1107920455116840612070039003c41c902e908548040345560070f00d00409102c0200c1070303400d00e45414801b0100c1c440090b01c21054003c9820260040d541e540301e15403000e88824690054810f0040c2c1c2090700c1e402400002d0740b10b82c8840341140d40303511020740703084990b480d0300d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 343322967 1250 343321717 343321721
    0x131e0510030f290409150b061603020d0915020d0f030e1219090812030606090402040305011406060f090d060212100611010207081603030b0913030207080105010e061306050301 77
    0x42c55100400d84581c8104000f007181481c03400c80300c0000c5600700041d64999444074200200a00c61100840c1d88070340c0c0200c5900d80b941194008190f8465540c4400c0076403400940d07407102001188001190300a0000d00b0384401c5c0004407080b2150303006402100f05240c01202c100c0c801c008100d04140e1150f4817141ca03140240700400141c0383c0c51120340c0d5605c8201c1910a41c0301130500d400400c0102c030040c10000d010f4045608106101081032481d83c9803076603030000740b050040558143c2d02034400940001045815403100c008000e81081e40c1207185d90300d4041218a020716000c80411903020081545145401c0a0740030315688180c6005040903400d20900d200543c1c1101e5129464196410900c00640c00081040d0740602e035100a5141001c4d030358581070300f8000e0354a194078110000d0615002c06010750451045204058552802e038503180c10034a249011014050b00540507040000c00e8080060180c1416170f80c01110700c0f9200d403601c806224030800d03400100400700395034540100c0d883e6028 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 343324217 1250 343322967 343322981
    0x9030213020406031401030c0302090c2b14060609150d02031819030905090c0712030203070e0a050a0e070c080406032c1b040e03030408131e0510030f 66
    0xd401611181003100282c11a00090114407044080341d0042000555506014054a50580d00792002e034031003040c1a062400351500007607441c0a401c400b60702c00074060318000181007241500f88581030340d140c9003240c440c9044d900c04d90003400402001203a0708040d040002e101662094651822070401119400c0740c2041d01c92211a04130b1840e00001c052040120881c05005aa26100304040ca03135409480c4110340d200f040d001e0f0403c0c2000811004d80c480c1a2007507640c0003000e00005481241004000394821a030f1800401c011511042490a10303050420682d0005080808018105090f201c60303004001c02d43d42c00c10a00c0f942040010f840307440a40020541c0d51408600240c03004680304100046d030782c10b00001041040340c0702c0840e2001400104030384910065400c10001d800c0464082d203005500d0585521000061004024210000340301005650542c2c48103103842e0703070205076000d074034120360039200300c282c1000e200c0c80c036207801e0684940040d410009502c2c2003000a94003680c0d84 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 343325467 1250 343324217 343324249
    0x120105040f02040c050f0307180302040f0606082d04060b060a0201150902033304020a120b060702030a151404080901110718020903030d0612060f0b0d08030601090302 73
    0x1004141411070405001d0400e80003c903040c0b242c24840c806d80d00000da400024250000c0200020307888000102c0007103a00040d40d0050410b000e4140000c1c000005031440e48078510005540d040002c106200c18038240b02c1d0324424401180b1510716250351140036500141c4140c504641d02e441d81d50084e035400004240002280c1c002140c0c00c02003c03030011095402da405003600da0b00400401c09454084288174041805680c20a100c00100d07080e098000166418043cde0020300c00540d007500c0350707000501e0382c1918103422002d10650154000380011401001402500340c1d0015156900190ba0070401e2414005010f00001c0c04114440101b13501c2841540d0030348100c0c1740000d0803409542d00071080b030501d2070b082c030003803222615020015000e071180340b54450203e5400b09041000d60b40038000c035255104041d0b81031061903200e8101c0c990600f80e14204030380307442c9085115505214680100c62030342d440101b40602010303081d21085405e61009120700d04014820728080016a83c8848061311020303 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 343326717 1250 343325467 343325483
    0x405060c07090501090b0d020121060b091c050a0b040f0f030e030c0f21100c0e010915020a02010311070c0305060604140103080706020c030f211612050612010504 71
    0x450a80040c0c00c032803041c4c0000440c542050b41c1c0c003200340c40d0310344861f254603820302c1c005150b070800c918400d080201034807400d4186420700307400041880c559000b429110004a6000d003070b1f240c01502c494403461000d00010b00303e801007003542c000310f080c00c18490780c09400313080000c001d5910344c0d03a108070f034140d0011700301c010407480010b0b0b00245c00c00f00000842c0000a588440083c24100d00003450324a01034000ca0402c643c1045000c00d11500b4024801d12407401941405402d01c41200a4100a070302082c0d240041d8260305c0000c2d03103102281981000b580381d82c014000b0308a2a4004401502c0040079030010040b04000180018110800c103400450007000a007002d8205003040105403030421184500014120005001043c8028110345201d54041d00043e95000211720702400d60080c0c4550130504240491070702d4020724540103591982034000fa40700404d903100142c5103070301c000184000d4006061506a0840540e07140e102a40100000b09a0380355203031410b083c6030135606d0031035040303644c42 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 343327967 1250 343326717 343326719
    0x31308060a0501051e040e01020702040e0a050c0a0e0109110c0d03091b030302060f06030715050c0d050a050a030c0207081e0606010f08040605040f080a0203031501030203060a090209060405060c07 86
    0x40284500c2e030140c44203c6015001c10380010307050258401c1d0842480c45560f0b00c00d0043c003d02000d40c12608200d6000c4c0c014881d5031466540b5685465550b042601c040c05052031f03080c42483c0c00228041510300808458980c0e90900c6480c0005141070b034210700b01c0e12020000c18800c1801007080004c5001a660b01155000707141c50210311a84100c00c02400c0c100314000d0600000e038000c00ea181c1d1044203080c1e449495556040000e2914106501900041c0c6e00b45030700c2550598004000c251038941d075000c5a0038502c00c1c000486251148109280014006100c00c03c1034612035040070b00712804510481c0e070313400d850f1101300f17041a0b400503041a1050142030034200300d03039017480030562000b070900301107009400b5074601034146d020040c030080000c5d686100040401c0030800351140c9150301f05029588680700400081d540b544281c403001d10001e40d05817072801c10341c170034002c03207210320f402400309044207240500c00406900040403055110006010202d82c907101c1001802c50301007840c00500c202 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 343329217 1250 343327967 343327981
    0x1415090f01030660050f060415021b030c0d0b07020f03040b041806060512090115090f140402030d030905070503060a0209010909062103021903030e07120f080c03130806 74
    0x400003141d0b5561300d54443e610300c5541c00f0290002404880b0f041c1c801d4502540700d8000201d1030310980c0c00c4881700305c0c25444603c0700079500241c0c000001d001e00240204c80015113041507030ba4500e00c40c0030340c1d21080c1e151415000405c2d44c1080d5421241034011589030002c41482a030441c0c003e0740140010340000300303040050803980c91407003592000340703442040724030b04000e40100303240310701c080403240c1c04501b40101301c0e201000d50000078450851014800c9207a00c1d10840c42c044c1070b800c255000700b1410508500240c05440c07a105002e15030007402000b95841c0d41c001500942501034082d203542c060480005800d03202480005e100d030700b200703e006a64000d11b40000d4004000758100902c81c074903240f814000d40f40075042480440034109614a903006243c07400304e14001138100080c09009164001c0e5042640581240c2c0d030f1902510706413062280c50391410b800301252814043d2031420710f0103040e804218402c005089044844007074a19048140902ca6458411580040100c0d07102108205030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 343330467 1250 343329217 343329341
    0x10e01050420420304080306090108010e06011716080c044a03071b141305101208120c0f090906030c041415090f010306 53
    0x100d40003100d1040b040032820400c00402c84a864140c0481c0e00d1a40012524810203003075082c00c00c3e10102031540d039244c10b01d41300403190419070700301380601c000100100e8041010b0040c207000100d81c0000740b9550b1b10303100e44880748142107182d1440030302a0100c4104c00c900c1d14240203000d09251402003922100420a12084406006054400c5040c0e0310114610040ca11941d4445e00b101d2034a10b07c0004000c0c1c03050007018210024402035120024101c0100a015007100740c451412040e266010359484003a8064800d922503056403051220a62070304240702da50156402019206901912a44031071a0074200048401c0548600340c000c074042100407006010103902c05050741c4010f041158884e0100d616010b20115031740705050420004016460030003200300f8043d4000d100380503181ca0b0401c0c100b001d81c82518040c01203132a8139426250f60820300c10541c003c2c94051840c0002c0da01e55101d2000900281d940488250030b440552880c60f42e00d60000d40d52500381680c030941c44400c60f612091 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 343331717 1250 343330467 343330523
    0xc0306140609010906080c1b0d1404140904060b100203030406060504110a0c1a0a1e090309180f3e0d0f0207060212060319050c12010e010504 62
    0x44581d03000c015070305050740e000c5510700441c0c643e801c11221680b18407900705550b0003000e0404c2401c4041c03039002c02406000141c07030124024582c941240326070400c209094284950701034022522440c0f16240150305000c81c40741d9100c0d010f00400104000c01074006455040c46111105c0180d0000c003d000c00d1181c01e105074001450102e4080100300031115401405000e030b92281d0702071101c44101ca40620000e9801407605850f10b80d03c514040c07401039100c80042c90310b02070341c2c182504d54240c15006112a44508084541c0544a00035002d00e04440341b403080501624086481761990390300302c0318050a00400c2442c071034000780c1c200031880034819100e2480e110134510b581d504405070b9010300c00300c00300104c80090110b40404038016888a80140280c441c9420003400a131001a0001b44291798118a43c010007044040da0b030360000141c1c58500d1480d03403100c040d01c60f80200e03114280905d8000409500702c244403002040228000d01628212501210191880340423075001c00c84044c941a40a0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 343332967 1250 343331717 343331719
    0x2e0305010b0a0906060903030e0315010b041505030c030402040c020f030a031a03031603081b0c240910050637170303010509060102070302030d030b0406120f060c0e040c030614 77
    0x1800386170200c0205941c5c03c0348806004c4c00070942100e580c6490510a030300ca04803c210310004156514080c40080c0d910a1145150310581d518200b01624410000c80b401050f4007560242140c0341c0c2d8003004008c0c22800403601c29441080f4100c43c1d1404180040d01e400038a6450000f01c03a100a03500088050807980d015100c0e401c1080840b41200c03a840e4100305554042c5001015565004c0070807000c0d0113419000a40608080342d400c015110004008404041a04003080c0e03040c101c0180d0188484182c0b5070802c0d45d0400c0040743d92000095214562160340200340154030005078554251000e83c400d1400d604e2099015001040c011007006113005045d042c00d0300512601f0f960b4805d40ba0300040c098544215910004644107a1013041418003543d0014140c944855803c140540200400c0300803e0003603080140010308100b098644810b00da03080304070483c100c07405545030300c020300d10710b2070705000d01c031455240c0201d5440c0d0788a10075450000c0c3c1c074001462402c1a240240c106507101d821 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 343334217 1250 343332967 343332971
    0x3090c152601082806091e0605160e01090603051909050d0206010b041d0a0f2a020309090f060415080c01031a060a0503040609020612010e0a090b2e0305010b0a09 71
    0x681c1051340d0342c030070f16040640054000900d103038989051110306040c8402c8980443d11400c02006106041d030003903000c0d6085c841d1092810080500c01d46104101c03a14040c086140041d08100c100c0c0250800c1b5806600e06d1320440303103034141101c148201c4401d038000340c81d5603004400268000341c041150a0140149540c41400e0a140200104100b54041d00c0d4054091a207404200c20040c6900009a40d0b20b00038070a0148030b0650301040c000800c200d0303013110341c21150692603001e50300200031200c2066000d00024915034843d00e03607041c015409445560017950f10321420403400b0811010034050641d40014200400203034000400361840050350350141007444210700a02e9581304101c503212a00350401a850f0341e903e00300380005000b10742e0301941100000560560b42d80c0701c5551141a203913a540609256110f80450b00c040f1618460010001c005400c04110700c00ba5450341103140c6036412174005c05c1c60010100782d406610155004840070b039120402e541032494140c1881c07002d040781041c1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 343335467 1250 343334217 343334263
    0xb13050d05070311071a0706020c03030f0603070b0c0604081b1509101b0e0a0f030c03030908060403090504110702030f0304060e0607050601120f0812060405060103090c15260108 78
    0x720080e06030340031500c106c80000040d060101b040a8040d0750b900480d0350152901c0b450441688002000120b030018400d0080d880003040148a400584090a840724014405640d50380e80d00c802c640d101d02585481100030f000e200601c41e100300650101407500c8882a00507081081c48075181030710075055000500d0801000040c4010444141c62122003107141000803409075601051144400e03400254002096660100a020048401e5001c80e440b80c0e44814015584001c003d0b01d406064400600280086004000500d0503402c100706456481e44401c0c500035146e8006468820400b00025981c2c00c08242041580d03005000f61074016000c1e504186401591707503079551203020501411030040d81410300c460138404000404024142d0040700c0c160340740c12100010480700e83c2240e81c00d220b1820724001030001d5100e4050050a654007c120342d0180b030a220f600c03111009189015800c01c80340300c40c02c140c1e090840d50401600400c3d80c411301400d50520020358184040005080e01102108034 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 343336717 1250 343335467 343335479
    0x9030c1e02060319060b0301030c18050103020616150e151302060d0c03060510050306040c0504260115030f0b07091503020904090b07030f0b040c05070b13050d0507031107 75
    0x41141c4d407008420790b081e200c032220000000002e201035044003500e1a4040004400c0140d40342c0c0c0141030791100e15100c00c0c0414814490005c0e02c0303003400029003095041c001849501960084800c9107031240380d01a0500d000c3c09184c0741107078210940c4801c0c1da40041d12003441c21000241003a040040400c04010201c850380114210b0b21079991002a956030b40c0344a12a07451082c3e104002402d801021410f40c4400114000c3c1640c0044d01e2803440b540c075090700306074028044c40032202124528111014122a0910380c00300c150072014074111195250000c4c2030300002540000b2011303500c0f406202c031001c9007505068000c000700400104c01d10110788000e004c1040004600b9007440d03078078900580d40c0c2d020f0341c01050142c011440018280044001403040407605030b00081d6030007042c8041001816258010082a6825600a0400304d00c00304007100109007071030045a03000310803a0842803226100da882528003c0c1c035403011000580040341c101c1c00c05600800f0204503d4004000703141da241005 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 343337967 1250 343336717 343336729
    0x50d0b04020a17130c0b1c050411240705030c100b030304090902060702030703151a0f061b030304061418072106060b19020604030813110409030c1e02 66
    0x40491034019030031500003241078414104e5901959408480c0641413070351001000700720f42001c21094402d02c00c00c41c0508061000388140d603c1560005034440b040b0300e5500c05e1041035400d10340824003060300c258071090102038480003000b0a51140c00210f81c0c0c1e003200040c031420710110031403110800b401d024003480c00b90307000000d40e020344540700c000044500c03040c4001006031052400094240c0030300000007040c052020400390400510b088103000c3c040100c9521005500c120b134601c2d52200c0f000c540c0e000c1c2d60403d031010300250040300d840d15483c00f540c0406030b403444e00115802c07031b4680c2c1c45994401c50301095031748054000240300c0c0007440b000c40414029440e250540540c062030b401c82c0f958411003014038070441005582090741007012540b070b00d02407140c581c0020050640350b1000a410a4203510002e4800d01c51905540e848119448080d880f05250034009030940c2d90700c401513110b1400f40d0303c034070a02d4000c61181e01c0c2c42d0210200c030310385141021450760001c990380920040c802c0140c4c03249 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 343339217 1250 343337967 343337987
    0x3304051e0301111611040b13050103020f1504090b040e030c03040815060915012f070f031a090a0204110a03050c0c12090307031b09050f07120921050d0b04020a 70
    0x80140160110b43c1700010600a00b0386a403d1540003003c0c0d10380d084a02d07580d0f88458141d900907110034004640c0b00c01440300b10303880185000c0c6c08200030001082400c0440d408024900c03001440418807411b654065455608403429102d4190070004080041d07003c104007a500e2180c051f40411110300d04640016401403000340b400e108603908044a400d0b40e882000e1400700c005041c070307408850940c1c0d2007110b00000c000741038240c118442c1e8500450045400c4071038004a0b0351000c4020038a245d80c440c02c141200001c1c01c13041b07051180f8a081c00040ea500d02901406401d061005620f80d10245d03c01426240094400b170314210003000120038140010840c580303954080e54145a49d4010740003ca803605116900181ca15181e49908a000c41c89121814080701c20072041400203460700b690445902005507200c1000c03495100c91142d0000c201d41002c0c0c0c50500440b01604614450f07030904103040704000f00c8ac00051800a95a000300b03c40348140300103060261400c50812000c1341000c4c1a810503 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 343340467 1250 343339217 343339223
    0x703120608160b0d0b120307020a050312031602070f090b19060e0613050a1710060518070c0b07091707050d0206160f203304051e03011116 61
    0x400124a510f0410942081800718401b910044424102d142c945442e41c00c40c0000300d12656000e8400221480c0c0013072813070032181403441075034595203400303404c01881100000084194040c401c1d0010b0041a207035840750060a549201081c0f041c250030800003001850180400c0d815150001070002d15071040c4401c090810598031950744950a0b8181c00c1c0d03101080d84019400803a40402181c00200c140301c5503000402d84044031000b514484030f04040e0b800f513005498100c518036445800c0e006148070f065400030500d00b041e039024080d680b01c1c0801c865044035070300007040c225041000326003444102d2014043d02c2c1000307031100504002c00101010385400c0080d00c9280040384600c08628646201c407286a032209c08440c101d5854a8200c0c0c0c28822200e40c442500c803c4c1c0404605414111044900f17607210078128144400c0700e0300303168001040303078442c40c3c1c1d0361800384008070302901d80407440142c1d80041a6603401550741d0400701404d4130f2030b844038a05800404d01038502c12240354031950100c00d034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 343341717 1250 343340467 343340489
    0x4050918060718030f0804030b010f03080906210421210203060105040f0e06190501020d030e030d06030804050907030e0303160c0c0603050a050702010b0609190308070312060816 78
    0xc0e0404411a000f001da0005412900c1e844580010404140c0013001268403d00c0c100000d42e989015210510700c0c548409048560308018519451070460002c01e81c6141c640030f10720010541440000e844401120212707603a14031a0b041502c40250380039410400c2d000e030320f0542c04000d801c04015a040b0480e103a04002c9a40100c04910240e01440a0f18050305207a901c00700380c15618100c0c0c0002c103a017a030325280101c1800300046054484440b181083d1201a00144090011610110001c080001c1c10708280c0c0410302c003a001041080c098a4001d50144800030344803424001003201c800700103003802e000d0619140c020201d1604c04410f40c0d0740701000c128000050307401000c05903280300443c1802003644405000125050b5055440680035440c404020005544c92050603400c840417070003529400b08062010b800c840c50701c40c540e802d80400c08001c48142681c2c1e9a1b600445401c481d00c200c2c0400c05140030540c200300e09100341c800a10a0000820889005a00010103c070942c003603c0c101e80 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 343342967 1250 343341717 343341737
    0x709020c1b1804050616050703050337061703090d15020d18110306010302210307050604060c1e08040f05032701030b15040504020a0c0611040509180607 67
    0x180c1c800b21618030425041181c0841464035140072500c40c001210941c0102803400b090014041c82081075501d01070345501c4a500e540ca03a1090700300d5200c91120f0b41c040892000310000071140520518446111564030041103942c18804e040d03007046000c0b102c8854540c01400710f46400c0e036505010080c02e50300910744400c0d80084007503c002910420024034001428001012400c600031003914280342c1c0140a110f611222a02c10141c440303c0030711010390f0040240c0f10b111081c140180c400002041a00101ca14085030395440c00d050900480341599031651354003078003909581051920441058200c0c00024030781807104040e156078005400580341c40c00007032401041040c1041141c914089065003208071a2604d50800c101182810300940024104282c0040e28181000d00e02c00320441d01c00018145030502040c4002034021342100c00801240c0e003a44408035081d803050040e003415050322940e036036003810140036984502410700c240d01382241074803180d4040082662900302c0210302d000341d280 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 343344217 1250 343342967 343342969
    0xe091504030c0b2401030203070212030c130b04090605060a05070809040e0a240c23070c120c06050a121505120a050c03070f0303030c02010915020a020709020c1b 71
    0x7038400c40800400c3c0c00c0f8040d09102589030403140e15012241d4022500007500d84200046060380000e4071110056401400a1124000607502842c0d02c040c00100d4507007085030201c1c041d90219400e911a424460001034140070b071219034004d14001e840b0a072192441c0020407200200103104000000c0c203c90b10109072614a591190449040340500d203044401000d4242445c5a402211442c18086020040030351801030003103004080010745151641d810442484a4264045180743d803940c0b034608041010000040320080c0400c0505036054468034241414a01840648010740014060200c00c0c4050840f0f0f551043c2c070032040d88015400400e1628841ca001c9421410942156502510b03411141094400004241e1182030082e0120b803c060441401e140d2900b03000d01400c06405043c0300103002090094001d103001050343e100000e4221019209d01660607840c0713103902c16090300000c0840141e6030400c0036030080d0484901c1103192450004110365920611701c401c0e03030b4074521a0900000c03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 343345323 1106 343344217 343344227
    0xd050f1e1b1b0d051c081012020607020f12071d1f05010c1505040303020403060506090601050910030e030a020c0312070506010311041506050307090e09150403 70
    0x14444101032050f42161000c05131614822480f42524600c21080044c01c3d10200c1c1d0b4943d0101c0c14481d0f6448060901e56021030442104a9000e00240c0d8a640031034480076411200010030904038000300d01309011800b109a107500600314009400102a500c400b4110b208070b11079640c5948681c1a00500105e0070000c0307401400110091151f54040c126950856010340940703222100d08104080542d242240e080780002c0e0081403c20412290380182600100110380030581864600f000078500d000700d04801e88204400310600e100c1c22b02a50050200003081400d486e80c030044807101039070f10f9426114041c024440c503201a40c02c0901c41c001e44110b140d2100c05032107164a0758859600180c84448000d52150742c85d20640107a403100030103031008110708c0e107910f622850850409441800907070302c40d06041400700100805910041080034070100e140180c42c0c00c1d0340b103508044031 = true := by decide +kernel

theorem cover : BRFrame.Cov 343165467 343345323 := by
  have h0 := BRFrame.cov_init 343165467
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343165467 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 343165467 ≤ n) (h2 : n < 343345323) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
