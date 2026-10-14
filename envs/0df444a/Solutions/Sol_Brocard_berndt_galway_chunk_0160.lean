-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0160
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:10:22.816253+00:00
-- url     : https://prove2.me/submissions/f085e549-e2a7-46ea-b6bc-4da82b368b96

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 28597128 ≤ n < 28776984 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 28598378 1250 28597128 28597139
    0x1e070e190f0903050313030909111804090c050d0c0806280501080c0d020609030307050f15090c010c03030b03010603060b01171003060921020c010801060206040b0106110a080f04060810 81
    0x80c1c071020744204203224800c001e0405048c011030392040140f4030450300b0811102e065043c00e400341c002c1840030024118150781c0d6401407804c0d00458050a070040511454189042c003080a508290541107401040380140085d002c41c0500c490740c401d481100c0ca01c4a0660044004401495040801800381e440c4c003005001b072840018094052070416100140c0c031421030700001d030030f07402407411362a81880006102d108201c400b003000c61440e8510000c0703640e000b181d01c90350820f1650850741d03600136030701c0749001110030341c414003000400d1402410001410100d510101e4255005c1d07400035581d203901c0341a10b04407540c0c0190040c03e4200042000744480c01c02e001b02810706c584034400508090707120007800e81440208080c1c070401c0d01c0c1035407102000419081c0007a48441841c2c01807800b0a443e040001152400881e0f22403181d0f40c020081091a82460030940d41c0c21051088040d40e0b2042e240c030840045d41030b000800c00030310024402d585683c40c240d402807082c4030081000c0b16440072400100322 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 28599628 1250 28598378 28598387
    0xc1a04030216051212090a180b0a0509091002090414040c030b100e040f0201020309060307030e101a19120f0606140105070807080f0f28021e070e190f0903 68
    0xc0000621950f031000c035a000125038620541202d07c00108e441c4282146202507480000c2d03c03071040c0c842c42c240b2603880d41049440e0204444080158000940c41d0319400c4c0140d0007012051001000011100204950540140710071541141c8205040805205100d1a181181c0c2d02c00301001d01c00c01c1e824100b004000c02d58901510090030706182486540031a0b009000b07a500d98107002e06007a03140d144c007540c0203018001240d042d8805002d04a91345620400754003d1324070110030401e196500300110000d02c8201c01c5040e070000c403d40c0d40314001280f400c4119202c003222a010714508480d0294a080003000c8480903403044084003405100344010b660008265101c80740c2000c02e040e1104468144141c42e4030035074024000c0c0070b0300007400c80090000da1010b0891001d480c180002c42058041080c05002615450000541d120b2106084040b800880808412400f44241d43c18181d4880800c0702d031410036500401441002c010b0441c42d26003500c0f8860f072450361340506001c0303c04c7d543c80251 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 28600878 1250 28599628 28599643
    0x307030e0a1d072a0b060301090501020a08041406010b0405270a0e011a09040212010f02030103150e0a080306040e0102090d03020c01020d0207060c0308062404060e0415060c1a040302160512 83
    0x85c0215081000183d09540a6010361403240d0400d0080d0340c0c80103103280050008108441c121085180c11030560121000020315506031080075040902d854245000c00041e1401000c0074050800c94203981c4514440e40314956005114400010640d95604045a42500c000701025a1807401c80031302c0c1c1040742c1c0c3d0748070056045501540c00311199281200450701500f0700400790043c19000100000c108076000b84ca09500210010003004040d03a8000181c1c1c5a1b566410040c1c0001c90030301c007080c1280f60540c408603201106a00051030410340703601243c0313541c22008041e80903030000070074042d0650f010302008503041100c1c400303801c000e410840040c01891103140040c040200c920001001038442e030211450380410419401c05191103000e0391320b0150302600070580040c850040c0d44007103003858003c07108100b0b044809020800c0c24001c08031614008402d041c4c0d4a0601b000361a0340b01c1602075803082c0070b207010380c0c080c120388910310601000d003407032a0744000c1c02000c07441d504006d2041c001c141403 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 28602128 1250 28600878 28600883
    0x13050312160819020a0308070201050702100b0f0415030b0c0403201516120509031f0212040c0503010c0503160e060f0c010b030d030c020307030e0a1d072a 68
    0x114125414205902c079030041052060b40b0510340002e1421260300001c5a8209038442c0d40e43c541c0680d96420304038207880041c1c902c800541d200c40080c0515050a4000445081c0c025189481120b039500001c0e00fa1000d00c034007402c651060031424802d200100320103540c82020102030300d1906103981c2c0c400c0380300a0b030760b4080c5032080e41c0c028800e60740e9696615551541001d0044d0161030340100840034101d00c25400044449000550640021a00540a6031140341c0024090944401c10f160318400141c2d0b00c00724000080e0382040a0006e1403003c1c0740d01c03805039006a00304559030341088149400c40d0103411914050002c24010850f00400c07843c40d10410b956645040500300c3e40e00008540d01c4e00600400c000c3d01c80c070200d03135601420415440f00e00026021011192100f000300d000b50201e410031065100140c0042045d8808a8018a5000c040341d00251401e11056075950b10300945900d0f0a01c8035004a4800c0d007400701541d07100031080b452004424007004c4040300300b4002540c040700304100 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 28603378 1250 28602128 28602157
    0x610030209040b1806090901060501200f0d11061e06060c0f0102030c090301050c03070903030513090603140d2a0203010b09090d12020703021002030c0903010f0213050312 75
    0x101107154503250442c1c1c5000c90b0140800f0501410104007000800040b41c030540140e1408002a040400501a4071b0031203c042c1c451410f900d40510110a4049010b0158911486440c03104944000304008200e480201961801144002009075504001c4040c003c6409554400300600020308410560364002c3c804503901035590841003c15400c120760b6002039072840d4404010481c3c020403070790041000901c1100200035070f40d540210840c5078042603801c01c0c00504210300a000080c001c02c000c0c003944550402c122440f96880c42403600740d600d26081160300c01c0e0400c00038840c203501003003400343c619800d007007461002c040300c8240c3c0d805280b603c81c84544e4031400404141992020b5000c90710441001e40f04a10b2460900300807a596100c00c2000d5000803103c04140f41070aa0f41e00c01e0f01c01703080e4183e005d030034881d4a40d80e03200b01130740000d40003d0b1141e208008407903040c3e809119a00040c0c04504000d0b0b16861400d00300408400683e120728026000072805841d0501c0351401c603050785200c03454 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 28604628 1250 28603378 28603387
    0xf1503020a170106091503050408070308041a160905010806030c0405060a090213030215160b061201020d05010e060d030c060203070903080a05032502150402220209040b060306100302 80
    0x508a070900c01002c01500200c10b00c030000301d80c0a80c0f1000701400d4070480c8078000b0682001c010210200c54080310301500c100c80604c04a00041e20618990b50082e00411414000a80700c5402e46450b0034203986800002c3d103500b00c0c0450300f0703030400041002404242009181c80c505440406e48407400e40104a100d0343d035840c000307111655000c1000f0007402ea002030031900c4100066844010880c40e00003648034444424002c440c1c00100801c0301c041080b207007a2039000e0343d00c0350344500740007201603c0c0326031124813038403842c0000f0003d10140c200d80e5081240030940d9454050790422600300038024502030039594072410301103500612801001d90380300344010307a44d1380d5105c800c69080110340c0004001000002e0040c0c0802e5000e400b95004044006150400410481c544948030303040a0750a400750b0041135007030003001c0741d070b0f0010340c0d006002030440e88000002c1000316000303006021042407030743c1e40458007452501b0036105001c14480142d0b00d1501e07500349000001c201c0140c500405041580004 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 28605878 1250 28604628 28604647
    0xe010503030d27030504050f04061d040809040504030206040204060e07051c020702030312010e061801031101030906020412050705030a0b060904050a08070606030b09120316020703020d050a020a0f150302 89
    0x306903c100b03129101e0b080c00c1191903450010320b16881032050074800c050010400801340341c21b00c2403c0840d803155041882820502c071142f180810014410313104010107110f20300580d203840c042d0510680c0b207940070f07089900d07083c810030046410503001090030340381200030072408903080f80442d50800c2501d01c03001c2c691070854210201034400c0c058000c0d018000450401c400c50227a41c40c8034117880220004030703007540d200c1041c401a41080708400d420415000010030120b0818162f9030b010003011b240208a00d4011b4a4040c02d86e80954010802840d2401c0c0c6881481000d005510140c10100c0203001308404c60b45800c203a44101610043c455406c5002040410000700001441c40d5801606251903540c1801d011008204600c0f003034500200c04c2d000500b4423900859869240146844075a096480e0036008820f1141030b01d14000c190302c11030b2008400b50703950020492401c0d1151000341614841441400f411000540c0070702d282a01558080c00003091480400c200c0c00c2480c50300684404015 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 28607128 1250 28605878 28605911
    0x20c0607020703200a0807030303020304140f191a0f0603010b010309050c100507050706080610020f0a110103090803040809041805060f0703021c0e0d02030708030c090d0804150206010e010503030d 86
    0x9500404141c42035087c0041015055000385210700d020300e000040900c0550003103034842a200f01302d503019070059104040440c00c0b20300c1c001030090144420709143c1d4081e080103050b448007070b80d000c41384022035800c200c2c0600c0c0900a44c0c0c2a24000e181c00c0c03040c0c500d80e940c1d1950310001703125820b03c00d580400c800d1207010710400544121a40060440e061070f5030360b800c0138140710310585815019400b41c00d88162154000110080c0b0b00c500d0030010716070980d19469a0440c100010b4000d4105600c4030800c0001c54841c1000d10b01460090284580e251840000c1008888490250030380d414070591103e00460320208081e503019406429441d2660366150003200203200f040010380020300501c41a8010b039030603611055001440d44119600e1513042901070f40d036400782c040c0003451924100b001580c030003050005003052840c080c1c03504502c0141542c0c0d200c200d0f00184c10011400000030300305403009604100a90041515240920140d41810082512441400442076100d92100a03007050011603 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 28608378 1250 28607128 28607149
    0x4090f0f0e0a080d0507020c1003020d1a03030304060506031c0305060a050f0d060c0219030309121d01030207020312070b0a06140a030b07021608070501031103072102040504060603020c060702070320 87
    0x348000c007849c86106001d8000e4210300ea0540c1d40303a10304104041c4480da420500070310040c000340114195a26556154060880248007d130107014140c10300c210507450003550004000d198802240629042050001503851540301d18801c00c0409100a1b00384c40342d41d1044000e03508a04003244500c0301007401d80c070341503901c40281f451000701d80031101819810750014103841e1240e1041b103182240054100d82c0110043c0640e14403940d94481d4050720341c002d0f030041503000d00c00f07400d0307807106801030202c0c0340c07903810414059400b0f0905404002248800380b0941c030240544801c0010b95a041001080c00d030b100501000344003c0c0d080c80440c0c0518004c000e8200000307140171301c00c130f2041c1e2250540b60311f0b251a40304040c0802c0c10598100f001f04181f00a41e0b00c01c1c402907981540c02c21a200c0b80340c5c19030f4120f2181c05d008985c2000042620b884a0140c0030281070107480140e40d41c070403240010314001009001400b150801203040c00010b0740f440150070390841c54485100d3740b01b120300010718820003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 28609628 1250 28608378 28608403
    0x70309080d091401090804050d0c03020306010806061003020c06010e0403111606030b010206090a080f04030b010803090a061106041b090204180506010c050a061104090f0f0e0a080d050702 82
    0x1404942091800400d40251028621074a942c488443d031410240d0f00f655082203000300b040c0707000c1c002400a030400d01101066180902d181088660b030ba50042818150f0030f07000340119420403010000582014418280d4449492908515040088807203039181c18040c0501c410707180750000402d050501c1103070b00c03080c0481083c00340c80300c031001d1320b03101154281d0620805000c28145104281158008543c140c882c0c0800c0018103120441ca5440d0080e641c49054000001c06040c00040013088006010501810001001b5550341c000c84040218040c0742d58001c130308202c0e05005403c240000032520b02d4001e94040c0c60320903e0075400001500581c41341e0440b2041354804070300010300c0404001504400d06000301c0410031602c82000441d417800da14240070742246c6c04603010200007000d5511030b802204001d010941040d4980031144155801105524106a02c42c400c80305100d185108060821184a00524407140207988998160040f808031040e01c55454002480301d9009104c030100d88079 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 28610878 1250 28609628 28609643
    0x110c030c0c0306070c05030403020d08160501050403080a1109010809240a050606070503030c030603071203050903070806060a0504110904020301060c150225020316081f0c090608070309 81
    0xd040039a0a0380e40c5518000e00e910a124402c00b26801600031450f481c00309401002461419085400340200d11145520403213203240104020b10200d00c020a120341014400d0300082024106030400400180005d040c4039103081c58042c4048000d000142183c2c80b50030203003404401a600d20341061700b0203580a200782c10007a12a20700000e10b24001900601c02c5280c0300041007540c540c44140011401460070013030040d4020804104e0840251018591000740142140c8100751601112110040907440460129402144682c0380349410300100c00502014401020310380307031260010310710640911440b4000d030b41e2400c4498000e400c080c00c4404104025105664a5a4843d4000c3c01c00c100701c40306540215442101e05507840c264000c558003052b000d640140c0e164000c1c41105021030304044101d0781442440382c114021140ca20b0010000d192002c050001c82d0741800038403044148200346109582c4c50b040c4040c10054020388400d050318a5450700480c165202c41c1d0540041c0781c07900000e460350303 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 28612128 1250 28610878 28610887
    0x10620030c0d03061a0403031b0f03030b0102060601030e120702030708060708040c1d0103020f040b040c111506030d0c150612060b0f0d12020307241104030b010603110c03 75
    0x594000440000011855804101003036175045a80f0745010310301d0f000d00aa000800081011a1298010311001800061500100344507aa620700387c00c1200c440490201740c4800403d1441e607010b002c90341c2e101c030082c01d0911441e9941da524548030305089982c0340745050040b44010541d2004c104d42005003886004884d003505000c0c0010f46010000c40c1c040b101412415001300c0c0107410040340450f03000162034404516400c66003007112241c2016512600150f032100c42000607990f5000c0c0c03007066809a02e900102d20054900507051803015a0000305007002541806010b4500162040c0180480c0c80c00d5001101c503450214245400055500d5400c2c0c01c01c1008a06070759024044a1840c1c4603181c200004042d1100784800d8001c0040141c2d4090f5142c8220b001081400000b01c028007520b106881c0303010800d9a0f200c1d2210f10f00420482c070041102905503000ba03091081a2202000310b03401810145513a0341c102c1c0c1c01105002c1d0300304258542e907041c5001d5840600755a81e0543c400241d03603c5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 28613378 1250 28612128 28612147
    0xa020912070f0b1905030402011202120609061c0b06010c020a063b0d050c10051902010e0d0f020a080309010903030b0405010503030405010c0507051207060801080c0901062003 77
    0x203810030703406414103a010080c4002525180d040072919040d582481c140f8044c0c40d07130082507444c0d4000400990501c600c50380c40300e41c11140c0388010145948824503824840c00c01c8000e026400380010000ba0080c6001130250407440e071500700115042d03a00810304041d0f0750311000104c0d082e081380300c00250844042d0704007042c010f410130002000e240180040940884911046916400c444051403e10000c0102c424070340307050150301c641840d4000c0d03084030740d0f02804c040403e0204074080d05000002d1000f05130070000845502840c900160b442c8000c2c40100384000004e07407522400c030080400d0150320b5424005d40e5009000d02120280c100070815140e02d072a0a50074060070750103804a000a10705441d00c440361401c0d1041c54165040a001141130905110040d900720700c1c52481640c0901c00c0c5400050150784547c0746078624050140034180503440c02074041c00309041a045512580c211004145064035240c8543d81161164500ba0304900b200341c8002001650000a02d5418080056031081 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 28614628 1250 28613378 28613383
    0x2120106030509030702010e010516052505040218011b0209010b070302010b2b05010204090c1107080d0804080306060d0e0708070806060612190c02070504050105011704020103050a020912 82
    0x403501103850601c02035942d02003081d140c1c480c1c43c100070302040b909107a9141c25407280002d405107003d0078958078682082c540303801c0c0c40d02c10247d4591080021044100303c0300070b107040786000200b034291400d60034031440241e40301000383c1c00180b10381001480956000c2002c0004050b03a041c0b0f8000d000c6000039611481000407540c01644141c3c059820059080f4030750078415030300c98a02c0300c00e070304c80030b0b4480c2d082031681040042c0010556486d1f40078407001c2002c90a51042c03919150154070390000c11100c40014500304982c907070049000380c1040d002c00884c95000300ca40b0350f005a020120f03541d02d07502d5400080c80f501070f400c0b010302c400b8504100c2014030000000c1040554484000300d60081c0e68910740b403540c5190440d03040f0b41100040c08844c4240000680742c5410010b551404108500f92182c540202c83c40c005007540140d229440401c0681800c0c418640580b030301b0f00e030000322034a11407450800c451002d04024109961a4009500518035505403101403000070304601200c11150b180a0703 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 28615878 1250 28614628 28614631
    0x30c04051002101b0813020109030201140403050f0a1b0f12020604121506080706120e0a0203030a0305160507120f020709020d060806010e04050d0c02031e0312180a0b04060207060212 80
    0x850705d190042100414603550060030194165202e00e509415a0b00448180c426045203d659120134040072000940030b103c20115140c81000506072091030341000c0001314010000007100e5031104000340300e440d00c0b040b00c0e00150350110822026540080c40402e1700c0c0c2c0b0490344408890000103038a00704021b903503c24180391000380c120038441d10b6155000281c8a00440c03041704040360b92400c0c1d8003005081c0b03030050140403448405552942800e9004a4150342c000c40b01d03500029a5001041941c00303448000880010030b618102d403c101c400c1e0351704d81c107407046030a010f030512410b00111700516208120440103040405820342d10b524540050b10045c001500072580d071406850000300f45003020003240c912072038002d401020940713082d803000d41d1b0711024004c2c1079801d80140b40c14003a0082c000700400c1e41c11000c6400442c0d40340b140e600715808007030010300a071200c82aa034206581118002903080c1c8070f180c10981c02c002a071603030300d0302400034880c0d44070040c68940040f51103c0120720200070305 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 28617128 1250 28615878 28615931
    0x14010213050f030c040b03010207061407180605040e10080111090306090a0c0b0f0403021801030201030c020d121107060c0801151b0605040303020c01060e160302030c0405100210 78
    0x40d881030344800c20002101a01840e45405500c50301502d840c5150a401c05c10240f1400b4000600c2c1070442c1e11030717005a03031b10b0300740e480c07500003250080c010120341c031922980488080441a10500f0f092070001001c0f4490f41c800c0310b114010b64030100301c00c40c8030a88581d00801c0319100822030100c0c1680f0038961a0400310700d46103e4059000040c8002902052050b0301075800782030031404a090000401440c0c00c40c0c9140c02440e2030030700010005031115566175800c802c40c601c00d00b85540c950f10004061b1100e84600604540000005100b820740289203440060810070300824944401d10a04007a4025035201900c128100505004034640012006050302e034100b5040080040c005001c1e04d000030500d00c50703c2280304504150340400e640341e20680c1c2062180c50050301c1d110306c40d8855400c5d1000c1b5045454641c4c1c24800307100d1000d1500d0300c02020006207040035030a52500d800e080985015901c14035000364002c44901101074030903c138200c1f4030030880000700490112005e6080c01d041807030001 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 28618378 1250 28617128 28617157
    0x140105040303240803070305090f0a030b1014152104080706050903070b0c030a09050a080a0807050304030507020409020a0e0a0606020f010b0105182106010905060103020702030619020f0c060402130608060115020307140102 97
    0x3165033f10b040f03855035201d2600613003180c06000801950000d640d1101d98401083c84c0d0300c491000389441980446805280602c854580300c4810b404c1002c215680030340000c2055004002100002d42000c4890b03601000e4140300540700d9586100810240460407801072072030151050303c2c010005800c0160001d801e051b61031600680d9050000d81e0103120988002e0007080044c003181c0010f1405401ca202c010348041d0810319080e41e03500310443c50070000d59100700c0c015192141440000e504100980c0f10300d405800031f0080710611400601548201d64100b03d142c0785240103868282c0300c080403010000901084420030300b1104c4100350319a0401e020701d500d160f0900d40492050747c070a00030307511003540040260110b03450b02c610209080c1d030000c200c2c40c2c0c101c0d02409507503410340c1d504c0058040700264901400941c030701441006505445c410880d20b10910308041440201400604581035444410301190050b03200e60007a4a14002e041c0e00401c403800c410300d5940140e006401a01080607032912 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 28619628 1250 28618378 28618411
    0xf140708070b190908060103080d0209040f0c1205010609050f0414040305120702031e0c1e0703020906060c070611010e100603110907020c0409140105040303240803070305090f0a030b 80
    0xf04441404084c41440039943c0000014804030351300000800072244a64001460300e1450008902034550f00c04980ea00555502000004140c00404540040000d55000c00c210740c1014406420f802640c040e50380202c584149040668030b882d0f200040b0b40d00c0d40071001540b0701c0c2030f2600612607800742c40c016049180070008a80d10500000903101a646c81050b040041d0341140e074201c032590000a21019640304444207403030120307031140c0001c0600c80000d001c1c00001d803d45c014841c09142c060311444c021001081100c0720340e41e0209030b02c000e6803c05d01d0802124200c0e00a658090407500494524902900c4c000e000e00007215403000046900c29001110201c007100204242c100c001c43c0c0181c09604030804444852500c0d0b44680c25481c403ca103002d403140740004e0329500b11102206d00b04c010176a1094442000d1002e4060403d050043c801d0054406060400c12600d900601e18000e05006e40841d458410740e4030f045801c01450005130135034842d103590f414403101c40301c001d49000610307402c00300c1b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 28620878 1250 28619628 28619677
    0xf08071a0403020d0503071e02030d11030108030901030b0109030602030a050a0e010b03060f07020f100c0201110f04140105040e0403020109030e010e011e0201060e191103040f140708070b 82
    0x803803440307681c058002d0a010320901009450760351001b8000b400300000c040029405041403c03418a1200084e8011b42e2108100d040d40002ca40440c2d000748400c4406000400601030000100d40303920800b840c0100e0700103807081c01030315400c0030b540000381a03a001008211110700c09620061141d828030a007802100b03071354012203080b17641809811f6095041107000a80102c002035829800980c24411140c2034001c021100d030914900c1810a59519152005003030100e509000d90154090106459403900c8090310421032641309504c15044001510010200d05a0144d402e440c01414000315280e55440d09240c000e0080144040407030100e02d0403001825a94440c0380111584041070f1140b420010700d103400340311228005d00e8494115074881c03401003501d01d00b05c010580100d130380f826210741044c00e0142003802e86100d140d01184e02c940030b00c10400030800400240d0381c0c3c2d5800280300b07642403a00b03221450411025401c980340c20b20880e04000b6151040342c0007403648042400c0d89000408010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 28622128 1250 28620878 28620923
    0xa0306051c0605060607020f09070e0d0629090106080603010207020607050a02090a0204050a0302040e010e07060c140102070c05060a0e0307060203070312020708040302060c0106030b01180c0207050312090303070f0807 95
    0x4d20303010750042401008e640003030900701d201a030410000d08020100c94000d82c001074200c0d104620444030181c4900c44a094070300c1c0840184001055251100d200c4800b590218000344e40c1403050070700700700039840400d140f07480a60444103c2034014140980c0c4811a0410a540390b0405100b24000d891800005014200034030a4a0640310300610f10301401e481e42d001c0101903c001258102c4030355039980750002001d001c00c034910040620b40c50b490640c03000d0341000550240b030105140c125034010440784000401940001c070603540c084541a450340340c02241120120f900011460701072041c214080388917500080030b040524801d544200c0d418143d018000141d004088005080c9801800b0038001498124007402291080c0000000d002c1d80c0c03a00d51498003002a030040e41079003594440c0e0806208a4011140d2500c06800142005450000869982c0c01070308644103204e02d000c100c111150340c0a10880c0d04080d000007858551140c2c0d81032291440d84041022203201420118004521000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 28623378 1250 28622128 28622137
    0x90e090714040e030f041d01060203030705030424050109021b0111091512040303060311040e06040b060a08010609020d150e01181103090f1b03120a0306051c06050606 73
    0x201d4400c0100381e000c400500c4050206104100703194001409461925401d00010f84000c280c210b8288120110084100f02115010b800043c01c54004004009949802c83c040701d8020340d20049035a06c00c2075900768410a841e14060051503241054000902280d04d0780140900382c1c00b422030301c44141d18080c1550f080f5403c4102600c4984400e004040c820301e040c09010005200c0034051510307050721b200b81113403525400c440480201740e484c0386c00e009110941c1d10404414070203403820082400d41d1074a140d40da2400800c0140b6402e0b10500107900e90f20b401007444010101e8000a200c840c1d2500054400307500b0001c3d10502c05031612a5040b010840d1344c40107002c4400149540240da420a004006c5002d1040c000d0800309031500f5440ca204952800254852500a00900f4003201100c681c0c034101a0580006425007480882e080115a404201c15041c62080c82120b940c40a0914040d13010307000d55030000c2d62000302103c1d410400b44000441b010b185100b05070405c05903a60004000c41c5009 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 28624628 1250 28623378 28623389
    0xc0306060102070f0e060d05070303020a150e060a0c030b060c2404031202090102010603171b010c0504050f0a030204050f0703060f0f03060902010309081b15010302010215070e06040303090e0907 85
    0x260ba01042201510074446400090141c0284602e16140d104c48d40340c15441e82c8201c00692100300c84509001c2004c2e40d28250f01d03038030b0174144404440a1481c42d51481c1c0502141e48065507680304801c0c3c1402540b241030b001d6070103840b690300c4004540003142c880c1400001ea120810210044071046e0703100c4000385209a80c152203540c00d02103100280d0000790845400706055645c6c41402002003941c00c26480c4c00e00070180c0c8104d0355400800c80504801c0c2100444108580c1415a56150941c105003594291102580c0e4004215120f1000034500c0c8101e500194001d4034000c01e001415455107007803031060006450038000603036038001081c4004050720810114600c0444280005103084d00110840741c0140350120750f400f1240c0b140d00c0304c4d40c410010503111282c00b0008a5000f02c040c81001c00d03074001c03119a03880359072443c1c0010351150800d0200c01c0c422f5600c0d100103009507001e410f001400400103803c43d40c0310b07520382c03802030101c0742180640c00c1800d04c402e0016500c0c0d60000303043c4042e10b8 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 28625878 1250 28624628 28624649
    0x10b03060112050c04090c17011514010e0a0b0a0f050703020607050d140703020307030e070e0106031d011406040f090f080c1f0b01030c08010f05060f0909090c030606010207 76
    0x3881c00e0041c100b845800041203885000d094940350f050354407070049414180c0644020b071943e52034640002015002092a01016410b251400b054070101e505a4012074094144415100490000407a000c0c0790000d00c01e503012100d807102044044581c0080c100c0e1282179180e6020198900b14103031070741d01500c0741c0100180e00c41c40025130b0140c41040500b480708800000420189145040400c51410440b0b40400003a404020016410b52500a40e1000c0504401800c1c0060070016010b4401c44140250414545c0f00e51140c4000780c8101042a03d2190f00c4e8020080e00d130f00102d6455051105564071489107041000106100040740700c2d0801c015030210f440301c0404e45c29a03030350640d1307000308a00c02014003481d00341100300d450304080e602c8440c144500c0001e200210074000340032281030707590120030005c03501b0050098a1626100b002641e40803980075440390800810890584104100c1c0307a00041c1e1803007400220240020420000d105c201c00b594241d40d00c40004a07681c0c40540b14020000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 28627128 1250 28625878 28625881
    0x6050304121b0503031302090c07031413080304030501020703030506060909070e0a05150301030b070206060102030304030c050307080d050405102c070f080f0c1005070b0702160801060303080108010b0306 89
    0x4500503140754102c22400701101c0c0c0e1140141c0c55541c19500100e59040f070303103c45031802c0e80c11481d00b540f205900070a480a15030800389142c40c000c0c0300100982501041203000114083c158102c00f080304002c1220707170203c07580d968882c90102d010b90460303030080f00400e04140110b081031410342c054800200e00504151401e55880c0811a00c200005480710f0700480c40e0000460300741c445203100d0074401c0d605103500d41d480d451454503000500004041c0004c6402c140705002041c0ea000c8101e035009078051500155a140c541030a038214402d441c8001e21703000c000200ca4001c035040ba08071601c21030180040e11080b0380414034900564000303503506c07100680d0101d40000c51441032088002e20003100c400701c0d0b60294a55250200751140c54101c01c0180d401150106d90700340080001c90700794102a05d2010080c807002c6000b0b071403400340c00c1c401000c00000b040080e031164801c2010546400030012106011aa140d581070700130b10703030f40c0400d50010315000d0010514003014050091604009801451035 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 28628378 1250 28627128 28627163
    0x60f0f010305061f050703020f0706020d110f030d06031203060f0501110a050d02011e090209070804060f051911040311090709030f03080604050601020a0b0103080d0204030c0308030601030606050304 87
    0x400d8003d0816511010304144441c244641c4c601c040c43e006500d0b01e5143c1c1c0d8809130300b07000c1d10300000240f2801040c2d010400038004546e0101d4000100c00d070508040794103210200506080064000d240c401c2d602c4086148042ca00e5590420802c8030700a140104050000c19800c034160390807070281000c0011170040800c410f5101e0242280404281e00651303100c0c1c407080d61680d0801c043e105000006030b440380d80e4102d20400035025034804405542c401c0240399055804100c19120042c4100d0038854550000b40c28005070760010591503031801803c1009207448007012040e1142c2a43d03040e14140340040302c1c014800302008640030381e500105050002c0002100700014904010902800c10075600d200000244140d130b10764111031300c00e03100c007103051404105110445100a10342c82c1154070a60100011500b4807140d00e05692700948d925a89500c0e0b8500c05000c0d100301e40c00140440c515045c00014420120003450184000b6601400b240c0d41d14601120203000a071030142080903071507040c090 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 28629628 1250 28628378 28628381
    0xa020615010e060c010614090f070f0c0506070801060906051e09060c070905150109050d0201030506041d0601091803050a0503150a170d03020307020a06240807080105060f0f0103 78
    0x641180c1490300b600e0110703072040072848680040b07004146580d151082800098a2201200484e10043d580280f6900e4600d0751407508150140005050181c0c004000d040148200c044d480041d03007040494100d41080704008080013801d100d031200040d00da100c00700d0b4079031146d0200c407018208003404c6504145401802200750f40144001a031101c0100310815021105200e1940144484000010340d45000342440454140001e24a810450610414030044d43c0f4615003080c01602071a00041555460b0007260007401c4a510030300c031004810385e060019400024020f4160f602c882018000d4060540420800703064203a80140440c80034003140b042a03200ea030245a00c9052081d6030f58540e41c4100214420348000c0d002074100316002003001090000c01c129003610400140703011881d43ca020b202c02525110100740c01030586440f0860f070711503400705202d60300018082e007525440d081d50f1040704680d506040d20070130340c45508100000700c044c40d0082480740d80710005840b080c0c80c6000c5400440 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 28630878 1250 28629628 28629661
    0x5120306240d05090703050706140d020310030b010b0702030f010605100c03030b04020f1206030d050d0f020702040c02060708010605041805250203030601230403020f06070b041110050a0206 83
    0x500c40d401800390809080e030b6409000c0c058984880507100007400c0d0706000341070802c0b68110030140141c43d002004a400b030341040f1651081c1c80f0b800140c5035100d10405c1284040b25900280c00d21130100d0010a00c072404200510038140b007141290544054450384909841c403171f110355544281ba502c00c004c0e985004014080030f9034801e01d00024440a007000090481e00b008034250a410340200d4900c1c00c26000001058010a045004009606120b00010114840c2e003640310700868942031454002442901a5010182d005109001800c402d501c029900c0030304413100c1000907084800044e400d03009104440551761070000c40c003200e01803501b20801602e805802240307000115640c0c0081005044140040d07244c16501840d0b490070301c00c00042140302950b02c207840060100032452950b00d01c0004490440e40c0c1a41c846e41c0711030b00100024105d00450401400742c0f009541000f003005a0207a50f005101000c5a5044440c55424012a024021003110201590000d408103480612010404 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 28632128 1250 28630878 28630939
    0x304021207030507060f080f0a021e030406090203120a021506011b1407091a09090c060408070e1806041403041508060301050109090804060c0c0512030705120306 71
    0x4090400550308100d14000580c0d0041d900d541141c40c007032052030703880001e0342500c64151500300400d040c1080c0c2c1844000c1c010b0002e03141180c0c00690145611484c55114103100100214651a4902800d181000d4188031400324401e0154504041041c1c0300d0506443c540e02595009102d01c0080c4008000300e100082c100c00c0c14044040caa584001e008500206c1c0003d03c50101040c1c0c4041d4011258a4000386410100c642414040d0100340b0381103130a030081040404450740903444d2030b000c98171800c0441c4208141d0f000304d4000341c08200110006982411511840a041c501c1da49a240b2045500d8400c09010019000b210110303000c42c1c07668244102404034141a81e1400707070b641a890010481114184011440f032100b004414a001c0c410540140014a000d100000e403d54400c6081d2150f4090790052001c503003000c070705210f0bc169044000d40806861603220250340050141c2d40d0b0003140c0b007201c0301e00c2007911074030f501030090040e01e024410250068404082c1d894052400d00c0e85029003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 28633378 1250 28632128 28632139
    0x10b0d06050904061401060801050d260a09030308070804030813020a050415031109040305070b0c0903030703030603050d1e05090d02040603030807020f0d0509040e01020d06030506071106040c0902030402 89
    0x1041d075988440081d40910b1095100246480b5901da1510004a050340510107015006004001c20385030f01c010032001c9648801c0b13406045100306030405100070705000024100c080410b809449c1c0f03800c200540281d80c06900c4083c250360b21040c00721038070b800840c0d0080000741241c003c1500401401030112200c1d10081040702c4080c0c031500401c0c01c4507044903606104141c9400100180040c03c885072028100944400c01d0b50301d400d40300a8024401c40100402660f2420b000500c02c070701000c01e803241c082c40101540c0e5181c041e418020090203260005842c107000e48480fa102a50041c00165510910300e6440c00c101180c204068805401c055211a008103504000710f00580c0c50348101405944240c6551544e410900c00092400368682e82010007a0b000b003c450f40a40d8204080e198240c0d0100c80c085101003110180c903000e800b406070705034552030401202000b042408188107204004c01e950f038402070520501c24075528074080c4d50181c59011203c20074410306019400a6620500242a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 28634628 1250 28633378 28633391
    0x20a0c11131406040e0105010503060c07020a0305030301230f0f0108100306090803090721060b0109030203060a1d0a030c0f0606030b010603091205040608070c0201140c060a0b011106010b0d 83
    0x200718058440242d4280e030b01d0200002081200d241170301c28118007a01840082015606000110b80d40302c0000c2e01c2c000711550007051000441d41e6452500c00034651140c1070780d03103030750391840d2404a062801c00e00c02e5101d102c40b2a4090f941c2003041a0074400c503c02000f503049000035400548410320007038285003800c4101c610210115075030b8003400c12040d124110443d0b892030824516400c2204682080f8107500c24400c8081080245001c00d101140d0003050024200040b440180c4501c03401e0703400290180074000401c02d40c1d00751036000c660580004c50f03c0c0d00c1903aa09100083c0c0380d80f01c3c11f9000340842d448050203404240002c948072515403140c0c60018281d6101d860704821200240d00100000e51110001750401045d100d603488803c1d00c40c2002800c00342400405071000800070040c104000c00501d03442d041da840b03440c0c01c100c8a0100080c00380e586003000307902515404201c80c41c0302d040381407209408040d44502c964840d01c1c01400c0c0a400140d08080c0350007002e621100c1400800350b190b05 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 28635878 1250 28634628 28634659
    0x60605040e160605032e150806011404080a080c0309040e030a02010627050949170c0405030303070309060f0e07050f0303040e011512020a0c11 63
    0x1c01d25070310080420082840e049105001190300d00325820400421205200f807203610b00c3c02d1900c0000f6140c180b815410904103034025940c16000c281d012501041d000300c1421001030300030a000e40145000e0741c50002c13881030b0510a11392407160b0b11913054a50f201107000d401180c0c112020b403100c06401c00a503450400640c1c0002c00b6501c0c85622020303a6040001ca0103125502440b802c07000f04504c24413404c410405aa48114030388a2a40c620a4140c0742e000064003450107201001c02c480d032a02911302541902c3c2000402180c140e0110507450054004c50007011a60005692200703a042da203244845007600b112540542001c1c0c5640420002070101186c40d66051015501c1500301da03600049054403420f1242c1650001807a507294036190554007100c1c001c0c00f14404e400d0703800640b4118150061031010071700d103200d660700024660001c1400031600c00000403581c02d8082a966481c290403941002c20000ca20a40d41c0c01c0d8003160780855014001002c040500000c80e900401800111a0b00f6 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 28637128 1250 28635878 28635881
    0x152c0109050d050301080d0903050307030f030f0504080c010e030c0a030e06070f05010b0a05060c10051b0403060507030516090e0a060e0907061107030507141c060504031e05030604050406060504 85
    0x4840036008500040300600003206d0401c00504025080c0c605099000d10303640382c0c2900c900c1401c502804200bc81380340148581e00035000040710200303c1204100901d0103082815064000104401c200e5080c03440801e20110000260750094000d40090100391180d583c081d6100c410014075182c00400900c900700104458000c03035090f060050001154a480900c100200307411503802c2980302c2c840030b101120048500081001103d0241c0c01d0003e4a0784400388000002e940442c049412583d00203004001c00c60107800c8035020f8201a1018811500c40c00700c2031622842c5a000c090008100c600e0420400704418080354100701c050350300140c1180c1341e10384524480301c2115143c03056444910100141648400c00c800e042104102811300d442c1140e0700c2035100d110a100325050b1a8075405000c405a4480100140307558035030103800740d41c10b07683c940200988030441d41900071075400a0017604010ba0101c04200101c146d980301c51030b50742d031401080010407019205a8415986580216440e101c6 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 28638378 1250 28637128 28637143
    0xb010306050d080301150504030305220801090809100c0b15060d02030f0403090b04080304062d09031109070e011d0405011202040509030a020604120e06040b07152c010905 75
    0x40c3d440c16640b9030500449031000c000681e2203008000d0704020400210307512409880d244000c25280030800c2503e8403c030b440c1d080c040e401010081d407904c1a141c00b00000724006003001202685d0f1a0710003410f000c015181d220003810041c00d4120030200046e0552040d505401c031140e00105014204003d080780041282c00c07c50b83c54000e20964814041030580040240c0e004000100d0440d2a090522418980743d0090744115014411001155503021080d1481e055844940003074504103540d20075002407500145120640d034541291209255074100444210310540e0f082c0c0b07440143e498004011035a030258118403a03120341d440ca50894541ea9907000780c1c0e0003405a1142c9280d0302a0900400040307034030140c840c004a500410040b048141c0200c0d0b15940b25410445403460b040c101c1d04151788a0140c181e00d290f2000d00050041223055108010b0300006002d284c104032140d4102d030f117420854511a01040b440c0d814500b0610707002503400041030000708000b001080350011680e40c40e01d014103 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 28639628 1250 28638378 28638383
    0x203130b030a0f090201091202012303180d080c03040305120103081903060806040311100507020a060f090f02150d0603050105070e0114070210030e0f01090507090207020604090b010306050d 83
    0x40000a100b084030351401810640d451034501000140c584c0d1340044c0c0b041805201e04850f0030340340c611101c150381c003030a00c0c3d40d000ca0018040e911008060103c410031940121001302000c018024140300d207440c0090750140365030144d00c2c3c4c0015515000c8501035540c02c020030440c00c1180802c4400c615003a2141d01d45c0c001d40c4608422a22210401125003d00f081d18030200101490010200101e400c0052069000364041c00d03c2c0203c4c42182c00d9007030400c88002e4000c0c040d10300782420300051aa001644419060056208015032000110020280d074980d140c06416000014440b03000361600748040d0500ea510725a41314038002203e020642030703500300c1d0b1050321565910420000000c0c0c0100c51880315500918126010320901d0112008038010000c000e4041c0c007802c60603005980c02680100c41d010500c0d01110b1545010071491030107000d076040b04548a005590f40010301908900940f920540d00400c0d2600702420f02c0900001019181c0c610360404d600c1c1d8000180381d8807243d8020b002d0a0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 28640878 1250 28639628 28639649
    0x3020f040b1b0c040212060d06020c0307030c05070e010b09090c04080a0f11060307050f0a0c0b040f0302010c020607050a0e190b03010314070513092102070609050609010e090403020313 81
    0x203072a0310000d402c3c5140050441d02881c0100300c400c0001204020540e030200c012910440c40402604051009000703103076428009220000c0d90405161b008101c04d501c85205004803504c0c591941280b100318982072040e4055541c041c0598420303480c2c070100e4544e004840000942c1483d540312031840c90301c0c107041e80c00e403026050712880d841804020600004480c20070350341c50345581001c2c84000c08910a00050790803141011a01900d024450740c02d26003029005000c1038014103084c10700c0903a80b0b0b80003000701c015600c0d102107040800d002041c814482c20b010780300c039400d11165000988402040c0d1008590107050301c034010201c50b49018005000c1c28180000649a41c110f20785a000c00108060311612944404410001556101701c0340140d000c0042c0041607010040c0b41c030100043c02280d80e81c4502c1159a20b118030168001514400c44605a4484c44c2076031790758091005c2d5214040e01540015152614a40b9900f803920305940c2080c0f0900c100e03860440c0c0c5919034203d02d955604401a000d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 28642128 1250 28640878 28640917
    0xf030c10031a04060b03070804030908060412120b031e150901291c0f020901030305031909050706031d1f0c030b091504021c020901080f0106020d03020f040b 69
    0x440c00419507400b4006803810084107051070601c4505020040260040001e801c00040070107115126400003841c0180454a107420315140209101c046c0703280b6500003801072035210484502078001d220f0112406805042408800e6000c80700d0070311080e41c0500c0c0e62080b01100c1075400030309a8030030b116085030400000c0c466081c02f0f0b500d100ba1048040c4420502014544248a54a85100c110000c1355034411008281e0280b07400da055504094019510032010b4000000313054110000354854050b50540d20707e40407098401500310303a8030450150081c3d00c595414000070b0b019520600c200541080001c41c21107811070254607040414030590f1850307003500c0144004540b9401488140c0d4881e003800d0103050300c000040f43d400c9400808510100001843c102103540300c540c1181c6501c856400b40d94012801c910000c00a90f00408046002074079050001d44499496164641a00c6e0203901404081c102c01d04100c000e50048850302d65000c0e0304010000710f0016120013484c21280d03084426124 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 28643378 1250 28642128 28642151
    0x13180e07030c0f050117060d11030d03050103031b080706020c031603020703051002040b0702010311040504060f0503060a050403080a02070c0b03040302010c080108030a090308030c040e01030b010e0603010c09050f030c1003 97
    0x715144d5212078103004861503080662064040c5150303101c20151814510900f09050180c0007100348903025402d40502111928405d50640086068900a0302c401c00c010020018000000d010780b500941800e405020950000713400ea002000f80001080c200c81c140244ca071320505c41d40d490000700310b0141e032004108208110781440f220302500100c0508506103403401c130100826115040300281010f43e51500d425615854105540150001030020007a440e10b61002c903520744224007495209225110005a42e04035501840e4401e503416511850305446021045021303402510048481d8080076001060094003d40550300c1240a940040b921910701a8090140c5a0607000f407aa26041009000b9009810144440071280d00c105402d41c2c4c1c0e42c5170800b0407039900854101a41000d404000001070212840116060b01ca2801d03140826488030401c2500300d42c800103400c0702152111a00300030918001500404c1400301805603840b2220038400039068a5030150224040380c0da901031040c9 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 28644628 1250 28643378 28643399
    0x6060915090b010201060f0611100c2d09050108090c0303031303110604050303070c0303060801090809010207060314010306020a0c050a030909140402060301090b010908030a0504051513180e07030c 86
    0x5542d00070300080040c05d0500e0415886c10000d4014401031102141030083e449504000204800003003d03420000c510600030005e1001d4002000b0340060700c5000720307805803000c4070700844403104140d8030740460542c9080c0041d1400d03200204002103a00520710b0380b804507103040c4000c610a507024600d00300400c070640ba000e0403040444d446010241e202a04000c00140300000320394100d2241c1c145644401c526190840c05040309400c034640f20b500f0440f02c00100203c03600600030210003602038410309030315403500b181222541d50030b801565203240c0c010404226290f00901ca40c81140c9040d0030506800c3d06c40c14a01041d071402240000e281d92410418003c080c0310b01c411101118030b032280d1900b090380001c0d019000c10300031426201da0f01e80d482c0c80140e0090010b44000e107031100c20769496103080000540f0740d400ca4841c96020320007801180305a0402c3e1421200f07140a2001c0001491b0309001c0c0c1d58094856600b405450703603545621181070110100b007140f0046100e400c01488041c2000315211 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 28645878 1250 28644628 28644641
    0x150504030218060108070806060405030f030903010507080903040909030512040309050a1502061609050a0602030717040302031b0f12030301080c010212031602100507021b01050a0e010c0606091509 86
    0x45800c003502c0074400b2030380c0d03c82c60700341c4c101005284c6650262035684c0012136520580e40710650510401568100da0075020002d8640b0f0303907048008016641e17030140d044d00d1111003140e00941e250020001440701450a50041a50754020b00e0858100082200d00b42c400800643c3c090300850000b100030450740c6400c0c0121400f800e040301000600f0403500502075618200034040c00503104601c0130510b0301d0340c0300700c0d0101e009020040941c4e24482d81c0e000b000c0d40b6548035460540d00b96201d2141110030b0480101200e080320760140041660203104148046c7c0203882510046d072041031103e050b005556500f0510360b44000d964003665480d49844405450300620034031460664122041003803d00144030141c95004022110102c06158101c1040341440d03440c8004007065031078001130080b055800940d07c082004217440001c4282c0940b4019601401168040d80000c0d41c503a05104403944540300c0243c800d4421580412016203900720031b0140c500e464090307403410b050480100a485414040c03031 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 28647128 1250 28645878 28645909
    0x606030f0e0705060406030e1006030b07030b0901050d06020c011b03020a11011103130c0503100902040c090308180105090301060308072f0906030a020a03060b0a0501090b0d151505040302 82
    0x8044441c9084042100340c00b0364424901495030300c21208c5182c890070b020039002c101004204000a40c0c90f89408080c001e0161062800645480c40040050038405429410b885008010150012082d503402010358442404840305540b02c420015810f82d040c001090090860b44000d40c4400309000c000f0440c18454044070b065a041c4100c080388054218102ca4000c0201000d6180140380703414208828215540710642500c01c06402c1c1101101c180e1040f15960b208540600ca52003500c80111451040c42c003002e0070640c1c04028600a03070350200d468000c0000d06060903828011080c00080c00c42d03000f0ba0050329a60000500a03082001803000c0d025003c500c032200d00001c105a08a960030b0040350840c0d9401008000003003005603030200181a0920781c01060301200941306d25000340a015640c54090164040d02c01c08205903009842070710039551901802c0d8200510704000f00003404400e0007410325200c18070004240114403c039418924100c0d61659030780c1d07030724520600203c410440500d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 28648378 1250 28647128 28647133
    0x30d0801230607030f02030403050307081306020307030f050a02010b030316060c0810050d0c120c03020405010b070503030610050f0301030c0e060f011d01140406020f010b03013c0606030f0e 83
    0x9400340c40e42c07020243c42e0b1031609442c00b103a0f141041e007401d900d10b10075a04064094800410301108204000300202040904800904180c980d115026070380c0740a0448010041024890045003c0344140081c199140b0306100100d80001e10201003402e5622820008216040034203011081c08294000d02c114005213152408441c6490101e4141031031042c0945403007681e4800400e024030045040003405011140749021000d03034a840d0000501c5000d2000300c0c055400e040c0002070703401007042522940ba0b0003001940c6541d40c1c0d20704118200c06080710740300500505015005e021151100910301075032144030b8881d034650070441c6a0011900c01041c1034441c4107580045012030343e0003030b00b03502c0e501ca0b05128075468507552001651440700d624640d084050b4085000110136070300051347e81460303d41400822145c02c09501f498281c0e0515946a01d1880101c1107054075040a8012407014500801009185a0130450036400382e0381d4503404035000035100c07080c0309c1c1d00d00543d10a1b4050a2902c200 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 28649628 1250 28648378 28648439
    0x40c020c0f0a08030a1101020d020409090c1a0702061308030307050c1203130809010c06020c010b0109091a01050304060f0903030e060a061406070f02151c0e15070e030d0801 76
    0xc583e5520320501c0d040800300040c8a8070081060400d40503200d044c0c5040b4415500e031034450000c074009186441040d40c0e01c46020400043c0b11030441500d045c1003040300c131080d1800c50305800380401640141c0c0413041e0380203071100c001840341e42480a54000d074589c0c0d64070381d5504c890a00c441d1a21480000e0340d81000b8003081440100e4010f03564076000c042e030051031192200d85480c0140d50714001400042c29146c000203c540740208194407402c03a86c40e0980340c641080d5120ba0108084031002181d690404140c034030708000640c040e0b000b55600c07034410140407950040302035170403040d00e115035002c4012a03140c00350640300c0b400a1148a42c420460302003002218a003485c916500c079560304e07406000d4080080c448061142380f100c030382d9a0381d4002c0c088801901c0041c045c102281d11803c5000413282900c42c1001d540c004e81d0080f61040025035004000d0010501c030302459540c0b02600c20400e0011100d42107070940c07400e020041400003262030360011989805410001134044c504400ca0101d120300 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 28650878 1250 28649628 28649639
    0xb061305071b020f09010603020c01060618030b2206090308010602030a09030209070203120c030106141e091f030902040e030a14032707150311070f0203010b040c020c0f0a 75
    0x15100a0703202c50344088003a00441400440c0091501032074040e008502080045002501500108692a280070081242a60303c6600300c6039900040311811480607652000c00115117a0034a42e50030841006c80100c030105450030076a810900f40707a084821a44412582085c10340003041e4900410761800030714070b0008007070742c01054210180002131140c41900040703020f0324070170010380e13003038600f00703d4428114108003050780002e8109115820000385101000c080120340401941d609405070018075051003103c81c400e80c3d03d50040032241c2c2d000003507450207040c0800340c0b82d10810700e001180c03000500d0003068018841030751001500c481150b40200300c0c60341d25a51041c1d500c1d1280c580d5405044d1a07883d100e500915207021400003114151252030413020781a40030403640d08442c0c0141c0c0103d00c3d50500c510a07010341d40c1c0025800c100c0f50090140c00d0110f4401402041d219100a000103051030305c1030001412201e010741200c0051f0b00c0403803c101141404040075450f188101d4480321110b140c803 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 28652128 1250 28650878 28650887
    0x204051f0e090f18070801090b0a0b030c0102060c03060319081c0b0d0206090d0b010f060806030105250903060e030405010306050901050306060d0602090301061512060f2105030301030b06130507 85
    0x11304410901c0065158101860f5401e2040c0005003030154024041004142810700c10a481038a007442224030700303881e402d054600001e03003025034001038029003125079a07034030103020a810040c0556018050520003030032403c11000520700a6110380c039441e4807004101c0c402810b40c0c03107900e0002141442c080e056103a0381d50f0361103071811284d0704503091659214014082210682c1001004000039603210012a54034038540c90007080d11440e56030b000982d40d5040401d802e89200391204501c4842c0907140301e921036500b0803000d10074089800c040407495034950303c04080f00c880480a91a070307000403500344460743c0d0500442c00181011200c0b21225410700000076211a000351080c0d2056109409030340801001d50151203034030500070000c0210581e620203040904040d85a0000090413401c44455402154402d00f0b0643d8005807080d04010b00b0034140005810320422085030147e4030305121030001d40d08000a6019500c01e20343e00d800390034408140004030101002c48001541494104002541d11 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 28653378 1250 28652128 28652131
    0x8070902070f0c0308070203060702031809130c060e0a06020c060d051b030408120a0c0c120507050304090204080f06010b0a051b01090302010b0102160302090610030204051f0e090f 79
    0x400107a5035901450072410402c0410002070158240703010010074820210058105580241c0a4405a42d0f680d07000304d13242c0c0305001c0d0303801290340031000e8855a0300b8903004140d0f101c02c05081440300d0041988981c6010089640480c000034000a26030350325041c829041c6005003958001040303425802c0001070494020401034454103030765400041d41074240e80c20b012400c0c81c801c6100300d0341d905107420128019440022004500480000803c0c40116540700c0c1403203c0a5580c3c403601820002d07030341c0880c000c0c0c0e000403500800406008075004146c06000603c0101001070f00142c0d00c0d841c080111b41400900c508001103038025600402c51070b29004201c0d151102c0500d4081d41e0350007120410390411a8404050740c2d03640c600320064007055015030003a07004503026021140714800091a12941e0609400000d400007020760101d10281003180c444140c1c0c10480c00c001d030900b03441d400400c0000c403420240a1300483c110302e1240da00d6401598000e562ba00640324001c0d14a042a00310402c680c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 28654628 1250 28653378 28653389
    0x50405090109140c03031c0b0d050c03010c0507051b220603020a0b0f0a050703020118030206040b0f07090b031e040305070b10050a0303051804020a1205010509041a04030215070309110301060807 85
    0x3440b942c64540648907407000588c590300034000540c0b02c2250a10701d50390b5458401450280d031038000c5628800307010b1803c0ea0f100d903520100a04480032a00c1411804090b1510341c990440c0c602ca4a40d40c06409100001c00854078100000590f60303d1401081016046980610b080080030061001c4011a520440c0c00500003800e0090ba24040c030328049004180503a500f01403101f81e441036404142c0e0102c0e81c2d178091030103402060300a4440361040030a440003035490390003162011108216124003140a5580082c1c0c0400d9017a400c0b02041402c8207942c4111030072000500c00040c00302c20001c403201031640107080855590540340c14000403074074200041c0000b030140000410390f42c0003001e903916001c40c001d402810075034440303480c40d40c082c06080c003000e55080c1890401d0b0011425040c540c0007240321320b810560790b4204041c49401142480c44c050015011800740420800d908540040464015807080c1e40c00250700200341042d050800340300350118032990400c0020460380e600024882d040d1390 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 28655878 1250 28654628 28654657
    0x70905060d120e06120105040c0e03100c0507080301080627060606030901020c01060e0105010f0203030405100209060c070b1b0d021005101205030a03060b041206090c050405090109140c0303 83
    0xb9000030641d4046110302c030301503100500003880751040d00c6103c0390504032103056400b03001104540d001994049044601c032a09a0310410600307541071081e8002c280144e04a0404170b1800e0780580f610380c540e601c241c1144e07165501802c107200c840030071a40701400910704591040504611150707075036200c480c0500710500c2030030044049000b00200b035040701d191802200081007190751710011003044610900c0f130140401c5641c100a90624000700469103e80e5210015011900358203d6650003508402e00243c0c02c030f0001d0007410030b058010401074000d03203103010070182c032080b5400c0285984521541c0c1c80c490798000340b82c1c854546400044131951601b181c200401e69503588800d2002c1e040711980b020a010b580d1404074814000701000404400f40707655000c0c041503441c1d010010183c03042c0c0c801e0002013110040060b000c1045907001c000002c2c4114084201190b66a0001c2e0035200103841e034135256503440c0440c50420804180105511039010090b0081700d031040c0001c0c0d201d0050007103904003c17 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 28657128 1250 28655878 28655903
    0x215130605270d0e030a05030f0d06050a060201050f01050604030b070806031023010e28060509150301051501020309010309050c060a0f0215010302100c0204090212010905070905060d 80
    0x91035000407525069a10780342c600900c0c400c154040d903440b00b010075041d0104900c0903030307000281000306020040c150050000d528109000303218010030384c00607008200c00c640d144d401080c10390300d400c44c040043c027040e400443c0c01d040ca000d05c02c101900680c0540c0c40780d04108800c00004241400b00380e4469000e0420b0300440ea94400031a080542e00d2001d40c0109152806e501c003840800905080328461040341c0408076a00c501c2c031000a02c2b000d4804010701e1200760200c07856108070700d0b02030b089114214404198240c0d142d02203000994180e80d00031030244444984100c6040c2441466404402c1100c5c8407035007484030002035200d10031940e4003410503449045040234050100021207041d48040c154564802045500a2a61944002c0d03000140101d155036511144507140041c1600d8005003000c0000d88010b50603034102c40d0303200c0102e03001600c46c034000b409030307440c01d1b80c422481524900200d420180b43c40c11a003044070300e41001e11907600d044140320701c54881c11590501c1c41e0340483c400c00d11 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 28658378 1250 28657128 28657141
    0xe01030201080a20120901060602070e090a120c1103010b01090b070c0510030209030d1416051507050d0c020321090f010513020109360b0d050604030215130605 70
    0x2801102c03015980c4103004606403a1300140e8071008140c1d8001004da200c803951540d000341c50a8488038402d02006a000c00020b015003103064030195000842c500c119915010b85668070112100040465408a02c0343c416003001e01603039050003890880c003180200200300c0548006030884e10301c1c0c041c3c1d0b00c0001000c110360081040c0700e01c0110240000400060070079045401c0107001e54424031016009018412407a0122030250102d0021560448503a41c181b164841c09001c41a8464000f070b0744503ca041403d241d0f0008203a041d5028004507034580e80d580c0207401c02001524200d0349070790704540c01080b04502141c2c6100d2000a00055820102c240e134a401c0e800ca458006100c0c1d4409195281c4020b01040300032100d546c4040c10b2007a210700703000b20b9445542124441c0500f951848280c503e0314000d410740c0c0c25054038072591007203c0000031070913051400300e01140b5502c001259158000400e01c0103040d0104501c1010781c0d10305201d00846d1038031207008401c1c0003c0500c020862500d82010644 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 28659628 1250 28658378 28658381
    0x10f1509091208090a0602040b07021c0807061503021011160e010510020f03120a06050901031a04031b050703060b04020406051603020c041404030e0103020a0903110d02030303040302030a020609070e01030201080a 93
    0x440e0380d0403040547d211609c480e402d4403e588404d4049200e80e00c074240d6040d170030020029461030b040d04448160305006d880d460780409800c40401258015078003000110042e9115001064406502e81e1001c011102c41c09005150041c0c55050400c2c01903001c0c01008010300c40183c186c1541c106543c082d6126246000c103910301860a60928142d02011924000e0025103100291141040383e4061113402d85d11014440440001e020142040210701420140b1982e07a0030105d4100d032092030301e00e407921540b241c00400d1403480310007101d03d030700540000c2090112501500401a10450301145014071707000014041d8401c03101c520342e161081c8494003060600a100749401440050b0050000020600b211f16065904540880109440f4084c40000354400e10a071581c3c0700d07090302c88644031411912100c2d039002e81c03040429808032880d120b441c01a1001c3c005540683c0c0300790011501ea50440e517010381000b900609251140e44030040c100300104c51200200d044a40a080420241d10b94403440d40 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 28660878 1250 28659628 28659643
    0x3050604290a0b0f0a09091503030513081b040f0501080c0909030d020304060606020d0207030803151201090606060807020606060301030803060409060e0606040605061206041805010f150909120809 86
    0x805543c0c01041d4045800e030204c000300b2207840300e40d451000181e00c0741c506104a62035588105400c48642c50140b0029000c0c00c001d2480c120740d0b00e20020103d64940019190015a030740c00006900101c030118010304040c01220720107a115074050225604040c41d4035075890b0b2401c1507601c50036407903001c20f00e0b460f005e0084500518a103135003556286400e04000300680400c0c45040c1c0140b0a1507518440d0a00c04240076056030f5000100620f140c4501d40c007890342d40d08414005520404c1e00381d401d030141e03c09125000c0d03000e00c02c0c0d0002c5001450075001600340c170401002503065410050070018141d6a09007100c1c1560740c006512500d980300c48011034024010280e00800c00c501e8a11084c0d420b8000007800d40c1f061000319824000982c0b51814030440d8003840c0c0c1d409600614402c04600e4525194101c1d1044c000f000140c80e5080000e0f4640e54255110401c000c0c0403150b8034180e0380003a0f61404419000b42001680a0000031440d03071f00d240c1c0c0f154440c884103003040342420110b4050b010078002c04 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 28662128 1250 28660878 28660889
    0x9030c050a0503090a0608060901090b0319060614010906020a230d020a0b0601020f07090b010203130f061706010c0311031e12010f030209040807081207020c0103050604290a 76
    0x1a140700703195240c030036504d40c013101d4614860690400001030301ea104101d21b42c443c403000381000c8841d929102240000d0319003071410706e41c035004d14048000c0318028903182c9120302d03026240210f1090b18146020b46031418a00042c0c2c100320310503000703110301034000480102c640c0d0302500b00000c136062417400101054182d12119800e00641c083e011001e640041c00341c4040d40558680c9015803510401680d40e00801030203101ea03900100e02c108138401c46903100d20302160060040d00c0c1360082c200910003440c0e0703551300124803604440500b40245940107001801c02003580102d0101c0342041c000107480c0d0303600c0315002810404d00340726450714004280180c2e110341d0031054107807101400090400f41c99800c00e0151808042019000054480b1006181c104581e0040c00380480d0b900c540d200c1790401c0d8400c0e94207480954080045c1139403040d04280f568800d415030390140c8440c2c09039900050613a08045d00c41c9110318145035003c81e9915200e0120301e48842904090040c07000581e0104182c2d142c9607112 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 28663378 1250 28662128 28662133
    0x7020a0f0606150302130f0f03080c070801020304031205010506030c07080a09080d090303030e0727020408160302010f0309150207020121060e09011401090e0f011b090b180409030c05 80
    0x43c500425050b4014000f0310328030003050340c80691101c00c000007005c0c482c031550b1042d400b406001c001103021700000304990f01805041da08919143e01e55603081e41d0013a1000c800046d48608035200740c81340c600c070b00e5000d414119031407413840c06c0810204a4a0040b013101604045000400f600d000f40503660400081ca01c8005644102550010240c5024481e100a4011034149404020711a2010030401c0954070b4207007007201524a200c40d0b09104c1e41e4a5032005164903070801021441403420445008184040082142c00505600c001448a6040c000b0385003030501f021000d10004041072501c110000007968010b841c0e403081c0c0012106801c1080345c0e0740f07514106100c04070240036540c03c42c40035582400510311098482000300c40c02c9840b2030080c8402404180b005000c510907941001d81103541d020210b81904801101203800c640c44042c1c00000714020302070308081c0d40e4000360081c004040c40005c040c240903400c609070021040089407248161355031008601014012107001c40826080402c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 28664628 1250 28663378 28663409
    0x1303121101050a05060307050a051e01020717060403110105100306020f04050409060606031103160842061201031101110d02060103020306060a1211040e1605040609020307020a0f0606 80
    0x90403c01880117540b114000c0c0520030f80030070782e42494060101210340141a280441d0401d00d0110301104c003181c85141140125240003484018614100040d1040c05001d0003013030a03d0310300a4404500194903c409034100000c020200740883d081404403a00254056507030020b11401114504c40c6d500411740c01881c0001060510009510840c140e8017581c41c100641c0c00340d140c0c0c6031903502045030402c1030110200721036010350788954903081d0405120b080e0408030051041c0101140c160055650004800007a24601000901c00200a03181c80075a1920300d030021200104a240f078050002811400c07010f010300d1840e07407085d1900500c4100c7d820558a1a4550100c001d488175800c1c401640700348680b0b00494003600d40810000300300c80f45000b032260b480d0b503190740d040a90200361414a510a940b44802052080b0903c030901505044405a04200c1e0410f802c0104444551700440102da00c10700811085540018264196980000c5070818560b40c5241050181c1540e03000042041003010 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 28665878 1250 28664628 28664641
    0xc021c03060f0503070e0103060e1002030702010c02060601090506040e060d020303070804030c050402040b0d05090a050d03090302060c0c0309131e0605130b060f0f120103050606010f0203130312110105 88
    0x41c458000d40d07012100c00d800d816078500415564090301e0007240055801680100b00091640d40080201a0403030244c0d00d00c082649504801c0783c000b10b82c2500540d46600e201151540d06001d10b6920240900301042c541e400c00001c10050302640c016000c511030034401040c010b0790b4042d01e462145074014202c0390b07200380a203801200d58215100865412010445c0032605240c0343c0291001d0b01d1030445010b04107005210024080d02000d4503072507090188900c030030046075041c0702140d030791000d40d24049401c011a20b8001e28007030005007040c0460381c00740180800d032000401210098901198000d11240d0744802003001459010a00f1040380781d0030917000990700607604810122a0708441244180382d00080807000d4441d40005030b64000c0d400c000742c1540b05200d02c0541300080780c0e400400e060a911044011100c0340030b070025142648401c3c108021580d200701242d480102d244061070408014543e041d8884602d4000103010041d0074851410b1a031007a44c00c06103024500300244490704015 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 28667128 1250 28665878 28665881
    0x1090b0703020415030606140f0909010b0301081e030a0c0c080a03032702090402090a0608060f061c0c0501140c031612090501050306150702130519051303030c021c03 73
    0x80c0306081c0030070240c00302031019a00038030800081f2465a00e070420008540031007078401764482604034030054010310450709591281e810303813800703068104a1140c0c0c1c0e504003c43c49180c4510400d092040c0343e0440800c0d40700d014080165080c00704035050a0042108a241840440b40c80390081d60403440b030444000141a81508091000d07008003201e0420003941040b805204070294001a41211100e8007240c0141043d500065000c02079800010741d40e81c8030790b01141403410507140c1103506c60a4006001c280d00e442d41d541d5074003014940c00c28940e011650f4400f425903005100b200d050100d80c0390f4403241002544101c54965801c103054942e00c0d0709219aa111542c18100d0980c0c84c64440d1051a50f030780e005a0194065070720584449085613503480411001003401d004001a082091043c0001a11a0202030a000d045031344007061525000301e0003040080210105503100d41030005114024818101284141d40c041c500400c1810204100380d00c1c00356103020310500700e20b24054260059a05 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 28668378 1250 28667128 28667137
    0x15031504110307020a030f050d020c0303040506130f030c0f02210c060315060309070302042906040308071103070e070c0203010608030c060105060a0309050a061b03061809030201090b070302 83
    0x4840c1008000c204405500d02408201c440b0409a807001c1c1442020a0003124040303240d00103442c08620f4030080802d007000b0b0382c0248a090b401c0b80d0001c0180820450144009a40501608585280c1d81d8403601c400710014001c010140030300c071204401e00280701075000010455034000d42400c3c141e84440401c90070b04000e00c41d5030b442074060b1085c81b084500d01602202d000364000105070a80400ca401041080e89c806400c0001c148070b513140c0007006171030313030b0040807600b10100c4030900314091540803d07210400240ca00500c036401c10013003400000c03004416207110f1034000404054041d50180424540130180e0070081500c051001045050b9a01107403139407000e03209030000c0c400d05584410007952170084e00b48600c0f090300070038014086d90034042c001d443c4170440340c82c010a8119150301c9141c1003080e0741005031690380d00d03840c84002e10030304c10a401312600002c0c0f800700065441c201d6405450150140e401c504651602252403d2620035000100c0a81d040301c075245190900c1400540254030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 28669628 1250 28668378 28668421
    0x70b13021804080406030c0c140d09080c06030a11070f05010501090b0102071d070203070605010602100605010206060924060c06041406040308040b040827090a060b04030605061503 79
    0x91114100c8024200c0700425004683c8105810304040c140281500030707001c00d1800d00c0030040d1a1a504000c211a01507100b07101c03140f0070246c00180d02c00c0c60020f010202a812070301e42580f082d02d0391a46603c0340700445e82d00101c04400080c020f5001e2120340034510810344d029141801c00e000030740030f004040d48800e040304c1540008100501c051001682c681a0501c50501c403450910403026051016040080d131200140c41500d280c20701070b40d030380030440e40700307801c0000141c0c0b10740b03150b4958000901c120005814240014440c03898981d0000b03081602c0200000800c071201301c001c13a135014219a001031551001800c46031620b264030318180e5100c9040b00d050745c110581810305140d014010902500881d0965154034042e41c9580b1050901d44c405001101c40d424100013001041da80120485001c203184842500340d99600d5080201222001e480c0d203280c5850000204024a00c5104460031690300c5900861b0039074503503002034100d103207204412000c49000000c12a6521134800300071301000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 28670878 1250 28669628 28669639
    0x10501080a0e0a1217090a05070501080c09040f0b0d03020c0a0f0807120c030b04080d1a06040527070507140a12180b0a050c0609030702010c1502070b1302 68
    0x195041408800d4400c0d0052015036a00560600f10200c0c4014100c090800c1440c2090b00f0118a5201c04404040301182c002d481500403843d22030400c42c0c01c2c4054002042c0c240791408141c01c011164910320700c6013022080c46280d50700f1050035040500d800241412000900c5c0d50700400240c18040c0d1543c44102e241e40c03044a0b000300c003050f84458051545c0c1600c0702e540003003850300c0c20000c2d0300040d030051200985040002d000000002030081c00c84500c214420307008035450314040704c00e41c41030322242041c02d1403421840c029070149468034000d440031600c04031840c070500031030091056070300420048400245141d031002c000e0541e802c9002802130510811054019800040a5903240d04070003100400040b404051600641d2181c1010604004c1000c0c51084081c1c6c1d96031003d64590061842c00c1c045000441d1802010350f00748041c951299000c0080d625041f0a03500003089024010742c000c00b120003840e03079101d5250107681901e800d20360000005407541040c1c90441507600d19000304900c0749 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 28672128 1250 28670878 28670881
    0x40b040e010f03050a0201050307180303050702040b01090e07050d0906020a050c1002090d080306041b0f0201060801050f0a0522030e090c0a0e060904180602030703050702070e0403030b1201020c010501050108 91
    0x14202c00901d01244c1e0440702078207003046076500464080e480a050341c0208403010b80580060f440750204000118482d8a034030b5511a40740c410b0100ba035080b144510306004140d070040150003201458154411942e05c0c1581d514440746041c64020035000401500c0c00c0e01c040f5415469036008002401244000380454025070080c4d0034180c1a480f8050065801200d010f00d0503000400c0340300a15007101004202054000b04d40e40c1c440c41110840701050b0003c4c0045965000c4240c080c42460048c100600080c8258035081290340300c000303405890107025654490000d019407040c0f9040000b10000183c400c1c0c0d05c0142c5081c0102050301038050103201e4020400441e110040300c000311180307141181c885071310120300102005200c0c0c002c9050a908952901c407151b881c141c540c0701008a042c4112001a142d0910120050458900924030410340d44600d00501c5441a0348504560195040c5404150310025101140f02c00d084c01150b00590760000c59100d04140d41900080e06035042030380d9a042c0d5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 28673378 1250 28672128 28672139
    0x2070521040312050315090a0b040506120a0807020103021e030108160503060403030c0e0d061e051e04030e130e0c030102090a0b030901140906070305070c0308060108060109030602040b040e01 84
    0x120301ca00e10000380601c0002da11103005a02581c09580d0011403440d51391a040a450b000c1007485500b11240010f882d65408a1119482d0904c5141e400c0202903403841144251030035419034512244201511004010030f0080441e84241c0441e406040c01c0380609010f40300d403400308160340d002800385103500d01911014051042c5c00c811494111171005008042e1503c494030140e00400314400380c50104a031141c0c82421580b900c0c180e03500254442e04c000140c0c50304c003255a106074100c40908500041c01c0c10300313000d029810780041d16015042485802465202c2e8034080d01d4498908100e1134202c090001d401aa80c5005c2c3c0c0210b0380c14050700d0643e0241404101010300307c0c441d040c030035035201c0110b64040c02440c04000c00b440d4080001c3c40001aa1118a0304070009030100b1a24030441e98068810011040d44c140101034100d801414414400c4034030740e030040e0240c2c1b0000c00c041c0c101302641d00011426803040c26940b009540215045540b80e4030390801031074a500c10300600c42040340e120000100c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 28674628 1250 28673378 28673443
    0x219030f03030c030c0f20030406020d0216140603180712050606040e0709020a020f060a0e0d0c0308010b09040902041103090c060705071a0d020a02070303030f090c1502010f020705 79
    0x41c415581d1040044242c46c2e0a03510002100304150719400e00d210140425801080104003a041540040060a000c034100a02d4a05c03000e10380036000030403c00c1013180c1c0c00c0c0240c03c503481860445d03d0603101e54070500841003038000c0c0384610a151140e0080060880381c56041c000b07201f400380c0c00340c2e4640e640e500140001ea40303203609100c5907540a20400c12200b1540c1e4041c202d030258a2054800c0040da0202d4a850034100380c0d80405020f0b0340300c480ca41000c000300316a0086286034240400c1600c4c0f13a440103020010148580d049c100e078006000785003590b0780e6010401280d4014030802c82c0407041202d00348260000c0b5000840340c030900d01d040307215240480540d5030071644000185019410200726900848240305d43c0020004240a01c00031494036002070000f52140754002c0004615509008040d600f83c025400030302c524001c1c00070045509210785074296000f441c0031058507005010102e0040c8000010061194800b0034039504000c00410b040040d4090380c2064080d10554256030b10 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 28675878 1250 28674628 28674641
    0xc0d0c060b0306060a03060c0201140f010501030c110a020402071509210504270b030a03051c05130609110a0b0904050117030403120203042606090304050d0602070219030f03030c03 79
    0x40e8010600e00b8104005007c94001d2070104140b031002044000c2400d0a10090750b03400d89520400201640040c06035590501c1002c003401c0e003138685003090504104425031212a8540064006da40006045027030080e1941c210ba000d04182c0401c01041c1041c4c244244038524841c01744200306400144226458400c1e0265000d64800c245103044000c0a1900024030080303c10442450b161a1044440c0340e650601020013214040c0e2920b036642d01313903030010603c49050384203204040340c5008280314102c040c5003c00c07248560f11080000d1511064204408803491100d52641d000010113408109403019001408501303205903001d00040c0d80b28002e0485040303115018408641c4244000c00100e00f4580f24107c40d0501e90059038070b0980c4600e608050201c0d071035050b00320702c0036640680d58420420172000740d004080340c002c0d40c00c0904040026900741691240980500e4011416030155620800000c2c4801e01404e40403600a1340c9280180001220400a901107490000a4440c940c003034000c19 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 28677128 1250 28675878 28675891
    0x2070501080907060804110616110a03030c020904060b0901080a0308010f06051e040302060307050720030706030b04020d0c0c050d08040206091003090c06020708071e060e01050c0d0c060b0306 84
    0x2480700d241800400c031030a0358002d10036250701c680205201a6901d60302d00404000c9c400134040d034045102408c1044101c040304c043ca43c01102c0044017000841e038403c2c4034003d03c0341d04686c1c209079070b21641051070280140d07245040d406200380c0300000c2d0400000441c5819603110ba01ca003c40d81e03903248009401c51041340300b00c202003641041180a07800009250109042d40c41c10484c0c01c2549a401080058004032403490106030700052403801c0c00400a0200420030300048040d4580000f171001c03d889a445200b968181030b181c5280803e10f07034941e01602d0b0b00c0589041d041000c403407a07000003010074000300c500755024060001c040d000280710301001803042c0d80241480c1c0c80c1400c01c00520a5050702614440304040c0d0f01d0001d0300002f501e080507180244a90b81c020035500c0c0c01d2202c0d403130800c0c140b0740c46423841c141e40c001210991001400c41e8802c94106080035006604100e0059801d4801d501460356203000380010407540d0b070f42092403855282e008100c1002144081e8052541d40e40b07003030310007 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 28678378 1250 28677128 28677133
    0x3010e060702100506061b0a0602070609141b0415030b0a090b010f0f0506090607020603040b0402090c07030e0904020d050a1a070309020105090f0112020a2a02150a170702030307020705010809 84
    0x21307458951f00034003c8250050000100d03100c0c1d2900703449000490300880d8040350107a859020480074460031100000031140e0b4917010380480d50001e00c01900040030f84003100e00454031003a0130000481e10040f42e10081d0780083d400c1820707107059102000149107204040741c00080305030011034030b25080042101900c1c0d855051000242c1414208091070f00000102c0d580000100b10100c01603c541018501a80c49003015803040d080c944100305500c500102003001c540f000344803a2000c690321030340f011601c2e003003607805142503160760010541500c182c04001c0c100e0311910300c4180801620301801c06882d85001902c604a848541044040c1c0b8000c220184c002a401d100b884200c3c40c2c007188210846405041031072412084d2444401030340c1180020340c0c0415082800041d950240d444902c0c552895082016001c81c0c4950000700004007440440c82481c02c0400d100036510b00595910044403080b5000b441c061410b510000e65a40c400c41d41c2e00300602a804000a1950080c80b0450055060402 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 28679628 1250 28678378 28678387
    0x61b0301090509031303110108090610050f030c1f08100f06052b0c090b030105030d0c050c04020409050619030b07030903090b0a020102030709081203040303020f0903010e06070210050606 82
    0x8010064071002e4002140e0340001c002185d02400350101d01401144244c00743e02014000c2c00000d48054401030002d0819000513041003e20700c100310100c81660302c121021861a4000710100f0320b860005c101d2583c00c401c100c410440c0044410381400c1d00131805039501a9160b4481d00d8505c102241d80c8603d0060200d0038038180f100718050740c0500f40d0380fa498070700d408035280701c0e0b840c14242cac11070b00505020341542d48100e40f0500703902c50321035009043c060220510b0765250802080d5511100d940d45070030000c1340d0425200b0800f092001c3d4562002c010001c2d234503551204104801800281d504620078220350b00c1c1403071050146910b00e01200d0b01703c45142c2c0c00f603980880c1030f0003612240100724100160038001148082c2c049020b414022825400180c5924104e0405030011600da0000f814951056800b0050942034004a90b0720030740c5850050307102d0821411410762400342d000b00030f5241d401c1c050786a00c441c00009215100b07003100e900704d412072a100f03103112084030019141f45030444002c01 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 28680878 1250 28679628 28679639
    0xb03060109060b0306041a090f0109060e0c090d08040f03050601090516020c01030c020c03070305010605010305060a0b03060103150e090d0206070c05070e060105041505070c050a080307110a090c11061b0301 90
    0x34040c0d043c951001d80c84051f50032402000816003203080f2543c0400341100342c018001281d07070b0301c00c450260800c5110f511190030000201c04250007124502072043e98002507003420481114250303401001800045240c0f070b51607190580d1910070074054940e81a18010003d2141c408603d1001d14215254014146c500601d00044019000e101074034015807040c0c03808428141c8040000300001c41c040c1000040c00740c1010300040c2a07400103010b461046064503000c0c06461403440441c0c1c0c000e1824240020748003076a5a03c2a4000780b6540b010701c58260000c10028102000308a801c00e242c102c0d402d5410710350301c0070380c01c0d16464141c4401810f603904c515003d01140c004c8040080d082141410301906056940514664900980c20307040c0c0017550104110b4200080c00001c5030140c101124a0740c00d00303081c40310080e5a4080c001c40509494010303006051942c40b200083c0d0054072200d0018440c0c1103481102070459510b6040800c0c0d6803040c4000207169503141c15070024818900ea00e51440e503482c00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 28682128 1250 28680878 28680881
    0x5010e0114090d03051c02070b160f03020319090b0405060a0e1203060301020c07080703030905011707030b0d0503040f030b01050904050a08030421090e07020609030a0c03021c030b03060109060b030604 88
    0x50021010702008000c40c0100c8200010082070304500d2050259a8401278a4420030041c00a00985d0f22a070848150881c043e410000e0980780e21018580141c5907510303012022006004480da094400340b80012250a000103e17851502c40c034020303000c81d8010344840d0918801c4403840002c8002c6900034003481c1e072503060800b0055410080040015003441066000c2c00d0070031384503034403600982d0b0007038a04100b0550401c01903401003009080c03a141c482880c00d0801d5a0b644028942d80415540e1805100ca503600d2200320b0318803070f4000c8200c0b5111501c880c882c04049400d40410384028081d040006001c0c030704501d11501c2254481c010f440c40c420203940780e5400d07401c046d000701e804510b164000c0d0b05440300c0d0080d10300c84d00741ca07551f107114580c82c00100310b1005401410f07003002c41d001101002071039040002103420329021840c101c80340254904049080803e80c0e81c7d54020401d8440885d1143da905401c50395120900320b05031030840c1d0f42c89000008035450f601c1001e84e448001d0000451920f0035 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 28683378 1250 28682128 28682149
    0x6091002010906060b090306010617010312020f07090605040f1e0504170a0504061b020d03200609010518030310030303050a1d0604050609070e061201020f0c030405010e011409 77
    0x1a800085502c11250b036450040c2d46403500882e000031400700e510585031508100160042070141420b40011300e01458011902c4030500024090b06400400c1d101410b10810041c10085032440079500b42903210f80c2d919018003484d00c04c080c0308904110074060840c500c0d04c01c6c04040010810b2800c0143c1228403200040e21000f8000d84501d41840c4045440380459801810b5000160380c520307941700e08010000c0c1400e40c0303101c11455104a060540001602c0d510b1204984036054180011100d100130304c1070034084000001980a030140d401030040d17080054101c5030040111041804400070042c44181e52804211419043d1589089013003020030b0095001c16002000c0320070104140c003046140b01d209944000c1104502d50140c0108001e00030240250341e0000c3c0c480c400b030080c5915048650300154806840d1612684940703000360a810401d50440e5008000048000d840f910705440040d2690800c1c45417501160141c18500604e6224441502c0c5680d490542d4500300b444080c14807070754821 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 28684628 1250 28683378 28683409
    0x40b070207030203190c092f0f0c07080c0108040b0c07060908040608150901060c030e040204031403071403160f0203070e0a02040807050a1d1e0c030a0b0a050609 71
    0x7107140102c0075031400e21440007400100d0013200d9482900e031800c80c2e151400d903442100c2d2a0300d0a0514414030034004660300d50004503007640c6900d01c2c40340b84103000390310404581e10381c489000240c101c0404008500d5100304c40000058903040d001200056541000031603004007903c0c0c0c1e1000045e800c5201001804803a805084000b458a40c0795030307024030650064001c240460110f0301000340c041150300380040c030001c055551443c42c0d40b406002502580391003400a051003052400661a601c0b568103860040da000859480500800d0080c643c4a6000d06419510400060b4449156910000440340c140c503d00c4c4800001c45019107030405441070116049a050049801c00a008299401340d6805072401c10001640c8901d000d44081c07821170294402400f0b01c8402d08100040d11070f10315005030001c00d10444442a40d26000e6101540740d0402e0b0401c008150700c0b09000c05904140c0185206410301c003003c01ca001070810030001c0c5040c85124080d800b980410140905081400740c000c081607 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 28685878 1250 28684628 28684633
    0xc09050904050f0d050c0606040c020606041a031b010f020708061503030d0f02031504061401200601030f110301090203070306020a02030405040f02090a0e0c0f0702010504090203090c01020706090e040b0702 90
    0x69408405013084000760403880021004141c080050f00207002c2150000400c40f001c0160b050800d0010f51111001006180b10311f964001e05040884424a00f00c4038100040a0303645014914050601d688400f00d01180001c030701e050b030000141d00016035030702070342c2d0410000c1000d503480a522113030303100a251106800d80028071001408c0d0186001c1c0d82d80d91400494007580786d2515a510050118044400ca4403d5040c1041042044460300d826030702c141c802c0c603020031008040f0300c1001e0103001380700b2100b01030700c00c0e00000824000020000800c90744940403907860400c001c0d040500b601c1524902a502d03400c059410800100300794010300ca8840c0500549003080c0e42d40b4001000c803001c2c404807401d0907400195024083c40d00b6040500540400301600d5003a040c110803494460041c1c0d1031200102c003002500409582c014016140203190746d5200b03661303078584480c1f9643c848460044031809441111400706009001e550580d040d1158024005800c2d910f0751200d515040010381900c0a60 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 28687128 1250 28685878 28685893
    0x1120f0203030a030507080a090b010e15030303010306060614040501020d110f0706080105030105010603020a0203030a0b060904091506061430010308040305070807030314090112050a09060501090c0905090405 91
    0x1030720184081c04020308540c03000640c41c40c0240740986030820041a410340310703243c80d010360001100118030034103403241000100d50031b5840b402d4100c125841c0c0415264184404800042085259004801078840a07901d64a800d100003c1c1140c241c0203c2c080c0c540560818125100118841c4e00c4908803203004a0840d401e40b440140c1050421880d500f000000a82810051103a0304090003800c0c014042460704500c1d061045200940743c0c000640010140c9031a10003500540d960031050b9804888024410001c1d100140380c18200d070444541d5801c80541014000500240500f00f0200384001da032514514103402200d80007041007031000c20300100c03c546100603403011012440140039502c0390890f61340e11400c41c202246030120650000d9a41d500492003800060f41c41031a10780c030449465681c0b600ca010000043c0c40307001c00000705800f058034120030400501101d410050310140035050822280c0d80314000101038a80100402c0081480f01404110781c1c1022524180e1041c0248181e40c0316 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 28688378 1250 28687128 28687133
    0xa050a0e0d020918010e0a02031207140316060b010c030210021308010e06060a0e090d03020309010e0a03050a0f0309020f15070602070b010504110306090c0a05090a0801050a140103050601120f 84
    0x4003e0281d542543da14050900703142800e500b4401d42603034511740705c000e001010485e400650354400da501200d944070004206041000300c2d49500001c80c3d07066a082d40e48030f401106050207000700740300781a1006406e00380c4081081d4000c51441a9039501940500381450585401d00080c0d881707610041004d0b4454000003035142028450640d050903040080e0841b0b082c40d004020310701003240c00800c9410394880a101200200080d03034070b068110ba090160300ca88d58815014018044504003e0b1680159010181091fa024000b09841e41454a80f0440c000e20780d2021012622101d0009400c0412003209803141e2800d9201c4206040100480c3c45c640070443e69040140e0b00148407c84078540400018000d6280c0743c003034860074890030078001e0300b14035082d0005925130b80c2c00307041d24140000000c2c1400340e003441072007203818842000c1d02810310b81e582c0c0c030403050003014100c1d560343d00e05141562100b500a1041c203010f040b44d800c20028195070b4248080c285800b04105003c80c0c1c12610942001d00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 28689628 1250 28688378 28688389
    0x20d0e06090d080a0806100e0904020d050d080604060906140607081306080105100c12032a20010905100b010302070c0e060a06030c0516080903030f0c0d03020a050a0e0d02 75
    0x84a4401c1e43c19940300d030058140603051000261100d403061604041c680c9200d40d1001018252480466006080b510f0f6400860100302c00f040d0043e04038058951009905504540210302411094400f0814503680b5000f020444c1c1c01801100601c1580b5080c0c0c40c40c528040d0027a00102d03014503013075407601b452202142e00f002c4142c0e1000d00410044401000140744c689101d1402c0c0759a41410509060300b036880321f80500703070706c10803106150351211052201e4610030000a82403001c0c910b540035a103a858400b9100030420702e201c0500021429400071a042d060049501b91684000102a00c2c503040001c003000c0e004d0009602c0c10190b01b8440540031810701c121150007091090403c0040f0300702101804001c101c01e401038024113043c04400905141e11070100c6404448a04c0c2200001c0d40314036009115106421607160305100c0402d4401c5c142d81c0a4000300041d0203e541114030210495805400740e00540703980e00042503061048420041c0208a00f00800c14004c1c80758509907907179030001d00d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 28690878 1250 28689628 28689649
    0x170409020a1d040b060702041a04050a0b0a0515030103020d03050d0203040c08010f0629040503160f17070902030a0e07030b07030b0409201302040305060709050d03020d0e0609 77
    0x4002050b5280c501c1c11440c101a6244180714140c0703090280180c4040400c109104980700217024503035076032114032013240303015400b00403500062081c00380382003408642001e0910a2070040c070070344105c3c1000441c6d14140c11702ca0090040080c400d0b041d40c0c40c5408000c2c00801040054081c0002041140d01032061880103500c20b92140303101e69141070410304450b08403807400d00101d444074503201c4140200c041114540082c000c1c0420310240c4c242c0802518501402070381d201a8140c0b09420395546100d240380010003d0301c0300001025145907507898482c00901038055218460b4221641c00d20260300d05070001d41c1d000c244c00340040741e845205a6050720b80319060303005440c10142d00f0140105981e06009010031200100c40500007442030785c807244c1d240c01c0e051026a0780043c0a00da1b041e00ea0b00c0d40c04400c03103420942d6400719255966420519120301c0200c0b842400284080700200301403404030045041070f901540100410398590310141d54a00300707241e2143d0311030001d001079441c69580d0038a00c1c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 28692128 1250 28690878 28690897
    0x507020d0506010e16180b0d02040803030c0309010c0f2a30030902060405040c03091e21080a110903010c1215060c030804080708040306020306150a090317040902 71
    0x880143c03030105d00070784c40b56182c4450802001070060414007010440105081550703102c084141c0c1e40c05100c20000001d1145038440d5166002c0442006003e6070708401841c070070912640280034201900c0000c45007640103c0419002c0380140c0055801e1400814100401000b0b2034002a03901c00b03651108800c110b0072060201d5151401c41c85440520113006c031103002c04d65207040500141035641c1c0040e902e0b020364052507014079607442260100714402c0c1c00c004040c50304858016860f0400c5400d0008a0b98098001d0b550880c5101c0e022521a49090182e400e035030680d51100341680310403040d500640460b9511147c40b40c410b020b507207904e82d020710594910b00c1d550f8440e0041141500140c6c015142d1105040042c94603101c41000301c641c01810f1728103174603410304d807001d0a42d80e180b400c0081400380800c058200100030401100f0003a1940c001d601942044035207090f16079520300307105514031420701e1901c00216050020000514440e442400407030605c011300c1d04041c0c4030042c1100b240c0002a18 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 28693378 1250 28692128 28692149
    0xa0306090201031505030a060905161e080601030b13020f040e010212010e040f0b070210060306020301141207060e03100e0105180a0503090f0324070e09010302030c010507020d050601 80
    0xd1104540c0c25208607180f41103010301002581e031400000030348503400c000b000350006886e074001d1030030004103004980c10142801c40c000341c0345031550b8050840710842d044558414041d0303500810310b180c0000740203040300d50001980510380d0b2040520718000d00c1e120422600004080d1003030f20681c0c4c8901600075003c180d40001a201d00815041c5842d045045e48241110b420120074040492940c2d807002c80303190b070000c24440c050345526504030314021102d030064020b01d2816201204124041e00114100c0301c1c3c100160440d41c40070000c100c1680c0e90b4003003c200c03690008004006c0c041c012411040482d00040c00e565451907809610026944102c0103604141d6450080104140482d80240e403201041c000074107511a0355620182d5078841d1504c8503104106801d1950402e0743c00308590700c403622508103034610040d141031103841003110035a40c40300411241c0d11a060710742081c2315554122900240100b071071099603c0152a603501652069800003404c428160114404204d824000c2c4442e8030b8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 28694628 1250 28693378 28693391
    0x6091909150501050f03070e0a0b0a0f120e0a1e06020d020307080c120720010c11120f0301090f11070507060f050327160b04030203011b0c110402090a0306 68
    0xd209401a0303242d00618140130f030034414807090b0324000b01903039489115807c207244e126407000001103081e21141d00c055030b8500e0005000751050790100082c0c000264a488844050103803603009030036036100c045d50f0001c0d13a01080380c1c10041890311424400c20301b10008042c196042da91079480903640000c1c5154407a540000c01e008100d54040c608582c010001a517250602000181c0e0305601c80010b08440c0170400a011030075201079040c100709030b4518007203008201c601c0d4880005440b074100300300c3d0241c4501800a41c0304144180c00101c032040f04084200916613801d1442185c024000302110f80300c80c955035071a800c80c5d100300700d000f404001c0c002c400500c01c03103240000040024902110a0342000010300074040400c0c59803103079403040c01960004c81036000d0b060b0405803030964115aa1100319008200009900310fa030401042524000e030700030b201a000c101ca44426110038503121200090010011401051100b941c46c591500f004202614045540e00098032003841ea80081da4101d59810 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 28695878 1250 28694628 28694651
    0x5040f0305031308010b09010b09031002030a0b0411090121060b070b01290301050d02010c080a030b0102060901060f0510030e07030305090f04050106050f0a02030702191805011406091909 82
    0xf0540c100414201d4000e0200001ca50003050840c07106105050141c0004101111256000e10a00d001d55103604021501d074a004003800c006460b003125100e0080c2d07e40320700050082e2225085072406030068503098094940306008a85005020000c11302c0e01d5500c00c40030441e4099240102020750049043d0001941000f904082603585503035540c540c5110b0b4000204040d00440680341120400c6503200e640c5545400180c88107420900020004a0002484100b950301940401c078010f5080e170813502c0c15074030b00c3c14032030807541a030090368038000c2c0c01c400030413451820105040c00410740380380105051285044880c5042040d41085000c01e801140081490814030180303092084100c40c148903175450001e000e4107901c00c48100a805002c001000c00c40c4c0c0340200210343d01d081d401303800c00081d01d520710700150641c2450f0041e51250010386210b050182554002c031811781718007841078a01d004513541004200c0d400364820300c1d009203003240203040b041c4038480300000902041d01c0c041076004155 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 28697128 1250 28695878 28695907
    0x50d12020601060507050a060903030b1306140f0d06090201050f0c0601140303160305030a06030c090501090b060408070b13170106140406030b011703070c090f0c0f1e05040f030503 79
    0x582010f81001014400035000c0b42000821030078094000100044000ea42e08044000c0e20000d47d1481d0807041901d00f0380810303541035000b541200c2000015200c0300400608202c0079445004100d640202d00c44041c1e40801c440364401d0711003600c141441d918061406036201d030300f500000c1c003031740560b001080104120283c503c0a108441421030241d494141044018910f0301d40c4c3c120041d081005c04800100f603881280d120b50003558028444a10150b65807003481c01400090140c441e046007803040110007402c1c440140c8064440301000341100c64203294070380030740d0382180128510045814000082c9000302030b1000e10010107103800441c22504042d50b0b45e40011101114078005c5141c45800c002007a28000c025054078486c8841d150801c0c0084900f61550081c00805000c005086400060340440c0d54815103250780c9154091050741c400c00b100b540c00514421003040410507880c00c083c0d078207050703604a003c6000c140c1401410140c64a0f010191100f0580003180e00394400520719900c1c81c0b61 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 28698378 1250 28697128 28697131
    0x81906080d020d090e2401110f010204090609090804060c080904060603091101050a0f030e010b090903040e090309061b010e07060c0203100605030718020f0a030506090a140c070507050d120206 84
    0x30520340c90b07030506c0716640401da20400009130b403200021001a41d142e11a602c2910f030300c40010101c502203c210002c49000354030520541d0442890503100056035080d50090340d421744c1d0401202810075180140a440c95403041e20101c0714204c04110801c1140c4c4c4034030071440602000da50001d0881e07030750701e080070034840c05240d40350510000384040740c440742e4401000301d07111000f440c0208808400c1851706003d012580e541035800050541080860a4000050411101e004883e5200c54448596041d01d0380704480e00103410500c20400883c0440c5c0b580110110294045c00001e4010583d000b0542008490f4112100041300321070bc2030194a800c10440230100040601000803c1c60180040e69070241d034480c1c00f0085511006400402c20203506a680070280c143e111039441500540040007400c0448005109280210114041d50094415103504060f1447c0304105601c031606a100d56402807201140c1034880c2c400c000c105900d4240e440b4090521a400f0035004c403120703900203400c0c400e0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 28699628 1250 28698378 28698389
    0x411040b0d05100e1203010803031f050604050d081903020c0d08130b040309090f1b0804050a110a0506070b060a05030a030503010b0d0b041d0c10081906080d020d09 72
    0xc284280c040410400f04001141c100084000140c51414445081c01c0650306106039104000c080f00018802d54007000861080100034603481205408000701d054080301801015000182404184814149030b0f0114000900501400b13042403903080c00e002ca1036181c803000d0740000b0b402190110342d8540c100400599000b45041603811480c11000c3c0d210001d01040d4050018140c100200d001d060145500801500c01050140204040c5440c480c020f0119150034160740c9054222001c10305101d800780c80d0249034424050300c40043c1d03a481d80c00c118401d01409940c0b0001003800001d00d0766030080107104280c490214034000d454010200006225940d00c054005e80200f101c510000e64000308a81c15502c523040819254084880c00c0300c01810b211040c1c5800c6071520301211042c9080c0f500007002e600154084600c80d2030008180030520091030802c030041443c0304d002c5007900750540716811144500800000b105640c0d401c5861070854101001e0b00581c00c0303145401000341d40308142001400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 28700878 1250 28699628 28699639
    0x30b150a020a0b150904020405040f0c0603050f0601090303050909090c030d08100b0a0210020a03180b1b040f050d02040905070b0301092a0507020a03120504170f03040302010503150402030411040b 86
    0x110b0386404900180c000510081c07223903a550001034200002941c1d005485070b00100f00380c104036191040070300103010a943c000200340340b01002440a62103198000c0c03d0302d0b41991064144240704c018000142805020303204c09004102d00102d198404109100104020303580703200040c200882181c00e50f0401e41c1001211007020441c80d01ca1b5500060383c000e0214a503000180d030740c0c51410781140144180c0602030485030605450009018000300024007601d00c980ca016005000351540b07652610603071080c0600403504400c208600c3c98940d800305000ed0000d8008101441d13a5078645007000c601ea08403c0e0f034041b01000520071003803903200b000341f1140036503061a1856403c44600c0d0410500002910401ca0001040320031901c03000c072984011948102070b40380c44030000c900501241c01a0003180481c000a510588070381100061903d81c080240014519150442e0011541c0d036100030000d0426410070100c45040d5141c0c0c1c4001c520590040450252250743c2c18104400d8590f00d4003100d1080 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 28702128 1250 28700878 28700911
    0x1a0a08010603080f0d0e1218010206150d0203070b030109091401060812160501051915050604050108180d21151503110f04050406170607030b150a020a0b 67
    0xb4155030880d07208070000c0122030380f175850107030622010744100030b5224a0740c040c03041182c07100d50514000d014980d4410124050185000b401203a40d61401c6803c8030b01301c0c1d800c40d200fa0a90038008040c0404c54006015aa8203e403152260f035410f500a034401841d81d03036100c01a00c14050403e0300342d505808020020311090386810000caa84400701001c010000314005468202c8a0036814130030681d0703034030000a00c801d2810b990055000d407030b07400019600c90b00b484407001b040c1c80070b131390000305840c1d000b0000c5003000c0c10031004440c140b800500007409507980e4014038844003000c1244910b10401641c2e080c83c00d40c84a02c0d400c01c040c10103a0151402d40c00c1c05240364003420303c5210b940564a040c15031009418000074228041c1641503181c0a95000010b00d4885a0b1607110003401507038016a41032060340c0d039840504900c038640040ca5225070b0084808158507621a07000700c1d4412100400619407650300b0704035800154445101d000159021000807020041400d940ca40d0040b048900001c06 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 28703378 1250 28702128 28702133
    0x60609040305030c311701060612050a090f0f210f0e031018050c09090607050a02010605060415030c0e0a03150f0527030f0d0506010c05011a0a08010603 67
    0x2c030702029040881032440442c20341d101d600c81c0728141400b1040101c01c081200301d0742c5040000c0003081d02035100c020803004401a1480c805010308400c07201584d40b00c8600c1009940c0540003014040c200018098841c3c00e0800401c001d40c00140ca0140502c40740c2039007040503d40900c10304c14900e80610b045101515500b6600d802406a8504601508107003510b07001e440002402c016807100800c150380c1ca003800e40d1004160318441c00c0d968501c54000c454081808408211107503d0481e030f508840d074060400618028030801c0039001d89907241c00003003849910340c0005044da4009404c0054000c0c00480342c205015414066880d040301507003482c0d62a8811900420a4810a40400f4000b03081d81c000700300041025522000480b03480300800c00c0142000d05181c030040e0243c14207101e4031840f05048007802d2101004448078071443c00d285170715000403c40e5407006031000034091414444039003040001300d0002c3c09142e20104103904250078030401e8100304004520f481d0000b40f0640e1400000303000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 28704628 1250 28703378 28703387
    0x6050c0d03060e010e0414060702070801060b09060f0d06031211010506090114010c0311010c03060608160c12020307020909070f0b030c03010303050309070909050703020f01030207050a021c0f050d020606090403 92
    0x191088000c000020340d8460030070b0491411f1594500c2d40030b1103404100000c40d0340c040b0300e03401a280510021301800359201d1001c1664042c40d8001c55002404001e07600065040e24018007038072031100c1002c1200f41c0d0301d032121240c0316103103000344012072184290030480f450700303125169100108544003261541090200180003038180d115905001441f07048070709240c080d0242102142d0100d0080c8860a16160000d01909240c802c000c08070703140c4e8000c00c0c8280000350b1a814281d03130955827210045002d0702c4001880503494400e80a50004110b0b88025031180da00544c445c11801c070060042c58a40081124484440c1c2d101500d07034541030040c0302101c17132100110380c1165010300d05540c40351640d0b143c09080449560141d0070710380c500b0008008101000c91003504072070007180c58454804c0d0810056050b13104042c0d000304141c100c042c0203001483d0030651004c45010f00796501c88403030169a92588a002c0c07106040e1003a50081c0070560005a0410000d035000c0f109650200690406030303070141 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 28705878 1250 28704628 28704631
    0x90102030f16090519051008010b0901050d0204030501050403090f09020403031e0e030307050a0b1b070f030e0a0902030f07030b0a0e060f1003020c0106050324060f0a06050c0d03060e 80
    0x10031240304828041006480f8000705009810300501d2158440d402c0d105115070704200b486903e00540c10a040260090300822134641200c2004e020907150040d43d00046481b80d01c1a01c02c0c0408507400e00010010a00074455140301d20300c40d0720341d40300a50400400050900065001100003401003000b440026805040140e03145c4841407041300707540e5101c40030384070420070390402a09480045100006d1140c00540964a00d004111040b01a220085002c815008864800d18001400c105000000c1c3e24450f41c12002c0f4007901d00102c500c4070140c00280b04a41e40e03408040d0480e0080244a20380b106108455040404d90500b0085013012201190949402e4440d400d540c0524500180c0c158584040c0031840803002404860500d461200190003500030440f01c031151340c0703001c20220300380c140000e9a00d582990344680343d8102008101c0440c0d00d41004003481c2e0010226150303054162105000030000d400c180e01c5161b01e94a40001052400144080311000c0606110041162140350682c19 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 28707128 1250 28705878 28705891
    0x20c0411040806070f0f091a0309071707030212010b01080118020408060c040e090604170a12060e01050306130b0406020a020102070b1f060507080301060e0307030b041505090102030f 80
    0x1203401440300060386564060355202400300d009580400050a0744117200908000341600d03102c086e03ca41002c211140981400b500d450002204010f28003804248060b5501111210031a0300503510742603811034440c000c0300000c1e002c2d80210000d00441c6401c1c20020305504103c1e0003000082c000741c000a001c0a010b00c144c00c5204003441410300000940d80442c0c01421700700b0b00301c800d01d0500d4800031540e40c0c440e108800d8034189000c00702e114194003182250142e50854100e542d10581d000c00e843e1603a00190100c0d003844401083c8401c4240103018040c014505c0722100d07801d40d0300d00401d050803d500200030009040ca214817450014401c480c0c5150080c2d0040c0c0016102d000911080e0700a1066400280c19250340b0000c011460841000e804a0685010500005c043d5141401d607681c2c015400f00900c104030900c010701009124098000040f0001030403241019540e85480c074140750144d4050700c82203810090510601840d003e0150822881c8000b1840c501d0700f0351058002c000060243c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 28708378 1250 28707128 28707131
    0x90e0c03030717040902040323190303230a0501030b0610050a0f0c0204050f010302010f02030f07020d02011e02060105040501050f01020a02040b04020c030c0604050c040b010c080a02030d020d0b1906020c04 90
    0x40210f41c0210b005403005800c40b540c0c110368840e100e0402a103404504103404c1e60301c1c1e444003002a13400001040305980d4901a82e243c14a883e8681c4c0d00b42c0150180b0707400c211300e8840d810350800480e2914607405020752010b00d4002003950442c10201c0140720b00078619402001c5134480805207aa001d81111312044d5a07140207026480122001c9468500b0f001c0065030241c203200031b015034508004c241c1c0d0304803403007600d540d140804152410b0342c40c3e0140d001c2c01c40c000300d81882000054142041400340d100c1c41450014480c0c1c11505050701d140380f0724406600181e01040040c403107801c00384500c501501381282e40314840003800000039966800520020b000d0354130380b54012010307191501900c0903851b80700180e0b61140744914409076201d0b000c0f603080d241440344204003810340c03c0a100b200b0591034183d40711030000180b40c03075050303995004001007004c62104001014001400381301034043c1016000010a0303803030b0804104803000c09d0b01d405040c901185140200b107205c5e0002a416a034580540c0c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 28709628 1250 28708378 28708403
    0x6040b041506031b2111120307030f0311031603020d06081e150903030402060319020d090b0f091b0a0e0702031c1512060207060903020601090e0c030307 67
    0x1072203020700144a070040788160030110084100080d9103002480704545130042030700b090750369038001a01401009a1143da45055940c6804a030428200b00c142e00707400f0b0101034040403d0301d1001c2c556449004181c0c0020081c050112940d6810f01800056200c9411041d0541c20605140d00710707007031211800f4061590005050b501d40e075040c0c2281c0f000f0941e800c1030300d000281050115424020780610394cc818011010008001c1c1c40051529008820650065095640c0c50f4240b02c056440506840380036100102511019a03aa00041030210815034011598240e2490690b9242e0030142c2000040120042002940c500005450404520f0080c4d0301c200b0a40301008103d5000c0707690040c502050006c01000b403040e4001005203040ca8080703204081301954400b208040b00c041404400e07440c50f403210104020341104410f410701c5809000f005180004a503201c0045407100fa00880243e00148010403070540c2d00d100d05035440d620600a0700b0516200000207899205442c4020a5200b1140 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 28710878 1250 28709628 28709633
    0x6100f02190501020307020c04050c0a0f0909060b2503020c0f06040906030b0612030c06060603100801020c06040b15011b080c0f01020c1204050d030305190c081f060206040b04 77
    0x222070100d04107800c0215215040003800b0790700444402c800b43c0316141c07600d1100c0c1011301c030b404d02c1810260f05450074800d11040484201c100ba0300840100480a10081036801c41885810001c0c40d070010100d5440301f0880c242103040d1b1880707000b1040341180c09042c402094000c14080d003c40ca0131918191101d4800c40094403074050340d040450200d28101003c01000341d185045401500120b80000b00c152001011a41d80e00c0382d0850032005401034800700e0018104400650b402c007141d50b01074003450340c54960080c00c90300140303c1341c20780d07500c0803040c0424407510303800301600040304d03e00302c0180c2e03050800064600c02140c5804083c00ca9507a0040061028400079154440184400c4d11411029402e01d11301039049001d0150b0075005000000c114004002c2c102c1d021144003500800c684100307510150024540100030030303d031701c803000784440d10920241308002d200d105c00e171100d00c65800d00a1303c200c01110000074141d0b04e1140c60409020b883e400160030740e0b020340c0c084407007e519911403 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 28712128 1250 28710878 28710883
    0x70b040605060a150203040801050f06030d051804020c160603050c07080c1212040506070305160f0c0b01120309050303030403090510090515030a051612090305090d0b0103021806100f02 81
    0x1350f100f012400984440d01110343da0100c000c104943c40c541c000d0240340c940407200c595004007951540d03456806449034100e1280034030050200381d0316a01c1f030381c9540b001d01c0d0003060580c0d002e030700250b545402c8401111300c03842d2403180e010302038280c0b4a8108810300c0c11443e01e81c0d5a11401700042c141030404207840140100c20010400804c2c104100c02e1344030180083e2480c0078080c15103046505006901c0000d190922030b00c2074921410300e8509055000074905d0041d240135079180c090804110402401c40c000c5015104541d0090851038443c481000d014100100a10301c95000707648603070800c105100101c0d621044800640e04202d8141d07024840d040810384020000342d101e2a0402500d002d080140301902c4003641c0300c0c0040319410f00650b41d8494101070001030307100c48800828001c0c100b00707980b226143c0c8800030040c0b0a00701140f03020b0951000aa48900d0600100c03600e110220050003142401b040040403055072710489462820564005080c12000b003018000f00325030b101070112298402c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 28713378 1250 28712128 28712149
    0x603110708040b030708010801050903030103020d030c020d03020c0a090608060109020f0403050607120b0d030f1803140705010e010203030403020303150f040504050115080c030c060c01060e100806060105070b04060506 95
    0x401c11007991940d5614021a03aa00115098808208140c0c0006145001800381c2441031803c007002d58510b03030940d03007001006070340c0e2030058003000b18071880cc0e001603c514591010650080e002043c5118000c81004400120360700301e80411800c1000410004100007031007410748022003000350325800610048c0949020310b03400134019101d18014000e82030b8004544182a80f0302e02e00500c941c0d03542070240f100714150454020006030b0560410b00c2006c0c454801c894155841c446d50f00c1020707699442c1c1c0c090100d0441d201c006203030000c0300108007a68002e00c00900c560020b0001d10304500d00f50320007079105d01004219002e000d518034405e541c20360729082c8120440000500800c80e42c03c040c00c16a0003000c00c6ca00305840342d54038280110b80303003d000030a0b03040c0642c0100100100301224091041c01c0c0c1002d180c6007001d40d20b071980404c0c204801130030203104120314020b403a011460015907514010001c4e02d290705100c6c04200c1134002c0745840f0004d5501035008007001ca400d03180e400104455009 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 28714628 1250 28713378 28713383
    0x30c100c0e190906050603060d030f11010207031106090f060109050402010903020d0f0303050a020c030915040905040f030306140a0b0901140417100606051b071a0408010f050402010906031107 84
    0x1100e4a10320303075030b0041105a034255903c58404003c0700c0e85135800c0c803465120546620307500500340c04500c80064070402e41900c0200c103620700340103002540000a03007681c001c47c0040b0041164103004c00d1824004101e61030b40030030094000e18505413840402c1c4e0b211041805403041c1c25465a0020301907901441c1c03220006d41e4050f010020304e14150130085010b1002d40e0040300041c1c01c10b804141000114020340d004402094055440e10381003804000c144050590098103001007030000048000181c41601d20480c015280340700542c90301d1900070115551508243e18405202c80d105001d80c590300c16070800d0395030100e140742d0f4510480d00140e03008400f108120264800004c1c0209103026440000c2a00c101c40d03c1c00c86600440e0700348008140c810b140285000241306004001a40d608040d42848280c2c143c400c1e1040c09448101c00040006086406507469074001010080705000b44546040150300041c03c004605069000800002080c4241c800705a200c04000300e010748260100e901465 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 28715878 1250 28714628 28714639
    0x140f041202071e06020d020c010e01030f060801020c03090114030f01150210110901020c0105120a020912030c011d1c080712060f03060b0108010f031b0b03180609030c100c0e 76
    0x105200186450240c0f913016000050040e0284041d00a000044501d443c5038140c550303a200c240c40c6070045000300403040208410035100c24000544500038802490410715070302c0a0b40d40e0301070b100b001424103403005404032441c1b0410010000d11400c0c8131300d010f06481c498080e5141f40020300c00d04910b882d442e119a080c0310f900d0181c03040002c0482034010900100d0a030241c2c1c0310b8a00010043d101805443c0b00f00c091402c0c100300007441d404a9600524402900400300700b640c0080d41040f61646d005100841a01c0e03664011940103140545485080b42c0401c0000b4040030f04070071100c2c01c800c80040904c40920418201041c00c507405103054200340000c408003000450782e2210a0085100c480c401541c0c0d25180240c8210340354428458103050b26404140500302e41e2456803445c40b80c001078080000d5807100c25402050001010b002503008840800e8081541c08080004a041c15005450b0380d070180d000b00112130846c040071846500000c7e1800001802d038018040903108039280b005030980c8030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 28717128 1250 28715878 28715909
    0xb100207030b011d010504020901031d06011d010303021e010b150304140601060206041e08030c03090106094802060109050703060b070f02130e010c03140f04120207 72
    0x15540050100101da0168540030440d90365104841302c1055107040303080e01e0404210051000d402d0079001000c0150041c9000109000c40302000c40c0815001507801100d03400c00001005190040180f402c1c005103404841d00300c0354035644e0b010f95100552100020300c540c1c10020010165420343c4401150030016180082d00f00b80c0c07000c0c040855104036012101c13000340000341e0307003030aa0008550f8165401d64000300641c2e1160740710410318100e0441500c220241d0b070108440000c10a10140d030007030060482403a1281060b464507800d49d00560095100f9600c2c1013280010f55550003102c80d2031042c40b0f4001c0d20450106802540703c85c01c03818001c00c86640003248001019800180303d4121386c034040c0104a10f440d202c1c02101a90030902c154194810140820408110511500303003030203100500f02031080e1054070001090702d0890351502c510340d5581480070703034064150080200300c51010103403504914000d40241d11820000d0005400a8400c11417280c0d032600811009010305440d4100c034160 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 28718378 1250 28717128 28717159
    0x120b01110d111504120c06020d110304030e0d021e04020c0a050a020907030c08040201140d0c0509010e0103050c030112080f03041b0b070f0b0603011508060402010906090b0f030403030b 81
    0x8640704402e402aa1140301c2d280c0180441d41900c6a00660348040707030301042c45051804440d4264104e0741664400d50030441212040410301c62400400e44800d0700585074505428090a4109445000d90084443d0924480143c1e2801e6010034540011401c140d001c00700000450024060b954100202d4440c840070700b001d2290015441c0340c098070844010009540340c00048081e1640e1070880c0010600001c0414015801612010401407600710018101543c4445a105850501c41c0341d0021a0300080e010200d541e200b06c181382121001e0801340410300705044d032a4828401440707000c1c0446c001c203a0200410a0400880301c200030750019080d200d08007810721541c9605000c0703400e440301c07c0300c0c0c40005d02d0015090075142400d4011401d50f070b01d10825201d645012038014500380e89550b03100500b0030245a41780f0168090316804000701068541340c030016140301d01e1900424140301c24944100b0519451130b0445490300e168034901c44d02c03030321145002c3e0050b118401d500d40c0c0c45101c686d0325421 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 28719628 1250 28718378 28718387
    0xc020111030f0402040b0a080a02010f0c0615030309080f060103020d0602070f060b040f0515040e070b04090212060316060c02030a0206030a0902010207050907020706140409090c060f020c01120b01110d 88
    0x1544c000c507000c1102c501c50700708004040202e88144580c075080403014601640c02200100800c3c1064100501218010380d68007046800c00d4503009118440c1700010310500d5072000348203010b4220000140100403555050f16642d140521000b48150403900042c010424107406403a01194000f000d540c1041c82841c160303018040c1440954000d238500b413402c403140856800b4176405145c5100c40e01a40180c0319082c003000d0300c1c1442d8540c81a204214000a003a00e041000f0002404190001038840d084c50140e0700c81d81002411207880b0381d115080c0000c01030540fa0420003103c041d03045c4418200751034404241896102c43c40650f0141012040140c0c10701150002d4809034030076400e54149076110350030810703a00001d0720f000d001a405410103004d180d000d0b4070341008212140d40c2040c00c06994241800c107552640e40115141003c01c1c10400906400140072448003d260016110b50810040002e090f00034013101011029142c000781e03900f42c0d01612045441041a030241d40c05e01495040181 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 28720878 1250 28719628 28719631
    0x3010605031608060906061e0301120605060d120c14030a110105070c080417010905030c010c140901020a080306010e030109121805030c06031e13030f0503190c020111030f 75
    0x5801e810030b00c8100c607420740300d1040544502c50007041d12030b40791103103010300c1034076003040350100c40100896460f100103454182c09036000b002c1c40789840c009090300b807900078250340003d00014041d5440704400c0c0000b5041d6480010344075281e10301189100040d003005154590138241407401ca0000156407049580d102542030110f106d120000e00c4640c89101088400a17031484000c3c00c0c2c208144000e020700104030b0644021900144000314442a80c0c3c1c40f56410740e4050704445071660341d14a01c001a40c0e4010103003903142ea90346403005080091900020b03441d0345e95004010310f0300000100161003a1301407000b00d140180c002d002085161034a02d0b0200b0309c114006d00010200d00d106d20203c5903580389003848000da84028015240808804041c000705804c050000c83c1500705c3c10b0708080c40c0c181800c140300c3c03041d04c41c411144c1c640c50490502501402c0c01c42641d01c1002020001c1151001c034100c0b82074980d603046040040c40e07030500c00c02240104511702039441050800428068681d2021200d00e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 28722128 1250 28720878 28720891
    0x190b040608070203090a060e03010b03010513060605010507150b12030c0a05070f0302060f03060607080f040905060603040812090f0109080301150e03070e0a110301080a05010b0a051509030709020301060503 90
    0x1910310351102c600603030740c0c0d002e20b0580c04c0e07000d02c11041c1800098410820240341913405000410340b59204400603003034503021244da103a030300011604c503c140442c0c0d0160000038042801c120389000034549800c840780103407001010701103031921402c80c2103444800e40944100d00c90300c180d948444150040640310401d40c0001e40e0244a0b024020400e00c0f1080c510b441120b40c02030a403071a010b00d8000703c4201e90001000c460740306c10148060804540e43c0b80007400c004003941d0010b0360310390505407107004071200500418010b031000c0c800c000c0010742c8942201c1c8010000300c3c011b2a25942c4c03550741403074104142c60442c045e50816540c8001c200c142000b0350305030b038020089282c3d41e480881e000c54070580110003045e8180c0c0061802c00001540c1301d1110742150090001243c003000310525000386a20a034021003031a44600001c8083c80420b100314a9095002c44541c02c4c00c516210004000d180003640b1480d84609c0004c82520703070355003000b49000410032124299243c0d0394400020b483e83e0422541c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 28723378 1250 28722128 28722137
    0x409020c1c080705091e150409050114010912060e010c05071103030309061602120711040b091006121407180b131203200106050a080303040213020306190b0406 70
    0x1000c441c0580b144510503485a500c890400020390100701c8401d660711070804111100d4618000035480e518035041403c14007110290303031a0300e0002c1100131114147e0104415241d03422110b0610303030784032050108899107202281e5984044c0c0c200b0344020178a8035101c40c00d6600c1e10880350422600a8041e22070030740140406031180b0743c10b20074141c5030b10085070450381603080b00c400174058003000f0039181c424031104e10480707001c030f0040075082d041a4400e20003580c1e02c10003540314440741e140034080c0c0c4800c0a004d98007112241000900b10110040d1350052006010100c2e01706003051041e030b44030050700c1d41400c15240990920103806006224000258003121102aa0106000c2c28440489404054030080c043d8694178000c88a50b800301c0c62441101044600c4641d0180c0224100c9001c50500307080700000b035428640001c001b1503082c02c0d804244241c0080c010000941d0301c95851841a0f44021400740c0e580c4e550030000344500d0b00f00341c41051403100c210f202182c2c4031444005401981c0d01340e1103 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 28724628 1250 28723378 28723423
    0x80a0609090b27060c03010f051c020603130b011706070c030903030f0c060e060709080c0d0f0c0305030705030705010f020c0a0f0606080f0c1903081e0409020c 70
    0x2401d4581e4810041c1214520001240b1a16140605032a08001c92841c95580209000e5241e060520540354546142d4000c0010300c1070100500220009100403a0b500150030000010316008811504d80644100b41c04000211a45110040d248615500c84141c2c075856842c0c4d1a4400c8403001064106264820b55000036803940c000c1041c07440701078060302c1d40b00880c1e2079641c0407288101ca0300c1c8042c2c10420020076100000d80350b07000c3d544c180c80303910010b040c00e4501460010f14a5a165204260b00e034011f0411f2031050300c5000c441100181c01280d003042c00c90311800c0c80c1c1449055584002c05900c4001840f00900001102030480c5501c00d00003400360075001c0076684140c2c007454602d000280c002c011b111001401d003400307040300320384900703004101c45540300d4040e424072026030080552078000c204004102d01d0151007020001c4000c0e04100e00c5241580c0f1036038810b00035404940b800502084e42e03215003812001c26034004080095095550350380951345c460300ca808949400100e040c9809 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 28725878 1250 28724628 28724639
    0x60609020a0507060207020406090c08060928020c0102090a06050a02010501050d0b06040c0c050613140d0e01081005130605040b030106180902010509030106060f020d030e031602060904050106080a06 87
    0x300c0303a2055296079110704020480d1135000007940704200413070b400366030780c0d10000d500c60300c90145034280c125607103c881c1c40e072400409020050000428000c44100b10310392143c2d002c0500030010340c0c40d0901c034000603103c4030311140b00d070700a220701a54160301c54022103001404e10380c4079004244220310341e8006d001690340d0300d0505c5130740c045965000304819600d90015030b10341400c1d80142146026450f1001c0d542801e03072961400c1070700c1501c0c1d11103800109401081444000e0785c031148040410002040c0d1403102c80001004002c0d00da80c02410002c414011031200c964968904024100040039681800c102c4800c1800a06091207054002c80c204103460f40300f49810700c00d1000300d4120340c0b040d00054a03050304003801000381a408034180b1000340840c0000fa1400d1051038054002ca4460810001550801a14003108154100105410400d099a440b007020003511001c485945950016212510000f0885e015140080390818a4140005152342c0d10150482c046c90389100f08206141c0c644 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 28727128 1250 28725878 28725881
    0x15010611030403030f08070e180105040605060306060703030507090b0c03030109180c030303021c0608030c06090307030c021306030b0a0b040c0c05030304020f0f060706020904050a06061e0315080a060609 89
    0x80c48050041408410601c000600402200f82d0041248c540342c4260100a80092918407a44220b040a442203000510143c01c05200e1200901800c8a84074250b1801c0f1001881c2440b0b0f4078001403c264403100415a114091040740010340b040094480d01d549680896559a804c00d00c42c041e0018141802d6410010081403d2070700d55411080d0010035504546003a00a94000c410070392200c40d500c20304072a0b0441781d100b44400380c0492805141c1d0381d0305c42c0c1c0c14513191110140001507503810800c02d0b0300010380c111110f411100e0341030b1000c900c10162101e82e0741c001d20140d800a07041702c010208101a40b1110381c050034507880110f0f800c0083d0501c5400841c4d40885500c0020074652081012a001d0300e400e58450310480c1c030003008280c3c0c6d45103000100b00d0301d403c00003040fa440d0703030041005006c2c0e280902809a00c0340148608104845c507011700101082040300347c0440b94088045035020052003900804211100385c0c4040b54019550910580d940c800d604d01640d206181c42e0340420f80d1001d6 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 28728378 1250 28727128 28727137
    0x1e02030a060b060d020403110907030e03030f0c0706051305060907080d080402060405030703030903060b1009030b06031e101103010f1e1505190c03140a09081501061103 74
    0x900106a00e0016a4078240244050a00164844030910441161040ca400240041d40c464030300e0000f550090307414000f01c8100034103c01c00f490304101c0520740040001082d00d50016410f8518022921416519001d61089640240240741404100b1070b845401c541c20800441c03103802150f1031940c80308880ae4a4005502030310910303070840980b8848640c13007104115003186c00180364070301c0d1a5403000040d2402d52140d0084020400d000d43c2002801150312407581c41c000c041c1e4810403c0e64003004002c0250300039000c01450b0004c5039001c94001d403010000c0320004460711030a018220f000b1780350701e580d030000302013031022071421f1881c07000b4a0030944003528101c031050410b44c90314900b484180391442855410040021072100c81c0083d0121101d01440d00d40b0300a0344a0359580c1441c1090003004038080c0e505c2d182071002183d80300e07001a82c4840401d0843c1c02640359140c41e9803200804889402080c0d10034809849601281201c840001031240e04a0f080c5480e15910141442603003501da004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 28729628 1250 28728378 28728383
    0x6090609010909080c160810020702030304032a06080a0b030102040f05010c140d0305040c140306010b09040902040f0c03200913020405040903020c04050c070b0402060703020a0b090a1e 81
    0x900c004119011881e04943c200b5489029068140f100078050a07241980d155011101e8440b01001000f000742c0911500900304818001980b0303040b981c0d008280d4a204a120080c48040300d4900010b40041c1024526510b46480711041805652a0402800da43c0191400b0301e00500e8050711040310302d814801c60342102c2120b00072624003881c00f80150340b4072107000741c15500c03ea0364028981d81328205104000000c412900c000816003040e090030b214a94a6401c21048540200411038240e0780000b4010704659403040340381e9072121117a011501600c281030b0001d40041c201310016100300340e642c104242c03d5400e5907041000d40e405511018000080032001017610500b000a100725003402a01820100b0304080d0151a02e959540810100c0b44240c80c25001a000941d070701c1201c1c038050143e41d810030314043c5d03010f050030819203801d41e107040c0160000744114400a14a01014002d000e4104840d400400b40c41c081c0c5070103890141c4071b10f45501700721405803054410030742d203450b901b00b560340164 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 28730878 1250 28729628 28729639
    0x90b040501050705120a18020303070506100504090308060d05010b03010c02030315040b060d020306011701080303160807020d03180b0f010311060a050d05090a0212010207030219110112061a12060906 87
    0x8a5540210740100703000b0200380007c0403e0f02d030f0140507850800081c01054801c900403d071903c4d01906140001c0d0b05500326502c600d06041d01d49c0c0110390302c1000960045000c42d00303200c1d480800d00e0510b005003810030450f074040d401c040d00300d505150048003441c41018490110150010100c080000711801000b080c5d51008080c0800c05c500d010650155611802c181490300c0040703030158054414203000da1040710b09510000030050303003846055000c25800541c3c14400b44908102001a4654411501c900101a507400c40007001307203d001500711015030024501a12402c01c10150380140ca02400103a982000d5600b50034032a0070043c0441c1e40910840d9501802d05284000840280002030034183c098800d1200304809a03607001c0400511b2148040010381e5039103245006030402c583c4200c1c90505c094900140004a110b00207540d8911500340b07003158040c200c00400340020021900302c00d050810b210125003211105000801c1e0080e0781c01601c0c0095510002040a882c204039140340e00711 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 28732128 1250 28730878 28730881
    0xf0a030309151206090e010c020c0906010c060222030311030405030307020103230f09070911040902070804080f0a060501090c0903060b130f06151106070e0112090b04050105070512 79
    0x1040c544a00200968041c40c0c2040c9400c021403910f400e4640c0f0340c225800065862500811090b424403500c50041c4403400a0101c1c0040c110000744e002c0700003070420317042c80503540d400300401903a0b0b0304440d00140070f202040d081001c2c120080034402590300040700469841406510a42400000d4500f103c13801001545048204e82c011006030043c02104002d00460312801c19040030301362400c0d4030034078840014100c1880d2016101d03103417070407035405a020f49241034990080782c0668422101510020b20000d0f070f0f1003156103030a41d010710541e44046000d000d07003000c84c06840404603040f008940103034001e2010b42d0301d03526a03200711100050780e440450301c807280130000a042c540140c21040f40003410b00d8003070240c40505c002690348206a03100026a50030080c404044c125405c041c0754803103440e0541d101110f200c02e0950300d80d009803921091001c40c001c040002c3c0e11566142042d49080c010902140c0c10600c1c003240d64007415207003220f55509141c0042c0341e17103102d1026501c00d60360915800005 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 28733378 1250 28732128 28732139
    0x212070b03070e040b040911010e0402040e0c030405030702190f090b0f01121104090e0f010506010c0b100506040303050c0105010b0c07060c080f130305010501050d11010e0f0406140f0a030309 84
    0x455026045940064446140080035981c6c0d03c51005031502030340c120154510010001000241c40d0000c3e184103600c144401d0002915400d000355201c5c03071040311240d503501c44e41440307841d601915400940c04140072181441118104055400b00e45000c000c2a070311548449a10080e07030703410000307a500000c42405080d1690312600c8040e04031101c0c03280000301036503865540d0b074160384503800c42131080342c0f6901899120001005085402d11042e40200718a08001000801d03114900c5805041002e41c0c2001c600680c40c80b0010f90001d110007086581e540d03989260161094108900c00c1c4070315480c000001034007112450446c3c0900d401c09000d82201400c10401780d034480005441601e901e00144005284804128010107541588a200034581c500d146070450a407641608160301540c0c0510303400740050039030065401c401900b400c01d05c00e040c1c005004030f9083e001000a540c0e000307041600000307800160680c003401043c0e0a07102c9480100301316090001440c0c00703120040010341281020044d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 28734628 1250 28733378 28733387
    0x20a0806061b010501060f090506180d080904020a0c0210020106060f030e0c04051008060709030209160507061a04110f04030813150801150c0b01170307050a0c030212070b0307 77
    0x1450035002c03030a50301c07001c0841c11070855100360405004140c201904454094100040c00c000309401c5030160314040c803601060460300070303480c0d110f4000c008180400041107000c1d000e1701e11000014100b19111004420010290b00c1828408c0e4002c03030220402c640018410700420b000c0d10900c4c1c548511694003000c08a000b440e170700c580c60000340034480d00c8000d640d4541c0036183c01a0160507650b01010f04280f5624108038019045c1e00c180b10314a10704000680399504c149502204081440b000d02046001c141d44d14070507851f0090031503140a25240b40c500521003051003142040d0b40c104203494001d807468580e41700c1d82c0c7c0c0c9880d040c5028042000001d8003a00100760016581e000c01e50039540d101c441040e0300b40200718100c08204d03502c1c01404007401031100c9403112030040c130301911005080c1d01c50000c06441130003007549808010030002640c3c0c00400c00c0300e94940d80501103619809030f5041058550401b400101d2291a50011040740c5501c001001c00075034505a40603455a1a010025207 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 28735878 1250 28734628 28734637
    0x40b01060f020115030803090d0513090b0a0503061305161208071e03020a05010c050403030e04050a02161a06030f07140102070302090c090405010510090303081b0c0f0f01020a080606 80
    0x1d003150b488011810804407400d0188008501c2a807641d502da04200c0b1450341000d076038041c803c0030068140006030100282c08100d00844c0c048080c00140424898041495030f802c580180313825100c0e1906000f0815041007041e000a40a401940c81115402103c1403440741d4520560740c004d00400032080114865900400e1743ea8801c10001034140c9803594280d9407403060f5402070b00543c015280840c1881001c5c0940700c1c0c4540b030340c0303441481c090450764054601d0540720220fa00650707a03280000d080c0942e40c0e0441d1280c1260050203540708403145031400d00b6000742d00d5281d03209103018020527054240054904095884d0340054004113040070100c00c1c0340e4601804441c11032103064030010141c0c40d0741441034000d4014000c415a20030f950028003080c1c960603400940140001c40082c1034081c0e10500c0350041d00e5140c640300609845c0c0001900009001e60000c07003004070001141c010381200000c0e680050355608007034034015540c55807200c1c00c03800cc1d41080710104804000003820346c50998000c1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 28737128 1250 28735878 28735907
    0x901020702090405062406070807030201060504020d0606021005011d100b0703080105010215040503040b0a02030d140405060106030b030a111201050103110f03030c0c150f030901150509040b0106 85
    0x1814048640c0001d400c1440907038003035409402117410700040460345090540d1314040025940c1001c0100b40c04111a440746c0040501004400b0844404152003034200000030440140b0554442481d104218000d010074464800580b0520b040c3c1d0303800051500034039048920844000c2c0407034120382070454603000003e006d088910140740380071034422140710140c5142c501a54805e0f22560401001a00c2e250198006001c0030241108007c00100f0002c120341c00c0e20300b05400c0e50f44070860400180c1c070710700810042204041c18201e50102c030080300c01c6c9035440745016000b100d01c01d982e12401a0110307804035074001d400d90055440880030441d1111000003580020300311030301c8403440d00c81c003e0031104d0030380003118002900142d05d00741c2c6c60a0300318031060342022000341d03181c09001843d00b503440d55103070a0b02e402042e5004481481076204401d503412110f8900313009a4918200103403030b00070411440503004044d200800071500317080c00004a4415a44000040da01d6400c0c00c0342a10501810b50b403e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 28738378 1250 28737128 28737131
    0xc1b06090d0201110105040b0a060e0f0c0c01140109020a0305160207090b010509090f07020d0509010504090e03040f080304060207060c021003050606090a030c0e0a0203220807240608061501080901 86
    0x6071303070604c0248600e0b80b00354000d5604084c1400d108241005030b41d03140d4400c143c0300305d0070814040c014601200113600040081c040f581c0d03860031054801d02400003041c03c407000c000c2c1e0400000364098990000c200c80300f00e07640d081000343d079a80b000d0207120840448072001684440000c0c48840d01d5980b00240100c014184141070090900006101c18811502c0e810f624a0304010f002905804000080b011041414042c1c202060300c00028014003580c0f161081f48c5444a5003038807484030600c03ca501409034011000000c544400009680303510502c40c0e07070f00501c201000058441e03c14000041455801001100802d5481c10110083c04000c0d1820754050010404e205942c1c3c0c40c03840c4240190b208180d1144a149070608900c0b131000d0003400801514010030402540d501010220002c0d1443e845086003c0d210314102041240a06003006000700c0c151800f00300c10a01c0005903c804849814080c0041905d8040350b80d02c0b03510a17505060102d00d020b010081c20760243c40010341c030800380d200 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 28739628 1250 28738378 28738397
    0x10030620030403030209190612020d06080109050a050601050312030411030c1f030f02090901051302070b0a0b1915050901050705010203011d0a11030a0c030b04090302030c1b06090d0201 81
    0x40320030103034015901180420b900050040701c1c0e00703000c042c02160884035603240503082d142a0002e00210100c49280c580113900042c1c4022101259008602526008008200c02c4002d0718090340e555a14080580d118031a00d4000074003840d00107006060b2401c87c8440c903013180c840b0398500c80410180c07a88030b40c1c18001c08820b441640c940c2c0505a030340d010385040d81840d0102c3c03100c0c00340886941e8004070784c42c0c0e070040040400b103485000103c2c0c1100c4013660700032841505801c000c8004d00030140300034841108403040c00015503082e00722151610085901000f00c0b40320070000c0004511602c00e01d0340c2011080c0d00300700320703a00900c050304030808181880f901d0b060349603480d03c2c01ca23032003604010420005855120144801c0301d0350580d0101580204000c1111000c0040545000003448040480e4940150000b03440c40707900294010b4201810521070b446031498081c1d04d94002905a01d143d106031000011900c4003802d01030505030f00500a01d04d0094080140880d00e01c1d2844240d040c0016a035 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 28740878 1250 28739628 28739681
    0x21e1e0f030f011a040501030f0308060d06020f07140609060105101709030c01061a04090b010302040e13060b1c08030606040803030109061d0402060d0905070902040303020318010206100306 83
    0x4060501070b0001000043c2d46082c0001d070014001c5940355030b0380590f180c900140001945030081c4003400307802d400c04c280d0302d6031000006160707920318442c024000d034004030b221604070f68100c014059052166102129001e1403040995840d80b0032030380310708503a0141004200b207041403110000c2054580c980a0500c00c170180915107480b1080e10500c0d05070b400014030204000003803003003501500010209650050381d0305007a00e02d502403405841c018542c0c8501c620610b0707000ba81164001c2c104800114600d1605d04a03210704c0070019001601e115082401c1d05241d4905104004810a00b1040c1c800079080c00e5114090650402883c80e80c014404000c041959002040030714000c2030103640216080d0f0034035132000c440030810f0400d114837562038014040165921401c0d2410248141000600070313400c0d0828030b00c1c0060503480280200c0c4006408818150b001c0010603c4541e0b40d80d03503850b59125203004980d2203e08641c0c500821240140c10b00c0040c03d6500070b10500008a40d054007d1000320 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 28742128 1250 28740878 28740883
    0x6090203120705070305070f030209010e220b06011701051813022809110405130f02040801200301050603010e0a0207050d08040b0702070b1603090b04030f021e1e0f03 73
    0x180400d0b903013644050420010441c0030808180900010503400c640d2914550110340342c800103009526600308100d0001d030901da1480c0ba21210307024601c01c0120700144600b800a103102058450314009084a00514204844004128100c0b0340c050320b903481403180b050b00103440f80c5002e000c0c0f00784900e0200b01140560b40f40b41040c00c840c0142100c0c24460110581405403c0380346500c4600700700d0426000f020007060041c01e40c0c080359010b4030301500310001641c1c540000c000c8002c106c1041403000c180483c48071015840050398030b15010020b60340521148181c0d005000074403030103600040410040c848103461101c980e0300403c48400250070f2140c140c4c0c4072800c0196803098800040c42c09002c0201b03001044034050307081002030000c0d110540c04d14840b4080d40c0304107171003041c45d044605100720030107129084402c000e20402c1d021039151600c0e41b42007902e5001c4207106900c282c80c03680c0600000c41e02519100e20b40b0a00400088100d0440003610500c03008070240554080e904401c1640c0f991410b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 28743378 1250 28742128 28742137
    0x20d21020c07050a080c0a050d020d12020609011802090109021e0d051b070302060408160605010e01030203011103010602060601120209040207120207080109050304030605100b0a030b030d08040803040609020312 92
    0x240005420240c3c182020f122805400d584134400640c4410035003800ca480350f6401c03070103992040e1481e2141c8980e50002c00c828601c0500c0c002c25441e9980340907080641d003c05e1140c05810440d00034880140200c0d04520b05a4121388040e61182c400b00040100182d035a00400030070118501041c5101e6000d0700c2004103401c00c410b10300443c1d440c0d80c10010311141d00ea04115040380090b0800381040c815032402503880300020401041c2c86000503440d21002d4054686030b80343c1c2e40c820705c140020368451200c0c024080080c8004c0340658202111941902001c0c0141c0b4141c4005a006241d56510940111200c000140d61124959420403400c07409480b42d000074921030380540260030403e0904a0001c0c90804036502c40703000b591510040c0b0000400110884003103d030000c0c004038040d1101d0380720203c1d60420380c0c004009508002407180f40743e605500b200720108011000d076590a407204a0942e020082100c0040855800300006000543d80c0e0b030020201d41d0004e821280d40601020aa000c40e600 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 28744628 1250 28743378 28743397
    0x21302030118060819030e03030a1107050103050403051c060e070c1a060a06050f19020a0302060705091003021e04090b030f0f1504050c03030d020319050601020d2102 73
    0x2000001404441140c5070809494864030704100400c1c0d2400f0301160b254101d40081451000d8400500418144507151000904a0040541c0c3e928110410054012031013030401f94294025018005040e43c040d01c00c852041c7e8058442e60316151041c04030039002c41c000f445c07040c0c5c0300365510000301e44155254080d6100340c0032521000512216400c0c4020b038080c83c045140c03505040c0604110340c43e1910b15101d403c5072818104240c980d60f000d080b404a60140361201d01c0ca03420140484a800c0b81e0020700c003c54a8060707020b0741d205845d510811600340c8039a10740349400c0404030030150b48452080d401031001412003c0c103500541050440b0300711650240e805242000d80350520003d5928081c81081740040b6104000c094424001500303585406100034440080010040010207122051100e40d16000c001010b03281c3d07510040504030000c0d081910003110207023003000704c7c000d0492140b02c1c060050005800406007444a0781d411a0b8890b92075070020610803042c03000c0400e07042e650010b000e2504 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 28745878 1250 28744628 28744631
    0x605040b06191107080604061a030106140103020708041508011503050402010206061201090501050a0f1107020d030c021f03020d05010603050402030c10050c070306020c0c03120301051905031504030e0f03030d0c020a0213 96
    0x15609e4030100c0d01245c00c0790f01d00d1180c0d00d001c40410110125080a001900081c280541c0380d1070142403000e050f0044e80c2c045c140290340712a071081c01a80c00b807400c50680e11b149000301c6083d001d4a1301103003254802c6900a025a1042000c01c60b649449034010100300002800802c8182003640d074103003550000d0f203000c03080c10385a0780e0040e04208903001c0c1107110b1a50300410703414840580c0000d850305082003000303000d00c0900705503d000e54507480030a8008440c4a42c120011000e60320b00240203612050300811040d2a050004c50303514401e02030340b4002d45d0018020309030031080300c00308140808000d001c030090100400c090300644e1010320080300254003410300142c41380d624a60442c02c2c21268500c00d0f109802c0a00d04580d40c010900640b4150f500c15071301da0485010141e5118084001d54000e00e0381803203245a4000e002001d9013940d44034902c01e070781d0030114000320410b0050038101805207030360542080c0b01c2e03000502510380c00310b203c081042c811034140a08035008261150045078030003c506 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 28747128 1250 28745878 28745891
    0x230d0b01050f030d021005090102040806010b040f0e011d15031f05090304050d060209010216030f02030f1207080304020f0a081c02160e0a09020402030108010605040b0619110708060406 81
    0x1e1400541c42ea4080380d066001e04402c03501424001c0d00e41c8220200c1d40107084d5a11b02091020740d09605540c0541885002c4a00c42e58407000800500c1c2c100303124045102030840408259140300d201c0c0c06048580e10508410503213041805d12a60040040107034042e03020002c1040300d543e408000b200100001c202d850f0190340442d03080c80040c0c0c2c0005150b80354541c0200001c00054952400300024240c000e0710040c0c4501d16100105c0c00d060f0107006c0e00c0031b10304003100007009210b044401030791910710840442e01034415800ca03a58a500307004c90010241d103801d00400020400800045a016100810010011041e5400a044900329400090031a0712501c802c02a84014900c410380850041c00100384000b1526075501c000401c500401d614010144007194080125401c05501d542d40140159240d68403019140d00030302c1141b0806124904040c400c4001d0b040410882d03400d03482d081c10800d48071750700420030fa4250042141e42c80340d91040d408000b64503001800028041d43c46445c0101d05d0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 28748378 1250 28747128 28747139
    0x20a060c02030c03030304032106030605010f330c020a030203030a0206100e0423030c100b1503010f0e25050706140708150103020f0408060a060e040c230d0b01 70
    0x40806a03c0954040e500400900022940081d1000554900c0b210b8021046001c01d02c0078000d410135901c0105814200b90001c03a00b40e06040b40308040e960704502406c0b040c0c2c000301d90034503110719500540c044034400000c1c0c9070586118031b001700c07002c03400980305d07200315644d0b6401b03e451903001c4110200180c000c0d03000d0200d001c2804600f02d00403c000d0300041440e06041d15003101d1203280b21100030f0004101501102d01c40014026113841c10500002e4603e001d5011003000060700b64482114440e0300b40c0c041e90a200c15103901a64140c0c1c3c1e8007003020002e1800d1501d81e00d0a0003002d890b6800030341d170300c03c04030301c100703260b86000341d40700a0643c2d030075440300e40501d4904184c8070402c100301c0925400704108902d00303601140c001d601003888841031080c1c05038880142c000b8840c02806800c901c40000700810794440001c0c17142d0050241c84000c021090b51818041440207003564018510101d00d038003080b607094411603810300312840c0c0600e90140141800002d25503181220220303082c03c04078004004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 28749628 1250 28748378 28748383
    0x2e030c140f060403050d050306040912090e010f0b0913090503030103060b090106050306030a030c0c080a05070810020310060503040c0902030f0402010207060305090c0d1502070b10120b06100c020a060c0203 90
    0x1a0010b5900605150455403a941c0310a05040a24104076001c400651703a41e80725001188002d8102e4825201c10420600c003d00307070080b074040c0c982214500c0740005103aa0000f62004200d4108240543c1081200410092720f2030100407560b08054807a075042c0c010543c00d00045000398480c01c1c00003140d80c00c81040c801c09500580c082c0e01485011300412038603460205403103111980c145801c0384031441c54a05104d11461075006040c4510171a130b0070744104040052010291000c080c200c0b01c4141c0d40d5407800c000c0c0d100454044828030b0300030300e040100038010400f40d900184280f000c0c0903201d0316118410200d0300101d0f00b10003405240001d101c29542c05002282c0030340307107610b0144580d03d00540010740d00c041341d45074103001ea61510703a00f200f40310030508800440391842009550b90141400c04c121080c0066503a6400b6205041000550140c1600c1400e84c0075400040342201c0ea90b828100301581a0800c401001d0058040c1000d00503a501002413000e031000c0e8490303609a02c4540181031 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 28750878 1250 28749628 28749649
    0x501060819080c0708060718080604020102030f0c030c0102191707082d0a0603030801150801150e03070b0a12061a03190608010c0807082e030c14 64
    0x800e01c0e0030100c608249818000a40000c40d90042481903403000800c03140341c54014103510090041c01084140101d2942c844034042c59500c4c406115480c0644400340359031520703000d50303000f409a0303c01c020700300c0710300400409881d14130b20900c1a6405d0286400c40355003a644800c2c2824801c40d900e40e1070f4070400c0d400050442c0b0f010f07980201e0005d03500e070944c07000d08101400f50143c114008808501c11a51a410368813103c0401d0b00c0c050b03030b0560308050840b540503000320b000403004102101c00108040359259442c800b03501700c0342c0e107102e1541d1034550210040c0030054050410810a40f5040002d51401c114840050208007115640c60072a02d030010400c0ea101c1455241c0e5909140c1300b00b101a400c00c00650451100481090352500d41c4181282075112172180d0740122801c002d40003654100662002001c14075079119010207a84600e030444011500700c886114913410315100440040f107043c085580051410f01e070742000c60312511a6203400b05282d00005c0c41560301c8005001d241820442c88 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 28752128 1250 28750878 28750889
    0x7080415020309120c0309060f040e060d050a080315120607030e01060501020c0402090307030b0f0406060e040f03080601091a09030708031201031203020d09060b10020f0a030804080421050106 84
    0x45055080c5542401e0300d070040c1c8a4210316114001c00c015010505c2070086614481e00245240c0d61855480618001500544241d4138400041e400003807070383c2080151540c0d83c0d03a03c10b014280c50620782e61182c00f150030150184c81c050240500311285515010510031a03903901c4001000b851904140c01415285034080305c4030203904000c0308100c0e990300040c4002c84c5050498025032204660000300c0c0ca0658a98005042c002c0b40006101c8070005c0000740c00c0c080e6001301d5091084036120754601907115410b0394003c0c104403071f41c011745000c20701c500f10307594000394140b4160200300d6846912000300c0340c007184104410940002c000c00359140c10000703d4000c00c8044003860510240034981b0b803207600140310291040d40d91304130051110344641e045442000e5900c104000c9001981004401400d400101c6406500f440d140e1700d20780d5000050860741101c0360002052503824541d42150355480241c4100d4500b0420300c0301003116403e41f4030200380c0304504800c00317400c150241061420360781d159122 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 28753378 1250 28752128 28752131
    0xc020309040522021e0d0f03030c0c02010903060e0106030803100503060f04080403080a0e060a030e0c0901030203030306010c03030207020406060f09090203091504050a06050405010209040b0306010b041401090e07080415 96
    0x406030f000340c9450102400354048601c005007048096450042c80707001d210003039221550700181c40401000035055010b040c040d41c0d0800903d80c003805c00340c2c2c3e1501030f1240640071402e841005c00c0001c1281d00715424003c480740010503a5a070741e82d1820350075042510220303120688404180401e0804008861340010955a0b030b900301c2c02e094a0301d4135180700d1800064105007000442018640c0166203052204c20081c00d2035664095001d0000c0040102400f11310441c003c000c0c46015a107884002c0d40d040e00e400130043c5145803940ba0064907183d07401c1104506044e02441414056682c0c1c1c401c00c3c0003080b5070b8444103010f4820041c01070810b903560300103602052050040c0b2400900001c0e0b284404481040c20744016291030410714544100d00000405080c04e01c01000100f1406402034000100c0588080c01000742e81c008054541c00b00f4022030071044000c2c07000300295403c8064001c80d02e101810945405030b201c4459815481d0111040c0b408507000380b003444108614051804102890200d0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 28754628 1250 28753378 28753411
    0x812040311100506091807271a0312090109031a01030203010507020a1e0c08012306010905090a0c0e0315062d010e04020c010e0115091103040308100302040c0203090405 74
    0x1805045d0141621b1001544840f8880050f0360801c4048090203100d1703034103591494880c0c02c060b01501191041c80040742403001e000c1c042c03140c54200c8100204000e0140c50b6801005000340010b412a400f410b0420400201c00000f280c03c0c02d01030301d9400411559180990304500616080d034001401140856100ca2103100c04600035030b4600c1d86514030f0f0f00380740343c4038002800c000c043c40d40700b500303c40403d5203402405003403e6000c85c1e0b400510405080c113416103940e40030042d82c1d01c1d0030304c2c4030721a040245000092580f21b420f81c85207000d06c4141c00e040189080541c0804e140c1500c1d00482e0b42070140d40703070900c200d80c5407851007801c9040d10343d102c140d8600d2114400504145822024a06100b28080c0c04281e43d0368603016501003480301d07002006100c040c429014044c0001c0304141c0ca2410820801042c00c1101307014620510700d245914501c0c545641d0340450b00e0074801000e8611040201c00c01100680e1a4004c451800036150300840d00d0320710401c200001c840d07010303060880a000501 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 28755878 1250 28754628 28754641
    0xc04090503300a0b04060302130902040c020d050d0e10110703080f06060906030402030f1603140111041701090c06080f060904050705010f05040815010e07030b09040f08120403111005 80
    0x42c0100d034000c0d0003000c045600c0f86104081005800715800084d400300451015060701e80c03650b0711069240d40215000d00841d514003505a07101c02201d0b0030740d00091000c101d41003d40320b094000d007209080b80c3d0104c0700000d840d41405401c0301d0702007094103140740303001649406041c0c2c813194072500f104080424646500341500016500d02c150030f145801080003000140645d034050000c0c8400090107000c1e04d580400c0701d0011344c82d4511501003100c030100001400807441905108075000180b500341c0d1a4981410b1240c0380c006010300070f42d945800d648480140d00000c203e00342d500c00600250b207441d840760405408680b0044001080c1074004e80c035000401012410006602e001c40d0030a081030f510390300c8000030464040c8140d801c80d002d5846004414a4900d00c030b021094100c0396072503c480800d440c2c0b070100710203542c651100182d00c10004401300d00815003800801ca18184540f10061400303240703e0f054110340318210b9058000c603600101040d418482880030721000d00c3c4212040180c0d14080c1c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 28757128 1250 28755878 28755967
    0x10606090608070203070c0306050910020702090612070902120106030507020c0f10050d09080403050c0907140d021c20040602120c0a02030f0f1902031903020c04090503 74
    0xd228070401c1000340400720394041e000340704481c107190700800304003003c544034184000500410341c0c02e540503109809800707500860520030340e00c07900c1d07000340451341503110541048030320824609000803a001700761000810f60a2803000709406981c803c02c810556140c01005070480310000c00040130341d008404400d803240d0768601c00d02d10503002110343c03010907001a03004440d0b900401e4000009070345040b0158080c05400000740084034400c00c1101c503200103402c00d100c1d020350141c07064000b0580300c2010701409001100034141e10040a05c0040c244841c0101902100715001c1d90b0348119035a98400c5103144003001c071481c104100d084040f500d042d2401100959800741c0b0541c1c1c800411000c540100c020308203008204a0700d80040c2103460204d01007039450f80f15140301082a0303603845141651410004107103021070b0016001000307480c03000b0900c0c08400b003201071100c088085000c5c9859032409550340b07100e1040b506000b4801583c6442c1400805210b10540d81c44070104000000948425031001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 28758378 1250 28757128 28757147
    0xf0f06030703150b160611090603070c030c020904060c09091104090b0d02030a20101205060301060905090a050f030306030604081c060308090f04090b06010c030e130c11010606 77
    0x40c640080c0d00d50160540310b0f0111240d8200540032034002905400403c0d860301c84d40141c6018510410800001c0c003034212580c8100d030003030740d0442c00034000500c145020f00d0ba200c420a02a08111622800c151300041041c1d1048808990407a55640f40404e81680007917404003a10b00305108008440e07202a450754140900e11032803007840d4071449050794503100c5030030580080d580030f0212054007440d4600941200c203e404000e00440100b60f2003499803601e070424110000c0c964860403074000d109681c2c0c00250000622003a055903c1b40303000544805640304881c402c42411002c3c268110355464a02d060a500c0b274000c8100e5407080c01441860758001c140540c015a00a0a85541d10300c207481544060300007541030a2098544840041484403a000a06d04000300f2140c00e0350b90510401000b01301d501c0c0b2080501801000b20000d4215400f49810a0485000b801c1c641442c081c3e0400107224464005540020300d03403140c1101e0003281c1c00c20f1800d161082c2c0d680091200da42088001000d07001c4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 28759628 1250 28758378 28758391
    0x3012c07200712050c090a02040302010e0d060e070e181b060c0715080a06050102030309060c180406090f061208071709060a1706030109020109090b040e0f0a020f0f0603 74
    0x420803551031101c204000007002007180794440600e600282c1866030700c449035149000d02900c00400001c10b1410a4800c490540354141c5500d403200f007035a02481111140c5070b0f0b04030b4259031395510780300ba031400802480700100800400a6042e01d48204590910111903805260603403001d88540314000448241d8112040159055600c8400d200820740c41c0001c503a0100c00100324030400300c0c00c07190b81314007002e1081403a80d10034010709a0b18401241d41e444100c4900c1c0c09071304201702050342010461700404044103800c0da80012031885178001012680035520607080c1e02c2d035842c4c822201d000c0d58006c860081031510030148203600d4985a621092140e090002d00b081d8000c0304884140030014140c41c0c00c643c014002c035448170f0074034502900d00c0c0027900ca4003940400000c00208103190500a040c400e681c103a41d40c4000030b03e00800d80000d0080010b201c0e5200d07849101d05650035500b00030302c0200b200c4140042850b04024010701038262070b490b841d103004942e82030016106441d03010413240c0024 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 28760878 1250 28759628 28759667
    0x2041a0604030206030705070816051c0f3f050604061d0603030d06060203030414370501020307090e0601020a020f0111070803040902070605010b03060102070b0c0304050603012c07 79
    0x1035601c64126601d11807101c0040c0254404501c0c651641c2b1000100310361144a1400c881c1ca440500c0e40b84413001d0104440c0500180380e081555259600c140781000c2c000071020f01143c4c0030980d00329121482c044a128002181500105010340900315001d02a0408003c0d54200003135402d00580c1500350b580d0f0704c8a10303481072400780803443c1501c0410444107042c7c0c000900300003082d20340e0380094880c1d005a0b010342d4281030303518407000c541001256410700a601c051840c0100054294400d40392410010a11580d03280060308001154003030006501c2038070141c0e01c00080c00e0a28958941345880544007504543c004070315400162141075101010b0042401d11a109403041c0b079542d850103080e82c02c807880d140404140045c10010300e4018003011440b84e08140210782c0c035480c05a201d808112980b600503070014904012819511005044e000c040c002540d00c0e00b91106e003c1445030f4020307440304680e803154101916000649032289020701d103c249090450303042c0035400810301100c6403a41440d00c0e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 28762128 1250 28760878 28760881
    0x907170c0708040302100c02090f0a05061e010e1f050702190e07030b03010e07030308100501110c06220605070303050a1806110c01090507090c020d0c060f0e0f060402041a060403020603 81
    0x540211f1106400c0c1754000c0c54189e03a464500c0040c0c44411054035003402150030b140101d80b0302d00c0c106481c207011143c0344041c143c01104080044602c2a07420500e960003144040224000c04101418045203113120f4680c1030fa10801881480400c010320707400038000c162089030612180c00802030054204485260109554200500081c0141011821001107100d41c500001c200f503003200750075101e450341480801419075584010342da81107011a100344075412244a541c10b900d8060007900c03111741c044000302c224070146c291805900c1c0d860b0f0000703000302d140403418108255050040e50703802a400b00042c002c00c0385103184103d5074800f100c0002e012648034244000052401b00c25101d82244442c020311044006081581e242c880502810140904190200c9503550001030036040502199466000079101038a90200501400e90242c655a80b5000c81d80500001082641b010341c00c06005050241020f1041004403086c0200348000340b5414084082c4550307820091740d0880741c06403640b650341d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 28763378 1250 28762128 28762159
    0x150501080412140c010e0c04060f05010203040e100f0e1603140610030b191a0306031c0c0b010303050a020606030606030a0f0611190905010201020f040302010f0e0907170c0708040302 80
    0xf40d0048502581840d0320b4481080001c82c00080d14004514055400b0009503840b4140d1400201d00340c055203015a104100400144c1003031020950301101c800c0c0304d4040303a611000308841c28481c503880114003402e00b4092002c00841000340d0500c6d40c60504040182c0c03c1e070356440a1221100801980c0703c2c03100401190b074201d019030046100d22000030030007100b07044009000b409c845480e003d41c0011141c0580a03058886012080307a018100040082c4a0062401c43e07401c030a003084c244101c200007220034a980003c1c1d02a4156010314403903121203880b41900b01009207440b200508651003548444244070241c4c5000c18012103281d00006112100d190f24142040a81664407641c2c00b50b480003d4a0322461642c800d81d030f6004405070391081e000550340d1004a09034001d11f51440076491040104000540c0903060380446001181080c00703800c8052030000390740c1a4104d8030b05000c10100c100c0c1c42c6c20004418401d0b64011248000a4280311080e2240820341c0103902000780120303e490300305800e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 28764628 1250 28763378 28763417
    0x2030406081003021008060117100602010b15070206030a02040306060e041e080d0c020c030f010b180c090409060b130507030e19120507080a030929070f0c0b0a150501080412 76
    0x1001e200f09c0301da154250802e0300d085501c0c21000e100701401540303400b405691501c0c1504000c0c41064414403a60b0412546800300b05090340302401901840c0c0d401c1000000241c22070107070780001e04880c864220145080e08100e030207030320b011540c80d070310460040e184000907500c08140e4200344404100050401d04c1d107041a450064842d01e0b040c1d05110b41010480404815040a40004d405a5106851501c08156a9170704032090b04c40c030398140790520030a00141851360090881c2400f8038404144001c0a20108014498051100041d26281c404000c9510303094007500081d000c980008048114801004112002d0391110080c0054205401580304620500c180d40d14141c01240d040e6440d510310001400409021400700d840306420011000c12218045d40c3c0200824055074001044d40c44a8003152110b04140044050182c3c40c000d2101041c0546001d41c412801303060009070400030550b01382d503048400d0380b0183c10032400c0e20801c0001008880044044419400c0134445440351005050 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 28765878 1250 28764628 28764647
    0xd1e020c030106120302150c0304020d0c03020402070b06030708030f120907081002070b0601050a0516031b060501050f060316030908040b0a030f050108031306050304020f0303030106020304060810030210080601 92
    0x360326600f44040414a9000300b02d0b400c00041c401c0d021116907459020641c6071100c021601c1e00c00c075490600014000d4285035140e0070700c00344140504003890ba100e6000400300d0300000401e54600401904100d000d0504001e00006040a08000c60405488560014003032042e10114012407940d14003144080360f0403c1700790084c2044a0588051400d884802e02c0250008102981d40d94a0800072034400d5024000321074043c1c1e25656032601d80124004181072881c4050740032803c0010308801d09080e4241d03020020b00c101d01c250340210316949003400704030f40c44c01120040c41c0b0814040091088060341c0c8006041e0a80701d074200424030010900b01007002d40150780c803021240400090002e5416419404064282042c0008100c41e90302d4241c680c1e1789020783d007100c070400c50115105020341d60180c1c01070350344070340300529904241000b003001c64210342080c0c0c0001e0141c1c0c4049810b0004941120502e5070000e0020900700010f4a1a00015050700e400c580000c280949400811102c1c1d1145210300e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 28767128 1250 28765878 28765903
    0xb060708040315050106030513020904140304260102041223010906051812180a08030408070503070e04080306090703020d05150111120d0b010c0c030b180d1e02 70
    0x40e5121552403c200750040e0110004280c10380c82c00c0000304a03c2d029100b4940103007007042218881c0f114550038410240005002506c12030010700d44804003107010801071010708203503184c401a6288680d03807070500700d20700088152242d006000601070302c0c0780344180c185c45e0390b040b2040d07550f50103070445410170204603141128125401c1045c601e05000903600700300e0040ba071109001d41030030181d9070311a48681c43c01e884420030441c10031096101e070036001c40c890010000281a2400a992541c3c52441c0d40c0c0a42d02c016896005000208010729080c0254402021282420010391815a075840714a100080c12503203d41110350208407803134400c1c1c0c15240f0900c000e4500b084142401040c5424079003030b102c415400690480c0d0000a404c10100e44031001100001c5418140064003028401a0160030640e50401c036001d401c020100e40b18103c800000d5000d401911700c00d050104075400d250038511003200f0954051060603d450b980071495901075043c0c41e2441030080280f0504a00b80500c040e00b4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 28768378 1250 28767128 28767143
    0x30f0a050a1806030615020303090a02120c0a080708060f041109040f080705010f2405041109030703080408010b010e01080708100b1201080607030903080412030219020318041e0b0607 80
    0x80f4015406034880340039140e81aa00304600c041c4141e08994030702c421103010170260050b07142c0381c0042c1000039000350900d02c400103a40803c82040c0100e801400a90710041607940802c2e4104102001840841c5e0883c03500c0110072000c1c0341907261129038040501d8001e00400190b00060301b401100c01001c0e42d1740360300c0b03480d0710f644c0c0e0843e040c80c0f4061f00400c848124045e14104a003c1c00d1f440445502d59241d0025085600c064903000c1008018440022448244072040021001f90b035000d10111010f14401c0c80c400d80c4071400c20000c01d007110184106030b414483d80d03442003203090f81c100d286541e021000d40740000740350f681d2440104c40e8036050752103070f0002000400d044d900001741c403458505803207000c821989141d8030460110305440d100305020303000c58050f8001c2000b180c00c2c0045120300c0d516034200546400c425080a0b0300005c030010505006030408502000f0060410142c440401c0c3c08603428051070301d0702d0001e01091184032100d00003459850103840c7c3c26031101029200d54682140c803 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 28769628 1250 28768378 28768427
    0xb0304060903090602030921030405210c010e130c0309050d02010b040f02090907050a0201021903060602060907080303011707030b013807080904200c010608030f0a050a 74
    0x40c010068200c140c41180412804500410340c2840042a143c2d41030004001e2400402d1201c00c5e035012148130f0100c8a82c03400208000705168849045442d1141e80e0161500e0b40e03040e00c2100c0c03600b8020329071804e9040182e001d084070f4860f614070b000c2c107051880501c1d00146180b080700c07041e0009d2079600340007002070081c0802e40880c10b03019484040c0100b0281d402340a41101d114110049116140841343d002d200007003c54600c0d4400c0025000191640c0001031820b0080400050328082403801040060740302c0c881408003e90500602d500503916030700810515062420107502c0f80414040c91240c1a19014401007490b42005940000c50304059000502d50710395903c041071900141c2e0701071545110920641440b001400d040d81c0f01c890200107182030100e40da45402d019402560903d903c1500c0703803c504005034012249206c50070420780115614030001d0b18441c21744005510260854006001c0351403400c0d412000c80d00d40d00460300d000c1e03544080d0b00038180d49040441440302c0b45480e800c1c5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 28770878 1250 28769628 28769633
    0x1309061706010801090221160f0f14100503060102160305030702130519110412060507020613030c0803040f020301020a0f03050703020901020a0f080f0f0403020301060b0f0d0509100903080a05010603050c03130c0b0304 95
    0x724100c203a8030a9082c1c00718ac1134440c00a0225501452805a00002c81c0401d05010520820140d034002c901441592854210010030745404140c94000f981e544e040020b20b0f004520342810700f10007010384a0014445442e100b250118260f00b92040f0030144c0391500c101d580d000441d8000c0714054880740c180d204141c4110b092550003002e080394680c1c050302c00c0f035000c2800d4588e40c6a240c501c0070361507503c210041c4600e5070b50b8107023608003900898401100d6001040140c4d000e00140118502641e18890b03e4004234100800390742e0080c100d8000d2510402c120291a68081002140c581d000240e83c6248031180ca85201d035442001484240303100b000c60814a094030010044c82205d000b20000d00a03540c413500481c0e0b81e442503031400b081c07514081048403d94026900000d901c09025401d44400c40b009966001c19541901000c81c00101c001c07040001e03c011078440d0b45c0c0505101d2604101c280303010b10300300f603c0e840050100003850041b0b10403c420445400302403130240101c692443d03107034240361 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 28772128 1250 28770878 28770899
    0x4050607062004032103020d0204120606230103020304080903030a0f090506031e040302070302040c0306030204110421050f07060e1201140a02130906170601080109022116 75
    0x31061030032544441d00401c2d00100d07420080d142940e4002030924020400c0c1100201410754103081c0c1d02c24036409002c22039800101d0b1001d00010404004c42d92140202d81c0352100440d0301c0c540050055184c0c164070803080070203045003561103a00a081c01a0b40340c0722810103100c54001c8020f070384d600d88000591744403040e40c0404015600c0d400c03602d5070b003405602c410070015039000c11281e0704841c6508026240200b9185002250024021700541d204180c5913000714055644628080d80170079100c001c20030450409219022024041c50441824542440002903540309101000d100902c410005002402400e1005910b031801540071121400d5903130301c001c1e1603070b00080c82180c4a03454040c066140c150301070050302d00a0a20348004207883d0340e1590b5120003500082088098010300c404081a201d58600c41c08010b40252014100b5454480c1c0c1c1c201d01d0880141c025100c2030b4180068500183c6500000a440411106450040c2c240355490b603440c0840004a070489402c42000010380e00d0f00c1d4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 28773378 1250 28772128 28772141
    0x7060c0f020604170f0303040201020c01030c12060e16030603080405060f0f030702100c05030f0103021201110d02071407081209061215090108070b07200d0606080c151e0405060706 79
    0x90300250307503a4918160945c2d40303902048a0290150704010b0ba11300d030940c400d03840302106401e103080040304104010107010881c3c800350044c0b000c100c000028000c030003480d1054101c2040c1240f4040c0416030469035540d146001710311400703000300008504014035107000b4041d40c90030b64940d000140c43c0d2514840081da1030688507140c1c452985001d81a50a40340f0600440c0d11070000c900106040d43d10b2359082c840d804445003140801135507500740d4a0320588200b0001d03c9a00c1c14007401503101c07405030504907407003052030090725482e5000c1c410402c00c2602c0818040c200e401a030000343d03110504840891034500c604206400054016810018200d442e12441081404103588051a9a0b00c070308016550302c580d4012903141c04018840702c400695221403071550f4010009030309240c80755080c040f46d14140411411a010754850205008c0f0840400c80241600d40445d52031401c100b00c0d4640d41081c1c4601804800070a00f0f2141c21340307000f0b00800490303005040c0500540d5403810700c0d0600f00024181c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 28774628 1250 28773378 28773419
    0x20103050105120618010213060201051501020105040519060213081005160c02040504050c0904080d0f0b06090d060905100207020306010f03020108060607060b0603010e18010e07060c0f020604 84
    0x280c140003142c0d90402c8a070000c40c1c03442081c002d20564070b884151000201041d205600d141d902005040e00b100c11404d00c0c0002000d00c0d0300003150b5400c0c000074072102d10f642e41d407043e41107a15140411002c038030000349100341119180404c40415040c0d04188010b0300ca858218511035042030800038901c0d4000070459000c1100040822250319211014140c4c15803895254000400f01c00c2c040300541b6165004640081c82541104e110700007000205080304021282507030b00d2400840d909403c990b89005020440c0c07000001002610459400541540038203501c01f03000d210880c0d807140801009900074040309801008441c40c1f2500d48a024010b9401580224040e028180c00029481411003018094030b41c144c540f982256510b005204081c5c0000b0019110130782c0310412140c240c0c46000066000c0c0105024140d543c0c50142d00111a5041c00910180168901076614079510004038104017550303201c1c9020944d9940c0760400c81c0003d100310700d010303501c4a00024005003682c400b0804150955 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 28775878 1250 28774628 28774631
    0xc03030403091502120301060e01090306150501111c05071a0f07090f08060609130b09030304060b0f010e040f0608030f0901020d050a0c020d140d03050601030b0d08040911040b0c0a020103 82
    0x24410310f0200e0325082d41581400400a0510040c02010b016200b100000c04043c900780c07080660340e894201c25500c3c00c282525507010f0391403050046503071006601e000845038500401664002811502c01052601c065004000000c41e45100308a40310740c2c8883c081030705400810b0142810b0b204264601015100c0d000812010341000031042e903082d40c0c0c8021284803030f01901882e0399080901c00301c213400034815a8030484d0f19000500041d2014001405000484e00644c0c0702d1a05140034012030b020701540318801c0201d800c4c110050703070f44241d1411400200303843c081035034880c1c080d843c1c0140c06507420007406800040303500107582c0003101c060022040309a088502043c0319107002c1c0c44610034440c1e040c00090103005503501608080100c7d41c052032044131000040101c00b00c000b8101b04502415100103a125020b1007465a414080e60450700700440c0c0c80041c11009a807440c0481c410b41c450011496180d13015085441081800d50f00200b590242d1180d40b005070300403840d1500b0645004a0100703 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 28776984 1106 28775878 28775909
    0x9040302030f0a0203120a1803030b040b0a0b0702041a090406110403060606030504060b06040b07030815100917160303050309120c0106091d0a0b04080c0303040309 72
    0x10300c03141d800f654031040c05986d00300e440d0402900c00d01d04142008c0110b000e11100500040d0f1070746d4541000562203d503040401c000e0294000803070391002440b000011888000c400919202d44226020451075400f88101d030010b1159201c20341c1c114506000140006406a1100008028084c142e505140d62643c8060a8503007076082500004d44400a210401c2a60300600e69410000c40f0103c1c10603082c03401d40b040c42d01072008003a0070454004081907503114840b00307074000c0030700140162030209030805020742689014424030007000c0c001c92604024480102d41da8400c0d106120724160110700e5910100c407d0b0300302601c1c082d503a00079860403030209000f07900200804c9050b48004503409181c1740345102140c1d850f4440704100c60005030402041840440c201c182c40e5401030310891103490358201004c05010f03403100007001e44000014042450b8014407004100e03048800f112268 = true := by decide +kernel

theorem cover : BRFrame.Cov 28597128 28776984 := by
  have h0 := BRFrame.cov_init 28597128
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28597128 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 28597128 ≤ n) (h2 : n < 28776984) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
