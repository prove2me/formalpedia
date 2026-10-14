-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3727
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:30:22.42976+00:00
-- url     : https://prove2.me/submissions/59ccba5c-2f64-4ce3-b107-c2ab830c52e8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 670143884 ≤ n < 670323741 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 670145134 1250 670143884 670143911
    0x2070f030f0213020d290301060b040b0f091003140f040804030b0703090209070305220c090e0703060e030717030f0c0306060702090a091a070503132108151210050a 72
    0x1009221b4040000200710038004005202c910509041e141c11002401032030720b0800400c00324000c40c01803050b51400029050000103491044032030311500078049496010f00600e02030018000c0c084101c164200c0075001030740a501080320b20b4426a4040c034a541040d0440c1c880000f400c80092002c010b160b6509141405640d50402d0148204502e90300403545240c8100d01512304042c1140303104061808070b581800185408050380b054581d0442c0c0051004c86050f403540c0f8003000c40d800135001c903281500e508161003010005142d52130007921400341044d044a022107040c031084900084414035031000c01d055564000055400850040025080c00f805400003058031006940301800c1a80d10940d8400b0400c482000f0300c50b4030b9013485040e6031850402c1000e006840000e000209103001008541c2c01c0101c01110440010070012038030b0143d00e4811000340c100301065460000f002e2002c00034100074030b4071504085105001d000a40a01c510308a19003020302005011810507079180d0b040248e0b00b5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 670146384 1250 670145134 670145141
    0x6010608450618070f0b09241b120702010c060906060f0b090301061403071413050103061a0301020a140f190914010816080a1506090602070f030f0213020d 68
    0x1144000f0203030844500c2007407500c0c9440060380c401e0481c44c5061604004050a40e000ea4071580e00603614051450b814004d24084070b000000d9150740d100380444c1c9416005007220840081050f00e8080702c1000070284a03041850140200090018842d40703242000a2201e8104000c071030710600c0040744160701d5140160303241e00d140e040111802404120041c143c6824010400182192201081000c0300940441e884070200c1c0903003080c044065200e103026403100241d10182040c006810852540c50b0301c0e0200c05040060351422942952080b07590003840c042c0300f1102402180e45071074041348260a003140c02034105d400c02c0e80404800b40031010042d17100300c0f034040d0401c60b81d68447c2170329801d00240304080301e03180515034104100d9004000c592103180000d42c113440d01c0c5040144040d84e40e2018003024000011017500390580c0d52000241c52500140e001050f43e580741c00351140300392280079034842c0c000648030282404003884a19005824170850168140030350040141c030344210f050340c0e241603 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 670147634 1250 670146384 670146391
    0x3151f23060a0315152a0f080f0f030708090c0901090e0a0204020c06061905060a0c2102010c0f1106011202010c0b0f01030201110c01090311040b0909060106084506 72
    0x406004e9490409610020070400d4284030354035403d80740c0d84000c54030b148466002000340800307044032000c000d00c207220054031a40c0c10f614000c180e891001e40280ac41541041d2041400306d80c00c071001c501c10900100344040c800201a03c04038285e840d100c0c544010b003034420035400250040d0740020700035031100c1c002044070354807400c000e00b1103050400510400098401440102c07a1001400784101d5441070226031081c3c019152503004001d5500713212140c1c945600c0d1271005010105405070300705d030701900301c07580c12505600c0708141c0055845080d540c08000d0b90300000f4a8002c000184085245440c000500d00d0041c034081c00d0705510355403039002d244000d0382c1c41d090100d58000100115a03028480700e0b0b0ba04540b50190204088620019085d0000350000a2808602d004018510b84803540901000703000102041201e00f08060346035203c2000303004260004030018000b035001160707014a40641c120b8070703c070800505000c000140d080c2c1e409012075000015020f040309021038003045850701 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 670148884 1250 670147634 670147649
    0x30b0906011406030112060b060d0f0b040b0d080d0c0908070b0d05010f0e0a05150301141e100608040f170d141303050903151f23060a0315 61
    0x9a550610340200a1030b02d0050711544510001c0005009540030a160403004681c02403001c21a8404000002d100e07004020310b022227940303000c080fa01d0100381074005010a48080d0350802c035800700101400300c401d01046010740f2102c010840741070000700c140d0103208070407d84d10b028800c2d1a1a418030601300109548280c1501c40c0102c0c0720340b62851a03124850042400303c0b4403540725032418156002845004018411441c0c1d22400102084015401840c0803400100200050484c80b401c0a8004100341d03042c1e41e600101c0e001f040641e00040300c005000752041c0c035020101c40d1a2540440b07004100401c1154901c507666a1000002ca03500b50003402030340480314032900c4070040c40b0f02000b1101c42c08115000e82070361074180045240d560501b00f6015406182040d903510301d02011030307e0082d030851a00c03105240f80d4100483d0407040252070b130700d48400f070540440d0642c1d80c7d0584d10b0105072000c0c0d41d800f036486040346a4102d141200091600000034180840c041c0303510040564a980ca6510181 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 670150134 1250 670148884 670148893
    0xb130510051c0f20242209020c07120506180a02091311010906140c03120702010212010f080303010b18041410082109061210030204231f030b09 63
    0x1607802048100880e03800c40d00340c41c201807903280086242080990601020000c11002880030081b0641d0b001d19010b16040e60b090006141e41c0b40c40c0d0100940c40403202000c207000301c100110300c0001810f80010625005001000c96840b9a1045642c8402204050302c240c82002040001a201d02888500c2540030310924111001103050505208001d4015241044011001800140d0700300041c0d110001041461680390191036081d03501d54031030400c0107640310b244a4104690598150010b04400c03411620b00006641e8403561280211302e980150043d9400074070051104d00310110151881c584c0d07072400041d5070301d414000724017102e0000090f05a2101c40908000003074a0039070384980100b144200411800d40a1000c01c07400032540030002040d00c800040c1600a69545030a40b080e100d00006151001e0030181d4400d044864107100403802603090001042680d040e03503640140c80c451943d03c040b1255a040c1d90103a0700500340b400f03040300f01110b0b1008000300d030403141ca5505c80c115000091 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 670151384 1250 670150134 670150163
    0xe100305061c0f0605070f090303030507090306150906080706020304150909050a0603030323040f02060f0c1612110103090501110c030d0f110d020a051c0b130510051c0f 74
    0x4c010f6410090402c828040e8845640c61070030b034400003038001c90307400d842d000546489010301101c1084503580054a018201403c5484203401064843d0494000a00800203c0e03590b800140e1610181e101e800c015820501c4100210806040102e102d14118580347c081c06445841c2d9030116081034401ca958240c0d43c44040c0100754261150121447e402d9405040310701140d020390b00a41401030000708103c0040509034115140c0c001500e200464421400d0b0322891440e1b0b44551f5080c242c026114851002c4000142d07a000e82050840101d4001c03401000144030207006401a04420504642c00e41d81c815180b10b030461a40054940d9801113405903540b12201005501030b0b4544101d498005480c2042210321503070450111400004013880150300c0e1000d00c0000e60b168050040000c08402c0c56140b5000e25040c1f5a010311003c040c1100c2410034050401209021140115030240040072440303010b101c0391514002510358100720b5050381c89400d00964800c280701020b110100e50745141903107507 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 670152634 1250 670151384 670151393
    0x20705060406200a1101020d0612110105030f070809100e0703031e0f0f030e013b0d0c1712040c090203090307020d0311070f150e100305061c0f 63
    0x381c3d140d400e550426410900d401010040c800d200e000c400741c00f441111200390b50844029015503070110945601041156078804600302940103284084800a0320300b0020f10107503006e0802d50340138001c01c008d0409283e0300c5d0407090780c0614014002c180c19100360309500c402100c00b8041c50886900c130700c0c003a0141a15602c0c024000c500c0e1191040d0410001c1074040754070a0740041007004000700c41c5800c04610b0300f070350800c2d8020322020810810035400d241d41809240340060040e5403c9900c900300ba00440c580b40f4117948030101a0b030a80c411a00700d031320414156442440d06501d9503006800004411a5880380031440b039111640100e02500c03417204100c07d005086099000400c10800e0951562804400c01030722440b40341e9000f0700c6480704900300c0e428540304c0d0312086150b121120403a90903640314880c0002054071072081e01802c2100c00c1410311414842c21005216440151034842c8a14a5080036400307410004c00207034001c400704001d841000c40c5114000e0203140500c022041484030b5040 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 670153884 1250 670152634 670152641
    0x50607030e160e15130608070509060d0302060402010f02070f0e10050913030332040b130305030f0912030103030e09010b0304031b0c0b0d0b03060f0c0f030703090204020705060406 79
    0x6001c9240601c4408001030b0074030050a50313110600b0814014500d02c4600001d40115085a24041e00752800e8030201d40c0317400000307040044c4d80089a100030307550341e240200b042419620800030010b07000803000ca0010f501560245d0801c171b1189c0181d41e421500d58140e40d442d400385030300c61102d20000c1c0080c04131348508411101d020306025264004149030500e000510300b984e4400040405568110b80202030f40340c0c808a90080c011003c00340e46003d00717440f00510f941c030140d500703881010389a0041844000ac02420b41481a4141c039610704580d140d900303000c0c0c0114001d002e00c289010380b44900d0310250790400154080c0d8441c2d162112310601010600c883c9050503000500c2c403980400610001c245c000c80c40d4544000940c14880ca05c5004c1c0c80c0200d48920a64420104107002080c5610b101c0816000962082e078240c00315900b40d40e455250807c080800d941e02d403000d26007044a86105004100199441019814040703904c044660104040740d1202c4026507442e0801d4051004000300c0b800b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 670155134 1250 670153884 670153903
    0xd09051501050301060b0a0507020f220e0105060a030803060d0c030c06170c07060b0a18020405120d080601080405010e1009260a030b0f0a090c0f0f020622050607030e 73
    0x28005c1045908026110340036101345400030007071000c08510781d0210364540c9000c08107490082c1c101450644040d05004107811200c0c1d4021296080140942d07002205100d128407820005000400991841e182d8140c6503001800c1240c002400740c2941c0042000442000000d62182c400c0384005883c01d600140010342070b10740c08984510240a00c0b24003000d0b04203607004180c0003100060303040358010020700044290b42c00303180c0011403901c01810009040c0d0240088034425078452050720182a00746031200e10051145020444050100b0701d15481001c0440e4042d20900002070010203174070030390746410381659940030f0b039580b600c600504010142e003403c01814040c500745031040c01b80510400c12401514000e40030903a41d04418001350342c079081ca10100c2c03200604064982e98070781400c9405030980658030004a0310b20490036810740cbc412035010340d005003c0d5001d0001074955211002c840d402c0c40e80440480c155012840f03001c140d0030700c0010301496040d200006c8500d042ca00d800c1c01c0400300c2 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 670156384 1250 670155134 670155139
    0x50d0809030a3501080106060905031f0905070e0f0a0c0c0b06010305070306090207200a0b03040807140d0f090b04030525120303050703050606040302180405030d0905150105 76
    0x5200c0c15140c00c3e00900d80080f20f202a000c803a01d02290b41c1c8101000d00d031803540660f082c0440500020311a04198000f4041d40c40310b903a0100308035101c400b8965a03100c1441c50054412086099903c559010b60101d038486108400360f8641d1035403460310511421b0305542500c1d0030751030b140074070420003540d1281004024440c28180b80d8102e060321007100e0203000900140c140345e21140060b5095120f51301c03682c054000480215100c002c1410901c3d500321552511039900c4180d04036800051503c9500481196980a82d00b480c1d0760f1241d443d0b12660300a081c2c100c6850320741c2c1d400c41d80149414409441c05c2001a40c601800d07140001d0b00070016a2943c1c04151040c0c000c10061001c60004101c800d0007041d01c6110540c40c181542e07264034075155583c0141e0f60403080801103030070113074540c01c1180541802d54092040e0b445960400459110300c1c0300003903100080f564158280342c0010021a8450300801c2501d00340441078040c00f00340d0b1034040c03045450350850480c3c49002040180440d014201c00d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 670157634 1250 670156384 670156387
    0x10051e04091b0c061d0703150f0209030a0f0501020403230105060a06050d0b1f050c1c1706010210020c0f011107030905012003071101030f110a051303050a050d080903 73
    0x6006000e820a000e03040041c0404e500c1d540480700c81c0d4142015488401038400031070358041d0b92401d00361440d0007403103c150021414021400403008882c0240d030340d0508000d0140403d6405640c03106100c919544044825540a2200001003480043d54051303030000441c906e0854500e0008803421103c0050115103c2d0b841d9a4042c0301144d0b02c03000b81c5126113500d81000500240c00c3e000500d030040b14403055103541000f10181c40a81d54807001400030009024102d4a483c10b82c09141c1c040015100d41400c001202c61141c800d50317900006c0001e03004101030040d606800d00f090200030603070b07004c080c284000e80e0101840808480c000d12490011180c041155814005130740c0d0004c19804542c882c4604100702c030b44c0140c0b03040c03500328400001c440015007200e55400f0240342038030031281d00441080c082491714111540c20720090151b00c11415101000500d00100f142050360786800140c51000d600f0540e13840800014010403038902c0140c0a400100030200706454000c208020081c10341806410 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 670158884 1250 670157634 670157681
    0x1061107081608150c090d02040905031b06150105120c222c0c07020a081c0f05030613050702010b0a03080306090106180e0402040f180203120403030e10051e0409 71
    0x1171800d4500068003100d207141d43c4c1c103a0b4000030f00584030081c405030a1b404005202e0b03900450781403800ea41240d0000984000b0303603810103524001c01e8801425408644100144140c9154040801394440002060b00341451440d001d100c0d20102c9900d8020b0785000c2135181400340740005011090b20040074404800010150120054481c40240200e80e6040010406204558030101d05402602d0441f080794451030941083c181461800242c12011404540709d185d1114495001c8034032444014002c0b80050300449180d000070304000700010215517890090030510741d0b4011030100214019501c0503102d040200403c0404403040c0d003c401841040341301040e240d00c084a18100300e640004000080796524000314003e1310036002681501841c0c00940ca80910f65070241c1c0340081d000350102e45180700f103801081283e12503070001501040c0407028031a014504100040394409480c80c1503400c2c25900d00142055454406a040700d00c2000714042c80701da4114441c200e0202300e000140e250302807 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 670160134 1250 670158884 670158901
    0x5100501090b0a050921061302101d0f0103110c0319030501032303041d0912031509060a03171801030207120c14190302010e0f060106110708160815 65
    0xc0740380486401010f400c0c0030003413440480e007946c15003111080709990441c9070108061020741900c6100300d1144405000d0340e0403151040d6a200c0e070000c0c0300d903400310380a241407003008014003d03460040c2c10580c44a070030624040c51b80d80589099007600008581f6108184a00d91041c801d00c6c030420101440c0800410100d451007281e04096001c0181782c090751000950110304502c030306d400c1340703001e20880c3c245441c0c2d110281c0c007124072800c01d00007a070306440124168801248001d84000103001c11500414440d0300d00013540c550080c07401880c420210340d81342d4442c0300d136141c00c51041303c080c0303804030b00e42107110303015543d242d60f0000074602180b40002c542d55103e1600140e412050420400b15400320400c00042d000080e01c0c3c1402c0110b503d184c0c0b0303000a09c08600284c2d0400c170015401c0c4451200c0e034020000d114200d5a44090161030544c0c01c1800450f40100244200405403241e11b200260000081c4114040c15981080f020034150510059900e8146030307000d80060400400c040280c800f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 670161384 1250 670160134 670160137
    0x60a0603020c0a23070e0c1b070807060f0206060103052401021e01050106021c200a2f010908030a03051f03030305070807020f0d030e030d02040b210108070614070605100501090b0a05 80
    0x405050045596216448235404d15040c1c5a4002123820f108180003c150039400c102500e200859540c22503940743e0b41d280c0114265101601c20442c520340c2810400c0160b401055901503401042c41220100780c102210040d00039882401d0204c50f95640300144205c031307414010402c02c0014102c9900d101000003200034944515641644061140c030410b60b0201c41050100c89d02d100d820030216001c1503100321448151108121960902c1c02041d0600640355001d40d01c41401c640155002d5030a1124440f420f03805010300800034141190041c0000b034002800c00343c02006036009139400903180c600b122000d804004042c191209661203051700803403042c0002032980b22f03000386180216804111026031807239401040c80d80c1880a001042c045008120074029080f080101081e0fa82d12007001909654500310a001b81404d607002050140325203401844034800d00d60b80c000115180114580340e0038122041036524801c0306a032400200a0740da80015990302424082c0340325481c0400d0500b001c0c1c043d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 670162634 1250 670161384 670161397
    0x11030103140f0a0620030412020d030605061c0204030b01150201050703140a0e030c03040e06090601110d0302030619060f030c02190f061401240206060a0603020c0a23070e0c 76
    0x400c0e254080c5c010151003000d86101c000b80084030580c2c5a00302850300010380b08202c03091100500c1000000342c0c000344a07000740421200058a52840c0c01c80b240c60580b03480707102c88003404045800700000000100f041c41903900030414480941075910051400a00303496028101d081050305120340702c00c3e0700d002428134a411082c000c0002940070000c3c01d403e0b0031801810301e11034940c0404580021101d401040151007148101c61980703d5030394a500648603007000f004990f078030354010500310466500950045130840b40080003c0346203100100d40000c2d550003600700d90b0001d2849054030303542d19054050310310314090303500140c5503c42082105840d806404800078240b68003c2d058882030080d239234401780050b4242d2014141640c2c42d410800c0101042c3c040032200c040d0889038a0240300d1011801d039020f52070042220110b245800d034120069040b69408140da40505401c2d20005281c010710a0200303008114041c081c8103c848034281401c18a601c00f1250541940400a16141c9441110314 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 670163884 1250 670162634 670162643
    0x303080105090a0905240f040f0b0a0e010207030e01030b0405060f060d1b090810020a020607030207031803050624060a0c0302160806190b030604060b060d11030103140f0a 75
    0x4942d507058000000d8980c00401914034003030782c0d4604c51b041c0f08412070300b0204003c1541d4840380b170f1140618140040f804550150007200c1e0780001c6000a102c180b0842d42201d807803007000c01c0481a05e0203850032603214410850200b80001d008070701950f01030098641e00c0404650402640c070b0104081442000d030800c20354418031001039014001103240e131200246901202a40101d00d9660070080d10004003030148201c10f01c507160032403140c2c41041c0200c4101500950103841540c5030800103402079005564101c00703110b4081c1115070204040e003240002140210020600c5040c04034200d03690495034115030b2800d0140c036900030200c3e1140002c0311458201441c002070200d0407401c080742403030030030b501c01001e030141b8550000d8101c0c4c0000b0145e0144a404000005800d441e8403802d045460038442e003605608120f001070041041540840000345014040500d0b108180c0200402c03a1103104000d840c0300030220052040c40078130940c1405603641c0d00000c000105544200c0303603458a00040041 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 670165134 1250 670163884 670163899
    0xb010c030c02090903070f0b042117150d050601150201020403050c0f060903060f0a0f060302030a0b1f2409030822030f1101021b01051c0e0f070306060b040303080105 73
    0x100300341c07805c00490f80e0958114403c8405000d030340c6480100c034102070702e00740d80c0050742c0a52030058840c40310850200c0c01d09525100e003400c00d003207140c1c41a00802080c0180c2c1041d61072010b40f164840918080440b031242c00a000c0960504e072000490740d400401140442e88107010500020b4400600c800380c00f201160310b104900000d030000340003480781c003030040e41501880d81404401c0c29884410303802948030903814000520100c104001300c0d22144006903250744200030120200340c030300c101241c02c07010704410031070a4413406540040000882d423180700d54448035081c80100d41d004440340c00b44980503140091050340345840c1c01c691409004019210003041148460707152030041c00302c000a40c0c1c41076100800c10394904044149401c420101d070301600880c0c10b031800c2c070705110f6194009580140c40c2c003800c0c0b45e840008400198a21074407551000d0362000402d412080402042020040301002044500e0542ca0020156145a4015105220180002c1c00040d4001c0d1301141559015902390 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 670166384 1250 670165134 670165141
    0x20306120c1012020403120203180105130909030e031e060c040e1807080a080406030f050c18030c0a150f030c0801030305180907120b01050702060919080f0102030a0b010c030c0209 79
    0x43d00244590b070300c014010345440c2c0c07242410070f401102800702a5001102001180f50328001907501e4400d603002202c0038404182d0510500059520407004a4002e1074565502c40ca01d1010038600b000c108800103006640d9590581c100500700a4030341c3c80408106050704080c41e0004070f603000080034102907241144230045a074041810440d140017024400200caa443e01c0394280034045601500030b03400003a082140880c40020207002e03242c01040417002c840d01d0020071403100125410040706155141c05500d103003580e6030342e40d54016000744c04680e0f1140b03140c003011540507045414000c001ca082c141000c024481c2e070780e04802103604498240c140307503030744441c80582000c9011202c204d89622100c5070f4244071199910510b60056061280310030045030b1100001518280500b80e0000d51000c1e00b00b04081c0340b420400405041c071074510140c2c404280d00c4021803410821042d01007075440e940401008403030013041c02100a5203d080c20919808030140c1c030010450700c80c40c080603024a0011020 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 670167634 1250 670166384 670166417
    0x6030f010b0f0904080d110306040501050f1305070c050102030421080f0c13170f0c0a050a0311061207050d06090c0206070f050f041e080606061605070e0406020306120c10 75
    0x102c6c0c0525000282c00c001c00c0c0b02c2104a114990800e8401601941c079100c00821141020503001044000042054404032000d44401c03024000040c0b00c482017000b800c0c1d00d240000d0f000d001540c0100d03c00c00c25604903040740d040006200d40525011030810404400303110034070007250807040c0c206040c1030226541c0c485501004120420581c00340b030030401080783e5444414004200555004a880103403405085828104083d03000035004890b400f54120b10104000703510b400441041d2640500001c0c24040b944122682c850011101c05d00441e0b000030386000c1e036201d20710071030014001c0ae590800051640c0800255a441c00600290602c0f12040002d0310450082040d10203910341d0404a40e91a6116000700407400d5025583e8000041ca4200100d070131000494113030f105003c06080c440c20004105c0c40c4050101e4601025a441e00409002103081c0c80c80251280c415401084e0160756400c041007482007014040a11034140d4000126440441d555866441c0300f00030540350603040131702410325 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 670168884 1250 670167634 670167637
    0x402060906030f040c050627032e0b0901031a0a0f0c0c0605010f0b0304030f0504050d03050c100507020303060f04390504030503072406030b06030f010b0f090408 71
    0xc0c4a600c480080200b01c0480e507040486842503124410140101e6900c0b001d00000b400f9452071000f08455011200c5043c1a811600044034a002401c9407100c100d0031034203003040380aa0b01206c4603621a43d00200c54600d0703074020005448815110507080c0d42c5107807035105a082c0c55460070510701d441c100c0450b09044a58001100c940051001080716900881c0044e001a8942904580040c00d140000600302006441d101c02c607100320411704c2c5540c0e1035590440e041c49180289a0030300001348008500c5840354224050315500ca0f80701c00341c1d01c40c01d02c5860381c548010f00d058665124107210130800c4150303001c001d0307a0b004101510038100c42c0003a480058064181c01540d000811008010844100b01c4510814a882c1c082d15049074a282c0c2740380116000d209901010b04598000c00442000172000a40c0c5c00d041c11035045415078001100780440b007540c42d59030041d5080301b020000d120003440c0902101c002071050100070002045440c0c0441c4840c0005659907104200b8400014284000e250 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 670170134 1250 670168884 670168897
    0x6101d06060d11090f0901030c050607020a0b0406090611031c05090102360a0806010b03070509030a0c0e150924090a090c1520010b10030b0f041b08040206 68
    0x12040c0f011096080105405030080c8203414400c06201c1c40342000340c01c29000150680e81c00c10301c4042c4260030706003840b030a588440d5040747c004000781c0d00000da40031920050005420142d031540d04091411400400c0c0d0b00c40d801409a45070070801007401c071000d10003d6030220062449000c5925640e01e0480c6009000b480a506c180c40070000541140310041484040035000600c2d4410101641105106001415000319505a8401c40050001c0384010001d95407201080c5001c40c98440350300042810111800c10803200301040c07000502c400403550860940c48061801d002450704000c4002902460018004c511900754444641030030b5400e00b4450f0038100c41c090310680c10341c03c0c01800d446c000c000d099000d83c2c0400e0340c8000404d0004014280009102041e51143c50039110302c040100715504044844149640e0307962205480c0d1102042d000c1c01b000e49890011314826a02c061040c0c41108400d01d0744aa031604400301c17040c04115102504c116100d103002c0545683d20f1020400520504 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 670171384 1250 670170134 670170157
    0xc122b1a2209030512090604021c020303090a080c090a0513060e010f050f160c03080c03060121090606080f12030408091507030f0c0506061207030c03030e010206101d0606 75
    0x40ca60003d25030000000d010907520781da0b9900e026640d0001a9032640815075009600108020b00062126000f04019a040e40001c00756407800424a0006800341e400d40d00403181074010706d50356041303032070700000c3c2c1907008200d49010300c824601061900305014550030000e043c2c55032303204641201c0c0c07002d41c420200010740d08020045410217407070401f5004802c895910342e00131650100c444035803290a40d0010141e01d6261114244c035860441d0086802c002c0c00c0398100600481d052410345100035501c0c00c0c1090410001030405141d0814800750788650700505000d501841d40d0301007042c00060030183d40c115052200382c9130b4239070b89000e5040c1d03c00e02140c01d9001c8a034110002411040e100188074040c802d494140d180c58501c2030980c1c001043c02000351035504000005001401c00313070300c511030302d910080c150b030106a100d2f0b0f6015071a14103500203500240001c45552460350701000082c1d0056140802410040d1420707100304011021100b5610354003a1840c04113203183c480000b92020030551 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 670172634 1250 670171384 670171391
    0x9010905070635160302041401050f0d09080c07051903020607050f0a0507061205060a2105011104050109051f030c050427110f09060c122b1a22 63
    0xc0c0c1c0200b0f51503d0686000801d1091204000c01e20780c0a803003103c04a4030400c50120303410f0402001900e494015040c0020860000c000c41104030455201d0049018481c010b895140e580d230a00d030f946840e03010341009025403501640000080100400041100d078100e44055603070340203152850800320b09110400c460310441c120350f000c020380822107900b521000c0e900c1070500c405001d500d400395482601d0494000680e44028010006175040710000b0030426190328162907110f48d1418210741c60308084030349007000820148401c6d1fa014000310020102240c0203010b407902c102e03141800f000101f4014081c15035907130780c0c2d0202e14000c4003078400401400c4515000c11030700003900300c207003852000542416868003039040c401948040076542040d44c3c0214040c00c0c0030251091250592000303030a40054802c50407450703029900304c402040040380b8014099580d48074000c81303c042c51003400190081a00b40440c0e1508445100d204603442e50040725400306480000c03001700c2d120203c094503890407a00307 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 670173884 1250 670172634 670172717
    0x10909060e06070c05282310020d0c080f0a020a03230403020c03030f180303091207141e0103050709170c0901080115031502160606050405090109050706 67
    0x3002010044801d001e00e081c0c1d40d00b9560703e1b019402000704400702c080c2c40c81d001079100021541150003820071002012505a8100c008030070a0300c0d01c0d000e982e440c0a030725000100c00b03580361380a00524103c81c015003030100c102d04080e030300121020300090446050650200d0101d45483c441d40080d0681001d180c18003011052140a074410300398210342c02d81c054400c0304030045a0707040000403038001003000e4480728104200030180e44600003010240c6c56051105000e591887c1e0b07240140c2015a2540600420321989051180d40c030381c0300c42840c010310600314089081ca48116440907a40444000d2070000f401d5651900c017590b510742150821000c444180701000464800041c5510320140112034030701081e039881c1c03aa182a250f8180c03080c800c1001c0b2107400c01c00a0940c0c510007a040303028030030150619081d02030f65040e10a0b040c41c00d4030016100c030020811070401c0d00c500741e001140c14009009019040d00c2d1b02d540c50704144140c80c10054109480202c0c1c1c0200c4014240788501c0d41601d002126 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 670175134 1250 670173884 670173887
    0x809030403021806120c06040501120621050f150a05040201030219020c040614061b1f051b0903070e150405150a0509040b01050402030403090506033c010909060e0607 73
    0x4a41e550b008150317880d02c1d0b54003900c00203401c5042d0180100307071a1915090000440c2d40c045031044038441e070ba84640c00030801a0810b100c2094400380d1407007004409085045c014946111200c003049c0c00e80040c00717503042c8031400000309603100701060700100d865107075031004030000c1c4901c4102101c00c2c03010403444c030307072590b80401e243c6030b404d030110b4090040c50303100c00e141282140300d201420750268080081c01e100c00c7c444040060000000303004c1e40d03c14803a60118404110034000036900d003d03a00c404010b43d810702d1280440454003010400c900704200e240120340c0c1c4010b02c1c092006a02c001303400040003590f2880c0ca034416071401400a014a0800307071a07213121140603003991440f551495030302061508181403d1413003145c2000d81da99141e464202808025400940b0550402003040808580d5450740b00c0198003072031141c00180c01010003458a501007181c2d603290417691044840401050350840440241540d4281e400060442e42c6032070b202d8010b0451520244403401000200b04625 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 670176384 1250 670175134 670175179
    0x70f1b0833090a0c12050114190f0b120303010f050603271606170108010605010e0f060c070803040602060903040303090608070903051f0f0605060703080903040302 72
    0x55404008036688004414440010103407044586812900c0c03000c8aa840d03440315070300c501d402828050aa850418158607a002460a541c00140f248180550241d040002c02d01c00c800c01c4c04115000a0000c1c20724088040baa04035028081c02d000391600e026903020340c20707644606039012000305201040030150344d000c0d481c1c4d0000d20400c1c0d030318555003000243da820b0078001c881c8107003130054040c1c403801410138020300c80304030b008404500c2e489144540c0c40169501320005002c0c2c1044c0e210200610340f400c102c0703442102e0580003417804d0307410100b080010303980000c8460f5085104684102c2c020b440b402c04200180110400c0c2500c603c24800006080c0038048000c2c0180c0b4000d40c2910610764a1144032a0788ac403d512004000070b0101c0001c000d82486546529007041351032902c090700d5a0f40e51100e500d00480c02d014140d4a140c84422000040c0c0070340b250600005d01d0181c01c3c800700e480c00c00001c20b2801016006024040d2503000511400b0092085402441d80104004136103101c82020b00c089 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 670177634 1250 670176384 670176389
    0x3120e061c0b0406061b0f0b0403050c0d02150a330f090603080d0e0102310f0b0306010e0a150306030c0b030910020a110a050a0515010f0902070f1b 65
    0x1d249880450940350a240c0030f0482591580d40340d10824000180c220002c140411405942e86883e80c103040c0c0000e1018201c99004900940e00c858450744c0e900d10040c00c011441c2588c40555100c4075183c900c268114403801c1d444400388100180c03868403203040d81049100100c005601001800c1b02c4882c40c1c203e42140d506031115038070070342c20a9840390900800c4038218040a010880305021302810300d5215000040c0b180c54400001d07040c03c0280e4020100b15a0f00c4010310f561002c0064000904500130075460020480c550070200d49502d402681102448054032041c10402e20b4070301c8801c82d445102a0500414000f602c5d2002c50210102c010f00800b200c1c00304aa4000c481e060001d079070312450f420380340541b4101c8050080307800e07800c060708002d6001c0000e04080c005400345500c00200c2c1480017154140c0140040e040171501c81c81c00303a040134400c40804208110b014018004860880310400540745800d400503a035408908105c3d0b03116143c040001c00c41ca40c642054452140e40740e01c48000c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 670178884 1250 670177634 670177687
    0x201051b06040b0f130305161106030a050f07030b0901092c0706020c0f1018090c021f05040b01030821150a0f32040203040305070b0109060302090103120e06 69
    0x110350312505121170b403640810801800003a400e0003e5206c980240180c0900140314440008802003204081255a0402c51b0000c0c0130903a20020007002c507801030746160b0700003454501000300c60a400300280c1552018090350000c20b45d50300d000010001414290140940055403452200703213100b920310b689414501600005021f00c0454444908150b0545000d1900040034220441b1903801d007110781110460142c4142c1320085070000b252441849031044454550b80a40303c411861001074804049001911000500d08410000071034080c0a000b81520783c01981e00d0360710f5865080342158201500c2c5145440c0341c0307541c14042403640f050f24201c911a41a9040605140d8070555003580c08014030400141250380b103240003014010254480000e5501c1111181d044220000b180898104807411030200e0000504e2000384060840342074010004070400380b01c1c180c00c50b8041035078000184030040c00030340007003a8000036034011010304440c98405000c10f500c41c0c1e000d14841041510079200000b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 670180134 1250 670178884 670178911
    0x20c0d030c1b0b07021f060302010e090c04060c05030d0203070914150912100f020909010b130308180d11040e0102030c04030813081501050a0e0f040201051b06040b 72
    0x60649029501c400300651040808000b10040c2e600e810080582c0208100214066282d8090b2480074200ca0841441d0f10520005442030452002400591450b10003600c501240c1c8104410000e44204843c103031115480c212106001034a0101c0c03650181000b1564564004010800225480315400c0c0c2100c40303a0036100031404020b018000000071502c0c40036030307081003040548958140a40641721445580c070440b42036120ba41c0d440021a100340b0401c450198002a034407225140c21100300e80034120301d407021031030080d84c00361a03012011a440020000c80c0081030343c405480840c0b41c1020102e00285c42d034819900c0c0c034070707103401c55044200c0301a119070310305030420002308014402d40b40700301155040e50f4500707400c40d114106150002803040c91204e140d800d0100e0158000c1c0260410950080c80e07002c0d1070350602040018259694201c010312a0400701005a11114030440f640c1140c1c0a00300541d40b40350b41e04030801280c0086240384a1031044c00c080c0004c1280040c800c911880c4484081b2 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 670181384 1250 670180134 670180151
    0x162f09010504050906150112050906070306051203250b07020a030210060e0408030408040b043807170409020a0c1506030b070f0306090f0e010e0c1e060d020c0d03 71
    0x700c50f41698160100e0340403200103103080c541900d100c440d001c01410132000440c2110800310a98504a841c94100d0304684107000d9850781500032070000c0c00302204c0c0ca0386000b0b0341c03c0c130113941c034001d0900c2041144480403c01507810b4444403415120354110100d68280c1c6030002c4007075912001c1030b808500500c25210aaa003040040c42400b064485504031480c85407500d031100c406581001d40142c510400c204000103411060304000d00003400009103007901110086c00502d03041d44800041030000080c504450300ca0507000b02215000d82d441044110107407500350500b003081c042c039080261344c184000340c12100d05030092075031843c442c0705515002c3c5292102e50141c0585050384002084059000b0100341c410b4090754082400550900d40090095a610600400d548801d0f202450310359441c4503a000c1e004080c0685d180e03484103007004142019144020441d21440b50080742c1002c840109080020b0b5200c00442e041032115000554441000c00050b903150181f00e91403001081c81d001c043c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 670182634 1250 670181384 670181389
    0xc040f03060c0923060c15090a110618131b021e0d2a060510031202060708010501050f070206040605120a0504050604020108041a0406020a03140c162f090105 69
    0x20300130301c10111001d4110300c40040c001190040c031400c0c07400f40141162441c11208000400f44151040c0340180340640d5141003034041c5642d24103000f40204000c00c1445001c40c3c0641085600c00d5040d56225004c03074070354144500812a404803418084c1c29903841c800d00d280e00184a205d0701c0c1c1488090340700c1c080092a41c95640503001c0c402d50100f47c8442d140009640f107174803803c40d040c0c0890f070101c0c03401349550b4550088600480c0d0707501d0400034a10040c018804c001c0e01e501c4a8000d03c0c001000142000c1c04003400410f814460f02e07041000001d00800740405080a54142d00d5002c2c01d1517071910380710040035015411007051143c5404002c1d0000720381d4020ba00078203005035000b070060045612280c00444940000a10940384003802d8003c200c804040b4610461080340910401a180d10300010f0081c25601c1404c010b416240100c0c0c240710f031454042c0e0031994100c0d9481c03825010000d80f460940789610652001c981008202001044a04402c8080440075181112080c440b683c0301d204 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 670183884 1250 670182634 670182659
    0x20f100908071202100e0a031704030b1e0f0601051b0c0111150a05060423060928051005030a050c04110414040905010209030a060e0f15040b0c040f03060c09 69
    0x30117540031a00800286100380100754074041d50f040900341c0392402d0389a480b250405032804108580340100003608000b84980440c450390000c010550006101303040311181e000095011300f0303d014a0714440701260091380600c04660b0301e8186120110103900408401d29151242d441ca21404502c614012254028002c2449072000a52041071136290301ca100480c4010800288226003091740d0b89001d2403403203c152483e20070aa909a440d03003070340c40c004c018008e840c0c102400001b403401e40086104840e09800c0480c0301d21300da0400000900303036281a10f0400c03203111940082d4143c0281c040e203105128020510304000b21054900740a1a031041a00800c02e109921405600c00249000d400301c82c0703044d4105281b50f50041002500f40080390300000c1c20b140302c040e411586165140558161140c007031180c45905880b81016203040c0b03000c5c099003182d91900420092a00c0180030002d0000110907094802070140382d110071414039124541700000f0030b2080900380c013080f440e900019000d0f18660 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 670185134 1250 670183884 670183919
    0x6080702120c12030103060902130c090e1e01030c08250b0d0603050303070c110d0206630a14040b15030417030702030702010c020f10090807 62
    0x380100303080810101410040d800c4100c45180758012105120039032a42e10002d180694081c10b00010020340510400c0100c4104009036000142080c3d02c0100403a0000140300845102e14203100740341e9100c46004140f0304000240160b6000598004000d210104030144180c400320400c9400f00140400d140600c0c00d50041414201d507190b000902c0003c2e1250007918440790b503140d02040b0142c0369a80d40381107030000c88000c13001607003200b81c0c4000d00c219016500340c12031040d14442030000154000c5030b454801c4070400d018203d403010802041014054240085201e00010300c2c100f100a02c0d101202c07100e82d49468516181040b44410100c0d440044510000780014000704001d45000601c1d0202c6035a2048190b025a54071400795541d1101a4400020808582c15903540d25192500c500e0750252103001d1680242c082c0100400030707800108039004141c09080058020b074442c80021901c1e030440c060b00342c010907090805103800c0d411100c05001e40c1c3d80c0c2d81c01c0d03840c1592960031007115889030a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 670186384 1250 670185134 670185137
    0x70611040b0703020f1c0f21020a0210110906031905070309030e040b010c021905041a0405011505120a020f0a0f091505030c030a0e0d020312180307170c01060609050a060807 76
    0x43c1101c99100e0003080640e910344268100441070032340d4894a85000c20b200c0508008254000403c2400c1c0e0740d05010000404641034130070402c0d000da902c0c0c2c0c044980107a0726110300070040000880d9070110b1001f03c409404540903010b1100303181030b1400a000d04044502280896015204442685054003c156000030103a449204c140060b4003000700341c45200c07401507001c0f01c1400e401b258a031100c2c000c44544035001440078803010103072001d21045580507070241588070382d031100d4010700c0c2d0740c0034044600400c00c148481d40b480c0c40756200c9030021700c200012808211000660500481e4018900d52084112900d45030f444a0b034469a2010301c146581a9500080003000010321014100300a0342e000004000c2c00280d1011115125181080303070441d120259002055619005104d140172a900c181034804141071591450300e025502c2c052060000d10f0401502e58480b500303d03c0c00150382c0c0c8072030007100074468540e60f0100540459190b00a181c0a491030103408511540521140c2e40908080d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 670187634 1250 670186384 670186423
    0x30b09150f092a041409070902030105030d03090c05040603060f050601030c050d05131e05010b0d081602181f05031b2b140f1c05070611040b0703020f 66
    0x1000c3c01c6805181452480359041d9024640302c041070302c8034402c00b04901d042002d1111141002d21b401c92501c0890b502084945004100500c2592000309107074444260506001c1000d4425291843d900303429a00b00c95041450600c0000500030107401404c20b41c480391074104666140c44004500740c80c3c200d40c40c1008241e04204040c0e030350900c0d40c0b007944c1c880810f901c100c8140420ba918004881503011130280c0047c04103002c441408000e108051211100704d030b1740c00c2100710503a218a41c074016200b80c000480e90440c14807041d074480d0352000112000344000260146007050f46c41c29030100f042e1207004108071101000c1103900300080c40110800c4081c507007103a00065001080144402c4d0625516601c4480313500d8402c2c01d140841003d4900d100e50440300c00049103802042c504501804001e2940d8800301440340b4882910418403010002c83c13414542d0b801c1d940c1044800741008040728080340b100020300094a00071800981142e910a42c2030350380310401d010030665500d080501d40500c4403031 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 670188884 1250 670187634 670187653
    0xf06060702120a0305030f070306030c060f02010e101a03120409111903060914040c0b0d06240207050604080c0607060b120a0b0c0705060109020a0207030b09150f09 72
    0x5014019088035440100721140145a0310200c0781801e41d0060204c0110300c000c420700c5120400381d00c88540c403190511302000640c1c0b8640300e2601030203540c42035100f0b00110844424903d8400c1d080340b41c208003640d0031035011a45641d502c1004252000000000d40150315500200d4076006c1121611607071581210b40c10b184c144180c6100a041c901400b035640340c0104a40142909242c0c411841200305842c0000d41602c0c1c90380c0c10b03082e1040030f03d101010a4201040000003250300300d080054500e012800d948031603030110654024110b54210003000b502e40058034450350310307400f200450003002d80d0035186082d68030010301c21140102e0140c01015040f49440b003007542030140c05803620a0140a0118002c50700c9000300d0402c030301c042460301042d00203c400b482404005031086822403050640319151031401e4480e030340c40e02d806020b1040384680000c0e4444810740300700414001b858011000c00407a00300280c0e4595030f03c3d841105051031081481c00210000c011022903032081500700b02074095401d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 670190134 1250 670188884 670188889
    0xc04050d0213090218100f03080a230d15051002030a030c0516060b011106062b080f03070e04061805071206080f06131e05071805010513050f06 63
    0x540c002c1e44500107030b0707840100501682e10084c08440400c42941c250320b95040c00b814044d1000190303001000e02c15414001000000c24107401c540c1140030030f02d231050506064420b09a40e4400c0b43d01e40035503045000c940d046030009541d010b000306270030401318081c00b55607036024019a0b0080f024501c000d03800511410700ca89020b500a8000704006203000d918103000b8484480030609000400e8034065a200c11032545560170004000000380c02c00010066480c10300300184c0701c80b503040002000c0080c201d0342340051f070000241c0391841d544d2007500d141c0c0340c0c12510f141d602a0742049680400052040292283c5030038940b0950b015100100c4504008060b20340020000c0c1c00c0c0907000318100040d10030f5002c0201020310030700014000000c0a0000940f11001d07540c90101d01130402d00c0310351580700d403283c00140d11440610210501c242113140e116200d051140c14821030340c2c4102103801c5650303909010307150941c0c4003a040e500111501d2800703030280d4804200302d40040b01c1d09040000c01070040759052 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 670191384 1250 670190134 670190149
    0x40c020c0d080405030d030c110705060414060708121e010305030403031d040911040605010e0306010909031403070e0901080615012001020706020d0501081f150e070c03080c04050d02 80
    0xd801161a60f24007aa42d2011038500512040e1340f03000640d0354002c0052240e0302004200800031098024a46e0504042c0010700c10b1142c4c1c0300341202c030080004411804d07259207081c0c4a0468000701001e8403101c1e41c2084880604084440403a4480c80030702107100c840003d903540d410b80b0b410000a508003420750794180c4e0359039600d600c904030b0101c95112600940e40d4902440c480385100360340e41070000e481001408140c030069009203040c8401840c403005c442d1030000d01681180c000d403070301140c0b4800c1d600b820b176401c0b5a241d87e1000891400000c00c110190030020011058006690245090307a8550b401911808107550a402903d60b41c200340c58158421010540101c621074064408010310941d00d908a9024007000caa51507008134400211800328070a1900400c41d01d4003030140d40d0f0302c036240803c814910080002499554489265030044030131200d07030160000c1d140c0040c950606d1800030700304c21074095041b400501c0a20000b00c1204406040c1d44c2211800b43c04e888810b8003540c204540b4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 670192634 1250 670191384 670191409
    0x1b04021b0a030306030615080309100504031a09070b21060a0503070e0a0c0306060804061a04050403121a0f2101111c230603070f0b0a030b040c020c 65
    0x4030000200004034203002842049a40c0e44251000181c0b2844d41c80c3c00f0060b51459444503411100082d001c100280d030100c1100c03a0f881c005c40350300d40410b24244058486008036000588049500040361454091501d84139000d4914007080f182c0565859008030403c0c41614610500c100101f0100c00306800c0b850402a00800020094412240c580c0003003881e0503560790259040b042d02074103100d90400340380704040c5104481d141c2440b500e820000041c15070b070405403000304040d40c1c0781b440b42520040e03081a004071810050090126040a08005146407000300813908214a0140000030b60f9130800401110701c803010b064503035104011800c0214184001244002c01e9031100d1081100500030b1040f0b2010300340e050303d080c0e1958400315816410444440d007200745107260059604c0c024820099200100c5c40010001d101903482c800440d040810550251030550005000401c00c01041d0024280f14609035400f000140d2500041005452080340004050f8005921217511401d000094002 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 670193884 1250 670192634 670192657
    0x1050105150702041b050403020108010e2a0c03120105091e160c080706050714030408030a020306011106070201020301090e06060f04021612080106031b2a0602030a0603050f1b0402 79
    0x190810a03211764409507180115000025400007070510856070080c0c0c20714003400c00d01c000c101207407074080303501001855011401e011070602042110703003c3e00d0030001c80b0f1482c02e4803015691212842e014814004c0001e0141511604423400040c1908c0d81c0d40000030415502807500c1281503c4250202440958102210301007018440204000c5060100140080c1d4443d40001820f4502480000c107010301c000b6444490207002c00900c4082401e600035650461100440180c0e01c0c1c84040040c4c803a440600c9003c5a580100000c02c18007a40660141d4101c0f10b0306102071250305c800b4140151202c8c4100c641980c042cbc4010303041d2030702c0c1c1060f030f01509440040c0386d17a4600d1002c03551118001100406082e1000079406001408110351600500c092502c08001c0130400d00440c3e48068028980d49a18040007210031440c0600030741400301d41c03115a508000704654030300340120244003802c05d901051740c1c144250403000304c15079400a810400120840c40380d81c0f0032080704007040042d6202e0116000e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 670195134 1250 670193884 670193891
    0x1020a0c061509020c0601030309050d03022515020f07050607020901290d0605010216050306040b040309090e07050f0102031e030c070210020c0909010c09050105221203110105010515070204 83
    0xc0c103e1044c40100f08a03103490005104941c514500200010b00c0d81d04514000c0341002840000203400240380c14900c0d600c0380d04000c40100151907040080c060707a00040841e852410610b0540b03402095600310610103109490b4079545400038810b00303100e4000d0094210408100400846000307254420504400d203241170318070b030f00c01c0b0700c1c0e0901707500300e020010407040c1d0304d00040040d50380412180c00041940c01042e181d4625160000e6119000203102503c200307107600010381010f00c00d24408014011013034080108600949045235070780054092107020300d62480150b1125800002a18130008240006100702c3d00f05180810003908081c2c8034444500c410701c03800005a581c004814140b0046d9802886103039520000c00c5222140a00f109002d03900d0242e03603400099002000f0030540d03900b82023a56607860211580d01c10b00d2064041e081081d0004040800d180c4d08403400610920300030341e542c50289a000d600f15089072070038820303550301c051581650f007660210b40005d40000341c0002c0002 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 670196384 1250 670195134 670195139
    0x70e09030d090b070801050d0c2607080109050c090903040512100504030f12050105010806010c03090807080a0b07020102090d11010315030308060a0603021e0c1216060e01020a0c0615 80
    0x40050301c1070007030b00711440300440702004a04c0d0b6206244500400c030444541c41020019116a50501c246015080700021100d4542c01d00300001500c0e8449200c02c441210f481c90f81d1100105c2c000c0044400864043c0544000e00d00c680c070309101c3c581c0c05000c240001e0341c6041c1c40c0004102d40081d401c0d100c00800d02580b030303010314100681c0c892117118a01949400c6154210070390300a000081040c02c3d040c0700b904d4503005200707603640000041d43c0050282401d204180c41070806840c200841c2c2c0c010300151044403c0402c1115011481c22445441459403140381e07100e006041e8207070b006c1c000700360f074000341003148110102c9d81c044c81d00c503925103040c100052022000e40c4090000d00c01038000f500070514100c10f01086040c400d0881c030003029207280c04c50614001001c00c0119500883c0c40c0014410041a180c2c3e803c0300a10198084215004000381e84a44400b0b400a20411500e02900c2e881e1038039000b079031000c034103008580000046030340d100c8500200759590001800c02e031403141345544610001 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 670197634 1250 670196384 670196407
    0x1b010305180328110a0201030c050c030c0309211f0207050d0c0311010603021302030606091f02060601142703100e061b070809060906161b0503070e0903 67
    0x4016800443c072540765120241c02c00000303451003422050040049407011070241c0c40303001c9880d56440e0340c2468040303642100c00380202e806000e200300c02200c80c00001500c0c8000d000000040180030802e54450070744000100c44140040340c0c00ea00c144d926003112141c202c00340c4000105d40303920640381c00d006061844a450340f600c2c15503800c4480300403400c900007401c03d15030007611030340c9500d141d4402444481d0959011464403080c03481689001900803000c40c81f42c3da1440c1c182c41d00c01070080d2020030b40441d03600503f40e160360256420005400780c0d0022520395449900042c1512510404040c80e01d50a81e4082b5000c80704d45080c59441a004107032400b0540e820b2110b4542040e400c5004100f94101001641c04c0000c007400c4207910b2500c0306401c5024003403d40035101c6840e04010599140c00b00a0301223885031040f4010280e002100103101d60b00301800714420b0503840c1c0200c5500c0314031303c41c1c21003134010050103000e0b1075816030249404118030ba0710621107540c4540d004041ea03007000198985d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 670198884 1250 670197634 670197637
    0x60c080d14070908030c032b0e1e010204030b06060c15132f0d0305040305060f0f070212271917030306063001170f1b0103051803 57
    0xc00010002006001e02c003644600780b80060411503000e0351400c103807204115680d02c12680d0b180c2040340500501c2e209110124030f15070744002c01d12018031141d1104411162115211102007140100c200d8610596180c14804c0e00c00b0f8070b0384a0344000c400d071525030400034550050b5444440c00d1103940b2001d2042445942001c0c0104d406400c1200401f90901c1c041c12110100040b0440701b541034500c10a10f03110082c4251096001912440c401884500b421940e41c425038001070240c0c0302c0c541c1402110070449400c20302c600801080400c0c0c42e107070500200e0300c03600c000a0f034000084c0240441d1b4201906480501c03d21809152840000444500030494004540e65a22041d09010a04002e03100c42039001960015210303000e1881c600c0c01c2d4001440c0c600a032601c1d14841070582c80528004005101034001751440c1e06110034a640c0e40d200180c0c900c0c0302c01100d0600074000d8034102403400703400055107981030b0080e000e4410b85020840044004240007090404010070355400113520200600 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 670200134 1250 670198884 670198901
    0x606030501020d0c1106010e070909050f010f061d040f0213170606100207120c0b0712110106060903110a050d14070f06050d0b0a05040e010905010605090402060301060c080d 76
    0x10001d83c4038007003100785804413607210140e1800e001040820a00441340815140e064846034442556651102e84007115080700c15000b543c1c21500d070000f404070380110201101c0c102e425074006078810548a480890b000c0c0c91500403442d1103416015030343c9403490321307400c00d803100500c1150041c2850700c914180340c4000c1803035118005001500038086448082440100d912040c2a6241d46203031079a8040259079503814441d00e0840f0b568840310608001c03001c41c07004000d24106000a071914610304101001d4401d50201901241c40040c1a00c8a140113001d40310455076540c4443c0c4106165403103810044460b200190b500c080001d0000c2000d9270b42a0715004014011246601038641c04440b06d441c0050a4014031243c46480008000d000e5103c0119a02008080f10105010702e9040116020086542055a00908094030240e41007030542c00340c2c0f03080d401140280002079540c0244a400038003685c0294000d0700c10001480514041c08000034843d1065200a103407805101d5210700311005070 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 670201384 1250 670200134 670200143
    0x11030709050109050109180b04050705150909070806010c080d0b0d03090905060102030412020d050109080a020f01110301060e150d060e0f070f0f0f020a051617070e010918060603 78
    0x61006200824a84c0f2074140500740425080201c047c3d10204e03810120b4502000130918407101c4002070806c4003d0005000411024004400d0164155400001504082480c43c00b846160002842242c400c400070f80c02a001a180c41058000c161903c080035841003030f000c21666200c02482881e034441245500702280643d4a00141c142001295025180017800da241154024802401001090003145110f103078111100c1e0600400351a10502505540c070303000e444500046207a4190742e8000c601900304d49100030007003140140946007042540030030300407200065034802c5080b1644c00c0c0031480c096200e0303411003068104100300d24102d0658080e90089000c1303580030001c0c00307071410400e00b9094200203582004683d980e15258024695019098803c040124408000003102c2c02401208416500701003540d4800c4120702e4016607500241c41610200303000c120341140145c5004c101c00d010b844a07807501d896545d203841180d03070140c599003402022551086054034009911031040000a40c480d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 670202634 1250 670201384 670201391
    0xb07030c1a1602030403030807050304050a050a0b09010b010903050c01112b08060105120c09041d011406220b0a150f0207090b03060f0a09021c110402210411030709 72
    0x10640d100142d4421808240941d4414041800000e8108101302e6002e012880c20350f4513a0394600b0520705d00390308007601910b01c2c060160321b10306210a500a5078802d03e4440001d0211251603001103c1e00c0055200c0544540c2022612024562084442011940d0300718201c5120800f075a0f400d00c10b50a8084950090358280e00c03179a0990b542005402d54004002d080c980d00385420655841c0c1071100c01070207810034031400070b200342d030f42da8072940011800c03418140520b082c8401e40c401c0900800c40d41600b6144c4940010004429152114140d542c103013820b007142880c8024900e40310701818002402daa80306610380740c04120074482414900811780709564200d562011240086e00f001c5d0680c002518250412521034502e443c0081c0c002e8000c0c0281d940365610ba56007212000040c039180500944c0040c1c402c1c3c2000148040d0000007000d9400758002051013250030342000308034490b201d032001802843c0102425916403403c0c02c0c40c0c0c050300171721207440c4540c8000000307400c8c500250000c00c21140d8 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 670203884 1250 670202634 670202641
    0x1d0a020f0d14150a14070c02150f07020f0604031a0604110c010203100905150f0d08040b030f01060525020a05090c0406120b0a0b0d270302250b07030c1a 67
    0x201520813030b000f070050102001086400c5518070110ba03801452041403080310f22054007107440320180e82c0c500300d0400303103030640b641c20f25100c414240e80150300a80c411241403000152501d012800c440440e54006486200c850010045041c80c0c031005144a50203941c400d0002140801500100489405c88000503034925008910310f140c2507840e045203460b40d16160401804840c102070291b000755003155044000403103000050421820b010006001017008100002c008484d00059030041c164015140f6042c0c1c0c0b100340c11289070040d0402e00c0a03015582c68510045000f204894610070f0000d0f100c0d480c07141e121404185400340c00d48001918480000301000700c1580070484010304800c1417401d004481070540040c01e80d0f5aa0302940540400015204900d414640d2002d481c034102400c0c90b0514100c60101280d154121071016000350181e00d0703c020f104058051054642c85a03142001007103424588440110340241718200c003440030080a86010900d6400c1420341041d01c1c2455186525 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 670205134 1250 670203884 670203913
    0x2304051305010e0708060c0705010b0a03030903052401051003020c1f0b030705150a020316050a120c0c03030f0c0503031008160e0609040213020a0801091d0a020f0d14 73
    0x350701540940350f6030003a4000b413009002c04603800e9000190811820703110107050502030f0042c0300c0721020507802020340100000b0103800888840449004106495203822400c0000c4604202404401040c0180c6801031080d40b4006480a801c0321a07440e0050034041520741e05231914800341c3c0901001396034a10681d90b21681c43c0503822342540d0a50250210500d00000310705405000d0707030074041d000d102140c0790071090320820903a101142803d903051040e882500341a512900042410b554200c42c05054004060043d100303000c0b80f40c2d00c0303019861072918527101261001903041070036081207945041031000c15000c0025500074402080c030b01e5800c40c03500c40d45a103410964504042c1c2264001c2d003c100408881c400725601600c203440d1110266140c5c4000b0380c0c29441c1c0441c01c0c026602c046803840346568807404441c140d46000d40304000741042c0c00050001d034040094070ba00e1990020143c0700060619560b40c61000f9800350141826181503500c4042081040c40a240c140d03201406e250000e4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 670206384 1250 670205134 670205141
    0x10216020a05040c05180103150303030f0605010806100c05011508030301080708060c160807211206080a11040b121b0604051c050f060a15090e07230405130501 70
    0x14a01203800b0010380c84c0d00d2501402c640500c0320f444010000c0105c0007412a40280c009846070f090705075100140e15200e15000d802030a0304800c40022500e41000841d0a50094130550700403900103100400f00c0c000660101e1700034401c100c0488480d529003500200d84814142038a01910010b005940c807903040c40010740c80c0640036440540140d0058040c007690070070100450344503221910584502480a003403801d00c503c50024024070b0340030115014601e000f050100015100e40303560343c1c40c0070f203c4000b010720266400c90150304519000450158005400e40786840719020000d8000304008248800081008402c0004044180c100c030183e0304070840b40e1100c00802c110300300c1c0d00c10704241c102404900c041b0704070040c0001c2d00409010040a21604203c14441d800001088031214a490090500034200031009148585100e800201340e43c42140a0320010700000c400908603145000c5281d88840401e90403903075007800b11401078489031503c0c01841d2088404c2080c01868441c0c83c6840e5084 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 670207634 1250 670206384 670206389
    0x70302060f0f0c0322080309191227030303020910032009030a0615050f0d120e130c1d100807030c050c15010e100807051011010216020a 60
    0x40780504000c014400c1c2901d00300039042441e24a80c10b84aa41c2d00f000811001030440201c0d0441c1000e03a042002c110490380150300c1503151900382d50040c030007004403a050000380d8000925622400961040301445001710004d03284044140c45c001070105400060340089a800640c0040e400180715001030902c81c00140100d8441d15040000d140c065408004044641109152003480020f05041c2c1c0e9400300305e11a44140c1010080045480240a140c50b003c45e0b440343d223014010035100039440b450b000b004400100e0304000035442d002231821003145d402c3c104102e40ba0b800301c0d150560255000d200d11614202c0713071454403455006e042602501001d20b0204082c18821811000003040c8281d00048140d0000e460b4100890654841041a00ca50140d2001400d45214851300c0c041d8404006180e181261425020a2455281c04150344d010b001580103c008580c0400001c0080e401d28084500440d211440d1a0010b0010340d080b070f81c2641d0015424840300010340300d00005619005001300300 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 670208884 1250 670207634 670207651
    0xe040606080c01050c030f07060f050a060306050702010216120c0503031810091e030908030706200a0207060e0102030d02030a1505100f0e0d080c0d020c090f0a0e100c0507030206 78
    0x41c103808141c40b6940c4d00c47d1040c80240f0388800700c0c100041080780c0c1c00000c8001c401840030300883c5000304600300185150301c02951000d0501c808151514010b100b00d4104281032000e02e002d40050b91500c0703084c402c0c0d101c54030041001540000012440c28405580240948500c100714102c1c2c42030990319104488110664240c035000c20000020740040103520914101d000e041d0040069040548a1080562004919000001d0782404000d4150b0118a006095044007201e20544615065242c05000200c0d00542e118800c1031103c240142443c52184d01d052040728540713200e209500e000d80c0c00030340d56507840742d40f41c03605424001041180c24001d03180c10b44011020560041c0020041103031245900e06010b02c01031154003c6c0c5543c15400c44164100c2c1c210b43e51551000d003103540d07591400800070b0060040814084541c80d060074010b0090104080d110303620784800c000c0740c008211010b41841c142c4100f005010402c0380c0740c0a01c1100e541e46071a241d85070354480c1000790910000034810380 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 670210134 1250 670208884 670208887
    0x903080702011a0d2a1710020405060405150f0a091d090309040c0e041a011b080a1209020901030c05011d030601140d0c0e01170f0d03150e040606080c0105 68
    0x1076040d04c0e0b8020004071241c00c46854164101c904841d41240c03800c03155150a0201e0107031010500d6120000300300c03d0800f18500300e07100f401031034044608a0085005040e8000c4080000b00001d00d0010b007502c40503c90014441d26000c4403401684240e80721985100209036042010015200006086810b03004c2c640304500d65071400ca006540c6902c9402060382c802c035980c8540303594051065450030400341c0040c00070001e401d540e405840030320b011081554005840788014401480c075101d00d198016034070030105821318140c40000d171069020145416040c5949410315409a07561034800c2d030095018903050081303c0d09140004100c1c4400c404c954843e4010103000242540300000c00da41142c00369510b900c01c00e03601c200002e001c9460050007a02e5141241004901c28090042e07150403030740300d8050b40a000d0100380499441d41010009010160000044010401c0c020780000000c016a0300150405644940341c00b01066419142a208290380d00c13024051445c00300700002004d0740900b46507 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 670211384 1250 670210134 670210181
    0x3050c301006090b0a063b0415030b040807210906030b18061201061805091908090f040e010e030304121707050d061205150a021c05090f01090308070201 67
    0x115504158406c00c0c04008040328401c12560318041505018400000a101c01c18845c88111500801c0d040358144190302c0d2012a0800451400c480c6040303940c40080f5141540d2070b03484004240d0083c0100340c072740c0c40549440620000c0000a0094015450303101c42e85484d04101005044605004281d4010a14140201d00341c182950245a00c458101c41840a20150048480c058000c65200d101c020340c24520108003112150452481510850201e9000303c04140701601000d0003804060001e9104004e405028103050a1164150ba0f0107400880d40b615a000c0391030846984414082c2d03260008400e000400240d03d244820740d001031725082d04071105883c5d114110080203007481e001e126000504864a200f50340101000700248600c100075020300c1c0c1812500d820442c0000084441d015001030303c0d2031018030903140f410001154140801529102c0400284800340c092082c52003072158000c01c8420034001c1d05d01083c1310fa0354010703d50606100203400d5a540404144114400c600107 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 670212634 1250 670211384 670211389
    0x705130911030901060e010f0306050628030506060321030a090b072003030601090b07030201060305061009140708010501030b0f03120705100c0f0302220f14090103050c301006090b 79
    0x3054140e83c0c020070009140d3301c440d40052100c86542e080c201c40d4498810b582100038450440c040100c034090019959680d035002c0401d51581164a41000d554100c2d6548094240e001800b9684c81803081d4000204d0801c02e88400600040131a20b410006100000c02100c4500c14480300c4545501744c40258118200303032001800040c0175001c2c5048002d00490040181403003508000002e50b008801e54000d8145810754211140983c01401b428500f000c502017441c040e1b00b0300d00d9114596507900c0302d0841c0d09040046000d0045105540d921505404252800703903000e0066052342040c0f40449940d462907498643c1c108560318000110140c5049a0b2201c80c540210f1828000d002600e0010380c2c40c001e4012000760203500703005004002010000106448624802d03a605480711655121068403c007804c11000301424000102160400410391419003001800040c00e680349a89002e4160744200241e540921040840c1e50b140c1d1000d41900d80c00807131b40c4660306c0034256105061040b082050003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 670213884 1250 670212634 670212659
    0xe07141207030f0f20120604211808010c14030906130c170f0705191203090b0f070b070f08040b04050c04020c0703060c02070e0705130911030901060e01 67
    0x400b401c0ca8040f910448100032183d200c2101d95948010f80038070b40e0706a840f003c15058490100503002e4000d05180442a0800182d2540300315444642241141c903800004084566002900014451144441105120458214406000300c00000520120110340c0289006d8509208584031002001401352503100419010351003500030401c10901205481d20440c006510b91240b44000a00c08172404440c001180e14510504808202d41406846e0000c0000c0c0005d61042c44001c074499940c00c11816042010304642e00b800ba00701078400c56a00c1644405550180780c1001e290780c0b0000b8000c00304003802040b1038000c04145840401c0c029030b00b01c00f9040724030150001d01040f040400040402204100f8000c10301ca02800941d1140701034044c480c1d031415240012921a41444800c413100c510000340700088070201354901c00305444c0d00c142510740da0700148506043c0940c0c807501140c240918090082c00c181e030303002c015a5a1814420090031104140c01c4400481400801003024141141 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 670215134 1250 670213884 670213889
    0x10e0103051507020a0f030302070204270f0507090606020610081b041806110403020913030516050c06070f0b06010905031c0c0609080a02060906040807030f050705010e07141207 78
    0x1002c04240c882c0c0300280d02d01141d018000300b03d950324900d89010580d042d0041c1804901c2507500748900c60b981a600d80080c01c0841050b080603507042e0038100030480300c0d4165081d45014800ba110341c680c6070403502007921040e0304100050783c441d4045c007004451030508840148400c030007400d45506d80e202d0360782404074000d0005204e1078a070249606911a2030100218196014204110300d020260b00c10120307400c984002e030300c00c24071500058402800c0300c40c0c00319000d030b044d6101c52030644030041840d18020004010340306841210468142519007800030a0010300030444150412098a00880c003008010a081e040003080740d000c0050782c4002030110003141c0c580040f800c1c00062075900b110102c2c010500030f041c3d6401d151050043c000800010030042c2c49550030b84800b50b0723231592081c0d907440050f07800400314142004440e0100344145605005151180b40903481e100b12600d519094072140f20203030400390000d0030204100c2c0008221300c242040295125883e048201ca01030741c0307405062 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 670216384 1250 670215134 670215163
    0x1302030109090218044e030c0503010803041205030705010e03090406080c0306061212070f0b100f03080a0504150e0f0102150103060c090503030d050601090608060d061d03041d010e010305 82
    0x24000d0b80c0c0e0508840045104009180d20101c2c82005500386d0701a07080c8841d50300b0f00420300e401c100450b098495411641130b80e1440000b10701d0145444a00c669042c40700c1c2c42525030f80400c2c052140010b20a0054074510203060b4000c50704c8101c0c02d0704000849d251580488480d6000c8039100605480100f43c45920100803030b04942c40c1c031552101581400d0340e04100351201ca500060510802c0320140f440d01c1d05501520001640382d883d022004040010740c040c0036144000c80c903007000010380d60340041c940014640b602e10309041c2d451107280c2070012a41e4150003c100014440d02150034038050b03161480109100030100da0814041181c9048010300020303007201e444201041c0c21500880f400401814094112640c545240c03c1540040000f51100390000d990841c0c00104948103032400b030b00031500100100050f0801d40e45140041c1240d2003072145841500a109110302c0c800d00142c1300401856002d81041c409882c054074012030142c1207128596840c0c001170020650000d00c040035407501 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 670217634 1250 670216384 670216433
    0xb090f040302030d0921030c0503190204120b09060c090f010c1b0e040c0807050f0402070c050618042012150a03031d041b0509130203010909021804 65
    0x340d090481c1184604841e2405031414002c40720304112155500c01d148003213000710501c0c0003010100403003d0302d00c090a4400000d03400d0000c2403405080d9241034201c0303d0700540040c80c242d51010304a840c861070b40025580011501d0401035850400e1219a9109070f1944003c3e03e0905040d001810840b410581d03c0d040124010b08041044120440c00074511000450800c00030b079190031a6514035404c8400310381c00805001c1c006408407002941d442503a0f00108010206151030302030200a401985c1e00340e60022075010f00180315142d0700f0044c01c0016a41004520303101d0340109010968000481c45a1740010380e8480e02034441c4060241d4a40c1d00600b400d000e07264542d807511303c3c050101c0002c0e26500c880070303000c000704164000071441700c02c104890400c2640a038600400c0211254009022070300665010050000c030301c04c0d00200b065483c000c11640000e290b4007040300490304260065a41591394a4448055240a0081c003122a0240920b01010b1400703649030b07141300e114402d008581381113 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 670218884 1250 670217634 670217641
    0x30f050c0304050604090203040507080a0b010b1c0e0304050103061208090f034615150810020706140103080703030b0d060e011a0d0302031209010603140d0801090b090f 74
    0x60088900400d001440c4c45c1d00d5a4840700d0b03210003580103540848852151082c0060380c2c1002281c443e4845030040301590640c0e10740108079960350b2200d444400c4400c90303401400fa01da40e49110301d0086204107002582ca447c102000542101c0180d0464190400074010120000b02164200d81c03900200340d03218130782001c25001091812200300c100c18501d4200e20781d40f68014071403c540822591074003500d044061000851380704080102070300a04410f103000110740881203981c10682c0c1815100303040800c45983c80180a080c0724081040d2240d542e0006075080034064035004042c40a4001464182c0d113514690b50811540700700301008050644510003c00316564510280c0366103908244180a241121060342d4000c000752002c502c641d004401500a4600308110045100740d0305030011440c007016112000500b20340140001d06079900c5480100000362020880400d02004030700500c54000b40301000b410900050b084511040c1c54444080e20640d60307a074903960800303602c884000e110b44 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 670220134 1250 670218884 670218907
    0x60f0912061f0e0c160203070503030c0a05160b0a0c030504030b04050c03010501081f050c040b0c0f100c0f230a11121e0a020f06070f1b030f05 63
    0x5249190380080c600071101000116203030306149008407008284146a074a498600002608000341c4141e40c0640b0f085c022600b454520f400120242c034002800c858620f5681c50002e89158058400d000031500440c0c0c2e0304d41085401c0080d65103050300d4010007603246041112507107150044136880400c01002e47c0011003814000d03002c0380c020310380010000415181c1403e14030b0752003e1030790074035010f9880c003000004e611038041410081d821000c1d410380d081010200c04800a0315021749200441c8504102c001405110440109000407010024201c03c1ca117001d411424200108089140759083c1423188030065400184026608014140921003448001103034000540c0c2250f01036525900280d4440746036040394040040c09440d0049841c8000c86600c102824010010084480b8541e04001440091200302400b1651054412150741210b0303810b01610300242503d201e80030949040c895012180d02c80c0440507002d0b801c0d00740e6140ca02c46903030010603500312013020104000d40031403e0308018 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 670221384 1250 670220134 670220149
    0x1302040e0a020702033a030e010513020a1d0a020c01090215040f120f030509011704201210020307050c0a0b070e03060106050904110d05070215090705060f09 69
    0x90103801050103161030461003000096000c0402030744640328448003030180e00d140c00340c0360442c01c030105001104d144029550300f09006030710402d081859140e4210b1401c42100b40300f468031900c901090784001d84404c1c0103220b80315000d42c10000b00400100c110340812501001003940020f080d02c80140d030b52084c580d8503801400d8620000703511200401c0c2002e00751880303201034810394007166041491a59603071a6a0380c2d60f0940361004201c2d40c003011000c0c000c40d019030080c004024040c1045c8802e00b0000c84000c5040c0402c44040b10504403400c4c2c00380c800f44091a01101159080ea65000da0f41c12014116a40311446403114281c10740000004041d544074800359180e05040c2c1c421074807003140341d1a060310130310421a410400a46024036000d414600064030a048940341d844080c9440002c00c1480044e011104000401180400c459094004e5900c00d4174418040c1c0d40c082c2c541d00441e005c05082906024002c00c9003640f00e64802e202c10b0740c3e2442291030100d8403522a6660303807401c9010902d01c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 670222634 1250 670221384 670221389
    0x1030905060a05040c0b0703020c100203121008070617060d080d06080c090c0f040902030a060b0403030203120601030501470408011803050409180818010809010603030e130204 77
    0x200e005a0042c80a012038603080180140d01c111040d01c1e68070b4036890b007080280200030000d001640036844035806810b004105603601034039481961f181c011610148100541c1c01d8a620710003149a00080201a005200c844003500711072400c1d240204007880031103d0144040d0080344540d01180e007960130010a0002ca0f0746000d0300d04001d0160b40e590302509520380e061450158007910080000890b03004000c1e08403000e1382c410700342c61400c01c0c0c14044020004d40009284800711541e8010200d424503c501c040d00045109500566441052640700b4030414006403480e4141410840144030f212a07900348070032100005e1b117941c241c07041c01c01103c192082c142c29003641c1580c10340d120001840c501c400100107070b5001e8002813044a14040d260401901041400707400110103100500c00700405400c10071403680140e1941c50024000c1c1c0703448250b54481c4a02c0c0e1070310585803280b200c003541c0001e20543d02c002c03044000c210041c610f403006006109100055440340c12124103020b5402c00940c1500d02 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 670223884 1250 670222634 670222643
    0x7080c0a090218040c020c0102070b0301030f1b080a0c091a06040b09010c0204061e06053a05150a0905041a1911090117060a090c0201180f060c0c0f0f02010309 70
    0x50341c5c034200103902d030b110140c44140140100d41c80400d034400c50f1346c02c80e03049951101c460b00c0c1044158580079005600c02001021460b024040040c80d80810440700e40600c0c0101c424110861071704490030100c0d01c62141400c140c840001c030700300307540e07580105031002c40f000e08070312542d11030f0104012100c0c0c40d84807030029842481d16801290550200686011400c0c945460300080c9441c0d40040d12035020342d688480d0401c400031a00c2c0090300c20381880da6185d12000c901034807030641c01c0c50143c040c1c038001c40b40801d00003140d011028403072516a80c0351000348039000e801c114a09190701c0b020510151916219082903e07640403a2000c840341c8290300c1c01e0180c0000c2007001d025409102600b55000101c44c50000759a41c00003804249416811801540010000c1c90500d10340903c1c1d80103807203202e10860070342d5a43c42c0c078150f04040c0c8401801b110761041085403201003152800800f2240308a54140400c42e0b4584a800025842c64003031903103581142680d04080d80520040300a040c02c1d050042 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 670225134 1250 670223884 670223891
    0x604060302041404021c05030307030b0604030807061406040905031603140a0c0501050601081e09010f150510030c05030705030603010f0e010f1a010c0f11060c0f07080c0a09021804 79
    0xe0780d0f0300c044401c03070003107108a481d00314501c001103048154040e075510141c159001080071400c003c0c040da0083d1030015000d010541030558a899408036038222990a80b04541c07207602c00c03500002c091080b581d10940882d070030089030403186c03030b020764a00450400d0052427080c441c25000341400344003d6000c40100c000302695906504100400c44918500c04480540c04c1c0400f143da40c2d805071a0b482d01ca014442c40b410142800011407182c403210241400a0715544e43c50845480314160040408081c00c0510709240245004240441828200070707003002c05182103042e6401d01e81c4041160b406c085c151404a840780c41340c0002900400711000c001d440d107403a007a002400c024041d0070035583e00d02c4010b41041302150038900c40c051012200401800501301c00c01400015080000c01d102042c09402c6007825000b0039000b00c2c2107580034035a459101c2d0b00c540c4080d0081041000000e001d03260040150a5603c0b0040104688134420301840c1e00f8550041402c40340f10380c180707200000380c0f00010806e1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 670226384 1250 670225134 670225151
    0x5071e231306030605010314060f010e04062606010605220b27030a02011b110a0305160812091002010e0106091e0603051924140603010e1005060406030204 68
    0x75604100315101c1d032030109042a90024540d0f02a110707039115014040320114030f6686072010000040d5005101905000c03034030916081d01d460314820308001d4507400c0c180f0341031404d07508589014031410403100411984042c0060080543c00720a503030b603140264900000c0b1511041060071901d6298202e6542480c002c1040765400d8400d244400c0d19a01c243d060b4000d04200c8400d040d22141d545c040030317021404034049145845074003801810081c3c0101901814400401d0010340754881503401a07440783d118080425030041c480d004c0324002c0c90450010501e81c040d150f034800d524003074040d00c0e0344a607a00350145c0031820700039000040300403000b6000b000a19200c41c80c420003081c0341101104805d80b07054516001c10050b1052005882e0044000c14401003992424220400082001c03500044100b480748190389070440400e06040a048012a1510502e108014000070042c8042d01c40c0c2e041600b41b0050510200740300c0d010601540e4042115550040401c014040a6000070b402034600184d0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 670227634 1250 670226384 670226407
    0x21e0a300815010302131a13030b3909150d05012103050313080403050d02060712090b040f03020102090607050f010605040203100b03100302130f05071e23 68
    0x24400e220303900c0c0b212020903a00c0011003c0b806451000040c0724030b03816050003080c50301e410405041110500182c070700500c445290700b0500082d4000c441456210060155222401802d10051421500d0071410070284455042035864811445e40b440c54001400c0754194450445d03001c09a10070013411a07460005031201c0780203202c00d104040d005854031000203608241032044903103080d01a070341c403070840e140c480a500034507072422012a101c076010400040011014007050b0345481440c2c0140845262405000d00300410b0200000c08042c43d151103240002c1d240c4500b1071700300d5001109a41c0a2506103426802071085595880c3c0c8440c0200d140020441c00158034180809070300300a10103556100c09003c16400302b51003000454651032810b0000c07004020245a001c00e40c0c0b190701000c03513506c3d000700741c00540c0b030b01e1002c0c16951111001c1440680c0380c02500d801c5002454031071540a82003581c65801a04607040404010070b02501c0e03e440b24240c0780f240c030070f041011403507550b81244458 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 670228884 1250 670227634 670227647
    0x70f0308060306090d020d080c16030c061a0612072d1206050a1205120304080c150903091903080c07080f031e090409060e01020901021e0a30 62
    0x31110300c203105000005130751990206021501904076001000c022118040540343c1c2a4014902406148140001d1002400d00c120f955403060103a21201d482c0110307030410a050781c00f0045031105140407018140d409486010803502803d505240603082078580900840700403076003448104000325070001c5d6014520b20781081d0003a80c00d041c0c031075500c86000b8440000950300c1612800b9409011201c00f040a110780c5019698500e100d1000c2e02c55200d9022001e03074850300180e40a40d101c034404180c2440078802004109101d1a040880b680d191a10724491692441001c0280f070284200d006c8a114011030900713420040d503403000300b65841e03640c15448a40d40b8841441160300760b22803045c82004618020044440d202d040450810b400c941041411140d540a0302c0000c2e000365940800e440072451380e01c1003200d844844c000140c0d403140c00c6e6000a00e080c0302c0c1c0603c4410b60003140203009842d000002c200034200da03c6a0201c11085a56104407450403c2180075074085000038000700000e50b1151 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 670230134 1250 670228884 670228891
    0x112020c0d03111b0c0f091308070c0e070234090b06040506030a0f0605150a03050421020a0b0619030b090102160305070203060c03040b04061e0608010207120c0803070c0503070f0308 80
    0x6d4510b15100b9481040000c1c141041d200200e03810049540c010100d01e446004142d2036014880c140aa20f44d12220ba50301a4011601030006030444a981d5001c1042044181183c0d40802003000000c5007188408009030b81c1d52180481032076031480301401070b07207541060f44d00400c0b0051542c0c5d1030b85401e15072500500b905501009004e403400401160510b0071102c44140d403a031541629080100c442e20940c020000900107450140c0c01e10000d6502200d000f20a10458000c1d5016080b80e14a07403400100c4524064080c900c036804290101c00e110043c0440d580450342c00c211020103649440384920700901c1245a03213000070040c413413180c0605800c5001080c80030320940803202141da8003d8003007109c0c001660014124000500402e0101c1d00980003055402c1d0f0383c0000c100600500c07002c2e0022242150702154039a5004500702c41888070310080003900c0c50440c1400701d6242080e644001e11840028100d90502c50040d080c1c04c14002c0400a6908880d840036070303561400301600f0007424015045 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 670231384 1250 670230134 670230139
    0x10e030d020318041806150e0c07020109060f020d0c1106040b1213030e0120030316110606060708070f06060902040819020619230301050112020c0d03111b0c 69
    0x8021080f0038142449044400d1030300c50562072407845640d483c0d60103000c2081e13131603400751a11075001c01e10074521089503010b00d601c20302d1141d8480440c4009021030803598018802d002d81c480290840da0b40119902ca00c0c0707503044c0340a502c80070081c1b800070205040b14003417a030011030202c0c000c29840740d2038000700000c44800e02030000c01c0c1c0c0d034682480b6000d00340000040015143c0d021802c0594000e030303006c152240010b00358010740710b1b809240511319002100c00143c2e400301c82d100440f610f40c00088003c0020344c0c0802902036031a00001045407413148080c000c0c488240007584105104000045030321590380071a0030b20526544e41c0c0c1172000303900705014800e410700541c2584010031b085024113407441c0341d02508150034040600303000d8100e0071088103010144000fa20310311549030340c05070460108034180c560042c2c80c0c0d4182000144554000e1030850001c91040240089000000804c050408518500400c100c50010200100c9002d841207041010800113666051040085400200d8030002e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 670232634 1250 670231384 670231417
    0x1605010213030515011214030903011e0b0405012610050408040906051012050a0e0a081b120706051b12041205040b0706020d0e0a03110616020615010e030d0203 70
    0x40e450000030030344007031141042c5d40f5540c000600c0010901d10301403811006103c00c0e80c1c11309a03a4400b10b2f0070b440c286c50201c0305d260202c0200940c00e42c51885aa8096070064800700600d40c10944502d00c4600395800f4500148000c00c040385001d4403c0110001d422004070301846141450314141030310760450b025503401c1701d091550201d42414100a102010078080e40e403002800400480240240400f03812072601984517081e00780003035810803104580d9032040d502c96642d400101c15400448050007003418054001d02d408002440b00d00b029218559006003000a20f078070b80c0a0b400c0b0411003582414840641d000c10300c0310039130381c143c80350030320035406085141c000a03a1654121510300c030754011284410030600050003c10f079250302804108102d4800045c0e1000c3c815443d92425100340070440002d00d44c9007400c04001400d014590300505800c41d0036124990641001c2d440b0b150080c010510f0030030008c01c07280d1607823048142c1242c403100a0305032442003000c244001d40725800f201000f4800b111 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 670233884 1250 670232634 670232653
    0x1b0c050f0a051521221e080d06080c031f0b090403120b041104090f090206030115090801090c050d0c1509050f0d050d0516080a1d09070806010516050102130305 70
    0x300c01d648144980c09034207100a1031141c10301d8105e4814401d0405035400c2000f5090319030075201c00e6846c1c800d41d5000d001e49a40301c0804e4983c0c0401d4a115030406030054022611001050710b0008000e403082d61703031a04060802207094602c40003040380809040d4080c00d45801d11040c160045546180300c000c0d82410306c0344410450600c016206030009031450701c00c0821082244824a921458880b4128078001c070755a43e40350000380040d0800c0c0c025000320340480d0040070400b6040742d100b000034a400b4000b40207045482e203503000b803005030b4480d02d401003840c124000e00308003110103904050403605441440c00b031410a00142690700074081d05010360910b890781d20041c54159400710b92a540000244100800034404079855001105449006a03c7c840d0100000b4102000783c00d40010650f41c000140705d07003c2d204031106c3d00d9403444a00414114051040c203992222030981e110800b802c007555220007980007008400000348025200794404600300720b2040d880c1124104032401441192a50795 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 670235134 1250 670233884 670233937
    0x1c0b0909010903052215030c02160b09040f0b040e01020a0e060c1c090803070f0210081504020307140706061401020f0718060312030c1b0c050f0a0515 66
    0x2210300002401041060108159203c5d03d072145a0200789140801c40500ba550030344520072042c48072003e4042612040c1c3e40343c03070319810044c1050719008030440c0e624461401c40c1c0000b880c0301c1c041c5094040c6864200342010b405a80c1c0104070307003042c054020810382540d030000c18000d401c018000c00c00600b40280403011803610f8010303170304101c0b0288082c02849031411061040750790301d40401c0c81070003140000000c1c2d0b10010b02c05404440d014000c0c11594443c684104500b10808800c03010511070418107105500e50803209034941e0fa201a100180d60762158241a11111080e50814810714000600f11080040b41e40000c801c88240ea0503140c4040001001aa201c4010254074030040c0c1c0904c2c0c0400068a514000c00050300c0082c2001490584a0701e83e003a83c00e5401c000100426216191080010382c4100d4038944d10b144103109100402c1655240c4026540ca44a40f901c1254800703c0e080150ba111102c14004120007850f1291042d895203240c2d070380782c00030451b515406519281c441540c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 670236384 1250 670235134 670235141
    0x2011b050a03091a0a2c0a06020304030512030c0a030e160305030415030b01050a1805060304060507142704020c0d0c15060303090e0901060b0a092d0b0f1c0b090901 72
    0x8542c643c42d03200440817900c001b0f982d106485144424510050031000c07600e51180305440010b04456409503588500b10f0601510382544400d05000e10001001000115140703601500c546000601d00415064201d44ca03261504008004038003002490304400400c02c0701c0040180103c03803902c8083d04103807404a178141d040300d2829580a011520401031191000d1240401080e1600d0f1401c4554100b920b030000f086040d0030484049860a540d5002e11124a40210120210b00381521003203103404400c40400302c044504c03170808080800644241e500070f83e01c075010f5417400d408600c1201c8020111000060104514a000303890000510f1480505101c050196101b80c9815807203039401c8a1801e00000030300f440c01800d15110717550701d03c000f0078000b40f070100030044007499540e0b01c88514140250030a030720140612a074000e145060450380c0100740c035035032182120303000d03800c4c00d403030300046402003400744a0380342102104054070300e41c69606400c950144d482e030042070380c85031001d5640d005c04900300c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 670237634 1250 670236384 670236397
    0x20601080109030c3507061805070b0c07081b21070b0a02010e0d09182304052b110d020c0f01030216050304050315011202011b050a03091a 61
    0x14000c84000001c170304080a8446200c40d4405105450300701c2a5240030030005910079004420800550001484924060800e81264110810941d4801a41c40c01d95504041c03185030300c0fa20f00441e061520010505c50340000381070002c00d5854100c090720709a1403864500742200d1007040c918103610204010b01000300c0c58401d0443c0101041d40c2003000c0306540b50030601c2e10350110364817210842d000b00018405100d44281b01e0719160700244c10070251280220050161602003407a104541d003010079603040d0913101c43c0c0d84050065050b1070f00e080082c01d00182d00090904080d810340c402c50001c46040b901d081c03c1d4520794480c155150700e4103607282c584050101c030b60016803007102003100314601505042010358050400500d4802a020700b1080341e101c2c64804e84081e040880c081160b03040500807029050800d110b40c407050340c104505004462200200a070400c00306040c02d64124007050b44c00b06a058200003103039075910307551400422082c1140200317030041c80c4003010001c8406200054130350 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 670238884 1250 670237634 670237637
    0x1060b04060c080f1605010606090b0a05121e01031103070b0702031506010e1201020403021905102616170c1c09020402030f100609030b0c220602070602060108010903 73
    0x100411142c842c8400f542041e010b040001c2001c02943c407142c0b81e9030b41c160002034401c000115007a403801c000905030140641c46005e159074200100c0180a92000840d0300c110015003415000e40c843c0607034214a810f0007601001003400910012040c001c10f40344d8003d1102c411000c641020361176407031800b42409041402500b550000952400fa5182e019101d82e201e80c041c5428400680010009550600e4a01c403c078810307540060103005600704684505500040c8000038603900b403130a00841c0380005139044c1842000201e600d0b41000c825524810640c5c1080c03018030100e6030401948032000b1a1120707600d140803c0d11803040c2000301c0c0c0142c29540c41104106211030504052400464030a00000c20080d1421783d620102c0c40180e035244042d5009510304d62010340145844c03071003040c2c100000d40040e014001841ca0402c001804000c0d8540c2c00601c1640c0d40e031300c8030344000400604522009440c40f01400d0034401180442c0d00040c05030403501c02d9802c0b2900761342e072599098200e0b410f0020280 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 670240134 1250 670238884 670238897
    0x271203030b19060c030e1e010518060a1d0d08030703090f06110912070302060d0e0109020d1101020d17040303020f0f0a0305101d041b0e0903030901060b0406 69
    0x480c0c02640a40405040900240b0640180481c0411400720303a41060000ca0400c3c4a04410302d40d00002028102d0350a540030401c403550404250600708004140e18104a00020a8141528a4410841c1c0c488000c0e2009480e40ca14140103880001550781d072031100e05881010811034941041e03030190481d0420300709495600c2d01c107401c80c007500540d04240ca01c2018000c030a0000b03101c42c4581e80da520f00d12100031b526102c401d0b00304100b0610107440181140d200c19810b0025030713242c504544c00b081c02c40d20001608100085018090a083c10020f940082c0018281c01400007000a803403014500340d00351850080c5400040c2da80c03010b0a110759544e501181c001400083c000c1e4018044000f42400c038a0611a0510200c2d02a5110521141c0025210340900c8140d103040d004200c042c00e4a00242d02800f455802202a440001400035200c503990201e00a0044950603a0354080c040305000591a03180585400780d590f403054414450f6507207041d10004011040c00c0545041d11660790301d24 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 670241384 1250 670240134 670240169
    0x30304020a0504230c0c070f080d030f0b06030708070206180c10200708120a02030315190e0f0a0e07090c0203040e0106030905010c020606210f0a0327 66
    0x30000f8289806440440d02014104c00c909020343c10845100301c00c11150569240c2e040a4058180940e03036222406030700c6251010322880002080c9a0100f510a24000918641440041010b40000c6000c50f0300143d00005020307450703501c861803910a070b11079002ca540689a10180002c40c0728030a10880007034020034040d030521306c1d00c00c480d903404082c18603110180382001c002101d00d0000846a25840f0380c0009410426180f0034492811b9810b100003196081122400e0041e40b2440002c0c645000013603803804840c0140d0780c0507868100c00c0c10320441041403c0c1c0307400600002500c00d54009038210a91800580d044149000e0002c605104c0005001200c2c90001c03144068804003030010250300042c400419041907205526000b022981e5000c01c00c641d00c1e08002e402c641000c44000119003000c02004150b0302c0b14543c1c0c0507140c1000e40c0a4900807200c010b05070a0440f450780c150518000c598400c011305078082070340d201c002d0031782c00103019152400301001c641002a1148424403402513204 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 670242634 1250 670241384 670241389
    0xa0803030109111c230c070201270e0405070f0e06060307170c0d0609020901090b07050a05060f071d09060d0804180e07060201050403021f090203161703090d141005090114060102030304020a05 84
    0x2b00c03500b0003180c180c0e08003800c24842c40e141c50608150401c1480c0300c550b900300020b015003003014a00910021040415450801c40442e00031080240198050900000403d544c5071140303004451852441c0408030060604007455800d60303100b0071110b01c002d0700301640410058418400c0b1040e150050b140c80304403030300c0e002090070075820841040d107950240706030bc0004924103002551107480c050280c80854a0260005818031401c0c0c1150b000b0490860042221515105070a03904200c0442d40325020324418500320400b40700719000070000c41200140c0b2503021129803c0000e002d043c050540c1c0125484a104900301c03441102d01800581c07002074100312541400c4540711419004103800705922041d40c0119151003401003405c1d00c89015000c00304903509041c8111a00340d01c0c540c01075807424040c0c50006092200044e00035200c10540414504162000c01c000703039420705100c0c401e1141d842d09440c854001c2c20009688440c2151010000b0240e44c80031003101d2080c0e074014200384499080006 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 670243884 1250 670242634 670242647
    0x1204050d0219081c0f110c010e060c0102040b0406021507080c13081506041805150c190c020f0a030305031b04320a0803030109111c230c070201 63
    0xa01c0c00b1902c0b510340e000c9000081400700c14201c810f03441144452a400c0f8070010203442d02e4211078401c004048051a02041e03020450601d0708109281400744e8450f80000140144075420f842c6413607610015000034072040e04409402200c04e0f68081d107005a158420058601d0030480d900000a544040010120012000074100e041408880d13030581c652640001480c04010f2443c5041c0d280c042820482a440c05000d410b05d042104121080002c4256645594070707900000745042c0004288001100e947c0c0120a481000b5907107501c0800001008034090310600040b00306901800f000440c02185081c03012a44084a03456981c4501d541d0300e810351400072558070103030000d102c4000c000005448400300c0044010000040741d46415805400c025645240740b45c2001d0302407280c4080c104080400130060380d0442d1507064000c5456010507110070003502c14440342a14020313903642e2199a451403a03000b04529003d50803100c0d601c4a60312002d00d240c08045510b40c00100c004c104507401540b0940 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 670245134 1250 670243884 670243909
    0x10503010e0a020a0c02040237051c090611030906070302040e070e04060312030f0b0301060311130b060a0914010908030a03090309050604122d0f020d1b06021204050d02 74
    0x580101c17a8003440c1d00181c2a03074032179408404a801c4da01000c14035002c1040317018088402d011135844810310399030405421402180d180c01c05005482e20f0004038a50190440c0e00740c0d5520440c200642d400301840c44c00240c1042c0c40342d0529110b0000007501050003482220191031540d400c80c0290360340c403c421038440d10072070200740d040354a441002000a60300200103101c8030f9240c41c0031900956060117030f000c0310305849009100f40e0400f101040032440310012900300c039030207860607503004c0ea02c0e0042c1da01a1107203845032a00820009003410031142d000c80e940e01502c005040500388840317000011545003d045c000e00f8042d410402140c030110340240d0110124034031034100344400350355480010781d65401a900140d50030454114100812a0360b080000456030032441c55149d00b11030540d01c0408440d410801810320004440e488190b54070860203064407540403082e401140346a600c568803000340c1d840754202603c40c900c4010740c00403003a401d5800b80e45000c1c100a95109071a000c03c032010701c03901c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 670246384 1250 670245134 670245137
    0x100e0a02041a0307051e09030d0306140621070305060a06030506130e01110c0c0a23240a030902010f020c061e070f030810120809011d030f0a050c010503010e0a020a 72
    0x41111400007000b07030207074040111b204404d0a403a150f080c0c0c03d25003000a0300f1803400416251180c2400f40c0c1d440e680b108803241c10195400754884821f06040d41c4800400e40e10380c1400349060041041031541500014820a03081d80c071400865a16102a01030354000c0d180260b1181e5025001244a9140c0d44502d003603c0301ca030000300788580c040320405200d5104890b20403164104808402c4107091603144000144801070495009814080035041c80369404c6820f41d00c40c0701e400b01c1c101490421401d40b000c5a01e0b011040c2e90b070318114000080c0c002c0c07510980480c0420b40c00e40c03d100c943d03400414014580700d000b0f0046450606c039154802c45c03007043c241c40021115014001a008641d545645109191198440c098075007009031705c007807080c00190b00c101000f0ba00340b02204002001c150a5401281080c2000003600002522401040c0401c40b8a03507090f120348041810408030001e6820300301c82c0079070191030030410b01c1d40045802d403209000385101954000042030612a240e8020441d00103d03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 670247634 1250 670246384 670246387
    0x41203061d04061425030209041d011a130905010e0d110106080102040303090e04030c02060c010c0905041407111005180c0d1e080d05100e0a02041a030705 68
    0x25591114a4031041c0405820624040420002001540d00c501020380c107000600b44d00601c0e042c10004011160702802c040c06040f00100000f02030300a8059448401d001001407041442d82152583c81e82100000303000c0c65800d103d00d500e42c020010885034803214000d424141c000030320a101401030071240004032160741d83c5101c558040f0a082c0990641101141d98511820384018001d6096680030b81040f50943d00c10003013000001d4101c5841d0741156a280d00030095950b4906082c1d401550140010390010300006007404001410340c08008012000d460303451719075481c0d40600044411900b620303043c078480700e00403d2406024200162481c906041140c1c0c40511440d420070507a101524a40f483c9501c002a00180c41000d2052404145041d20385203621100780d101e140143c0c0c41c1d40c0c0e0012071200490541f1003070041c2c2904482e0142c0c0f0b0303a030f011721007801c2046110148421904c40d504000c1c0c1c04101203082c1920b203000315021124041c524502010818912421aa1010700310b481071140 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 670248884 1250 670247634 670247639
    0x9061c05180715020613060b0901095109020c010f0516020714010c390e0c0d0209031b030c0102030a200703080d050103110405090604120306 62
    0x4540500d40c03084541d620885489041c03640c1081c580301003030b003140050700409000c45000950000d1043c1c1e00404c2012100e44032162400d01000910750000800d42100d40b89001044d03000d49900500e040e0001011146410708881c118044070300b881400c092104d0400142c00b100d40c8000e1414075803100302d020f148400456403411000220703408140b100303d0310b944803450048544450702c50140c2c0050405005a055000c98000940301c03075079400344481e11a980d0b504925282d00c1003240110850748005902900081c02c441481d0b1040e039082501d0450058140c0c180841c00c114a000003221100e018a4840d030700ca070501080b25820141619001c50382c01c0c402c803409503408004601d0303550110901c0d001059008002d040c00c02030802c00304c50565104101c08440c2c207500c00a4410b4003c0185400241d40c130004801034280012544043c020f4003020400c440092002da01c540e040324422110581e03200c078200184800d07240100c41403801900803500040126081481c00203400d0224a03002900d0b64 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 670250134 1250 670248884 670248937
    0x90a050f06120103151a0105071b080d090807051f0c050a170c010c030b06070303090f02040e0d11070302010f1d0303030a0b1516081c02041502010c0309080906 70
    0x709074802d90304141c0d03008172001000b56070300c11104241d90f4103d403a484414010300191841c0b041c40d40003800d0142010000d90080100c08030320b8041c180f075201340c41c240b03080100c0c001c203036410714021520680509900003c9a02e40b030340618901008410701c4056125840400741c1d681581c41e01e090303810740564030f0310702c0000b040c40040c0183c40060300405501c980303120400e039007180c444030844800d152501102c40c80d242d551a054500c1c450381484c02160440b4103282c0903000317026001000350428100050b424a960700421101940c030816580c1102c0401c240308016682e209910019001c1400803260140b003e11940f8181007840041c000c0311006240c00010a2956004807514801166542c5140d034040c43c1c04c03070100251030300c4509030130b041c070261000280051400e500d0080070803400080c112943c07540e074910261044100e0908540b030700d0b610342c1c00100504108200c10015407030008030721302260107441601b24140d044507030300e410044488140300099020100d000070b1000441146810007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 670251384 1250 670250134 670250167
    0x1050915012d091413030e0f0d17070b0c1306050c0c0d03030609060522240e01170109110f040b030a0c0f0f0303080402090402011205160206090102090a050f06 70
    0x81025003c001420030342c2c200d0340d10703135a000905080b040055140d8a5800300c0c0d480320340a0342c50030b400c0341c817540c0807500384002500100c866040141b885020b0820807424003030700d001914001c0d01807d100d140540e502c81c50b2001d14030403d069a9030740801120140103051245000e04007020b005000c44105242c41c80001c2c1a80c504e00308100c0010751900c5d01400300b0309041c0241d50051106075000000c0c40d01d0800924481a5855182d01220ba5605280031108000641140700507003103181c0c0c5c80340d02d034455020b006511002d02840a8031514000c8078030440b0720503c1807106864021a206035030301400f00400000351813a4200681c410785034020070740720707030b070280007001780188985008070005252001c440000351040d400000940c40207102003010176005007205d540b084d81140e908019540c1da02c01a41d0110149415118084c40c001c100005444a4140344a4054180d02110081e03502c00c1c080c503081c0e01c1380c08070281c6c000f40e04200400450601c0001c0e0202860000d0480f41004a1142c509058 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 670252634 1250 670251384 670251389
    0xa05030408090d1506030c08120415020c1801051806010c120504080106180e0f030703030f140a0906140618041505132906010c0c15050a0201050915012d 67
    0x41030ba8440e17007001003003610807100300280101000b03005000c1c90f055942e902030040b4890940a4030780240c4141003d0700c280007058042c02d00515041280c0f00d04050090060800d0141034060004040921181d076441c0e00313110321407003050307560b241c0ca05002c4d9502e41c0c2e04050f0726091828807905000200e08414203000c0d04018225a541c503071100724141c01444151803004c180040c80d904402d030300c0507012902100721a034031b41d014140480d000c410402920700030304074410000280701100303050080214007500100782c05409103c051120100d840c2e0019081c070720964800b6441055000d800c443c00a01e541c28940c030034007418030b580031805045040f43c150b032011942241c41c50f011411600412560390881400c01c22140300c1c520240f107210515101d001409000b403410f000142d034450703081000705c2040201078400d0500f441c0c420741c1441c0f800381c00c58010312542000f6509010009140c40c00000307a00310300c06070b07081c40c0402503407034801c1c080035103000268550075070080c0d030342001061000480d84100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 670253884 1250 670252634 670252673
    0x270a0801050a0c08060d080304030516020402070807050d18051215011d010f0e070c06150608150612150d120f1e0206070f172a0a05030408090d 63
    0x980e880300f040010a5071100410b00c034440c0c414042c0c00c0c000728620340e003540d602c1503041c20b0090740d0b480f41c403c48030655140d41d80025030003800028920304000100c2c004e454260b00c110112094101441e6082e80d80039880000e60b500e4004050003081035250040074621480000b9051f2040e410102c55107000c0c1795000d0b00040c8503201c1101c8410400e10300c0360141c2d4010b084d10f4490100050030b008c804141d4000103407404042048540107001440919440341c40744c64400b8039905041d44d035401025042c110300700ca2800d42c4d6000d0f03490700c28940c205801116501c510003405c28000c1d595520481083d071003180314050b0040e035001000303030001ea41d00170340d00c031810840e171a42215108085002020080014003101c001c3c41c0b041003c100e02d030740000c3d00b0390300110181007500316078111120848007030020408082c030121410060007001c003201050050742c050026025444c1901030017406c0518403a0002000026404000150208840e400680a021801028210307440f41d544c5466466014030701640f603 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 670255134 1250 670253884 670253891
    0x1e050c04090513120f02060406051b07050106080f030c031c1e020304060c0e030a0b280e010e0c0112110706050c0306130c23090d05100b0303270a0801050a 68
    0x402e0000c42c41110036a00c1e079529160b5170b00701030603100130f44985001d00002d00c120385850104903055080d01c0f1090740150b5000b0300c141c4aa2640c100350b406000d007031140004601503019081880711010040303610b4150050011413800092890b1608450741c00742030301c14142d80e5083d1508102075000c001d407001d2000b403003000d070b22801d25003009811074000f00f1700c0109018000401c1009502c0200e0031121140d00720402d5045507403a0b021815100e81120092024400c40110615007840a980075048002100d002045400c070110031150743c0c0e96000552a01042240000270780c1c00400d40c100c49003c41b40c04840350308050f865540c1c2c00c03e64609454541d030a2a02204000031401e141c010034610b1181d00205001c00203980030f000e0301500da907412904111280d070300c504010300f83c0d1b44c3c11285e480e40c001d0440c04201d540d03401c240b51240507114640c282c031814081c00c045d05140000544036503000204400700403103d020b40d0702c1c2515181c030794001e030002078480d40090580300a03c100c038400e408104010 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 670256384 1250 670255134 670255171
    0x100f03120f0c0c050f1908010608240f0c0c0105100302040b0a150f030b031615030b100c021212030a0b090c1812030d1407031e050c040905 61
    0x54902076180c5200400c02069200c94070110f1840360442d0210b80054940303015500040d008a445d4000124032109418403000c00014a8441540b00030219003400080d1200120a1400c0003200c1055101c02104060f0400105990b0b00b203243d2b00a800840d483d0b40a450300c01d10420403801d490f0100e0b50f450708100c102008100f541007078041d151031071308110340c244c0419090820041c1e658210480d55003c001d404030f80004540e003c4e500494945e41c00604440c04031040020306403802d84940a5800c84400c02001440304034040d002e03000b01d0090042c00311404414825044070341c80d5003c100bdaa0003214000e8080030503400f84a21034441c5420f0315060b54920b4044180002c2d03c5203049070b503004000c04020002a01545020b50b15144091b58400815244103000141d0b65060044444601d01000600309000b10036980305220011060050864546e10071a0a0b42107400388036a552106101c641001049080c0340d01c078550059449020320f0615850780104011140219107202d0003e0440443c2c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 670257634 1250 670256384 670256387
    0x51008070f0f120f061109030109060f0e03040602060606070825020307060c08071b0b030108010c0207060c030e01082e08120403030c0f020103060b0d0b120c06070308100f0312 77
    0x21480030b00a40a0b0026680e006641e480f0910310310743c040900300603035a0554206d40b00031b0134100c0d003000130010000c0c4212036103070400900400e02c12000c0150035260003040c2251030717008001e96003111b41d40e402400032075071a1401d0100c0e55000312011940c041c810040322003503580c0314040103501e03024180b079040c40b0710706031041c1458201d071071b000070050180c18400d0800181955080301d405980c0b00314000d045251401c0580c02c0310401d81c02c881f07000c07400032001040d1110150310003c803500d80f036800c48400e280d4420040e10021004a40079000a0143c442d0b40c1c05540280c90290300141350304052040c2440c4801d4a84150081400f8842c0840d100401080a0401000f021401a0001002c1c0d031a0030300e5554080d10800c4205130051a00041e0344842041d0fa020340e104500901407801c080c1d94504101840754000d001c40743c43c5c60703c03414084001d020740f00c100040c440ca03d402c010f4101841d2603030945082c0c60824008002a40219101c1c0f80451541410881305009501c0f40881c0065401181c00 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 670258884 1250 670257634 670257659
    0x52a090d0b0402090606390d0f03061509031101091e051f0c0f06111206090a0c021b0f0307060320090a03080304080d090c0503070503061603051008070f 67
    0x2c1d803280b40107100300d20b80c03d80b002840000f402d09020300c0f4004920a14112280120030196500359402103c4514401507008040b00700089018ae504015603900c1e12141040500e1115610300000d80782c810500010f401e441e92840030784814107044540c5540c030498141002014010300400882c4900100301908105a0700c403010042d04404810044000100502d407100400c00900042d02c0c4440d0803061207030a40c0b21826188010240c160350703a045800000c1c1d0001d00340c903100d008040c00400200ba195162007034800c0f2201941c040c1c800c080b1030400d03404518104020696100180c0003114003243da04010160003050030342c034046071202098200301e0b448a1710f140c807951504001c001316550f07a039580501c0e0040c1c0c0d5010200315266121410885140c0c0074003400c002d09035103400071110038407188030b0342002181c4d02181103500c456140c1c810701d612000e043d00e000c407100d90301e88000b8007075a00a41002d0b502c00034848111410580d12100b641c40d1091700e500c82802e5101c0340758207021456031901c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 670260134 1250 670258884 670258891
    0x12090d140711010c0c03080406031a06030f0136050405012301050d0312050405070302190302150f09060f0a14091003110c070e19052a090d0b040209 65
    0x64540d06045960b00d505a076039050103085810442010f071407000308000307022024042d540000c022610b5503107c0d000500100040100c102c4041940101001d541c5040c00c1100e1245004008100040e442e14403a510307011700c8113080c80c3e40d41d41548540313085000c10704001e41c00b01309419804101401d180c00c2c8203085580b680301c9071281100081e00d00d0142543c2d21001d9044032004c0e505c081a10310941011541003144841050846042c1b41c28041030003000610385054074022140000c2c0d40e416200c0c8000a50b45511000350000c602c010035481d0324045401170503282c40c10b244a1441c011010740020007030703840040068529800800d11003400e950140c1e294610403500601d007480c040d041c8d000560200b07910f900500826488400241c440d0320f5803000d0f0b0303c5842400d82104d01d4144c1303c2c041402d4000d42182c01c1a1074507502012610707031030f0f041e001d60340c02001c0c19081c030010b0100c0c015030704039000e00c01c24003604851001c004044464850620008002d80038196000441c141441002021007000c0c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 670261384 1250 670260134 670260167
    0x30b01090525030204050a08030703020d1b080c0c1017070201090b0406050406140109020a02060a02190f030908070b18011e1e09261305010f0512090d 66
    0x1081000303a100d212078040082c201401d80d90540103034034408502900c1641c0241d90820304070300d00021510800805000b4440c401d800355089035081c0d0508a4412038a44610880800d515200d20049881079005042c0043c1c040150341d48000c1c41c001084141175403002d50070001320513a05515000103c0140345401c800c01d403000780001000e03030321001c070041030103030024100c580d42c0d8000c90200880340d0322406100030880c80300c403542d60f0749490100003500500c0d0100d0140c0941800118803800a1089441c041e120320160200c01da2406001c03600508100e418509050f03480074001c000c25100c0024181a03403246040d089685040d00d581c0340710802c1610200f460f40e0600d480c0400490900204000c174081030070000550103a0340c0c10410394011030303038040c0c60a980303010340890501c4400851416204034024140c1d010f2450909400c07417501c962281d0a644024000060110f58842c80345848968000c0c038005003004981104030609a1080d50803402d40e60044029514054018040a0803080032 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 670262634 1250 670261384 670261391
    0x9170f042d0605031003060b1c0516080a020603072102031015020d1434020321030123040f09050607090302060706020c0f030406020d0816120504020f0607030207030b0109 75
    0x107012850345d2807951b010081c00d00703444140000c620340b00c99013855401d03a1022101400d41d2141c1c00d2060b207a180303000c69071120034642c0c003000c98252800034801006940c05404d180c03555941e01412903440403010402c900212180b42540302d210702900145010300151000c01e070703000d40f0b00101e2810307030850b074110001590050140034020580001111410300e020400b600d54072000c840001124007451000c2501d1400c050740c0640d1410840c80403c6d886a200f44d00311a45032401c2007103004003600f41929449032403420801400004110716071902110542c0c0900c18000e4804000102980c481160182c04035070b46038038000c2403160421203c0c0c0c10031014203003000400c1c11600459000d20842d42c021300401d800180758007020f1410400010f080d04040c003602c0e1079070303160100203484071003000c00d1038001180031001c161907501a0a1242682440352540c001c4041c12003141c0000c0c0038000c0080e40d000e8034403640916140c807a90000d1454a109070302905115041d03181c03045440d10183c0082e40900d24 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 670263884 1250 670262634 670262641
    0x5010b030a05250e070e01020106080d0e0301050708160509040912020f1c140f07020d08180609010807030c1e090603060803070503120c0c12070201030f09170f042d060503 75
    0x50a00136001045c5103410307920b50100b0390060340507000684c0048076031b1007144161304005501405100701244100c000b801a0388400300219040d50040d528030000300400c0c00e03146074450150004043d0040c0c05080840d032240700d42c4585440401c41e003440303800350700100d10001285006014880400d038002c9001c0901c1e40040b203000345a041d940e948000b20800000f0021001d002e00b80c291180b896000b010102003810030303c0c200180360070201c0c075908581e4005040b001e01e445c1000694407485010703902d4000076a2444012801b40104006d103001340302c1d4188500f100c0c6503481c549002c088a0036280d42c6910f03441e20900034200c441c240d00c45030540d001884200001038000c02101c04249001840d1629600d074108120750f9403003001c09c6a0303201e11a00c141c410002140c0b00141842c1130007600c0400c1010041e069130800e0700c0344003d00800c00d450603070041c1d080350700c0c0201906041c0800c001817401d0035112104601a031500030004400441d445c101d2084240d25503d1010241c01c0d50300d0200d01390309 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 670265134 1250 670263884 670263899
    0x41218031e031403010b040302011d060f0307051e0901090e0f040b061309060605090f13032105010305010911030d0203030f0a090b101712030a0905010b030a0525 71
    0x5464102044030381d04524103800a062048101d4010380710360006450356943d40d55400c2001d030f846840108e011440e100ea0b2541c660b01101c01c1510314140251005181c0405c0000d010180c2d13000070000e40c24080c080c4510b0707403500e0310f02246060f100b11103800245c1e03030210320700054245d06680e4424607496014408002e40d4400168000d608242c0c008001421922104e0014500314102c000704800240392401d4501405602c6e04660116001541c03000c1964460b08081140810103e803c81c4800c034070000d03445c0020340b1035001d030f54561041030030140d0205200541d0000347c0f0302c00c2e8020344090303441d000300806000c5000000c02120108a0003006504a8400080d440c1d00009040018100070107000400070f0b0880d40020784001e070300c44070101e2035180200145100005900801052880b1000301c00e841f00c800244555091604040f094103503a9039044400c0a040402401c658554803400714011a4804008098a243c07007500940070030403440d8180070601d50014034840e042c07141228100b0900 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 670266384 1250 670265134 670265153
    0x6020c01141014030a061d060c1312240621171314060f070302011a030102130b0d1103090d0f030b0a170a120507060e070609060c0c0e04121803 63
    0x360f10150109050642c68080003180d1a180811f5030b09002d110f0030480750311070890040c0060030404070165909034440221740c2408100c0c4c180205001c842942004600301000c206009180312a0380110391651a190302d4111600c0c03640d0070003549943c21090104000c90b020500304903e5012522605054081e0030900c0304015610036041d12240002c1c100c0d0490300c0d010300f1511001c400007d515a110200d1400078020b00d03150603a040d0600e00030300740c180c0ca0301d418000c891f58800c403407401c920201d0030403c0b110103e44c0700b1709882600301c0c1e8605545086101c04001385204164110140241c0200307804064600e105800c00101003610308810034025680d240e400303c0548000c00003003100c1415165440d80ba00300c094001402d01f007030f08403030b15500984c020014140540300d0503080c0f0403203000141c642d0741c07480030b40503110124584040900c41c01c0d21640101c1c2c18240681840d00203642d40c1c1840881044041d03034185d613259800c181c001e8065400c41407495081e188410f040081601d580c0b100c4491 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 670267634 1250 670266384 670266403
    0x111120a020102301602070306051e06090403081f090f02040f0905010806010608060f2830030504150302030a0e0309010210021b060c040608090d0503070c06020c0114101403 76
    0x108242200b0104946c801c0122030040c60303006800300142d00b402402c6416991141c85a20b503c032406d000000e80030700f4070102990141e58161103d0314142c8504001105034800070340d0302c0f020411988400140c1d03c1d0f8600030381c0400c8035140b4005907554100300c510b40389400345070030542c6c2503800c26004025182000030000e044480c41d20703120f402c0e625040000b420311203c14428607409030301e44110400c1010060f6900c09a010fa40368488900303030752841c540d0340380b8810b0341a54990a1075031049410540b00c100c0e030b0f920324511034034049140a840340400d5881c500054103403070001f5804420400c840c0498800c88800304c0c0c00c1c0d80114100350190000035582c00001d11000e203540e4001c20000416031208060114a40d0318200303030340c8d080c98040d50741c10040e00181b007400000307a00400882d01004003c21040c00000640d501d0710719540c1c4001081c0c40e001b00000e03080304c03003e40c2044030400c1d0708400e20421080185004140501d0b0421200c842c40d492040e4015501d80071041800300c10365600001e412702c5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 670268884 1250 670267634 670267651
    0x7080108100b0105090d1401050106020d2a08040902180409200103060504090b0f0c040f2c0106021c0806100e030a02100807030f060b07020111120a02010230 69
    0xb5800142d000485250043c100256048008201c681081040d0310010040e4500d21200801090307036101c01c1265070310815000003000c079103000e401482e201214141c40d0281118038001d207200e08010394402d00c072075000d5070160303003410340c0460a507080302001994030041c00412a02403045c1503203619440718944518001013000154030151850990094200e00d0040100038410040b0b5600d81c10a4503d074030341190201d0480030008009482040c0038030540d070648142c140142c041f181490102c96180a0781864103030700c500701000c3d403908509920207035806000d2036809000c07140b007042c42c216548050f03194100e05000ca0f0384200816a125050349218030f0100e07180c0042c03070f20b08000c00701e41805540702c000794201c4080c03420244038980100e851402031100c0d0380c0c1045200300c550908804ca840c0343c000e540701d00c0d074104031940141d03108040d82030400700b4900540320039842c800c0c50320707906600c5058400007603500412140c3c00440c010800b610502040301c4102d07110404000b0a0380030900080c00c25a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 670270134 1250 670268884 670268891
    0xb030a081b010b1302090a330e030105010f0e0912090d060e01110417030c0d0804051009050705130e100c05040305030a030f06050102030c0a0b07030902150408060708010810 76
    0x6a003d40000490160140000200c005020a00710195100b04081070141d6114800002c100e215004d400841c209000d01030a1a56080c90244080b051740500090811240b00940000340c1d40030300c03c00f8001c01695180401c940d00d041e20491306080010100c0c00c007a0040c00704e481ca115604001c0317941452003292109860031961600000420301c03841d86007042d42c40c0c444040c107000100e800820540d1001c252040c1a505540d070072981c0c909c00e07007030400d030700e6080a5083c040040c002c1013078a4000b4855004e44203180100074500c01140d0b0710b2402520b0f5580081c40800141c2000a06191128051a028001d00800c051410303a2000301c100f01d19581903503840600030b01031003541503501865011080c1d070303680d0728416001005004046070081c3c1c401d240a00018903580000308543c4980da403440503104a000c6a16089499580208008141504c554000f00107a4420400c0b0010700118024282c8030703410035646a2500760000c007240140400c0200605c8541e80010b49044d50205450010 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 670271384 1250 670270134 670270177
    0x6090d0210020f07171c0e010e060f030403080a05060f0307030f020a440a140f0102070f05010b010f02100903050d090807260d023007030b030a08 64
    0x4a1802e43c0740c440002003801800d0b40412050310485941d0000c96a103003c84000700d40500050000800819280010850304880a00c0e5940180c0c0c0700d00038454010013180c180004004a441d0581c0100c0b0700b10005421042000140005446060b40204003501d01511240d55040440e56501407800302818080e10b511f212011943c55540240c042e141c55000e40c40d00760600c0c456200707000c180ca49001080c420312500300e0700c051b20740086103840844200060084e04515158034031080034802c034001050080d01e0294401c074001740014001c5511a103159240003805051441c215000b003003c41d41003162120740962003980c001000051510821400a1100014601074825110b030b010755401032418428007505220f02280508a4203000701010002c6c035201e2160300142d0740511200c001010414044405075008584c0680500d80d0f03a4480411142050244102c01403081c09000e03045450703200800c85d19640c54020710740d002c68250000c1c102c106041e91580d450b40900c42c884d9a01c80070300b9408 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 670272634 1250 670271384 670271387
    0x90203014a0d091d280e011e0b030303070c03260708340c0201020307020d060506030d02030f0910021e010c17010312030905100e0303041106090d0210 66
    0x100308a90340303480c04032100442007a40141024540380301d044440300a403036070a142c00718008a414840c17040c224050b0b03480c0c5400c41400e0f800c05903805018500c41c0e620080294000c00910540c080b02e40710072010141c2e8519842c40d00107844040e5001400381d041072040c013041c1d5400a994641c11076242c202180301c8904680c1210300c007034070075214a01b020300300d000348450b8a4002c481240034441d025550b0b009040e408603480c0c024401d429184891000c8050f0801d14a07108103112012103205106803868104241c0006506643c0044196a903e540c0d00c248501c5180800280505011900165040401d8080740307880e140501200703035015140008202403820f00c2444540306180c03640b51118040d103150380c4424020420504c0c1c48001c2036039100714000c100d20316680903040302c2d4232880580040f00320b290110050400004110740701e210344001800001400d004d60140490102e008680700e1030142062901542d1f400c0703405010748020085842d19840d4481280d1880b9010340303803401d405000c50300 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 670273884 1250 670272634 670272761
    0x1e090b09091305010501030b060f0603040b071101020f03190b011b02040906020d1b1b020307030204090303140a0c02060c0304152c010f06080c03030a0e0103180609020301 75
    0x60041055280030001f00405c17903000456030042e0401da65280c41c600704074050000350b210586000d044004564001a0207910610824003001c1c8a4000542071020815081803982c2054990750030444469441c01d0040381d452086500e602c100346480c440c2c8081d0101d40c3c41ca1140b00ca90040d00071500c0d40907040900c030864048a101304908101000388400e040c203001c071040941c0d860100000c07010780244461150b409030380130265400030f0180c41843d00d19400c000040c202e0110440900d03444946032504003080507102442680380b407102007403035001ba803002401c151000f009846414801d2082c840420000406031481c9000c040b0b0014600040071580c1026140b1100301081600241012060080041d00b010612859517407041c007030ba98036070741a140c8502c211005079400d42d10920126480c54441c0007043c0c05a10103040000340c00e110344141c0b04004c50320101c142c600e40d80700c000340b2045050034810301c070503d01c0e50044450040c41a41e0044440d202d81d40410074207868180408242810404c0c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 670275134 1250 670273884 670273921
    0xa0f080901090c031b08121206030a0606060c03020634030e060c120a02030714070318030b0f0f010f06050d06051f021002071110050c0d1e090b0909 65
    0x101c07100f522503501d2030680f0001074550803681805200001c0060b8002c00000d259109070000740c1c42508102642c00c5581200b03000400d030341c0e814400c3d1054a00810f540340710f4640906115030350104e04000c3c1d130402a14103040175000030b20707018121315441d0002558804030508180801107203400088540e80032005800302c11035400450003031105010809000c3d4004011003074a0941014041e510003a04000b24081100d561000c0342c15200a520101292402044000d11a08000128540c568403843e188a803642040310054814024840c03210380000c58682d100b075001098504030340c10484508401700087c89440148500820300c6080b40010b81c00c090302801024101c1181012150b14041c5140165200b0401500500d541e0b92140d15060084840b07058000320840360240e80304e0140b214040119410408012040c800410105011f0007070b003e0f84515176a4401c5c240c2003100540c2d00004d211500f2005002c4007000400030070403035209407000b11600310b804801c1951200e641031a4641c42a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 670276384 1250 670275134 670275143
    0x31003230a0b0c120702010f0c05071106030415060b2104110103020a14030a0207020f100c0f020103470904110a030c150215011404090203030c0706030e10020a0f08090109 75
    0x4400c05c00c10300c0e4158007400c850b000c400018440401c0c80e900c140d4003403168080180c10032120301c0d908189828810002e58100c0d2140019040488440707850b03108440858211110b220030000d1155016a020240480316042400959845081c25a20a440504e001e8480342c14540c01158071040d55002d64050860f07030707502d00c50555880c640021800001d601c4003038100d1082c4000804042c0c1c5080c001c4401c40c0444050315008001d0010703443e1402d41d000fa0b580224101034507001c04420140d40740f4468a00d40e00c0c0030030401c04540d1a4480503010380c0c0851100c40d0201400c5040641c81d59926072001d07001604240e82e196409810000314814102c10341001d0315000e4080000100001d0241550520303c9042e400e8a000507020035641d05802c4080c401c1790000041d501080f10b032890240c1c00407810b68401402c480c81c05004151746414104245e2140303011a44c0d83d000d2900511703041c04174281030034a8800452801840c4c010140500c440302d102c000030014010005144030000754007810145400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 670277634 1250 670276384 670276417
    0x3060d2010020307170a0801090e120f030f01051c020402180a030c03150623010309170c0609060919080d1e201e070206031003230a0b0c 60
    0x195402079920b900610048a81e6511101780d10802d207801d40c280c960b042683e0342d48003110303440c003070070307500600143d003808540b5002d6601d00011040841e001001866900c0e44841c1c1c032844c016003985000b0105901040c0501a1518220101c2d18803c20303900440354100c90050b210036466080040340301910310035075000003064802105001401c05244200da1050320a000211450101c56042d1111841004508404c1601b000d400707500c0740344081c400d0b4006250018a40301c1c1e41d1503115001d10401601600e0820008912005040500607650f202401400921050900c103504a0381c521040a20044a54403800380713504100c1500c04640102c0005c000c00c0c0030100e0091442d00c800d141a0801c407907820316200744003403000038031384400f202010341200003070038803200903050250000004000c0c82020800c010b810016030b81c49003d140500c00b0101c001400a055260102d5202c101021004030709450041c00c1182402c001a0113004035442242c12039582c43c0c2800c0e100d2503000c1e154085010410 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 670278884 1250 670277634 670277659
    0x50715050103030e130b0306130812010906060f030902130209060f0705011b0c0201080c0f0405030a0b0a0507300207021839130302030f010902011403060d20 69
    0x900c100c40da444c0b080200d031690200f614600b080c200b2550204a0b041c2c1580060300055002003c0d01c10580b046801400200d142c441e02c0110444001c0090300201122a60380d002401050b601c4000c4072101045070030100003c42c0d02307400113094603107058115214190005203020a5854070400d9401016403082c1c000d072507444524041d8080c2c1050700420b0304510300d014581e09214840d0080d0b40d4001d07010b03154071034182c89032070b40350600c0d901100b5031080a0340b0402001a164608004041c0294010f0100c02c00a0801002205c151180940280104180c2c1030407412030600744c1c000003c50106001d2002903486080418402900038404040d40c0f040c044000400700c2c3c019070145611400306034082a40d40c2c9101c0b058501d92045070008810310217480d0a03020140010300e80240481074000001012845ea2a400689090300041c500311755651280c00300c6d401c40d60007811386030b0300e80508140c880c250b14111b808034401da8040c500c00307411b94141600d25490801a5249000403481c0070b842c0d01002d84 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 670280134 1250 670278884 670278887
    0xb03010908072f010c060c090b040602070807050102030a02030d020a0e04051e0601030c02030405040b060d0e030c07080c0d0f02010c0206040b04060806090403080c0c030415110d11030a05071505010303 88
    0x24040004012120880d243e2402c00d51010071003041e110058460100c034030102d4850030000d0501ca0800d0301401800c2d00046901404203002d040144190707402850042e0070100d0303c60500c81d1551106040d580248035054250740c02105030303085507144030030042c0c0390b10414000303c07044860a100660018a03003010b019034159030426404040f002c41c0c1000384580c842100440844000d00c01c110016042030000744031a242580050301c1c80000100010708100710f90749900c044451004501000c3d030700004444c50402010720419008002c6800034050300c00e841c1d0301060301071444450060500442001230703421a030180d030405880c0c0c0e0300600800e8449454840c6015640d00030301541c00425001000110249041d034101485240d05954081c400e40710301c40380a10340d410000c003460441c0002e02c0003141c064810007072070b542102d13643c0c3d440c000340e01d01c00303801410050b490441200f00281624207401d010f10020494200f11582d242c070694030b0150707051107504800a40504401c1600b0b0030000001d05 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 670281384 1250 670280134 670280153
    0x3082e03290103020123040503030307090f080303040506070f0302191115010302030d08060d0f050601060f02010c0e060f0408010509030417031306030c0e0918100e100b0301090807 79
    0x500d01945444181001e105032280602444001d0010305914034204000c503002c840300c209100048005803c00b130b1520002411030b041202d03d0400210482000c200a11000340000001c0042030f02840c41d6090503145c268964030b00801c450240640801c510040c5442941143c010401010b8881d40d02c0e41c07000070040c689110124044204e101d02c8005012003c88010744504807940100202801040d00505440b5084000d100c1c0da402804134050b000403e40628051010300d1040b40540aa581032900c007500017082488038100310385c03414031414150307a000b581006910004541d8a900d54141280400241c462908a01c815508043c14807444240010250065921038914100311000000d84190b69001d5480100f41d2481c001c1c0040011a0081e8414040c0c0700711407800c2d01004035440f0102c8c45028055494408103a242005c071181d82c00d083c40802070000d030240c400d002010504e0001540e40702c0f180314a00301c507951081d444689075025884040072a40c0008259113032041070030401c114 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 670282634 1250 670281384 670281413
    0x3210d090c0803160b0109110904090c050a0e04021f08074d0307020a060503190606020c090a0c090315020c010e070305070b090a09020304060b06030108161203082e03 73
    0xf20b6111720b00100c1e15012a000b2070094220b120459802c00110204010152600781030650b20304000701c8020030103417a10000b070806051080c0c000d50090502c1e206001c020b43d15810708181c81b00c000714400031140d81c0440c0c1a908100c5034900b1f90300600700d059000c21010b04038a6610f60450a40318003520300262102c024860f50a0400080c6030300d00d1151b042d5807a407190000c0250300c110803002c14070807140100c0c041d640008503085102c92001110020008070707000341d0085000350f8001c8031a8841c40c50514150f9078807050661040c403064001c0240035050900d035002c010140030301020344960341010341d41540c842c100742100078408001c03034009480d1122081d00050b100b6008841010503040940340481c5e4001d6000351100402c2440c0c010395000039000070b041101c1154841c03110041c50340c0d600015602905000014003400448400354020800c40317644070120f004128107100e400729410100066000000902400c00c0890142c00d0758607500700581c502d8008031b50300f440401071104612102c0803 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 670283884 1250 670282634 670282643
    0x603090c0f0306010e0c0d09060c17060111030f0c0109050a0b0f070206100e060105160b0117071d061c03080406050117060106050922020903210d090c080316 69
    0x40d400c001c4001d240c1ca80a007405644c0c01c0f008014042090303010703a00300801d10f80f035032011700144402180e910b040690f40041c040d100010200b001044000c805000200d400c070f03c003402d2485555034546103440c0c503030080310f07035400500501203800c08000400707421989070241d1010950303400340d01910740b000c0494010b503121601d81c4810000600001c0c0005102400b41e0a1030003820461803511303503490800c200052049040210500c14905410642990010954442c0500d01031641c10141410b26111403031005c18401d51080d0010801343c6031500c0d501d4140104030840c10709035a40d0300045000c2c1040e030074124401c1212031400600349684248058000c1e881140e041c050750341e0b03810042c580c0010030800c04c803007900b250004204050158004140c950405040c954410f243d01c03d0100c0b407502c2480d142d900340f07500050b10304120f02e02403000d11062a01014401d80c0e410300d440310380b113140c0204001e0f140c4880c0d560030040103000240c48000700070001c81d400c42c0c1d03031011350240c000005007483d0070484 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 670285134 1250 670283884 670283899
    0x5042309060702070e0903041202010c080307031409010c1b0c0308131d0f06090703110f04051002070b120a0f0203190b1e0d110402040b0c0705060702060702090702010b0603090c 78
    0x78807800c585c10800c0c05140c01000541c1080d0900382c501100000d0080304a0601840d54010000910200080e520a4000791000580720300c40b5912100c9944005050030026450102030040e5141c10003403040c8d443d5500c0072015042c5e2040c0c80c0000341c860b20703a000a0319034039010409a0440742c1c8803a182c41274850b8981a101900b5103a00b042c580c9a1040d03408188200300d100000e0340e00c1c1080440558448075625000c0782d505110f866100941e03000310b03003990409000103000e004078207080c806440420000c3c4000c101701c03482c01d030740b8400c68010303a4548002c84254001088951351a80c008100000e03407108115504d00307003004000071104400710540d03a440e081100c05e0100c3c0c50030910024400481140f1407440700985803c215441101d608201e034424084006081c03161540d20240003e0039000e1045584c810600e41032601d040c0480d40300c2c510a020804c1030800503141e00055404207030703040d22001140c0c1c6400500340d0240080018a41e084000801001101c20000502d020490070954044 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 670286384 1250 670285134 670285139
    0xb13021306180509280614030705060703051204051c120e07030c18090b1f0f0803070212030c010f1d0a0506041101021204080102190302090a0504230906070207 70
    0x1042c20324032620030300750700c514a100054805075894000300001740c100c1c600943e50a001030a04800c542003500005d90302041d0b0755255a060804201050242c202100c0741410207441c1e0307030028114465500188003081d0b0900c007040c2009000c114152408000c0090341c1440304008030001c1c8802400e0301503900b0a42450003d81032501c0100d441c000b501e81100c101c4444604003501031403030a070900104c0c0c00c6180d64034040c2010804800155018268001500301c0c8940990f0003d880000690004403141d00609000c1145280c004102c44006605a403280f000c05803d1282c1415402203425020280d400d02c20f0006000460360312900f60003205508152010b141c3d000450360310b501a00000b0a264400400718011448010060000c00b8051041351003001d842460306c440c0c1d4000e07900c0308100d42c0d0007040c5040748400b00044080150081e00d811401d04401200240c440c011512a56008540d110710000d840d941c06000b8201c0c0200c607649211107400c16403402c40d039503401290554014011903602 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 670287634 1250 670286384 670286417
    0xb1c020324220c030b22050a0501050609090a1101110f010e010f0c1202070804050307090b1c0807060509030d02180915011e02071d040c0e090703060b13021306 70
    0x125880780c2e82205600440c0c50540d51410843d8030702410300321141e1229211306c00720303003141a44030a04a01c40c40150040c0d2030b403864118292000034104034450890b030000c1003254440040d040c00040d402610f07076403042d4a0400141c417480c1020742130340158059907545014104054208501c0311180300001c10601d0300080010003110000c40300380c00028807485407003410601980240a50714054007c2519044c0e40d140080e1600005a101992080e22580c3c0c480c024035080a0244410300040d41d102500c2002d640c41c0c1d101885000307130042c460b0f642d81d00400e2540e5010020b8490000c40c1580442d51802c220010310032904050102500c035610b800c00007080e0030000e0454030144101a11000c50400d65810b03070040e41c41c2c0000b03084045100781600041c1c49030b0840701204041c0e0801c3e000007882d0402d802c00e0a036210300c0b900084120080c200a002c0101d400003a8032080329002400007a040d40300c08002101c001c0180170060300940049076420400c02e034003045104503801034031041c0710111348110 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 670288884 1250 670287634 670287691
    0x9040204060c02090708190506190815011d0c18150d050109020a2a0c0906051807120903030e0a1b080a080d0c2c0406090b1c020324 58
    0x61034047c400000000846c600d1064103c90b400800c02040f034403070882804a5001200c04daa031041960341d00c011078692150304154240781c058554030140707032244800d540140106030030140070301d05c04c103400040b03842844801c003844400c0114028080e1030641d040b0444847c035604243c205564031803030080001000e0145200b00c501e4492151035406840101d031201d90340310100a1318400d4441c41030000500003071901c01240300501458080026100d060405000c12152002d070501f03860710300d0034140504140c00151001804503c0e410100700e4000918049001e007064007000c642d544241221041049001e4403042c2c90345200100380d55040da59030000070380d200607007480540500000c120031034024030303590010a169101da0802e1007400c615019544095031140b03180c2140305072404400340803403410b80100c00c020680302105121908281000903845030822891445140408002000f192010310074031524406403070400413220240d52800d05a55011510080c58003009194481009584031 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 670290134 1250 670288884 670288891
    0x2220b0f03030c0d050705100509030d0f141b040b0d02190f050d0908120403031e3e07030509150a122406020c18160f030209040204060c02090708 64
    0x600400b905140c1c44c1d810b607003903072041e501a16140100c18501b042050103000b07050042a040006551f81c0005444641c116428a12960080340c10310840108c868040d07011180c0028450408451009007601c04e81a41c1c0720303d5020940300070b00030a4503100541c155000e0030100086030980070140f070b4000e2084401c9100302c0c02c01008110240125944205154003c41c5158030400016107000064603440100d11000ca6040340040e8803500d115030302c40c102c2c02c50001d15080c0c0003424045541c5011038100c42d02e41e910300c00f103031801028902038024020a42c0d00c4244c4100d030000e003680c034002070600030484c1d8040d02c1464064903d10840d60710080615040342c800603010707a50407401040403490040074010405000440720300310b41400040300079105410009044c90780090816034003d20030300403401c6c00045512040c001301e90030018407180704011000381442620b0910740c0c044c0c1d1420254005d0090881c2c0907042032001c038002c40c4454200c210001e45500880c1d101c1c4403a40d603e5402c480c1a44100c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 670291384 1250 670290134 670290157
    0x7020105071b0f1e090605330f0c070806040b180703050d09060908121c020f1c0f0510060309020d021810080109050304030b0402220b0f0303 62
    0x704811070106615610962482e0909540002042d55a074a00c20008400740c0003000c0c0c9100342c1c4001c88031510807145400041903412001d00061346044001440f40300f01005107240d800d103a4818882440124580c00700441101c1240d507242d410001021500d5003104044620500c5a0360011414880c0040d0321485603500900d0396a056403000d00c0400780b00114211002136200d0750001000143c000e02c00c82201e00025696042c6491600c0300003091000144d00c03541c800d40042c89040500852f42d000c071341c4e00b0075103440784d1204189034259000080c460000b216403880d02c0800e100c0129024004003150304080010144000202052003200721002a1403a40c024141580c0800c45940030b40c0011583d40e000424091802c1802d8000c0369005003d8150f01c81400e030742e40700308000c22030b681070000060b1040d000200000000f980d81d46070b8030f2180c0d010150401d060600000c046642c0d0704068184545135120342c4104010001c0700c0e43c0a00102c0b2015841b1704120010b400da14200041620300c01d4850 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 670292634 1250 670291384 670291387
    0x512010b09010908010501150c060212010801020d180206070209070504081632101b080c010612031409040902060a0e0307053a080309060114010504080d0f030f15050f030307020105 79
    0x52400b2745150014180885101c1c0d02070010300c074a1200c0e02c11185c000c140f000000b60361800a26010301c11901132840000c0012654030240c1c0c007584800e003d03140c40c254140e800030704580320040306544030b026a40c44060f0f00c0c0708000320410820303030b4509880c04580ca1800e4410403d07402c007800700f41403010300d801041c041641d031300c482285103800c6550202e07905103410a15022245074603c96607003010001c099819601c0020040305101c800d1081c00010700d044216920f01014940e03004080c0c02451204807c04400490f5408039036a4940c008045503074003d09980d03482600d00d1001d401c0710b6050280501c68083c41d180003c00d41400948503a40306072a1f1921941c11402d445c020003a5164185040010703020400320900188000e0021401892080001c050540c908502410740400404426041190078002000840c0c1c0000340d601c02a01503003064990300b88810811002441500244a91507080181c4981e440d0200040f800c183d07030b4160365240c481101c0740180741c0d0364803c90780c000380000c50 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 670293884 1250 670292634 670292669
    0x1621210b040e030a08040b0c0301050d08180a08011a0a0b0403151104030b0a0c03090b04060e150a06050909010204051c080d0f050f090a02011e0512010b09010908010501 74
    0x24a5448503140d910001d100240c00c82420140900c1e68000314801ca0200390008244801d1000d03803104e1981c0441003100031883d560410f004142c074a017031345400920990010135851292126800c2010080d080034058201290b0b0f80c9146038003030140180071244407c020b82040c50241406541201550341520119241901d10340d5071380b03c90b280030640222290342e12100411564440300040c00210302501c510280c90602443c44403c0b40d1800c0d001d003007898503100500b0000380c00381d40b180d6401904108001039451410890fa03080201d03990140b102c014900c1c0c100a0601c11a0b80310000b9030b0030587e060402d645d942c0182c2400c074031850043c6580044100c1110200504030520f00031300c0c0f445641200c3c10b0803010b940180940780d1449150520a403200100203800e000807440650114101c1c0041c440340c1c40e2a00042c0c42d1340103403455100006030381414800c3c020b01880c2115001900100c0d1841c5540e960b03410440d00b038000440007400140d205034005544c030b805026203410b9800c4402c0031180c048 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 670295134 1250 670293884 670293947
    0x90b16031a01121811120115090902030f060a06080c09010f420e040b09070509060715060501020d08010b0f0d06080316031b0b06151621 60
    0xc54030355092540b02e441c0d200c00c0d0320f00d0b84c103003000c0c86050744101400c40c1441c1065040040d21122200e0140c0d25a240ca41020460300000c0002c40498100c12000518420b440c00420b00b04820200c4101040c41001d0602c03202410740d620202c204c44c02441a2111105880c04001c440c110a21440301110741d515010b0100d40d101e01e134200141c81c0c0500a19a40c0380b1400c5481c0710080e40300c1e210aa21700440da024081c540d80280c1d0301448c02504503020020502e035140001c030000c41c041c00500401901081880d4152111001c0f1800507800ca4044016004a04285c0020340024001c1074010302440d25210502801100054140e8044409160420b01c102012081d55081894510400c580f240303000070341d1003418002040c0d00310045407101c10109180c103002e8100d5181250391403c400a0304142000304032407000b05034004604549000f503889002e001d000b65401001d16040c4041c607070107400001c02c11410043c404004200d5910f582c00841c0f01016100e40060325441302d00036502c0d07840f100c0c80700c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 670296384 1250 670295134 670295147
    0x8070b0720011b050105090c0405010315200c0106090605010f02190f12110d0905060403030503040c0302040507050a03050703020a08060603060d080a0c02030c033d090b16031a01 78
    0x3003010f160079107101a0705030911200c00078007001a07032503943d06c4080c4640000c0600c00084065800c0d20b0902080d451a681c0405074883c070400801c200380e5401c14282d115050203034240f0701a41201c0803540f50141071590354003c101b030784120061249000400104c0d54000d0001c203840d0050b5030081c181c2c103013840c01108003020f40c00c00c08803011140504000700058070001803011110712955580c2ca5048250850762400310300381522020b10002620401240d503910b400c55059a03850300d0003e0700e0703844601d4080f1072040079400c029400350030007082066450384200506502100c0c1d80d400e1115032105001a0100c1c496541c4100010704d81d94002491802c00200464111502501c80008400184c03150300a07904041c60030400540348081050a6103020002038419190881c0900820060b28400c480c0d5041308020804040d8551850481f038150381c21410613601c081e20b9000e021488107881c0140800c181110042150001c45c0c0ca541c0d90fa510a220f4545109103042410890075141801074646 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 670297634 1250 670296384 670296443
    0x5041503081b060403050705160b270411090a1707030b0c070218090c031203070819060e0105131802010305060f120703022112090a0b070c08070b07 65
    0xb42c400c07102c2011100020410140310798042e0f900c0a840382000e1034818101101d00c070891044141d014014030401c03600100702c0d0280c407489200710512030f0040c0d050000223284000d540398054501100180103401c00e0b001000840c000302c40d5180e0864803103a90150017807141410b11403075444041c0a0000901d0f5001c8180c100030704101041c200005680010a62200c41d01c1d802c482d100b04000b808085981003142c3c0e00d0107001100039289500c0e041d00c01400c030340401042c0c0300412401e02e02140448080b440f0401021044030010310016440310b05000600c0030038810f990007049c814100000403010707071040700e0500c0d0050ba4490004c0341c2030f40044000d07003005000c10f940301c200c2018500243d0764421021400c0b903140d0025045a61640c01040310808480c40c0c80501c805901c0401c0c1c1d42c0d00b40201b10400c00c2da000003240c540714100c01012403075510b01604001c3c1440c00c00619201401008100711003201d041c001140c090307580b07030200a141c502492100a0003680c1b4402ea40c0c9043c0c1c044242d50700d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 670298884 1250 670297634 670297657
    0x7020f030f0f1c0518070b0a1e091e050114181003020d0204062c0a12150e160f080304120602090301050103080c010b04050705120403170109060608010504150308 71
    0x4600082d540c800085420696445e00561410b60003c541e030601070044c000200300500c0d202d0705000c4800310140904031502c02c601420543d0190991800380103403181400b030558801c04001e24115890301054000660140e903010070100c681505503041d00304215009201a1501c0b11b1000d58603000f40540c5140304642001890303020310541c1c09039020781c80036000600c400d650300341218440e19000c44103000c46082e8111600c180039400d64890b1100c5580900b1243c2c045160b410a40042c1090307103403031101c89403502000e0308154003e890300070002030020307641080541d9480500d40d00c20b000c4803410035520581c41e4603003042c00b080101c80c00340300c0c3d6003202c00d0003240d0240c038011341d0900090131110241c004a58110001c2030003540c4150900c624078240e02e00b40d604120b03034148040c0140c228000c0303e45044440311000005410107201e0036074400368403180746008811303584850b00c0e078000c0c1078603018104c0064000c178000103962420303001d5000035804001048001138256210700c1c174194003c60070f240 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 670300134 1250 670298884 670298917
    0x20c060a0c060f06030210091a04030b0417071a0415051504090201140d2a020a02040c1206080c0411120c090a120305030f010504051918051507020f030f0f 68
    0x5610b440c1410203051f0190b5440000d002e0624500b400d10400c107919101107920300340300a00c0002d0002c0b18480d00240c200c01c1c149919002c0f0b031503141d403501c51342c00020541c0d00d003810301c0b1490a10204645d80254484d100c0410201920782044003265412986d1003891029225078a1090516621200d01d060040c98511040601c0c2071280600d0350160650282c0c440c0e60b50704503480c0301552018034041c030689840d400f425240e055002036851201c10b00282c4100d40e640388221595024403c01c0d000c4002250080c45010f83c1c614500c0e1300e810320404094001c1d030814009042c1700c030585086035500e071546010f402c11a1950f00000e2250b8000652403500256101e5001c101018103240c00072040f4840c0da101c66403031402c0c42041d0709100c0180d001700c0c0240c0c1802d0903c40340b00035084e01301150100242000420344559a804071a440f030000002e8500d000d014000c240710031000505500c198281e40031a00806040102d00f40d45c2d100d210302080d003200085c480b00c909810380c0c1c801011500903000c05031 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 670301384 1250 670300134 670300139
    0x17071514030108060106080106020d170717150f0303130312020f0714010314060d06050604180f0b011212120605100c050606010201060f26010e0a03020c060a0c060f06 73
    0x39500358020380114900780e01c988010414264000001400b5041c01c1c4060311985400c0d1801421550311000004c06a0807100000781100d03100d14610341400302c44e01104522030405d8076660301464a030020180c01554800702d003403140c1c240081240e030401d80121130124003901d541c5820750b249610104c03500450180d08803010071080200581d001a00444080d0f8840c03980e940009000c54504429104c46041c0510410405540f00420000480c0d0040d801140564403040001c00400b180000d10311300c10502c260000611281042e0840614410a0780100598030360070750030a40c60391080000c01302041180181d503441d11a01c001052000107540200d0a41d448400282d20a08181c0e4940005520317448000240001006107580090080c0000c10146060080c5000666040e004501808a070303003020342c0b01400307691130f4850700d044103100030810340c0d6181d04030076101d5040c1c01d01a4010301c10700900b42440e2414808030b9041442c55207c0c01c0b04107003c3d0741d405016058038115083d07126582e4400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 670302634 1250 670301384 670301417
    0x110d02040303080907230616060606180e13030c030306210b0a14150f13200a050901080604090b040303021314030304120f0f0f060501170715 62
    0x500003642c401c2d19100c0d283d142110000b40b52088a6000c421008480050004810140100d109040105607107071592800c0f90400541c03041c4285500400790780c54072000088580c0d10060807614420484090510750b5681c4841d641d06040c00d45e0050080c2e2125441540002e0048442d1032030f040c0b003402d02041090345c6d82180c4006c0071200c1c1c8285030461007418290308100600d049164007904088007001845510600c0c000550b034014200d01c10a00f81c43e20708082c13961158410b0844003401480c0184485698030f500021b09146100081c4001000f8100c4028880d42c4064910080c52640c4440c2051504401110b445502030b002d290006c0c0e86881308004500d5208505210b140a5200940e841d60541e10000c140c02c000e174040da085000c104070a5240340c1d00030049a0407148420a80002d401440c200803c5489450600500c002000e80b500001c0044048001c0e848a00a80c0f0070003460780d80380340d50004d601d0030a0b01e100b11500501014090809002000c05800c4111b14004255005803441c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 670303884 1250 670302634 670302637
    0x3190c0f0605151003150303112a040b06070512030a2a0f0c02030307260706150b04260c10090801050c090109062102070305090312030118110d02 64
    0x58620039640c82041030449030074091013004640949103000c02419102e510404c400040a00005040060300180d02070214002c102030941c080c01e828003440c03070803000d09555202200388103c160242d402c2162440c4145003100940300c000350400045c000460130344501c0200c2d50702c01032074403112035038a42448144070f81c104040d040d85605c860124440c4002000050712518041707440c00c040003607011081c001030f1070120580d0300e095400001c1c1d11000c03031241d0080d1581d001107244103800e02c001141460606c403283e00706c013840c0c0f00e9608403813100c0ca484400d5105544547e001d8040c12510f418203040c14240440f8004426a03580d07801d80390042c0c42500001c082210321081d071000641c20301d100744441d540a1041a4200381c0014585203071401110001e81504420f01c60b82d02403040b61245850701448003030882440340708040085544003180c2c603025001d6040042e20b00d0180c4a0a107601804001c040c040300d060b14061548000c10a034240080d901070284d130b1626460f212018020f0b0440c2041170f00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 670305134 1250 670303884 670303891
    0x61107030f05011e020906040b0306040e0f0a06060602060c0a260a0204050901050306091c02070b070305040305010c02161502120d06031a040c05040e0c10110c0303190c0f0605 77
    0x800e044c0e40c155507620040703103c401c00d542c96510410aa0310650b8072a0101c8044a41c2d020b01c07181c07a0340d200c0002500030082c03200819003d0069040d448209540800c0c086d000c10b00c140f208000190701c80b2030881e540d88080790350140c0d45108102042c40079001c0c5a03003409440ca4901c65000c4010500303503400700410280c580901d0950089800c1c040da1801485280c058481600105a00c2c58282d82c0a5550b003d46000d9100f8000041070342c2030710505c21301400018201c0c0364281d5560301c6003481c0080481d4000d1009070703819441d041c800c641d00ca2011581b00314040f036030308007040541c0c01c01c1303020032201118a050340c06522400381351800302c80101010f08035498042500060992070740c18800040500c0c10310100008000404101c00500b1000740e0000303441c01030b07600180324040950090f04e0441c6909600e588101e00d00c031714800081e404009001c0c01c80481d4140c0c2c01c0040e0400925035a4040c070000c500d440702802032001452807042026082c003e0241220982d0b01091f41c94940c1240c2054 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 670306384 1250 670305134 670305143
    0x6030609030702180a2c15060a051504080a0f032706030507230a0305060114030c0307032a0e01020a0b0118110a090e060901030b04020904020102030c030d05040b010b070804061107030f 81
    0x5c04c0b403240110080c042ca5000700798071441c4a11f10320f81200010b2081c1c0c414002c1a1040991084a840f8403002c507041c0c90240c00322000300c50303440d5030b1801c1200360f04114038400c130001044400314803500512041c0c00c441c1411501c86002c003250400c00150060b010041840c010000d0281f0f07000d40d2216032a0700c050040760703080342c030301d95032810f80300000d0544c1c1c8010006d6040c00400a058a621a19001240e510030200303404291a91601c09044015004d06114449100c50340d16820341540046850208482130b1a100c01c0107a50030b040059850302c14940e005000d841c8280d0040003200c4114a00000b505101c0500044190020080e41043e070400d090b10000038910040610440701105050360f003107401188c0b841140c0d031443e039032215003000060000780214400c1011400b107900070401d40b060030001d1030035251a81005440031000302011101503502090660000402c0b00240c01117840054205a00a2509007420801e423a01c1800e80c0c0c00100b148140440040801e2500c102d280748180318 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 670307634 1250 670306384 670306451
    0x100c030e0102250504050c03010b041505120106080a0c020f030d0e0c06040803030f0903040f05010e0d08030117061501020d0807020a170d0b0a0810150504110306030609030702180a 79
    0x41c0000d000441ba401080c0c42500340e820001070125102c80801e940c111100307040808042d20303003102d0489180c000d00b0006103040394020008190282c004105911840540d20100051244000d0480c0c0c3ca030810a2280c3c66508200030040c040340854000d180301c40b480800704c8180e24000000308266904c01e9000303401c250000701c10302c81301c4500c01d807000d900003186400443c00e143c1400c00f02c0e9800720700c61103074505000351540fa0800a440344202c048595801101240d00c84d03960710303a40110f240c00c06480d00014018540020040714516219499100e01a8000c0070448075011080c0c4040da4040c020400394880c0d4006513001410240c10211920307039007105c1c0c40e01d458101c2c08040680300c50010140c81001110010f00992030009080c42e41030122903004a0610100b10820680020a40002e90014102400c0c000e4041b1084002e60003090242c040380e50710b51380c500c200c40d228002d180000358000d1030341c4d4000b84098800640c0b5a00503102c0400001c09400900038100d41d29660054521440746 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 670308884 1250 670307634 670307639
    0x10e03280309062a03020c0406060f0906051e160f110405010503030306030a06020a090902040f051011030a050307110102030f04050c18060d0f02120601050f100c030e010225 76
    0x50207407400c0010602810511012821380301e1184054600d9403803255021180d180b01070a1501c00c00c821000c2c1e8501074810010941c490310010510040c41c105000881e108071000220188100100c810300300d002c50080b440280740c0000c4200c19403000d0181504462410f244d44041200b00c0e40700301c1464821103002801074031000911058800580c40f55119410600802505031004a9281c1855038860001607071404580810f541005142d048042d03014030108000c651002038102c441d040d1031044801b2499103020f2041118100c5442401003800c6c0c009114254030140204040c1d504104c040c285030303c80203008030a090132604112002c0c00950411020700061080c00d00070200313250400c1e03e6915602d10091120a80180054140d034060312054170441d003442295600c008009900519030302e03203030021001e1195074540030b0141c24416000081001c074203290030800500e000c0c3c450381350903690f009540c4054405202c401c1e11203040d40940b4103080282d507142c20400d8140c00081c034050b900c160 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 670310134 1250 670308884 670308887
    0xd0e031201050429090a1b0513080303040f06091a0a1a090601050a14041a190f1b0201120f06031b21050106150305160e0f010e032803 59
    0x1281c1070000c85100c03119242c44100c500f144245950340040a44551794035880c1c01c405e600003011003040588034505800c12004800e503002000700310707250888c0c2c4952a42c6803075440081d00e030300c0250b5004000000c40c001410000c1c990b904101801070085400c2049080d2030f82248a10f007800321001e646055980e403404207801c6154002c8200c40700152030082440c80d102c000606188500c0350500d090000701100d0810810801c000c8070040c0500d1101e9080c0602010040401034024523000460200540485400c0c144a0745034804c10f400169100c9040c0d00c550101d1524004c4121001d81c1088480780100d1004c061900a11980308420900051554958103001034186144507500104900100003040b40200000b001107481940d1502d000000d0b005182040c018450f40d4008110041e1407016541d210382c240c0d200d94807481004112481c000004002201d0900401d00030b19403054960501050651160407402d18008000d011288103050b05951501721010030504114101142c01da40d000b0035 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 670311384 1250 670310134 670310141
    0x20a171e0a1b0c050d05070302060d150b07030807030e0a0614071704080706050c190201091103151b1c020a0e03060f0402090a0b0d0506011a090102060a020d0e0312010504 75
    0x390440802c1c0e50741c00b11140c0e51150f480405206042c8140c02d484502420700405101070001168010081690740650107610006015180300041c1c50601c10000050181c2205003180c60040d03040d92801ca240e5500c400640042c607600e60304c084944110b4296400044540c840c4422110059402c5110b83c40e180000400d03112480c441c00c51521007000500c0001a40c810503a207240b58441404a11540c03100b021100902945100310024500c4002e070400741501036002440a034040c03003002c0401240c0c0428103503103440070100040603240001c000350f078500c00307058541004c00011041e00d24251035074885449540c1034424440115600103400501c9130f400104a00040b02c1c01c0d00581894948400000b81c0040e00810180c051050180040d41041c541d40c00b44104010090215022814070f04016640702000d00981c1c40c02c00450300400c1c05c0141d24000e036456014142d0040c0304079560740c42d101c03000c0e4201c0e1088240350354444c001c041c2ca045081c00030b880c01d8000d0740803120841d8034010800094 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 670312634 1250 670311384 670311407
    0x1c1509080c0714040614150f0304060e010c1b140f010c0905030105070201060602060f06010e060c060a050601110a0318030501020f0c0d090609050f240904050f07020a171e0a 76
    0x2140b40410070800710348281040010320703000315030074501d01101210301201c174407030032380320481e000c030004108800c119040e4000d41440140c100200b0606821180903104103000b0350903504020795019400000415140e41e0340c40600c540300903140b65141e00c400d01801e5418401c868000f04041810501143c202445047d07804401e501c020f002003482c112002c0d48449002e030035894420480303000a04c00d07034065000c124490350050440e03681c0d100151030315529240240e03540b01103e0300f080c010421a61003048031130040c000b80c0d0f0241030840e074144d5094a05021000402c64203640144000001c10303400c0c0b01410410801d0400d15a540d031805000d41e040003144081d0500b800882070040c000c09520141c29800e850080c4e414400c100e00490001c0c1400c0115000fa8407000d80e2140a0410817440001408191200741e07800d1003c1e0b1519120002d05400840e02c10005a2080c0d03070744400b04000055003000d21103c0301c40e05180c030b103050440b10240e030000c19030710520510005803001080e5001c20940034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 670313884 1250 670312634 670312639
    0x30d260c030c16020604090606080703090c0b0c0f070306090b07020f030319090c0303091403010203090c090c0c071409071e05210f060a051c1509080c0714 68
    0x18030300104609958040038000707020702c403004105229070b40800c0500700001c42d0010100e40e11255124200b001910310750080c00c000502d01004203141074000d00988410702e0b441240030100312708086a03800e803a00140c1110200303100b410349400d80e050b424801000030794014100440c180c107942c24692000740d0084c007600215800402c0010f0500d2020050701c0e01b00c50071500200340c040052840c00c001d06007010010344860801000007080503081280c110846452600103a100c819450415080740411244078a0b150409807041c0c1e510301e4143c10719548180007000d07440c24195001802d41c43c00350650801c10001d80c2030361407a011450300e511300f164042450300d88490308030000e070f1041004910300b100301d0080c800d012a6000290740880055420070941c1000010f0501c2d004400000c4a60240d9600307002e440403078000710b503d00744404100c5150828201c00038441005964030810780c040001908200d0381e44400280c001f4055100030a06285040c006203031003400c1c030f400c0f0556002c0f26150280b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 670315134 1250 670313884 670313957
    0x41205030d0507050316140c060a0509010f11041a040f09090b06040c0c0f0c170a060b01080402030a032a0b09010c0f0c02090901181a06030d200705030d 67
    0x1619041b10118000420714a0400d6616400804400c0749016850030100c4a002e50420807440381150303440783d07200c3c403081b00090003e00080208081141c01c42c1606002c402002c01c01030081402c092f03030456040d8001c111140c50135540700880700040e00e0a40281070100d840da440c600034000300004880e04642d0441d410001c801c3d0000d000340c64401c0002004101da15480c800c0c005000380d0b01074850041141d1080b000c10a10b410105a440f0302e1185000c0343c50a01d07104107881c0d154490301e0204d210319800760041400032507540f0141c425061203c00e400d0f0929107840e400c0a9803152044124600b41702e01e07079002075400e00011407800d4a80000d550020070066800f1000d20640c44400107000a4045d00c0350500ca84031952140c1c058800e044000c61488100071940007081a455400440ba0380c0c0d11100490700d4407220101034440d00180008400200e2404160311801000718440900d029400104c55100344c3da400801e04241000e08510041019442140400c2e403014413414085160b54001c1d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 670316384 1250 670315134 670315141
    0x1060503011202010e0102010b040c03060305150c37051b0a1e030203090306011203020f070e220203060a051029090a0f0e0a06090203060a030602030c041205030d05070503 75
    0x303403450084042c0a41006000440c0d001941d000f0f5011a04140d0b019100b03006410304180050050100d5100480d01d40c881d0091034154111a4000c0320b00801031030b02c12038a0010030900b004c2c101c0c21102c582c2c4034856440790001c0c403580c041110030120110161a4541c684c40d200c06072020442e5020341659654101904640005144004245400306940d03801c61803e44682012842d44c0a403000441d0907100d00c80021624843c50711203441090700c80d900f254034482810b5031075074450f685840b840c190322150001084210b11100c0e6a138130300c01c0c1c091101d40080d00300781c1c00081c5041c0381aa4422506644d8400303101518521075842d001902d01103022100b130016082180b5151000d02007903640c0380d040441e04c00c400340e4881c0381d03034001880300c08001580240c0726040483e00307030029161417600754a4400c0003e4010041d0095a2048000038984d0803014a541c84140c00307507000622044070a0020840070400c500c1c1d400c03101084038050401952640030400314501200c0e0042c2c400f100703106061040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 670317634 1250 670316384 670316399
    0xc01140f01080c10120b04090501060302091e1b0c060a05061003140105131e02030910050919080c010c0e0f031f020a020102041706091c020a0305090d020a030b0f0106050301 76
    0x52018003078642c60310382e81480103480380714010110924240d03803003808d107142502840030540001082d60b000311520241a2910002d2442c41c0d22110006603410f01c5032070000c0c50784140c50860f9250170101c00821460442c0e18055941050001c903810301e10183ea80c000e00c020341c24103e101105100050404100080305404a0000c0c910148280791145120006082d40f400e1207030842da0040380e060801d101c444280782c0080c00a50012100041d0134480c4589000090034107000d500d00454051019011f0305c440c11085140006a05400342d031744d21010490350b03502820901c0780340e4910a00703a030b54012006800040020f803841d183d0905120368068005d07444550074801040000040c404030050395450b9040381030340640195030208a0202144003031410300034000c20004d2285090100345c2c0c1c3c0800050f0091510130a104641000581c0009801070000b0300500090103585402001420f4080644c0c0c0010500c45070754008841c001c1c03018040c011880c20382e29172580500b6082c242507003117605042a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 670318884 1250 670317634 670317649
    0x51803130b03100b130303080f041709010215160206150f10030f02040f090518060601050a091e0e0703020901120506061b010c090503010b1e060c01140f01080c 70
    0xd1001180700002c0400c903052110304440340141841e58015451790543c1c0010b4001c15454801a404100003c00186806469102d4a48501d40c803060f400c11040381c45015400c075070810802203066100b4030101901040c0150095842180005001d001103035202d10000d042807005001542c1400944900004c2c6c0c0c2c1d90950782c0c01055501f581d051800e502442011000760600b0100c4c041010700c00100481c418480d42542c5055403100c410034807081e01d0304080e01000d5550401c58082c9500160007081c410341c4160700130040f400280c94160340c0d284d01d4001024040c0200165501d2500c00e01508001d4202000c80903a801051800c0841c108020340d000a0480b6020701c0c9003c2c030440d500c00000b038569580703109494a100002080606808802d16194020503600341c0480214110130f200103800c2ca01400381404942001d0920030444050701c0074015007012104007182d2241c010320102d001400c091045c0c2c3c0309616079808500d601d0410300891010004107030061146074012001c144200d46903240e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 670320134 1250 670318884 670318889
    0x15050906010c1a0f0412110a0809060403051f1b0804020d0606090c272103111606030c050301050105121506070c09051f0e04050a0f0605180313 63
    0x2000d00d4074070b80c14070305002075080d10b0804541500b004000c2c4081c0c0c205450750341d0b100e984541c0030301e074222080240030f07103801c02a2501c05482e035014a2400c00025001c902810a81c40d019224030b007403079166558a030801c0c5a454a00d24820038071400e054252005002e00311706402c44a015021203e850320700248070860050000c2d00031090103c4500c20030020341c0c0b1520041c21415030402c40c10300d130450300520610020510b1500074405480310384900701407085000c1140c44034948110081480345c03c02440000f00c2400740c0a00040c00c60417880404180120044c045103512401c0c0840d00f000c0e406411201c1509101c0d0411906000500260360020106c906440201615000f9640c07000324461640340c4400c00160400400314010303080051a07201c08081d50398120f800c1c0010781d107005608000e010740815a080e9105410410042c40d4446c19401e03801c140180240e40d00056a52122031068542c1c24045409a40e2803080200b840c40040403070118160081c0554584010004030070580e10660 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 670321384 1250 670320134 670320137
    0x40302010804031b061406100f0203090114040b070c030611041220060c010e1c020a080a0e06030f070e0102012f040305010509030c100618021b0609060601031505090601 74
    0x301072065109441c1c1d030030300501c1940000107000300c0b11b03820741c140340080003903130041c2c020352180708080d81c40340c010510410715100f42e500031410030907203c00440c1c403200302d514544403c26017040041010341050004201d1580514031003a1207615500e00542111824250141e03640c0b4144414009002002047c0710441e400035200003842640045000390041d05400041c1e10500c0003910707c004a1040d00180745184014081c3c0300220102000181d800400400d00001030700700607200e038002403006002d04107810403171a000c030071192440d0101d840c5500035100019440c0ea8a01008140e5501040d0112842000c1c4028014440130301c889000c10040c80140328001f0025000d041c0c400c0042900707840045070010020311042c104654a00e40726440313000342c036003240940400421030600d54040c500407110040da83c00c4841e58401120002034018140c10a01001c920704940301401003006920700a0707041801400d030a041083c000342c2290b030303800409400c5040141040245a0b1381a074400d41c404000e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 670322634 1250 670321384 670321397
    0x2209090302070909150f0e010e06040809060a1209110901060c0b060913020418020102071a1c0e2a010318020f010203160c0302090f04110103150513091704030201080403 74
    0x1c0d80b03440800017210441810040389859070302c2c405d0841d0f035000b0f81d01d6028444020400300441d4003456031a40360850300505601400c0006045605101004003c098118901586e01190800e50807040e201c03c118140c9503401982d03928012440c04c4c485440c010405804c00440894540d0b60b200c03c8081c000300760f140300b90f080800243c80e4110021803100c649a001748100f14004800d0880303e14541822030980c0107201d028008a80204982811340c01134429500c041d0a1603164241f22090446801c0100f49168450400384040041081051640c4140c0ea00d60100d00c1e0b4005020820300c16010012070405052182c0041e10f00421002c112b1016010341d09181400300c0380005078a580300b410055042d1a2061003c10188005412000d0a680c803c8480251640302d213642041c1c140c40c143c401509900901c0445002580607a2142034040440300007403210f0341e40c500000e050071b01018071244100380c940201000300b04132000310002c014040c6074a00c1c2080d041d41c000800c0d0b510001c1004080c00f1a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 670323741 1107 670322634 670322651
    0xf07080d0e0601260712050a060b011d13020f0f040f0e0c04090c0903080c03040e090a170f042c09010501063222090903020709 56
    0x200c1d0780e22066040450000c0c207134071100d4003e189480d1107898800101d440c00c40760800c248a0150019283c80352a034245501580e1500880c94100408608412001b06e030510071108001c90a44005d80801d00c4450004000e120b17002e903000c869040402c03000400c0c040c2900800c151070075415070f4002d803981c88861400325041624440f01c480020720027448100351075840b801140c1e403640361440c0d001d6540d0311000c40543c0200c41d0a88281c01c00507003849810fa110011070307003040e00c290051282d1080e076150800d84103500003000500d2080010500c014a00d6003090300c010707081100150309860b014081d14132044102901d030381400204400002c0c0d80c010184141030484a1a40340d0000d104000031942541c88850070f440d402480d0148200b000080c5054050582e011141c1d64000000f0f141c8103a280031021b03154050141282851422000681d010821404850400c00c01040f210b0 = true := by decide +kernel

theorem cover : BRFrame.Cov 670143884 670323741 := by
  have h0 := BRFrame.cov_init 670143884
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670143884 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 670143884 ≤ n) (h2 : n < 670323741) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
