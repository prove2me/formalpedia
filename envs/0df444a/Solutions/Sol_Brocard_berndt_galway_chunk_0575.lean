-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0575
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:31:32.325471+00:00
-- url     : https://prove2.me/submissions/85129570-8ee9-43c6-a571-1f0558661851

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 103237410 ≤ n < 103417266 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 103238660 1250 103237410 103237423
    0xb0d02011b081204051c180302060307030207020306041202010b03240903071202031c09170a170f0603061605031f09240906081b040e0a0f03170603 65
    0x850401414507a180d25205545204840404a10352042d0701400108100001ca9820345103c410b06409081c00c04001100c00c02000300c02101c5042c007007034080000d801c001c40115080403961802614040380f0b034000c286800001d807000c030358050444a2002104d45e0a204800203040c0c214013400b14841107861028414024050750003000d400d80c0d000c200b594400308201d0340c1103680040100201e4038903040c003948039004820742d0012030712001407004c2d14003d584203003600107074850301c0018152400052801650810b800c1d94082c040400381e43c00c00051441c07522482000c00c44c0c50b07442e0310324141040c5828801c02a141c00e414403421103504e0360741034101e01038030b038080d46074101d0301ca40c0701ca800d600d05600d42c61680200303645458000314084015204001590984402c010011201c0c2d4564450301111458403ca1105070018001c5010b2046542c0000d850403100034400f007a1101c0401d4541d0822112480440d0100e44a0700150109600000401e00d800b1000181d40f00614144010944894 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 103239910 1250 103238660 103238687
    0xa05090708030318010b1203030a050a090f060b04020f04090f0f020901020d08061804050c1504050a0504090602041a0c060a021215211e060c04180f021c0b0d0201 71
    0x740b1030f0048008000b58000c01001031b008000d01b03040351a03509640c4d100d80c0240c0710f1003541818180040c100b04074074095242566804048214003501c180c0781c0e6070050280004043e44243c007005038551050a49001e4030291050b40c1c0e0008025440f00c500300104c900c030b403803c0d0002074010f0040048a03a001f040146841d0200d040801007541d4440000c2c2c0321501064091054000038014001400720018480500c04020344445a09002602400c03a45021383d108083c1c2c810f009000038030030303424a40c01449810348640c0000d0308041d12070241c10f544060100b00500e1038000411412100032080140d1a0050008042149418001e901c07441140c900103003045a03c0781c0b4400070300d03074540b140c09420f170315860600d0282040c24401c0e1070140d00c8803807000c0d400c2c07440c491000440c2d00312070010907150b00540001d42c0c40b0f46001d241c10840200f1514050741240042c3d0350390102c0c5140805400103000308c004401d40351070a0750a441c282c00c212003500030b05502071030005201d81c0060342c00a20b60003240 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 103241160 1250 103239910 103239931
    0xc04080106290a030e060a2301230102010609110903190f06050402180f0105012006011205121801120905070506090a030501060f080d080f0c07031101050403080a050907080303 77
    0x3640801020307006441c6021710052076200301d408120904003103600c459030030382e121403480d800d045a050140c54803410a01924208180c008540003981c00e601040c02c0c0344500600000c80c00650b1241c500c0308440f03400c008000d90f4000024400c01924090002c05008a030203403030348411810f507032108650072640110003010fa55441e40468195500c01240d0510101a440000384c1c07442c201d2904904c4900071f10540740442d00040c01042001c0c50381d808000e10072800c070014002a8a40103900c00f204801c0035082d0b0b240d010f400c0e0703805540801d07030000740500315070f0481a550310050b15000424032a50103040030203191a01031440e0018002040032011554101c481e2929200e42c00c00051036440c41d5031008007070b0340c43c00c98000307a4080b4140c4401d0455251704252881c014440e4000d64950504036065101c0c1303001100020721845480001d40b40d41e40c060b240640404941a608508682003518140c0110b1000010800300710341c1030048540c810b4044000d4107905107041d07003907030b524003010f411350790306 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 103242410 1250 103241160 103241167
    0xf06181f0b0a140f07020910030212011a09060612070207060206150306150424050414070801182306150c03040b1602030715080603010903170901140c0408010629 71
    0xe0460800e417240c5a80041440c0c2c140c2c02d040710001b030015078922040b40120f00000f41b680340300d40180704a03004220450754105070304c40c8030010401e07100f0000348101d500103020b01100c8858080601c80d1882001240c00a100181c28604081d29014004040c22465080010050150f4501041c0180c220700e00040c0680565407800000d0302a212a1680d2100205d0004400503c001c610021108843c4c0541d001c0240b005d40401901d001801103810101089100d00100242004660070300c81c014019400024150b4483c40d100840f0722400c00d4440382c015955040c4065480c040302c0080545a20030040c900d80360072921007940b40e01581c0300b6207405000c04580d058401030658134058160380d00509071000107486100551607403403444030002c0040e024400061540c1014403c0411b9941c05480e10480d002640c80c201400480c0188148000c2d526003c05240700322001d01403d000e00e40300c54005440340e041c00b00741421218298400822081c0c40d075a4007050402c29124440c0c1503a0241d1319903503 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 103243660 1250 103242410 103242427
    0x18030c0a180b060a050d050a06120201050f070b13021c03120b0a0e28020f090f0105370806060403020607021c0c090507030e060f06181f0b0a14 63
    0x50102d54155904002c0001c2d4241006611400500540c0e000d54402c2296407141c0d48400201ea00f41c0c0548040c1145d40501c40e4007541c041d8002d803546002010f0500d10b8412645e9031242c1940d810707950801c1508821480c007045150007034180f00d02e42c40556102e00c44002d0303514000c0040040c00142164581c0e40c042501140d01c5007030030700000e4558040c03c01030b1420111240004150003146100041001c8401c81a102c141402261458110600203174100000c0c10100141c800c0c2c14002141400342c01c12141d588010f414406642c12407624101b0b040e647c0c000320fa16840741d846000301a0420040c0c000300b20700e035a9000240e5043d2601a20195102e00452000c0740c25030844072030865504103000e00d0b103401c0058110b22001074605a035024002034840900c02d505403902d01c0c2e0341c42d07841d400600014100803158480180c0c04000144101c2c880203090303040c0030b1000c4007070304c44000103044006050444104004107200a00004c41a1403a020402000400503030700160380842c800030000e007044 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 103244910 1250 103243660 103243709
    0x3110c01082a0f180d0506070302030604060e070f020c120604110102010914060108070f051008041b060806030714030304121104060902070302010b040b0618060c0a0818030c0a 77
    0x11052980e04205507114141c802003c09600404880940040082801d102509140109141c0c4c2584070f03005080e0750b10385481c280c0103500018881c640141d51010001220342d0789806085c001ea1301c90319015803944442d0002810208005096409000d5118050140000004174103034041d401c00c42d5280078040d20b40040340544440c0342c0103890300d007450000030b4a811001c03c0c2c85040f03901100860310040ea6650700c0340b800751031521490343d00007001c03406071914a024122040c0d00912611460049072a6111b01000715407061b040070000546003070801c411030404100800262481d00d486880c034030b10b15000030342d80b88543d005002d6010160000c00040000c0903803008c0054000034400d114060b1240d101c00003d402404094005608140014420341098820100c2c1040c0180c10303985800d070070220546020001d11180394000c4002c202e00003481c2010b000104c0000d104003611981c40020a1040c4149009000c00c60300c260800010b40c4810f50381c24602100311000e21082502803254a0442c8 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 103246160 1250 103244910 103244971
    0x60207060e15010806011514070204060e0a0b0f03030705071203050d05070c0501150602071401050c0304090608162301020c0307030c0f0b070807240908030403110c0108 74
    0x44078648948900b600040788408000ba05070f03000300007191056070340c440008003000e0740a5084004030b05650b000b218096039450040452500240020820307580d00c8010260105085441100341c0360303910070b87c000b2417406c40b4116400d20000c40c001d40c04d01110b074803803030b48034009171050044002c00c40c9494400c042c081e0b400d40e4142440742c0700410542c608540c01a15051601104450380c0d46000010030204c80301c8040e403c04d40d0300c0c550040c00302e1130030003098020505a072148281403010a010040100b01c0400090000d0140024041615482c6c001894130300000385400d0942001c0444040c4030703182e509080000d031845402111182d05400703100503420080400079064050280b0f44022050061706000c402c210740390f2040030041c0d183d480d501d18400740102e2034010080402040014045103142d949400c60071140240c918004d0103407003090080f50f4074000100c4844101008110905811021b07500c07030306c03074040f0203042a00302100c0003d151240c0205110030190100c0c0c070000b410360007605003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 103247410 1250 103246160 103246181
    0xb091201020408010203061003140f07091a0d0606090e1518040506061002010b060306041a03030c07080d0305060105070b09190c210f030813021309050706090b040306020706 76
    0x310342d00c40d100e00a141c040d500443d5824014000c3d503c810300b5042c820b101f030040d080b0f661072088401d41c0720060310101c81c00e8090000f20810001c0072005c04c25a000c0004980790b11000501c459442441d0744d145001d1318010751001c41404510322003000070040401c0300c513621000005584841103102d030b00040b503c0c4d00c400d03010f90388200d41a04000811170009402e1703008240407244440035400a50040b802d0b10400304403540c01c000d00f44003198072070419400259542c5001d240c0d5100301c1d051040841c4c80c1da0420807501c20180e01c80f402c1000760010034441c83c6c4141c0da40e0b240034007407480c00c000041c00d02c0c40790880062003003903841c0000e80c2403001444403038003c29030405a80c10b40446800c01c0d81c45402d06006004a0316240c1d0418003500781507084a0316403235130000c4121343c0c848a50310b0030b0711100d4004200d43c0c06040025400c1e4016071b036030349207210b0b41105a040042e40e0b440b90b0070014035000ba175400007018882c428006004402c1c1003800c0d0341c00c882c2d0085000d0780d140d40030301d030038000781159422 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 103248660 1250 103247410 103247413
    0x70804020a030c060c14030306030a080304050106120302060a05070509010905120109200f04050f040f0314041205010b09070207050d05030906031501120b0d02330a1202130b0912 78
    0x1051303881d80650183c0390617009415808401005c54100d545903c02903a03020b42c035a10031a515000034403404080c580c0907000d02c000080300c641e03810300450b03007031104101100140c1240042014841c0c16115058221100e8509103050181c0040003a0035403c1d07501841d0321a0910070198040003209420070389009a0180b40c81e0741140e10415000014001441000d2081e000c0c811100c0d01c0d414a8440c0900c503607102901142c0fa1784440c0c4070310341068013601060301003280c1c2e03180d280c001c249200e00900061172000140070010001c1c0c00c205085500c406220b40c440c1c0c01034410300c03004560010301078064903000c9030300c0b1005a00c1882c10b1403a5128076002c994201c1c10200800c501103a0b080b400b01a8282d080e01c8a16420406110301f204603090002c185a00ca01071a010300054242840e003901807200404d8a01584584d00d038624910007408a21a001c0500c006521038403203600c080608410500342100790b051000e440c3c0f800000300c2d402d004a42c4a1100400c0721251540c847e0012019000d0400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 103249910 1250 103248660 103248683
    0x20303190201020c07080114010608040c0b0a0810090c121d010f0e0105090303010b19110303090708010b0109080a060f0b06070f0317150d0302010e01020a02011b0801030308070804020a03 82
    0x40041d0203074020003070070300082c020f10b117000418600c18080e0302d4010540e41c810b0401a800e007034041d9041240904180c84182c1040d81c0400c004400400600c80400c50313444003407040c94840c12140589015800488400d81025580f910840d00b0003000052180c445001040c0c81c00d600b200080701c605001e480007803c5d07003041c504e00c002c114141e00c14490051004c00901007a910442c0195403840288a0300c40d000c60200203000000b0325605c290325520080e4030b4240312800201014901d183c01c20f40e00c805e4250030041040080c03480c240b15014030b00600f0b0803e819010300e000134880e01e5181214000d00aa40c031088030300c0c9005490741c4078901001006010503216a214208136000c01c00348503046010074210b11411002202c0010301074841c000d6200c103013070404808010b100813107100400840556403134440c03080300e00728280040d1401c401c040d400011284c0e80e041003100c0c00b50144600700d050001d110014000709034420700c40d50f400b01c1c031800c0c40620b0345c82d6032021400818550788054840310800 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 103251160 1250 103249910 103249957
    0x120106060507050111040e011401090302060a0e0f01081e040c050904030f02010c0e0607032712020a050f010221070c09060602010e0f03031b070b0f010503060a05010e060607020303 79
    0x1400303003424078060002082000200d8001217401d00c124020404092684001040054403840c1804003010041c075065403615541d40c0861060780081c5001340c08240d1818000c3d206061080146441400900c1d120b2054240f082c2da808481941640d050149542580024240112200341000515000e0002001403400d07040041044811080d240015404e110040c500302e42b142c804114070740350003403800d8075000c40d43d0b50680c3c982c0d0000007500b603041008172244100800c10011030740102403940b2580301c60746061040082d83c20040e04400d1290501007030b03480003079900145868a002c5c4040030041201d255003140c1915000d2407100505106250001090b07c442d40d400200444003281c00034041c0720b118900e03042d210029220900c400d90b00c00c1c8002001c0c1c1c0303080403402440500c00040e540c0f070020680c17250203240300c0807116541e21469403c01000726040801c00903520280a550420007035040c0054510410303806072807984603100102e072240c295502807045544410106d400c40034083c42c072 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 103252410 1250 103251160 103251167
    0x503040f090516021c0c050f0a060b041404170310090c030914030c0d122003060f0108040803070e0f03061515040f0e07030b030a0b0f1b120612010606 66
    0x11102000441c082d183d1500d0102d0000449180541010200206202c42c1e036204548403407000c40241d0b418403503032030b03001007101c401c1c41580306043c010364020441034040c1b403d004c00d03510b1200600d00040340d070f0000c010201d443d03d1840742c003014088050396529101e44201c0207520404d40c110f903175454506007980070801c0c0c2591100b8901c0d8411a032080b11500070000d100d440b8040ea900300306043e00801c0310000c8042c4240c400040b142c92840001500440343e0301892072000780104440b05501000040c00154a0a41d10030800f1107001d280003001480c2036510301d4928040034150800740100070001c1c5040b903a0b420840909941d003e003c03900949801e40ba540741d2010308094060003400701c0300f41c40e4641d1203c2e40848068030140c0320900307100751070641101402000100070604143d40c0b090941c3d100d0317805010b0749601a0240200582d542001070b007d9200c0c0001501d002c0328208419440c00710b1207200401d4504d603180d138400b54046036480c1030114030304031001070405421b54038140703010401681 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 103253660 1250 103252410 103252421
    0x150908100501290a03050a06080d03061d061305060a03081612020c01020a020f0310020406080106020d05040f030213111603020114010f05091b040b0306040e0a030e0d0503040f09 78
    0x1412a0203d00028055a0300c03410140304111070407910300030003100c40d9030350090708015000100b5840005074556903070030340ca06000e0135070500d10010303454900c1008240000700c0020940c552004080d00e003420213500248031414a1216040c05944484c00030394580d84a401c07200085801007103090740d49002200460b03809100480481d00a03040302c001804c80341c40081c41080210041c0c0082c4500341c5940c08200e07042034022032185d0705100c3c84c4054000c090030340c0042c000805040e00c07856a19410114080d060980031003080d810010148010412416000c40601c201c0b501501c6603c0111020b00640d0058040c03032104086000300010001c010f498009840c82a9600903802048820044210910541020301c12444250119817003400310b4648540c080d40c11124130000141c0d102e03403c07085800b05401a03030050103070346408020001c0d182054020300c05210800c10141400b2022550060550815002420b001e9046203400c0c0040110401c111009050029110207500c5e40c0c40c01d50201800 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 103254910 1250 103253660 103253669
    0x110301090605100e0603180a080705011d0f03120a0902041401091401030203070905090a120207050f0619050c03090301141005180402010e0105071212061e150908100501 74
    0x84081000c283d20760b102c0d510b0001c03004e100612451464491444c543c501c020b0b21111401c0c01e020300480741001402040080100700d00c2a000481d4200543c070388060340c4510701710310310900d400040b400e40c1c140c00c0c003104950828002d0200c442c181e07210f00b581c034401004900d800a402c28030340034008840440c1e140701d4a04858030100140000381071130b0341c40703645500b00780300003500350340442c80601c00101c40e50480c9612a20344400c5444d2440305460f490b07008a880c203c00809a04525002c0c002130510108850030640b0a0301c007a45008102d01100341380c00e00a050f41c0f001c011012507800c00c041414000c0b00c0248030018000d201da40203807106640158815914181240c000310f1001445003050801482c24a04e410307564603569450360015030700318940030111030411004210400000b0034032281c2c0c0450781c0b86640c5140e0300c05140c0c0c5050b4215502e0b508014803010070b02005c01c841d02c040840c10750507150b01d2400c0501e03a10506005895851050300310950718022814501591002035200c03e0407513 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 103256160 1250 103254910 103254919
    0x6270b0103051b011b03020a150b01031b0806010e010908010c020c040f09030203180a051c06050718031113020f19030b1018090c02010b18070507020d0303110301090605 74
    0x1581c03204030f11a18400460240340c0441d9085604030b203c1e0100c08900821503000e80140d0f002d550007a600c4100303039510065000f40e20f42c1d403610400d5032035a161086401901ca01d042d80030002c41082c5000d444040300034605c50402c0041003800300240d21400340040100400c1d002071145d400c0710203019440b03810318800319009600d49010031408100e14010031000310342507009146040070150505d000300400c0d540300750b005946064001015101c1447e40c40e9202c424115000201c20b10340341c00e50642303e0143c040010040c6e4181c0c082a010070340d100c0d50040304da00c00640c4a090440b500807880202d81e400c015840c1e28230100b45100c5088994001302405109000010281a0264400d404845115140e04d42007007940d407000c02c60500885551b02d0302c0c1c070580d00c41c3c880140c1d929102420f0b5050403c2c2140180d44544c52601d643c100440b05400008001202074110b107440c440081c0540111113000c0d03c00d40b800c005c0b2b9003c2c903009500c1003014189a45d185541d0750386034a820350190032030f0f1103003074000c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 103257410 1250 103256160 103256173
    0xb09130303150302100f05070206070b012303030d02090114040311010f03140f0a0b120115140d0204021c050106090f1403070b0a0e0a0905060a080601080a06270b010305 74
    0x440c10000a010b055990080400701c15800e640004c491080030000d40d6400d0110801c048030141e2382c0c00b006000020b1069a0090b015810841a0362078104c01c50f40d102c0311074100b014580459078000c03007540d00300e52580c540141c84114501c0102c9864424002494480800160100034080301640b00e1030080f40c281c80b0340402e004520011070803a91400561043c4016030008145820a10043c0ba070300301080f01008030350103000a001075400c0c0c0310385076400010307036403603812081640800c200403006103201c1c29603810703007082640410303044004100000d1195500080100c0c03100240b2149240315603803000104010361715a41d01800b458a0340c003415603030308080c0c1e0000034100003958500010100142c00740030040d00d0640403d51607003000c80e09905000b02c036400c140e502d07158601d080700144080f100116450400f00c042c0319040446420140392a00710000600041100243c0c85905035400000007a0040d071040420b400c840e8508582082c00c50b1031180c00040c8a0403100360b41c10380740190180c488 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 103258660 1250 103257410 103257431
    0x20d060506030f151f030c080c040b04030210090e04060509190f0f021f0302040312080903161b0608040302060601030e0c060c100e07090506010203030112080a02010b09130303 77
    0x10140000c032810f5051038403050010b040420381d007801c0128014040c0011102c144100c1c0c03440180f038500c0d03a2100010b0b54401c002c14420761710016194021300310180c40362500781880d6035524607101d43e01019004441d42081002c0035449540440e0013001d03850145116820103103009006842c0540d4004043d20075080550b4a9819062403014519404100341141440569400c0e032030280e940000e80e0f0220300c000e004245882103040300c09003210990f400680e11800c42c501705111050406410303040041003010400303d60000411219502071f170000807a01c84001c2c0c5000480240c03028001000d10100c01c2001074142c0d045203840313005902c65000d03603a440c3d454000441c02c541c00440c550110b80d200d00c54080590800b40c2c004c0102d2030b950415905408001c6d504c0034180c1c0c1d1007030600c2109511036201000010030340d00c949904944248042c5246500d8410240c03403e60036218094441080001c0c0494824000d500510109074060f000d114685400d21401d0750000c0c000d4009da0101e400c0004118 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 103259910 1250 103258660 103258669
    0x605030105031b031e211201060c02010e0406172407050d0b0402040906050913030206071103090d0f030824040b030109021503150103140a020a0c0f05010c0f020a020a0506030c0405090109020d0605 86
    0x1d01c7c21500400741d202503132a20204848841e0700c440c060b418018240040045030b1624000c2c6c00c0585010109409000700e00385540e0720785103e503594031000c0403000c00c0c40d01d4501484038645030094240c1c9081c907111071030609010010059842d440e07520a100050014186030304d6000b0604a49084568442c280e0390500c21030750b9051645c20050060f0005000203000d80c0c002c3d0310000102c0e256800300d80c14101d1040104a800c4444602501c0c0050045081d004040c0d0101d00594082e004248592400400108120510101c801d0350b5105a03103030225a405900e00350310141e07241e0380050402110010701200c802003130748159030402e2110000b04540e096035000b8010b035a80104000382040c4140e4070510104001e400c0070141c00704014616a00320003044880e0a064a89030007130000042501e000c140190010401681ca403095411003803241c80036175240c0d600c0b00202d42065410954030b903100400b4907014400ea4002585c08040040042440d040b203038003900c13102d07154010030010181c40e0030420 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 103261160 1250 103259910 103259917
    0x30901050115020f0706030c030e01022818060c020d05030307080a0b0a03080702040216230d0e01080a15080d02010605090f0f010b0c07210605010605030105031b031e21 74
    0x81c0c2d41944a88806c01c003403446548804864051880e00043c0125142c03600ea09990259410141400c10303413071000601c0440c2207003652010b01a0400724041c4120407a449480781045c8200d00500030041e00300025500c4122902d1038940e8403c041c1c0e69039103010070001c4c1815400780d850071469403820040c1c0100b410075117082000d80e50810344e44d5051009940c04c01003e94010100240880052229440000d00c480f14400700300722014500401d04141c1d0302000c1ca0081c91b060761904001c0481c0742e807032160341c00111040e0455000000400c4080c11609440c61544469011440034401d00740481c01280c0c0c190b020030700351001180c1400150b10703500303a401c2003100e05803884004400c2c29801003100104030002013400b12031080a540c0c4180c1c3d5001403c13009000c4244a007046100b10401d401042518440c05000d40181d050031402c5505141c0425524091b800141d1408007500b07035801c450b5507040000e801003400000e04400c010308040080b0340c84001c0f044100524003490f105401d900104101038 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 103262410 1250 103261160 103261183
    0x21060f050402030406020c0601230a1203030216020a17061e1303020705040f0e060601030903050906090d0b0a230402030c090c0d090b060f040509060403200303090105011502 76
    0x95060030304000c00c010081d8805007049500c15800c000c070030807020040c09046d00a0000d0203140f402d80080141500d00142c44c1c07a285449030b034121400f841540140c0031030141146d09031030010384038035641e200049550342411740a0340c049014100040e640e05e0194031003401d5030711f580540d045500c0740340c211a00e2a145558800266001e038000508042603100180394460091045a140380c0e9240045400c40f9940a4000b15154031441d0704c0407501d03002c1110540149082c03a08104640b0700d038030002c00c1c174020160980d100e1200050100c0d256612401d03101500c54100a40c1503040c2403080c40440100003d640044e840110303c01040404840101a148101d8000e800390100303d14000800020003c01040341c0c415001c02c0c00095410010f900c03d0403079007031180e0070107081420440c08100b0134806507072165100d00e041a0810200729404580c0c1078000740c0c94140600c5601c0c2d024028460780b1002000c0c003030f04c1d1001004001c052501504524102c9402000c06040f520044c0422616445074422 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 103263660 1250 103262410 103262429
    0x90f09090c0108040c0e01080307020a060206040201021002030c0c0708010518071d1801091a0901061211010c0b0405061608010303021b0a051c0c050a052b0605072106 73
    0x14001415409010a1907101744981140c0e6403041d00c904405034446c000f80c103c007010b54000300e001011814049050400350403940001e22503460036900003543c83c107061282100b03d940200109014034824810303125103444960075541041d8940920318000e040c1103480e4100801c4c203011203030140c1004141d10050307070b0708602191050542d102045001003005808907104c501c2d0301b01c1320400140c0038420700a5540c403841207449514141ca07200141000301402440e5164542a4100484440500404203142d0b11900b00c03008130f0103040045c0c03680060010050b1020040c0b070100000c20601095061155103010001e00001d28295000c0742c1c0c0800174000280980e1102014543c030001166214440b240700a080a0860351501c0208103459143e00b41002182110950001041208840203010f00310035915120308031324110008440e0000c809050200c1c0c0000c090080001018a11801280c0c5e080501840b150404c071400400d078808149100003014401064801d84640340d008100c201c0ba1a0311 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 103264910 1250 103263660 103263673
    0x40801020f070c0b04081e07051507030f0f0f14040812030a050a0209010804020904060b062a0303040c170304030615051008240f1008091216031d030106030602090f0909 74
    0x41d101d050b0b1f100c102d044642c0d50300c43e071800080d0755660301020301080c40010030f505c3d40310390300c626002d028040d20107022001c4c400c002400301521503000d9100c00202a051500ca0000f040c4948410070b03622468000c480a402502d44001750401500001c5009010300340e010403071039a900380c46c1d4040303020346000a400940c61001240140c6001d00b046074000e03014110015914075500c00250300e940c031400c018902c0c1030301032000704c2140c2101000e5090130701024025600c0c5180c60f50f902015070f0320074014000010384200c100c0c0e40c410020410f540185034072040400c00d1541c030142804c00c40d4103074810103201d01c0108507840202d5204040850144d00d6200602000c013850541850301151020f50a507000410031312403809550f01e1144032255000141c680d500030f8200003c9030340c180720b005038410802040c20000074014024200711112016050302c1c1c42c155001881209485e005449414503505609002010050100c80c0c1e0091841600071161001d0300d03056102448184c45048607011010b80110 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 103266160 1250 103264910 103264933
    0x30b010b03092410120503030a0905100222090212011703090d0b01050405130302120901030b04020c0c03100e070306090809030706080907050105030103080a030908040801020f070c0b0408 82
    0x40007440d040300364107050740c8001d150005122500f200418101c0c0003411001d0503c03500040500a100c0039081d0079003440c00854568640310f54174400a01440030441e52149090180030060200550800d81c1440c01c0d90740b544d14071000321a60602000090382280610000144500c41c3d208a400e890b01140140406070300c0c00b81800c01480b07482e600c91110f40810002ca21b00b982d243c0c204d200095120751925020344d410002404111500285000c4561507070401070030100e03800003039030750066207580c4101d0760365000440102c003c1c010180c030389504540042201c00006801240c052000c000c107400b147c0c0401e0940c000c0030150f541c6100000b4031a000001e05201181c499040004003d01600c2d07054680030b100408a441e11089522100006540d0310600006500500400d0001d10f002d103012400c550440d1120211407090300044c40606603101d8003036040060300c030140c50080444000841d101c0460319009a070a502110003201e0007a00604042001603059080c1c6050b642c103c0020310904048 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 103267410 1250 103266160 103266179
    0x30a020d02031002070f0b060d080d090618030507030810050d0803060d0b0108160e04080d0506030f0304090c110a0c060804080c0a120f080f2214030a0f030204030b01 73
    0x2850000c1e80c06010754400d2074030210081c001005103912405418036485214240500c44100203816148218a6810554080740c0b8400681d00c600e94a5000018200a589890b00c0141b000323011228404901810f03003401d0540041c05460104d010b5110a0031175503d48226265681d028001d6680c040c00c10301c07a082c007207020031000c0c6901c4980608210030050303d60300c820300c0b0300d0004d80c0703d14100ea2003d62528404491842c840004001e0f54803049014105641c0c6c10f202406840382081d20240c0d10000038140e0340c0c08000c81c010748000c030029a580c980e150f070810300250040340940408200440200448003100040000641e078100000721020b504140c8100c4000744090000e4903142010302403401c038a4414031540781d00c00d02c551101024000c21100c007419080c0702c81407040c14003011008003c40b40c039842e511103600501000d40914884680207203400e0140602c00050000340d40c0d1500c0309098100040103144095268075080740080c0741740c0048084c1c5c820340c0001401c03080d0007401003051582 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 103268660 1250 103267410 103267429
    0x200304120c0902030103080403030f030204030803190906090813050306010e0103080c10020409020706050105040e0d030b0d0803090a020f12070909031b151d0312040309080f070602070e06030a02 85
    0x10072200c5080070360ba200198816604280c000b41c5029200042c20230415410040324150000141010360401e0300d5070306ca1404602000300115041002e00785e203100103005941c002e008182d48910108500200da0800c1811030b0440544040a400703044004255890001489030480d00c0c58000d066080e0300750f6039041c03242c0e000310914030b1451080500b08016003840303001030806000302a80040c0c81e4007881c140082921010f07070013113000c0e514000050058030310114a40420b00c546040114000c8031f40307008034414401c00c030406042008044188070320301030045149101d140c022100b24a0700b488e1841046030001142c60a051710b54000700b001c12907003a450b0800854180641050a614a07041c2c0352035000c0e040440c4100ca00a40f80030341c0000040f11445019a03201d02c8a038100d000c00f20312010319580303120300040b00d5201040d00000070105482600c03800c0140840f4002d66018030b0744000c1d00c2d5601c000a02031000503020306203004c02c1e042800d180d0b0510800b00140186201e040c139800b800110702 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 103269910 1250 103268660 103268663
    0x9180c0a0b0906160b010306090507240806010516050f0606030d0c060c0c02040504050114150a03110d0507060f030e06041e02030a0605130303060801020a0206060915030d030c20030412 81
    0x107240b20304d460201758100d50242c020b500410020440380c1087c607040b41082e8858100501c14180752222a240d41014240d2040040540c2000101921000b005071584d010b200814050a90440154001c20501241001050700c8543c11241240c80e880205034a07112110860400640040078440214405400c8840c0c06005824940400710981d0082070540c0d070211004d80d49607445890b0140b8440c0c107040041e5010346c81c0100b0851803c03000002a4032119503210182c942c8200024105040d41c410000031400ca62020031280d0300c990354480038006000013411080464903100c449000010040760103031143e0b038000d0a55003840c80404403000e60300c08194084c0d8040c030440c0070403000101140b00340d41c014400354032260311141c041d00d0010f080d12026040180b4990052050f0500d49800113245074000600f201c0302e00d659070300c24000ea04001104805583d2500c07803084000d156507010390080c03d0520290b42c60440b403203241c0d6503540120005900d0320085900404c41000030300c42485990404170b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 103271160 1250 103269910 103269937
    0x50f030a02090d0605040218060109060f050d09060e0706090506090402030405030c011521050d0e0d081201060306050607030c120908071707060206011202100e09180c0a0b0906 77
    0x11031080003042c0c2125020783c00715000b5a0729400d210a40c507092480151809040905c41c00350700d0144002403078803c10344a0b050034400030121680d42c83c0e008205517012600c118100b0000d4503182e0400601824456100807268040da29000c5103039842a40c4040903680701070420f0f8a891901d44c2448000d5100500690710386c0014400f40000040a001c0c2144804144d44d20805141c145418444c11000309040709421044140c446800140080f40d907607020221400c3c481141d034070880209281001546008100d0500021441041c01d0680800c0e814ac2c3c60b203541c01c000040d16101800000d204021015001c154005003070000100e003482c1d241d00350225481c10842c041d0b9581549072902007540c02a0412050132000147c011800f042480c00a01d40c9100801d00ca51504000008181192a0290056003502e00b4001c00d5401003000c4107580303101074158145454100c01c1000d5088061018442c01d0003103440c01600c034640030000b1800d071410602218501040700b010041c0a078040d04504004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 103272410 1250 103271160 103271167
    0x702120a050412060b030c030a0b130515010605040905010902070f061d03160b06030304030209010b09010201140a051522090f020301110d150b0301050d05010605041d0705030d050f030a02 82
    0x5400c1156040320b429031240343e010070040310701c00070542843c8202e02d01f0341c0240c1c00003403a01c0c04110340b52001d54004549042c850320b0345281c1d041c00c606041862803100c4582c00001c1c00004c03602c0e4460005c20803144019400c0000e41d813a084500c1c1644030b60b40010b4002a03c0382c44207070104da030940c48203e401441c03007030000d42510011000790440c3c01c010100c6100100140d000c8080c0505290150751101c0200c02644c5001e041d5030024000718018082c00c030b0b0010b0701045940c0564000d5000f000703144283d00d540c2c0ba43d46040c1c1048800f0740411158000040d0302c1020741c40e0b0900b4003200d00150100c1010f200740c00c444c00d40c003e01004000d034040c140d640c5800c4000c80000768400b032080102505c004d00c0366540c0c48082d1000f00c0150b802c1c49510940041c9000e50410501000005403410b40d801199444211811402e2040c050035260f00150351203441c1104c4e10411089104002c60425006000d07140031540c3c80082548030380e204150400800e2040040721a440f210388000d40d440009000c00508 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 103273660 1250 103272410 103272419
    0x90703171c1802040506060c0304180f0501090b030d020109051e0312040308040c080a08030a05070c0209070221090303160203100f0f050a0506280b1207030b090702120a0504 76
    0xb41d6524281040d407086102080105500301809104d600070010340b030003450b01c4d00d4031500350342c0e80c843c40c8140391030fa02841e01d54144d0001150054885032460100500030780d49c55040c02d5000304100d00c0c40501c60300c10ba2a200304400c1c018065402d006402030302078180404120303070680c1c40118812100c517060004015070202852002c2d036150203103000c8d65402c2d03840d2030240786c4034001c8552508130702001e500c4198280700146510707049a601c210000000301b00c1c1d488004068130400d06000c1c3c000d5110b028201003000c602e900044540301060f0700100d1040060a24512103a02e10403411042e41541041050040d0b1955801800541a1018044618800b450a0801e044408800b52404065214030080e200350440d40a82a0007140076030b0100050b08024000031155140b00400100c0c0c107684448400015100c003202c84d0007000d40707c0312188d542c08041a8100c01c0c031021102d080c0440d1a0a66400d0107080113010340d4800c1103150002c01e000303094000e001c050f54100400c0e40080010410011a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 103274910 1250 103273660 103273717
    0x4020403050c01080705040e130809062106060c19080c060a0203040314030702031b0106080d1107060e0319061d030a0201050105041806050408190c0b09070317 70
    0x4000c0d40240050211040b15500050101d6806011407042050522040c0038802c1000c59141e0040d141da14060003440741032914803014014290720030b90142c000308400044240c2004100b840285211501e001c5586031002c002d440c0c000c680e802002a03010850070b00030b0000c2c2c070000b0005107000c1c08803c0e081c20f1520302154500141150701c414550740102c284420141c100f24002074142030b00606a0031444d007603c0003036490051009107240d210300386c00300d400d0a220030b62050001d23010850985100c130030301a070054804501c01200c28010310900b44005801c0748540b00b0300c0b00d0742c80c00901038403aa904100c0c40c4160040740000a6070310a944482c1200e81c140306170a0b406241c1140700c0915160480440080d0071100d05a1085004a0512034a0301702c14a2000c41c000800d40d01c0180014541c4860809109900a294860b20440221442c003680c407600464091040b520030007407040c1e10365880038880d480310007510004211104503a034540c440b101c1c0d607004d41800c08401c044103e91526811800 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 103276160 1250 103274910 103274917
    0x40f0e150616050705061c2d06050f0301060501050316030e0607090302041d0d0302070602041206150906030b0c0703030b09010b0d0e0a0c060e030703170a0e011701050114090402 78
    0x2901030181d01d0650740304004040c1305450042030308031012401c050085a022192001d00905900e0081d40c5403806052545100c44c010300c64008035800e031904c024124034400040a09008480c40f8030340d00c142c042c140b031505000343c00640c0c2069440340e05540300c1080b03900690b8500d6609601741900d810690104d400300300a2288105100e0341c0781ca142a01e58014042200c0d50981c001d41c6a0284100c0044404800968403000070b08074580182d580780281081c00003070180342c11a040c00c000c001903010a02c032050300320446218801c0414104555514a800308490980c40000c1074481c83c0e4001a1021090348050300c45940241004944034000400049100009810030801c450001c01d4030044440e01e0f200700003515410900411084a40d502e0708a01840d05125640822008005441c8184c40c01d1001800441d881170f040d1680203c0200b10784281c1d040724140c4000140b0f00c1200c1c084941c4102c25001e51003090b4000280d40f0b9090a004440078508514501c100341000c02000f083e075110b52004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 103277410 1250 103276160 103276177
    0xa0f02091f090b070f0b1e040209071106090109030f02030403031b021c05100f110409020a0915020c09060f0105070609020a1509080d080403020616030b0a06050d050c040f0e1506 78
    0x41441c41551a154864910140003078602c0032102e90031b5413002601f000d00c0c680043c1c049680802c140d40c0c4800880d0445ca1100700d800c024003568046c1b100345c8405401070940c3c00c1c800d03103410600c40182c0740100d950740140c1c400a000152a225240700b5004440005140b00e400900000164210394102080b401468801180d2540c88074135000c203050880d00c51000203454001d41809100c420810304e021901480c00380e1000c041d80024444c14250103500080000c0012900035414251301e11400b0351140d0f0506d84d0240a4015a000030711180741c09240904601e005840312070804003191180c200400c02c03030030226080b15080c00045140a036451031b0180184456030b40b540071600308030345a8100210810f200044c85a0b403018800002d40126109600415107280c10b0031101910804802410b80d900503250807940d030b0000495400da0240003441c9151485509020503200d011400d1290700c51485000080c2710459800d01c21100602d42c0b03075420002c44d034040c00c0c2c2c0d0310a10000840c80e500802da03 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 103278660 1250 103277410 103277423
    0x9062007060e01020306030703150b0301150303030507031e02072a050a0504020c030f030403020106030803070302040305010c0908030904022101090e1c08070e01021f050a0f02091f090b07 82
    0x3414801c11005005885441078004001d506506100010a076110318500004158000c0140c120707501e000903902c1484c0c40c610080080c4502042524900118007090000fa00000d09103000100298000d0240305a1300c2038904a28034542d0304411614025040303628101d03103089078030441000405401c1034100c01c0d103108500e94140c40703140204104140c16681e018500950041c04403000c0f6001c080103030341e455041000315591340d035a00e14049005040d0f541004140310804000e10405544c90b901920560344520020407903c4d545100640e462a11407141c01d040d5802001540c11509260f00940340010b240c0707a9030000b1045a010300008000c0980010b980a80c1d58054030b400440b04204284009804848152036420304100c0241a50002401601440224001c0740c80d5640308002c02070180381c02a40c00300c5903515900e0707804041e181c141c408003c51424842e142c680d46040784222140c0e50030080203000a81903440308441d08080244140c01030100900c00007500300c10100013010040d12405 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 103279910 1250 103278660 103278667
    0x70e030a0b0c0306010210140408070c0803030103060516031a1e0406030f1e0c090203040807020301021209011a01050d05070302130306050f15060703030915061d06010203130603090620 81
    0x4c00289840401e154068089041a0800c3c2c9844820590715030020381110050b030390b27503495040c0345006a0040d0300c201d0192100000000070b0000d02e1740550701403207101e40854800d4000a03400c40c281c80351300803103190130060b0354005080b80c50503140b0005080034807007901c010f908040001404988282d4000da80c1d11520102d0401003202d10703242501f81509028107244056503641300d031650551140110502d00380c0c0080403809000f4001e05403100c0c5c9a0060095656a07103000358410800e01c19601004151308200741c0448020a040c640440c030903041e994181030040300a10700d005800041c01da1018540c0c20030540c03204110f4900b81c4406103000300b00100e80e60805401046c40c0c40b00007010103454900c01c0002166940d90300d811683c002d501440c020600c143d183c144034440142025590b190280352010025a918542040b100182140c070424029599035800598591151403000381803280110340600405001e54400d44240380078080015544a0303542000d4198034034505803002909020 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 103281160 1250 103279910 103279921
    0x40b0a0504140f1014070c03050715020412020a0906210f0f031707090b07020103051b03090f0601050d03081605040f0e060325060c0303090803010e04020310090209070e030a0b0c03 79
    0x18003810517504000b10a440340ca251244000300800c0120787c004041007400030b440c1c0c044c0003207030f400c0000c1c405090108550365507407120f508105089060003280600c14100001558004900c540801c413191018000d0303a00d020a0348811a00c00307580d0044522140001e0300801081e55500c052400130700c691614002c0c40849000d02110640c005e00f90404c0040742c40c42442070205440c2075911450703080c203011a950305d845024024004446071401c440000100070040b60520000313000c44c00b41d03516815558641d03291004d11007c40080503016020030880b1001c10f0107920343c03800c400161042841c1c0142087e48803080395408045940c8108996503144051200c14a03041c018072075641a003e4007080070060001744610740500074030a200070300c144010b1103001c2c180240c01202e07005611000c0255203685844400340c01007015a4168000d1240306041c40118007988a952907032900144040c825a503049421142d40ca481a02e194241c0266092800066081c10302d00340220701041d041502d81c6400d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 103282410 1250 103281160 103281193
    0x20d05010b2107020a0f030201240f05031204140d0b09030405090919150204050a09050109060611030403020f040902060a0c11040213180212040b0618040b0a0504140f 73
    0xb40c000d402100e003078280a010425070002540b1301007903440302200001c9196401c050f40140540b1420030102071130407442c0050841d500240c4410380d100058009000380e01c903010b06070b4600007668110801c0e81c00f0030051041100080220419407002001000210000e9580d1114a0400d80720301045510209040c4007500e031141500e94002c0d0b000c001008a0b0002401c03803503020140c0f43d0701070143d44400039000241c4900750111006001c01602c1a0b02c1c05a40e400d90000030582482905403003803402c040810500c3c4a000552001d40302d410046061504640800500ea40800e075441d0344142d03500d100341d0040c1c9500307000c3c00a10005403a8182d015903d401d15150f4100081c0e0002d2103240304000d11020b14103c4c10040041e074601740500b10f90010500d03081802403058480300d83c4105441c0042000b04003080b0402d0f40b1512064402102c0142228540340711500151030080000f80c0c2400040c41c1d031015079102070341c480d006000d9010040340164180e81465111380703c0e024150810f44541d60f58281 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 103283660 1250 103282410 103282447
    0x503040c0603050c07030f14070302070806090c0a140d020d080c0615130b06041703030907050d02010f030c0e060f0403171206010804050a06020f070218090c0d06020d05010b 76
    0x103071400c081c0603900c0e11070088801846440c0004043c005100c180c4c1d5500e0703204240c1c1c4180d410491001c40e0380c8002d40e040c0070350384103000d1141c3c0c102c0d8400c1c040058100310021078040404280a0001500c450906482240c140d1017030f02c1130340e00042d44101e0034000da070b10b080c0c905035400e0145404665406e030036582141810300007000040700c036031111410707141a02c5030843c4400c080302840000070107850750300002b14148226480401e03584e1640300034007059130f008001540903840d80821559815a5403003442142c80b030b842c0000c1c0c045000b200d066040140290403030781e00901e1910300303d01081c1000c0e00041451b003080c0b803074454100010038240108019410f286030404505403007541022441d180c450422030004041c41d041100200c003290402204000da005560b50081c015511120a00d4040c4000c3c0c01002c8243c4c403903800c0c0414201c9a02c018210b65010300c0d0b0001c058902070504800380903080480202c00c4070707080c0c0e0030001c1500c9003d042c1f2030f45020309015103030b060741c607140c0112801c0f1040 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 103284910 1250 103283660 103283669
    0x50702030c01020c010e10021e01060501020712030818031303050303100506040e0112051c081b03070e060f040302150706050c040b0403030f26040201080a0b06030a1104050604060503040c 82
    0x51010b001404c45a80000702c510b5820400c03902414940710181c422418810a0a88145881004045101c199030190400020b0f03c1c0207908035000c4c42d41e07600c0c1120445044010242c08a522040841d6a985814120b04102000344040f05c0c41d00e00e181d150301404151690046e05c668001000f40711480f0200000341c0010082100c2203400d003401d10a0100b100a010301c156080001092044000c0000900880700b010910a0f0380034100a0030035006003281500b11540410030751401c00a0a4050041d0300303490003081c0c5541d40c460500c03002c0d4140645680201800c1501c410180000001a5200c9000400c0080402c84c15500c2e05900e103040e4050710300140c00560305803002e000501051199105490849416181c0584460456034040c0c800c03125041e0300b20342c0c8002c44102150300000c0c100c01c1e540158802e0b80d80705202e560340c0031024200ca0303002141c80d030b0112041010864025254020075494207214001514180d51000044d117680d105034803030401301d10301000304030602a96240030380041 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 103286160 1250 103284910 103284913
    0x4060501060906230c07050a0f0f05010f0804020d0206041e08280f0f060c020c100305090d080c12010f0305010c0305070905120c032413020a1214030a050702030c0102 73
    0x50b190710344112100b44c1c02c0790001d2020200070488000c5241d00708480001458058001c0500c641c65941d1206950502d004052028000c1038000072a5481140624010307807a0750b0b203c0603103031216403c1140d2201c11a0060342c0c0540107001c003250484138519140038a02a040c42c4007003191a080c54203003044680c58a0400702c1800fa40c031514442c400f22003035645158400210b860f0007850f4901001c80c2c0c02000300240505207048030f082c60881e00015200c03078290f4120b03008030030f1030803d490032001d90380c045400c0300d101d400a9000e21003032805030803140d42001c101c44005091580d40c00c03585d005404241c1c012148402c40c40420002c2c480c1c280f0076a81c50300010301e4103206620b031090000e00844014402c8034016443c140e1a079645aa0620000b00b1015004007070302d01344140e8040e400400b4100e03100d01c06000416078003144002100c450406091a4060010708026240244501072400d4071101a1403800c1206040451030344148014001c2989036112113494540f80d005051406c11101c4050381135 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 103287410 1250 103286160 103286177
    0x131407170c0303030103032a06021c110a0e0103090f051501090203251704030206061302031b070807060603120306080609062802030c0304170a120207140604060501060906 75
    0x1c549011040303a041d81c0d0182010744013400301074101c001d1401340405410f0440e01e562401820490290020314003600c00c4d40c4451600c00040303803061300b00c80e803045030500441010040308000a0040c0c0702c8040c802d0050400090f140e07626250000f008030100001c50b0190009044c4e4410710924111440c00341c019000114158509500b4400c1842c0850600e07104210315402040c245d030b403286074040d0075041c01e105d0b4140c85081c50b00c3c020303584034420354a540c41544800030a0790b4240507842500d1203072418210320924911002c032000d540303900c590400c0d61008803c1000c0c6001c280c9a02440c0000c0d40302d200343ca030301c000410000904407125500562110b41004c001d20154480002d0280d401c200c0c001d07001d100c0505c87d42c0d03001c031114101c00c0f40712900398008001c1100600a0794040d502c103900641c4044124212018800c0c15480341580c48401b18140c070071940c900ba0041e0303000d02401d40c8581403a9910614192140c2c0c47c003c1c007207400303d800c1601c4000601c29a80d005103002e00526142c1000f004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 103288660 1250 103287410 103287433
    0x507050c0a020d080f130905070c050c0402030601200705041112042a09021806030903040e040503160609050f060c09130b04150f0518010306020313140717 68
    0x1c4595910401074443d51080340d0400a0100c503404840d030203281001c066664010104640b01c0e540802e10031070306014501000200b01c0350040d50032410155100015203914800d00d07042000075000944a40e04001109005080280c000468441d41203c140300600200f4500710401c815102c503443d09421030102409031405400c074000020341c2040e40415140041a50012800d40d4010b10300481c040100c01c1c035200144180d810350043c9076402e00d501081d22207651000c18441c17580f00a56098019510400040040301d4004a0442d04248101d043c0c0740f0b041024555568441460082694000d41c0c640d400420410100081107500107200e001d0482880c00c00842c40050185120084c011880c5003040c0c0d5540906c0c0d84401140007005108201207004d080b025604584640180b2002105062000c100c82c90010909400e070090380d250320b10717581e003103580700b41c06500040d080342044501600441c0010715400b00361981208000c6c02402154501845075032004c40401640c420754100010004 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 103289910 1250 103288660 103288663
    0x1050a14040b01170a0c080108060103030221040504060f140904021e01020703050a1a090c030a0f060e06041b170a06050601020a1505040311190b06040f0213030203010507050c 77
    0x400e5150440d0009502c100440c0180d8040303014442c2c010313004548108011a44141da40b110000581d5651b6081807680c940607459550b0b00c00b800082c0159106414582c02d403c2200f8208201003110886582096a10300204050700c069030805070401a0f560b90501a910040c1d46c3d051030003c08842c00c1030303a42000e40110788103420854110380a94405a444142d6900800c14600119446800c80b180341c206810540c04280590040d0411204084042100c807000011036035210320b001806812850400c2d42c514090b810740c010212821621168500c00c81c08007070101c14880d1740208285400901e0303028030b944003c10980c114100c1c605800103185803040000419000040d8000700000c0c0c0d035250007005030301d00883c407000140441d4070354440e4a410b96590f00482c0c040e521030380310708051440104841d521a624941c0304103a00810107582400b0540031601d09070024000741000030000c40d6055080160380c00008000c244d01f2141c0720400440c2424810700368880c0340e070f02c0e08500b000d50540d20359 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 103291160 1250 103289910 103289939
    0xc0209010519120609030206060916050702010903060c0c020a0611030d09021801031514060f01080a0f0c020309090a060b39061b0903030d0e0106030203030a021501050a 74
    0x3070b0060a04001014091021041d44005030180035155240118203240070300140c000040110300501415000c9801402c00352001c0f4044d40000000b09000c100101046070f59070045e04090741001034104000020420911581c0c4600b4115510302080c00d4a50040c03045880403a80005d0812850301034605280c000801542d0381c5031902e00f004554080c0304c0c0001066a0084140b500540e59001d000100300b03c00c5502c0015201d501c4101480848002e01e00d40404c0341c0119202c82d00803498040359003081d80309611741503200b5010071f000122803001440c140c0031282c030300080c0c4000d81d00005d4a15035601e090842c69a001071152010710042d070808501c94001d010305c5200701980b111020b80c02130302100103010034494007040c054044c0a0906800d0311035951405a9648181c00d58003a40209801c4011085800844024004501c0c1c0904403104d04000c105140c484940d5569540c00400103079814001800010041d6000b0140140f0034510a04081d806900c503034800e012007602040b2103120326040 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 103292410 1250 103291160 103291169
    0x60a0210050c04150914060306010906030b12010c0527030712050f01021317070501080c070c05100201090302120304050c01050906090a0e0108280b06030304031703070806010c020901 80
    0x869a5201c1080d0325070036008940101d59080094040d11206030307404000601181c9403183e55071b02c1d850b140028403041c0e110030342e001800260420014410f00d4000d80040c40c101901a05a0060140502c44242116000f090000005a00264050450140c4116079203040038046803048001010000680c0d100c0d900d1040c1010300c0d2950982c0c0040c01410700400c844810800300a5503203000380141c55a41c182140240310550300c810541c002e007440c000910300c040d030b54182c480d80040d4941107d454540e070807100c000c44008840c1440854182c40e940c0d40300b14200690740001c24010020700c3e01034200701400340007044d40c5100740304102c0031500024024418440a003007080d40d51025801140007485200c0d0a907801c0764810b10001041f0100a05250407680b0302e100f0ba402810800c280f00004086074003000510a4011180d04049004401d401d6085400102120f1520361340f6031390310310010b400748800c071a001d1003c010000d41d65004180194400002d01e0f00c80c2140c1c4c504d42c00103000c500306025 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 103293660 1250 103292410 103292443
    0x3060f040e06012904060806040f050411040e0c0301090605070f0804030e0112021917010503030405010503010e07020a0209070305060117010e0a1a062701080606040306020a020a0b0103050604030e060a02 89
    0x5020301443d88a40308070405584026020741d280d450706d401502440b02a58098001e920f00b503c1c05e01c0d0031480f8495540130ba13511014009442c80300b2000c2101405042c010810140141f164213100313644c091045e040c215124070b8011500740f4041c0d1014080000006681c020700080f0001c200000354410204142e102c42400c2041c0026a9400394000a0142003d100c54184001844c05055a0404483c204180c0311640007031507070b070701e8a060685134061032242c1c17408a2014001801015074a941456104820784111035005145400081828070142c4d8100080b0742c1c0e800a0000c1945d121800c00c0810021506000389540f400f000c404526000420000103503598810a0381000d800b10701d5103514031801090542c850076640010406218842c140c09a0300c0c00c1c4025002280d4082d404007842802c000b040941041d00d56100c02e40a0b620500c1c01070114024862030800196200055030702950003403004104c80e00e09454040d00420f054190580306d01030510034210340a5000541e03031442800700c0c8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 103294910 1250 103293660 103293689
    0x405010501050a1d120a02240403030e04020d050117070f0608040f030c02060408070e0f100e04050a0b15040c1106061207030501050108030a0f0f02060c07240203060f040e0601 77
    0x10300d00d40e50f50b80540750b11741c84100012a1044250006040e40802d4021124102008a602c035995a031215a1207010b0090302c0610080001c2400f0754000d03503290102810161800080c18890b01c1251340c00d0b00058cc4c010703107a110300c90b030900003041244044c0110803100329486051108c050400348009200508600b6005819020903100307021a05407658003034100c54075551175050b0f4a890394818010802e49900010005610641014429020380e516000080780e00d0308003240c210420000600564051040440c0075002550408185102d20074030104c1c050007803403901c100000d0f03a9800d0203074004c06c01400007201c81030b0808140c1581103a011651400e98278820b040750303424800c8550004d086135180000020358100301000410100c00c07980e071840702c008600b5030256020304000d0b40030320040e4002c0b40016541441a0001c2040c43d01440f0b10302c0d0120001d000d4201e4029480f80c031208615004030900c100750610302c142201071102100d0070b1002c90680005113556200502c00c5510040740e25 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 103296160 1250 103294910 103294937
    0x601030b180604030305150409120f02070b03010306060302010e030607120c020c04050c07050f06040c0e0604091401060810020702060708030403142b0603110f0f0d050c0f0405010501050a 82
    0x350188250700d4848401d490442c50103080190080400319280502c040a13007038181e00074945480f03440000f543c82004120105001d01080324036805285200301540300d0f0700c0c0e0100d0590703d044080c500071486080c000c00c0d00f0342140700040c484c0c00303041400c0d8041d5110303006111507207411011480140d891080c2c00078250b1580d05080340341140303041d9a03942151821040c810071002c1c80c4002c2c0b5400d4010760440700071030711144140382d9402c2d0440d0003510510740c43e00107006070724600c0a5a5000300c0006e20200c1c0d8103106440313002111140800301c441c103a5440c0ca040220301010301402e1095840f401086041134295008250a40304280004240060000000d030400d400340b4059044003290700340e4036444811440c010711400100c40501c01c0901282040103080300e0070f0b80240030a60303510154001a80e42400244040030007a044295880011074a0720a00340d02d40740c041c0d1984900a00c01014490b95241c01d00c0b070503220100721607004506000040c8000d9230000111100f820407442c2940c3c60359644c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 103297410 1250 103296160 103296181
    0x30626100b0f10140a08041703040201020d081509070f02060105030706020c09040204020f030103050a060b0316091a0411040e0c0403051c03060b030f040b0f0f1303021c0207170f0601030b 82
    0x20135903450b41440081001c04650303a100c0d0380203100310f2050300c05c550880806500319200340011170f0024010f81c060026034000713038801c01a80342c200110040d6258084c01040c0000c0da44603013240d180001038040454801072a03810004503004000640140680354100b2100035150700000d64494040c1c01d844021a00710744545d81260700440503140711507101d586900e811074940d510320605603100c504000e1301c000645001b00d110010090141410440f5038940409007020f4070645030501d8030340140510489203502c0c1d9005003114102400707480d40d80c450a280700001012005007104204401c18001440002d1001512480b14207101e6a0810000ca502d081280607200c02e0300050241e000100030f014004440610007030181c2c2c4101c07a4006590781e07079084101c64a40c101d03540300000704864003140748042d80140000c00c1501031b20603685411203440300340c19582c04030b90800006a103ea2010030500743c102203800240684000941024a00078083c0b503518203040c00041c101e60220b0f404160690403 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 103298660 1250 103297410 103297427
    0x50306060c070e07171e0609040821010906080a0f140307050a0834060b04020c01140429060919050f0106030e070614030601030626100b0f10 62
    0x1600419803182e1a007514010560182101c4142c1003603250004144d06c0c3c0ca03e4070841980da441d102d00e101950b62085d04100c41c40c0c10180040c1e504e14000c001000550308900e40380d1004084000070301d201035242c40d10240842d0903030b030300102d0390303800c001510350010b0410440c0d15442d60b0054260b00c2c5000c0c0c6541100d09500c0b884100902520070241003004205d00306014100b4102d0304412030013404100200900d03081c4000701c0402c5060703451a45100041c1c0e85501c40c038070700803001c1c01c01414010450348290854075024002d0f00b614152108000800603011030502204111801560340103100c10703401407203990007a00191003140460001000462134100703115041007a06000e11513410242d0b8421200da60038020300c800242400341c1c1100081000130750b0411142d035591072240301e0411080c41c4949820103031109042580b16800055602202c04040b8a0074a5a00c581d449aa00346040d0914061801183c21801818100c501200d651441c0702075401c4803007500c3c5080284000c0030f080741c0210 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 103299910 1250 103298660 103298669
    0xb06010908030406031a0f030d030f020f13050307060203070305030106030b0609210106060201020f09090402041401030b011e0f0506030415180302010f110307050d02070c030609030e0907050306060c07 88
    0x400400c000411360380c150406480e000c80b03502c510070550205004e015246801c2c580041c0c059201c540c1d0a01858825171080e0500c2c501c0d50300040c05c05010f00316480e520b502444500d1200c21a818041c0401d00d801d01440300280542e0005520300700c460782d005082800144a58400d05907580c00ca429a51034400468243c440c004203220081650202080c01c18942d1031001c00700c540c83d0400c08900302c1d00520880e060014510741460500d04c11404001d91a8001401240c00c141c445810308100c1c2900542c1078042c500c2a15840c0666050811440c88009050089040501c09882c20800c0910319035081007603d07030030b6032459544da07902c0c03e050b014661814890f0301541e20740b0000d424044046851100242d1181d40240403024a016018050700c0f003c40840d40c0d10b030720400c00700d010940140020480c0c00004031002d801c00140da1501d907448410b80d8025580c241d1904880300c1015400b0f100e00501d038500312044400c0b07042c10714000305907000040840f40201c00000e4184a00c2d4010400d0f24001c1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 103301160 1250 103299910 103299913
    0x61303080a11060609070915030b030106060203092707200a0309051c1502071406010b0a0801080d09090209010c051f060f150e040b0405040308100b0702030a0b06010908 74
    0xa005401d0020300c42500840110254015000882c1e42ca00d0030300343da540a183d259503202c6000d8180101c070b550400046007581e09160351142c0500a50301c080c09003400900e515000f658641001034103000c1504174201110300f0700c43c8000a03c2e540280d9443d2a56007000d0700d4a0301d00315006141e00c002c05901c1c91110001d4152007204041c404050b0b001031000d0a548081d00c0c0303134408900a9840342042141000b0003080440d07000d010b024202e01950245c1000c6002e03000310600ea10448415906288080c1c22584640c5000a809405660080c5800c0d00402414005050b85a02c0960050880743c07a400340480d41d50b000101c03491546e100701052101503403c401a9809140780c0d90300590a0410041d811401a00b04032000a030254101185002c9600f0044a603060008905003100c0300050070403041d40c86681c9000790200d03a11280b140c40d2060388240c0b00c0400e242001003280e5011030642c0e10850100000b01700080040c3c5000c6000c030144c9502040405642c1c0790100181d0700301d0000e42201016 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 103302410 1250 103301160 103301167
    0x70f030c0204092105120105040c0903020d11010806120c0904080415020606091003031d030a0b09030a111b01050f1b0a061505011707110708070501080a0501060e06130308 75
    0x41c1302100d071041001e1000009602030800b0b4030b1009031003c1c01211aa901c0032056240108003a0409030800b504118051418045540e101d60000740c0010f4a8401030f2002001c0c0003403c2900c0d60407182480d013042045501c8624003502100307240c3e48440700010603008000f0b10021030200002d800c1990040c0450318a40c404460300004000d40c0d860007150030030322031484200410b031500804400300e4103880c0c043e560b0301a07119000504940c0303004a1a489609803054040c114003158207039064034015103001d80230315501c03680384500418692108600600b82d8000c00d6914040b000c240c1e624441d00c90302030074070a440703140c5046104818090104101204660310b808120100400f00e00240002d10842082101e211040f1020400b580240202c03070109250340c03148505402b04200b01c50b0321202c01d02e46504200308d22039019040c14050b51204202d0352203900d00303001568009161941c40042080f04110715031400d44001c1540b9040101c140c081c1400040d618000c01e00c0030500b40280d604001c1043e075 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 103303660 1250 103302410 103302413
    0x1030b040f1401050405090d0813021c02090f10061206080303150109170d030f020d0c081e101505120106050712021524030703050f010b15070f030c020409 68
    0x25040c4660b0007000c040c107040000c95075161900c142801012110010410060300324002d03205030b400981001c82401030741503c1001a0388909840e4158402041842d070000c1851050121110000d010341159451010401003a00b004003420821a00607107046d807550462201800001d04640c2c00c140c0031400300000304151100c10301010269013000707036984480f5940e2280b1503540100303030582115140d003000c940e182000b4403030380014044c0c0d141100300610704034040782c04000f2200024940300c00700da421010840c1d611034010340c80302d03048991000500d891800842c000803103070700c0303003d4821810b50100d142d2400600c44ca01b540c22212048407038510550712640c014240350882241100d81e0032810340382c1d0756403038800b0501070201d44407900c031002992140c0304401c070448546602003048110340003884a1650b41000503800440c080d074003030191a0040d4003810b0947e00712a503114000d40080045041c1c0c0d180250486040c0c98000c1c128414005041c9000c0310102800036010b94498244140e410 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 103304910 1250 103303660 103303691
    0x524041a090c04050a06020304060f0507060e032b060602070e071e0504180218040e0f070b030603060106030e060f070201021201150906022109120d08010305120405060d0b01030b04 79
    0x30680d4001c0b6240d20007146d0701c8108903601d108038041e40c000074102d20319404100d40900090105544141c0c0003051802001e031455107950458a441c2c119154007410711140402c003d000250010101e401c14001e003414000040e645070b806104800040c0715070400184120f01c1a003c1c216000c8083d03c82c1c00507074000e07441c010300c250000e029804140400000c4190485807030b200310b030007410b1401100f84148846804010040c101400c1548090003440705140c0803400c148505c0c8058a0449140c035205e041c40420f16291250503007000040c58908200c1d060121340000780d1035409040003408250365070720514100c0c068000c801884e00700c100441c0000c20f00195203150746107400201d503103410b0220780c2d405089a980c40c040e0200c890007660214142102c002000c024180401c0150050306034000241100d494107501c00740020000d03032120b006004000e020700c0b01c1d010a013132200d51141000c0c00c10700003695500c18141d009400710780e030b9060a05a64002d401001c07410000070b2041110f10034900f03111 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 103306160 1250 103304910 103304917
    0x90506040b100504090c09020d0e1213080708060c0304080d0c080f160504140f09100807080307051c0c0c03030207060219080403031b060509010f0524041a090c 70
    0x601e0b010340b05035008940c0341828070030394640c03541000d1100c41203440d00380804002d5001c008150801e036101c0088450b4000208440805200422038040c0d80f01c250070301800071042d0341e420412442d0131200c400c100c1744600003012600311040500050340e0340c540340b5118040703224032840041200e00b01074050250b107070400006845150590401085a82c0d400c020001e00c2d4013240089022440a000c188010315035031018500148001d082800d1480700300000a12845080301ca0341451208028103000c0b0b0441404600003c01c5485c3c015070812556555440d102c510341c00d2103c0c9020b02101a85410078440c1c41c02242d0541c00c103c8082560b610303414000d44031010b901030000035104805d143c0c0e074103000c20020286400c2d08a501d2508040c1940d40490b20f1194041c2c1c0c01e50100c104810311000b103440da100b03d5020310100c400014051822461030310035103100410314041000b1303000c0011030b0000d1407030380c6943c03840341290b0005004140c0c14074685012000c42c0742941108130902008014510311008 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 103307410 1250 103306160 103306171
    0x807090c0302090102070608060103200901110a0b0705031314010f0501080c01050403060c181202030c09130f022d040506030f0307060b01031b03091713030312090506040b 75
    0x910001400003025400d9228000701140103070310880040200301d1082c0801c3c3e0700280140340c00b0452240c034003410340c00003000c012417007880b00002800d80a19a0001598504443c0da080540180e8103203480360049514001c6c11041445000400100000008000000c0065012994071041c0c10200b16181c02032010141101d04181b034400049250314001555030682c1405948641c581411070f81c501000d01064944c0e44248040a070403072101010424251024003503140c1c0c60712808141d8010503151450901c076041c000d098070400e020488401000841c0c1a607041240ea625552452000c5040302000480c88004420a842550031001440204c0032648008540600054444804054132001c280103c00c103660300c1007040b00b0000b6810f800c0200725000506000031084580c00c0048034042a01640500203566808103108001c06445c50300c2c0201e400104032810149174051080021180340000b43c1880540c0001d42a003100e42e410100039254040c0c25110641428034152081d138805a80703 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 103308660 1250 103307410 103307429
    0x70606050402031003110a03060c05030f010f0501080103110d0507091d0303090a15060302132c030a110304170303071707050729190c0e06090f06040e010807 69
    0x4000303020724081c02501c1c0140f40003245084490714580d6000000c0d120312078031a070040600c200020110740d01c0e11403150710b0107090f00c0301680c0785091030348991030550581040880ca40c00050a2005036804021035040da0b900410315100400c0d48000101c401c520307511300400038400d414001c203111032030f600200d0420200204980390060030b42d1016489000807a281c5400e603000c094048003040e040000c605030182c0c0300c04002052912600851044d517580000c080e880740d02d45060004482c070303950741d41c02113100c1850304098900060704130607142e124140406081005504031200708200c1803040f41c0041210000350070f003040c2a40c0e030003a125001250841c0110704c3c280d600b80404058560800c0c070589455544a00c0c2001c9959801003604541d402c0201e221100c070851305008110700740d298042c0f080b954020f100d49a0b103540f0841990ba24215070320410a80184501031500d60700250350361030700222079510301003404601203001c9024503400050030041c407400016000001080d8507090f1074039001c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 103309910 1250 103308660 103308671
    0x10c1506080c101b020103090f0b0a0207020112050f0f090106080a1a0105010503010b09040510080a0b010801150303080a020c0c0604060810060c0503091212070309080727020d09170706 81
    0xc0e010303554a00b80c80c480701c6848050a64104c015032181d80b100010510500c000500b8030a582c66540c45410211105143c290303001a0303140a668000401a541842d154820b205a1034000d5812810b0315000d0302c0b0100e05441c000c04250103580a4014401a0a000c421105410624203000c0349101021f201009151842c41c00407541d544100c048034160750005009503d86141c6d40c0a00c802410020700c2e1035542071110801007000781051040d0f0031f607a4050860740003a541071901050844160f42420045d000c0465001c01c00250070904c00380c0d0241d0921401620b507a131300c4007a24102003190359400d502130340001d004202d0581200c101e500500c2401045583c031034454406031100489190040c01c00c0c2c0c420b0100a00a1070540d201c510700100c04c6064035480e13411781503400c0140c0c03c810403c40106449807000d020070340c0f08202e00001003050314883d05c1010700310840e4031103942c02554040c61a5800003058485a507554009c1c206075644118040d81070304291528803000c1e004800d003203c0d40f44c1480c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 103311160 1250 103309910 103309939
    0x1903120306051c0507031208150418020d020301090f03050c121321021507030e09060d17070503180906030d02030409230106090806091605010c1506080c 67
    0x2403140708250740b005019448005041c00f0240c0002008030303c00c0f03030248200c104c00320006040c49000488403200b500c860150b07040c070030403010041c020008000e00452603d4514104d007089108507281054056414083c284034500200740549003c0401600000d8000c044a04141c1c0c031100a0850301c24080a0b590802c0d41c04054200c81c0c03141e1034100c101013805e64000d003c1c41142c200c80842400c0601c169040051465001c00c40a81c02001c03110780000e400304151041c19040408280300c0c1a0031102c002d450f00c0c0040005280c04c118490250402807810302001c190440c182c04c8903c0241c1040490b40c0320060a8803006800b86070b40800c0c0d0040b00c0a0b80440c1c500d04000070166a290451b030091803c0508004403480140342d051000d00854503586100a409000310401601800541e52038580340c40c01d0903101403070580d026040300425480103412503591a031480001c42130303032000d01c0d00444823501801c000310407450080280c81d509207031410000304041c001401940449090350803030360000d501d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 103312410 1250 103311160 103311167
    0xa02061305060406050c0c0d050d0605012109021c0c050109120b010e060102070f080c01031508060103020d06140702010501050a0504020f030c070f08070b070810030807030c05010b190312 82
    0x6000001e0032a40404082000604a40c000c10f80c4a04002415400c02200845e110700d4a0091b45495020503c001103e19a2070010300481000d040282469940f0944800c455020b0b00d808ca408001c09130703a52042e080455642d801c800035000105a18640760310802d080298010750359114150120307136001d000103092040215840e540f80d400c0011202260700c0d020782c50301c54590082420f81140140b000c0403e8440c0304c490000c0203006480b00419959016200160480d43c110058814510101204002c00400065428103499050f0303543c621520300d03464400c0160000c446c091038291000004c01c402d0715415400a03041380c1e01118070039030140c0d443d004d01003244186000c486081c8000c000144540400b200189051442291070070103001941c0c03280d1041c3d4026030343c100d40082ca58800d202c0d40507031005500350490001c4000c0c2420602e150b84030344852050400041c1030003018054501444000e50084000010280c0000c0c40c140000c00c46681c031569601045480303250503030042c07001038171 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 103313660 1250 103312410 103312441
    0xd240204080709050411010e2b0b010b072001020a08120603010b0411090409020a09020703050406031b0f080402130f090204110c0a03051612030218010c1502090301020706060305030a0206 82
    0x401640b01c146880e801b0b00111362440c10807003a5500260f82200c1f0280110407110040002c2c0104408080e00510524041c15111010707813112020301401e0120781c020420101548010b04546504030840c3c211683c0181e041c160701d881c0103480040041003442541140d50b6016228803000c400800000c40c01c08100402c0760b002d12900500ca00003031000002508041d0302c038072401c50009241c410510364455060042e0b82c01440308600040f004141000310701c2d00340c0100041016034804202c1c007c0608a40200200c0000c1c030084108181c100104d001d41d250b19140421401c01c220301070112500900c4480045c003400700040b401540307080c0c0c04a50055800c7e0556000c110001c0c0600045501500c0c100c0b40340e0400301d1501d8424403100c2e88040040c0e107420344007045004903140540c13600c01000c041c000200c3c03011100d9051286480035400000c50030416241c144600340d000584070701c907400c00700b402070117015002002d442c600a03001c001e1000c000094014100036900f210625541c1903000e071618035 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 103314910 1250 103313660 103313663
    0x9210213052e03020603040f021c0201020d120e010c0201150506070b01060e03100f06061418060309010204080307060204050f1801142701050123090d2402040807090504 74
    0xb14040b030b40c03803504110804011801c40042903000301c0589030380001e60503501c2500c0807241c0718a400c3c5100c0450070012494448010010312242d2883c0003900042d450361024a26001003140030000d48600718982e80c800046460520020008049040c1020b802060840100c490400210b100003079141f030311800700d07540d090380074104445903480c104094801d28040d01c441c581c1030007441e00c0a22803035060f1051052103101d8031303404a160352038401c0c058006240f420054803068001c000c0e4038a07041c2c03603d2b01e0040050b03080e51195503917079482c00024028055a0000b804500000030020103201c41c9401034001d590044410340788002001c41080024060452490105074072003004100004045041c1c0081d108003034080c2c6031004010740f07500c41c444c010300c0c1c0300c5600400e10070042c486940e1012180070fa50400c881140b8404521074407245041c0100c110086c41201d0740d00154042152045007034400a0080b40700054040c4088031603000303134006000f10031480c4501503001890116a008081c002c9 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 103316160 1250 103314910 103314931
    0x1020901140d1404060204050f010c03050a0c020f030a030201020306090612060403050d11030f0a0f0c02150a0608010608030703110606010503010e1305030f0901031d030f0a0921021305 81
    0x71030301101c49803281d00484101c10300c1d0350b41c901c800031400c021904400e00c9548159001603686041c9010000e00000c01030281d410403c40380c00d07000002c1e4120b01160700d002040e00703191312717030a03054400640c4549280341a40d0305070284c2c0526108040d0150091b601451007141c615517507544050500c24446c1c5400030003800d1354010400304000c40c0c000c2c00100f00c0703103081e1600880c2401107a180300c5003540c0152400c0f10b0030303809481040410980d80c0b15080650145810900c602006540020340e18549504403a030303842c80210101d11014450f910010080000d20001d204103542e683c189520b0342c00009064000c280000400c008401000c5007043c400e90701611038605507420001083d840902c01000c41c2d1002d03110010142c0490010000f0340310401e0240000356490403031500040507501d1500669100381c550119a02c0b0b212404000c0c1e9800c0d8842248258407110f0b2503a044031019950780c80403101d00500401c40c05003040c1d00030039101c0d25000b0f83d203009607000403201e240101c45045a607045031 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 103317410 1250 103316160 103316177
    0x40303050310031a04060b01090510051b0a03030c02120301030b0f04020d05010f0b190506090418141005011e17030c1f0b01050c19021f0f03060801020901 68
    0xe028401a580100c82003030a080c01503180c1c2d0f101001c010500c40c0f9110710b050060108410008203010702d0803204000e180c841c043c0c03031511020800040100c440da400b8440045403251201a500f83c100b441114404121543c0c0559030501030020030752130340c02c0c1c40140a1403680090042c188800c80381241d50211801860f17954148102446ca580a17000f2603220454148a030003182c001d0240402c003070900600002d588120504005011031078081c5042500f82a8900300708a0381d484040d0b0b044240d0548000c9802c0802401002000d407030707804d009112803400f46001440b4000003920900380ca6051008100a1341c850b11902c0c0d1411941c201c2c0800401402d40601c03c540c404c1038020001000f803c05c407824040038514450500601c0030301c0d41003051414802c035180c02d440e4040c440c020380c0d0030f09003d4078001d41d50b0b608940307402c031a0f40640303540340e690085001103450304080d1100d5903407902c2464080004880006207010125464000040e08041d000b295550040c8200c03108078a058466001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 103318660 1250 103317410 103317413
    0x20606010305150306070906080601021209130b1509010807030203060906300f07050916080405070302041b030c030501080a0b040503090603100f210b1003050f010e010612080403 78
    0x35040040c444243c10710820441c85007038404000300c1d4015002c0f80c40b0200c0f000c0c1000c100030100e94005081c141150b0020000c032103204058011180b80d400103650801d050300113550000c004d041e40a030b000390003180752000341c42d9031602c00300034251035802642e42c0202921445800c0b000c0c2d0105440c115484804900459498030b000801c4a15001e5140340c10000508207603120807080d80303185d0944045401003009007003941310901500d00a810b0403141514141004103c144045501420902c02d012f4000082000e04c80100800d00003580e00400602004544010b905a141d03010f440c0c00b400702e814800031501070390080c00349505072013101c0c000f03200400c51903c0d502c0d0030b114081d10981e0140810441e00c0e80c07070744940d002188a028410040b681c1c803480c040c2c6c1d1407810b0080d94003044038525481420076034002ea4264034bc06594002000a805464100b80001288016031004015224451b0a48204901900866000b0f15030360000c111039a50340d44805010728000d42c00402d08070f0104410710 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 103319910 1250 103318660 103318667
    0x801180207021302180a08030414332106100c060b04140108060705030603031603030f06030605011a19110703050d1806032003060f090c04051f02060601 67
    0x102e00052602d030b202c100741c088440407a0f1000d0300d070394007107400802ca10300320381003c042c1e02d8014a844001103152516181616400320325a8002c280f01d1000c0907040c64031401034071004180350f28404d1550402e0024111554800ea00030100101d0311710290800c01d5400c5000451584036400152048131040b401c2c1000300c450304a010412104039030745150651244d00d80303200b450310110184100003400d50506001c5450b00d24020b0552081202c10001c000c56520040b040c0c4030943c0b84d825001035090610b03d0298081c00c5400c0410303c6491078103400105000868215a04881c003d501c6c1c030316060965084185284680b01c1d555080000840503466003600c50826400701007540010307103894030703200d682d100c4c1000d8180e0b40c0076000420214030300a5580241d2610001421581020403450b0742d41103c0580103440c01446480406000c80019a01d8481c8088040c6405008116071486d01d010041070480343c0281c011217000e4060f44180e5000d41d840a514600c01ca42c0540060031556101030044 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 103321160 1250 103319910 103319917
    0xb100e060102031204030e06070b042003061012030302041e0306060f1d040c050d0803040b100621020d0905100f1e0e0a0204020a02010e0606031f05130512120708011802 74
    0x440e0000001c00c40c410216926100303c6026034855003414289800348cc034425042b4111300c1d907140c800d03000b402c1071001200086034071900322a0040382e02a210090b608041d0001d00965000c41c1c11038039884001c509400001d4004d205892003890200300c41074680007140c402100354010a04030002c14079103c8540010103440c03c0c2d020f4441e085401c0c0740c2c0c0e203540c003064258060500c121400c00c0c007c0309100400c40b094544507804204884203c602c2c80c58840020a0f0307241200e4130600e030700e41301004650184855011104001e15031403081c010703060301c1e290142d5601c0c0000c0641c10340c141748c0220481e80e5042401040b15040e01c2c092a81007030300903640500c0003001084440f40315881a11040f00041c2c956002800390741017203400000d038200719680a50b040c0301c0000c0255209800c00383d004000d00041c4048015661101c4000240307540d0744d02c107007074a6a4204803000e0100e2166400d00b040d03c010342d0005041418200b00103120549840ac3c0641c2c4401080c001e00d40101c840516582c41e444955003c5c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 103322410 1250 103321160 103321187
    0x2304030f021914090415021303150c0f0c030c020901080723060712051309060302120c06180102120d020304032309010804020f04050901021809090304150207030b100e06010203120403 80
    0x4200200c11031045d10100e80c80180c0c0c1e50213000012390104284920b2070040490422400340a100c001000e40005103400901101c00c3c05000011101314140b520800c1d44074603082c1d014215103400d5031650b20880c0d50300e00c20b214003070042c2450401c1c8054000003c44400c8800c0c0e0182129043c030113a82e80300c0124800c004020801c0100600c0503c080c0c10090812034014414584c0026140b400c41c01030150280c41d90158400c181d00818075102180c64200c12034600c061700006c141144a001030040703040c440f4844074000b1811011842c1c064491a49d40190f020398400d84035125010007070507018001201160b40d40000c03120a000c2c010243d400f407026150320520041481d014a112540010300b161002e44801e52aa90702140c41c0805040a82c208400c2c0c3d141143c0c2d0300d0143c9440e200e09035407845a0b01500110380719880a000c0c13154001c005910185030310200c6c210305840d000301c02440304140c500c9400201da54240c0899040e500120451305101c0e001118106203a907162010740d0340c400382809 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 103323660 1250 103322410 103322423
    0xc0d02060c0105131118040305030a090f0b0f10030b01031211011812090f15030615050d05070f080714040f0905060a06050c0303072304030f0219140904 67
    0x608601c10080c4034151082010381904100c1410600f80f00d2101e681015049000d001014103040109200700101d03984168140741040d03580c0d54515031030024050f9010300400c943c0c0d0010440c420481d81003005072284004078100d8070746d5580d40c12000c5085085d4800030303200c58812401032010804000899503091511300b0414200c2005900b407500b142c2c600c180c6200340550f425400b81c00c20a4090642c9000007462528912842c02c00181000c034000c0c034410480594120343d40c080c0f5880c0070f900604010001c2410617020350304a010050480d070b0051504030b507041d25240001c0d441a004142550000e030301c6075604481a501c0c070354280c88518000d60640d10754001444001460580381200300c000d88002d22000c603183c10000c0c00d005050855030001d106007d8140304800c000e40c000400c0da6800700301c1e0b240070300400075480172080e40c50b01901d500915506001074003000b40004140148082c5209540450400910b5210340044e642a4003840740d03240c0c2c00291a40389481c24450040c2c21501a21 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 103324910 1250 103323660 103323667
    0xc0201020c1c02240f09030f031c1803120504050a051c1707020c0907050f0711031c02071205030c06010f0501020f0a0201050406030c0e040c020606030c060c0c0d0206 73
    0x800240c2c0b40408854034407124003200100100b1800c03c1d89000f80c0f00e450144007107104004110460550340201c590540600320301007003101c0f0907030302000703000524200c0106580e520078058001c4048034100904260b0b5143c10300e9500f2600381030264080801540556078050030003510318006001d440c0190040d142441000b0103103022480034420180704080c07c043c050105541608080c04c0c01804065040800300d0040407c401990040740708402c1b501c003220407454a0343c54240a9801e4054021a0001904d002c50b10104107c03c982d84074110060840442da0340d00550010030001807011003141006800c0198100000742180c8004c2e94094807800c04d42c0c0c103000c01920b900745402c109900580341c18109a0040000d540c041c803014400c0b8003020090040e90110740c002a05034404d520504082682c0c46c3d031710241243c0b046615000c0c41a005105001c050310116000b951920300b40d87c014441e00038441c01c1611403400b00100c03404d55200002510a042300b1904000e100d0155803810b82e04100c041 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 103326160 1250 103324910 103324933
    0x306190506040e1e180d080103080306300a0201031a011e02030d02190305010605030106020d12020702030f16060912020f031e24090619020d0e07031a0112030c020102 73
    0x913840e0b0b611484603ca5034560007031419070003030314103400314035078400380040080180003044280003180e5208030162444802d240c0350f03480081201c202100c400c08051288050b41c11200c00220b0450310142c000d903801d00000c100480000d41c5405002141c40c04183c035181420007074602020288240701c06070055a00341080e200c0b022007a41c0c0b022a118600e01182d20414001c0e9801d885079901500081c40c0940c2158142a0060351b9040794980d08414404d402004140b0520f40760102c95965501409440031200240800759842c54100320841c1408030060020840030301c15000d40c403c5074006d000e0800b421032141c091104014008032015014002c40b6101451041c29040001e0800d104100602c010740441c01035202215503a18000e010030007150a00010600009501d5004480001c03840402d14281401e00c000b4490918000c102600340b0003841744040340800c010701281e00500690072081c4042010003c101c2090043d441c1a0706800035181c040b0f0b06c1501d0010b145481801155042c2402 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 103327410 1250 103326160 103326211
    0x90a1d06040902120d0804051005070c0f0227090c010e010e0607020301021e0309010c0f0f1b0c09060f05040b01020604080d060506070623060f1309080d020306190506040e 75
    0x617050398004614821b0511041000030403c11003180c01c0f2940070003c2e400c10a1004100b4100102c000d0308140110410000703540c1c80441244541c1c01c0000001c1c48500d104041e1851010121000703001c40c000d600c105402c65004403884645003005032340300020595008200300080e0407840c1e05903090340d805c2c804800c4465800d0305001d4800c655030340903a244d2070521115400d4504452240c020801c00596480c040340c4c114070b178031641c8581d6052450050308405060502c0080407800549103005164000850048581c0401c1c10323640c0311040810302039280c2e03003400140c550782d80c00240164840000600840c414001800d50b03288000c40c040b80701940c8400051440e000004151107070341e81c5008080078031200c5424886c1450444200071418a002c100084d0041610210309000d09038514200c04854107584c0110340c0c0c2c1da44103202030385400e0a15083c4000703400c21141140a103050b1a4008807200f14042c1d4041181c1000f807003146401d0804c850840020400382c8250b64a03460040047c3d0f4078203c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 103328660 1250 103327410 103327423
    0x20c030105100503192319080c070515030109020a180602060a05060f0d02061602040504110102060603060c04090c09150f031b02061302031e03090a1d0604090212 71
    0x216441e65840040c00d1504150400044032444134012404020386400151081d0084669075406c242c8074124880800b50b09086c9086180c1c034010402140d091401000303042c4004c0e0104c6035805080b0355626440e4002e20001e04500b8080d14039460f0213000402107022a0340040910003000c2c540958207458060400411804642083c070150f004002013042c180200c1c41000c0c1d1011003141e001000c2a0b20002040f14144c12502c041e015803000550464800c010110901e640b55015004014901d02810000f4403100001449030050184102250701850000380301c5000341280440c0c1d51601d46400e400c0002800c0c450480024400350080001e12400342c00030700c031101a6951a8035900c0317966200010100c41140000300114002c0c50044408250300040e0542e20025000f9030044114850000034606030a051542806240100c3c94840114021001c0c009005082d64494000c1d82c903500080041c6e41d0829051040e0200d000000710f0702d1401e46c02030715240780040c0c00810094928264182840b4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 103329910 1250 103328660 103328671
    0x60d020304051c030501060f0912030e030c0d110406050925090902030a021b01110904021c0606020708010507030b3003160c05030309010c0f08120a09030e0306010b040510020c030105 80
    0x20b517518010002180c10082c0b018440c041c0d850401c94240c2044600e0300481c090150180c20041c8085d1200c145407410400040c0002e4003d09030030340d42c4d2003494170078a0340041c0020140124109600000c041c01c0c001805401f80e528810a000a152941c205424030380520842c94108000400009907c0380244029401407031012030141e510042040ca4411801030340c0d668024981c9414050b170382861751801a90f648000844015a4561003424204007507a0750401e1032480d80e1514400103019900001d2590848204034003d001c0fa6841490980071070f10805002a044402c00705505041418608244144007942d240c00312002e280041c0589560020000c2c103956560700780000f001c0c000700c000799100815048006524003007185000134860142000b0080c02111503020788020010a8010b07201e030f404000b00c034108140350101c400006442218020350200c2d01c0c00341400200e0a010403800e045c4d070f503900f07441454549408144210703201c0341c02c0603d0460040c9044d0401c1660700307020b00c81c040d1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 103331160 1250 103329910 103329917
    0x40207060501050f1915020f1903080a021204080304022d030c0d110904080d09050d0809010e06040b0601030e060408071a1b0a2f07050609060d020304051c 68
    0x30340c101420b03c00049540e040b01489541e980030070042e40380b41c1c4017540040d100700d940803030540e060f40b0780240d141124002902d801801055414000000013100141c02c89019560b01c0e407003920341c44900750880c4206888030441d2000180024045503d100065400510140500341405840703030441510440280e15020000010400c1008602e81000301003070590b070489256420b01401d40d510a9064000e10f4218000e1120200040520801700d0036540d2004210704140303c40d035031614180e51500c3c800c3c9078076000308101d107000c42c0203088140f080c6110300601c03c3c000c10a5407610346a40c420f200004018604050300c41d119800d241d45c0a001b014007461164407455201c0800389041c40007030f401e0304c4269803208020010003000310b2020910110700b0781402110b544d030f131254040440d140046140358007041a041614460340c1c0109c14151000d5440000c15503a80a0302c84e02042514444d609441317501520a0001ca4124a1076900468100b4469030484044505050b10301c0038101c0c0030782061020 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 103332410 1250 103331160 103331171
    0x90309031e050105070318020f030a0f0303020306190e0f1504021303060507020613080705030f0a080a0b06130902090301022a01060812040603021e161406070c0b0901020904020706 79
    0x4004013401083e800101c5800c060050780e04030a0054400c6402000103481291031035141c04040e2004e001001d0f100d038022007518400780c490f040c0600654015a4450b02882003045030034030700c8140e0041b03182030716070301601115603468159070610110030142c01111205110740c200e02c0b65075075030310046c5005c94a80c00b420481a1444c01c01000300c2d04010800800c0d9005001003003000c0c00f1840d003003001558061006038070707801c1506000345507003e000c111032001b820004881d1032058106211901c903414900c018081e400c03c13003040c0320403401142d0001121540b05141442540690f0700500a220400781c00141403071010b55600501d1600721b00e10203031242071802c509900c81e50a00034500a8012040100032007075881020b0034240c401c1d441075804041d80851090700041102120904d40d0f0051001962241a02155141c0b10180780108840e81c01d85894290799465010405c00d100302d981d0349031890a1501629218400304008203403c401b95401c00100c4240c6d81c0e1803004c0c00702c0c00c1c045c08002a2 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 103333660 1250 103332410 103332413
    0x15020a02040506060f0906030403050903070303110d0f020c0f03010f050403030903080a180206030402010e100503071701050f011404030503030403120609020306130c030e030c0d030b10050d090309031e 88
    0x200c0750042c3c141d0f402000b080001c600c08184285c201d5040c543e0a0b512035503690348904041350035004800785103505024260000040c5039100c000311040e10054030549051045840f4141e6a03a441d0010f4100540c0001c12000341d545016a404504444098004518000100f15800450784201c6084010a54400c4010700349540b04207407941c050f120700c00410070b11001a054944050720000000c0c0b20703031400400501164451580514901c1c4050090729100b003902d480030f009500700300c1d400e100003001c0b076010300a1a809401d4160403188094101c551800e00302c40111a103a02003012641c0c0c0c418204400030000703000300300461083d4029510000489509688071096804940c000242107005000340103280d41c620100106d100540040001d44a1030b030403040d00134104001080d080e074000894004910440842c5c0f10310080c117960f604202c3c0c601ca91040010b100f45242818002034418803540f0b50655680d80a04070729030003801d00400d0242e41b9035903442881840400081200303003007000b020 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 103334910 1250 103333660 103333669
    0xf011505010f08010306020702060f0706090b060a06080c0705011b09031b060203030a271a06030106030302071e050904050313060221090a0b0c060f25030b03010615020a02 75
    0x4014020901c2c100c8030203a01c2500083c00f044040c04058003103580061410110354a00c803c032654020340520842e240e94113828a2001031200a50039100c82c1d11794070010388540f81c2600b03814295021500c420031203880f1220011166080498216119980c40075101101c454031034155440910968540d0b0307409003103140c030351070701d10189920548080007200d013070200d143c011055a600c010f04190009a075114030075429152050b15281d20842d1440e039100f00c2c103001e0b8281150b1030450b80c00c80d950351103131035000c00d042c02c03a21548400b40040e080300b403040c0b001e00501030548038003441402c0080042508e440004003150310681d4101d405a10009202840502c4074001800601480c00641136280151800841d10700340501d802020080000d0184020b96642440d030004d04284041d403919914160700e030598418055886080780346406000030194044000e041100302030002510712482e01360401600504201141941c0c1075407594801329038080e00d80e84004951509600030030381d886281c014170 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 103336160 1250 103334910 103334951
    0xb0a0e150406030c060c020a1503090c0b04050a120c0302090f0702010f05010e01141302040b0c062d040317040320011a06070305070b010308030a060803090f040e0309030f01 76
    0x24041e606020003000421108101981220010f0a1285203810144001020060140c120300b0103041c4403d495101e80b907040d400040d50350320446018032501d4031101e18201030702592040c0c40d400310801e1000c0c052014030b161001a110302ca80920380310140ca0303500080e29004200c660240c4030b00c43d1000c10141e65424041e903090034001e00400c0007694101104001c3c1401b05019072840d02514000640c100d89030030ad004c0a0752011743d03034110345450312915032172000e611484004203103220301c9000c03e920030581812041d80c41c41000c40c80c490041c04102c2100186401003080e01440900791a2072090500c1442d481d11039031003a5200e038103021380c20750f1500f2224062906818030341c0c505030001d00000082c91303c0004a42c0100d80caa03440d132419260498040c855860020100c0c02603400000401c03c44030055800340524480500125172071300303002940c0707000e201016076201841d0785a12070982000e40c403104001a150058078030702007400001c640307000000090f01100f030f95580240084190703e0340c00c2 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 103337410 1250 103336160 103336201
    0x10b12070804020a03020105090102070b040e060f06030709030204180203010203090d0906020f03390d020106060302090105030604051012050321010510030c030207061802030606060408030f030a0b0a0e 88
    0x22001608154000c100b00c54490b000080c140280009c00f80e0160f0b0081003010014000050301c035070390f203454a890725070060081c0d0f1001c1c081e01046000301d00720320f4035030107403841500d00741e0791080c4a51070354007040003829101c5600a40c003028000284c1c0135840c203000840c41401c0350001080307038601c520402008800640e0100003150014114030018540c048212401c0d005401d04006481c0c8201c4108448003c4071445c681f20550200420032140d00045601c1c960400c65400820481e40e84213015000d03440b80320801400668100001202460181d01030342c0c102604141c03095085031100c042d1140940b0103102030352390341c0c00800c400301048465000f41004450603080c016035940340002040b107480c01a0f40c001c0515484d41d1003440d92034401c1c0c2c15541c100360014014021602c4111010408200341c42059001303000d04d07000506641000d074100c0d01120240340003945407002e90003e0b0903041e0405032042144130346079103080703a142c0d07100c00740080580b0f5038040d044c066003030500c0c901c9079030030f840501d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 103338660 1250 103337410 103337417
    0xa05060f0603090a020402211807060e0a090c030e0102040605070c05030c0d0320071d07090810110417031902010504030c02040b0d1502040602070801021201050118030506010b1207 79
    0x1c0052500000c240246203d80c1503501585454100c008da4000e1104d1880300030080c00c8107401c0001a024400c81044c5207124802952030f0070b519160115502643d000031207412144054003000341c55682c2c4d00c040311800841c03500041d604440312005099078025440707040000c601154600c10f02106607140d6000704006c03402044040c07041800b2440010021002809110b038407034640041c41c02e5030082e03c2d140c040315020348040c1030301d407051240034104400c10100c43c080e9180c0000c504502400032030041c2e41483c0000c069014149031880f002c2c05e0040c081c140220024400040c0301c070304080f400f10417074603403101564503008413107880c1b25225003507821181160706001c01c1c040030036004000080c3c017540503600441d407003035060041401d04c01d100200038000a030340c2d591000030302d0340e42d4060410358015500b940c68082d51010003600b40c3c0241c1044554800300c441c0108895070040c850440c0c203414042e42e00d01215544d40320141800c500341c0c8414001e0800240c404001005007041c90b0b884021402c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 103339910 1250 103338660 103338667
    0xc180c090302030a11030f01060b07060b090403080c1305040e030703140f0306040f090b040308010905010f05031507090803070507050306070302040e07080403020c0d051b03061e070c0b0a05060f06 86
    0x100081d503106550540604a1211100e145425407014132440062202480090003927955491140d402036002d00420342c1d0301c80c0b03406100c01c41c920b480e41d0705502a940540e41e0003400c0e2140034180407580c0c441001070390500102e0000080c0d0707840300c1c021891058807107000b0350b440e414a070a0241141031602d45140100104003e0200d1001240c801d0780d41001c41520002002ea18940304800140050031340600441440420001010b82c40012941a101c80e20f00510607641d84114840060721607000ea01d5140c1c0001e442c590031004800083c81e48007806160002e82036a580030b90a0540d1b00008055585810200c400d0015060070003001d90000b6891030210f01c0c1c02c1c940b2600e0000d11401600d450304111201c808a02032501c200311641d10682c009144007540402460000e687d42003120b004030a20140070122001440c020449034424401d4203402d240910707010741c0019a2080045c16441170100171041c0001042140c40c21612485d0b5056001076a410050b0410840d006880f2025200d2030042 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 103341160 1250 103339910 103339913
    0x510020a02030d020d020421050c15220b040e011d060109030f020103060e1603061d28020316030f29060403021207050112060609150c0c180c0903 64
    0x800c48a10180b03c010042c0c031a01c01c0c0007408040d00c56640015802c1803040e00c00c6540f01d407a042c4001010344200203c0749907540720001d00480090840700c0141c640b10601c00005034040c40410000380b4200c1c1c481a04030140c4030b00740280c1c03641241d0003041c401c20f0240018800c480e00054000c640400100c80803240d8030300500000e080c0103150000809140304001c10780116402a0801805040345035610780d16131a1210f0090440c000d00d40c3e1b60740019003807501c00290106010b01d0304000c589603244034101c0b55126084924048642c482e010f044034000e0301210841180b40c800b0f18040c00c09000446408415a200202690624201101000e10380610780c203210840010030410869a01d08075556282a200000e50b0b60240b6070001c6d400454912219060240104c1c282098407001d8807410a2070104000c15022540140503400100d110f580040c0312038040c540700e00156200c0303854202440c0d00319685400c81805d095106088403000d07003882c0800c080c3c09000e0004403006518246601901d103 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 103342410 1250 103341160 103341163
    0x10e100509060a2406030209100e0a0e070207080d081608061e0d0602040e1e130b040611130302030c01020a05060f18070308030609060a08030a0806040b0d0506040510020a02 76
    0x904503102d81d40d51441d028400c1010300c008291480308400c404c60405955035000740c0658000482c180c4910040d0500e1110140680025404144080c0c041c030101824a503004840f07101c00750091041d842001400900b481c41040302070f690940d1030f40c0b40704070741c01d06409001425491f4101107080c04004070401ca56611030b2171200b134080d0a2140307011241ca0500300400d00004500d80d001d0803150002401050849242c40c1060003174140e460190807800d44030304441c01c4072805683c824026407250344200c1c0400c00344815107800502505000034032164002040382a94000c0d181911030184c206002c00c150300e07060000482c000000c0c0054a1800c8460365a582c58440041005100c0003c030340c04956840c940058140d40c40308040c0c02c0b91000c03a141d0a08840c9c5801c21281c6500c00e445410001e1210700705003040e038044480807001142821038000041da48888000c051a4009903120141c800c2952218407180545010768042c2c102428182030950070301d51907116140b4002e00401c50354030641d50 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 103343660 1250 103342410 103342423
    0x51608070b0a0e19080a03020303040b010b0c0d080402060d050406050a05010e07020705010c050309030102040b04080d030207080a030b040e0d030b030c030307020a05100207030b0703060611070f12110909010e100509 94
    0x10122500d00180d0201d03c0840e84540075034018012500c46c40040808258000000714000e5009201940300c0760790300c280d01007442c821205540d420f60842e5220211081c000e055486d0480d2004001c1820102c20340b0b00c400848804071015180a03840e4820b000600903148610303805824005606809442c080c44040e5840d8070b14400d07a03040100502c60002801010700035030b21b0b03980004000f903542ea0f5a038031700e5100d0781d001405603c0b110301480c02c0c070b00345442c00ba1007100c1c051580401c01d1410103580c400d058005280403c0010742141d2907141a4001031802d21004914104584002409139101070515282590503039986000364070400403080907907070b01c83c2200304540c0b0031030301035030381441c404003c03400c044d12036100900304e48000c5c00740015240c05801600a0352135170b40d11450041100d410066030344100f1703c41e805604440704818080100e03241c005a52a90003000c020f804d0040c00e5000c12500c410464100c0b071165540c1c00505078119062100f028510982903040c080c900300403804079205c10 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 103344910 1250 103343660 103343687
    0x10060914100b0d09080a020c120f120306010c050a06051012020901030f031b0b010e060915040510030c0306050a110705070608040c080a12090f080a08070c03051608070b0a 75
    0xc003040350b03800583c258100f0740a10b40d126512a0303c40501d020060758480200e00e070b0501c64290720424980f0004001100d0340e0f84008040140000b881c103940d48841540b02411070390400000d04079640114500f001010001c5118100014041ca0055001c04410140b50055400070000c200003801594030242c3c0241540d4002e00030071581c103018641a141c09811030045044108100707201310900c50307501d031090b040350034813000d151b850340d500420040407420858503580c150700a036a50b503180d401c0540c00300c2d03400703030181420040d003d480c0d1b12403a010351540e80c402c40f42c0d45e840e042004843c501c3d500030080d0692410104d517003403001035035030702d601c80705180680000c025030540001c0500902109c1480146404000daaa904825042035000b4040700756040011500070f81000803c50080c0040f4003c13100540060041c002d0303141d480d401681c2c00603105a4080740f600f00b021011030030902041d6100031035481c54089540c5020303601802e1400c260300a00b00302c0000d020072040913802c54844074505 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 103346160 1250 103344910 103344929
    0x40e03040b03070509091e0a180b040512040b18100512040c0e01080d02011407020c011b05010e0601090f09020a090b1306140315010b09011409031006091410 69
    0x30343d0f0301c1400321124010041c5950348800c1640500180c4405511201c200c0c51282c04400204d03694500d41c8415140120048411580740000642c0803542a8802c0e40e00148100103072080d80c1c2c000140c030710141e00982c0180c4004500012091020741d201400c0010002041e10710303080d8200e031001c0c050440d00070144603445c0c0b43d8a0800084c204a9405c400030054840d059401ca000c6d6120740303000d9a103006030603401003d07610700703c01440c0280160700820710860381d0f03500170141071a40200444202c00d011070b917501a20707034500c1880002002806540c801a0b9041c00502e0342c0c4d85890002ca00b43c0c1e5a00c013170700d0140d62500c400341000d40c440e09480307000d4412045c80070034005d410001040b4140e0000380003a0071545003102c00724100c044d1140d96404544e08404070740d4070b80c090706681c468140080c030400032201010481d00400354011078007010318800201c0041d01b0000e0724000300c0e06100c500c0c0210360103665941001e020782e418a20800e040382030030f10100301583c078010300d000c81b000c8040e001d1120714 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 103347410 1250 103346160 103346167
    0x10020a02010e1b3001110901030f140105010f02030d090b040b07030608100b0f041406040e01360501050106020d090b0c0a030e0f1c23300313030905040e03040b 70
    0xb204c030030b20b02c00d61803203004100800071000c500103546400e800032450030f4006400d05401142511031b602404100b064401080c0c0907503482c0100640d00702d1912000d50b0705500003400320f10803056441c03084043e00e034043c084204e103034034191130000c0c4811801420003040c185000c40c28022500b00245405498550316400180040c0140004841240030f11005d94050704000d0a809404408020140261020b0303406202400c080050743e82603c4488800c21041316805c5030209004401d51420541070000c07509289824440742c5440d401d46500360055000761b07020000241c0c49a80c041a01d40007040503d44580c100303c503000320781d0303110f8141010203002c021000b11001e0b013580c1c42007034009080000901c1d03149a20703900403040b00248814001910b244450028400000e0300010000440c2c3c210b100141c08820601a220320740740f000c42c08119540106824125a000c004400950160324001c80c0c081c1c002d080c82c9802415a10b058100d64007590074007480d0404c14100009440903901410201c50301e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 103348660 1250 103347410 103347469
    0xa031509050405010e0c10121104120c140a05030a0b071e0801170105090604061104030209010e090105160c03080c19090609080a0b01051210020a02010e1b 68
    0x6510003a008003a4a924190070b00c0b00f00b04055203c8012000d200c400d03200a54403100821841602645405000c541940000e1400c6040c0b5480302031600c113110007080c1020348812942d5400180c0c120229003c4107492401d2080c442292281c03081c002045031500105030130840400d860341c1c107442000f001241c0080100b500c4601801c1440020204d800303a15000111114009203080c000707124100c20104044030900c0340074010b0144c184228600002880a52102c1c0d0b00e5400400f100600f0740318880040c0301c0070005a0302d031010b00e4001d01c1c4c00f01d00d00b4110b06000f01e2803400c480c005001c0c07240c04400400741c04481c0390084456030b07a0582506100000c3c0c1e45420310b00c0207d03c05e050304000c00e02d0444440c226600d803c40d420100b80c0b004e5a136804001d540780c4801c0c955400307105002034110008240100424039140c03e044400560340c400340d8050705855140d91080ea0070000d18180584d440304d01c0b8080f4664204460314462100f451100750254190f03000c44e00843c2e611030a00240d0308004182003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 103349910 1250 103348660 103348691
    0x60a030c0c02030d0207060e09070f0813020a1d06090f060d02030a120801031b06200f070609170619020a02120403050313080d09090203060112180c05010f050a03 71
    0x240468001e020b44d134580ea00c2410094a0b02e116020340b001080d0101c1c603a0055060418800b0b2065186465031000f109410380240c9130310138014100c051200704e102c01e00d00141c8802182100070f00300b03804110f500310003414500c2c5030706d6801405503000d140d01804209002d0fa21000d0315400500c1655020116449030000c2800c3c0300b0b0150f000303004030402801d0040440c0c0c0c0440c81ca81200e01030580d541940c841e010700307552074540170711840f00003402c3c80c0c02d00c18810f000e150f50740e41003100352011543e40c5c2114000c0d007420711405510407000f040b4800303410405c440810b1210440200d14501404607460901d1140756540044503011081a0703000c02c0c0b0b030070554000c00141c0300629912200b5500c03181c1c0e91074038542e02c0e800010207542e5503002480c0003440540001d422003030880561140c503422810201c1032002900300078a02410803035110700040c0011010f128504100f040e014041d0180d64160420101c903490b194840d6040050900d89000b40a40c02015698898100c2c0703408160b0090b08170701d18 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 103351160 1250 103349910 103349927
    0x11130b090a0803160302010b0a08060c2a0f1006030b0f0a020403021206060a0e040f020d08041a0405120a0b01031101020c060c030d060e01080a06050c04080a08030703060902040302060a030c 83
    0x381c1d84800104101c0c54600800e130818598403aa0003844407400582c1400f0a00c11140f0602030785a001b140419014000b000c090801c41e0f95054902c805200080341003c1d540d95030051403001900005500079040d4424007001001c2403030404107100191660342d6007007807944001d29443ea2000e440d004907100603880d404803002150002c02082180c105480300980305c0c28190b81051047c0003c69001420043d8135510703600c0350390840c144401c189800c0c0c0a2105070428840100c0e140781d01080045405003552042c01120700d04002c5464a031410002401022072a002c01d0000e176034802e02061000071481e003840340c1941c0e8496a04c2d020414030301c0050346040d84005100380d0210b0301040b103114000001000c1c2800c2c03038140d60305010b419a0745104400c0701e2420b00402d070321904140c1e0301ca8089540c5030403031500600c0d42c0380218036281e5501545402d26540e204111202c0d90f0020500596941c1401420b0261000c028114501803566002403e9031103032104840525498001070100c190161001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 103352410 1250 103351160 103351169
    0xb0f1303060c0503010e0105030706121a220509010b210703020405010b1c0605010f05160515040302071e15170f100902270a0f030305030a11130b090a 66
    0x600c1810b20841000c0d14036002406541c1c941040480002000c0c0f400007010030498080d1f407195841100318420950143c011080c0760590411200010100e54a4041d105a5480c3d00400c0381902044512000810307110301400001e40d907030400614890513034480c49040b42420200850040300580d4071301072414500d00d60b0010354000d15007400061207400c000000c090454840407041e02514005030b01d0403c40b40503002d1140007510310b0512484103130256008165406800c0c21004a1140d190745251a00c590542d0000709184080c0c180410990100f00900c0904107120131085528041100114411002e1264400c0d0392102c09203142401d004d962480c0380c4001c1440c3e032108514210b006a64100002c0d40c1d01483c0c02480f45c0c0010b0101101e100341c50401102010f103002c10384096804600a41c000d140c070070b50080040c00c0c0000c0300c01020a2040085111b41c403403a480b890b000d94800d0490700a0427074601031200800c94001055500c041d02825500744103035036030b111140100170030303651401da801 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 103353660 1250 103352410 103352423
    0x903080a02011d03120403080a060f030501090b0121031206050306090d021002070201081302120604030c05070609050d060509010e0a0c08010b010513090f09080304120e0a0b0f1303 79
    0x1042200c269064014101c03110300c400b0341d80804400c0d100204e590b44110381140d1031400c440404a00040e1007038020369000214002c010071104d40300c01403501c041c0c2090b88111401c1c1c2d582e150300c2c000c0141c0c8003d024010300d050480c40e1400c95140c483c00c4c4254204c81c000a0400880021203001103100394000b1001d0a03010b001c54a05141c418001035458822102010240c840c0043c80e2549138428021a01c1d01c41e410713514028252240a41600022500c030340c2281e115000341d804806891040180c40d200d81d0080d5184401d2a68a041045c109841500903408011030f408043c44291619400741c0510741d848030300001c075503560000d100d00608455000e0700c943c0c0500c010030340921004044d40000e40705114000c0000c16996401510300c0d114803450b041d00841200020850503c403584188501c500c01c56021031501c01d103030303149071140e801100c080711540c240401051120340d1140f110f200c1440c05a800050345803c0911040b19030080201e04010300e040040c4c40102e4921001018004550041 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 103354910 1250 103353660 103353667
    0x51201080c0a091109060d0e0d081005060906160609170414100207060c060f0510060e030609030306040e070308070b190b09010506181002030a030c0207030209070c03090308 76
    0x80e80303a45800a01c0c5045100c0d0a1004021410702594803502c0e41c981c07002190345140001440510600b038100594500000d40d642c101341c20850301c1071100040e08031440c0d0702c0039170038031f4402c0040c0ea200d4110b80055006240500a000940d100c42c411144940007181c1c0345071200a580c541040603051921000300810102224204020704480141040d141e9021002c42d41222480511440d40c4a00c9219801031740030120801c40d682c090313a0030440542c09014045440020404888159201a0b460314514202582d04000e916805045155150340480103000c403428402c9038603942c1c0c000034224512803030307482c01043c1ca86c1030b0401c86440150745c4080119118040c03414a5101b80070211340307824016004003010000b103190361242607401c0c0801080100d103a4200b500380a0369400c80e501010380e210400409445030382d40c20402c000780c00714030b81c020356660400d49001420b540000798008290340c03141b2014001030f61420b4040f07500480b98900300701c0c4078105040803548030035640e101034014031002 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 103356160 1250 103354910 103354919
    0x10b1003020a030b0f09040b0c0d060308071a04150c02150c070201022107110411070f050c01030e030301050906010309080c0c03060f090d0c2a050a090902090f07051201 74
    0x1a006881042c0182d2400c0025407544d1040c4010900d00300b0341c2a60040c40c020008000900343c2044a80104050314400d08100243c0070000440c1c00350340042c3d52205d4007141c108104103800b182d200503002d803451110301d80d00303080d542c445000d08000c1883d1042ca1f100c85030022840c0c4200295000c03c0d161000103a518200b81500e82f14ad40d0112a05a0050040e81c0d8080309007038074044030056802064144170300c0c1c0b4200b526101d40c00644c0f1b07209035a1003070b122940c2c2c0b9510803011001d01001d5001e40715807600510540b03881450600d15102207410b02d402c0c10362004000d000841904c0c111f031010b0350000310b180d13140320040300100b60085004007080d60201c0d0100c0401c900080d20b0036141e0f021b9084840944600d1044500034408a8401e80103905c125080c041d841c1c800c07032005031824070070013110780b4502001c81c01d903a425040c2d01400e240c0300d071b2010301040036160403113001c0c009040150081211075010380215108880c01401a10070b0303855030011a8080d031281041303d1026914240c0c42510396110b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 103357410 1250 103356160 103356167
    0x2220c050c0c06070f060e010603080d140901050606070206182d0603130303150806070f030605100c0323070b0601080a15050d02010210060f0302030d08010e0a0905010b10 75
    0x348070208000e100c0e5a080429506000089402480c1c103c0d039070208042056590101070b0a990030440442c2d522500000000ba1402c80940380b00303011048042103030107051140b0301c02602e000746500c000c1c0e81020207000080c0c50701c000300c40c001901511030966550480386400355010050582c00c0c1c001000070640c540b106121013024420f00045c0000c990b81045240400419000c10344800385000814880d40b00024040e500c5440c40c0003015000510301d0303a41d8805107060003004c40314080801c00e903413010202580d01d807040e2009800111a181000e12000c000240b0804071003e00a06000803003440c9002034000f0340c00740030301e02400c1199540d2044a03103019000b00d042a1012404921900302081583d040d900038084c011100e4000b82400615000401580841011050b415401101d548810705d510074052000500380821202030b8252640c81410715264030f1720500020420004014042c03000d1070f2001c1ba4000c080d000b40800c9200e10b0f8100180106180400154001e4800c2d480d40800d580 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 103358660 1250 103357410 103357417
    0x601030f0b09041113061d0604090506070e040e0616082208090f010305092107080403050a030917030313060f05070e010e1008040f050a0209010e01051302120402220c05 74
    0x3815280172644040450305141a520207005840509051540806410a000d2410355020100500206031508a516010306081c001d0300c00e440010040959910745080c180107842c1ca082c024001005130f4a010201c042409114150640802c480c1ca40842d0303007410003490b54030080c0a203801d1b4801c0329404d0b00e001c00d07081d4410f20300c1c540518401c40d5484a00d6000f44209846800c00f440540110120301082c200c43c000c05a004982200b0107000300b03008140c5410181014612440c02814078031468117026004207140e03842204c424808003400d81e8580408010750b80c0201c410700a00850385060b1406002816000c500040490710301f01c10040502d038003119401c0680404e80382e006400c2d08907024004298040b801e1382000ca00520042000261151402450280070700147c8442d8051580055418982a0b001c0c41d600760810b4018000d5160a0500da6488030a42604610b0101d51148030301e41030b400100003a11450400014a00b15640c2e0000c20800d4000c001c002c0000c6840302d40081c20940 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 103359910 1250 103358660 103358693
    0x310051305010305060c030405102c03040305070b090604031101021e06070e011d01050322030c050d021506010503091203010915090e03091516081c0c080601030f0b0904 74
    0x11444021546500c0d40e0400c8a00449c2c01c10003420100e055004c412003d00f001200202c0c1841100382c0c0030800070b126040092050b0302d544c000e940e490746581044e500e8003405400460a00c2800c10850301d00b0f64443c012942200ea0202200c2c0d01c030144000140e00703050501507114841d0340314a402e81500741c004500107118181640760318031030382a18170044500308401c17030401d80c0303074a1090900d000c0c135800351000d554400e20240b004000c1c00640c1c4030f00078090001c020100c010803041c41800040200c2402441000c03403082c401403100c521322148150501d1000f605d40c3d418480c0003c04240f1500091040303010b41ca103031007035490342e84d6595010f8000404c031581310090b000c10f11540c0820301d4115409600e0055550000a5040c091110100001c003554103510300040101040740b0300e00e050710f540d013404140340548103241d00c0e000c069039109211007002e007140307000a01d401c10400e4a99049900143c010a003841c00081c1d640e02c02130b0b20001030824019041d0700900c84400c11041205400c1102c1c04074 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 103361160 1250 103359910 103359913
    0x9150b01031a130b03100f05091209030705150d0e060106090b0301080601140a0312090e15030a080c0703140a020102010606110a060b0103022b0501050a0311060310051305010305 78
    0x2c02d0b00c04180203001c0c044400259000003821803c240f81c040301c1e00b0040220038018261004040013507001c208075405009420340b0b56449404015100d07000340a40042284800f0400345442020b0780020f4076481180035031441082c080f01803100354840700307003600d00c1c602070000300704548074604c1c402503510700382403040d0000502095070104031080240b043d070b4100d900350001030031182d0909800204101082c411a90080b010010003c00306105981c410b250007503c0d12500c01c030700d0510f02c68040c03003c2e0082480c04034010200035002c15440004040c0d240b180c10201090300c03444031001e03c0e414a001540007a091075540c2421541030200458079034070b504d200f600200040c0b55901e2041d1003a0583d0b005103940c60b00003801c400007290558001c10b516080514005261000340d040d01d459401c01c80b19085808419642c101003150030520a0f20b001d007400b241c070400401d186a44c0d0703000c11460729268502403000880030800c21503003d1091000342c0001454a521101c0c02554400141404d2106030360300d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 103362410 1250 103361160 103361171
    0x20613180e061605120405160e0f06040605030604060f0209030d051207020703021005090a03080309030703020f06011a07020f09090a050d0c08040b03040507080d09080f01050105010e120109150b0103 87
    0x200c126018480024202948409007002441045d028003042c00500581d01da00859541c1c4001d01052401203002c0c246900303200030345042819040250490040040380520301d0075206010035540000e000354041d0340151302103400c2d018041c1b03100107405038400b5580c1600c940c40200701c0503908000900000e141d4500543e00da03907106081266541164032000e50081141c0012100d46807080c0002c0030f8592002d41203030341c911358a6031400a55841242d05001942010641c2810584c0c1440081c1e900035560000b080c0d02d5050400e0b0000c41c41c204601440d080e0000150321046494060401d5400400103281c01c100349002040b4648405000c101180d450007203010750340c4502e006403c2205002d400c81620740c03e0604158072030301658006042565540b140260001d403560042000318584441c59a415001740c2c0f402242500e0301341000030040c03403030341400d0040c001640d000c5e4840089403000c031424a90580d2804545005010500c0d02402c80131002581b2000060705400c0581d8025081e07030104403 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 103363660 1250 103362410 103362421
    0x80c0c03070f0603141302130209030303181c0206070c0f0f060606110601030b060f01020f010e0d0207080106081209120105010e1909030e010806190e01060f0203070807020613180e06 80
    0x11451003c81b0003c00c0200304070a400058103065a11908a0740c00410061400724110002882c0d40c10031150244001e800c5820180782076400d004181c04030311032030100d840c401c40e42d00006c2d440d07038030040c100c0c8100418000c03610300f4003001c0003201030f8940c0c100c16412180c08090402070054001c0740100400b2035180e04607000751440004d1040d0480360006075040f501d440e41410421392540c4130420364118806d10003400c0f14140d0a101e0102c418001000400e4030031403450000c5d00b04640707540002c0c01645084010010b9140200300f540700401d0244001d691507014100042c421f10384e1285e00e01c995031901b80003140103000680c129006500d50244ea80041d084900c850003039690b44007000700081ca50000102480d401620001c0e00201c00408136149010a40e050b00800040d66024000019030440104516600111025115074081c4003541c41e040c01034588103114880d000c07000307001e80c0d0001a81c01e000e80c240041000988031120072130941120303019408003d003007031080e9089240500ca02065 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 103364910 1250 103363660 103363691
    0xf0109050c040614030402130e061f0620010e030309030304051005060102030711061b1c0206010503060f0901060b0d0e0c03010204210204060803070c0e13020904080c0c03070f0603 79
    0x1803c40d00e890759044210342c81006800d0f500c0d0405401241c1055103001d40d000616440c1c0540d1502e65814802407500b031400c80100090007044484500c080c0d03140d02000e02030300380d010008070f5560a4680d480e140c01104202c036280101107064001040d400044107102c5140808001503000701d01400031280e4809400c4480f8081f22810b484050140c4d1007000380e60001645605011f0002c40010849070170321101042c0d07000b61510815100340300340c100e40005050b10701c000304c6c0c0810074074651005103501e60405020955600d0054510071203502c10100150080e0401d400c1100580b6a074031245455041209099000c0c165078041c51215000b80f001c110814101407084d1801c0f1107c807140303054147c0c0740309402c904100b440b4505981082c2c6800b0045a02e840c1000105811031083c1003403900d80d80f0b80101c5042610003d080452034031149141400940c1d10043c10a400039000218107965281162400d444d00c241c40d0300484d098040c0e00c0c0d0000d007a00031170f008002200c0d03030307a00c00f4450b51105100b0384 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 103366160 1250 103364910 103364917
    0x703060e060909120307030b011d0a0b1b2b030b0906010507030507120503090f0a030509060325020609010606050f0f0a05070602040f060e06070c0e070c0b0f0109050c 73
    0x84a050062000080c1c1500d001c404494024140c0000c3d11001d44003064960101e61044810702c0c0447d0b00c07011010103039680900003900c83d6480981c101240000e010004061050500c90036410030702c085070755142a01203000040b40c0b100c02030b00b21440e8103540b9105154000c0700c0300d0707071030000d402d504140500700e40240154110000300904181c41317695600010340701500061000e03010000144440f9000520b040411041c0d1803a948030182c980c641801460300c0c09081c407605c1c09207a0003c0d40035100190300100be0307a0442108503072403500e0359196024ac60080b040e1401d0102d800e58502d4001c00040d40124403140a209000020b02c0455110b4000751072030b1241b2000f00781c0042c0d040083c11b03485204c140c054541d4200c0762800624155a649a2106a030003542000d0007182084404106040c2c101e03556558100040e103010342400c2c803a4a071160310221612512007813594001c0090040c0d8032602084100300d501c801035032010700b05000c10740e01d030040034044d25041c10f1501c004607041c3d90886094 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 103367410 1250 103366160 103366169
    0x15180b1801120b0f060f07060f0e070f080709270f03092709061b020d020601090606051b10020a0203040503060601020f0601060302131206090201030b0108010b04030201110a020901030c030b070306 86
    0x2c12000c400c3d42c05d20525500c42e8035403040703c0d40c05121a400045c1c05000b14082e1980341d01c00030950b1191506154100b0845521050004403240800c03ca80381c004622001100e000c1000055210044040140d2281069001054000c8405158000c01804c1845100014040d59511060a0711080c0020340d0680c105c00000e080700c10800051551002c5402140510703214440100d41503a0360178440707100e1001c0d8010070000d60415451007e9156040019030f00401c0007000034070042d1300c0d0140c00381840c03040b5064082c2890b100e81c0400c1e8140000c00601c001100214411540c5090503000207449806c02d0103081d03c00e0058a000c903040b980300080000c060300c90309000e020306920300030080c3c000703621105881c0f40c0003020503400140c3e1840c2ca0400b8034010b010340c0e404181550380d0b100041c02c03518a4941c1ca4140035602c00180078140f00b41060350152582070800030303c000c0c0110900d501c0c01941000081d80301c40c0e940008010400c00601a02c101ca1041d071001c090764560360415800d442d124001c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 103368660 1250 103367410 103367419
    0x311031312050a0512030a140105090412181e0b0f0316020c030706030f05130c060e010e0d060c0813120804020d0204060f050a0801020415180b1801120b 67
    0x1814019603945141d5001450b215908031484500b041d80c580d030800f161545000f015203004403c000b42c410050160b850035003c0401410295070400000954411000d00050840001c2e460f400181502030700c407890082c5404070150b024241c4d1510011081c0703803941d207001d40d0540b07a40c0780040ca03002c2c40c0099403411080c0030074040c11a40c40383e10140d405084001c241d81144500150b0100b030380c9003800a030014003950781d808100280801c800b0b000361034019081c1a00c0c012142645008070712504008801d071080ca1130040484070b41d500c012140300030b035030420540c031410141d51181046071a81c41074160001d59103a110041e9213403104403d00c101f80e0300f17003c0c00850f541c10789544a0b07803080b106254000d100820820300d015058010070201c4240b0307000304001106036007003400203182412040000346245002580741500300040a0420080d4030f1040d4180440c56002c03060000400c042880980500070110713803204000e42c00c8414207451740700d1050101d0740c2100d000c802c1c42100c0c0910079070414044c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 103369910 1250 103368660 103368697
    0xf0606090a0b0d080307020d03050601020d020a0303150902131e060504050603060a08011805060c07030203040b0313020607030305161d010c03031517061612050c04050d0609031103 79
    0x81d21000500140340030315601c0b20311483c2000010701c204d0b001e98090101540181a82c401319000a022140003510f2681550300040d0890b00841d400038950701201c0c2d040c1342c003080304000e18a80034440925a003044c00d1b01c40c0049804101c5086600c803813000c503a803200c00041800001c80c48003100c142c29004403000180108814419402c1000065801003409030500501c1c42e5039100340c90031109640c090541c0c0f1801a48042d0900104004403508058400d00852600e4503d54020f580d9106034424903000342d07400320009524000c54040746070140d4000d0800e0380d80d0303003a1b8038004000348009c94201c06110ac0c0020041d5100c0d20a003039a09030703d1107404068414007031903230040d2103800420310105c00f0542c8500c0d00819060701141003000030102d000c1f005100d11405032143d400c1840080c40c04101c0c0c0d034001c1031a0031043d80000f002100d21650b40c40000c1030780b1241000c041511494200341e800103500710042c01004030030740c440c061240c040d40e0b41c00c4404280c40300c01350301c900c100b004034000d0032541c1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 103371160 1250 103369910 103369921
    0x10b0903060109270b0f011a1210080a080706050703110f0c0705040e0703050606030c01090e1b040609090509010c0906120207060f021207030903081b0c0f060106020f060609 76
    0x2d6100c124800300301a40c0d41c11911440012a485020300131045409a0341c50702030202850b1141156405024078040032030485c41440104a040d010720a09860561840c10102d00302d5000f2440a80c00b50171610140c03078564102d03041102042d400100201c40162506001400e114803901c100c41c019038001c1401d9161490902411002e500005c101000c00c0c01041030015140c0e556109a080d0b070300c100300207403072200d1842c10560304205000f0a100d020341c01c20203a44d4926a40030007140c00351411705003c0412902e5000030440c0c00f1502902c0d41c01c2e030340c4000070081a9690042d04100c1113510340e4100b402240d541e40071250a8074800400503011070f09180c010700816014013103481c41040703000c0300181004da140d11520300b40d441caa2503051a841d400114240c084e00401c101903400b40c03940c00c1c14041c2c810700f07580003445d03114000e114207985c0c070a401400600d640076004132014075940408903010b050044290640395902846500098460081d440c103aa490100e071141c42040c00030072074440396562 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 103372410 1250 103371160 103371179
    0x201080604020715061403070501020105040c05121e07050a0501020c0d0b0703021c0203011508090a0f0807020306240d0308150609091609050f13090305090307031a010b09030601 78
    0x102021146080d9030102035002d8125849134170700a1410042030041c2c0180e04051508100703c0760041e504590428007004081020703000c81034221581902c1030480e0794240100d032420a945160841c191110a00303207a0141000001c4130340030380304100c401c40d1a4036a03600040e43c0d00c20420001c260409031862561000c1242006021380c003d9903414054644100c2850808218603620a80e8484179400b200500c030480c51400740704540065030504030900d0402d0004160340740102c080040c0500c040f540d440d8204032010081e036900e41e0380501101d8107802c0c0140c00e1400c109980a400d03c3d60004450100400d207450803c41d05001d8160301d50b50442d46400800040103040e20860340c1d00081c04000301005501c0d2803c0440c030400300c43d128066031100301140140300100c00c0d44160b2055140c0041e4024540d9101d10740c80f901c01107400d001401c6d80b1249001d4509000c2c1c004c90170343c5405803040000c18030042401c0e042c505e015103a9180440c1c1e1300c072148004540240d4445541592000300140103030500c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 103373660 1250 103372410 103372417
    0x7020c010e031626010501080a1511030406020714010c050d0b0a3302010606050a030b0f06030a14130b0c03040501110d0e0d030b01141605010207062403020108060402 73
    0xc050705440c29201c0340e8442c0420a50309520050749140c03814029440c1e0400c09400704e1000c40f0f090000d0244c2d524080d01c0706c0e52009510f4000c0d05031824032391001c4098200d076014144160559800350b4603480c00d41807000094000780f400341d0b01032411180000e544e0fa818420200c40c6074407a00d0700e0342400c074140c8420000f04282806a50003405075030001c1000702190300003030041410810b841c0c10b071a041c00e22081c11074000340342400540e0304040080c0549a08034013502d0f41861145000035600324030400140d09a001c1504607604080004240003000c0b03441e81064411410780314a00d24185c407150281e4885034514400613100c000c3d10700101d500d0701e02c000d0003150400e028000104900e0000e4602c40040d600c41c802c0740f552695070745a11048220103010101d610440d0303042c104403205984001030a500d02502918050202c00211120300c0d0501021a140c5940c20000840d01e4000398a8020010300400f00104625040c2e4641d10126108024009040d42d5040e500c0761450b40741c41052002942 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 103374910 1250 103373660 103373687
    0x30b01180902030613120906090608090307020a09050108070605070b060906060f2206080403020c0f030f010626030307020a02040f0902030a0b0609010b090609060a0201090210030603020406050907020c01 89
    0x507110315072540075903800c0181c540164807100d030f20440103215103491000030545244003414400041c40030094a900100701804448460400f90300f117560704d0801e6030071842146002503000b00655404280200c050b84154141c85440040350312803038856400327613103601550030018400c11010000640c103007004003455400c200c000d002c0d03e0807c0003142e24000030790003821511154945851100216801681903c1c0c01003405050000013030030951002034603000100d64540c05490034500e01441a14100310440400341c80c80020090a0740f101961880702907902040703140900e01d0f5000f2003004402004403800382c0a942c0003044603209039400d000107050607403017440700e556803012140c001d61800d00005040e9445007020f00041c1c03421200300141400107800540c2d04917400d220020075032711181d08840700c0b44001c50b0040e84850f6070450072030142801080094015541600d610b0700c40d030701608070ba01aa13108481c00c3c4041a05c400502c04440380c1100d0401c01640300729201c7d0465405540c42d0503180 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 103376160 1250 103374910 103374959
    0x1081b06070f081909052209141b0301060b0c15040804030602030405060f0c0415211104060e01050304120e040e060c070302010f0603082208010f020903010b0109030b01 74
    0x2041600c803450320383c2003800854601350310311250a80c001e600124441c00b914045481107554103041e14007030b1031031120594a1200d140e5801000341070080154007000c1d41c18a00040f2201b643d50401254918032a07009050b00a40c04c202003c241c4580c0c46003912100b01d0003c00030080c3c804407407056400c00801170425540c2240401c408170104103503000451095002d00c00408082c00d01242004d224030001f41070b0402d03001c06000038001c03280c0f44000b00708608214500040c2c41115691807406003e01007503407009030352400c1d24403024045103001030b02c201c0d000c03900d84101200606005480b10f00c000c50780100554240034040607001d001700d01510354503401038800683c0d041480e80d01460481e003075440a544000100d40031080650900600d00300340520070042c84000d2940e911000c45000d243e081a8026041d0a006043c10651002440081804800902000008486480c020750000303810a0295003011140c1445502480024041760f5200082d00b220740c1c40c001e80000903502c07105402402 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 103377410 1250 103376160 103376183
    0xf080a05040b0a05190c0c151107030609030f0207060203030a0f02070f0309140613030201140d060303050301060915020c011805090c0405090f1e0a060b120106030501081b0607 77
    0x2010b0041001c2c08480a40b81c680da07540700000c00c020380320001220f440e60b04000701d800101000560b030017170707880c1242d01e040109515400008016500d14818026540c00c07407140760341c00014006d003a0422407003180170b130b110740d40105095081282c9440da00c0c000c0c0400360344201301040250310150b020419103084251f0040c140a0759984d88103041c0f01c524400e5001420002092200b601d4203842c043c81d4003c103c400e2840c042e43d6441d0003910116510010f8140080b2030001026a0f01c41822204502c600701000c010003922490b002d0001c1c0c1080c0100030025000310380c0030400000741420120100c0b140d80050004541c42e2004580001d42e808045101590b130703202c00940c0d0f40b980d13002c0320b000f02118040c060300c2d41d0808042c0204c100d0b00500001d1001800024001b072504200f1950182c1c0300307034003c06034180e83c420a4000182246901120180000044406038103811034401416622180c0e010703c0603980e035407121a5611b040641c4800304e2007510940543c140751090084c03034260b1180b8501e850 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 103378660 1250 103377410 103377419
    0xa0f05090301140108190f0b060d050604060f0b0402031e0604020f04080a060e0105040c09050a090807080909060121021806040602030c0105061e121c050903190f080a0504 75
    0xa5500d80030b8806903065505005001c2e8017010b2080900c0b10740c9507806e501c60401280c803041c4544111020180100b400c94021600782c0d2129004441b1503500b0404880540c201880c18074010400052117204840ca40007010446203807500885c0d00444c5104071203140f2199281c0c01080e003550286c00184c0c89030f820890315200103400c0d030142c0000c111440103408200d00c00d040050580c0c0c0d0001640f070003031745003008100c00980c0c4200c0c05410303a04e07081c0002600340e503104250780081c0340c0e0072000b8202903404203a20f010803003104010854200c06594180454481c4401511031403141d009100238800001c640190108032035000d458441c2d406011200480c41420100d8a01d0f8410b420100050f0400910403031444024010345401800556220040202510040903071007050491a413050203404403248180004004050501c2000b600c040301070048000054401c0d4407941101d40640104d641005207041403100b102402034020060b04203425250707448100320362000d8374140c14000d09100218 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 103379910 1250 103378660 103378663
    0x30b03060109060f08031e1803030d09031803020105030c090f04061e080f0303070507110a170d0908030f0a0c0512031b07020a090209040902040519051303050a0f050903 74
    0x74020700c0102c0e030000f4850306110f003030700821640b6005844280d20401521070b804042409211300250604412a21840c1031808000c202c104100c40f240d046c0b001040f1980804410f6000e103003003521130b4952403220b03582d00340445828100c51202034081002800062026034600c401420002002001c22030541d21480000f821600740307401440c11064500c0c41c2c2c0d1080c1c40b4491210000c0c0031080010805500c84100751656071200400203401c04c980130408030304010340004000c070b841c10b0050054206e19220a050f06280380a0045281030b07110f8020220f2800d03000d49440360660342c09201842c6009030000480e0901c0d07200c1c0854408000c43d070680d500204138140100b00e80c0c00c05d46c1407002e0340c0303080058074448410b05455810403510800c122940050382c803050014112012220003503101c644040001e40141076014000e50030a04010802440b2a02007010807107130180030300100300548030980a200090410356000380803030010400355000e0350062403c0030f1800040d00e84280740c84940380129 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 103381160 1250 103379910 103379923
    0x20c0d080d090206032d0f04030c0201090305010c080718030b0c160213020703020d0906050702010c0c05040903050c060a0b0a0e0901020d0e1506092403010609110408060c030402100e01030b03 84
    0x49000150581910206c103042100b503460840c001c800030411704000e49560210b40000d8001004e1141516020003164041c3d49510f00640c2c02600811585a0b284400b0b000c000b0126a8100040c260116030102c000400b0f4911054941106841d0a5035585180e10300c01caa010101d00e40783c0b40e207400103110045c1d4034101c918188107002130300541c0740c1e110b52602910b481c1c04c0c01e0842c002c0c00800d1100307100d41640031003603542082c0c0910b02102c50314036500b4445a9004580c20041c0c2060624401605141d0001300410025031035004544440d640c1341740035001c036034001078410361100a1000c1042540d40c41304440345c100b59010300042c94210780c407030100f046404490b1b0600c15600600d002521002070010610382c044415503c070341d191700c0c2441e0f4200000341408000149110000c0382186a5142503001d240a011008403c100701d15a1207452003207600a0b02c03461006206031400600e07141e0000d03058900465001d0200300c4010742d6140185e5888941720711a50425a50381000a103950f0200039a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 103382410 1250 103381160 103381171
    0x507090608060301020a1d010c0b070216080309100c170d060302040b0a0e07110a021207080601090b03100b030102070f06020a14030405030a11120409021207020c0d080d09020603 78
    0x1006921854610003621403003000b884103109134814008402601c0d000b05410410101e0f215207082c030130318420b0068800c45103450024100200c41004c1125050300001d100c0d5181d804064107201503561000000e40d81e10035002420b030402c0700c44021030741e1b0350301854000788150300ca2010f058401e0051090107019130072886c01700864a4841c0f9041080d41130911808540c41030954510003114102601195060300c09403400d000c1242d03000340d00c421440248040c07440e0642c02440c04059801541c040d03546c400b00da0144030114010342c0c00008804034903208402010a015000d480e20100148000000f000004140f41d0155020003145002504842000000034880d000c0140c44025140000b010b16503805218103100750304000780804120700005031041034100707241100921060a003014142451402c1804c401038020030049194801c17a006810b01c00003804c0f40c2e0800d59a4148103d941761032030019103070007594410003c80441c501000400c01001e107400041551005d03540810243c4c1c0c001c541 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 103383660 1250 103382410 103382417
    0x7030b0c07051b0f0402030f010311121507030c0c0c0e041728020111030615040308120a0c0903030527030a0f0606120209070f0c021f090501030e0c010509130507 71
    0x30210713460408020120b004065070b08505515040e003502d5030000041c000504603070b13102d0307049091a5503058440c0042c0940c644c1901e0b035014002100020007034040da0715002103820600c031b55981e41d11030b00784500700a070000c400380d26541c50414605012035001c1d00948000b006e0700380320040d2034142d2005160300c450038040700e10107000e00074100300c000b6002e10600c0110b90414082c005000c58071429680c00900c102d9201c580d103618007001507114402c540c40102040004038190b11141035030411f061140980410920002c41d56803021108030a05000c0100070460070b002d0030f0740d0045e074112a408051041e6142c0b01c000c410f0400003915040038400112080c20382d00d000c90081124038003c0e000200829903100d0000750180c2c0c002001600002c0c40b8904021080c1080b5200038400d481d24181550003800000d03007001040c07444000028201a54004070b114020005001c0d40700e0300c030b03003000503a000019058211084c801140d15501084400c0c0e448641c034483c07110740484c0d0307209680c061019070301c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 103384910 1250 103383660 103383703
    0x80d0b01090905270304050a0303120b030105070c1a130609050a211206080a080307050d09080a020f12270406140909030702030c0609010302070b04120e03010e07030b0c0705 76
    0x184e021a559001608451164106110030801900c0d9420030406495050070443d068000100e0f003c1c006045149006606600340020f10170003e400207108244907001d00c40501da8280760483c075040241007030b12203820310510829000040340301a0312607282d4920603010794000c0c0805881e0507003031aa180145117043d50820340d40c035070884d07007252882c41010404003007070000380d01e00b6060607100c001c01940984040000030000d4200d510600c1140d03000c4007581c108016007501402d15601627008800000007612a100c2c0c40e03a0301c640300042003000d0080070030040d031030103286400300007805009155003e1000d40d80c0903a0071042ea00c0c1c0c0610000f170818807020b0300a007802c200c00c0200c032500c00740c40c182d81500100b0400c00540c5010a007401c3c00c500640d0309a58800310400124024861000044e0040b002141400200042450701c2c550f481d406075582140881410200741c2207030300c041c0742020b107644040c900708009500320000701c0d84424200d07000360525a203500e40600300540c1c5405004030501c4503 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 103386160 1250 103384910 103384951
    0x50f0a0b07090e010b0901140c030c0307060c2c030312090a02030606092a1612030c030e0303040b07031407090e070309030f201b0f0d080d0b01090905 66
    0x940c142d000744030b070030200141540741a080020512035021410304001c1404003031601d006020b0b046481140001c0100da6031030101d41c0010380c40f6000b0982c00c40e109410103030f82003078840c0704481c8501c01c0000d6001030b07034503e0f4407104400c03006d01c9910b140da60076000903c0840044401100079a00c00c002c10b101600c80b81d9614410035060000040030140701d2541c1c0c0c0140a045403c55400200a8240308002d403028030300800780c00003a002d400120303182882c00030756000070810f00c0b000980135002a500c0c24040305101ca441601550820700d0f0b0144103a10510001d800b050271000300b5a0409541d05000410100040400740c1c1000f04132400b0300451766222041241220034030070303154808a80d02d410003151260740c0d001400e110130540b0040400401501c000121035080c511032180d52041006c8610000c0743c20500700c550810f01c2c6496224000302d500802544c1003905211904503070110707505107801c20038400710f00100720400c0e940f810441904800701d17440c0c3c0240704150103003440075100c50100210 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 103387410 1250 103386160 103386167
    0x219080705070503010c170604090206030924070f030504020d020409050f070b0a050412020307090516031109061603090e0106080412030608120c0a12090f060302040b0313050f0a0b07 80
    0x2a0f911107802a07141403880c060440d48070f0581e0390300d01002d82d680190f6403150b2000502400c94004003a5014400105000c0481400102070040f0a400382031850b41c11449440556951411100100072a104101c00e0800c148240e200300d038440c1c401005044116034a0300030400b181c003000310032103040e8000c1c10651185002040200c000b0b00c039001c0f150f45001d264510040c044c4c0124456804001009194030f811941d091100901800c000c0d07400300101d28189500c0e01c10600400c4110001c13918107084240401a13000c101c840d103580113840b1501d0702000100c070b04000c012001d02a003c20a43c010041906c14003841c03400c1c000e1205030380300d60660409080480042d9000030b41d59040c5444c011080220384030100d0300a0070254280c031850b4503181104c5280d8180030081500804030320082d40c0200505400c03401e18415201c1d0742030388064854445000341d0403445203010380c0c801000e0034800143c2c1504a10a1a81658070500a03550314001d01c0c4d039284d04d005c1002c030003200c148180100304291160b0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 103388660 1250 103387410 103387423
    0x1905161512021e070203150a020a0906170f191415180a020a050c0a0b0f0606070b01090b06040302090f0106030b04021606183302091f0219080705 64
    0x78a51021803900c050361400640e503d040310110488444003080440030365170240103960030800041c046031513a203000103140f80250300c5200102c1c00320794103540c04142a44904040f010070500441c0744511615000a0402c210700010b285442c14295a0318082081c00c1a010300c103258401c0f4074600c5018100740126122070305100300c01034058100310140009000401c01d409800003c000750043e80e90000c07900c00c5966201e0350100704241d10a04020030108911000b0203842000340316844005070b158003040000130f118190002e400c4540820050162803981ea20012024038014982d5141555907408121040411219803a030802c441004201603901030088000c2c051088404620b88031121101d80c2e140f80f094440907080b642d94007074001c070380c0201c1620f20f44c2c030a80001d00c0b1514220f008555500e42510120014407400526901c594a810f070350080d81c41201c801003000c0100d240d19036644c0b001c0320705000540114444c04204d1a141c84c6c044110343d400d140a60491a0741d40ca45090480c98100c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 103389910 1250 103388660 103388687
    0x30f0c010b010c11010c02040609060803090a050d0201050d0c09030c0b03070f14120c07230d020105011401051c0e0705030c03030c03071407030803070c050606030f19051615 76
    0x6003500d10748005a142a0b5480140a09081c03485c030346c4c1d540303002080c020080354011058262505101041d0004000003809040d1403c03101440704a403590f0038000062040c01009022035000c0c0300c1d4040242c0d094200780d030b000c91700c0c2c500440100d5583e00d6644000820380d210881210000003403001182d44a01101504804d80c28140019215101401c28600c0340900c0d4025810b03040020030900744084045800540e0800140d10f05007000780703c09a80e510759400d5041c1184100b11f0000c0300540180030705412030b80110848568502550019030301a8405041480100382490180420010520403442904503850080c14818101010325250541d1407036041c1c480d90080c081100050f00000849039800d900c6100750107445c4643c60401e2628189401c001c103101804020883e800d41c3c003c82080707219000e20700b03c4400c1d407102024192201204095a0b906030800d10b07403550307501d407200210341c80d00d0301c1041119096502803810084070003068104006c140705030300d400b40005501180094030031 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 103391160 1250 103389910 103389917
    0x5040303180e01090b032a1009030203030a14070b091b0d0804051005160302010c09090b01021203150a03080909010605120112060209030a0b1f0b03180a05030f0c010b01 74
    0x381d00300b4807100041501480b541038a251907940c0c0c0300107600c06201364030303901a55070020308a206c030503d4110103413000d90070b01c140a2080c02e5181090380b40705111030310490f500600554a0400c0d5004101e68034801000d2621403064200718190004101c038500750b12480e2403101500c40c0c1850f029528000c202020300c2148136075030462040000c43c40b0142242d00300e030700403071385c950440701540e00c00e6855000c2c0c030200b500e43c1c0b440020114245034043d003107455000c00d16a9184110340d250b10b0b4020440c0c10102515006074440011910003455800045030010075040103105140d0b044800201506180d400c1140c250710f020461140c1400d00c2e03485503024111604007141000340240e200c042544051046036421412800a03a09010180d07040f5140d21070040d05130b0321840620f007002e80c02d2081c00d0720100301d0300c480b02d40e04110b514403040300142070b140071035491891911250701e4181405040c0790030700140e020b0742d60050700240d810001010b0070500d0440740d40c0c90300c445640303003421664804481810b1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 103392410 1250 103391160 103391207
    0x30b0a0207030e0909070b07030801091104230f030d02010b090606030403080c07031e0e0f0609130b030f0d0c0b010e0c03060402070309090501060201020903010e0c15030a0b1005040303 81
    0x41d402480c0003a403c107060360543c04680c0c448005510300380c0360b80e000f940044000900b400505a00c4510141a180c2d12502846031070308c3d00d2004202440760340b2604403207828842d00d1000d60b034000d0032a0030f420100103021308210a241000242403440225104015039500c0030469020b0414207000303a88800120b0b20306081d80b9050300c0141c1072000081410b20304810000f0030601b018002e40e00800c00b11003c1c04080c843c00f20313405010700400c0350f05030030f42d110324001c10132007440f4130308001142c1e141d50000d040c40a0462944443d08040d103410103c2592500503a00c40c110903600400464004500b140ea5803124145039040c134520116041e0403101e002c4900c401040b6400303089a0440e0b401241c01e0f100140e4416441c03c04980c1c00300b450308181d82d114288000000c200358150050128814220300030480c142020300115030f00c02600b14a150841c0c0070b1a907130700012912001031640212425401308810340804000340346114118408000710b8000310301802070660110b04d0001d1240c40b1441088c4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 103393660 1250 103392410 103392413
    0x20c101b050d090602070f0b0901110f07060b030111040e010f0501020309010e0402070b01080f10021602120a080f130b09030a021917030a030b0108070909090303180507030b0a0207 79
    0x240c05444100303440c20710000260119003407003154010007031143c10000854a0300250310b0841c0d0003080c60346080e61000d00200109201800c103118080421200b0000b151800ca0751000b8408640c00403803042d9000ba070344a1402003551403c1c0140018408180f541560722410502c540c1c0b01c420040e0400905110301c014184101d980010845c0c00c14002420400c0d84654483c00250103480703013220050808410780300024158400040400d100e0110381e054030301d08501c802c40b080c100d0140688003503100081540780340c05814842c8070501c0c81c00c403280c25200d45440c55140e61040c0d601000c04001c080c4000210300006003410079032080900b0a14406500d00300c0510002581c034407403d01d02034491216941120954807040c4100c50040c41c1000c112074001109089554494222804203030110307050a684407a42e44c46100384512034030541e1038a005442c14117400c0c02c02050b00c0c440032401d02d0f907102d40221558007038441289080d4806e00007003411500710301d00029002c201a005607413050041c0716540 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 103394910 1250 103393660 103393691
    0x50d0c290307080c090d03020c0112020a080114121b030d0e030d08100504060b1201060c02063004080a1106010f030803091203070503040b06090606040b090d021201020c10 75
    0x342c0141d030900e007a020760703211120b8a8409104a1500541c0811a0b5080301c0815170007082050744220240c80700400f0062036003881c800d0b803194508650005506200504c090725089407100b2900101070402c80e00500002c000f0342c0307054990f4500c0728441c1d0980c0d020840034902040748190414403490401c0000392400042913451070300d256803501f400300000014180824900c0108014070307000b00280201c5d9030700c0b8200d00305940041f40302114642d05100110b6043d000f007401c01e51080d4090300d1585090b841c104200a03140040388402800c80b2003c011003903034000d045000340030394024507029a41c2c0d1308410000e0400c480144210383d41d5040b2400400021032b03000460002c4a802214207692a03a903041120304100200107005140354000c0144100c10382e0080c06544a0ba11454942c40c0c540ca4031400c01150204c1128040e40c0140700b00014401c0e5400a0013500391000301808941034540301307500186030818041d030b00074080d80d0f02040420621108014004800d03103d114200719200040c0c0440 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 103396160 1250 103394910 103394917
    0x3041d07091a0313080414090c0a0f0804050f0d0f170603100b0307050a0905090601080304050d141e010e01061a090d0c09020d020703080c0315040b0604050d0c29 71
    0x1c0302c1220020000071107201501d000f00b94110750004c5820341c0c99894954208400034a8542c40d401000703100700203503249030b030103040b5041088240c40302060344000d0700d0211441d0100a0003103405004040c4001ca4143c410050314400038255106c1d22184404180000d04000c004444a5528404c41082c009184c40100b0000b0401c940080c000c07881e503240201203403514007030b9844140c1204400750f000071200306a0b846540141c14482c01e58115980e6901070540d40d00550003520b910030880c6070030100003802404054040282c1e2025640c0c0c03d08508200303201e54030258000031051351580040000901c082c448d11000e0400100e541004460b03c4842d41c0040c0100710540340105442e6403648140070126080d8001068400400e554400145099501a400c0200304801042011005c901003160400c2034a1046020024a203151980c140800002d45040c3e20703800d8015004001c04215611665a40f00b0158061520501c03260305c0c0180000000a21021075070000d400300c03001204504095048 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 103397410 1250 103396160 103396199
    0x27030a140901050c03030c07110a2d0305030309060609070f0c060c03060b070609061a09060409080408010f051008030a0c1b0b0703020c0310020301080c0103020309010e03041d0709 79
    0x4507854040201c0103850074401c5a2000740184000f0041191000190004004032446004080e4444608a061004640081c00758a0318006e0307601c089c21051441c00322145001403200d2000039626540d0715101d0861384241c4400b901904010208602800c0000c10b054100101d40707007641e030080d8a80801001c1c80100c4c4c400901d11030f1030f51a22070f00c180c8030781c1142002d03050145040766902d001d850b000780202040402100d4440c140350400d241142903210101410388003808001d02c503603d0f4420000100401070341207400d88024000070600c50f000741300b0841c20310a40000020716084c5540e4901303ca02c0030354803078202d580c801c00c80050380580c4400c004900b0f40c1c2c0542100c0072070031a0148002502001e03042405100800300301002031580c00254219150001e0b01555845802c07100c03c10147d00c024014a0590b5206185901c2c80d54405d50045901c400c0f000c0001464020203c03d16086500c10307030020102c00003085280515410745061030381c00c0041401c002032484d02e071030020401403400008 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 103398660 1250 103397410 103397447
    0x70906061d03191b0f1a1b0f03040303080903090109050d0c03080f090301291003090f0f12090b090114120c070b07030e070509060f0306070216090614190e27030a 71
    0x901c0b0030103601d4080e018038087c0c1340d1410b603050448071484040e5039800500c800c0e000107808030003050b41c0e80408001c032540d450042e541d1101d41e900b82002d10034440b4940c101254501d001c144004081000c0c4800307401c4209140c4504e80e0750300f040038109400c1d41d024035500440c1d1b003181c0c03642030b0b020580041c02845048003581d0ac500c2e203040484041c1c0082618620181002d40760103060020400e04207001c1d82003a1107049280680002e00004594058083c003502c000c1d40c5080041030050344c0110208100e11401e108154500380030562000e1640c54165003503004413002041240402a0714030100c0d90064041c031b010441c100311804101d980c0c122901c1030303070701070510b48001c42c80c641c03940080c0d91000782c0040c04071032450030020300083d80c030030140d07201d03082c1000824808611075a007405010101c4402d401a202924440f40070041d0924079405140114154085e00180e80309110250501c6101c801c1d80c01d245240b03505034046c0540140c003070381c10929001013104000113508080302c0c004102c60201e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 103399910 1250 103398660 103398667
    0x5010905011e03090804030f0813090c0207091505190608010506120402040b01090915030302071401020718200c070e0115030e0f010608060108070906061d03191b0f1a 73
    0x1420040e40c4103030b800c0500140d00140c008c009102c034400082051580d40010107102a50790841042250010001200140c000345420071440102c0e42010000641003020450204d035180005040c0489a01d401c03034400c4442075041010ba07806c40740b490700400e03003a00c11030300d4041544258480e10400034002440303039039181000075079a44210000c3c00a080010303010041c040c5846241068004d061000b24014800d004000c00c03400d0304104980c00b500c0d81a002000075900700482d028441d81e900241000310780d80c960050400a2700c0408541160849405481d510762402d20407509240302902300148484000004014001c81a1440c0f00c02020a04e400143e48401e05400f40c184000400208190740c00c0000c081002d00c004500745048464002c11149030340e607100c0b0b46170305640092043e4004600402c542f0780c081e04000c4a0002c0e208002820749100c001c41d42c0918058250380c1100340c42c00ca041c01109007240c26001030940280c0644a851103e0074074110140074011440f0705120440d03070010 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 103401160 1250 103399910 103399913
    0x90c01141c0501060816030605010203070b0a0b09010e010303030b010807052704020c1f0c05031f030501051e061503010515040e0106020f2404020d05032205010905011e0309 76
    0x6804075007940704074024400b03541e540a00600150040e102c41039000266800032071514024400d40b006c460341a00618108141c0f6160350513030355002441c003540540c64402d0914599207c50680e8044d181c54031042c0200e5041d800c00074122151003000506000e00c04060018480c0c009c81661031050b409032560a05d020307036810b8400064540c2c50010340150000c200c1c501da402000c10110580c003122402c01c2d0800e803070210381c1c0d0141e40c44440d101000c1002000851000354140114a0350443d41c1da462020145d80c1c0d5a4141c00c61380101c500d070a00100d9680d0340c10000311880092074200300c1c00c84071558155a00886100d652206215651040810780303860780c00b41140c802502c0007030424401e40c3c1c01e55a55510003944410114440c80c50300e00030301119402051640d5420401d900b501032030746c5c0e5181d0356030f421712409010012041d5207510085c0548103207070025a4036800850901902410003030b180c07900151a0b045550025414804981d4100c0340c41d05c3c00954540b48241c4601d00400c900c00b5a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 103402410 1250 103401160 103401187
    0x41703041b080319031a0f0616030804030324090f06050607050703020901120b0601052b06170106180504020105070c0306020301030b06100507030c03050405040603110405090c0114 79
    0x90200c0c100ca8101d0900d070000b900000030000d0090807100c5000c1000154088504400b00d801010f0b014210450712004800941482c1d50b848801c01d2024250514004103003141500d0480045c804400041c0024200410103926001b0a004084000140d09d142c0301c0c040511004c00c100b50040040c0c3d943e480200040380009908100003c007001340a00d650740100e400c1458403140d0501003a401030720301200020301d505015800d8003130640c014506d2206520303050300454080d0f0264650401c06040c0a000c850401d49100800307090708040c03800080c09a19081a507440e07070b502c0800328151a450141d0401040c00704c8133301100349038420100028595034600c01aa402d00031914007512600c070700ca0000c420840240d0055044e0380c094512502035030f41c0c40c800c010043c1ea00c42a9600018000d006d5a800240281d4000c6c0c8814840d04115017050b84800102d400c880c8a41c0c82500d4200ca008000c0441e400e02c0e11890703801100c100080e00110b038044002808a041d2190704080d50a00022103100300c000c2e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 103403660 1250 103402410 103402433
    0x14060a2712060203040b090a0519230d03062403050c0c0607080901050a0c090905060d021e0f0301020703021c090e0708070e010c0b060607060b0603040b1e04170304 72
    0xc400305000314066182000b20094108650071500b9030307846130111342d4201e8000358141313066500c800100002a100c00c0180300b4008e210234105e4007a400429054040c0e01c104801c0d10b14012914010180c0071500c14004094500c0c03944281c1d810b14503044910903600d280091310407850840c0c100855a515000310101c414455080ba4144600a0341d05201c10300794403268007401108588001e005684079000745070219017030007403207001103500d01e9410800e002454101551021008000c00003c1c3c00c2e907004205890340d000d58a401c4a648140015030503d0135275180001c14405400841c20109595406503985064000141041300d41038081e01d0143c0c440c101c690040c00301407101c0c5159060581029100c52010f55217640411034012107000294440c440314001c00e90401c0e00110952690410b1020583c0250010303035281e900e45041001c561a514021401180f14003103806c010720b402d8042c503c0c3c83c0254000310611340d001c1380c180400708401c0d4801c0c1890301d0380301804d1550b90b1520318100362900b5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 103404910 1250 103403660 103403669
    0x702010504080d110d020c030304031e0f050d03151a070f0609031d09100905100812030109061a07060c0c050115061409010917010207170414060a27 65
    0x304103416042c1c01e030392082140c0c06441c480811610000021740040c4d07107030314015213400d81540c0284403c00c082031000d2103111a2100d0b055080d0703070300d035416200c03002c8004001d81c00b56110b50142001008213640352040a01151071041c1450305141804c0180300c072030422003966214108040340d42403e110100880b8946240d01c01b104101c155140c0c50003400707048990052000d0070201c050f4100c40c50418600c0303584a481c941050000c03080c00e0101210007404040c00003000c08207080404955004100109452540b0319107a1725160b614112000003580d4880d00211080401e903d01c88038034050711419240b0343c03036000001041406a11608594602d107090303000e40a5820800c42600c001d640d01901c60994107240e66294250300e490201c00c81d2881050310250000305001c07010850b140c20b03021a89070700050032001516101d4191152009604411401480280001030400c40b900d5007100d003081c00c5c5c170309032082414809581c0000d00040301480503001c01e040c610030a942d951000103070240140 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 103406160 1250 103404910 103404913
    0x301020f03091506040c1b03020f070305010e0c01050f0d0b0f040c030b01020f1b090613050108030a0e0316060e0301110a18090b060702060d0b0a1202040c0e09010506070201050408 79
    0x2460b1000100d90b848041d680d000110500640220b0b81c0f904003801000c0c14000140c44880e003405024461003644802034106030110302400880d501d1964050210100444c020f0001042c112911a1001e0a04000c018214140601044404d40d100410713001d03030300003036901400062250b0859000c126240d1441c00540e034000d2408001d001e401f81c1581c0900712440c1c0a0f800c41d9a00802060107540e502040d54040441c0014950702c00c3c1d55141240c8e00c41c0d885180034151486284d03101604c14151007003a00070701160303040410010200c0b6070085408020f5103044008021025085042c000507503102d009030001c100c4042410401c1e903d003500030540c02400c621165035036698015008203ea2140c0207494a4031017019400203842d40503004542090070028030082c540704807a0f080055581c008040d01c9141c50f101d40540815a841c1900030009140d000303021485229a4810030044a50000d01402444141c240c010703401c0c0c99004549042d81d40580d1895601e04041c00181c400340103d9220b090103 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 103407410 1250 103406160 103406167
    0x81308030a03052205031801030e0105040f0b070c0c050402090d0203060405030417010e0d03090c0806010315111206060c010605060301030606031a0c181c050d080907050a140301020f 80
    0x76a945607000621035550741c054081000014080841030800721000584240d00a1088826600392080654080b4030141800954224411820303801c1d01d01c1201c00381c0345025070040a006120345060b4096101445150003c1c1d0285907541c1e105071310080c1d00485000740c4d40803e29021607120b0b402580611a0014221001c0c1e140030710b0110341ea0307030013070180d100c0100034403109904440c1c050040c07140c650311081c0541481212290f00301c0003410f00d040d0035034142d4000079002651100501482e4043e602403420750900d10b08448912094443e40000b01e1100041004580030042229243c1900032104564890751407a0040125014100302d0b007005600c4000080004204500382c1d101c0400c8070310139281c402c032108440300b491420341400c4807401c41d62003040004902007062680644031583c8003c210070101c50b0f61700e04070003600c60600c0041300d06500c0b0505046e850394001c091a0b0740010508002c0038401d0401c00400c87c4d0880c00d205201402285a580401d1a40e080d01034415580d14061403688 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 103408660 1250 103407410 103407427
    0x70c020f041a0a0506090f09040f0f0b090607080103030e09040204111209010c02070803041206020720031519020c07080118031403040803040803040201120e0a17030702060408130803 80
    0x255100b1002c800c0c03284041010001e0142021010b40d0144903008006000c844100c0c0c1c144503510300010300c2210000c1c0d505100038005181a0401c9059074010401260146040541c10389808809400001400070301c400400010380d000c1e008140128081c0c520154a80b10707440820058032222000c03200201c4080380400c410110b000c107076403107001440c00901c80440c03440020b0f80c8444a034051100b094008000074000c1208041960b001c051080e0001031030406103072600c8104c0e444a078803e04800c0c0e254080341c03107185010085042000c03c2207061003c40d0514100101e10201034152407120541c001c1a0f00200d2003050114030010014203000748030b400b0961051a1018141540450106101c0d001ea120711184110550344200d600c807140601d55151601d9180568100400c05c03030401030102c144244544a0b402590b803001c050a0050507066034030b1401020000b03601603281c120341d0061082128041d0b0001e0800c1e04203801002065803018080300b0b21080700e442d0341104c1c4407484000b84090 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 103409910 1250 103408660 103408691
    0x140106020a0201180e01170322030201030509010b010e010e0a1203051b06010b07200301060605040503010c03020c030f032e06030c05090a170102070c09060f050306040b070c020f04 79
    0x8007440c03003662580c0e41010f1400d0001a0b2003040c0c011031300c0f02c000500050103200c001000c241d0300004800d040324203080c02d100e600d08903200c0030341c41c0388a181c031200020000c40d601800f41da41c11090800086c00300210740380000b000707143c40c000c072141003100040701c046140c1c98a200c40310150102201c4405698602c1c01c0c090a80d41c80455410103400340031840307070107165000c220103042e00c04480d006441c0903125292540c1811015007002861a5035218000c1e842e03501340b01315402000980c40f907a07103c0d89800700b01400c4507443c80411090500400c1004888000030003141c000c0307240000c40a031207031118403809079040c400701501d0f844521a250001000a0555182c5040750f00a54041c40b540d0f56400c021074003802076405090b0840b8074004280042000b440c0040443e01e03502000604107641c0752a6000007a000751b00080420745c0d41e01c0107020981030700c5c1e0950041c001c25401031105007419610340c404694001e00c1142000112082d10302190744000030304814a0340100107005141c0c0100108 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 103411160 1250 103409910 103409923
    0x608070305060403080c070b060105300103050106080d02030306090c07050d05090405060f0f041d0a0303090c05010e0d060e03090904030e12060c070b090c0402040b07060f0501140d03020114010602 86
    0x26000300b005c4100041a41c0c0c0d1030001c80c2c81d49503100c1100082d07902c1c0c180041d00c65030003490707980c959408440d0328001e140201801c107408d4420700050b13900d030951450801e07500b12070345c40d041080503401c40c4090680c0c1540020849030006001d941001c07070b541c0c1d503103910b80c1a40140a13000f0500d000b120300c005e415913403050292444c10000c90b0300304459181d01c0d00b004030390445824490380000500726020780e145042da00149407051501c554421540d010314104e4104616000c04401080c0e60b01d0b6100207100c000c2450201500081c04e000c6003d45645001591851094000400d103540311804085280001d0003518110b09000e44100070506203440d010300400320680d10603000300251882204c91100003d04140200d114045941ca48503164481096041000700340300840c0c8202510368020382c4543c0b000303000406291049944a40651610900341c480400320300c0d40a41c00c1c400103218001c00020840c000c41c1d800ca5050035010900e00e410380c0540010f20302e01855075410703000060041d8020901 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 103412410 1250 103411160 103411163
    0x12090d050307082503080601030903021e030403060609050906040f0302010608030f03090d0c030807121803050a170603120702011205101415030610051902070f05030c090a0b0406080703050604 84
    0x10000410514106401301c265010025000460160120360700b54000e40c03229040074020f10664a0420016840416548018612100076800020104280186489890044d240900e0140a03a05281d83d5480d921400500090185013a003054101018000d51004004018403070669880d4954500041d2490300308a442e94050b028000001c4851803141081c8204554107888081942e12802d5080341c035001407004600d41c0b82e56a02040310103042d54201c120350148a175170b8481ea01c142d1140c005204a010a0b00900c0d45043c510910901d40d0703020902c00f42c00205041030549901d07050004a0345c80329083c3c164400700e031400003403044014038074030b12206071007004024203c05103048050208400d003544294406d22018400f04020307241002040f02030a0345440c0c114208903884a40500181e800648040582d011402c01c1001c428490168002848110301511031040200046280d0000080840071007a60300d6078207540340d0fa01c41d80a20060400d000071907000325124540140d6030b91043c0c60 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 103413660 1250 103412410 103412437
    0xc021e0a090501060c20010f081b040b0c250302060711040207060f18020d11010509120106030b220b091606030203040b060909070e0402040b10031505100212090d05030708 75
    0xd40302d4503651a84811600c0f44410fa49100c204020344c441204c0d27611000e040d6490018090b1203100000b100c072400f90018001c20b407016580c5410034404545840f80c20301c0d03445131016040c0042c032111b80c1452403c2003243e0301680c503503030b0b1401c7e070749001400c42c011841f61036881031011a40c0c50130301980e580103400b4110348600c100420355501403840c1e5002440400254020007191100d80012070807440e40d2601130b410b050290070075102100240c400c1a03c940303121141d80d92104200180003058030f00581140c0303481c6200080700c00e0360401c0d84014041c04030181c40400b02e84007203800510200000389458620b2840c0e588002e0701c92800601a60050b5410b4880703945544c045586440c1030213146016000309002001814500200840305910040c03060780d1150f610940c0b9003040c0c0302e803140d407948001e65580011340b01c4c03c01501c200412840741c1202d80600c00a080c081344007034000078807406420340e00d41b156484e20b0244002030021074403148001d00c2c03030102180e0b074001c000c0b40380060102040c2030305 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 103414910 1250 103413660 103413683
    0x50106060509030d0c0602090a12060c03090b07050c0705090703150f0b04120501061206020901021009080301050f0f0a08010219030e0d0516051c0f0c021e0a090501060c 74
    0x3008590754040d4030041503040d00450740207281180145414540648603580243c01c00c40322200140d002e80c000d0b032050110001d104078030010019075224200c0025100e0804202c0030080d80c6030041d410300300070802014008002459510244c08000c1a0b0040c14020104c80c02840e119600902500d02d0f0703890440d10840550010915030510400142500c0400300141d040038585103845251401e008401d45d11035607942000304000201c02e00041056010b282c0150303844c1490301c0024a00b51810b001c04850b1450421880d00248400085034111003040b510401c4c8160203d00052400d80b9940348150300486100c2c0010304044190041e08503910f02082480c100c80c00c402c010b405032420307090301c01225000324500311102c6008101030210140348241d03060608005940303030362030250085042c4101d903404119aa0002d80c2c407154040001d060303450802c01058185d801302d800300b03003804000713003007000a01501242a100d452580000301742c0c101c0248150750f5102e102420000d00d180058072000501d1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 103416160 1250 103414910 103414919
    0x120117010e0f0c061b03070503180f0a0905070203160b010e070504060503040303050c0715060806011d0c0a02010e1c02060c0a021b120f0106051228060603020405040b04050106 77
    0x214031400b008040201810120611804201c05039101070101d0000c9400c030800c00c44000e0041015001c0c551255005640c0e4024003124404c03201035040b40c1c0c9206096414503c04107880d05280c0d08101c40c3d540f00089040d45400341d0a90031800342290624003007100c100c501080c005403095850490301081100d00321500c5106044686204902405011500030400b05002034800d07441a07038410121890103080a1259079410100004021b2500e8916292002441400d50030300406004290401c82d40b50070400a055000300603000415401040002240160080303000390050907242e070f0080c003030b944180e0303404143d490040440f08044c00144106000200c880c1511030458914242c15002441050540882c42c164005813500c0c03541c0109250b90005200d42040180110881d45900089111030522050040b040307110a11800151300240c3c500c0002c02003145184007000e12492900341c10a41410300301c0241a16920080d04503252000f000180034020003500e001e184583c000348000f0341e54 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 103417266 1106 103416160 103416163
    0xf0e01181d09030306010903150b0901080607110303070903140c04060801060603050606070f030f090503030403060903180819020307090c0c1a04030203030703020c03120117010e 78
    0x303408541034040300310207445600850101c000c50951a0500000b810400b0038400607103c0118081120031940058009410941c800381180441d940c0d01d0425030344c2c650048030004001441540c0380440ea00020084038040c5245949000b015800d6482e000704004484101c2000c512506002e200a03469a0048400403c21000000381241c40e110020341030f984000c1c030300c1d0300c6250100039090000e1051f904500541b038040c50100103c2c241044107544d100001c1d005107515200101c0c0000400165400002070144a0f69581f80d55020005854030a00601e002d8002c2039040b295803010128241100302d05001d0005040710650780c0d580c80008201c8002070b1501d000502c8c03500800b018011400509a811540c0070640d800c1c0385800d8a001303490740409410f00c0704042d00011030000312841002030b1182e0801c0da00880310300d965103801d001800500c88103a09444d500341110130000000 = true := by decide +kernel

theorem cover : BRFrame.Cov 103237410 103417266 := by
  have h0 := BRFrame.cov_init 103237410
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103237410 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 103237410 ≤ n) (h2 : n < 103417266) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
