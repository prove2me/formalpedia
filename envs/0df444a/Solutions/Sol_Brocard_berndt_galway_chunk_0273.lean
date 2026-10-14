-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0273
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:53:21.438282+00:00
-- url     : https://prove2.me/submissions/59f051df-4819-415e-beb0-ea8d3da49078

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 48920867 ≤ n < 49100723 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 48922117 1250 48920867 48920869
    0xc0809060d020408030d060506180904021206040309080c1f030f140901061706090304031424041202120d0207050109020a060e0a08030307020c01050304021f02010f06050109080a0f02 80
    0x7251280d0081d9a000c41d9180c2d514941c054481c0c004070342c0a00702c107161100000350390030428101c44900b0211090320007141020307030800280010107001681c100d5080307080c01480013020010640142d01a03120309000d5440c0051091030500200320042c0111100b11045002090f1283c02d01a0302080d41404100c10025200c4c1d9002454001070707004d110f120301000c0c40412001948640160381c40348008005c1a085141c0300b981d910800e40d0200e405a004000070000f06a018100f140410003074401e882c40b110201c940301404c12044800b24010704686824001005490b03141d200d000142070000d0840080c0d0200441010300401c0d0420000c1c503000a00c110800c00c081d44501d42c201d50040401110903107961008241521924116000da400c0100100d243c007c0007003502d20550140c1d00400d00c500e8407a0044819404c060000c07a0401007040e9240050742d04501e000e94000b24a03400060740b00324501c000425240641d100c507040c800d000c07400b8801040080f4500d40c3c070640100e020f0601c448184 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 48923367 1250 48922117 48922129
    0x30905041e060e100519090203060607050102030403020616030e0703080d0e0709020a0e0a0e06040f0207020405091606110304090509030c060709031106031302210f0102220302010c0809 81
    0x201000140910b000404220454100c00c00c9001d4242d4092041c0a0390b2108140a0303142c038240b422107001042d4600400403840150000c5a002c2000360605041c0030302692400d0aa070810f45049015070000c01c1000241c00d0348005020b400e1110303140601c0101c168041161b03c0384a680006081b0640001e1040b0060480b500901c0503007a4403030440729000d6850710040000d421072011480080d030a00d20301c0705549840034003001940c42011a45038039845107820040103040340710440303000a40920604000d640d841c030415202d50040000352016410062001c8a0031409410040030711440c1c0c0540141e800c2c0001c15a0103a5001403000201a00d41c070300214a140118000c8001c0c81c4150b50400140652141e000000c0302d00c01d50b03404809071040010040039010413900c0100840c50300c01c0680c05403070810850074001c02040c50102c410f000003a480f0741440801a1404407982d000207956613681111402c030600b524000d41c0c600c07034031811540001c0c40c405d04400003070007052003c42c145916507686 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 48924617 1250 48923367 48923411
    0x8130b09032a2e05070309020405040303050a0e030313060504020604030c0338150a0e100e090a0807020d060b060301030c090c031509020a050403080f07150903090504 73
    0x20500000d0301d0440390081480d0a600c01c01280b032a01800d102100c1c0c03e440071a000c0e0720032425203191403000ca040ea0044004000c010449402c140d294500300c0056191031042500880c003980e408160341c42e02229650640700600c1c403c00e150780c820010090b10c0482d2000384882c10780d209102240549550000513424000c6802c05400d4216408000041001d041d5070b010340f00310a12036410780380d1401d90042182c01d40c500c900b80210503c0e10001030052081800340000024028a182002c644420911144500072510380c058490590000e02c41c46a480c50850f41c4050154000c01d2030490310ba507891014040c40030024003d407268001e440c10000c440d00103d0070301002508107922581c2d681040c40c100c4580d440303195000d914140b48404424070a0150310492810050740204040c0f400e5204002540014201d100300b01c0306010100002e0082401040360030240c41140d85c03540c1450402e50b2203502d801c1044498030745008400710001c0c6e0000103210864400b00d50000e0344a5844014800041c01 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 48925867 1250 48924617 48924637
    0xa11010c02060f040e0105090907030201230c0708100b0406031a091f0f050f090a080f0c01050c09040b01090609090f0b030d021005160503010b0306010207080d120b0108130b0903 78
    0x4130b00443c5462240c10007504a80d400c0301e0354101034030b82d0510b00f80c0300e009a000103400a001840e80460fa025844c04947c50321480302c81c114541503094000c1030800c0519000342d12141c00c80301802d130040405000b118940c180c2154100301241c81d540d07038000740c203525020040c0c6111484002403020103003404400c4070190050340507517071610001c3d141e00c01042c0d200810070070207103001e000c220301c1202d11040034419060030004144a0000307459245903034105100300e0181035000c0000c8001682d0030f0190303601810010b840e0680b128029402c00007a510b41c16041d40c1008a182c81c01c000180e80410a4011074501e0800007a8010080745800080c04c80c50745c030290584101c1d4050340301c956002440d00c5410710007030300810140d120030395500c00f22007143d104180000c60900040c070000a00c04011038208c0d505004031001c0694802c00d0506004a100210005c54007158021590005902a00c0e4442c0f1091820b20346e40d04c0d0241014844041c08138000e0000b01a01c0002505d00d601041141d00c2120 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 48927117 1250 48925867 48925897
    0x60103060e061003090b0424060503030313110a03050703060c0503070207060f020c0a03031809061a030901061505030906010503120706051512030d0e0c010e1e040c0f020f0a11010c0206 81
    0x1f0b42030500d2040c4800d03080349010341192003400000d00d45240d11038041583c400030091403464507180031f901800c0807900402c1da01a00100064501c0f0f036100451800154890805884150f2440c1004001c49001c0030800c0c090100810420003290b50104076041544c0537400d105044118288040346090029010039030807200b0b02c80301005064200c040d0145140048403811140307a10b940c001420703186c1d54030030350f400d412b03003c0303030645400d8124005140c2c0030740c00c1400050038070358a4400c42c0e40e9082c8201d400c00803590000a124120300140b240c203024203c01c0c0d000708024071401d1701030940c902ca82c2002030804c5580b8004038100740030300c2c52504801c0704020a09200c100040305a60380300e5006240203d4a140f9000d0745400210000c04c18442110058482c170038511400310500140c15115a0303c1c0b03202c601d048421050750740d0350b446000b08155203507540048080c2d030240c01a24084804070140c44c2a8050540b8100007441841000c103405028a0000c5064013a1700c00310f070b03260040d22001ca141d45 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 48928367 1250 48927117 48927121
    0x504020f0d06110d0203010305010b0a060516050c0d120206090705010906050a17040303061d040f020d0c150c020a0605130b090f12010906052503020711130c08060103060e061003090b 80
    0x138616009941624001e40081185625090400402d0f19040c840c81c000300d01c05101c03034420890f440388840051030158040d242041908000120f100d0019441100e503100c000f203180a074036504004640d0b100c801000141452800d1400187c92110036200b1001000000150310324100d200b40d20200004041500000543c105482c02801401a0b4003e10a54640300717078001c11291001d15140c3d00403500004128001c2d8280e4080c044c3c507031240e1109484009500c0000101c130b043c0b0110003030310b5925998804021141c80e104002d00c0c1d0040e5400300082000c2401051842d601084940c821118445207442e43c4801d500c000c11a0040205000c03644408400000da40ca5001904801c074580e1040004001c40e0b543c0151402607902e442c004440140070706005003900900075402000c590b40101240502c1007848400030311440091840040308c2038441c082c0f00f2101d9040b440c41038002d0024202130000d40c0c2001c0840106801c0142110b220b0183c00303142c42030440c02503010071040c40e04078401c00341e24 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 48929617 1250 48928367 48928387
    0xb090c040504020d0605180601020d0e010507020d050f060a05100e04020609010c020406050a090204080708191203090212030a080601030509030d0b0d050a0305120901061a03150a14010809010504020f0d0611 90
    0x1f20408645050150250018003490503105124248403150140c4510342000426004d11440503449031342119940302e010310640e9100410060f4521138600e917080403406250a103c0c0c0301d600e0505a108445501c42c1c0300078070005a840310140c0300c000d50300703183c5540025494000900a03266641c8031a4200c11038050110380b0307210b070b0303002441a980c9890440318029529003001e551620311020003100d0740014041940059008901001c018400d482e0104008403075800203407864400c42c16401855000080001c0c4050304400413a5114009081c00c10031840d001c00015168441e9000d2600860341e500c10207802941e801c1096141d0980110403103210242c1c5d4500035100741d0200380034205080c1c0700030000e90500e905000d51030a0b910b040d01d014421030a541000f4030103030409401b0040c404032184c112401d58441c81c4120008021014050400c40a031130005000180043c10a0005034105010040035132150034040040c00020f035440341d078020190600000030102d040d261a0000c40000d85420303e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 48930867 1250 48929617 48929659
    0x3060f0e0606030c01050702091b03070509090a09150c020a0f0803060a12050a0320010c03020301060f08310b040506040c0801020a02210f0408030d0b090c040504020d0605 75
    0x40080c0400c21100161505410940c2d00d00c0406001030025008019000c01418140996034109181e05010b826020903e02401e0160700100e071040c002410102d10300c400e40c03401400031908a2480881009800025100c05a000c1e21312120980c5180d11020480c40c81482007010144142e00030040301a0300d9214074090003d0303402591941e100307080040c00401c44aa004865134082c0d50b0000c001c0c159039600d80c0e829a180105e054024010b84070040b50103003110800e010b01140d890003a500141e5a6040c0319001d0b0080c4062803061003000468400c102c09181300761020b0b011080340c180000c0d4030341c1450090710031051441e14000c009148120912007041400100503000b5071048151000c410b0720303950307110701301d000e07141c039500040e4008a003010418444080c000d1600110344405480d0541c110490001c0e98800d03031040300d40703500c002442014003000340b1407101002d8048480314081e0504c0210148240614010030340300f181d0005050840d018680c1c4058010701d4054102c00e20f1480c00360f500c5003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 48932117 1250 48930867 48930881
    0x109050f0f070206070e01030b091e0702030c0304140402090a1701061401020d030915021c0501080a02060d0216020d030201020d0f15030803060a08010e030406021203040b0609060a03060f 82
    0x1180034031400414960148112141d2094480350300510140c0d5808600700c0c0da500d003d841c100d050540c0e440032a41c6503201d4098003803003a005421348400d100158240c5d040003490080c0b01e0011504140111aa07502e008070468003101c602814a1500014100014000784184081c10fa4028036040c0c00280c03440020110500c1809642c0c020860b490f0303511007203040c60010840d40c50040c0c1102803d11075003406070348000c880300d00840504c2d2010b2003001111049034400f28071034040c0c190340c02003443c12078480d0090074003602232400601480c4040e68081102070241044500243da0040b80710a00460b03013001d0006034a030002d00b03078036410303d090902038001d5100300380b0b8a40301403d1102d40c031807202c03450141a40026441c00004403491441d04c84022540000e45010750010300a8400580c400e0240500e10380201000040c0d56035518260000c1c4c42c10314503280d0340d507400c0c40500410002c11b581d0522542c0c8480250b500c400b10b540c0e8a00000e0070100c603034100030100d03071504031031009458156000c40 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 48933367 1250 48932117 48932131
    0x18020d020f220e0105211c18050a06020604030f0c02030a08090f0d050304050402070f0b010e0702100e03030114060d15140406080601030201110f010501061211030601090b09010c020306010905 84
    0x40c4141c60307040b000443c031030900600350007100e658003520040b00904481c0e0300300c194801c2902d681d85c1d00d414006603425880c4a6010004262890030181040b07554041c100030700d011190008454617060002c0c4d03c1d10001007020b030500c180300e58a4682103014100d0715801302d900030251041c118aa00e04202035403c00d210044c09140c00c1c0318006031604042103290131594004005500305441d04081102951003461300b00c45d0070010240a02c00115525030f1640030381250f01e0281044d18001400914106001d80120b00141c1001c2d100766507a0b4010040302d06640786030318208886d2440300f01040b03051141c44c01e1612000d140c00031208104050b0071008040d180003c00c4040307102d41150401c01518214081c540007900034000400056025010b404014110503003912040507620301c490303085880136480000412050313103c1174135800312842600c117035214810f20341d82107003017080c0000e081e12000e000f003c50140d80000e80040c4c60b0f010b00b100d0368a81e50700030215051341d03842d10103c0000d80800d480300 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 48934617 1250 48933367 48933427
    0x3020601030b16020a0b0a15080a02091b041a040305100c080a0606080f04020a0b0a03061802040303081b0c01020d06090f0501030201050a12060e0703050601021618020d020f 76
    0x100c0c1c40400000002c4680f0942c590051a9084082d00d40960110b0058541820156191028480114050046001892040b02400d00d01c1c0389401845492400140000e40703200c2d8407204148203100e4001554151254007160414149110980700c0c014491601b02515912589105072941c60f0703950050080521f45507113050140d203901d20040306441c1c4034003d8001050349400020b112400c0303014120f80c81400209051101c1c2d0380c0b01d01446850b44001003030740010b41c42c1d02c0d06000740800e804903c0d2004044100840c03401c1d00d1628000c1c0000c0000c2e0603200d11103141d4901c07141102d40704c005e032131034659a00021542d0703145a100744002020b82d44584034034142445035072000c59031244a1a0304880c3c06848980c58521100300072a240c03031030340c0d0302840080c1d90349802007004c12040b12410701c1480300c4d880024040c140700001a140c000a42004040004280c50a05c014440c17075002e06d2003d0801f000140c2c0360124610303c480a4052011310f61188103021880f05041424818000703030074000e0740c1036 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 48935867 1250 48934617 48934621
    0x20c04091b0b031605030a0605060a09030c0605030402060909040302010e07090b0306010515041503020408010504030806040510030c050409020103090b070203071b29130303050c070503030c2d0a03020601030b 91
    0x1101c0c0b802c0c00300300e90079144181c491100c4094280140000c0d07074003000b1305200080d1f494640001a08641002e03030003500040c16100144100b1142c4446a400b500b42030130464258a070030790010b240c42c450945040e011701c03074880201c0c00f014005d4018001d1800c0f0802640c002c1612941e60300d0052207070702c0310603200348103000001400382400c05010009810403c400da241508182c0280044600100c01c1010190b08000000e95103000303200e84c902481c8640d03030b40c040c03504040c0200401c0e035001410400710040014010400640e40c100840c0440d00151070100345085030f4001a030090102c4140581400002c804010324280d001c4024490340380f142c0a40d80400c400c1c40751a00281d0440d014503001c4054a043c911495903924051845000300030241c107261a0038240e403400c1c0c141c01ca5200310080742e404124904205001e11520300904800c2c0d0046080003582022540d58598028480c8001203508908460700d09008a60081011a0004940c0c0460081c50000d40c0c1d203d0900c000d5540c8500080 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 48937117 1250 48935867 48935879
    0xd080705010f1103071202090303030109090215070b100504150603050709080a05060a0c0203120c1c0213060306150c020f0402090307060f09060306060c0627050102072a0b0703020c04091b 82
    0x82542d40c01c2d80027030001c40c11070b0300702040c1c00010030001009070b0780102c1c11034844d0b0710362200e0b800510301a4803894690442e4100302002c600354080e107400c401d11407400c040e03420900e40c1d90444030700101c544a140100381900d550201356010b0b0105e8009402a0207407220a50a0207000034007a800360460003400c1109104087d4203d89902130407105800c0d5a03103201c04643d00340401400f0b0030800f442c4518a064004646006030201e9100480c240c0324140b40e11001c200c040d825104c1c4c81c005084a40a020105080107801001705110443c02442021409000c81468450b60f0543e2003e040c09022168202c6d02c074003000d0302510780c21600d200090300405021031260b120380503030011101c15490303160b028511035854a02a0500c035104554442c070f030301207441d40340400f8201c440007035005000040c0d413070610341030411074501681e002c006100561030741c0b0044108039499007003c8502c3c20380030070303191a80c503c5d041303051414003504541d0081c01c2c0b407850018083c8100003260ba080c20044a070602940d228 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 48938367 1250 48937117 48937121
    0x150601030e0304030b09100f0905160b0d0e0705060708030406051f050603090f06070e09091b0111031303030905040b04090809010f020f03040f0806010608060d080705010f11030712 79
    0x601e880a81092004000041940001c607801850b03100548001d07032101c07080c020840e0500300702c09590640b82d801c00024440705228841c8159003001902041c1810311600700d4007842030082c0d1aa0f010340d0f500414600070001e0104102400c40145281c1e43da046d0340c24036000c0740d001030380d007510f0551a01c00401d234610700080c0282e000b00d098180f03002c4503600c0c103010000c00d0f4000078500403040c019016503038403410007480594452013031038451540e074a4406c0140030031a04001d01c16030442e0310030b11349564005507140c1c61084034032092030250707400d548120b2020300758010214600039044091b0000320802d908901e07050103449003940c0030081c21400700104004c0d654501d601a02c03907441007102c290709500c1403144d414911043e004481e140451410384a241da40030350300c850140741616800f441aa103080c0201c0b8010705161800724200c0c14072a002400a60641100070220b000000340c01e02000b500303400090804003041c0b01008940c0f003070522910399034404c80c0c0c810000b802500701021070650b14 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 48939617 1250 48938367 48938381
    0xc01090b070b01151b06020406110312010b070206040e070f0e19060305130503030c1902060417130803030411030601060c0b060d24060302090f010608160e030703030215060103 77
    0x102c2c0c40007040ea407070290700309640950500c4040400140303c4401c0202da4418140345811403141a005a80301c0c604a401031907a258245012500c0d08100041a4002d64440c040360640340c68649055031450940b00088080c0701e43d50003051585864420031074000e0f000043d0721400751051311001303800c2880e003007009540d083c080101e48107210459003d01890388640d000307550000075801d41121001564440c14a190021a410868404000b8141c80303031000310107014004100a000030720490030103694200408481c1c1c2c01040c50281c000c1400705140524010103002401010140d80d0b1700d00701401e22018503c0d00b43c0380180284181000003c03520302c0303441d85610180c1c1141248440b81c5480007007041030b0192a00035100044204080d461070029040c000c07100402014002030158698418802c03c1c001c020302c1c4014070b828403001040500d4018001da580038240f4101146504800e440a07a036019081c1a0702d43c152080b48400b0040580001d9070b030780e80e02d5802540c1102c5589940044040d01e0032 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 48940867 1250 48939617 48939623
    0x9020a021902040f060e06040e030c1207020402190224091e030408070b040810020a0c0b04020d05160f0b0403080a0c060f050a06090b0d030e0f0604030b07020c01090b07 74
    0x6440c0315804441401e06092885100400116521a4041424003510312581104907040c1c0c805c014001c41d441c051180100d0103400030051414035025418594540f100302c00d550740c00c1a400640d50b02196201d40c1240e002c540c20300d403180307010021814001e503600019044000040200c0f02c528411068a00d241c920441c3c10100400c608041c0c000440c2981210043d52585c1d448184004216000140071100c00b4040115441e40c843d0b260040013880c1ca900c107854a521140304020814215501c403c0024110790420060804ca440e00e02c0898110110508040c0003805102148040e91015110f000201c81200204d00e840c2612070001c02c00c03d00c40c510000304450b908105d52400140207108000980380681c0303000070700e0103100ca00d0304140c41e01256062303046661040244802203c0d8803030001003102c1a02c0b01c0e0401c050a9801526284e20740e82d04c5407150303921000754241985e035041198050756201d140000107003020a07020313641e04203a6460364040f4034131010100e85070307510394191805990 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 48942117 1250 48940867 48940873
    0x3140a0210050a03060b0c010b10090602060403051c09060f0c0e0a0504270309030210021f0e01020d0e01052203020307150b040e06040c06030b03030315030c12010c020709020a02 78
    0x218081d05940d5940030043d51014907458100005030242000c01600d03060810a0000c00da00f5051000c00c400141030103444403e22450500a100080d0300285407680580d041c24619600d5540e200c1026214001011100840d4146050001041700700c1c0c0094880320504c41c0140078822040a041e18800700440d10203800410100c4208003070326017904800282c0d1080c0010540b20f4649024085a00031031100580129924610410450810010141407065188054a8640c0c8100c0da050311001860110030707481030300e0b0f00f59481c07101070079411903400c00c05400003045006c03140e00701d5030b000c3d040403583c20303000900c200c501c0c0b10300c0785881d202144859496409185000d40d55959031607103142104481c3ca10a5841003406041c0d240ea201e0070f1a0303071940300c0c000c0180e480c00f4901401010344a80056080506080e4414140c0e03c00105480d048400a00703019140360b52140031074900307000c9005840d40011442036451340b01c01c040d4000d5005200a03400c1d69100c1341c40318401c406070f1090303051207001a8 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 48943367 1250 48942117 48942139
    0x80114030c0d020d0f11011403010e0403110c04020d14010b030c0304030305091f09060506060a050d0e10050c070309050603040206040e04030e060c010b27040f0303141003140a02 78
    0x490b14281c0e42d000c09100801c80d0041d5126516540d081c041544000c58000d0750003003d1000e15a0007916000302a50a078030348a24640c1040c0c41020044070140000b01800603600780c90444280034070040404800117041151101841001800035001c1194041c01010701c0e07034004908014207400b10381c4615400c42c0c2003442e540b91682c1c2103004000081c840d500c3e60081c1440948d41c0e10001d070361281325080620000c03c0d41c540606000702107860180500f0301c50001080041a00e94100007500c600c0c02c00181c00064100c00010300b641400d41440c518410f507880d050070842140400c0c00680045800f0f83e0350701001e540c42e8001e01c9007a210030f80b0044d42c40a8103100400400702101001e60780140709207011f5407004100c002045145e044010101c15994644011035001d04004080304424250103122038441110b2030301076000840081c1018100e03840c5410580103150198000b0055803040201d10344035481d2001d854402e0603818002142c0940e80680046840040011880480f81d0000d001072420 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 48944617 1250 48943367 48943369
    0x611030912070602040504020a120c031505011d0a0303030e0d0e06041a070b0702010203180703080307141b060103020103050a020c0c010f0c0501020705070f08060403051c060e0a0606080114030c 85
    0x50b0b00001c0c4201d83d81da0f020030000ca601e4072603001406074050301d071322650941c1001c3c2e0b11800c2642e281450300401c00d4644071869040d500072130003032400c44a082c20b01004801c054015211040200040740d074100a0341c0500208055042d030240052210b104261140100c00e500201c1c0c55400a01009910010a020a00425003d20500b0120b0503454000d52320b002c40e10755a00309440b100311210b00140c1d6011003042610700c01e1401d2249280e003400c02502c1d00e6811b5654500b0b4900010b01150b04110919034100c00d400528411240d081410200c1ca0a04590750241075035541d0090104034006402c00012070300c810780c1030081d07408005048004e0203814038a000111168189001c005040007201c1182c000481c00038402003c80b41e000300c0140c5901820800c0d01034112400d40d01c00310682e48503004000100c0d9100b0213407101c039403091841d00d0203501650a0080a0481908500e0b2200f5000c010710680d902254400000c035006a181c3c0407880e81c0e2480c3c50a542e04000f40d0803901501f0008005c5a9 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 48945867 1250 48944617 48944653
    0x9050609180f01050406090915020a03060807080604170313030807180306020304050f0d050403030e06070b090c040b01030b012709020304030503150d030c08090301060b03100306110309 81
    0x181040508101c15103a100c5005500c40541501c4024824800000501440c2060b01400b006410b40070401c8c001c0d881c89940f00c0754000c90001c0e84c95030295012510401700b500c80d8100710010115403085840003038650340d03415180d47c0240d8041711422485200700080408080a480c81100241d48410540d1110703103042d47c010f00020501c0b030801c0101c1c955005440805502d10002c1d50103040010380b00e103424600245410fa0900d500d00305540109004424958403000700d41c1944d9040c40d00d0600d25198801043ca10302070300304001c260701e018804001c0e411000242110340300600306c03400d1000349001c0006500712807207010703001c0c00140c443c9114403c0c4825910400448100c0402c081a400d64a04168080740c0007500e040b0000f0704c00000b40311403055118a10001c20b00100c407004124282036074060001100c24200420240c80424100825a0203500880040c0f003075880c240d44c4c2e46810b0a40c1c284080280c003049484c0340c41c000c02d01c480380f4200c0c02943e2140e200080108803409441c000a00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 48947117 1250 48945867 48945877
    0x40903030e01020c07060e030304030b13080403050118110a0f060e01050702030f010b09010b091008130c0f0501020d0201020f0405010809070b0f043201030f02040905010e0406050106050406090506 86
    0xa041d107030104003107001c00910080034090700301006130030418141000100710701003072060f2074403079441031000f4400f143c02e1800b1107420080d9500000030140792031500011a008035440030708194030300441003406000003a0010b031424420301c01c41192071101c0b0200701e21121280602040c201c9440d40501c031440c09080c48000d0329205061160405180d0b6001174034068070411101d025135190805103541c0e0801d10001405420990b8a860910182101241c0b10012580c00d030020003503144040b03001e84048440511800f500540c151035a141c0700c142e14000c0a04134071a00e80144100c222030380610703106101761810000c1c9a000103103014540001180c0d040720240a0602c24001d0700d100041581d03070b84004050414102c49400c2d200c0b440c10607030b111404284411030450081141080030503080484c20402d000c0800d0900080030702440d54140024003850308914401d80c80d0030000f03d040b0412101d407a01c600d124082c148841e81c7c940c8021201401107100e40408a1034007481441640b4000000d40 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 48948367 1250 48947117 48947123
    0x9060d0b06040f060305060c070506010b030c0d090c0b12060a0902070302031909120b060301050c07031b2102030d0c0203040305060f19110c010c02030a200f0105011509050906010e0409 81
    0x401d20907120741782c1509050083e2841c10034034600240270420020300f400102d0040c9001c011040c1140742842440c002441808041e410391550785100c1070400a2520a45014050988029458054030034044450341c8082e2211031165101c1c80c40000d0510300b81c000c58040c41d505502450410146c0c0084400f0546030681071000d101550074042003403c940c0c044000201e001e030403100340b24141802071608503070005e003007040d101c2e10820140d40402e400c4035151403813a00e1404800043c12031410055503190303100c18801d03080c80b101c1c80104100b50740080a0f045188501008000c5042c1d4000c00740d0f030380c1c891840020301030381110000400090301c2e040455441040700d00558030305111b1030708803070840314500c070109050700001c80d103850410030901ca844045040c1d400212300d049905040136004010003816400c0c030712a0b140c01481c0711342007409118080c1401400a1000b5615624460002011101104006a0103400c00911868040c92403801408180c6407044071891090502014081190040d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 48949617 1250 48948367 48948371
    0x609010b010c171b0d030c1806050d0b0424120f0311010b060d0c0e04110f090d0b10061202030402060a030b0d0b1005031b03250801090305040509060d0b06040f 70
    0x2410200101049810520302841c0c0617006106012401a0441e44a020f0319410420b03240144580d24600d0740c400c000303589540c241140c41d507030a050701c90003504901d09036a411a00b01140b55074050031006586440007840349003001c0450b11028800114a100b88003d4089004500d00f44003080c011a16900c03c0061040046901c02019020070801da05c40348041d01c0903641c84c1740385a80c80d60b204506848458040720103004044024803014100d004041c08412407000026074804c50756500440510740c1548000044254a4201c01d4804013403054456900411104080c000d4010090b1003281d01c02d96000b06460b081002c4c5000c00c60082c00c1e1410056040f000c14114940881c01560100d8031954031000901003060420080c542058911465a045440c110003442850390317012030040130304e02d40c0d0aa641040d07a0350403104000c1e02165405400c140d40780c980c9190034194014020011b65000342e0700c4003115100c0c001400007100842c0c0c17026050300d00d01000300d520351400d9001101001c07003071100 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 48950867 1250 48949617 48949627
    0x31e02030910020309070e071b0201030b0102030c011e0b0105041d07110303040501060302011812082a01022703031606110c06040b07020604032010020406110609010b010c17 76
    0x140b0030482e40141e035058040d91043c101000742da106144440d903c40c1507807502210240b040c080c00d40d00c501001c00028145600c41aa04106034805c1081d42c6003c01404000e0044541042d210b9a07041046800d64803903506004241c079481d40180100c0d000c507101070a011030207102c00340654580d5100500030a0410508a04101c1b54580c200065401280103100010702c0a24500c0003501209440522299070030700000c040014113403d403403140b110351304502c0040e580c4a05001e011142601c10b403103900680c5801042d60038507017055019100b28440048020103044014444403400101020310b16072680c41080010700100f140301618444c80d03c544404200401140d06405080c6c22040406d005a03000404110a001c1005e036010342103401e0340050000d606103900c0c0200464111281005c102e41175082e0f56442120130400680a1410761804644481d11010000c201d0f481815400040c2c0c850034010034100030040c0b083e40031045050711225035030039480da900b890110b1400ca03168449641849 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 48952117 1250 48950867 48950893
    0x909020310030c08060702100509120f0d060314060c190c030e1e01030f0603050604080a020a0c0e07020609070e150402090301050a0b0307080105041703090c0315100501031e020309 79
    0x60f00f00d02501800300602007a01d05401c00a103001d48640720030010314201014041080800b14440a40351003000f252665420403c04003016442500c00b179001c80c91400d5000001d000900d440100c40c041480300341d410700d0b100c20105802d03074001e00040c81e2008000c10740810300700e805600e540c252507100341003411120a9040014104040740f0410446841c40d038088403001f0f690510035068003801d0030394200070041c19a16015941d0000400051146a000803000c0c2243c3c0200310000103207601039454805241c8502d080e4200a03404c0c0e4074103006d0b11070305010483c1c40c4c2001c204081500c102002480e51650b81210022508610307448481d0080d500700404040c6803404c0c05003611800e05200d010030454164000c3c1490590164008141649480d00740400688a11585030020154035445504e9031981442c46007032130600310704240c1c14403a080020035058141c102c074500c9191b0b000e440400c40342c0ea402c01175042d1000b44440d00c001c1e207101c4031030708003041d8560302440c3c0108008045460f80c5034521 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 48953367 1250 48952117 48952133
    0x80411040606030c0f1b0201050901110604080d0e0f1203331801030f0807020a0b0c060a0b041404080a02031e0405040507260c090d0606080c010c03090902031003 71
    0x90000c00000751100c10340e40c0c0e005c1d00900c1c40c040e0045d0924154010046000e121000301c882500c00030f04020002402d400030f42e1042000484a45072001515140d0416181c1210550310040e000c00e0107c1c180000d007007140c20007040d0400080a104081d00002c4031500c540790003503100a019031641e02d810700c4c121180a1071607203030031558640f03040c1c00c2e6031108030070080101e180c00d004a05440d01c1d0452006100095017512019083d540c8051010340f54101440000c0156469410101e0001c00101d96501c1e4a040020301600400c0401820041d0303020355424070007500c8480fa148950f00c0e1090340460700060b16031005110414103841500c5c02c01e0106403095007050003400c18001030f0b201c00b01d018081c0c1d140c20701c1002c0d000402c508000300d400039080700c2c844003025412200c5507001c0800d400100000d00c0b5008940c00b000008101094620962034450014400d42c01000550f1007021460030542d4000c0c40c100c072880340c00d40c03109103c803850403903e480030f035000620941c0341400003000080095003070 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 48954617 1250 48953367 48953369
    0x60f090c191d04050c0d0e010902220f02031b07020f03010c020601080105070206060904021002070308160605010902181306030813090c0e150d090f051f020c0c010804110406 76
    0xc0d5807800101c40d40a41060b84040712402194800d80c40c0c0018051008201c400319005108281c0001c03030341c1840000014014028204060b40040b1490024190070701d2100480700f4011520000f04145114000c410080380401c9030300340342001d00e60800418088000014022a46c4010300040345500c007140401e007902c03401c0a01e1783c0540d00c4030300148114142030041640c010050b02c0103042e545051000102d0071078000d013000c1c0c0140080c08030710030f001d03100b40308900256400c14030403540ca40c900342d40c0903640940c200c0103480c40ca18040c0081102e10322802100c03070354001d000d84441c2c1800d135031041000c405070031030100300055603610b80040003a800ca00503000440341000340c002020300e030141c0f41068030607902c120340030030030749000002d0300790b8403c40c07000300024070500313001d4858128a040000a0400807005414101001d00714003c101d0000341c81c2003101144141c00604505c16041c0b035040c0d00810402c1b80e00c2d030b081070f051003d00c2e52141c0c2d281c6070300c2401550060901204a40441d0440b0ba90b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 48955867 1250 48954617 48954667
    0xd15080109050f0d0905011b0507060801060207210305091813060b0d0b0109020a0201021605010c1b080910090b0703030b010912020112051b130914060f090c 69
    0x15500300340c060003001d001c5a0010322050004d001100302c600002890600f1078011281845100000d42070f040e0741c1d000008004030343c010201d40050740c0781c01014007189424440c401c0103100344000443d000b05401040032a400c1d50100f4502045003681e002c0e141d40d04150200c03501b0071482d0240ba206070504013003007805500640e403210303e0304c50207090000a6542c4640102d01484041800000280400108604441024600584a0080e04000c80c0a8411108040d00711b0b02600c40d0901402010350240b007540425844107200a0004103250f0300300c1000c10005400c800081c0101d03a441d007440d00504075040850b26211403810384581e1180400d80240d8030030360009598941c40c442950304842e01d640500001c04c06458604481da0000f000044290074240c2410307152004a07415100745142044134581d807100301c0d5142c42030440c80343c2820309244079070301600f0f052500c0347e9029032450480a0180324080c280c02c00e890350000c144080c070840a4030681c0040000c0200042d806071404400503a104 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 48957117 1250 48955867 48955871
    0x4020d0c030b040c090b31110909010603051009090213020301030305090405090c0d0618080406020d020c0406030c05040b0102070317090103060b0a0203071e02031005070201050901110306060d150801 87
    0xf030500301000d49103113035040850420301d000802101c0e959040d400304840c00419880e081d1b8494681200308140800c41c04c800d000c6401c1041c1e804010380000301a0001036001d440340b425a80c1d85036001c4050341d400359450f014901d60300c103044c4603107800fa0f04060f84080c0054500074614a00c000e4850072a4001d034000d5000800100b103520310742c0b0b044d0080541144848004000649502000031049520584001c0000e0ba0b24085940c920607010311096a40c0d0700a04e10300d48499541c0006525101e403020400014010300100102c0c2e49001d03c981402d40f41c103c6591007410b42418140001032030a00242410b51081c1a0000006102013880c0c89940c0c40b11140b050302d070300e1310000140070ba80954000030072114040c848150140d0340001503e5540c2e811000346205218001c02d217980081c000d64019405004546154400c0d2400b904001c0c005c190300d500070021696100d4075103003281c655002100d5200c0d810000b09940785454005003140007203010340061601340d41031600c284803d16621481e1565 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 48958367 1250 48957117 48957121
    0xd030b010f0801030209190605091501021903020303040f06020d05010308210c070f031e03020301170a020d03030507110312070e0109030c050103051803070302011a032404020d0c030b 80
    0x96401001c400000c40541020a15941968001a04010010b0100101425a410f80c00c25215140c20010003400090b0000d049405c004541025100c090f41c4514003510510140d864400d00d80006014104c5e010ba001e142141c0b0b881d681c5803cae041c2c16010070b071a016000c2c089490102502c1c03003014000d611aa4060340e88049d89410301080c80481080c01403840035450030800391030428002c4907010340d032140440804100e140740c180c426140a00010b001840910110407040b9090740c02507042e81c107600c14a00301075015400040c0d94100915000750000203030001040005d00940266810110324140301c81410a014a89891500008241a5040a4102841a42604500311048010084c60300380350041c216243c031758080c0784174851281010340d108001091131541070420200e410400782542c2e070f1502c0300c0c01c0085c080d1003a11070300000345140300300080342c9103000500c40d400c2d410035070307048000d1a4640d00b2164a0035030040082e60005c80340c40f1880c001442d002d406501440c072464810601e4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 48959617 1250 48958367 48958369
    0x70f02040c0e090702070f090e0307080d02040504050c040302010512071e0c0b010e041205090402090406030b040203070b0a1b0c0f0312030608010605010815011e0210050906010e06060d0e0d030b 85
    0x201c070f02401107015900003101c248a0b51145000100644040c92400306071002c03007000c1e461842c400c002c0c4c007400004000c034140001100381e8005100315401250244803a80301c0310100b012911462000a020030380c10807823040a400030030107441d4008441c1c103110340c58400820752541945030001a04000070344005502c030810541c5d00c51103014182006201500d864242c0da00d460740c4480b0080c00d41400f001146108803961f440c0c0488004050141003441001c3d540e203004041254240c41c1248a8001c4880104000c41d8010a4480c0e1ba8069078802c408008501c4181107000200d042c1071ba07201c41006004920036082420b048020340c4605c20f122154a41441c0080850b2a603800201d92039060070720400c11607a020301d006030800d00c5082160000164000180c0300f180400d4001d01a1b08500700c1c01806564002c03480e43c0301c0904944040c07001e0b50350301039500c0e100c5100740210361120350740c0e1020508608054000c0e2105c5900c490001075203120425903186003543c100c2808000923200c0b01c1103402 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 48960867 1250 48959617 48959629
    0x30209090a05010617040501111305030607020105040c0b0c01020f120106140a091401050c120301060906050405030a060903020a050f1b0409031e140d0c110a03050702010302070f02040c0e 82
    0x10081c840002000300b0350510500501c1d000075080d445028845183c041000d000d03080d40074043d0501c45015441e95180b100c1d2080b5949442407280303034806c0c00380030002030040e8018041c040c41980d000e800030394540e04000030000107030481070340d1307100c00e40d420b2086079030441c0b1480003030164681c103a144041644c504080280f40308000081040c0b000000c1c84a210300304d40005071082650800a0415804060380b40100d07a18000c50078120510320413000c01c80183c002c071600942c141c030125554020b00a031141c0d01500e040c41144145034041d4821100c03800400c1455006219840c420b00c191481c018942c2c503824036010401604030303926003000500d100307052480364030151200d0f015142840704018030b49026041d150320300c84c0d0703820810000f11524881031051400742e21440e1801582ca803101e2420315103030000c0859080781c0c0003203080c60b201d264401000184404840d58140d45562074440107500440283d006041c0456184860090580059960340241441604540e5a66581300d80310010020 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 48962117 1250 48960867 48960871
    0x1090515010906080f07030b06070b0702070b0f04050d08070c03050304050a2408070203090303070506160903020603010b1c05010603050f06090106020706080c0d020f0301060e060306090402010c150c03020909 91
    0x2040c081d100710204183e82d00071000b150311a206600b541c1d41960342900540140140101007030303020300000ba06004205c030290034540240d0303841d030803900c0040e15803444180d41c1c8039842182c401140240301c10022450041d00f402900d522881205050030250f1b034803400400f4a82e0130803585074002140612007400c10f42d40c4e20700245040068888500c40b907140c0541c1724090840c640e01008050b100098109000b00121820b603000901201c1d80d0324994104151101c0b4107071a103241c80c4000d01e10080c0603a00c00c011000640343c0003001c07286140d1070100c10821076407140f1b40b07100700020b1041c0c070714526010134820a0300034501903d000c5903511306602451000c0d9001402d086c46150802e005101c2c0d154001940d0f4142c0700642420b90658030b508902c184a8050350002d4040b080c00021923001c5442140040c50480b000341d241d06c2d240041c034208100250100301c60b800e8022046000060256101c0c000d2146260b000d40074011016007090300113416192488028408640c000890f0380c2c460818440e659 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 48963367 1250 48962117 48962119
    0x40b070506060604061704020f091305010e0c01201204060c050c12030d021b07030c030302150c090d030e0301090305180406180207141c14130501110703020901090515 73
    0x30304d40303803d048001c3d001400c010f8034030110050010016013151500e00354495202d00040403030241d0700c2e00098014101140d860121404d500700038200115a400081010f02c480c0c0584503616003010900d2407401c01d18802090510911401d07003507403020366480c001403002c0d0134141d0725101e201180d42001351504030b00344109405100d80385100704220380d011003a1254010340442c0583c2c1c0390004030111420012010344001d0502828500104000b80c1c02c2c1b860084900c07a0702501c40c0742100141000b1840000c94003144204010864541030f46072041d0050b52a80c401d0030009402e50080000c80d08440d0850000c80205034005440c2d900c034004109008001c80089800348001c0d030501890724050310600c0000740c4291f030003103000b1041080310402d20301020f044100300d03000c07424815042030500d40410710701004640084005000c103030001c01144c40807040c0004d812080703480d00004484c4145642039601769401420004401a42c0b200ba40f14000c02c180880400d15052080e104168020611491 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 48964617 1250 48963367 48963379
    0xa0906050304020d0605090109021f020c0102030a02060112140313091d19080f030f040b0f04020d23030a02010504020a06020d021002030a02120c030414010c17090111040b07050606 79
    0x800181e403504d040c03c0c03210368004001329840d110300c01c807039001d000c0c800d400075031218070040d41c0740c580d04c50101d85c1d00c54007602d5400c95100c44566001a6102e100701036108006170480c034010f203c800d400030b002500326445155804a0840498002801e58001c10200100c119100c1c80803c41f4007101d00501039201c4000d10507449111010300c01955943c008510b18946043d0074140c0400c1c40014415140c401c040310481c11b56903d8000003644c90941c00712011107054404101140005419441c100c4c825039001e40100480103a0351034401c40300c100c05020313010052004d90101c011a2007480604031106083d00045a00c0c05c0038410030511032100d4024400b103611090b81c0d51300d51a800103c40c040700b1030090006a0b6510303030098080180c480e84015245070007090040c0300311030002c0d500542c4114006d000340000903061085003400d0741d404050020003e07100362044500d40402e10310907030b04580200000290400002c0c01400d10b5041580009124030020860005024080c40100d501100494071 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 48965867 1250 48964617 48964621
    0x1719020706020303011d090f070e09010c18030b06040f020a02010914011401051509030d0f2c060c0304030b0103080318120a030c0323010f0506090303071e0f080a09060503 75
    0x351150306440e500c110381c00030501c0e2001c00c0c07da200501c8000303036816844007a22800c82c0ca450b00188030810640c2d103607a8642c43c10440c3c25240d8400c1d0030046010540d00e41d107101300c5296448224540c5000382401d68090b50310554108098490310050040311041d800100d1a800039040a03800030004540c02c03501c1e41d0504c11350441d442e1500718828150b0302c2c00c032450300f0b0315440d07481070040900038940c2994051042d184d2004a580c0c2003040025a19120b0b502da0001d20035000e142c05240590b60000c1c00240a0042c0c44030841c607040028084d1000d00204807810704c2c0d0381380c40e00510340e402039000750303501e440020621810810840c2898144c0300d8a80041140d0340321440302180502c5004882000c0698665404451612a0b000b0302d0004c0300c003030242041d0144081d4502d00c420002c0c80f039611001405000000e40c1e081a40c295a44464010095410024551182e03030800624081e4900550100f41c1d090b03001443c2c1c1d9440c40c070001c3c00fa40749540c40740c400000c09803441d22103802c14024040305100f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 48967117 1250 48965867 48965879
    0x50c011b0206090111120a020c090901150504050c09030a080702010e01051201120f06020309070f090c02030d021317030306091005100309060b060d021c05070c0609171902070602030301 81
    0x108a80881c1c00030b1824810342185200041c0c02c000000406c3c814869000600d880103c1d800a007103030503a80c04031030290300c80c4c0b91074140d07501300c5509039900110400006c8082000349403a5101c00e030301c4180640001d141200c104002400c001c05001d0884c0d0a540200750401036507400003041403191800e0a00924044440075100d0001d041441050104082c4800f0f16040148503608001d5556102d03000755200c1c1000d810540c0c41d440d60b400b031291801c0135040c00081d40d0381c990141210324003140c0c010b58a000030b10060040030b503003d01801031a0030a502000100020000e01c01c082003c2c0b00b00c059510380c20036108020f2161006042280002c0000c8802c3c080350356905444040c0a0b13250070005040c1d2034615010018110b490b18083d80300101260b0424254110740041030303c90704820690124503413000401048400a6944500081804c0705001c005155540000341c038074065030044401100c184100b60303190380303c01119090041400e45540c043c1d501007189034050221800914190342c1040c0d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 48968367 1250 48967117 48967129
    0xa05060405010305060a050606070602071a060105030c0406050c030c03040f0303031a360718090e060103030c1403040f05100e010e040f0b060309030a0207060504180507030216050c011b02 82
    0x80d04011b07175a070b600c0d0702080261792079600b21910940d00403000d40d00c421a508009000c80c41441007410318042480010718070303610800440348103884080c0100e06140c10020f049807140c000304030809441c4010011b20f00c1e5450208080d0004158140c8010501403d52500405541c5941d07035901208030000043e1205a480403040640f1400381c10314540707030300091350f00c00081030030750345081f2090203050040c4054558050505075022031401e00d121040c955500414080b120303840980341d07158101e02c00500019114415548016003d0000c0d01d41c0c5a8080b0300590a56000703501551002031001e0f4100203504043d92003036280f52160901407400514000080d00800c0c04842c006c0c803c07035440c8004401410a0350040301c0d4820040d014a84900d08145200e079280e1010b404000584284ca1001984600c10000c440540d21032203400b2000150f03a02407140030749400b4003003605068092158114580100740f00198140c05a4010400070780d0000c0098210780142c04041c06010080f0100800b40e1150b07 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 48969617 1250 48968367 48968371
    0x1f033306080309130b0d050d2606090907030503030106050d0b010e0f1516050a0201110d0e06070c05030d1e030204031e02040608030705100501060804020904380a0506040501030506 79
    0x5407181d403404d0a900180790018519810501d51010b4640c2c003101c24044000345444040d5403946400020506000204d0004120400750341c0002100340e001468604104181542059031501181d842c2510303540c6003401c40d0400d8006400054000c500319a000d00203005c1c0b03448068081c20031941c144e070010080754a041b03403c910a4050b42d11212042058021003048070b04480400510a550708220300d02192100710f805d009078002001052003080c0c42034003050300d60084109445003180f040d020030911206d074100c80402c0d9469892414002420380b02401001d800a21a658400c000d1004080500c0f00e041c0c40c00c1c1c168109072051000b4000605650b203060f292200e8a9145411110a440090060810754120a4050002041d00c0381080b200041490003c400110700b400300b03071b89a28046034801002c0f01c1c00381d4851503a1021401268a181070645907000d0169088019010b10300344034075134a001c1c0781d50240d0892000c01c0108a90041c85400c0d0042c1c0201e40500c19549181c9511350364040c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 48970867 1250 48969617 48969619
    0x314040e0a0b031002040b0d0b03030301051f050d1e06091e02070f051603060c08060603070806030705150403030207090902180a090b0103080301050f0103050f1f033306080309 77
    0x10302e000521503a50208403620004032501c074159912501c030b000015047e0081c14800c1c1140d42881d2446e070540c9000300a6034181d03000688000501411301460400e50a0900050710034030104210074401c5185074029610300210700682007140f03916070031507881124050f42c001c4e00540c0c6020f854440c4916091100c1c49000b03011840541c80f03140c1c034105010340c00c82e0754000910a11035231050000c954480450b280c1168020001040180c502d901c0a480a43c800c03034103103600800800001e160507000300e6005410020207012164216200c20100301c0031603668040b00780ac1070740401e042040642c10006140a07114412041c0b020000550104000001c1d0010700900108690001200c03ca116400312900c0c0c1c0d08403040c0141541c1d03a00b07011985503c280901c501036800083c281000e54000e0040c0360203045440b00b0031802c0d60780e0b440411400d4101400c40c243c00000e8410000c0070459140a02640c0c104190501594801182208681001c6400602809806d11008018004010050b81c4d44150 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 48972117 1250 48970867 48970871
    0xb0f031c0f02121603200c01120212040b09010606020114010e07050f0d150914010902030603030c031c0b030a15020a050c0d0804050d051c02180a0e040314040e0a 71
    0x100e0050300b607007030160321051070892440200700607200e00d040c6240d811141e07001e501c945440505202c54035a001080741e002144640c003466900e58036500c81c4540209100e030030b00006051500d030038041e5003118030540303040c1c90840b500c2c4c00b0b202e0110720038404d280c02029240001c00100d003141c01522119001403091001703036807810f40010882d60082080316038032900c5c9130301e4654840c7c80e00c06420040c1084005120460040340d8003003207141e110f100703036520802090005049a031908821501a500c000c00454041c04184008000084100040c0c450500200c0d0074030807181030030144c10102c0b0205200c0c2407280c4e01010348030010800440c40909041c001034009030b0f45060000055a50344244022480c142c1710300d40d900031351944d03c100100e004da4494003d03180c1d2808210b404803001e01401d8521440101614460141c4101aa005024090b010090048124080c10004040141a078080c2c0c0c0491030100802c4105544103912843d0004000540e1b41014108142d014130800e0040017006159 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 48973367 1250 48972117 48972137
    0xb1303060f06240e040510030b042913020f01020c03010903030501080d05040b03150a030f05010203070807050a12051308070c080106060507110409140714090c0403050a0f03030216060b0f031c 84
    0x5280d11480402231a0845900412403c0c24940100c0c06425609180d4a0076940e07105940781c0e01c1e5101281d4060554000b840e00030000c3d80d020011583d80066942d415881411803a1000792028010440c8203802a140054690b143c0740c2d445040c108864095420440104400d0211254075010303a13811a404071035071480c2050640c08141c5416041d0070140800e1810b05d07544c402c11505400561081207260b6440c0e0301501c80c11010f0b120b900602c004900031400c01694aa03a00584d81e0205600c040300f0f1640106401503511031003500d900221013a039039084d003640140308040003405490000c200c24070340207181855680b10710003405802e280c0c0a10590b11741e507040702070100610604820515a506030b41003d5940d0300590b00c080400c0c0036142c000d0300b0010000f440c103001d40e0309403012030b60010701900f201112035960301903c00f81d0321412421302d40e00b0b00c03001c4644041d02401010f41445110b0000e00304c8900b50800c1003103818400c010740b0a60040c81310424050142211031256619814460018 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 48974617 1250 48973367 48973381
    0x102031608090d06020a0f09030201020607110102120106032f0405040b0402071202030a030e0a051e03130b03040308060d1101051e131406040803040b1303060f06240e0405 75
    0xa071080c00c140750b0b4040049070f441020300c122980284000040c540343e041201059050991300e25045200183c00340e006140000c010501070500c01640903608400107161403d02104c1c8010a0000c5e00305800007aa030f5010080d080c03403e89440940768030000c0c0142840c11003209100d119119038080c5a000715142ca14101d05900d85806513032455a100c10b09800380c1c038110714000e541e80c100d140d01d000000d081194001c503581c0046009011160000c002d000c610078200d080c4407120364010340d9405a4402042140641c510400c4404080e0052000469490405080041900b40091700b07091217244404103100010745044503840054500f800c0c06a145c1d40401c0b032159140015001a1508110000d02854140d00f009100d1007034079100c4040c0b110074416142881860302403401034860683c800c00080c0013082c440405020b5134001d091a01c024a80c4036a81c02041e94050190346110689410040c0400d00e0003900a120a590f20154041c0303070222100d0060190b2030340140b06001d55521000704106e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 48975867 1250 48974617 48974633
    0xd030b010e060d0504020f04020c0a020d0c080d02010e070b03070e19050d0606050310020c03030a0902060d0e0c0109210803040606120506070206060105031e1008190c120201020316 79
    0x201078010500c507292644046001d02415089030200d00c070303c0003480b065800d403410b48240e6404207040b0000380003480d82079003807000e03d0100300303810342d402034140b040081c41000030040846038403141e81c00442c1c1d4481010401d4a00401500846c0340a1000c0c010400d10580c00140c150320b080e4121f41c000c50715150f000c02404480103d030485038014000584074400d0260311740065044074410350440d4541c00240b04c95108034000d0680600060308100302040324400340f60400724001d40020f10303513803606130100714040c2120078480581240d40c101d40006e0b0314960700f00c40315500510300403030307064400c15400c10030200d40861107400400801d00132010805224540c4d010307102800f038040d042840c1c204103090032540e603181251144018454000050815480f4005490043c00710940c80c1c064228080c2d1011202031000700040d403a2780c4405000984104100310544411780e10800400700c2520500340ac1d1301c00c07001c0341c0040500d07040c2c00c01c6600050768000102d5880d18500c0001110030b03003a81c0350100e1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 48977117 1250 48975867 48975887
    0x605070320010f06060207050f01050301030b04110402070c05090f09030307120603060e030903070f03021509120706030b0307080303011419120b0618040209010e1302270f090d030b01 80
    0x256290842c03c4580c5503440d4000b105070344140d000c40341d10980d5002044800d8006100850006030148010000540d205a81a0704140708540041d208003546010804a800c20780b019110a010245c1c10801800e2106d442d0750060004c280c14403461900c165000d03502d220140600d004c000040c1c041c44040b42c105c1d8054000303036601c1942031055002803800d50ba9650800c6182501ca409000400240c070b1092016140c22280c3c041c0c45030107c400d80014247c051b0300f000e2151030f08061100c5241643ea43c06122f41000703040c90740c40001d0b000c1441c10605140c40c0d00360300803940340d9000700014090301e25a00340400f021001202e1300a41001042c1d80c00310010030581c4141074a083c942c1058040258031204240b04800a4881440f5450070f082801d1010a042c0c038060340201413140107001400c8900301c261f0f0f21511496541c03014400c19401706100d59400c0c0c428100610034071040c01d0300c243c522541c1d00d8001c840a140350b4880d0800c0d44005031201c500000310020315940340c80d17455250340100e16400d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 48978367 1250 48977117 48977177
    0x6041b0b040e010608091614012106080615031e030906030a020409150605160204020903100b0f0a151b0b13060c050408030f090a090612110a06050703 66
    0x190729160b5609002d410441d003800350702c0104402100142696100141c1480f0102c1f140940110b45071401c5103c0c0030300d0010342c800c1070420044954402c900b070108540803000703403040c010015400349045051400c001d0003501d8646400601d001001665500203aa03008004034502c80078560820035118a00e9403041b01121500b01c200801002620095a4058011505a010140300745c800c0c01c00c05204a0601c0c1c040c80700072403414000720101104100c090b00f81c01d03102034001454100594002171904c0e10403070060030019100c0702440c415044c10070640e440c0c0101602d0f1500300908050152904104038040c2c80100654400c20143c602d030b090000e00021a0015a100824100051400510700c10904241c8065041c502054840f5100e00102e800301d40411001d5400d14200b9a001000d81d4021580c9590202040b0000301c1d06024510502c6c0040076180741200b6503011030f2901c4500065009021441030329044c104003c15a000300c11914013a50520b4000e0a80242d01c02420141004040c01 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 48979617 1250 48978367 48978389
    0x60f04150305190c0e010b0304060c210902040b0402041a0a05071a0f0609070e0d030201060b130302130501030b0c09060c07031101120506100f11030304030309021005090306041b 78
    0x3103074a5441c40d8014240c0745005411140c5445c1d12003a201d08045428800c080d2864020000180842d03269440f040171103020303140c0010703500d000313060003051303904140794040b02c0d10b54825800045150911400809070fa00b540c05508007460104003180b14114444c0006000b040001d0081c1c100e07124030219405964400c1e2442080700e4585003280310000304a42090ba40c3c0061030205000d4580400300910a80d02540c802950307014241c1880540001c1c102c1c21010340d034881a0101303940c4090f802034940c41c1080c404100c0d55900d50700400401c10b00e451100400b0a18010051010404100d0190340c45008514140d50b81c40c0000040340d45840b40d606001140c0c00f801d4001f000704020078002c0302181d0001da0b1040190110003040310211001a149260721a8414440c1510b0138040c90004184c80700e9401c2c650a28103084d14583d04613441140e0843c00240d0343c4075258114a84911210039503006490414105449400071035030f03910000c0e102a201d075902c4c402008150307492419102c05007075540300d0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 48980867 1250 48979617 48979633
    0x912030901060302040b01030b0a05010e01110604050309090721050411030a0309090f0606021903030e03040e0108010c0f051b0c060a021f0b0a09200a0216050405060f04150305 77
    0x103a0700030105808101c0c842d0341410540700c03d41d032203405848012503000741a1840245880010340e803040000e1245c5c0d0601664208030f071060507060041034402c5010b40c014641e44d015000c2080442080200000140420380a44241c0d00d421545e02e480f0310285203c00213a43d856600707102401802c241441507061040e184003908042e40300c82c0c1d08040310701d80f140071302c02900c1c1c0401d081d090312418056203006a101d4001c003275000018000d02c101c1c681c080c2c00e00042461100c0c1003541140c2c407a402c00d080307644800c0010001c0316001d100340468108180391a200d484881d4200401d80e02c0b906603d02504450842111099001802424a8004014003160ba01d07622610060f4940c0100708010303800680440080f035259615010341101c030600142030b48512400d25202100a04ea0041d00c00a00d028400c1da20812580b040d00601031241a40c0040c1080c2030140c24101104e035940d0042070240717042c8400c4c040d4a07210503044001d0a141120045515010380a0300c014441e4aa0b1000d010b074410402 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 48982117 1250 48980867 48980881
    0x60a0f0603120c020906220504020f0604060c0b0901021e09030f010507030b041401050117150301140612070b040b1b010606110f0607020307030302070201021606030606020f0c0a030b091203 83
    0x340c5954581309441c0000c05a603100308000c491402008414442402e055070a1032500042e07100f9035001c1c1c1b00811b649215a004404038903207030016044540414034600004040c006007d0009600c011104025842c020022031950f400e50809400031201e40d40102d004501680e00707020620b007a1440400030031207841c1c5400c00030081c2000041c064041e0b45000c3c039150b11107003848030583c1a40ca041e128030a4000c060110504000ca0040900d00606820842c01d85550f600703008078103c0121300d00300300949050403c01c0044400e41034803600c089a00600b0100842ea410b981900d04440d8160009510b40104c3c0b01d5066038041480d4002803c6d5280000200d42181c00800d41c05600c00124100d503a901040800c080c1d4500080c1e44031000340e8000e2004e200040e200390000c1105a10610680303000440a90000d87e0380e030215043780b004207488203030500110b80e040113800480f0401304000c041120140001c1080381c40c030713400054002e5480e14009078040c8410880a000c0d143d900101c1d0327990703142c030759 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 48983367 1250 48982117 48982127
    0x50d0908090301330e010b03070c0506070807030b04050402011d010201091703100501090f0b09060403080c1e070302060909150d05010b13020301030206120a0605100c11060c060a0f060312 82
    0x3002040c0710000450003100d8201c5030082a04c05c4003911110590802d86a81d41c0c6802c0240784408001c4d21040c03160014000b81b200071301800107a00c5130001800d10f031802400390380481d10300c5d0340114600010400542e0340880040b500200d000000c000c180c0c052070040f8054400c041014114480b2450904251250b020003188500b1079081c1004e01140c41340011107030060300388034902c5a509032420030711091904000408411100400082c44c00c1e82d130b59030720850754014481950050300b01034034500619984040746944040804c2c05031a905055038000740c0c0718016a00541d00070540c400001d200020300400c0400c0e400c60041c031a000b08001c51400502900c0405075081c042d2012800500000449d4000c0c1d905032a401480c16040516140481e1400c0d0001481d0728201610746400081584558074811104640c81d550411070a50609203490801c94034454540551070070486ea1422840108540e03411001d52040800e06d54545040000500280d410242c80010041452a5400e8102c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 48984617 1250 48983367 48983411
    0x305180a050a0b06010201020f030f1504111305060a090603020310120c030c0602070e040f26070606050907080403110f060c04180b0105041217030103060207030212070201050d0908090301 82
    0x40c1610f001d5503442c80c00482c00d0780030b1000c26009070390b41440070404400034081c1c0f00d075118400103010912003030000c0c0083c00380c80010380e1070080a94001a1810079590014180010304810358002d172824200c2c000c018100c49880c4246410980d0200204154802c1d546003107008204e442d854207040c0070981452920440c5912003100d02452401d0001016800400d0308021a444e11090169075074440e200c0e400ca44004501c2100c0344c0c1c0380b4000090b81d034041402890049160a81c4068031445a03244c16000c41e46c55030041441448148100110300e680050f0180d4800d503d4640301c0c1102c0d03400012640307090400303080d0135094021242002604181c40000d0000c481240800c801c61b12140e0b02c1e160202e40c42d03070300b4550000d101004140b100b0540c6a56840b940d030311401c0d43c0300030070010b14500c40c1c86400c2030b00304075502500042d10200341541040b10580b503104051718689804915800a05244034084c0d1142141e61500ba95005008250058030303010300000d0300074081480030303942501e149641 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 48985867 1250 48984617 48984623
    0x206190504050117090a1217071107080102130603020c0313030f02100f020c0103020a18080102130506041409040f05030304050105060a0b0f070b06030109020d08070201030c1409010305180a050a 85
    0x101e0642c0000e403070090b1406001752050b00180a25810b0f42d01c402142081c011540e00c28440360804841341c0b0b40c040c144943c420803d03551950b000c094010001340c100000740d806040140e0050040700e01700c018510480d411140c10b820010303501d640181449045003e0240f04d40d5000100c44000020f00c00c007001d482d64254404c443c100300d18042c0110a0b512540c1c0000040b005034001180412503500982c01031017060510700300713150101551040c0300100c0504d0b0700440d4a5940104020300c000d140140f404000c0c04088450504040c204400c200c201b0075004083c511a1400101107004c0c000c21840b410009074001c03042e60b80e82e2403c0d05203540a4841611654002c902102d4005444c0054509076510402c81078160340c0384c1441a2501e1040da80c01400c000c0d0706550720000140181d03100c03000c4001c4584569009a00d41e000740c0000f40441d081c880f04036047c17126403c054540c2d0b107060700c04c8500d015424240054591121182590802901d5514040314454100d1070414414001610961144 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 48987117 1250 48985867 48985877
    0x927060a0f020304030c020d150c091503050702031617180915030309040e0c091f0902040f09021305060f040e06030c090105010c030e041a010305070309051902061905040501 76
    0x40c1c9851601240300848015000448400c0c502e00145050000c200303005009012a007861341d4404842c10480720490102008192821810045240c1c05891644074803c3d40c20200290701d01101c1c080e40302c0c07003803040301c000c2d00e83c070000d2180800440300c08061400038810074040e10b0b002a1404000c50a40c1d01525904c5070410301c0000e0f184105200c250386078000081e001c0c6040612080c18000039018581c0c0100141c00f0744140400542c40351800d45104110500302c00d1112480c05030412103901545c1c01c02d0401500400007400200049040c500072070340b80c0e1800598510920301e0840b010f10700c50304141e5108500003244c503040d8080e0b01c00780042c0d8038507040f81011512404205540c1d205030950305600908107030010001c0350b000c0c0d400000e4180c02818000b002e5001030b400101125520214038800d03000102601001d0b50b403610400e0ba2111050804002c04c2400e40c40d2203a844440c9000318107142007044002003103403a0181561114514007000c252500c03000d01019041d5000b0f8000e50f40007031 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 48988367 1250 48987117 48987131
    0x90b0d050a0f05190e03190302120708040305040b0708090904060225020a03062a0906080106080f01090b06250203120403080301030602070206070503030f010512010e06060927060a 79
    0x1940522035540111401c004404403940e00004c140f02401c521010350300640000c0c41001c0c60020011240c00c007000c80ca40d0010fa980d0304949807011a440d01134162000c102c031440400c00002e81013403c45040d9a00c0c041c990b034488410b45407000043c8500e010f443e0300446002c00b40020030a03d5000340800c03608400091030780d0803122a00010343ca100c030001a510083c804400c2000c1b50050b401000241d071500491955103442810001e403a400480c900c00025100c0a0b0170401c2a620140090151600c0d151003440790030544044101c021040c090410b01d01c0c0c0d40c015881081d42c617842103e1050a03a55803d0100d44603421700f0802140617080203900902841c401d01300100d00000c12101170302d60000805045034290b48481c03000750043c0e1022a0000c0c0100540404a401000514494507210035402c1c007540c100807d1211052500f0201c0701d13583c0c10880001600070380480d445078004800d443c0010940d940740324004010b9480e4614a41d002e1a6006004e42c507900410054030469030420107101c0300e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 48989617 1250 48988367 48988391
    0xf07050a061103090f0301060e0106090302040c050a050a0e1f110c060a05040e040c030213020a090905060d03081510050301060207060c0209151201020a0f020f0c09010b0307090b0d050a 81
    0x30880c2c0e030440c81c045410130400c807585890300c3e204111940c50007500010315a0380b203070000040e180007a0061004280e104508100b185440c1c000e40481068a1a082d820030340e18010140040c001d43c0c181d5001e11440714040f240d541c0b110110188441c9100c040c202c1070480d03004d00500005140c01001c0043d004029440440d400e00600300d41030341d600b9030b4445103003515020094118190282c0229100407061200101507070707071700c140450b00aa14440044e034079080c2da040075100041c242e000b001480c4c01c0c0000c001041d41c0380c1202c00400c64041c10b0214565413144440410892401125548824501640e081c2d080c3e00c06c005d103040e24829021907940941300c880c280d82c0d1201c6d01c440254069416000200315003a0031910154006001e88140c55500688003000c2c2aa000511a1030014440c600a0285280d0412000071249551005044003122200c003144852805000d1244d4850000000c40c690900c15a80100200340c1d44500315101d00c411312510015202c152045101c46081055504034 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 48990867 1250 48989617 48989627
    0x20409052401080a05060621010f0c021b0a140105090607050102031e0402060d021b070e09070b070b0c03070c080c010501030210021b0f0312031f0807080c09060f030f07050a06 77
    0x4a405c600102071035580c4004100034120721500c180d88203180f07a960590850f80c240118038182c2c81d5008045040c0c501d821000340380c0000141044800341d009240f40c02152142d031903000955040072507494025111200594070b91003035200701c0e80c01080000360308050010643c042c40c01140a0507140c042c00c605407a090540304000da82c0654401e40030410304084129a6004080c461080501c0703400f1100281081810154070340d0001c5e6130300d1545e0081202a28041c8070200242055800450400145850f02c1c0b008820081201201000c00070214034900e009241d4040144da000d00c0702e5a5620010080740e010340000e00c8124020540ca50064100600100d40c05444000004c8072580c2c0c401420200070429a00e600d1094042c01510380c1c0e164004042c82c0190321810380034801e01c04646410070201c0d0088181d0b44100055000158213000f00361000c100c101c40100219400c88042d160280020202400400400d515104041c20190002c2001c074564003141c5045503541c80440e0342e1300060354 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 48992117 1250 48990867 48990883
    0x306011a0703090503030714070515070602090f12010e010b0405040b06010e0a05130209030d0c081801030f050a0e0d02010608070e10080d081501140702090402040905240108 76
    0x12565504002203414060385101600026000e480c211080503030b100c000c281103a1040c58181c0ea4812201c107c414410300c20010100240310a41c5c0a2030418480111200c2d940200c0100821107500020020a16542c035541e642c00c0b52b100601480c004c8407200c04081c001c013555a030040482d400c0662010052a0900c9254402c58103c10103c8096071408c0044803078407400d80c2641d84c07200304107102081c41c0e1104ca03040100d084c620403006a0f1480c81800301403501144405640030000e0120500c0c0010700f80700103941e13003041010301c016225585c900058004d01a455280c0d690710349000b0800106507065005020840e030300c40240c5444901d4100d049080c0c400038014590769520290040012046020117a81d02100c00b00c241c4000b41d4803082e010782082c035490a440700181c0f0300c2d81400485c50300c0846540b0854000d081c04217951030210300c001d4040c0110702001e0712591354540040c081d9191a0031070021180c1c40010707038440d24030490746842690121070a0780c1c2c0b41801c44c1c001294007200010180 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 48993367 1250 48992117 48992129
    0x206010605070209090f1903031802150c010b10050702010314060a12060905060406060315020309060a0902030f07032a03020303090607052517060f010b0c010209030703140c030601 79
    0x41c50201c031a0240131150034050310138400e81c800c4c075012018180b81404082c0119a0402031003000400305e04006040d17902c00a02e80d00082180b03000c0030700603500c0310150007176401c00d00240c070b4071280702100071401411410103003a04607a101d144030140c90f6000c0c0c010800c6034801d0301d040001010b280501c518640e0308031103060308200104000c1c08401c00d05141801003a21802001c0b9a0042070f698043c02d00384291400c58429895403400c0c41048061680101e0340c240c002011400c0d072800108455680f480903060b1008142e5820160040d07450902481402d1080d000031620026540d19112600070181e5a401aa42c90100c25100f10440280041c0c000c03290020300450a010400e0100a802d0f0300c401d40484003489003164422042110401241d14140300c40000c52040386800b0344407516641c0b24815a041780c0114081149070b03146070107803038151590501c03c641c850301a8000140284039030b40001e42c3c144034a10740041003007007944c4e4130040c048200061320700a901201c18955140001e00a034 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 48994617 1250 48993367 48993377
    0x30c081005070507030c020f03010207080f040918050a0f0c0302030d0e0306010603020c0a0803060f0a080604060b010e0306070c03022d0717060705090a030b01120b1807030221030a02150702060106 86
    0x413000351401041d00408d03504010001481c0400c940d448039415844804419410800401c0c1009a00880e00c2121101604100c1030b40480b030840c0d58041c0c40c5d446006009040e064254411424402043ca00c20302455003d0101c1d040c3c400e000c603003e84030301c907003011440c8240709110022551034840d009030740840316281700628604841d5030f0f440c0e400303410050203140c0013824080c968095980c3c407441107000b012032401911241c02c0c14203207103058955800d0180c4c1840f491141c20001502d001950603440350b031038a85420180700b1460308904015001100c600c0d5540c000ea14407a0710301c00a00f064500c9a1344c10b0490f520203a98000100e801214201c00c0c21180d00700314001080980103000401c0c1103c2c00411600d00740703869545051460100b81c210480001010640c3c104010641001980004c038524044289030b400144595403000c01303000090044e142410051000648424105c1e400c640300000e69407580c4602c00000d40c0d52200f441800d8901c903925011038912800480c100b0b05175492030ba070f4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 48995867 1250 48994617 48994637
    0x5160f05090f03070609060201051e040605040f0c0603060501090905010f0e100306051014030a15020913091101020d0302040f060f050c15061201050c03041b030c08100507050703 78
    0x640d0300d6008008400e800c44014480000c0a6906001002c064900c6840346c2d44000c1c18240000e0071100e00030840d01410800c00350711220300c480519802d90144d400f100124869a99280c1700200b0850138a0082a0720b000400101c1d001e609904400f003a90fa0070f90f16036009136918140c1078191402885407040c7c802908505005048903030031081d41c8003034081401101c241c1c0d40c0d6200d0003101d2003110680c20030810724005020003414032440000048084000344010036054946d0a6080126070b8031841803580024500e0301515010448404000500c0080012140034104103803501c42401c0000c0c01402450f05103801b1034041e01c26101a84d4100d0000c071034980c2000b8040d54050500348204040c090705022213031050f00c1c00c00005804078507a210241c0c040c2448020701010700780850040f160740c1d04100c00c005d41c04030349a080d268002d0b0410303180310304240e5890f040d41102d0890340014041010780f00000c0380c005000a0244001e45260f00d04100c1c5940d112000c44450103980c0c2c004002810610b4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 48997117 1250 48995867 48995897
    0x717031501140d0c02070e0c0a030606030c12051009050f0615040e010b0a0c060c120c022a0a03080a08070f0c030804021002030f07030e0307050301050103080d1e1109040516 76
    0x88402804c9400b80103d130b42040d22111091026841140c84d50f03c1c00c0d40c0000c05078082c1d0340c1400740c0002170105040921030340350b03e0b000280006450914140c0d07565aa680041c080034080c001c490010000b8680400aa061840d52118058022940c0c58040c003114185885000c18410403582101c0000c0450200d903403c104100050f07621801c3d038142000140c0903000046200c510500d41e00007901d4840030146100350700d1b40c00580e820b00715440255001821401d040260500c1d906842000042c00d1050b12100d61300040d0040c0c402c6d40002d0903541002c240d070b65103075401141450143c0c00903200d0705001d154031242203c0038404280c3c0200000d100c44041401130810031140441da01090060747d04040f600c0308168465001a4026000070381a61804095030900384510005404294028402036045403100f0486108000050010542e1121a8000c41700f284031409152802a541844612807801031044590052100d441c4940e02e0540490400400c92200410a1207141c448081c078242c940 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 48998367 1250 48997117 48997121
    0x2030d0318080408010912051806220605030106090906050f0f01031407020a06050c03151302040e01060306140307181d0a0c0e1602030d050c0717031501140d 69
    0xd10900c0358040321207150001034080000c0c0002d007038840c00014030440c0c142068800225180001001d2000030040c80c10030003260b8030220405841a02c545540305500912543d641c2e14101035201031808007400030544070b90060085048584a6403510902a19212402d00b201d03c10b00c00c055100104528811481c100520b1207800300205040029113070300490301c080d0740507004036801c80c01078000c08024000c020b9203115058100140c00d484504601c1e101462107040700c0011200c81c0720707011a62101048001940484020b410001c0300710800b565079010180180906014041e9080700000e001c100c2d5080004901e0101c81c410992210f0354003d1600072801407828031400590080720011030114400100180d0300c4891244080ca0245860000203020030300f8060500b40500e11040c48803219154004180d80c48264070080001d00380e100e9603590350040c81a00388c010f000080101c02ca02c40b2400d80b8014600c104404007074007488880c10001102d007801007034000ca8800409020817400d2014030b07 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 48999617 1250 48998367 48998381
    0x7031505130e070b0a0f051201120f05030d0204052e1101020c071206050105011704061a030a12260c0306030c060d020901090609030b071101020f0705070f1202030d03 73
    0x14a00010b541c02c0c40c0300803906040c400d801001e00c05000150544480d94040804100c030b144a01e062401c04030b41c03180d00300c100481842a118a44200c246c60b00503c49805400600c16a00c070302101d65907070100c10584c000e9009031041c1403245804000c546040281d1022040ba81000110301801d01500544240c0c3c16000340c1100d41742a40d42031000c3d1800200030440e42015086d880e00303419100d8214076040080d1201600094108003404501030398080c0b8890556401c25030015000c038000c461444201284000c01c11480c1e8103209103080314050040c155400704442020356503010840c10314007201d04506c0e011070b01520070389100400040300007030514099034000d60002c050300d0701d0751403600c00204140c0100360310b50541075001444030103960300949100001c2c40d00f400c0003400319146031500c0c3d9411100038402020b0040003450400300d41020760449032810148280503403180b105040c880e654014038014402c1c4103800340000710b211004e201700c2c6540c480c0e004004203004074058104802404031303 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 49000867 1250 48999617 48999649
    0xd050a0215071b050c15090108010b090102030d23180c13060306090b090609010902090a05040609050601260106080703140313032d0201021c0e0a0b0405030607031505 73
    0x3e4015680201241c1120064110340143e0041001403204000c00036100003280b0a00320014040040c03803220b90300079420904580c001c5207001d40f130f440400b0041c2e0461182011030b12800c3c1c40c12000541030020700328144d01270900c2d2082c1a596a48541503c0c2d101c01200501182c1c0d0761000c0e010448914000780c0310030002040c4900071a00790f40c0e03961008144c41011500b11400f20101c810030040050400906034002c01500080c0118030b2140c001c1180320034003400f8868a80e1300d036800982800080c3c1c1001003900d9203d402c4600030b603950620023021084076241c0c2c00d0716192818004000c0780c0305004060036984400c010300740084c6036554801d0085071520701c0d02c065000511505040801983c140c000440c014441c03d500c070381c0f50075150034001c845680342200c0002d003060210050323680001c0e4051701c208030340c9100e060707105000000d0356101d07501d03501d00340c7c04a56500d010411010b008040d00469200350308a410b181c07a4081d0560a4464002c0d0f004400d81c03e010b0300301300a240c911042e2001100c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 49002117 1250 49000867 49000877
    0x1501020304030b0108010b49020a03060e070e1006050a0909050406140703051b090a0512010c020111070b0c0f0405060a0207140a05030303011502010212040b0103050d050a021507 78
    0x542c0b5543d0800d4500241d0040c201740c1d644070980080c41c2800300780c02c2040020340340c0032502078481c00c5408680c1c03030740268620440e818041d642d0749501094900401c94540052005814035580d141000150400ca02c1c210020f000c3d00c400000c4103150f0766441170251907116030307905006051884c121446d030464403814041041103200010708940c03a20441d0b002c3ca014000100300e03041c05241288040390050504400c0516003010030100d01c1c0c54a162452291b00d20242690301c11025000882c0d410312500925408542190440d20400f0150700522000703a503130b0001d200949403403441c08480d024844029010200c8c0c0c0c40001d82428459008102c50032549941030f04081e103640100e202e607080b00d0030300300150707008050500134481e03912203600305440f044520807002d904200c01f1a0300c90106100e0764101c55803503400c010781c06000b9015034150040c6154090840c0c64207040070b5811540a03c010380c2c0c10302aa403607201050b0310500840c0d034225042c1c1c00424440421444801444130001d02400400c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 49003367 1250 49002117 49002119
    0xb0402090a0b030108070f06120e010618090b07091503090215030c0c060105100905010302030a0f02071b060305070c03110a050105091509160303260a020414030106030b1501020304 79
    0x155403400c041020302a00c6682c80c2c0c0700c0d0305041c020742ca40410f40d000075205088001c000c01c03005500c100b00315100001c5000100d1408100000c1c6030240c02c185d04024440e52500d1001c8500006941c0009100c0d8040c503900142a1240a02a156001c0d9400b8000c0d100818203910f4440303501a0700001a401c0c4042c004012600c8203401c8400203800903078104000800014400f00c403800100940e501429040758049a642160100606401200c0c40b41034180340d000710009179524165845039100300001542555074842d00c1c640403506902101801d030403c0d05002002c03c5041c840e02c81c2c0c0b03106502036110031800c3c0003203403016518990b0141e00c170302c90340c411070b000840000c400b030241d1801071210000408985005c603441251250f4002c1000d00d855100200b03040043c80307250040b101310303901402c000380c0d402c00841141030424407205090610103288414070581416640c02001100c041c00000e494518000b010907080e40c00e648000381c041c1c2030f50380100c0ca107240c1c3d000806901e412b050040b01e10385 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 49004617 1250 49003367 49003369
    0x4020f0d1502070f150c0813050106050a0308040609082a03010b1009060311030c03011e03050a0f06050f0412030b01030e061006020705120d0302091210090204061a030a0b040209 78
    0x40c3c0c0c0140000c07100c40c0c041c880a070b41049040b24a0700030034034102e20140000c01c0404002031101400a110000301c88a42c5141c80c1800020348c400000340001510034003140351039007412a80381c0e10910420b400516405000180c02d8404111010b10003110b0013410502c40c2c0c0b4100300d07141c01c80350140140e8107541c0d4240c0002d843c0e9030000341c20b01d00c4406445103012a46410310181c1103622144181248500400c00c010404240c14103e9040d0707400c01d96940508801001d880f580d400042d00003c2c1a8030924442c5414400515416910f4a07c5240c0501040c0d45210802c00e2022060342c00405000b480751007004030a000b40c010345c0070310f030041c50002a9034140200c000e25003c026140e11030300c00344c09502400300304e40c1804150043c040648d0701005034103180041e103548404103d204001c0540c04950416035984905070380c061014800c040702c00140d01c0c1980760f001805d000c141203100742e160a800048124100d103524812003449640c079400d46d510070310800040c017062107070f80343c0c02682000101c1e21 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 49005867 1250 49004617 49004621
    0x3060607020a051e0f03010e1c0908030a02070f05040b03030d0e030f0409050402040b01081003030f1412090d0207081f1d0618010b090c1614010209040b04020304020f0d15 75
    0x401601c00418241c1d80d450101744a0b204020003106401382e41081211142000002034440e07098100101850840441060459003640c458214903070601002070500342103680003d920040d40c80c0e0080e000000c66943c3c04000480706001803480e0180c105201c00d050040840d8001d0360290b4002003524a8202080b41c1d102c00c55200f0b0b084548030030740e01c42c180010740c14988070303640789005c080c244404170f400c10032075444520f04a84002010011420350310544180b044070f45007100384040a02c4d5480d5902e607413110040e940c1c21540748405100f00d0340302c941c1451002030301d00d044501282c050062414200d45c010380c0c60040d40341c4542800d442e1100300c0f0904540524107542a0f184c28040c0070705092425580c884111011400406030f814610754040315511419155000480c0301c000c0e699031048000c803040a8134860002405641411055614003103064000f0074900c8411030301080142c1703445041108a00003902c021b500000b821031402da885c144400d1a030300003805131801c00c54414040b003503002 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 49007117 1250 49005867 49005889
    0x3090106170a060e030a090b0a0302070f06050105090906060114130f12051501031a1504050403020105010612060b1b0a140a140114040305090f090c07020306091203060607020a05 78
    0x180340d12201100042c403041380f084103503104414024501c0d00d2140403008100809900a40380e080360009000c0c403c1901035812544020743c40000c01c000d0301c80b142003000041c2402d205107401505444c0002d0354405003c91021300c90f0700143c4070f01c60440303503040c00380815030031018038440f041100c0c0c2c20200f1821000c0c81c1d18030040038181c3e4800c07082100b40c90310b9030401c1c00c00400714030107180c040018000500c01c04c07007280030054458100703229a0758880e689074003c402d5070903050b00720b4a4402840305159040d04424141e80d01615402c40c41c022580c0c0c1c20080380c0c214410003d042205006d40075200c21115030030b0244503420421160064043d032560920003004088030882ca52064801c601000b030480c0300850404240402005001504448a850000024001410003000081800007542c03600c0c1080d8403564003a10280e8185000780503441c0c1d5902501d01a0305c207100d40d40000b4282c034000a2400822403900d0400303070458440000303000c1c103504a010102c2c0d00005440003c039043d102d07628a02 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 49008367 1250 49007117 49007159
    0x120d060314010e010b09010305070501030903050f030f01030309050d030c11030f0303010b18040c020307030c02040608120304050c040216120909020c0c0411042306070f080c01050105030c010801060503090106 91
    0x240d1190690078043c00c40b6407000c5174034001c9024800400100d0400f0410030111507003801c02154800075441d00315031501c0344d4100d01e240c0150100c14450b9070a4480c40b40c60581e0702c60388918444688030b008114115651910050000d8500030031000000d403154942204c40e20043c0442d2074040c032030a004d90079600700340c11403021000041031180d40c076000428030a600c580240c40400c100740c0000d400039141d1060714005401e004c2110115400c54955070710181c0103210301c02c25288003000c090089a1998000c0d0740540301072040207108102440c2900c00c4036103c2182540c12a00c0b4101aa41e810b0800b80440445003031201e88400042e1141c054002000002c4002002e4000c01441404000850348040586a0a080c0612042c88801c00c10803c0c034100360f000c202001c5900b08003400060091240700802400103503c1319043e0304000a41014200360b80c4400000d201584e01c0d0024141e403000040b000c180064210001040207601600041d500003c0f01d50021036415266100460400300904100c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 49009617 1250 49008367 49008371
    0x50304050414040611090d030e0a050402040f050108060f0d1401020f07060603030215040b0c0f040503070905042306040308060111010c0203030712020405151312080711090702120d06031401 83
    0x1005040c1c424000070002c505c02c03107802d00e00400c01051342c03098485da00a041c0000d80508a02075918440e114004044c0248103641d80c640b2486001e22500e1b252040c207002c00c0d50f07000411210300c3c090020782e0305600e010303204d4040041030381c490044250302041c1200d0155801c1000ea05255403480c0201400c1e406084042622440c5181c02460001c00d4105008102c42d80300c180000990480c080c2031b0044891f04c55503891700c001400d1140c8502c9654007099061041d1040020080d0f02c640195100e1030050341c485290758510040744414400c1e00300c4402c0b490b00a0b90004000070f00030b681c110b812034010b00d0003d03500310083c20140d003103607081d103000b41c0503034004410001d19a03481501e2200f51481c0c06800c0d4181460040424500b1509800403c0d4004000c270345d003c0c0c0100c010503520014000450030404802c06800d10111036840014240c41c40600008122142c1c00c040ca621809000c165004111a2120309084860358100d5640c551a40e81c0700d25001002c580303083c240c00ca181241c0400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 49010867 1250 49009617 49009621
    0x111e04030c270219030b0a080a1a0105030a150903050705060a0902100507050c09070216180b0105210615040e1503070317280507050106090203130807050304050414 72
    0x51a90b182c110034a0580d0301c075004101c0e281c0c0c1c07044003d1032202c841c0c0403401c0c0441c80340c02140000f81080c5940d0058801c900c1042c07000f40501a5036280c5c9215140c6803a400c510702e03601c5006041d100e400d40d402c080c03c5d52810341c4c0e0000310313840c3d0350380441038030b6019240c0981000181d699407428544203a640d940c3c025211310f20700b002d618000d5805100740307400d0f041031464401c3c10395031107485154101d1001d2040c00c6440004440900901224440720302950304021035584a010300700d17071070847e80041e0002c0351804d64680800d5009030202c0390350601d16148c11181a034014091080c1c100b009003950303000b00b9406140c1441c07002410140c0090009031485280910349450000759528009a4040c8280e1201100b00007180305118000b44440410031102d94450f82a0103d0803002c4080600341c0c450000310202400c3d003503100d4040c09003a4800d038020300c102559100b07d0b200364001655044241d641600d80303440080c880c2d4000f082c4443c4960305407424a07640341c0019046640e041c4c0f03450210085841 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 49012117 1250 49010867 49010909
    0x100302041404020a090618050c07050114040302100231080105070504060815060306010503040303021608041706010506090d050a0b0c0301150c03020d0815030d0f12111e04030c 77
    0x344010140c40417410030060586000c0480700e16652004440300030702e50b80c1c40814080c0c80c0003000c131040d1540210080c040c43c81a08c24484114808440c150010701414007a4045407455000b280c0e2071100c8440206107204403607000b02c4081c404001c3c4402811510200041c45520070700945104031075030341b81d142c1c9980c9801e0000e01013031001402d000090030380d90500c04550341c1d403100381c0350044030a09c0c046490380d80700d01d0b0980080c407950655401004082c0480010800004c00030002d58442d0035000120f9030001d00040da8412080c0101030f840842800001114100b8800240310136000e0340880d400148503440c3c501c40710501341c84030042070038004018003101a0325503000f02e01c0302243c5001c2e54000fa00e518002c4d280c41e000c00b1504200102c00000c51103c1000c03030111420034070000c042d1014412050400703880c2003c0421501d01190340c0039101a0748420314841d11940c0340340c03900075030300d842004240100300e1040c1c00e03a000d802c0a002d00c404408200c1d64585400a81034480c41d0b102d40c12031081c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 49013367 1250 49012117 49012129
    0x6010c140307050a1110030e060403030504021305040b0103031706010f230c061006090803070b06130203070305061c05100f06080307110a09060b0909040507080d0806041104030309030b10030204140402 88
    0x4400d001f41400c0c0701c1c0075046290000340c03040c2c0c419010310f0300042d561a2440001e501c11000c4840302011818101804203100110380964100d034841c1c0c80d2248010103143c240c0e00311100448810303001c158aa0308500010b406031411010113001e1540400484110a031095400d8001c60f101c050316a200c6000c10450012010706200900b80504201c1d00d880e00d404085603580c425402d0090001c866100800c107180c4480314841007207203080030159164036200708020001c0c181140d105101788540d6100101e217115404035080c440d1342240241208810503c1c600000d4000760210a2145507114800115127105001505c1a54800d180c00c01011100da0100409208140c0220b2505403601200b0410740022004540ca100350594100e06240d84504044e030501d221540321041c64000c1e24000f40002743d1180700103120b40b80450341040302c1d013198030a095040c010307404000d0114031081000d002040c2c2d0b02d0041a440552400006005030700c03540480c06a880c40501810070540319418041146401 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 49014617 1250 49013367 49013389
    0x20c011b0908031e0d02030109020d0506060a120203040507051f091a191205070509181302310e010509060709060e010c0c030515090606010c140307050a11 68
    0xa280c04a8424145018079880f4468580710300074220b040b0800004c060031034025624600d40010003151a9a505d50789100654000502c02800c10f20780400600245002401e0320b244650603500d04062404d080e110307400a500291080d07500d80300720130b0300203850307540c1860840918100f601040300000c80303e00c01410408207600419984d00a11400c40505e507483c6040e264044200300090311802907408060740c440e031480340c0044000781064100080b07182c001004000501040d40c1e06c1582420010420450003025034440344c40c90303c0180860094540004101c500110b004902c0b0301c00101008026640030182d000c9040203900c400c0180300e104001e11900c2d50080025001e07040b0b40c68450002400400340e4012071081c000c00b20307410701c6613034415070291000720b50028441403256128100b00d5a9181c02003842520384d0001c0001400000e40480c90900402c8180c4415100d0035407903803a005ca142e450f55a5490f20302c0180b11080100d6010407a078600c0b9400385401442c4880710b4001c0c01049170b41 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 49015867 1250 49014617 49014671
    0x60206090712030509040e060109050601090801050411192d060305100b0c070f0f0504180305030a0504060b0d1a0c040302130e010e150f07090506090f13020c01 70
    0x2081400b00118103040e40100d51083e858500203030340f1291072001030700921048010080c240314400012940b2240c69006c68050403007621070f81c154541d50400c5509842c0200c0780101154000c1c00c1284203070404c800400d40c160341c0d40c6401201d494071680c401c3d02c440c1c0d40d1b5007413806818003289441c0481c01c1c83c1107090007a03c1c0900d170520161405030801e885450452082d2000b045000903580d12151050000e44054a00c0c1400d04410a0703444154031001c404d01e00031035115901d80b5101d9130030445400b513045009a0300da2511411542d0758005d007402450f0081041c1d42203034651000c1030745c40da0b07040c01012590b8410000606c0c0d455000c648a1030342c100c01441c005000c2000c00c014009640e480749404002c0e28030b03040204d05400764441d540c2c05080800c1c40c9603414481c2651030350345036440c0b01c10b403480755180307007944507440d034551408480546c240e00c101d60b0031882c00c00a0301c54032700700f0b4840e2074021000540381d15003101604681c4000c0742d2102c04208034995440c040d0010350341c40b0000340b10802d14 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 49017117 1250 49015867 49015873
    0x306060e0c0a0c050106080a0c03050f0325030e1809010c050f090d170301180e030901090b0a0c08130602060105040902100809070306020a03050a0b04110a0315030203100606020609 79
    0x1c1e100c41c6101d0940b180d18400400e12602d004440e04028094000501502200d4150b549010392842d0903038460702540001c903120b0084c01100445200000199580700d800300845c98100810407000040460b002c0b1000e40030000640030000c0c045c0c03a110f00c811001d4102840d000d40324a07000c0c00c0c15085500b105101020450108203c56014403440140c541001085580401c0e0002905c3d0a0b41d8071082844010203c010110000074100d0800c1c001455614003500103000c1d80300c42003241c0ba00e03485800b45241c00300701541c0341400a10114006007481d46081d040030f221407122038444008642000d401c814900038880c0c2c0612003280d044c09800c0c01020144c50a03c4600d440e0f5000031013504040903200b04202c40720700020040d03082048444010b6400c03140031940e5901181d0020051300003203a905200c3c0d820607940010070300305840b5084c68490b0b98404541440342c1c486044001d0105061006011411064040096901442001c00100f501c03400010000c0c170f80f0070701900708903000307241d105950 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 49018367 1250 49017117 49017121
    0x20f0a05180a0503071e1205060702060a050609010605030405150a060f0603050618060a03080c0c01030c0206090706050313020a0e09120f070201051b0109050c09060a0303020705060a050909040c0306060e 89
    0x500c0004180c0192104070038a034100c003c0702a5440d110340c0c6c09034403644000f403020100c0000e0240200e070071070081442c0d900341e9010340e807480d03001c5054500a98503580c000d000712004100a0740310f04081e6420510a40070740e0100d03244400c0b5801300380001d031110700311159243d42c1003182d40741420251004240750300341840145084000920703c4203482401c071004040c50000140c0580d81d00d00d000e405180d0080d441034840d4100b01400740d4030761443c000725000c03901d0680c900d0401400000c000d40300d4800c2c0720003001c1c002d080500c211240d41024010000a6899001100050741e400000780085c207130847d80e00c030721032800560543c80c0400807585011102020801d4000320095401102e0300240c0a0802d180e4400300180c01c4041c414507069181408d52803c050b030002c100002c01c000c0040d0380300300c13191186a01c4060401c00049181c1c40000c0c00350b07100a200308424113040c006822000e240c0c5c04c01c141003604a1004c03c91460701201c0484a40c8041c00040c41003080d940704510240030070b00d01e0f0a0442c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 49019617 1250 49018367 49018369
    0xa020a09091a09161d06040e010f0f0b030c09010e01021207061506050702010207091802040504050129180903070605010305030a0801060311070318050402040f031707020102070302100201020f0a05180a05 89
    0x112100c4102600c0c1005c091283c08581c1d211801110010469240171910540c1d44030005a00c4a54a01031101c0d004594000001e244280d001a28001e4003402c1006203415080801035403200150080342d0f0540c01020160004008070320041c1032000c0c0a00c1d40820300815900e189403459582d80c0110080c072409000c0075000d80d900044c5281510442e050001306031000c0e840c0860381c407a003075400941c400e00702000c0208005e8190002c244032101c840c42e80c01d011080d00d0360010224801280560002c5d001400c0311040422901d6840d04010350905880c505003842d11780200b40c51090b002580d19520007c0d5080b000b540c010703e22401004549010844080f00030f18508407445002805010412000c0400900340d0030b2501401c000c00004108558659483c1902d1080445a12054400645820307400a015061200302e030f807456070590281030610304550811420050344a203200840d0740c240200180710703114000402036600c0e2a00e40315240d00c00300440754601039014800c9400798014400c20026 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 49020867 1250 49019617 49019627
    0xf06011a0c120307090501080609010b1602042301030c080304080a060b060d0c0905040b01030b0913050a0605040c030c06170c030601020a060906020301030b16080a020a09091a0916 79
    0xe44003090500a41d1866450400c40c0340c11110140c0c1d403600c000000a12400760740082c0804100d80082c1c0700c0c02c0c4196640820071003c7d400034130503250001410400884416940c1801c1002e0610003000040e42c800000c00c0c0902003038003500c1000c28030300f40b64014800c1c4600c449900c0c000300740020040d41f0b0103044c600e000d40c07910310707118005048903250038003489071760f03598000d80300f480c02c15101c10000070990700b50007010742c285441214041c0d03151454407000c0394464011000050005040c070a040c0d2a0003c18180540d518007040d00c050043c0303c8003000040c20341c01010700031801500b2141c0d0b400d0131400d0003c4444110381c45030b401d21000c2ca89152401242d040420360003100221001d480c1c3d52400010303030504000000081c80c2074a450707503050402c0354030b601540c16030740034010a401940c0d48014071908810007004840126501c0e90020703000e01c503a070300281201e0405d4909030340625a185080e209441204076000c041d0203010051441c1402c00d11060782e8424120154500b25404c03a074000341c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 49022117 1250 49020867 49020899
    0x2070c080303010b0d0b0a05030d0206010905060102010b180a1e0c02060f040b04020d170c01020414040b0a090b040902060408060a050c09010e130e0d05030709150f0309020f1f020f0601 81
    0x40c0c41625030403141c006e540c8401001c0020140642a01c4003840042d0000351101c009000b542011403504000c9a002d500c1485021551000980500c020785a840304200350142c000703108801880e2203020f881d80e018a00c1503801d02d514801c2801040140b880c0e0740203800e0070740003060740d180403041108100203d15410041d5030400d405462080c1c0c80000e608040c41e250103600945065076800040368001c0d03403015801002254050303000c05544d44100e008000c103503807206040c80c2e440342e9040401d204000c6564824038080d880104001040380460f404507506070820362200015402c01010001c1d041c1013401902da01403107605055140905040018141001e00c2551500410b148040140351020a9100b00308034041f00044404822845000a20641c400c94580700041c8108100143e40010104503407030b10207068940388405249140200e0050000c0003040c1d90117080b1201405460300ca1078003041800d0121000803240d2603156401900d84942c614442846901c804c0042000041c0600c900c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 49023367 1250 49022117 49022137
    0x3030f0810050d0302010e0f07050f061201170f1b010815060a200709090c0602010e1009020619050d0b0613090c0c0512030621120f070c030602070c080303010b 70
    0x3800f90601d41c00e0480c0101082d070a00a60344c8100074840352003820000340070045410444070b040b0389084d101e05002050150301281445140280010b01099240c40d00105541582c03000b02d418440b0a41030741840d0520600c51600619007005015106507888030b400c5a1140c0c0640c070100c101945071000c02c030207100c1d440140381007200901485001201006001040501b000101c520240e216210740c2c000f42030465003210040030081e800070b0490300602419513020404405007c040e040420950040c1084600890f8020001c0103100ca00320900302c506903548400b552001d07129100401888119031300d12502c0303485500c05202c1402c40c001540c242505403094003c006c10b01030310501040d100c2583d2101d000b003650055840c0102c03041c0d00d107000b46114180031200e018070382040c6a40403060740000c5000f4403e80c8c0100c144d0f4039084c02d4070002031505c90003d8024510340f45d0035441d08071140d240340d0021541c40c0e03000203000701405a1041c0758000f6254800256141d03514051400e5141d214984e010 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 49024617 1250 49023367 49023379
    0x9091505040c1209120206070c0c090902150c0c030c0301140c07080403050d0302030f0703020a08160210060923010b180f0a06050c1e03040302190b1303030f081005 72
    0x40d142e81c0b84a5a031007856401510320034800c8030014505002c03c80d600260f5500107109410008130241e01c0f40781500515500f148580300d075282031408440103401e030390005030f03000402404031000803106540100305140c1804007030020b640350182003509103525030400a1003030307060400241c6200c0034906095080b500c0040c4003555002c0b945410f031003500580c3d00c0903100d401507400411003c0d80503002144aa001c030003d0552503079520101354200c0c018920840000b40c0504005801c40030426450321002000f801103842078a08400184140d84254000001541d00c41001040341c3c03110000d081102e6110b91039a128a605103e52011140242d000036043e96541c808402c550792a800c030f50040410014040107407003500d4010140c400d6010681081892060301d14441510703429107100504c0b41c0001e8051440d20789560208140b80d903403414a000b0300300c845c0200081114000c0c0c02440b800034205100c02050349503060113030141650300e5041c020b202c040000c00210b458450b00d140c042e9034044483c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 49025867 1250 49024617 49024631
    0x50f06100e15160611070b0c0a0314070216090504031e0c0f110f03060907090c02010b0901170f070e1308090d14010b060c0a030c03020f0a03030204060909150504 71
    0x80c500e10b030140341c0040c0340ca0001600020032a4002c0d9601510350141c0401d010300c090b0f020401700d0603c105032001e4110416800403507041c3d10500000c0081881d189004a080d0008103000c0e080030409407030441c09a4040180c0e1000e00504800c0c807070040400000070442440e048d200601101800c40d00310f078120401c1c4d030841000f18003450100c2c3c01a9004040c0c041d02c3c141c3c624040350380310b05410701e1511800041500e80794a14000403214410100b205c0a407950910b40000c0c0d070b000d0507405480400395500c4120032500764892204490084c18006001c0c44030711000581a404e1440c04141c0360110b030003501c000d0141d110184a503079004403c803801c012800d4035a04000040340144550140d103d01a00d40ea00300b44000c1070480e5101c500408005c1002032105400c1004078444c0c02805100d94029409100110703005500b1030180758002d006032084900029095400c000c00c4890032000309501107800d014140d030210700302c4040e0541110810800b800610555109a220f20a0b01e200341d071036110b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 49027117 1250 49025867 49025869
    0x4050f0310110306120a11010e0406080a060921020a11060d02220b07030801032604080307120905090610110714030f0312160e10020a02010201050f06100e 68
    0x88451100941000704040c1082c01c078004101c0d03000b40d400c1031052200e802101c00044c00811000c15039540894140031b03450501c00113480c010b6414152591140d83e40701e0028002c18203003d81100184100400903011040e807034190f240704920070b200030341598240c0340e000600790005030b01002e09810050020081c0f100e03030005030203031050308101d00d031482c0085451460b0240111803584c90510201c4044501510340c00450060f00891101400007040c8000420204900440107404a02e40c2081d109403001800046142e030350003580030380c0d4181e200044140a106480301c0c12030410440345005c4041628150000b04092000b60502d80300340204041003604034005c001c0f0081d901c46450a65411603a513030003400050340182c0405000b030191203990f604003003010085402e1b035007407011140250340701d42c80c40080b800c1510b0320321418000c040c1c45a444691356085000591146135008050292062000a00f0749134082d01461201c0454028010503641d090300c0c80c80160603a00d005107209940030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 49028367 1250 49027117 49027123
    0x903040e09010221071101020a1d0a0e010326070209160c05010618060b0f0301060f02030f131404090314090a0f08010e15010305030702010302030402030c040f0e1b0604050f03 77
    0x180401001010701c2c10021203240513820240d100f031400ba1200903940c8500000b4900783c0c030031800410006101c02c6003400300c0c0000031205505034400908810030307090320750385131710004a008e03001030759086208502c10b00f640f0102090150070310409a64203041ca200e9a001c210040d902070490b00c0c21020804c4180700313507072046504100882d04100240103071035403012605041e0f1009a49069500c0c14401d000c514280f154046640030340700b00040b289142c4c40c09100b2203030407098000101c1140002c01180c62961050320240c2910b1904c400304544580c600141410448001110580510300388801e80010030381200b6148848501100700668901c001c41c000360241480303402401408824580201d051441503100d042c03005004400c0300c20841800e52054401e0341c09200040041c0d104000690043d44690003842d081840a01181e048100480018090b10f208409460007281d80d5920f00b0104017040003000d041510010041c21041c0b000800b0036954416401181d014018a01c03103050503071810 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 49029617 1250 49028367 49028377
    0x60905070b030603330c040b03010e0105130b03071721032d0703110c010509010f0605041107060902030703051c03110c100507110f060103020306010b030903040e090102 74
    0x1050a40d94a1500c8004a20140d001620b040c0d0280c4100b00401c195428007140036110710007032404185414807103100c0c80c0e4204400800b0300040080511000640c0448000503501074000007280303003141c0d0304240612032803d00581020350034500386500c64125407008501d62090720300645031074020a44108080303191142c420740c0841c001041e0760300100490203441c0030718002c860038680c4040b000000c10020490518401a000020a5100100d03171054046e50044241142c0540c4e400d00340789502c031403182110700c2220100c0b8140d441e4504c0307441c6040f852281c00090441120100006442841c5903a442d020f06c0c040100407565035200c400556404015520045034094211500f110800103084c0b000d06c03582c170808000c28240404010702d0a100d40039904540c0305880207040c07079441305800e00b002d042d0180400b030901c02907140c1444142e03000c0c812a081840b40000405865241d8814503181040503408080000400c5c428008050404000c4a00312240110000c4540e01c50846490081c410 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 49030867 1250 49029617 49029623
    0x10e18160305010203060a080c211606020a03020708070807061b051204030618020f1c021302040602060109060b040b0a0201111602120607050d0c0905040504030806120703051203040609 81
    0xd40c20020800c181500110310421041c1c504158165403102c0440c0d9880000d00c0c3c60341e200d103001000301c0342101100400c034610b48038001140c00c500003407400305004000030f802410040e00034130000c805064042260300000d244880c000c00b000c07841d010400d52140c1c6640035003000c00c001c02407282e000e1052444030341c070340c0c5402c8020f0320782c1004865101c050607807141c0300c11100300c0e08050032081940d8074410102040c07034010340000c911002c0d443c2007000c40c814070285264614514540e100140c0c0b2480c80701d0940559030040142d803103003000d40c0640790800c160312820b011410110180800381002c02690b0854003e2003005031503030b42e0a80306034003610407e20100b01c078003400708a01d400c03039440c0500111440e0003038442181c1040c0e01800503444200072a03007200810002c01c814000d80503603a00122100740300341344c4200344c291900e0026064070000e86054000601c190140f00c8245040d2120304007918215009145030713441c40d91441c1c0c41c4c03803e070b220026101c10b002c4009000d02007a40c1028410940c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 49032117 1250 49030867 49030903
    0x1906030507090501060207090209130902060c070e060a050d05071205100903030f050601080402090609060f06130305250603110d0905011407050408030301050907200c0117010e18 78
    0x5102c504840041109104000043c420080c00043d0802280700f16100301e840a810612072000402c01000a010301c60f178200d800190420179912580418454103001d085440b03003403a00c908008040240e0090f03640c04c1117101d030007094003507000a0390001d00d01d030444003000719020fa1800c080c2841410700d4010116044140d00f09542441050740c154402d1800401000042081d9241c0c3c1004417005001120003c0d00601d0b070300c000c24030740d282c018281a8040300007440143e680c3d03e4040802d0042d04030750006900034144d07620900c10048240314020911003242d9141480e45038401c040d00c111941442200c06040c2d54481c18803240d04144c00b00d605400716183c05102c41c221506d0500e0003000401240241c02c0c11200124034018410411501150107541c0214103503400c000400c0b512500240001c3c05001068860b80400e90401c0c042206c43c0320600c01611500c850800058401e044101c0081505011000184280f40740ac206058105400410480704110304401407490075a074995840c000ca1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 49033367 1250 49032117 49032119
    0xa0504090f1d0708011a030c0112020c010c090305010509030f0706090c03080f0d11130302061305090c030a061203080103060b0d0501020f0406030e0703020d15090804030c090c02060f1906030507 85
    0x220700010f40400b12000c0400030801e50342c503403004601031007a401503031742d142d04200c124028940c885c030240652626440d10041c40d261001a01d542165a0110414040340742810208103000085c416a50b0000b03150700031714a0f03c4170108800c5564440d00c4801000c0075500d8007088184610290910050740e0300c0701a550307441301250881e03e40c5400000092044034240079030a021500a04140c425001070101403040380c50441d8204112a0803420701c144e2017034140c000000e1140d80701d030800307401a08000d0441359a42003d02055003079034482d400c13001c45200b03c20560030000340c0c040c5005044941000c1c00094070080c4c50b001640e5181c218501401329070020502414540d1100010070849071283c90030400418141540707030712140c01c0d1102960003600441d40d00b0100f074a089204d0891074084100080601c1c00c0d5495414035046a0030507981d0800710740c2e00784180071080c402c40c042980c60340000c0555103070004154604a600400e584400f00031210700c55085071141d00f01c0c0f8081c40d4040306030380707000e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 49034617 1250 49033367 49033421
    0x40305190c151713020a17100c090303080702010603030503010317070b0a050711060103021011030c010c050301030b0a05091b0423070206130305030708070c0204050405060f0a020a0504090f 83
    0x800d12050034098000d420402094130f0320405810f0100c2550701800038507100f8548000c00501c1a42d200c0e0921040c0100e030841c01540b24207200b040300c00e110300d4564150142c110b080017494514000c02c05010741e03240038070600119030000103680c116030f80031441c144131850002c01120a4094484000c0c1805010800d1081000e1203420483c4128540d0341c0c1c4903001480414025560b24081c44060341003038014100350310b01840f4140340003403000380c0c40440e46009110f201480c00c43c1c041078069000108040010300401c03001140171600301c0490310060002e410082041511340c5282c00c0750302c90249001c00015490780b559004203c0d10340a0305402d0301c80e20b403840080c0d500e10030101c0b415001806090005061021030303444240003150944c3c2c51070f0443d500e616003607030101d60242681052084100e80c44006070b5490042d50701c078900c00d801900d198284001c54210204e13015005a07002d50061050305101c4d42d0000590b01119142ca80120f815000c00c40e000004220701203840400d40645002070803e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 49035867 1250 49034617 49034627
    0x711010c02060313110402041206090302070b03010303020601061b03050a18050a030602040e09010903050a0e06090901031b05031c03051e07050c15100302010e01110d030603020f0303040305190c15 86
    0x1406010300d0448170075004080400c0304030303c0b580c045c1d4911100c88100300d03404580941d008040d80c61180c01203c0d04a034540b40c60b01340c2c61f04264002c4005900a01c010f01404d58491307165440107548190303040d0080704940d009415030041402c180c0403c0320f4422400c104003c07003050f00d03006200141001c40d00f192070f410201c029510034010000103a192002040440805120300f2502d1500346d03882a080204540d411100e80c08100407180c0c1c440024401c40b4001e0703a50901850086100d007050101c40703980c2075090704d070a00c00b6520461013074011624240c10748840b882d100000c03444501d0002081c0e9904540744210562041d0708020040006040040440d0420010034211035541c00701c918000342003012140c20002210403011110b8600800c000650107020b9180b40c003d01410024403420b8080c01451904c080c1070440350000c0d441c4c2d2410019414900000c0c41c407070000364080c600c2d1900b1503c0f141e944801c45003481041641041e003280500030007164100140501001d641c10740c000c07850000b04 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 49037117 1250 49035867 49035901
    0x140c1501080a06050c1e030a0204030203030a0903030e030f070b0c0703050102070503070b0117030d09020409061a010e12030f071407060f0305090f060f0606070605040f060c02070b0711010c020603 86
    0x540703d441c00c804107266203c401c0036160120b0300c080e0301c24000340c441881d080c0e058001a100342501a000d12011005a5041c80a420315406e15905d0a038820724606004083c4a0b01c001c2c03440c020380142d6422140003002244910503a80413010b41c1d6660701d40c1d4404545085c446600c01b030308551010580d10100040400140700c80d600410346034002c1e98803920098a6802d00524294840d881040340b56400441380d0000c00710b184c00104001000500c0c3d407a80d5058440c1461045409113054080d18102d41c1c01041e041c062600541d04a01c500c080700d440c0c3c1e0798901c04c440301c81d0115100403890004025917040120750030708000095401160703603018041d104030783c0c110040e00464117140014520840025440280c000200b0042059851b601c887e0070701040d02030301c4190444400c00412000c20b02e1400365038000c030b10070000b01d030b03880946007014030469504000b0b10046402c40f5104100b503004943c02e980303005402c090030681c4910341c0390046e0b0f541005110025048180442000b50301c0d4500c1e080b2035 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 49038367 1250 49037117 49037123
    0x120506031f06090b120a03031109090405070806090a020604120c0f08060f0a0b01230f0406050309060a060f0303050a1709030316090b0a03050a0209060304140f010501030201140c1501080a 82
    0x2200042044e02080300107400305000207095441030b100d04010078400d400c01d0045c45070002449190545c00004240d80c441e04650549544d070250508001c40101080481d520500c401c0107801c5110b540d5000502d644124400e00382410300b220501700c207016a04110700010311900b43c1003000701c0d54a240c0300d034079400c08031030380000324000b0400101d85540500896001d082d050790f9016007070071920740d042c4225030010710343d00400b402404102c0035888040e0080c80904400d850381510307807030020010b51415800a10901d12207040007810002c444540c00041d054039410f05150351204080700b411a8616a80214407001c0001710040c80003100c404401540507418400540304920140442522205514410b90072501410058083d5140c841d0f032240381c1200300000058549008d135000a03105804c25982907891141d12540003584460400950791840b1034000280300d40e42c550340000e400031014201e80c00ca0310200181107540c103034003070040b1095040002c03210902541c45104107582d074902100d0807 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 49039617 1250 49038367 49038371
    0x1e030705061605060108061003320f07090b060301060c080c0a1a07020a0b0601031802090a0209011701060f0c0201020c04060609050a060206240316090b04060b030601120506031f0609 80
    0xf0800e1030300459914401c91188c005021014a507a239030030305021815000c0305038040c000724468200074061003045070f80704400004258514880c190709003401e51079480068040d10f0300150f021580c44050640f411aa1607080c032190340015030800284501c5445000c401a0184402810800040e00031002c461060401d50020f150741d0301000ba6655518039401810390304012001442ca90b00c0303500802c00d02c0c03850a400003148112540400d4200a0640351352400075000f184d020610750b8800d0504d8504200555010ba16514080300034180680d01c125100030041e02c490020f017564000c0050446182000d0000c00086a44201c001c2c20b1410340c3c0120340c0b15075882d03040006c1c0b6902c006000c41c000c40d80200c1c0d03411015100010720020f6030741c00302c400b81c05015440b58078a030000b01510100c01498915070102e00f030050001000126402c0b0740016000c56410b1082c04042d0343d00105550100442c00c400291030340b01e00d400030b464906034103000400108a140140384c181510341102080f0398502e002 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 49040867 1250 49039617 49039619
    0x15060312030e010b0d12020c060f030703050c0406080103060902062116020d2a050d020d02010b011b03321b0703050a0f08120a1401090b1e0307050616050601 69
    0x14190a0341e6044801a40c040c101004400214090a24401c03403c019401142c0500c8523040100318144c1058940d03485492010042007601509805002d910001c100c01c00e5180030f0810030060800141130001a00295030703003a582086441d40000c0f204106040110006800380200b0340244014080300c10141c51404807000c1844640001102c80c01003403180c59041d0808449041e00b440e400e00b211000d903040d044100c145d004030f0340601c2640d1a50440f58058500c2400d070300c0d0041d00390390410050a04210b034034403000842d040f845141901c1c0c04d50514240000161045a00903040344d2240c0746100004651101140c601d9041d00038410201c0c89030921703900608114102d41c85500302c2c40060595044500c004c0c0c0001d40c0043d02a00c45071142d4206410481c2c19154280980800c4a10888855030f40c080c1d102c03241014035500b070050050703100500540032014003050380700e41ca071110548a00c00500b0015000d55080c00400050100640483c1c0c8900840741116000c0a49503000d58480c0a6440 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 49042117 1250 49040867 49040891
    0x20304020a0b130504050916060906020d0c11060705100c02030a11060103030c02060706090c060507350d1e060302090907030809010807020a0b010303110c0913020d1506031203 77
    0x200f6200480424050901414544030034030000d000300030084c490740e0085000d003500030b84c10030000001030700c010790360420f4940c20300401916001401c00d9403c144860b2420300400a40410844000c0030010391b074080e1903040b58a0064a00301c403800c0111401c6040c6040001240d07400400b9014220f000d640320001110740706001920f03603000307002c00f40004801900210141c00c000c001414001e10855000445841c181c0707504002c01d8642d000080002c00c0001c0350b2040c0603004c0f640c2c01101c0562000c04182c0d520900d983d143c41c3c41800340361010100d02007800c0c203503045958002e44a409030620402800c55058900b140102a02c0c04101c1c810308100008c81d00f4070b0390015400098a500030b071a1482c0801e107400544031040010051021403040340c445c6400079403074481c0b940c021440303900c1c0e1030000750440c4145401c1c05078030a0702c40d0140300000100415031000180c20311040b0f80603100902c0b004c1c02c41c01c140f21a14240d070f041c0540c0310708014001040164a850f45a00010a65010081080a00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 49043367 1250 49042117 49042139
    0x609060503061302061b03030f15030616020102040e0a0b01031b0804030503180a030804020f0d110405091504030e040b040507050d0c0e03010f05040b070806030a14031309020304020a 80
    0x405016095801080095404205120f211070000e000401140c00c1403005a146c018074a00703081c603c4195000402801140d410721601a0b4100d4510a004000500408003007546c43d00010705070070500b60b0712a981c0a040c0c1c000e41c12140904107007400b02c059032810b029818068058800880e00084c070700400115181c4d0384c081455603407039603a51400c400c5c2d01d5035102210b41c1d410241100c00c80c0b5a04c0c4000c0700248400300489200716209840385405450540104000c4107140c1072014010f541c85003046001800742415041200e1040b10300007419125203043d14503044540740303c5c9181141801c05d00c814542c204c01d12074103110040b541401600c4030001804240d81e019261980480d800b03118040301c11116400c110440c0e0018a04a98102c00c500700084c00d5840000b1549190f99461003808140b02d40341e102d0a0303000c5042e0602c5141801c1c00e0010999a5040a401a240729500c04142c40201800c1c022108098142c0340851010760b15600b100d0001d6000345d4013248903950015000400f00020 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 49044617 1250 49043367 49043369
    0x60c030417091906210501120b0a060503011d101e090f0203030d0b030106050301050103030f18030b070801061101050103031d04020912010203040201090b0c0703120c0c060206070201060906 83
    0x2250032800c011101000100064005035209544803000621201d0b04210240f021002880140e60701ca03112440c2c0a5801c007000510000c0341c2c0301504081c0140f00081c0b4100c12a039a07541e0246540c112590380141603c010801030704241c0c3d045d400e102c3e600c0a507000c3c16442c02e41d009814400d80d00b0601280c20081c080340c0000c00c002c62444200b5059540f08006a40b002c40650301a0120706038205d020360010b4115844041d01e802900c1d91a40500d0050409200d401c0103864142c008000950440d1400340070744816480b1403040181d00f1000c1d00b9800e51a40085c0003d55001d03020380c007107081428002d040034000340505800210005a0250040414000c0740e04903905901d500810091011030081c1c41d00c8001d051640054080105010710b4440108414061a50741700040e22070034144001480600280e020070844a02070203180c036100c20100d0355504880d8007450703400c0031064a40080c2e45c40d06905801408810f0111170003e030356070b0045589442a1b096a000304059515180a04115602 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 49045867 1250 49044617 49044623
    0x61e0515070f0b0c0a11010203010b07020909030c0102160b1f0303050315130e010506100806040f0906090f0302060106020312011809080406021c0306080307020103050411120a05060c0304 82
    0x241280c0440e48030801402848180d0207031140c0903600b5850384514a040301d0685415100b010000340780c1e150180e221103c543c1c034140d103d000b5840d5515110071001280541c100c0607120391280d0307010550202c410000c4922018052000b991901100b2001c41c24035801d00905481b105e0412002a21100c40100a10002100b50003050b001071300b540c900719800d4000500c2c003e50036200d80d400b54050b07940d5910440942c00010804507206000c0010035007902e4024000a020f55509078001401c40e81120804d5400003058400080e42c0780b507000140060080c1440241c07940c1e00d04400002440b20550840200e80c1c003039000c5a480f079a03201e800326070720712420b60411113000044005202c41c01017600205034682080d10041550b8510707445002035641320750720000259110304805039000701c060500c840303d2030013030504100e034070701d0108241e480b441400d60080c1050741e00d20000301040030580c180381055802400c00c080a150640c8016510311180000751090320403000014881500c41080300d20482d8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 49047117 1250 49045867 49045879
    0x10c0e0d02010516020609030111070c090c0801090b060d02030c030f0c0c0307020108040507051c050105012103030f1d070306050a0b01021c050705061905180705010c031101050a061e05 81
    0x200d004025810361031101000c1b0f84c440410880b2643e240c0c1d00340207401c0c6c1400940c40d22650352a085c5414540c601031944900c684904058030050750580100b52181140c948880118029064400080151140403000c0603000d1000c130a100b86140085c0c007952040540c441c04c00901e0321203181c041031030302400c05000c0080c0c1c01045448015481044140c2d00b1511400c1154940ea444100045e00340c840f02290f0320b8194048980d00d024800700340102d50040031407100d40c9141009180e1181d2240f0320304034015051540310a4a103089075116809003222140c1004061084501140055291400b510080d180d25061002046d000d54092143c2c1754400d80c160010800e41c0610b07048200200b42c0c4030280340500c80d0038800b043c04502d0a010040c4210841c203081c0c0c1484080451075400c8030800b40ca03505002505451907601c40c00000345220070b985007420000b0a5254600d012140446003604810b180c0d401c10040c0401c040640d0003202c15036901140c50aa01e1004c048641c14031046817041c903038088 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 49048367 1250 49047117 49047127
    0xe0a030503040902090307030f03030e1c0807031e050a0606112a0d0602070302030703110a02130209060f070503040501170c09060d0b06030403021c09060212130314010c0e0d020105 79
    0x11100c2e13004150b80180a815144c0d000c2e625114070f50b014000d2541039001c1303a100e00c0f4040340c1840c280a007541e000c412030172144164440007001004c40742e00405010516a44045d44020050403080300d60b00f40394001c109220900d419a40c3c0f002408842c4a014081103a20300813074080c1030003003040f203003005107030586100c07041e2011580e2415a11454007103070821451461035021645500082000600980085565400c203103001010420090401500c81e00414640f00040c0da8007405a11100c03420440962101d01160000c1c90f2485000984614003030005009030030841c011018000b01e0320240ca650644511001c01c12503041000c0b5400006840104a210180d15046000d40348007020aa4001090304103c1c001c180076601c01d1b10290090fa01c01c03104044201e0300756207241c4a145591134108000c3d1319201c406507503172020040ac180040d0b40450304544900741340d03e01c6c80045411000208481101e414160300030220140c00070000703100109080310030300b00b0b42801c9504581c1a59168600 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 49049617 1250 49048367 49048379
    0x270712020607080412030804021507020d02011d0d050a1505010f06030c0201020f0408060a0509030a0215191d0d02030a0504030605040c09111c060303080601050f12070804030e0a03050304 82
    0x90b0340480c1e011207900e80240700c041560810044c1100074a4400d440d68007a40c1414010802c1e1141c2000801030310180c00c01c882801070b203d494412429650a08045c02e14000c5442880c5e80c8030303484424250094070149485092040028a5020b04ea01030198240503070f404220381400e484090140d420400c2a0440c10802607110741d0141085031054400182049d04a1421040a0340315500400d40f80d8820800e0040002072485000e070407950900c001c51a00c02c0d03040c0c01940f5401441101c110003182000010000c1c010008840707004c400600c0f08011200d08200f43c582d9404503124480c150b841740784a0051814000006c035004130100340c862900f807a25507587c400241c94010011540886070070030010717100c001c40c000e9518a40d4607020094541078107003012500340d44620110100303d8184041000425000100c5581151083c81c00d0303540c4010008000050388140501581c034420150100894160b00c840c2043c02684203944100c6400d501c40700b04003450040e4000901950000c00c010468 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 49050867 1250 49049617 49049629
    0xa080a080901060f090b120109030806060c0a06020c01020408070807030317090a0f0c05040b0d0f03141603020c0a0914070f0309150c03050f07021005060a050927071202 74
    0x407007000c8800100c0c0140e00e0300c2d100710160b0141e9000c0014152500c03d441c84174602140348183c000c1002c402040304103c1e40c3c90080a00074087d1040f8000c2170b00044016891006010307030300000707411500c15035075506052000c82c000c0d070091140c24064001c8080100d010400441c0c1c0c2c6044981582d11211507401c22102c800c038400f405450013a6901c18032000400195243c11b182d003066014003404078500b8603210902c0b040d20002440c15100e000104582000146241c104513000740e05031615102022464585014610800c0d01001c1d07201000c0070500d042541c00030f00d40c00c03d00003d480720705410356600403400030303542c0da41442d0020f141d01600240d40d41d88aa1b2440000710b58034a80861502001d03207404c0800c042e40d44980d200c00d03449074140d041c1c5540500900c3d4001c00d05c614043d00500c1d01c510020348454000400c56620768403000864001d50b070321401d00c0003400340242480c4940c1400e03c900d192803003000c0380c0c0500c824550041041109070225854085a04031800022901125420030107 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 49052117 1250 49050867 49050871
    0x60c0d1b0f060e060907060c0609022407021c031e050d060602010615050f16020f0a0e06010f08060a030206090d060204080d02120711130603170702120a080a08 70
    0x4000040201010045030a40896441c1680285000110060640c44040c00e06000a20070743e03555010f00001c022207540071601214441e08136500141d0510f003440002c0312494211001d559101c00c50200485e0440c1c0c5c40014202a4400c40c1e0301c1c1c010b10814000740c8140b20241718098045071007507580c04401c44c0c2075002c2e00e1401d1810b2a00a180543e014104012103580350809001070b951601d09002102241d000405036800c10704202c0e06140b01a130100d002485522410102c034944080f004046481d001505503810800812001502d5100c088180c000401128541e000642c0c60542070f9078240a0b007181d9004401c0030349240c580c03e0458007030241585c481c44070560848040c8103070300d0104020340301030005000c195016019030050404020714006002d000c450303280304100b141c00d0001f20f5000780101d0049090310b11641c0d00e0003038200301005101c2035101a1119a1039060071004401010007054201d100711086000340e0081c0b80242d94075100000001e214a10420600c10180c1c001c1d00b00766 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 49053367 1250 49052117 49052147
    0x270106050405070f0e06090619020705030a03080a050f0f01050d110a0807050102070b0307050405090a0f0f0204090f050c0403060e07080703030203030103020909030a020a080d0204030f080301090b060c0d 89
    0x10401a55510101d800c4440841d91000020340d80d0a4401c0083e0380010000f080750801c071001400d1009000008120748a40d00113001c40c0050b081d820f20043d402803100b40020702e0001c060362010007450034050022101120300041d1140b80000180c00500101c0415001d4280701481940a038205414480074031a1070b031040c2c50421414001c002c0a0755829105030107048000043d04a06141c0360019250652070341001c0b000f842c0504c1080074040d0700400750b0301140c0046407001d00c00d484140110004040010604085a04040801c0c9086a041e0018003c50f211141c0404c240e5006008010844a00b80c95805003107004200800109500f07410a1981d502c1c0030064504d07071541c036a00945841615402200560030100c01001075142c020702c074070b0344000140082c0d46410044100291110800d0000a190810103d00d42a580c001a07055401460340700c40500c80501c0241811742c0290400d101c0e02c2e014508142c080750035400c000d000e943c03440040000400e044542c00d00c09035a140710000c022 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 49054617 1250 49053367 49053371
    0x3020310091e0c02030a0507020913141e010b01020703020402070303150602010501030b0c0c0d0807020106081203060a06030b150702030111030a1401050a0803040605130e090f060601082701 83
    0x70640161612580c80b0520b40e2005030400486041d02460503202d21000d96010b42d003052003400d0315540c018003200c0d10942c0c11698500f582d42c1d8a0342804a41c00701c6400070702001882036101d04c500c080041e1494500c100c3c1c0c80d0782255411a400418240e4881040290040c0c0095200b000181065000f90076102d11a00b404640c07012990b030000e984000c954000c00050391030704010014840c007054003940080e17549030198a800707403040c011030795143c90302c180d04104161940001e620034404c0d403101025152070415601c000d581408400310940080d00d101e841004008400120240030b80704100d02c1007406002010711501400c0c8424030303070300580016a01552201d16083c0c082422100a511070350b110300b40024021070103888000c0d00d10f0144c00c1319010756490b48040c4465900007007520201c0d103682c60241c0d40c0b40754500e04a1a01c12103035010412044020060240c648804115003400032410012140035a480d034004540403001590800160700c21440350801506250340710048541d085000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 49055867 1250 49054617 49054619
    0xc1203090304031e06090f17041202120f0607030e07050d17070309050603010603060e151c0303020903010e060f090c010801060c030c0209070302092706060307092111010c03020d03020310 82
    0x1070403003a034080c240300700d0720701c411642e0034020003101c0c0c1520b1405223038110441741424104038035143c60303110400c0040d01c28500c000201960031000c0240311504103000017030f80c0c95403d000d04060050003498822a050340510f0b140801e0504010b0b499003d400c1d00000c280e1000480142e04003480d1344540c0d019410130441c141d0100e9513407a1400114000d100c144d0340050907034030702406405509000f50204000800d040e22000e40c82d50303411142d0b8080c203000c0c00004c00696442c81c0560081c86030000b1140c0550802190400040002c01d000307105104102c0951015500d40042688400003040320f02d01285000005004413441006503694691080c10300c104040b000e50005030b1216011101c010001e50001154040c2e0304194012082105114114226010385105416004e12008000602401c00440040d419910030303c0c1c4400200200c50a40ca541c50703540402c119400103010043e01d0301e1242c61060141544240440c81032603400d540585034801e00304004030047e500150403070324030441c4540 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 49057117 1250 49055867 49055873
    0xd0609081605100516020a0b0703060305100912090807031104241a09221401030302030703180b0d0f02040801020408010e01050f041a040302070e0703020c1203090304031e 75
    0x41000540620001c2c98402c2e882c070a43c80c141c440040007a6010030283c680b0305459500001c90303090166101100c50392555420400b103000f40020b5002070074911507250741c030302082c02582c0640d07507981c003d02e401c4034032039071010702502d40c4940ca00c1a030f003182d4400c81c2c1c10004241da980858030001c01c010700100b0704220040c40160380014002407031461029138182001403e03c40441111042102000b2a0074003210340001562000f0000c0b1392900b81c00c02c0617007102800c00a44c00041c243c802d16000041303d503100c0c10002c0d50f83c0c0014008402188041ea850701c59160b05500c404125051441594030303040310100ca03000a002c2044203010010340910000c1040f51007800544082c1046100000d10841c40c04522400d582c0043c1400c0100e942c1d1205201c0800d64061103001100c107400104003c54546240483c5004502e5001c06044a4400e06000881c1ea060b002024481003000031211504010724041c681407006880071042c66000304801c000040d0703c0c190704030841001c21140b84901d25503403 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 49058367 1250 49057117 49057147
    0x5090603010305060601090504150e180604030c15111801090801060b090103050f010e070c0309180e0c01031109130902060a03090b0c16060b030a0f150b0306060d060908 74
    0x70b0030031691600318130100724036560702450300d500401d0100ca041c80701c081070085005550340380d4050f40c00641601400180d101c011510044084902c80084a243d8581070400901280312a9030444620790782c1d03c41109560528018041c4d42a8218074982c5044820b00038459206102482541808a204000205880c080c42050010203021800c29514030911700010120f0f44000c10300103002240390300602180c8010b801c1254000c0c440c1c00c00e0001c5007028181501c1d1034070280e001d20f49100c0f11010101c0c1303032800b03604060103010040044881c0b06a0b00d1005409803050071002100040041c4000605c80c500040199801100c49500142d400e03d00e070003040581d808210220b0209843c1e8030703600204156070a0381d640c030810300400309042040f21481c0e00c20940380e180b0b01800c1c141d00c90710741028588d010b001c2c0c9a1003e80c00b84084882030007074502704098145011201c80c01900c1c0441c80340007810046495481650000d0812030709400300c4d50b0301c000402d03c40c08141d45200061002e00c1c00c1040b40 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 49059617 1250 49058367 49058369
    0xc060702120f060105030114040506060f060f160303060605090306070302130801020f03090f0a05060a09081b0a020301061a04050402030c0405030d020312070c0b0f0a111605010c050403020d0b0402010509060301 92
    0x180043e040660410040c50b0a5450300e02d02e40ea622641d071020440421404210305820040c1240d040e00010401d1000442c44d0103010002240b8040000310150003100f0342185200c154820b480c02e2040c50fa075640e00ba121401120103e44e00b41c0c1020700001e440d1807080e4001d00a0745903203900c004585032510710a608a07042140b480700910400802d00c010b400d01000000150045000200483e1600d9501c0a80b600e1001c0c0010b148107840f0300344042000f00c840260744541b5480026040f40101c01210603a42e000011810385c001e510303042d000301c0e1022409680c820205854020f4034902441d0000b4840254001412540c80520070302022a03590743c2070120540c0c1400c0d99006586403085090080550640900385509104180384000001044131101c2a440743c0c08412210165480100c050060080c40b0030001e56107000140e800381e42c1d40405581141d150158000f003140100e4848103641c107101d9400301940c000c034039141401c00140c0020b80f2a900c544103250060403c8045030129000c1c0c0c0003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 49060867 1250 49059617 49059643
    0x10090201120c0e0f03010b0a0306020304020a0302311116020301090b0f1603050712020c0c151210080a080f0d061401030b090408030106140f040e0106200c06070212 72
    0x40c02182d0001441c00e0300707000401040032002008035008407c006003880c0e00a200040c141c0740c01200050666441a029500468014115480f14110510002d14100581c1000c068208a80b0000081c1c0d0741644280380c0014554442d00749480d03104442458007103442001203a041d900d82d582200080d0302c083c43d481c001d507081c146035040c40c10700c0c0c0c0014902c8000041404201131801c0e007040100e0f0361081240c0408480100b00617a80c0c02c811078040d003044a00308e42103822058a20403407850755407050003462007691f003021310001a01c80d07014071a204029403140c0d00c0107a1000f0b803000003244107000200001a440b400162038011501d0000058600642c81640c20901002c040021540c240c0100e07000c2d9042201c4082e01071034140d59503801400f0600800c0b0030000181c042d070264090103c1102c0e4044a80751000340c0743c607a200700b0a214018240201c0000030050300c80c040045010024a91000020310081c0000481042c1031182d01d41101805a0384000c4400b00171100050034440da00060032 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 49062117 1250 49060867 49060877
    0x2010203061804051911180601020705010809060f071b0c030209010806040b04080a020c06030901060302120708030409020a0302071a070e150313050a02030303090d0e1210090201120c 80
    0x41d10004000a8151041454918109500401c4005080814440c00030401a5044820340c00241054513044809100e41604040c0350b0150000030502c0c284a035200f514240c0c00c0714089500c40c00119000302003903e59802560102002c80c0b28001c018004c168001d42c645000184c10340c508540701c28860462200380d660b2840d189060081d41840705640d409000c1030b0b0b005041c80d003032554451603021001000034080090110b000c2302280d209021110321040300604690326410421540381c020569480100e1090000c000c2841c41030343c02041110480d40780c80e000c1c500301881c040980010303500108005080541c04c10034040059200d014508003080391515040d00303450104c901a01d07070303503403001802d2003481178011001041c94140104c81c2e0080d10b040d81110700080e149481440c101e03100701e0003507150001000b0004a0040090321b260281d0465940c0c0340026210400d1090112000c1d074420615009070301c0a0340b1041807500480f8010303106241c503110001d80003034403004443e412031486000403 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 49063367 1250 49062117 49062121
    0xc0e010e1602060a0e0c040603060f051b0d020306030c0907050a0206010b091011010921020c150301050d0c03020310020904060b040803070209130606060305010e180622050d02010203 80
    0x480d03510103194410001115212410401c0c0000703980d40c60010007440c015500c5458004010405109002c5507410140c002c0c840b40343c90303240c18000b034881d03082c404ca415450140001d5000c04440300031600345480c0d8a03418031704507107200303100047d51004080542500c00c140b03603111562151a0850b204080e40c0c2c1d40d158450881407002428035106a00c4200f11420500c9204050b6a98654400240d081400c024180c3c80c0c50a41d0345003d412511400f0b07010352000d222520204030018020030150000b80d0a41d20515004810004421130b840840c1f16481c1003400140510b08100195840c00e9000351074181000d03a03250300180c0780c05c0310004540c4d405a00443d000744241820302a140103005400c040d40d0031b050030300d8203140d5603004142010380b080c4505004902c100340700440e00079038582c00210a01c40f6a0711484c000e00606420b2041200541c842d40001d46404c1230b2610f205100f4409402a00c000c2d214244144c4042407066844820003034105a21400203808018024020056800250300d034 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 49064617 1250 49063367 49063379
    0x40b100315090b100806060409060e010c090f060203041d0402010e0d05010b0a080c0d12050d1a010813020312030601052115030a0b0105011d1306140303070b010e04030c0c0e01 77
    0x83c40740a40ba6800e46162000203201c1c0d0701002c542d59a100c02c080d035001a0b0388505040180141504540e0284c041d4038049103d19842da001c21581c0070303a0010320f0180c1403995192012070392032140b44102840001d800484442c0301c0c0160110310303040781c0149491650707030f0b14141c00540c4105100f202116282c3d5240035659541c2000c1d0140c10080c1007881c0a0003048030210003041c1401d010550003090012190420294280200c050b110390420715102000083d100c1d50303950080900c1a0012030200f500f00001500781807809098948055000c2c01500144592030f81c031400a0b000070b09024180407040c8031020980d150302d00caa06000041023a031007200e04000c2d0001a0a144500c60b560094002680b240040340001900504580007071a040403100c60105440c1101208607888941c05040308045241d121800d030042019100c82d48100006030f21043d04240d924415142d0051442e001c070001002100c0301003488680c4030b4005d041c0884001c416684510320f9444a070020403207048140c00601072 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 49065867 1250 49064617 49064633
    0xc020303030a1d010b010c080304050109120c0302011104290f071b060e101404170c01030e0309011209060902060301080303010e0c031003080904090506010902180a0e040b10031509 79
    0x20b603c660b07402042082c02000009206100402d8041c2881d100000400c003040401d600c5201e031103400c503c1200600039901c10050181d04900c50940040d8205200f41c0102605041250201d540132a40700403228241400c0800102c9001908a00c002080c0180c0d410035895200a01c00383c0d01ca1600c0c0d42c5040178032100d40c1d20340d2009400410811141040c0b54141d600d454201c40303450ba03403500b0440d81074118011071088ca0f00c02e41c1c200300e034244e20707152040700700d10710005c3c0024050009032014854034500b1043d142d52805500403050000301281c2d81c10300040d01950001581c507003c0c29000c904100642c0201e84a90720a91007050a944008010003401501000d26600f2042807100940381d4148070001c100e10031050b0001500300c810009001301c031070313407554465800164480241c40c80e96030b503401820000d42140004400641d040c0030404c0280c9450000402611801a1001d2a6448985500301d40c03420051062108591034600840483c00e079801d030503c480d071154000b0602d00824940404 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 49067117 1250 49065867 49065911
    0x6040b070209160e060d0603061d0c090c0f180d110102190b01030b19050103120f030e06071b0f0c060e0f01020c060307091a0405090106081005060a0c020303030a 71
    0x840841403c003c984141d1060400b11102c404507002c584a8103003850490040035140d000800283c6007401042184114041400940c82d1507400e462900d01328005101310030504842100a1550412000c1c100b841c601002e05035000d1044001400c178004100031a40080003442c0684180701682e820030a1581c1c104403103c8484c030034030503003c043c0d400daa8038500b5054041c040100746060040005640e5410b08440d40040c07060010107004a5940b402c00444451b298401c150000d03401c0c400c4641074038042d000381c100003030036600104440c4d80d41d10005c4070b2000844003c240b0f040c0003075085102060f002c2d105040c0716801410071040b442c3c5041400380c81a560000054000d40101c0d41d980681d0780c011909014904c1c0c260340c0f9903a0ba0b07070b0321182242c2c00300d078070703000031440302c03c806d4620303001207151000751090f614160b07078a44059032240350940f0b180e801140c41d5640c001e0803038400d0041d4201340e00988030321407850500017080c40b41139000a056410445070981010742e40c0c803d81080e480c0a8100f04 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 49068367 1250 49067117 49067131
    0x1911040b0408070b0408191713050102060a090b1611100c030605040b03060a0903090b0403050601050f0603040b130510020406080a0b091006050f0c030403030f1e080601110c06040b070209 82
    0x18505031900080c56200c450b03c02c0325003000e044a008602c1032108c07403d80000e144040000d06652102a01110408055140a101c0c01449082d001a070703445814880e2201240d001051248503542e80d121000706103140c1000d1341c0c200b080381203c00c070030180200a0106060112a008540030000c03d0008044034020790029100e1030070a80c030001251008210107400c803240c03581c04250300046040070344820381300754880c4c0e0304079400150020a000011480c01d042c1c032001c48814082d60130700010000c950100b601c001c0c2811500d50042071540080e410788030a040d1264041e1040030400c042081300302c0c2c019a000300c002c030b5410710401c40481c0191154400040c0101c80d0980241002c18800d0300c000514001c400500c440060809800e040c02800c4e11541a100b80403203544546034900104000340038240500814440400000304101445c0504c0d074010301680c82426a03501c01c4011100d925907000c0802081c05440e003071465030344800300104094412088500d0395081988144043c011005001c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 49069617 1250 49068367 49068389
    0x20703020f0c0d0f0b0907030c0803040e010b03040c060f0c120305040510060810021b07151404030203030a0f030b03060c041701020408030f07020315041b0605121911040b040807 78
    0x210f4001030004003124440c0e0b40005e40340c0070954840b080f103450004142c00107044100b1500000401040010003482a12400c0001040d0769a850034655000c0c001542c00600c80c0d00c1c545818400c5900c00c40c8403460000640c94031050b61002d80c1c903060300099040080d070000944a804010038014200070416006250900c2081024138080d0b00903182c083c0c1c129801b08550300092802d08070940320b9122284010490f0554071041d81c0c0d84440c0d001109902072030800700344002c0e014034028011209503001c8036005006503150906560048501d000a90b04660625a80700108804e80d181084054480c0710384c40b03d150b5441d418003d441189038007415414429070300400090141c20408019a064002404500d0781c0300c40d800c1c400a424a5080a0300c00e1040380707010204401e0101c1107080302c0c004082544400c0704680c880a0403070705031081024400301590f107203010610508038840c03034030004068960002400c005150403920749501991042c188000c002c00c0500c1225010310070200140041d10364 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 49070867 1250 49069617 49069639
    0x60501050612060123040806150303040308090d080d02071103010b0402070f0b06180a06051311030403080c1b0303090f0114041202031b01020a020601080c180613020703020f0c 77
    0x40010401801c5138100640300d50801c4403101150b4000c002000f5000c0c54030f03269511101103030b5840740200e61220f0301c20b86500100403181804011681a281c200855514108502c0d080c0b00206440201c101c80300041004240c3c0d002010740b018140180c400c440d401c4070b8051100405081d5800c1d03030308851046204201040000d620410341500090784041030820b0355031800c000450304109085024140c81c00d8504200b04030100350b1100303054501c201e90306094641409001c008130380070007140420500302080800c020031300a130324407588410301c241e00c546044234401c07444103464041042007043d07900120501030103000c140321005d5004c03281070081244a22080c0410050f400c040c202400051002c0724a510303042c4288101c452901d961031081940b8480351031268001d51280046100600072400049020403012036884411540104000c1c0b0304411103001d847d4400001d80410303804840d0301030a15011205001801a40e4000d4010305a030b10807182d40b10382031071404200c1a12581403c50 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 49072117 1250 49070867 49070887
    0x10b10091401110f06100f080106030804060813051b040501080309030c010c060e01060b12090c060a031802090a0605091317091206011806060e1f020312010803070605010506 76
    0xa224204070400d203030103001e8100300311000b42003001280400d4907600800c410003800c00c40d14400301040710392441d1044c030980da8500b0307120b0881d0b0035400000c00801d020007080044500c51001d4030740016903000e503610300041581e2540c0c508055807081c401b0b082c0c81108242d055207094800c043c01040c825014500d8940e08900282d26001c030b91081700d050015040008050100c1503206c0c042500c0c4c0c400003001070585405c0d1441040d000b0041c00c002100e503403030004026200c042214050340360090078240c101400000180c018041003d0805000d284140c4040c0150b0740d240030440c0184240080080c2460500c418080c10540080640440d100c0a06900b00007a2a201405108074959045503490f140440c00050100703500401c051901e108400020500901c071104510740311681c0c40781008031035607030a420307200540d0301011680d0081c1d40030324410107154468403c0700d40903490302c142da1412040304203034810b86800303801080c02a8408280c16007040a00e114541c0901400c442682c20486811 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 49073367 1250 49072117 49072139
    0x60305030a050f12070c0605060105090a050111030c010212011d07020304060c0c0503011a0102012910090b030c0a0e010806060d110d0c1d060c030d0e0717010b1009 72
    0x100010042e000441c414209900c1d030583e0010910b440c1142540d0a00b480020415813075280203440c0145890003042da550300490486400c5400640340e0800e680c64203005554202210712501601d0100f0040a80170500031b10003400c9403109880c43c21207a5061610507070035004520307600c2105002ca8810321003000d4000040d2022903c20b0310b0000200c100e40e00d00000340f0800ca51000744c00d03600b42031201d048010b000080904a0070283d000b007200042c20410041c5002070311200d9410b41e460030107050598103000384d1850301584941030000c0d0180e0740741c1038089203501c01c032070040b924200401e50725102e56000044904445c801d00c0c24007607030304004d000981203100e030700b80103400c5a90300c6811401139885407054a22301c11070b032402045841c1c216030001d081c0328004100701c25540003002155041c7e1401c0419030b120301408100850600b824240c0041c0104480f0811413443d1117442400968420226504501c030480200007017004010103044c018841c8040c00480306214a590003800710036009 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 49074617 1250 49073367 49073377
    0x2010c05041215050702011d0d120b27010603060e01050f04020a02010e100f11120f04140d0309050c040b01050f0f0702040e03030105010f180e1e010303020105010f050406030503 78
    0x10382c0d0a031100d200038a0034081c40340c86801c3e15110103040c901080400307501940020161245200508641002ca504035501c6001041d40800442c1c010309401046440e198000490f60740041c20700c1c3c481c004000b2803e00f03014030060460000042e070100501a0342d5040c0a540c00034008140307000125410600010046041e0104c21030241c0da0210342058124400d400602c00411104191a000d03052100d02d04041c082140505160074140030034420503a80c40c9080320120a07442e641e40460b80c8404c60341c400103d001400035645161150910843c462003803107444a08441610700259242c8640b40060900d91008a020310503490440c84440a9800004403050781a0000400340c1d10380850307c0f68021801803c41c042c1d00540303442808805914000001c6044c0d800989481c02c0d02c1c1c403140b000300c5126141d8030380c08064103100d14040003020036143c645a006101325001c10040040540580c103000c50980c0251700503912040108140d41c650030941016110136030382442600e0460b16010303030b030b4030034 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 49075867 1250 49074617 49074629
    0x105090c03090307170d060803030105030703030c02030708060a0c030c0f0c02090a0e01050405010b12120702040b0402091c030e030c03030f090d050d210209090f04030e1c110102010c0504 82
    0x800240b80020520440e10741ea940100c088249940c2518036880c0c0d034004860002c2da85103060300120b28800f0002c1924120348004004049950459500312000929490228dc051083c2000414403400500041e445a1b00d01e103000181815003d02c01026030311040d120005101d04100390004065011051010054040d5804040d0780c90700035100c00204048003089c40e044d445c2c075041c80100031064101c0382101c44200c0e00e10704c01e4205002103648a660001e0465541c403000c000920050400b83c0014454110050005007450954030104000901040c17440800094401919040542180f142080110141c00030710311000c503007000c0b80c3d6a01c505117910f040803c011a0880300c50740c40407201000c0039070209c1561468600c050020f4008a9803000200700c2c0c034010381044071001c4e040d1080d981541703030003428050b0700d8494881a04503268080c109074100301410300718049039114459007005034016213081d15a40302542c1001100d00c1c068015450440e41095000d60086030b00c102541d00b0380d20 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 49077117 1250 49075867 49075891
    0x6030f0601020f0f03041d0108030a21020d1b030605130e01090f050f0607030b0105040e0615041d0c0901080f070c0c0e01230112020f0f0310150305010509 68
    0x9034040180e10746001030780307034007154401c10711a011260004400f5004841d81c2c0c098080401d00154840342849209000c0d9149039072081c058442410b22905802c5001c0080b112250905024103250806a0b0b02002d055640703d80c440d1600c03010030303090350002044620b07039150411040b030a000000c1c40307441c5446009400310b9280c40e000f580340c810279441160341c103034007055a0b852458980b501035102c04004204401c00d00401001a0896000307004000140405039111807815082902d121007211014000c0d64000c03144040f00040355130328000801c0a0440076442c20481d502c582618198030800070701080d8150f00074030078007610383d07084404650841101015402d00e696001011540c40c00c0f00d01c0c000e08901c8094400044620840d06510f06070303080240c070308401850f0343c0640e2403070000e40402c131400a40c030764071080e03445e00c0303d54090443e8461080500c3c3c981619a0480480390b0000c0c0c0341e09860301202e020400458040e00d0000c1e81000781820140003540c90708000541845008009600f044 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 49078367 1250 49077117 49077121
    0x507060c020f060a1e091203030c020f1006050a140f0d08070503030705030403172509031401020301050306130c05060a051603020a0b06030307110411130608060906040b06030f 77
    0x240d52014180c09055003c0c00381500c85041d680300070480380e2a00c190b01040b140383c1502051491145281c0d00c01c0c0d41802c0a8030300b07900d005603812402010000d0003a000c41c001c103507039060001c0050220030083d44000754080740581c100010070101002caa480703010805d000580365011038907100001d020f181001c41e10260f0f024810f04100e910b503c20000c004051f40000800c0110040d002000707140514040d03503a05411404441720944001d5040d110a21074a5106046000b400b03c0304a09003840319403407034203034402541c96880511014101c810150641d402000510460504000751684800000d000480104040d110000d0700c600600483d4040c680c00039103511401e00bd001200c1000c200f0005c800080b0000f800c1c02501c1f50313498882214120703c3d0002042207460000300340e42031240c00c8040403204103240700030407000744080300301c09900040c1030250702c13801403005c61020014a450b0b10340585a1402c0c001300044000003c2503d88121b280c4042c0a007251294801d8030783c805013480094600f6 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 49079617 1250 49078367 49078369
    0x70501020f070c0f060503040807020d06060b0409052202210703081903050105010e031515210d0201091e0212030c0d12020a020d080a0213091b0206040507060c02 71
    0x1a11503002841d0551400081c0340782000300d00c01140c821644911859801c941c0c56a004039468842958041d180309000c3c0440409890a5016118014400c1200140790740c0c0d41c800f045d801f500036900440080750b441007085440501c280c0000800498448904e00340805903000031604502c4c1460501b610000304000c030800c904c10813840300503582043c0e00d00d4940c10040990901425207500c02d4000a041c9000041c4650203001781011004005002e0404e000b41030100400c005001440070310118001c501020b0759842e0590500c0c41165411a550403551412240e94030f0074119003004030840e85000c50f04400701c0c5c10307919102191080c010300c4625800260000417510548088907858a000c005031a000350900001d1810703040c00d035515a10004082440f140d0100d000d4030007000c000d6005402c00c0d20801e80f088038915809112100e0050800114407a42e042491090300041340095803401c0842030340104031100c1d1245103161004101c60702d01995866220b14041c8200c0041c4081d03040144c1c11 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 49080867 1250 49079617 49079621
    0x40606030e01050f01030503070b0a1442040b01091a0403020306010e06010503010b030a02070501060e06150903100b010212070b010f0b0a1d01020f100506040501080a05060103170d1d070f05031002070501 89
    0x140000c02c4a071030301404c05180742c5420a014400e2455041c2cdd403a184495070f5042c443c05420502000c0d180201103003860b405100250030b0070070300360f810070110740800700310410f0600750b2401440c0c900000356111800c0d8410b00d032030010103030400300300c2444541c200b200c1c40e80c0c80801c82c0e06443e0340340c404580f26254104030301c02a011749080103116500340000496040c20080b9018403c8900b1142d032502c41c110180300a483c1c0c42005403007a0580c106514001c41c2001d25040800d1b044010b1041b54103d640c1080941b940c0d40108400b22842080380c0c004000e00290030416601a10200c0036452500340b941202500e01c04d510100c10160710600c500003500c0740e00034803500302d820390700605490541041d500000700070041210018420b030307e484004150035800080141c90a548034004102c240d080d521100b4020800e15100d40402c0340c01c1101c2d0000140c2070040904090490b0802c129114403001c400d414030540e500314a1358000ca846080045a500146a0708079854041c001a91407410f824a140 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 49082117 1250 49080867 49080881
    0x30304030c060608030319060501110a020f060702130525120507021624050a080403080a23040204140727080f1f0903050423040606030e01050f01030503070b0a 70
    0x604d4080401004600076042a036000700032030002c010071601d074961005680500c0c01440602140d0302030310210006040084c407100c050030000703156500344003981d400503c0c00c1540081c0c102442e620382051040d40c4d15401000c4900100d08141c8803121a44c82c03200130903245084060f03030395140c3c030b6401046141c1d00900401301d000312030440c034030003c540341c510b1400000b81c01c00703100b141e00044d8494800c0b5184100140c800c0c00b5500c0c0c0e2004060703181e980741240c0c41c2070050490050182da4000c3c2809010211183e601e102c16031403012003c503c0c0a00420089564081e08a141e41223048200024250f21151521361000c00d08030202085440d42d461031500320791504503251512a214941c004404002052410a402981301c44114443d42c0100c00c01d07030365907200040105800344402c0c0207401040d2400d13601b0641c280c1c0704030700003141a8001400d80b42e042e804030300443c3e0345602c3e20b140d080007030007801d600100c4902504025403450755103d5981c80fa55001030031942148010402c00344c1340d038000c03003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 49083367 1250 49082117 49082129
    0x6090609040201110d02030a02070e06010807050c0309040204030b010e071e11010b090f100f030308070f0201020c0105011e0b040302030d140403120203041805060f10030207050a0804030b0108030c030304030c0606 93
    0x24000c0d500100003e0358923408410310700054812040e00007500601500c41c00e00c40c24040e52802e03800d4884c5601070f111034200c503c40d01c20902040c801004203454030b00c050030045000348182410383d49401300703a602815010b8034002c20491800c04106c40040800701c00b440401031850510544100554100d00404c000141d00750700c00c145c517092204526114104c1c034044d4800c4106070302c65070341c1c3d0003041c031050790b1602c00200810405800140168001c000007a59080b0500000d440c0c03002910281d0f0844e0000d801401c10100041d540075040c910a0a4110203003883c1031a442c13901c1c1c11900001d944107040c0b032402d0100908a460705082c0d240010555005662180b80001c4a0751042006500c071380050107410b0315510200841f80c040c4209000c4c45020302000f6006002240c06e040a2041071218104100141502080a180010807c00c1031801c611300500b146c513122819072802001340d680c107900c43d11941d4424400d510003c500402282d40103503250806100c400100c0c0781c56030243c03003d6130002c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 49084617 1250 49083367 49083373
    0x31115040c0302010201050c070f020103051b0309060109050106090305070510030e0a030503010501080f0114131b081605070309090b03070b030103050607201e0f0307050d110102030609060904020111 87
    0x4403080110550001054a03c02d80003489a80d99040180750f01d4003480001070540d040340740a8202550113603020a0b00941d0f03a0b041c4010401d0601002c0c0d010790b0044c0d800c050340b5400f000040054049503c00c5901400726860110001459510b803566115004d000744c602c07a0b43c8a099040000d0301030b070300a0100a41c100292860140d26040c00350543d00309201d106c1c0498103020020301d46070040304405040e10075035881100c102c001e030010f1100d0b4407c0400361103803181d510016000c20130075103000010310400a9866680500e00302c403800780407420b550700b03d1003440b00510403500040c1d040140d243c291403160b1800600008000c000910f0007203141d00c0340581000000010003880404180300c2d00c030300c816071511141e000100841c4033007910981110b00c5581c11501800b40d03d00820990724220360042c004540c030406010300d55500b107034010f031011540e562047c00c090312a25081000407400003e040e0086045203802e40204030140c200500051041404800180071a801030203c1c9404038190821 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 49085867 1250 49084617 49084621
    0xf03080310090e07030c061416050c06040f03020a0b0a05030f0403020a0206030717060d020f010e040e0627030a020a080702030a0b0103030503010f0b0405130c1e0f090603020313031115 81
    0x6101d131612007500055404c03245507400803613258010400100042d0b0300c2e005180ca021001008002c070768004440450341c0c0d00a42e4544003160f86c03a10050b0000e00002108d0f54a201e00d03501c10000044020b84c064065114140580c03050702d60408160307070f400f41d6240100c9140d41d07140c0c54201e00b04000414000e500c402c012041c401d225910203250380d418103444001c2405500c4120030882210f00310000250302c000400e280e0b4500c0d501c280f0151400c1c007005800882c18000b43d014a03410800c1c105d4101c12410b15003103035180c015541692984600402101440c82c018503000020b454013040030780a02401c1c000540401151410030503444000e0f0080711080c3c080d6160700c1d0042180d4000e22641245411407030011401a0141d82103804941000303204070703009452000b401c009840c80803c2041800740d0061202c400c1ea601150003903200e02d807607842c000c0300f00740c0101c060001e01d00c0f0340052040501c18010030581d81d294601200a454050400560509000240501d0003c0001144400e0300341a01 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 49087117 1250 49085867 49085891
    0x411010e03210901030c110c040b0117090102090f0a03170a09090203090604050c040204080a0f06060e0103050c01080a0501081009060209040c1e020102030402060304120203041203020c01030b0105040f0308031009 93
    0x4054800ca43c4240d8040c003107188034482c1210001d801c212014016081080f04400c5031920380c0c000400901e060400002030341742c00039802051202291444880c1e500042d10088600d408000d81c0b0551208442c0d0100003030a54a0b26176000700442d0000c0030340200010302d22100b030f0140140310020004c40301c1c29903403490002d1449403503190544003200c50f84103003d1810510318240c001d0320207a070180c1c0010b200c6640d07580c56041c034414008a041c4d0b00e071660b0700000314207400100b4000740a94041d400405c5840c841200040840c94000c00c0d0381ea441c1d00e890014044c0c0e0f4004a49502d602c901c540380801e245641e4142032000b8460340c484680e00510f007114680c0075039001500c049111240890f10b00300c100301464181d00380e00c01100c00961003801000000c0000d61010700d00b4482800b98811203080a4032004207682c200440c05043d0b01503408094540501e43c0d050141c152120020b203851810f01d46000030005c01a1101d0100400c0d00e2000300008020b11601d5840200901d085101404900d41c469 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 49088367 1250 49087117 49087183
    0x90c0516050a0218071b080405040905150f04020d030c0507050a061101150503030a0f0c0c030c032006032d0708040507090c09090b2101050603010c02060411010e03 72
    0x82401c9005088840c0741340300c030740000e90722248140746130f84640300e000d00c141280800c420740000f03045070703401d00500001c02e07180c880d0711801010707600c03c00080195035490070104103440702c001c1c107400103d1601001c0100581381c480500d120b165050030025146c600b28501541401c3d029040150400e41c00c03500000c2e0240d0007115a841200240000c02040e52601038010205c21036001d110f405500030002d0711380c06c80c85258055119100c41c034050303004101507510390101083c690300696030010381c03c60074800d100a81c40c928040c55a20041c03401d01074000700c04208940401050b079004178241c0a600e045c44004d04030450080040c21500140524203020040c059100036501a00e461040840104503003001d88100d501284054a0b80052189007110704006004402d862641050001c1240c05000020400e0004050140e00010409150000c18103085450b0110203604540c41300d0240b1011544590000041200a181c07a136101690f200200303140c508400c4001924100380d00b41800759001e80 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 49089617 1250 49088367 49088383
    0x2041104090b040203040c03020105070f140a0c060519050d020f070f1101020a170d060909060e0c220c050f070303020d0b0105030f0a0f0b0301020a08010812040f090c051605 76
    0x1610100a4090800b00b444100d0100301c40082a10701c00d88014405076003d0b00162400501c00e400c40c0700c484280c0e0340d411012459400c11005680d00102080302040707401c0c915000a0a0300d0300d81076041c01c40803c502038001c540390501600b80030000034103c07903252058040392001e840700483c082d940c400700c4c60000e164000c0040c003034032090581405510f040d0300c041100007c042e04804001c00c0302c0d00000c04071080b40d004055014560341d8a0358000b03000d07225809607880030343c0103280005201105d04406400e141e104416240704a410f80c9070000500d00071100d8880d584402000010b00918001081c1e0b40c9218094444185803008620740e4101a450340080c080d540394400d090015002580054030f003400151116601c0ca64100300041c07808410758080100daa90b00b00c804244d10400402003822a88041010030004501030018481002d040010700d044105041c40e0320315180c6024410780080b02c0794000e288a0b07a8503585100d81039031103101601c1c1c22382c20b408a642c080d8142880d02075940c40c01 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 49090867 1250 49089617 49089629
    0x51b0313180509070e39030915010b040b090409020406030f1101080105010509120a0b090a0c0b0901210917120a0b03030412020a0b04080105090708010903021c0c02041104 75
    0x2c10000524825010455000711442011084481d40712400d009014040d61400012540c1c80c4c0510380080c013140a10464414822144180d41d078200050301c6404c2902d41500d0f0074481e00c41800400414003e41c02700e604581c0f1150748651160702d401c00140180130b804c00302075030141c00c0c20030110a004c0b070769185202803441801141d102d000340000550f80180c0034410702d808103030148030004103030420a4103440481d11900903942205100e80e01c0c01030407041910f02d910b00da80000c2c00b400822541249400c06441c801d180d00781450364000008200d1000764200c072a003100e1500c290f50810501d5000103400030761040c030044030b2502400e0003d90a400a154400124481344023140301c1c441c4620500c03401c1403020b070286240c142020b07210b40f0a46203c82007240c11822950000a000d5400d101034000350003030500100b050700317058000900e4a0404d0308143c8403640b501c0c69841c002034000171070301c00d00180c00c952440b4005600780d00b61018818224043d4009061500e44d0411305c031814000c00035205 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 49092117 1250 49090867 49090871
    0x190207061701050f0904020301150603021306030e070b0a0207080703290601090302060c03040b1204060b060a080f0606190e0316120609050c0604030c05030705040c051b031318 77
    0x580038544074054028421a81c2101e00603005004500346a43c2c126401030028002184869183c240380800c02400d5111100081d80450341c0810300b4a00f00703400006000514060140020f60018107440d81e20600c5070000c4000c0000c0e01140c1c4a0082c440c0100070050302054032851a81c0f03042881042d000c29060070044240c01c04c0308115030304091520b83c0a040180d41d100c524500759400e0007a15801750000540038807050000095040d802001801742d004072250071052402c0a10700002640d0061140a22441c02400042c0c801c1e41d01590160348040c00604005040d03c546000c07803024400c142d0100d106600040a440115801100d44520110190b003100d4440c400c43c40600000b4080d4000c44441c681328641c41004148690095954503002d0803d403038104034400d00003265136116074412242c1c2c501c4450104801e24041c0400700050006a4003849028001c807801403c0e4421030144605d014404003146410300e5040055400e915441c5901c0e224107500d5607594000412194200c580041c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 49093367 1250 49092117 49092137
    0x1501030501051b2d1b0f0106120303020901030b13021306020705010203040603020d021b1609020307050d0903090b0a0504050310020c0a03260c040602010b01080601090b0705010219020706 82
    0x5203003800082c9202d04002190341480d01101804e2082c040c0a1081080e000801007030143c1c5208983c018101c807103101507102c14401c800700d016803c001c1c441100175002d925000d41007111003001c42e042c1c1405a81484c0050b030307031026a0010380082030900300898109007045400c15034042075600502d880c1840302400d580311541d40070100d940f03940c28000d041c010380050101300180c6000350046d02c001d400d0050301508050040412400c01d50480000e203507a0b6000e042d48041d0b50500c032050601074030300c1440551a41c982150083c045105000d4100b82c41a034991241050520800b41c24002e462400901079603039103403038002005904580161481303405140000b0058668520850303101d00c100c075001c0d040558050318140e5055400c070400103807203840c0e0715000c07004c080e481502c40d2280000480700d50300c03039060440c000e00311840b010119050080400600200382e8100c1c0502040b100c02140c00750340c82140b45001030180c051400405030035081c807201004020b8000c034004062300d0065075840c4002c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 49094617 1250 49093367 49093381
    0x8010f0b0315010b04090f0e01111309020901090e040203100c050901030c05041a030709080a080d0b09100e090a0204060f1d04080a050306011403040c03060f020f090609030a05150103050105 83
    0x16402c00c2c801c6070070303da004110801280140f03801c60140c0c56801d180010b0390040c40030159084d2144019420110580003aa43d103050b50100a0b1801904070309004500700307420072002034506101c0d030055494145508001900315642001020840c0350b03c4c02c01404444400000a041074210000c01e034040ba00300a084404280f142003a5812908103501840300c5169500031030900390300260460007001114500030462803001c0200c0500e041c1714641c1c1c103030b699083c80640d2040310180322405114561300c1050004100e28071140c607054a50b031004141e616110000400d1506020980007504142031440020340392616022038811100d1444403a01c109050b0300828a60341c5084600a104043c2445404419841803002e1076009a0604140615920410202e07a8a03081100e0403500c8080c460814410000d4902510122104052040d0708080c00c1c0360700e890f464010414420f000d00408a0301c18050356041014940c4030750014203540082550700d03956101041e0900041c1da1940c2401c0100c0c201c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 49095867 1250 49094617 49094653
    0x30f0b1c05071401080a0207050c09040803091c0c03181a030103020a050103050405030a0c0305040f03120216051806060403080f0a020607020a1a090a0b070c020a0e070503011a0408010f0b03 83
    0xb0f031034141d5680760556035200324031009403c002070994480c4a880c0001c0721588640c40201d000b0382c0104806601d1780303428031281d0315151001d01114410620804c18034966a0000301801060341e0500301034401c0b000c20f6502c0c80c0c42c44000d0707000180c091180070700c3c84003824055000b14180d0f03000b590015041a2100015010b07243c090740c0c0103009900030010b10411510601d85803080b24440d00d403240c9800ea5a00d24454500b58940040c1d030080301e154220816680c0400c8980f0142c0c00003444014420f1070071000589003080e84800025502c003000005103141d998504907006076500a8903191224208891980660041c0003c80d000d8415000420000343c000110949000c1d808503482c041c203c03001c000c03c640010040e042d40c01910401290790001003d1054440c403500b40d40d6507012243e80c1c0340c010424903564580c800d07042552000280f00029520004480c103640e00108507404030320007035807002124490ba5002c20090b528000e224022003906400c5510340700c8044045504201ea50104060 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 49097117 1250 49095867 49095899
    0x201030f0b0f0d06020f0f0316090f060e010504080d08042003030406113d050903030708040305120108060a0b0315040b090102040914011a0316030f0b1c0507 69
    0x80d220119042c9481030385442d410700e42c4030030302c03909001d07081214501800502c1c0c0c114528840c0070540201c01c005503064552092003050340c3c5468120300c02e5103004280341e9484c040340140707000c00900c4940e0514a9018200f181e00a100d14800c03242e2600031750b5001001c54000340d5003261188a146802180030348058110650850000e010b94a802c1c6801c100f5180086017042801d018029111038000d612403081d0021125905d4900f084403040d4000c84054400c110350b205848400d10309410720441517000000c0d203911103424206400103890707500381a1058043c84c0a0072000b01c0521002042e5070801140d02c6008100080b414003810310907008140d2545007100c034000220a1050025001c40c000325400e90f00070403a00001407400d070b11180075606840c622501010302690980040101c40c084110a0100140d010b031000d007507090410500c80c021002d6000402019200d50310303404d0010950380110315103503005040c111046030343e540309400d850303054406807074501849500003030081c003030130400c1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 49098367 1250 49097117 49097119
    0xf0604030207060e0409060f140109022d07080301030501020d06060504030f0210031b0804020907020601030201020a0f02060f03150307050a0f181506050c0f0109110103021c05010906030201030f0b 86
    0x6500c50403d80101c4064261910455001e0741b69420440442d41c0c500c200140368410080108110300002070313940c04101c041c0d010b65009881000301c00c4160b68488500750881c0c0c0c0c48401600000102d049224641c06008000b42407840004000810070105500406218003201c2050250a90745c0e9003e0f00c05004a1001400040d010301c4514010f01d441c020641b1024440d0800040c451035021221041d86601d0803071b400420130440500c0300750b01c0d0003014641d100300107100508603581140d0000307448840300d5900400c0e004040318003504547e04d20066448aa039407010090300e919200c0c01c0c08c0aa600f881907018080e004425010583d03013010848031080d43c08030701e20800c4c50340c6042d000c250b99546040003d1002d65039a9000700c1201d41110380c0300014141d0756500c54850444d6140c181c240301a100410040c0ea03d4230045100041589000c0c444001090030011b07260081c18150030014440b0000ca0081c0c1c0d498907001242586031139000c8416030b4001e030b030f08016014001c08500704540340c0d000a2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 49099617 1250 49098367 49098373
    0xf1818030a050406030c02100f060303021203060d2405070c020111010606080105010f0207090905030909010b0705070909140109030203031f051c08072f0f0904060209040608060c0406020f06040302 86
    0x113002c4540690804242001684100c8000c28450b04640044403039252001c200320b034964804009142d41082481348003541520010300d541010400104510341e6900c005228403602c20308154441c4c6e11503410040c13100605400e001e1031600090040001d180b1f190308a000c40d00d604090000d0300c805116030800c0d1000b0b81c840c4601642450019161882044070410441c410a8004643c0c41e00c14040d43c1d000e070788a10021a1030745000c100700000c081050304081e42c03600d0140161404604c0000d01320302222001000021078003043e080846602c030b003103020080c042d03080800280406600000642c414041c403100784422030700858103e08601404d03c10242d05c200d816000394150b0711003206894040703100e8030486182c03e1b01603854003e9850005403103640d41d240101150f0446440321120584904110350700c0c06540f681d0300c00912609806030002e03000540c0400d00c64241c0e115a48003201500c0d03078504488481c941118007601d40e42c040e0141c003005009003884a07081120024901d40510741c55006 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 49100723 1106 49099617 49099619
    0x41a1305061216090e1009050703060503071a1902070f050a030206031b0c100f0605010f0c03050309011104090b010201050f06010c0b060f1818030a0504 67
    0x254011541001103800e8600104000da0303103c042d85481400003603181c0011a01d01c0015004551981c544405018100c04074580c2c081c11a548554240910380d20544220141c546a10505404d0752003e60280580320300c03003858031114002c4000352400c0000d10030640e9071941c41c4540650158001c0c01c01800f44240d11a19600a07000990310801d0b45031071a4003080c0107203c010b200ca01c81300021080c19045543c0c500c100c4881c3d1f421901101c506100d41c56441c402418800a00c2c140c81d490900000344a5010b0001d905020146442d520f2038080c0da504c09035102d0740001c0c0f15900656860b045c810984c2c03041d4010b040a01144000000d00008030b0b4000ba0171208090540d42d6200341c40d40420069030f0f88000d4031641207601c9141d107102038035020041a16609a0401c15900c0f00e0400e4110101003101c0501a100c5c40c04000e40003010500b01002c0d544a00c11050120002842040 = true := by decide +kernel

theorem cover : BRFrame.Cov 48920867 49100723 := by
  have h0 := BRFrame.cov_init 48920867
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48920867 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 48920867 ≤ n) (h2 : n < 49100723) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
