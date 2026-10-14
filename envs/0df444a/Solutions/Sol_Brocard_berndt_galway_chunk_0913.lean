-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0913
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:54:49.09057+00:00
-- url     : https://prove2.me/submissions/1e62d838-976e-4f6c-bcf1-878d5c682f37

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 164028776 ≤ n < 164208633 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 164030026 1250 164028776 164028793
    0x11509030b0f07030605030309130c0e0a091b0c020607021216080708070801150e040606210c080705060a110307020910090c050a05042310121b08060909 67
    0x756034030110240c48a02d42c402c00c0c0e0701030002c441d400d07114510042105402460070000360100241800040d401c0e00e04040740c482d4200c050301840b503072411030030707650040210741d80c80d88801c0c0b58001018090b520180584104a42d00e182501690b104041c0720f5004041ca45811000d03401e00c0004480741403404d007a445081040d6405c1c0700045805006080075030000c0c50101c3c81c0c01450351800e4540d912600340760345071030480400c0d40c06510080c019241c84490030812a00c480c6402c0b0001c00c5598040844c41c8004a8048403000c03454a002440e14012810080000d0f1078503225a2102040c0c441d082c0d026404001040401d400345440c110203481103820b49041601d603070080346115200715510600c400380743c681402440c1c41481b0b421921811440c025040451180015100784038900590351019040e40e00101044803100000c0f8100ca8050806002042962030141a52030301c01c040c030040c141020911040b085176081401141e4455558840454842805000c3c07200b002410502090046014 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 164031276 1250 164030026 164030033
    0xb0a0509090d1409181e040c0e090c010e0d081225030b0a0311121c1103070b040b10030c060f080702060f012607080c180f01150903 58
    0x114500c21404400901200c0b41181c10082c058948004807418001043c040702d10300b40c0350340c03010416400c1000080c800716151a590351548075025904000380c0c5a080d004c100c204a242580030341260800340e4205a0741c0c50311049280c9864003001e80e2400100d0170314040078140f4082c03180350700b0107000d038000c9440c7c202c1d00c0040c0308441100b110103644a4a0841400408080c83c45d800120a0702601d002c11200da0928001820095103101c090512504140b088815559440002d40381c880c290084421400c0c0c101e02c016580e0101358804002f00c0c020060080ca41440403080b200300d1a4864032850041d6070f2a41c07000c011900207803890038000d50190b000700011708480c161402030100b540300c00d000100c0d8640001c1031100d00808490854121200340500c0d609400c801d281940c2294a610b000103955540c0c0b40c030804540121180b446c8624800003c0380c0c03001056800102d501079802d1000030000403126509110280d5441e54141c42c4c0c24010050b1500507465201c65804d1484c00c1d074840d0f540e80d02c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 164032526 1250 164031276 164031289
    0xc020c011d1507060b030c15031303140307090602120a0e0910080304060905040b0a0509040b0c0c07030c1e0b0706110f070303020c060f130807050c0306011203080603160501030b0a05 80
    0x11030440780c20f59500b8440c5c14500d8200000c0c104d10400b21116030381c483c801e0580340c02c1d6002c0039242c50f903031641c6400180c040500403070040800c0054102219101d1818090050000d4124031882002d40200c8001d2004044070f0300403150819013940b03408140010a070103121400000500c00b500822030141d01141e800070510041c8010f10803a034500200f2810322003003000320303840006080e03c12040407404025944626030801d501981044c04042c03039030f9032615601e29522030000b03001120b000d0301c00c2c00300c10440d0710314941040d110a4035070380e10400c40c071401c0105070400b58003418115260512005001038000d80101c0d410814580000e0b04080d1880b40152440d08901000c90100303802003000a02000b04000a962000019003018160700b4034907910800f102d64a2400303004a48000b950100b808402c00103070301020001b400325409580c0d1060710754003c000b620740840000d000c090206016180c000b4401c00a84460705800350b245141000550042407070794460341d08950700902c005490360b101d5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 164033776 1250 164032526 164032537
    0x30f0812010b04140406050f0904030915020304060806030601080c060a12020d0506130519020d060b030127060b1c1803180e012d0306020307120c020c011d15 69
    0x4040d2151294107050130f000c1001065103456000e28a00070080102d982d03100b8062012402c1618688000d4460341400c81d0302c2c034402c1d00005181b801c600440c08070154000024400c881182e941c0a9064482c1c9082580b9450700b8400d0f1802544115001c22113480c2c81c000810f840e40090502d01d00d03e0b113541e4054816a041428600003086d944c600b08945070401c0c402044881c08c03554410000c1c0d00e012400100350300200d5803440c060660114440398074555039880400684942c01d1810345960b0b452600381c604c080d200604041803608c089000f00c002695004020580308090512403c06008010b07800c1c0c5080181d101e440c040d03444003000c00c1040d0b488030b549140f860180e900e0001c544d81465600d182440c00b81e00040d003507024800108103c12000340000400c41c2c4050f2038540100c0e60500646140040d500050322862002041c410042d400000c02c0203501c050102c18041780b5164102030ba181c2d030007100902d002c10b280e006a4a201c001350030071200da0520090602800e00c00c1c0da040c1c480d154004 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 164035026 1250 164033776 164033789
    0xb1b0f0d1e0e011e090506010e09190f170a0c030509060d0515121f020c0102040515040305070f080606010e041e051803090d0807050c0616020a0816030f081201 70
    0x4907500140313402c42000c1c007103440ca203c0c240b007031181200310390340e2a40e80d503030500c0703403002c08080880403500c4070400f4015840141840c0241c08810341c05410036004d2502c08610403150040250582d0000da01002c2c180d0359070041c0f03038a64445c1c2d007959860523a0203034072040c40164004000c0010358425900ba01c13500d400380389803c00800313482941106100900e240074001c8800f540c00b00443d0f015800d03034410b4000010400840141c1c541505100c007601a0143c2d41107242d2101010804c1001001e104000c5e00840780101c045500c0943c1c0c0344050120350b4154000c5c66425040b90002600781d501a040b111003a460152001a61222407203003084cc15040d015400305554881082c442d004011880d00c1e90a040200061483d04607054002901078040d640000c0001c0d1010440c0c83c180710084c40180c9103420080c00c107e03500d041c1c40d02080352101240740101d00c240c1ca45400411075190004645103282c031a0881a8482411610b500c80fa9000c01e10086444402c100305911b0b40742d0720b6103445c5008200 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 164036276 1250 164035026 164035031
    0x20d140a1103032a0109120206090d0c0201090e1305030412030905030c0303040e04030905030d0c0b100e06060702120a060221040308010303030506060c01090b1b0f0d1e0e01 76
    0x141841c000c566040004407641c842c2d4020301045032001040000c1543c601d0740c20034186180c800c0e08035664050700100d42c003d802011088204c024590300455110f00c18061002901e01c40c84603800b007a81c00c070500f604c001c2d000800e800410300182e81c2407901103400500c1403a4059050041d50385040c40d550080c3c0140c0c00d5032444246100c101508a0b0202000c2c1c4400c80103003904501410100c0d54074011442072280c82411075001c282894081c1d000400a0070018065440b84808080060003003042d03914200c0c1e800450500050000e04a10701010540382021030390107090300e6100800c505a00407181c00e9a002c40d00c2825003503601020400c2d810390750302c50000561603801c6019205c24201500d44405c00c00b0004904020020354007905c071a040d217030300d4100001c960310b4880109502e401104040f408540ca000040c4040c808210f4045210310100d05840300d0001d540380d40c0302054025030721101c80000d0300303018070400c800040c3c0004041d51503a007440c110000c4220135141c00d54010032807017000c0780d5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 164037526 1250 164036276 164036293
    0x9050c040b03030c03070b060607141f02190f11031315140d0c2105180c030c1212040b0a0e12030306010309030912030305060301061403060103080304020d14 69
    0xe160103551030414048016504081c6001080340c0c0380c0c803071640e0040400002c0c80016440f40c0c5c3d550150354206401850036100304082040460342c581c100d18a056014415011040b88200f46000302c2e5041e03450b1054244031007003903031820703502c1c0c03980d01e071540003480060644010340050420180000201c520f09401d041e0f450003001007145c041c085403001c100000740c01c3e00e807151841700b411142000700001c1c000407005506c51089424800c0d12044011a0540580400034220240c10060152101c07001542c04000d010302955500e1500708c00b0550540c01480c040c1a40b032502101541402c42c62105440e00e0141e014500035140d8066002091aa440854030341102a44107403004001d60003559030280384140d010f40b0036503d00000782100c3c1050f03111004801050300c94081c0e040103002d819a00340e1410f800e0326019001d00811244507000358a0410005810500001d030008103100160145c49071384d0860b02e85a000c0d500081090380c0140c110784001000a5141113452494103040001d8510131 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 164038776 1250 164037526 164037529
    0x10c0203130504050f070c02190e0405060703051302060d020909010f09111612020a0b2d0408040303080901090203030406091503050417091305100e0106090303141c09050c 75
    0x301d0709a000075000e28a00b0007000900709200309010341044550610f0219180b05200143e410410403102c03980d92600401c0c005061802c0746101800350348200c090f650b255541440860440f80210740b1070710200d021041100250400c007008080b44418000007525001d42c0f900402e02001d001e81c042050020030000c1000115030a1103840c1d00c416204000c0c5141c0320550107000d014102c0e0701d1000d400580c41c1c011980c0d0300c41c0200040b00070182d01101c107456910304640c5050440781e840d00103148078100c2d2170806108104541e000d510440c2d000000904141c15510704a45102d00246043e2556603183e003504096501080644018040d035075584903014140784203e00440036900c846418141404140700005800d802d006450b08202d080090311401c2e51400182d6024140803885001450103043c020700c1140c003603960007685e0920106d0710300d50b60784401c1291a10914030010700007410b6100c0b25480c80c0c0180c00181045103104001980c000d81c1c008680044a0b0707400301c112000d42c8024008040d9 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 164040026 1250 164038776 164038807
    0xd080a09060902100f080108070e0703020c1903031508060906040b0907081c09080607020a080903070506030c09100c11010806060d0e1006080a05070e070512282c030c010c0203 77
    0x500088c901401c4403a1411602078204100500850203058020070b0380f2141200801046001003464122003c50080d10f05001d0010020301258000c400440b40d00461507007800a01d882c00b0351003500040110b603a85845038141500090001c0100380a240b000144c140c030704010a04824940c61400391041030580e0000c2e01c0c2e1042a800710420380c00c00810880d440343c0201c0c814045a0304807154a03620002c1d08000307414030703c242d004158005800b206001d00f22518001500342000f042c0c80c2d00b40d0f690980e60042e0307201d11a18000034880400c40805151755440741d2401600040081c05a0307041c1132601c8003901c02d546e1103007c401c940707911061f484401450305003d14001400345102400740c4c0c000d191a032a4580780eaa000381c80c007070080000401e0303410780b01d64202d038804072006880340c006007010401c81e0742810010f010003809681d9001595090725441c407a5203509869405d0b8210440191014400c3c808010501c55140e03000a00c00954810028011004a00c0280d1b004c1c60741c9140c0700b440b0000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 164041276 1250 164040026 164040029
    0xd050f071b02010f0e0d14190f12030b060a121103090312250507050709022a0a080d0b09010e09060c0d06030602041d090d080a09060902100f0801 64
    0xc002004400d018030032100c05000d00c4807a0286000c8621420112080e83c005c219642450340269001000304140304200c418400a000111b0665010820b80540d0100c86056103d020300301840410a2000007040150f4900007a58181400f1484e0610403000680ea50880074800010419804250720031100300d22031100c54100f003400032400c504040c80c08550b00d0081c0d140070301c0d0300c5400c000801d07180321030106c0f03200010f040d0040c08034000d80d0501008041d070f00039100c11200c520508001044003180c80c026501c4080805403000031200a413145600c03010b80c030903a184440d0141072441000310350648002e1003444070407038000c5084105c1d00140003540d84140e02440520694000340130384030002044c442d03008200010300703645a17030b1802c01440081c1060790006005510001d40060a100c82a20103109c02c1003080c0381401c5582d41280321030b1500c2e8010445400a9040400a1030100c1d2070b52010603031030302403640000d0410311030340842c80006100b00f00c6e0380030030040108081c00340d0340000f1960 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 164042526 1250 164041276 164041291
    0x15090319030f1101060f030507030b010605070807020f2409010f0c0503032d0a0605040606020102070c03031b150203060316030b0402010c0f1a040606120308150d080d050f 75
    0x340d14185031002482950003000e02020800168500c1c1000351094102c42c01a142d111850041030f41d80b4688260303100c040d0311044030b240070410000102540580242c40da110341020ba0f0b54546141c82c0c1c00c000d140e54118407030581c008a02254074007003010100303c56400c1c94a001031240d6694402e00054261403083c0c0c1c02204111422440c94005480801501d4022202d16056501c0c500c8a10040d01044088580c0714003001c680c40c00c00517588a84d401c148101c400944040240b1501c4600803400d078030818501410350407480c5000c1000900c200b0a02c000709400c0d0b10100b10342c0b0100d0f99020382c01070316030000b060b02c0d60b004010704c00245802d10906549480304810b4142880c41c5a40d00460381500800190511000c3d00c0c4030014000d0100c0b407100c035140d105100c20302c44070742d080809901c41c0b030986054880c1890b201020401d00c0c2035891440090350907445100c800c2c1e0b100c036100c7c000145800707200d0fa0005003410031500082c41e50384c00340c081110804000700e41850054098212410000c103640c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 164043776 1250 164042526 164042563
    0x121b09080304060c0b060d02100509090c0702030d18050a1d0f0f0705071b0905070807140414030f06010b0d05090a0c1404060f120203070816051c02150903 68
    0x1000082d8000030b501156980c1700444010704d036109000140360110214000e5008003c1070440c610b1554084010185079130101c4010300e0503107070224080a2805a1310000790954000382810000c14001c0320025560543d69000742d0403281c40c3e070b012a0009100380c2c42500409131562608400c0c0c885440f1969224440c2d01580c203d5282424400baa20f0401400d210288980051481e05004040c81f00090740058030a07100c500d590b907034030032000415080381c4460000ea00c400103c2d5079a4490110780d0b4410b655031540d107040c14103221001070803000400381c0070344c548a4800b816600b08000d101407402007000c070360031503192540a4852001e48170020400360322600861122000519100701ca04244d07000c5c1c1c19414402504040403e009060503001b480801802150008048240708542401c0a10a038240d43c5410f90780c4598036516840c6032420302c8402401c4505102500700040c11040245c0064060380c004001500496021140e912054207070300c9002070024030707078241008814110f11106086 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 164045026 1250 164043776 164043779
    0x110a0306030b0a0b031504060f02040b0c1b012f1b1002010c1b020f03010905030a0f0503061f0203041509031a04030c23030d020d0c0207120210121b09080304 69
    0xa499914080d00c0c1c0242c04446c8001c07030140452070b0721480c80014041021551640c46072003d00d001d400805a14840b4071503d84040c100d6803803054a0301c0d1252040e103c0030581c0d54414020101e1044511703e682e8100300500c0e24400b040810040c0d0400d24030f14810340c03085410400c087c040b454221111042c2175a051130214070700c85520102001600d14003407103d00b0b40e20210701c0002d105242001502da40b5609010190040c810040000d006242ca15210400c000e40041410ba03014001150300d81c2d48a08204554481c8800c42d00c0c0e8410000e040340b05813803a041e1203c1e501f1704404007401e200400200030714824400c00c13a506184070585500320407107240c945802c0c3d8000b0490100f5040081200b00c03c0030000c8903550740700c0c0c480c55928121200303880d182d4152907001c0009411980e441c19015081600c000402d81c0003242410548400220103000d03021150284004805150003010070000c0e18040b03a910b1a071180300b081c6140c021014049006042000014083c0c605504038501a4008000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 164046276 1250 164045026 164045029
    0xb04060207090506040e150a150e01030b0405190605010807050402270a1a0706140106080a02030903091e040c0f020d1b05011814010c050702010e0301110a0306030b0a0b 74
    0x1108022141e0b1201c0228107962007402240281212001c02d000b688521030000603210130881c7d5092085108060170016440b800c0b50400c50000248151040891000d005001081c1245001075100340260100c40107407503561140c40c41440000c0056800b10b56070710041c815914188030020080504590950406003030012200400c0f130104622242030400c59010306c11501c603803903030f440203004840004402c10f0000486003083c0c1e000000c101d404519005a540c50402d00000c002e06031000c0e0345e501c415a640d4020590000d40c0003400414091209010110640c0d682c0d14955009080e4480403440b1245440c05010640d0004c1031170382d0a105000d03103000303991580040e10340c10018107482e1110410740f281800b002890560400580325508002507000350094030390b01036200621442d414101c0c1d4038185500d508030b03044060603000003481000001c0240d03220b10800510700d1340003000000c2c0b4500c121400c682c0743d488844a00e01003510798004005000d03002c0d2017268409014801404210540ea0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 164047526 1250 164046276 164046283
    0x40f14010f030c11100c11030a080f0406090b04030302091305090606010c0201050c0708070302031606080f060f090106020d0f080606040b1c050112020a060302090f060c0c0904080703020105010b040602 88
    0x1d081c0400d50356414840407940b00d80203a1100303440314800e84248503a041c0c041c1000c0c00c1d4007844e032004a00c41040c0605074850020880320419129030799a101c54543e8003c54200d520061300c1540ea150b1607403403920100c0c0c0d044c0c1da021b00407480391300c0069a5912075418400c0e5050128083d16031103140000300400c0e04400314410794848424645188141c2c200e1006962074062a14856900d1260910200d11290001208400d603802282200c5540245140850592005005240005402c00040748450341001c0c007032500b01c8c40050103141c101e50740002090280b0002d0344501d0060f808000c070715011a4015142c0504a4042e1400400341c2c81d0010100b42c95101d03902c20780321001c400090445001c0c88060038052a803810310028012569540c4048242281c1a50140c0c86004041d000142050191084400104016010400145181e010451203800c03043c00c1040c54014540000b54554414a080b4030032880b80c0f00003600ca94030b80c2002801c50741c0c160072204006404001c140101600003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 164048776 1250 164047526 164047547
    0x5120c010f0c0b1003051519050a0b2701170601120311070e0604060608070c12031b121a031015030b01030b0a0507020102270f0d0503040f1401 63
    0x7800d0020210103404400c03110b5100c004000f0384459098001d001c50b13882841044821680910221561a0407c00c5044842c4606a49034800c94050542c001d070150055080303107621502c031210001e02031390b820002c500040803500c1100802d840c60313404182e0b05200024414050015100031100301c00d0050f1040c5c7e9606018007a100c200341c1c2e4a01d203e01094803c02c0182240c43c2c1d00015a40603c0d6203d0f400d140781d0320160b039000e204508144001c0303940c0c2d2213140c40a100b80708076600c052228040d03031500510600e030b0b40000d0b010583c940a5401c03000404140352410048140c0c1c80343c42e081c03101c8400c403040b2588401d62640860302c1c48030303035001643e000400280030a2001000501008088081c0314050f44a42c801031400c0c2d04200000140300300300300d8880c41051105002d0000b9903070404100c1c204d20640c3c0c2c00b001d40b259080c1620603202c21892600ca01102e02511003a06240101c00040010341e56400c100c4160b4800901407280c0344062040f100141203058401c0c4804c025100040c5c01c02e4900d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 164050026 1250 164048776 164048779
    0x304060906052203080a03050c070b040305070515131406040305031902070f060c020d030507090b1804110702030f070b04032409030206011403070b03070302031308040e01030c05120c 80
    0x201e0180b12a2581c0381e01001c0d01c080403c540004984e6a01c3c01700101c0d000014440c2c0030902d0704000401903401c0504903004107503c010000150b0b038659600343d40070b400642c000c2c0c9041c41103048202011810301140d0380100609600c4042c2c9103403502e8821900c003140c40001d58941c10810070302c80040d4121040e82d800455001c092184505440c0f00e5100a000d075402c064040c50b911280442400655032141c001800c0660a80300480107000b0240d040e00c1043d83c0c45000184066000c01400b01058090a1045000402d4011261181c0c0008055a10804002c484404e00003030020851404001e8006501c2c0501c0242402c9860611003000710f000702d02c03016240d06101040f80f004420b90054001e5064803100c000c000e11101420f009540d85400d004052161404034282840c40c600003030484122841d400702d0900e036030340304201200a500054514a08500040004030002720010080d1014002d01d2001e01c1c40d662441c180120031550030340c000d0f8020800800c4844101d0004070304040e50140 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 164051276 1250 164050026 164050037
    0xa110f01050c07090603021309050c1302071a0f010f080706030f0207020d0b0919020d0807060b030d020319030507021908130815010b030f040b0603030f0a0305180304060906 76
    0x24010384852003291004405070181c0300021801c0f42040d4480d406582c02035900b0b44180006070b00602c11030b9202000135129a10803040b44665143c803011070320700b10801c03040250070b09040780e9070210351000002000715030300104400c0284050104059078010211004950714032441d1000a070740324500c9008010405840718500700c84225950102d441c103a6010b400c092007201c2d0b13410709210b1b120b425134068515000b0460b2040b0f5130034a06160500c0150001c01402214031b15036030f039105a070b2000404643c11074076035140c4442650140a68504450300c1d0f00a560394a02c5601c1c6c11840c8811000314a0915203400b081c8080c1550024462502179030507003981302150341c41c0c109001d441c014500b015240d01d103101c0c404aa196000b184400b4109000c0c1101000369032140030f6065203000c01c84944007480401400100071407465099103400880160075a417401d2521080420194016a2188c0100b0386072401e210b9080310b15079081c0c000c0540c1c0e502840c201403c1400043c02415184118001c004 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 164052526 1250 164051276 164051299
    0xb100f0503090a0b0901020304050c0f060a050c120703020a0501061203090902031b18011101051b1e1602010e0a080601290703020f12030c0a03020f09040c0e0a06020a11 74
    0x80007040f801c6a4150003410780110f0b8a054207486020754000c8904603064020007101c1051810b0000c1884034040d00103010605090300900c046500e6081640c40707030514030940018000b540c96034002032154a00a0f07002d00004030b2035040041c290b0f0f00682c002001d800c24104803801003540000c003681130300c0c8482405660b1741c0f44c881c020592040d1800030950880c60000700d0380d907140c1340300d4015115120287c03030b12200002c1000101e402c070381c02110310031a0780352000180c811a1079007900900c0305840c14410712803d020407001d0514170703030400312410755401c0614030f010042d984c22040c003c04004c002c0b03a024480508002c480c50302e4079811f1203605140741c07a15600169802c10700c80d0304e072400c8410508032900c0e5100750800a54601d1030814006090242068658a10181c482102c0c03184d1194000c0d0f51824a001200710020361080c400a043c1040c14400311115039140e002e03c080445041e91200c0359013101c00d0411038005900e512071030a541c48203c1810000c2c501004c0e051070038004840d202d1410 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 164053776 1250 164052526 164052541
    0x16030309060b030d051c0e0a061e02030705181e0f010c08070b150603010308071212020724020a091406091002030309061509041502041208030108010b100f0503 70
    0x1400503407241c642c1802140d0440d103d05134850060400c11100b80c20f1250b440024480007800c50350250107c40094002c040d400000c0b50158115904200228440c2e4182405031100d41c0c00b00e03001510403900003140026040d403000500b1055120b4041c0443d00e8a003642c1880303e00604450a0003022805506442580c2c0b2640e030052040d042616001156603690f42c0071072810841030301d4212440f000301b250a81040410741800301c25030f07044e07950142000381780c00200d48a0400d862510b0f6140c2d0100329114002041012003400038198040c4a2803401b820300301c02c00f4003650740c0074016104921039881805001080c80d40135400000311003e4240c112030082e041e00104030f061092032601608404441102e6040070707030020044d44562191801c2d240d00380c913401e903920501111a007036143c0c0458803201250100382e80da0035810100c12100350040c03030030341d8507803490000b4000a41c065809c13910200040060341428010403060340300444410810360340005c0040d26003218450300c0c0003001008000900c14 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 164055026 1250 164053776 164053781
    0x60a09060612080705010509011116050106050a03080d0e2a060c030a090305060106080c03040b060f040c18090b0a170c0409110f01090f170c100207030311031603030906 74
    0x82d06140e05842840703445802d000b800d90307000c1c8504030fa803903181800089035810184290700c0c00102402c5090b10300344003048031b08180d0740c680f0030581e5070355030750900081ea540e141c03284c2030021481111a40e888000e400c1c0c0d414201c881c01144008684c2080d480c01c0c12402d40b01038411055042180762144000d20440030031150301900101c000d603807000058552500d40c000f4a8201100e2040d821594240e0303c40c20f0032a22900140c500703481009060010900141014003802e6202034013400f12091141030300001000e5600003005c101c04688a442660311000707541100c040500f2108034140012410345001c0f4031500107034800c0748885d184507840001891800d00a907681200f00070400d00c035004460800011100c1d9404d10b180c8510b503c823525400780d50180390214115518041c048280302d00d840303e444528068446180154000c041cad03a44895070f1200428031181c61035500404250323055150140150740c0d0031500004030703402400303025003082510f00c11401c40d651616000c1100241403601101 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 164056276 1250 164055026 164055029
    0xd0c050102060f3d0e010806010801060302090a020a02190804060f1b020402090604031a0f07030b0306160210060f0524040501050a20210c0a110105190c06110a02060a090606 76
    0x1103031043c0500010f000c4201d02d050306d060780c408a0540d02c159988140c49800c84208d884001d40003500000040d40c1303240c490b03000e030443d50075a0050f500d5100602e214480f00108010086401650106050001d00d07840704100300703e403103582003040b0441045055850010020580240f240e900003c001809448010039100110391003044089400e00c5030111040c4528111341d01c445242070707440080c0b40742d0300c01c0c040c40d2007106000d40504060f40301c1102094005000001e03034019442405001010100584218401040d005400030b13242e504000400c16070440b20164940000c0c80a002e02e04641040d100300c0d400c03a0004d0814641e1004114004d951b100c1131079021040074500c0c0141d17403a4101c1c021030f201000c107000080040c80020b00b0002c07078500303026401545055600400030341d800a080c0003503a40b0394840c141803c606180f1680d424500040c3c450350040c000505814026040154600174109410840000305042441e064002582c8001c000d20b04050740c0d4031441d001060101c40d500200 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 164057526 1250 164056276 164056381
    0x20705011d0106060e150702330301030b07050906040e091207030f030b0603150603060f0904121103030415020a0e04020d0207110603010e04020d110d0c050102060f 72
    0xc40380d56800046402041548112004076500c88405d8440f480c0c072403005001c00009500144c104082c640078440800320000d82c2280c42c126061000d08081c0380c84603070a59101340184030075640c1d8198030300780c1b5050102400300014030030107118031400e40d5603010984003683c49481c60703201c0c541c0d10760021a151100e01c0c00b40782e4500f10300140800916071b101e18030701008000c42c0c134240810b400b4042440940e200488020801501e00c5085840500c0c00c64010350b0403040061800070100002d6001841150098404503002d50f2008a888044c5c0d40000981180105250140d401d500d0039803210805d4456400c1c04485032940081c41104003401000c03851400c0310080c00c110b40780c40c1c2e4080394000070350102105a5000c001017812112900c0e202d0200c0703042e103076840307411201c68030340f5130911071001610401124903518039214a522a07c90b1264070080c03a00540e03000106924150000e8140740001e042800408104010040e807070038900c510220004072009000c50f04e1083c1d0a49804003100402c685 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 164058776 1250 164057526 164057561
    0x2306070c05130207030315180c1701080a05060109020f0909091009120e030118060b180a1a01020a030c0210090812090102010b1804420b030c030a0602070501 69
    0x2020b0080c0302c1d501034050b0394800e4500300142d00c0700c1c00720024540d5841c032910440761074400b140081421a60021403c4030a682401400134192a201444010b4240c21001c13955000c991140240442000280c0c010080c0740300851900210382e40c400b00354840ca414803800703459482c000c40c586500810000c0c0240c0702c4070307038200120412840c0c4004006000001c0b84006a80040340c06901c0c0382c18415411211014240743e810400c566580e400a00740c0d0b00c800e9a4080080c0060308481040f01001510170001c07a031002510b11101e00c44411402d0381c1444841c115409041c8400000c2d4114400c862440e4040356203c54803006168100e8001041e0742200056008400d685240c014840f80981a0000f013600284400c0020b5000d00051015441090048201101c04100852007580c1e580b8609542c80000075107504d5408514040c0041c41445280000c012981081c2070200c20310507448040c00450280400c0d00030540004d6a13509807250180405500240c4e580410809602c40103d0100000c400e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 164060026 1250 164058776 164058799
    0xf0f010902090d06150503010b06040f0e0c040b0a03090314090603070e1f181208030c0c030d0905030d0b0f1003020d0b0d050708010c020607050f0c0703060f0b0a2306070c05 76
    0x1c50514032803440390034041d41c20109c4003a454505030055a0984c0c04c0841c400c1c070420b19001d0174200900c00a4101070120b4000c10003c104540c0ea5070091a211070395031000705142d4100d10780101a81200300b402c8201c070f4000c1c0300d16450350342c656040702d0b0004c8041c0b030000b030031801c60700000c0e0360094045004504444905e903280c103c590014559100d500c0d00c980c11440d8903a0701c01d0070162100c003428000b4010f004c03c10000f0700401c0c2001c003410011500700b003244c1c10102050096403c480004100740d6007940040356205c4201154080d081d5403007015614003011302602d001044041e441d484440003410740100d8481c00c2110213503c00509048000c00c503100448082c14840e1311065203010343c903455428002b0500760301e40001052401445d03d903550a1074140c4230320441106410014040002d40194000007000c55403d024111500a211800060f204411408c21400088a901108400c0a1150218105a405103241c1c40515050302c40d180d0701c4250380b801ca4940e049036006154404c0101c0b0303c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 164061276 1250 164060026 164060051
    0x140909040c2d0503011104031202070302101d0103090302100209010e030114041703010302011b03020f01050702100e070e01030605040f080d090606050f0f2101060305030702090f0f010902090d06 85
    0x18152030303a281d40c0d40c5541c0b20a4590083c1401c3c0e0760291031200308624208400c200080350420702c2400c414103441501e8240d44c1b01d5000880d000803070303003075900040c469942044c0d1a049014014001040900781002000c040d6030b40a5210a00c0303001e120f60040d8041566400e40e40504144205400010300810034150310007506099103400740c41c2501c900c040b01e903c543c0c0c4801c07a0390440f81600d070141c544d01405040360500312040000524110114000e880d1034414022090041c1ca000c0d40310740e0098000d604240b10580100c0f00030442480c0300303600c072290400c9103501202c0c030b19041d640c103c00d02040d542e86504110545c442d0340440107141850000720424498640d40c0081d07090b0744a00c0c81407017a80d40d40e608000e04000b440304d410b58080c455005e107481740d00e0010841c80000d106018992035412800c0429400c5070041d42c000e60703c907040068450111302d0300b00c03101940043c031240f0411043c2010304004800140502880420690014640c202070f9614800c03200c606520440511010f41c1892 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 164062526 1250 164061276 164061329
    0xc0109081b070e1302090c09031603140a0308011a0c0312010302010305060a050f0d050f2d011107061a270928020d02150406020607140909040c 63
    0x701400c41e90044410100b59000200c0c0218018650781c800c44001c00d00940070403801c03c2000d454070903d07a44c10031201e007240d2018482c655001c0200f040141c0312928501700080c480100044000554106012a10011340c20a0142d0f0660f070150119480c2100b80c05124080e501c80c181011030300b4030000c0b07003407040c020580c602c25060300e2007a0fa00384520f403100c1d400e0280d0780c0300900400e40d11540544544000342064900208064000d00890b2403084d1001580390400290203242e500401c54904998094100c0b000000c203401003c0e03008101481070303c070f2003402900448500400003500d4003c2c00a00052603a8008081c12000b8803041c1d01d50340d4000b03070910030303c0158103401070b56110100140501c00042485840c00c0801c055215600f0624070b50003810000208040341e106098007180d00c003503211041c4101c810000340408603919410401c0103441c107000102070b4410072003280242c0c051050f0400584040c00000d4645120759120762810580b8483e06400501450100039084814030401c0b1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 164063776 1250 164062526 164062567
    0x30403140f010204031509030c06060602100b0916050c0102040f06030504030f0c03020606060f070f0f150b03030901030c0e040f02180d0b060d0507091a01080c030601080103080c010908 81
    0x500c1200ca0040c0210111400e0f40120310000e08078610100320700c5c000c0301d040c0d040122074520928020000b0101c5a0710a0100c800c0e40e040b00340140c1c001882c40414140c60f00c01d2850a40003101c4403180380c0b41a000030344500c80b00745001000c1103001701c0c1e0564040000d40543e00500301c0040442d405d5a105d480c028020070b4120340c2078000034946048810024001c0302c1804400b07406501810301c594a0606204540c1c1c8031003003484800702c080222030003144160705480707146ca11514000103520070604259200b81c130030720141c50341c1c1403800006003490350b000800c13a141608203007404603144428040565064424803102500300e4142001601d165400d907009020600700c80f88400071450031841402411ba102c604014000306161021480d1450401310300102039105200b203032181a00e50202c4001d0780e0a100c810184030702200ba00c48055031704160429445070000d00380f9829440c102c00020015103040c40040c1c0240000603032342c0b144401c02e4002c0c0500303542054003203655103d016070845070b03250030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 164065026 1250 164063776 164063813
    0x140705011a040213150210022d04080709050a0e060906190b011407021f0c05070b07080a030b190b0c0d0905130506131a031002090d03080612030403 65
    0x40081d800000d10b090720980d000080c200c41081040390500c419000501040030b206010343c0300700f2444e2070f503140d20741c001044500c0f48007220007001c848400c14a40e04480c000100100c07003038203200038810744400040c800704691204501091039210f9544000090000102d4107107603000342010011880300000708680640320b20400220103100541d1450200c8204469060000f048041000b910407141409440031034001050081a910300150b610341d104c000c0040e41011038025034190301402000d11400e4000c4c00c04101052402c40141d54085592180009440a056441140d604151244604100503407035030414a00700700e48411054445801180f0180640c4c452a804081c49500c550611811100050040d031004500103d6410181000820311030b0460780c8203502103643d9003540550004000d030000d03040010300b02001403505020340f4040c0308600500412181a180c4c8583c1104844160503241003c0c86489182c0022011551690207000610000c5004000d0014059030707401685038 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 164066276 1250 164065026 164065061
    0x20f130303031d010e07060e132f070f06150503030a1206050a0807060807050d1a01020607091a07020325060f0903170c0f0f010614010903020303071214070501 70
    0x640f400610f0a850481c400c5440c1500285820454980550b49a51005c28000d0826140d55903101c0510211801840d80c40f2581c410542d41903540505041c54501c51000d00100b2403402d04607441d280014010900000c0880e980c641c0c0c40301a18030b00306d040c140600380040c00d6035030b02c0e620b00e03400400800f2080341c0c0020007480c0030400101480c000798000d08450300c440107030405e18030304042503e6501004011106104041280b07001c07115182c07040e070540046c1c45071008800d11510000a2034108010307c20001c0c000b8003802402450500d50848924040c0ca500c0143c0d10010351010908000c800d1300c100d007101c1d0b0205825002d41c90b241d060341c0c00390303613099075140340240c8040c80c111f800741e61510000c1c20032605e00322581c604401d20f00040c010103140340300303d4460007054220035203032210700074a20b07000f03075900c400c04c3c04051040030601e50f46920900c1e0040c0801d0035900044d840e403040820061100d10003c101e5185c0d5400341d0381c0d68034020090240e039a20303601036003000d0340038240c030407042d03852100c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 164067526 1250 164066276 164066321
    0x120f020a0b0301090f0216030507051e03040303080a0203240604080109140d020d0c0837030c021209040b181806060922020a080304080114100e0a020f13030303 70
    0x1e58420381d00b9020b03420007d0750400d40c150320b05035000c0d48030003c05d40300c90080321855041d40300c03c072030020382c02581c0c03030010f656a602e1410000d0105802916481403903004105021208091041018000c03407081440b050700070002000549134415648214210750a000c459424010030382c40c1410300161100c103035105813990703680c1261903034180c03525440410561400d600c0412803050150003804113005410204407142d004002002d585080f0004100c940d0400410300180e06001e06583c8000500060200d400441d40d4000c0901404007504d020b150b848401c0d00e0a5078903030f40c2401c400d0b141c080400b082400c0030070380c0302c032502024a000030140c400c1001203030540c145021490712403c0841c46000449800580c4c0342074a4107480720503a0301c08000800412207500074001040244591000000c1c2002450409408a103005280144d0322000d414200686a00011402d601000c0d0b4a0010780c1e802030048183d51034019402d10052408001d8404010550158030010f801c1400e441c1010404 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 164068776 1250 164067526 164067551
    0x1060b0702030d0e04060504020f0309010f050c1209120c0a0506060910090e01060320040b1c080307030207051002030f240103090809030307030e0117040c120f020a0b030109 76
    0x14030466400940551280d040200c4840c481e40b1403030780c00c0000520200b88503079540c0000d000e0340c1150354103180841000050251701030091049181031000c0b11824841480c091508001a004071804c1c4801c65180302c002950104061000e032100076030300d607000c0791140455151296115a000e8049540344a40008a200c0349081500386202c0c4c40c140e540d00e50180d0824610300042c06d0140000070440d03480d8400807000800c0030f82402c201c000c045140c2035010002004100035621011115400f03038002d038015a0282588079030b0194040e401070400c030b45c0c3c0e4442d54401c40092044240140a1380940f0b10100c80c1040541c0080d4021030070340200c949251600241080d00f01c51241d0300380807510810a1840440d4026001400101e00079100d00c2d0521488102090a65201e0b0b80114002039604070303500e0701d940c0c004002c9100c00c0c043e200f40b074a40e441c2c15500c080103203005001c0d11403402c440700b031450100001d030741502280c00e9000d0100d10055645401801980c1c0081c09261412402c014034081c44 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 164070026 1250 164068776 164068799
    0x313090501050d080703020a02130b030d1b02100c080d0504110f01270b0403050c01090605070305030f180f0609070b181c0b0906070305060418030e01030e0d020703050106 75
    0x59030301c01841c0c40c443c0d00075952020110303404034404509600640c10034002503075440060303105403442c00601084103a90f000c100341c10540f68035510030038440c0622030556140401c145080c1c5031641500c80c600c440c2e103105010303a0415001e0100800c24940007802c4130b1142c030941c00444c091803180800c5820303581200c0400c403215403035a00700c60000d000c1405454500c020007142e0310156000074a01086607441d414002c8542c0d000b03400c02d4034503501441000c98070b5680700341c0541c010b010303616020382400761a5800034024400501450000c440b110003180b114401c0700b050380030805084049492008a0324400f40d2600d00403070343c7d80c5050180400c00201d58900c0d60440b64001c4004031001505000030040281041c1d0f040c540245c40503414008100250b02c00300028010400c0500408507813405800007000c0d13802c020038181c0100c0c24000d8400c3c0d03d01200112490495160600ba5191408180103c000304400c07010742c8460b1044607030f018006034003c142076003600d008a00901c00360341c840c10300110 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 164071276 1250 164070026 164070029
    0x405060702120f011a1f12020d021303020a09180b1b072102071511070306090b04110f0604030b0603121603120603080a140d06090b1306051e030a05010501080313090501 74
    0x602c441456007802447c0700d1003010440306182040141090040c031310f0340049801c10740015540c1e103a540014001d500d03240c40e810008000108041c00700c1800880210321038099110010101c0c0c01c2078010070304200076400000401c5c0746000e0080c2d141c40d01400c050781d46041c03085c81000d9540300d0f046443d0100b440403810605407006590020741a58441e5011942c2018030100002c523402540c1d80400024001c1c0212840b1a0080102c5881800c1c0381c2401d1514101550b001031042d80840820a900e445000680d01143d400404509403540c980300817074180109a40c440d00914800501c840030a08100717501010280070b0f5a401c11007162055030307881268420302010b00086810320000a61030710031180929407010f03008a031400c00d1360b401c1210041d0b5030142c02c08070710580c480407540c01f50305080400780030320104d03480280441e0b89040d02250158411001000a5a08468040724544c90401041c2102540a80200001c0d0703540c4040c40d03201e03008003840345400c40c403880d000540c1440f103004250 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 164072526 1250 164071276 164071309
    0x8030a0f0f0605060a0c2111070e01060c0f020301021b0616020609030313020d0602040303050a0806040c08150a0807090501170d02070e18250503120405060702120f011a 74
    0x2443c1601c0d170f0f0780607508600226011240c00112401200103000c5610400c4d0b6002c070a80c590402503a15010345074101015a0081000728440400422405600c00c0c606a00c4641000500707100c44030900210340a841114202d0b0901c040b207051300c03081d250000800e1440740c41034081c4a40741d817200f41000c0340c45203c20760b000d030602d034024004207920700c101d80c8003040014402010700071a402d0664070601270382c0141d4019030110300c0114100b000380e900326418943c001421282042146c0d02c51901400b042c10182032142180700e0b045005210b515071440d08000b610b00c1c9411949490b43e601002c0016000902801d0200d02010b03441c03d1400d50002165420303420305402508149003811750480304a14024003c0f0746100d020945070342c2030704080c854016504506401a900d1206030408003440d800703036070b0000e40640e00286203d120039003590183d030140da004179401d6503109807500001c0c11420b41d90055000070301800c0104090100158004120a401e1500e0346519581e10740801012450880251 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 164073776 1250 164072526 164072539
    0x1091a03010e07022a0406170604060f180602031e0c030f090c0d110a0f0602031c0603050f061807030b0a0905100509031e0309250308030a0f0f0605 65
    0x5100000c0300150041c0d000b16144103c50071100030742140ca0100c1ea2089940e240086038550040c5c040c24240161405080d034000310002c900c0358101306c0ca0361038500600103000c166840814106458554000e2290000c44560700d80030030500f0f00f004002544140d51042e10210030114400203400100310f46031141c28085120b5081d03030fa802000c07901441c40240100c0c4076008600d1036000c41c2d520f803d403800ca40da001c0e000c0c0319100c02e030315000e1040f00429600284202c16400d1000c100f80380e400004c46e00e041101c100300100c07119050296801506079a000101603000300c500401c0702c0d00000424a104541005882501003941e18415458005502016041d030801800042d40c40c1002d070010080f4a100303a0442c1d103005221080c200071240c0c1602c120364135810011340304e8010500403c03141c1c9007400446043d460760800c0e0991950b00e0810040a4001258007903802c60719101050f882002542c0080441d5138900d01030b25810010f100100081c07640e94580300c40007042101a1045e04152140902003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 164075026 1250 164073776 164073779
    0x16050607050102120103060f1d060105100210050408131d01120f050703080315030303131e060c0201020901030c050910081b0414100c0f0b0a060e130201091a0301 71
    0x2402199445040e05840030340d004c1045000030340304c4581e081c0c002d40c090680066035800c1d00c154202601d890111010400c40c49040e4000101c20119040d411224121401c8004901242c41a41040030052283c240706240a0412041c840448014078100000d120540d842544402c05401c00d060090610310381c40f4050300043c004210301c0c000f40100300e40280302170300000c03640f6520300e858544075403c122640d20002c418000740110242c0550b203580400c41c0514111324003000d0441d4504503c104c040c14903031034203103010070050011104160558100c0014840b455810304040c4c040d6110540d2140000d2504136401011407281c0c0036912240e500804240c9402001031003216480d90283c107214807000500c00100389842c0cad010003030004041c5e40e1404000240170f44100054000c03080c03075000a102c1c0c2400c134400002e01d001300946525900120124007a2100301001005005640011902e000084140614440555405034000340700340d8606800644403000c00201420106096840703401c140300 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 164076276 1250 164075026 164075029
    0xc0406020a080904180f0605062d300d081608190f0504150504080f07080405090106050d1d1905030f0403030809010c03020901050313061e06060801081605 68
    0x141500f0800034004100c41e40e0020100911030042203046602c452444030401c01c0200b64043d055000b0b83c00c451400304a01d60801d01d44441140c401034040001e00100910802d82e500201c552600700d0340305020700340d4007081018201d40b041004c0c40146900c81e641e41d1050ac14811b1044c00d104527501d4400d44412001c4060a8404150143c032001c0e1070301c4200040c2000007030a03c0380901c0045040808a9507080900f001c8031442428a0031019042c02c000810012800c4402200c5640c8400c002e40c036651a040e0070b10440c180920340095601503e80000010a1540b1002604001b403401c40100000741003050b0b402c01c030080031040041c4c1500039000810f001c020440c0e189400724000c2d4240c03841d04044061402899009810840101d80c011080c0f001c021000d00c64a0311104482c10214540140200064181e002c010300e00c0f444400224444170030401a0341107040201c2103529100040100074a5503009452203010303000005900c5030000990030310028900b039a2001c0400f0280050b800d010 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 164077526 1250 164076276 164076293
    0x108100b0d0618210e031b010c080904090b01030209151f02030d05010807080d030507080f0603010e060a0c181212140a0c0201110606090a05071205041101080c0406020a 74
    0x32060011501a8118000c0f44201121a40e5601013002c080034420000c4000b604c1e100c981e50126001e07500078005c00c1d04a050301c0802d00c60b40002400d204201080d2442c00c05114401e1840c01c41e0864180544a801c00100950060680340308490140303681da1011145c440c11080d900416500144c0d800829214030b041d862080380e002580c0c416a49000f40100916042e11300a0780040d00fa540000806c002c0c1c010284100e5250282c145428001c5e81001d003c002c0c0001c402407c0c1001042c100f13804030b10165400d41c451780ca0f000c042000e450710344c40c00c3c0803240024a85414420080f541d010174150511740007540315400d0f10702c40488944640352075242c8103035252610107000188a402543d0b81c44001071540a002030310410768130724071082c11510004007540358200860301d81d44d2104003400b42c65a07810b60f50b1984800850400074440d40d406a04840704007514100750210752030042400b041c0441d80103150210803007030721900f4a82e1592007601c80d00307101c2d9103c1e000050b00302d010400000350308032 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 164078776 1250 164077526 164077541
    0xf05060105120609090c03061611070b0d0506060c060a0603032703170903060405030705150105010806040b040f02070f06060e160f021e0f060a02091302070c1d0108100b0d06 76
    0x507011031b14852a9100403c2c50444140d50441400c2d0301054414403541d030113690588603800c0040034100552501614160602800c2c560035a4203884000251041c1c80309803e0b00c8290700c0020840b0464100005140d0040115000550004a500c060b818485515000c000e102d40228081c00021901d035856150200c0d4a0003264290105c1c03c200c400324581e401c02caa24021030045e0040c40d519000c603d0300524201e802c10300d05841c1441c1c280100305a80e04810a41d80c007000984002c1880000000081d00400d609540084021b202207450024451f011490306849803082e2810413a49850b844040020201200d101d000c00140c5011440018482c00d140b4841c1c00c02401103031100d40318003011004044144000fa400d85e0300c01c41a07819041d004200035504200034070411481c180d0304001003101c000d0070b00c101d01d018940000300c9004100464036110000c00d40d02c40c114442aa260006c40c120500078403038000701703101d2041d20840141681c071030741417000002403584591300750329074800c006000035 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 164080026 1250 164078776 164078791
    0x3071a040509040c0512031c09020d020909011410030303110c03030403050f1e031f0e0610022a1e0a0312030b092a030c040314120705010f05060105120609 68
    0x4c240700080a403101003100e856844a030003e1521841d0b8042220301e8600342c85801c1c04206d0512000d00003584590700e40c941e00c0d80e0107444d0242e150b5100d40e5081c2c090041d102c80400d9a500c0c0174100019084451080300070340c1e11a503418010304403c101c69460900075262201100d8208001040010380a04010403c0d08088142c940c2002803001c040ea140c41101803160307607020400020000740300d04200c0005100b080d4022031070382e110304103500d00e0300c0500c1c010007203030107496150142d4a200b4020886229103040c200001054a104c241b85c0000b0318960381409030050709a05086a40d8910b0b80408110400000d0a00c400840c60b54035288041d0002e44c1d504410b0603915101c290150302c444980511030f0302d0000e0b14904902035038070500d0101c981984405c544880074818040045140401c0320708880c3c024110301d5030010b00c0f10440d0704048905e0a083c3c110000024040c0400006400c0307164001e105260030070440c0e4903900151b406208141030040d641511200162241c0741201c00290030480 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 164081276 1250 164080026 164080043
    0x409050705121504030306050a0b2a01090b011409090706080c0715021b070b0a0203090f0a0b030a0e1c0c03082805040b01090b090f06010c0606031103071a04050904 72
    0x81490b8440a0f2580588050300041d8580500348401d080420007040100f1200c2000c91a000302003040c2c0142c000540c081c008048038642c2d400416000c01d4200d0042d9079001840c020055a469420340e008611034000d20380265501c00025005100c00f2940804903032542e100c0d440300d030340c030b130042c10340c190307001c440205c1e02203040400c00300307000c0c003d0b101401d41c030b41540e21080140070484000c1440c207200d540c015281c0390005c00c0407003c416070110640d0360301c42d801d444500d804400c0c540040d07181806a0455895444e0100421580444030380085400c62030301010341e10101820b406100c90034580703030400c001054440c0c8580c40000d21400c010780d84014803a5611003e004405070307100d41140c100390702000c07403901c6205001c103000010b890b40d030040409000c1000f4016546000c40d111210042241c0308880c124400600c2a90084112001c0e00b50b001100308041e549911303100036040d0050b400e007402441582000300344903101a1078038290021100340c460409151004000252100600c11a10944d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 164082526 1250 164081276 164081293
    0xf070509010512150a05040c0210050406020c060412080105040c0f081803040f05090c130b030703020702030d050403031803020901090f0204051302071203090b15030c100914040905070512 82
    0x6000c001074900401381030316002a19002c00040008845460f0080c0f0310441c500500701401d83d030001620842c0061340100404d9507596420b00000a02410208461600aa034108020030440400400500443d529151034690702e5000f8002201d001d0400c20000c0b540880400822078000c01c4400d41c0b000000c8842c03601030f041c034040c10742140c120798080082d030000c00070103000c1e514184c003441d13074403654001149050500006581c0c00103641d07407041040c289130000201c0d0700503220b501252032054010781168a514240f02c0010f040e540188000c0e00041c0c440d40208175400c8070910003104481d002003501c0010390034108071800604d029030a07a44500d40c200b00006058a0701141800852070003000180c80304054201454000480c3d1310340003c05180440c41c100048081c0800d50704450040c8010816403407150110b0303e0244044d10341940034a0581003000c12540c00008602079607510801c501000d100b450502080c1d90154400401c1034024000c10300850610051048a80d14207108036100c0c072 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 164083776 1250 164082526 164082547
    0x17040609050111040620070603110705060709050901080f060705130f0b04090c02030c120a0306091803140a090909020102071701150f0b16020a050307080a0b0f0f0705090105 76
    0x5860342104045040f40204040096039080b240c40c0314525032821021060600e6900e0103038035940d031070090744180b5a654180d035001c500c1c107030142c4c0d001d09c0d0b000d0211034960405501c060407440d03080c412140308502030000480c04038001308007aa8004115001441c460701d540d0410ba80300c2d0040024291640c3c1200d500003210030790070100c00000c0404d10440383d51076080c0480d48065450081c280415940108403282d50098005950000a901c68400c0e41d2039150701c4104070081d00b520350008880c1410710214000a03e004085014114441c1c0c0f24100850002c00346107206010b40703601040840c40c1a0b104002031101c07600403060307051051040d01c0c1d4891301e51652010300e4084100d114490381d510b0100407005003402e030554004e000d04450300416145403950700034091066428100fa0451a220039408640780c40009501800d4010140c0d005c81c1c0d102c0002d150341e1034081c4400c1d0755288610005c640d00b1300f4102c950b00e00410020080c110690b0303e00300152902c0c0c3c400001a41040000c006600a6 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 164085026 1250 164083776 164083781
    0xb03030d0c0e03060a0e0d0518100f02010b0a05180c0705030c030c070515031f150203090310020408070b1605010207030e18360a0320060403170406090501 68
    0x400c421501d819441e90400c005140c503013a0010009503445140c14020f80b5480c1d0001071202d14116145801a40c0b4645107500030354944100d02e242d500400b80400c148a2241c20189424028540390300030040d5404c00da04200e04400207104058202001440245035480407241003a400240c00001c540b40100300e598852645d800700c00ea211007070300b02056644049006100d914020305044404920328598800d400c0c1e01c030b1101410003100f440d2501c6100784600c15046890b0000c0c00041d803c0e0b5904103046001079202d41c000c3e15924400d0180520450780c081191083d541507854031401400000d040c507a401200381e00440c50320100050407204c110004209000814100d442076868904403c18002400b680c0040031881c195046414410800011610301000ca12510b0745450510210700700b070540c2e00c0e000c099490403207185c0960102c0100740350b0021030201c440c141030b01c001007004019090141d12074605446c01400210315540703412000d500801015002401141c00203440100ca40d1010308 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 164086276 1250 164085026 164085041
    0x15010309020328021302040b1902010b0a08061806040804090c0513030615080a050c100e09091e07080d030915020c060f0a020a0c0b0421050405032e0b03030d 69
    0xa28a654202404608000485e101c2c0300c00001400d43c109420800080307240d0041c00703040007114400da070110020310300c02d4001c5040039101a000841c400e444e56511a00c82c0c00032180060010550b01140780300000c0003800d1403046421050140c20603042a500c0005030805020340790800c0024050911003400304103442c0c00a61081c0c100107554903c0f01c1d803102400c0d8059100200c1500003110550110758003054141000308106c82600200c29140000d595100034211a0360b003141c00d540421002c1180043c8030303d0354044660b06001c20f4100301cac80e41da13a20b440e1070244a0b4690021341e12441070741c0c0207800c0742962920841c060344494006c1d00c4808100d0300424460780c159032100d018400000d15040380b098000c800410103501d0881d003694003070302c0c41c114808001c000071020704c0003e0601c118104104006c24000100740d134a0401c8220080c020b40040c040d152090294001c0a441b00704007004d000c0388503000211000c410070a0440f00402842101d82aa4040c08200600e0362094114482e508 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 164087526 1250 164086276 164086333
    0x1e0203032410020a030e0a1809150207050309040e0a02031f02040302040c0203070605180a030509030a020604080a03080a020414010e0d0b0108150a0908030609192a020105150103090203 81
    0x104c0c00c0c0a810001e0542203500d00b0320f4010034040800340030040d040076442120f100030400201750103c180c0303811040718010744034a5035514070108000040207004002012030117800c56041c40303c0e400400d000e40c2c550100c001e000754503600605100d603082242e42c4424080e0246540014101645d0390041015101d208007140010b803c0092158100b0010b44907154014120429480d06030003032109640d5280700480c0e0280c180500030886410541d130402c50004510f034083c001e603845903914541c26544001c40d890072030115244400003203559416200707032012a41d03890351003c00d2000c00401500d10f1a00d41d039003150049100000180414015560503000344041002050300c0710076000c8007100800d000d800d000c2d10070f0901a2260108000c1000d498000c0700c102c0e6607070316a4854080c0c040088241b018421000343c24105202c00300004a90f08104d00201e00f4030b280812141680103e01705c3d041264503050b074030403201c142c0b80c1035440307540080341c07a42c07000d0200d03107600201d550b9100c0c1484102440d803 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 164088776 1250 164087526 164087533
    0x6060807030b0a0e06150402070203032203050f060f06040902030a0f080c070911030705030c04030b0f010608181b010903061401090b0108130209060f0907030b011e020303241002 78
    0x104003030082d40705480c1020810000781c45c480c10503483c4142072142c91418640302d103401040d81e0080d5a028401c544100c5042551039050443c00140c24496007a10311043d5214050307440384a1180e10f0104e406032054200302401c1c44d07295211020040105030746002680c05214400014000a421501c2c4003400c0b4081e002075074840c81303002c0f940c0c0e250010980000800a04100720b000c2424500406c6c0d80e00121a0b080032a103907030312459403824038056503201a110000d0101402a40951108424142d6520b0340d079102c0d01c0d6680c41086808d10407040d07002000e603401200d40f4859241104201c0789084c005243c000b0011fa50781d01d03003000351001010760348817188141004204294151140082c001001c0c00d00d4251454840d21300c1403441c046a0b400f900038020b040c0060010b5443c28a40100402c005048041d00d0528500040c02400d080036614042981c00d186888000300340c2c202281040d004c2d5000b580795a460000d00d8201c2c03400c0500c20809000030120810b440e81d1800c2c2e48040c503104980c002d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 164090026 1250 164088776 164088781
    0x406050f010501020304240203070213060305010f111225081909030f0e030106030209040b07181406070606050d051c0801050109150216141509061606060807030b 71
    0x44145000d0603031041c2e06642c4200300400410402020800041903041140400030554000a07411407250801c020740c01040d40c0c00c071602d000f4441e8008003c0e02d010341e00801080420080100440c1d554030507a10080c0810b012281c8c10070312000b03d02e40d0101c1d10001e1243c40302480c15a01810415809868021491000403c00b040c0160720b0480d1903045180018800d44c52140c6004c3c01b242803802619007000494424a4030313a480c250494001550301600c12030083c42c00c1e0074240c103582800c2d60300302c00241010345482c0e024030a206104003a01c5103540740540e070000e240c041255507030103400f0131500141c48440c0010207541c0c01c900440014080c401030f00303103d0042d4900340c0380c0071b4a8000990a01844000500460b41d0043d4840e00b903130058440082200c0c2007104c142c7c035043c031000c112a01b100d0b0b00180811703102c0b4030b40c1501058850030303030740030542d042c81b6140300340e4a005000c045074001405004040003100d005d03184040d00c5016074800642d179515241003509102c4ca81e0010350f10301c0e40308010f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 164091276 1250 164090026 164090041
    0x603040f020f032a0306091222181b020a05030d0c031509061502010218060c0f010c110d0503040f060207080408012c0c03061b090306090d02060606032203030e06040605 74
    0x4187e40c0030f207030600030b0080b02510246841003030281624845100385400c15080f040c80b4a401c190019220320780401c4440b10300902c8480282000c2c01c80f0000813840c03248003001e003900000d071504001da8401c0241d370900c0d8000100740010804404540c04050311410280d8013401510549006400c2116001c0340660074520031990700c034076042010003107a10400074505041000c01010341d012008951300782d60340340101e03c06450010701034070b2800103503e003c0d1000c145e9904805800d0030003c06005482c06c03100d4803801950240002c0780c002d00181000a42d5800145042d402001d50303621840c1c07190304068440340c8282c21a100e0040901c40c4401c050f4401c50010055042c07503540d00311910080c034190034001c002ca030329001302428070910099080d003461000b0191509403540030b08094200c481c1440c0198406075540c0e002c100000240c055400800c2c0c1d24288282142e00c642e08290510038080248d000d0545040501501641050b603141001b268000d01484600e00484c02007a0206a5090501 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 164092526 1250 164091276 164091283
    0xe010318150b060f0a030c120c08010f0504020703020c0405040302070f12020f0418060b1309050c090c0903060c0a02030f070812010608130b0402031216060b0603040f020f032a03 78
    0x71140c0c1c030944013030203560754101c890350440b045a81c041c074000c694001101f0003940c0c84012410f0300e500c481d08002041c448203034410721003070407a4012a8006051555072040c042240328500d030180061704010082c403107500303264022a0f0020b206c0c0c81290b510a03625500c2405e03c000980044480c074508110010039490905250300c90030303108407402c004000e0f01e5885241d09040c0340c44002c100d81c0c0c4440060300c690303a070004030075010140c2035400d20070902240380c46510780c8203800c40781e88a2090040032036a19034000080e03c0d0000d0b0081c0003401551161032203882c0a0704505410f00862000b04005401d000d000c6000e400d0042c0725086007038403200d0003904840c032071030f0580188080004000400298298049101c401c1c203420a0240c085510382d400403d042042e503200b0054140070011b10404080000d505681ca0346010300c0c1c080103e54400c03410000d4a100503a40038241404500070940540f030104010944440010101da003500c001111402e105c80e50b81c8041254640d24981182c3c4506042c07 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 164093776 1250 164092526 164092541
    0x40302150910120608070506180f040e01020a110a02180901090c0f0824071115070e0901060e0a09111201030309050102010c03090807060903021207150b01110601060e01031815 77
    0xc0140c800142400081004d500035241a025007185c20404407210f619004001d00c3d82d0ac001030f00c2880740303481ca2200c0902030740c0106034400000301c0e0240c0c0f840041c040480c8007210315900602c0011220b0f42c2d00c01c0c2000e1500c001d060301120f03568076551680010300d5540702e00c0007030040d41c1459020340d2401102c01e0400e401c8450b418001d400700d1002042d1240140d20407580701945041086410305451681031401da01d44210811004200050014054114a901d0000c0c54225075886881c2c0c1c071004100e485001c91114140c00080305102444117101a801c030340c20390a080351850b42000058030412002d81802c3e0303c194045407002005020559080c00380601030070342400c003440410050740d04d01c9294030540c3c001501150390350f40e040041510034464000840d11410585846a01c9820312030008869038000502c1503240c40b050750415400b0b40d41c14000d002030000079241c56868003000352030641c11001c0c460704050740c4101000008258050320242079004070b5440101c5d40c081c00076501120800c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 164095026 1250 164093776 164093789
    0xc070311150712050a05090a081509030a0509010f0c02091504050a0b090c09010903080a031e050f061201060f0f1a030c181903050c240403021509101206 67
    0x30041d00b00455400402048645200c3c58034039694031a100b002c9401c2c1c0242200c0c154070103100d19000443c07903000a141b00300ca034440c5400c10b44a0f00c07000012a5244100c640364008901d041c800c11042d5809158140b40041050400101a401c90fa00044504000b06d4080c0f00e00e0344142d0b02c48032a0709041c86066808074140804016030244035000585415006200301112440001e050140303900c240082c0000355440441d65031102809400500a45550001401c6c241c0fa4001e640307000c00f8003801030383d01884102084126070785408090000034410b0000d048095901d4100010383ea0001480100c000c06800000c2d20207507041402044600d00d41c803441e110782250034405d10811120b408201c07800c5081040420f6040050700000ca40d031620358200150b55000c01303850001c188034020890540c50321003100c8603466500c0c5440c06080c5101c0c100003a184504042c0424401030070001480c500000b50380e6512410701103002d00003a01da500d01c103000c1000400d040c60450042090713001c0c50016158 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 164096276 1250 164095026 164095069
    0x216050102300f031504050105130f0902030d0e0103060512070b030709051e040c030908030c0c120d0204080f0f0d03020d02130b0306030d0305040f030e060c070311 72
    0x94240001d40d9490b000c06001540c002111408202c0040d0303031031400b0002203240380d45440701030345a859607850f0800c903000c940b075001c4004000b00d14034091140c1410f80d0340040c08400504043c030340c4400104282940c0c0031700540d481241001682d0308206d11542d00000d951480d5050301c44d1800102520029403029008140c5403482c44003c800c00f207a1001502c030b605642036120740d0345080c00c88103c01c4036400303a07070045030320100b440c20040061485050840b060302c0600c00c0b00f42c0000b0072412030725500720280500340140081950350701c10000400500c100041114141400c80340050803660000445180595001400f003140748000c0c80107520501025000c0c12500318280304260b241c2d15120540d0b810541c0c0065011010b0710b059040d02c5080c0e1010640340b44942c0c9a2044494039801510050b1180c810860002c05581c42805003d1050fa80300d88070701c51760310f51680c0c02d803811050700117951b43c403030828403020000810800110b0b00440c00350042020725600c003001c0c0a0914002000b1403803025 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 164097526 1250 164096276 164096279
    0x3040609090504020303030a0b031c020a0c08030a02060612250e06030601080c06031e1003060f15030f020414040f03080c0906070f05030c070608100b0a1215120506070216 75
    0x245c004c0142c03584440e5a41002c1031078880000020b060103241c500034070f2485504d07000410803079070000740910a40d00c0ba1140c01041505c034004d1541d00c4c001d003007041005070302140c0040e50f98200496140c24070038081c800c90320440d01800e6a860701d109a4040c003140004c01e40c3d002c01c41c941d0800d04d0290003400a130083c125035410001d490f91038400740040c0034000c46001003c10f034450045c2100032421020a4003071401d50521160030351140c1190310043d0740c201e08200c80c0130300c080514864807503041c8901c090081506d1540c1c0d03c0c6000000c0308502681d1040e030b1110303100c150b2130100c441517104074821790010402c6103c901d07000e0725212018040d0040c10074148624005030722070508484502d0707040204001102107501c2e0541c51407040704c034210424041c0100001d112500047c103140a0410b41c00000c480b203444410f0086c1e18001c0c202c41030000381c481d54140700310300003590155403090b6408181d003e006450f4880d036044c081c01c24a00311250340c40f11707040000c42981171060401102940f045241e02d80e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 164098776 1250 164097526 164097529
    0x80303150a0506030a1806111305010e0120010f0e0d090602010510120221010e071d01180b0d0f03030f05040c05011d031b01020601060203032a07140304060909050402 73
    0x203000c001d01040b1407035038480804000d01e05418000d00c551f5801001031011040c01c1614aa0a8100c0d500326251020400004a0b0030b41c09103107040a1075206035244540c2504800c00580b8000312004442c0c081c0d503032060806600101030140080c13a106e036600414421220a1006020030385580c801c208692401060000c02640011400b0488c0d4014a002100c285103000040c4101a401001c0300040c61001c10410b0051041d0040c001141c3da030b01c280c03281203654590030300f050121400c48400c0c00607003c0040c0080c0455203142c00740c04011010004003046460b000c01d0408440031001d58180c2040e003610410143d25014080aa00049a051085003003035502e04a08040314001d00c0c0c1404003103940c11800321491010b03005c0c0c206008040b5041c100803a00365203001c0207a0141b01c0d0050240700c0021500c076000001310303405842c580c0a0f0840c10341610f50350101c401e6aa51496003c2401005120082900306aa00d80d00ca240f080c051541c0f82d2078810302518442c0d036a400100c62900b040c0400015 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 164100026 1250 164098776 164098789
    0x10f080318041503030e0a060219260406050d0b04090317060303070c0e0402040b06030903070f0206120403020c03061501021906140403020d180302030a0213060b04080303150a05 78
    0x110101c5180768030300d0945080001c0151501890030515260a06800000d066121580524142050302d0049106840c1c42080342c0713425080d071507101880d03440c420785400074208085195005100285940c5555440441024140e0040d4010400540040307041d0458242920900003482c0c8210780c200524801c659004d070903070800c0000221144416000681541c078144101c504099101d18171211194940045441451055909a0185150030008410360800d00c04a0740501c0c00300f0300840c00c040e2240c0d22170400f001c040c03100b03e8100e0024000e1022005e0040c0c0c0e5a80507610039005801c0111121040c036260180041014481d008044c03040d85c4266000305030001d56400c203182186417083d0600303004029007480b8045094040503030b8204800c0c9517010039508a0080b1030303a10080c1c1d100541c445d2914104160001a41c15000050090018900100c03000494020702d040481d43c1a900c103441000e5400c1940b240101303800020400000250b200031070764030203c003107818100850074400842e12 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 164101276 1250 164100026 164100037
    0x612031d060c100c090501091a07211103130e15030d0503010306052d0901090618050c030d08011503062301030b040507020d0e01030f1104030506010f0803 68
    0x3030100c44016150800c00003010000912405440141d66485a0403403c2d600c07083c0300d81020020340303041540005207100d440400110380c030583d0341103090360619100691080b40100c094820410800c41c11000a0000100100030b41460f000d4144d00b140c240c2014002c0c01785107074400c100c0d802c00c000140c400344000d0325010a442e1b05408807412582c0320549902001351030340d08143d00d807003100b40055801d5031040095068070700c100300c188010b4031020015080050805078902d4070214206281c9503841c107400f1200e501c400e11800103d030040040d1611002c441d400d00700c0a602c215042003107810f00c0b074108420b1010690903001070407400c030350b0900106000418041d00a01c10000f450661155200f90400e0014108000194141e4004111403402c59542c0b411720703034086030800c1c0301002a880c061240600c00c07403040d00a00b030703100f014801c220b030100b540c054528140760352440811180c40440c0301d8411400c01c000500d81e6918210704109140c258142e11082100c1c0c1030407420710980d8004000d541 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 164102526 1250 164101276 164101283
    0xa060506030a0b0d050604060501061d01020d050313150204140111030403030305040503070506090c0406080a0302120310030c030609140304031109040f12090302010f170612010912050901020c01030612 88
    0x40f001580400160340003150300c800b07401441004144001e010a0354010b0341280c4050b12000766418071080310b050003100054800b405604401208d080c007a028800841d409080c0c401081c48134521665440e040032103070400d10102960210341800b80c15200030010242c20024240300031280c884441040d500c3c401c0d030000404040e00c45020404102080041c2d0b140d65611405503501440c294040503582c4042080f45441503092180001f82c3e04004a94089403035090744c0604002c84408206044c00c0d48040e044640349039000c800000410104503901c1e01a52084101190390059030070303da500b0342149503402c140c2e50810841040014a19641040c8001003510000101d40d1135081040c1d00c881c0701d200c00350800c1c903403588030164240d203d0001010f030307031003620399465501c00722904480040c3d16043e0b10080403103003008180a46041c03136a28000200e40400400d07482c503281d0701c000c1e12032583c00380100821404654020b1543e018010180465020b103010010140b0700254084011810100038 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 164103776 1250 164102526 164102531
    0x6050117190615030203060405010b03041524030311070b03010e01060309020609040603030201140a1a0d21080406140c090616060e03070b150918010207150203040204050a060506030a 80
    0x60090301c8054000c1002481207121514007102c111001501035441294003e12036880c00001103820411901600e000c0c9422032101020001220180c000400340d4a0352038051100754002c05070440844040300028520035503c1c4d40d04400b0040e01c5c00d207000959000a04110b20510051206040c00e032003049c11103000f8136000c1610740c083c1c008501544a01d1441b69040f03410060302009254054000d40c401c2860b81b00076031040c0e9281c1a02c4021110420700d071401c44103440750b02145901e004190560828095046480f15080c0401c8922294040844120200c1c180382c0801060094500c10025080582d192100144c9012804030490b4840e0000d402d1144001045800b808042130300b016119641c403807410000740301e410304d00b2580c980112804884412001d00081c803900508040c40c0f5010001074081d485940f20383c0c0c0d00b0b102060035402401030565003808148042904201e06840c4045000d10059a0f1300b0140144416210010030301001300b41852000c1010743c0380d44040b03070303070100c0ca05500 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 164105026 1250 164103776 164103811
    0x220b1e130e040b181b010e0109050405040b010f08030418020706150929180403170c210f0103080f040801020f0a09061106010306090804050d0c06020106050117 70
    0xc46103030005500420011040c00c0100820000c00d000094012030a108400850703540c80b0b90400d941e0084210b900c3d400015568031030440c0d50040c25440c0b0811014100700907950f407071760003041c200c13801201c080d644101c20a004100202d030100307011001d40320350005585080d0038101c0c8801c0054058207941c9849600007078100c07e210de1940110003400c1050a9058526954503910000c0c0c2201007000f900c4d58401c0c1146040d4510a000f501c941142c05000a4080c0482c49860150004014015818840d40b0605400c1c0c810100761103034840d22038598190b842d403d80d030880640c58450440c004501d280c3e0442488000c025210120381102d510003610b40c0e075003c16a042c11000d00807a03006000c1076001090703040343c481d0401d01501202140e651403c04103517079207808a4100008801440103500000018800b240803908040d0440b07006240d040c2c41c4c260340781d021800b00b95008400b5111000441400e000f103650a0240c0b000904003440c002d0f00c0c080c09010341d80c0045001501500f00501400032 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 164106276 1250 164105026 164105047
    0x60e0114040b0f040504021902010b040b130b04090803090d0f080c0d0911030304030507030605060603010f060e0301060312020c010201141b13030206041e061704020907090308220b1e 80
    0x211400703048060802e54694032030112310510302107000840400365003407c151101e103081a22891880e280c0c02820011014100071721030006122980305c1c15009a2910302400125140ec4021806000329100406c4110b2401900600c1e40b0300718210f04040203032640c10700c000108000f0540c0c5001603c000c0000c0c220249103030180390701080300f01954040c0000320700001032010108043e42100c0c050882444169510b804001803441b0901031980300f905a00420701101c0e2064410101c1c0380e10260000030095126200c80003066101c0c9542e10040e44450031003011568280282c0880c0c80d0103020008203030501c00e0880000f0560018158410000402d42c001500c502c16410030003540c0203000c90355500d44402080c1c421030241d80c001c14540554610000b02e442c0f00e100c1407843c03414002c20071091a20f0310b600700807040c00007074032403c10801d102c0004030100f4901380040200250780c0b00e12108003000c0004403a5481c045602040300e41c4070500c100f40f10480c90050450f903064050b4519992206d1020 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 164107526 1250 164106276 164106307
    0x1e07060c02010b2b02101d06070f080a0302040f170f0a050c060d140106030902100e010c0204050414100506010207050f0f1207080d0f03050f07093c060e0114040b 71
    0x10040e50201035074050546ca15000301d81610340e60b200481c1da0449003401c609002d458824180002e01401101c03500f14046800240034201c214a285005854566a00d182d224078001c680c01444050b115110300100c0c0440c01c1181e000d6909000010704801c2c1c480c1e8503950344034180b00369540d010b45000110f16005865640c01140d105200000c0c0540a584404000b4001c00705074504a01821640c41c0d84a02d2902441c2910b600c0c0005070b4030320314108219400d01c0098100030304101d41c4052a03040082c910117042c8030170f00840045500024280c035240b0300091410325154001409201841801111030301e030341a41b440c62070025590074a41130341c140b10091811400d58015001402018130710204e103640030034034110403945564203000640b246280107600400545413040481d0b1000010000070744121080c500003210f21034440854000d003280f180e035140600040c05074080610000b03104142d0003c2c400450700000f881c00c619400941c944d00c0c4000c2c411400703094491040481e10031050101e04 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 164108776 1250 164107526 164107609
    0x1b0c050a0206160c0905090c010804080a030f090b1614160602130e040b01090c030501150c050124080d0903022101060b0a02160801021e0f1e07060c02010b 68
    0x104000c1241741d44001080c014113040d01e222139140281c450707103011903109108041c0500d0b008181a1300d00444c5a80c2035004218600e0070907205070301d07141007002003102c2191a5110301d0400d520902c1c1030415503002001c901c003206005004201c184040c03004030301c4502180541c503600020050381c1e15034000e440c000104966100003042c0c00c990007040f04115201d02c0e9141218038144040c0300719a0302c0441907054030400d005090050035108800401a4031440b44540898080c10000907801071002c100d00860140b03c00c00100788140113000c2004190801800c2e0102510b454a281503a095a0004556028502c0640c0c1c0d2524603001000081000b03501c0a002003101814040d03598a074510081d4890200c100b011062603884440041c01c2401802118105104003003a42208007021441c3c1c0d001e171700b00b046a17955580051041c401c11742c0c0c1820030780c0321442541075444e803128664a4680180da0101c034504c01103904002408045031120450300b00040031004083c10b1060308400000314020f05d6 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 164110026 1250 164108776 164108783
    0x30405041d160611060402012111161718060d11160201021b0105190509041a1c03050708030402040915150e10170a0f05011b0c050a020616 61
    0x850542d28840700700c039040e2000301c50064440544242080303000035280ca404450207404100f086000c84155150700810006002d04018005400080c4030025006500030005080c2c0c290340c003d0491040c0122240c854140d200303043c01191808481c0e02d0701103152072481c58098090314001c41c04010508240d0807250104550620258036140000e420240280000304140d016000e40340e151202100e102c9410560303510f06843d0585440e40b256610784201681c100c81d001049418040100c80b42e41da40145241b1a27a48070041380862054803c005003014500744a42800d80915a064000f03034100c030a80f121940c1007241a070320b03540d4034004200904110308008001090a6850302c2c2e181c015a80002841c210a03103c40a0306a00c650104842d090151005000050040c00c2009100005400710301c0402101c0196000344403540c0d9901c1005001d030400311026510b03142c4040582e00300012641d011800361030302c0d02c0c0e154850746589864070102d44010b400f0307000001e03c16a0380c8082000252540d40d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 164111276 1250 164110026 164110033
    0x10c0e0d110613091b030b091003030813050f07060f0f020615010306030209040b0a0e010207170705160b07051203070c0f0501021605011d01020f04141309050c03060a02040602030405041d 82
    0x5140d4111a21000c4070500e07170200749002c00d03d51807030422142092040700c14140c0c0801c20341c11500c01740d0303190b00010070803c24450403450a1000034070a106204840034500018011941041e00180100701498480f00400840310480040e4990000d0841c1c0c01c0b0340306c10b0103503c440315058012009040d040e0030194000c5054070901c0100508030200500c0f4a48002007004029406e6201609074800d01501a007840c180580a28001c1d0b04100100360b40e6115804a9021500d214220303800c400176a8040c1c1d001410210341070341448800d0102d031110540303407688685189451030014000e02c0a400d0098880c0b10042041010004254100da02242403031030f402c40045010f180440c00307001c500c541202400030f560045101c8010500136290444400152941428200344d00c41c1c10403682092305030780c041140030440f00703040c2c4244a0b0040c06030292014108102040052525240f006082e90120300c0c410841000003a5020080d542030b03c104440100702c00141d2180d650118100e1040300c4141d01 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 164112526 1250 164111276 164111291
    0x2307020d12051c0618020d0b030d05070302011506080a02030a11030c0405010905090705090607260a0e010918020912160602100216120c050a0302010c0e0d11061309 72
    0x20741202c00341940c025820080098000c0842da081d06440851058444400c00d160800381001e400350054511500302460024103a192200000c0c030300b0320a9800c40010031b400050f210141079082c0a91039802e46440000a03d2038034024004000201c01048021007580c048041a485010394200650704081141c2141c0c0740d08000e01c0b203d0159100348583c41c0850019100000c9900301602564030402c01901e4250602d80c4200c14080240d000d0441102d1352011039110740030070499243c0c0d01c0c1c03e502100030310700d45645410801501320015621000e041c080001001c1000d1580e060052080780c0d0905800350b21503455101089004400340d284640c40d0141d02c4001c2e000b0469003007000105c0b20246d084502d050950306000d0200e10810902d400d8441540020f1340c0440c121a01c40039610b40c0c00d240203401c1c4842a02c43c107040c02d040000450041c0d440d40c0700c119aa540c4103151030b03207110302140c5410f0301c14502e644001d444803100c80494007422001c00c1910892003140d03d65402003180c0d903130500004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 164113776 1250 164112526 164112563
    0xc030509192904030210110d0306030b0a0b090601110c0a03060e07051e010813060e0105010302031c1d15030103110415031e0212030705010212072307020d 68
    0x4210b4054410345080001080342a9442056108412290400400d00e0301c0e0843e000c0c8100c09546910640500c0811341b12041020350070441c04c940d1480076900098054103601c0d10212402003d00355503010350130070310085241d680b5402220b03000202401c1c41102d1038800310149007014190030050760300441c40c030b1000040c01040e40000005202d44400e844030191564200300040d0b4100007040d10715903800c0d040c407006501032410190403d2142c414115800b406540b042e083d02c100c00b51084e11651034034010421410200120180207032030103418041c0c00b00c100d000800c40200710560940030403041400720b80640ba1000e052465005120119a070b80d0307104e003003c03045440081070050040e0b150011124850316100d00f0142542c0d40078000032104c65a0f1001c621340030001e04401d80e40b03c0390741c46007041d9a5030200b00401d0b40601c6200090b0300c079483c032401c01a1152000b04400240444c0c0c20004507a403000c21414044410181c08150701c03040c16001240300d040c44071310000c01c1e0504a11814111 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 164115026 1250 164113776 164113819
    0x3050411030318030f010501080601031b2304050601020c01050d02090409050a0302060411030604030f120b062d1603050c0102090409030903020f100e010e010309020d23010506100c030509 82
    0x650f4082d403c6901014092601ca801c8400905c9000142c0d00305c1e600610000e0b1352407426a181042c010038192009407112407416680e4402032004002c01005c0c0b402d10781e0303418103003e015840341c002d001400c00d240f14800040e1251050500c85402940d00181c58078040d80d803a4001c03426180c00c2001c881201d1494a000380d41c0346016079050303420030b14040340d0381c02d207190005985116543c15622410f4050040f00107030ba81d402c0c8a5131004510791518604c0c2c4181e11100040d00c9401c0582d070030a00b10589005680c413626022011b2803030482d200300841c1c52080c50328145c0c4090a40e05180680e03851380340700726031030080c02190750465019080401140078036610846207000c0c0c03402240d1010350300e048241041810071103601d02d4004240306000c421400e40c042d406000200c0c6041c100400c144800d58009446003840c0031003184d0102000b540f064001c0c10710b04080640e180c1050080101d414103100242a46e40170141c00410401c040141c0c038202340c424020340c4c21500000e0801d18008112441c0d1860 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 164116276 1250 164115026 164115067
    0x140111120a02030402010c030c031b032003040506120705042d14010806100c08030c040e060111060a020901090306021804051014150c07060503091e030a030504110303 73
    0x125200c441010500319407151080ba80200d5050315245101d00d0b840c0d9081e14a03118240b015024081e1001000390710f2080c004910201a21a030740c1d10f008a17541e1081244860f0000f850740c0090352050009200503143c01c0100c484207002c0309110000c0b65240c0b542100c0510858001d10b46010600380c206a031000d500d00a00380d142450b003c4920040e80343d0342128040d04485d001a40022043c0700030800c9802c20880311540180c141ca08881450103d46034a0b03002d501c16510700040440c001410801c64003403420103a04410246403006e102c0710000411607031050050610350010344d000804846d982c1c05980520700440d8003900075900c0747e0503078191a07103010040c40202d000c2ca00340000100000e00e2901064247c501d907800c044e0f6140038800c244812030700302111459441500b08200741c13480e02c00300103003802803040e542c07071540c4ca1410808090401d0520300ca920085094030150b03107040d00010040d22101800c40ca4006015600c0d414013034148a00301242e0f80e0140000030f00211810301c0c010069a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 164117526 1250 164116276 164116297
    0xf0c070f03030318020d1203060b07080d1d030301030b100504180b070311070305030603100603050a030e040c050d0b1801080115080d0207150c020307062106150c140111 74
    0x201e9041540d2983d07021388004002980140c0360640702d40040c01c0d460098815503150b10b00090880d440e212200c03e0f0b5846800187c0e100d50001c01c0c0c030114400e15005101c44400c041013031400521110089607945e001c18000108002500c0b000101d000030850301c901d00030b000090040c8410401080800c10781440c440702034800440341d00000b00c22500130b024056048840310714241c5014203903102240d007600040c0c4580c2d030500405480d02c0741e5545500460000e98050405054821400d00e000340c440c07140fa040040c0102d09041000b00d820360804152000e280e0a0311010503c114900d0002c0c10140c8480314240203041d461001007200300c415400250307070036000210415060740f614181d55481880c1030805d00141c2c49088140503404080c440e14a5111b0310b0b0602030401d40d01a0300080c10481a50842c800065010501e01e000384080445540101d000301000c205040c10598018a00f0810f92007a406002c01c002000c0c08005580300308107070031a13070384000704050b100841607000303142d21260190 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 164118776 1250 164117526 164117531
    0x210020a1703040308060114091e0405041208090610050103050705092116051003150b03070c02010f0302070b0601110f01050a060906172116060906061205070b0f0c070f030303 77
    0x601d56502400d55100104223000c2d8880c1130102c82d04c01c100d0030308914203074507640811800105440b46c80e20b010340340c043c5100b0a41b01b000091044002407004030000c10000f0164080024030104102160085c41542d500b0300c1d000c14030360b643d01c4041d2002d10600c4400303904025449640e00c41080384040380f8503040c0000b03060f50000e0003110310001221845020f400d40c0090980101d850f0b6900070361028044100e410800c8050070760300c021039100c2d6003040341c0d140d000c81c5000741c04070219a4004d807041503011446c14118240442c54a030801840301c000e094505110340c9000ca50410202081010740621242d03000784043c0c5841d14010002d00078910a01660a00740349010400142821101040c409540003c140c0c400203440c4030a44001150f0140d44252800c205841e003246100d898084214084c0c00045180c80c100d01c2d200c000c0b19901e5210407101070000c400f000000704013203004800c5480400a1580384d540c02001601d46105c0d420b1a40301364405c452001402d03403814202e0304100c038000d4404 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 164120026 1250 164118776 164118781
    0xc05060a051917102601060308043f03080411100e03070603051b0a1224080c0a052206120b01081902061605030414040e0304030b040210020a1703040308 67
    0x612134000c014040d4241d00c0c4c400c80c40d481c8801c2503041c03048a81030442800480e6a0340d480c1c54020650307101d0f8024046010046891001e00740e03003542c484034580b407942c02143c0041c2d03804a0180ea4520305800040c1004214004102800214590081d6107600208448041d1500d12409070000c0001300041c2d01a003d030030300000e41c0354001e00c24640300300c100148280c100d00c40d604c100429548140031840c00d0001211186c95a01443d2180a00b50120340c101081c0c6100680d25010556481e540158007036070040110f000561218004401116070603501c0200500d008003c2c3c84411641790910034070f03146041c5002070100180030b00b0017140c0d8040d0401200b180d0f2103091258942e04031030020440524040708420041c28280c0c002c00c450b2b4102d0b2041c0c4800300c819649c0d10b003158003d9011044c01d0985d54448a00741c038141c4982000c419048000354507051560340c4500c1050300007440a03114456070040021020b00a00c0b0007000c4c1588007115901c160348070500340002e034005840980008540500 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 164121276 1250 164120026 164120041
    0x4020c0717060919050f100e1c09260a0515070504060207030b0601050d0f020a0311040302030d0c05030d060303080a0c02010e0601030210020708010f09120c0c05060a051917 76
    0x3207950064000d9401381812210500303404036644c83c1c0d0740c800c85980c0700f20103040304a2142408590591003400002240c1707174101d031403403a151a91a40d2040c00d581c4808490385c4183c0c2d000391021045401d9043c0e0001c40d04400c0c065a55281d01130743c101d0849002c0ca0351b045003000b0300820402400010203100107855118200115a1070195000700d40141c1d0180c0c9060000c00ca8942055501031014580b0f10300c1d20340c08400d40d1041c0c1da101c4200c8011141c010031804100798242c000e035041190f55a0400e401c141c80c6400003070b5680030001e4918103114820000c0410301005200f156460a5081c00900c0030300e95a2400400c00801100c40c0841289002c4844012a20601800d50964510b00003010f45901716000c004420980c8203501042d13118030100050151401e020301c1e9509040c0c03900020307041102d401d01211002e000a054420009250001c10004892401c0b080030b841040c2c59460712008200c00079942440351820100115154014900c6016480f004200c07001d1415403c0701307500e8a030681c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 164122526 1250 164121276 164121283
    0x100c1b0b0f130f031421010609060201090305160503040806040f1707080306010e011101091110020609030a05070609020a12050c0108060f040e010b0919050f15010c0c0504020c0717 79
    0x400080050500e16290f0b0007107803064000c036040c5410800d459280c0320811082400c0703407080004603544031007104010817115400104c0ca200401c041d0000f40081342c0c0740d0b60300038814410010707112036207000051280c06001041090343c0c00f0389400e100311941c40c2040d0400a06070349000c070040320141c0c8401045e103500c020150a9600312603002485c1411600c81700010348034000180f4040c0e0410007d20600080040300740a80c41410380501c2080003d912240180403c480031444500d007594440e0003800f501000c0002100e9044003a4544941c41c0e130b0161078148098016001c02035402428404040b402c0406c0c096000000c40c8510200c3e600540c50400555540400f00c2c0c80640c865007460040000341020340000403d0b030840c10000408050a0700000e2380c1407429680310303080c1da140c0b00c116558255184145034106441c071103416660300e850500240c10640200d841030410944103405000c2001c1d1126a0f8045c000045c010f546802c200d002da56500d404074803400c0c3c5c0c2c07072440800715002480c011 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 164123776 1250 164122526 164122561
    0x80106030c2c04030f0c020415180203071b050f01050705030106031a0a06111501260f0304051509040e0d020d0801030b0a051801090503040e01050303090102100c1b0b0f 74
    0x40c00c41501c1d55a0f64409440c08640003c284040c030120754407036401a66280704e6040c03400740c0021102890750500d94452001d00c0c03001c1032401c0a502c1003040c00a80ca1300860b4070032a881030176840c40200c400030b203025401c2c0070749001e030f205403907082100380520719400002450590b15244e400304581c610000c3c8400310159003240b06500008000814803c691044148514094408007203c1d030f0b101000c007075040d140030240e0014940e03500002c1c980b4182540b0001c02c861188100c4d0091001030351005040e5201d00c52272040070704c0360100522100b60240d4480c01c0e9044030b0700c0107000300701c2c991071240c05a4a816609091000601410500741c82050140e12000e058a40100980300c1680d141034180005000c00313403801180e003140c511241e2180d5024000c16420a200c2c0c2d01542c2c407986400000d40d907112040c1c00c01c520a420a0052a5199900040c02c860b102581203010490103412681610505101c41018050b2812405d51005010100c90746900815605036503555995400151031180b1030728 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 164125026 1250 164123776 164123849
    0x80411040c090e070201060e09010518030c07120f02030a0c03030206090d1d03070312030b030d03060803030402011d100c0b0601141204020613030f0605060f0f19080106030c 76
    0x2042070502c07201c410003c0d400d501c40300a0000086040d158410f040c0c207400d0469002455039160b034204001c07144140700144805100000540c186510510115101c1c4640c0c0038008090002c0420701d000d00400f01d806079121398016040c2c0e440c050003030400540c401107500003600588142c42c04113026201c0010b8111281a45d5903841d419440003d411907820390b0f02e03403401c660601c258040070010503007010395109141d0701c03501d00003a00d511040030726081c00c0510070032200703041c640381e020807a08201004507580180d091030700401a0314180301091040d054a40c0c001d030812050321232906000d8028180f03031030160140c818800e40340d480c100111104402e16031226400c0e4802c0c4844406105003452113030304a48020003141c10104c080305080c0a0b0f5015906c2612200100000001400020305c00c40d500104184d800c40b208404400115420102540030103000c0c0001c179410180c0c10050b0241c2401401c141d07002804040c2d034030b00340810400c21500895288940401000c11601d54440200308040304 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 164126276 1250 164125026 164125037
    0xf0504060e060304050709021603090f0609031e0b0106020d0314010b070f0317070309060c0212030c07050f1b0307060915030b0402090a0e0a290904031202030403080411040c 76
    0x1030010b036802c060021030783e0b0b02c00c40c0e10101d9084011700107171008000d01000c58018641da418020100100760303001c0244c01d50701442c2880342d55880343c1d01d4400e0300d400c55240350a004048800701c1441021000c0070f0b105000b150004074640782d01064004038880d2035030302400514000040521414400c0c41403503401e001c02c010075000515803d03800c0354124080d040811007406260310403922010200c81d090000f0340d03940345002c1041914480c04503504054030050202000b024010034492102170912114087e000c90b500e01044401c2144404140c500c01c19100c3c1190307070308800c100c03540002c00600c3c424094180d021070200d2042d80410100e40c02c280c6002458000404258000d0016010103901703e50200a9600207445840050008220b02944c1203658602081d142c01190704c0040700081c0c2c10071a00302245040717000d00411408010881d500702c2541c48510301612141030b541c190810041c0048100002c0c160030034071f10351289020f1411112414190303000c2004480d1200c50010100d203 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 164127526 1250 164126276 164126297
    0x9060f0303030b0a09180c150f030b030f011a04062306030a141e01090b030318180a05060a051203180a0807080c030d0e060a0503150618010f050406 65
    0x244650490f0034404800f4000310005611480ca040603110007101060b0802c0c1c1184064041018021000f4010310106107984507021001000618044000e0b189004064035070410100c07550b0284688042044c01e840204080c0b4040308603007103000d09900e5024800e07071900c00300281c018900607002110140510000040e03a14440420402d0740000d0a0860010364030000100e000f40e0240d25035009144003651146e80b00c03005418001a400160888032003c0d0501c858459551400403d43e800320f00802802100d00c00f21750040780c240520001400680c0c0100c42c1400a8510294003580c00b0340c8040d91480b03071071078654050140340e10600c0440300480c2c0c001c00c41d80e1103d0702020a40c003020b4800820001030385a036821400d02d000695008509a9040700001d0302e030fa80780801c12520324803400d041c05a520190803001624500915100c00c1c01d02c580000081c07912100f000000c40203540c000c00198560241e0404625858900d042c040c4c007003842d90b030281c0b290a000f00c2c184c504803007607503482800d010b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 164128776 1250 164127526 164127533
    0xd0c020901030f06060515190f0912060e01022802150112060e010e070801200a08070c080a12050601030510150e0310051b070c06080618100f09060f03 66
    0x81622060a8031407640e16007000c10701f9030700e020005000d07613007800c1c00640f40c900b0700c40403a101038865114801400102d1107010803140d04004080b003240c2031410901d0756110349003814009025100071442d42d6510000f5040c807460301804400131a01150302000c24407410941d401d03070752002d100039a507050b034003103100401c003400b410080505a1846880040381c2100031019103070a5603030114018402723421141062003580d0003480745c00e214105040e40e590074000118032218503441110000030402c80340d4000a0342c190300802c019a01164483c1c1c2443e5102d5500784000c1c84901102040c104544c00c0c8800b00d001c0d9132007405954059405040e80750607070b51420603000001c58406c0b040800344070700782c410000030341d41c244041c00c0030b491040e00106007032038034414411804e2a02d40664005180c1400480045049410100d059450a0030862601d0301c60100046462001e02d00c6d04208400c100d04204400048424034411030f0880007601913032036204e0700d41c4010f544880c00f0300d2821400c00d440c1040031 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 164130026 1250 164128776 164128793
    0x71203020a050105040b0a0b030307020d060c020a050709061a07200109050603011701050105090412031109062206090320010507020a0f050906060309150c0c030414030d0c02090103 79
    0x40511900407141e000c0e40c69a500c6003555011035013620010f503c1010407181c2c071094050002590300880145107441c01a6002038103110722104054085641d941140300c00d03d000f041221000764111040b03c4d174603540c2e010840017a002c0d0340540f00c0311000c1e2034400500d0229020641d0003807540502840810040655008072041e101c4075407904121070107900080c1074441200941c0a41b004a01640d1546004a041801d4038030680c0803500805e070710000c12010811f41425116815041d01c4c000c1107006800548503240e024011003144c0c400c100007800050020f0b00a100340440540924280c1d1282d6101ea00365500c40f100d03c40a003680c00d01c4480e074050003d443c0318910b200e010506200b4102000c60300400c03040b8959400055880c2040c1c2414000c0d894407000456004174201c2c2e109145251000846484a240c03600c000740150003400414014515a0f06551a020b04403044076140e0ba65000700c40c0070072a80403040d5000303005070459440b1061181c00040e801e0745d0081c1c09a5000d900c0c6903240090b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 164131276 1250 164130026 164130059
    0x50708060d11060a05070b010b0a09090c090b1b0607020c01050711060c0a1406061e01031e0c0215010f1a0c01090b0403030203060f0906031b04060e0403091d0907 71
    0xd241c0c00a0382c4882c80b954440020f0000345106548450300c60010b0314007800d40690681184980803070900005800e168003200c1d120544003281d8011074003040070070090f22001d0454101803441c000c04a4040040040d402c080d601c17102c000011101e19454110050b40c6405691580b14001202004504040750f20038580f55041c50001d01420319184124211500f4a81c1d05101100c1ea080000455400740750200400c035040007080b202601c0e505d40301e0051241000209a03030034185512041007002e50400140b542d8050340d8021828012003043d00c130002d4841100c0d289003240c3c4901c030070012a207941c5000000c8141e420a1040180750b6047c0c00d804200ca80141201e040e1380d64a030f21505c0c00290b00070f1189801603100b9100542c0b6800c00c041044124811482a280a083c400041059540e00040c488241d0040a90900200071414000c0f901a00341c5800c5100e614040c0d9040c0000c05034040003050880f0668008528220040a840f8550482c01d866907040c5501a25060101c001200052507 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 164132526 1250 164131276 164131283
    0x60102030d1d06040506041a0c040303031a130b0406090b0d110a0f03030f030b0105070b0c03130602040329010f05010e04091a0402040e0a03080406020702210a050c04050708060d 78
    0x12490100060b01034500503013110121041e0f040701050000b04001204024086c01095884501924049603090400d0180384006800c241e19403500510301d032440d6100800c1c051016082180f8880524072810103400c0c1450b0345030241c0d1a043c0e00181d101540e00c10410f20800c010303c1c41e800450305494296070000c00070302c10742e44004605030000b40482000004002035105c0e031140c0020100c070805c054200c6518400c0746051003010844400000c8000c044141c0c40039810040940342d0b04d4500412400e401805002461644001800300a01c078002e072504181401c994041e03040d5410010415040e01c8082c070071591105280076040c01298020310031090601d01c041d00000d10920145c5507481c401c50120303047d003412900c0e11300f40010f504041c024140c0c21400840140f4000344039680050202c94011300140c0410b501007101c3d01195600c85400d0416460030b9007524070b01e0900a074040e19808800700865241c45401c19a980c1c0b0705090003154440d4440e5202d84002c0e81d104428002e0180d0002001c5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 164133776 1250 164132526 164132561
    0x7060b030f0109050c0a08031207030f020c1606030b031005070e0405010909020108010602070602030a05070203030c060f0f0a06050d11010314270f0a0f030203090603010923060102030d 81
    0x119680e440400c020a00441880004100f908950138042d08101440065501910384800e0038041030100100303c03441145401c407a500c090707a80c09011002030003842c0d00c51400398000601c04d00c3c05800007400a01c4401800d4081503181d6542108bd802c85600086041e095002100c001c280c081d080d51200354031002d5803d10110034403500001404a900c240c10114841d41d917180314800390f5034800a00d41c00b52060340010401907007824000b9613603020301d14070700c000c0020028100c030440d1004d100f40e4182c2618001192030900341110304414500c021191411480c404000056108503107004078070496101400f1a800300b03181c0c0e03c82600a000007003909040c5512107039681ca2403010758182d070f03205003401d070043d00c149001080d00e105a031500440014983e4014050320084140104020310031992000c0720b54451800741c6408d0341140078010100d41d000c04040000142e412164102014403c085004040d1210707201c03220f51a186000d44001d40187d10078052000b40e0360095004010400d0210741c034 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 164135026 1250 164133776 164133791
    0x71a16050a050d090c15020c090a0905070306020c030901120b0108010905060d0c0b210103120f12150513020309060105010e030102091e011b0f0f150905010b190f03080706 75
    0x1400039504846003c58040341c820705c04120003144588041000d19041c409001381d601500700190750130001501440c1c4040c0c2c2c90740581304110040022030011a403100003503458003d00710416072644c100d4030303600740403460100301b4021001c0c640c400c021030600c0c1610340480356405c1206010091030024251600441c250071041c0201d0316040f5840e0040185120903540c4076400c50301c5550000346101601d58210703941d001440020203c1d100d0203510b0300707603240a91414112400440b0003d01e803c4020a52903d40124092201034041c40402035a000ba02d149000b041c0c148611006c03440308440c01000c540042c40180b140e9807140600c0d8822520040016061003080800511019064500243c0780d0b044000c14400558000107501d13500a0204a442082619516002050407610030001d10340c0c000c10a00004100500b1030707009030007180c04c0e0200000c00e0301b407421038002c0070a0b1040c54842c01c840944402c2a8a68208010070ba509000d42c51000a10750f6503054000e410900c81210604d032620301 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 164136276 1250 164135026 164135047
    0x409020d1d101a0a1802070803090d0e010807020c040e03130e100504020301050d03030e011808030702011515030209120303070c0b011d060f0102071505071a16050a05 73
    0x5035444107414100c05818109041d1000320200e900c80000620060303d40401068141d440c080140c1c1180c2c01c07410007080031036601507030754000c0c8250034004040340b0001c414000d54203000554050407800a80b10050141165001901ea8480441c1c1a13401640706c1002c81226003810b0b045040543c101100301ca0818084010111410416402c45040007509100f002400c140e40802000242020748045140d5410300010034000f640025000d000e050301c40080781c1c0110750960080d030b46502d19039024080c409083c034001000c6e0380140d90542c015801c0c085c0262070910391b00c0101302161603a03c6050070342070142303d0541c0690002101c1070746c003d0303803501024a6140c0600c01984111300320b6503119160b8020b49030160601038186c0161100300002d240600007980004c04098102c0c00840300c003d40c220407600100d2400349079400c001441001d030a03e240074140c002d006424001e00c22414010041048045c031100c0e500102c9501a4070622041040300190094009100782c004070b1900a151240d00103 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 164137526 1250 164136276 164136311
    0x90307020a21121218080f18061602010e010315050d0c0801141b0307020a0809030f0a050d0f03050405070b07080c010c2c010c0b06010203090904110f060f0409020d 72
    0x3140d00b022581c086401c4134081510300c901d106800826a0400c55001d01c4c1d00c51840f1400341c240c0900000f1130001d95a410008080d000703110b004c0f0002d080a580d01c4503904250700c844811941240408d00c0500384003035540c0a07000e40300d0400044070442510703032b02d0b001c10801000390017001a52202a0800f000c10303540c200b805039a40b24840c0760040c146070f05105840e85407001e0761070350030f1001d1281441400f40b19030f0b02080780215150081c044945075511307400000d041c000100c4469009100d1304641c1410020082580c03001400a42c98607881001300310002e40c01d9440480c0c00802582205405003d00f103010005050141e01450b185800d000400f410982120f07440550036000c1040003c080714030010b10080714415100c15000c8180107040440040d01006461900500307690400000920340e03482002a119486c5c40107100c1c0a032070409040008003010380411080c007d01111103500000e0828000701e86410f0300c207601003483c00e4a00a20180203401c841e103000038561304d4401011f00d203c03e41 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 164138776 1250 164137526 164137553
    0x50406170417090d02060c0708060106020a030207091a0409061d01020a080c07080909010303080609011a07021210060b09030705030105010e04030309030e0a030602031014030c010c0501061a03070206090307020a21 93
    0x607c001c0100c2804c01400703502c0d201301640184115400001b0301c1c1c1c0040c2c2d010450200b00c41350800041909201007241d1504695030405082d00b0505c1d01f0880c1091154a030415800ca0541e0380d2024099440705176150700b80c0c820300c41c6032004207002001250703a1a0503600108a80e5015454071818095000f00207011a00207074800d900040d1a0ba003408103074030304540010300512406035610840c0140c0200900e036070107002000780c03052110055003065034a0600203c64610401001084040e407248138000140d049104e6035800b074491001e001c145070905114180c160f1351003403080e8146507144e0798210082c000030703c021002c0145035540452191181c11751000030303521030034001d80c50f0314014219400e550210341c0114980e03406800040c0c115100841c40518028007841c00f204090300505000b03001d407489500c008034151b002c044044480900001840c080e8040358280c5242c3e1b2110100960307640075006001e0b500900c001000c105040d450801c0c6050b52072a06091004201d070381e240d094140010707 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 164140026 1250 164138776 164138797
    0x32a03030403091a03100506160510020c070e07090e040501090b0f06010e09060604060c11061603080901020a1209031707050c010c170406050c0c0d050406170417090d0206 75
    0xf0504188442070703840e43d241d40c0402d40c0c00201c3d4110b103021007002c01c050382c651080d00d0042c5000030301416a41e1030548010300103500b04c01121a05007410011600079801203503550200e005010002c644009241c055501520080d0f503142b0302182403c294003520400039008031041c0d0360f900104c1c0e000840050405224004565603036100d41740c510300260407241e908900714482d00c00442002840e95406d02943d0075500d4516110003201601d1814003104052118450b90102e4041420780c00f0150f000700092256220369200c12507501d074404428241d0140d070400c2c01c0820340401c44807644031040d038401000039001c0c0c90440c82c0203404040c003001901003556400c000540c0001c030342c020400f0034010b03031150144c50b1419009000101c1052a070350b00f00580001c00c407585400220b42c80b00c1c40401680c4a846128043c0d5864443d00320029040380d00a20903200800c1d40b0307800f00803c8140c50502c40d8815900250420f03c105890600c1800c10342c00300c5556540000d00307841d04405a00c52001400c2400132 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 164141276 1250 164140026 164140037
    0x31f380f221508090613110a0905010806160f050403021909020d0501150e090a0504030309020a0807060306060f1205060a0b0d0f06090213150e06190806010908032a03030403 76
    0x3440302c01000d6030001440003e0fa5802203043c00804440401d5111403241c1100c03140048100f46000225000e13070b5940580241414440049035000300403a04034002c07184485178810070004d20034260b07032031101c6d607803c000413480501041001d800c0a840d040c401c484113000040e491520341742d80b18120f0b003003607a00185003651a00180301014005035070140c1a502c60030720300c251001d86000075641180003000301c03002503202c0c4082010503000e80c00c044000c80e8020207000032103484190040c1e480702544240d000190400400148590041c0703101d01038140346d9030307604164404007440807000e03000280140d90003140101000a0750884030003e001600030304400495036201170340004e01907404a4110240140c130411400303000e45882c550340021507044079440311544040f4002034824840c450401ca030012000201171280c00c51000240c3c4200c4007a496400164407611f00440300030354640520a0298000c010300300f1080ca880c50060085200d64980c5e03406401d102c42080c5c11a04284c904501198 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 164142526 1250 164141276 164141309
    0x302010f0503132a08070b0a110a0807050d0806010f09091a09010b09010206061005250b16110a0312270c03150506030303070302031f380f22 62
    0x810009880f8000e1a10b10011b00c581800c1015007500e034450004c400b400d01050f82030325102490188000c0000d41d4100d26910303200c0c0100e0070202d845140a0302c50750f0000d40d00c00c0c00100d1640c0901804602c0420660310080e0840c14003003c2c000a000240845d000011580c0c2480025601c40e00014040c140880030b0325200caa941001915050700a480710348034865031511245000e034000150340080714460b842d00000501c8042e04005442000c40103419184810708001d4190082c01d654001b0f8105540c540000c2007071a10541d4981c0742ea04001000680d5110300c0c801d410447c0d0700441c2890000d1180450024a0862850252610780382c04803100000a2000c1090001406600045404000d001d010b185400c400181e01c921008010105250303003c00401c100c03403921544024012407004003801c1c00c40d21008200030780780a030946214408179442c020114009950b43c014851340010704107070708025071050552080d400485983c1181d0003a241141d85a0008040c071000a0940000d00e00300103 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 164143776 1250 164142526 164142593
    0xf0f0f03120601180914040210230310050d0606082812051b010905010e0d020303132f1504150f260a0c02070302010f050313 55
    0x145226442520903001840307801010391910010907030050003403800d0301010a41c60f04403e10718615404c1145070600c1c000d000d004100240d104076020303500031510951246010001111010b809a50003c5050070305c240000c02805010040c5400c854100b8207242c1c0b003921703100801c4072611244815100b098407140c003088803010900c042c40c149916035840c0240c143e92000b45030416907400a00810100d441d000d40d028480c0b03d9000e66203880c10031450545041c91001050b4041d260034001503800e035103001510b000448000a50700d403c018103070055419952901c1c142c5104841c00102610216042551001843c0400d00e00d04600b084468181c503508035540709000e400102c0d032490521010341007000703001c8e41da22445001c901607403c1c9410f6848000c008411a83c00000c852401c04d0413103070300b091689040902c204103100b0081564100501c40007040c00b280c0c1e401d103510010b804200642c24007100d043c4250000c0d50310141d40144504c45807101d07a80c80c3c5000c0800001010581c0a800341319151 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 164145026 1250 164143776 164143783
    0x2070c05040501050d12020102040b0705010c140406090e0402041805060901110a050d1e0c0e010224070503070215040c0518010e070c150509070e0901060602060109090203030c0f0f 79
    0x20300401c0e1020015581000041000300d03001102c00342100082e010000d00c010300c00d4040718041c187c43e4480c00c3d01d841e06440c0142c00b0788a55105400030800e88929000606100d400f658200ca120f99140005185030000c1207000b10000352003a81c100d0307150200d4080c00d03040d60091540f158440e4000f0019840c159219500311404034440702080d0307001b0403c8070441c0341d000c0c042d120803640000c0000384000c04545646a64124001000c0d8640e041004540c3c000d50003030900c3d41c0c480002e800355050b802d0f42030600b01004d2a00580124280416030101d18154480c501541d40904580100c0e0880c401200030786258080454048480ca08002014845814a214083d1501c446040100a00e50408041c61660300b0010840010024140303600011711141c0c100c202c2c41f82110090400c06410100c0e00079480d400c090061114903151036010a54040301403040310211480c1d43d0180034180d080c840032001900901200f80d030300d84030a110301c001d00c0700d0a1100844a0b040c0f04000c00381e1200e0303d09050709 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 164146276 1250 164145026 164145029
    0xa03050304020a080a0f08160f05160b0918060105070f06050411010c030e0405091e060601030b0a0e01061b02100f020f0705010e120304030c1710090519060f0c020102070c 75
    0x3603034200d2410070380043c0703401c02080e040c1c03503000d17811f03949a03041c60000411361101000050724054210789010240040881d02c2c80e208a000c05074038040c9a140c030700081540c4142e0004c03a4021101120011180e00f200c0c0356a40c000e81c0501d0194608a404c0e02d42c0c00301d40c3c4440800303840083da50010f01040015040842180c040d0a00741800b02e804c95403000f030280310076411600c1c0201c2e03c030400148842030502485581c140c3c00c10040e0403e00415801c590b5540c4111192400b2900e040747c58095403801090000c03c469410030019060782c02c00208440d0002c0084880850302c201160040040e07843c410f0002c400d03a40740c0d07210b4400f1600900001c0c6040c000101a04142d0043c800078070003a60300c1301c1c5d1a010a44203403001c42061001200041c41c6202c1d03580003601024a0314804a10101c0d10250380840c4540303032007160a8034000e0b490220481e003c0383c8000b4216488a0801c000c01100c007002c052881d8001c107400a07070004241900e400350740743c1c1d10903a40140d50000c0d0200410140c0c0a4400 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 164147526 1250 164146276 164146289
    0x90109020a09090903080414100216110609030a14120a02100501140d030c08090402070507030314190804020d020901091401171905070801090b070f031b031109030a03050304020a 78
    0xc84c00300161405403a07600043d0005e00b00c0380084079500080c5000f0024100c918030301202c1190f46a00046810f807020581140842d000000854503140e28544141a00c241440050180071141d04e07682d13030a81c0342004480c00c1b10540c014441c5504c0310503009005000084156005042140c00002c0490102d44e4142c201c6210604840d46156070780e140c0c21640a41c066043c02d01c10301004060800d11a0340c0203001245900600014202041002c00b040040c01c4a101e501c030301c0d8054140341d0403904180510242031601400348007048910500c604c6600f60411700292180400315200d4010503000c6200b41c20030a0055100d40c0b45000080c1d07024101c50051078105584100780d103040842640f40c110720f80c2454038940d141030f075420a0003400c0c02940001c040c424000c000740f540d50300e0704080040040b40c285000c609120740c0c902d82507019004400d125443d4442c036400900311000103800400c0f0841c00302400640612490368941ca08001c1e9007113250203a201e45440c0d103450303c100030361140c0e90341258 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 164148776 1250 164147526 164147531
    0xa1e0207350d0203160512070c1a09030309091806070e03160b12071202030f0402010807030921050c01021201080d09030b0118020904021206040506010e0d08030403050405090109020a0909 82
    0xc42c103243c0e010068442454078540c00c80301500850400c80d2402d01c0c51001c00000e2000080c40c0f100b002005007004045071002c110034030722042803101e08003280c0524044113405804c2041100c04c0d81c601030240784d038841d03011f030f0044241d00405038103c0c0c070305541200d50a000c02d52821001d1130910f0200000c0401f46041c0c4d5081003641d00380f405406850052132103440003690302001040b403039400390f200103420a908003400c6450b0310b40000310030b8000c9015a016404031b041800882d218070310901514810581211000340d0603820b0b0507009441c52040c00703020040141c20311220701d00d602c0a0000307101e112240d413150013055042c07074002400d29180c849510705008520608100140c80d858001d411505030f442030f640119207a1485901901c81c1e404000d40c40352000541003a60020b0002c0d40f0b000312000c0d0390030405940d8400040d1110401241c4240d817010807140140c0010302498000c50b0321a10a10704581456540d2380864a0018280c0040c2c04164000c1120440c45d940308800ea801041030903000d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 164150026 1250 164148776 164148793
    0x50609030307151d010b09130506070c030516050c1503040b0705030601050f0d050403030e012003040c0e0108210f16061b090504110a1e020735 63
    0xd41e80d10a40030001c1044070a61846100c10034564030003003422110403500c080c0d04074060011170007090366002c06440fa0288102140b40786105072048116240d10000803d16030f1100101510300c851014411820400108400b4100b050404800107010344914010055150b035001042601010034040d6801010b05100b0000445e01c40c82001d500110581440c1d580c94854a004854038482e80300c3d0000d5803100010884810b0000d40c1c420b510440c060742e4104414460602d03501e00340c0d90003403c0804038110460041c2804180c2d0030040d50031500c14242e0b617a40390368556410f840400241e100d104150003004001d41201d04d07a10072412030681070685240780031480038021029009403445640c005204c25410000c20207a43d1001c440030800d500722104101004e02c0041c8200303082c3c09164025030520030103040c64100d03002034071150a80b03a01c89400c20742c074031030301e00502280024203101148900280000da12680c1d0008107628900180c040040d10410f011072a65445036100c038006542c0004907 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 164151276 1250 164150026 164150029
    0x304030311010e0a0f1a041a0a09020a090f0209121e030703090e0612150601020c030106080601140616051501081507050309031b070503060108030f0f0318010c030f06050609 76
    0x801d90901c941c06968403d0741c08250525089120f0000880e00106601da801e200900c11752031030841e806004c08808c031a159484039030140640d0384216000390401042c3e0028407860031607030805000d08001010050404410750001f50290000c100c0c3c00c0807c1d000b0311036403880c203591240c1e03c1400050600c0110300d803903440e503030003040c40c040c074403801c0070608240c030115103a075440801607005408104116281c15095410704144844280c03441800341c82040c41e00b040500b418095802290450009031003568030700b20121079401d00c0c5c601c1c22540300e0b0040112b9410b09440100c1c26440328041d40c01000c4050600b00400d103201c0d41a0006502988180c191011a0200c00141c40c0d1082c6140741150700c80d100c00c440383e4950700a0200c4d844091040103520b00c4060000203032801140c10031800c0f41c0041c3d90711503200d41c81e0320407000000d286440c100b1030f0003200701d0404025500121004e1400c0d00c0c1300042c10f05182102d42c64484034000a4942c11040c01085481c007030b140c007800c01251103524040e010030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 164152526 1250 164151276 164151283
    0x1a0d240b161106071406090c04110405090702010605060f030406140405190501150305030c0d05030705040b0a0c02060d050f01050a14133c110a030e070f080304030311010e 75
    0x40e40108110300c1c0c006481c2c410b845072030555200540c000f007100100d041460031584c4445044030400b110b40706961081200c1c2c601401000340c2d070096911040c0c5040e0401007031080700b16004006609540d00c5180c00242c035200c000051400d450002922500c07414185404410b075014182051040c103044d00901011500c08100300240d400400f0503500d00302c000340b4140d40034160303040c041241070b180003000000784180071004203256688079080e10242200c1100c1560700d8001580d2460004400b400140456450740000340308040d454100616050320983c001001c40c0c0c001381109003203640b200b041c8a019815898114094242116003045d2a07081c50080041883e800c40501c4c41440030061162152040d0741c00059504200001400003a003e50300203000c001540c0824074400640303444c101170031060b5102c2c08183e1071980c02c107585412003c180480152241141c03081d40d0340512100010010102e43c071040040507a08080c649a074614100580302e0740748088040342d241d04025008142e80000b0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 164153776 1250 164152526 164152567
    0x81501060c0210121b030603060b0406080a080c0106080d0c030e032e110417150403091203050903070f18021305100c061812020c0a1a0d240b 62
    0x6140007498070b03554000110103030080c00ca11217200740e100c0495079a007030780c160080b4007079901030703c024440040000d0510080760803038810794040d504642e18040000344200010051107542200114502d03890310281c40c1003410000300d6a010520b804c848a080540040e84000078079000c4015001208001a2403000b00c0d00c49640c0c20b0025100302111074042c0d290394440e403035010000380081c0d03c0d00e44803041c54003181600708546029100740c1080700024030f07143c01102e03c0f0326859514110041c1c5409444130304205811422418000184036803103298408124050003030041400c5117034200d150a40e10740540c0351802c00d00d01c005004004e01402c807442c0e4590103045030000e8540b6405144100803c550300840410024401420310046008200007003130380070b054901852603074200450108080e0382c0c0e5181010240c0d000b80100004010302051000042c0341c0b6035042481c1854000090008403c8034000522050b00344c8040000d09a894545503001018001c8000320900d06120a030081c0140e401c0c0303 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 164155026 1250 164153776 164153809
    0x102011a040f0609020f040611060c0f070f0b0405070302010f02011406120106151106010b030610030b031905031207020303090304090902040f05040501020903010b01081e0c070507081501060c02 85
    0x5030740c1d65030100b00d1142d00c0800101180b0508540b2501c45510a411561191207003070002968041300382d0f07801130081203040c0260901841c0300e00d410420081c689082e0022102a00c2041c22203140d170000c035001d131000e5442030b807050000c1c25005085200142554208041d100300716032418030128a0600701a681941100d4101ca03002c124142030301c28940034209a40100d90541600311004a402c2c1d005401d100c022241c000c1584c86076030700d03164110a2404222421540b0044440388500c8c290301990140c0c038249000380940e90f0074041e156403180e8000c2c4203c1c08441030b03817000846501c00e1480ea051180c00500c54809940f071818500c18160b546e01403802400b10f415920480700b4115a20f60b401290900d0030284244140c0c606030a1282c001d402c2407500034000d500f03042c0000069031003180d02a101e110ae66214055201495a0f00c105030b010080c40140c41040c20090030004c210100040c0006011020040885411090310303503c2e9001c0c1a8481010310800902e141300590300d50000954080342e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 164156276 1250 164155026 164155031
    0x5030a0209040f17071106090a0b09030f01050903070b01080c01090b03091603060204080105070c1511040e0c0901021603032a062f16060903050f0310050f0102011a04 73
    0x5890808082c5040c08120080c400030b40c5461180009444e0340140616034011441d0b4110421010244440d500c0b41400c100e510901b940f07400c0c007005420b0b00c0600403624014084a010501c00f60310903003151001d580c5480c1680c004034910040003824400c85002d047c000300a00948001d04002900000250144645141020001807150b1104101c0c4000544c01110b8030f0358186d559060400013540a030180380c10715400d250000301082d0140c512a61a0790b8080e00e4012100c1380242c1480040c0030036400060346c0b5104100c00101e500800d80c200f400b5a5080d80307081c0c0d41f0a03c040c0064070b803681031032a8a014002440301000072a4001c000d100c0c1c91403e4002401454000341441d2210659031003004001a10700340f03c0e07000b0310042e1800c00791410901c2c003840343c030501c03802d8801005020b080100003110517a19000d000080c110341009680d60700c81c0c20f0440c20b000303100f00b00110f242c00c1211081280051407100700494900b081402d0b041c14800e0008200d03035101220401080c94046444500864 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 164157526 1250 164156276 164156281
    0x3031c0e03220302121b0103021309020d0501090501050a03030507080a090b03090609010c0507020d0611091c02011e05030601030504080910080108010c050c0a0f0c0302040c0806040f020405030a0209 87
    0x1424000c0360391804a0002070255080040c401c071040480900003039005818a40c803240c5d150800003403c035000d80c0d40c411030480340030f004001180694000003c08510308090800010400150b00240c0120304400b000031499604021301075040f03400c140c1c030152140c0e89a01d01040401e403c0000c070745c03542c0d803c00c0070183d03507030b50100e01a641800e455200030f0309207900100b040b0b14041e010809a01038034a400003446481e10b0524111040d001d8000040d501048640030000010019130048918400410016041650342c0c00081c09600e52204c000c1c0006030501c80c104210f613804445401802104451f16807080a144c800802c1404010600c07414155a140031605104c14201039a80b0b04000405d000007001e20503030300800944082c441c48150750b0802e106034071024006d80a0380c40c0220346400a040301d40040c2c803100111403070103c059130341d8040d1410210250710350f4040c0111841880d140c410150800000344011250000c903215115481800180310541c1d01044034600c1301e8045486042a4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 164158776 1250 164157526 164157551
    0x60e0c030619080c01020706021f0f1b050d0b0d0809190509090304060e1c0320010204090603051006080615040e010f050105090901140a0905010902090408130503031c 73
    0x1990881050100041d00c04000640400d000910741e404c00380a90a44480d50b5650b4000d0b030b601e07000d880e851022240784484d08592400d00d070b441824020f11400001c035102400d8444c00c0310f8002a48500000280001190b04224149006102200e1004d03541e100c00c0340e009840d11480c034006c03503601a10400b07515800c0b82c03e90541d2401c2c07202030b0100403d5400d99007801d045043c0d80f0f80c041d00c160004900710700040c4016103024188042803807c0c0700808e1064814a5800f12650100812a10074640b0418000f030b04001091000d0000b504801b000020040d083d800c6c01403804480070821403829007880024015210b0104800e900410303031401d40c0301038680c51400138001e03103a460f40c515800d40c43c00e000c419003107941d50011812a182070b02c5005c980e8a84031049801d032484c2e000160100c4808401245254006078081b200c0240030b840009501603043d8000342e0520300695050f180540086411701701101d180b8518801004110b00440c58010300c4000c240822a40c0d1000840c00e039a20891180385 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 164160026 1250 164158776 164158789
    0x7080c120301090b0109080c09040f08070b010603050112050c01140f13061115041b0902030a0b0411070c090f1401030602040e070305130b04140f030c10060e0c0306 72
    0x105081025140140300440d26181150001d10803014031030708014141c802e95000d100c11b44251070440c00603186598681e01404a0403001600c2118407441c00d0704100d0104615602500d00c46100769003266483d450034000a0036140180c10020360715200f5030320f20380000d4000603050020a02800c02c0d01551110000441407402100062410103400055080070b0a00300038540c000c0c0c420343d88404262110500140d661049840d2802d640d104a24001c40c010450300921884050645902038800c203449100d40426a041515490802a1180d0103410140752902940120303010200f4002e0500400b07480d418202c620a00c511810075a84502104500d0003680000c5204010910401802d50303592400034000d500620134980c01140c450081803045201f80615030040708001c5102a03014100d84800e030003450003400481e4100603481c051600d1240c1404000022810351000e140c0312060640702c03a061078800d07040082d1180ca07103d414000a0175080c0d226401c581071100c09a2290b4072100170410 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 164161276 1250 164160026 164160037
    0x10608010b030f07200a14121213150f20070803090309060a0f171009021b010606030606020c030307050601060f02030f0d050106110d08070c230c01080f0f07050708 72
    0x542203850502c40c201741c4c10000341d6420481c0b15641da50b0703000c4480d00c20075480d00340c0c1a0302141192001c001c468884000840202d410040302400301c0b021b48650350740d054005c0c1c001d000301003070039407140c4101e40c9a40d090b205211452000058503081c00e20b90040c81c50707003072040000043c191031010011a004c850b0070429684001c1c005040c0750303600d0301800406455036603000341c1e43d4001046046c680000c800c85204050103002502450300049040ca00440040e401c20b01011815800382100940d000c0c1090003138000810003501d0014640341050002800c100403000c4440c0640d000700304800c0000d80014034a4119132032403a01400c01981000100d0542c495039170240c1c04504040740c0018500450b5010b1412168a91240e42c0743c0c801e084a4903454095000203100840e124000103504103000d200080c1c0d1880c403c2d120b46101140f01075103e0070044c0c9003580c4856960104202d501a540c00c08a0320b600318007507a10300b1142e403400780145c7c180000020503501c02c100000c42c040040140c4001a40e1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 164162526 1250 164161276 164161307
    0xa0c030219030314070c1a040615091a0603040c050114120108030901030614011205060d05010f09030e0102030309070524030f04060605010306030206040e13080c060609010608010b030f07 82
    0x1a85900c1d5420000e000d040c000c151080d800d0a4100401c4180c4d016500b45410150700c110f0010048002264008810400510aa8106898142504e61860040e0741c60700034148007034000860851101c0030b080b035241a0555180600340410500003c6030a103456081210024a46081d4401000d8400c8856002d4255009910324140d00080392020700071000d4181d962080ea02017012664603c500c0510f0f051030220140841c00400711101241403d0f00720f26400707600078051004d040d1440d540c0030f086500d9006035040442e40e81200f03008140c0d1118014921039401d00c000c50450400c44259600d40c1c00701c0c400d49118070402200301d100c0019465504582007001c0301026140e290040100c004100c0413103040324601c0c86c000021455600074481c0d441074a4015250314286070511a00c00b520200280c0690541008100c2c4000044c0076040100110b171820f9020f880541444400d0050352103044e0804000d002d590780041c09004410f805aa86c4940560041c0b0360507124108181c030541503c040c8072 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 164163776 1250 164162526 164162563
    0xe0d050a0210030e01050f011211010905031506030105060103090203060c09130207111f02120f0f042309060d020f040b15041d0108070513020c0102070c080d020a05030a0c0302 77
    0x2d46045426034402168800200002e103d04d07a40c160300410311010034019070955070100c0c01041d02040c40c2d0b00c040300d4017030b2040c181501c1e220380320030009103483d16180e450740144107904c04004541c1001e0245a401c44802e0070305100001d203680c002130301e07404010084080d4500c082400241981e9801d980e0140c0d0643c09411035842404e82001340001001041031401804134a0b590380c030450290103401c4541285601030a02940040c074070036541d601550a00a08003800d020365084101c1c00c5005200510301042c02903a8000c0c2050242c40d00d4107000107140c400d840d45000c0100359250050706140d419070440d2a03100c08030300440020001d00744840400e80015041603402254041c420041080d201d00904a896240d9000845511141c00f40540e20803504030003810000d60078802d000c03140074a00c04002601f011040280d99003260402c4000741d80032400c80004100c031040c01d001412207606180301420100a0369250950b90b4032410004400700184040407105240c0709002180c0031201c42402c031b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 164165026 1250 164163776 164163799
    0x70506070b040614100915051e030d030b031c300b030616050304020a0305031324020d0e03010b040504050606041824140916080106060e0d050a02 64
    0x541c9048600b1601129002e28069400c004824800b003418440d0301e8121602d40110305202188002c1d0100644643c009909004042095510040c40350401200c010402e081d80e078000c020185803a0303201d400d090a040c5004200f6460343c070080f43c0340746852200c0321000550641f04004440750070b81c0c18010314a00320481410511b6070009108207490321110a03090054100314410076845403c16201920b0141100c40000b118601802c0516401400101051402540e075100c1b5130542c1d010700d12400c800714003000184003048003403005001d481036100200800d044000c6010b0360b14042642c80030301740000d0400c1071850340e909400c0b4801d503032000391052104c1d007000d00d0015510760303040d194940714504018001404c0c80001c1007210449411403e80c006d01e0703003054600c88020980c842030380301082e103812918241d500250001030050000710000c0503201016141c40c8210a41a08000c5d05a41804410405c46500880403803a2034401c80d007215440c03007035181040c607000c0120002500003244282 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 164166276 1250 164165026 164165033
    0xf07230307050d0f09050306012108160b07032304060b03030d1505030c03070b031015020607030c0516140304050301060e1009090b041209030212010c0e03010c0504031407050607 78
    0x148144400c415841e00901440c96140a8440c038031725000b03440d055406103004014600d03840c000080303045943d00d044000c3d2002d64581e254160700817148018071020340b4010100300156606080d80c4001e80d803a04000541960088002c00e03c01441a100e08050141c04101886200d40c0000042c3e080102260340d103072519040c1c0c0d4054801c001103e0000b200c82803000032181004500c0e031203010001006091454204030303040340c954001425104003084000400306884c11120703103809442c0455002082c1d05e03e4004401000c4c1c5981e42200400c2010501c6030b40040b440d808101d91026510a150802d881701d1500901c0c9503004690040f64950b080081c0040e9036000f0341c1110303000d44104101c4c410031581f240c00900075150b0082d8001c045001c540c0009000c246000e0350085080d030300c1c0c5401c0d40302c0c554a0300020b40c900403c042d210302c40d0355a02d00382000785800408420140f0000d034000d03c0302500345a009480c034011480050300040d55200b000c02e040300f05000f0700015090007003e49466003820700303 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 164167526 1250 164166276 164166283
    0x15050d09020f041b08151c050f0d090501080a0c1e050c0109150e160626070306150318030324081006120f0303020309070e0a0b0a270b010302040515030402040507050f0723030705 78
    0x840d15012a04140208400c500e05004381789600665480d0601c0011034a04408560249180c01071304110b4184400c144d078034002e0181c0c071000c40c012100a6100041004220221200500c2c01140d0758002c50300c0301412040c0c0d5071254102d401e541000c080c1044d466440c0c00b48056942e844012030b50f541001c00c112a41c140d8851000d4800544007040e140c40908001d41c00c855401d201940e04540d421404c00000e4482c0e0000200e003441d01d411662000c400481c034401c1140181c100303103540d4200c541c040d01c1c25000344c400d80d80104001c03012600b03500c2054660a000f001701c404060101600000010b0402e1001c0021000411040400020900e000c1c0003c40040080b00b844602c41c8400c0c07100052004030085e09000126000740a112440181c69002c0c0014003a00e01118103040e000d001c001800e950f000e08040100340300d8801e880e5a45820301c10807048400060041080c03110078001c400d080c035801c4081c1c03810640c4c03118802e003900d40300c810084042c60080b8201d019512000640208000010 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 164168776 1250 164167526 164167529
    0x2040c110624010207030b060906180f01030611070c051003020403050a080415050306061c0b130504111005030403050306010c080a051315050d09020f041b08151c050f0d09 75
    0x341c0301d505110642c0c0d00481e2034030384070710001c0c00704481500072408524080c04900e402032002000c9141c81c28000000b800c0c641c0c6d0846241100700b04010040003403140074007843c1c80020754400c0203860042290385650440c00e0710700801340941c0030070440e0000d941c001d038100c502031600601110720000052414415941c4180295140c201c0302210b000c0c0303070303d00882c00e59000d000e0003131080d410b00e080c041c1070712200c040080c03c0c109034940f07030000c098031903d51510722322121a40070804225440c05003000e080c0760038130405143c090081c2c1e520f9150030325802000d4a4110b0707418030f029940c17505e603040100c0e000001402d01030284140054011600c50704a4000c19040c43c00e02c0d590824a070391180c100c814500706900f0003010407004c02c041402e03140c0c26442005102c0c40103001314900d940b8080440e0450f0414034482d400310920440d003540560700100d4a40d44404008291808841d055010078420130402c08452101c210700d407007881c2009410702c001e11000055404a4800c1c20817090003c2c40c41e45107 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 164170026 1250 164168776 164168821
    0x80609010f060c030309061410090c05070b01030308090111040620151f0e0a0b0301180203030405150408030c01060503210f03092506030605060f07080a05070f08030615130302040c1106 81
    0x104032050004602070000d37140e04540007d0044556869500e080c1c524071001070401c0210b5503a40c0c100030788100e85001034800340000d82d48001c03850b400c407500001080c9080f00740100766440b40b01c002c4a440042c140c569400a10400c50b0741590003209017009000d01035400409400300400100300103800540c4c0204e41c41c40c0114001d103e036000b141003205285080e0705c0080c1d01500108000e1000e41800c2c91406a0f13100c0c41404d203071915548903d8a421500658000c400c165107401d820040340c9000c0000000078288000c0d1010900104034016090f8803070440c01c40180c110201c00078030500741c1440b025110001d414286000720b001a800140c04003824000c91000c01d1400e900031900c1d080c030b0822340d1400700c101c0705018070340180c170380700c07230b03103035801880c410300400108001543c0043c100d00443d890340d9200c0d00010380c483c00d11034100480301c0000707919100c0c100d0050004a028441c2c61302000e0440380c050714000f80505544008032030480740754030416201e21469061129180711003081d001305045 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 164171276 1250 164170026 164170031
    0x3050402010801150c020103020a020f06190e0d05190908010f05090f190602090f0a08060106020c040c0e1909060e1506070b0708060307030c06080609010f060c03030906141009 77
    0xc13940041c0741c0da20480000c0c100000d011110003001940031794010182002d05004840040c03100b0403c0a02d07000f0304070303030b800c82911890200040092150107940d18140c540310141c040c01070000d9000300f05006021040d1040c2d41c80e202450041c1d070103005c400c40a8881354000f4400e152598a20388040c04040d1856901c81c071a62090f01c195000c0460711705402e0401c3c207007054100c015070715600065040281079582c400d50b000081203403a0754001d280001482101f02a1074550f15122010703040464029509000394104a860040680e2002201d00d901718207c540b00d20b4120002c480d107400f22150341207589014a00b960228080350042100da20914050007000e0f2003a031100203000c01401004001041082240007142266028110242d8004000740072a21000e980c0e8440b104440b2490344054041403468003400000d0074100c1449015011070841244694a000802042c09440c0c51015003019a1000d00d41d0400855400994403602401100c08160410301c10210030b180c8988988001d552 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 164172526 1250 164171276 164171279
    0xf0703141603030b03032104050f06010608042015070c09060e06060304031e050720152a0105061309020321090306040303060512070b0a0c021f03050402010801 70
    0x49a040780c1201c1100845007244203880c0d0b5040e0f01070f041000b4800c0d4180410b1000c54029001d000210340d1495044a000c40642024145035042180510540c4403640040d001884400d4005122070740060f8480a0412203d103229058a41140c0c0f1402480e4407850303001452080c0e07541c05026221440c0101c0c5e074001041ea9480490048404030700c5400d02541c03807000040c042e450310300040c5a01502a04010103172424004074803400b01c07008804000413460202c1c5510500a120b0015440502c1090758100d40031480d0300001c0300080030804114002d000042c00c003602c40c1c00074a4581315059040d85501945080d040c450340600703022170350746000d11100314100c180d0700814028860f0b0b842c0c01401800a01e026150500302c5141607500391880707010200301a04203602c04004e07040c07081e030107594002001814002000320b03a20300c9060b040d0041c2d20280007405481249001c884510a90382800054040184086104010100c00d482c22242c400c400310806190141c204500c518800d80c3c2c1d0303442c544e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 164173776 1250 164172526 164172557
    0xf0b0601180f030609080c0a0b01090501050f03060f2805180a030c0f06111204030e01020109050c0d020d12050d0c050403050c1e04020c070513060e071803080f0703 72
    0x104150300c07540409505035041000801c81541c44250054003c0b050745e13143ca019110064602100701300210b827280c0c07480d00100000701d007a108003405801c0440d400021800103100081d66202c020f006c41d920002283c0c04106103204174002882c1404480402c80a41d0351184070a40040200302c5010110010800120038038003070101c1c184144650544030680e4002040d200e00c2c0c181841040c04a800680c0c91880080003400400905010401100000024036107850300418640fa003207429030541e81800c0501c000507002041c02c441800e016240440e00c0d0140b0300005889800c10180505a0b0b004011013040050b0f01000600b40da40c004007051090143c10b40003100c1c5032050f44400b42c03460f0080703105640c2c0d9240c0305030490002240c6602c000100a85074000904a0344851010046588442ea0401150400b010700380e070511180d2804002903890a50800310f00000103281d030b41000f19840d00749589071450074214001c0c5400014140e1554840c81014229900c80ca1040c3c02045403442c403034900 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 164175026 1250 164173776 164173817
    0xb030a0201090e04110402030a090203070e10050d02131103040506100312051b010c0c02041404080f030403111c08090109030207090906090807030c0312020403120e010c0f0b0601 78
    0x440d0306a64000300c01d8a008004207511801401c102c032000002039540c10f5a0340c1714000780d0301a00490100050460700c910400d40780c0741d1550310258000140354100701100030b035184460f08a4409540c0c2c0b189291051000404003400b4500c003050003031034a05202e4210401101452140b0b102e4012240c0799150391031350b80d8030ba07001807000511007035103000703059022792046026041c440c0c070300c0f20000503404030004030600303480031880075a000a11942b80740c0154601070013a2a054101020440710703d0929840365000c80c4100301e103035142c1c04070000104003012704c0f584544d0385a040361800e40d0303205c0499100001902c0d154280f010300041c00c0c440880d644070411b100d04040e059068005283d80c500c0d08140301c02801d60a40d041d200346658541ca80085008040180207080c801d64840003080303003074540580031541131005240c00c07510500c01403000502401c42c00b8240c4507603040c000f01200b0761400403509414130010082103d5110810001040107080303c443c0a56400d0325403141480354600b000070f0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 164176276 1250 164175026 164175043
    0x90e030901050702120f100b0402070c0302010509031006080d0801140a03021c170c0f16060c020d0821160206040b06030a080a09091409100b0a05030d120b03 69
    0x6904104840344040d0b014400405210384041e2a81e49106001110a4100382c1d400c05021041d8002103d41015103000d4400d007034001c2390482c1c00b141000034503204c55500104a000081c1400800140d02d1401e64080020001180c07044405100e22a1a170488980301d0f02c0d0002e8000c00715980c8400885c0151800c02910500c100c09000c00500d58074640070004100c0a01c04c06c0b041915081d03008601040c4401c3ea043c2040a0044107203035141d22251119103400d03102910540c1d03130340202d51038100301d182d00e0b200c2c4400c841162510440c0741c500c50001030344014054400525000001441404000899a000300ca5540b02840083c03a90303155100783c0700300c81d090015480160041c80c002000260000c407020b4201a0250845000403161381c2c400c1b41941c040201003010030341918040061050a000d00780c08007800200101e01130401016099031040100d001902c002d4458003c0c1c4c07015165006660000c00c8001c00302c903005541400041c110300750b00000c004603075007000c54030041030a00148055 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 164177526 1250 164176276 164176301
    0x3020607060b0105040b120402090106090614030702030d020705100f020309030a210203040b1602070f05010e131a011101020304020a0b0d0608010507051b0d0801050607030e0a031b09 80
    0x5160409a644034001095500e150b01d050010034030010980d08107403000741c40c605a400240341501e003814010840080d905900000403c240d401c5d06010701e0350311801400c03110450b1480e2039140c0d00c0700903007a4294004d84040d44000d901c0440c401082c488006480400c02c00c45600411903044004854826803200700e4100c01d40d03500070001941c0c61440742c5001c0036610a5241d6244c03282805840d400e05a0303105640523903100e0415001d11884280d10078540d81a110345000421885113441194000d0841070310545d0b0601c4908100920300c2c8d00c2e200050096014800d44c00c018901081a0228002031a001c80c02e0002c2c000c20480e000241c414801c403406190002d120003000c51030b1030036005403607200c296103e200d2070316000001f8100c42e017401014080c05107500c5158541c2030036000c0c454220b1156044128aa200d45050030300d25411011040c1992400d60b4020743d20010740c00e0603a007101741c440b240364204000540003c244040c445140400850200896114541e00c81d000380542c1c00004144 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 164178776 1250 164177526 164177539
    0x504140c150901020309040f0617030a09170309030708010e0c06180913050102040b09150304020a03030503060301092117072c030607030b0112060803030402090406061a0403030210060302 82
    0xd0740016010805001402c030144122860000d500010034150b64041e200340c401151100d10500407454942c2c54610204042030065080000360380c40101140850310600c0513088500410203c14601881161504c036809400c41d262070f46d4851446008040182e07002021f402481a084841d20b01036007203d040c0d815a45200018528803030810061000103020304184880d01180352002a20a00182004162282d80945c0f02c15003c1c080c8100d01c1e0340132000e00617505c0701308108401a41c650001e8800d803500340c07034070f02e84a41c1c440011030700508444001508003c2c0c0000f00d858641d04c3c81103080d4004649650b001c0c0800080010080e0400c0246d85c010b010a001c88840c8000b1004030001c890a03503202c0d900800f1004140c00420308045054032180c00207602c603c6450070070b503000040d131610b008564801b0000c0310303c0c082c062600c03800003a000074403e10141d0007107414082582c000c00b015000012402c060380c6409409048070341d01c0707440210007501a00c010712004181754451801140d4002d086d5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 164180026 1250 164178776 164178799
    0xf0605040b031b0403051614090112230f1b042903010f06060309061a030307060e07030501110a0201051e070c02041401060306030c080606060703050d0608030d0504140c 74
    0x40750005180080c2141d44070014130000000c21801c100c254100c9501c0500010001e0422820005500c8200d103014002c541c40c0c0010403a4200c808001c40d2007075002001407000c4144142d142988102c0e440320840f59110341c010416100c800401c00c4a0480c18000304211090074103410312040da400300601da5440304600c2450306412040340082c052516008000190b221520841d62003224100e8001000083c0d1b04c00c2c0358800c2100d0740c4511001c00c45000c8030056400101d000190382da204090f070080416481d119101c101540800c20900a55072103002841180044240a203c40e003004c0d07402001913013442c010070000e8990f248440c000c882219035440b590360320502c054560440c440d000700e130415503a80b20011300e115285800e5028111650300440d88500e5805d0400005203990400307c0e540c2c01000c140012660b64808581409916040164a51654981c150028007007540700750404d000020740e080b0203401b550b0200f0b120303034400d05a500c0500f00244000c1e99030b5002e9201c01d6000450000b8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 164181276 1250 164180026 164180041
    0x506040b18040f02062701031406010509120d080610030504020a14030a0b01080601050f010306050609150f0705011508060403020703140f1c0f170a0507090504090b010f0605040b03 79
    0x101c041d80729000d030151400c250b0390b99011424560108041204035001c6202c0300440c2c0c610f0011400ca0007000b40380601c802c0d0741e0182c82441d200da0141006051000015130500c99403210041d0010811040c0217640c0100300020f00506006012034a40c2e100fa10395989405070540241b02e018002c540240240c000207040819844803c1e0b444500c9580c14410070443e000020030785014140a440c090000e4909545400c007800b012b211120340390b41c1418140041031040ea103807102a2481140c04444000d4000c600380f030408801d204107627803000b04401c0012020240181504a2115160128141100c0650f01c2e1446625400c007a1340060058004060802c04603180c1004440e08507030700c0007942c220f0058001402d02d09035086c0b0090640942000d048080c0a0b001a0181c2007519a0b00701800c1402da02140c0540c4070700c00418140d5429035400200d00f07840e2091a030341000e000041c004001d101024101214140024803075480c0061400c0000305d0140d11940a075401c40d2444443c42e400c6489201 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 164182526 1250 164181276 164181319
    0x8040501030c171909020d050c090a02070b0604050406140703090c0b0906070b0a02092106010e07080117100f020702040b0f01121802061b0105010b04030c15091701020408010506040b 80
    0x304d1003110b8a6072051005642d0304140d521400e4070903801002030400c131606110780e03600014903034140103205100c9200031440711316070075038032550480d00041c4c0ca5465140c45001019541c0d41d2000d56203800b410840502e8255200140345801032a40d003030081d980d41941c0540d449444803a9070000424041200021040240c19400818115000d820813585102107000900c0e040c000d080d500d001c2c1300881402174010700141d070152407100d0b120300103490f0915000d40303404410300c242da00954803507034174140301c030f20034410b050340400005024400c2e0f21810610700e003c2d40101d070061b0b21807440c00d0300e00c94061400c0200203030342c0700068444444a1010f000d5000052100f000c800d001d542a040b04000140d81d030388000c0220725210083c021948401a00090849005800041c0710b100104014804264070301c00800c00c54501d41440c082211030550121210001075100d2201c0b03005911140e001e4583c103402500540f918440200302940d602c2c01000180c1d081c800c0da00c1d400c04000c5500140c50038150 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 164183776 1250 164182526 164182561
    0xd0e0316110a080f031b010209030c090901140106110d020a1203020c0a020a03081b010b010507080c010b03060c0406031a0d0f0c120602030601090b0c0d082208040501030c17 76
    0x14440c03960b1640d030302c1680f4141014115040c0a503000010b40350305040380c103401c504a00c0f010300001c50403c41076802080e618036502c0706407441035100c0ba0018294072400d412060000c009074070940c5c0156034818010b8540103003220040d00c2e5000c0d0f070211054003440060f0741446141c00003007148100d5042c81081c0c00030b500c11020903050b0b000340940500581c46030f001c004004e5224403d416a1550540c5a044110550300c65041081e41094002209a0390107007d5400b401c0d08505410b42d6030211034525801444010601c6825004103010042621500400303481218442d4400340260a0304100c940c4c05070890100700b50780b0980488003031003c12148034602c40c15501c07131302d0840e00d80c546840072101c07030708100a42100c0c4c0e260000100003055a00001007401442503100050030030310890b205036226009044000101b01c5142c00150f010b400c0c0a1040a4810840c02c0c150ac0065850070203000c1da5200b4050940460b0034010b25844161081840640318501d40340548650f4445682084668049 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 164185026 1250 164183776 164183779
    0xa020c0618040504080306040e06090d0e0409120c030809030f04150207210c0e0601081807050a060903050106050a0501050d1a041b0f0305311202030d0e031611 70
    0x50706030740d41e15584251401035000380c44031901ca25201c4104030540b4000513424805400c004140482c2490010f4481b2541c0310604042a5403299200030074002d0503a80805805a110501251002c5030004c0d807a803401800380e03961281d0f070394401ca50941c0e688606d031250780220000708420080e003440c0c2c403200c2403413522500c182c0303014590380c00e50f14951a0701c1540d03440944480d00e0000d0b0401c04806a0130000b404050344039001442d155002910b5920014400c2030110303441d032144042d015007405400043d28004041c0429181c94100c000c0c0004020300046450b90f00c1d10201196914104550800b2200c050b56410324004003815844060901c40100221010420944040568a6005404140c0d440d1803000c1d1302c42c00030740710050040440d01c424500b810310b84000c1c400c12142e088644084003004880c00781c82c44044581050b803017000c222028044103459160512016404070042c8501001c00c0300c03d01400c1041c203003650f103e11920072050003442c456801c007000210b00b0381561406010 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 164186276 1250 164185026 164185057
    0x11d0f040207120207060e04061805060f0a180f090b19270312111603020c300712030f0c060615091d0705031f080105060a0602030a020c06 61
    0x2d2a41da24003e60412007681c400743c0c10a1400b8001540e12050b01000660700b101d0500046280c180304d02071590791840409000307510b92001442c02d4480901c8203008507009000c01d00301036030301c40303882400114007044042c405003443c005110303005890041e4024950008a03c50280d2103240c11025420012420384e42203503104c60325228503076840041d10344d030011408a6440904414036004100400441d1005c00891900d848810020848801ea800c20746800f80311802001c040e04003a443c102500c55540c1e4804003000c004850400b80c4032111510140e0468421101c212000456807a295203015402000449010380307400f0901c03c1c19200803500346414030400c100043e49400c0196145a08803003290400040d001c0c2950f40d105d11048024205007040712580c46101c405010041d0014007458100a0040003080e803048120344401d8080300c20031855142140e483d07108901a01c2c0c1110454880d007605800090810b00100c1121030522465003e06000f074a00320030824940c00c0180305412410 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 164187526 1250 164186276 164186287
    0x40812090d05120d050702010c080a020f070602030a23091009060608030a0801170109030212030703060b0403050601032010140d020408070e0106020304030c06030c0c0b040b0402030c011d0f0402 85
    0x4605001d2541c000300b0902e041c0f42c0d44c8440681c3c84090361405054481160702d058202c808896110350135581001001078056542c44945054034041c0c090608080e00d014400400d00c20713489a260300c00d1111040f11640320780a0214245441c1c031030441100c2d440710a400c003211680800304ac42d40220211b521600c0002040c0f5203034009903141d07401c502c15442c00b01d050320700188840d040341000401c0000d00f1078005c0c410380100b40d81c000e4035210603070320010401c82d003c000310f1304041c040d40211014203d60013100d502d40c0c1e580d05003140d031600d080c4401d80c5c2d0514440d0100c003074210300c2846a82d07034078806049000c0412001c002210000180410140e05400511680d20f400c2008d0000304000c1200c5801415864100460540e40c9030060380301000b998410030081001402e130101081c102c4402d4140012101c0c210b42d0180d4907400c0ca03d00c01444000f21004000c20080c23100403160095000340d080707910107402c2c54015038551000810700c28458042c1d80e5240410720340310396004001c40020b4800750618 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 164188776 1250 164187526 164187533
    0x70b0a11040311011e17100510050706150b0906090a03230c030f150a090501091a060d0b1501110114090d0305010b0414010c12020106050a0803040812090d 68
    0x9030482d07002154012000c1845100c9981d001d101c0b500e40c0160b406005c81c0d081035441c00a01051191055403006200d2040001d0809901d1000d25001742405403814110121850006005a001c900101c0f11145050804101c2c4030102d2140d41c107413800400e0440c9011a0001045050b07004500e01590002071440040002b80302e805c070030038900c07406003001314024407414002d81c103100809041c0c500aa005c0600080001e02c00900c0d042ea038940c080c144401070f11800320301406402070820107006982003a0025040040240c0d070081400e581503049413450301d400003040240c690341da03005001c80f0409008103a0b41c01607400f404544400504040ea0a400101b00b59805d507480b1081c101d000d005150300f002419141030200c000e800519150402c001e60502c203001d03695002c0e600a4090812181c0c81c020351300d1f405007240c080d410b90411200d000d8105c90707e8009011f0038503401b43c0c5009038a100c000290303040e800019141694a0700700544415289510007810940040c0c1d819a40302c11001000b5010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 164190026 1250 164188776 164188811
    0x2809090501050d20041109030723010c02150406020d08070f270e09010b0102061b04060f0918052703070213060b0d060501030b010801080a03121d01020d0e12070b0a 72
    0x1c400c0d050300915160451f0104241c20301c0401d070311422608241800805c1e071058208000b07046002c00b42070040c07d42c512400800ca14004410100020050000300032400c10b400150342c07003403425240d40703060865890300c0781200c00c40480307078100d404181c88180704a80b170341d40130040c2401c0fa420b115419008641d0b0360401801c80c0310640340c005841e552410008000c0d60b05000f801c2e070207103000202c045100014540768240d4482e511490302000520f014160840f0721412031540103002603c083d445980c0c0000c140001000180e86804150a604407000803094603200080745241c82c0304c1c042c500303010131a0203104900340b070000c0c0c0101807a40c448011480c445810050003514003060b80004840d030615001600321990302c010306060210120040003900d2001a034102d900b5814034007a040c2c1005d4030b103010007034036082910200c2c8540354040c4005e158015805004400c4951400340103030410b03252050f84030f5180d1007c40c50b112204024085c0403417000a28a6001034009000003007a6107400a42c604 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 164191276 1250 164190026 164190041
    0x50105072f0f1605090a020702010813050c040c050c0d02060c12180706090906091505040e010b120a051002071a2a070308240d02062809090501050d2004 67
    0xc10304440148400e0805107140d1b51302200c00d0100b113143c6641500060076821000300070095a1040040010400800744541410404090818481710724005806442500501280340c0503115200d00c01318071510003e0000c0c021002812001d103066074008104280090003040d6030344411100340182600d041c01c010030001130085603504500300381443c1c901c405640156001c0d141c028240040c00f000d199292140f041100c1084800003650b460b46418180580018052170303501200144090081c5032000c510140d0341c502c2001941c03110300c1500072842c00c0b4042d00001400b00041850410480041e850500e6001080007052400420582104034420940103269505201c0c01062220402d40c000b110507400010b03e001e140e5812040451108100083c040150b2286540c05401410344d00e4580403101070220b50496202d9881144400ca01c80841880c03480c000500344000000b8400f0441c0300d02e50503036200801028540c1180c0d20780e8812503010559000700384c028140c0b050140d50b2039108100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 164192526 1250 164191276 164191303
    0x1026120d020a08090703020a17010902120601080c040e0c0103090f21030b010c02030c090a020f070f0b07170c0d022710181802040308040303030504050105072f0f 71
    0x5030b0703030001c44800420001c03015040d1038180c0d00a40f814001603440400410564000310780c0d00c080c1110320f00c18540942500303503000e50001e814441501003050085500c0d41a9a4004201c90302c0391019000d000c110344580090241c41d82082860103610b43c031030f802c003419250141c0500c0c5100802a2a503e0600c007035103c1c40b03429100b032095503c5a15406001e084a2201d00342040000c0e400c80b5004203460744c4c0821a514881d0080100144c090b25069060703174901e00d142034410351110000d180014182106005c11703903004010780c0015444501c0f0307034004424410001e00840e043e445d13610410b24103802c046115201d82d0340900540781004035888403c10401c1c101c45d07800311000c00610600a030302d03150422440400142c4000b8840c0c052008030103008035180c0d041c580c10141c040c80000300090041ba00000c00c00340c00000c001050590640045001b503005030f000f08403d4844810070307603401d4041203002900380180800b11121911200552900396401c505a911544111031030a00300910b207024032 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 164193776 1250 164192526 164192531
    0x50715020f03070f090b0a211b0905030714031005040303021b010914120a080c130f0e0108010203330a170714030703080d0204150c0b1026120d 63
    0x140000d61780441e2140040000407041c0b442c001c0b442000400d19560000d280c0b002d11401e02c0500404203050b40011039002c00907540c820040c4028000a101025520895100784540c28022403016a00c2c10824140c0d10014010200b400c03484c1030f40c0b001b41c030008005405140e820300100921903610110300c1940c0300c2ca207000085d070b61042c3c0303441100c0d80b4515401d40d030180d1000c041c0320305441c503140c21165020890300305034203582d80e42e20301404e05120350880019010030305100000c903104c00d01020f00a0b01d01c41014107d1030b0380c848c400300d0308070b00080f0ba0140030f051901513850200c0c0c022011104c001e4200200d006507241109001c29844280303030b0f00215528040d29a100c409040500840c800341c80142203003402d9518140000b40d642c0340b6400050301030300d000038042481d0780080e412034008100c1d51000031001d003002a00a044050700c020151110414100015100740002a0b80015910744100340074040d424154040c40c680050f4035002040c2c03041038001000c40210201420701000c444002 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 164195026 1250 164193776 164193797
    0xa141303060608100e060109151203020312010b0909070807030f05010305060a0b0a082e0c02030901030c050a0f081b07050a1a010308090103022104111207030201050715020f0307 78
    0x10301e40201c000203078021620341100d45c0100300d00401c8481c115030341d020010458030004020742a04038000d5110580d0b803100c00e0103810405070013001a11200000202c40c854680c1e854410500b948030340090a64001041400103d025004080d101c2c2c1001c414540000c6407030140c004601144c80c00c0c2c10540d61940300d1410411601c2050141d88401ca100b42c846ca42d0051420313406a55071a4600210742c00481c80708000c4a03c5440c030b240d5031005400c946020300420323421101c0a5122f510075158203000a0030107255881c0d0b54091703000c65001c4011b0b80d5850030013080b000c0301102c02e008050304540f0381c20024a024400e201824024200340e0340502c0c09032088440620303000c1c1411108021a032561042d0100410100d0240400d0b1000c418003824003580d20301900c1c02901c4c0c40c0001000f244140d40a82d01071205212a10503060480101034a90034031503c24a00d01a40e500c8007880006d00281003080b1200000390703d049003c2c0c0c80541e6101c0541041900e200c10040342d00704a0703011000858040c0c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 164196276 1250 164195026 164195039
    0x12032301080c0f03062205031902060c071104050612011a090a0501030503030109110403060c080702060a41130507090c0f081008060702010c0806030609030a1413030606 74
    0x55540020001c590f070601e10700b090030109866900042a01d0102194104040c3d600b24540c003001039981e61100580340e4503084404815401985003000e1300061081c0400161034803011000c58103190303080f40c5c1c101e0307842d1442010400a448010680c5420070f807032410b810f030000006d0280e01c0d42ca01d101840c0c40440c0781c2103010b01140d150004c0031001c0990a00b401080454408011203054803070388140814190440c1c428007a92340308940c00100000d140c0140c40d1801030303014031200e00a0305580d01352245a204d4540b05001d03210b030500261981051003c10070100b400095205165940702441c0c0f0a000402804c1c500b010102144c0c61084243d204032882c00300701c070038402d2102400e8200010006640c1168000300b40c1ca04c010029814080d610011034181141501c00c0f800a089502c2181c0003480c100314028040c0c205181d12401080f52540400c66a00c0c0100d031586c4280074200c001c1d818001240d4044036800344260803020b103014100b00c0c4107614044058900d025600031100450300d20301d01807 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 164197526 1250 164196276 164196283
    0x10c140f060a061415070219050303030c0a0e010e100e031e010204030c060c0b190b03010914010f05061003021b0601151101020a0c08090a0e040c0e070c030c1203230108 74
    0x2600203204000951521000c50901000d07104c05e0f5405840001006860100185002303225800c8180c5c584808020812014034110040c410020540d48580218400c0c60054403000150001d0a0b44529404142d019040c411075654500300e40c000c003103030000140f41c1c1c2102242d4160015540342c59400240038024003046d65070610040c4070030f162500c0c480b00f103500c8002c54118058503100311807a1004c0345040da031016400410021000900030020361110f460180b250700d42d1041000300650078440c1c1e260710705440e44680c3d442028080d02c840c040c11f00d210b9048000b5402800340c07140c0300040f090960b50010b0100411800f03005810b030240c26040b0849409026030f10080480110f030b070700400c00c0c00300391a4011130080c0555031200449403541d047c480011004c4100c1c3d0802045440785000f080244070150071808111603800300050840e07101c0640845459407880805000b180404020100046000a040c810078001d031400082c800e000203035800083d440c5044052001c03c01000600c000e06050 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 164198776 1250 164197526 164197559
    0x705220806041a090c09040f02030f1006050a03050c0904030306030c03141b100c05100f050f01150503040807061e0c0905120d080901110c0d0305090102030402010c140f060a06 77
    0x2803001140f81d151842c403090b0340301400400a0301444210010908101c0c509031002e80d110b03401400c0c2d424208032244e140c1c0e500e40b40003e40300041d1742001400100313410800104002e890700440980510102001030140308203020300124101980c4041c0080841c80450551001d1403080b4a00c00e580c1c0040070440d840c144449030032080cac507103d441405070305581301e07600b2009250351030601c1400c56026080081c10210803da21050090600f42c030b00f003050601394007180c840e000c5040e52200c280d0320b54000400701c034100b004c0b4401081d00ac00209010550b0070001d4007000f8420342001c140c0807160303050002c541c1c444117a0000c4040c1ca0b1400300841075000b400c6440501016955128000e001003e4541d540712a010b03400180452040820f804040a4020700c00d02010342101d43d03981c0d425600082e542d5a01c8140c4100080d1600c00410024038040c000c4078000c9405a60300398035894551207124003082088002e461030700c46c2c4403c59800400c1400301c0b61068020140000b410f524060364090f520070303030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 164200026 1250 164198776 164198813
    0xd030c12050a1e140f0c160302011709160b03150405070e0d060f091112070e1506070209100602010e060405060408090a0b120103020f0117070522080604 67
    0xa000385429254000b02012100c0c9018030b4000e0758000a40007901e1402c41c40c102c40f90080da00040082d10085040010b08103030786c400046503403030389600801c41d580c5c14031030000900180b01c0d03801c0990160b05c901c126640200e855016a0030b400a44542980782544523405030551a0000c000c008903026005100d41a00d07805403014403007880c007040010000030318000b40a20400003d010741090000590103503d40d03800b100c10801c6482d89900f0842c80c200c5c116007c03070b445200c850480250000740803c41c00105d030903007000c0d0030181d2111201e03a0310024811081e190480f034184540000340c1e80d8020350500800e510211003c689080001c02400d54581450701c903129800340742440009a00014030591141e001100710340c0b0b40e080da0f80003900c3c240303450740041040c44020440402800160003c1d50480e4800c403076003030348440c6070390040d210162551030300c0901001780e90014410600401c002c000c3e0726030114021600c14603c0c08800101c001d290410004d0398040720801c0200507001417004060f501 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 164201276 1250 164200026 164200037
    0x10204060206040b1e0402040c0c060608030d1b09050d030c020303031f06050c0a06050a0902030618060f16030c020c04020408030415020c06070f02060f0301180605040e0a061a0d030c12 81
    0x401082421707503540c001d80000d0080ea500c910381304241d072083d9480c0c1c6006511520521440341c0d2640c1c0c00b5902c1d044070b00d00040d624581060800310b0009210b2202c804160f13038803110400c82c0303401c0401103006170024050f018011b0010000006a0f8107000540c82010044419000c9580d05140300c0c0d41c01c00581c101b01c007480010000000c906500040e01a102d42d03000b9030104a81c4e0719203d101c0050910074500a41510031503081c488412850a8403120141e62542128001e40d00c080a2600040080e01c0740885224806440002d4511035001816946814012503804035581d2003c90201e80c007070b5008945a80000c0b030203016a98040f207054a42620790310040c00301c88502400070b0854403501900074141c030159003002d011502c0c1c1c030007507801002d103104100d40c43e0341c3d59940054200c0219048118098078141e0301040790310b8944544202d080da01c800801c2046040d6480d0f40081545e0b0180e40c0115902c6d85100d00c09680701d00500c080355100ba554003050040d50318041d2030488000009070240f10 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 164202526 1250 164201276 164201311
    0x3060e060403091733040b0f0a0c090e181002090f09010303200c04050a1b0804240b030a080702100305060d0611160b0106090f1a070302030408010204060206040b 71
    0x400000721951800303810401210a03407002003042055010841c00545e041554000b0042031101030054113128480154645440d6500c4880034811299041c206e44049001c4113024446800d590906c1a404020031044a5030303070303200200c1180340221004000c00400d4001950350100d04160000d0f100074001900c48041c1c95040d603401524800700d024100016141c040e440322201c0030208810000b41c1c001a0042043e0308181c40410040c00103d0207841c112110445c1c0c002c4280c0c41345404c00d05c960b40104029248030400b00130412a00e420000c4001815210303c00c800340c0342e0b01030003445003142c402c0030110364a40321481840054444010300c0c40a2501c0e1104000464581400c803403c07965000300300080080000b841400c542c051441d01560f48440d400c0ac610411600b50000382c1a0394240d2110101c2d03658810b9405500c500c180511001c01580181003600744113030300c0281802038864010b40341803986030030f81c1e242240c20903030083c00141c2c0000f040c4420301001e0b803441038021038061a680d002c1e0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 164203776 1250 164202526 164202569
    0x30b01052103040b0c0a200f030c030d0f03240306050106020706230f120103020102060603032a03190302130603110304020d110a030602040305010f0504020102061f03060e06040309 79
    0x2070143d8401c07010030b03000000305031078150400d0104883e21030748110f100050218210414013100040820b1500850140c010070300e50b1f190000e107159448100a005041541400c041103030b048085a04150605444050720603c01e54800988070001540510380b0240601e5410030105440d010b90104055403c041000d12000c0d502403850b110803025050310340510180c0b0342d0560190710078841806102200811140708801c0d072160aa4100d900036422203c0c6030700c4482c01c1640340e04c0b4080c14819242500c0b1030b580280c00140c201602c164245000784c90030b010010032500d140d20000d04100c00003941c0014030140c0c880b21140004050011860200411401c13084450180c1c48060806440781e000401c031002000070800c800c10440308040c280040f00c5660b8500000179400030301048540354200310700e40b40700110760b1013500d104d903405a00421594a1b4200700454028a103245a2614400043d000c008282035004a0311407000b410024482403505040003400009590458201211401c6079103050 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 164205026 1250 164203776 164203783
    0x913081c1a19121506140306160e120309030a0f0303180206040311030109050102041707050603100302090705070b070903030f03110301090b01030f182109060309050313030b010521 79
    0x980345000712001600c083c50030300d83c005140500307106859900300070f008070303040d05075002026140d10258201c8100f0303102c0302c20741008240041c050000040c4108511610340c90035a140c0c00840c1c0704201564078000d15140440e090031581c01003590011000051312040641c54442d524040c051104082581500c9a0020b10fa030b20036488040c103181d0140e0104501781d40c081d07100005e00b60b03221000b1503503960f4840c0701015400e000c0030100310364013070200000341c0c1e81010000ca0740720b40c085884d02c1c18010b0440d401c0000000f030181c214804c110062000c031001507010501d15004585d80d44611400c0ba10703500d0001c20844c0302c0041c40e0300b01418201b0f91030414521030240c074107403249140301040e0100c071080101c0040003641d60604c080c90a11540000080806e1a501c80c514041ca20009038140c8021035440500381510301c480000d442e401003084642d1280d80800a21442001034a20341079080000211100141c3c100707440c411300d00b100400c024a0030a07403100020024074481e80c0e0071041c10140e9510b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 164206276 1250 164205026 164205029
    0x30509090a09110904020f0a030b09070503030903030a05160804080102070b01080d09060813021512010617040201050307110a0605180106051503040c0e0901150906050913081c1a19 79
    0xf4101380c4c0c01050466030751403428030034810040c201c400c159a0302d05042825010a844d01ca00c580210100070540307007000300807603981c1c800c041c00651500c07072034110443e03071940078220b40b81c010290741130a000011468001000103004a0002507266116420044c000c4401030380258803540c1f2a41c0c0c1c0e0746c6890b40008240f01100e00604040e08a40d840c81c41d000d80190b03e60700300a51010300c092161000d507481d68085c4c0b0b84042d2004440d031030b5030380301c65058801303617041c0842440748450380001400540c4640f0003903900581510b0003100c815843c108203441d06080960441d00d250311141041050400500780158920011b0003d00c00c0d01d2405002c41d10300141144580f40303110000000505100c03202c0041c6000340360700006101c240c60010304403402441940c3c0b03080464080c5d00800500140103010740780642c0c80c000c01b105a07035203400001151074004d5200455014205100d00030030031018681010500c0f0000c007010175171500c0e942074034107a0303881422110700c1400003407822807840b143d03a4050070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 164207526 1250 164206276 164206279
    0x5030d0f080a0905070503030a111506030304030b0903070c03080702090a180204020d0e1507091d0f1905010f0f080102040303050a050c01020403061506111b011b050109030509090a0911 81
    0x152490413418a02d003802d803260442d9400d40f000250f1900c10347d43c80181100c03e13406500a44070b114140a04510755164113a5540758941d10500042c0082054011501e0b0002d03190003c5034500500ea0f81d80a202002c3c81d4000e42c4c08060108032001035081544195902c1441018108541e0b9144403c42c030540328040c2d0041e0044d6404200c45001940a501248400c101e00d021540e06440440181d0300300d071022900b200006010301e400080c1200a1030b1102802070342ea000b40009aa0388400088520100030301e00400e150040c125448820042d1280c64080c1104e00031001905051510045040c050b66100003203e0b8030401003000420b5004080e1a450519803070900e81e6074030380d00041c42c003a000e10340000c0c00103454066104101300300e44840204940840c1c0b036003030460b0482003e12713032a0030846080729003d04809061800c69841341e82e0704920700108070045800c9440d103455107400c540d042603045000c1760001410900510701604010340c003401503e401d02214407159148c403417030804540f005 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 164208633 1107 164207526 164207531
    0x4020310020a09051513060206150102030414040510170a12030c0f0f020106090f0507090f060c030e06040e0403021b0f0607020d1e050705030d0f080a 66
    0x900d4402d203694441e20042c902d4401404400244000307203009050081200070192400003509001502c40d55008050a00d0200f00345007140080440a90540d88180701c1000040c0500c491142d50f00c2098402283c0c035200c65140c0c20f52060903802495108204501c8011403070000581031101da070168440788502c003000ba40a40840c0e08884580c0c0001e020404000d000900803928450300050f03910000800300d07640c010b150110f49175101c2244030340d5107a0080c080c130b403540091554082d241c155501040103203004c1016206680810009040c00113100c035068607551503009850040080d80007046861a02c0d14000703440d0100c0500c00041c00c00e461020b44072906000d41c88601d81c000160a0701e02e400460340810442c50425802200e103c48074080000e40f29880111441c0e200f80300b40e0081c142c03c0d040c4400c00d400c011030f1108940400c820034091031480d0394010101500031200d100300 = true := by decide +kernel

theorem cover : BRFrame.Cov 164028776 164208633 := by
  have h0 := BRFrame.cov_init 164028776
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164028776 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 164028776 ≤ n) (h2 : n < 164208633) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
