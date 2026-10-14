-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0011
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:21:03.911755+00:00
-- url     : https://prove2.me/submissions/89523847-f204-4438-855c-c074fe789d6a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 1798569 ≤ n < 1978425 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 1799819 1250 1798569 1798571
    0x7090302120102070b04060509061f060302090406030507080303090d0c0f0305070623010f0504050903041401020a0602070305040504050f0f01030201050a020a0605010308030a051602060a09020604050301020703090f05010201060305060a 103
    0x8014000c1d070080d4100c5116030342c030a94407171481c2402d0400500900080701d08443c940b083c84041408010284800308140039485401c452240c2450001c030044d410a44001c0d0f041522040080300185082c4441000740110078000c0d5102d140c8080c003246405410315803042403002100109020480700c4003082c01c02c2d50142806075481c60149046001400c05070001404400301030140e80d400405e607200103040702c40d0b0450340c8107401d45610802c0201c0e10181d501c20f0b0ba550041104008902c0c078a03649ca603000740b050051340d0840c0503c1d01d8120aa91000078114000703800054248540c1c5440d10840d0382041c2c00303940308a03991a040003040c03200d001c1800080c2c14001e02152541000d84208080101d21740d01c51410b221950303407440d11810303503002500c0c103021039800c000029100c44034a04491288040300d600a05a03500c5038000c0390700030f11410500340d801031002c00001c14152000d00040200134440d80d40e103880c03e8941411150708110580043e411641041400c0011407000540590050780c4440 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 1801069 1250 1799819 1799839
    0x909110904050c03060105060c03090d02030a0203060103080a1202040302010f1202090307030807050105060f030a0b0a09060204060809010e01050c0901120605040606050a0801080604080a050a090807090b03120307090302 96
    0x1041084051501046a0300c006610200400c011011642100b01070060f4101d0b02c860741c03203100300700e1a030040200031403e07544180b00c1ca00e441e00d05001100500350000e820395169482580101e824040b007604141d072079120015000b010f00c3e52082a91242c24541c40341107017070904582c0001c0c0340c01114404602040500640700740c80303050030b50448060210040842d00040e80d40d01d000c1503103811114080c0d40d1546007100081030360401c440f40c5001107100a02400b5070b07800c1580e440d10000409004855400c0d580d8002d100001d81c584010406407815031100c1d03020b031401e54445030a440c0c1501031700107182d06000901981a1140342034618105017420402c4071341c0945444040109020340c00302e54882d0a100000403290b4000c0c0081651080a9840c0c11443c0c1e20342246035511002520b0040502c442001103214040c4540e0150401e00c60524003200c07000c0c2d640c1e50709440e150103504520600ca580f00210a524501000050351080060380518110301d80040083d01340c0c4100d100c080e0043c02150 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 1802319 1250 1801069 1801073
    0x6070f080a11030406030b04060b0414060a02030c01020a0905100f1202070303020c0102070f02011202030105060703050d0902190906060e0901060e0604080a0b04140102090f060c070b040305030a23040909 89
    0x30000015912a801241d4036140e8131701340240642204021140039038903065020030121600d00c100d80c2960982c00158450340501c0d41400a698000c9241d242180401d10002c220603c6c20f00040000801030380d21801d8007801c00b001c00940c114041801020b010354440c80e00610303500040e9074013152000101c01600c0d001c07030341400c0d8060b00c213009001e2a5544002688401c0210714561032080c14000e0b43ca4000070300030200d01a08a00c428015543e0044041c03001000191080004005040782d848000c10621225804200f1400103207400d40c0c81503403507460510204a0511404000b00b02500d00f5041c6140b1500100d2040001070247c00100586220021076a448a0003102c0092068404680442400b800c0084940105550407140c859001e121f00f103c22005009507401c1c0300004100c281d4400c058420408141c0c410082c0c40c0c000c1c050f1f00d03c000b40818440015100440c003950145a07074000d84040200f000340541320612800420690700c60442e0614420390701595140400041c0d00080340c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 1803569 1250 1802319 1802327
    0x20a0917030403050105040503030106020c06040e01120204090206070309031103010c080103110102070b0c0102040501090e01030b062107061d01080903031308090402040303020c010201050a06050121060305062406070f080a 97
    0x2d0f803c007606560a00081c4800c002000000303504a0340c81d9400c1d200542143d40800c1441c0c80f840c4140c6083d02130310801070000d250b03201118022144010300c000394404480d40424101e1b017090205401044041c0c404201b4803080020081c0001c2c0c08030000c1008504208002e007040b0720601024015007100482c2c03d249034000c101c0400a010100e175410f0b1102c0c0c4001c1114043d5105009142c0061411440002d1043c44d44d240d150580e64454508001030b03550701d0074000202d0302d004036041c0500b010408001d1584040c4507503c082c203035980e29120301482031708058044141c0d411295042120b040104000b4510200c15a900325003960a1803a05001c45c0c20314030032038042c1b42e00c80c1c2e13800b03407001a0000030103400150300d00320580282c001340401d41e503540d2030408441e000d10a080c00f04209041c41ea8a0145002c03507001c285d6000400083c10a031a074513050304e012812a01190144089141c0401e0480300300300000c00000d080700e00a00d0403485907038001c04103120102c010b0540901007031101c0080e0013 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 1804819 1250 1803569 1803577
    0x301180f0b030601030f1a010b0f0706060302100905010908030304020604030206070609020405100e07020f03090f0303041e0302120703050d0c03110d1d040917030613091505060103020a091703 84
    0x401421620a561642021012540c0c0b200c030444410788040380b00000347c03041005c928101c5a20b514041e0404004c000450360641c05800115000740d50f81001000503501c0d201441181c009940d51203032000c0c00c190026100c0304c034a401c106a03552040c01004016039401c400c46060740e82c19241e040d100c060a180c94405451801d20003035006042100700503803465110014001c5516840307424000c1d0b140c00009a0301d4150b01b00813010660002c1001203481d04294403d444503000280803246442d50b6140b41c072604003250010b900c1c1c80200d015040040d4601504d1486da0010900041c00640e441c5556455441c5168805603061203607558980042c180075440500c6000b6042c41a24082d012402004004401c00481d03030764405001c1d590341c0d05d41e003410303c208203500e540500212080710400503082e105400040c13541e540440c0360f100310386814070b06000741da024902c6980f20aa8075035844502c41d00b900c01c0203000d00c0c1050b105100100400364041c0325441180c10062440301d13903900c811140ea0030b41c41 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 1806069 1250 1804819 1804841
    0x3090e01090504030305060d0b0f0705040305030c0303010f08030307090e0c07050105040f0302010501090606080a020304051e0a06050105010f0c0212010b04020c1c020307030c03030b030712030201090501050601050301180f 97
    0x1494000004001d00c103038002503c2103100755402c1005650384410400c0c044103103a00941112501c90006041101c1006d0305901709409041007400c0642d603a8501c0d1030340e808100c5100d826040480108124401103a51002070480b80020f1405c61402200c000e0099801d032103440f908036400d40204001504d00320854030035540204c0240091715042c100f09641040102c0300310019813804000103050007192003000141e03002a620243c103510390940a102941000d441580c4d94000d0003441e07000310001011b00203101d08000050408010743c0e0501c80300300c507070590055040c42403002503e51103d91141c1c15160840c0c0c101c40b0542819a40c05005004245500a1a4000d03100068407000310701c0004008044c43e00354007400c075000d00441c10481e141c2c0150040280418018084980002d0190f0440c03225864054121014540d555100000c0c0d05401c3d40183c0140c1d6603418610706002e4280105640480282405491545420404500110302a4414a6017035850400c891100641d401c40500341c2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 1807319 1250 1806069 1806089
    0xd020f0706020a0e030303090705010503090c040c020d02010c05190309050114010605040302090112030806120a050304031406070e0a060309030903020402040914070c02030604030305091006030602030702010608011404030c0309 99
    0x116007458020000e6000c01074481c080349441c00585403524000013101d02c26000c50f400340008920381401512207030400b4000200c0e40c0503204c41e260b880e03103c034868210910110350081c01900808440642140d0940c140001013083c00c1110400250621005a81c02103261400007540f404605050b40100300c03028152001210550000a1080d0320201410039280200c41e100d4007030344da888101500c4d54000b0401400710303d6040019243c0c1ca0410082c202e82c1600209441001030345940302400c60740f01360411681c01c00744c4440458031100404c0304e194401d0a604001c0100a55400013907607046040c0305c0d00341050303190003a4a0406100f80031380001194058425512503071204044c80182c9008490340d02d07000080400034400031b01c504113400c869030b0054060001c58440307840880140400400c0c42d03da510442080350711031459407081e100114081d41c0c0c01a205c0c18a260024256040c0f45d108030001c2e81040303244000d401050a031590410791508201a02c030300c81e80f03410307107081c0e0469010b040c40c1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 1808569 1250 1807319 1807327
    0x15051207030204051003020301050a030b100b1909060206060d12140315010e0303030f0103020607020105090303070b040203060c07080409020d06050d050607020118050c010f030b03030c0106030c08071503020d020f 93
    0xea03010b4001d402601d41c2260302c01c400700c41c0254124200e0200344201e6611010909040010481003c1042d810480e651040e50190307450700721080482d4412a41016052121040700c03120b203501c1841c20300a499240f024007510f082076000110b10340240c0d08003402011211400780d80f07460080800c2c141a2106c1c00503c1e0302c80c90840540540080e06452243c086804042d004c4035900c1c000c81141e202e018211071944043e403c64003030291075000960100c4c1440301c1001902e10aa40c00c1010308012846070001000364501441450300b0041b010b007100840e088103000301c500142000c1c055400356041680c0050700d0342080c60042c40604801c0e4850742e040f50043c1d240009014002c140c0c5031040c050354000f17009000b800303042112900c022400c0900035401c00d2a1141940d031003034a845005403082c1c540070529032807010012341541e2150742040c4141e951000100100100b4160388001440c845025180607840c012035070307404455030130300842007590020b4504100481607065440140c0c02050154079 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 1809819 1250 1808569 1808581
    0x30109050c030d020303220501140f09010c020106050102030d02030a060e0103050604050c0904020a060503130204020301080a0201020708060408030402191206020405040e0111090d02040905010e0303180304060207150512 96
    0x1503020860031103010f40100111141014000400c41e401585103004c40b07152801e0b020500d120022050b00704445035501d0751503c0c1218003e110509000300c4181f4030240b03a604099619134210f6114141101c107690400000300032913a00801507403100100c072400587e403907490f20502002032280780c006c0c4200301e07e0b6100100901c580001c5640c0718521810841d11000e080c035080000c00007040340c009500a40e091802c2c00381500c5440919007250b9800e40b00ca501452580c00a4180e810076004555658045d0a900042d587d04010450050403003501a224505203a2507403950381c40001c1001c0d005805001c841c1c1402d01c00780c0c84800044c910144101c48a0240f0f1800d940690702c0361090a12440c00c00310001400c8074184140951801581d40d16480c00c0381d0340050207481600840240c1c0d0290341c800b040742c04030b0700a0081d40c4001d0300b601c018543d68601420700e2000e80c801c10300b0080e03007030b1300600c018072115070001803040c02d5942c10152029800e9020350f00301c0b041d10880140218100c196020301c54 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 1811069 1250 1809819 1809823
    0x60c01050603061509010302010f0201150605180a0e0a02070507080d091401020309010206040b0a020d02040906030501060611030a0e0d06090302010b010207170c100509030307050a06050604020702060a030507030b03010905 97
    0x40501c1c0120240c0c1e003951204d966103603075080024030070340d07202c40260700403c01580a80c1b20b161041d5070074000400d8080900141e07441c2c031b2240e0ba100700041840001e0f0030b091240300c0d034070700d560f19082103ca5600c030320309180120100481c010f1072901041e5001510109202c0c08116903402002114201c3e4030540c051403005120f5145e901c21403480b4401c82a8501700f0b0344c00401603c00d085010703401803c040d600e0792115018100c01610201485a081068110f4184d41d030008002500304da52001c291646907182c0075084656583c400d00c104900c400f540c1c6047c8001100321000d2103003d01d4540c40340030110002601340c0c044603100500103850007241208158041d0400d400c071b400240c00351072115a90f10600000301307400c0c0c411002d01c6d03044254181600e151920780e080f9a0f142c3c0b8034107241840f2112000c280345500991007950b65900844e042c5003000681c2c01455842101a1810b5040c14210303800729440340101c4d016902495141ca00062001c1c1c42940400b5021300004c2c02402007001c2418455 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 1812319 1250 1811069 1811071
    0x90106030f050f01030f030e150a030509060108060103081603020c0a080a02030d080705040e0c040803030414010c03020a0c1101030b0303040609080f06090c0105030702030c010c030222050f060d0b060c0105 90
    0x14158500b810001020b9056503d070040c101e90f00062141650400c2d1360781224001680c4941d158882d1780d01c03410121810703011000e00581c0c6d200d41c4001500d802c0ca02c0ea254030b080e0050b48641d010303600c03d4006200260001c01541e43c8020a0b1040121310b4a10349016030a211211030040e070070680c44000000d0915000270701c5004180280e058582071030a6280840350980b0847d00100420f00800c810407a0f81000b02405030f0040e111550507003025143d554050459001b03070780a41d14805030002d5000c85100030b01c54218488210304003140b07800605138018200b201c10100181656900c5505070b00340d40d020750403880c004400101500e0750f994641201400c04810ac1c01122503a10881c045035045d41e000091031802007807004004c102d2030200c0d0004590395400200034504500080c403104c80201302c2409060100ca8041d1405615030202500c0c040b20020299400c210701e156048003004551644aa0004d81c0d2304141c65199a480340e0341d0040c000381a0002c0b81c242c1240000030416034090065004e0703 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 1813569 1250 1812319 1812341
    0x8070209070c03090b090609040f0209010807050301030b071b0204110a0909140411120106030c05010f051201090c0201020c0a05070e100303020613060b090405060708011a040302040b0301090209010603 88
    0x164241e031aa404100c84a548084004012a94030541400081441805414180f02c0284914500a140c1c00441d0a03501912200010280c0204040860f903810040983c1c0c803d0061034205d09540c0b450700e855000d4a800380c04402804a010003007541e5800c60201c80214540142013445540c05015070707281c3c5c503408905c0140000381462008180720700140a94844031980099840182c0c0f0360351504200703a642c0fa01442e520030b44130f40384014842020b000303d500031741c0a8000149040d10700f800240c1614a054980c0e01007000801aa032041001d0400356410f6900c180c0c000222040998800d900a12644103150000e11903ca1624200180000d1000035920318990044680d143c0d900b80210095240c04024056004500040d10040d02c0b0381c0e03060a45400f52501044c0c80b10300c1004215200c000390340c161040d40165040241103600030603194010881006641420600e0486043e224005c0e40002403107544c81d0002c900c40c41d5425044042a587c008100d9031b0703035584d5554050000d0580d4020 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 1814819 1250 1813569 1813579
    0x40b010501020d0903020609030a0c080105010e01050904020d060b01110304030b01080f0102070305040e10090c021b060309070501050c0709020408060405010b040902010c060216050706020a02130501050f0904030e0607080702 98
    0x8103480d440400e02e0501c81c00d1a4852007001c030300f184d08006a503000b139485e0682510074a150000480c2100d82c040c40100300c0040005800e5051100d40b1905235016008580107803168014080103840300c1c804000c509421030f0300040c0800d0744200403100b030302040310b900200d403201040c04014040c45c0360260741213800050803602030304407604a05090f40914200035010800c18482000b0006078802410380c017075103410001302e0f499200c88200e0100e510711440349005900141003410b03207120760440c2c8507186c5400c50b64141546460485d06a0b00c40701d600409040140110b541901241d04000140141c1826541075440d241c8510103955203d0045070180d90560070901c130705040b82454444c1c0500c003070301030796106144d071a5516100b02a512041c40382252006101e10040826030611061f400b40845602034400c1c0c0000b070040000c0c2030803880030824024034200042006079910800c000d51080c050380c030012142d40c1c50909840042d024041640c00407000a5103008021065004024031407080711 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 1816069 1250 1814819 1814821
    0x40b03060c0a0f0908010c030204080105060901080304051e03010c0206090d0503010f060e010507050706030c03060b0c03040303080402010203070b07080105040e0102090a180e01090b040512030405100b0103061d040b 94
    0x41016a5914151144201c01c00c04002544000780b040c42c00c000d000c0322905102e1803c07903407032564030708480464440400180d40450b091001010a001d21508448221036955640d4101456280c0781d01c5140320b154030803203900c0031544554543d40f20201d4040070050007002020348a0501030744882e0102c4140009002c0d00500c0c41400b8020821789050710704c000464000c03d0308000b401e0ba040041307681064140318080c0b00c04000100e00b041618003401c129540030a856040c040c020301a224075070081505014203005210200800003f55002c50f900342c41c0c040c82c0c0341c50310b0005134298801d0b00390260840407003000f001101500b000e5103038102c9009035410400303038248a01003403c0707004402c1a1503001c4030b041c0081241c503101810481c07504201a400052200881229a0840341034040840710003540000308018410140000d62107440d80041040ca145801e50740c03942c03074480c2c289448020702d0752a070210000d64401d0740003e01400d0949011034400b080c0411351841350004a2b0202d4210304540 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 1817319 1250 1816069 1816091
    0x112060305150708040b010302010318080a0905091003030203070b100b04080304081014040209090f0304140f0a0e0408070f080403050a060b1207050405040819120b04050403050d020702010e06030a020904 89
    0x12134141c8a260070410010099085600450261071038000c000d104ca005c03110040042080b40c00144141d0415031a8070004ad0301c0d10044c480d80400041c41b40300400743d041c9080010035004001c81d000590f200c01217184a5030380003580444001c0c04e400c01c00c3c1101002c54046582c2c000080180107941140e02200c030a8810110701c1c0c010b490507581400c0b02c551400b00420010704055140311f8015540800365003480312071407201440c40d00107a010040c0e0040700001031140d803c0c00c1e5212120400196481c0d281c19041c00149114031a0180000b01080720015002c801d10080c0c4100100880d8404040345d0303038a903a801e001d5500d0070f01d210f050700c9803885c0025880c2d0b00c4c41c1c411005143c0580c600b02030240546042e080100600c1d008000741c0e80e00104011240f41c0c18440c44c0c1c1c2c000e100841d510381941c207483c06041c0c40126910304203d44d01076407501d07041c0004282c002040e9101d1b02c54000016079a21640d100403181d042103c10411381062021051000309451034000c1c0488807403d44082210600032 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 1818569 1250 1817319 1817327
    0x31104050a030201030b0f06030703060302010e030a030807050708120406060512010515010e0105090d03020706090b1309090f0203060a050604110f03060105071a040b1005030a03120b01120603051507 87
    0x161080c1507004038049401c2005500a4021240c120002024600c1c2d461000c00440c0c40c651007201c1c0880060f584400500c21503070480c1c611803488009400511078010150780240070098068003d40502602241e10420070a100040b80c2c442429207400080c10f040c189419000380860f405802c2c403c000c8500c403102410310502c6207500c40e0800000144100ba034aa0054500c08400a04c90341041010804202c454403020700b0074560398407a80c0244466460814010240401900280f0000728108503074001441540311450a64050100009030441a440c20003503054914400a4150142d141040950314441d032007580301d000191001e102c8505903002c0850b65100702c0220144144044c40412400e510501c06054460b00c545a520202485840d4080300e8150440d02114880d8203801003280440c0c00e941c204004207419401007140c03451316a000b42514200329400411300b80d40f81c00a80035a8401c40702d40c08802da5844d4200a800d0700ca007041c544500598040703201d040340f040040381e800c03441 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 1819819 1250 1818569 1818577
    0x2010b130b01030204050306010807060807110604031209050d03051807060203030a09020319050105160e030d030e0715020102071208010501140304021813110603060d080309070b0a08070311 83
    0x8000c2021054010940c0d0050081078202952030400d0703820700001ca00764404204080c00780821030002e02409240800c01040540000c109100700510099040c001e2080010320607005541070400c030280818451502c0000c0a1505000d800341c4150700c00c2da03000c580c055109500404180e00504072400c01e10000c41d42e01c104501c95040183c0c010070015415180039801082903600c010309488201d07103000b000c1503e020100406072100c4e5541c10a2201c5d01140214100901c0058200b401d224451100001d0725820b8024508041c11348424460340b0301c02e01408100054100342d0082c140075000c00c10024002d4112043c21203111009038404041c0034001c0640034100c6005a5581c603041d0181c4101880c10b0b000030300102d03003000400e94440d0314100200880c034400d12013819010592041c0341000018148880718460003580200203000094641c03110701500141c00ca59007035900e1725080e088502e008895480926611000b044484025038442c0d141e80c0103003000d540c03e0140405038a2180083d00c2 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 1821069 1250 1819819 1819841
    0x1080703110f09030708030406050a0e040b0607030804020d05070602030d05010b03010b030402060a09030803010b0306040f05060906060901110303010e04050601060306060c060f090c03060b01120207050705150c01090b06040b010201 101
    0x4014007000c41c40c0002c0310000c007007820300a81551581a070301c0051900c2c40d0441c7c0c1040300440e102080b101d06c0d0687c0a4800ca0f90210100c409210b50006580459400c0c032400c0c0001d010403910b0760004080d5101d206e03903044041d500000710b03000c0da0b556100c025101d812100131242500e041000000780581400d007509c4c1610700c410040ca00e15101c5608101c202d9100c12112406d1140344000080415620b1000e10f00030a07915108950700d2a04008100884100001200e00b1603d40341c14882d17681c4400413a50742c0107109031a1207555034030000042e204000c160142a00134840040040b0390b039048034a106005921400880301d090340c03110020380964440d801030f140014a4414440086020398200b0382403000351490008101c5001d446610740e621260300195002030729400d07840395950b0b22904000102c001c00c01e086081908681d240c9468070450300c12107100318030000701e80f402d6130a00302c21256161243e50081241c01d102e40342200c1300180c1150b103a842907190810501d81c030f50040c0030f0495010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 1822319 1250 1821069 1821101
    0x10c1701060f0909060605090103060b0c07090e12030103050313080a050a080307050d0f060807080109020108060f040e0f0609010510060503180309040c0201090b06040b0d030c150507080601080703 86
    0x10307003020000c40d8444500c1c0c18510801400000020741c0419502c5420041c3ca901e0b84d4056a40382c144e000941518102d0380960303a41e03030040000003200785001c9550381c15580810f1002c21a1030380107410920b440c4041d071251511220000c00042003000c0000240381c0c210f4804844075005139101c090580f00d0090620242c6103802021035500010000c00c02141d00c064207081990a128238400301c142121888154032260b5950307501300744020541000501c0060940390001d00940140740e0000f802030b0400341015004038102d001001c1c40355a50740001240a00540c2190458004003044d959100030554042d022546088081850074040c07142d6082601c59548076070345944c4418031030100004070380c00c000000c0c2c0010302c081d00280d60b86000d403c000590070341c008280f604850030a2000c006014100d1845203203043c0c0b1501b043d0700e585c008203481c44c1d05410962410800c074108002d0408613b0199900c1d20b103404104100c150b000b415050082d00d080e660031159030741c1d002e019011120410a000650 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 1823569 1250 1822319 1822321
    0x20901060c03020115031202060108030309030a1b050102030c0d0606050301050d020d02010903080a02010207060501050907020a02100210020f07060c0327050a0203010606021f06050109060804030302070b01060809010c17 96
    0x40c0e4062041106079910a200004051040e54494000c15885030412110503440340070b1010308943c108042d07800340c490480518074500b002100d60703a480c4590204c01c0280304100700ba00c0c060402d2010052000758004d8020341d40da140a540f969001c0e40011200603100b4508000416290320640030b5034140c503005024110080b025408110080310f4140c01241001003400010000660b03100141080c8905500003603240d02071803500d4000d07120160041d40c0280c1c55003080041999001804920180e0151a03a855510384428120304084481c00c04d008090f00004000400d200315400a0107079034001c800030480c075040401b049080d50388407107000d0444011208811400100003240c001c0003442201129459a000c0c1d011a003510000d600900143e084001c4503e0010f90524000440d4240002c1c100403041c1084c00103001c088060185200b0865020006410140039a04072155190441c0c142c0d083d5607550a0018100102200d001e4110f5091443d90000280203100300c048413840c445100000e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 1824819 1250 1823569 1823579
    0xf0305060105030105011b0606030602030703060501020c100503090313080c0901060201050f0604020306030102070204050c09040501050a061d010c020d12020d03020f0301030f030215041407060507080904110405030d02010501030213020403020901 107
    0x87c900e22101d81e00e0060780c1000041c40007510620541000b503126540160b11303883c2c200d40190480300c05600c000d056400c5400d20900f5a41e8610341c0481c02541810001e480e5180c8201c0c080c55409841c60340c0d00c006a0000300440c2030795001810300309200c0f049035a012107030303280e100407070a840013a00c222180303680381000701b01145001c0c1c000d10390002000d0300040c10981140c00050980758184e85c20968141c00042204031424a40200780c0503040585185088616010b8024843c401c40605948075080001528210f40c0c480c500e202d1220b41c004180b94211102c6082082024144494480c050712964003050360081c001d0094914103840187c1043c01c680c07079921040358805090078110214013840303587c0024908101e00a90143e0300480b0389401221400690a14043c402e82060b03090280500c007440014084a08890800c1016030f40840e05020041845042d400345401490b4517000d038144010b000c603415400b20303048a0007240e42c1d01c00b140c5a081004100d114502010350484103203001400 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 1826069 1250 1824819 1824827
    0x3070f0204020c0a11030d02120304060203100510030c090806060303040303030f020d0203130b07020a020f01030b0d0605010b0a02010605060a08160507050304030308010518011412030408010606020c010f030506010503010501 98
    0x901203001030005031a1a904150352400d00c07801120031109564070a0b20f003411400e081111006949060004002c00d01d80c00961420501000308020140390300040094408140c2c0700c0d00100a003000707420000d04080d208005005404200706542c0011042640050703200300c00968503010f18000740c0503614090560b14214058281d1800c150442c035001c000d1051a0b403c14801148100303e0704174100c16560705442c042d075120001904030301c11075101d03560701000340c0d0b1120f504009030038003400d002401816150104120380807030080644101c2ca0b08000180c0840605c00070034006020fa402080910b803036504021441c0030b0001070754001661080010324403007100d4249010340089083c4241013080c266580351070b6034401c5d002200007038244001000035041460840d0900702c1100700384510396041000494810454007180d6100701c2d83e00d98400e103040310901c2220701a1800e00000d00a40c0d48a4402a41d84c214841145001905403182610294480d21469005640594440340b0756464000119 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 1827319 1250 1826069 1826093
    0xa020d020c03030106020c0109060206010e06060a02010f1b090605040b070809010203040305070f060f030504050a060b010e04060e01150203040303080109050709080a03030605091503060a050c09100504030501050a020405030307 99
    0x80005034200601c440701d103800c0001e14000d0481754020466154070a0006207660080d0740a2415035000e08014004160002c1c49241e100009884107501e4092100c0308a0261070100d0300ca030002c0b031900441c03010b0410500085130103035070030f0746031000c8060380c981c821a0148900c4c414a00440400e0102c00002050000240210713001407040303c0c203060302d80d12043d042101e15401144000314651041100c144c00c040c5002c0c4410302c60070104080d03d40386d103860780c4820320300500400080d0344186001c0e00c5c0c8c3c0601d9981c0441301000d4410003186486078000d16146000b07000b84040c06545554000625200008550583e9403540c2c074100386034a020895006030a001d4145001c1c08806400880c014004200011040c2c5c0030f954003041d4a031a1005001e0080c0000e0194a02001003241c480c0b0741d0b44001078030542042d000300f00002c456903455200b0045006d10f9888a9109092500c204105ca512501900c01c0ea80900003c0020751510705e055000c07807080f8440e1a40581023407103d04003150038000310b0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 1828569 1250 1827319 1827337
    0x6020309040504110306070503010603050a0603050c010804060f06080105040203010605030a030c1410020c0c0910080a0f0206040e100311060403020a030305030702010e030c0706110a02030a0f0c0b041805100506030a02 95
    0x134013140f591090000f07040c154200d9482c400104044010030485600d40541074000ca83e5040812180f403c1d43c465035196099094003606100c0078070003040c100100c9a0210140a281c110100410346e01d540010b40a00016a0160320940c05c268005c2000c1c600420100740d06980340c1c550485140e4181d0b40d00210030b241100d00102070042c41040680681c04d40001d040e110a244094482101010100409544068840d10f422280341d0010b000d038190025680000310b4000d140007224801c1840000c900703200e2500101c010000e00001c4c801040700c01444041500c1c402c40403400710807521805c0c020680942c1c807010703510010809013000402d0040f8011600300c0d10038800413685c04503480d0039520b985d12614400d151544070305400c10885900c281407201d02049100a041d0f128040d8001990b038004240c000b409200103141d2810400241d200c0c01d000419145003129211562176004c1c402c00403881c20180c0c400c03030400000a00c24142000000c040d240010031690440e294000b9400080d04280e1103 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 1829819 1250 1828569 1828583
    0x610030f06020c01020a03060303020d080108060c09030102040b0408060106020709020702030705040c0e280503060c040b030603030d0e0102090f100807050306030a140f01110a0801120204090210090306050601020706020309040504 100
    0x100703c032044028001440030300d82607240498000e25500d0024a0000c90381e007421704001c5428018460302d031002c98250780003c205d16071180c4038100d44000074024800c40c1d204495610002400040750303000483d80504a5510703400307880c80a42d9803071700d0030140d10038000000d506400c09041804140781651000d5010711103850070038a580c0e070810110700c4403501c840380d0300c2c200100c810034a40000c2400140c10301401c404d40242c10035042c0b5003c00c2e10b442c002c03406103895003c80840000e0781c40c1c8040054030083c848800060002011401f6514002c2d03010510a070f000303030030407511048039003030865012010350084c0d600d500c800ea941040850705c50700043d0542d030303240c020381039030b40003144551040045196500c000f034041d5140140b80d050856a450780480004442484007070303c2d907500107000c0c50450741c1c007028400580c072086c4000350003840e003071710300962002d9501d001134102a0310080035000e480c82071a04002a131281401a80c0d02c15191240d080180d00411001d01035041c0342d00407580041c45542 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 1831069 1250 1829819 1829827
    0x8040c0e0906040203010c03020c0604060506010c0c03081e040503100c090b04030302070503060601090305060f060d0605010905060f010201020306060a0c050f060f0916030c0302010309030908011802120610030f0602 94
    0x2030354404030300055030308071241d900c14802d1000798a4284940c11000321681001c500e081003080d049622000000d001404184c4d07558001015640100d4904005561100c007845101c0d46030f140003905130300106031400186900e40140a01c0380c4038201210240d0b02d0045c0103100400c1d0b40c0d045080501510f107108800c01140140015000b4114005040038503c682c024000c00c0b8104401d2502c0d145000780540c0c1000a548020400700300080b54854100c0c2400d101c0214594820740070407642c203e0020014000342c038007c0000f6844038550b00c2980907201c00c03034115801800310070049003070b80025070324550301200c01c06c401c00d1814040c0b9400900f1620070015694045141038680d03040000803a20200868a103200b046070007501402406042101d40c040042100c2c01d5480d44100f01025001c024141581c170742c0880140b5020340d03001d0b001409400004c0c01141c4124500002a8101c114208e00a42814818861550010860702d00c140c8088094001c61031860712800f1980000490585100350700700 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 1832319 1250 1831069 1831079
    0x3090a020a080106090506090103080702010f020307020a030b04030e0909030405010e030a021005030402090a02040602100203090a05060103031110050121030507050102040902030f060904020d02040c0908030705100c0801080a020108040c 103
    0xc041c030401011501c000003070142c6413054000650328010b0443d4030598016006100241c10300b1700f40c030020742d020f10340b11040300a881c9090303185100b03d140281d0300092800000080210281c00248140c2c03007662078074003400100003070014115081da40721900b0b400501081c001548240300b1813031000f00c01011100500fa2a401042d89061030041c40d00000e4400000c010650410b01c5100341c105000303080451a0524200c0c00035250380c0c03c490414041500040480e0b0340c0041001940d5040c1e4000c402c2d00d120b565a03190140c102d080001000000d8041c2c41001804000d103481040d04941800e0f0030700202c100d04100ea201c80c50183c2070b013102401814808400411400d101a001400074000c2c01030b43c9043c00406600540342c000c00c102d228003c1a400c0000503202e803522500040d5040d5004580c2c03075030311542680e001c603550700000102d11000c00c0600510400051140032030209507010011100f025004a038040024014003469900c00c850200040d48100380700c40e40305026010007200c075a251 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 1833569 1250 1832319 1832329
    0x3080910050a0b010201060b070803060103020d06031202010b01180501270305030a0305040c05061602090903040b0703170901050603070e28020706060602060622090f080a030501140607060203090a02 87
    0x589290360100c0e030b55904070703c20b035809105201c050f041d020b41481c1841c1003665880c1c064400100420b0400d90003288888010b030607600454061944562245140d200c9000024002d04156046034001829880000b8000070520110b40c15104180e45040d4081d400c007180811003041390149645a15242c0d8000002c80c40502c0036024641e0a0390b00420b003800d2a0820b2400d02c0542e40000d88101010032184010303000192049540750380c10b49545046903a000080350550145600020702c2c064009048010903511140f200841358059580305140d4945103501c508030b6808490203501507124000c103204181030800401e0b801150a400c0e4481600710384480460101c50b000c1030840300d07401081803003c0040500503030004c4c02d1180b0040c4914134140b0000f900741012a08030a620484001d00c00845070f0031504140c089541001021001400618080c00c242d4030501c00580000d180c400041200b008007501c0e220300d078000901d06820110030340c9488000750300c00340c03604401d40702c0c007018040140c0f55 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 1834819 1250 1833569 1833571
    0x30902180907080d0201020307051801020a020406060201022505060c0d020403020409030c1406060102190503040b0403110306010b0301050f010e010201180b070e040e0a0611040308030901050106030f020901020a0308091005 97
    0x1000010b418090320308890f86141071310405030007095900501c00c0010050f4810140c03100303036280c20a00c1e0702c5650360388010b07070802980d080e011750403d041c0500819420780540003004104410a1014500d440ca00c0300004d0408045000900d2a0440710100c3d840d00712081c0980030400c0c403030400628041d03403640081c0840e07090300000c901182c400d02d1110144107070f04038942c4442807031a010f4081440c192000035118014040c4031400800505940301c1402420820360b8050300070503110b541c0d00e503201d0400a040d41c0d209008588a0b2142900114241d0701e0070041e64121000503200982001580005640b0302a0040c4940c4c11507580f019003e92807108591034a40350750007003402020074105010700406c13a644c5206524040c41c10818418994500060622001500710800080f1008184401007840c425640003420101c0040140320b10f408065200d181200c540341c9080000c54039081c08801a4082d0f5001c95000d41c12508851004c28020030030154000c68541c00c2c4c6005500da04010011254 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 1836069 1250 1834819 1834831
    0x1e090601030303050a090c0605030901060f08010b0a05060f0706021810030914010902060f0d1103041401050112020d02040b01030e030f1306080f01060f02010f0c050702030105060118050103090218 86
    0x4484001001855010b1180c20b41101002d00203101000a82c0c07076040d5109a02d00ca100d080160000000d10300010a500480180c5036182100d480c2c0e603613070b0100a0203008412109481416140400a128030b01001190b003110300030020075050000d41d458410094020f0100321554445504103408260b8651203e4045810a610005142221030404009484001e50791805c41d038075080040b400b5943d141c05507070304002c0305005165202500f00a1074090b0103d02c604100031400801880100400c901c4c000c0300340c06c880c00c02040103a0340d6484000c00400e18900c083d407c2031802c0314500c090f0605810032212040c060501040c10000e03c004503141d80d203c0e2100c0c860141d400f01d2441150b603075140c00000202a1483c140020f0305240c07040d981440018491780040c49802c0101c041824000e400040d00390054950400030548400303005001640b010310203d209510302000075003690700440155180d0903081e00402012810000190000d1001c044280d0344564108021008105800500c5202b00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 1837319 1250 1836069 1836073
    0x20102040906120c08010b0d11040b040c020307030f031109010e0301060503030301091d0706080711010e031201150309150905070b031003030801060203070f021e0901060503060a29031e09 82
    0x1c400b13424089613181c403035045010144d0401400d41059600c0c0f5210b86015030b001020181216404000640205002d81d01e050304035060051184200ea00072003d0184180a61260284d200541c401101142c0e0b0b410151107421200380000d1201d94440e89212001000140001801c2501c44000034a5604244d000c94107264452002c030301a50000342c64030013840200380050031540c2c203044e00507083c550010720903400c1104908074064510742c00d400c40d51485042c0019a981d500d03203a11940045002405010061086410340c4000c1d41c2c031900c91507072040d4000451803004481a55164050405640107441a03c1042e50214401c100c6500441c01450111040c0403010f26518002d05100016409242950014043d50020a2400c070701400c1003981160441c00b880482260865004120203506410540361400451000d4000009600854040710701900081e0b503031205000200c81030715281901c070780e43c500c0360030b20604080240d9049006a001c104c81303134659541605140d0803c886284140e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 1838569 1250 1837319 1837349
    0xf02090a090203011d040c0308030c030f070e01140a020c030609030c01050f0709030602071a04030309030306080c03030f03150d0b01030201090b030903090907030e10061404020c0d0e01020102040906 87
    0x1514000308000c00401809505504542c509088400000305500054030100030183c00902085816a085809154081807003503e90500103207503101d6400403501c142d04d001c100700200d210b01d4001e0fa0140346480e016544c80e01c0b1640010036200c2990802c248000651280d04d1080c82c0554050041d02d10a003501402075450300d14007500e00303080d564060006c25080294209000f81c680e4840c40b07031415030390020030140c1e41d002d151038610f0040d2401900040740448010506c0304065158015918241c02540c0c140055a1140d00503034440221266244c0c1c0356108202c02e084001c2400b01079988001a03400d030075070004880011505400c0d12003007c80b5541d02850040c81190b070080c0c00d4401030300c12240c0007425860150341e03482c1c1d644079600655100c0c3c02c00b43c0001e000140310b9000104500225000d94441000c2d4100a2025025901911544419119102c107840c01d161003900c4404424400519140024060564281c8a503070f910b241107540030000400c038900316005030390082101540120341 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 1839819 1250 1838569 1838587
    0xc0203010219020a0c0b0901020a03050f0d02040303080a05060f180901060302030304080307060c020601030309060c051f09111203030f09071d010501020d0c050601140d0c03030809060702010b010c0b06130f02 91
    0x8410054002610509007444242242d27680040c8140966500d410005d550361640890300e0841d014101c606101603000103408010181c0c0500d41c503003d000083c2003071202d51102400c0121440c2d0301818140c21404251000c0c0d400d8400c0092150040b10050000411644a802090a60b441a00550700135440003480004000d00d620903150850740a101034580c6506544c2c00a00c8200c885c0b00302401c208040120006010080c03240012040000c024202d5072010340d0540e07005052000000e690074040759101c1c0940303040c80d042840402035404003840c51a520048081c00000c03001d8103401d164401d140c40400c2c51035a02d13130a460701e8281c525020748290300d800002854000280c84031020842c0400340c0e080001d10004515054072440200070108444000c00708403c42904980940a86c09000000061542060704507001e401d03100d05441956440c844264280c50040c2941d5000441884001c00402c00c00180c40d03400c8800144241c8500f45001c09910503295006c842625890380040d5441c4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 1841069 1250 1839819 1839833
    0x901080106090e040f0602090916030c02071404050c07050604030903020901080f0607080a02090d0c05010206061215070302070812010e0612061803040b070803010306060b0304080702010c0203010219020a 89
    0x100400d480d20381a0b000e2418080483e068600262000303083c640e00120300d00030004d41e60107440b45c0d03e0015113a00e02c240f0346903c0382d00e1100f80c550201c40c0843c1c45c0c400707041c000d2480440c0a00030340e201c2c05c44207401502d008092200800c0001e000b501a001c0c10310203c00000c0d0103100c0180a903029a5032241340e14110b00412070b40e100182c0c88602107910086552448040c0130440c1c0390b01c0403c6007401c040543e60411203801a218103100d0692041e50304441804122040303013042e040d87c0d02070f0708a502e0f5070b565206000d03040880c140d000085500686402540300780f4030305003a03071111462402600340901a03172a0395080d0030051582840c1d44102005020041c04003100d141d001a048948412031140c034019603485a00180200e56440d4104100000070f89080040328010110140d100d690344016040c00300340380e0828042141c20b9030504500007001c01404048c0c3e801140c10000c000e10702806940196210b0b0000e60040307816540900007040d046521501180d8141d044d074014010740071841ca0003038 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 1842319 1250 1841069 1841071
    0x1306030b070e0a06030902010c0609020f0607060509010f02070203030d0906150902030603060a0b0604060813020a17010501090b0108010909020a0b0d060311030d02070e0702031306050903010c03050106080a0f09060e0102090108 99
    0x44c04261900c0da00e200580c1c8e201749411060707500f00d80c0028041210b0b00219080003000d0b409943c0044c0b0009050342040040e41c45140b16444620003044146040180c04080c0d00c1751900c060f41c180c1c070a200759046200350fa4022052107120f000700080110901d0302882d94050580d12614810381e0110400542d030800780007407603210151348070421035030003030100081d51030046020348810031858900092403900403a00c4d03914600d0b001081d2030346141d03460145400290741c0054850305942440d0001031009507038028402e6009051f1154102030f820a40c80d54000c15007840d06a83c00074510340005102c000c1e200080c421071201403030100c2d8060850509110b07640b4024003003402544100c5400314000d40c04640b120a46e082100c03c2d450907156800104e04d035000b2441400c2c42850071038400a420f64000b0014143c418046d40240130744140c01c40281d0880f0424172850000c600044005401340500d03522640201d464401c0c00154040291981c00899409182683ea03503035000507001019a0408209 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 1843569 1250 1842319 1842329
    0x60606080604050601050d0902011407050120040e0412020a060c020303060307050603010506030604020a020f030c0706080604050906010501050c03040e0103050601050114040812030a0b040c02070603060602070602060103021306030b070e0a 104
    0x3d00c19810300d100000e00b40e10820307210324803559660440404583c4201101807415503944669916a18141840c500034402d681500407480c4401008040000001c01600e00321080e00702d2081e40c942d00c1e84c0740c14000f040e480c5120411405902d000700d0003c2d80b030f4882d08241d9010755000315203d182030400d162410400e030304954425581840100300350340e590021281c0c4060141c402503259030003400268070300401400c0c48a01030001082c007004140c000a40441142c00a5031440308a4071810f003800120342050703400c40c1550300140010b101c0d075400341700202514810081201d01e420b030f850701c245002d00c100f131f0411910745d08440d00400c81980d00001c0300320905005c80781076282619200007255600c2e00c070441040d00140100019219400c585c0c01080c107800301410a2248124100001b52106201c0c0669000b180c030f0030801050207880010280c00382c4442c1d4004004690840c0c08103c004c861980c4801c151585a850105c00628026030807030141d495519041c56842e02c0408010401101e9004 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 1844819 1250 1843569 1843571
    0xf020d0504032001030207080c010209090c1206010f050408030a02100c030e030406080402060904020c0307120306050d0b040204060308130303030b0102060709031104060b04080a0b06030607021c051303060606080604 94
    0x10620104514041082100700780035a030f8944a820f200069010313016180d005445244040b401421186042d001405a030303904070340c10100c40c3d40d58100003016000300301c0c441880d03501e1040012520f50248140c80309400140c10568100b41d658804c6518561100c0507040050b080394964243da1485406101d20b481c482c0d00b020721414100214450340d07805503104036010080c0880105040d502c03200115140f50f42c01400956565480c581d5043c2d59901c0a00102c0d101e12a1201d5108020310a12662003641c00052011541180c55114452100d034040e1050b684240d40e03d20000000302100001c01003054034200590342e5902d503040280448040d030362401d043d50406010400f2465102c407458059a51091420740c40151100208004220300e0b00301c0362031440000380c041842c04000840c4558144110042142c0b0b684400600d922440242e070090096840214080349400002072840c003000760510b0418100001c0350580d40d24000302d503000b51a02640d4040c14002d560344007510542c04007003510 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 1846069 1250 1844819 1844827
    0x40b0307030302030a121509050603060a140601120b06030a050103260d050901020702040501090605040e030f030114030a0b070507020915090105060a03020403020307170c010903030f030203040c08030a0f020d05 92
    0x2c0194991013002464030400184240d449007210300303a800084070600d001d42103030100c0d480e09a03079001020150b804074032a10540000842c044100e0107004158514800c260300e13203482d0000103450328200791186010242d101d40d0188003031f845d0070317000d14400c1d81c1c4a100410694036604040d85010f5010300450020503003101c403101195203501c216200d8030000c100014150380c40054140c020301407020000c0d8002e061100000300c6042d541c01c07080503a0003c580030840c003000c0144080c0d1304c0c0300e2408001c00d0001c080c0b0040050800321000145001c07405030545d00c594441d6a9844c0c2c0c80700c03080b18040c000c103401040301c4003541068aa00d6070b016541c0c0c5108400c040d03060000a541c25414403c1c144142400190800740c03500c01d8050304d0086d07502030201d590850b282c203030354200341c222034420608500c03038000126607540c440ea8031001142d80644440010f2090818110080c1d03200600030398000302802c40014070140100000e02061a07140d840e00d03200070701c109000342041ca41c0c0d6101010440244 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 1847319 1250 1846069 1846073
    0x102030304030903030804030c020306150f0307060c0b0a0e0f0d020606090402030c09060102030d1104090b09040f080706060302130203070306090c0906081503070303050c01050c04030b040605040213020307020705040b030703 98
    0x103e40101900e0700742c108200259220f1030119020030440c000250140140001c6c00000c864441030039142c82000c981d407a43c405824000d05030f075048680319001c0011030042c09032011a0b0101000ca8111041c0c903000700d02008261000ca00c0c1c8181b0480d0000d081e44566083c040f040d60500440d601701d8400c480300281400c0c1600060707034070355600301c00c00d00c034800035400f08107248c2c020401c94000b46440300e002d1090346000c13400c00c0c5081d08940714003030441d414040c0c1040c551400c454824491940300c0c402c00401d80c1d1544585403941c101d00c1c0111401c1d0b555030004005a55003119500e0904910343c2c003d80d5030300d48128010305654040d48805012400e01d0001c020482d0065110b03c00c2d100549042403055541000d202000140c54030708580600441501106065000c4028107809036800001e1003580c503103951030205c1e84100e100103410b0300889004640021090740005400500080408000000450080080340e00949003200540e00040d410486d42c10107002e422400310013103024292007032031a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 1848569 1250 1847319 1847327
    0xd0c050403020604091812090302150f0a050304060b04020f030403030e0c010816021e060103050708060112020d03050903010f020903070501050f12060111030307020703060e0c010c1202011404050604060605010203030403 96
    0x280c05074000644c6c40302a84804c6244a0f464180c18a070407955481c1c90780201c3e00c0151054070a800240c5c014991140707000700822120007116200d0302030f4644145010078400e002c0368a90000f0300200c8095403103001d960602d40c0c690010f060071140080c149507403414036140281c12070782d0900048440390004282ca8050740c0c0c00010b4240c1c0018429034803620b454414204a0608002040007184100008138a65a40100003002810b880c0f05808403034000351180422661000300340b040d03080714200001c94100508004000d101c000d8804d06106040414030000a82503810301440283c846a02090702030003450200011001450300b1300301246040c000d151038410921900380c94a0141e801c000c0407031603d074031645082d08071003045410780c0e84900b00000b00035142c00544c44180c030441d0410304404820003011410a41e440c2e4140c588110180741d983c0e444104500031000e48055558504c02001c42c101e1024030940306600c540c014056603e4203203402c60803900c564000c54110340c0107204010009400c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 1849819 1250 1848569 1848577
    0x201020601091a0409050105060405090a110f0120010903020d030603050c04050c0408070e04020301060905010605030601080a0213030303020408060106080408071103070302060f0702090702060c070b13080a02030d0c0504030206 99
    0x20500c0401d40d41041e0640c0b40480f050707981116005407601c074801c414040107603c0310b80210300481d811300ca6511740c0417443c3e907184003400300507003000300b48003002c0401d14118206401011060400320600e02e03000c40301c012004000c1a032144543d444202c06010180c0c140403181107100982000c002d82415070300d40d1699081c8441c2c41a000d030f079946e80803603205414141694014103104048422258a070251401d254030250350484c060342c00c1540101d015440da0094506843c920f6440343e08641da17010044412400141460411507420059501c0e0307102078822160107903010f9100507a0300c91515003480c2c0762640c142c0c4542c040100900038840022200c070100c07041e258100d0914445403688100103820410644d0000398000000203c401c007a0401201a00c0807034002c0b1100f100030354410000380d171900d00c12038104030042c500700442c0d00014619000180c00c101100c00c42101e18100b5940d800c0142d001800c4880541d0001c038042d842d5241c18000c08910002525000d41400e1031540440c0c06401 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 1851069 1250 1849819 1849829
    0x303040b0406030e07030210090905011a160201030e070b04051806011b0c08030706140603060115030905160605031008070501050708180a090501050f12060402041517060105100c0201020601 83
    0x6284d50550a6900b0100900400382d60024201406141c40e62000f1b1710b400b80c0e0b440780380c1e070749420a400080d60301400f100c2e201d40c0c1132101d0300c01ea29082d46d00c0b00d509400022040100c3c1071580c1c8803640d1402c1c0b04100850800303400d128014591f6103081c20100201d00001508103038428000304c0030040301d83d0b88141075450407529120f1070310348010a40f406090034496074100021a1101142c007906000c0160000d410445d4070851500c5c039501c80300285a1190000d0007408206000d40c800301d05c52520075440307540641c0c01030056070f00380341c021408035212805551152000030030101c10320252401040309040200681001886c4541c5802c001904500a00030041c2c40c5c5200450b02d50b8038044101c0d41040380792402001d40b61504d8039501c060008010030700805020351405040701c4801d040240746502c1c40c81e0480000c2c40603507500c0e407c1001401e4001000c044030b203070303502c00040c283c000c1c540500170941c1d82e507000d0b000c158100000d0100e854940c482141c20042003d803041b0250360003040381c0d819a8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 1852319 1250 1851069 1851071
    0x110a05120a09030501050702010c030b0405040203150a02040308030112020306090a0b060105030c040504050a06030b0105030102040b04090c03020903030d0c030506010503010e04060b03030c0d020105090106050604050306010608060312070f050c0303040b040603 113
    0xc40886402e0390802540d0740f02401950034107041050b61541035000030100307030040d28104021408003040c401296801c840094044d4001d80c405600300c2d1442da1000e500140621025150540369030721032402c1c0d00300ba8841d01485071400301d800114a001c0c48115401f03502030b0001c0801070260340b54801c41041c0a000036040c4100040400c012034040c0742200c0182c03c002d00144614180500d242d8010049484142d5101e14208004100b628041c001c8600320740300700440d1410b060070070451a004200d80b407610402d0590030820789865480c140094114800b182d000000c00812860020342680c40040c281340c1081b40810042c07246413074104000f40c1141d08504006003014506010030718620592040c500a441001c03410142075a0540180b072040d410440207110b42c60b81c520500c0703240d004500620303038140c100800501c0300e00d110301030b5198003403802030486520302e0314071100c20200d078401c003001e481c0c18030905c202906102007044070840e443c00580003185040c0c50000500345130700441c01004105 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 1853569 1250 1852319 1852327
    0xa02030903041205030702040507021606030213030204060e090c040b0108040305031b0c010905150c070206031519080c010c0209160c02060301080706080a02090a1206090c0603020901110a0512 84
    0xe0004209990141c1403c0840700c80d07002e00740c10481c0d070342c1d00a038000720301c5641031400003400c1c0340c40452103000b4238840324000c104013400e11005801a4000c81c0040a4400c40b5810000c05a619030003a18001c00c2c40180d2044141810075100b4281403c1d01501c6001d6820300d00e12805c2c9036404200e05a10035054070340390f078480d00d03a1005040744001c3d01c0c0c8112241200490f007940441e4065000040c800d11a4080360601410302030f40d1404401c04840140e00703114144401d01c003608101006603842411010f0581565111200040043d0a0143c105403041c0354200c0c28880c4d140e040100c51400c03102401c00e40d8066510340d0000b00000c800400316030740b00f0021010a0b4a1380e015041d55560b255000b0510340d140d41c0c4403007025503144098802c807800550580041a6505490310032200100f4000d007443c3d620a040844071500b10019210440e16141d880f134001c00490040d1304101c020380910303a4050703510724540f030006000030700701c9000068640146c4090300000e070340003c88403014491001a9516 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 1854819 1250 1853569 1853581
    0x302030a02040914010501080c040b03010605030601030f030203041211010f0302180f010c02030a0602030702070b03010605070303050c0408030d06030204060b1305040c050f04061809021801030506040605030a0501050f010b030705030a0203 104
    0x4a220000c1084c0441d0708000001c540300e080400d000c8003450701a03404118000c4a00101800d0b61801c0c030603150107030040380061021a0035011070042050090044034501076851050310901440f10200f51114403a4009404032903900c0a403115011046103004d60901000b56411100706282e03140087c40350007000000d42c8164025411f00075401e4008042c1c42c10354255080110180d4000c840345401401082008602c0c1c100400590f410b031401640c941e803c1240f01d580607002040098031034180b0b02e10511002030f40e01000c10091030549074980020880d10b01c0d5106000a48107030b80c01c20002c181060100c1d2212048140100040b540203c5000c52540254942960580f10b40c07600c0c6110444001804078906401040740850800c07000c07402c4d400c4683c3d0b00d250500320b010740f100000120b20701500c00d5a0070740c0b282d000302c2d801800080c400106644d4460010380782900b804401c481f9651910100610503142034052401414611749507403079898540001400c51000400715884181e0210100300 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 1856069 1250 1854819 1854833
    0x307050a030303020702030601050405010803030f13020d03020102130501050306030d05130b0304050601060e04050402010813031101050910060b0703020c06070305040504020a0801080f070501021b0301090602030a0e0d0302040302030a020409 105
    0x400028042000468882c100107000c2d5200c0841a4028442d803000028541014498541203039282c0e8055821902e59411171200e030900035003203c070400302c90300e09030016039241c6e15007103506886500016030700c030300301a14035050400d02da1041d0705003e070510802c202a200070440207040881460b010755100c01155030310404502c0f07a000344042d00004001c0204110001900324182c980b0382d00c2e40f9008041d02d000f00720940e0402c40d0005d0000d240c0c0c40126035004da084103442003452190400000d0301e420741d200d542c215441112a00401c2d4010100189001c1c060f20a200c081c12002c0d00080c5080350a40700a550b0340d03540302000340100e0f0001011018988035030306481c040d190092055540d03105800d00248081c10a000e0600c9a000d03003081c8000340c501c0040c03503400711001078000d40f0000c0030b80d014602c1a14155070740190595265500b00d400500e00348001c40c440c0703590784400038140e040000100c0c54280441c04c8101450310402051000d640e00040c0601610b41c1101d011414000519142d8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 1857319 1250 1856069 1856083
    0x30903020f0a0302010c140403030e040203060d020405151801050306010308030c0403060f0207030801090e0703030e031f061409220320010b04180804030f030203091002030307030510050105090f03 86
    0x3503082c0c040c14480004043c1d06411017550460107545060703410844203484d1700300b4030941c440240420990f504004190800350095a44144010a094500e822a40100e000da80c4212840d10140c1c181545000440c03810584404140000781e03000c0d4030560401021950799101800050034071040480002c1646804908039400795a002e001402911004901e80c40690440801100801c1c030b040000b05840b0355922408c40d9450041008180440ca561029500d900d88035030b101b80c05016001d00c076a030100c40020742a40d280c110340800076015140012122465010184003845500c0301d605000c4141401c2445030410f01e0410502c4c0e074500101c0c40e05545000c0701c036000d5680171002d0610b120640c2c1c019440031036070f1101a034050000d2030240b9060507248424070030041c44090140003d0001c903c1084601c829144240122840d12031514001496200244803c1005910010811112a5148c0200d5070043d243e81c107900300e05030800380040c08034040d58241d90302030543e11450461941e8100464 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 1858569 1250 1857319 1857343
    0x609050a02030a06020301230d0609110d0c0302030c06030610030506010207030c031401050a020c0d0e040204050405010f03030e0f0d030c03030f06060306050102011b090302060c03070602040e04060b10080703090302 94
    0x56841410f40d2502d10065042486a508004100314602141c2c07940e4240c03826058000034941000d020403030756031400501c2e8110f4155203200414000003925155240c0040c1c0d4107006d40c03030800e42e040c80e42c410545040c40c1c40e00264040d0a007401401025110b140e8048114142820081290355032800101d203090200c2d0320140001c01006400001c1c844202b141042a8580d20000e01542d030390301501005902c40e0048c920220380c0041d480c40499440743e0200e03000d00301f0041001d4900740d51003000506903082a0040c8070301c0c201c00c85040081640082c1c0c50500341d40305684120711582d1203c00642228030114000e0207001600c00c1c4002010301c60750040c2c40d0500b60b1f600400001ba15010010020882c2b4040c0c103001d5843c2c0f0300700b0094a0481104801d080b0f240d0b0f940c280200e0300b142e0900c641c2e90000e000c03046680c40306101d201e00150a44c0054030140c81c00c0c0100e4100d03860a42051419120580310403405047d40b410030510540c0e010709643da002506007004900400c4d24036003245800d040c0285 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 1859819 1250 1858569 1858573
    0x30609090a06020711042406050c01060302060403110306070305010308030105040207061b09080c0102060f01050d050f01020a02030d0b040c02060708090712080a0305010e01080303060d020619080103060509010b0306040609050a0203 101
    0x50042044455810302d80403290646c0e007004502c6003403044005500242e0b80013000350000d40010802c1610540041060030788a20001c00c0c001d503207601103441900241c0040316080742e2402d00c80c070103007000c0010643c090090324041c0b00c113500d10303147d401e410b2006010b110300032500001c2000500c1059040426010383c0b042da0214a0b15080c0d9004203012154096407a8902901c00000034661001410034021580d000f41603119900c0c040c200030b40d82110710811104c0b4010301c00c130380c507201c0380a00c068409090340e0740107190b0310720005030843c0491707040c0c0c1c406a105a180241c090071a5500140c526444000350a0210864071416143e500e0010a83e00501d1941e14808081081100d8800641051580364900348426620713140140c2c0701c1e4809010340c18447d8401e1000602a252a018503200c01e400689040e00e07202c0d621044900002201d0852008600c2c4030300100200181c500c2200c0d40004641d001704003004100d000a9107644000e0000350209032220000409e2007030502281c3c80702513000f81 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 1861069 1250 1859819 1859827
    0x50a090b0a0b0306010504090201050d090f08040602010209040b12030703030506010e0a060201020417010501050d08070c0f090203070f02070803120604020c011b020601080a020609060706060b0a02030408061605030609090a0602 99
    0x800740c1c0103440c450b2002400b07801060000075450070280111140254161035250030f0400360840b003c000d200040d810b5801800e07410405010660120080020301101e50016030351300071400a000c19a4061200a401102c440b10030100054010040c0c0e8103d550619000c200c170340355000104c640d002203044496102c1c030711040001c2c0598056009100702c1d8885207079440035500024a00e822140c09104003900400f08a01c1c2c07000007402c260007003100324842c80a01e00469190504a007507241c5a401045116a00100f0b0010303507504100c46c82841c20b403030310040501034148071000e5282d020700100150304100841c00f04c5c0056079150152008003030440002c22004000c081555440d0440780301640c05401100008180e101020030000c0e80680c026195600d4103510006105035548180010340da40ca503101000300710b142c442d10003402d914043d5401551a01d081c43d101074101071000d0880f9081c030326000c40e950780c1ca5802501340c07940914105c0b80346650b82d41e0100d1440c00c0c000c0c0300304c00401582c8002 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 1862319 1250 1861069 1861081
    0x20c010b060f0a090e010305030301031e06090605071b05030409090611030408040509010e07050a0e0103021201061101060603050f010302060a021005040b011a0703170601030b0312030411100f03050a090b 89
    0x182c00340042e1100d036900d45100c182c1d601c05884140e0300a0101404642040005001041d0340012031085d405d010404014040300c5512844104e40101c501114800d448100303120310141c0c8002070310440300740124101f40c0f1900903aa0b82e640c84c42107120301610355445601c107505001860b030140c041000450105a031300c0c506440c043c0015030041c0205031140403110000710746030840f441c0c0b007031203410203844a602d080154a8190303a0031801d58141030425800f00b008410740142441031034000c18150311a1b003040e2140a103080d003500c034941c01401c10940341800b0440341180382d00c0050b04698060750055900e0b00780300c030100e0621f40d414145031091400c000904c000c000703c03003901034100d545c43d0070009031540100540204611400d800039000614507101d00303640200400340c070b5820810504002034000443c3c0d01090904c031041c3c074904402e40d400700800c41800021000300d0081007017100d6806610b4103020015040b801480040000c2594440c0026251159071f8040c4007032a4102d11602c500d45488 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 1863569 1250 1862319 1862347
    0x50c03030405010b0907050406020601030602031305010c03050708090312010308030603150c03160503010602030702040f0e010c0206040507090506060a14120c0d0c020705060706050901020d14010906060f090603020c010b06 97
    0x4c000c03a40108038100000700343d1441407068030190b401c3c0c1c0e8050b004903441c1d9160f09010b504080c241c041d60440d120380c80800200c091141504000054402156a152001d00684601001810301745a0b070010400207601c64400310b000340c10b482d8800140d036106c0d181c50011030b10344000303040b00c000c0043c0310742c0900c5040d504103005544100d501003062000c00500803006c44450000b03110b5600942e00900440c001407606810a007060b01580a0001d004941070b4900781c2981d03c14403481c009600541c0910040c00030a0000e50060010108140100d0401030041007040c8501c106a804000020040c2c00303013a44140100c8900321004050901e4608000030288a19032181d42c47c048424502403550401d03500100e40300c0e04883c070080c0079030f041c01000e40750b00c3c01070b040042540b4160b540c00c10a12080c1050303445010443c0b41031030301208056041824140445041d504010240311561406224299026903030034140c992616016031100580944c8901419452400c0d580c01100807800c0742c0b19581d8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 1864819 1250 1863569 1863581
    0x301050103030c0b0603070f0e0405010f02041805010902040302010906050c0703050d0509040e011b050f0403060c0e120111030c090d021201020d0f06030507030206030702070e0c04051305070c03030b01050c0303040501 95
    0x200c815001a40f03500c4109941e030fa00c42c1c0b0400ea4161035004080000c27200d0700300b24552140c0070b076001041007800741c80c03030804a9001e500a00164a00d40500061001703803885581e0160803070502c11031600d821900003074012100c921900d000c0060010710950750850511a0b800119403040454403500c080710809440c540000710710b0303070003103142540301d00b0040340500030b822600e0100e81c0c603400e030740b9200786c01200c15a01c0320341500c1105804000c00400100d2620410b4400034031a13a07503040908020042045400045d012903205030706020b407107140317034550404a070781100300700b210507070b2300c414100c082400d250311100007944c04070401d0400b4211071819001800c180341d00c614100005031009512608641403808042c00700c2e48a0b60301840141855402581c00c04a280100d038220340e510300c40010200c074204c810307200405001c1010822410702500003030303851100c0e0b03d0500907440c040400600303540030201c2c081d003019150803031105982d0060048444d0b1004a0043c2c1c1e0b660303c3e090070400d010b480 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 1866069 1250 1864819 1864823
    0x6050411030303060901060e01090b030903030907050105030f1f050409030305061903080403020405040302030909010902070302060601030605090f040201030b100201090506090c090106030209060d0603030f02060c0414090a02090301050103030c 106
    0xc050340c20056141c04000c4a1048a00800784400c0703900b070120886d42480b180d8540c2e811310030620404030f80316291001452181240c2001942d8034030b08076441c1414000c043c0d002c14103001d42801484400e45a80e40c1e007651141c1e10b0a80c544181d48246c2541d0300004c03007540310310b40141c0b808a00b4803d150b4103401003842460140c03210014086c0400785040d40e0f10366840082e001076001e120034801031410780c00041c0c009003c1c1c81104c2c1170105000004201d00c100307034407942c034a0340d0000f03188080580500046a03c8a000d00301000314601d031070081000803e000782040300c4940068001021a800b13940041d055050162000c03040008405000e0b00034031b00c06600341c516100354000500340001c0081c1d58000c2c1c01000c0c00b5094203902e0302400354041d4201400c01d40d0b114101703100324090b8030058802e0000550203a940e4000041200e80080d003021400750840c03440c204204418070040a004040310004103082c3e40c032164980d82c544882d8003d018181c03015a055007080d00001c24140e10500b0865458 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 1867319 1250 1866069 1866083
    0x308040308010816030204020306030109050d050c070f0509060d02030106080102030a140c0301030201050703180b030708150109050616080409020d02091003020306010e1203090301050c03090106090204030506040618060207060504 100
    0xe40c0f40c0006980d80c45a01c1e400580030b48500000740014245600a540c115001a0000c80c1500d41d0359581810a628001c2500005074081101c402041c420040b01005000c091100703841035040002042702d05400500060080d0a216020001c54809500010090456200031510f03030500c4001080500f00c074852040c41508410085500700c90300310f003241d0403286d058481c0c82c984642035405844522200d44000711020401000103044407041000350310621159560103e549040c90b48400b4201c804c110342810403800c90720501482d141d0703404881c005c604041d01c43c3e16034602d0b46480f0903d8862a00704058203800421010f200d8030954011b401102d000302d425680502910004604900044441500144100c2c2e200c58043c240940c4644d81c0d111b007901a6441e140c401c0010070300351030054071340c0c0a00107000010448106428400c24001d850050000e41c038052031900c07103a50b9010040c0000d0481550b031007800119002480c110100701340e10030000c1d51102e01c1070a1078402404101d405403518 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 1868569 1250 1867319 1867321
    0x509040b0103060803040306090c080a080a0305130c09020d0209040f06030203070515160201030603080c07030209010b070305070809010c0203070602060108010b0105030108150a0b04020c0a2604140301180308040308 94
    0x140d07000c0c3c000d80d02551558402941401d195072a034901030002d5040c260354154180c88007103a50780003440140c4000b4052224180c3d14640358070300400b118001811452070401c03000c440313000500021030380c0084880d05d10b0091303280d01e290b4408200034070900c5603850f409464041c000403400070940220003180d0084007a10400d9503071703000b4030500c03580301d0102e02c00a03001041301141e1008070510041c0c0840c0180340c0080c505407607950b1040f16a100c100440c0040e405004208118580554a24050002c2900c3c1608000165502506902a000000303100100100e12001760341d100d889921045030700101160400e0b40e607018041d464110038050f90a0b84d500349070300d03080154080e4046034100c540c15030082032040f098072842517941002504034800940c550601d544e0541d568000717080403242c00400b520a6405610f0502c952142191a05903e44030101e46074282e00010310070344007141c807681e0041029441c803800190041406000380040e072800058030400741076101101074401d92107a15a0111 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 1869819 1250 1868569 1868591
    0x91d060307080f10020a0306050915090714070602090411130305070602070302130b0a030b0a0c03060503010504020f0d080c01090606140102120f13080604030c030f0c02010c020108040305070b0106050904 89
    0xb2000c0c0f0844046841c0c1c44904001109075640d070007800c08407854a030005182d07032600d0010b501804190703400c189a600ba440103001c1854062000354101c0214100701c2040d91023041c410129000345c1c500a8481130307000c03500e40040d0311190410f400d20451480b145940e0f05640e00b100c000b2480d203010603102c81c0700c2c03100040b418031700020300c44040e680c0080c4a540d4000440b41020042c10310f0a00c11a086203c80b08000005030303414000d14015400c0304404a4205080f031002800c54074254000c0d88280e040ca400d10000da1541c80203643e40301c4007aa24220000181e08144200d482000c02d525100e6180176681018016942d20640079585041000840020341350012643d6640810340d40001c007a0400034001102e01c504020506890411440503000c0d036904045828403000710760543c0801e140b4840c1c1070400d588010f810802d5151800c1415083c4016000208400f00d9640001e040c0428100441c1c01d05018100b590110740e0b0000e0315644a41c1c581c0801044c0340c100e80b490f50f0055051414000b9 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 1871069 1250 1869819 1869823
    0xc0708010c090504020d0f05090304060e0901030c0b07030203160503030114010804020a09020307120f02040f0e040b04020904020409080a0e0a0501090305031602060405060304030906090e010e0a0903091d06030708 93
    0x540509a0340d4182c42c603428803042100179849540c10b5600c6543d5003250919030b820340e00406105014400203507440714904603000d01012190f1105a214840004c0140002040603d203801901d44440e8080d4481085190981c650711442d045191005140c2c802d450420400100550503590301c462000c1c1b0000b0b040005583d0a08155002503000d100c032031080c04045010740c090f50340820640790045030b01c218446200d045444081d034403030102d900010248219220000307101c0c001d0520828a0400d841c190315400e00c622030107400248256000c4010500359503a5401c80303149140c11050182c1e543e100c1410240007034810a00e118001c40d00d02c0000100380d03014000b402c088941100140d86086940c200000c0a071440400499001c60148404111342d1a01c3c4040c2d0321079071081c1c40f101c1d5000d06002d000b4019840030303402a622090301d1001482a0001c040305260400410900845c003e00c442ca030654480100f07410804c0c0740340201d1b00300d064000c91013034800d001d282c0980c1074555898035220b40d15 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 1872319 1250 1871069 1871081
    0x3010f1a07020306060103050603070506160c060c02061803120309010c030b010203130e040206070c0303110f0106030804090506010309060f0603060b0306070206010501050a020f100606030e070807120f060903050c070801 96
    0x2940c5a00031384000351495000341c01c03080d80b0410007003e46690503292000602030783c00c01c011205890000e590400104440440002d0140c0240e04280380f000c06140c1c0000d030b4902c10b0a0b05d0603040c0113400d4022003940c030108003240700c0380c41000d42585ca1340391080707005d4001c2400070015030000b41820300066065001200721a00707800304c410540031280c140084a5605a0050000c0f60403010400c60030000c15501400701c400b42d4486da90781441031207165806481d00c035408034250216450304a003040003400143c121400c6448820000c5615075911006a00070f005000c80600010f00f0b055841e402070f04241d2142058074410b0608102010009040c1591564211644009a488540144595806203000c0e0101000610458010f107503a55103d9041400031407031415540c1e1612400d01080d03416008110403d40d419008002c4a8a040000c42e62400785100d416403095825800b0030030700500d81561000c0d0740c1c010340d090140c0c0b0b0a03450000d1043c2c0c0f240c6484106400343c1000818202e4060243d1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 1873569 1250 1872319 1872323
    0xd090308090409030203040e0f040b010f06050a0807050706140601030f050402060304060b031204090501031509050705040b0f06030c090f0306040803040b0a02120411010306060203090d060905011103010f1a07 91
    0x441c1001808018400203122a400a800354402444001800540302c008107110301040303601d0302590304041c0303421400c280040c0c00001110000c0d050900406600c042501d18034490343c5860400d503241c8940c03c0c0c0d2240304501c400f500c410705040c102c03d46040c441c601c2a000f0792080c0d03002c01548011115810444c2c0056600a5105404002050110b16603400c0200e1040d401019207144094504d20040b8960043c2d1040d02155200c10040040c020f45402a42030320081000910240d8025642c0e00d44a14213800f60714822039a0b1110024651036100d4810050500500341d00d03600d06041041d54440d030022005503220b200074030030010302d82c100420020b010300d034014005401d41e01c4a68520704640300007002c010100e603007071100765403041c0042d20360ba000e00c0c01841d034000480c190b80001416954540c00c9032085d5401000710040f1616540d841580540d04640c002074002e880340390482c003501c18040017011007140440085403028154045008542e0044844140d44103c0122003000d80240000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 1874819 1250 1873569 1873583
    0x6090102070b030c040f030c0f05010c020102060402190b0705060f0603010c0906050d11030414011a0109060c051002030108100609090c0501270605090918060115030b0603010b0a020d0903 82
    0x300700714036100e1038007850301310780b007020201c0c18507403201d401c8603400d4001da1060f40c0515540000f08103640c02209a00003a0000303103000108078841e40c0000c0d5496034050320090051515250105000d8400041300c0064146040c400da074a410904145580e0002a290110591814000310305a89030502c07480d000c1840d1501c0d0b0741c0c140c0e460410117951b45d82104034200ba80d0b81d100d0405004226600c001075102d83e100348509001d0701c0101c180c290841d410114900020030004540c0c40c004da03000000001102e51a01e424440c0788064030707250741007801403008110700038004000440c2d03144010921102c4422503134410441103940381c2e0a00151108828041d00c85400c102081c401c551242403e803072039100280c00c054202080401d21090b040a80d480b280000328041a038040e1403034056400c9070040319460312050f61031040b2400c5070712410f040c070890070700c80d40d1a010307401c0550190b04664100c040c01491070341c4035a0742d01c00c1c40c030b001d038001074a500050103203d048003040c0e80144e000d03000742c07904a00c07 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 1876069 1250 1874819 1874833
    0x30708060408130506040303030603030215040804050d0609050a0b04120c031d040e0706020606040b0603010e010504020c0f01050c030703111201030213060305010603060b030d0203030108030d0207030e030609010905060606090102 100
    0x30780c09900e90101d96283d803071100a10010074503132201c1c0000c000940c440e079400202c103031650900900b40f0041c40104149c5044103003e02c00451590010384080e00c10032691100b225055181a00082041d544024100c0c051070311a2030510510a105074847c50007040c5010224890729000c80e116030034440e00501041407040c0e0715140742c1d014030442d00c41140c00b620001e040c2c0380e03010300189002e01d10340c042c60050b8040001c100c15424140102c95070290266040380c11941404100001003005000361405158042410519404200811210116920000c10003403d0a0034410100c0e40110703042c0001c80e0038000040035a2864800b1250300d20ba5181aa0420364215400c000d4030501d8501120203240c1c40305804000704200b0b110300c0c2c0045104a034000384009201c010301d4101103803030340c901086d90000c0c801048810004070803160f0521022800503030700d079668902603861019503c159501072041e0030402804600540c0301002c114000d500b140d41c0c9540d110708001d11449a00c100c540182c02001c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 1877319 1250 1876069 1876073
    0x30203160201090909050105060a0501030606050d020a050405090405030301030218012d09060b0d110304080304030e060706020a051305040b01020304090e0111070c03030e0301020909010b0306010309060c02010603030e0307080604 100
    0x104901000c1d20500d4900c800507035070050300d41602c01501d000c0d0384995607a03051000350b14211219200400302801c05004540c940031010b0a03d0003540124a00030382c0000d203150002d4425000c540240600074280c10721414503040107641c0c0e4001f400220302a40d001c101d0040c06041c0460000d04850350380058116030f0794140000004621a0055402491080321b03021032011414001c91010300340c4401080c0e20f503140881101c06035800e000c182c09407110100188004503211000b265805505410405c2c400382408c40412064403525001814491002c038029407060341c00401000442846c154043c84543c43d0300c20481218040d44007680541e000b0001080141c4542d04140c05c0c17041000b000083d5042c0c0ca4907481801ea01410007125506503861080c410580c00c641281c40810054000f10304014020700810704584060141d4018100d02000142260380b0079080b208034a42e00042c21f103c0710b9041e50f0064007a000034003040b00860101d095480003801c00180c014101c801d11002008551683d03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 1878569 1250 1877319 1877347
    0x602070201021e010e060604050108070b070f020a0303030207030e03010605030303150a0e010e01030201020f0f03090409080d090809030709020c06040609030c0506011806121a09010902040501081501050d030203 92
    0xa8104a0550050070302d1420078800d40c1515102e44581200040b5290014444003800d1110040c034440c0b00700e1401005004880c4005014010780d00c880352071a030380d80502c2c1000300c08200818402907210003031000c0441090351540242017002d00c01c1d2519040e000381c0108050a13288503001d6150598400e00008030080288034500300c60300c41c0034200030865a120400c407025204240c1141002d000d9401c010021540e04100c0060003c901038050301080401d1030056032203100b80900e440c429512040c000e01402081d800302da0401c4200042080301e5403183c80d022649800414940d44640501c03030b80083e400046000b01c03618185a440070701426996542c41c90001d261405040d02084024448035000a40800c07105010744050040071410113281d0018106a07440ca400c0060041211a09280080c0782190b85080740103800140e200303541c1d1403081150050406100183d0700c0390422000082418010034100c1c00c2e051100b0841015a0721101445100014010020700581c07040001c0d1038401d0319 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 1879819 1250 1878569 1878577
    0x20c0c010f030209041a031e0a0b070302040b0c0a0303110702030705040f02040803031905060d05100c120f0603020a0501091d06010e0909010b0102070e01060c060506060c12040303090906030f0602 86
    0x800d080042c104100800480c5c1150784d0143c44002c80318600784403444c180703400c1007500e00c1d108008900c074100d100400c81843c1c4a840c403503802405a6148c90210b20301a00a805035005003510040c0951108050b00c6015074888183c00e00340c0219180442c0380c030b41c1601d014120340340240c01034018000d88e440d00d0b00b03000041500d4104885490303030074440450034020a00086008103d952034802c1c070004e0000c030601c110303040513100600c03503241d000d00000022800310b1200d0040540380b1000501115035402138518240105603000411f01e401c0750501e103580d1b541c0c82507065900a90361503180a44030001558001428050086c600c0100d8401c6c0d040c40c000c204006a0211040c5490818054050f020404004080da0390300f140d651a03072103045080d641004200c006102918402003e94541300c80030307105000300f84016000c1c40d20380700004c1d21611240200c410070441c00003180c800320070300042c04890350440d00048001035031900740000c0032a03042c00b4103020f40350022448040340107241d80315002540 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 1881069 1250 1879819 1879847
    0x8090102030c04050d02040f0203130b060402030103020a03020603060a030203010606020718060b03060d030203070f030804060507080402060f0d0e060a0603030801060201060b0a050c0c04060b040f060309210203190306050103050604020c0c01 105
    0xa110611090348c81034a0000c0d5024214500340c0700d00714030091500d42401d280007803c0b01d001d14030500040025903074141200080365010394489943c1d0b2900c40c04103070b00803507541001c0d425608043c00001c0b00341d80054903c00300d4004a041c02103107402c0c0000202501c04900c181601d010051002c2001841d00701000140c040c8280100c86c80c03d84103640756144010805003e85c0814001d0040006119030740c000c0d1640682645844c50f010b01c0d180d80040c0703c0d4028400042482c4e00d000c01d240c1050503003507110488104a0104503550f80c0b5080005070094422400220000741d285000040c25034014010302d0142c0e030301094810700305407000008483c0c82d00101c60000e62807041035810301680d10740d40710700c4000d0b2541c400c0701aa00c40c142007006124031a558084410145840c454801040f00000c0c3c1101d100c82c039462900599040300001c078130314050f030841c80d0fa60640c0c07102000031041d055402a01110421f817800c0c004c41d41d8030700402c01207019005048074142c22041003510903610a44807440c20362 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 1882319 1250 1881069 1881071
    0x4031101140403150603030909020c06010308030c09090405060601030b0a030b06060f0405040905010e0105060609010503011a1c05060108070e0d060506030708010f060801050114030709020906070b090105060108090102030c04050d0204 102
    0x10364a49404111300b810056103401a55145418424107038404c280c0c4002c0c1100c0c2505500c2c0200e20907415a0380c40781444068200c0c5804000320305650707481c008650000c28000d00b000702c20304050410a440b0441510100d0120380751050325445800c100d40c00c041203981200020465641e084141302c2c0350b03407050f19101d903842030800012a913507440d07108040b0554050000060900002a00039003111300107030980d0302ca50790500520f0314603a48a000c036030558204003490f0b41349030080f19840c900c90007090708076812001070b6201205600c1d0300d81e10151040d5000da0350400d454640c220700ba264a54a51051508022490344100114003075800c035030f400c0358021307003141e15056988404a00b1140d00f10f051602e01c40d260301702005200c00900560b400341807810442070380445140002030b034400c260b20030302a059801145403c50ba40d2100262011289c002c100f6060510300040c0107802483c00310303030b002e01040b451404950700390b605200f602c2c440c1211660152809003860200802c1308103000c4226402 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 1883569 1250 1882319 1882327
    0x50604060305060d0b090a0501050703060f0b070203010204030204050c0c0706050a05070303020304030c0c080d1101020a02030703110c090f0708131203110d02070b071e0905090a0b18010501020c04020403110114 92
    0x82d8204170705403050194002070504480b0514202d030075100080d110400301400d005003840b8156405690000b101c0700c00e0f100541d107410030701c082406809140c0c0040c2d8000d2402c0204100119204000c11512400d40180c448064540310140d405005056592002031814030801c40068000d40c0150b80042c043d00300f071000040b6507550081e0b085026000701d00f103a000583d905501d690400241d030003c0340408020341c108003a03450300a581c1d000f0500040c0030410700c2020200e842c181401406d42e1090040d1600040c0e1400315200c40c10301d039007900c82d05c0000b640000000d028800c14024070a4840e0702c184c1410080000580440240901c40501d21610b80104010f40c0c10242034802000c4051203800290a42d1500300000782c131b080c0500d0660a01200c8428090202d16400031101098644c02c5030030710b407240c03103c8030000001c180641005070003480001043d0300310032707100c05214100c4009074201c50120b003514007803205034001d500c002440d001c40d04900b500320b5800303903c2e40303510074482945171410 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 1884819 1250 1883569 1883573
    0x3020c0a02040603050115090504110121020301030305070c05010203070b0105040507050919030302010e0a170a030605031e0601050d0b04140102070209010e011d010b2a0708030310050901050604060305060d 90
    0x889001c0d904c2111160755400d00c01c1504c80301085c480000780400300c1c040150385415120040100c1000c00c0b90ba04101a41c0c1c214140020000014403815030b110300115182e42e100e02c2d0241156000030401d5942c007000401c001207640c8000708072480d15511208440450f440d090a0002034280945080b05110003404045c840d07848881c40e03103507561004541c18030401d00d0350030082c0c215040e40d40c010030a43c02c406458400f10300901d00485120004100c480e684040d549421070091125030052a854005c00b0054001d0f25602c5180800c5840403c050354030076640c40701004004103115800402c1111150006030100308180d0102250889100000d883d000460703002400400302604846505101200141324055801e0007805254091810000c41d5506200040c0194040c03040d14000f03541218490a18a00c2c00c10014043c107410300049981c11a160105c0c1c1e900c03074004a4002d0f507000504040081d06181081d21035040315805444075290508240e4228041c1c0001410603030800d07450211000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 1886069 1250 1884819 1884821
    0x3030d0f0209040509010501120f02010e06040612050610020a020603040f0c080304030302010c020303040c030209060a050a080f01050907050906010807030204030512030906060301290d050607110d0c030503060103020c0a0204 98
    0x4480303500140060381c070740c1c050040104507000908001c046038500300050044810b29440b031307000941c200000c20001c100d90320048402c175060b111420381242c404100080c041e43c0010b41141200302c00c0c0740a101c1035a030007050080b1140400c20340c0c001a4001032a44002d4100790f801140c10600940001010054a8071442e110380000d6000c0390302a40001410000d156081c410000c6d6041c7c184003a500d1800d054030390b46000081404081e201d00500004039200e0394580800800070440508100b2410b907503041199100c85041540079900d50034140054a6200d002c076401e425154010083c00c0103450b00401115052001401c10b000c2c10fa00304004800700740200700380002035050000d000d599180c2140d0071820a20003424a40c040ea0420511502d100c88013a01140006e0760b02d41c0a20100070b41d103000070010000340c00090283d000d508140704501d940030030080c2d110402001207403030b05007556130101c2c2c2c02c0300002405000200e050020940541c070a0b00101410b2002c1812143c8004207500014 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 1887319 1250 1886069 1886081
    0x403020601051909110c0f0309060301050906010309050109050606040b0a05030703060c11030706020901090e060d030e030a0b01030b040201110615040207080702031006050111010b13020901050c07060c0302011109030a1103030d 99
    0x205c0c001c240441c0e0904100d808220000b40803419902650400c9123420210341d8500040c0191032080e41c0480024807680d10035801a1441900040203100390022820180c0e1503610584826000c2e0342000701507016070400700001801c0b600c014005164a80c0703141c40e060014610200380c10200b0984000c0400041810006040c00c40d00416006a0700e210050015000c0020743d402103000c0207081d0200045540c454200d80c040d1501800c0038107004000200280c144402840c0007014110135000202c213000c003041c1c0c5c440c400c91013a21181c4444230030710320541e41c0d16011038140d20b000c000d0070380352451400c082e00070300304592095050900f8000550300081c14000c41340d16a041169079030304200100e60b03000204c00c542803030040003040740403e0071012603032000d5050304030604a500021260384503485442203a10350b007001402d990003d91500b5004004182c9c3c40400e0300150700700750410904845c01021140c004100030010240c2c034029503104840505810708080d4180400c1c0a00c4800038102e000d52 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 1888569 1250 1887319 1887341
    0x90c060d050124020a03080a0605130501090c0309020607030c0302070302090106030b03010c0905030a06200a0c0311030a1704030c08040605040315020408030901050f04030c09050612060403020601051909 89
    0x319542d81060103e0141c00211998000b001e86082280c0b081d10350045820040c20741c0518001526076240030700c4501800141e84580c0c3c0010800d00d2040c00341947d54000350580364194030a100c0d10000913004c40136242d40c183c4c00380d0b01860030080c500010703006240a6500740c6c03080c0180d5595a94039000140458001d030f12460200351a8041a100c6140c207203d02c0240c03c4050070003504440c00e11020070b0741c801c0c4000000b0301155907890500740c1250701111030b928581f5490000d540c0c1c1e00d40e180d0010071125441078100c1c0031071190362902d0040070010055820543e19513071448001590083c041210200190090b410f000990540744003160701900100094583d60311139554a038550700d000c00c021100c50001c0f0820320303c140000d20039900080201d0b6417010003440c2031131300e0307118442c480b181c288507a40c0002c1050b00d0300c200026569a42c1d800092181d1070480304040c089541610854481c4030485d00100140c0180e0300512042c42c108001e52443c288244410700e400b03407035028220460b00c0144c0c103 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 1889819 1250 1888569 1888571
    0x3f060801140403020d0509060c01020d02070c09050606030604020304030309060603060501050102070504020f03010b070317010306050711060708010603020c01060509010e01080f03040605090f04020f070c0302030d02190b090c060d 100
    0x61164610900450100540003903032840a450241c6000b52a881c40c0d200d6102000030000e4400081d54440007928060744062000310744d1220f0f100124030096124a000b201c0c03400c00d03003c0024032240c0b00d103e00c1c1d114400c05082c1528569a02c0100f1009620040088040c10b55030580d010200b80c40340300342000385110b154005140e50410002900c0c000051740117500c25070040100d03004048907981500d045500041040b1b4440c6058903080c1d500c43c1c03131f40c2c4190705582a448000018000b494001c91f00494041d00c5005035500d01e0180e00e512003c5c101d82100200e0a9640100320a5101c1e900610010910500019401e606c450019401c4142130b81320803540c181031001030004e42d00034440040e269101100452406103800009022802030303049103445452002c042c0400394a407601210061440c140c1c6980d40c480442c680401e20541a000c241d02034890392800038446800020500d14090048049441241d11640e0300d29030040000e000300d01502071782c402c1403102d403070b030201070b01c040021054 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 1891069 1250 1889819 1889831
    0x70b040f020a05060a05160f05060c04090c0905030c0d060609020a11010507030501030b0c0306010201060b04062001020405031203060307050303040608070305090a03090e040302070513020403020a0906063f 90
    0x4000d0712904035001103110340740400170182165040400c4503180791402104500401890070419042070901c88098164001c0c04200700006200600500030781c0c411740d404000c410001030081364102450f018154040e4031482174100e00f881c1c110504030300c0700d00c200c00100b262a104c45201c0243e802c07681610007c651010b8880882050a001d800c3d448603151404011541c9107071035034191504017805008090a0000c04510300ea4401e4104001801400e07003e15542d5954200041c0152a849010a41c4417107104003107516000600885c2c1c1200e000070000c1444030100110030803654400303040c855242c42500310004045c1c40a1011304021314854440300d141d031401320030280a80300004d001030300ba80c202e4001d00300040c0e00080c0103010780d420010048116a00c81c038050f4a088403640101303a020452401c1644a524503030000d100303491003075500d80c8400ba6904203840603140c09001d1480480e40d003a03034103204141040c0095400302c1044010407522440301e00380a0b00c0140303580e040c1002c25150340b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 1892319 1250 1891069 1891073
    0x907080d020c0901051504051203070602031302030c100e04020a030209090108030901090e0108070b0912070e1006020102090604090b060d02040e01051005070213020307030e070803030403020c030a050c01080408070b040f 96
    0x83e030550040c2015140c030f800152200f1849143c91107540a003c0c80340040300d552404026041003540c800650041c01150b80307013419000c1c3c011580024004a101c0c2c4278841c0788842c2803d1980b00009200120740b0742905580e81101000003a42084c164a070416500344018045540c0d26490315000388a5400078683d20b01c40c1c0c4000420055080d08503400008146004108004000440c0000c544e0011416515040840b0002e07045003028140c8039a40e1040300c801041200462000320f01401c2c80900001d00c80da90303a0016800d03400f9070064254700c440706010402c554030568200a0744004001c104600d0090100e0504049030007640180300f84407000d00042c0200d04104080500241450524900708440759000451490500d840c00c94200c0d004004076544038041c2d04400c404000c03050a4441568a03030b02100c0c2d503030b082114250010300c5500c5442031503003408621400300981101c0600503800401c00155448603001c0c0c01103c07a91000c02c5014041508804e04c2e0b070150344283d101c0c1703840600314 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 1893569 1250 1892319 1892329
    0x501031503030512040201050d0207050607020105060109060905061b0601060201020304051018060b0a0f08031903050903040603020705031603020109020f03060106050403060902040209040e0607030c02030406080a050907080d020c 100
    0x2080003500000301403030050010a800c18280c9080c500d031030000483e259170305c0c8012140760180408001d02c4600202d00c1e00204040401d50500c42e4000e58002c000301d9552100440300c0c0000c520a00b0080391002d002445503003860300080903510178000b91140003000d10301c0340351315101c026401400140d41c08414481044010702c00c41890380840c800a0000030600883c0c0d8803401c654440041c1401c0e642e000800090b12100d0003080102081c01800150395a600840d40d01c0303038031601600800390741c0e6400c1401f42c18001e00c2000d001c1c800c08401942082e00349142a00207600c034550654941c8400d018094811259941d8101e04521030f90000c20701c1c1c4520f106001140d22841242482a00006c0041c03000952000981e03003266000301d0b0104510301c8900108000340b0130364015075005410005800e0790b2040014145000c0c5144c1c1d0790400c0343c40110070f4100d0700c03406903014100c0050001d00c00b040e00908a900119040b107041816244681d83d50720003103203000300704e080700d5015800107621180c4d203140c0703 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 1894819 1250 1893569 1893581
    0x703120309030f08060112020c0a02040b030109032c04150e070206060f010f0c06020703090810050412030207021206010303020f010b03010209060406030c051b070509010b0a02070303031d1204050103 87
    0x1642024804035440c0ea0340980814a00e40500f4200846a000246030b43e12031255103800c40700403a03045580e0901421040d0306d440c0d07111400d80c02181404600136860805124514289801d580c40d580710205440340005030b42d8000500003841d80c280c0d0b18601c1c55039501d20410504558200c4540b40c058507001c01d5510650000300f080e800d640100d400c102c8241c40303640300780e40500303424a04071880c220010000e0750000240b05010703264904c0412003004150b00b1000303940030b40311010100c410213000441c02a09407075044500908011852400840e518040e401500201d071000b00602c00c1d03000c00080e440c0c9841004d078415001680a5540010b440f0760a1180c0b0f4440b42c000d030300a52070302d00340da000b02eaa280306901c956001c260751070021071001882482501c04201d80070324500e40340c9001c2545960f5030001402158421600b05000041498000c0112000200ca5030040c0c00800d2442d01c040d4020000040038031000e2040c3c1280a001a405010020030861108511510349023003200040407524 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 1896069 1250 1894819 1894853
    0x507030c0206040201080604150f03050c09090c0609060702120109120c0302070302060307020c030604030306053c01030f020f070501060503070608010b0d06050a0305010507030c050301141201090f050703 89
    0x1140c00d404039159a408a801503000d0780a0804550648682001c01d0007450741061b50000c0548081000c0b80007482e1601c00011640140100c41214600704104942584203840d80c80030790340094035a5800c0c0c24914094610f0800c0180b80f2420071455401180300030200343d200d058141d41d02c1e8802e03404c200c14405400b464038681e1400c01c40d011241d0394069540c0308ac41c013010340300b0000400000c207082d00c204649281c44101030f0030303206203081500d80600640254000c80d481001e40f1b0041500e1000041c00100040c40c060540c0140d440102244042381e81041c1c1c9014105600d40b0340d4410301c450b060000303201c0d25400b150740c0317680c1d100c00d0300b0080e013107440301e400040c8640c00206013003000c5980b0140305810354524070341c065500c99440c0340c60390052903c1da02113074001d045050008140b260640c00780e44155500d440c01d000700115118101c070503200074082e400c100c41e01440d100c40759081007100c50072841d480d0000003e0315182521240c499a01240d8100c60aa103c0da20600800850b0f003c40c0321102 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 1897319 1250 1896069 1896071
    0xa031203111801110304050a0b03040b0106030b0105040302060a0e0405010f1d0103020102060c0c1507030c081003030504060f05070602070809011b050604060504031b0605070216030206030601030504020d06020301080c04050703 99
    0x2030b0b02c0d2007040504100350100b00b41004080e50210121850900c1100c005040040ca8075140a81d524056001d540003164140d0300b84103440c0001a4941c042c0c001c80d460041c7c140d4610f0300d000d055a08000c611703080103090000300030103c208180717a52103511641d4082c107246e01200344120329044035489101400900c141004448500400060340c000600710b80207214540f0017910350300480c1d802803401010505000c40e002008040c030410f176400d41c1c42400d210000303544000b060f07500d5100309007152000d03100c000c001403c208410495240b0a4078000501c1d48280382c01c2d0302d8148503403280d03403c0ea04844001da82d00c840001ba61241903801202101200e03510030340500e81c214040d141c0c603844207001000a0090344d00c0708005410507108007201e5809418030354204402c4251070420300024a8115100c00241c0704506010364503251083c1c001b01100c2d80101224a59510040114050100a0000c0384c02200c4e01c503480e0005030060020b50b01030a06400102503801f220704c10001a500007600c008281 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 1898569 1250 1897319 1897327
    0x1090203030405060313080a0806010e03060405120a090b04030809040b0d0b04080a05040801020a02060109060506040302220e0a0803040312050402060304060506010e060d060305060c0406120b0f0a03120311 90
    0x140c4000c4141c60482e036007100c070307191a55a90340300c04085506141e0000d296490000b4003980c2183c00074006030140c102a62081100c040d038009043da1184103031000381c180d500c200e100110074404440103141000391480c143d50f18039a40c0f04841c10030381103a00101d07005030010803026103506040c42003805815089401d910900b0454039900c42403680580040c0101c100064000d4045001c1c0045030010020180215500e01800d00b0003900c0306c100f802100862801d0100000d102d1800d01c0690b0183c0350010003012122503120b170400340301080c114203540740070780b54060b00207450010b02400705507602440b406940d0349481d15008001450796503103e07291038900000d00c801b60301e4000c02c1e40d50050340100001100d4030750b2401683c0300040e031800250701c82c0001070300342d904981a42190301164403c204641003900d03191425001303402103005490000c0e8071190140c4480750190490103000750060031003800901c51102007180403029400a60b8003086000710015006da042c070521070100c03242038003507040c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 1899819 1250 1898569 1898573
    0x305031b0a09060e0612070309050601060302182106010303080412080115030c0201090602030a09051b0102030a0f0905040603030905010f110309130e0303040302011b030905060105060d090614060406080109 90
    0x5500307190269804104d810800f2112031344446045920f0003140d40500419407400c4840200a880d1422003204d941c0118000002e41c54068001d480101240b5100c08040070340315828045808541600da043d00c1c4000d413092140f00405001c114080d5004c2c0da1000b03400e280500b400300c944403800c0c1e0540c040004001c01000707211030b6985921040340080c5004607001d022104200e003d0041c0e0305015010620001c10f200360100e0700d6000b840201e11070f8083c0c0300742c030751502d41c20114030107101c485c2030141c1c20401842e09c42621420511480400303d09040c09a291114007080441e800e60304210040707011020140002d42c2c104c20240080d204601c0e204481c0100201240c5e10780c000c0100c01401810488a01c140f2007015410001101c080316040301e890740707414240240600003c00c4101c10701d410410003002914400d0040f41903a58010008240e01d91a0009000c10783d809140c0f013014080d507590805002410394040d058903490052000c40030780c03e16504010490b4500e500654560b8545000d001c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 1901069 1250 1899819 1899827
    0x405070f08070e011b030314160f02060606030f091207030c0605010b070317060102030d09050102030109050105010c0b0402100c02030d0c05060903070b0609060402040503030d05100f03030e0d110a030305031b0a 92
    0x4a08240106085004422403500f40c01808c80c0d0640300140d420b488c4204505120091001c1100090950710702205810060042c0c1c0c59010a40d01c40780c00400400000342c0c0388900406080d00001180200c03058005045050300d525003000c00c044001403200078454003804410b0017400d000d44902c4580030326000050341d001e45030503207541c14114003842c134100003062a802801910740842c40141c4c01e00c08604945041030003944240107540e0501e25003000400c43d9442142e014a0300c3d5401285080181c039075800308100c1e80100380507681005195180c4c500140c5090013501c20301e5040b5112800549040d01d4500e0030081e00914104040e0300500090011030281c1e10b119802090554405030716488480c0420068803540e00100c0d010f100002d4001c500440c0703540140e11843e61307a0380c0070142d1501c880d0001c510751803d120140002e424410407542c20b00e230114421604a10481d0580a0162094003144e1003400a603c01c3c0d0114001204004030781c8140a10340a005c0120003d84d03103420305040c4050 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 1902319 1250 1901069 1901087
    0xa020c0405040201090f0902040305120708040605160206040b0703030609020c03090103110903010e0d0306050f0109090f06150f02060a0606090e0c0408030f0301030201020c0f101206050405070f08070e01 89
    0x51160752900701140079a402000a030740584604420060340c0351711500550082d41c8103100c11522407190322000039071126440d040d0380c0318990101d6045e00d07142c5000c1044800c0d42001c4c55000c0d445081e180d002c0d005a6500005200a0100e44002625580c050a02600b15601544a0002e490041000421448000c822100301c54424280082c1060400030110118041e004520b9015031034000d441076560700025105400c0c0909a50a011a036220001e002600da162400c841c08102883c0003813040200580040d06079000d10700c9d00180c1c040d0f6620348629122150010b0101040000c82c018810660500034198001000c64061280c10301c1d066004201020313504c6803059102600020a095041e80303401c440080040400302ca0b02c40d40208080d1650354820b04c4124054410121240000c0c01d15030082440c003080109004074002c81600c0c25240c520081903000381c4160788040c00704041d80c81d03100f924001c80080d581d10344010004900645031001c06070201084c00015031640501e680d00500300 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 1903569 1250 1902319 1902343
    0x60a0b0919080105070206040209100b030103110d060606030c090b0414060c030706050405011b02060702060f0709080102070804030219080307032109050c010201150f0b0a0e03030a03020309060105060a02 89
    0x12a080c011091503500c44a035a04841c51550130b0506000180394000344c90b5000d01d0003142d65281d0b5480e215044817000d69140310780480100140010008100401c3c41c03025202000343c14a9100c401c00d5031180115134543d00306901013541c40c003403084074a40c0300c1801c101a10801082e1032a10f42060313046008020791003d814030403800052600f00c90207040c0151210b0b99402042405541001e1a0050180c540014919041d092000880351030740d10020b6010700540480d000740150b9101c13040441d045c130800408807000d0190400e030000d0558424401003860502684d00345442d00d0a500c100402d185244107c03d10361040e81c2c505015444000c4112060349074142000010241c002c0c601d11044c2c0a90555090210701d032580b08003c2c03280128240c518294264020003400541d0310394007100111500543c01c0d08604807005010929041c0c000346150342c1142412182c0003403040c002460f55000c0001840040c0d0044248a1080f8041000902501c8101c904504200e18200020740c3e84000c9a10 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 1904819 1250 1903569 1903579
    0x304060501150306050a090209031504060605090703110d0c0513030302010501050a05010201020a090b3007020607020708150604020c0706090303090e0601080a02030402040f0507050a02060115050306010f0513030f020405060a0b09 100
    0x181d09c03100ea808011945040403080002d0440d0b2602d07082420040800d4032515004d41c482d200080e400c1d601c42c5c0315403050700d102100c040f41030000041d10400101a1071040c03109010003007105540080c050540f40005500c80c2e8000318040d8107000c203000d030080981e48094156130040c4903a0032215041003208090762190b5040f651200d52148801c00035001e1190500281885450303128007090640300e44c14071400c4150200d91180e214804106da90b0b002a1048138081e8010346a10b5500a0491901c070303802000061015042051045055080002c03542c4000c02140b02210100201604152543c00800d5440c6581c209131410f01d0004c6c00c6180020b1a81031005c0d400070000b4115501c0d507102020328489904101b210b46807590f800340103948441018400b40c0b180c1800002c5001400c5211010507070556107032404c54481e0702c0117440d00d8010030900002c1c0315043c8503409802000b40d030039000850003130b0a03545a04c40703240180412501e0252070140038400d540380a100c040c401d407046071a05441550 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 1906069 1250 1904819 1904827
    0x503040b0c0a0f030c021c0c12150c03050103030f02030705030301050402030414070305031e09030a0f030215040803010608071107060518090109020d0506100c0204050403090b0304060501150306050a0902 89
    0xc1910304141200360002c0041116012500900d40c0c054103001961b48250b42d4440d649445034244100c503407200c18014a0034404071404d0101103190000303c036990303105161060503010b04030403042c02d444110f0507000000759241d0041040c554011041c9130704442c0e81c0003070741c0382c80c0382134441c0754481c813050240502823034001000c682082500410209115000b005403a4215102d14290f500c03136000a5006c244c00c00b4203c541c1a0418a00d0103c4284030380040052800c0030a5980d1414020310345a0160b095000394010164402d504c010041d2259206520b050398960400d680a0100740000d001101000b084041000240100103650416103ca9040c5240c0315103141e1015600c0c08404900950892101d100008001034a500a040c03103180700e040c14003155a94805000d01200c880c5d40180016485000d0349000d414281d0080350058041d16000d1011038541244d02d00d0f5900c150b034115000c507915030041025034002d1600c81c002c12402e26050003220300c3c220008205c0fa001e402200d070340590002e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 1907319 1250 1906069 1906087
    0x50109020103051b0301060c02060403061508010b0307120609081204050606030d0509031b0a09020c0601091b0504030308060301090f03050304030207050a080307060f020c070b0c010501090903080c0d060801020d0c020f07030503040b 101
    0x503043cbc41c0150340c07208081c800305c000c0303075045042d4100d14854080c0315801c12460a4403480c001c500042603400120203012103403269103418018200018054980100801080b03554a0f90264800e100b107006600900c40c3e400d0030006c0c0b40c5006c0b800401103040190602024056503070200e1000d801040341008000250040400a070704081144e0084c2411813000400030000f02c0c01041d000e040f114104020070030002448541004000f048401c2e80c00070350204020710009000701a540e400550103000002c11440303030741d140365014140c18410340124402100b001704156040007120007502c400c3c1d5001460b20300d045821940c078010501c0c01030045480e600250510440b6a044e9445801e1070021244600c2d034580c2880d58075804004850704035401d020000c1030300a030b28000e1000d00b42d40740ea60569142d6030542e1184403038200105241c6803549170340b8005085c40090018040c10848684006502c05560001070314014080f00c1c140481c1e005044200042400803050b14202d035261451503030303501805 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 1908569 1250 1907319 1907329
    0xc0603010e0703050a1b02010b18010305060711030c0a030306050f0406080304060c0201050c060f0103030807020105090a020103090f0b0103140106060908030708030601020708060403090f0602030306030a0303110d09050109020103051b0301060c02 107
    0x41c0c40c00c00308074602106da0136003413a4150440c0c1c9004134241c418480c40840e007550802e400400f400060b1480d0b00c00c0f808582c01501c034040031014856910701b43c038108458602c2283c189440c0403c20340000b5165207061006241c014072545010404580800840307203043c0c4070a849020300e1148809202521a001c01564001c00403216240c0c0b2110940d140c518142c00030800070f05084c0010b40c00911f0000018405138014400c5a01a00042004004540d6260700440c003401c4011401c45194030380121410000d0411201039004e18401d002500c10110f0030740707046086a000d580400104000c00404001e04040403048034111038018101c0340e540d40e1010010303072901045521200803442000300700020305510512500690b44400090f1981c00d903900c0c0201c1c1d50b404292035031545904000400030010303010b540b12071480c1c8803d03010304d030901e0504203ea40131204990829144c903519039011000710341e414480e03568000500b402c486502030a9007190b5020340414041c0c002842076015a020079075940e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 1909819 1250 1908569 1908581
    0x121020d02030108030406080c0711090709080f06180c0105070605060406050904050a050705010c02060d0504030207080f0309040501090203010e0408030903040504020c0a14060106140f0405040204060c03020c0603010e0703050a 99
    0x394000355901d5079106400381d80c80c0d0180c441c8000051000300400c00170078900e400c603481107810110641c692030042d020800380e0302000d0314030300612000c000e001441c04c000b40100310002c103000015102c43e140160345c0c250000346803030ba00c4030301d44c2002050038920fa070014161b40d4640d0304201c0004890360359201145c0100042e82005a000c1010010041004030002c0d00141680c403c2041d03417071040d070b124019515127040d1200294000c00500440411051652095074803034000d00c1161645940d43c0c1981e810141e400c100700010740c00000380b019050405004260041034215000c61466152400f043d102c0c00e000b520043c000c000000100742c181600300f00782c0700a01001801155101c8a0a0105645150500003103405501c03440c203160280c240403d0540c104d8102e0b84030018940309c0106400c210703510001c0c100c0d071001014413000c03400d03403a9440500090100380c5c42c1e00100c4243c606000e1314020441510b10b1007100204010b000702c0030f155005580007189800c0110f0592a500840c101402e6 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 1911069 1250 1909819 1909837
    0x10902030604050303010603060506030f070503040204090210050717040b04050d03020304030614090d08070509131503030206010f0f03050d05090102010227010906080402060307080402060c07060302030f010b09012102 95
    0x40381c2010b110078400080020b5040703501540301003004650303400500506010440b02d0358010040f440003c5c00c03c6006074019a40300c0d01c001d04c00074045a103540040c0840f100f94051500003007000c40c08004120a04258901c01c1c070043e500c25080c140f5046c1003450620580c000e560081d03480103000c208041c001c10940b009180e10031414844030f00c5120100340110002c540c8000c09200320000c4c804810300502c40e0074024000c956a107864640c3c40d070144000d403450b070b00003610001d41d07a51716003808038141101100914843d03800381500354906180059100641e40000801d8910074070200005200015144040d00726401c00d981c440c0a00f2006034024041c142c0003402c200000c009030654a54a00c1c003640882c1801d80745c0f02440398070303407004841003007080b0b5009400070400c1001c921554014620705a2080c030051002d403030044124281400c003001540000c0c082900403091240c1d40181104050240003410001d41c00c1ca02104002807000a10310300c403851401700075102c1b61120742503404503410b00c1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 1912319 1250 1911069 1911073
    0x7081903090309090e0a1106040302040e0309010201150e07080c0405040903030c0305011a0f0c0a080c010504060b010509031b03030c0d080603100e0d0e01030b04060305010c0801051002070e060301090203 89
    0x1404546000c0c0c041d0000100440002e80421004903007111244502402d50041c5e100400c9030401c82c0e03480c43c840c0128552115808582072100100580d2203024501d60040503102654031600d0310380000e400e40c2e100c200114205040380d14244491a17a0b1000700358800d886142450150300d5a03d444103483c812504000d80181c10840070105040e0181c2003040c2c3c040507960100080e81c6c5e240c80ea051b61300b81001403109401410840f801c0c092100001600c101245581500e18490039640e03903a086620594403192565113460801052000382c1c801c00c10213400a081240c500100c0900007600d8640000380701c010102d144802c43e0558904005480e01d00a28104031500e81e604020b02070080d21040390028881c0c0708421204940000500501540702c9003c001030801500c00c0b03100303960304022a03444a04140d514030909407e60790b5401020001d5000300700004034080021802803282005810060282221050b000c00903a40040c450f01100c1142d015050785031203400002c1e000d0000440044e44c18 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 1913569 1250 1912319 1912357
    0x7090e0f06031002040602030a03020906090612160201020702090f040614070c0c0504060308040b07060b0901030b0103050c030d020601210b010303090806010909020306040609030c050105010803040501030b0102010b03120708 98
    0x3803405a4281070259004404403803001c0a11840c0400f680310358000c0d200103070001e1060b501c1241c004c0d0058006503800410650030318803040c0111b02183c004a2420481000d031406025228440c503221020a000e00d100a51914103a5004685d040c4409442410800c440340d00140c14042540e0000e03280700c10040248015041a00c002000941049016984841c0310a030000d050716151240d001103a0303005c50142e0a243c500710780112290030044d0140c070055115100301e41c850b901c05420601840c8540b80c20a055411820014a070140051300030f8025408650705000d0181c0000f00c0504507416252107040224541071074560305241d1070340080504961200110825408c40c5007141641c0c40c003811070745140c1e640c03841d403010381e441100c1c080c0d09600120040390126102c3c4d017200310f640b4000e08054600c0303c000d60325503003142d400340e202c1e440782e41011400740001d43c2e15004180304907000340f0007802128040d1000907100d12401429030b03482c0703030000307a00c02c2007000b54002d503403081d0003c03580700d116 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 1914819 1250 1913569 1913581
    0xc11030f1002030a0b010804020a05010809100207050a0303060e0708010302060306060702030313050405132006041509080c04020c030f0304050a08030103050703020108010b07050d030e0102040807080c0f090702100507090e 97
    0x283d002503900f15442c45c10300305242140c0d489032000c1c920840d00200441d20541c071340001996070000140c00b91040b070185c0203a10704c42005d180000d1002602c101700501704907002d030500a080302c0309034000c1c41c1d1039a03139503080c043c01e5a444036085040d0380d0102c451607602d0300c9038070001c0c030f1611804c00001c3d010b00020541260a105034603000080307030410b03101445280d40314105042d411134079140041040c00c984010b0086c020b49200107100c0d16401800c628509070f11543c4000402a401c403140c400514801005c0c880c01c041032004841e58181650258240480e81e00042e440c2c0c051807140c403007803020100001d018001d007046030001e210781040009583e940c4904281da2910500d000503404034801000000d419034560b800c0b6080c203a0080040c1481141c2e4520407000b1b00020301415034259000d00000c103242e50240200d500800001004241030080d00081c492540b8000b50028441c103101c1c8100181582c01040c000841c2c1a10500001c03c0c1e99490300c2034030a500d49800c0b403482c0d800d200c0d080280d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 1916069 1250 1914819 1914821
    0x10090f0f090c02010c02060a02090102010605091305010c0201060b070201080402040906020c07080705090c1207090503010203010906060206061c03080403090b04030606030506090a0512070215030a06061202030105010c11030f10 99
    0x9540d0007041c00c0c40034401d034240a13400d0350494501710740141e0010001440901a5038007070240450b0520010922036075441c00113810400556202041d101d0307000c400701c10000300f4800c010348200ca80c002442218a0b01034444054014244042d05100c80031001804560302d41c0c0c1b0040031268090421900c034844190b05039600c06050080321202d20540501049501d0000e10382da20803046113103114542400401e0700d10021002038441c1c024880c5040020450755002e0000e18003811306202d0008181f40f03410340092070301c02c01500d098001c1d41c0c42d607103915150702100c8c40e6103c2290542010700058641e03103030850f21400280c5c8036941c070b2440400c0c08010440160040300c2201c0c0504210b81540c0c5502105540754084a00c0c010100c0d4030100070981c0d035a1000001d00242400281503c0c1824540540149582c0c003c88070550451f6440c0f030180319441d00b00700c1a1a40b03803403800d41142598180000039004044480c009400141d5050340643e90760350800c1045440304607201624400480150500 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 1917319 1250 1916069 1916099
    0x20406020607030b0a120303020712080a06050109050a0303080c0c01060902040e070509030c0f030a020402030114011103030408030604090f02041e0e0a02031504050106030b010803030105090109180210090f 90
    0x8006000d10030101d9046031290280b071018080003085000320a00e8824055503032030601c00300f1000e0603000c0c45850085464950700c81d50566098850102902e00030090904803042500441e0500c200b1201c14443c0340c0f681007440003680e84c9800c00c0c1d002901d4520340e008040c065450301c4111903003480300c04512120641c000d0402c48914264080e001d0316002c1c0d0640d00fa00505c0c0c485505a80300c102060500d2404540701400360070041e007940c071710060036004102071340e1090f004041e660340c600003442100d5a02604007040982040c010b1815410319076185001440044e040920903a01e612489003444101d07140d001000b50300520400c00c00d642403190202c020000c52656800503e00f0b00d02c0f82a11401062664103558028080e000c0016060002c882c802c01c0a042522550360f1800b000c80050f40030550140a844e542c2c00560b100d40c5044100125900c3c1600030300c4000e42080415444084003103022001c031581141d0400030040414001c5a1541c4507901020280041e04000030b0142004500d0f2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 1918569 1250 1917319 1917329
    0x60312120b060403020105090904060605060d0e060c0703020a120203090d060c030b040c050406140403050d05030108061003030806061b0d0903020102010e030f04030b04150501030308070201050907060210020a050c030705010204 99
    0x50166081c240c0401c50745004510010340419803c008054041c5051400c0c50ba10510400c1c00150290311000856100c1d0044647c000f42d441c1c4e174036500c11020004015103a4010091200f544c41d0a03010b070b070020740301c4020350801020f000c02c5442c280000c0c1c1c02401034403201407018081072a41965810080c5c09000c120301c0590100e86010009002810103024503e005040d40c0c6503a883d0618081c41200d108441e00070b40180300740300f84004070002c0c00900800c20703134078040e60303442e500ca50602110f00e080c1078020f46514007400b0061002c00000f600590107503400101203880c03940703554200358810698081e1150564090186100f0941041c0e0010b50f42c2c000c1e03d000b070340204400340391310040b070780e61380300700000c1801d19202404104001151601001da0040c883c2e01c034003170504512100300007680d8007a00100c000c500300e2420007d103a6824404c05500c005500300600d00e4601c0c021010703407558107010404110300d800140810440d4025002c8886038080c1c08c4c211b1382e0702e5002d8100355000f500300d4003c07 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 1919819 1250 1918569 1918571
    0xd050f040219030503031504090206040b0715051014030c040501090501150203040308030f0601020304031523060d021c0506010f0906061106010b090a05060a03060e010b07170a0306031212 82
    0x80b8207000315203031206002ea03a8060b0055180d03413030b400d0f900c884002011103441ea0041e1103c86140040c0c40d4000a00010036200d1030703540e01c0f0103c1d40703084040311071703415540144203241404001a10031140b98074011100e00c0d6040300000403851001c641000b05443d0695000707030130305c400000c4000c6141d0100d8100c0d914441017034000c1c8900c103800c98580c030451002420b140c10510204820451034806150081c005004503490180ea0303941d450042c80185019104159035400c19180384020504402c0041d0101c441901191070304100007000031540060281c0121100000c22400c040504203000445410400712a500d40e91240024804a0305004004445091072000960240a01d0350b5041000688015010340da08052201f40150050390102d070380602600c0c0c0c0000c0680301d20700103000307400b544d5030085001410012000544001070b8008406140100b208030042240862540510419810003541e201d145000490103000582c001511050400050458841d08070240c07070b1034001c60b160 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 1921069 1250 1919819 1919839
    0x204050d050a030905030d0503040b10120302010506030c04060b0304030e040b0409060902041103070206010303080a09060c05091002030a02030702010809160806070906020105040206070609150614030f0105070e060a050d050f0402 100
    0x30302d43c45001c7d9407443c034003040c42480400c001980c3c00d1002c9038450613640d8208112681c1d080c04054194000c0d100f900542d55800511469003020320407201d4200d41640d052140c1403030444c1a1100703120040002e400c00404005c0c1c03164555136504a5142d030394008005100006442c04d1000080c050104100e2140d40303000c1d41c191029000c201685e104100c2d50b00030b40001da1071a102030b103c030880101140303001941c0d25180c02c00207555100d02d80d0b14000c140e8481e51100c40c42c80510181d00c80384014030381513620510240c1d80c001d50000c11a01d81c940d0a00c0d001ea01c44e00d0700021103251008041d00e283c0580091036002c070360b2040000346d0304e20030340450359010102c075650711099089881c180c401a410101c204030800c04100c00350040100725110f0301c42e498085c1e064001c1c1800711141500103c80210001041c02103914080100d8040c000c0c0100003000941010a0b01901d06041c07504094060300001c600d5600542c0201c068032b00d04190320b00207221900d030200550091660031101203210300c034889 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 1922319 1250 1921069 1921079
    0x20f0106051c02120a021c030e04110f0a17070f08010f0302030c01030902030c040501030804050307080102030c0d1d07030803010f0801020a0f050c0f1204060f0203070309090f0204050d050a0309 85
    0x9149000451004254245a40e50b0f000c0c818260103019102041748642640000142c8900c80c4070100e60f2510300724030040074140d19005150030483c150709481142041d140c48050204a8119410b403640d50340c034940d45d440d03507080c2555100c081c4900d0941c640e070700000b00008241c02c03081c03030602c183c00c0d50b481c1070440c0e888500303d81c400603184c08080d4141d80b0403416071910354000d41c480951a03000400321740c41c2d9802580001e0035900240c004032000e042c0400c0811040c01d0401c40c031009802d050000b50b04610308a12008250700805101007401515a0040005003030100154440441040261098180c480c1860300d081c2c0d00c02c0c455880c03502850500000c5400d4180300340c072070110341039840710004500c640c1c1c115440d80051280c101140200b0010b030311a903004100075040483c66414040e2124a0a6030107000b000f0440804815900200175580c0081e600140c440150741d010b000000d5407006c01c640100003030066070461508a400c2e0740340142031140c0001c0a910b022310a648200c1c0c0a41c4030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 1923569 1250 1922319 1922329
    0x9030606031401200d0f0605030a03090503010c0c020d080702040207051009030e0105030601020309010c02030705060406020f0d030e0709090302150403020a05010b0f0d0206071505040c06020105090706080a05070903080a020f010605 101
    0xd13044800b881040c030141408100642210072440c050620201340c0985032030003e42000e62100049002c2089504c0030801420300303000b200f4040c4500d081420b40226079401180503030b880060010940310000400c0011903407240d0543d00c62540000c12601100c0c01c984000703000b08804c1d40f09801107941142c410980f5031185007164880d032410703806581440400b00055600c009804000c0340e06024060010615803500303009400200013070b9000f03009a403c0c061900d8203000244042008060901031420044040043c40804860f101240040c05289500b42207084c55450340c0720b41580806e100a0109160b40020001c0310035019400030410003e00c6410051900e40b0300f2109500002d180c0361150151038004058000207005040c0315128801c00c603c158110340c41200e088440d4125010107112039982481030507800424034008000d03203030600d140a454000020005e16900e0b13107540c002680795120390302500085a0056038245c50307001e41000a926040d007070100b1802c1d50300e0020001810b1403c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 1924819 1250 1923569 1923611
    0xe0606040f090e010f0e07050405010902041409070203070506070c02011806021906020c030301030b090607091a03061206010611010e060103021f0c0803010806040b0702010203090601140109030606031401 89
    0x60301c40d0021800b8500303400708000e4142051010440d540e601142071540b0102d0050000703c1e01c012004d03042403400e1404100850b141070304403100c864410300c01444403214810540031f41c01d800300c5071050180d0b904081241355103d44031008040b4042d080511103283d42023503c0000051003600c8292140c049400030301d5420703509108440069104000101e4140500075945070982e0081401600e4641c030300011030b203982e000380e1040b02e43d420513508100a84005000e1950020300625210380304a1404401800a0a8040c074903480300000102050344c42d5113502e440840e40e503903502a100030b0f682d29400602844c1000100c42510b50038103000002c58038011030154140d039402400c122540d400014004407095a6943c10000d0162001b41032001c0b4540030301550082070500c1c018190381c40c0a21785040007640c05090703401035a00500600916071000304820b81920700d441702c20700100c041c94004030342d074103041d80c40078044900c0d0603404014840c01032190050100c04500922904004992140282075 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 1926069 1250 1924819 1924829
    0x1a09010c0305030606070b13020a050904030203030601050d0b030a030e01030f0e070905040c08030c010b0103060e010e13020102010b0d0501050603120708040e0601030b0a060f030506010503010b160203031209070e060604 96
    0x80d5490080010340036101864010700c0107448076082c034400c1d99030031409a0381506c0700400c54045500c510700f140f60000c10762015103001e0380c001c0f146040507a0065030f02d0001601c203a042c0700000c203030702c244c92200e0750210229500081c1140d8200000d0f040c06000ca007100c0091078006402d1035913103a02c50b10b00d40118040e0030641c07402880c1440c68170280f41d004090107801154000382c801c0001828120800c044c102c001214000000e0b03000c801e10000d0308031002507200d5049035040304010048403034485005980048003c009415080640c40101e0040c24806a00380d408507009400105111056204034407c0000342d0442d00c0a50b2081c01270140350203080300060902404220510030b0b60a1441d04603004201070601244442141c03000a0044080340c20080009402003e100b002c550300d80115608000b00703003081485c5505007002c006951188002040070355031030044c5e21085450800c100e0746010b4502a400070581000c010369901e90300c2c3c511070780501090342400702c0c801c2e1800d0400c40f82214 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 1927319 1250 1926069 1926077
    0x60203040308090406050409120f090509010605070311010606110c060306030303040f0606030b040609030e090702030f070201050706050f010e09010e03030402040b010507050d0503010801060f030203070302090c0d020a0302041a0901 101
    0x615540c1d80d10420780c0441c0f4241d41081c1c85800c001410f03229030140f82200340c4141140d4044184044c0c0040070008182c071248108503008a00300704540380d20400905541c094904650303130754410706007076075900482c2c0392004566180100019040d40e07c181e00c0103450701000140d900b003010010405c01113000c1507030403036855082000480c00281c01500d601d2202403103008041038255503030300d40102c01007080702d042d1640c43d111240202003641c40340b03425003404400caa03480001e0510b014000e540303000300d50380700841c1d0b100010180c2c296030044069803021544040c0500c154607001114440c0e00e807082c42000160000310010600418060180103030100b900380081d0700319035654003000007a00001003e581800800c11200b4080b607400d02000302d99000c0d80e15015036a506d4182c04600b117a9040d48858140f91b130b000d40500069802003061000c0b00d404447da03651545030400f0040c1d00d0702c1218110100b00b84001000d01c0c40ca5003540140084038000003007282030802500d26000349210b8462214005 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 1928569 1250 1927319 1927327
    0x30c03011a010309020d0606080309010e04050702060105040e01020f0d020a0906020a08030a15030b0f06030607020705010203180301020906070f050c040e06060d05010209120106080607020102040303050f0309010b0d0605060112020301060203 105
    0x80d501c42d501c40d552075030008007407411300b44440d125a400c4030042d80100c952740e00300041060403075801082c0c2c041d540000392401c10851400b0500203455090600802e88140e0302d03010103104d0403800750180ca90314800f00502030707076500c1426184402036000e0b80c424400703c0c2d12100001115400810b80d10a140d8000026605d15a50548460b0007000c00c03184442105da0040b0000c40070607507a101d4107100341c5000d141b410490420030304152610800070003040441d4092403044c0b040e43d90200c15500051a00341000c0070400741500080e01901440039085d40210380416a030b4140038443c450301d40c0c580e004000343c620b02035034602407100f03032100ca42d0300003034030380c480c01c0418558140565640301141c050000141450340d184000740395680f20301080c26103070f9194142446440301c1404041d410058500003149028a5940c001c3d182d4021741402d0714114002200140000314290400c13110388c1c0d030082c112804420b407454032400500c07054410f94009070302d040d00141045518421281a200c15400450070 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 1929819 1250 1928569 1928621
    0x106030905070e0109140a0b01050a03020306040603020306070207030308070813031d090109020901080a0b010e011103040e01031401050601021b0d02010302091c021305040201080c0705011b0509030c0301 89
    0xd8824080d00300c0d810321a000d40000c20020424109020b4410f692003c0341c0d52460b50502600b04078090f00b8080200d2501380d1407030b440e83e00107040f15881d0800742009038490392104001740007071000d94000780d010701608003003110b07065001c113114059074400c0c0c480448a80716103808542d80d2404481c45490b540d403661613540802e00802010f90104c0440400180000c0c0041c082070140030203a100285658000c11201ca5941e0404622684049801400c000c02040303030000910b040d00300840c803414080400f402003040c40c0c0038012140503009400c03113005156501e1404610040c0700690075401540381c140810520342c400702e9810740144074026459800c948500800c08503c0406a00b207040c59420008683d55032240c0d00140912001a0b48444404e2143d005001c0c40e00400d0035541c0c030580c6003104000050703070080c240036000200b4040003034850103e0300d4054010100b00116070300d5403800a00f40e0b40240d1303003c0004d0000480c207a0a440300749400000b03060176506c0c28000d40b2f40da4080841700d005 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 1931069 1250 1929819 1929821
    0x50d09080a0506041401151403010b01030216021c060504050a030e12070611030c0a050a05010b010c05030d02070201050d090b0114010302040e010506090a0b0f0403110603010308070b18010c02070305070b03010b03010603 96
    0x442962400e00014000d40b25601d01e4a121f8025070140310681d00381c030300c0d0702e8080c5420720030f000c407514081c01c0179458003000507d250741400d500c04009108034407060001040035240b10034600d000b81d0044040045003017a0500b02d81d00e1050100c00c6000580c0f603581d0140380c0c140300d41a40e801c0c185180c01401c0c1a400d019058403444000e80b411420351009200b09650008100080c80c8018019000703000e0300103590a03c81e085d074511302c03111414040442c482100082000080310034848235590010f840e0001c0d0310049419102c1d24590b40b4215043c9461401800043c0300180d040301c0600c200d503480c1041e901c005400740d0040f48144842000814010881d60518000070002c00400600850403261110704c0c84416401c001c0384201031a0700480c003070081103003100703004004040032600700b4115031460303440e0001d034410b82d0002000340c058400890740c1003034000c540d400c20b204160000d008001c1c60880003907a6100c14402070724248150b000c002901c0c81114201c0b4143c55408440d2451070b0f0078400154 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 1932319 1250 1931069 1931093
    0x4060507110307080c070602061905040201090905010b0a03050601020d0c03031112040506010906080106030c030312060306020a020f0c0a0501020703080a020a150608010c08010503030405010309060b0607050d09080a050604 97
    0x80c0c140216050100700c0716009000400f0982e00c986a40ca46034141684040e00d418281c1e0030500c00c2d5405881805190904a407002105002420011803a9581d030310040701c0700c0c00c943e400030107540e04020001c90044614405041e05102c04d5408000039a61f403001240c0d541c8030214180e010900e8031280c48046882a0020044070310007846440c82d284072210340b80c403800b03000c0304c003a504c0e40c00c0f280041c048203c05020708170040c10351000a204050071903d5040c0c1000700c41c4002070902c000030b40300941c0190309411810040d50010b80440d00c0d8020b143c0080d40341c0c01b100786940b82c03a018000550100e072405c424035206980040e401441c0701c0d800e5a4135603255070b0040609001754407844000ea00040c00403088900c000e60035032004241c0070310f448051400c0d1340340c550504003032011000060060342c400009840443e20300b460040385215107070030404010700c4c0e00115160081d0000501c401481400201802c18506598528000c0c0d03940d035500c1901c8280303603c0010143c1d0170190220b008110008408 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 1933569 1250 1932319 1932331
    0x921030b06070501060e01060c050d110c040f06060f090f09020304020607050a0318060c031706010c06050c030105090105030a03120b0406080d120510120f050a05030a0e04050a02090603040605 84
    0x4a04850100007981c0d0741207500c1c1211960744442080c04042e80402075a4014034441c14241e005401e40e6480d01c0e25600040800402c0000784000d00e054404e0400141c89070800c0035001308400720b0400b041c03c02070040c0c1e014030030108160072006800244101801c5040b10801c2805c0e1030300d00e0030300061401951010f00140ea220714203002c0280410414460110040e10030345030030703d40821003201101d102070350b45c0c4088103112a8001900219800603540b04200c2004000b000c0c5940d542001030710729900428000d002d241c9801c0800400c2602c460095041c0c420840300c1841603aa100101540c1e60490034004000850404a401c500940ca13000b461081c50018408210039464865491070b00c1803c1c50504002a0690720309401c0741d180e0f1081580040c00701c0c000c2d64050713040400d04c182003011080b009105848072007080007404402c0c09400d100a03800029250780f03a0380260000e280c404606a010300c12868000860401e45c028400c86084500c06880f06085a0319a121040200340041103 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 1934819 1250 1933569 1933571
    0x50d03021203090609070b0901020604030c0201090f080c0405010906030c0b09010306030204020d0c0e01020304081f0e030a05030702070b03040b0a0e0703080d02070b0f01050607021201020906030705040e0901092103 94
    0x4050318040d900266200f034039400014a80791506a0b5040d1a040c2103a0101101801c00c020114082e41d0125022f42d0040d01410005001041480125484c640681c405007449541c408046140c40c0c003c0366607168503808175028811662540340e0b40d005c5400302c1c44024205003010301d041200020400143c05071349014140046c00710742e00e80100e016644071070140310b01199140c0c24428490b42241c0142c620007400c2c4000c5003401e08010040d80d0b1041d00118081085d01e4a54400600d0755154200b00c1c10844194162522882c44540141c100d80090302e003040540220800420860502000e4030311403900301180711501d03250b030580c02e40203200411501c08140130b059008000b155207500206032851900c000141e486c0ea44d8106104449030241600031038800103801008541d44001c141e030a6a0f8040300e460014402c0e01c15110700a01c540d6042039007001c2d000c000c203c107454108002d0400c0300d144810114840e40d80c294914201d03070814000500342088211403894001100740e04007442c0f500c0e810 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 1936069 1250 1934819 1934833
    0x306030a0b0711030f030f0f1603020702040b060a02060603060702030304120804031205070905180408040e130c060c02040e010c020a03030e01060902120405070503060f060609011407030207091b0504050d0302 91
    0x80a0b815a8031a820317814102d800001480102d4100c030007010b0740400b201c4526030441c18004008001d171100b80e01c00204141c0c01042000030740d40c642d0320010119400401d159a281c071000f001a448020485045110f401010001001540003000b00c9108580c400511603800070b156500751803403a4013500550402c45140303510550000d040c80380d2030060b200d64036001600e9151004000d02c8000003088910b410f00b0650601001898850640c1c05803416088050220b5a9007100030350140c00000700605007645003100000c8503908041d0002c5118002d80d0305100d50b4102d0585c0e00d003aa00b83e1421074005900613201880401d10039803000c1c04241840e800030a005980c1e58804040e03820521410300e000d1200c0040c00700b003120410000340146030580180c1858500111914510007005114030f000700310008081e407040c0c0c4203c4866540e03043c41c8202e180c0f12100c6050095440c3c0d82070203207600c15440c004013035000c0342c00c0040c8461a01655960305103454102001c4c4010000c1040c01281035200f114 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 1937319 1250 1936069 1936097
    0xa08060d0c03020306190c02030a05160f12050304020103050705070209060d1b09061401020c03030307030203040501151203020105060f0a060c060b100c030e010302030c04030204020c071a0702030c03030306030a0b07 94
    0x4003c01c6d0003518005080003100e4076017092001110f81c501000c0056510407c00d1002661300801906d4034103011201c90404202c41317007001c007400f80d5182c400501c0c030b415004150002c4c0ba00078014501580c001e0380d08000507515980152454414010040d40c08181800015507506d400d15001c4641d0748075105070711090b00c1c021440c3c20541565003007003d00d9501c5840038029120b07445007070402d408092004001454501012984030300c80900380800f010380000c00201481f000750454541d008100050303040302c40ea15682c02048904425044005500700300200d0694600048124006180100140313605481c1c90310559154610090859040741c880805c1c0034980e42d0740030607152121407070701eaa014003500c07850014640e42c11044280e041c1441071043c026185c2981e0140c4040e241c0c1510016940c06c90310188529011f40c65002020840500c0ea4207940480d00e900984402403091b411500c01d0208901010744a000c00c03540740da05030703000041e48404203070340c11303c0c16420044038100403072074152030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 1938569 1250 1937319 1937323
    0x30309080307020a110414010b1605030415080f01060207060507020103060305010612050f01021c020702010e0306010303050d0612050d0f090e0103050714010305060d080f04050d0b01090608030a08060d0c030203 92
    0x88803804090703040900c4c02c0061055100020381e8000c070440341044520415071684240000c18050b11500143c0480d40768502000c44091400b095040012240c955035030b8140440c61603000700a500c0090010700c086035001c803001c040c0c03a050310116009000340c02e092910450350303500a4003041c0c1c10591204e46c0080070403c01e104841c05400401c0309041e43c0c400a0920700d18101c1040c1354280705070320421607581c80d2182501e00404050794084050f03540d0050b0300040320030300200c09500d5898000d410000081542220052129180c82070040c012982e0301c030b09420603042400c0e009052354022041c440c06143c4101400c20382d0308404c2c1040404661162906441e10b0f00036042180c0d680d000080c10b00c0407509804080e05822000d180c244a20b10b001808603010884015000707003408404210400d45001800c1998050580682a980c000c3c0007401e21144501083c8220030281d490300c00c01040040c00031048515000c00fa8990360555103900c4188155000c4d591400d940c0381074420030110060350700b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 1939819 1250 1938569 1938571
    0x60d02120708070206040308060904080c01050906090106080109030903020411040f03030806030606040903020a020d03020304150207090509030403030c0809030c06070302010b150901020a0602090406030602070b040c09150b070303090803 103
    0x144030000d030041c1c5000a4050280580546043c2c02d40d4050341c10000002d500013005a80b12500b40d407c1d0440d40c40300c0c5411348007801000c540740119420041000f0f08000300080c1c0074820b1501800a0100030754888040c0d00b200c0103110041c000440800007407015081030741243d4901550790140300d14050b40c82180a40c40500c54004034005a09801801824036040241c144c01140884041101180710b9502944d50868500e00a0180c4662072415061500a1007581c004080801010f6540008104002d45824940c01740318412032429002c1880700d94000283e909581d41a02c4840d1640c9541d141c003003c0d5000301801c40c1d45481400c031103983c40d89489002d024840d109400105100000d4000c104181200203100e21907080f060060244603a800140e50010580001e4016500c0704070001250251600d40c002603e100e00003c0c80d842044401e44e00c5611581c02091000900ca8440b4841000d5601210a00010f8696010b045c8001d40c411001400382500c01e09000910307182d80e03a20a091908 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 1941069 1250 1939819 1939837
    0x105010305060f090d08070e0d05061008060c090109030201110106080a0c090b010c050303070e0d02030703030203070b010902031006110c120601090e0a0203030304120207080303150f01030b010c02040506060d02 92
    0x401801e118210400c0f15825400044500c041c2100900c0b8481c0141140c0c001009801081844401ca401e69240c4004003001c664000d42602e01900e4018060742040c810752052620a2085030000380c5680c8040040e20100700c4140c0d101e0418600d56001150241e140080f2100c855685040004403003c1c10050780107450700c10401c44804031300c1c007103400303040399003d200c214140182c02c00d00318001361001c01140c0e40f0888604004a80c040e030b00e00820228200208001d4042c4907020021061540010161903c244034000c0b90206a8036481108180d00040c0d4041c3c02c0f40350b000300c00340301160240026070781c070180ca035003203540500d610b5000942003000118148000d030403510052008804030302512010400440081085548650100380c2c0e901c4024400b520f00da0001503424070051080c04010001c22803074084235141d04003461580341c0c09000348592441681440068032030382d4007a00411224000503100d404007103105409010141c0700003080c10f0303440b032000c00c0200c840c0302ca80e00c0075181900b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 1942319 1250 1941069 1941073
    0x60e01050111210309030403050105010306050604050709080303070309080d020315040f06060e120c0306070f0201061a030f0601050f04030303050105040f050105030706050c0a08070f0201020705040e03090603180105010305 97
    0x54034180001d03003003030035201d203804554119030700105665050140d400c2c5100507182900780e80380c2d50303010341504501450700700a1031542440000010701c60280c000c1e501610084904001549400300244d0382d0b585036114100b8182c0051002804003402607010b0307000903009100d02441c0001a03540c002c00c990003101c000550784071401c44803206040070b21404903c1c508510301082102e0600d0000b1f08101d400c000410720030342241d080c100143c042400301149900010b404c81390070741014a40501400c41418070080150310b8080005010044146040003d01c004036042d031444d119558070504510b0010320b1681406810001040d1440070300c0d0080000394003030340d40002c007941420100b009482081100071010780c1450010710007541c001c0354200803105541400c40c0d840a0044400e03040143c090406000d0240200d8402d040c8030030302c0c1d0408007051003642900ca44545a40402c0101e48000c102d007a1941d100380004555801c1c9200116080740d504004441d2001c6881c0e50301d07082d60f400342c000303c0301c607 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 1943569 1250 1942319 1942321
    0x510050d0c0201150b0c030405030109030804050c03060f04020603040201030b060d0c03050c03040804051201150909020f040507020709180b04030201020901021b060f1c0c0207051002010b03060408030606040801060e 94
    0x80480c9110303a010301c0c441c80c0700a00241003030068000c101042400b50b0488880006005076912104001701c1c2d0040a002e00240412100f5041c0a0120001204c0581d0140540a1403030250300d00460302034400c3e5011800145151a00d070240b001e1504001e000302d05040c2c0c4d030341d091150783c0c7d01c0ca0054400c1519040c00030400f5400c031000101075990240c240e03107220782d0500500c00003594600a48040d80d0003600d50f00422424005000d01510005c00395504110820310041034808441d0090301d00c0c9402a41d040c503c004030301041c0011640116080c20068002e10814041c400d86908101182c0b02030341404060030b4001e0319440145034050742c007107026070b50000d40c1c20407550301800980340c01c2c1000744500c0010040f60b00450760321b124035001207501880005644814050143c0840c8040c441ca040420503000d0f10000a59110b035103004070303407017103c2d180014015107205004840103c00090301400c943d4955030b549035015040a04078582c0320307005000104110800b442884010103202880c0016 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 1944819 1250 1943569 1943587
    0x10e0606030c01030501080d0503040c0b04260307030905040b0d02061c0605010206040c0303030c031d06070806060705030711040207021201091104050906070f0201020906040806180a0309030f0201020106051005 92
    0x82c220080740403d041c03505050042007070340d1000c54130003c01c100c6030800d69034a985a1500c00c001c1241d80e0000b8441c4c2401280101e00070b6106414400702c0020b02e260700b003041c150968001d90328001d01600030005180c2200034095401c081d0062003054038003030074005580e81c03564006022034004480a05107000035039900002402180a561b0003068280054411405c1c80c0d2200d44800c40540009401d00d40c841daa1090300718442e500c42c80760541098502c44138419a03607031454880d80151864800204900040344aa24188084070b0403664401c00031441c01c101c0d5640c00ca000241c807807205602590038421074002d603d90201d20300100301d400713000080b10501c5180c018240c038510204103018903d403204218403250002211a0003c030942841c0d5400700c9840303400c9004e4810100ca0340c0d00402e0201d40002e40c4031000991500843c2034070241550621398001c9182d451004c20005000100b504000f0004120001c030007030143d0340103200100e802c070303100c20108800d81050400600002c80001d01c2d601 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 1946069 1250 1944819 1944823
    0x606050d0206030a05060d0c030506040507080607090909060605040501030803040605010605090105090904020f040606020d020712020306061003060302030102120916080714040608010f02030412020303040b0c0304060e010e060603 100
    0x151804540821108003a038011030701d01d00004201c92415991031001c50441c3c1d441030320b8000e0403507006c101000301c141c0300c0c6443d82c0c5610064404444903c102030003c1071990700818514400c180d40d0361800c40c42440c121581c0b01500c19228250b8840d692081c001c117940d22107001d528003860003a10200e40e20304207842c004040300d00c1644102c081040510240e9040c0c1c0c0d000c0c04443c3c02103011510245241c5581c0002852034544c6071020341e0061074020001502500460741038024030340ca4081e100c5140d070350040003028481e0702400950640000d00041e1451070190303190000404146800502c9503203230f601003400caa120003030310f0b17646078203800070406c0461042049008100c00004900720343c601d0300741d520b95501785901a0081c0c80000c0d018509158941c0c3d448a001032040300001e004a440da810407400a500644017581d040c207031230006c518aa0b000104990003030350b020180581d1551010003440c0e45800207001150000e4803402802d40e002d0090040079609441840944218100750341098 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 1947319 1250 1946069 1946081
    0x60618020a09050603060102030c150106090501080910150906030804030606050f09060f040b0402030f040506010509010303050306010302070c080109030f03060801090302070b030606042301080c18010c05010f0c0c06 94
    0x1000403401004520307001030303020080c1d1046802c00d80e020744d00d9442d10b03c010f03030440c06010a0300300700d4403914040300c00041840a2841c121507464039000b0b0000d0f1030308011180c0001c112518a1641e0142036107103068560b0307038424243d0440100360040783c2e5840700085415038855900a59204002007024410700465100e03a000500c8211078803218003240302c001c1021410000c0816100f07000364110350344251150f81110f440d09200901c110355074980a815030740640e20960b000d40d9140300c4c480010490703003003452110b4140e90301138450038119510403004601039031084001700d620345881440084c0c00142401028221880303910b4600800020b10300c01422541503501c105145da05000c4620003094001c10701c0004d070381400c480c1582c4d994411000c581c0c54803850b446aa00d000350b50301c0381c3d008841040c1030600182c03402d0340e4550b101d8440b0740310003101e07000307100402840d40341800303000c0d0f0f1642c02403c02c0d0205520480001c6191000c16403a1400c031006800600b022034404000c260070403031103205507 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 1948569 1250 1947319 1947359
    0x20f0a0605040305010f0603020f0103090512070b150d030507060905030f0301031203050c04050a05010309020a030b0c0301030302010f09022101141003050f01060806040803040606050607150c08060102030a050d060b03040606 98
    0x4001248c9542c002070002900c03880c90505040d515403403002401414082c600d0300e001d0780344115030b94040f1450404a4031404884020301c214100c0c420306610703d00f10b0b007050640d80d015030704d041c108141900d0b00001000c0b00c031021a4288810802c0d40c0314040200040d50085016940344140700304002c00c058140c4400808080e40000c04000611444d03880c0401101565828a00014000c80391b101250f11010750b80c0000e000d0314003410400c40200070440c0114181c030320a44c000c0c003100030b400300b104c0b041c1c400c0100001d50001954504550380300000e500c1c0d420072003181c800800c402c1d050302c5100002d840300740c0300003d80d260090340034001c6c01410080c07001803c021400801c00246802e004a03151000035100501c41c3d0400004501448080c1c0c0007000580001002995900700c0d40ca000304460043c0601403405604200d00e51049900500204c0c0c89040103801440c41c0c60500001280c0a41c0454010b032150f95450101040d4000e031400990b104900c81c0ca00040c001d42405041c598005080040e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 1949819 1250 1948569 1948571
    0x60103020907030f020906190906170103080904020d0e01061511060601080403091a03190b090a0c02010f0e0f0f0303160509010c080307170105030307020603060d020f0a0605040305010f 81
    0x1000140c0341d841c1c00395803000640c03034001031294841000001912500e01030301d91060002c981194030303510210445141f0754141e2240c070010703a55030301d0076074050320004840c0c0715810521004001045e100d100804404c01c00900c018505681050728038211080a44451090ba40d620303402d00040441d92040c60b01035040e410002d103800d081d006941d9036008001c04107410041900041000c050181911202a200041c0f46000d101c4d846c114a13501a00112200c42d41046151003003042d4144510640e65001c00142c1008034035a1182c00002c0981b2214074806c2c115980d40d98003060003445032041c1d44491a000002e44800c3c9550301e03101e0f02d0105100149100c41d003080051100b1880116140d05141d201030030801e481d18280300058030a0030320120080c00d50340c8001704008d149540650300341d250300c210101420150b40c07124281030303590141242c021f410000800c007090a614019000c4400c5506c000c1281d030820611a010800844417680000041600441c01f0310412500780522203e400b07015030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 1951069 1250 1949819 1949821
    0xc01021501030f030207050a090b030c040e0a030c1401021b060606030603070303141306051b03040807050405040809030a030f020601080d080c030403030605030d0908010509030703091a040302090c03150306 90
    0x1540c805888010300c0001c000b50300ea0101001014024000100100002007030984001c0e503e805000117415540002446800780f180070f0081880d040c4581c66000040034010200044280c0e0103a81b8a40c982900355084850801310001091090000740b5030703014142c174046840c9040c015028a80f4101900c9188146001d10822059071800200301080320b805103404000c11000c24103581e818490303100050043c040c903900200c0d8290b0018000d0660090010358a0040300721071918540f030340294042c40c0d00f00c2d04403410030007042c0f40c130f5084a508a070295100910f081c6404000901c0d120b038034041100402c000700780045c5216010b0240500411080c07028001540b020000106001c02c002c00300c0351ba100d808404501814429404680a00006000c5413107401c046040031300101e0080c070a0081c0b56003404001080200040242e4207810b80c1900d48284090a040742c180341c0901d0b0004076010034000340000400b50f42d41070711090080350341218066590a010100c0751406034032102980c002e5000c54 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 1952319 1250 1951069 1951093
    0x30d0f060803031603020f0301060305091501030c050111030c010c020d08011d0604020c0307020409050c0a0906080309060c030c0102030f040c09050402030a020108060d290907120206070c03080c070303020c0102 92
    0x20048130750040d203070401d0b1a0f654140c00b4066009002e11020180050004000451f40c17a8140e071045016245090481c1e4401c024402440d5840c0c3c02400003c00c0f811900c442001194060000d22007407000010582e400e2201554815003120214904000141d000c9072502e49480c1e00880c034240544802c3c580001e1541a0a0b804484610090a41805540e0014480d581030b403050056a15141d40104240300141c2641002648c6012007040244500344071600015003055500c141021070340e800f0055030074242ca1350100007007a04900010151170100b00303c0341080c94000e10081d44144a02d03003441c0e880d41411304000380181026041b824500385010203100160b500081c242c0b40c01c60782441c00f06042e950340700103d0240d01010a00500130016130b2813411528151508910000d185040c0400e0165180d00c0c0c1c066032024144901c001102d07440e014940036040641c01000035030301900d10700e912103941e540c0b4005d2692005540700c00c40e402003070040c8101607050100ba030302c46409100519102c6110 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 1953569 1250 1952319 1952323
    0x305040501050906040305010504030206071b0203070509040602040b04080a210203031504150305010e06060409030903060509031207020a11060a050412020d0503030702100606020303070914010e04020c030d0f0608 93
    0x3401601d05100e00441d080315240d0342c050883d005154010020703c807038105494080d54911055500c2d00200300c954013140b85c012102d041704216550024000e007070041c9010f09001b4000005401038070710303940800000c0742d20310089004000a100540c020300c2140501e05101c0d400310805018030300041c2000840030100c65000080e031ba0800c14256900103005440d00c000390007000041c01d010242c1c0c2c540c2d003002080c0601940a2040800b83d078080d15869a10b0004200c116103c0b402e0040114102c01001d00118550382d10003540100c0500071645400e850307854400110108aa050006900100c01e18040000b013001854503104140d900a003000000c2c8000752080c02103008070404601000116002c1d0b41c1c2c2c0c80c011070041908a03050765175904086400035120b200030856145100d080540c0058020302c0001120712500d410b946a80c040b40c10501c0c070003000501006964100541401c50300301c0c0da0f40d20301c01401480c00130402956242c0341c08540c9070964526140c2800e1061600a041100e8440 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 1954819 1250 1953569 1953577
    0xd0906021b0415030203060c0405040609060506030403050c0a050604110102150702060a0207020102010204030804030602030105030d0503070c0305090102011407051b0f0a0305090310051003030905030105040210031109060c070f06020a0305 104
    0xc840120360089981c100f50800b0445a0003e90b041c49201c080c4101c26003004003c3c815104180c60501c1820f44940d429003d480540c4100340c2c0005d4100005030110744240c01034001d03a2030f100291071594109848042c0f40007010740302a0764440c0b42405c19001e075070b0104800310209850900c0c00c80185082e040180d00d0f20340007003810381e000c1e0300050042d04680c402c0d811035026681c0404155200c84d10380c1401d000170b420034000d0500920a624210341203601400960f0700c101e2090399840c00c505140e5900715040d400c42c90505040d503490740001c0340181c40c0090f40c240304071400d5680680b1185981242c1082044e44004008503800c0418020381441c00403900c02c0c3e6042d01804c085580c1d00801c03010030b00d03002c81c141c0c0031170010785408140b01c6082c04142428044a0003640c400075520b840da01014202e81013030f20020b40c8400c10410070309816001ea00500484103e1004041c1010040400300d42c40380c0c00340c051402c1d19000343c4800d01c40b0303100600b1884090910b500c001c242d101e0260f900546a0309c1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 1956069 1250 1954819 1954873
    0x40c05041a0901140109090509030901091703071104020405040c02010507120903080f040c080304120203010506010305010b190504050418140303010e07110307021302030405070e0c0703030f020c030304050d090602 93
    0x80c81100c4e05506034040c00d0324000400403007070200154645446610340f240c20042c1400e0000b00c0801d00010b0302c044151210102d0045c0c000550714201c1c0b03543d514009030803540b0049403c6030f002d200001e11951903104c1d42140c2e00003600042907515006600800c8184e506034200b91503403802c1d4032800400d51003048180d2041178645603a9054866080840c035003803041c3e100c401c0501c40010007083c1c00894091207241c0c0c0d48250000c0c40b094940800640c10b9500074020381c090364200340310f000d01001c068040c5070290070007030034160318090301e6038007280980d400c02d9080c1995032040841c04040021841030640b215209001840c1554144a202000f580002c0c11100810074170f0703812001c0c0c04200b8801c4030800c0e80e0040c110070800180340640307800b070f402c00c9406a909000d0140c00107440b280110800d48580c9561800c146002c400756015002805400503203144154203101d07480703400c20108000d5010300c3c005c00092020000140e8000c04a6105400490442d002240c00412020104441c180c4d030803 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 1957319 1250 1956069 1956089
    0x6050f0309010603141c0f05090402090109050901060302070b060904170309010b06040e090c0301060303091a07080309010605030f0a02010512150301060e1009020403050705010f090b03040c05041a0901 88
    0x70319000300312400752110b80c0014149a03c0000004400e031800620301929103000606055030090032030303080d00c0c44554041c05201054082000f0b04042c42c05070b000384007800d01410b1030f60101c2c2e241c3c40810200304098120700003203a40010343c1d41c18403122241c4258068011240000613152503a28541c84066050809140ba04080003064080d02e00703411201c0c2e03109020b821580c603603555100c17400da07141c015110096503002d201103140040c14103000e400f05598040d202c4055442c038110901400385203e0b140321a08010a02102c4005040b4034011341c0120425070011030114100010142064007007185142c041d0711a041070401070741c201c0c0589880c107000002104266071003110054542c0c0383c3d2602c140d03044d4a010008182c0050b80f074500360149148030500e0882d1502d8882c000201d12560002030b0090f40290810072196201350b0302420407601904c1c250480130707a41d2242c040035030800d40301228112000007090015092512170000c1d640401040c01052102d0003010590028060040c81500 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 1958569 1250 1957319 1957321
    0x807060b03030d09080d0506090402031c030f020403081306021603170f13030b060f01080c09010c0203100501030201080f01050607020f120d020606090f04050d0c020114040806190606050f03 83
    0xa9941403094030f81080c00c209040c806421185048000c5610182e01040c083c1e10b0000440c145041094045119503405401003c031100c48038050b407040d0221801800070142c07151116a600314031070018000540c0300350300c090703280c91046c076003e207181d271181d045001154402c402c2c8444880045480e0030880b0b4001d600c04a8010309551107020901c1611070443c44250006541d424450040c130402040303a0244035404e815032142c10411010084590080c0e000400031340124140303210034802069181d40504010008440d00d5012a04003c00500045034039580c0d88010400e55030402d1b6580e500c141003a4000d50150304040c0016658080c1220190290981c0d8400c0103194403400803415142920074200c0c0c21201d50804001c0da2040c0465965004081c003502081041c40741d80302c440e00455100014040c0001480e41c1100c03032814440c0241c7c10401a113012034803910300e1500600140c220207001c1e00492521425002815094448003c616450400e003008070640c440142e810906015951641e0303 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 1959819 1250 1958569 1958591
    0x703030b06070b0604050106030204080c0105090a03051e011107080f0307030f0513020102010e0a050601060f09030605011d06030a03080601030911090c0405010f030c02060412020a0b0a02040602010f050103080706 93
    0x1030200d40039903504a5000034104080c00315260b4124841c030030445040c806170ba201e141c101c0c243d0045d441400119880b04801200d190f000e64040c04901c40040e000100d04c56803600d51500c0c00106510041114002194880001c0d40038001c83d407a43c2ea40074041490200103583d58501481012140b00c0d1210020010401e00303031080d08590a00300d41600280124106242404010f21082808030302562819050340f4089030040760900d103058005010b02282d83c80d1000c182c60303515031010b000b02081031500002c40010520b2150074003800400040b10a074808240e041c411561018005a02c6075000100c050006580304d03440503880341c420320300800c42c2c0c01c0911701405440c50000f0420360050041040200c00305200c0090003c8600c240d90f240306520301c859017581281c5520380710100503000b500000340410f019a014810300704040c4100c5a90481c5919240781c140340940700c0d0102c8640019041105032ba09000d100c5c010b170110b11042207994510742d07030700e0340d40d108142c0010003a6440303220140d1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 1961069 1250 1959819 1959821
    0x70503090a0303030e01060504090b01030204050601050f0c0705010801120b04110a03020409140c09011206110d0c030605090a0c02060105040507050c06010803070b0a05090d03050907051203030603011a030a0305070303 95
    0x1181406031444041c5500c03450040c0280201c8500c441d1198640304002500b454107000d5100301940200501d00d01e070f400c5409210140a000703007210305101040008840203884000200310f0f1b13921501c040c28885080c44001426080c3c11792001d50401040700c0d00c0400b003400c04005e0341c1c21a6006c800400920341b80c030046455044240d00207503115180203128000c0c400c503041640b8030024844180d41e0650742a4041102041081c00390080312040c0014202c0010b0b255404070a60b2455030744400d061160400182046d80d00c04241c240009480f10340c204001c1c14200340050700311360f0071003091080550307441c002560b60780148a41c512850b11a0081040e80c0c0c06901203d0368001e58509661942da103412581e07540e03500035041183c000540d14005a0340101d248280360095400202174000c10044c0700c2c084001d01006801d030441c90044910005403541e90003422020301c1a604003035901c91034110101400c607408a0340c0325100321000da000814954004c100101110381c035042c001d44410850404070 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 1962319 1250 1961069 1961077
    0x2030309100e0604060206100e0108100b04060b030a0b040e010506030a030c020604030203030705030c070b0f04030303021b060106020109050f060f0106050706060308030703050603010f0908090103200301090504140d08010b070503 100
    0x5030040f00002c0c0100741640e0204200b44220840c0302c90703188660340e44200840c600004d11800c07802d034004968000f506005034100040700d1000901c04904c6030740340c1520b0100c6510542c2c0310f00001b036a42c00052428281400b60701800c1103c000208441d00e080c0d00400e8480e000302d080181009034840801003150340340d005942c06141c015044070f0300d40c0e01500d0040d58961281480380d1b00e0b88210304001821007821021030386c000140c88080380c200783c595902640690051a0b4078181c00b100d0040800720741008000081c0204007950000c5030262240c18500e0a0010801d00b00c40603800c100208107105d2185103c03e4110b907030918207290b07151003a00b01140200400e80004011450020601c020716a16070415809803901b00e008120300c00020b00d00ca0210340300e0b0100246581810301c030702d00d030030340c001d40c002c588881041078000342d54580c140c080b003401e80c03013600240c0400b580c0f8001d0006004074651081082d0b40500300074400f04614040140c10100144034030004031000003114010420288151 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 1963569 1250 1962319 1962347
    0x60509240c030c15010302010c0b07030b120601051005040302030606060304031107030308040b09030a090902030c040302030106090f0b06040b03010b0d09060c090e0c160204020a030e0a0f020405010609030203030910 94
    0x426107450030030420035160b611510380c10409205522131600300d01200c00d1524102c80e0305840310b07907215080da5610410750900400a4091581c0c03103e040c036017500c0d02c0103032031401c842c00e001031306666061400300514035642501981c10800244000d000685001440c150040011683c060b00c07965a40380483c6c0300e04140744010400c4c01650400420107810a1f8501e0086d441407090046581d600d80e0781035501d0007092001d90000b41c3c542e000b002020722990080da0010b6655049900d0261a40c0100382514025071240000d10b60751080d0f40d0300710842e0702c26200ac40340222000342c0380ca842c0c075034110418001801540701041d00006e00d00402081135200c0e8100a500c008c0501054981c2100a0000745083c401c00b805000d07908001901410300c90b04862a00715683c805204504054081c000250845040310090668400040306506410450b420203288125040355552f1068814002940d40603480a007c1c402002c01c2403006a03000310656090071001d0780c45074801810300c0740c1280c0015146203c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 1964819 1250 1963569 1963639
    0x40b070602030108190218060f0303070507050406091803080705090406060309140303071b0f05070807080c010206040807020603040c05091e100303021e010204090609020a08090106060509 82
    0x410400c0c550007440c125501c400680b120405c1451009102c1c0882c40d03002980148210010344188983c2050300350080c102401200c00110b554011a16540c044001a80c0a034800c6404200030319007409100054440ca0038148030b03c1181600c19070440f0384580c001814044014001074041e8800c606540d81100001c100b4041c15a84020140040a10410644640352011031102a01b0030000c1100d000b41119611001d0b51141910121420032002a044540b0000250703e0400704004021100c040c0c14280040c1c80421300c0d080340c051034504501482419900300404100205901070203460350190142d60051b62a5620324001e0792180d0035030071084e0b201e541035091107005851000b0b1000300c03208050301e07136a850301d84207109220b0046e107101c010300581c40000c140400c1c070a6030b05411108214800054102611100410140c0d503107900b1052881d540410f850040d20740c003501894000c1080c41c000c00c182e500f0914010701502ca54a11503004805e1804481003611a25140025115980724 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 1966069 1250 1964819 1964827
    0x90d1202160f03060b010c02030304090207050a02030f012307080a0b040e06070201020301051503090607030207031101050103030507030801060f0c11060702060412050706110c09072d02010609020a050906030a02040b 94
    0x30b0b1244560510f00080c2c51151034040603d125501403501c101d40103400034001c6042030315001e0408045e500400c401c9905004410700b405c0161010030141c0000340045001061035440100018800c0c02d2428080d03070040ca41c0c0d0b0a05c566190072440f800d4006184840115450b01e403070740402d0181941c84041c1741b1a10a01042101da00c8e03041d40a10305880d0212000562801c040280e9401c0380803d81d5510781d030350000e40219100038041e138004c00d00f040c13007824221503612441240f0f6003194000d0780f041d404501c001800400300759001f1010303805400d00d07003000032000204100042c01c4120040e0010b10741c0038016aa406660f440e08103132419a940100000ea890351607600040c007490520504895500c1080e5006c0780c00c07800707010141032402090005017400a82c00c0304000d1003c1c0080c10071004c2c044c912040090980c0b0f55800c1c007580d02c1c4004061800120556030090860b506503018200c00c2c1e00c1406200c02c000e40c04000c845000404035801922520b0304003000c4000d04c01d681c03100070305c103074002 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 1967319 1250 1966069 1966079
    0x30c05040b0c07050111010902180a0b06040b030f0c04060206060d03020f010c0302040503010c0201050601020307032d080601021606020304030b190204030f11010504050105031303030e010213090b06090d120216 92
    0xf500001c0c0d810aa071045170418080c1e0300707a0700f62000c4a1001b94489648901140786400090806500130100040841c80c03009402c04110310340c0c0aa0032004903c04000708000341c002e008110300f9044030324070701e01030b00c0c061038004c0003034507003401800032449410602400c600385072007007201d00081c80c2d9000013040384650442014009501510a031401b03542020b00c0c03460b502d40188200c601c104410303000345103001e90a0740e0440f0b2505454400c43d8a800c00c1c400d848407a0050030040541542041d00c60844505140c8006440c045420034607050300401e02c0800d200c0c0c0f03039010080d500ac5a5128815107040e031a4072030301000306c1d01185041224181b0201c0c001040c044000c46602200f07004018032030041041c0c000460f002d114038002d00d03010030010000b041d1100d184085a90f6918000e02c0e00040c800e007180625400da0740310b5041e0a043e0402040184091840d03842180951007003201d44915007a41840072030440746424601810311056120740c842c82d140248042c01d5019200350350130309a29120 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 1968569 1250 1967319 1967323
    0x402130e01060906030b0109110a140c0105040b01030204050f040c0603090f02030a0503040501110c090103030c020123040807060201140f0405070f03060606030e060709031103031605060a0b0d0c0501030c05040b0c 93
    0x511094403010f0001c0700016130002c0078440c00c617102c2c581c000310620300303c40105cac152075403035951791341301c148141c00c006486030010b007880340302c1c01544a12031680e069455401000261038014116200d50340c4541d013400001109102000c00715041420081098096800c0c000d4440c038030010041e40500400340e40408022000c401802624000d0700c0726003001d01c030306d010030740d540c0c10340d451a030703048000a401400400c0c0940c1204003000c0c81454901c0c51503220319800a2960b44104c803045240001050a020200d0203101e03080c05410769200030807030f0740c0c0d41d141c105a40d150040e00c0d00e10649010008a004e12105002c1400030741950712050b00c03807075030703038542034004001600c214030000e0f1a20211210100e0f012902e24050500b40d900c041c00075085071541c621805403131203655414442007100801030074145598040f058003d901a110364602032042c07000f9606440c88291090304a41d4600d0000354071103a108003660001c0c0b9000039000251682507440c0c0c843c5800c03d01c142240890104210400 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 1969819 1250 1968569 1968581
    0x1d010504050c0a08060f040f020c07050a08030c0606040b0f03030c06040b13120807020c0409080408010c0203121302060409050a020702011d0a0e090c0607030c03080105090f0402130e010609 83
    0x810390301003206a0301c0300c0402c1c0c4a80500002200000c040f0004a800f03450201c90451a08034002c2c400262007020355040012030344105092790340d41c0c2100e07808100503e080000c04c0014012117002d1460701b0144a0603a4403248014152807240f550b4408210aa8a9155801607074207405011203036207840407042e50307686041c00c0718101c0d00e090701d8000181c42080f00d00d00400069903c644030aa60700141c2c4000c0c0e0b00d103007005114904620602031840304c140e60f940100d190190054421035036443c00c0480c520b0a4a414100c2601554010800b601517145102c8942c0d0303001c1e1b01d100d281d10300c200245c4000b8540c0d100755844030382007a05103001e009e4841c400e40e000f020744034803d032582d20324503101040d542c000159442c038143d840344030007004002e4550a40c8170168020045c500b50381040c052040020401c0c0c01900d015800202001070202c1010b0304081c0b840e001d0801101c10900da8500002d807440041c0005000a02420310343c00d4a8104c4842e50b0010900351000c00001c0c002583c80382590310082c01 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 1971069 1250 1969819 1969829
    0x60308040608150a03080406050901110118031d090414070503010f02120601030b0108070c0606030b090303010e01060203031003020d0312060801020a02070504090b060d02120610051002030901090e07091d01 90
    0x1c0310748580ca42440d10814140461b03920203001c0c0d04003454000296266080200d10505100c0301812000c1d070560b003032045802800e0304c0c0c5d80100c140c0c407043c1401000c00e09158500095070340d0301c40303110919564440180e640203034400d030221070182601c46800c0c10030720075a00254140d030800f00b0810900b11030b038014115a000d5940b003101c0555030200118280e4004069142c003203000440840e5486100d85180c0c62000c1c020a0701282d115036a41c0c41844040045450b90300d542c002000620103c1102c007505801000540700540c11401c1044202e10f20154521001740310703007079902d801d000b010b0054580301d080f01c0c03043c40304107c81903036003030114081d5208500d0203005016051002c0781c13a1915104451440342c0007944a41c07103a031a402070299112421a0680e03008070300c0108802110010004944909201d02ca400341142c544018081c0c0100304488a8003590020711401e005a40d000c07840008454247c550034159443d082825070b8044069040864040203500080381d5581c030076444141290 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 1972319 1250 1971069 1971091
    0x90312010906031205030403090501080c0f040b0702030105060102070f06030903141c05060109060c020f240901080c0406051206060c07060302070b010501080405030d0c0e0a080c1201051005090a060308040608 91
    0x2182201341190a8402214000c0104041f040f0038080c5500c5030306a190f0100d101100240381034140c1e0510341c0300d60400d6000d07941c403200009003142103040c280141a000740c0b0030300040c4074a6080040340b6403074030002d0007402c00b056956403440050510480b180441d041400340c91582d10f15001d10170559907250352501071341c0103042070040f400c076500c40c1140004460182e03503406201e55042e82007003030759511114403e0348110001064080000c860b4410f022500d0061110f5a44065240000d8010f0f10024018084d0365814801041163340dc6003c54194808141e504540da41d030b02e030005800c1d0f02814507094207038850210085142500340d8014070f402e502a030014100c80c4e03038560044030380c0b0f4001c4800600503042032007078443e07030300964102c2c8038a00c0050038100d0310351102c440070444152103076001c010242c0c0301c0c2da02c400030340c200f210042011031140710081c051841c1100703031610b802d4041d00c1a10b000b43c8212000a1406119600c080082e41d4410301ca10340d915540d26008007541c00c242c400881031 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 1973569 1250 1972319 1972343
    0xf03060602030906040501030f020f0307050d060803040b09010302030a0e0f030a0e0307080d1101020706050c03070e0405040b011401090305030a0302120109021806030408070506010306020d0f0e060f09031201090603 94
    0x225000100381c0c3e02d03007040140b6240c41c0078208001100a030202e0b0745180d4071243c080c44403015090b200401b8511420b4142e40306a102c424801800c400d880d620f030720611294104200c140002c07208a01140c00700002820007680d0b03902c40b9003003007000340014030400420340030700c0200d8401000c000c001000101000d0380c82c03802101039a0101a02c412080c402c0c1403007940450b240520503030140039000d0008051600041c00d001d5292038030000d03150202c590f0801c944000007044030043d08028048003602090700c0c00c00c464502543c034449001d0060150700001012900301c50303000da110344a454007440d03001c82502d45817035030064050041d400207961079128078040b000104a4031b0840c800d44183e000d0280c1854881d03803035101071001e158400340064078461000c016001c00710b01d04000480c001d521417400141c1e03030321075032868034210b482946140d045a0f08100d841c1c0050180000d81035041502c1172643e020580341d4250141c0b940c400d820b0980940031580000055074806580705100b12405003200b1440 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 1974819 1250 1973569 1973579
    0x2010f200301060305040c091505010324050402031305120c0f06040506040b060a0b070c05041d070e15030a06060f0b03070f08040302120d0504110906010503041101090909030f0306 79
    0xc240348000c4400c1905028070040100724420307004144c01500941481d15550b0315141d02500b910402141d80032083c410b0344c4101300d25640b51080c081440180f80311850b0031328901011002055091203030500c05d54020002c40c0f0340860824860340d80c1c540c000216401c0e4401c2142183c400d4001c80750320080d50082414900341c1800100d4500c1c49260b118010b07142943e00d550f62121084805000b040d00202d0407000072480703041c10401010740c0fa004209055000b45800100001d076600b107900d40c2d0400768610500c0e030511381c000403440161400c2244012903070b07842c100817410704843c04103180c1d8544282c503c0c3b601072021a50041082da40c0c8a01541500d9854907410f4065201c2950b02c000000c40075115250120710a1142e43e40040c46071040c0c1e205200c0400c0c82004541008242c841820340da0b8061004200341103040030001842501c80001038504080040c1440c007000b400a010220303922603502050f8450740700c10015120041041000c02d040d070800808464814540e000407a10f88080414 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 1976069 1250 1974819 1974851
    0xd0e0709050108030f03070311040801050a270201030b131508010b0303030c040302120f07060306091506020705060307110604060b0f030a0b01060c0503070501020d090309060503010f0308030c07021002010f 90
    0x105a403c0040118500407428104200d40e5100a00c100d00f01640d80002d03d2032000141c000300014110600045820f04004d800c82048810080c0004141c81101886540b0b43c22000908280c403074090070000f56403161000441c00c64211550f032124403d1910300b000444c02d260303920703d0301901c0c0034200801c200403459040c95a01d11003902d41151070002404100014900000031120303c1d00040240c520402c08400c101e484c2c9086500154080794886ca010b00880100744100100e50366403282070743c4440c0c0342c024080c3d01c8106c1401007501a0100100140c070032400382002c401d02025240444440745018203001000f4a042c0450b20b1003103141045485243c6400a050301505030071442e02401c2e07901e405c40907109412426001c5a40c4d0009218010108000b803000e02a202000343c40490401c00d94580200300400c00d402c483d081c44001c1c0300502c01c407a100521070742074941c801441503494585004600d2140030303810b0000e51003804a01151200d66041d04903480400e580c4d0014030480300781244d020303 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 1977319 1250 1976069 1976071
    0x215010807030209150409050a080c0c0a0e010605160f0302150105010503041104020307030b030303010905010501080106050406020d05070206040302030f07030309150c0b06040905060705070309061b020d06020c030d0e070905 98
    0x3035446100030b0017040d518420003401900c0b02c00300401c0006c0e00190b41d0745090070024001350a51715000003091070041841c01b800180c103803031412074078180c8850400031b0400c0c400b0018041e01007006000304060030801d4550f840c40c401c2c0380d000360102c400c20a1900c0d00955403c030403041403180040355000080c5a500803000d0703a02843d80b010002c0d01c5200ca5806110007500020603010816440701c02d02021510103000560103081d5011010840d9814440054401141a4003110030044100410024a036010510211060041c40c20381d9507134015000240141c05250406945802009080418030f04000740810450380f107921100c10700c036550072070754010301c2034042a1070111308501c4e01c20340040e2018880c2588401c00620018400c203894480300d14204085910b42d011132800507881e03040c140c1158101000b0038003071600185901c607028403050b14001c5018024000c0c0039840114040203007540640c0c400803045001c40ba1100b112090f20005010f08104115250250481c0482c00791880c0c003c4c2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 1978425 1106 1977319 1977323
    0xb010302030105090f07030f08040b18090105040b010212030a020c060705030f060405040c061b12020102040f0b0301030305030105060c030f03040303050a05070305060a0521030a021501080703 84
    0x2040c03c560001c0d10549041c1e210050300c52200300001100821b8a5115400c0c0390840c0281ca86840f8502840d081000162800726a08030300d00658081c46140000031280c900e883d903a903005010403140c0d0b0704035040c0107821503a040541041c64400458200030000c600525003442c001510b401c0130025070b41d480005d4000420b00c641078104010884c2c100b01c04031420050703410950b42c0d031107601142d031040c0300038410030240101d00304c2440f00ca002d0310150401c40b00b052038015078400078001d42c0a030050036488160f045010a09a4403001601e050ba80d05032078103441c5900b0b20003000061380061210894912080103803007035801d0a10090740c0518843c5d2008100b5040c44014002039903001000310041500c2e103410006c5070342e44c00d000d0008540341511042c00002c500f490381040d8103012074017a120380c0300014024444039400264051400c070080c050044598a071505503455403094400 = true := by decide +kernel

theorem cover : BRFrame.Cov 1798569 1978425 := by
  have h0 := BRFrame.cov_init 1798569
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1798569 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 1798569 ≤ n) (h2 : n < 1978425) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
